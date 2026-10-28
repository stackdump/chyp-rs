# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 the chyp-rs contributors. New in chyp-rs.
"""Differential fuzzer: random Chyp theories through upstream Chyp and chyp-rs.

What it does
  1. Generates random theories that use only the features chyp-rs keeps:
     `gen NAME : n -> m`, `let`, `def`, `rule` (= and ==), `show`, top-level
     `rewrite NAME : T (= T [by TACTIC])*`, and `theorem`/`lemma`/`proposition`
     with `proof ... qed` blocks of `rewrite LHS|RHS (= T|LHS|RHS [by T])*` and
     `apply TACTIC`. Terms are well-typed by construction (built bottom-up from
     the signature, `id`, `id0`, `sw` and `sw[perm]` with `;`, `*` and
     parentheses). Some input is deliberately bad: wrong or converse rules,
     non-isomorphic right-hand sides, steps with no `by`, `by refl`,
     use-before-define, a rewrite citing itself, duplicate and undefined
     names, generator redefinitions, unknown tactics, ill-typed terms, and a
     little syntax noise (comments, line breaks, `==`, keyword-like names).
  2. Makes most steps valid by synthesising their right-hand sides with
     upstream's own engine: a ProofState on the step's left-hand side and
     chyp.tactic.ruletac.RuleTac(...).make_rhs() give the rewritten graphs,
     and chyp.term.graph_to_term prints them (as upstream's GUI fills `?`
     holes); an edgeless result is printed as `id0` or `id * ... * id`.
  3. Checks every theory with upstream in-process (chyp.parser.parse, then
     chyp.checker.check; a case where upstream raises is skipped and counted
     by exception type) and with the port in batches (`chyp-rs summary` on
     temporary files), and compares the parts (kind, line, name, status, in
     order), the errors (line and message, in order; for parse errors only
     the line, since the message text is a documented divergence) and the
     rule names.
  4. Shrinks every divergence (deleting statements, then single lines, while
     a divergence of the same kind persists) and, with --keep, saves the
     minimal theory as DIR/div-<seed>-<case>.chyp next to a .json holding
     both results and the original theory.

How to run (from the chyp-rs checkout, after `cargo build --release`), with
a Python that has `lark` installed (upstream's only core dependency):

  PYTHONDONTWRITEBYTECODE=1 python -I tools/fuzz_diff.py \\
      --chyp ../chyp --port target/release/chyp-rs --cases 1000 --seed 1 \\
      [--keep DIR]

  --chyp       an upstream Chyp checkout at commit 3d28483 (only imported;
               PYTHONDONTWRITEBYTECODE=1 keeps it free of __pycache__)
  --port       the chyp-rs binary
  --cases N    number of theories; --seed S makes the run reproducible
               (case I of seed S is always the same theory)
  --keep DIR   save each divergence (shrunk) as DIR/div-<seed>-<case>.chyp/.json
  --case I     regenerate case I of --seed only, print it and both results
  --exclude T  leave generator features out, to look past a known divergence
               (tactic-comment, corrupt)
  --corrupt P  share of theories given a token-level syntax error (0.08)
  --dump DIR   also write every generated theory to DIR
The run ends with a JSON summary: cases, upstream crashes skipped (by
exception type), steps compared by upstream status, divergences by kind.
Exit status: 0 if there were no divergences, 1 if there were.
Stdlib only.
"""
import argparse
import collections
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

STATUS = {0: 'unchecked', 1: 'checking', 2: 'valid', 3: 'invalid'}
STEP_KINDS = ('RewritePart', 'ApplyTacticPart')


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


class time_limit:
    """Raise Timeout in the main thread after `seconds` (SIGALRM)."""

    def __init__(self, seconds):
        self.seconds = seconds

    def __enter__(self):
        self.old = signal.signal(signal.SIGALRM, _alarm)
        signal.setitimer(signal.ITIMER_REAL, self.seconds)

    def __exit__(self, *exc):
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, self.old)
        return False


# ---------------------------------------------------------------------------
# Upstream Chyp, imported from the checkout given on the command line.

class Upstream:
    def __init__(self, root):
        sys.path.insert(0, os.path.abspath(root))
        from chyp import parser, checker, graph, term  # noqa: E402
        from chyp.rule import Rule
        from chyp.state import State
        from chyp.proofstate import ProofState, Goal
        from chyp.tactic.ruletac import RuleTac
        from chyp.matcher import find_iso
        self.parser, self.checker, self.graph, self.term = parser, checker, graph, term
        self.Rule, self.State, self.ProofState, self.Goal = Rule, State, ProofState, Goal
        self.RuleTac, self.find_iso = RuleTac, find_iso

    @staticmethod
    def wires(n):
        return [(None, 1)] * n

    def gen(self, name, n, m):
        return self.graph.gen(name, self.wires(n), self.wires(m))

    def ident(self):
        return self.graph.identity(infer_type=True, infer_size=True)

    def empty(self):
        return self.graph.Graph()

    def perm(self, p):
        return self.graph.perm(list(p), self.wires(len(p)), infer_type=True, infer_size=True)

    def run(self, code, path, timeout):
        """Parse and check `code` as upstream's GUI does. Returns the result
        dict, or {'crash': '<Type>: <msg>'} if upstream raised."""
        # Upstream only ever sees text read in Python's text mode (its parser
        # opens files with open(), and Qt's editor normalises line breaks the
        # same way), so "\r\n" and a lone "\r" arrive as "\n";
        # tools/upstream_expected.py reads fixtures the same way.
        code = code.replace('\r\n', '\n').replace('\r', '\n')
        try:
            with time_limit(timeout):
                state = self.parser.parse(code, path)
                self.checker.check(state)
        except Timeout:
            return {'crash': 'Timeout: upstream took longer than %ss' % timeout}
        except Exception as e:  # upstream raises on a few ill-formed inputs
            orig = getattr(e, 'orig_exc', None) or e  # lark wraps transformer errors
            return {'crash': '%s: %s' % (type(orig).__name__, str(orig)[:300])}
        return {
            'crash': None,
            'parts': [[type(p).__name__, p.line, p.name, STATUS[p.status]] for p in state.parts],
            'errors': [[ln, msg] for (_, ln, msg) in state.errors],
            'rules': sorted(state.rules.keys()),
        }


# ---------------------------------------------------------------------------
# The port.

def port_from_json(d):
    return {
        'crash': None,
        'parts': [[p['kind'], p['line'], p['name'], p['status']] for p in d['parts']],
        'errors': [[e['line'], e['msg']] for e in d['errors']],
        'rules': list(d['rules']),
    }


def run_port(port, paths, timeout):
    """Run `chyp-rs summary` on `paths`. Returns one result per path; a
    panic or timeout of the whole batch falls back to one run per file."""
    try:
        out = subprocess.run([port, 'summary'] + paths, capture_output=True, text=True, timeout=timeout)
        if out.returncode in (0, 1):
            data = json.loads(out.stdout)
            if len(data) == len(paths):
                return [port_from_json(d) for d in data]
    except (subprocess.TimeoutExpired, ValueError):
        pass
    if len(paths) == 1:
        try:
            out = subprocess.run([port, 'summary'] + paths, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return [{'crash': 'PORT TIMEOUT'}]
        if out.returncode in (0, 1):
            try:
                return [port_from_json(json.loads(out.stdout)[0])]
            except (ValueError, IndexError, KeyError):
                pass
        return [{'crash': 'PORT FAILED (exit %s): %s' % (out.returncode, out.stderr.strip()[-500:])}]
    res = []
    for p in paths:
        res += run_port(port, [p], timeout)
    return res


# ---------------------------------------------------------------------------
# Comparison.

def _msg_kind(msg):
    return ' '.join(msg.split()[:3])


def compare(up, port):
    """Differences between an upstream and a port result: a list of
    (category, description, signature) triples, empty if they agree. The
    signature names the kind of difference, to group divergences."""
    diffs = []
    if port.get('crash'):
        return [('port-crash', port['crash'], 'port-crash')]
    up_parts, pt_parts = up['parts'], port['parts']
    for i in range(max(len(up_parts), len(pt_parts))):
        a = up_parts[i] if i < len(up_parts) else None
        b = pt_parts[i] if i < len(pt_parts) else None
        if a != b:
            if a is None or b is None:
                sig = 'parts:count'
            else:
                fields = [f for j, f in enumerate(('kind', 'line', 'name', 'status')) if a[j] != b[j]]
                sig = 'parts:%s:%s' % ('+'.join(fields), a[0])
                if fields == ['status']:
                    sig += ':%s->%s' % (a[3], b[3])
            diffs.append(('parts', 'part %d: upstream %s, port %s' % (i, a, b), sig))
            break
    up_err, pt_err = up['errors'], port['errors']
    for i in range(max(len(up_err), len(pt_err))):
        a = up_err[i] if i < len(up_err) else None
        b = pt_err[i] if i < len(pt_err) else None
        if a == b:
            continue
        both_parse = a and b and a[1].startswith('Parse error') and b[1].startswith('Parse error')
        if both_parse and a[0] == b[0]:
            continue  # parse error texts differ by design; lines must match
        if a is None:
            sig = 'errors:port-only:' + _msg_kind(b[1])
        elif b is None:
            sig = 'errors:upstream-only:' + _msg_kind(a[1])
        elif both_parse:
            sig = 'errors:parse-error-line'
        elif a[0] != b[0]:
            sig = 'errors:line:' + _msg_kind(a[1])
        else:
            sig = 'errors:msg:' + _msg_kind(a[1])
        diffs.append(('errors', 'error %d: upstream %r, port %r' % (i, a, b), sig))
        break
    if up['rules'] != port['rules']:
        diffs.append(('rules', 'rules: upstream %s, port %s' % (up['rules'], port['rules']), 'rules'))
    return diffs


# ---------------------------------------------------------------------------
# Theory generation.

GEN_NAMES = ['f', 'g', 'h', 'k', 'm', 'n', 'p', 'q', 'v', 'w', 'e', 'c', 's', 't', 'a', 'b', 'j', 'z']
# Identifiers that are keywords elsewhere in the grammar but plain names in
# term position (Lark's contextual lexer), plus odd but legal identifiers.
TRICKY_NAMES = ['by', 'proof', 'qed', 'rule', 'apply', 'rewrite', 'show', 'gen', 'let', 'def',
                'theorem', 'lemma', 'proposition', 'import', 'as', 'to', 'refl', 'None', 'u',
                'x.y', '_z', 'f1', 'g_2', 'idx', 'sw2', 'id00', 'A.b', 'a.', 'simp']
RULE_NAMES = ['r0', 'r1', 'r2', 'r3', 'r4', 'r5', 'r6', 'r7', 'r8', 'r9', 'assoc', 'comm', 'unit',
              'idem', 'fuse', 'spec', 'frob', 'absorb', 'swap', 'slide', 'x.r', '_r', 'R2', 'rw']
TRICKY_RULE_NAMES = ['rule', 'by', 'qed', 'proof', 'LHS', 'RHS', 'apply', 'gen', 'refl_x', 'id', 'sw']
THM_NAMES = ['t0', 't1', 't2', 't3', 't4', 't5', 'thm', 'lem', 'prop', 'main', 'aux', 't.x']


class Term:
    """A term's text, type and upstream graph. prec: 0 = top-level ';',
    1 = top-level '*', 2 = atomic."""
    __slots__ = ('text', 'n', 'm', 'g', 'prec', 'size')

    def __init__(self, text, n, m, g, prec=2, size=1):
        self.text, self.n, self.m, self.g, self.prec, self.size = text, n, m, g, prec, size


def converse(expr):
    return expr[1:] if expr.startswith('-') else '-' + expr


class TheoryGen:
    MAX_ARITY = 4
    MAX_EDGES = 14

    def __init__(self, rng, up, exclude=()):
        self.r = rng
        self.up = up
        self.exclude = set(exclude)
        self.blocks = []        # statements, each a list of lines
        self.atoms = []         # named terms usable in terms now
        self.graph_names = set()
        self.gen_types = {}     # name -> (n, m) of every name in upstream's `graphs`
        self.rules = {}         # name -> (lhs Term, rhs Term): what upstream can use as a rule
        self.seq_names = set(['refl'])  # every name in upstream's rule_sequence
        self.theorem_names = []
        self.fake = up.State()  # rule table for RuleTac synthesis
        self.rule_pool = list(RULE_NAMES)
        self.r.shuffle(self.rule_pool)
        self.thm_pool = list(THM_NAMES)
        self.r.shuffle(self.thm_pool)
        self.current = None     # name of the statement being generated
        self.planned_steps = 0
        self.synth_steps = 0

    # -- names ---------------------------------------------------------------

    def fresh_rule_name(self):
        r = self.r
        if r.random() < 0.04:
            name = r.choice(TRICKY_RULE_NAMES)
        elif self.rule_pool:
            name = self.rule_pool.pop()
        else:
            name = 'r%d' % r.randint(10, 99)
        return name

    def later_rule_name(self):
        """A rule name that will probably be defined later (use before define)."""
        return self.rule_pool[-1] if self.rule_pool else 'r42'

    # -- terms ---------------------------------------------------------------

    def atom_gen(self, name, n, m):
        return Term(name, n, m, self.up.gen(name, n, m))

    def base_atoms(self):
        up, r = self.up, self.r
        res = list(self.atoms)
        res.append(Term('id', 1, 1, up.ident(), 2, 0))
        res.append(Term('sw', 2, 2, up.perm([1, 0]), 2, 0))
        if r.random() < 0.3:
            res.append(Term('id0', 0, 0, up.empty(), 2, 0))
        if r.random() < 0.3:
            k = r.randint(3, 4)
            p = list(range(k))
            while p == list(range(k)):
                r.shuffle(p)
            sep = r.choice([', ', ','])
            res.append(Term('sw[%s]' % sep.join(map(str, p)), k, k, up.perm(p), 2, 0))
        return res

    def paren(self, t):
        return Term('(%s)' % t.text, t.n, t.m, t.g, 2, t.size)

    def par(self, a, b):
        ta = a.text if a.prec >= 1 else '(%s)' % a.text
        tb = b.text if b.prec >= 1 else '(%s)' % b.text
        return Term('%s * %s' % (ta, tb), a.n + b.n, a.m + b.m, a.g * b.g, 1, a.size + b.size)

    def seq(self, a, b):
        assert a.m == b.n
        return Term('%s ; %s' % (a.text, b.text), a.n, b.m, a.g >> b.g, 0, a.size + b.size)

    def ids(self, k):
        t = None
        for _ in range(k):
            i = Term('id', 1, 1, self.up.ident(), 2, 0)
            t = i if t is None else self.par(t, i)
        return t

    def pad(self, t, n):
        """t * ids, padded to n inputs, ids split left and right."""
        extra = n - t.n
        left = self.r.randint(0, extra)
        if left:
            t = self.par(self.ids(left), t)
        if extra - left:
            t = self.par(t, self.ids(extra - left))
        return t

    def with_dom(self, n, size=1):
        """A random term with exactly n inputs."""
        r = self.r
        cands = [a for a in self.base_atoms() if a.n <= n and a.m - a.n + n <= self.MAX_ARITY]
        if n > 0:
            cands = [a for a in cands if a.n > 0] or cands
        if not cands:
            return self.ids(n) if n else Term('id0', 0, 0, self.up.empty(), 2, 0)
        named = [a for a in cands if a.size > 0]
        a = r.choice(named) if named and r.random() < 0.8 else r.choice(cands)
        t = self.pad(a, n)
        if size > 1 and t.m <= self.MAX_ARITY and r.random() < 0.6:
            t = self.seq(t, self.with_dom(t.m, size - 1))
        if r.random() < 0.08:
            t = self.paren(t)
        return t

    def rand_term(self, size):
        r = self.r
        if size <= 1:
            named = [a for a in self.base_atoms() if a.size > 0]
            return r.choice(named) if named and r.random() < 0.85 else r.choice(self.base_atoms())
        k = r.randint(1, size - 1)
        a = self.rand_term(k)
        if r.random() < 0.35:
            b = self.rand_term(size - k)
            if a.n + b.n <= self.MAX_ARITY and a.m + b.m <= self.MAX_ARITY:
                return self.par(a, b)
            return a
        if a.m > self.MAX_ARITY:
            return a
        return self.seq(a, self.with_dom(a.m, size - k))

    def typed(self, n, m, tries=40):
        """A random term of type n -> m, or None."""
        for _ in range(tries):
            t = self.with_dom(n, self.r.randint(1, 3))
            if t.m == m:
                return t
        if n == m:
            return self.ids(n) if n else Term('id0', 0, 0, self.up.empty(), 2, 0)
        return None

    def with_cod(self, k, tries=20):
        for _ in range(tries):
            t = self.rand_term(self.r.randint(1, 2))
            if t.m == k:
                return t
        return None

    # -- synthesis with upstream's engine ------------------------------------

    def g2t(self, h):
        """Print a graph as a term (upstream graph_to_term); None if it cannot."""
        try:
            s = self.up.term.graph_to_term(h)
        except Exception:
            return None
        if s == '':
            n = len(h.inputs())
            s = 'id0' if n == 0 else ' * '.join(['id'] * n)
        return s

    def graph_term(self, h):
        text = self.g2t(h)
        if text is None:
            return None
        return Term(text, len(h.inputs()), len(h.outputs()), h, 0, h.num_edges())

    def register_rule(self, name, lhs, rhs):
        """Mirror upstream's `rules` table (first definition wins)."""
        self.seq_names.add(name)
        if name in self.rules or name == 'refl':
            return
        self.rules[name] = (lhs, rhs)
        try:
            self.fake.rules[name] = self.up.Rule(lhs.g.copy(), rhs.g.copy(), name)
            self.fake.rule_sequence[name] = 0
        except Exception:
            del self.rules[name]

    def make_rhs(self, g, expr, limit=6):
        """Upstream's RuleTac.make_rhs on a goal `g = g`: the graphs `g`
        rewrites to with rule expression `expr`."""
        up = self.up
        out = []
        try:
            ps = up.ProofState(self.fake, 1, [up.Goal(up.Rule(g.copy(), g.copy()))])
            for h in up.RuleTac(ps, [expr]).make_rhs():
                if h.num_edges() <= self.MAX_EDGES:
                    out.append(h.copy())
                if len(out) >= limit:
                    break
        except Exception:
            pass
        self.fake.errors.clear()
        return out

    def rewrite_once(self, g):
        """(expr, rewritten graph) for some applicable rule, or None."""
        r = self.r
        names = [n for n in self.rules]
        r.shuffle(names)
        exprs = []
        for n in names:
            exprs.append(n if r.random() < 0.7 else '-' + n)
        for e in exprs:
            res = self.make_rhs(g, e)
            if res:
                return e, r.choice(res)
        return None

    def chain(self, start, k):
        """Up to k rewrite steps from `start`: list of (expr, Term)."""
        r = self.r
        cur, out = start, []
        for _ in range(k):
            if r.random() < 0.07:
                t = self.graph_term(cur.g.copy())   # reprinted: `by refl`
                if t is None:
                    break
                out.append(('refl', t))
                cur = t
                continue
            res = self.rewrite_once(cur.g)
            if res is None:
                break
            expr, h = res
            t = self.graph_term(h)
            if t is None or len(t.text) > 220:
                break
            out.append((expr, t))
            cur = t
        return out

    def seed_term(self):
        """A starting term that probably contains a redex."""
        r = self.r
        if not self.rules or r.random() < 0.12:
            return self.rand_term(r.randint(1, 4))
        name = r.choice(list(self.rules))
        lhs, rhs = self.rules[name]
        core = lhs if r.random() < 0.7 else rhs
        if core.n + 1 <= self.MAX_ARITY and r.random() < 0.3:
            core = self.pad(core, core.n + 1)
        t = core
        if r.random() < 0.45:
            pre = self.with_cod(t.n)
            if pre is not None:
                t = self.seq(pre, t)
        if r.random() < 0.55 and t.m <= self.MAX_ARITY:
            t = self.seq(t, self.with_dom(t.m, r.randint(1, 2)))
        return t

    # -- rendering helpers ---------------------------------------------------

    def eq(self):
        return '==' if self.r.random() < 0.08 else '='

    def tac(self, expr, apply=False):
        r = self.r
        x = r.random()
        if x < 0.55:
            if expr.startswith('-') and r.random() < 0.25:
                s = '- ' + expr[1:]
            else:
                s = expr
        elif x < 0.85:
            s = 'rule(%s)' % expr
        elif x < 0.93:
            forms = ['rule( %s )', 'rule(%s )', 'rule(\n    %s)', 'rule(%s # c\n    )']
            if 'tactic-comment' not in self.exclude:
                forms.append('rule(# c\n    %s)')   # upstream keeps the comment in the argument
            s = r.choice(forms) % expr
        else:
            s = 'rule(%s, %s)' % (expr, r.choice(['x', 'junk', '-y', 'refl']))
        return s if apply else 'by ' + s

    def maybe_comment(self, line):
        if self.r.random() < 0.03:
            return line + '  # ' + self.r.choice(['note', 'by r0', 'qed', '= LHS'])
        return line

    def bad_tactic(self, expr):
        """A tactic text that is wrong in some way, and a label."""
        r = self.r
        kinds = ['wrongrule', 'flip', 'undefrule', 'later', 'self', 'unknown', 'refltac',
                 'emptyrule', 'badexpr', 'nobby']
        k = r.choice(kinds)
        if k == 'wrongrule':
            others = [n for n in self.rules if n != expr.lstrip('-')] + ['refl']
            return 'by ' + r.choice(others), k
        if k == 'flip':
            return self.tac(converse(expr)), k
        if k == 'undefrule':
            return 'by ' + r.choice(['nosuch', 'zz_rule', 'ff9']), k
        if k == 'later':
            return self.tac(self.later_rule_name()), k
        if k == 'self':
            return self.tac(self.current or 'self'), k
        if k == 'unknown':
            return 'by %s(%s)' % (r.choice(['foo', 'auto', 'rw', 'Rule']), expr), k
        if k == 'refltac':
            return 'by refl()', k
        if k == 'emptyrule':
            return 'by rule()', k
        if k == 'badexpr':
            return 'by rule(%s)' % r.choice(['1x', '-', '9', '.a']), k
        return '', k

    def bad_rhs(self, t):
        """A replacement right-hand side (text, kind, Term or None): same
        type but probably not a rewrite of the LHS, any type, or undefined."""
        r = self.r
        x = r.random()
        if x < 0.6:
            u = self.typed(t.n, t.m)
            return (u.text, 'badrhs', u) if u else (t.text, 'badrhs', t)
        if x < 0.8:
            return t.text + ' ; zz', 'undefterm', None
        u = self.rand_term(r.randint(1, 2))
        return u.text, 'anytype', u

    # -- statements ----------------------------------------------------------

    def emit(self, lines):
        self.blocks.append([self.maybe_comment(l) if i == 0 else l for i, l in enumerate(lines)])

    def st_gen(self, name=None, n=None, m=None):
        r = self.r
        if name is None:
            name = r.choice(TRICKY_NAMES) if r.random() < 0.08 else r.choice(GEN_NAMES)
        if n is None:
            n, m = r.choice([0, 1, 1, 1, 2, 2, 3]), r.choice([0, 1, 1, 1, 2, 2, 3])
        self.emit(['gen %s : %d -> %d' % (name, n, m)])
        if name not in self.gen_types:
            self.gen_types[name] = (n, m)
            self.atoms.append(self.atom_gen(name, n, m))

    def st_rule(self):
        r = self.r
        name = self.fresh_rule_name()
        if r.random() < 0.06 and self.rules:
            name = r.choice(list(self.rules) + ['refl'])  # duplicate
        lhs, rhs = self.rule_sides()
        if lhs is None:
            return
        if r.random() < 0.04:  # ill-typed sides: refused at parse time
            other = self.rand_term(2)
            rhs = other
        text_r = rhs.text
        if r.random() < 0.03:
            text_r = rhs.text + ' ; zz'
        e = self.eq()
        if r.random() < 0.12:
            self.emit(['rule %s :' % name, '  ' + lhs.text, '  %s %s' % (e, text_r)])
        else:
            self.emit(['rule %s : %s %s %s' % (name, lhs.text, e, text_r)])
        if text_r == rhs.text and (lhs.n, lhs.m) == (rhs.n, rhs.m):
            self.register_rule(name, lhs, rhs)

    def rule_sides(self):
        """LHS and RHS terms of a new rule (structured laws or random)."""
        r = self.r
        by_type = collections.defaultdict(list)
        for a in self.atoms:
            by_type[(a.n, a.m)].append(a)
        x = r.random()
        if x < 0.35:
            laws = []
            for (n, m), xs in by_type.items():
                for a in xs:
                    if n == 2 and m == 1:   # monoid-ish: associativity, commutativity
                        laws.append((self.seq(self.par(a, self.ids(1)), a), self.seq(self.par(self.ids(1), a), a)))
                        laws.append((self.seq(Term('sw', 2, 2, self.up.perm([1, 0]), 2, 0), a), a))
                        for u in by_type.get((0, 1), []):
                            laws.append((self.seq(self.par(u, self.ids(1)), a), self.ids(1)))
                        for d in by_type.get((1, 2), []):   # special / spider fusion
                            laws.append((self.seq(d, a), self.ids(1)))
                    if n == 1 and m == 2:
                        laws.append((self.seq(a, self.par(a, self.ids(1))), self.seq(a, self.par(self.ids(1), a))))
                    if n == m and n > 0:  # idempotence / involution
                        laws.append((self.seq(a, a), a))
                        laws.append((self.seq(a, a), self.ids(n)))
                    if n == 1 and m == 1:
                        for b in xs:
                            if b is not a:   # commuting / sliding
                                laws.append((self.seq(a, b), self.seq(b, a)))
                                laws.append((self.par(a, b), self.seq(self.par(a, self.ids(1)), self.par(self.ids(1), b))))
            if laws:
                lhs, rhs = r.choice(laws)
                return (lhs, rhs) if r.random() < 0.8 else (rhs, lhs)
        lhs = self.rand_term(r.randint(1, 3))
        if lhs.size == 0 and r.random() < 0.7:
            lhs = self.rand_term(2)
        rhs = self.typed(lhs.n, lhs.m)
        if rhs is None:
            return None, None
        return lhs, rhs

    def st_let(self):
        r = self.r
        name = r.choice(['x', 'y', 'l1', 'l2', 'lt', 'mm', 'pp']) if r.random() < 0.9 else r.choice(GEN_NAMES + TRICKY_NAMES)
        t = self.rand_term(r.randint(1, 3))
        x = r.random()
        if x < 0.06:  # ill-typed composition
            a, b = self.rand_term(1), self.rand_term(1)
            if a.m != b.n:
                self.emit(['let %s = %s ; %s' % (name, a.text, b.text)])
                return
        if x < 0.1:
            self.emit(['let %s = %s' % (name, t.text + ' * zz')])
            return
        self.emit(['let %s = %s' % (name, t.text)])
        if name not in self.gen_types:
            self.gen_types[name] = (t.n, t.m)
            self.atoms.append(Term(name, t.n, t.m, t.g, 2, max(1, t.size)))

    def st_def(self):
        r = self.r
        name = r.choice(['d', 'dd', 'd1', 'd.x', 'delta']) if r.random() < 0.85 else r.choice(list(self.gen_types) or ['d'])
        t = self.rand_term(r.randint(1, 3))
        if r.random() < 0.05:
            self.emit(['def %s = %s ; zz' % (name, t.text)])
            return
        self.emit(['def %s = %s' % (name, t.text)])
        rname = name + '_def'
        if rname in self.seq_names:
            return  # 'Rule "d_def" already defined.'
        if name not in self.gen_types:
            self.gen_types[name] = (t.n, t.m)
            atom = self.atom_gen(name, t.n, t.m)
            self.atoms.append(atom)
            self.register_rule(rname, atom, t)
        elif self.gen_types[name] == (t.n, t.m):
            lhs = next((a for a in self.atoms if a.text == name), None)
            if lhs is not None:
                self.register_rule(rname, lhs, t)
            else:
                self.seq_names.add(rname)

    def st_show(self):
        r = self.r
        names = list(self.rules) + self.theorem_names + ['refl', 'nosuch', self.later_rule_name()]
        self.emit(['show %s' % r.choice(names)])

    def step_lines(self, chain, top_level, last_side=None):
        """Render a chain [(expr, Term)] as `= T by ...` lines, with some
        mutations. A Term whose text is LHS or RHS is a hole; `last_side`
        renders the last step's term as that hole instead. Returns the lines
        and, per step, the Term upstream will build for it (None if none)."""
        r = self.r
        lines, terms = [], []
        for i, (expr, t) in enumerate(chain):
            text, tac, used = t.text, self.tac(expr), t
            if last_side and i == len(chain) - 1:
                text = last_side
            hole = text in ('LHS', 'RHS')
            self.planned_steps += 1
            x = r.random()
            if x < 0.11:
                tac, _ = self.bad_tactic(expr)
            elif x < 0.18 and not hole:
                text, kind, used = self.bad_rhs(t)
                if kind == 'anytype' and top_level and r.random() < 0.85:
                    text, used = t.text, t   # an ill-typed top-level step makes upstream raise
            else:
                self.synth_steps += 1
            if r.random() < 0.06 and not hole:
                text = '(%s)' % text
            e = self.eq()
            line = '  %s %s %s' % (e, text, tac) if tac else '  %s %s' % (e, text)
            if r.random() < 0.04 and tac:
                line = '  %s %s\n    %s' % (e, text, tac)
            lines.append(line)
            terms.append(None if hole else used)
        return lines, terms

    def st_rewrite(self):
        r = self.r
        name = self.fresh_rule_name()
        if r.random() < 0.05 and self.seq_names:
            name = r.choice(sorted(self.seq_names))  # already defined (or a theorem)
        self.current = name
        start = self.seed_term()
        head = 'rewrite %s : %s' % (name, start.text)
        if r.random() < 0.05:
            self.emit([head])   # a stub: no steps
            self.current = None
            return
        ch = self.chain(start, r.randint(1, 4))
        if not ch:
            t = self.typed(start.n, start.m) or start
            ch = [(r.choice(list(self.rules) or ['refl']), t)]
        lines, terms = self.step_lines(ch, True)
        if r.random() < 0.04:
            lines.append('  = %s' % r.choice(['LHS', 'RHS']))
            terms.append(None)
        if r.random() < 0.1:
            self.emit([head + ' ' + lines[0].strip()] + lines[1:])
        else:
            self.emit([head] + lines)
        last = terms[-1]
        if last is not None and (last.n, last.m) == (start.n, start.m):
            self.register_rule(name, start, last)
        self.current = None

    def st_theorem(self):
        r = self.r
        name = self.thm_pool.pop() if self.thm_pool else 'th%d' % r.randint(10, 99)
        if r.random() < 0.04 and self.theorem_names:
            name = r.choice(self.theorem_names)
        elif r.random() < 0.04 and self.rules:
            name = r.choice(list(self.rules))   # shadows the rule's sequence number
        self.current = name
        kw = r.choice(['theorem'] * 6 + ['lemma', 'proposition'])
        L = self.seed_term()
        ch = self.chain(L, r.randint(1, 4))
        trivial = False
        if not ch:
            t = self.graph_term(L.g.copy()) or L
            ch, trivial = [('refl', t)], True
        rtext = ch[-1][1].text
        x = r.random()
        if x < 0.06:
            u = self.typed(L.n, L.m)
            if u is not None:
                rtext = u.text   # unrelated (probably unprovable) statement
        elif x < 0.08:
            u = self.rand_term(2)
            if (u.n, u.m) != (L.n, L.m):
                rtext = u.text   # ill-typed statement: refused at parse time
        e = self.eq()
        if r.random() < 0.08:
            head = ['%s %s :' % (kw, name), '  %s' % L.text, '  %s %s' % (e, rtext)]
        else:
            head = ['%s %s : %s %s %s' % (kw, name, L.text, e, rtext)]
        self.seq_names.add(name)
        self.theorem_names.append(name)
        if r.random() < 0.08:
            self.emit(head)     # no proof: stays "checking"
            self.current = None
            return
        body = self.proof_body(L, ch, trivial)
        if r.random() < 0.06:
            # a step after the proof is complete
            self.planned_steps += 1
            body += r.choice([['  apply refl'], ['  rewrite LHS', '    = LHS by refl'],
                              ['  apply %s' % r.choice(list(self.rules) or ['refl'])]])
        if r.random() < 0.05 and len(body) > 2:
            body = body[:-1]   # stop early: qed with goals left
        self.emit(head + ['proof'] + body + ['qed'])
        self.current = None

    def apply_line(self, expr):
        self.planned_steps += 1
        if self.r.random() < 0.15:
            tac, _ = self.bad_tactic(expr)
            return '  apply ' + (tac[3:] if tac.startswith('by ') else 'refl()')
        self.synth_steps += 1
        return '  apply ' + self.tac(expr, apply=True)

    def proof_body(self, L, ch, trivial):
        """Proof steps for `L = T_k`, where ch = [(expr_i, T_i)] rewrites L
        to T_1, ..., T_k."""
        r = self.r
        k = len(ch)
        lines = []
        if trivial:
            self.planned_steps += 1
            self.synth_steps += 1
            return r.choice([['  apply refl'], ['  apply refl'], ['  rewrite LHS', '    = RHS by refl'],
                             ['  rewrite RHS', '    = LHS by rule(refl)'],
                             ['  apply refl()'],                 # does not pop the goal
                             ['  rewrite LHS', '    = RHS']])    # no `by`: always invalid
        style = r.random()
        if style < 0.45:
            # forward from the LHS; end with `= T_k`, `= RHS` or `apply`
            n_fwd = k - 1 if r.random() < 0.3 else k
            side = 'RHS' if n_fwd == k and r.random() < 0.3 else None
            fwd, _ = self.step_lines(ch[:n_fwd], False, last_side=side)
            if fwd:
                lines.append('  rewrite LHS')
                lines += ['  ' + l for l in fwd]
            if n_fwd < k:
                lines.append(self.apply_line(ch[k - 1][0]))
        elif style < 0.75:
            # forward j steps, then backward from the RHS with converse rules
            j = r.randint(0, k - 1)
            fwd, _ = self.step_lines(ch[:j], False)
            if fwd:
                lines.append('  rewrite LHS')
                lines += ['  ' + l for l in fwd]
            back = []
            for i in range(k - 1, j - 1, -1):
                target = ch[i - 1][1] if i >= 1 else L
                expr = converse(ch[i][0]) if ch[i][0] != 'refl' else 'refl'
                back.append((expr, target))
            side = 'LHS' if r.random() < 0.5 else None
            bl, _ = self.step_lines(back, False, last_side=side)
            lines.append('  rewrite RHS')
            lines += ['  ' + l for l in bl]
        else:
            # one `rewrite LHS` per step, maybe on one line; maybe end with apply
            for i, (expr, t) in enumerate(ch):
                if i == k - 1 and r.random() < 0.4:
                    lines.append(self.apply_line(expr))
                    continue
                sl, _ = self.step_lines([(expr, t)], False)
                if r.random() < 0.5:
                    lines.append('  rewrite LHS ' + sl[0].strip())
                else:
                    lines += ['  rewrite LHS', '  ' + sl[0]]
        return lines

    def st_noise(self):
        """Odd but legal (or deliberately bad) statements."""
        r = self.r
        x = r.random()
        if x < 0.15 and self.gen_types:   # generator redefinition
            name = r.choice(list(self.gen_types))
            n, m = self.gen_types[name]
            if r.random() < 0.5:
                n, m = r.randint(0, 3), r.randint(0, 3)
            self.emit(['gen %s : %d -> %d' % (name, n, m)])
        elif x < 0.25:
            self.emit(['gen %s : %d -> %d' % (r.choice(['id', 'sw', 'id0', 'LHS', 'RHS']), 1, 1)])
        elif x < 0.35:
            self.emit(['# ' + r.choice(['a comment', 'rule r : f = g', 'qed', ''])])
        elif x < 0.45:
            t = self.rand_term(2)
            self.emit(['rewrite %s : %s = %s by %s' % (self.fresh_rule_name(), t.text, r.choice(['LHS', 'RHS']), 'refl')])
        elif x < 0.55:
            t = self.rand_term(2)
            self.emit(['let %s = %s' % (r.choice(['LHS', 'RHS', 'proof', 'qed']), t.text)])
        elif x < 0.65:
            name = self.fresh_rule_name()
            self.current = name
            t = self.seed_term()
            ch = self.chain(t, 2)
            if ch:   # a rewrite that cites itself
                self.emit(['rewrite %s : %s' % (name, t.text), '  = %s by %s' % (ch[0][1].text, name)])
                self.register_rule(name, t, ch[0][1])
            self.current = None
        elif x < 0.75:
            later = self.later_rule_name()
            t = self.seed_term()
            ch = self.chain(t, 1)
            if ch:  # use before define
                self.emit(['rewrite %s : %s' % (self.fresh_rule_name(), t.text),
                           '  = %s by %s' % (ch[0][1].text, later)])
        elif x < 0.85:
            # a multi-line term with an ill-typed composition in the middle
            a, b, c = self.rand_term(1), self.rand_term(1), self.rand_term(1)
            self.emit(['let %s = %s ;' % (r.choice(['bad', 'bad2']), a.text), '  %s ;' % b.text, '  %s' % c.text])
        elif x < 0.92:
            name = self.thm_pool.pop() if self.thm_pool else 'tq'
            t = self.seed_term()
            self.seq_names.add(name)
            self.theorem_names.append(name)
            self.emit(['theorem %s : %s = %s' % (name, t.text, t.text)])   # no proof
        else:
            # citing an earlier theorem as a rule (upstream raises KeyError)
            if self.theorem_names and r.random() < 0.3:
                t = self.seed_term()
                self.emit(['rewrite %s : %s' % (self.fresh_rule_name(), t.text),
                           '  = %s by %s' % (t.text, r.choice(self.theorem_names))])

    def generate(self):
        r = self.r
        n_gens = r.randint(3, 6)
        names = r.sample(GEN_NAMES, n_gens)
        if r.random() < 0.15:
            names[r.randrange(n_gens)] = r.choice(TRICKY_NAMES)
        for nm in names:
            n, m = r.choice([0, 1, 1, 1, 2, 2, 3]), r.choice([0, 1, 1, 1, 2, 2, 3])
            if r.random() < 0.5:
                n, m = r.choice([(1, 1), (2, 1), (1, 2), (0, 1), (1, 0), (2, 2)])
            if nm in self.gen_types:
                continue
            self.st_gen(nm, n, m)
        if r.random() < 0.25:
            self.st_gen(r.choice(['s0', 'sc', 'phi']), 0, 0)   # a scalar
        for _ in range(r.randint(2, 5)):
            self.st_rule()
        kinds = ['rewrite'] * 28 + ['theorem'] * 28 + ['rule'] * 10 + ['let'] * 6 + ['def'] * 7 + \
                ['show'] * 4 + ['gen'] * 3 + ['noise'] * 8
        for _ in range(r.randint(3, 9)):
            k = r.choice(kinds)
            getattr(self, 'st_' + k)()
        return '\n'.join('\n'.join(b) for b in self.blocks) + '\n'


# Syntax that upstream accepts but chyp-rs deliberately drops (README): a
# corrupted theory that contains any of these is not used.
# `id [` starts a typed identity even when the bracket is on a later line;
# `sw[n]` and `sw[Type...]` are typed swaps (a malformed index list is not).
DROPPED_RE = re.compile(r'\bimport\b|"|\?|<=|~>|\brd\b|\brewrite\s*-|\^'
                        r'|\bid\s*\[|\bsw\s*\[\s*(?:[A-Za-z_]|\d+\s*\])')
GEN_LINE_RE = re.compile(r'gen\s+[A-Za-z_][\w.]*\s*:\s*\d+\s*->\s*\d+\s*(#.*)?')
TOKEN_RE = re.compile(r'\s+|#[^\n]*|->|==|[A-Za-z_][\w.]*|\d+|.')
STRAY = [')', '(', ';', '*', '=', '->', ':', ',', '[', ']', '0', '-', 'by', 'qed', 'proof',
         'apply', 'rule', 'LHS', 'RHS', 'id', 'sw', 'f', 'gen', 'rewrite', '1', '(f']


def uses_dropped(text):
    if DROPPED_RE.search(text):
        return True
    for line in text.split('\n'):
        if line.startswith('gen') and not GEN_LINE_RE.fullmatch(line.strip()):
            return True
    return False


def corrupt(rng, text, up):
    """A token-level edit of one line (delete, duplicate, swap or insert a
    token), kept only if it introduces no dropped feature; None otherwise."""
    lines = text.split('\n')
    for _ in range(10):
        li = rng.randrange(len(lines))
        toks = TOKEN_RE.findall(lines[li])
        idx = [j for j, t in enumerate(toks) if t.strip() and not t.startswith('#')]
        if not idx:
            continue
        j = rng.choice(idx)
        op = rng.random()
        if op < 0.4:
            toks[j] = ''
        elif op < 0.55:
            toks[j] = toks[j] + ' ' + toks[j]
        elif op < 0.7 and len(idx) > 1:
            k = rng.choice(idx)
            toks[j], toks[k] = toks[k], toks[j]
        else:
            toks[j] = rng.choice(STRAY) + ' ' + toks[j] if rng.random() < 0.5 else toks[j] + ' ' + rng.choice(STRAY)
        cand = lines[:li] + [''.join(toks)] + lines[li + 1:]
        cand = '\n'.join(cand)
        if not uses_dropped(cand):
            return cand
    return None


def generate(seed, i, up, timeout, exclude=(), corrupt_rate=0.08):
    rng = random.Random('%s:%s' % (seed, i))
    g = TheoryGen(rng, up, exclude)
    with time_limit(timeout):
        text = g.generate()
    if rng.random() < corrupt_rate and 'corrupt' not in exclude:
        c = corrupt(rng, text, up)
        if c is not None:
            text = c
    x = rng.random()
    if x < 0.03:
        text = text.replace('\n', '\r\n')
    elif x < 0.06:
        text = text.replace('  ', '\t').replace(' : ', ' :\t')
    elif x < 0.08:
        text = text.rstrip('\n')   # no newline at the end
    return text, g.planned_steps, g.synth_steps


# ---------------------------------------------------------------------------
# Shrinking.

def blocks_of(text):
    """Split a theory into statements: a line starting in column 0 starts
    one, except `proof` and `qed`, which belong to their theorem."""
    blocks = []
    for line in text.replace('\r\n', '\n').split('\n'):
        if not line.strip():
            continue
        first = line.split()[0] if line.split() else ''
        if not blocks or (line[0] not in ' \t' and first not in ('proof', 'qed')):
            blocks.append([line])
        else:
            blocks[-1].append(line)
    return blocks


def join_blocks(blocks):
    return '\n'.join(l for b in blocks for l in b) + '\n'


def shrink(text, diverges, budget_s=60.0, max_evals=600):
    """Delete statements, then single lines, while `diverges(text)` holds."""
    t0 = time.time()
    evals = [0]

    def ok(cand):
        if time.time() - t0 > budget_s or evals[0] >= max_evals:
            return False
        evals[0] += 1
        return diverges(cand)

    blocks = blocks_of(text)
    changed = True
    while changed:
        changed = False
        i = len(blocks) - 1
        while i >= 0:
            cand = blocks[:i] + blocks[i + 1:]
            if cand and ok(join_blocks(cand)):
                blocks = cand
                changed = True
            i -= 1
        for bi in range(len(blocks) - 1, -1, -1):
            li = len(blocks[bi]) - 1
            while li >= 0 and bi < len(blocks):
                b = blocks[bi]
                if len(b) == 1:
                    break
                cand = blocks[:bi] + [b[:li] + b[li + 1:]] + blocks[bi + 1:]
                if ok(join_blocks(cand)):
                    blocks = cand
                    changed = True
                li -= 1
    return join_blocks(blocks), evals[0]


# ---------------------------------------------------------------------------
# Driver.

def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--chyp', required=True, help='upstream Chyp checkout (commit 3d28483)')
    ap.add_argument('--port', required=True, help='path to the chyp-rs binary')
    ap.add_argument('--cases', type=int, default=500)
    ap.add_argument('--seed', default='1')
    ap.add_argument('--keep', help='directory for shrunk divergences')
    ap.add_argument('--dump', help='also write every generated theory here')
    ap.add_argument('--batch', type=int, default=100)
    ap.add_argument('--timeout', type=float, default=20.0, help='seconds per upstream check')
    ap.add_argument('--case', type=int, help='only regenerate and show this case')
    ap.add_argument('--exclude', default='',
                    help='comma-separated generator features to leave out, to look past a known '
                         'divergence: tactic-comment (a # comment before a tactic argument), '
                         'corrupt (token-level syntax errors)')
    ap.add_argument('--corrupt', type=float, default=0.08,
                    help='share of theories given a token-level syntax error (default 0.08)')
    ap.add_argument('--shrink-per-kind', type=int, default=3,
                    help='shrink at most this many divergences of each kind (the rest are saved as found)')
    ap.add_argument('--quiet', action='store_true')
    args = ap.parse_args()
    args.exclude = tuple(x for x in args.exclude.split(',') if x)

    up = Upstream(args.chyp)
    port = os.path.abspath(args.port)
    tmp = tempfile.mkdtemp(prefix='chyp-fuzz-')
    t_start = time.time()

    if args.case is not None:
        text, _, _ = generate(args.seed, args.case, up, args.timeout, args.exclude, args.corrupt)
        path = os.path.join(tmp, 'case%d.chyp' % args.case)
        with open(path, 'w') as f:
            f.write(text)
        u = up.run(text, path, args.timeout)
        p = run_port(port, [path], 60)[0]
        print(text)
        print('upstream:', json.dumps(u))
        print('port:    ', json.dumps(p))
        print('diff:', compare(u, p) if not u.get('crash') else 'upstream crashed')
        shutil.rmtree(tmp, ignore_errors=True)
        return 0

    stats = collections.Counter()
    crash_types = collections.Counter()
    step_status = collections.Counter()
    divergences = []
    by_kind = collections.Counter()
    if args.keep:
        os.makedirs(args.keep, exist_ok=True)
    if args.dump:
        os.makedirs(args.dump, exist_ok=True)

    def check_one(text, path):
        """(upstream result, port result) for one theory."""
        with open(path, 'w') as f:
            f.write(text)
        return up.run(text, path, args.timeout), run_port(port, [path], 60)[0]

    for b0 in range(0, args.cases, args.batch):
        batch = []
        for i in range(b0, min(args.cases, b0 + args.batch)):
            try:
                text, planned, synth = generate(args.seed, i, up, args.timeout, args.exclude, args.corrupt)
            except Timeout:
                stats['generation timeouts'] += 1
                continue
            except Exception as e:  # a generator bug: report it, keep going
                stats['generation failures'] += 1
                print('generation failed for seed %s case %d: %r' % (args.seed, i, e), file=sys.stderr)
                continue
            stats['planned steps'] += planned
            stats['synthesised steps'] += synth
            path = os.path.join(tmp, 'c%05d.chyp' % i)
            with open(path, 'w') as f:
                f.write(text)
            if args.dump:
                with open(os.path.join(args.dump, 'case-%s-%05d.chyp' % (args.seed, i)), 'w') as f:
                    f.write(text)
            batch.append((i, text, path))
        stats['cases'] += len(batch)
        ups = [up.run(text, path, args.timeout) for (_, text, path) in batch]
        ports = run_port(port, [path for (_, _, path) in batch], 300)
        for (i, text, path), u, p in zip(batch, ups, ports):
            if u.get('crash'):
                stats['upstream crashed (skipped)'] += 1
                crash_types[u['crash'].split(':')[0]] += 1
                continue
            stats['compared'] += 1
            stats['parts compared'] += len(u['parts'])
            stats['errors compared'] += len(u['errors'])
            if not u['parts'] and u['errors'] and u['errors'][0][1].startswith('Parse error'):
                stats['parse-error cases'] += 1
            for kind, _, _, status in u['parts']:
                if kind in STEP_KINDS:
                    step_status[status] += 1
            d = compare(u, p)
            if not d:
                continue
            stats['divergences'] += 1
            cat, sig = d[0][0], d[0][2]
            by_kind[sig] += 1

            def diverges(cand, sig=sig, path=path + '.shrink.chyp'):
                cu, cp = check_one(cand, path)
                if cu.get('crash'):
                    return False
                cd = compare(cu, cp)
                return bool(cd) and cd[0][2] == sig

            if by_kind[sig] <= args.shrink_per_kind:
                small, evals = shrink(text, diverges)
            else:
                small, evals = text, 0
            su, sp = check_one(small, path + '.min.chyp')
            rec = {'seed': args.seed, 'case': i, 'category': cat, 'kind': sig, 'diff': compare(su, sp),
                   'upstream': su, 'port': sp, 'minimal': small, 'original': text,
                   'original_diff': d, 'shrink_evals': evals}
            divergences.append(rec)
            if args.keep:
                base = os.path.join(args.keep, 'div-%s-%05d' % (args.seed, i))
                with open(base + '.chyp', 'w') as f:
                    f.write(small)
                with open(base + '.json', 'w') as f:
                    json.dump(rec, f, indent=1)
            if not args.quiet and by_kind[sig] <= args.shrink_per_kind:
                print('DIVERGENCE seed %s case %d [%s]: %s' % (args.seed, i, sig, rec['diff'][:1]), flush=True)
                print('  minimal theory:\n    ' + small.rstrip('\n').replace('\n', '\n    '), flush=True)
        if not args.quiet:
            print('[seed %s] %d/%d cases, %d divergences, %.0fs' % (
                args.seed, min(args.cases, b0 + args.batch), args.cases, stats['divergences'],
                time.time() - t_start), flush=True)

    shutil.rmtree(tmp, ignore_errors=True)
    n_steps = sum(step_status.values())
    summary = {
        'seed': args.seed,
        'exclude': list(args.exclude),
        'corrupt_rate': args.corrupt,
        'cases': stats['cases'],
        'compared': stats['compared'],
        'upstream_crashed_skipped': stats['upstream crashed (skipped)'],
        'crash_types': dict(crash_types),
        'generation_timeouts': stats['generation timeouts'],
        'generation_failures': stats['generation failures'],
        'parse_error_cases': stats['parse-error cases'],
        'parts_compared': stats['parts compared'],
        'errors_compared': stats['errors compared'],
        'steps_compared': n_steps,
        'steps_by_upstream_status': dict(step_status),
        'valid_share': round(step_status['valid'] / n_steps, 3) if n_steps else None,
        'synthesised_share_of_planned': round(stats['synthesised steps'] / stats['planned steps'], 3)
        if stats['planned steps'] else None,
        'divergences': len(divergences),
        'divergences_by_kind': dict(by_kind),
        'divergent_cases': ['%d %s' % (r['case'], r['kind']) for r in divergences],
        'seconds': round(time.time() - t_start, 1),
    }
    print(json.dumps(summary, indent=1))
    return 1 if divergences else 0


if __name__ == '__main__':
    sys.exit(main())
