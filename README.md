# chyp-rs

An unofficial Rust port of part of **[Chyp](https://github.com/akissinger/chyp)**, the
interactive theorem prover for string diagrams by Aleks Kissinger. It was ported from
upstream commit [`3d28483`](https://github.com/akissinger/chyp/commit/3d28483) ("fixed some
bugs in the docs") and is licensed, like Chyp, under the Apache License 2.0. chyp-rs builds
as a native CLI and for `wasm32-unknown-unknown`, with a wasm-bindgen API. It has no GUI.

It is not affiliated with or endorsed by Aleks Kissinger or the Chyp project; the name Chyp
is used only to say where the code came from (the crate and wasm module are `chyp_rs`).

The port is deliberately narrow. It keeps what is needed to state and check the laws in
[`laws/`](laws) (from `ontology-pflow-xyz/ROADMAP.md`, Phase 6):

- parsing theory files;
- the hypergraph representation;
- matching and double-pushout (DPO) rewriting;
- step-by-step checking of explicit rewrite proofs;
- a layout.

Everything else is dropped and [listed below](#what-is-dropped). A few pieces of syntax the
laws do not use (`let`, `show`, `==`, `lemma`/`proposition`, `apply`, `rule(R)`, steps with no
`by` or `by refl`, `id0`, `sw[i, j, ...]`) are kept so that upstream's `frobenius`, `hopf` and
`smc` examples can be tested verbatim.

**Faithfulness** is the contract. For every input that uses only the kept features, chyp-rs
must give the same result as upstream Chyp, run headless: each statement's and proof step's
status, every error (line and text; for a syntax error, the line), and the set of rules. That covers every proof Chyp
accepts or rejects. It is checked on 23 fixtures, by a differential fuzzer (28,040 random
theories and 175,172 proof steps compared since the last fix, with no divergence), and by
three adversarial reviews.
See [Testing](#testing).

## Contents

- [Quick start](#quick-start)
- [What is ported](#what-is-ported)
- [What is dropped](#what-is-dropped)
- [What differs from upstream](#what-differs-from-upstream)
- [Upstream behaviour kept on purpose](#upstream-behaviour-kept-on-purpose)
- [The laws](#the-laws)
- [Testing](#testing)
- [wasm](#wasm)
- [CLI](#cli)
- [JSON](#json)
- [Known limitations](#known-limitations)
- [License and attribution](#license-and-attribution)

## Quick start

```bash
make test                                   # unit, faithfulness, law and robustness tests
make build                                  # target/release/chyp-rs
./target/release/chyp-rs check laws/*.chyp  # one line per step, theorem, proof and qed
make wasm                                   # pkg/: chyp_rs.js + chyp_rs_bg.wasm (+ licence files)
make wasm-test                              # the fixtures (not crash/) through the wasm bundle (node)
```

A theory, as Chyp writes it:

```
gen join : 2 -> 1
gen fork : 1 -> 2
rule spec : fork ; join = id

rewrite fuse_two_wires :
  join ; fork ; join ; fork
  = join ; fork by spec
```

## What is ported

Each ported file starts with a header naming the Chyp file(s) it was translated from. The
header reproduces their copyright notice and lists what was changed (Apache-2.0 §4(b)).

| chyp-rs | Ported from (Chyp `3d28483`) | Notes |
|---|---|---|
| `src/graph.rs` | `chyp/graph.py` | Hypergraphs with boundaries: tensor, compose, `perm`, `identity`, `gen`, vertex merging and exploding |
| `src/matcher.rs` | `chyp/matcher.py` | Convex matching and `find_iso`, with upstream's depth-first search order |
| `src/rewrite.rs` | `chyp/rewrite.py` | DPO rewriting (`dpo`) |
| `src/rule.rs` | `chyp/rule.py` | Rules, converse |
| `src/proofstate.rs` | `chyp/proofstate.py`, `chyp/tactic/__init__.py`, `chyp/tactic/ruletac.py`, `chyp/state.py` (initial rule table) | Goals, rule lookup with sequence numbers, the `rule` and `refl` tactics |
| `src/checker.rs` | `chyp/checker.py` | The checker, as a `Checker` that checks one part per `step()` |
| `src/parts.rs` | `chyp/parts.py` | The checkable parts of a theory |
| `src/parser.rs` | `chyp/parser.py` | A hand-written parser for the kept subset of the Lark grammar |
| `src/state.rs` | `chyp/state.py`, `chyp/parser.py` (`parse()`) | Building graphs, rules and parts from the parse (upstream's Lark Transformer) |
| `src/layout.rs` | `chyp/term.py` (`layer_decomp`), `chyp/layout.py` (initial coordinates, port offsets, spacing constraints), `chyp/graph.py` (`box_size`) | Layered layout; the cvxpy step is replaced, see [below](#what-differs-from-upstream) |
| `src/json.rs`, `src/wasm.rs`, `src/lib.rs`, `src/bin/chyp-rs.rs` | new | JSON output, wasm API, CLI |
| `tests/`, `tools/`, `laws/` | new (but see [License](#license-and-attribution) for `laws/sync_spiders.chyp`) | |

The theory language that remains:

- `gen NAME : m -> n` (untyped wire counts);
- `let`;
- `def` (adds the rule `NAME_def`);
- `rule NAME : T = T` (`=` or `==`);
- `show NAME`;
- `rewrite NAME : T = T by R = T by -R ...`;
- `theorem` / `lemma` / `proposition NAME : T = T`, with `proof ... qed` blocks of
  `rewrite LHS|RHS = ...` steps (whose holes may be `LHS`/`RHS`) and `apply` steps;
- terms built from `;`, `*`, parentheses, `id`, `id0`, `sw`, `sw[i, j, ...]` and names;
- `#` comments.

Tactics: `rule` (as `by R`, `by -R`, `by rule(R)`, `apply R`, `apply rule(R)`) and `refl`.

## What is dropped

The port keeps only what the laws need (plus the syntax listed above for the verbatim
examples). Dropped, with how chyp-rs treats it:

| Dropped | In chyp-rs |
|---|---|
| The GUI: the Qt app, editor, syntax highlighting, completion, error list, graph view (`chyp/gui/`) | not ported |
| Editor support in the core: RHS synthesis for `?` holes (`next_rhs`, `make_rhs`), revision tracking, `part_at`, `copy_state_until`, highlighting | not ported |
| `import` (with `as`, renaming lets and namespaces) and the parse cache | syntax error |
| Colours on `gen` and `def` (`gen f : 1 -> 1 "ffdddd"`, `def g = f ; f "ddffdd"`, and the two-colour form) | syntax error |
| Typed and sized wires: `A`, `u`, `u^2`, `None`, `id[T]`, `sw[T]` (including `sw[2]` as a count). Wire types would let `drivers.chyp` tell order chains from searches; see [The laws](#the-laws) | syntax error |
| Redistributers `rd[...]` | syntax error |
| One-way rules (`<=`, `~>`) and converse rewrites (`rewrite -name`), which upstream reports as errors ("Non-invertible rules currently not supported") and does not register | syntax error |
| `?` holes in rewrite steps | syntax error |
| The `simp` tactic, the local rule context, RHS rewriting, size bounds, `repeat` | `simp` is an unknown tactic: an error, then it behaves like `refl` (as upstream treats unknown tactics) |
| Goal assumptions (nothing populates them at `3d28483`) | not ported |
| Term printing (`graph_to_term`, `rule_to_term`) and graph JSON loading (`load_graph`, `graph_from_json`) | not ported |
| The cvxpy layout (`convex_layout`) | replaced by a deterministic layout without a solver |
| Drawing data on graphs (coordinates, `value`, `hyper`, highlight flags) | not ported; layout is computed separately |

Of upstream's 12 examples, these use only kept features and are tested verbatim: `frobenius`,
`hopf`, `smc` and `module`. `ssfa` (`import`) and `proof_test` (colours, `simp`) are tested as
derived fixtures with those features removed. Not tested: `interacting_s_hopf` (imports with
namespaces, colours), `qt_modules` (imports with namespaces, `simp`), `quasi_tri` (`simp`, and
an `import`), and `typed_module`, `typed_rewriting` and `sized_rewriting` (typed and sized
wires).

## What differs from upstream

- **Layout.** Upstream lays diagrams out with `layer_decomp` and then a cvxpy convex program
  for the y-coordinates. chyp-rs keeps the layer decomposition and the initial coordinates,
  and replaces the solver with a deterministic heuristic: alternating barycentric sweeps
  between neighbouring columns, each followed by an isotonic projection that enforces
  upstream's ordering and spacing constraints, until no coordinate moves by more than 1e-9
  (or after 200 sweeps). So coordinates differ from upstream's (they are not part of the
  faithfulness contract).
  - In the second crossing-reduction pass, a box with no inputs or no outputs is sorted
    using the side it has; upstream counts the missing side's position as 0 (the top of the
    layer), which pulls such boxes upward.
  - The layout is identical on every target: the wasm and native JSON are equal on every
    fixture.
- **Where upstream raises.** Upstream's checker raises an uncaught exception, so the whole
  check stops, when:
  - a theorem's name is used as a rule (`KeyError`: theorems are recorded in `rule_sequence`
    but never in `rules`);
  - a top-level rewrite step's two sides have different arities (`RuleError`);
  - a proof has no theorem (when the theorem's own sides do not type-check);
  - DPO meets a rule whose left-hand side lists one boundary vertex more than once among its
    inputs or among its outputs (`NotImplementedError`: "Rewriting modulo Frobenius not yet
    supported."; terms cannot build such a rule).

  chyp-rs records an error on that step, marks it invalid and keeps checking. Upstream also
  raises `IndexError` while parsing an `sw[...]` index out of range; chyp-rs records an error
  on that line instead, and a step using the term is invalid while a `let` or `rule` using it
  is left out (only the error remains).
- **Permutations.** `sw[...]` must be a permutation of `0..n-1`. Upstream accepts repeated
  indices and builds a graph that is not a valid string diagram.
- **Limits.** Upstream raises `RecursionError` on parentheses nested deeper than 492 levels or
  on `;` / `*` chains longer than about 490 terms. chyp-rs accepts nesting up to 500 levels
  (a syntax error beyond that) and chains of any length, parsed and built in linear time. Its
  parser and term evaluation do not recurse, so input cannot overflow the stack, natively or
  in wasm. (Checking a rewrite step is not linear; see [Known limitations](#known-limitations).)
  Generator arities are capped at 65,536 wires.
- **Messages and flags.** Syntax error *messages* are chyp-rs's own ("Parse error: unexpected
  X, expected Y"); the *line* is upstream's. Upstream prints Lark's context excerpt. `parsed`
  is false after a syntax error, where upstream sets it to true. Errors carry a line but no
  file name.
- **Line endings** are normalised as Python's universal newlines do when upstream reads a
  file: `\r\n` and a lone `\r` become `\n`.

## Upstream behaviour kept on purpose

These are upstream behaviours at `3d28483`, some of them arguably bugs, that chyp-rs
reproduces because faithfulness is the point. They matter when writing proofs:

- **A rewrite step with no `by` is always invalid**, even when both sides are isomorphic. It
  uses the `refl` tactic, which finds the isomorphism but does not pop the goal, and the
  checker only accepts a step that closes one. So all 20 steps of upstream's `smc.chyp` are
  rejected. Write `by refl` instead: `refl` is also a built-in empty rule, and rewriting with
  it then testing for isomorphism works.
- **Theorems are not rules.** A `theorem` (or `lemma`, `proposition`) cannot be cited later;
  upstream raises `KeyError`, and chyp-rs reports "Rule NAME not defined.". To reuse a
  result, prove it with a top-level `rewrite`, which registers a rule.
- **Rules are registered from `rewrite` statements whether or not their steps check**, and a
  rule may only be used after its statement (by sequence number).
- **A theorem with no proof stays "checking"**, and proof steps after the goal is closed are
  invalid while the `qed` is valid.
- **Keywords are contextual**, as with Lark's contextual lexer. A name may be spelled like a
  keyword (`gen rule : 1 -> 1`, `apply rule(...)`). Where no name can occur, a keyword is
  split off the front of a longer word, so `genf : 1 -> 1` declares `f`. `LHS`/`RHS` right
  after `=` in a rule or theorem is a syntax error.
- **Tactic arguments are raw text** up to `,`, `(` or `)`. Only whitespace is skipped before
  each one, so `by rule(# note` + newline + `ff)` passes the argument `# note\n ff`, which is
  not a rule name.

## The laws

[`laws/`](laws) states laws from `ontology-pflow-xyz/ROADMAP.md`, Phase 6, as Chyp theories:
three from search composition (orderers, filters, drivers) and, from model composition, the
`lk:event` sync spiders. Each file proves its laws and also contains steps that must be
rejected. Upstream Chyp gives the same verdicts on every step (`tests/faithfulness.rs`), and
`tests/laws.rs` states what each file is meant to show.

A rejected step shows only that the cited rule does not turn its left side into its right
side, or, with `by refl`, that the two sides are different diagrams. Each rule-based
rejection except `unitR_needs_comm` (whose point is that the rule does not apply) has a
matching accepted step in the same file, the same rule with the true right side, so the rule
does apply. Chyp cannot show that an equation does *not* follow from the rules.

| File | Law | Proved | Rejected |
|---|---|---|---|
| `orderers.chyp` | Orderers are a monoid under chaining: `chain : 2 -> 1`, empty chain `nil`. (In pflow-rs the monoid is partial: at most 8 pieces, no repeats; this is the total monoid around it.) | `chain4_bracketing` (all five bracketings of four orderers), `connect4_chain` (plan:connect4-exact's chain), `nil_middle`, theorem `nil_padding`, `nil_keeps_order` | `chain_not_comm`, `chain_not_comm_concrete` (`by refl`: the two orders are different diagrams; chaining is lexicographic); `nil_does_not_unswap` (cancelling `nil` leaves the swapped chain) |
| `filters.chyp` | Sound filters as a meet-semilattice under intersection: `meet`, unit `all`, copy `dup`. These rules model plain intersection; with the ROADMAP's empty-result fallback, meet is not associative. | `meet_unitR` (from left unit + commutativity), `meet_comm_concrete`, theorem `legal_idem`, `meet_idem3`, `meet3_regroup`, `meet_drops_unit` | `unitR_needs_comm` (a true law, proved as `meet_unitR`, but not by `meet_unitL` alone); `meet_not_absorbing` (removing `all` leaves the filter, not `all`) |
| `drivers.chyp` | Drivers are endomorphisms wrapped around the core: `solver = core ; null_window ; budget` | `solver_unfold`, `plain_dropped` (a hypothetical identity driver), theorem `budget_rewrap`, `wrapped_chain_regroup`, `wrapped_nil` | `solver_is_not_swapped` (unfolding gives null-window inside budget, not the reverse); `driver_orders_differ` (`by refl`: different diagrams; no rule equates the two orders) |
| `sync_spiders.chyp` | Event links are synchronising spiders (a special commutative Frobenius algebra) and fuse | `fuse_one_wire`, `fuse_one_wire_mirror`, `fuse_two_wires`, `sync_legs_unordered`, theorem `fuse_three`, `sync_loop_vanishes`, `fuse_up_to_box` | `no_fusion_through_box` (fusing leaves `dequeue` between the sync points); `boxes_dont_fuse` (`by refl`) |

Caveats:
- The ROADMAP says driver order matters "in general"; pflow-rs's `plan.rs` currently applies
  `null_window` and `budget` in a fixed order whatever the plan lists. `plain` is not a
  pflow-rs driver.
- Wires are untyped in chyp-rs, so in `drivers.chyp` "order chain" and "search" are a reading
  convention only: the theory also accepts ill-typed composites such as `solver ; solver`.
  Upstream's typed wires (dropped here) would rule those out.

## Testing

```bash
make test        # 14 unit + 26 faithfulness + 5 law + 6 robustness tests + 1 doctest
make wasm-test   # the fixtures (not crash/) through the wasm bundle, step by step
```

### Faithfulness fixtures

`tools/upstream_expected.py` runs upstream Chyp headless: `chyp.parser.parse` then
`chyp.checker.check`, which needs only `lark`, with no GUI or cvxpy. It writes each
fixture's parts, statuses, errors and rules to `tests/fixtures/expected/`. `make expected`
regenerates them from a checkout of Chyp at `3d28483`.

`tests/faithfulness.rs` requires chyp-rs to give identical parts (kind, line, name, status,
in order), identical errors (line and message, in order; for a syntax error, the line) and
identical rule names. `tests/wasm_smoke.mjs` checks every part's kind, line, name and status
the same way through the wasm `Session`, one step at a time, and requires the one-shot
`check()` JSON (errors, rules and layout included) to equal the native `chyp-rs json` output.

Results (one test per fixture; two rows group 3 and 6 fixtures; every one agrees with
upstream):

| Fixture | Source | Parts | Steps | Valid | Invalid | Theorems valid | Errors |
|---|---|---:|---:|---:|---:|---:|---:|
| `upstream/frobenius.chyp` | upstream, verbatim | 78 | 58 | 51 | 7 | – | 0 |
| `upstream/hopf.chyp` | upstream, verbatim | 148 | 118 | 118 | 0 | – | 0 |
| `upstream/smc.chyp` | upstream, verbatim | 28 | 20 | 0 | 20 | – | 0 |
| `upstream/module.chyp` | upstream, verbatim | 5 | 0 | 0 | 0 | – | 0 |
| `derived/ssfa_inlined.chyp` | `frobenius` + `ssfa`, import removed | 110 | 87 | 79 | 8 | – | 0 |
| `derived/proof_test_explicit.chyp` | `proof_test`, `simp` and colours removed | 24 | 11 | 11 | 0 | 3/3 | 0 |
| `original/edge_cases.chyp` | error paths and checker quirks | 63 | 24 | 13 | 11 | 5/7 | 14 |
| `original/tactic_args.chyp` | raw tactic arguments, comments, control characters | 29 | 16 | 10 | 6 | 1/3 | 5 |
| `original/glued_keywords.chyp` | contextual keywords (`genf`, `proofapply`, `qedtheorem`, ...) | 23 | 5 | 5 | 0 | 3/3 | 1 |
| `original/long_terms.chyp` | 400-term chains, 300-deep nesting, type errors mid-chain | 11 | 3 | 3 | 0 | – | 2 |
| `original/line_endings_{cr,crlf,mixed}.chyp` | line endings | 18 | 4 | 2 | 2 | – | 9 |
| `original/parse_error*.chyp` (6 files) | syntax errors; same error line | 0 | 0 | 0 | 0 | – | 6 |
| `laws/orderers.chyp` | the laws | 23 | 11 | 8 | 3 | 1/1 | 0 |
| `laws/filters.chyp` | the laws | 25 | 12 | 10 | 2 | 1/1 | 0 |
| `laws/drivers.chyp` | the laws | 26 | 12 | 10 | 2 | 1/1 | 0 |
| `laws/sync_spiders.chyp` | the laws | 38 | 18 | 16 | 2 | 1/1 | 0 |
| **Total** | 23 fixtures | **649** | **399** | **336** | **63** | **16/20** | **37** |

"Steps" are rewrite and `apply` steps. "Valid" and "Invalid" are upstream's verdicts, which
chyp-rs reproduces exactly. Two more fixtures, `crash/theorem_as_rule.chyp` and
`crash/illtyped_step.chyp`, make upstream raise. For those the tests check that chyp-rs
agrees on every part before that point, marks the offending step invalid with the right
error, and keeps checking.

### Differential fuzzing

`tools/fuzz_diff.py` generates random theories from the kept features and checks each with
upstream (in process) and chyp-rs, comparing parts, errors and rules exactly. Theories cover:
- random signatures and well-typed terms;
- `let`/`def`/`rule`;
- multi-step rewrites;
- theorem/proof blocks with `rewrite LHS|RHS` and `apply`;
- deliberate errors, and token-level syntax corruption in a share of theories (`--corrupt P`,
  default 0.08).

About two thirds of the steps are made valid by synthesising right-hand sides with
upstream's own engine (`RuleTac.make_rhs` + `graph_to_term`, as upstream's GUI fills `?`
holes). Cases where upstream raises are skipped and counted.

| Campaign | Theories compared | Steps compared (valid / invalid) | Divergences |
|---|---:|---:|---|
| 1: initial port | 19,309 | 124,429 (82,004 / 42,425) | 800, from two causes: a `#` before a tactic argument, and the line of a syntax error inside tactic arguments. Both fixed. |
| 2: after the fixes (seeds 101–105) | 11,594 | 71,538 (46,727 / 24,811) | **0** |
| 3: iterative parser (seeds 201–205) | 11,614 | 71,789 (46,914 / 24,875) | **0** |
| 4: final code, indexed matcher (seeds 301–302) | 4,832 | 31,845 (20,959 / 10,886) | **0** |

Campaign 4 ran on the final code. Reproduce one seed with
`python -I -B tools/fuzz_diff.py --chyp ../chyp --port target/release/chyp-rs --cases 2500 --seed 201`
(repeat for the other seeds). It needs a Python with `lark`; `--corrupt 0.5` raises the share
of syntax noise from the default 0.08.

### Reviews

Three independent line-by-line reviews compared each Chyp module with its port. Every
suspected difference was run through both implementations, and only observed differences
counted.

| Area | Inputs run through both | Result |
|---|---:|---|
| Parser and state builder | about 3,600 | Six divergences, all in lexing: tactic-argument comments, error lines in tactic arguments, glued keywords, `LHS`/`RHS` after `=`, lone `\r`, U+001C–U+001F in rule names. All fixed, with fixtures. |
| Graphs, matching, DPO | about 19,800 match, iso and DPO traces over 380 files (vertex and edge maps compared in order), plus 569 whole-file comparisons | None. Each vertex touches exactly one edge or boundary slot on each side, and ids increase, so Rust's ordered collections iterate as Python's dicts and sets do. |
| Proof states, tactics, checker | about 2,100 | None beyond the tactic-argument cases above |

A robustness review fuzzed about 200,000 inputs, including random bytes and token soup. It
found stack overflows, huge-arity panics and a closed-pipe panic in the CLI; all are fixed
and covered by `tests/robustness.rs`. It also found quadratic costs in building and laying out
diagrams (now linear), states floating to the top of a layout layer, and bounds that ignored
box sizes, all fixed.

## wasm

```bash
make wasm   # cargo build --lib --target wasm32-unknown-unknown --profile wasm, then wasm-bindgen --target web
```

| File | Bytes | gzip -9 |
|---|---:|---:|
| `pkg/chyp_rs_bg.wasm` | 273,888 | 86,868 |
| `pkg/chyp_rs.js` (wasm-bindgen glue) | 15,089 | 3,098 |

These are built with `opt-level = "z"`, LTO and `panic = "abort"`, without `wasm-opt`. `hopf.chyp`
(148 parts, every diagram laid out) checks in about 60 ms in Node; a 50,000-term chain in about
0.2 s. `wasm-bindgen` in `Cargo.toml` is pinned to the installed CLI's version (`0.2.129`).

```js
import init, { Session, check } from "./pkg/chyp_rs.js";
await init();

const s = new Session(source);        // load (parse) a theory; nothing checked yet
JSON.parse(s.outline());              // parts, errors, rules, status counts
let part;
while ((part = JSON.parse(s.step())) !== null) {
  // one part, just checked: status, diagrams with layout, and the goals left after it
}
JSON.parse(s.part(3));                // any part again, with diagrams
JSON.parse(s.rule("frob"));           // a rule's two sides as diagrams
s.reset();                            // check again from the top
s.load(otherSource);                  // replace the theory

JSON.parse(check(source));            // one shot: everything checked, every diagram laid out
```

`Session` also has `check_all()`, `errors()`, `position()`, `done()` and `len()`.
`outline()`, `step()`, `part()`, `rule()`, `load()`, `check_all()` and `errors()` return JSON
strings; `position()` and `len()` return numbers, `done()` a boolean, and `reset()` nothing.
The module also exports `upstream_commit()`.

## CLI

```
chyp-rs check FILE...       check each file; one line per rewrite/apply step, theorem, proof and qed
chyp-rs step FILE           check FILE one part at a time, showing the goals left
chyp-rs summary FILE...     print upstream-comparable JSON (the shape of tools/upstream_expected.py)
chyp-rs json FILE [PART]    print the checked theory as JSON with laid-out diagrams
```

The exit status is 0 if every file parsed and no part is invalid, 1 otherwise, and 2 on a
usage error or when a file cannot be read (or PART does not exist). The totals count every
checked part, theorems and `proof`/`qed` included.

```
$ chyp-rs check laws/drivers.chyp
laws/drivers.chyp
   47  valid     rewrite solver_unfold by solver_def
   52  valid     rewrite plain_dropped by plain_id
   53  valid     rewrite plain_dropped by plain_id
   54  valid     rewrite plain_dropped by -solver_def
   57  valid     theorem budget_rewrap
   59  valid     proof
   61  valid     rewrite step by solver_def
   62  valid     rewrite step by budget_idem
   63  valid     rewrite step by -solver_def
   64  valid     qed
   70  valid     rewrite wrapped_chain_regroup by chain_assoc
   71  valid     rewrite wrapped_chain_regroup by -chain_assoc
   75  valid     rewrite wrapped_nil by chain_unitR
   85  invalid   rewrite solver_is_not_swapped by solver_def
   89  invalid   rewrite driver_orders_differ by refl
  13 valid, 2 invalid
```

## JSON

A diagram (see `src/json.rs`). Here is `join : 2 -> 1` on its own, from `chyp-rs json`:

```json
{ "inputs": [0, 1], "outputs": [2],
  "vertices": [{"id": 0, "input": [0], "output": [], "x": -1.5, "y": -0.5},
               {"id": 1, "input": [1], "output": [], "x": -1.5, "y": 0.5},
               {"id": 2, "input": [], "output": [0], "x": 1.5, "y": 0.0}],
  "edges": [{"id": 0, "label": "join", "wire": false, "x": 0.0, "y": 0.0, "size": 2,
             "sources": [0, 1], "targets": [2], "in_ports": [-0.5, 0.5], "out_ports": [0.0]}],
  "layers": [[0]],
  "bounds": {"x_min": -1.5, "x_max": 1.5, "y_min": -1.0, "y_max": 1.0} }
```

- Box columns are 3 units apart; the input and output vertices sit 1.5 units outside the
  first and last box column.
- A box spans `x ± 0.5` and `y ± size/2`; its ports sit at the listed y-coordinates.
- Edges with `"wire": true` are identity edges inserted by the layout, and are drawn as plain
  wire.
- `bounds` covers every box.
- A part carries `index`, `kind` (upstream's class name), `line`, `name`, `status`, character
  offsets, its tactic, its diagrams, and for proof steps the goals left after it.

## Known limitations

- Matching is upstream's backtracking search, which can take exponential time on rules whose
  left-hand side has many interchangeable pieces, for example several identical states. In
  the browser that blocks the page. The robustness review found 9 such inputs among about
  200,000, all artificial.
- Checking a rewrite step is not linear in the size of the diagram: like upstream, each
  extension of a partial match walks every vertex mapped so far, so matching and the
  isomorphism test grow roughly quadratically. On an n-term chain one step takes about 0.1 s at
  n = 2,000 and 3 s at n = 8,000; upstream cannot parse chains beyond about 490 terms.
- Wires are untyped (see [The laws](#the-laws)).
- No `simp`: every rewrite step names its rule.
- No imports: a theory is one file (concatenate files as `derived/ssfa_inlined.chyp` does).

## License and attribution

chyp-rs is licensed under the Apache License, Version 2.0 ([`LICENSE`](LICENSE)). It is a
Derivative Work of Chyp, Copyright (C) 2022-2023 Aleks Kissinger, also Apache-2.0. See
[`NOTICE`](NOTICE) for attribution.

- **Source.** Each ported file in `src/` names the Chyp file(s) it comes from and their
  authors (Aleks Kissinger; Alexander Koziell-Pipe wrote much of `graph.py` and `matcher.py`),
  reproduces their notices and lists its changes; see [What is ported](#what-is-ported). `json.rs`,
  `wasm.rs`, `lib.rs`, `bin/chyp-rs.rs`, `tests/` and `tools/` are new.
- **Fixtures.**
  - `tests/fixtures/upstream/` holds verbatim copies of Chyp's
    `examples/{frobenius,hopf,module,smc}.chyp` at `3d28483`.
  - `tests/fixtures/derived/proof_test_explicit.chyp` comes from `examples/proof_test.chyp`,
    and `derived/ssfa_inlined.chyp` from `examples/frobenius.chyp` and `examples/ssfa.chyp`.
    Each lists its changes.
  - `tests/fixtures/original/` and `tests/fixtures/crash/` are original.
  - `tests/fixtures/expected/` is upstream Chyp's output.
- **Laws.** `laws/sync_spiders.chyp` adapts the Frobenius-algebra rules and the `frobL` /
  `frobR` proofs of Chyp's `examples/frobenius.chyp`, as its header says. The other law files
  are original.
- **Theory.** The theory Chyp implements is from the "String Diagram Rewrite Theory" papers
  I-III by Bonchi, Gadducci, Kissinger, Sobociński and Zanasi (arXiv:2012.01847,
  arXiv:2104.14686, arXiv:2109.06049).
- **Distribution.** The CLI binary and the wasm bundle statically link the Rust standard
  library and third-party crates; see [`THIRD-PARTY-NOTICES`](THIRD-PARTY-NOTICES). zmij is
  MIT; memchr is Unlicense OR MIT, used under the Unlicense; the other crates and the standard
  library are MIT OR Apache-2.0, used under Apache-2.0; the standard library's Unicode tables
  are under Unicode-3.0. Anyone distributing
  either must include `LICENSE`, `NOTICE` and `THIRD-PARTY-NOTICES`; `make wasm` copies all
  three into `pkg/`.
