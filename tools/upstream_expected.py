# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 the chyp-rs contributors. New in chyp-rs.
"""Produce the expected results for chyp-rs's faithfulness tests by running
upstream Chyp headless.

Upstream: https://github.com/akissinger/chyp at commit 3d28483. Only its core
modules are imported (parser, checker); the GUI and the cvxpy layout are not,
so the only third-party dependency is `lark`.

For each .chyp file this parses and checks the file exactly as the Chyp GUI
does (chyp.parser.parse, then chyp.checker.check) and writes one JSON file:

  {"file": ..., "crash": null | "<ExceptionType>: <message>",
   "parts":  [{"kind", "line", "name", "status"}, ...],
   "errors": [{"line", "msg"}, ...],
   "rules":  [<sorted rule names>]}

If upstream's checker raises (it does for a few ill-formed inputs), "crash"
records the exception and the parts keep the statuses they had reached.

Usage:
  python -I -B tools/upstream_expected.py <chyp checkout at 3d28483> <out dir> <file.chyp>...

The upstream checkout is only imported, never written to: the script turns
off bytecode writing itself (note that `python -I` ignores
PYTHONDONTWRITEBYTECODE).

See the Makefile target `expected`.
"""
import json
import os
import sys

# Never write __pycache__ into the upstream checkout, whatever the flags
# (`python -I` ignores PYTHONDONTWRITEBYTECODE).
sys.dont_write_bytecode = True

STATUS = {0: 'unchecked', 1: 'checking', 2: 'valid', 3: 'invalid'}


def run(path):
    from chyp import parser, checker

    path = os.path.abspath(path)
    with open(path) as f:
        code = f.read()
    state = parser.parse(code, path)
    crash = None
    try:
        checker.check(state)
    except Exception as e:  # upstream can raise from inside check()
        crash = f'{type(e).__name__}: {e}'
    return {
        'file': os.path.basename(path),
        'crash': crash,
        'parts': [{'kind': type(p).__name__, 'line': p.line, 'name': p.name,
                   'status': STATUS[p.status]} for p in state.parts],
        'errors': [{'line': ln, 'msg': msg} for (_, ln, msg) in state.errors],
        'rules': sorted(state.rules.keys()),
    }


def main():
    root, out_dir, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    sys.path.insert(0, root)
    os.makedirs(out_dir, exist_ok=True)
    for path in files:
        result = run(path)
        name = os.path.splitext(os.path.basename(path))[0] + '.json'
        with open(os.path.join(out_dir, name), 'w') as f:
            json.dump(result, f, indent=1)
            f.write('\n')
        n_valid = sum(p['status'] == 'valid' for p in result['parts'])
        n_invalid = sum(p['status'] == 'invalid' for p in result['parts'])
        print(f'{name}: {n_valid} valid, {n_invalid} invalid'
              + (f', crash: {result["crash"]}' if result['crash'] else ''))


if __name__ == '__main__':
    main()
