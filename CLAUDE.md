# chyp-rs

A Rust port of the core of Aleks Kissinger's Chyp (string-diagram rewriting
and proof checking), ported from upstream commit `3d28483`, Apache-2.0. Local
repo on workbit (the Mac); **no remote yet** — Matt decides where it goes.
README.md is the user-facing description: what is ported, what is dropped,
how faithfulness is tested.

## Layout

| Path | What |
|---|---|
| `src/graph.rs`, `matcher.rs`, `rewrite.rs`, `rule.rs` | Hypergraphs, convex matching, DPO rewriting (from `graph.py`, `matcher.py`, `rewrite.py`, `rule.py`) |
| `src/proofstate.rs`, `checker.rs`, `parts.rs` | Goals, the `rule`/`refl` tactics, the step-by-step checker |
| `src/parser.rs`, `state.rs` | Hand-written parser for the kept subset of the Lark grammar; AST -> graphs, rules, parts |
| `src/layout.rs`, `json.rs` | Deterministic layered layout (replaces the cvxpy one) and JSON output |
| `src/wasm.rs`, `src/bin/chyp-rs.rs` | wasm-bindgen API (`Session`, `check`) and the CLI |
| `laws/` | The search-composition laws (orderers, filters, drivers, sync spiders) as Chyp theories |
| `tests/fixtures/{upstream,derived,original,crash}` | Inputs (verbatim upstream examples, derived ones, original probes, inputs upstream raises on); `tests/fixtures/expected/` holds upstream Chyp's results for them |
| `tools/upstream_expected.py` | Runs upstream Chyp headless to produce `expected/` |
| `tools/fuzz_diff.py` | Differential fuzzer: random theories through upstream and chyp-rs |

## Rules

- **Faithfulness is the contract.** For inputs using only kept features,
  every part's status, every error (line and text) and the rule names must
  equal upstream's. Upstream quirks are reproduced on purpose (a step with no
  `by` is always invalid; theorems are not usable as rules); only places
  where upstream *raises* are changed, and they are listed in the README.
- Ported files carry a "Ported from Chyp" header naming the upstream file and
  listing the changes (Apache-2.0 §4(b)). Keep it accurate when editing.
- Never modify `~/Workspace/chyp` (the upstream checkout). To regenerate
  expectations: `make expected PYTHON=<python with lark>`; it runs with
  `PYTHONDONTWRITEBYTECODE=1` so the checkout stays clean.
- `wasm-bindgen` in Cargo.toml is pinned to the installed CLI's version
  (`wasm-bindgen --version`); bump both together.

## Commands

```bash
make test        # unit + faithfulness + law + robustness tests
make wasm        # pkg/chyp.js + pkg/chyp_bg.wasm, prints sizes
make wasm-test   # every fixture through the wasm bundle, step by step (node)
./target/release/chyp-rs check laws/*.chyp
```
