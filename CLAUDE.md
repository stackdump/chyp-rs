# chyp-rs

A Rust port of the core of Aleks Kissinger's Chyp (string-diagram rewriting
and proof checking), ported from upstream commit `3d28483`, Apache-2.0. Public
repo: <https://github.com/stackdump/chyp-rs> (`origin`). It builds as a native
CLI, a wasm-bindgen browser bundle (`wasm32-unknown-unknown`) and a WASI build
of the CLI (`wasm32-wasip1`, for hosts such as wazero; meant for sim.pflow.xyz
to re-check theories server-side).
README.md is the user-facing description: what is ported, what is dropped,
how faithfulness is tested.

## Layout

| Path | What |
|---|---|
| `src/graph.rs`, `matcher.rs`, `rewrite.rs`, `rule.rs` | Hypergraphs, convex matching, DPO rewriting (from `graph.py`, `matcher.py`, `rewrite.py`, `rule.py`) |
| `src/proofstate.rs`, `checker.rs`, `parts.rs` | Goals, the `rule`/`refl` tactics, the step-by-step checker |
| `src/parser.rs`, `state.rs` | Hand-written parser for the kept subset of the Lark grammar; AST -> graphs, rules, parts |
| `src/layout.rs`, `json.rs` | Deterministic layered layout (replaces the cvxpy one) and JSON output |
| `src/wasm.rs`, `src/bin/chyp-rs.rs` | wasm-bindgen API (`Session`, `check`; `wasm32-unknown-unknown` only) and the CLI (native and WASI; FILE `-` is stdin) |
| `laws/` | The search-composition laws (orderers, filters, drivers, sync spiders) as Chyp theories |
| `tests/fixtures/{upstream,derived,original,crash}` | Inputs (verbatim upstream examples, derived ones, original probes, inputs upstream raises on); `tests/fixtures/expected/` holds upstream Chyp's results for them |
| `tests/wasm_smoke.mjs`, `tests/wasi_smoke.mjs`, `tests/stdin.rs` | Browser bundle vs upstream/native; WASI CLI on stdin vs native, byte for byte; `-` vs path natively |
| `tools/upstream_expected.py` | Runs upstream Chyp headless to produce `expected/` |
| `tools/fuzz_diff.py` | Differential fuzzer: random theories through upstream and chyp-rs |

## Rules

- **Faithfulness is the contract.** For inputs using only kept features,
  every part's status, every error (line and text) and the rule names must
  equal upstream's. Upstream quirks are reproduced on purpose (a step with no
  `by` is always invalid; theorems are not usable as rules); only places
  where upstream *raises* are changed, and they are listed in the README.
- Ported files carry a "Derived from Chyp" header naming the upstream file(s),
  reproducing their notice and listing the changes (Apache-2.0 §4(b)). Keep it accurate when editing.
- Never modify `~/Workspace/chyp` (the upstream checkout). To regenerate
  expectations: `make expected PYTHON=<python with lark>`; it runs with
  `python -I -B`, and the scripts set `sys.dont_write_bytecode` themselves, so
  the checkout gets no `__pycache__` (`python -I` ignores
  PYTHONDONTWRITEBYTECODE; check with `git status --porcelain --ignored`).
- `wasm-bindgen` in Cargo.toml is pinned to the installed CLI's version
  (`wasm-bindgen --version`); bump both together.
- The wasm-bindgen API and dependency are gated on
  `all(target_arch = "wasm32", target_os = "unknown")`, not on `wasm32`
  alone: the WASI module must import only `wasi_snapshot_preview1`
  functions (`make wasi-test` fails otherwise). Keep both gates in step.
- The CLI's output for `-` with `CHYP_RS_STDIN_NAME=PATH` must stay byte for
  byte its output for PATH (stdout, stderr, exit status); `tests/stdin.rs`
  and `make wasi-test` check it. A CLI change that prints the FILE name must
  print `label(path)`.
- `make wasi` is reproducible (same sha256 from a clean target dir and from
  another path); it remaps `$CARGO_HOME` to `/cargo`, so build the module
  with `make wasi`, not a bare `cargo build`, when its hash matters. A
  toolchain or `Cargo.lock` change changes the hash; update README's WASI
  section (size, sha256, rustc) when it does.

## Commands

```bash
make test        # unit + faithfulness + law + robustness + stdin tests
make wasm        # pkg/chyp_rs.js + pkg/chyp_rs_bg.wasm, prints sizes
make wasm-test   # every fixture through the wasm bundle, step by step (node)
make wasi        # target/wasm32-wasip1/wasm/chyp-rs.wasm; prints size and sha256
make wasi-test   # fixtures (not crash/) + laws through the WASI CLI under node:wasi, theory on
                 # stdin, byte-identical to native summary/check/json; also checks the imports
./target/release/chyp-rs check laws/*.chyp
./target/release/chyp-rs summary - < laws/drivers.chyp   # FILE `-` reads stdin
```

`make wasm`/`make wasm-test` need the `wasm-bindgen` CLI; without it,
`cargo build --lib --target wasm32-unknown-unknown --profile wasm` at least
checks that the browser build compiles.
