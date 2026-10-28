// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs.

//! chyp-rs must not panic or overflow its stack on any input: natively that
//! kills the CLI, and in wasm (built with panic=abort) it kills the instance.
//! Upstream Chyp raises RecursionError on terms nested or chained more than
//! about 490 deep; chyp-rs handles long chains in linear time and limits
//! parenthesis nesting.

use std::time::Instant;

use chyp_rs::parser::{MAX_NESTING, MAX_WIRES};
use chyp_rs::parts::Status;

fn theory(src: &str) -> chyp_rs::State {
    let state = chyp_rs::check_source(src);
    // Laying out every diagram must not panic either.
    let _ = chyp_rs::json::theory(&state, true);
    state
}

#[test]
fn long_chains_are_linear() {
    for op in [";", "*"] {
        let n = 100_000;
        let src = format!(
            "gen f : 1 -> 1\nrule ff : f ; f = f\nlet x = {}\nrewrite r : f ; f ; f = f ; f by ff\n",
            vec!["f"; n].join(&format!(" {} ", op))
        );
        let t = Instant::now();
        let state = theory(&src);
        assert!(state.errors.is_empty(), "{:?}", state.errors);
        assert_eq!(state.graphs["x"].num_edges(), n);
        assert_eq!(state.parts.last().unwrap().status, Status::Valid);
        assert!(
            t.elapsed().as_secs() < 20,
            "{} chain of {} took {:?}",
            op,
            n,
            t.elapsed()
        );
    }
}

#[test]
fn composition_errors_in_long_chains() {
    let mut items = vec!["f"; 5000];
    items[2500] = "m";
    let src = format!("gen f : 1 -> 1\ngen m : 2 -> 1\nlet x =\n  {}\n", items.join(" ;\n  "));
    let state = theory(&src);
    // As upstream: only the rightmost failing composition is reported, on the
    // line of its left operand (`f ; m ; ...` fails at the `f` before `m`).
    assert_eq!(state.errors.len(), 1, "{:?}", state.errors);
    assert_eq!(state.errors[0].line, 4 + 2499);
    assert!(!state.graphs.contains_key("x"));
}

#[test]
fn nesting_limit() {
    let nest = |n: usize| format!("gen f : 1 -> 1\nlet x = {}f{}\n", "(".repeat(n), ")".repeat(n));
    let ok = theory(&nest(MAX_NESTING));
    assert!(ok.parsed && ok.errors.is_empty());
    // Every level a different operator, the deepest recursion per level.
    let mixed: String = (0..MAX_NESTING)
        .map(|i| if i % 2 == 0 { "(f ; " } else { "(f * f * " })
        .collect();
    let src = format!(
        "gen f : 1 -> 1\nlet x = id * id ; {}f{}\n",
        mixed,
        ")".repeat(MAX_NESTING)
    );
    let st = theory(&src);
    assert!(st.parsed, "{:?}", st.errors);
    let deep = theory(&nest(MAX_NESTING + 1));
    assert!(!deep.parsed);
    assert_eq!(deep.errors[0].line, 2);
    // Far beyond the limit, and unbalanced.
    assert!(!theory(&"(".repeat(1_000_000)).parsed);
}

#[test]
fn arity_and_number_limits() {
    let ok = theory(&format!("gen f : {} -> 1\nlet x = f\n", MAX_WIRES));
    assert!(ok.parsed && ok.errors.is_empty());
    for src in [
        format!("gen f : {} -> 1", MAX_WIRES + 1),
        "gen f : 18446744073709551615 -> 1".to_string(),
        "gen f : 1 -> 99999999999999999999999".to_string(),
    ] {
        let st = theory(&src);
        assert!(!st.parsed, "{}", src);
    }
    // Out-of-range or repeated swap indices are an error on the term.
    for src in [
        "let x = sw[4294967296, 0]",
        "let x = sw[18446744073709551615, 0]",
        "let x = sw[0, 0]",
    ] {
        let st = theory(src);
        assert!(st.parsed && st.errors.len() == 1, "{}: {:?}", src, st.errors);
    }
}

/// A small deterministic generator (no dependencies).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[(self.next() as usize) % xs.len()]
    }
}

#[test]
fn random_inputs_do_not_panic() {
    let tokens = [
        "gen", "f", "g", "m", ":", "1", "2", "0", "->", "rule", "r", "=", "==", ";", "*", "(", ")", "id", "id0", "sw",
        "[", "]", ",", "rewrite", "by", "-", "LHS", "RHS", "theorem", "proof", "qed", "apply", "let", "def", "show",
        "\n", " ", "#", "rule(", "simp(", "refl", "\r", "\t", "x_1", "1,0", "é", "\0",
    ];
    let mut rng = Lcg(0x5eed);
    for _ in 0..3000 {
        let n = 1 + rng.next() as usize % 60;
        let src: String = (0..n).map(|_| rng.pick(&tokens)).collect::<Vec<_>>().join(" ");
        theory(&src);
    }
    // And mutations of a well-formed theory.
    let base = include_str!("../laws/sync_spiders.chyp");
    let words: Vec<&str> = base.split_whitespace().collect();
    for _ in 0..500 {
        let mut w = words.clone();
        for _ in 0..3 {
            if w.is_empty() {
                break;
            }
            let i = rng.next() as usize % w.len();
            match rng.next() % 3 {
                0 => {
                    w.remove(i);
                }
                1 => w.insert(i, rng.pick(&tokens)),
                _ => {
                    let j = rng.next() as usize % w.len();
                    w.swap(i, j)
                }
            }
        }
        theory(&w.join(" "));
    }
}

/// The CLI stops quietly (exit 0, no panic) when its stdout is closed early,
/// as when piped into `head`.
#[test]
fn cli_exits_quietly_on_a_closed_pipe() {
    use std::process::{Command, Stdio};
    let hopf = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/upstream/hopf.chyp");
    let mut child = Command::new(env!("CARGO_BIN_EXE_chyp-rs"))
        .args(["json", hopf])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // Close the read end at once; the output (megabytes) cannot fit in the pipe.
    drop(child.stdout.take());
    let out = child.wait_with_output().unwrap();
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "stderr: {}", stderr);
    assert!(!stderr.contains("panicked"), "stderr: {}", stderr);
}
