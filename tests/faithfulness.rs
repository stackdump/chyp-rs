// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs.

//! Faithfulness against upstream Chyp (commit 3d28483).
//!
//! Each fixture was parsed and checked by upstream Chyp, headless, with
//! tools/upstream_expected.py; the results are in tests/fixtures/expected/.
//! For every fixture chyp-rs must give the same parts (kind, line, name and
//! status, in order), the same errors (line and message, in order; for a
//! syntax error only the line, as the message comes from Lark) and the same
//! rule names.
//!
//! The fixtures in tests/fixtures/crash/ make upstream's checker raise an
//! exception; chyp-rs reports an error instead, which those tests check.

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn expected(stem: &str) -> Value {
    let p = root().join("tests/fixtures/expected").join(format!("{}.json", stem));
    serde_json::from_str(&fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {}", p.display(), e))).unwrap()
}

fn actual(path: &Path) -> chyp_rs::State {
    chyp_rs::check_source(&fs::read_to_string(path).unwrap())
}

fn parts_of(state: &chyp_rs::State) -> Vec<(String, i64, String, String)> {
    state
        .parts
        .iter()
        .map(|p| {
            (
                p.kind.class_name().to_string(),
                p.line as i64,
                p.name.clone(),
                p.status.as_str().to_string(),
            )
        })
        .collect()
}

fn expected_parts(exp: &Value) -> Vec<(String, i64, String, String)> {
    exp["parts"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["kind"].as_str().unwrap().to_string(),
                p["line"].as_i64().unwrap(),
                p["name"].as_str().unwrap().to_string(),
                p["status"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

fn expected_errors(exp: &Value) -> Vec<(i64, String)> {
    exp["errors"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| (e["line"].as_i64().unwrap(), e["msg"].as_str().unwrap().to_string()))
        .collect()
}

/// Compare one fixture with upstream's results, part by part.
fn assert_faithful(rel: &str) {
    let path = root().join(rel);
    let stem = path.file_stem().unwrap().to_str().unwrap().to_string();
    let exp = expected(&stem);
    assert!(exp["crash"].is_null(), "{}: upstream crashed; use a crash test", rel);
    let state = actual(&path);

    let (got, want) = (parts_of(&state), expected_parts(&exp));
    for (i, (g, w)) in got.iter().zip(want.iter()).enumerate() {
        assert_eq!(g, w, "{}: part {} differs from upstream", rel, i);
    }
    assert_eq!(got.len(), want.len(), "{}: number of parts", rel);

    let got_err: Vec<(i64, String)> = state.errors.iter().map(|e| (e.line, e.msg.clone())).collect();
    let want_err = expected_errors(&exp);
    if !state.parsed {
        // A syntax error: same single error line; the text is Lark's.
        assert_eq!(got_err.len(), 1, "{}: one parse error", rel);
        assert_eq!(want_err.len(), 1, "{}: one parse error upstream", rel);
        assert_eq!(got_err[0].0, want_err[0].0, "{}: parse error line", rel);
        assert!(want_err[0].1.starts_with("Parse error"));
        assert!(got_err[0].1.starts_with("Parse error"));
    } else {
        assert_eq!(got_err, want_err, "{}: errors differ from upstream", rel);
    }

    let mut rules: Vec<String> = state.table.rules.keys().cloned().collect();
    rules.sort();
    let want_rules: Vec<String> = exp["rules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r.as_str().unwrap().to_string())
        .collect();
    assert_eq!(rules, want_rules, "{}: rule names", rel);
}

/// One test per fixture, comparing chyp-rs with upstream Chyp's results.
macro_rules! faithful {
    ($($name:ident => $path:expr,)*) => {
        $(
            #[test]
            fn $name() {
                assert_faithful($path);
            }
        )*
        /// Every fixture with upstream results has a test above.
        #[test]
        fn every_fixture_is_tested() {
            let tested: Vec<&str> = vec![$($path),*];
            for dir in ["tests/fixtures/upstream", "tests/fixtures/derived", "tests/fixtures/original", "laws"] {
                for entry in fs::read_dir(root().join(dir)).unwrap() {
                    let path = entry.unwrap().path();
                    if path.extension().and_then(|e| e.to_str()) == Some("chyp") {
                        let rel = format!("{}/{}", dir, path.file_name().unwrap().to_str().unwrap());
                        assert!(tested.contains(&rel.as_str()), "{} has no faithfulness test", rel);
                    }
                }
            }
        }
    };
}

faithful! {
    // Upstream examples that use only the features chyp-rs keeps (verbatim).
    upstream_frobenius => "tests/fixtures/upstream/frobenius.chyp",
    upstream_hopf => "tests/fixtures/upstream/hopf.chyp",
    upstream_smc => "tests/fixtures/upstream/smc.chyp",
    upstream_module => "tests/fixtures/upstream/module.chyp",
    // Derived from upstream examples that use dropped features.
    derived_ssfa_inlined => "tests/fixtures/derived/ssfa_inlined.chyp",
    derived_proof_test_explicit => "tests/fixtures/derived/proof_test_explicit.chyp",
    // Original fixtures probing upstream's behaviour.
    original_edge_cases => "tests/fixtures/original/edge_cases.chyp",
    original_tactic_args => "tests/fixtures/original/tactic_args.chyp",
    original_glued_keywords => "tests/fixtures/original/glued_keywords.chyp",
    original_long_terms => "tests/fixtures/original/long_terms.chyp",
    original_line_endings_cr => "tests/fixtures/original/line_endings_cr.chyp",
    original_line_endings_crlf => "tests/fixtures/original/line_endings_crlf.chyp",
    original_line_endings_mixed => "tests/fixtures/original/line_endings_mixed.chyp",
    original_parse_error => "tests/fixtures/original/parse_error.chyp",
    original_parse_error_comment_paren => "tests/fixtures/original/parse_error_comment_paren.chyp",
    original_parse_error_lhs_in_rule => "tests/fixtures/original/parse_error_lhs_in_rule.chyp",
    original_parse_error_paren_in_arg => "tests/fixtures/original/parse_error_paren_in_arg.chyp",
    original_parse_error_unclosed_args => "tests/fixtures/original/parse_error_unclosed_args.chyp",
    original_parse_error_unclosed_empty => "tests/fixtures/original/parse_error_unclosed_empty.chyp",
    // The Phase 6 laws, checked by upstream too.
    laws_orderers => "laws/orderers.chyp",
    laws_filters => "laws/filters.chyp",
    laws_drivers => "laws/drivers.chyp",
    laws_sync_spiders => "laws/sync_spiders.chyp",
}

/// Fixtures where upstream's checker raises: every part upstream reached
/// before raising has the same status here; the part it raised on is
/// invalid here, with the given error; later parts are checked normally.
fn assert_crash_handled(rel: &str, crash_line: i64, error: &str) {
    let path = root().join(rel);
    let stem = path.file_stem().unwrap().to_str().unwrap().to_string();
    let exp = expected(&stem);
    assert!(exp["crash"].is_string(), "{}: upstream did not crash", rel);
    let state = actual(&path);
    let (got, want) = (parts_of(&state), expected_parts(&exp));
    assert_eq!(got.len(), want.len(), "{}: number of parts", rel);
    for (g, w) in got.iter().zip(want.iter()) {
        assert_eq!((&g.0, g.1, &g.2), (&w.0, w.1, &w.2), "{}: part identity", rel);
        if g.1 < crash_line {
            assert_eq!(g.3, w.3, "{}: part at line {} before the crash", rel, g.1);
        } else if g.1 == crash_line {
            assert_eq!(g.3, "invalid", "{}: the step upstream crashes on", rel);
        } else {
            assert_ne!(g.3, "unchecked", "{}: later steps are still checked", rel);
        }
    }
    assert!(
        state.errors.iter().any(|e| e.line == crash_line && e.msg == error),
        "{}: expected error {:?} at line {}, got {:?}",
        rel,
        error,
        crash_line,
        state.errors
    );
}

#[test]
fn crash_theorem_as_rule() {
    // Upstream: KeyError: 't1'.
    assert_crash_handled("tests/fixtures/crash/theorem_as_rule.chyp", 14, "Rule t1 not defined.");
}

#[test]
fn crash_illtyped_step() {
    // Upstream: RuleError: Inputs must match on LHS and RHS of rule (...).
    assert_crash_handled(
        "tests/fixtures/crash/illtyped_step.chyp",
        9,
        "Inputs must match on LHS and RHS of rule ([(None, 1), (None, 1)] != [(None, 1)])",
    );
}
