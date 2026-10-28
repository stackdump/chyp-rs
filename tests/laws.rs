// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs (not derived from a Chyp source file).

//! The search-composition laws (laws/*.chyp), from ontology-pflow-xyz
//! ROADMAP.md, Phase 6: orderers are a monoid under chaining, sound filters a
//! meet-semilattice under intersection, drivers are endomorphisms wrapped
//! around the core, and event links are synchronising spiders that fuse.
//!
//! tests/faithfulness.rs checks that chyp-rs agrees with upstream Chyp on
//! these files. This file states what they are meant to show: every named
//! law is proved (all its steps valid; for a theorem, its `qed` too), and
//! every deliberate non-theorem is rejected.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use chyp::parts::{PartKind, Status};

/// Statuses of the proof steps of each named rewrite / theorem.
fn proofs(file: &str) -> BTreeMap<String, Vec<Status>> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("laws").join(file);
    let state = chyp::check_source(&fs::read_to_string(&path).unwrap());
    assert!(state.parsed, "{} does not parse: {:?}", file, state.errors);
    let mut out: BTreeMap<String, Vec<Status>> = BTreeMap::new();
    let mut owner = String::new();
    for p in &state.parts {
        match p.kind {
            PartKind::Theorem => {
                owner = p.name.clone();
                out.entry(owner.clone()).or_default().push(p.status);
            }
            PartKind::Rewrite if !p.name.is_empty() => {
                owner = p.name.clone();
                out.entry(owner.clone()).or_default().push(p.status);
            }
            PartKind::Rewrite | PartKind::ApplyTactic | PartKind::ProofStart | PartKind::ProofQed => {
                out.entry(owner.clone()).or_default().push(p.status);
            }
            _ => {}
        }
    }
    out
}

fn assert_laws(file: &str, proved: &[&str], rejected: &[&str]) {
    let all = proofs(file);
    for name in proved {
        let st = all
            .get(*name)
            .unwrap_or_else(|| panic!("{}: no proof named {}", file, name));
        assert!(
            st.iter().all(|s| *s == Status::Valid),
            "{}: {} should be proved, got {:?}",
            file,
            name,
            st
        );
    }
    for name in rejected {
        let st = all
            .get(*name)
            .unwrap_or_else(|| panic!("{}: no proof named {}", file, name));
        assert!(
            st.contains(&Status::Invalid),
            "{}: {} should be rejected, got {:?}",
            file,
            name,
            st
        );
    }
    let mut named: Vec<&str> = proved.iter().chain(rejected).copied().collect();
    named.sort();
    let mut have: Vec<&str> = all.keys().map(String::as_str).collect();
    have.sort();
    assert_eq!(named, have, "{}: every proof is listed as proved or rejected", file);
}

#[test]
fn orderers_form_a_monoid_under_chaining() {
    assert_laws(
        "orderers.chyp",
        &["chain4_bracketing", "connect4_chain", "nil_middle", "nil_padding"],
        // Chaining is lexicographic, so not commutative.
        &["chain_not_comm", "chain_not_comm_concrete"],
    );
}

#[test]
fn filters_form_a_meet_semilattice() {
    assert_laws(
        "filters.chyp",
        &[
            "meet_unitR",
            "meet_comm_concrete",
            "legal_idem",
            "meet_idem3",
            "meet3_regroup",
        ],
        &["unitR_needs_comm", "meet_not_absorbing"],
    );
}

#[test]
fn drivers_wrap_the_core_and_do_not_commute() {
    assert_laws(
        "drivers.chyp",
        &[
            "solver_unfold",
            "plain_dropped",
            "budget_rewrap",
            "wrapped_chain_regroup",
            "wrapped_nil",
        ],
        &["drivers_dont_commute", "drivers_dont_commute_plain"],
    );
}

#[test]
fn sync_spiders_fuse() {
    assert_laws(
        "sync_spiders.chyp",
        &[
            "fuse_one_wire",
            "fuse_one_wire_mirror",
            "fuse_two_wires",
            "sync_legs_unordered",
            "fuse_three",
            "sync_loop_vanishes",
        ],
        &["no_fusion_through_box", "boxes_dont_fuse"],
    );
}

/// The laws proved by `rewrite` are registered as rules and can be cited
/// later, e.g. `connect4_chain` is proved `by chain4_bracketing`.
#[test]
fn proved_laws_are_reusable_rules() {
    let src = fs::read_to_string(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("laws/orderers.chyp")).unwrap();
    let state = chyp::check_source(&src);
    let r = &state.table.rules["chain4_bracketing"];
    assert_eq!((r.lhs.domain(), r.lhs.codomain()), (4, 1));
    let state = chyp::check_source(&format!(
        "{}\nrewrite chain4_back :\n  chain * id * id ; chain * id ; chain\n  = chain * chain ; chain by -chain4_bracketing\n",
        src
    ));
    let last = state.parts.last().unwrap();
    assert_eq!((last.name.as_str(), last.status), ("chain4_back", Status::Valid));
}
