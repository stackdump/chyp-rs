// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs (not derived from a Chyp source file).

//! chyp-rs: a Rust port of the core of Chyp, Aleks Kissinger's interactive
//! theorem prover for string diagrams (<https://github.com/akissinger/chyp>,
//! commit 3d28483, Apache-2.0).
//!
//! A theory file declares generators (`gen`), terms (`let`, `def`), rules
//! (`rule`) and proofs (`rewrite`, `theorem ... proof ... qed`). Terms become
//! hypergraphs with boundaries ([`graph::Graph`]); a proof step is checked by
//! finding convex matches of a rule's left-hand side ([`matcher`]), rewriting
//! by double pushout ([`rewrite::dpo`]) and testing the result for
//! isomorphism with the claimed right-hand side.
//!
//! ```
//! let src = "gen f : 1 -> 1\nrule ff : f ; f = f\nrewrite r : f ; f ; f = f ; f by ff";
//! let state = chyp::check_source(src);
//! assert!(state.parts.iter().all(|p| p.status != chyp::parts::Status::Invalid));
//! ```
//!
//! See README.md for what is and is not ported.

pub mod checker;
pub mod graph;
pub mod json;
pub mod layout;
pub mod matcher;
pub mod parser;
pub mod parts;
pub mod proofstate;
pub mod rewrite;
pub mod rule;
pub mod state;

#[cfg(target_arch = "wasm32")]
pub mod wasm;

pub use state::State;

/// The upstream commit this crate was ported from.
pub const UPSTREAM_COMMIT: &str = "3d28483";

/// Parse and fully check a theory.
pub fn check_source(src: &str) -> State {
    let mut state = State::parse(src);
    checker::check(&mut state);
    state
}
