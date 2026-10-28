// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs (not derived from a Chyp source file).

//! The wasm32 API (wasm-bindgen). Every result is a JSON string; see json.rs
//! for the shapes.
//!
//! ```js
//! import init, { Session } from "./pkg/chyp.js";
//! await init();
//! const s = new Session(source);       // load (parse) a theory
//! JSON.parse(s.outline());             // parts, errors, rules
//! let step;
//! while ((step = JSON.parse(s.step())) !== null) {
//!   // one checked part, with its diagrams, layout and the goals after it
//! }
//! ```

use wasm_bindgen::prelude::*;

use crate::checker::Checker;
use crate::json;
use crate::state::State;

/// A loaded theory being checked step by step.
#[wasm_bindgen]
pub struct Session {
    source: String,
    state: State,
    checker: Checker,
}

#[wasm_bindgen]
impl Session {
    /// Load (parse) a theory. Nothing is checked yet.
    #[wasm_bindgen(constructor)]
    pub fn new(source: &str) -> Session {
        Session {
            source: source.to_string(),
            state: State::parse(source),
            checker: Checker::new(),
        }
    }

    /// Replace the theory with `source` and start checking from the top.
    /// Returns the outline.
    pub fn load(&mut self, source: &str) -> String {
        let fresh = Session::new(source);
        *self = fresh;
        self.outline()
    }

    /// Start checking again from the first part.
    pub fn reset(&mut self) {
        self.state = State::parse(&self.source);
        self.checker = Checker::new();
    }

    /// Parts (without diagrams), errors, rules and status counts so far.
    pub fn outline(&self) -> String {
        json::theory(&self.state, false).to_string()
    }

    /// Check the next part and return it with its diagrams, layout and the
    /// proof state after it; "null" once every part has been checked.
    pub fn step(&mut self) -> String {
        match self.checker.step(&mut self.state) {
            Some(i) => json::part(&self.state.parts[i], true).to_string(),
            None => "null".to_string(),
        }
    }

    /// Check every remaining part. Returns the outline.
    pub fn check_all(&mut self) -> String {
        while self.checker.step(&mut self.state).is_some() {}
        self.outline()
    }

    /// Part `index` with its diagrams and layout ("null" if out of range).
    pub fn part(&self, index: usize) -> String {
        match self.state.parts.get(index) {
            Some(p) => json::part(p, true).to_string(),
            None => "null".to_string(),
        }
    }

    /// A named rule's two sides as diagrams ("null" if there is none).
    pub fn rule(&self, name: &str) -> String {
        match self.state.table.rules.get(name) {
            Some(r) => json::rule(r).to_string(),
            None => "null".to_string(),
        }
    }

    /// Errors so far, as a JSON list of {line, msg}.
    pub fn errors(&self) -> String {
        serde_json::to_string(
            &self
                .state
                .errors
                .iter()
                .map(|e| serde_json::json!({"line": e.line, "msg": e.msg}))
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    /// Index of the next part `step` will check.
    pub fn position(&self) -> usize {
        self.checker.position()
    }

    pub fn done(&self) -> bool {
        self.checker.done(&self.state)
    }

    pub fn len(&self) -> usize {
        self.state.parts.len()
    }
}

/// Parse and check a whole theory in one call; returns the theory JSON with
/// every diagram laid out.
#[wasm_bindgen]
pub fn check(source: &str) -> String {
    json::theory(&crate::check_source(source), true).to_string()
}

/// The upstream Chyp commit this port follows.
#[wasm_bindgen]
pub fn upstream_commit() -> String {
    crate::UPSTREAM_COMMIT.to_string()
}
