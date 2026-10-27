// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/rule.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026): translated to Rust.
// Upstream's `equiv` flag is always True (one-way rules are unsupported), so
// it is not ported.

//! Rewrite rules: a pair of graphs with the same boundary.

use std::fmt;

use crate::graph::{type_repr, Graph};

/// The two sides of a rule have different boundaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleError(pub String);

impl fmt::Display for RuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Rule {
    pub lhs: Graph,
    pub rhs: Graph,
    pub name: String,
}

impl Rule {
    /// A rule `lhs = rhs`. Upstream treats a missing side (`None`) as the
    /// empty graph; callers pass `Graph::new()` for that.
    pub fn new(lhs: Graph, rhs: Graph, name: &str) -> Result<Rule, RuleError> {
        if lhs.domain() != rhs.domain() {
            return Err(RuleError(format!(
                "Inputs must match on LHS and RHS of rule ({} != {})",
                type_repr(rhs.domain()),
                type_repr(lhs.domain())
            )));
        }
        if lhs.codomain() != rhs.codomain() {
            return Err(RuleError(format!(
                "Outputs must match on LHS and RHS of rule ({} != {})",
                type_repr(rhs.codomain()),
                type_repr(lhs.codomain())
            )));
        }
        Ok(Rule { lhs, rhs, name: name.to_string() })
    }

    /// The rule read right to left; its name gains (or loses) a leading '-'.
    pub fn converse(&self) -> Rule {
        let name = match self.name.strip_prefix('-') {
            Some(n) => n.to_string(),
            None => format!("-{}", self.name),
        };
        Rule { lhs: self.rhs.clone(), rhs: self.lhs.clone(), name }
    }

    /// True if no vertex occurs twice on the LHS boundary.
    pub fn is_left_linear(&self) -> bool {
        let mut seen = std::collections::BTreeSet::new();
        self.lhs.inputs().iter().chain(self.lhs.outputs()).all(|v| seen.insert(*v))
    }
}
