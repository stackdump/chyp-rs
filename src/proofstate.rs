// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// files chyp/proofstate.py, chyp/tactic/__init__.py and
// chyp/tactic/ruletac.py. Copyright (C) 2022-2023 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026):
//   - translated to Rust;
//   - only the `rule` and `refl` tactics are ported. `simp` (and the local
//     context, goal assumptions, RHS rewriting, size bounds and the `repeat`
//     loop that only `simp` used) are not, so `simp` is an unknown tactic;
//   - RHS synthesis for the editor (`make_rhs` / `next_rhs`) and highlighting
//     are not ported;
//   - where upstream raises (a theorem used as a rule raises KeyError; DPO's
//     NotImplementedError), an error is recorded on the step instead.

//! Proof states (a stack of goals) and the tactics that act on them.

use std::collections::{BTreeMap, BTreeSet};

use crate::graph::Graph;
use crate::matcher::{find_iso, match_rule};
use crate::rewrite::dpo;
use crate::rule::Rule;

/// The rules a proof step may use: every named rule, and the sequence number
/// at which it was introduced. A step at sequence `n` may only use rules with
/// a smaller sequence number.
#[derive(Debug, Clone)]
pub struct RuleTable {
    pub rules: BTreeMap<String, Rule>,
    pub rule_sequence: BTreeMap<String, usize>,
}

impl Default for RuleTable {
    fn default() -> RuleTable {
        // Upstream seeds every theory with `refl`, the empty rule, at sequence 0.
        let refl = Rule::new(Graph::new(), Graph::new(), "refl").expect("empty rule");
        let mut rules = BTreeMap::new();
        rules.insert("refl".to_string(), refl);
        let mut rule_sequence = BTreeMap::new();
        rule_sequence.insert("refl".to_string(), 0);
        RuleTable { rules, rule_sequence }
    }
}

/// A single goal: an equation still to be proved.
#[derive(Debug, Clone, PartialEq)]
pub struct Goal {
    pub formula: Rule,
}

/// The goals left at some point of a proof, plus the errors raised there.
#[derive(Debug, Clone)]
pub struct ProofState {
    pub sequence: usize,
    pub goals: Vec<Goal>,
    /// Source line that errors are reported against (upstream's `line`; -1
    /// before any step, as upstream).
    pub line: i64,
    /// Errors raised by this proof state, in order, de-duplicated.
    pub errors: Vec<(i64, String)>,
    seen: BTreeSet<String>,
}

impl ProofState {
    pub fn new(sequence: usize, goals: Vec<Goal>) -> ProofState {
        ProofState { sequence, goals, line: -1, errors: Vec::new(), seen: BTreeSet::new() }
    }

    /// A fresh proof state with copies of the goals, for the step at `line`.
    pub fn snapshot(&self, line: i64) -> ProofState {
        let mut ps = ProofState::new(self.sequence, self.goals.clone());
        ps.line = line;
        ps
    }

    pub fn error(&mut self, message: String) {
        if self.seen.insert(message.clone()) {
            self.errors.push((self.line, message));
        }
    }

    pub fn num_goals(&self) -> usize {
        self.goals.len()
    }

    /// Look up a rule expression: a rule name, optionally preceded by '-' for
    /// its converse. Matches upstream's `(-)?\s*([a-zA-Z_][\.a-zA-Z0-9_]*)`,
    /// anchored at the start only.
    pub fn lookup_rule(&mut self, rule_expr: &str, table: &RuleTable) -> Option<Rule> {
        let Some((converse, rule_name)) = parse_rule_expr(rule_expr) else {
            self.error(format!("Bad rule expression: {}", rule_expr));
            return None;
        };

        let mut rule = None;
        if let Some(&seq) = table.rule_sequence.get(&rule_name) {
            if seq >= self.sequence {
                self.error(format!(
                    "Attempting to use rule {} before it is defined/proven ({} >= {}).",
                    rule_name, seq, self.sequence
                ));
                return None;
            }
            // Upstream records a theorem in `rule_sequence` but never in
            // `rules`, and raises KeyError here; chyp-rs falls through to
            // "not defined".
            rule = table.rules.get(&rule_name);
        }

        let Some(rule) = rule else {
            self.error(format!("Rule {} not defined.", rule_name));
            return None;
        };
        Some(if converse { rule.converse() } else { rule.clone() })
    }

    /// Copy of the top goal's LHS.
    pub fn lhs(&self) -> Option<Graph> {
        self.goals.first().map(|g| g.formula.lhs.clone())
    }

    /// Copy of the top goal's RHS.
    pub fn rhs(&self) -> Option<Graph> {
        self.goals.first().map(|g| g.formula.rhs.clone())
    }

    /// Replace the top goal's LHS with `new_lhs`, pushing the goal
    /// "old LHS = new LHS" on top of the stack.
    pub fn replace_lhs(&mut self, new_lhs: &Graph) {
        let old = self.lhs().unwrap_or_default();
        match Rule::new(old, new_lhs.clone(), "") {
            Ok(r) => {
                self.goals[0].formula.lhs = new_lhs.clone();
                let mut g = self.goals[0].clone();
                g.formula = r;
                self.goals.insert(0, g);
            }
            Err(e) => self.error(e.0),
        }
    }

    /// Replace the top goal's RHS with `new_rhs`, pushing the goal
    /// "old RHS = new RHS" on top of the stack.
    pub fn replace_rhs(&mut self, new_rhs: &Graph) {
        let old = self.rhs().unwrap_or_default();
        match Rule::new(old, new_rhs.clone(), "") {
            Ok(r) => {
                self.goals[0].formula.rhs = new_rhs.clone();
                let mut g = self.goals[0].clone();
                g.formula = r;
                self.goals.insert(0, g);
            }
            Err(e) => self.error(e.0),
        }
    }

    /// Whether goal `i`'s two sides are isomorphic.
    pub fn validate_goal(&self, i: usize) -> bool {
        match self.goals.get(i) {
            Some(g) => find_iso(&g.formula.lhs, &g.formula.rhs).is_some(),
            None => false,
        }
    }

    /// Pop goal `i` if its two sides are isomorphic.
    pub fn try_close_goal(&mut self, i: usize) -> bool {
        if self.validate_goal(i) {
            self.goals.remove(i);
            true
        } else {
            false
        }
    }
}

/// Split a rule expression into (converse?, name).
pub fn parse_rule_expr(expr: &str) -> Option<(bool, String)> {
    let mut rest = expr;
    let converse = rest.starts_with('-');
    if converse {
        rest = &rest[1..];
    }
    let rest = rest.trim_start();
    let mut chars = rest.char_indices();
    match chars.next() {
        Some((_, c)) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return None,
    }
    let end = chars
        .find(|&(_, c)| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
        .map(|(i, _)| i)
        .unwrap_or(rest.len());
    Some((converse, rest[..end].to_string()))
}

/// Run tactic `name` with `args` on `ps`. Returns the tactic's verdict
/// (`Tactic.run()` upstream).
pub fn run_tactic(ps: &mut ProofState, name: &str, args: &[String], table: &RuleTable) -> bool {
    match name {
        "rule" => rule_tactic(ps, args, table),
        "refl" => refl_tactic(ps),
        _ => {
            ps.error(format!("Unknown tactic: {}", name));
            refl_tactic(ps)
        }
    }
}

/// The base tactic: succeeds if the top goal holds up to isomorphism. It does
/// not pop the goal (as upstream).
fn refl_tactic(ps: &ProofState) -> bool {
    ps.validate_goal(0)
}

/// Rewrite the top goal's LHS with rule `args[0]` in every possible way,
/// stopping at the first result that closes the goal.
fn rule_tactic(ps: &mut ProofState, args: &[String], table: &RuleTable) -> bool {
    if args.is_empty() || ps.num_goals() == 0 {
        return false;
    }
    let Some(rule) = ps.lookup_rule(&args[0], table) else {
        return false;
    };
    let target = ps.goals[0].formula.lhs.clone();
    for m in match_rule(&rule, &target) {
        match dpo(&rule, &m) {
            Ok(h) => {
                ps.goals[0].formula.lhs = h;
                if ps.try_close_goal(0) {
                    return true;
                }
            }
            Err(e) => {
                ps.error(e);
                return false;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::parse_rule_expr;

    #[test]
    fn rule_expressions() {
        assert_eq!(parse_rule_expr("ff"), Some((false, "ff".into())));
        assert_eq!(parse_rule_expr("-gg"), Some((true, "gg".into())));
        assert_eq!(parse_rule_expr(" A.assoc "), Some((false, "A.assoc".into())));
        assert_eq!(parse_rule_expr("- x_1"), Some((true, "x_1".into())));
        assert_eq!(parse_rule_expr("  -x"), None);
        assert_eq!(parse_rule_expr("1x"), None);
    }
}
