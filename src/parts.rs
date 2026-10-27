// Ported from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/parts.py. Copyright (C) 2022 Aleks Kissinger.
// Licensed under the Apache License, Version 2.0.
//
// Changes from the original (chyp-rs contributors, 2026): the class
// hierarchy is flattened into one `Part` struct with a `PartKind`; ImportPart
// is not ported (imports are not supported), nor are the editor-only fields
// (`layed_out`, `stub`, `term_pos` is kept for the JSON output).

//! The checkable pieces of a theory file.

use crate::graph::Graph;
use crate::proofstate::ProofState;
use crate::rule::Rule;

/// What kind of statement (or sub-statement) a part is. The names match the
/// upstream classes, which the JSON output and the faithfulness tests use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartKind {
    Gen,
    Let,
    Rule,
    Theorem,
    ProofStart,
    ProofQed,
    ApplyTactic,
    Rewrite,
}

impl PartKind {
    pub fn class_name(self) -> &'static str {
        match self {
            PartKind::Gen => "GenPart",
            PartKind::Let => "LetPart",
            PartKind::Rule => "RulePart",
            PartKind::Theorem => "TheoremPart",
            PartKind::ProofStart => "ProofStartPart",
            PartKind::ProofQed => "ProofQedPart",
            PartKind::ApplyTactic => "ApplyTacticPart",
            PartKind::Rewrite => "RewritePart",
        }
    }

    /// Proof steps carry a proof state after checking.
    pub fn is_proof_step(self) -> bool {
        matches!(self, PartKind::ProofStart | PartKind::ProofQed | PartKind::ApplyTactic | PartKind::Rewrite)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Unchecked,
    Checking,
    Valid,
    Invalid,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Status::Unchecked => "unchecked",
            Status::Checking => "checking",
            Status::Valid => "valid",
            Status::Invalid => "invalid",
        }
    }
}

/// Which side of the current goal a `rewrite LHS|RHS` step refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Lhs,
    Rhs,
}

impl Side {
    pub fn as_str(self) -> &'static str {
        match self {
            Side::Lhs => "LHS",
            Side::Rhs => "RHS",
        }
    }
}

/// One statement or proof step of a theory, with its checking status.
#[derive(Debug, Clone)]
pub struct Part {
    pub kind: PartKind,
    /// Character offsets of the part in the source, and its 1-based line.
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub name: String,
    pub status: Status,
    pub index: usize,
    /// GenPart / LetPart: the graph (None if the term failed to build).
    pub graph: Option<Graph>,
    /// RulePart / TheoremPart / proof steps: the two sides shown for the part.
    pub lhs: Option<Graph>,
    pub rhs: Option<Graph>,
    /// RulePart: the rule. TheoremPart: the statement.
    pub rule: Option<Rule>,
    /// TheoremPart and proof steps: the sequence number rules are checked against.
    pub sequence: usize,
    /// ApplyTacticPart / RewritePart.
    pub tactic: String,
    pub tactic_args: Vec<String>,
    /// RewritePart inside a proof: `rewrite LHS|RHS`, and an RHS given as
    /// `LHS`/`RHS` instead of a term.
    pub lhs_side: Option<Side>,
    pub rhs_side: Option<Side>,
    /// RewritePart: character offsets of the step's term.
    pub term_pos: (usize, usize),
    /// Proof steps, after checking: the proof state after the step.
    pub proof_state: Option<ProofState>,
}

impl Part {
    pub fn new(kind: PartKind, start: usize, end: usize, line: usize, name: &str) -> Part {
        Part {
            kind,
            start,
            end,
            line,
            name: name.to_string(),
            status: Status::Unchecked,
            index: 0,
            graph: None,
            lhs: None,
            rhs: None,
            rule: None,
            sequence: 0,
            tactic: String::new(),
            tactic_args: Vec::new(),
            lhs_side: None,
            rhs_side: None,
            term_pos: (0, 0),
            proof_state: None,
        }
    }
}
