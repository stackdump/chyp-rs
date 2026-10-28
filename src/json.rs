// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 the chyp-rs contributors. New in chyp-rs (not derived from a Chyp source file).

//! JSON output: diagrams with their layout, parts, proof states, and whole
//! theories. (New in chyp-rs; upstream's GUI drew diagrams with Qt instead.)
//!
//! A diagram is
//! ```json
//! { "inputs": [v...], "outputs": [v...],
//!   "vertices": [{"id", "x", "y", "input": [i...], "output": [i...]}],
//!   "edges": [{"id", "label", "wire", "x", "y", "size", "sources": [v...],
//!              "targets": [v...], "in_ports": [y...], "out_ports": [y...]}],
//!   "layers": [[e...]],
//!   "bounds": {"x_min", "x_max", "y_min", "y_max"} }
//! ```
//! Edges with `"wire": true` are identity edges the layout inserted; draw
//! them as plain wire, not as boxes. Coordinates are in layout units (boxes
//! are 3 apart horizontally) and are rounded to 4 decimal places.

use serde_json::{json, Map, Value};

use crate::graph::Graph;
use crate::layout::{box_size, layout};
use crate::parts::{Part, PartKind};
use crate::proofstate::ProofState;
use crate::rule::Rule;
use crate::state::State;

fn r4(x: f64) -> Value {
    let v = (x * 10000.0).round() / 10000.0;
    // Avoid "-0.0".
    json!(if v == 0.0 { 0.0 } else { v })
}

/// A graph with its layout.
pub fn diagram(g: &Graph) -> Value {
    let l = layout(g);
    let lg = &l.graph;
    let vertices: Vec<Value> = lg
        .vertices()
        .map(|v| {
            let (x, y) = l.vpos[&v];
            let vd = lg.vertex_data(v);
            json!({
                "id": v,
                "x": r4(x),
                "y": r4(y),
                "input": vd.in_indices.iter().collect::<Vec<_>>(),
                "output": vd.out_indices.iter().collect::<Vec<_>>(),
            })
        })
        .collect();
    let edges: Vec<Value> = lg
        .edges()
        .map(|e| {
            let ed = lg.edge_data(e);
            let (x, y) = l.epos.get(&e).copied().unwrap_or((0.0, 0.0));
            json!({
                "id": e,
                "label": ed.value,
                "wire": l.inserted.contains(&e),
                "x": r4(x),
                "y": r4(y),
                "size": box_size(lg, e),
                "sources": ed.s,
                "targets": ed.t,
                "in_ports": l.in_ports(e).into_iter().map(r4).collect::<Vec<_>>(),
                "out_ports": l.out_ports(e).into_iter().map(r4).collect::<Vec<_>>(),
            })
        })
        .collect();
    let (x0, x1, y0, y1) = l.bounds();
    json!({
        "inputs": lg.inputs(),
        "outputs": lg.outputs(),
        "vertices": vertices,
        "edges": edges,
        "layers": l.layers,
        "bounds": {"x_min": r4(x0), "x_max": r4(x1), "y_min": r4(y0), "y_max": r4(y1)},
    })
}

/// A rule: name and both sides as diagrams.
pub fn rule(r: &Rule) -> Value {
    json!({ "name": r.name, "lhs": diagram(&r.lhs), "rhs": diagram(&r.rhs) })
}

/// A proof state: its goals, top first, each with both sides as diagrams.
pub fn proof_state(ps: &ProofState) -> Value {
    let goals: Vec<Value> = ps
        .goals
        .iter()
        .map(|g| json!({ "lhs": diagram(&g.formula.lhs), "rhs": diagram(&g.formula.rhs) }))
        .collect();
    json!({ "goals": goals })
}

/// A part. With `diagrams`, its graphs (and, for proof steps, the goals after
/// the step) are included as laid-out diagrams.
pub fn part(p: &Part, diagrams: bool) -> Value {
    let mut m = Map::new();
    m.insert("index".into(), json!(p.index));
    m.insert("kind".into(), json!(p.kind.class_name()));
    m.insert("line".into(), json!(p.line));
    m.insert("name".into(), json!(p.name));
    m.insert("status".into(), json!(p.status.as_str()));
    m.insert("start".into(), json!(p.start));
    m.insert("end".into(), json!(p.end));
    if matches!(p.kind, PartKind::ApplyTactic | PartKind::Rewrite) {
        m.insert("tactic".into(), json!(p.tactic));
        m.insert("tactic_args".into(), json!(p.tactic_args));
    }
    if let Some(s) = p.lhs_side {
        m.insert("lhs_side".into(), json!(s.as_str()));
    }
    if let Some(s) = p.rhs_side {
        m.insert("rhs_side".into(), json!(s.as_str()));
    }
    if p.kind.is_proof_step() {
        m.insert(
            "goals_after".into(),
            json!(p.proof_state.as_ref().map(|ps| ps.goals.len())),
        );
    }
    if diagrams {
        if let Some(g) = &p.graph {
            m.insert("graph".into(), diagram(g));
        }
        if let Some(g) = &p.lhs {
            m.insert("lhs".into(), diagram(g));
        }
        if let Some(g) = &p.rhs {
            m.insert("rhs".into(), diagram(g));
        }
        if let Some(ps) = &p.proof_state {
            m.insert("proof_state".into(), proof_state(ps));
        }
    }
    Value::Object(m)
}

/// A whole theory: parts, errors, rules and status counts.
pub fn theory(state: &State, diagrams: bool) -> Value {
    let count = |s: &str| state.parts.iter().filter(|p| p.status.as_str() == s).count();
    json!({
        "upstream_commit": crate::UPSTREAM_COMMIT,
        "parsed": state.parsed,
        "parts": state.parts.iter().map(|p| part(p, diagrams)).collect::<Vec<_>>(),
        "errors": state.errors.iter().map(|e| json!({"line": e.line, "msg": e.msg})).collect::<Vec<_>>(),
        "rules": state.table.rules.keys().collect::<Vec<_>>(),
        "counts": {
            "valid": count("valid"),
            "invalid": count("invalid"),
            "checking": count("checking"),
            "unchecked": count("unchecked"),
        },
    })
}

/// The same shape as tools/upstream_expected.py writes, for diffing a
/// chyp-rs run against upstream Chyp.
pub fn summary(file: &str, state: &State) -> Value {
    json!({
        "file": file,
        "crash": Value::Null,
        "parts": state.parts.iter().map(|p| json!({
            "kind": p.kind.class_name(),
            "line": p.line,
            "name": p.name,
            "status": p.status.as_str(),
        })).collect::<Vec<_>>(),
        "errors": state.errors.iter().map(|e| json!({"line": e.line, "msg": e.msg})).collect::<Vec<_>>(),
        "rules": state.table.rules.keys().collect::<Vec<_>>(),
    })
}
