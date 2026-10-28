// chyp-rs: a Rust port of part of Chyp.
//
// Derived from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// files chyp/term.py, chyp/layout.py and chyp/graph.py, by Aleks Kissinger and
// the Chyp contributors.
//
// chyp/term.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// chyp/layout.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// chyp/graph.py carries this notice:
//
//         chyp - An interactive theorem prover for string diagrams
//         Copyright (C) 2022 - Aleks Kissinger
//
//     Licensed under the Apache License, Version 2.0 (the "License");
//     you may not use this file except in compliance with the License.
//     You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//     Unless required by applicable law or agreed to in writing, software
//     distributed under the License is distributed on an "AS IS" BASIS,
//     WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//     See the License for the specific language governing permissions and
//     limitations under the License.
//
// Modified by the chyp-rs contributors, 2026. Changes from the original:
//   - only `layer_decomp` (from chyp/term.py); `convex_layout`'s initial
//     coordinates, port offsets, ordering and spacing constraints and final
//     placement of interior vertices (from chyp/layout.py); and
//     `EData.box_size` (from chyp/graph.py) are ported; term printing
//     (`graph_to_term` and friends) is not;
//   - translated to Rust; sets are iterated in increasing id order, so the
//     result is deterministic (upstream iterates Python sets); the ready
//     edges of each layer are tracked incrementally instead of recomputed
//     (same layers, linear time);
//   - in the second crossing-reduction pass a box's key is mean(sources) +
//     2 * mean(targets), where upstream counts an empty side's mean as 0 (the
//     top of the layer); here an empty side takes the other side's mean, so a
//     box with no inputs sorts by 3 * mean(targets) (upstream: 2 * that) and
//     a box with no outputs by 3 * mean(sources) (upstream: mean(sources));
//   - `layer_decomp` also returns the identity edges it inserted (drawn as
//     plain wire), and a cyclic graph falls back to one box per layer
//     instead of raising ValueError;
//   - the cvxpy refinement of y-coordinates is replaced by a deterministic
//     heuristic with no solver: alternating barycentric sweeps between
//     neighbouring columns, each followed by an isotonic projection that
//     enforces upstream's ordering and spacing constraints, until the
//     coordinates stop moving.

//! A simple deterministic layered layout for string diagrams.
//!
//! Columns, left to right: the inputs, one column per edge layer, the
//! outputs. Within a column, items keep their order; consecutive boundary
//! vertices are at least 1 apart, consecutive boxes at least
//! (size1 + size2) / 2 apart (a box's size is 1 if it has at most one input
//! and one output, otherwise 2). A box's ports sit at y + offset, offsets
//! spread evenly over [-0.5, 0.5].

use std::collections::{BTreeMap, BTreeSet};

use crate::graph::Graph;

/// Upstream's `EData.box_size`.
pub fn box_size(g: &Graph, e: usize) -> usize {
    let ed = g.edge_data(e);
    if ed.s.len() <= 1 && ed.t.len() <= 1 {
        1
    } else {
        2
    }
}

/// Port offset of the j-th of n ports: 0 for a single port, else evenly
/// spread over [-0.5, 0.5].
pub fn port_offset(j: usize, n: usize) -> f64 {
    if n <= 1 {
        0.0
    } else {
        j as f64 / (n - 1) as f64 - 0.5
    }
}

/// Sort the edges of `g` into layers so every edge's sources are produced by
/// an earlier layer (or are inputs). Identity edges (labelled "id") are
/// inserted into `g` so that every wire crosses exactly one column boundary;
/// their ids are returned in the second component.
pub fn layer_decomp(g: &mut Graph) -> Result<(Vec<Vec<usize>>, BTreeSet<usize>), String> {
    let mut e_layers: Vec<Vec<usize>> = Vec::new();
    let mut v_layer: Vec<usize> = Vec::new();
    let mut v_placed: BTreeSet<usize> = BTreeSet::new();
    let mut inserted: BTreeSet<usize> = BTreeSet::new();

    // Inputs are placed; an input that is also an output gets an id edge.
    let outputs: BTreeSet<usize> = g.outputs().iter().copied().collect();
    for v in g.inputs().to_vec() {
        if outputs.contains(&v) {
            inserted.insert(g.insert_id_after(v, false));
        }
        v_layer.push(v);
        v_placed.insert(v);
    }

    let mut new_ids: BTreeSet<usize> = BTreeSet::new();
    let mut edges: BTreeSet<usize> = g.edges().collect();
    // Upstream recomputes the ready edges (all sources placed) from scratch
    // for every layer; counting each edge's unplaced sources gives the same
    // sets in linear time.
    let mut unplaced: BTreeMap<usize, usize> = edges
        .iter()
        .map(|&e| (e, g.source(e).iter().filter(|v| !v_placed.contains(*v)).count()))
        .collect();
    let mut pending: BTreeSet<usize> = edges.iter().copied().filter(|e| unplaced[e] == 0).collect();

    while !edges.is_empty() {
        let mut ready: BTreeSet<usize> = std::mem::take(&mut pending);
        let outputs: BTreeSet<usize> = g.outputs().iter().copied().collect();
        for &v in &v_layer {
            if outputs.contains(&v) || g.out_edges(v).iter().any(|e| !ready.contains(e)) {
                // v's out-edges now leave from a fresh, unplaced vertex.
                for e in g.out_edges(v).clone() {
                    let n = g.source(e).iter().filter(|&&x| x == v).count();
                    *unplaced.get_mut(&e).unwrap() += n;
                }
                let id = g.insert_id_after(v, false);
                new_ids.insert(id);
                inserted.insert(id);
                ready.insert(id);
            }
        }
        let e_layer: Vec<usize> = ready.iter().copied().collect();
        for e in &e_layer {
            edges.remove(e);
        }
        if e_layer.iter().all(|e| new_ids.contains(e)) {
            return Err("Could not make progress. Is graph acyclic?".into());
        }
        if !edges.is_empty() {
            v_layer = Vec::new();
            for &e in &e_layer {
                for &v in g.target(e) {
                    if v_placed.insert(v) {
                        for &e2 in g.out_edges(v) {
                            if let Some(n) = unplaced.get_mut(&e2) {
                                *n -= g.source(e2).iter().filter(|&&x| x == v).count();
                                if *n == 0 && edges.contains(&e2) {
                                    pending.insert(e2);
                                }
                            }
                        }
                    }
                    v_layer.push(v);
                }
            }
        }
        e_layers.push(e_layer);
    }

    // Reduce crossings: sort each layer by the mean position of its sources
    // (forward pass), then also of its targets, weighted double (backward).
    for it in 0..2 {
        let order: Vec<usize> = if it == 0 {
            (0..e_layers.len()).collect()
        } else {
            (0..e_layers.len()).rev().collect()
        };
        for j in order {
            let inp: Vec<usize> = if j > 0 {
                e_layers[j - 1].iter().flat_map(|&e| g.target(e).to_vec()).collect()
            } else {
                g.inputs().to_vec()
            };
            let inp_pos: BTreeMap<usize, f64> = inp
                .iter()
                .enumerate()
                .map(|(i, &v)| (v, i as f64 / inp.len() as f64))
                .collect();
            let outp_pos: Option<BTreeMap<usize, f64>> = if it != 0 {
                let outp: Vec<usize> = if j + 1 < e_layers.len() {
                    e_layers[j + 1].iter().flat_map(|&e| g.source(e).to_vec()).collect()
                } else {
                    g.outputs().to_vec()
                };
                Some(
                    outp.iter()
                        .enumerate()
                        .map(|(i, &v)| (v, i as f64 / outp.len() as f64))
                        .collect(),
                )
            } else {
                None
            };
            let mut e_pos: BTreeMap<usize, f64> = BTreeMap::new();
            for &e in &e_layers[j] {
                let mean = |vs: &[usize], pos: &BTreeMap<usize, f64>| -> Option<f64> {
                    if vs.is_empty() {
                        None
                    } else {
                        Some(vs.iter().map(|v| pos.get(v).copied().unwrap_or(0.0)).sum::<f64>() / vs.len() as f64)
                    }
                };
                let src = mean(g.source(e), &inp_pos);
                let p = match &outp_pos {
                    None => src.unwrap_or(0.0),
                    // Upstream counts an empty side's mean as 0 (the top of the
                    // layer); here it takes the other side's mean, so states and
                    // effects are not pulled up across other wires.
                    Some(op) => {
                        let tgt = mean(g.target(e), op);
                        src.or(tgt).unwrap_or(0.0) + 2.0 * tgt.or(src).unwrap_or(0.0)
                    }
                };
                e_pos.insert(e, p);
            }
            // Stable sort, as Python's list.sort.
            e_layers[j].sort_by(|a, b| e_pos[a].partial_cmp(&e_pos[b]).unwrap_or(std::cmp::Ordering::Equal));
        }
    }

    Ok((e_layers, inserted))
}

/// A laid-out diagram: the graph (with any identity edges the layout
/// inserted), its layers, and coordinates for every vertex and edge.
#[derive(Debug, Clone)]
pub struct Layout {
    pub graph: Graph,
    pub layers: Vec<Vec<usize>>,
    /// Identity edges inserted by the layout: draw them as plain wire.
    pub inserted: BTreeSet<usize>,
    pub vpos: BTreeMap<usize, (f64, f64)>,
    pub epos: BTreeMap<usize, (f64, f64)>,
}

impl Layout {
    /// y-coordinates of an edge's input ports, top to bottom.
    pub fn in_ports(&self, e: usize) -> Vec<f64> {
        let (_, y) = self.epos[&e];
        let n = self.graph.source(e).len();
        (0..n).map(|j| y + port_offset(j, n)).collect()
    }

    /// y-coordinates of an edge's output ports, top to bottom.
    pub fn out_ports(&self, e: usize) -> Vec<f64> {
        let (_, y) = self.epos[&e];
        let n = self.graph.target(e).len();
        (0..n).map(|j| y + port_offset(j, n)).collect()
    }

    /// (x_min, x_max, y_min, y_max) covering every vertex and every box,
    /// taking a box to span x ± BOX_HALF_WIDTH and y ± size / 2. An empty
    /// diagram gets a unit square around the origin.
    pub fn bounds(&self) -> (f64, f64, f64, f64) {
        let mut b: Option<(f64, f64, f64, f64)> = None;
        let mut add = |x0: f64, x1: f64, y0: f64, y1: f64| {
            b = Some(match b {
                None => (x0, x1, y0, y1),
                Some(b) => (b.0.min(x0), b.1.max(x1), b.2.min(y0), b.3.max(y1)),
            });
        };
        for &(x, y) in self.vpos.values() {
            add(x, x, y, y);
        }
        for (&e, &(x, y)) in &self.epos {
            let (hw, hh) = if self.inserted.contains(&e) {
                (0.0, 0.0)
            } else {
                (BOX_HALF_WIDTH, box_size(&self.graph, e) as f64 * 0.5)
            };
            add(x - hw, x + hw, y - hh, y + hh);
        }
        b.unwrap_or((-0.5, 0.5, -0.5, 0.5))
    }
}

/// A wire between adjacent columns: (left column, left item, left port
/// offset, right item, right port offset).
type Wire = (usize, usize, f64, usize, f64);

/// One item of a column: a boundary vertex or a box.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Item {
    V(usize),
    E(usize),
}

/// Half the width of a box, in layout units (columns are 3 apart).
pub const BOX_HALF_WIDTH: f64 = 0.5;

/// Barycentric sweeps (each one left-to-right then right-to-left) stop once
/// no coordinate moves more than CONVERGED, or after MAX_SWEEPS.
const MAX_SWEEPS: usize = 200;
const CONVERGED: f64 = 1e-9;

/// Lay out `g` (which is not modified).
pub fn layout(g: &Graph) -> Layout {
    let mut g = g.clone();
    let (layers, inserted) = match layer_decomp(&mut g) {
        Ok(r) => r,
        // Graphs built from terms are acyclic; fall back to one box per layer.
        Err(_) => (g.edges().map(|e| vec![e]).collect(), BTreeSet::new()),
    };

    // Columns of items, and upstream's initial coordinates.
    let n_layers = layers.len();
    let mut cols: Vec<Vec<Item>> = Vec::with_capacity(n_layers + 2);
    cols.push(g.inputs().iter().map(|&v| Item::V(v)).collect());
    for l in &layers {
        cols.push(l.iter().map(|&e| Item::E(e)).collect());
    }
    cols.push(g.outputs().iter().map(|&v| Item::V(v)).collect());
    let x0 = -((n_layers + 1) as f64) * 1.5;
    let col_x = |c: usize| -> f64 {
        if c == 0 {
            x0 + 1.5
        } else if c == n_layers + 1 {
            x0 + 3.0 * (n_layers + 1) as f64 - 1.5
        } else {
            x0 + 3.0 * c as f64
        }
    };

    let mut y: Vec<Vec<f64>> = cols
        .iter()
        .enumerate()
        .map(|(c, items)| {
            let n = items.len() as f64;
            let step = if c == 0 || c == n_layers + 1 { 1.0 } else { 2.0 };
            (0..items.len()).map(|i| step * (i as f64 - (n - 1.0) / 2.0)).collect()
        })
        .collect();

    // Minimum gaps between consecutive items of each column.
    let gaps: Vec<Vec<f64>> = cols
        .iter()
        .map(|items| {
            items
                .windows(2)
                .map(|w| match (w[0], w[1]) {
                    (Item::E(a), Item::E(b)) => (box_size(&g, a) + box_size(&g, b)) as f64 * 0.5,
                    _ => 1.0,
                })
                .collect()
        })
        .collect();

    // Where each item sits: boundary vertices in the first/last column, boxes
    // in their layer's column.
    let mut v_slot: BTreeMap<(usize, usize), usize> = BTreeMap::new(); // (col, vertex) -> position
    let mut e_slot: BTreeMap<usize, (usize, usize)> = BTreeMap::new(); // edge -> (col, position)
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            match *it {
                Item::V(v) => {
                    v_slot.insert((c, v), i);
                }
                Item::E(e) => {
                    e_slot.insert(e, (c, i));
                }
            }
        }
    }
    // Each vertex's port on the box it leaves and on the box it enters.
    let mut out_port: BTreeMap<usize, (usize, f64)> = BTreeMap::new(); // v -> (edge, offset), v a target
    let mut in_port: BTreeMap<usize, (usize, f64)> = BTreeMap::new(); // v -> (edge, offset), v a source
    for e in g.edges() {
        let ed = g.edge_data(e);
        for (j, &v) in ed.t.iter().enumerate() {
            out_port.entry(v).or_insert((e, port_offset(j, ed.t.len())));
        }
        for (j, &v) in ed.s.iter().enumerate() {
            in_port.entry(v).or_insert((e, port_offset(j, ed.s.len())));
        }
    }

    // Wires between adjacent columns: (left col, left item, left port offset,
    // right item, right port offset). Every vertex is one wire.
    let mut wires: Vec<Wire> = Vec::new();
    for v in g.vertices() {
        // Left end: an input, or the box that has v as a target.
        let left = match out_port.get(&v) {
            Some(&(e, off)) => e_slot.get(&e).map(|&(c, i)| (c, i, off)),
            None => v_slot.get(&(0, v)).map(|&i| (0, i, 0.0)),
        };
        // Right end: the box that has v as a source, or an output.
        let right = match in_port.get(&v) {
            Some(&(e, off)) => e_slot.get(&e).map(|&(c, i)| (c, i, off)),
            None => v_slot.get(&(n_layers + 1, v)).map(|&i| (n_layers + 1, i, 0.0)),
        };
        if let (Some((lc, li, lo)), Some((rc, ri, ro))) = (left, right) {
            if rc == lc + 1 {
                wires.push((lc, li, lo, ri, ro));
            }
        }
    }
    // Wires by left column.
    let mut by_col: Vec<Vec<Wire>> = vec![Vec::new(); cols.len()];
    for w in wires {
        by_col[w.0].push(w);
    }

    // Alternating sweeps: move each item towards the mean straight-wire
    // position given its neighbours in the previous (or next) column, then
    // restore order and spacing with the least squares change.
    for _ in 0..MAX_SWEEPS {
        let before = y.clone();
        for c in 1..cols.len() {
            relax(&mut y, &gaps, &by_col[c - 1], c, true);
        }
        for c in (0..cols.len().saturating_sub(1)).rev() {
            relax(&mut y, &gaps, &by_col[c], c, false);
        }
        let moved = y
            .iter()
            .flatten()
            .zip(before.iter().flatten())
            .map(|(a, b)| (a - b).abs())
            .fold(0.0f64, f64::max);
        if moved < CONVERGED {
            break;
        }
    }

    // Centre vertically.
    let all: Vec<f64> = y.iter().flatten().copied().collect();
    if let (Some(lo), Some(hi)) = (
        all.iter().copied().reduce(f64::min),
        all.iter().copied().reduce(f64::max),
    ) {
        let shift = (lo + hi) * 0.5;
        for col in y.iter_mut() {
            for v in col.iter_mut() {
                *v -= shift;
            }
        }
    }

    let mut vpos: BTreeMap<usize, (f64, f64)> = BTreeMap::new();
    let mut epos: BTreeMap<usize, (f64, f64)> = BTreeMap::new();
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            match *it {
                Item::V(v) => {
                    vpos.insert(v, (col_x(c), y[c][i]));
                }
                Item::E(e) => {
                    epos.insert(e, (col_x(c), y[c][i]));
                }
            }
        }
    }
    // Interior vertices sit just right of the box they leave, at its port.
    for (c, items) in cols.iter().enumerate() {
        for (i, it) in items.iter().enumerate() {
            if let Item::E(e) = *it {
                let t = g.target(e).to_vec();
                for (j, &v) in t.iter().enumerate() {
                    if !g.is_boundary(v) {
                        vpos.insert(v, (col_x(c) + 0.7, y[c][i] + port_offset(j, t.len())));
                    }
                }
            }
        }
    }
    // Anything left (cannot happen for graphs built from terms).
    for v in g.vertices() {
        vpos.entry(v).or_insert((0.0, 0.0));
    }

    Layout {
        graph: g,
        layers,
        inserted,
        vpos,
        epos,
    }
}

/// One relaxation of column `c` against its left (`forward`) or right
/// neighbour column; `wires` are the wires between the two.
fn relax(y: &mut [Vec<f64>], gaps: &[Vec<f64>], wires: &[Wire], c: usize, forward: bool) {
    let n = y[c].len();
    if n == 0 {
        return;
    }
    let mut sum = vec![0.0f64; n];
    let mut cnt = vec![0usize; n];
    for &(lc, li, lo, ri, ro) in wires {
        if forward && lc + 1 == c {
            sum[ri] += y[lc][li] + lo - ro;
            cnt[ri] += 1;
        } else if !forward && lc == c {
            sum[li] += y[c + 1][ri] + ro - lo;
            cnt[li] += 1;
        }
    }
    let target: Vec<f64> = (0..n)
        .map(|i| if cnt[i] > 0 { sum[i] / cnt[i] as f64 } else { y[c][i] })
        .collect();
    y[c] = project(&target, &gaps[c]);
}

/// The closest (least squares) y to `target` with y[i+1] - y[i] >= gap[i]:
/// pool-adjacent-violators on y[i] - (gap[0] + ... + gap[i-1]).
fn project(target: &[f64], gap: &[f64]) -> Vec<f64> {
    let n = target.len();
    let mut offset = vec![0.0f64; n];
    for i in 1..n {
        offset[i] = offset[i - 1] + gap[i - 1];
    }
    // Blocks of (sum, count).
    let mut blocks: Vec<(f64, usize)> = Vec::with_capacity(n);
    for i in 0..n {
        blocks.push((target[i] - offset[i], 1));
        while blocks.len() >= 2 {
            let (s2, c2) = blocks[blocks.len() - 1];
            let (s1, c1) = blocks[blocks.len() - 2];
            if s1 / c1 as f64 > s2 / c2 as f64 {
                blocks.pop();
                blocks.pop();
                blocks.push((s1 + s2, c1 + c2));
            } else {
                break;
            }
        }
    }
    let mut out = Vec::with_capacity(n);
    for (s, c) in blocks {
        let m = s / c as f64;
        for _ in 0..c {
            let i = out.len();
            out.push(m + offset[i]);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{gen, identity, perm};

    #[test]
    fn layers_and_inserted_wires() {
        let f = gen("f", 1, 1);
        let m = gen("m", 2, 1);
        // f * id ; m : the second input needs an id edge in the first layer.
        let g = f.par(&identity()).seq(&m).unwrap();
        let l = layout(&g);
        assert_eq!(l.layers.len(), 2);
        assert_eq!(l.inserted.len(), 1);
        let (fx, _) = l.epos[&0];
        let (mx, _) = l.epos[&1];
        assert!(fx < mx);
    }

    #[test]
    fn straight_chain_is_straight() {
        let f = gen("f", 1, 1);
        let g = f.seq(&f).unwrap().seq(&f).unwrap();
        let l = layout(&g);
        for &(_, y) in l.epos.values() {
            assert!(y.abs() < 1e-9);
        }
    }

    #[test]
    fn spacing_and_determinism() {
        let sw = perm(&[1, 0]).unwrap();
        let n = gen("n", 1, 2);
        let m = gen("m", 2, 1);
        let g = n
            .par(&n)
            .seq(&identity().par(&sw).par(&identity()))
            .unwrap()
            .seq(&m.par(&m))
            .unwrap();
        let a = layout(&g);
        let b = layout(&g);
        assert_eq!(a.epos, b.epos);
        assert_eq!(a.vpos, b.vpos);
        for layer in &a.layers {
            for w in layer.windows(2) {
                let need = (box_size(&a.graph, w[0]) + box_size(&a.graph, w[1])) as f64 * 0.5;
                assert!(a.epos[&w[1]].1 - a.epos[&w[0]].1 >= need - 1e-9);
            }
        }
    }

    /// States (boxes with no inputs) keep their place: `h * f * u` has no
    /// crossing and `h * (f ; f) * u` keeps the chain straight.
    #[test]
    fn states_do_not_float_up() {
        let (f, h, u) = (gen("f", 1, 1), gen("h", 1, 2), gen("u", 0, 1));
        let l = layout(&h.par(&f).par(&u));
        let labels: Vec<&str> = l.layers[0]
            .iter()
            .map(|&e| l.graph.edge_data(e).value.as_str())
            .collect();
        assert_eq!(labels, ["h", "f", "u"]);
        let ff = f.seq(&f).unwrap();
        let l = layout(&h.par(&ff).par(&u));
        let ys: Vec<f64> = l
            .graph
            .edges()
            .filter(|&e| l.graph.edge_data(e).value == "f")
            .map(|e| l.epos[&e].1)
            .collect();
        assert_eq!(ys.len(), 2);
        assert!((ys[0] - ys[1]).abs() < 1e-6, "chain bent: {:?}", ys);
    }

    #[test]
    fn bounds_cover_boxes() {
        let f = gen("f", 1, 1);
        let l = layout(&f.seq(&f).unwrap());
        let (x0, x1, y0, y1) = l.bounds();
        assert!(x1 > x0 && y1 - y0 >= 1.0 - 1e-9);
        let (x0, x1, y0, y1) = layout(&Graph::new()).bounds();
        assert!(x1 > x0 && y1 > y0);
        let s = gen("s", 0, 0);
        let (_, _, y0, y1) = layout(&s).bounds();
        assert!(y1 > y0);
    }

    #[test]
    fn projection() {
        let y = project(&[0.0, 0.0, 0.0], &[1.0, 1.0]);
        assert_eq!(y, vec![-1.0, 0.0, 1.0]);
        let y = project(&[0.0, 5.0], &[1.0]);
        assert_eq!(y, vec![0.0, 5.0]);
    }
}
