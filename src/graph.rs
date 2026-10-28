// chyp-rs: a Rust port of part of Chyp.
//
// Derived from Chyp (https://github.com/akissinger/chyp), commit 3d28483,
// file chyp/graph.py, by Aleks Kissinger and Alexander Koziell-Pipe.
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
//   - translated to Rust;
//   - single-sorted only: vertex types, register sizes, type and size
//     inference and redistributers are not ported, so a (co)domain is a
//     number of wires (`type_repr` prints it the way upstream prints a type
//     list, so error messages are identical);
//   - drawing coordinates, colours, highlighting, the `value` of vertices,
//     the `hyper` flag and JSON graph loading (`load_graph`,
//     `graph_from_json`) are not ported;
//   - the `__mul__`/`__rshift__` operators become the methods `par`/`seq`;
//   - `perm` checks that its argument is a permutation of 0..n-1 (upstream
//     accepts any list; an index out of range raises IndexError);
//   - `remove_vertex` and `explode_vertex` return errors instead of raising;
//   - the boundary index bookkeeping in `set_inputs`, `set_outputs`,
//     `merge_vertices`, `insert_id_after` and `remove_vertex` updates only
//     the vertices involved instead of every vertex (same result, linear
//     instead of quadratic time).

//! Hypergraphs with boundaries: Chyp's representation of string diagrams.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// An error from building or composing graphs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphError(pub String);

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Render a single-sorted (co)domain of `n` wires the way upstream Chyp
/// prints its `list[tuple[VType, int]]`, e.g. `[(None, 1), (None, 1)]`, so that
/// error messages match upstream's exactly.
pub fn type_repr(n: usize) -> String {
    let items: Vec<&str> = (0..n).map(|_| "(None, 1)").collect();
    format!("[{}]", items.join(", "))
}

/// Data associated with a single vertex.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct VData {
    /// Edges for which this vertex is a target.
    pub in_edges: BTreeSet<usize>,
    /// Edges for which this vertex is a source.
    pub out_edges: BTreeSet<usize>,
    /// Indices where this vertex occurs in the graph's inputs.
    pub in_indices: BTreeSet<usize>,
    /// Indices where this vertex occurs in the graph's outputs.
    pub out_indices: BTreeSet<usize>,
}

/// Data associated with a single (hyper)edge.
#[derive(Debug, Clone, PartialEq)]
pub struct EData {
    /// Source vertices, in order.
    pub s: Vec<usize>,
    /// Target vertices, in order.
    pub t: Vec<usize>,
    /// The edge's label: a generator name, or "id" for identity boxes that
    /// the layout inserts.
    pub value: String,
}

/// A directed hypergraph with an ordered list of input and output vertices.
///
/// Vertex and edge ids are assigned in increasing order and never reused, so
/// iterating the `BTreeMap`s gives insertion order, as Python dicts do in the
/// original. Matching enumerates candidates in this order.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Graph {
    vdata: BTreeMap<usize, VData>,
    edata: BTreeMap<usize, EData>,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
    vindex: usize,
    eindex: usize,
}

impl Graph {
    pub fn new() -> Graph {
        Graph::default()
    }

    /// Vertex ids, in insertion order.
    pub fn vertices(&self) -> impl Iterator<Item = usize> + '_ {
        self.vdata.keys().copied()
    }

    /// Edge ids, in insertion order.
    pub fn edges(&self) -> impl Iterator<Item = usize> + '_ {
        self.edata.keys().copied()
    }

    pub fn num_vertices(&self) -> usize {
        self.vdata.len()
    }

    pub fn num_edges(&self) -> usize {
        self.edata.len()
    }

    /// Number of input wires (upstream: the length of `domain()`).
    pub fn domain(&self) -> usize {
        self.inputs.len()
    }

    /// Number of output wires (upstream: the length of `codomain()`).
    pub fn codomain(&self) -> usize {
        self.outputs.len()
    }

    pub fn has_vertex(&self, v: usize) -> bool {
        self.vdata.contains_key(&v)
    }

    pub fn has_edge(&self, e: usize) -> bool {
        self.edata.contains_key(&e)
    }

    pub fn vertex_data(&self, v: usize) -> &VData {
        &self.vdata[&v]
    }

    pub fn edge_data(&self, e: usize) -> &EData {
        &self.edata[&e]
    }

    pub fn in_edges(&self, v: usize) -> &BTreeSet<usize> {
        &self.vdata[&v].in_edges
    }

    pub fn out_edges(&self, v: usize) -> &BTreeSet<usize> {
        &self.vdata[&v].out_edges
    }

    pub fn source(&self, e: usize) -> &[usize] {
        &self.edata[&e].s
    }

    pub fn target(&self, e: usize) -> &[usize] {
        &self.edata[&e].t
    }

    /// Add a fresh vertex and return its id.
    pub fn add_vertex(&mut self) -> usize {
        let v = self.vindex;
        self.vindex += 1;
        self.vdata.insert(v, VData::default());
        v
    }

    /// Add a hyperedge with the given source and target lists.
    pub fn add_edge(&mut self, s: Vec<usize>, t: Vec<usize>, value: &str) -> usize {
        let e = self.eindex;
        self.eindex += 1;
        for &v in &s {
            self.vdata
                .get_mut(&v)
                .expect("add_edge: unknown source")
                .out_edges
                .insert(e);
        }
        for &v in &t {
            self.vdata
                .get_mut(&v)
                .expect("add_edge: unknown target")
                .in_edges
                .insert(e);
        }
        self.edata.insert(
            e,
            EData {
                s,
                t,
                value: value.to_string(),
            },
        );
        e
    }

    /// Remove a vertex. With `strict`, it must have no adjacent edges and not
    /// be on the boundary; otherwise it is also removed from adjacent edges'
    /// source/target lists and from the boundary.
    pub fn remove_vertex(&mut self, v: usize, strict: bool) -> Result<(), GraphError> {
        if strict {
            let vd = &self.vdata[&v];
            if !vd.in_edges.is_empty() || !vd.out_edges.is_empty() {
                return Err(GraphError(
                    "Attempting to remove vertex with adjacentedges while strict == True.".into(),
                ));
            }
            if self.inputs.contains(&v) || self.outputs.contains(&v) {
                return Err(GraphError(
                    "Attempting to remove boundary vertex whilestrict == True.".into(),
                ));
            }
        } else {
            let vd = self.vdata[&v].clone();
            for e in &vd.in_edges {
                if let Some(ed) = self.edata.get_mut(e) {
                    ed.t.retain(|&x| x != v);
                }
            }
            for e in &vd.out_edges {
                if let Some(ed) = self.edata.get_mut(e) {
                    ed.s.retain(|&x| x != v);
                }
            }
            // Rebuild a boundary list only if v is on it (otherwise filtering
            // it out changes nothing).
            if !vd.in_indices.is_empty() {
                let inputs: Vec<usize> = self.inputs.iter().copied().filter(|&x| x != v).collect();
                self.set_inputs(inputs);
            }
            if !vd.out_indices.is_empty() {
                let outputs: Vec<usize> = self.outputs.iter().copied().filter(|&x| x != v).collect();
                self.set_outputs(outputs);
            }
        }
        self.vdata.remove(&v);
        Ok(())
    }

    /// Remove an edge.
    pub fn remove_edge(&mut self, e: usize) {
        let ed = self.edata.remove(&e).expect("remove_edge: unknown edge");
        for v in &ed.s {
            if let Some(vd) = self.vdata.get_mut(v) {
                vd.out_edges.remove(&e);
            }
        }
        for v in &ed.t {
            if let Some(vd) = self.vdata.get_mut(v) {
                vd.in_edges.remove(&e);
            }
        }
    }

    /// Append to the inputs.
    pub fn add_inputs(&mut self, inp: &[usize]) {
        let i1 = self.inputs.len();
        self.inputs.extend_from_slice(inp);
        for i in i1..self.inputs.len() {
            let v = self.inputs[i];
            self.vdata
                .get_mut(&v)
                .expect("add_inputs: unknown vertex")
                .in_indices
                .insert(i);
        }
    }

    /// Append to the outputs.
    pub fn add_outputs(&mut self, outp: &[usize]) {
        let i1 = self.outputs.len();
        self.outputs.extend_from_slice(outp);
        for i in i1..self.outputs.len() {
            let v = self.outputs[i];
            self.vdata
                .get_mut(&v)
                .expect("add_outputs: unknown vertex")
                .out_indices
                .insert(i);
        }
    }

    pub fn set_inputs(&mut self, inp: Vec<usize>) {
        // Upstream clears every vertex's index set; only the current inputs
        // have any.
        for v in std::mem::take(&mut self.inputs) {
            if let Some(d) = self.vdata.get_mut(&v) {
                d.in_indices.clear();
            }
        }
        for (i, &v) in inp.iter().enumerate() {
            self.vdata
                .get_mut(&v)
                .expect("set_inputs: unknown vertex")
                .in_indices
                .insert(i);
        }
        self.inputs = inp;
    }

    pub fn set_outputs(&mut self, outp: Vec<usize>) {
        // As set_inputs: only the current outputs have index sets to clear.
        for v in std::mem::take(&mut self.outputs) {
            if let Some(d) = self.vdata.get_mut(&v) {
                d.out_indices.clear();
            }
        }
        for (i, &v) in outp.iter().enumerate() {
            self.vdata
                .get_mut(&v)
                .expect("set_outputs: unknown vertex")
                .out_indices
                .insert(i);
        }
        self.outputs = outp;
    }

    pub fn inputs(&self) -> &[usize] {
        &self.inputs
    }

    pub fn outputs(&self) -> &[usize] {
        &self.outputs
    }

    pub fn is_input(&self, v: usize) -> bool {
        !self.vdata[&v].in_indices.is_empty()
    }

    pub fn is_output(&self, v: usize) -> bool {
        !self.vdata[&v].out_indices.is_empty()
    }

    pub fn is_boundary(&self, v: usize) -> bool {
        self.is_input(v) || self.is_output(v)
    }

    /// Vertices on a directed path out of any of `vs` (not including `vs`
    /// themselves unless reachable).
    pub fn successors(&self, vs: impl IntoIterator<Item = usize>) -> BTreeSet<usize> {
        let mut succ = BTreeSet::new();
        let mut current: Vec<usize> = vs.into_iter().collect();
        while let Some(v) = current.pop() {
            for &e in self.out_edges(v) {
                for &v1 in self.target(e) {
                    if succ.insert(v1) {
                        current.push(v1);
                    }
                }
            }
        }
        succ
    }

    /// Merge vertex `w` into vertex `v` (quotient by v ~ w); `v` survives.
    pub fn merge_vertices(&mut self, v: usize, w: usize) {
        let w_in: Vec<usize> = self.vdata[&w].in_edges.iter().copied().collect();
        let w_out: Vec<usize> = self.vdata[&w].out_edges.iter().copied().collect();
        for e in w_in {
            let ed = self.edata.get_mut(&e).expect("merge_vertices: unknown edge");
            for x in ed.t.iter_mut() {
                if *x == w {
                    *x = v;
                }
            }
            self.vdata
                .get_mut(&v)
                .expect("merge_vertices: unknown vertex")
                .in_edges
                .insert(e);
        }
        for e in w_out {
            let ed = self.edata.get_mut(&e).expect("merge_vertices: unknown edge");
            for x in ed.s.iter_mut() {
                if *x == w {
                    *x = v;
                }
            }
            self.vdata
                .get_mut(&v)
                .expect("merge_vertices: unknown vertex")
                .out_edges
                .insert(e);
        }
        // Replace w by v on the boundary. Upstream rebuilds every vertex's
        // index sets here; only v's and w's change, so move w's to v.
        let w_in = std::mem::take(&mut self.vdata.get_mut(&w).unwrap().in_indices);
        let w_out = std::mem::take(&mut self.vdata.get_mut(&w).unwrap().out_indices);
        for &i in &w_in {
            self.inputs[i] = v;
        }
        for &i in &w_out {
            self.outputs[i] = v;
        }
        let vd = self.vdata.get_mut(&v).expect("merge_vertices: unknown vertex");
        vd.in_indices.extend(w_in);
        vd.out_indices.extend(w_out);
        // Non-strict removal cannot fail.
        let _ = self.remove_vertex(w, false);
    }

    /// Split a vertex into one copy per input occurrence / in-edge tentacle
    /// ("input-like") and per output occurrence / out-edge tentacle
    /// ("output-like"). Used for pushout complements of rules that aren't
    /// left-linear (arXiv:2012.01847, Section 3.3).
    pub fn explode_vertex(&mut self, v: usize) -> Result<(Vec<usize>, Vec<usize>), GraphError> {
        let mut new_in: Vec<usize> = Vec::new();
        let mut new_out: Vec<usize> = Vec::new();
        let vd = self.vdata[&v].clone();

        let mut inputs = self.inputs.clone();
        for x in inputs.iter_mut() {
            if *x == v {
                let v1 = self.add_vertex();
                new_in.push(v1);
                *x = v1;
            }
        }
        self.set_inputs(inputs);

        for &e in &vd.in_edges {
            let len = self.edata[&e].t.len();
            for i in 0..len {
                if self.edata[&e].t[i] == v {
                    let v1 = self.add_vertex();
                    new_in.push(v1);
                    self.edata.get_mut(&e).unwrap().t[i] = v1;
                    self.vdata.get_mut(&v1).unwrap().in_edges.insert(e);
                }
            }
        }

        let mut outputs = self.outputs.clone();
        for x in outputs.iter_mut() {
            if *x == v {
                let v1 = self.add_vertex();
                new_out.push(v1);
                *x = v1;
            }
        }
        self.set_outputs(outputs);

        for &e in &vd.out_edges {
            let len = self.edata[&e].s.len();
            for i in 0..len {
                if self.edata[&e].s[i] == v {
                    let v1 = self.add_vertex();
                    new_out.push(v1);
                    self.edata.get_mut(&e).unwrap().s[i] = v1;
                    self.vdata.get_mut(&v1).unwrap().out_edges.insert(e);
                }
            }
        }

        {
            let d = self.vdata.get_mut(&v).unwrap();
            d.in_edges.clear();
            d.out_edges.clear();
        }
        self.remove_vertex(v, true)?;
        Ok((new_in, new_out))
    }

    /// Insert an identity edge after `v`: a new vertex `w` takes over `v`'s
    /// out-edges and output occurrences, and an "id" edge goes from `v` to `w`
    /// (or from `w` to `v` if `reverse`). Returns the new edge. Used by the
    /// layout's layer decomposition.
    pub fn insert_id_after(&mut self, v: usize, reverse: bool) -> usize {
        let w = self.add_vertex();
        // w takes v's output occurrences (upstream rebuilds all index sets).
        let v_out = std::mem::take(&mut self.vdata.get_mut(&v).unwrap().out_indices);
        for &i in &v_out {
            self.outputs[i] = w;
        }
        self.vdata.get_mut(&w).unwrap().out_indices = v_out;
        let v_out: Vec<usize> = self.vdata[&v].out_edges.iter().copied().collect();
        for e in v_out {
            let ed = self.edata.get_mut(&e).unwrap();
            for x in ed.s.iter_mut() {
                if *x == v {
                    *x = w;
                }
            }
            self.vdata.get_mut(&w).unwrap().out_edges.insert(e);
        }
        self.vdata.get_mut(&v).unwrap().out_edges.clear();
        let (s, t) = if reverse {
            (vec![w], vec![v])
        } else {
            (vec![v], vec![w])
        };
        self.add_edge(s, t, "id")
    }

    /// In-place monoidal product: `self` becomes `self * other`.
    pub fn tensor(&mut self, other: &Graph) {
        let mut vmap: BTreeMap<usize, usize> = BTreeMap::new();
        for v in other.vertices() {
            let v1 = self.add_vertex();
            vmap.insert(v, v1);
        }
        for e in other.edges() {
            let ed = other.edge_data(e);
            let s = ed.s.iter().map(|v| vmap[v]).collect();
            let t = ed.t.iter().map(|v| vmap[v]).collect();
            self.add_edge(s, t, &ed.value);
        }
        let inp: Vec<usize> = other.inputs().iter().map(|v| vmap[v]).collect();
        self.add_inputs(&inp);
        let outp: Vec<usize> = other.outputs().iter().map(|v| vmap[v]).collect();
        self.add_outputs(&outp);
    }

    /// The monoidal product `self * other`, leaving both unchanged.
    pub fn par(&self, other: &Graph) -> Graph {
        let mut g = self.clone();
        g.tensor(other);
        g
    }

    /// In-place sequential composition: `self` becomes `self ; other`.
    pub fn compose(&mut self, other: &Graph) -> Result<(), GraphError> {
        if self.outputs.len() != other.inputs().len() {
            return Err(GraphError(format!(
                "Codomain {} does not match domain {}",
                type_repr(self.codomain()),
                type_repr(other.domain())
            )));
        }

        let mut vmap: BTreeMap<usize, usize> = BTreeMap::new();
        for v in other.vertices() {
            let v1 = self.add_vertex();
            vmap.insert(v, v1);
        }
        for e in other.edges() {
            let ed = other.edge_data(e);
            let s = ed.s.iter().map(|v| vmap[v]).collect();
            let t = ed.t.iter().map(|v| vmap[v]).collect();
            self.add_edge(s, t, &ed.value);
        }

        // Plug the two graphs together: merge other's inputs into self's outputs.
        let plug1: Vec<usize> = self.outputs.clone();
        let plug2: Vec<usize> = other.inputs().iter().map(|v| vmap[v]).collect();
        self.set_outputs(other.outputs().iter().map(|v| vmap[v]).collect());

        let mut quotient: BTreeMap<usize, usize> = BTreeMap::new();
        for (&q1, &q2) in plug1.iter().zip(plug2.iter()) {
            let mut p1 = q1;
            let mut p2 = q2;
            while let Some(&p) = quotient.get(&p1) {
                p1 = p;
            }
            while let Some(&p) = quotient.get(&p2) {
                p2 = p;
            }
            if p1 != p2 {
                self.merge_vertices(p1, p2);
                quotient.insert(p2, p1);
            }
        }
        Ok(())
    }

    /// The sequential composition `self ; other`, leaving both unchanged.
    pub fn seq(&self, other: &Graph) -> Result<Graph, GraphError> {
        let mut g = self.clone();
        g.compose(other)?;
        Ok(g)
    }
}

/// A graph with one hyperedge labelled `value`, with `n_in` inputs and
/// `n_out` outputs.
pub fn gen(value: &str, n_in: usize, n_out: usize) -> Graph {
    let mut g = Graph::new();
    let inputs: Vec<usize> = (0..n_in).map(|_| g.add_vertex()).collect();
    let outputs: Vec<usize> = (0..n_out).map(|_| g.add_vertex()).collect();
    g.add_edge(inputs.clone(), outputs.clone(), value);
    g.set_inputs(inputs);
    g.set_outputs(outputs);
    g
}

/// The permutation `p`, given as a list [x0, .., x(n-1)] meaning
/// { x0 -> 0, x1 -> 1, ... }: input `xj` is wired to output `j`. So, for
/// states a0, a1, a2: `(a0 * a1 * a2) ; perm([2, 0, 1]) = a2 * a0 * a1`.
pub fn perm(p: &[u64]) -> Result<Graph, GraphError> {
    let n = p.len();
    let mut seen = vec![false; n];
    for &x in p {
        if x >= n as u64 || seen[x as usize] {
            return Err(GraphError(format!(
                "sw{:?} is not a permutation of 0..{}",
                p,
                n.saturating_sub(1)
            )));
        }
        seen[x as usize] = true;
    }
    let mut g = Graph::new();
    let inputs: Vec<usize> = (0..n).map(|_| g.add_vertex()).collect();
    let outputs: Vec<usize> = p.iter().map(|&i| inputs[i as usize]).collect();
    g.set_inputs(inputs);
    g.set_outputs(outputs);
    Ok(g)
}

/// The identity on one wire: a single vertex that is both input and output.
pub fn identity() -> Graph {
    let mut g = Graph::new();
    let v = g.add_vertex();
    g.set_inputs(vec![v]);
    g.set_outputs(vec![v]);
    g
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compose_and_tensor_shapes() {
        let f = gen("f", 1, 1);
        let m = gen("m", 2, 1);
        let g = f.par(&f).seq(&m).unwrap();
        assert_eq!(g.domain(), 2);
        assert_eq!(g.codomain(), 1);
        assert_eq!(g.num_edges(), 3);
        assert_eq!(g.num_vertices(), 5);
        assert!(f.seq(&m).is_err());
    }

    #[test]
    fn identity_and_swap() {
        let sw = perm(&[1, 0]).unwrap();
        let swsw = sw.seq(&sw).unwrap();
        assert_eq!(swsw.num_vertices(), 2);
        assert_eq!(swsw.inputs(), swsw.outputs());
        assert!(perm(&[0, 0]).is_err());
        assert!(perm(&[1, 2]).is_err());
        let id = identity();
        let f = gen("f", 1, 1);
        let g = id.seq(&f).unwrap().seq(&id).unwrap();
        assert_eq!(g.num_vertices(), 2);
    }
}
