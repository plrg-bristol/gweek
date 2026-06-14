use std::cell::Cell;

/// The canonical index of a logic variable's equivalence class.
///
/// A `Root` can only be produced by [`UnionFind::find`] (or the self-root
/// established by [`UnionFind::register`]). Because its field is private to
/// this module, per-variable storage keyed by `Root` cannot be indexed by a
/// raw `usize` — that is a compile error. This makes the read/write
/// canonicalization invariant inexpressible to violate from outside.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Root(usize);

#[derive(Clone)]
struct Node {
    depth: usize,
    parent: Cell<Option<usize>>,
}

impl Node {
    fn new() -> Node {
        Node {
            depth: 0,
            parent: Cell::new(None),
        }
    }
}

/// A union-find over `usize` keys that also owns the per-variable data `T`,
/// stored once per node and only ever addressed through a [`Root`].
///
/// Fusing the union-find with its associated storage removes the desync
/// surface between two parallel vectors: there is no way to read a binding at
/// one slot while writing it at another, because the only handle into the data
/// is the `Root` returned by [`find`](Self::find).
#[derive(Clone)]
pub struct UnionFind<T> {
    nodes: Vec<Node>,
    data: Vec<T>,
}

impl<T> UnionFind<T> {
    pub fn new() -> UnionFind<T> {
        UnionFind {
            nodes: vec![],
            data: vec![],
        }
    }

    pub fn find(&self, ident: usize) -> Root {
        // Find root
        let mut j = ident;
        while let Some(p) = self.nodes[j].parent.get() {
            j = p;
        }
        let root = j;
        // Path compression
        let mut j = ident;
        while let Some(p) = self.nodes[j].parent.get() {
            self.nodes[j].parent.set(Some(root));
            j = p;
        }
        Root(root)
    }

    /// The canonical class index of `ident` as a raw `usize`, for read-only
    /// uses (e.g. displaying a residual variable by a stable class id) that do
    /// not address per-variable storage.
    pub fn canonical(&self, ident: usize) -> usize {
        self.find(ident).0
    }

    /// Register a fresh node carrying `datum`, returning its index.
    /// The node is its own root.
    pub fn register(&mut self, datum: T) -> usize {
        let ident = self.nodes.len();
        self.nodes.push(Node::new());
        self.data.push(datum);
        ident
    }

    pub fn get(&self, root: Root) -> &T {
        &self.data[root.0]
    }

    pub fn get_mut(&mut self, root: Root) -> &mut T {
        &mut self.data[root.0]
    }

    pub fn union(&mut self, i: usize, j: usize) {
        let a = self.find(i).0;
        let b = self.find(j).0;
        if a == b {
            return;
        }
        if self.nodes[a].depth > self.nodes[b].depth {
            self.nodes[b].parent.set(Some(a));
        } else if self.nodes[a].depth < self.nodes[b].depth {
            self.nodes[a].parent.set(Some(b));
        } else {
            self.nodes[a].parent.set(Some(b));
            self.nodes[b].depth += 1;
        }
    }
}
