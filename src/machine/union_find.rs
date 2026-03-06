use std::cell::Cell;

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

#[derive(Clone)]
pub struct UnionFind {
    array: Vec<Node>,
}

impl UnionFind {
    pub fn new() -> UnionFind {
        UnionFind { array: vec![] }
    }

    pub fn find(&self, i: usize) -> usize {
        // Find root
        let mut j = i;
        while let Some(p) = self.array[j].parent.get() {
            j = p;
        }
        let root = j;
        // Path compression
        let mut j = i;
        while let Some(p) = self.array[j].parent.get() {
            self.array[j].parent.set(Some(root));
            j = p;
        }
        root
    }

    pub fn register(&mut self, i: usize) {
        assert!(i >= self.array.len());
        self.array.resize_with(i + 1, Node::new);
    }

    pub fn union(&mut self, i: usize, j: usize) {
        let a = self.find(i);
        let b = self.find(j);
        if a == b {
            return;
        }
        if self.array[a].depth > self.array[b].depth {
            self.array[b].parent.set(Some(a));
        } else if self.array[a].depth < self.array[b].depth {
            self.array[a].parent.set(Some(b));
        } else {
            self.array[a].parent.set(Some(b));
            self.array[b].depth += 1;
        }
    }
}
