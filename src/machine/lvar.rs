use std::rc::Rc;

use crate::machine::value_type::ValueType;

use super::{env::Env, mterms::MValue, union_find::UnionFind, Ident, VClosure};

#[derive(Clone)]
pub struct LogicEnv {
    entries: Vec<(ValueType, Option<VClosure>)>,
    union_vars: UnionFind,
}

impl LogicEnv {

    pub fn new() -> LogicEnv {
        LogicEnv {
            entries: Vec::new(),
            union_vars: UnionFind::new(),
        }
    }

    pub fn size(&self) -> usize { self.entries.len() }

    pub fn fresh(&mut self, ptype: ValueType) -> Ident {
        let next = self.entries.len();
        self.union_vars.register(next);
        self.entries.push((ptype, None));
        next
    }

    pub fn lookup(&self, ident: Ident) -> Option<VClosure> {
        let root = self.union_vars.find(ident);
        if let Some((_, Some(vclos))) = self.entries.get(root) {
            Some(vclos.clone())
        } else {
            None
        }
    }

    pub fn set_vclos(&mut self, ident: Ident, vclos: VClosure) {
        let ptype = self.get_type(ident);
        self.entries[ident] = (ptype, Some(vclos));
    }

    pub fn get_type(&self, ident: Ident) -> ValueType {
        self.entries[ident].0.clone()
    }

    pub fn identify(&mut self, ident1: Ident, ident2: Ident) {
        self.union_vars.union(ident1, ident2);
    }
}
