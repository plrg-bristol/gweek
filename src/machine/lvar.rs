use std::rc::Rc;

use crate::machine::value_type::ValueType;

use super::{env::Env, mterms::MValue, union_find::UnionFind, Ident, VClosure};

#[derive(Clone)]
pub struct LogicEnv {
    entries: Rc<Vec<(ValueType, Option<VClosure>)>>,
    union_vars: Rc<UnionFind>,
}

impl LogicEnv {

    pub fn new() -> LogicEnv {
        LogicEnv {
            entries: Rc::new(Vec::new()),
            union_vars: Rc::new(UnionFind::new()),
        }
    }

    pub fn size(&self) -> usize { self.entries.len() }

    pub fn fresh(&mut self, ptype: ValueType) -> Ident {
        let next = self.entries.len();
        Rc::make_mut(&mut self.union_vars).register(next);
        Rc::make_mut(&mut self.entries).push((ptype, None));
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
        Rc::make_mut(&mut self.entries)[ident] = (ptype, Some(vclos));
    }

    pub fn get_type(&self, ident: Ident) -> ValueType {
        self.entries[ident].0.clone()
    }

    pub fn identify(&mut self, ident1: Ident, ident2: Ident) {
        Rc::make_mut(&mut self.union_vars).union(ident1, ident2);
    }
}
