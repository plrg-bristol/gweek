use std::rc::Rc;

use crate::machine::value_type::ValueType;

use super::union_find::UnionFind;
use super::{Ident, VClosure};

#[derive(Clone)]
pub struct LogicEnv<'a> {
    entries: Rc<Vec<(ValueType, Option<VClosure<'a>>)>>,
    union_vars: Rc<UnionFind>,
}

impl<'a> LogicEnv<'a> {
    pub fn new() -> LogicEnv<'a> {
        LogicEnv {
            entries: Rc::new(Vec::new()),
            union_vars: Rc::new(UnionFind::new()),
        }
    }

    pub fn fresh(&mut self, ptype: ValueType) -> Ident {
        let next = self.entries.len();
        Rc::make_mut(&mut self.union_vars).register(next);
        Rc::make_mut(&mut self.entries).push((ptype, None));
        next
    }

    pub fn lookup(&self, ident: Ident) -> Option<VClosure<'a>> {
        let root = self.union_vars.find(ident);
        self.entries.get(root)?.1
    }

    pub fn set_vclos(&mut self, ident: Ident, vclos: VClosure<'a>) {
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
