use std::rc::Rc;
use super::Ident;
use super::{mterms::MValue, VClosure};

#[derive(Clone, Debug)]
pub struct Env {
    vec : Vec<VClosure>
}

impl Env {

    pub fn empty() -> Rc<Env> {
        Env { vec : Vec::new() }.into()
    }

    pub fn lookup(&self, i : usize) -> Option<VClosure> {
        let len = self.vec.len();
        if i < len {
            Some(self.vec[len - 1 - i].clone())
        } else {
            None
        }
    }

    pub fn size(&self) -> usize { self.vec.len() }

    fn extend(&self, vclos : VClosure) -> Env {
        let mut vec = self.vec.clone();
        vec.push(vclos);
        Env { vec }
    }

    pub fn extend_val(&self, val : Rc<MValue>, env : Rc<Env>) -> Rc<Env> {
        self.extend( VClosure::Clos { val, env }).into()
    }

    pub fn extend_lvar(&self, ident : Ident) -> Rc<Env> {
        self.extend(VClosure::LogicVar { ident }).into()
    }

    pub fn extend_susp(&self, ident : Ident) -> Rc<Env> {
        self.extend(VClosure::Susp { ident }).into()
    }
}