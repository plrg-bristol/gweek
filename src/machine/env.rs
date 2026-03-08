use std::rc::Rc;

use super::mterms::MValue;
use super::{Ident, VClosure};

/// Optimize every function in the environment, rebuilding closure chains so
/// that each function's closure env contains already-optimized predecessors.
pub fn map_env_vals<F: Fn(&Rc<MValue>) -> Rc<MValue>>(env: &Env, f: &F) -> Env {
    // Collect entries oldest-first so we can rebuild in the right order.
    let mut entries = Vec::new();
    env.collect_entries(&mut entries);
    let mut new_env = Env::empty();
    for vc in entries {
        match &vc {
            VClosure::Clos { val, .. } => {
                new_env = new_env.extend_val(f(val), new_env.clone());
            }
            VClosure::LogicVar { ident } => {
                new_env = new_env.extend_lvar(*ident);
            }
            VClosure::Susp { ident } => {
                new_env = new_env.extend_susp(*ident);
            }
        }
    }
    new_env
}

#[derive(Debug)]
enum EnvInner {
    Nil,
    Cons(VClosure, Env),
}

/// Persistent cons-list environment. Clone is O(1) (Rc bump).
#[derive(Clone, Debug)]
pub struct Env(Rc<EnvInner>);

impl Env {
    pub fn empty() -> Env {
        Env(Rc::new(EnvInner::Nil))
    }

    pub fn lookup(&self, i: usize) -> Option<VClosure> {
        let mut cur = self;
        let mut remaining = i;
        loop {
            match &*cur.0 {
                EnvInner::Nil => return None,
                EnvInner::Cons(vc, tail) => {
                    if remaining == 0 {
                        return Some(vc.clone());
                    }
                    remaining -= 1;
                    cur = tail;
                }
            }
        }
    }

    pub fn extend_val(&self, val: Rc<MValue>, env: Env) -> Env {
        Env(Rc::new(EnvInner::Cons(VClosure::Clos { val, env }, self.clone())))
    }

    pub fn extend_lvar(&self, ident: Ident) -> Env {
        Env(Rc::new(EnvInner::Cons(VClosure::LogicVar { ident }, self.clone())))
    }

    pub fn extend_susp(&self, ident: Ident) -> Env {
        Env(Rc::new(EnvInner::Cons(VClosure::Susp { ident }, self.clone())))
    }

    /// Collect entries oldest-first (tail to head).
    fn collect_entries(&self, out: &mut Vec<VClosure>) {
        match &*self.0 {
            EnvInner::Nil => {}
            EnvInner::Cons(vc, tail) => {
                tail.collect_entries(out);
                out.push(vc.clone());
            }
        }
    }

    /// Count total IR nodes across all function definitions (top-level vals only).
    #[cfg(feature = "opt-stats")]
    pub fn count_nodes(&self) -> usize {
        let mut total = 0;
        let mut cur = self;
        loop {
            match &*cur.0 {
                EnvInner::Nil => return total,
                EnvInner::Cons(vc, tail) => {
                    if let VClosure::Clos { val, .. } = vc {
                        total += val.count_nodes();
                    }
                    cur = tail;
                }
            }
        }
    }
}
