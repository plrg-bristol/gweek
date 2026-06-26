//! # The logic variable environment
//!
//! [`LogicEnv`] maps every logical variable to its type, and potentially a value closure if it has
//! been resolved.
//!
//! [`fresh`](LogicEnv::fresh) introduces an unbound variable of a given type;
//! [`lookup`](LogicEnv::lookup) and [`set_vclos`](LogicEnv::set_vclos) read and write its binding;
//! [`identify`](LogicEnv::identify) unifies two logical variables, making them indistinguishable.
//! [`canonical`](LogicEnv::canonical) returns the canonical logical variable in the same
//! equivalence class; it is only used for printing.
//!
//! The equivalence classes of logical variables are implemented by an `Rc<UnionFind>`, which is
//! copy-on-write so that a nondeterministic branch can clone them cheaply, paying only when they
//! make changes.

use std::rc::Rc;

use crate::machine::value_type::ValueType;

use super::heap::Heap;
use super::union_find::UnionFind;
use super::{LVar, VClosure};

#[derive(Clone)]
pub struct LogicEnv {
    store: Rc<UnionFind<(ValueType, Option<VClosure>)>>,
}

impl LogicEnv {
    pub fn new() -> LogicEnv {
        LogicEnv {
            store: Rc::new(UnionFind::new()),
        }
    }

    pub fn fresh(&mut self, ptype: ValueType) -> LVar {
        LVar(Rc::make_mut(&mut self.store).register((ptype, None)))
    }

    pub fn lookup(&self, ident: LVar) -> Option<VClosure> {
        let root = self.store.find(ident.0);
        self.store.get(root).1
    }

    pub fn set_vclos(&mut self, ident: LVar, vclos: VClosure) {
        let store = Rc::make_mut(&mut self.store);
        let root = store.find(ident.0);
        store.get_mut(root).1 = Some(vclos);
    }

    pub fn get_type(&self, ident: LVar) -> ValueType {
        let root = self.store.find(ident.0);
        self.store.get(root).0.clone()
    }

    pub fn identify(&mut self, ident1: LVar, ident2: LVar) {
        Rc::make_mut(&mut self.store).union(ident1.0, ident2.0);
    }

    pub fn canonical(&self, ident: LVar) -> LVar {
        LVar(self.store.canonical(ident.0))
    }

    /// Identity of the shared store, so a collection can rebuild each distinct
    /// `LogicEnv` once and share it back across the machines that aliased it.
    pub(crate) fn store_ptr(&self) -> usize {
        Rc::as_ptr(&self.store) as *const () as usize
    }

    /// Rebuild every stored value closure against the new heap during a
    /// collection, returning a fresh store the survivors can share.
    pub(crate) fn forwarded(&self, heap: &mut Heap) -> LogicEnv {
        let mut store = (*self.store).clone();
        for (_, binding) in store.data_mut() {
            if let Some(vc) = binding {
                *vc = (*vc).forward(heap);
            }
        }
        LogicEnv {
            store: Rc::new(store),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::env::Env;
    use crate::machine::mterms::MValue;

    /// Regression for B1: binding a *non-root* member of a merged class must be
    /// visible through every ident in that class.
    ///
    /// On the buggy code (`set_vclos` writing at the raw ident while `lookup`
    /// reads at the root) the binding placed on the non-root ident was written
    /// to a slot nobody reads, so both lookups returned `None` and the
    /// constraint was silently lost. `union` makes its second argument the root
    /// on equal rank, so binding the *first* ident exercises the non-root write.
    #[test]
    fn binding_non_root_is_visible_through_class() {
        let mut heap = Heap::new();

        let mut lenv = LogicEnv::new();
        let a = lenv.fresh(ValueType::Nat);
        let b = lenv.fresh(ValueType::Nat);

        lenv.identify(a, b);

        let three = heap.alloc_imm_val(MValue::Nat(3));
        let empty = Env::empty(&mut heap);
        let vclos = VClosure::mk_clos(three, empty);
        // `a` is the non-root member of {a, b} after the union above.
        lenv.set_vclos(a, vclos);

        // The binding must be visible through both idents.
        assert!(
            matches!(lenv.lookup(a), Some(VClosure::Clos { val, .. }) if heap.val(val) == MValue::Nat(3)),
            "binding lost when looked up via the non-root ident"
        );
        assert!(
            matches!(lenv.lookup(b), Some(VClosure::Clos { val, .. }) if heap.val(val) == MValue::Nat(3)),
            "binding lost when looked up via the root ident"
        );

        // The type must remain consistent across the whole class.
        assert_eq!(lenv.get_type(a), ValueType::Nat);
        assert_eq!(lenv.get_type(b), ValueType::Nat);
    }
}
