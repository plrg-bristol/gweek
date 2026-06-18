//! # The logic-variable environment
//!
//! [`LogicEnv`] is the store of logic-variable bindings and equivalence classes. It wraps an
//! `Rc<UnionFind>` whose per-variable datum is `(ValueType, Option<VClosure>)` — the variable's
//! declared type plus its binding, if any. The `Rc` gives copy-on-write semantics so branching
//! clones the store cheaply; the first mutation of a shared clone deep-copies it.
//!
//! - [`fresh`](LogicEnv::fresh) registers a new unbound variable of a given type (called by
//!   `Exists` and the case-split branches).
//! - [`lookup`](LogicEnv::lookup) / [`set_vclos`](LogicEnv::set_vclos) read and write a binding,
//!   [`get_type`](LogicEnv::get_type) reads the stored type, and [`identify`](LogicEnv::identify)
//!   unions two classes when two unbound variables meet.
//! - [`root`](LogicEnv::root) returns the canonical representative, so a unified class renders as
//!   a single residual placeholder.
//!
//! **Invariant:** every read and write canonicalizes through the union-find root. This is what
//! makes binding sound — a constraint on any member of a class is visible through all of them —
//! and the [`Root`](super::union_find::Root) token enforces it by construction, so a write
//! physically cannot land in a non-root slot.

use std::rc::Rc;

use crate::machine::value_type::ValueType;

use super::union_find::UnionFind;
use super::{LVar, VClosure};

#[derive(Clone)]
pub struct LogicEnv<'a> {
    store: Rc<UnionFind<(ValueType, Option<VClosure<'a>>)>>,
}

impl<'a> LogicEnv<'a> {
    pub fn new() -> LogicEnv<'a> {
        LogicEnv {
            store: Rc::new(UnionFind::new()),
        }
    }

    pub fn fresh(&mut self, ptype: ValueType) -> LVar {
        LVar(Rc::make_mut(&mut self.store).register((ptype, None)))
    }

    pub fn lookup(&self, ident: LVar) -> Option<VClosure<'a>> {
        let root = self.store.find(ident.0);
        self.store.get(root).1
    }

    pub fn set_vclos(&mut self, ident: LVar, vclos: VClosure<'a>) {
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

    /// The canonical logic variable of `ident`'s equivalence class, so that
    /// distinct-but-unified variables share one identity when a residual free
    /// variable is displayed.
    pub fn root(&self, ident: LVar) -> LVar {
        LVar(self.store.canonical(ident.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::env::Env;
    use crate::machine::mterms::MValue;
    use bumpalo::Bump;

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
        let arena = Bump::new();

        let mut lenv = LogicEnv::new();
        let a = lenv.fresh(ValueType::Nat);
        let b = lenv.fresh(ValueType::Nat);

        lenv.identify(a, b);

        let three = arena.alloc(MValue::Nat(3));
        let vclos = VClosure::mk_clos(three, Env::empty(&arena));
        // `a` is the non-root member of {a, b} after the union above.
        lenv.set_vclos(a, vclos);

        // The binding must be visible through both idents.
        assert!(
            matches!(lenv.lookup(a), Some(VClosure::Clos { val: MValue::Nat(3), .. })),
            "binding lost when looked up via the non-root ident"
        );
        assert!(
            matches!(lenv.lookup(b), Some(VClosure::Clos { val: MValue::Nat(3), .. })),
            "binding lost when looked up via the root ident"
        );

        // The type must remain consistent across the whole class.
        assert_eq!(lenv.get_type(a), ValueType::Nat);
        assert_eq!(lenv.get_type(b), ValueType::Nat);
    }
}
