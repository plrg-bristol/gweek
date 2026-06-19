//! # The logic-variable environment
//!
//! [`LogicEnv`] is the store of logic-variable bindings and their equivalence classes: an
//! `Rc<UnionFind>` whose per-variable datum is `(ValueType, Option<VClosure>)`, copy-on-write so
//! that branching clones it cheaply. [`fresh`](LogicEnv::fresh) introduces an unbound variable and
//! [`identify`](LogicEnv::identify) merges two classes when they meet.
//!
//! The one invariant on which soundness rests: every read and write canonicalises through the
//! union-find root, so a constraint placed on any member of a class is seen by all of them. The
//! [`Root`](super::union_find::Root) token enforces this — a write cannot land anywhere else.

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
