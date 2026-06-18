//! Surface types. A [`Type`] is an arrow, an identifier (`Nat`, `Bool`, a type variable, …), a
//! list, a product, or [`Any`](Type::Any), the wildcard for unannotated positions. `*` binds
//! tighter than `->`.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Ident(String),
    List(Box<Type>),
    Product(Box<Type>, Box<Type>),
    Any,
}