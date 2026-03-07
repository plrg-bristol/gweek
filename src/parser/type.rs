#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Ident(String),
    List(Box<Type>),
    Product(Box<Type>, Box<Type>),
    Any,
}