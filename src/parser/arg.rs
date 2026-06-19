//! Function and lambda argument patterns. An [`Arg`] is either a plain identifier or a pair
//! pattern destructuring a product argument.

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Arg {
    Ident(String),
    Pair(Box<Arg>, Box<Arg>),
}
