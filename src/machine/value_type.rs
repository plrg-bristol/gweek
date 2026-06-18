//! # Runtime types
//!
//! The runtime type vocabulary, following the CBPV value/computation split. [`ValueType`] is
//! `Unit`, `Nat`, `Product`, `Sum`, `List`, or `Thunk` of a [`ComputationType`]; a
//! [`ComputationType`] is `Return` of a value type (printed `F(t)`) or `Arrow` (printed
//! `a -> b`). Compound cases `Box` their children to stay finite.
//!
//! These are the types a logic variable carries (via `LogicEnv`) so the eliminators know which
//! constructors to guess when splitting an unbound variable. `translate_vtype` produces them
//! from surface types — e.g. `Bool` ↦ `Sum(Unit, Unit)`.

use std::fmt::{self, Display};

#[derive(PartialEq, Clone, Debug)]
pub enum ValueType {
    Unit,
    Nat,
    Product(Box<ValueType>, Box<ValueType>),
    Sum(Box<ValueType>, Box<ValueType>),
    List(Box<ValueType>),
    Thunk(Box<ComputationType>),
}

impl Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueType::Unit => write!(f, "1"),
            ValueType::Nat => write!(f, "Nat"),
            ValueType::List(t) => write!(f, "[{}]", t),
            ValueType::Product(a, b) => write!(f, "{} * {}", a, b),
            ValueType::Sum(a, b) => write!(f, "{} + {}", a, b),
            ValueType::Thunk(c) => write!(f, "U({})", c),
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum ComputationType {
    Return(Box<ValueType>),
    Arrow(Box<ValueType>, Box<ComputationType>),
}

impl Display for ComputationType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ComputationType::Return(t) => write!(f, "F({})", t),
            ComputationType::Arrow(a, b) => write!(f, "{} -> {}", a, b),
        }
    }
}
