use std::fmt::{self, Display};

#[derive(PartialEq, Clone, Debug)]
pub enum ValueType {
    Nat,
    Product(Box<ValueType>, Box<ValueType>),
    Sum(Box<ValueType>, Box<ValueType>),
    List(Box<ValueType>),
    Thunk(Box<ComputationType>),
}

impl Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
