use std::fmt::{self, Display};
use std::rc::Rc;

use crate::machine::value_type::ValueType;

#[derive(PartialEq, Clone, Debug)]
pub enum MValue {
    Var(usize),
    Zero,
    Succ(Rc<MValue>),
    Pair(Rc<MValue>, Rc<MValue>),
    Inl(Rc<MValue>),
    Inr(Rc<MValue>),
    Nil,
    Cons(Rc<MValue>, Rc<MValue>),
    Thunk(Rc<MComputation>),
}

impl Display for MValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MValue::Var(i) => write!(f, "idx {}", i),
            MValue::Zero | MValue::Succ(_) => write!(f, "{}", to_nat(self).unwrap()),
            MValue::Nil | MValue::Cons(..) => match to_list(self) {
                Some(items) => write!(f, "[{}]", items.join(", ")),
                None => match self {
                    MValue::Nil => write!(f, "[]"),
                    MValue::Cons(v, w) => write!(f, "({} : {})", v, w),
                    _ => unreachable!(),
                },
            },
            MValue::Thunk(t) => write!(f, "Thunk({})", t),
            MValue::Pair(v, w) => write!(f, "({}, {})", v, w),
            MValue::Inl(v) => write!(f, "inl({})", v),
            MValue::Inr(w) => write!(f, "inr({})", w),
        }
    }
}

fn to_nat(v: &MValue) -> Option<usize> {
    let mut n = 0;
    let mut cur = v;
    loop {
        match cur {
            MValue::Zero => return Some(n),
            MValue::Succ(v) => {
                n += 1;
                cur = v;
            }
            _ => return None,
        }
    }
}

fn to_list(v: &MValue) -> Option<Vec<String>> {
    let mut items = Vec::new();
    let mut cur = v;
    loop {
        match cur {
            MValue::Nil => return Some(items),
            MValue::Cons(head, tail) => {
                items.push(head.to_string());
                cur = tail;
            }
            _ => return None,
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum MComputation {
    // Value eliminators
    Ifz {
        num: Rc<MValue>,
        zk: Rc<MComputation>,
        sk: Rc<MComputation>,
    },
    Match {
        list: Rc<MValue>,
        nilk: Rc<MComputation>,
        consk: Rc<MComputation>,
    },
    Case {
        sum: Rc<MValue>,
        inlk: Rc<MComputation>,
        inrk: Rc<MComputation>,
    },
    // CBPV primitives
    Return(Rc<MValue>),
    Bind {
        comp: Rc<MComputation>,
        cont: Rc<MComputation>,
    },
    Force(Rc<MValue>),
    Lambda {
        body: Rc<MComputation>,
    },
    App {
        op: Rc<MComputation>,
        arg: Rc<MValue>,
    },
    // FLP
    Choice(Vec<Rc<MComputation>>),
    Exists {
        ptype: ValueType,
        body: Rc<MComputation>,
    },
    Equate {
        lhs: Rc<MValue>,
        rhs: Rc<MValue>,
        body: Rc<MComputation>,
    },
    // Recursion
    Rec {
        body: Rc<MComputation>,
    },
}

impl MComputation {
    pub fn thunk(self: &Rc<MComputation>) -> Rc<MValue> {
        MValue::Thunk(self.clone()).into()
    }

    pub fn count_nodes(&self) -> usize {
        match self {
            MComputation::Return(v) => 1 + v.count_nodes(),
            MComputation::Bind { comp, cont } => 1 + comp.count_nodes() + cont.count_nodes(),
            MComputation::Force(v) => 1 + v.count_nodes(),
            MComputation::Lambda { body } => 1 + body.count_nodes(),
            MComputation::App { op, arg } => 1 + op.count_nodes() + arg.count_nodes(),
            MComputation::Choice(cs) => 1 + cs.iter().map(|c| c.count_nodes()).sum::<usize>(),
            MComputation::Exists { body, .. } => 1 + body.count_nodes(),
            MComputation::Equate { lhs, rhs, body } => {
                1 + lhs.count_nodes() + rhs.count_nodes() + body.count_nodes()
            }
            MComputation::Ifz { num, zk, sk } => {
                1 + num.count_nodes() + zk.count_nodes() + sk.count_nodes()
            }
            MComputation::Match { list, nilk, consk } => {
                1 + list.count_nodes() + nilk.count_nodes() + consk.count_nodes()
            }
            MComputation::Case { sum, inlk, inrk } => {
                1 + sum.count_nodes() + inlk.count_nodes() + inrk.count_nodes()
            }
            MComputation::Rec { body } => 1 + body.count_nodes(),
        }
    }
}

impl MValue {
    pub fn count_nodes(&self) -> usize {
        match self {
            MValue::Var(_) | MValue::Zero | MValue::Nil => 1,
            MValue::Succ(v) | MValue::Inl(v) | MValue::Inr(v) => 1 + v.count_nodes(),
            MValue::Pair(a, b) | MValue::Cons(a, b) => 1 + a.count_nodes() + b.count_nodes(),
            MValue::Thunk(c) => 1 + c.count_nodes(),
        }
    }
}

impl Display for MComputation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MComputation::Return(v) => write!(f, "return({})", v),
            MComputation::Bind { comp, cont } => write!(f, "{} to {}", comp, cont),
            MComputation::Force(v) => write!(f, "force({})", v),
            MComputation::Lambda { body } => write!(f, "λ({})", body),
            MComputation::App { op, arg } => write!(f, "{}({})", op, arg),
            MComputation::Choice(vec) => {
                for (i, c) in vec.iter().enumerate() {
                    if i > 0 {
                        write!(f, " [] ")?;
                    }
                    write!(f, "{}", c)?;
                }
                Ok(())
            }
            MComputation::Exists { ptype, body } => write!(f, "exists {}. {}", ptype, body),
            MComputation::Equate { lhs, rhs, body } => {
                write!(f, "{} =:= {}. {}", lhs, rhs, body)
            }
            MComputation::Ifz { num, zk, sk } => write!(f, "ifz({}, {}, {})", num, zk, sk),
            MComputation::Match { list, nilk, consk } => {
                write!(f, "match({}, {}, {})", list, nilk, consk)
            }
            MComputation::Case { sum, inlk, inrk } => {
                write!(f, "case({}, {}, {})", sum, inlk, inrk)
            }
            MComputation::Rec { body } => write!(f, "rec({})", body),
        }
    }
}
