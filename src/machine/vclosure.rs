//! # Value closures
//!
//! A [`VClosure`] is how the machine names a value whose resolution may yet be deferred: a concrete
//! `MValue` in its environment (`Clos`), an unresolved logic variable (`LogicVar`), or a suspension
//! (`Susp`). This indirection is exactly what lets unification and the eliminators discover that
//! what looks like a value is in truth an unknown to branch on, or a thunk to force.
//!
//! Two operations close it. [`close_head`](VClosure::close_head) resolves one level — a pending
//! suspension escapes as `Err(SuspAt)`, prompting a reschedule. [`close`](VClosure::close) resolves
//! fully to a ground [`Closed`] answer, iteratively and under a depth bound, so that a cyclic term
//! — possible only under `--no-occurs-check` — yields [`CyclicTerm`] rather than looping forever.

use std::fmt::{self, Display};

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::MValue;
use super::senv::{SuspAt, SuspEnv};
use super::value_type::ValueType;
use super::{LVar, SuspId};

#[derive(Clone, Copy, Debug)]
pub enum VClosure<'a> {
    Clos { val: &'a MValue<'a>, env: Env<'a> },
    LogicVar { ident: LVar },
    Susp { ident: SuspId },
}

/// A fully-resolved answer term, ready for printing.
///
/// Mirrors the printable shape of `MValue` but additionally carries `Free`
/// placeholders for residual logic variables that the search left unbound
/// (printed as `_<id>`), so that solutions mentioning a free variable are
/// still reported rather than silently dropped.
#[derive(Clone, Debug)]
pub enum Closed {
    Free(LVar),
    Unit,
    Nat(u64),
    Succ(Box<Closed>),
    Pair(Box<Closed>, Box<Closed>),
    Inl(Box<Closed>),
    Inr(Box<Closed>),
    Nil,
    Cons(Box<Closed>, Box<Closed>),
}

/// Returned when an answer term cannot be printed because it is infinite,
/// which can only arise with `--no-occurs-check` (cyclic bindings).
#[derive(Debug)]
pub struct CyclicTerm;

/// Maximum nesting depth for `close`. Beyond this we assume the term is
/// cyclic (only reachable with the occurs check disabled) and refuse to print.
/// `close` itself is iterative so this is purely a guard against unbounded
/// cyclic terms; set far above any finite answer a program could produce.
const MAX_CLOSE_DEPTH: usize = 1 << 16;

impl Display for Closed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Closed::Free(id) => write!(f, "_{}", id.0),
            Closed::Unit => write!(f, "()"),
            Closed::Nat(n) => write!(f, "{}", n),
            Closed::Succ(_) => match self.to_nat() {
                Some(n) => write!(f, "{}", n),
                None => {
                    let Closed::Succ(v) = self else { unreachable!() };
                    write!(f, "S ({})", v)
                }
            },
            Closed::Nil => write!(f, "[]"),
            Closed::Cons(..) => match self.to_list() {
                Some(items) => write!(f, "[{}]", items.join(", ")),
                None => {
                    let Closed::Cons(v, w) = self else { unreachable!() };
                    write!(f, "({} : {})", v, w)
                }
            },
            Closed::Pair(v, w) => write!(f, "({}, {})", v, w),
            Closed::Inl(v) => match **v {
                Closed::Unit => write!(f, "true"),
                _ => write!(f, "inl({})", v),
            },
            Closed::Inr(w) => match **w {
                Closed::Unit => write!(f, "false"),
                _ => write!(f, "inr({})", w),
            },
        }
    }
}

impl Closed {
    fn to_nat(&self) -> Option<u64> {
        let mut n: u64 = 0;
        let mut cur = self;
        loop {
            match cur {
                Closed::Nat(k) => return Some(n + k),
                Closed::Succ(v) => {
                    n += 1;
                    cur = v;
                }
                _ => return None,
            }
        }
    }

    fn to_list(&self) -> Option<Vec<String>> {
        let mut items = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Closed::Nil => return Some(items),
                Closed::Cons(head, tail) => {
                    items.push(head.to_string());
                    cur = tail;
                }
                _ => return None,
            }
        }
    }
}

impl<'a> VClosure<'a> {
    pub fn mk_clos(val: &'a MValue<'a>, env: Env<'a>) -> VClosure<'a> {
        VClosure::Clos { val, env }
    }

    pub fn occurs_lvar(
        &self,
        lenv: &LogicEnv<'a>,
        senv: &SuspEnv<'a>,
        ident: LVar,
    ) -> Result<bool, SuspAt<'a>> {
        match self.close_head(lenv, senv)? {
            VClosure::Clos { val, env } => match val {
                MValue::Succ(v) => VClosure::mk_clos(v, env).occurs_lvar(lenv, senv, ident),
                MValue::Cons(v, w) => Ok(
                    VClosure::mk_clos(v, env).occurs_lvar(lenv, senv, ident)?
                        || VClosure::mk_clos(w, env).occurs_lvar(lenv, senv, ident)?,
                ),
                MValue::Pair(a, b) => Ok(
                    VClosure::mk_clos(a, env).occurs_lvar(lenv, senv, ident)?
                        || VClosure::mk_clos(b, env).occurs_lvar(lenv, senv, ident)?,
                ),
                MValue::Inl(v) | MValue::Inr(v) => {
                    VClosure::mk_clos(v, env).occurs_lvar(lenv, senv, ident)
                }
                MValue::Var(_) => unreachable!("value should be head-closed in occurs check"),
                MValue::Thunk(_) => panic!("occurs check on a computation"),
                MValue::Unit | MValue::Zero | MValue::Nil | MValue::Nat(_) => Ok(false),
            },
            VClosure::LogicVar { ident: ident2 } => Ok(ident == ident2),
            // `close_head` propagates a pending suspension via `?`, so it never
            // returns one here; the occurs check only sees resolved values.
            VClosure::Susp { .. } => unreachable!("occurs check on a suspension"),
        }
    }

    pub fn close_head(self, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Result<VClosure<'a>, SuspAt<'a>> {
        let mut vclos = self;
        loop {
            vclos = match &vclos {
                VClosure::Clos { val, env } => match val {
                    MValue::Var(i) => env.lookup(*i).expect("index undefined in env"),
                    _ => break,
                },
                VClosure::LogicVar { ident } => match lenv.lookup(*ident) {
                    Some(vclos) => vclos,
                    None => break,
                },
                VClosure::Susp { ident } => senv.lookup(ident)?,
            }
        }
        Ok(vclos)
    }

    /// Fully resolve a value closure into a printable `Closed` term.
    ///
    /// Implemented with an explicit work stack rather than native recursion so
    /// that the depth bound (against cyclic terms admitted by
    /// `--no-occurs-check`) is enforced regardless of stack-frame size.
    pub fn close(&self, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Result<Closed, CyclicTerm> {
        // Post-order traversal: `work` holds the tasks still to process,
        // `out` accumulates finished subterms. A `Combine` task pops its
        // children off `out` and pushes the assembled node.
        let mut work: Vec<Task<'a>> = vec![Task::Resolve(*self, 0)];
        let mut out: Vec<Closed> = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Task::Resolve(vclos, depth) => {
                    if depth > MAX_CLOSE_DEPTH {
                        return Err(CyclicTerm);
                    }
                    match vclos {
                        VClosure::Clos { val, env } => match val {
                            MValue::Var(i) => {
                                let r = env.lookup(*i).expect("index undefined in env");
                                work.push(Task::Resolve(r, depth));
                            }
                            MValue::Unit => out.push(Closed::Unit),
                            MValue::Nat(n) => out.push(Closed::Nat(*n)),
                            MValue::Zero => out.push(Closed::Nat(0)),
                            MValue::Succ(v) => {
                                work.push(Task::Combine(Combine::Succ));
                                work.push(Task::Resolve(VClosure::mk_clos(v, env), depth + 1));
                            }
                            MValue::Nil => out.push(Closed::Nil),
                            MValue::Cons(v, w) => {
                                work.push(Task::Combine(Combine::Cons));
                                work.push(Task::Resolve(VClosure::mk_clos(w, env), depth + 1));
                                work.push(Task::Resolve(VClosure::mk_clos(v, env), depth + 1));
                            }
                            MValue::Pair(fst, snd) => {
                                work.push(Task::Combine(Combine::Pair));
                                work.push(Task::Resolve(VClosure::mk_clos(snd, env), depth + 1));
                                work.push(Task::Resolve(VClosure::mk_clos(fst, env), depth + 1));
                            }
                            MValue::Inl(v) => {
                                work.push(Task::Combine(Combine::Inl));
                                work.push(Task::Resolve(VClosure::mk_clos(v, env), depth + 1));
                            }
                            MValue::Inr(v) => {
                                work.push(Task::Combine(Combine::Inr));
                                work.push(Task::Resolve(VClosure::mk_clos(v, env), depth + 1));
                            }
                            MValue::Thunk(t) => panic!("tried to close thunk: {}", t),
                        },
                        VClosure::LogicVar { ident } => match lenv.lookup(ident) {
                            Some(inner) => work.push(Task::Resolve(inner, depth)),
                            None => {
                                if lenv.get_type(ident) == ValueType::Unit {
                                    out.push(Closed::Unit);
                                } else {
                                    out.push(Closed::Free(lenv.root(ident)));
                                }
                            }
                        },
                        VClosure::Susp { ident } => {
                            let inner = senv.lookup(&ident).expect("unexpected suspension");
                            work.push(Task::Resolve(inner, depth));
                        }
                    }
                }
                Task::Combine(c) => {
                    let node = match c {
                        Combine::Succ => match out.pop().unwrap() {
                            Closed::Nat(n) => Closed::Nat(n + 1),
                            inner => Closed::Succ(Box::new(inner)),
                        },
                        Combine::Cons => {
                            let w = out.pop().unwrap();
                            let v = out.pop().unwrap();
                            Closed::Cons(Box::new(v), Box::new(w))
                        }
                        Combine::Pair => {
                            let snd = out.pop().unwrap();
                            let fst = out.pop().unwrap();
                            Closed::Pair(Box::new(fst), Box::new(snd))
                        }
                        Combine::Inl => Closed::Inl(Box::new(out.pop().unwrap())),
                        Combine::Inr => Closed::Inr(Box::new(out.pop().unwrap())),
                    };
                    out.push(node);
                }
            }
        }
        debug_assert_eq!(out.len(), 1);
        Ok(out.pop().unwrap())
    }
}

enum Task<'a> {
    Resolve(VClosure<'a>, usize),
    Combine(Combine),
}

enum Combine {
    Succ,
    Cons,
    Pair,
    Inl,
    Inr,
}
