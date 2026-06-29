//! # The transition function
//!
//! The heart of the interpreter: a single machine state ([`Machine`]) and the transition that
//! advances it. A [`Machine`] bundles the running computation closure and a [`Stack`] of continuation
//! frames; the logic and suspension environments are now owned by the [`Branch`](super::branch::Branch)
//! and passed in by mutable reference. The stack is a persistent heap cons-list, so
//! cloning it is one handle copy.
//!
//! Each `step` matches on the head computation — sequencing, functions, the functional-logic forms,
//! the eliminators (which *case-split* on an unbound logic variable), and `Rec` — and reads the
//! deadline through a `Clock` only once every 1024 ticks, lest a divergent loop never look at it.

use smallvec::SmallVec;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use super::branch::Alt;
use super::config::Config;
use super::heap::{CompId, Heap};
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::{SuspEnv, SuspState};
use super::unify::{unify, UnifyError};
use super::value_type::ValueType;
use super::{CClosure, Env, NodeId, SuspId, VClosure};

// ── Stack ──────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
pub(crate) enum StkFrame {
    Value(NodeId),
    To(CompId),
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum StackInner {
    Nil,
    Cons(StkClosure, Stack),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct StkClosure {
    pub frame: StkFrame,
    pub env: Env,
}

#[derive(Clone, Copy)]
pub struct Stack(pub(crate) NodeId);

impl std::fmt::Debug for Stack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Stack(...)")
    }
}

impl Stack {
    pub fn empty(heap: &mut Heap) -> Stack {
        heap.alloc_stack(StackInner::Nil)
    }

    pub(crate) fn push(&self, heap: &mut Heap, frame: StkFrame, env: Env) -> Stack {
        heap.alloc_stack(StackInner::Cons(StkClosure { frame, env }, *self))
    }
}

// ── Machine ────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Machine {
    pub cclos: CClosure,
    pub stack: Stack,
}

// ── Clock ──────────────────────────────────────────────────────────

/// Polls a deadline cheaply from a hot loop.
pub(super) struct Clock {
    iters: u32,
    deadline: Instant,
}

impl Clock {
    const POLL_INTERVAL: u32 = 1024;

    pub(super) fn new(deadline: Instant) -> Self {
        Clock { iters: 0, deadline }
    }

    pub(super) fn expired(&mut self) -> bool {
        self.iters = self.iters.wrapping_add(1);
        self.iters & (Self::POLL_INTERVAL - 1) == 0 && Instant::now() >= self.deadline
    }
}

// ── Event ──────────────────────────────────────────────────────────

/// Events that a Machine can emit after running deterministic steps.
pub(crate) enum Event {
    /// The machine reached a value with an empty stack.
    Ret(VClosure),
    /// The machine failed (e.g. unification failure, empty Choice).
    Fail,
    /// Object-language nondeterminism (Choice) or logic-variable case split.
    Split(Vec<Alt>),
    /// A need-obligation has been created (fresh suspension registered).
    Need(SuspId),
    /// The machine is blocked waiting for a suspension to complete.
    Wait(SuspId),
    /// The heap nursery is full and wants collection.
    Gc,
    /// The deadline elapsed mid-computation.
    Timeout,
}

// ── run ─────────────────────────────────────────────────────────────

impl Machine {
    /// Run deterministic steps in a tight loop, returning at the next
    /// significant event (branch point, completion, block, timeout, or GC).
    pub(crate) fn run(
        &mut self,
        heap: &mut Heap,
        lenv: &mut LogicEnv,
        senv: &mut SuspEnv,
        cfg: &Config,
        deadline: Instant,
    ) -> Event {
        let mut clock = Clock::new(deadline);
        loop {
            if clock.expired() {
                return Event::Timeout;
            }
            if heap.nursery_full() {
                return Event::Gc;
            }
            match self.step(cfg, heap, lenv, senv) {
                None => {} // continue — self already updated
                Some(event) => return event,
            }
        }
    }

    fn step(
        &mut self,
        cfg: &Config,
        heap: &mut Heap,
        lenv: &mut LogicEnv,
        senv: &mut SuspEnv,
    ) -> Option<Event> {
        let (comp_id, env) = self.cclos;

        match heap.comp(comp_id) {
            // ── Return ──────────────────────────────────────────
            MComputation::Return(val) => {
                let val = *val;
                match heap.stack_inner(self.stack) {
                    StackInner::Nil => {
                        return Some(Event::Ret(VClosure::mk_clos(val, env)));
                    }
                    StackInner::Cons(sc, tail) => match sc.frame {
                        StkFrame::Value(_) => {
                            unreachable!("return throws value to a value")
                        }
                        StkFrame::To(cont) => {
                            let new_env = sc.env.extend_val(heap, val, env);
                            self.cclos = (cont, new_env);
                            self.stack = tail;
                            None
                        }
                    },
                }
            }

            // ── Bind ────────────────────────────────────────────
            MComputation::Bind { comp: inner, cont } => {
                let inner = *inner;
                let cont = *cont;
                let inner_ret = if let MComputation::Return(v) = heap.comp(inner) {
                    Some(*v)
                } else {
                    None
                };
                match inner_ret {
                    Some(v) => {
                        let new_env = env.extend_val(heap, v, env);
                        self.cclos = (cont, new_env);
                        None
                    }
                    None => {
                        let new_stack = self.stack.push(heap, StkFrame::To(cont), env);
                        self.cclos = (inner, env);
                        self.stack = new_stack;
                        None
                    }
                }
            }

            // ── Need ────────────────────────────────────────────
            MComputation::Need { comp: inner, cont } => {
                let inner = *inner;
                let cont = *cont;
                let inner_ret = if let MComputation::Return(v) = heap.comp(inner) {
                    Some(*v)
                } else {
                    None
                };
                match inner_ret {
                    Some(v) => {
                        let new_env = env.extend_val(heap, v, env);
                        self.cclos = (cont, new_env);
                        None
                    }
                    None => {
                        let ident = senv.fresh((inner, env));
                        let new_env = env.extend_susp(heap, ident);
                        self.cclos = (cont, new_env);
                        return Some(Event::Need(ident));
                    }
                }
            }

            // ── Lambda ──────────────────────────────────────────
            MComputation::Lambda { body } => {
                let body = *body;
                match heap.stack_inner(self.stack) {
                    StackInner::Cons(sc, tail) => match sc.frame {
                        StkFrame::Value(arg) => {
                            let new_env = env.extend_val(heap, arg, sc.env);
                            self.cclos = (body, new_env);
                            self.stack = tail;
                            None
                        }
                        _ => panic!("lambda but no value on the stack"),
                    },
                    StackInner::Nil => panic!("lambda met with empty stack"),
                }
            }

            // ── App ─────────────────────────────────────────────
            MComputation::App { op, arg } => {
                let op = *op;
                let arg = *arg;
                let new_stack = self.stack.push(heap, StkFrame::Value(arg), env);
                self.cclos = (op, env);
                self.stack = new_stack;
                None
            }

            // ── Choice ──────────────────────────────────────────
            MComputation::Choice(choices) => {
                let choices: SmallVec<[CompId; 4]> = choices.iter().copied().collect();
                let n = choices.len();
                if n == 0 {
                    return Some(Event::Fail);
                }
                if n == 1 {
                    self.cclos = (choices[0], env);
                    return None;
                }
                let mut alternatives = Vec::with_capacity(n);
                for c in choices.iter() {
                    let m = Machine {
                        cclos: (*c, env),
                        stack: self.stack,
                    };
                    alternatives.push(Alt {
                        machine: m,
                        lenv: lenv.clone(),
                        senv: senv.clone(),
                    });
                }
                return Some(Event::Split(alternatives));
            }

            // ── Exists ──────────────────────────────────────────
            MComputation::Exists { ptype, body } => {
                let ptype = ptype.clone();
                let body = *body;
                let ident = lenv.fresh(ptype);
                let new_env = env.extend_lvar(heap, ident);
                self.cclos = (body, new_env);
                None
            }

            // ── Equate ──────────────────────────────────────────
            MComputation::Equate { lhs, rhs, body } => {
                let lhs = *lhs;
                let rhs = *rhs;
                let body = *body;
                match unify(cfg, heap, lhs, rhs, env, lenv, senv) {
                    Ok(()) => {
                        self.cclos = (body, env);
                        None
                    }
                    Err(UnifyError::Susp(a)) => match senv.get(a.ident) {
                        SuspState::Susp(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Run(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Done(_) => unreachable!("suspension already done"),
                    },
                    Err(_) => return Some(Event::Fail),
                }
            }

            // ── Force ───────────────────────────────────────────
            MComputation::Force(v) => {
                let v = *v;
                let vclos = VClosure::Clos { val: v, env };
                match vclos.close_head(heap, lenv, senv) {
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Thunk(t) => {
                            self.cclos = (t, cenv);
                            None
                        }
                        _ => panic!("forcing a non-thunk value"),
                    },
                    Ok(VClosure::LogicVar { .. }) => panic!("forcing a logic variable"),
                    Ok(VClosure::Susp { .. }) => unreachable!("forcing a suspension"),
                    Err(a) => match senv.get(a.ident) {
                        SuspState::Susp(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Run(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Done(_) => unreachable!("suspension already done"),
                    },
                }
            }

            // ── Ifz ─────────────────────────────────────────────
            MComputation::Ifz { num, zk, sk } => {
                let num = *num;
                let zk = *zk;
                let sk = *sk;
                let vclos = VClosure::mk_clos(num, env);
                match vclos.close_head(heap, lenv, senv) {
                    Err(a) => match senv.get(a.ident) {
                        SuspState::Susp(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Run(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Done(_) => unreachable!("suspension already done"),
                    },
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Zero | MValue::Nat(0) => {
                            self.cclos = (zk, env);
                            None
                        }
                        MValue::Succ(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            self.cclos = (sk, new_env);
                            None
                        }
                        MValue::Nat(n) if n > 0 => {
                            let v = heap.alloc_val(MValue::Nat(n - 1));
                            let new_env = env.extend_val(heap, v, cenv);
                            self.cclos = (sk, new_env);
                            None
                        }
                        other => panic!("Ifz on {:?}", other),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let empty = Env::empty(heap);
                        let zero_val = heap.alloc_val(MValue::Nat(0));
                        let (m_zero, lenv_z) = {
                            let mut lz = lenv.clone();
                            lz.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: zero_val,
                                    env: empty,
                                },
                            );
                            let m = Machine {
                                cclos: (zk, env),
                                stack: self.stack,
                            };
                            (m, lz)
                        };
                        let (m_succ, lenv_s) = {
                            let mut ls = lenv.clone();
                            let fresh = ls.fresh(ValueType::Nat);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let succ_val = heap.alloc_val(MValue::Succ(var0));
                            ls.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: succ_val,
                                    env: empty.extend_lvar(heap, fresh),
                                },
                            );
                            let new_env = env.extend_lvar(heap, fresh);
                            let m = Machine {
                                cclos: (sk, new_env),
                                stack: self.stack,
                            };
                            (m, ls)
                        };
                        return Some(Event::Split(vec![
                            Alt {
                                machine: m_zero,
                                lenv: lenv_z,
                                senv: senv.clone(),
                            },
                            Alt {
                                machine: m_succ,
                                lenv: lenv_s,
                                senv: senv.clone(),
                            },
                        ]));
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            // ── Match ───────────────────────────────────────────
            MComputation::Match { list, nilk, consk } => {
                let list = *list;
                let nilk = *nilk;
                let consk = *consk;
                let vclos = VClosure::mk_clos(list, env);
                match vclos.close_head(heap, lenv, senv) {
                    Err(a) => match senv.get(a.ident) {
                        SuspState::Susp(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Run(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Done(_) => unreachable!("suspension already done"),
                    },
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Nil => {
                            self.cclos = (nilk, env);
                            None
                        }
                        MValue::Cons(v, w) => {
                            let new_env = env.extend_val(heap, v, cenv).extend_val(heap, w, cenv);
                            self.cclos = (consk, new_env);
                            None
                        }
                        _ => panic!("Match on non-list"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let ptype = match lenv.get_type(ident) {
                            ValueType::List(t) => t,
                            _ => panic!("matching on a non-list logic variable"),
                        };
                        let empty = Env::empty(heap);
                        let (m_nil, lenv_n) = {
                            let mut ln = lenv.clone();
                            let nil_val = heap.alloc_val(MValue::Nil);
                            ln.set_vclos(ident, VClosure::mk_clos(nil_val, empty));
                            let m = Machine {
                                cclos: (nilk, env),
                                stack: self.stack,
                            };
                            (m, ln)
                        };
                        let (m_cons, lenv_c) = {
                            let mut lc = lenv.clone();
                            let fresh_hd = lc.fresh((*ptype).clone());
                            let fresh_tl = lc.fresh(ValueType::List(ptype));
                            let var_hd = heap.alloc_val(MValue::Var(1));
                            let var_tl = heap.alloc_val(MValue::Var(0));
                            let cons_val = heap.alloc_val(MValue::Cons(var_hd, var_tl));
                            let clos_env = empty
                                .extend_lvar(heap, fresh_hd)
                                .extend_lvar(heap, fresh_tl);
                            lc.set_vclos(ident, VClosure::mk_clos(cons_val, clos_env));
                            let new_env =
                                env.extend_lvar(heap, fresh_hd).extend_lvar(heap, fresh_tl);
                            let m = Machine {
                                cclos: (consk, new_env),
                                stack: self.stack,
                            };
                            (m, lc)
                        };
                        return Some(Event::Split(vec![
                            Alt {
                                machine: m_nil,
                                lenv: lenv_n,
                                senv: senv.clone(),
                            },
                            Alt {
                                machine: m_cons,
                                lenv: lenv_c,
                                senv: senv.clone(),
                            },
                        ]));
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            // ── Case ────────────────────────────────────────────
            MComputation::Case { sum, inlk, inrk } => {
                let sum = *sum;
                let inlk = *inlk;
                let inrk = *inrk;
                let vclos = VClosure::mk_clos(sum, env);
                match vclos.close_head(heap, lenv, senv) {
                    Err(a) => match senv.get(a.ident) {
                        SuspState::Susp(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Run(_) => {
                            return Some(Event::Wait(a.ident));
                        }
                        SuspState::Done(_) => unreachable!("suspension already done"),
                    },
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Inl(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            self.cclos = (inlk, new_env);
                            None
                        }
                        MValue::Inr(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            self.cclos = (inrk, new_env);
                            None
                        }
                        _ => panic!("Case on non-sum"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let (pt1, pt2) = match lenv.get_type(ident) {
                            ValueType::Sum(t1, t2) => (t1, t2),
                            _ => panic!("casing on a non-sum logic variable"),
                        };
                        let empty = Env::empty(heap);
                        let (m_inl, lenv_l) = {
                            let mut ll = lenv.clone();
                            let fresh = ll.fresh(*pt1);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let inl_val = heap.alloc_val(MValue::Inl(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            ll.set_vclos(ident, VClosure::mk_clos(inl_val, clos_env));
                            let new_env = env.extend_lvar(heap, fresh);
                            let m = Machine {
                                cclos: (inlk, new_env),
                                stack: self.stack,
                            };
                            (m, ll)
                        };
                        let (m_inr, lenv_r) = {
                            let mut lr = lenv.clone();
                            let fresh = lr.fresh(*pt2);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let inr_val = heap.alloc_val(MValue::Inr(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            lr.set_vclos(ident, VClosure::mk_clos(inr_val, clos_env));
                            let new_env = env.extend_lvar(heap, fresh);
                            let m = Machine {
                                cclos: (inrk, new_env),
                                stack: self.stack,
                            };
                            (m, lr)
                        };
                        return Some(Event::Split(vec![
                            Alt {
                                machine: m_inl,
                                lenv: lenv_l,
                                senv: senv.clone(),
                            },
                            Alt {
                                machine: m_inr,
                                lenv: lenv_r,
                                senv: senv.clone(),
                            },
                        ]));
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            // ── Rec ─────────────────────────────────────────────
            MComputation::Rec { body } => {
                let body = *body;
                let thunk_val = heap.alloc_thunk(comp_id);
                let new_env = env.extend_val(heap, thunk_val, env);
                self.cclos = (body, new_env);
                None
            }
        }
    }
}
