//! # The transition function
//!
//! The heart of the interpreter: a single machine state ([`Machine`]) and the transition that
//! advances it. A [`Machine`] bundles the running computation closure, a [`Stack`] of continuation
//! frames, and the logic and suspension environments; the stack is a persistent heap cons-list, so
//! cloning it is one handle copy. The scheduler never calls `step` directly — it calls
//! [`run_to_branch`](Machine::run_to_branch), which runs `step` tight and yields a [`RunResult`] at
//! the next branch, at completion, on timeout, or when the heap asks to be collected. Each `step`
//! matches on the head computation — sequencing, functions, the functional-logic forms, the
//! eliminators (which *case-split* on an unbound logic variable), and `Rec` — and reads the
//! deadline through a `Clock` only once every 1024 ticks, lest a divergent loop never look at it.

use smallvec::{smallvec, SmallVec};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use super::config::Config;
use super::heap::{CompId, Heap};
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::{SuspAt, SuspEnv};
use super::unify::{unify, UnifyError};
use super::value_type::ValueType;
use super::{CClosure, Env, NodeId, SuspId, VClosure};

pub type StepResult = SmallVec<[Machine; 2]>;

/// Outcome of driving a machine to its next branch point.
pub enum RunResult {
    /// Reached a branch point or completion; the machines to schedule next.
    Yield(StepResult),
    /// The deadline elapsed mid-computation (e.g. a divergent deterministic loop).
    TimedOut,
    /// The heap is over its watermark; the machine is handed back so the
    /// scheduler can collect at the safe point and resume it.
    NeedGc(Machine),
}

enum Step {
    Continue(Machine),
    Done(Machine),
    Branch(StepResult),
    Fail,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum StkFrame {
    Value(NodeId),
    To(CompId),
    Set(SuspId, CompId),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct StkClosure {
    pub(crate) frame: StkFrame,
    pub(crate) env: Env,
}

#[derive(Clone, Copy)]
pub(crate) enum StackInner {
    Nil,
    Cons(StkClosure, Stack),
}

/// Persistent cons-list stack of heap cells. Clone/Copy is O(1).
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

    fn push(&self, heap: &mut Heap, frame: StkFrame, env: Env) -> Stack {
        heap.alloc_stack(StackInner::Cons(StkClosure { frame, env }, *self))
    }
}

#[derive(Clone)]
pub struct Machine {
    pub cclos: CClosure,
    pub stack: Stack,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
    pub done: bool,
}

/// Suspend the current computation `comp` on the suspension `a.ident` and resume
/// at the suspension's closure. Shared by the Force/Equate/Ifz/Match/Case arms,
/// which reschedule identically when `close_head` blocks on an unevaluated
/// suspension.
fn reschedule(
    heap: &mut Heap,
    lenv: LogicEnv,
    senv: SuspEnv,
    stack: Stack,
    comp: CompId,
    env: Env,
    a: SuspAt,
) -> Step {
    let new_stack = stack.push(heap, StkFrame::Set(a.ident, comp), env);
    Step::Continue(Machine {
        cclos: a.cclos,
        stack: new_stack,
        lenv,
        senv,
        done: false,
    })
}

/// Polls a deadline cheaply from a hot loop: an actual `Instant::now()` is read
/// only once every `POLL_INTERVAL` ticks, so `--timeout` is honoured without
/// timing every iteration. Shared by `run_to_branch` (the inner step loop) and
/// the scheduler loops in `eval`.
pub(super) struct Clock {
    iters: u32,
    deadline: Instant,
}

impl Clock {
    const POLL_INTERVAL: u32 = 1024;

    pub(super) fn new(deadline: Instant) -> Self {
        Clock { iters: 0, deadline }
    }

    /// Advance one tick; returns `true` once the deadline has passed, checked
    /// only every `POLL_INTERVAL` ticks.
    pub(super) fn expired(&mut self) -> bool {
        self.iters = self.iters.wrapping_add(1);
        self.iters & (Self::POLL_INTERVAL - 1) == 0 && Instant::now() >= self.deadline
    }
}

impl Machine {
    /// Run deterministic steps in a tight loop, only returning to the
    /// scheduler at branch points (Choice, logic-var splits), completion, a
    /// timeout, or when the heap is over its watermark and wants collecting.
    pub fn run_to_branch(mut self, cfg: &Config, heap: &mut Heap, deadline: Instant) -> RunResult {
        let mut clock = Clock::new(deadline);
        loop {
            if clock.expired() {
                return RunResult::TimedOut;
            }
            if heap.over_watermark() {
                return RunResult::NeedGc(self);
            }
            match self.step(cfg, heap) {
                Step::Continue(m) => self = m,
                Step::Done(m) => return RunResult::Yield(smallvec![m]),
                Step::Branch(ms) => return RunResult::Yield(ms),
                Step::Fail => return RunResult::Yield(smallvec![]),
            }
        }
    }

    fn step(self, cfg: &Config, heap: &mut Heap) -> Step {
        let Machine {
            cclos: (comp_id, env),
            stack,
            lenv,
            senv,
            done: _,
        } = self;

        match heap.comp(comp_id) {
            MComputation::Return(val) => {
                let val = *val;
                match heap.stack_inner(stack) {
                    StackInner::Nil => {
                        let mut senv = senv;
                        match senv.next() {
                            Some(a) => {
                                let new_stack = stack.push(heap, StkFrame::Set(a.ident, comp_id), env);
                                Step::Continue(Machine {
                                    cclos: (a.comp(), a.env()),
                                    stack: new_stack,
                                    lenv,
                                    senv,
                                    done: false,
                                })
                            }
                            None => Step::Done(Machine {
                                cclos: (comp_id, env),
                                stack,
                                lenv,
                                senv,
                                done: true,
                            }),
                        }
                    }
                    StackInner::Cons(sc, tail) => match sc.frame {
                        StkFrame::Value(_) => unreachable!("return throws value to a value"),
                        StkFrame::To(cont) => {
                            let new_env = sc.env.extend_val(heap, val, env);
                            Step::Continue(Machine {
                                cclos: (cont, new_env),
                                stack: tail,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        StkFrame::Set(ident, cont) => {
                            let mut senv = senv;
                            senv.set(&ident, val, env);
                            Step::Continue(Machine {
                                cclos: (cont, sc.env),
                                stack: tail,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                    },
                }
            }

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
                        Step::Continue(Machine {
                            cclos: (cont, new_env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    None if cfg.strict => {
                        let new_stack = stack.push(heap, StkFrame::To(cont), env);
                        Step::Continue(Machine {
                            cclos: (inner, env),
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    None => {
                        let mut senv = senv;
                        let ident = senv.fresh((inner, env));
                        let new_env = env.extend_susp(heap, ident);
                        Step::Continue(Machine {
                            cclos: (cont, new_env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                }
            }

            MComputation::Force(v) => {
                let v = *v;
                let vclos = VClosure::Clos { val: v, env };
                match vclos.close_head(heap, &lenv, &senv) {
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Thunk(t) => Step::Continue(Machine {
                            cclos: (t, cenv),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        }),
                        _ => panic!("forcing a non-thunk value"),
                    },
                    Ok(VClosure::LogicVar { .. }) => panic!("forcing a logic variable"),
                    Ok(VClosure::Susp { .. }) => unreachable!("forcing a suspension"),
                    Err(a) => reschedule(heap, lenv, senv, stack, comp_id, env, a),
                }
            }

            MComputation::Lambda { body } => {
                let body = *body;
                match heap.stack_inner(stack) {
                    StackInner::Cons(sc, tail) => {
                        if let StkFrame::Value(val) = sc.frame {
                            let new_env = env.extend_val(heap, val, sc.env);
                            Step::Continue(Machine {
                                cclos: (body, new_env),
                                stack: tail,
                                lenv,
                                senv,
                                done: false,
                            })
                        } else {
                            panic!("lambda but no value on the stack")
                        }
                    }
                    StackInner::Nil => panic!("lambda met with empty stack"),
                }
            }

            MComputation::App { op, arg } => {
                let op = *op;
                let arg = *arg;
                let new_stack = stack.push(heap, StkFrame::Value(arg), env);
                Step::Continue(Machine {
                    cclos: (op, env),
                    stack: new_stack,
                    lenv,
                    senv,
                    done: false,
                })
            }

            MComputation::Choice(choices) => {
                let choices: SmallVec<[CompId; 4]> = choices.iter().copied().collect();
                let n = choices.len();
                if n == 0 {
                    return Step::Fail;
                }
                if n == 1 {
                    return Step::Continue(Machine {
                        cclos: (choices[0], env),
                        stack,
                        lenv,
                        senv,
                        done: false,
                    });
                }
                let mut result = SmallVec::with_capacity(n);
                for (i, c) in choices.iter().enumerate() {
                    if i < n - 1 {
                        result.push(Machine {
                            cclos: (*c, env),
                            stack,
                            lenv: lenv.clone(),
                            senv: senv.clone(),
                            done: false,
                        });
                    } else {
                        result.push(Machine {
                            cclos: (*c, env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        });
                        break;
                    }
                }
                Step::Branch(result)
            }

            MComputation::Exists { ptype, body } => {
                let ptype = ptype.clone();
                let body = *body;
                let mut lenv = lenv;
                let ident = lenv.fresh(ptype);
                let new_env = env.extend_lvar(heap, ident);
                Step::Continue(Machine {
                    cclos: (body, new_env),
                    stack,
                    lenv,
                    senv,
                    done: false,
                })
            }

            MComputation::Equate { lhs, rhs, body } => {
                let lhs = *lhs;
                let rhs = *rhs;
                let body = *body;
                let mut lenv = lenv;
                match unify(cfg, heap, lhs, rhs, env, &mut lenv, &senv) {
                    Ok(()) => Step::Continue(Machine {
                        cclos: (body, env),
                        stack,
                        lenv,
                        senv,
                        done: false,
                    }),
                    // Suspension needs to be evaluated!
                    Err(UnifyError::Susp(a)) => reschedule(heap, lenv, senv, stack, comp_id, env, a),
                    Err(_) => Step::Fail,
                }
            }

            MComputation::Ifz { num, zk, sk } => {
                let num = *num;
                let zk = *zk;
                let sk = *sk;
                let vclos = VClosure::mk_clos(num, env);
                match vclos.close_head(heap, &lenv, &senv) {
                    Err(a) => reschedule(heap, lenv, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Zero | MValue::Nat(0) => Step::Continue(Machine {
                            cclos: (zk, env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        }),
                        MValue::Nat(n) => {
                            let pred = heap.alloc_val(MValue::Nat(n - 1));
                            let new_env = env.extend_val(heap, pred, cenv);
                            Step::Continue(Machine {
                                cclos: (sk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        MValue::Succ(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            Step::Continue(Machine {
                                cclos: (sk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        other => panic!("Ifz on {:?}", other),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let empty = Env::empty(heap);
                        let zero_val = heap.alloc_val(MValue::Nat(0));
                        let m_zero = {
                            let mut lenv = lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: zero_val,
                                    env: empty,
                                },
                            );
                            Machine {
                                cclos: (zk, env),
                                stack,
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_succ = {
                            let mut lenv = lenv;
                            let fresh = lenv.fresh(ValueType::Nat);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let succ_val = heap.alloc_val(MValue::Succ(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: succ_val,
                                    env: clos_env,
                                },
                            );
                            let new_env = env.extend_lvar(heap, fresh);
                            Machine {
                                cclos: (sk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        Step::Branch(smallvec![m_zero, m_succ])
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Match { list, nilk, consk } => {
                let list = *list;
                let nilk = *nilk;
                let consk = *consk;
                let vclos = VClosure::mk_clos(list, env);
                match vclos.close_head(heap, &lenv, &senv) {
                    Err(a) => reschedule(heap, lenv, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Nil => Step::Continue(Machine {
                            cclos: (nilk, env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        }),
                        MValue::Cons(v, w) => {
                            let new_env = env.extend_val(heap, v, cenv).extend_val(heap, w, cenv);
                            Step::Continue(Machine {
                                cclos: (consk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        _ => panic!("Match on non-list"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let ptype = match lenv.get_type(ident) {
                            ValueType::List(t) => t,
                            _ => panic!("matching on a non-list logic variable"),
                        };
                        let empty = Env::empty(heap);
                        let nil_val = heap.alloc_val(MValue::Nil);
                        let m_nil = {
                            let mut lenv = lenv.clone();
                            lenv.set_vclos(ident, VClosure::mk_clos(nil_val, empty));
                            Machine {
                                cclos: (nilk, env),
                                stack,
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_cons = {
                            let mut lenv = lenv;
                            let head = lenv.fresh(*ptype.clone());
                            let tail = lenv.fresh(ValueType::List(ptype));
                            let var1 = heap.alloc_val(MValue::Var(1));
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let cons_val = heap.alloc_val(MValue::Cons(var1, var0));
                            let clos_env = empty.extend_lvar(heap, head).extend_lvar(heap, tail);
                            lenv.set_vclos(ident, VClosure::mk_clos(cons_val, clos_env));
                            let new_env = env.extend_lvar(heap, head).extend_lvar(heap, tail);
                            Machine {
                                cclos: (consk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        Step::Branch(smallvec![m_nil, m_cons])
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Case { sum, inlk, inrk } => {
                let sum = *sum;
                let inlk = *inlk;
                let inrk = *inrk;
                let vclos = VClosure::mk_clos(sum, env);
                match vclos.close_head(heap, &lenv, &senv) {
                    Err(a) => reschedule(heap, lenv, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Inl(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            Step::Continue(Machine {
                                cclos: (inlk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        MValue::Inr(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            Step::Continue(Machine {
                                cclos: (inrk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        _ => panic!("Case on non-sum"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let (pt1, pt2) = match lenv.get_type(ident) {
                            ValueType::Sum(t1, t2) => (t1, t2),
                            _ => panic!("casing on a non-sum logic variable"),
                        };
                        let empty = Env::empty(heap);
                        let m_inl = {
                            let mut lenv = lenv.clone();
                            let fresh = lenv.fresh(*pt1);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let inl_val = heap.alloc_val(MValue::Inl(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            lenv.set_vclos(ident, VClosure::mk_clos(inl_val, clos_env));
                            let new_env = env.extend_lvar(heap, fresh);
                            Machine {
                                cclos: (inlk, new_env),
                                stack,
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_inr = {
                            let mut lenv = lenv;
                            let fresh = lenv.fresh(*pt2);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let inr_val = heap.alloc_val(MValue::Inr(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            lenv.set_vclos(ident, VClosure::mk_clos(inr_val, clos_env));
                            let new_env = env.extend_lvar(heap, fresh);
                            Machine {
                                cclos: (inrk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        Step::Branch(smallvec![m_inl, m_inr])
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Rec { body } => {
                let body = *body;
                let thunk_val = heap.alloc_thunk(comp_id);
                let new_env = env.extend_val(heap, thunk_val, env);
                Step::Continue(Machine {
                    cclos: (body, new_env),
                    stack,
                    lenv,
                    senv,
                    done: false,
                })
            }
        }
    }
}
