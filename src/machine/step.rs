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

use super::branch::BranchAlternative;
use super::config::Config;
use super::heap::{CompId, Heap};
use super::lvar::LogicEnv;
use super::senv::{SuspAt, SuspEnv, SuspState};
use super::mterms::{MComputation, MValue};
use super::unify::{unify, UnifyError};
use super::value_type::ValueType;
use super::{CClosure, Env, NodeId, SuspId, VClosure};

// ── Stack ──────────────────────────────────────────────────────────

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

    pub(crate) fn push(&self, heap: &mut Heap, frame: StkFrame, env: Env) -> Stack {
        heap.alloc_stack(StackInner::Cons(StkClosure { frame, env }, *self))
    }
}

// ── Machine ────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Machine {
    pub cclos: CClosure,
    pub stack: Stack,
    pub done: bool,
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

// ── Step outcome ───────────────────────────────────────────────────

/// Outcome of one step of a machine thread.
#[derive(Debug)]
pub enum StepOutcome {
    /// Continue running the same machine on the next tick.
    Continue(Machine),
    /// The machine reached a Return with an empty stack (thread-level answer).
    Returned(VClosure),
    /// Object-language nondeterminism (Choice) or logic-variable case split.
    /// Each alternative carries its own lenv/senv clone.
    Fork(Vec<BranchAlternative>),
    /// The machine tried to inspect a suspension that is not yet done.
    /// (Used in Phase 3+; Phase 1–2 use inline reschedule via Continue.)
    BlockedOn {
        susp: SuspAt,
        resume: Machine,
    },
    /// Continue with an obligation registered (Need creates a concurrent obligation).
    ContinueWithObligation {
        machine: Machine,
        obligation: SuspId,
    },
    /// The machine failed (e.g. unification failure, empty Choice).
    Failed,
    /// The heap is over its watermark and wants collection.
    NeedGc(Machine),
    /// The deadline elapsed mid-computation.
    TimedOut,
}

// ── Helpers ─────────────────────────────────────────────────────────



fn handle_suspension(
    heap: &mut Heap,
    senv: &mut SuspEnv,
    stack: Stack,
    comp_id: CompId,
    env: Env,
    a: SuspAt,
) -> StepOutcome {
    match senv.get(a.ident) {
        SuspState::Suspended(_) => {
            senv.mark_running(a.ident);
            let _new_stack = stack.push(heap, StkFrame::Set(a.ident, comp_id), env);
            StepOutcome::Continue(Machine {
                cclos: a.cclos,
                stack: _new_stack,
                done: false,
            })
        }
        SuspState::Running(_) => StepOutcome::BlockedOn {
            susp: a,
            resume: Machine { cclos: (comp_id, env), stack, done: false },
        },
        SuspState::Done(_) => unreachable!("handle_suspension on Done suspension"),
    }
}
// ── run_to_event ───────────────────────────────────────────────────

impl Machine {
    /// Run deterministic steps in a tight loop, returning at the next
    /// significant event (branch point, completion, block, timeout, or GC).
    pub fn run_to_event(
        mut self,
        cfg: &Config,
        heap: &mut Heap,
        lenv: &mut LogicEnv,
        senv: &mut SuspEnv,
        deadline: Instant,
    ) -> StepOutcome {
        let mut clock = Clock::new(deadline);
        loop {
            if clock.expired() {
                return StepOutcome::TimedOut;
            }
            if heap.nursery_full() {
                return StepOutcome::NeedGc(self);
            }
            match self.step(cfg, heap, lenv, senv) {
                StepOutcome::Continue(m) => self = m,
                other => return other,
            }
        }
    }

    fn step(
        self,
        cfg: &Config,
        heap: &mut Heap,
        lenv: &mut LogicEnv,
        senv: &mut SuspEnv,
    ) -> StepOutcome {
        let Machine {
            cclos: (comp_id, env),
            stack,
            done: _,
        } = self;

        match heap.comp(comp_id) {
            // ── Return ──────────────────────────────────────────
            MComputation::Return(val) => {
                let val = *val;
                match heap.stack_inner(stack) {
                    StackInner::Nil => {
                        StepOutcome::Returned(VClosure::mk_clos(val, env))
                    }
                    StackInner::Cons(sc, tail) => match sc.frame {
                        StkFrame::Value(_) => {
                            unreachable!("return throws value to a value")
                        }
                        StkFrame::To(cont) => {
                            let new_env = sc.env.extend_val(heap, val, env);
                            StepOutcome::Continue(Machine {
                                cclos: (cont, new_env),
                                stack: tail,
                                done: false,
                            })
                        }
                        StkFrame::Set(sid, cont) => {
                            senv.set(&sid, val, env);
                            StepOutcome::Continue(Machine {
                                cclos: (cont, sc.env),
                                stack: tail,
                                done: false,
                            })
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
                        StepOutcome::Continue(Machine {
                            cclos: (cont, new_env),
                            stack,
                            done: false,
                        })
                    }
                    None => {
                        let new_stack = stack.push(heap, StkFrame::To(cont), env);
                        StepOutcome::Continue(Machine {
                            cclos: (inner, env),
                            stack: new_stack,
                            done: false,
                        })
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
                        StepOutcome::Continue(Machine {
                            cclos: (cont, new_env),
                            stack,
                            done: false,
                        })
                    }
                    None => {
                        let ident = senv.fresh((inner, env));
                        let new_env = env.extend_susp(heap, ident);
                        StepOutcome::ContinueWithObligation {
                            machine: Machine {
                                cclos: (cont, new_env),
                                stack,
                                done: false,
                            },
                            obligation: ident,
                        }
                    }
                }
            }

            // ── Lambda ──────────────────────────────────────────
            MComputation::Lambda { body } => {
                let body = *body;
                match heap.stack_inner(stack) {
                    StackInner::Cons(sc, tail) => match sc.frame {
                        StkFrame::Value(arg) => {
                            let new_env = env.extend_val(heap, arg, sc.env);
                            StepOutcome::Continue(Machine {
                                cclos: (body, new_env),
                                stack: tail,
                                done: false,
                            })
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
                let new_stack = stack.push(heap, StkFrame::Value(arg), env);
                StepOutcome::Continue(Machine {
                    cclos: (op, env),
                    stack: new_stack,
                    done: false,
                })
            }

            // ── Choice ──────────────────────────────────────────
            MComputation::Choice(choices) => {
                let choices: SmallVec<[CompId; 4]> = choices.iter().copied().collect();
                let n = choices.len();
                if n == 0 {
                    return StepOutcome::Failed;
                }
                if n == 1 {
                    return StepOutcome::Continue(Machine {
                        cclos: (choices[0], env),
                        stack,
                        done: false,
                    });
                }
                let mut alternatives = Vec::with_capacity(n);
                for c in choices.iter() {
                    let m = Machine {
                        cclos: (*c, env),
                        stack,
                        done: false,
                    };
                    alternatives.push(BranchAlternative {
                        machine: m,
                        lenv: lenv.clone(),
                        senv: senv.clone(),
                    });
                }
                StepOutcome::Fork(alternatives)
            }

            // ── Exists ──────────────────────────────────────────
            MComputation::Exists { ptype, body } => {
                let ptype = ptype.clone();
                let body = *body;
                let ident = lenv.fresh(ptype);
                let new_env = env.extend_lvar(heap, ident);
                StepOutcome::Continue(Machine {
                    cclos: (body, new_env),
                    stack,
                    done: false,
                })
            }

            // ── Equate ──────────────────────────────────────────
            MComputation::Equate { lhs, rhs, body } => {
                let lhs = *lhs;
                let rhs = *rhs;
                let body = *body;
                match unify(cfg, heap, lhs, rhs, env, lenv, senv) {
                    Ok(()) => StepOutcome::Continue(Machine {
                        cclos: (body, env),
                        stack,
                        done: false,
                    }),
                    Err(UnifyError::Susp(a)) => {
                        handle_suspension(heap, senv, stack, comp_id, env, a)
                    }
                    Err(_) => StepOutcome::Failed,
                }
            }

            // ── Force ───────────────────────────────────────────
            MComputation::Force(v) => {
                let v = *v;
                let vclos = VClosure::Clos { val: v, env };
                match vclos.close_head(heap, lenv, senv) {
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Thunk(t) => StepOutcome::Continue(Machine {
                            cclos: (t, cenv),
                            stack,
                            done: false,
                        }),
                        _ => panic!("forcing a non-thunk value"),
                    },
                    Ok(VClosure::LogicVar { .. }) => panic!("forcing a logic variable"),
                    Ok(VClosure::Susp { .. }) => unreachable!("forcing a suspension"),
                    Err(a) => handle_suspension(heap, senv, stack, comp_id, env, a),
                }
            }

            // ── Ifz ─────────────────────────────────────────────
            MComputation::Ifz { num, zk, sk } => {
                let num = *num;
                let zk = *zk;
                let sk = *sk;
                let vclos = VClosure::mk_clos(num, env);
                match vclos.close_head(heap, lenv, senv) {
                    Err(a) => handle_suspension(heap, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Zero | MValue::Nat(0) => StepOutcome::Continue(Machine {
                            cclos: (zk, env),
                            stack,
                            done: false,
                        }),
                        MValue::Succ(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            StepOutcome::Continue(Machine {
                                cclos: (sk, new_env),
                                stack,
                                done: false,
                            })
                        }
                        MValue::Nat(n) if n > 0 => {
                            let v = heap.alloc_val(MValue::Nat(n - 1));
                            let new_env = env.extend_val(heap, v, cenv);
                            StepOutcome::Continue(Machine {
                                cclos: (sk, new_env),
                                stack,
                                done: false,
                            })
                        }
                        other => panic!("Ifz on {:?}", other),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let empty = Env::empty(heap);
                        let zero_val = heap.alloc_val(MValue::Nat(0));
                        let (m_zero, lenv_z) = {
                            let mut lz = lenv.clone();
                            lz.set_vclos(ident, VClosure::Clos {
                                val: zero_val,
                                env: empty,
                            });
                            let m = Machine {
                                cclos: (zk, env),
                                stack,
                                done: false,
                            };
                            (m, lz)
                        };
                        let (m_succ, lenv_s) = {
                            let mut ls = lenv.clone();
                            let fresh = ls.fresh(ValueType::Nat);
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let succ_val = heap.alloc_val(MValue::Succ(var0));
                            let clos_env = empty.extend_lvar(heap, fresh);
                            ls.set_vclos(ident, VClosure::Clos {
                                val: succ_val,
                                env: clos_env,
                            });
                            let new_env = env.extend_lvar(heap, fresh);
                            let m = Machine {
                                cclos: (sk, new_env),
                                stack,
                                done: false,
                            };
                            (m, ls)
                        };
                        StepOutcome::Fork(vec![
                            BranchAlternative {
                                machine: m_zero,
                                lenv: lenv_z,
                                senv: senv.clone(),
                            },
                            BranchAlternative {
                                machine: m_succ,
                                lenv: lenv_s,
                                senv: senv.clone(),
                            },
                        ])
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
                    Err(a) => handle_suspension(heap, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Nil => StepOutcome::Continue(Machine {
                            cclos: (nilk, env),
                            stack,
                            done: false,
                        }),
                        MValue::Cons(v, w) => {
                            let new_env = env.extend_val(heap, v, cenv).extend_val(heap, w, cenv);
                            StepOutcome::Continue(Machine {
                                cclos: (consk, new_env),
                                stack,
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
                        let (m_nil, lenv_n) = {
                            let mut ln = lenv.clone();
                            ln.set_vclos(ident, VClosure::mk_clos(nil_val, empty));
                            let m = Machine {
                                cclos: (nilk, env),
                                stack,
                                done: false,
                            };
                            (m, ln)
                        };
                        let (m_cons, lenv_c) = {
                            let mut lc = lenv.clone();
                            let head = lc.fresh(*ptype.clone());
                            let tail = lc.fresh(ValueType::List(ptype));
                            let var1 = heap.alloc_val(MValue::Var(1));
                            let var0 = heap.alloc_val(MValue::Var(0));
                            let cons_val = heap.alloc_val(MValue::Cons(var1, var0));
                            let clos_env = empty.extend_lvar(heap, head).extend_lvar(heap, tail);
                            lc.set_vclos(ident, VClosure::mk_clos(cons_val, clos_env));
                            let new_env = env.extend_lvar(heap, head).extend_lvar(heap, tail);
                            let m = Machine {
                                cclos: (consk, new_env),
                                stack,
                                done: false,
                            };
                            (m, lc)
                        };
                        StepOutcome::Fork(vec![
                            BranchAlternative {
                                machine: m_nil,
                                lenv: lenv_n,
                                senv: senv.clone(),
                            },
                            BranchAlternative {
                                machine: m_cons,
                                lenv: lenv_c,
                                senv: senv.clone(),
                            },
                        ])
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
                    Err(a) => handle_suspension(heap, senv, stack, comp_id, env, a),
                    Ok(VClosure::Clos { val, env: cenv }) => match heap.val(val) {
                        MValue::Inl(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            StepOutcome::Continue(Machine {
                                cclos: (inlk, new_env),
                                stack,
                                done: false,
                            })
                        }
                        MValue::Inr(v) => {
                            let new_env = env.extend_val(heap, v, cenv);
                            StepOutcome::Continue(Machine {
                                cclos: (inrk, new_env),
                                stack,
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
                                stack,
                                done: false,
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
                                stack,
                                done: false,
                            };
                            (m, lr)
                        };
                        StepOutcome::Fork(vec![
                            BranchAlternative {
                                machine: m_inl,
                                lenv: lenv_l,
                                senv: senv.clone(),
                            },
                            BranchAlternative {
                                machine: m_inr,
                                lenv: lenv_r,
                                senv: senv.clone(),
                            },
                        ])
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            // ── Rec ─────────────────────────────────────────────
            MComputation::Rec { body } => {
                let body = *body;
                let thunk_val = heap.alloc_thunk(comp_id);
                let new_env = env.extend_val(heap, thunk_val, env);
                StepOutcome::Continue(Machine {
                    cclos: (body, new_env),
                    stack,
                    done: false,
                })
            }
        }
    }
}

