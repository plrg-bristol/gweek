use bumpalo::Bump;
use smallvec::{smallvec, SmallVec};

use super::config::config;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::{SuspAt, SuspEnv};
use super::unify::{unify, UnifyError};
use super::value_type::ValueType;
use super::{CClosure, Env, VClosure};

pub type StepResult<'a> = SmallVec<[Machine<'a>; 2]>;

enum Step<'a> {
    Continue(Machine<'a>),
    Done(Machine<'a>),
    Branch(StepResult<'a>),
    Fail,
}

#[derive(Clone, Copy, Debug)]
enum StkFrame<'a> {
    Value(&'a MValue<'a>),
    To(&'a MComputation<'a>),
    Set(usize, &'a MComputation<'a>),
}

#[derive(Clone, Copy, Debug)]
struct StkClosure<'a> {
    frame: StkFrame<'a>,
    env: Env<'a>,
}

enum StackInner<'a> {
    Nil,
    Cons(StkClosure<'a>, Stack<'a>),
}

/// Persistent cons-list stack backed by a bump arena.
/// Clone/Copy is O(1) — just a pointer copy.
#[derive(Clone, Copy)]
pub struct Stack<'a>(&'a StackInner<'a>);

impl<'a> std::fmt::Debug for Stack<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Stack(...)")
    }
}

impl<'a> Stack<'a> {
    pub fn empty(arena: &'a Bump) -> Stack<'a> {
        Stack(arena.alloc(StackInner::Nil))
    }

    fn push(&self, arena: &'a Bump, frame: StkFrame<'a>, env: Env<'a>) -> Stack<'a> {
        Stack(arena.alloc(StackInner::Cons(StkClosure { frame, env }, *self)))
    }
}

#[derive(Clone)]
pub struct Machine<'a> {
    pub arena: &'a Bump,
    pub cclos: CClosure<'a>,
    pub stack: Stack<'a>,
    pub lenv: LogicEnv<'a>,
    pub senv: SuspEnv<'a>,
    pub done: bool,
}

impl<'a> Machine<'a> {
    /// Run deterministic steps in a tight loop, only returning to the
    /// scheduler at branch points (Choice, logic-var splits) or completion.
    pub fn run_to_branch(mut self) -> StepResult<'a> {
        loop {
            match self.step() {
                Step::Continue(m) => self = m,
                Step::Done(m) => return smallvec![m],
                Step::Branch(ms) => return ms,
                Step::Fail => return smallvec![],
            }
        }
    }

    fn step(self) -> Step<'a> {
        let Machine { arena, cclos: (comp, env), stack, lenv, senv, done: _ } = self;

        match comp {
            MComputation::Return(val) => match stack.0 {
                StackInner::Nil => {
                    // Reached a value, must evaluate all suspensions in case of failure
                    let mut senv = senv;
                    match senv.next() {
                        Some(a) => {
                            let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                            Step::Continue(Machine {
                                arena,
                                cclos: (a.comp(), a.env()),
                                stack: new_stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        None => Step::Done(Machine { arena, cclos: (comp, env), stack, lenv, senv, done: true }),
                    }
                }
                StackInner::Cons(sc, tail) => match sc.frame {
                    StkFrame::Value(_) => unreachable!("return throws value to a value"),
                    StkFrame::To(cont) => {
                        let new_env = sc.env.extend_val(arena, val, env);
                        Step::Continue(Machine {
                            arena,
                            cclos: (cont, new_env),
                            stack: *tail,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    StkFrame::Set(ident, cont) => {
                        let mut senv = senv;
                        senv.set(&ident, val, env);
                        Step::Continue(Machine {
                            arena,
                            cclos: (cont, sc.env),
                            stack: *tail,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                },
            },

            MComputation::Bind { comp: inner, cont } => match inner {
                MComputation::Return(v) => {
                    let new_env = env.extend_val(arena, v, env);
                    Step::Continue(Machine {
                        arena,
                        cclos: (cont, new_env),
                        stack,
                        lenv,
                        senv,
                        done: false,
                    })
                }
                _ if config().strict => {
                    let new_stack = stack.push(arena, StkFrame::To(cont), env);
                    Step::Continue(Machine {
                        arena,
                        cclos: (inner, env),
                        stack: new_stack,
                        lenv,
                        senv,
                        done: false,
                    })
                }
                _ => {
                    let mut senv = senv;
                    let ident = senv.fresh((inner, env));
                    let new_env = env.extend_susp(arena, ident);
                    Step::Continue(Machine {
                        arena,
                        cclos: (cont, new_env),
                        stack,
                        lenv,
                        senv,
                        done: false,
                    })
                }
            },

            MComputation::Force(v) => {
                let vclos = VClosure::Clos { val: v, env };
                match vclos.close_head(&lenv, &senv) {
                    Ok(VClosure::Clos { val, env: cenv }) => match val {
                        MValue::Thunk(t) => Step::Continue(Machine {
                            arena,
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
                    Err(a) => {
                        let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                        Step::Continue(Machine {
                            arena,
                            cclos: a.cclos,
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                }
            }

            MComputation::Lambda { body } => match stack.0 {
                StackInner::Cons(sc, tail) => {
                    if let StkFrame::Value(val) = sc.frame {
                        let new_env = env.extend_val(arena, val, sc.env);
                        Step::Continue(Machine {
                            arena,
                            cclos: (body, new_env),
                            stack: *tail,
                            lenv,
                            senv,
                            done: false,
                        })
                    } else {
                        panic!("lambda but no value on the stack")
                    }
                }
                StackInner::Nil => panic!("lambda met with empty stack"),
            },

            MComputation::App { op, arg } => {
                let new_stack = stack.push(arena, StkFrame::Value(arg), env);
                Step::Continue(Machine {
                    arena,
                    cclos: (op, env),
                    stack: new_stack,
                    lenv,
                    senv,
                    done: false,
                })
            }

            MComputation::Choice(choices) => {
                let n = choices.len();
                if n == 0 {
                    return Step::Fail;
                }
                if n == 1 {
                    return Step::Continue(Machine {
                        arena,
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
                            arena,
                            cclos: (c, env),
                            stack,
                            lenv: lenv.clone(),
                            senv: senv.clone(),
                            done: false,
                        });
                    } else {
                        result.push(Machine {
                            arena,
                            cclos: (c, env),
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
                let mut lenv = lenv;
                let ident = lenv.fresh(ptype.clone());
                let new_env = env.extend_lvar(arena, ident);
                Step::Continue(Machine {
                    arena,
                    cclos: (body, new_env),
                    stack,
                    lenv,
                    senv,
                    done: false,
                })
            }

            MComputation::Equate { lhs, rhs, body } => {
                let mut lenv = lenv;
                match unify(arena, lhs, rhs, env, &mut lenv, &senv) {
                    Ok(()) => Step::Continue(Machine {
                        arena,
                        cclos: (body, env),
                        stack,
                        lenv,
                        senv,
                        done: false,
                    }),
                    // Suspension needs to be evaluated!
                    Err(UnifyError::Susp(a)) => {
                        let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                        Step::Continue(Machine {
                            arena,
                            cclos: a.cclos,
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    Err(_) => Step::Fail,
                }
            }

            MComputation::Ifz { num, zk, sk } => {
                let vclos = VClosure::mk_clos(num, env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                        Step::Continue(Machine {
                            arena,
                            cclos: a.cclos,
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match val {
                        MValue::Zero | MValue::Nat(0) => Step::Continue(Machine {
                            arena,
                            cclos: (zk, env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        }),
                        MValue::Nat(n) => {
                            let pred = arena.alloc(MValue::Nat(n - 1));
                            let new_env = env.extend_val(arena, pred, cenv);
                            Step::Continue(Machine {
                                arena,
                                cclos: (sk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        MValue::Succ(v) => {
                            let new_env = env.extend_val(arena, v, cenv);
                            Step::Continue(Machine {
                                arena,
                                cclos: (sk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        _ => panic!("Ifz on {}", val),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let empty = Env::empty(arena);
                        let zero_val = arena.alloc(MValue::Nat(0));
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
                                arena,
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
                            let var0 = arena.alloc(MValue::Var(0));
                            let succ_val = arena.alloc(MValue::Succ(var0));
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: succ_val,
                                    env: empty.extend_lvar(arena, fresh),
                                },
                            );
                            Machine {
                                arena,
                                cclos: (sk, env.extend_lvar(arena, fresh)),
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
                let vclos = VClosure::mk_clos(list, env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                        Step::Continue(Machine {
                            arena,
                            cclos: a.cclos,
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match val {
                        MValue::Nil => Step::Continue(Machine {
                            arena,
                            cclos: (nilk, env),
                            stack,
                            lenv,
                            senv,
                            done: false,
                        }),
                        MValue::Cons(v, w) => {
                            let new_env = env
                                .extend_val(arena, v, cenv)
                                .extend_val(arena, w, cenv);
                            Step::Continue(Machine {
                                arena,
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
                        let empty = Env::empty(arena);
                        let nil_val = arena.alloc(MValue::Nil);
                        let m_nil = {
                            let mut lenv = lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(nil_val, empty),
                            );
                            Machine {
                                arena,
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
                            let var1 = arena.alloc(MValue::Var(1));
                            let var0 = arena.alloc(MValue::Var(0));
                            let cons_val = arena.alloc(MValue::Cons(var1, var0));
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    cons_val,
                                    empty.extend_lvar(arena, head).extend_lvar(arena, tail),
                                ),
                            );
                            Machine {
                                arena,
                                cclos: (consk, env.extend_lvar(arena, head).extend_lvar(arena, tail)),
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
                let vclos = VClosure::mk_clos(sum, env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(arena, StkFrame::Set(a.ident, comp), env);
                        Step::Continue(Machine {
                            arena,
                            cclos: a.cclos,
                            stack: new_stack,
                            lenv,
                            senv,
                            done: false,
                        })
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match val {
                        MValue::Inl(v) => {
                            let new_env = env.extend_val(arena, v, cenv);
                            Step::Continue(Machine {
                                arena,
                                cclos: (inlk, new_env),
                                stack,
                                lenv,
                                senv,
                                done: false,
                            })
                        }
                        MValue::Inr(v) => {
                            let new_env = env.extend_val(arena, v, cenv);
                            Step::Continue(Machine {
                                arena,
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
                        let empty = Env::empty(arena);
                        let m_inl = {
                            let mut lenv = lenv.clone();
                            let fresh = lenv.fresh(*pt1);
                            let var0 = arena.alloc(MValue::Var(0));
                            let inl_val = arena.alloc(MValue::Inl(var0));
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    inl_val,
                                    empty.extend_lvar(arena, fresh),
                                ),
                            );
                            Machine {
                                arena,
                                cclos: (inlk, env.extend_lvar(arena, fresh)),
                                stack,
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_inr = {
                            let mut lenv = lenv;
                            let fresh = lenv.fresh(*pt2);
                            let var0 = arena.alloc(MValue::Var(0));
                            let inr_val = arena.alloc(MValue::Inr(var0));
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    inr_val,
                                    empty.extend_lvar(arena, fresh),
                                ),
                            );
                            Machine {
                                arena,
                                cclos: (inrk, env.extend_lvar(arena, fresh)),
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
                let thunk_val = comp.thunk(arena);
                let new_env = env.extend_val(arena, thunk_val, env);
                Step::Continue(Machine {
                    arena,
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
