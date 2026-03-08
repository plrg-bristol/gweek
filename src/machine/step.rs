use std::rc::Rc;

use smallvec::{smallvec, SmallVec};

use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::{SuspAt, SuspEnv};
use super::unify::{unify, UnifyError};
use super::value_type::ValueType;
use super::{Env, VClosure};

pub type StepResult = SmallVec<[Machine; 2]>;

#[derive(Clone, Debug)]
enum StkFrame {
    Value(Rc<MValue>),
    To(Rc<MComputation>),
    Set(usize, Rc<MComputation>),
}

#[derive(Clone, Debug)]
pub(super) struct StkClosure {
    frame: StkFrame,
    env: Rc<Env>,
}

#[derive(Clone, Debug)]
pub(super) enum Stack {
    Nil,
    Cons(StkClosure, Rc<Stack>),
}

impl Stack {
    pub fn empty_stack() -> Rc<Stack> {
        Rc::new(Stack::Nil)
    }

    fn push(self: &Rc<Stack>, frame: StkFrame, env: Rc<Env>) -> Rc<Stack> {
        Stack::Cons(StkClosure { frame, env }, self.clone()).into()
    }
}

#[derive(Clone)]
pub struct Machine {
    pub comp: Rc<MComputation>,
    pub stack: Rc<Stack>,
    pub env: Rc<Env>,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
    pub done: bool,
}

fn eval_susp_then(a: SuspAt, m: Machine) -> Machine {
    Machine {
        comp: a.comp,
        env: a.env,
        stack: m.stack.push(StkFrame::Set(a.ident, m.comp), m.env),
        ..m
    }
}

impl Machine {
    /// Run deterministic steps in a tight loop, only returning to the
    /// scheduler at branch points (Choice, logic-var splits) or completion.
    pub fn run_to_branch(mut self) -> StepResult {
        loop {
            let mut results = self.step();
            if results.len() != 1 {
                return results;
            }
            self = results.remove(0);
            if self.done {
                return smallvec![self];
            }
        }
    }

    pub fn step(self) -> StepResult {
        let Machine { comp, stack, env, lenv, senv, done: _ } = self;

        match &*comp {
            MComputation::Return(val) => match &*stack {
                Stack::Nil => {
                    let mut senv = senv;
                    match senv.next() {
                        Some(a) => {
                            let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                            smallvec![Machine {
                                comp: a.comp,
                                stack: new_stack,
                                env: a.env,
                                lenv,
                                senv,
                                done: false,
                            }]
                        }
                        None => smallvec![Machine { comp, stack, env, lenv, senv, done: true }],
                    }
                }
                Stack::Cons(sc, tail) => match &sc.frame {
                    StkFrame::Value(_) => unreachable!("return throws value to a value"),
                    StkFrame::To(cont) => {
                        let new_env = sc.env.extend_val(val.clone(), env);
                        smallvec![Machine {
                            comp: cont.clone(),
                            stack: tail.clone(),
                            env: new_env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                    StkFrame::Set(ident, cont) => {
                        let mut senv = senv;
                        senv.set(ident, val, &env);
                        smallvec![Machine {
                            comp: cont.clone(),
                            stack: tail.clone(),
                            env: sc.env.clone(),
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                },
            },

            MComputation::Bind { comp: inner, cont } => match &**inner {
                MComputation::Return(v) => {
                    let new_env = env.extend_val(v.clone(), env.clone());
                    smallvec![Machine {
                        comp: cont.clone(),
                        stack,
                        env: new_env,
                        lenv,
                        senv,
                        done: false,
                    }]
                }
                _ => {
                    let mut senv = senv;
                    let ident = senv.fresh(inner, &env);
                    let new_env = env.extend_susp(ident);
                    smallvec![Machine {
                        comp: cont.clone(),
                        stack,
                        env: new_env,
                        lenv,
                        senv,
                        done: false,
                    }]
                }
            },

            MComputation::Force(v) => {
                let vclos = VClosure::Clos {
                    val: v.clone(),
                    env: env.clone(),
                };
                match vclos.close_head(&lenv, &senv) {
                    Ok(VClosure::Clos { val, env: cenv }) => match &*val {
                        MValue::Thunk(t) => smallvec![Machine {
                            comp: t.clone(),
                            stack,
                            env: cenv,
                            lenv,
                            senv,
                            done: false,
                        }],
                        _ => panic!("forcing a non-thunk value"),
                    },
                    Ok(VClosure::LogicVar { .. }) => panic!("forcing a logic variable"),
                    Ok(VClosure::Susp { .. }) => unreachable!("forcing a suspension"),
                    Err(a) => {
                        let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                        smallvec![Machine {
                            comp: a.comp,
                            stack: new_stack,
                            env: a.env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                }
            }

            MComputation::Lambda { body } => match &*stack {
                Stack::Cons(sc, tail) => {
                    if let StkFrame::Value(val) = &sc.frame {
                        let new_env = env.extend_val(val.clone(), sc.env.clone());
                        smallvec![Machine {
                            comp: body.clone(),
                            stack: tail.clone(),
                            env: new_env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    } else {
                        panic!("lambda but no value on the stack")
                    }
                }
                Stack::Nil => panic!("lambda met with empty stack"),
            },

            MComputation::App { op, arg } => {
                let new_stack = stack.push(StkFrame::Value(arg.clone()), env.clone());
                smallvec![Machine {
                    comp: op.clone(),
                    stack: new_stack,
                    env,
                    lenv,
                    senv,
                    done: false,
                }]
            }

            MComputation::Choice(choices) => {
                let n = choices.len();
                if n == 0 {
                    return smallvec![];
                }
                let mut result = SmallVec::with_capacity(n);
                for (i, c) in choices.iter().enumerate() {
                    if i < n - 1 {
                        result.push(Machine {
                            comp: c.clone(),
                            stack: stack.clone(),
                            env: env.clone(),
                            lenv: lenv.clone(),
                            senv: senv.clone(),
                            done: false,
                        });
                    } else {
                        result.push(Machine {
                            comp: c.clone(),
                            stack,
                            env,
                            lenv,
                            senv,
                            done: false,
                        });
                        break;
                    }
                }
                result
            }

            MComputation::Exists { ptype, body } => {
                let mut lenv = lenv;
                let ident = lenv.fresh(ptype.clone());
                let new_env = env.extend_lvar(ident);
                smallvec![Machine {
                    comp: body.clone(),
                    stack,
                    env: new_env,
                    lenv,
                    senv,
                    done: false,
                }]
            }

            MComputation::Equate { lhs, rhs, body } => {
                let mut lenv = lenv;
                match unify(lhs, rhs, &env, &mut lenv, &senv) {
                    Ok(()) => smallvec![Machine {
                        comp: body.clone(),
                        stack,
                        env,
                        lenv,
                        senv,
                        done: false,
                    }],
                    Err(UnifyError::Susp(a)) => {
                        let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                        smallvec![Machine {
                            comp: a.comp,
                            stack: new_stack,
                            env: a.env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                    Err(_) => smallvec![],
                }
            }

            MComputation::Ifz { num, zk, sk } => {
                let vclos = VClosure::mk_clos(num, &env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                        smallvec![Machine {
                            comp: a.comp,
                            stack: new_stack,
                            env: a.env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match &*val {
                        MValue::Zero => smallvec![Machine {
                            comp: zk.clone(),
                            stack,
                            env,
                            lenv,
                            senv,
                            done: false,
                        }],
                        MValue::Succ(v) => {
                            let new_env = env.extend_val(v.clone(), cenv);
                            smallvec![Machine {
                                comp: sk.clone(),
                                stack,
                                env: new_env,
                                lenv,
                                senv,
                                done: false,
                            }]
                        }
                        _ => panic!("Ifz on {}", &*val),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let m_zero = {
                            let mut lenv = lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: MValue::Zero.into(),
                                    env: Env::empty(),
                                },
                            );
                            Machine {
                                comp: zk.clone(),
                                stack: stack.clone(),
                                env: env.clone(),
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_succ = {
                            let mut lenv = lenv;
                            let fresh = lenv.fresh(ValueType::Nat);
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: MValue::Succ(MValue::Var(0).into()).into(),
                                    env: Env::empty().extend_lvar(fresh),
                                },
                            );
                            Machine {
                                comp: sk.clone(),
                                stack,
                                env: env.extend_lvar(fresh),
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        smallvec![m_zero, m_succ]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Match { list, nilk, consk } => {
                let vclos = VClosure::mk_clos(list, &env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                        smallvec![Machine {
                            comp: a.comp,
                            stack: new_stack,
                            env: a.env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match &*val {
                        MValue::Nil => smallvec![Machine {
                            comp: nilk.clone(),
                            stack,
                            env,
                            lenv,
                            senv,
                            done: false,
                        }],
                        MValue::Cons(v, w) => {
                            let new_env = env
                                .extend_val(v.clone(), cenv.clone())
                                .extend_val(w.clone(), cenv);
                            smallvec![Machine {
                                comp: consk.clone(),
                                stack,
                                env: new_env,
                                lenv,
                                senv,
                                done: false,
                            }]
                        }
                        _ => panic!("Match on non-list"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let ptype = match lenv.get_type(ident) {
                            ValueType::List(t) => t,
                            _ => panic!("matching on a non-list logic variable"),
                        };
                        let m_nil = {
                            let mut lenv = lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(&MValue::Nil.into(), &Env::empty()),
                            );
                            Machine {
                                comp: nilk.clone(),
                                stack: stack.clone(),
                                env: env.clone(),
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_cons = {
                            let mut lenv = lenv;
                            let head = lenv.fresh(*ptype.clone());
                            let tail = lenv.fresh(ValueType::List(ptype));
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    &MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into())
                                        .into(),
                                    &Env::empty().extend_lvar(head).extend_lvar(tail),
                                ),
                            );
                            Machine {
                                comp: consk.clone(),
                                stack,
                                env: env.extend_lvar(head).extend_lvar(tail),
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        smallvec![m_nil, m_cons]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Case { sum, inlk, inrk } => {
                let vclos = VClosure::mk_clos(sum, &env);
                match vclos.close_head(&lenv, &senv) {
                    Err(a) => {
                        let new_stack = stack.push(StkFrame::Set(a.ident, comp), env);
                        smallvec![Machine {
                            comp: a.comp,
                            stack: new_stack,
                            env: a.env,
                            lenv,
                            senv,
                            done: false,
                        }]
                    }
                    Ok(VClosure::Clos { val, env: cenv }) => match &*val {
                        MValue::Inl(v) => {
                            let new_env = env.extend_val(v.clone(), cenv);
                            smallvec![Machine {
                                comp: inlk.clone(),
                                stack,
                                env: new_env,
                                lenv,
                                senv,
                                done: false,
                            }]
                        }
                        MValue::Inr(v) => {
                            let new_env = env.extend_val(v.clone(), cenv);
                            smallvec![Machine {
                                comp: inrk.clone(),
                                stack,
                                env: new_env,
                                lenv,
                                senv,
                                done: false,
                            }]
                        }
                        _ => panic!("Case on non-sum"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let (pt1, pt2) = match lenv.get_type(ident) {
                            ValueType::Sum(t1, t2) => (t1, t2),
                            _ => panic!("casing on a non-sum logic variable"),
                        };
                        let m_inl = {
                            let mut lenv = lenv.clone();
                            let fresh = lenv.fresh(*pt1);
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    &MValue::Inl(MValue::Var(0).into()).into(),
                                    &Env::empty().extend_lvar(fresh),
                                ),
                            );
                            Machine {
                                comp: inlk.clone(),
                                stack: stack.clone(),
                                env: env.extend_lvar(fresh),
                                lenv,
                                senv: senv.clone(),
                                done: false,
                            }
                        };
                        let m_inr = {
                            let mut lenv = lenv;
                            let fresh = lenv.fresh(*pt2);
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(
                                    &MValue::Inr(MValue::Var(0).into()).into(),
                                    &Env::empty().extend_lvar(fresh),
                                ),
                            );
                            Machine {
                                comp: inrk.clone(),
                                stack,
                                env: env.extend_lvar(fresh),
                                lenv,
                                senv,
                                done: false,
                            }
                        };
                        smallvec![m_inl, m_inr]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Rec { body } => {
                let new_env = env.extend_val(comp.thunk(), env.clone());
                smallvec![Machine {
                    comp: body.clone(),
                    stack,
                    env: new_env,
                    lenv,
                    senv,
                    done: false,
                }]
            }
        }
    }
}
