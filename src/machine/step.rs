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
    pub fn step(self) -> StepResult {
        let mut m = self;

        match &*m.comp {
            MComputation::Return(val) => match &*m.stack {
                Stack::Nil => match m.senv.next() {
                    Some(a) => smallvec![eval_susp_then(a, m)],
                    None => smallvec![Machine { done: true, ..m }],
                },
                Stack::Cons(sc, tail) => {
                    let StkClosure { frame, env: sc_env } = sc.clone();
                    match frame {
                        StkFrame::Value(_) => unreachable!("return throws value to a value"),
                        StkFrame::To(cont) => {
                            let env = sc_env.extend_val(val.clone(), m.env.clone());
                            smallvec![Machine {
                                comp: cont,
                                stack: tail.clone(),
                                env,
                                ..m
                            }]
                        }
                        StkFrame::Set(ident, cont) => {
                            let mut senv = m.senv;
                            senv.set(&ident, val, &m.env);
                            smallvec![Machine {
                                comp: cont,
                                stack: tail.clone(),
                                env: sc_env,
                                senv,
                                ..m
                            }]
                        }
                    }
                }
            },

            MComputation::Bind { comp, cont } => match &**comp {
                MComputation::Return(v) => {
                    let env = m.env.extend_val(v.clone(), m.env.clone());
                    smallvec![Machine {
                        comp: cont.clone(),
                        env,
                        ..m
                    }]
                }
                _ => {
                    let mut senv = m.senv;
                    let ident = senv.fresh(comp, &m.env);
                    let env = m.env.extend_susp(ident);
                    smallvec![Machine {
                        comp: cont.clone(),
                        env,
                        senv,
                        ..m
                    }]
                }
            },

            MComputation::Force(v) => {
                let vclos = VClosure::Clos {
                    val: v.clone(),
                    env: m.env.clone(),
                };
                match vclos.close_head(&m.lenv, &m.senv) {
                    Ok(VClosure::Clos { val, env }) => match &*val {
                        MValue::Thunk(t) => smallvec![Machine {
                            comp: t.clone(),
                            env,
                            ..m
                        }],
                        _ => panic!("forcing a non-thunk value"),
                    },
                    Ok(VClosure::LogicVar { .. }) => panic!("forcing a logic variable"),
                    Ok(VClosure::Susp { .. }) => unreachable!("forcing a suspension"),
                    Err(a) => {
                        smallvec![Machine {
                            comp: a.comp,
                            env: a.env,
                            stack: m.stack.push(StkFrame::Set(a.ident, m.comp), m.env),
                            ..m
                        }]
                    }
                }
            }

            MComputation::Lambda { body } => match &*m.stack {
                Stack::Cons(sc, tail) => {
                    if let StkFrame::Value(val) = &sc.frame {
                        let env = m.env.extend_val(val.clone(), sc.env.clone());
                        smallvec![Machine {
                            comp: body.clone(),
                            stack: tail.clone(),
                            env,
                            ..m
                        }]
                    } else {
                        panic!("lambda but no value on the stack")
                    }
                }
                Stack::Nil => panic!("lambda met with empty stack"),
            },

            MComputation::App { op, arg } => smallvec![Machine {
                comp: op.clone(),
                stack: m.stack.push(StkFrame::Value(arg.clone()), m.env.clone()),
                ..m
            }],

            MComputation::Choice(choices) => choices
                .iter()
                .map(|c| Machine {
                    comp: c.clone(),
                    ..m.clone()
                })
                .collect(),

            MComputation::Exists { ptype, body } => {
                let mut lenv = m.lenv;
                let ident = lenv.fresh(ptype.clone());
                smallvec![Machine {
                    comp: body.clone(),
                    env: m.env.extend_lvar(ident),
                    lenv,
                    ..m
                }]
            }

            MComputation::Equate { lhs, rhs, body } => {
                let mut lenv = m.lenv;
                match unify(lhs, rhs, &m.env, &mut lenv, &m.senv) {
                    Ok(()) => smallvec![Machine {
                        comp: body.clone(),
                        lenv,
                        ..m
                    }],
                    Err(UnifyError::Susp(a)) => {
                        smallvec![eval_susp_then(a, Machine { lenv, ..m })]
                    }
                    Err(_) => smallvec![],
                }
            }

            MComputation::Ifz { num, zk, sk } => {
                let vclos = VClosure::mk_clos(num, &m.env);
                match vclos.close_head(&m.lenv, &m.senv) {
                    Err(a) => smallvec![eval_susp_then(a, m)],
                    Ok(VClosure::Clos { val, env }) => match &*val {
                        MValue::Zero => smallvec![Machine {
                            comp: zk.clone(),
                            ..m
                        }],
                        MValue::Succ(v) => {
                            let env = m.env.extend_val(v.clone(), env);
                            smallvec![Machine {
                                comp: sk.clone(),
                                env,
                                ..m
                            }]
                        }
                        _ => panic!("Ifz on {}", &*val),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let m_zero = {
                            let mut lenv = m.lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::Clos {
                                    val: MValue::Zero.into(),
                                    env: Env::empty(),
                                },
                            );
                            Machine {
                                comp: zk.clone(),
                                lenv,
                                ..m.clone()
                            }
                        };
                        let m_succ = {
                            let mut lenv = m.lenv.clone();
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
                                env: m.env.extend_lvar(fresh),
                                lenv,
                                ..m
                            }
                        };
                        smallvec![m_zero, m_succ]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Match { list, nilk, consk } => {
                let vclos = VClosure::mk_clos(list, &m.env);
                match vclos.close_head(&m.lenv, &m.senv) {
                    Err(a) => smallvec![eval_susp_then(a, m)],
                    Ok(VClosure::Clos { val, env }) => match &*val {
                        MValue::Nil => smallvec![Machine {
                            comp: nilk.clone(),
                            ..m
                        }],
                        MValue::Cons(v, w) => {
                            let env = m
                                .env
                                .extend_val(v.clone(), env.clone())
                                .extend_val(w.clone(), env);
                            smallvec![Machine {
                                comp: consk.clone(),
                                env,
                                ..m
                            }]
                        }
                        _ => panic!("Match on non-list"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let ptype = match m.lenv.get_type(ident) {
                            ValueType::List(t) => t,
                            _ => panic!("matching on a non-list logic variable"),
                        };
                        let m_nil = {
                            let mut lenv = m.lenv.clone();
                            lenv.set_vclos(
                                ident,
                                VClosure::mk_clos(&MValue::Nil.into(), &Env::empty()),
                            );
                            Machine {
                                comp: nilk.clone(),
                                lenv,
                                ..m.clone()
                            }
                        };
                        let m_cons = {
                            let mut lenv = m.lenv.clone();
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
                                env: m.env.extend_lvar(head).extend_lvar(tail),
                                lenv,
                                ..m
                            }
                        };
                        smallvec![m_nil, m_cons]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Case { sum, inlk, inrk } => {
                let vclos = VClosure::mk_clos(sum, &m.env);
                match vclos.close_head(&m.lenv, &m.senv) {
                    Err(a) => smallvec![eval_susp_then(a, m)],
                    Ok(VClosure::Clos { val, env }) => match &*val {
                        MValue::Inl(v) => {
                            let env = m.env.extend_val(v.clone(), env);
                            smallvec![Machine {
                                comp: inlk.clone(),
                                env,
                                ..m
                            }]
                        }
                        MValue::Inr(v) => {
                            let env = m.env.extend_val(v.clone(), env);
                            smallvec![Machine {
                                comp: inrk.clone(),
                                env,
                                ..m
                            }]
                        }
                        _ => panic!("Case on non-sum"),
                    },
                    Ok(VClosure::LogicVar { ident }) => {
                        let (pt1, pt2) = match m.lenv.get_type(ident) {
                            ValueType::Sum(t1, t2) => (t1, t2),
                            _ => panic!("casing on a non-sum logic variable"),
                        };
                        let m_inl = {
                            let mut lenv = m.lenv.clone();
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
                                env: m.env.extend_lvar(fresh),
                                lenv,
                                ..m.clone()
                            }
                        };
                        let m_inr = {
                            let mut lenv = m.lenv.clone();
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
                                env: m.env.extend_lvar(fresh),
                                lenv,
                                ..m
                            }
                        };
                        smallvec![m_inl, m_inr]
                    }
                    Ok(VClosure::Susp { .. }) => unreachable!(),
                }
            }

            MComputation::Rec { body } => {
                let env = m.env.extend_val(m.comp.thunk(), m.env.clone());
                smallvec![Machine {
                    comp: body.clone(),
                    env,
                    ..m
                }]
            }
        }
    }
}
