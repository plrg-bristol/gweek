use std::rc::Rc;
use smallvec::{smallvec, SmallVec};
use crate::machine::{lvar, senv, senv::SuspAt, value_type::ValueType};
use super::{lvar::LogicEnv, mterms::{MComputation, MValue}, senv::SuspEnv, unify::UnifyError, Env, Ident, VClosure};
use crate::machine::unify::unify;

pub type StepResult = SmallVec<[Machine; 2]>;
    
#[derive(Clone, Debug)]
enum StkFrame {
    Value(Rc<MValue>),
    To(Rc<MComputation>),
    Set(Ident, Rc<MComputation>),
}

#[derive(Clone, Debug)]
pub struct StkClosure {
    stk_frame: StkFrame,
    stk_env: Rc<Env>,
}

#[derive(Clone, Debug)]
pub enum Stack {
    Nil,
    Cons(StkClosure, Rc<Stack>),
}

impl Stack {
    pub fn empty_stack() -> Rc<Stack> { Rc::new(Stack::Nil) }

    fn push_closure(self: &Rc<Stack>, stk_frame : StkFrame, stk_env: Rc<Env>) -> Rc<Stack> {
        Stack::Cons(StkClosure { stk_frame, stk_env }, self.clone()).into()
    }

    fn push_susp(self: &Rc<Stack>, ident: Ident, c: Rc<MComputation>, env: Rc<Env>) -> Rc<Stack> {
        Stack::push_closure(self, StkFrame::Set(ident, c), env)
    }
}

#[derive(Clone)]
pub struct Machine {
    pub comp : Rc<MComputation>,
    pub stack: Rc<Stack>,
    pub env  : Rc<Env>,
    pub lenv : LogicEnv,
    pub senv : SuspEnv,
    pub done : bool
}

fn eval_susp_then(a : SuspAt, m : Machine) -> Machine {
    Machine { comp : a.comp, env : a.env, stack : m.stack.push_susp(a.ident, m.comp, m.env), ..m  }
}

impl Machine {

    pub fn step(self) -> StepResult {
        let mut m = self;
        
        match &*m.comp {

            MComputation::Return(val) => {
                match &*m.stack {
                    Stack::Nil => {
                        match m.senv.next() {
                            Some(a) => smallvec![ eval_susp_then(a, m) ],
                            None => smallvec![Machine { done: true, ..m }],
                        }
                    }
                    Stack::Cons(stk_clos, stk_tail) => {
                        let StkClosure { stk_frame, stk_env } = stk_clos.clone();
                        match stk_frame {
                            StkFrame::Value(_) => unreachable!("return throws value to a value"),
                            StkFrame::To(cont) => {
                                let new_env = stk_env.extend_val(val.clone(), m.env.clone());
                                smallvec![Machine { comp: cont.clone(), stack: stk_tail.clone(), env: new_env, ..m }]
                            }
                            StkFrame::Set(i, cont) => {
                                let mut senv = m.senv;
                                senv.set(&i, val, &m.env);
                                smallvec![Machine { comp: cont.clone(), stack: stk_tail.clone(), env: stk_env.clone(), senv, ..m }]
                            }
                        }
                    }
                }
            },

            MComputation::Bind { comp, cont } => {
                match &**comp {
                    MComputation::Return(v) => {
                        let env = m.env.extend_val(v.clone(), m.env.clone());
                        smallvec![Machine { comp : cont.clone(), env, ..m }]
                    },
                    _ => {
                        let mut senv = m.senv;
                        let env = &m.env;
                        let ident = senv.fresh(&comp, &m.env);
                        let env = env.extend_susp(ident);
                        smallvec![Machine { comp : cont.clone(), env, senv : senv, ..m}]
                    }
                }
            },

            MComputation::Force(v) => {
                let vclos = VClosure::Clos { val: v.clone(), env: m.env.clone() };
                match vclos.close_head(&m.lenv, &m.senv) {
                    Ok(vclos) => 
                        match vclos {
                            VClosure::Clos { val, env } => {
                                match &*val {
                                    MValue::Thunk(t) => smallvec![Machine { comp : t.clone(), env : env.clone(), ..m}],
                                _ => panic!("shouldn't be forcing a non-thunk value")
                                } 
                            },
                            VClosure::LogicVar { ident } => panic!("shouldn't be forcing a logic variable"),
                            VClosure::Susp { ident } => unreachable!("shouldn't be forcing a suspension"),
                        }
                    Err(a) => {
                        smallvec![Machine { comp : a.comp, env : a.env, stack : m.stack.push_susp(a.ident, m.comp, m.env), ..m  }]
                    },
                }
            },

            MComputation::Lambda { body } => {
                match &*m.stack {
                    Stack::Cons(StkClosure { stk_frame, stk_env }, tail) => {
                        if let StkFrame::Value(val) = stk_frame {
                            let env = m.env.extend_val(val.clone(), stk_env.clone());
                            smallvec![Machine { comp: body.clone(), stack: tail.clone(), env, ..m }]
                        } else {
                            panic!("lambda but no value StkFrame in the stack")
                        }
                    },
                    Stack::Nil => panic!("lambda met with empty stack")
                }
            },

            MComputation::App { op, arg } =>
                smallvec![Machine { comp: op.clone(), stack: m.stack.push_closure(StkFrame::Value(arg.clone()), m.env.clone()), ..m }],

            MComputation::Choice(choices) => 
              choices.iter().map(|c| Machine { comp: c.clone(), ..m.clone()}).collect(),

            MComputation::Exists { ptype, body } => {
                let mut lenv = m.lenv;
                let ident = lenv.fresh(ptype.clone());
                smallvec![Machine { comp : body.clone(), env : m.env.extend_lvar(ident), lenv : lenv, ..m}]
            }

            MComputation::Equate { lhs, rhs, body } => {
                let mut lenv = m.lenv;
                match unify(&lhs, &rhs, &m.env, &mut lenv, &m.senv) {
                    Ok(()) => smallvec![ Machine { comp : body.clone(), lenv : lenv, ..m } ],
                    Err(UnifyError::Susp(a)) => smallvec![ eval_susp_then(a, Machine { lenv : lenv, ..m }) ],
                    Err(_) => smallvec![]
                }
            },

            MComputation::Ifz { num, zk, sk } => {
                let vclos = VClosure::mk_clos(num, &m.env);
                match vclos.close_head(&m.lenv, &m.senv) {
                    Err(a) => smallvec![ eval_susp_then(a, m) ],
                    Ok(VClosure::Clos { val, env }) => {
                        match &*val {
                            MValue::Zero => smallvec![Machine { comp: zk.clone(), ..m}],
                            MValue::Succ(v) => {
                                let env = m.env.extend_val(v.clone(), env.clone());
                                smallvec![Machine { comp: sk.clone(), env, ..m}]
                            }
                            _ => panic!("Ifz on {}", &*val)
                        }
                    },
                    Ok(VClosure::LogicVar { ident }) => { // must be unresolved, by structure of close_head
                        let m_zero  = {
                            let mut lenv = m.lenv.clone(); // make a new logic env
                            lenv.set_vclos(ident, VClosure::Clos { val: MValue::Zero.into(), env: Env::empty()});

                            Machine { comp: zk.clone(), lenv : lenv, ..m.clone()}
                        };
                        
                        let m_succ = {
                            let mut lenv = m.lenv.clone();
                            let ident_lvar_succ = lenv.fresh(ValueType::Nat);
                            
                            lenv.set_vclos(ident, VClosure::Clos { 
                                val : MValue::Succ(Rc::new(MValue::Var(0))).into(), 
                                env : Env::empty().extend_lvar(ident_lvar_succ)
                            }.into());
                            
                            let new_env = m.env.extend_lvar(ident_lvar_succ);

                            Machine { comp: sk.clone(), lenv : lenv, env : new_env, ..m.clone()}
                        };

                        smallvec![m_zero, m_succ]
                    },
                    Ok(VClosure::Susp { ident }) => unreachable!("shouldn't be encountering a suspension here")
                }
            },

            MComputation::Match { list, nilk, consk } => {
                let vclos = VClosure::mk_clos(list, &m.env);
                let closed_list = vclos.close_head(&m.lenv, &m.senv);
                match closed_list {
                    Err(a) => smallvec![ eval_susp_then(a, m) ],
                    Ok(vclos) => 
                        match vclos {
                            VClosure::Clos { val, env } => {
                                match &*val {
                                    MValue::Nil => smallvec![Machine { comp: nilk.clone(), ..m}],
                                    MValue::Cons(v, w) => {
                                        let env = m.env.extend_val(v.clone(), env.clone()).extend_val(w.clone(), env.clone());
                                        smallvec![Machine { comp: consk.clone(), env, ..m}]
                                    },
                                    _ => panic!("Match on non-list")
                                }
                            },
                            VClosure::LogicVar { ident } => {  // must be unresolved, by structure of close_head
                                                              
                                let ptype = match m.lenv.get_type(ident) {
                                    ValueType::List(t) => t,
                                    _ => panic!("matching on a non-list logical variable")
                                };

                                let m_nil  = {
                                    
                                    let mut lenv = m.lenv.clone();
                                    lenv.set_vclos(ident, VClosure::mk_clos(&MValue::Nil.into(), &Env::empty().into()));

                                    Machine { comp: nilk.clone(), lenv, ..m.clone()}
                                };
                                
                                let m_cons = {
                                    
                                    let mut lenv = m.lenv.clone();
                                    let head_ident = lenv.fresh(*ptype.clone());
                                    let tail_ident = lenv.fresh(ValueType::List(ptype));
                                    
                                    lenv.set_vclos(ident, VClosure::mk_clos(
                                         &MValue::Cons(MValue::Var(1).into(), MValue::Var(0).into()).into(),
                                         &Env::empty().extend_lvar(head_ident).extend_lvar(tail_ident).into()
                                    ));
                                    
                                    let env = m.env.extend_lvar(head_ident).extend_lvar(tail_ident);

                                    Machine { comp: consk.clone(), lenv, env, ..m.clone()}
                                };
                                smallvec![m_nil, m_cons]
                            }
                            VClosure::Susp { ident } => unreachable!("shouldn't be matching on a suspension"),
                        }
                }
            },
            MComputation::Case { sum, inlk, inrk } => {
                let vclos = VClosure::mk_clos(sum, &m.env);
                let closed_sum = vclos.close_head(&m.lenv, &m.senv);
                match closed_sum {
                    Err(a) => smallvec![ eval_susp_then(a, m) ],
                    Ok(vclos) => 
                        match vclos {
                            VClosure::Clos { val, env } => {
                                match &*val {
                                    MValue::Inl(v) => {
                                        let old_env = env.clone();
                                        let new_env = m.env.extend_val(v.clone(), old_env.clone());
                                        smallvec![Machine { comp: inlk.clone(), env : new_env, ..m}]
                                    },
                                    MValue::Inr(v) => {
                                        let old_env = env.clone();
                                        let new_env = m.env.extend_val(v.clone(), old_env.clone());
                                        smallvec![Machine { comp: inrk.clone(), env : new_env, ..m}]
                                    },
                                    _ => panic!("Match on non-list")
                                }
                            },
                            VClosure::LogicVar { ident } => {  // must be unresolved, by structure of close_head
                                                              
                                let (ptype1, ptype2) = match m.lenv.get_type(ident) {
                                    ValueType::Sum(t1, t2) => (t1, t2),
                                    _ => panic!("casing on a non-sum logical variable")
                                };

                                let m_inl = {
                                    let mut lenv = m.lenv.clone();
                                    let inl_ident = lenv.fresh(*ptype1.clone());

                                    lenv.set_vclos(ident, VClosure::mk_clos(
                                            &MValue::Inl(MValue::Var(0).into()).into(),
                                            &Env::empty().extend_lvar(inl_ident)
                                    ));

                                    let env = m.env.extend_lvar(inl_ident);

                                    Machine { comp: inlk.clone(), lenv, env, ..m.clone()}
                                };

                                let m_inr = {
                                    let mut lenv = m.lenv.clone();
                                    let inr_ident = lenv.fresh(*ptype2.clone());

                                    lenv.set_vclos(ident, VClosure::mk_clos(
                                            &MValue::Inr(MValue::Var(0).into()).into(),
                                            &Env::empty().extend_lvar(inr_ident)
                                    ));

                                    let env = m.env.extend_lvar(inr_ident);

                                    Machine { comp: inrk.clone(), lenv, env, ..m.clone()}
                                };

                                smallvec![m_inl, m_inr]
                            }
                            VClosure::Susp { ident } => unreachable!("oops")
                        }
                }
            },
            MComputation::Rec { body } => {
                let env = m.env.extend_val(m.comp.thunk(), m.env.clone());
                smallvec![Machine { comp : body.clone(), env, ..m }] 
            },
        }
    }
    
}