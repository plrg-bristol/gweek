use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::MValue;
use super::senv::{SuspAt, SuspEnv};
use super::VClosure;

pub enum UnifyError<'a> {
    Occurs,
    Fail,
    Susp(SuspAt<'a>),
}

pub fn unify<'a>(
    lhs: &'a MValue<'a>,
    rhs: &'a MValue<'a>,
    env: Env<'a>,
    lenv: &mut LogicEnv<'a>,
    senv: &SuspEnv<'a>,
) -> Result<(), UnifyError<'a>> {
    let mut q: Vec<(VClosure<'a>, VClosure<'a>)> = Vec::new();
    q.push((VClosure::mk_clos(lhs, env), VClosure::mk_clos(rhs, env)));

    while let Some((lhs, rhs)) = q.pop() {
        let lhs = lhs.close_head(lenv, senv).map_err(UnifyError::Susp)?;
        let rhs = rhs.close_head(lenv, senv).map_err(UnifyError::Susp)?;

        match (&lhs, &rhs) {
            (VClosure::LogicVar { ident: id1 }, VClosure::LogicVar { ident: id2 }) => {
                lenv.identify(*id1, *id2);
            }
            (VClosure::LogicVar { ident }, _) => {
                if rhs.occurs_lvar(lenv, senv, *ident).map_err(UnifyError::Susp)? {
                    return Err(UnifyError::Occurs);
                }
                lenv.set_vclos(*ident, rhs);
            }
            (_, VClosure::LogicVar { ident }) => {
                if lhs.occurs_lvar(lenv, senv, *ident).map_err(UnifyError::Susp)? {
                    return Err(UnifyError::Occurs);
                }
                lenv.set_vclos(*ident, lhs);
            }
            (
                VClosure::Clos {
                    val: lv,
                    env: lenv_r,
                },
                VClosure::Clos {
                    val: rv,
                    env: renv_r,
                },
            ) => match (lv, rv) {
                (MValue::Unit, MValue::Unit)
                | (MValue::Zero, MValue::Zero)
                | (MValue::Nil, MValue::Nil) => continue,
                (MValue::Succ(v), MValue::Succ(w)) => {
                    q.push((VClosure::mk_clos(v, *lenv_r), VClosure::mk_clos(w, *renv_r)));
                }
                (MValue::Cons(x, xs), MValue::Cons(y, ys)) => {
                    q.push((VClosure::mk_clos(x, *lenv_r), VClosure::mk_clos(y, *renv_r)));
                    q.push((VClosure::mk_clos(xs, *lenv_r), VClosure::mk_clos(ys, *renv_r)));
                }
                (MValue::Thunk(_), _) | (_, MValue::Thunk(_)) => {
                    panic!("tried to unify a thunk")
                }
                _ => return Err(UnifyError::Fail),
            },
            (VClosure::Susp { .. }, _) | (_, VClosure::Susp { .. }) => {
                unreachable!("tried to unify a suspension")
            }
        }
    }
    Ok(())
}
