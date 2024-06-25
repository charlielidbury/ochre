use std::rc::Rc;

use crate::{
    abstract_::{Atom, Env, OchreType, Pair, Type},
    ast::{Ast, AstData, OError},
    erased_write_op::erased_write_op,
    max_op::max_erased_write_op,
};

pub fn erased_read_op(env: &mut Env, ast: Ast) -> Result<OchreType, OError> {
    match &*ast.data {
        // Things which are straight env lookups
        AstData::RuntimeVar(x) | AstData::ComptimeVar(x) => Ok(env.get(x.clone())?),
        AstData::PairLeft(p_ast) => {
            let Type::Pair(p) = &*erased_read_op(env, p_ast.clone())? else {
                return Err(p_ast.error(format!("attempt to get left element of non-pair")));
            };

            let (l, _) = p.split(env)?;

            Ok(l)
        }
        AstData::PairRight(p_ast) => {
            let Type::Pair(p) = &*erased_read_op(env, p_ast.clone())? else {
                return Err(p_ast.error(format!("attempt to get left element of non-pair")));
            };

            let (_, r) = p.split(env)?;

            Ok(r)
        }
        AstData::Deref(_) => todo!("erased_read Deref"),
        AstData::App(f_term, a_term) => {
            let env = &mut env.comptime();
            // eval function
            let Type::Func(i_term, o_term) = &*erased_read_op(env, f_term.clone())? else {
                return Err(f_term.error("not a compile time function"));
            };
            // eval argument
            let t = erased_read_op(env, a_term.clone())?;
            // eval return type
            erased_write_op(env, i_term.clone(), t)?;
            let ret = erased_read_op(env, o_term.clone())?;

            Ok(ret)
        }
        AstData::RuntimeFun(_, _, _) => {
            Err(ast.error("Compile time functions must not have a body"))
        }
        AstData::ComptimeFun(i_term, o_term) => {
            // Check function body with max value
            let env = &mut env.comptime();
            max_erased_write_op(env, i_term.clone())?;
            erased_read_op(env, o_term.clone())?;

            Ok(Rc::new(Type::Func(i_term.clone(), o_term.clone())))
        }
        AstData::Pair(l_ast, r_ast) => {
            let l = erased_read_op(env, l_ast.clone())?;
            let (l_term, r_term) = match &*r_ast.data {
                AstData::ComptimeFun(l_term, r_term) => (l_term.clone(), r_term.clone()),
                _ => (Ast::new(None, AstData::Top), r_ast.clone()),
            };
            Ok(Rc::new(Type::Pair(Pair { l, l_term, r_term })))
        }
        AstData::Atom(s) => Ok(Rc::new(Atom::new(s).into())),
        AstData::Union(lhs, rhs) => {
            let lhs = erased_read_op(env, lhs.clone())?;
            let rhs = erased_read_op(env, rhs.clone())?;
            Ok(lhs.union(env, &rhs)?)
        }
        AstData::Annot(_, _) => todo!("erased_read Annot"),
        AstData::Seq(lhs, rhs) => {
            erased_read_op(env, lhs.clone())?;
            let rhs_val = erased_read_op(env, rhs.clone())?;

            Ok(rhs_val)
        }
        AstData::Match(scrutinee, branches) => {
            // evaluate scrutinee
            let scrutinee_ty = erased_read_op(env, scrutinee.clone())?;

            let mut result: Option<(OchreType, OchreType)> = None;

            for (branch_l, branch_r) in branches {
                let mut env = env.clone();
                // get type of branch
                let branch_in = erased_read_op(&mut env, branch_l.clone())?;
                // narrow down scrutinee
                erased_write_op(&mut env, scrutinee.clone(), branch_in.clone())?;
                // execute branch
                let branch_out = erased_read_op(&mut env, branch_r.clone())?;
                // union onto result
                result = Some(match result {
                    None => (branch_in, branch_out),
                    Some((total_in, total_out)) => (
                        total_in.union(&mut env, &*branch_in)?,
                        total_out.union(&mut env, &*branch_out)?,
                    ),
                });
            }

            match result {
                None => Err(ast.error("match statement has no branches"))?,
                Some((total_in, total_out)) => {
                    // resultant environment has all runtime effects erased
                    *env = env.comptime();

                    // match must be exhaustive
                    if !scrutinee_ty.subtype(env, &*total_in)? {
                        return Err(scrutinee.error("branches not exhaustive"));
                    }

                    Ok(total_out)
                }
            }
        }
        AstData::Ref(ty_term) => {
            let ty = erased_read_op(env, ty_term.clone())?;
            let loan_id = env.loan_restriction(ty.clone());
            Ok(Rc::new(Type::BorrowS(loan_id, ty)))
        }
        AstData::MutRef(ty_term) => {
            let ty = erased_read_op(env, ty_term.clone())?;
            let loan_id = env.loan_restriction(ty.clone());
            Ok(Rc::new(Type::BorrowM(loan_id, ty)))
        }
        AstData::Ass(lhs, rhs) => {
            if !lhs.runtime_comptime().1 {
                Err(ast.error("lhs must be comptime"))
            } else {
                // comptime assignment
                let rhs_type = erased_read_op(env, rhs.clone())?;
                erased_write_op(env, lhs.clone(), rhs_type)?;
                // assignments evaluate to 'unit
                let unit = Atom::new("unit");
                Ok(Rc::new(unit.into()))
            }
        }
        AstData::Top => Ok(Rc::new(Type::Top)),
        AstData::Type(ty) => Ok(ty.clone()),
        AstData::TypeQuestion(_) => todo!("erased_read TypeQuestion"),
    }
}
