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
        AstData::RuntimeVar(_)
        | AstData::ComptimeVar(_)
        | AstData::PairLeft(_)
        | AstData::PairRight(_) => Ok(env.get(ast)?),
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
            dbg!(&l_term, &r_term);
            Ok(Rc::new(Type::Pair(Pair { l, l_term, r_term })))
        }
        AstData::Atom(s) => Ok(Rc::new(Atom::new(s).into())),
        AstData::Union(lhs, rhs) => {
            let lhs = erased_read_op(env, lhs.clone())?;
            let rhs = erased_read_op(env, rhs.clone())?;
            Ok(lhs.union(env, &rhs)?)
        }
        AstData::Annot(_, _) => todo!("erased_read Annot"),
        AstData::Seq(_, _) => todo!("erased_read Seq"),
        AstData::Match(_, _) => todo!("erased_read Match"),
        AstData::Ref(_) => todo!("erased_read Ref"),
        AstData::MutRef(_) => todo!("erased_read MutRef"),
        AstData::Ass(_, _) => todo!("erased_read Ass"),
        AstData::Top => Ok(Rc::new(Type::Top)),
        AstData::Type(ty) => Ok(ty.clone()),
        AstData::TypeQuestion(_) => todo!("erased_read TypeQuestion"),
    }
}
