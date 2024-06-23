use std::rc::Rc;

use crate::{
    abstract_::{Atom, Env, OchreType, Pair, Type},
    ast::{Ast, AstData, OError},
};

pub fn erased_read_op(env: &mut Env, ast: Ast) -> Result<OchreType, OError> {
    match &*ast.data {
        // Things which are straight env lookups
        AstData::RuntimeVar(_)
        | AstData::ComptimeVar(_)
        | AstData::PairLeft(_)
        | AstData::PairRight(_) => Ok(env.get(ast)?),
        AstData::Deref(_) => todo!("erased_read Deref"),
        AstData::App(_, _) => todo!("erased_read App"),
        AstData::RuntimeFun(_, _, _) => todo!("erased_read RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("erased_read ComptimeFun"),
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
            Ok(lhs.union(&rhs)?)
        }
        AstData::Annot(_, _) => todo!("erased_read Annot"),
        AstData::Seq(_, _) => todo!("erased_read Seq"),
        AstData::Case(_, _) => todo!("erased_read Case"),
        AstData::Ref(_) => todo!("erased_read Ref"),
        AstData::MutRef(_) => todo!("erased_read MutRef"),
        AstData::Ass(_, _) => todo!("erased_read Ass"),
        AstData::Top => Ok(Rc::new(Type::Top)),
        AstData::Type(ty) => Ok(ty.clone()),
        AstData::TypeQuestion(_) => todo!("erased_read TypeQuestion"),
    }
}
