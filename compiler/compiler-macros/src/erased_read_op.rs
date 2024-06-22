use std::rc::Rc;

use crate::{
    abstract_::{Atom, Env, OchreType, Type},
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
        AstData::Fun(_, _, _) => todo!("erased_read Fun"),
        AstData::Pair(lhs, rhs) => {
            let lhs = erased_read_op(env, lhs.clone())?;
            let rhs = erased_read_op(env, rhs.clone())?;
            Ok(Rc::new(Type::Pair(
                lhs,
                Ast::new(None, AstData::Top),
                Ast::new(None, AstData::Type(rhs)),
            )))
        }
        AstData::Let(_, _, _) => todo!("erased_read Let"),
        AstData::Atom(s) => Ok(Rc::new(Atom::new(s).into())),
        AstData::Union(lhs, rhs) => {
            let lhs = erased_read_op(env, lhs.clone())?;
            let rhs = erased_read_op(env, rhs.clone())?;
            Ok(lhs.union(&*rhs)?)
        }
        AstData::Annot(_, _) => todo!("erased_read Annot"),
        AstData::Seq(_, _) => todo!("erased_read Seq"),
        AstData::Case(_, _) => todo!("erased_read Case"),
        AstData::Ref(_) => todo!("erased_read Ref"),
        AstData::MutRef(_) => todo!("erased_read MutRef"),
        AstData::Ass(_, _) => todo!("erased_read Ass"),
        AstData::Top => todo!("erased_read Top"),
        AstData::Type(_) => todo!("erased_read Type"),
    }
}
