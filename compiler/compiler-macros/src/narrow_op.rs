use crate::abstract_::{Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use im_rc::HashSet;
use quote::quote;

pub fn narrow_op(env: &mut Env, ast: Ast, val: OchreType) -> Result<(), OError> {
    match &*ast.data {
        AstData::RuntimeVar(_) | AstData::ComptimeVar(_) => {
            let old_val = env.set(ast.clone(), val.clone())?;
            if !val.subtype(env, &*old_val)? {
                return Err(ast.error(format!("type narrowed down to a supertype")));
            }
            Ok(())
        }
        AstData::PairLeft(_) => todo!("narrow_op PairLeft"),
        AstData::PairRight(_) => todo!("narrow_op PairRight"),
        AstData::Deref(_) => todo!("narrow_op Deref"),
        AstData::App(_, _) => todo!("narrow_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("narrow_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("narrow_op ComptimeFun"),
        AstData::Pair(_, _) => todo!("narrow_op Pair"),
        AstData::Atom(s) => match &*val {
            Type::Atom(ss) if *ss == HashSet::unit(Atom::new(s)) => Ok(()),
            _ => Err(ast.error(format!("cannot be narrowed down to {}", val))),
        },
        AstData::Union(_, _) => todo!("narrow_op Union"),
        AstData::Annot(_, _) => todo!("narrow_op Annot"),
        AstData::Seq(_, _) => todo!("narrow_op Seq"),
        AstData::Match(_, _) => todo!("narrow_op Match"),
        AstData::Ref(_) => todo!("narrow_op Ref"),
        AstData::MutRef(_) => todo!("narrow_op MutRef"),
        AstData::Ass(_, _) => todo!("narrow_op Ass"),
        AstData::Top => Ok(()),
        AstData::Type(_) => todo!("narrow_op Type"),
        AstData::TypeQuestion(_) => todo!("narrow_op TypeQuestion"),
    }
}
