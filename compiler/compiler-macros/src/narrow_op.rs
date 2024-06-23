use crate::abstract_::{Env, OchreType};
use crate::ast::{Ast, AstData, OError};
use quote::quote;

pub fn narrow_op(
    env: &mut Env,
    ast: Ast,
    val: OchreType,
) -> Result<proc_macro2::TokenStream, OError> {
    match &*ast.data {
        AstData::RuntimeVar(_) | AstData::ComptimeVar(_) => {
            let old_val = env.set(ast.clone(), val.clone())?;
            if !val.subtype(env, &*old_val)? {
                return Err(ast.error(format!("type narrowed down to a supertype")));
            }
            Ok(quote!())
        }
        AstData::PairLeft(_) => todo!("narrow_op PairLeft"),
        AstData::PairRight(_) => todo!("narrow_op PairRight"),
        AstData::Deref(_) => todo!("narrow_op Deref"),
        AstData::App(_, _) => todo!("narrow_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("narrow_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("narrow_op ComptimeFun"),
        AstData::Pair(_, _) => todo!("narrow_op Pair"),
        AstData::Atom(_) => todo!("narrow_op Atom"),
        AstData::Union(_, _) => todo!("narrow_op Union"),
        AstData::Annot(_, _) => todo!("narrow_op Annot"),
        AstData::Seq(_, _) => todo!("narrow_op Seq"),
        AstData::Case(_, _) => todo!("narrow_op Case"),
        AstData::Ref(_) => todo!("narrow_op Ref"),
        AstData::MutRef(_) => todo!("narrow_op MutRef"),
        AstData::Ass(_, _) => todo!("narrow_op Ass"),
        AstData::Top => Ok(quote!()),
        AstData::Type(_) => todo!("narrow_op Type"),
        AstData::TypeQuestion(_) => todo!("narrow_op TypeQuestion"),
    }
}
