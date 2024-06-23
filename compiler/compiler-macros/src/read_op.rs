use std::rc::Rc;

use crate::abstract_::{Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use quote::quote;

pub fn read_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), OError> {
    match &*ast.data {
        AstData::RuntimeVar(_)
        | AstData::ComptimeVar(_)
        | AstData::PairLeft(_)
        | AstData::PairRight(_) => Ok((quote!(), env.get(ast)?)),
        AstData::Deref(_) => todo!("read_op Deref"),
        AstData::App(_, _) => todo!("read_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("read_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("read_op ComptimeFun"),
        AstData::Pair(_, _) => todo!("read_op Pair"),
        AstData::Atom(_) => todo!("read_op Atom"),
        AstData::Union(_, _) => todo!("read_op Union"),
        AstData::Annot(_, _) => todo!("read_op Annot"),
        AstData::Seq(_, _) => todo!("read_op Seq"),
        AstData::Case(_, _) => todo!("read_op Case"),
        AstData::Ref(_) => todo!("read_op Ref"),
        AstData::MutRef(_) => todo!("read_op MutRef"),
        AstData::Ass(_, _) => todo!("read_op Ass"),
        AstData::Top => Ok((quote!(), Rc::new(Type::Top))),
        AstData::Type(_) => todo!("read_op Type"),
        AstData::TypeQuestion(_) => todo!("read_op TypeQuestion"),
    }
}
