use std::rc::Rc;

use crate::abstract_::{AbstractValue, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use crate::move_op::move_op;
use im_rc::HashSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

pub fn narrow_op(
    env: &mut Env,
    ast: Ast,
    val: OchreType,
) -> Result<proc_macro2::TokenStream, OError> {
    match &*ast.data {
        AstData::RuntimeVar(_) | AstData::ComptimeVar(_) => {
            env.narrow(ast, val)?;
            Ok(quote!())
        }
        AstData::PairLeft(_) => todo!("narrow_op PairLeft"),
        AstData::PairRight(_) => todo!("narrow_op PairRight"),
        AstData::Deref(_) => todo!("narrow_op Deref"),
        AstData::App(_, _) => todo!("narrow_op App"),
        AstData::Fun(_, _, _) => todo!("narrow_op Fun"),
        AstData::Pair(_, _) => todo!("narrow_op Pair"),
        AstData::Atom(_) => todo!("narrow_op Atom"),
        AstData::Union(_, _) => todo!("narrow_op Union"),
        AstData::Annot(_, _) => todo!("narrow_op Annot"),
        AstData::Seq(_, _) => todo!("narrow_op Seq"),
        AstData::Case(_, _) => todo!("narrow_op Case"),
        AstData::Ref(_) => todo!("narrow_op Ref"),
        AstData::MutRef(_) => todo!("narrow_op MutRef"),
        AstData::Ass(_, _) => todo!("narrow_op Ass"),
        AstData::Top => todo!("narrow_op Top"),
        AstData::Type(_) => todo!("narrow_op Type"),
        AstData::TypeQuestion(_) => todo!("narrow_op TypeQuestion"),
    }
}
