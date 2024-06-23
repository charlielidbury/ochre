use std::mem;
use std::rc::Rc;

use crate::abstract_::{AbstractValue, Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use crate::erased_read_op::erased_read_op;
use crate::erased_write_op::erased_write_op;
use crate::write_op::write_op;
use proc_macro2::Ident;
use proc_macro2::{Span, TokenStream};
use quote::quote;

pub fn read_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), OError> {
    match &*ast.data {
        AstData::RuntimeVar(_)
        | AstData::ComptimeVar(_)
        | AstData::PairLeft(_)
        | AstData::PairRight(_) => Ok((quote!(), env.get(ast)?)),
        AstData::Deref(_) => todo!("read_op Deref"),
        AstData::App(_, _) => todo!("read_op App"),
        AstData::Fun(_, _, _) => todo!("read_op Fun"),
        AstData::Pair(_, _) => todo!("read_op Pair"),
        AstData::Atom(_) => todo!("read_op Atom"),
        AstData::Union(_, _) => todo!("read_op Union"),
        AstData::Annot(_, _) => todo!("read_op Annot"),
        AstData::Seq(_, _) => todo!("read_op Seq"),
        AstData::Case(_, _) => todo!("read_op Case"),
        AstData::Ref(_) => todo!("read_op Ref"),
        AstData::MutRef(_) => todo!("read_op MutRef"),
        AstData::Ass(_, _) => todo!("read_op Ass"),
        AstData::Top => todo!("read_op Top"),
        AstData::Type(_) => todo!("read_op Type"),
    }
}
