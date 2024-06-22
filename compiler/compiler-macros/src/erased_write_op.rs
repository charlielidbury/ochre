use std::rc::Rc;

use crate::abstract_::{AbstractValue, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use im_rc::HashSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

pub fn erased_write_op(env: &mut Env, ast: Ast, val: OchreType) -> Result<(), OError> {
    match (&*ast.data, &*val) {
        (AstData::ComptimeVar(x), _) => {
            env.bot(ast.clone())?;
            env.narrow(ast.clone(), val)?;
            Ok(())
        }
        (AstData::Pair(l, r), Type::Pair(m, m_term, n_term)) => todo!("erased_write_op Pair"),
        (AstData::PairLeft(p_ast), val) => todo!("erased_write_op PairLeft"),
        (AstData::PairRight(p_ast), _) => todo!("erased_write_op PairRight"),
        (AstData::Deref(_), _) => todo!("erased_write_op Deref"),
        (AstData::App(_, _), _) => todo!("erased_write_op App"),
        (AstData::Fun(_, _, _), _) => todo!("erased_write_op Fun"),
        (AstData::Atom(_), _) => todo!("erased_write_op Atom"),
        (AstData::Union(_, _), _) => todo!("erased_write_op Union"),
        (AstData::Seq(_, _), _) => todo!("erased_write_op Seq"),
        (AstData::Case(_, _), _) => todo!("erased_write_op Case"),
        (AstData::Ref(_), _) => todo!("erased_write_op Ref"),
        (AstData::MutRef(_), _) => todo!("erased_write_op MutRef"),
        (AstData::Ass(_, _), _) => todo!("erased_write_op Ass"),
        (AstData::Top, _) => todo!("erased_write_op Top"),
        (syntax, val) => Err(ast.error(format!("Attempt to write {} to {}", val, syntax))),
    }
}
