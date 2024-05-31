use std::rc::Rc;

use crate::abstract_::{AbstractValue, Env, OchreType, Type};
use crate::ast::{Ast, AstData};
use im_rc::HashSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

pub fn write_op(
    env: &mut Env,
    ast: Ast,
    val: OchreType,
) -> Result<proc_macro2::TokenStream, String> {
    match (&*ast, &*val) {
        (AstData::Var(x), _) => {
            // Make sure there is nothing in x
            env.bot(ast.clone())?;
            assert_eq!(
                env.state.get(x),
                Some(&AbstractValue::Runtime(Rc::new(Type::Top)))
            );
            // put new x type in env
            env.narrow(ast.clone(), val.clone())?;
            // Generate x
            let ident = Ident::new(x, Span::call_site());
            Ok(quote!(#ident))
        }
        (AstData::Pair(l, r), Type::Pair(m, n, _, _)) => {
            write_op(env, l.clone(), m.clone())?;
            write_op(env, r.clone(), n.clone())?;
            Ok(quote!())
        }
        (AstData::PairLeft(_), _) => todo!("write_op PairLeft"),
        (AstData::PairRight(_), _) => todo!("write_op PairRight"),
        (AstData::Deref(_), _) => todo!("write_op Deref"),
        (AstData::App(_, _), _) => todo!("write_op App"),
        (AstData::Fun(_, _, _), _) => todo!("write_op Fun"),
        (AstData::Let(_, _, _), _) => todo!("write_op Let"),
        (AstData::Atom(_), _) => todo!("write_op Atom"),
        (AstData::Union(_, _), _) => todo!("write_op Union"),
        (AstData::Seq(_, _), _) => todo!("write_op Seq"),
        (AstData::Case(_, _), _) => todo!("write_op Case"),
        (AstData::Ref(_), _) => todo!("write_op Ref"),
        (AstData::MutRef(_), _) => todo!("write_op MutRef"),
        (AstData::Ass(_, _), _) => todo!("write_op Ass"),
        (AstData::Moved, _) => todo!("write_op Moved"),
        (AstData::Top, _) => todo!("write_op Top"),
        (syntax, val) => Err(format!("Attempt to write {:?} to {:?}", val, syntax)),
    }
}
