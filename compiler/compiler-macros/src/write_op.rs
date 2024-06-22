use std::rc::Rc;

use crate::abstract_::{AbstractValue, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use im_rc::HashSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

pub fn write_op(
    env: &mut Env,
    ast: Ast,
    val: OchreType,
) -> Result<proc_macro2::TokenStream, OError> {
    match (&*ast.data, &*val) {
        (AstData::RuntimeVar(x), _) => {
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
        (AstData::Pair(l, r), Type::Pair(m, m_term, n_term)) => {
            match (&*m_term.data, &*n_term.data) {
                (AstData::Top, AstData::Type(n)) => {
                    write_op(env, l.clone(), m.clone())?;
                    write_op(env, r.clone(), n.clone())?;
                    Ok(quote!())
                }
                _ => unimplemented!("write dependent pair"),
            }
        }
        (AstData::PairLeft(p_ast), val) => {
            // Get value which will be overrwriten
            let p = env.get(p_ast.clone())?;
            let Type::Pair(l, l_term, r_term) = &*p else {
                return Err(ast.error(format!("attempt to edit left element of non-pair {:?}", p)));
            };
            drop_op(env, l.clone())?; // drop the value which will be overwrriten
            assert!(
                matches!(&*l_term.data, AstData::Top),
                "attempt to edit non-depedenent pair"
            );

            // Write back with new value
            write_op(
                env,
                p_ast.clone(),
                Rc::new(Type::Pair(
                    Rc::new(val.clone()),
                    l_term.clone(),
                    r_term.clone(),
                )),
            )?;

            Ok(quote!())
        }
        (AstData::PairRight(p_ast), _) => {
            // Get value which will be overrwriten
            let p = env.get(p_ast.clone())?;
            let Type::Pair(l, l_term, r_term) = &*p else {
                return Err(ast.error(format!("attempt to edit right element of non-pair {:?}", p)));
            };
            // TODO: drop rhs
            // assert!(
            //     matches!(&**l_term, AstData::Top),
            //     "attempt to edit non-depedenent pair"
            // );

            // Write back with new value
            write_op(
                env,
                p_ast.clone(),
                Rc::new(Type::Pair(
                    l.clone(),
                    Ast::new(None, AstData::Top),
                    Ast::new(None, AstData::Type(val.clone())),
                )),
            )?;

            Ok(quote!())
        }
        (AstData::Deref(_), _) => todo!("write_op Deref"),
        (AstData::App(_, _), _) => todo!("write_op App"),
        (AstData::Fun(_, _, _), _) => todo!("write_op Fun"),
        (AstData::Atom(_), _) => todo!("write_op Atom"),
        (AstData::Union(_, _), _) => todo!("write_op Union"),
        (AstData::Seq(_, _), _) => todo!("write_op Seq"),
        (AstData::Case(_, _), _) => todo!("write_op Case"),
        (AstData::Ref(_), _) => todo!("write_op Ref"),
        (AstData::MutRef(_), _) => todo!("write_op MutRef"),
        (AstData::Ass(_, _), _) => todo!("write_op Ass"),
        (AstData::Top, _) => todo!("write_op Top"),
        (syntax, val) => Err(ast.error(format!("Attempt to write {:?} to {:?}", val, syntax))),
    }
}
