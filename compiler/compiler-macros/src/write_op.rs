use std::rc::Rc;

use crate::abstract_::{Env, OchreType, Pair, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use crate::move_op::move_op;
use proc_macro2::{Ident, Span};
use quote::quote;

pub fn write_op(
    env: &mut Env,
    ast: Ast,
    val: OchreType,
) -> Result<proc_macro2::TokenStream, OError> {
    match (&*ast.data, &*val) {
        (AstData::RuntimeVar(x), _) => {
            // put new x type in env
            let old_val = env.set(ast.clone(), val.clone())?;
            drop_op(env, old_val)?;
            // Generate x
            let ident = Ident::new(x, Span::call_site());
            Ok(quote!(#ident))
        }
        (AstData::Pair(l, r), Type::Pair(p)) => {
            let (l_ty, r_ty) = p.get(env)?;
            write_op(env, l.clone(), l_ty)?;
            write_op(env, r.clone(), r_ty)?;
            Ok(quote!())
        }
        (AstData::PairLeft(p_ast), val) => {
            // Get value which will be overrwriten
            let p = env.get(p_ast.clone())?;
            let Type::Pair(p) = &*p else {
                return Err(ast.error(format!("attempt to edit left element of non-pair {:?}", p)));
            };
            let (l, r) = p.get(env)?;
            drop_op(env, l)?; // drop the value which will be overwrriten

            // Write back with new value
            write_op(
                env,
                p_ast.clone(),
                Rc::new(Type::Pair(Pair::new(Rc::new(val.clone()), r))),
            )?;

            Ok(quote!())
        }
        (AstData::PairRight(p_ast), _) => {
            // Get value which will be overrwriten
            let p = env.get(p_ast.clone())?;
            let Type::Pair(p) = &*p else {
                return Err(ast.error(format!("attempt to edit right element of non-pair {:?}", p)));
            };
            let (l, r) = p.get(env)?;
            drop_op(env, r)?; // drop the value which will be overwrriten

            // Write back with new value
            write_op(env, p_ast.clone(), Rc::new(Type::Pair(Pair::new(l, val))))?;

            Ok(quote!())
        }
        (AstData::Deref(r_ast), _) => {
            let (_code, t_ref) = move_op(env, r_ast.clone())?;
            let Type::BorrowM(loan_id, old_val) = &*t_ref else {
                return Err(ast.error(format!("cannot mutate through a {}", t_ref)));
            };
            drop_op(env, old_val.clone())?;

            write_op(env, r_ast.clone(), Rc::new(Type::BorrowM(*loan_id, val)))?;

            Ok(quote!())
        }
        (AstData::App(_, _), _) => todo!("write_op App"),
        (AstData::RuntimeFun(_, _, _), _) => todo!("write_op RuntimeFun"),
        (AstData::ComptimeFun(_, _), _) => todo!("write_op ComptimeFun"),
        (AstData::Atom(_), _) => todo!("write_op Atom"),
        (AstData::Union(_, _), _) => todo!("write_op Union"),
        (AstData::Seq(_, _), _) => todo!("write_op Seq"),
        (AstData::Case(_, _), _) => todo!("write_op Case"),
        (AstData::Ref(_), _) => todo!("write_op Ref"),
        (AstData::MutRef(_), _) => todo!("write_op MutRef"),
        (AstData::Ass(_, _), _) => todo!("write_op Ass"),
        (AstData::Top, val) => {
            drop_op(env, Rc::new(val.clone()))?;
            Ok(quote!())
        }
        (syntax, val) => Err(ast.error(format!("Attempt to write {:?} to {:?}", val, syntax))),
    }
}
