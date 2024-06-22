use std::mem;
use std::rc::Rc;

use crate::abstract_::{AbstractValue, Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use crate::erased_read_op::erased_read_op;
use crate::write_op::write_op;
use proc_macro2::Ident;
use proc_macro2::{Span, TokenStream};
use quote::quote;

pub fn move_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), OError> {
    match &*ast.data {
        AstData::RuntimeVar(x) => {
            // Get value for x
            let v = match env.state.get_mut(x) {
                None => return Err(ast.error(format!("attempt to move non-existant value"))),
                Some(AbstractValue::Comptime(_)) => {
                    return Err(ast.error(format!("attempt to move comptime value")))
                }
                Some(AbstractValue::Runtime(v)) => v,
            };
            // Replace it with bot
            let mut x_val = Rc::new(Type::Top);
            mem::swap(&mut x_val, v);
            // Generate identifier (union is copy so old ident still usable)
            let id_x = Ident::new(x, Span::call_site());
            Ok((quote!(#id_x), x_val))
        }
        AstData::ComptimeVar(x) => {
            Err(ast.error(format!("Cannot use comptime var {} in runtime context", x)))
        }
        AstData::PairLeft(_) => todo!("move PairLeft"),
        AstData::PairRight(_) => todo!("move PairRight"),
        AstData::Deref(_) => todo!("move Deref"),
        AstData::App(_, _) => todo!("move App"),
        AstData::Fun(_, _, _) => todo!("move Fun"),
        AstData::Pair(l, r) => {
            let (l_code, l_val) = move_op(env, l.clone())?;
            let (r_code, r_val) = move_op(env, r.clone())?;
            Ok((
                quote!(OchreValue { pair: Box::leak(Box::new(({ #l_code }, { #r_code }))) }),
                Rc::new(Type::Pair(
                    l_val,
                    Ast::new(None, AstData::Top),
                    Ast::new(None, AstData::Type(r_val)),
                )),
            ))
        }
        AstData::Let(_, _, _) => todo!("move Let"),
        AstData::Atom(s) => {
            let atom = Atom::new(s);
            let atom_hash = atom.hash();
            Ok((quote!(OchreValue{ atom: #atom_hash }), Rc::new(atom.into())))
        }
        AstData::Union(_, _) => todo!("move Union"),
        AstData::Seq(lhs, rhs) => {
            // Evaluate lhs
            let (lhs_code, lhs_val) = move_op(env, lhs.clone())?;
            // Drop lhs
            let drop_code = drop_op(env, lhs_val)?;
            dbg!(&env);
            // Evaluate rhs
            let (rhs_code, rhs_val) = move_op(env, rhs.clone())?;
            // Return code
            Ok((quote!(#lhs_code; #drop_code; #rhs_code), rhs_val))
        }
        AstData::Case(_, _) => todo!("move Case"),
        AstData::Ref(_) => todo!("move Ref"),
        AstData::MutRef(ast) => {
            let (_, m) = move_op(env, ast.clone())?;
            write_op(env, ast.clone(), Rc::new(Type::LoanM(42)));
            todo!("move MutRef")
        }
        AstData::Ass(lhs, rhs) => {
            // evaluate rhs
            let (rhs_code, rhs_type) = move_op(env, rhs.clone())?;
            // write to lhs
            // let alloc_code = env.bot(lhs.clone())?;
            let lhs_code = write_op(env, lhs.clone(), rhs_type)?;
            // assignments evaluate to 'unit
            let unit = Atom::new("unit");
            let unit_hash = unit.hash();
            // combine
            Ok((
                quote!(#lhs_code = #rhs_code; OchreValue { atom: #unit_hash }),
                Rc::new(unit.into()),
            ))
        }
        AstData::Top => todo!("Top"),
        AstData::Annot(term, term_type) => {
            let (_, term) = move_op(env, term.clone())?;
            let term_type = erased_read_op(env, term_type.clone())?;
            if term.subtype(&*term_type) {
                Ok((quote!(), term_type))
            } else {
                Err(ast.error(format!("{} is not of type {}", term, term_type)))
            }
        }
        AstData::Type(_) => todo!("move Type"),
    }
}
