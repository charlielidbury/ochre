use std::mem;
use std::rc::Rc;

use crate::abstract_::{AbstractValue, Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use crate::drop_op::drop_op;
use crate::erased_read_op::erased_read_op;
use crate::erased_write_op::erased_write_op;
use crate::narrow_op::narrow_op;
use crate::read_op::read_op;
use crate::write_op::write_op;
use proc_macro;
use proc_macro2::Ident;
use proc_macro2::{Span, TokenStream};
use quote::quote;

pub fn move_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), OError> {
    match &*ast.data {
        AstData::RuntimeVar(x) => {
            let ty = env.get(ast.clone())?;
            env.state
                .insert(x.clone(), AbstractValue::Runtime(Rc::new(Type::Top)));

            // Generate identifier (union is copy so old ident still usable)
            let id_x = Ident::new(x, Span::call_site());
            Ok((quote!(#id_x), ty))
        }
        AstData::ComptimeVar(x) => Err(ast.error(format!(
            "Cannot use compile-time only var {} in runtime context",
            x
        ))),
        AstData::PairLeft(_) => todo!("move PairLeft"),
        AstData::PairRight(_) => todo!("move PairRight"),
        AstData::Deref(p_ast) => {
            let (_code, ty) = move_op(env, p_ast.clone())?;
            let Type::BorrowM(loan_id, val) = &*ty else {
                return Err(ast.error(format!(
                    "cannot move out of {}, not a mutable reference",
                    p_ast
                )));
            };
            write_op(
                env,
                p_ast.clone(),
                Rc::new(Type::BorrowM(*loan_id, Rc::new(Type::Top))),
            )?;

            Ok((quote!(), val.clone()))
        }
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
        AstData::Atom(s) => {
            let atom = Atom::new(s);
            let atom_hash = atom.hash();
            Ok((quote!(OchreValue{ atom: #atom_hash }), Rc::new(atom.into())))
        }
        AstData::Union(_, _) => Err(ast.error(format!("Type union used in runtime context"))),
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
        AstData::Ref(p_ast) => {
            let (_, t) = read_op(env, p_ast.clone())?;
            let loan_id = env.make_loan_id();
            narrow_op(env, p_ast.clone(), Rc::new(Type::LoanS(loan_id, t.clone())))?;
            Ok((quote!(), Rc::new(Type::BorrowS(loan_id, t))))
        }
        AstData::MutRef(p_ast) => {
            // let span: proc_macro::Span = p_ast.span.unwrap().into();
            // span.warning("rference taken").emit();
            let (_, t) = move_op(env, p_ast.clone())?;
            let loan_id = env.make_loan_id();
            write_op(env, p_ast.clone(), Rc::new(Type::LoanM(loan_id)))?;
            Ok((quote!(), Rc::new(Type::BorrowM(loan_id, t))))
        }
        AstData::Ass(lhs, rhs) => {
            match lhs.runtime_comptime() {
                (true, false) => {
                    // Runtime assignment
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
                (false, true) => {
                    // comptime assignment
                    let rhs_type = erased_read_op(env, rhs.clone())?;
                    erased_write_op(env, lhs.clone(), rhs_type)?;
                    // assignments evaluate to 'unit
                    let unit = Atom::new("unit");
                    Ok((quote!(), Rc::new(unit.into())))
                }
                _ => {
                    return Err(ast.error(format!("lhs must be unambigiously comptime or runtime")))
                }
            }
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
