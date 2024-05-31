use std::mem;
use std::rc::Rc;

use crate::abstract_::{AbstractValue, Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData};
use crate::drop_op::drop_op;
use crate::write_op::write_op;
use proc_macro2::Ident;
use proc_macro2::{Span, TokenStream};
use quote::quote;

pub fn move_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), String> {
    match &*ast {
        AstData::Var(x) => {
            // Get value for x
            let v = match env.state.get_mut(x) {
                None => return Err(format!("attempt to move non-existant value")),
                Some(AbstractValue::Comptime(_)) => {
                    return Err(format!("attempt to move comptime value"))
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
        AstData::PairLeft(_) => todo!("PairLeft"),
        AstData::PairRight(_) => todo!("PairRight"),
        AstData::Deref(_) => todo!("Deref"),
        AstData::App(_, _) => todo!("App"),
        AstData::Fun(_, _, _) => todo!("Fun"),
        AstData::Pair(l, r) => {
            let (l_code, l_val) = move_op(env, l.clone())?;
            let (r_code, r_val) = move_op(env, r.clone())?;
            Ok((
                quote!(OchreValue { pair: Box::leak(Box::new(({ #l_code }, { #r_code }))) }),
                Rc::new(Type::Pair(
                    l_val,
                    r_val,
                    Rc::new(AstData::Top),
                    Rc::new(AstData::Top),
                )),
            ))
        }
        AstData::Let(_, _, _) => todo!("Let"),
        AstData::Atom(s) => {
            let atom = Atom::new(s);
            let atom_hash = atom.hash();
            Ok((quote!(OchreValue{ atom: #atom_hash }), Rc::new(atom.into())))
        }
        AstData::Union(_, _) => todo!("Union"),
        AstData::Seq(lhs, rhs) => {
            // Evaluate lhs
            let (lhs_code, lhs_val) = move_op(env, lhs.clone())?;
            // Drop lhs
            let drop_code = drop_op(env, lhs_val)?;
            // Evaluate rhs
            let (rhs_code, rhs_val) = move_op(env, rhs.clone())?;
            // Return code
            Ok((quote!(#lhs_code; #drop_code; #rhs_code), rhs_val))
        }
        AstData::Case(_, _) => todo!("Case"),
        AstData::Ref(_) => todo!("Ref"),
        AstData::MutRef(ast) => {
            let (_, m) = move_op(env, ast)?;
            write_op(env, ast, Rc::new(Type::LoanM(())))
        }
        AstData::Ass(lhs, rhs) => {
            // evaluate rhs
            let (rhs_code, rhs_type) = move_op(env, rhs.clone())?;
            // write to lhs
            let alloc_code = env.bot(lhs.clone())?;
            let lhs_code = write_op(env, lhs.clone(), rhs_type)?;
            // assignments evaluate to 'unit
            let unit = Atom::new("unit");
            let unit_hash = unit.hash();
            // combine
            Ok((
                quote!(#alloc_code; #lhs_code = #rhs_code; OchreValue { atom: #unit_hash }),
                Rc::new(unit.into()),
            ))
        }
        AstData::Moved => todo!("Moved"),
        AstData::Top => todo!("Top"),
    }
}
