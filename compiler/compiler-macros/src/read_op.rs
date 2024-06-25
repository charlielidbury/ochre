use std::rc::Rc;

use crate::abstract_::{Atom, Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};
use quote::quote;

pub fn read_op(env: &mut Env, ast: Ast) -> Result<(proc_macro2::TokenStream, OchreType), OError> {
    match &*ast.data {
        AstData::RuntimeVar(x) | AstData::ComptimeVar(x) => Ok((quote!(), env.get(x.clone())?)),
        AstData::PairLeft(_) | AstData::PairRight(_) => todo!("read_op PairLEFTRIGHT"),
        AstData::Deref(ref_ast) => {
            let ref_ty = read_op(env, ref_ast.clone())?;

            let ty = match &*ref_ty.1 {
                Type::BorrowM(_, ty) | Type::BorrowS(_, ty) => ty.clone(),
                _ => return Err(ref_ast.error(format!("cannot deference non-reference"))),
            };

            Ok((quote!(), ty))
        }
        AstData::App(_, _) => todo!("read_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("read_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("read_op ComptimeFun"),
        AstData::Pair(_, _) => todo!("read_op Pair"),
        AstData::Atom(s) => {
            let atom = Atom::new(s);
            let atom_hash = atom.hash();
            Ok((quote!(OchreValue{ atom: #atom_hash }), Rc::new(atom.into())))
        }
        AstData::Union(_, _) => todo!("read_op Union"),
        AstData::Annot(_, _) => todo!("read_op Annot"),
        AstData::Seq(_, _) => todo!("read_op Seq"),
        AstData::Match(_, _) => todo!("read_op Match"),
        AstData::Ref(_) => todo!("read_op Ref"),
        AstData::MutRef(_) => todo!("read_op MutRef"),
        AstData::Ass(_, _) => todo!("read_op Ass"),
        AstData::Top => Ok((quote!(), Rc::new(Type::Top))),
        AstData::Type(_) => todo!("read_op Type"),
        AstData::TypeQuestion(_) => todo!("read_op TypeQuestion"),
    }
}
