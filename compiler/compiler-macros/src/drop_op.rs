use proc_macro2::TokenStream;
use quote::quote;

use crate::{
    abstract_::{Env, OchreType, Type},
    ast::{AstData, OError},
};

pub fn drop_op(env: &mut Env, v: OchreType) -> Result<TokenStream, OError> {
    match &*v {
        // No deallocation required
        Type::Atom(_) | Type::Top | Type::Func(_, _) => Ok(quote!()),

        Type::Pair(l, l_term, r_term) => {
            match (&*l_term.data, &*r_term.data) {
                (AstData::Top, AstData::Type(r)) => {
                    drop_op(env, l.clone())?;
                    drop_op(env, r.clone())?;
                }
                _ => unimplemented!("drop dependent pair"),
            }
            Ok(quote!())
        }

        Type::BorrowS(_, _) => todo!("drop_op BorrowS"),
        Type::BorrowM(_, _) => todo!("drop_op BorrowM"),
        Type::LoanS(_, _) => todo!("drop_op LoanS"),
        Type::LoanM(_) => todo!("drop_op LoanM"),
    }
}
