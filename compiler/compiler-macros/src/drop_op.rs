use proc_macro2::TokenStream;
use quote::quote;

use crate::abstract_::{Env, OchreType, Type};

pub fn drop_op(env: &mut Env, v: OchreType) -> Result<TokenStream, String> {
    match &*v {
        // No deallocation required
        Type::Atom(_) | Type::Top | Type::Func(_, _) => Ok(quote!()),

        Type::Pair(l, r, _, _) => {
            drop_op(env, l.clone())?;
            drop_op(env, r.clone())?;
            Ok(quote!())
        }

        Type::BorrowS(_, _) => todo!("drop_op BorrowS"),
        Type::BorrowM(_, _) => todo!("drop_op BorrowM"),
        Type::LoanS(_, _) => todo!("drop_op LoanS"),
        Type::LoanM(_) => todo!("drop_op LoanM"),
    }
}
