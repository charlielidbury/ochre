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

        Type::BorrowS(loan_id, _) => {
            env.terminate_loan(*loan_id, None)?;
            Ok(quote!())
        }
        Type::BorrowM(loan_id, val) => {
            env.terminate_loan(*loan_id, Some(val.clone()))?;
            Ok(quote!())
        }
        Type::LoanS(loan_id, _) => {
            env.terminate_borrow(*loan_id)?;
            Ok(quote!())
        }
        Type::LoanM(loan_id) => {
            env.terminate_borrow(*loan_id)?;
            Ok(quote!())
        }
    }
}
