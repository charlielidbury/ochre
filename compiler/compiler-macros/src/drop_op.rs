use std::rc::Rc;

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

        Type::Pair(p) => {
            let (l, r) = p.split(env)?;
            drop_op(env, l)?;
            drop_op(env, r)?;
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

pub fn env_drop_op(mut env: Env) -> Result<(), OError> {
    let top = Rc::new(Type::Top);

    for var in env.state.clone().keys() {
        if env.frozen.contains(var) {
            continue;
        }
        let val = env.set(var.clone(), top.clone())?;
        drop_op(&mut env, val)?;
    }

    Ok(())
}
