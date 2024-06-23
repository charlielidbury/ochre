#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]
#![feature(never_type)]
#![feature(try_blocks)]
mod abstract_;
mod ast;
mod drop_op;
mod erased_read_op;
mod erased_write_op;
mod move_op;
mod narrow_op;
mod parser;
mod read_op;
mod write_op;

use std::rc::Rc;

use abstract_::Env;
use ast::AstData;
use move_op::move_op;
use parser::parse_stream;
use quote::{quote, quote_spanned};

use crate::abstract_::Type;

fn gen_result_code(result_type: Rc<Type>) -> proc_macro2::TokenStream {
    match &*result_type {
        Type::Atom(atoms) => {
            let mut match_arms = quote!(_ => unreachable!());
            for atom in atoms.iter() {
                let hash = atom.hash();
                let string = &atom.0;
                match_arms = quote! {
                    #hash => OchreResult::Atom(#string.to_string()),
                    #match_arms
                };
            }
            quote! {
                match result.atom {
                    #match_arms
                }
            }
        }
        Type::Func(_, _) => todo!("gen_result_code Func"),
        Type::Pair(l, l_term, r_term) => match (&*l_term.data, &*r_term.data) {
            (AstData::Top, AstData::Type(r)) => {
                let lhs_result_code = gen_result_code(l.clone());
                let rhs_result_code = gen_result_code(r.clone());
                quote! {
                    let (lhs, rhs) = *Box::from_raw(result.pair);
                    (
                        { let result = lhs; #lhs_result_code },
                        { let result = rhs; #rhs_result_code }
                    )
                }
            }
            _ => unimplemented!("gen_result_code dependent pair"),
        },
        Type::BorrowS(_, _) => todo!("gen_result_code BorrowS"),
        Type::BorrowM(_, _) => todo!("gen_result_code BorrowM"),
        Type::LoanS(_, _) => todo!("gen_result_code LoanS"),
        Type::LoanM(_) => todo!("gen_result_code LoanM"),
        Type::Top => todo!("gen_result_code Top"),
    }
}

fn ochre_impl(input: proc_macro::TokenStream) -> proc_macro2::TokenStream {
    let ast = match parse_stream(input) {
        Ok(ast) => ast,
        Err(s) => {
            return quote_spanned! {
                s.into() =>
                compile_error!("syntax error")
            }
        }
    };

    dbg!(&ast);

    // Invoke Ochre compiler
    let mut env = Env::new();
    let (_code, result_type) = match move_op(&mut env, ast) {
        Ok(res) => res,
        Err((None, s)) => return quote!(compile_error!(#s)),
        Err((Some(span), s)) => return quote_spanned!(span.into() => compile_error!(#s)),
    };
    dbg!(env);
    dbg!(result_type.clone());

    // Generate return value
    // let result_code = gen_result_code(result_type);

    // // Output code
    // quote! { unsafe {
    //     use std::ptr;

    //     union OchreValue {
    //         uninit: (),
    //         atom: u64,
    //         pair: *mut (OchreValue, OchreValue),
    //         func: fn(OchreValue) -> OchreValue,
    //         ptr: *mut OchreValue,
    //     }

    //     #[derive(Debug, Clone)]
    //     enum OchreResult {
    //         Atom(String),
    //         Pair(Box<(OchreResult, OchreResult)>),
    //         // Returning pointers or functions not yet supported
    //     }

    //     // Functions

    //     // Body
    //     let result: OchreValue = { #code };

    //     // Convert result to Rust
    //     #result_code
    // }}
    // .into()

    quote!()
}

#[proc_macro]
pub fn ochre(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // proc_macro::Span::call_site().note("hello there!").emit();

    ochre_impl(item).into()
    // quote!(42).into()
}

#[cfg(test)]
mod tests {}
