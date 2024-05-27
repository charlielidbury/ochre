mod ast;

use ast::{Ast, AstB, Atom};
use nom::{
    branch::alt,
    combinator::{all_consuming, fail, map, opt, value},
    error,
    multi::{many0, many1},
    sequence::{pair, preceded, terminated, tuple},
    IResult,
};
use proc_macro::{Delimiter, TokenStream, TokenTree};
use quote::quote;
use syn::token::Brace;
// use syn::{parse_macro_input, Ident, LitStr};

fn tok(t: &'static str) -> impl FnMut(&[TokenTree]) -> IResult<&[TokenTree], ()> {
    move |input| match input {
        [TokenTree::Ident(i), input @ ..] if i.to_string() == t => Ok((input, ())),
        _ => fail(input),
    }
}

fn punct(ch: &'static str) -> impl FnMut(&[TokenTree]) -> IResult<&[TokenTree], ()> {
    move |input| match input {
        [TokenTree::Punct(i), input @ ..] if i.to_string() == ch => Ok((input, ())),
        input => fail(input),
    }
}

fn liter(sym: &'static str) -> impl FnMut(&[TokenTree]) -> IResult<&[TokenTree], ()> {
    move |input| match input {
        [TokenTree::Literal(l), input @ ..] if l.to_string() == sym => Ok((input, ())),
        input => fail(input),
    }
}

fn ident(input: &[TokenTree]) -> IResult<&[TokenTree], String> {
    match input {
        [TokenTree::Ident(i), input @ ..] => Ok((input, i.to_string())),
        input => fail(input),
    }
}

fn brackets(input: &[TokenTree]) -> IResult<&[TokenTree], Ast> {
    match input {
        [TokenTree::Group(g), input @ ..] if g.delimiter() == Delimiter::Parenthesis => {
            let (_, ast) = parse_stream(g.stream())?;
            Ok((input, ast))
        }
        _ => fail(input),
    }
}

const PREC_MAX: u8 = 4;

fn parse<'a>(prec: u8) -> impl Fn(&'a [TokenTree]) -> IResult<&'a [TokenTree], Ast> {
    move |input| {
        match prec {
            0 => alt((
                // Seq
                map(
                    tuple((parse(prec + 1), punct(";"), parse(prec))),
                    |(lhs, (), rhs)| Ast::Seq(Box::new(lhs), Box::new(rhs)),
                ),
                // (Dependent) Pair
                map(
                    tuple((
                        opt(terminated(ident, punct(":"))),
                        parse(prec + 1),
                        punct(","),
                        parse(prec),
                        opt(preceded(punct(":"), parse(prec))),
                    )),
                    |(x, l, (), r, rt)| {
                        Ast::Pair(
                            x.unwrap_or("_".to_string()),
                            Box::new(l),
                            Box::new(r.clone()),
                            Box::new(rt.unwrap_or(r)),
                        )
                    },
                ),
                parse(prec + 1),
            ))(input),
            1 => alt((
                // Let
                map(
                    tuple((
                        tok("let"),
                        ident,
                        opt(pair(punct(":"), parse(prec + 1))),
                        punct("="),
                        parse(prec + 1),
                    )),
                    |((), x, opt_ty, (), m)| {
                        let ty = match opt_ty {
                            Some(((), ty)) => ty,
                            None => Ast::Top,
                        };

                        Ast::Let(x, Box::new(ty), Box::new(m))
                    },
                ),
                // Assignment
                map(
                    tuple((parse(prec + 1), punct("="), parse(prec + 1))),
                    |(lhs, (), rhs)| Ast::Ass(Box::new(lhs), Box::new(rhs)),
                ),
                parse(prec + 1),
            ))(input),
            2 => alt((
                // Match
                |input| {
                    let (input, cond) = preceded(tok("match"), parse(0))(input)?;

                    let (g, input) = match input {
                        [TokenTree::Group(g), input @ ..] => (g, input),
                        _ => return fail(input),
                    };

                    let inner_input = g.stream().into_iter().collect::<Vec<_>>();
                    let inner_input = &*Box::leak(Box::new(inner_input));
                    let (_, branches) = all_consuming(many0(map(
                        tuple((
                            punct("'"),
                            ident,
                            punct("="),
                            punct(">"),
                            parse(1),
                            punct(","),
                        )),
                        |((), atom, (), (), branch, ())| (atom, branch),
                    )))(&inner_input)?;

                    Ok((input, Ast::Match(Box::new(cond), branches)))
                },
                // Dependent Function
                |input: &'a [TokenTree]| {
                    // parses (x: M) -> N
                    match input {
                        [TokenTree::Group(g), input @ ..] if g.delimiter() == Delimiter::Brace => {
                            // parses (x: M)
                            let g_input = g.stream().into_iter().collect::<Vec<_>>();
                            let g_input = &*Box::leak(Box::new(g_input));
                            let (_, (x, (), m)) =
                                all_consuming(tuple((ident, punct(":"), parse(0))))(&g_input)?;

                            // parses -> N
                            let (input, ((), (), n)) =
                                tuple((punct("-"), punct(">"), parse(prec)))(input)?;

                            Ok((input, Ast::Fun(x, Box::new(m), Box::new(n))))
                        }
                        input => fail(input),
                    }
                },
                // Function
                map(
                    // TODO: disallow space between - and > by enforcing the - is spacing=Joint
                    tuple((parse(prec + 1), punct("-"), punct(">"), parse(prec))),
                    |(lhs, (), (), rhs)| Ast::Fun("_".to_string(), Box::new(lhs), Box::new(rhs)),
                ),
                parse(prec + 1),
            ))(input),
            3 => alt((
                // Type union
                map(
                    tuple((parse(prec + 1), punct("|"), parse(prec))),
                    |(lhs, (), rhs)| Ast::Union(Box::new(lhs), Box::new(rhs)),
                ),
                // Repeatedly try parsers on the tail
                |input| {
                    let (mut input, mut head) = parse(prec + 1)(input)?;

                    loop {
                        // Application
                        if let Ok((i, next)) = parse(prec + 1)(input) {
                            input = i;
                            head = Ast::App(Box::new(head), Box::new(next));
                            continue;
                        }

                        // Left pair
                        if let Ok((i, _)) = pair(punct("."), liter("0"))(input) {
                            input = i;
                            head = Ast::PairLeft(Box::new(head));
                            continue;
                        }

                        // Right pair
                        if let Ok((i, _)) = pair(punct("."), liter("1"))(input) {
                            input = i;
                            head = Ast::PairRight(Box::new(head));
                            continue;
                        }

                        break;
                    }

                    Ok((input, head))
                },
                map(
                    pair(parse(prec + 1), many0(parse(prec + 1))),
                    |(mut f, args)| {
                        for arg in args {
                            f = Ast::App(Box::new(f), Box::new(arg));
                        }
                        f
                    },
                ),
            ))(input),
            PREC_MAX => alt((
                // Deref
                map(preceded(punct("*"), parse(prec)), |m| {
                    Ast::Deref(Box::new(m))
                }),
                // Top
                map(punct("*"), |_| Ast::Top),
                // MutRef
                map(
                    tuple((punct("&"), tok("mut"), parse(prec))),
                    |((), (), m)| Ast::MutRef(Box::new(m)),
                ),
                // Ref
                map(preceded(punct("&"), parse(prec)), |m| Ast::Ref(Box::new(m))),
                // Variable
                map(ident, Ast::Var),
                // Atom
                map(preceded(punct("'"), ident), |atom| Ast::Atom(atom)),
                // Brackets
                brackets,
            ))(input),
            _ => panic!("parse error, input = {:?}", input),
        }
    }
}

fn parse_stream(input: TokenStream) -> IResult<&'static [TokenTree], Ast> {
    // Convert input from stream to vec of tokens
    let input = input.into_iter().collect::<Vec<_>>();
    // Leak input so returned errors can reference parts of the input
    let input = &*Box::leak(Box::new(input));
    // parse the insides
    all_consuming(parse(0))(&input)
}

fn ochre_impl(input: TokenStream) -> TokenStream {
    dbg!(&input);
    dbg!(parse_stream(input));

    // quote!(compile_error!("hello world")).into()
    quote!(println!("hello world")).into()
}

#[proc_macro]
pub fn ochre(item: TokenStream) -> TokenStream {
    ochre_impl(item)
}

#[cfg(test)]
mod tests {
    use super::*;
}
