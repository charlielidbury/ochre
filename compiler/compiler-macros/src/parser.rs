use std::fmt;
use std::fmt::Display;

use crate::ast::{Ast, AstData};
use nom::{
    branch::alt,
    combinator::{all_consuming, fail, map, opt},
    multi::many0,
    sequence::{pair, preceded, tuple},
    IResult,
};
use proc_macro::{Delimiter, Ident, Literal, Punct, Span, TokenStream, TokenTree};
// use syn::{parse_macro_input, Ident, LitStr};

#[derive(Debug)]
enum OchreTree {
    Group(Span, Delimiter, Vec<OchreTree>),
    Ident(Ident),
    Punct(Punct),
    Literal(Literal),
}

impl OchreTree {
    fn new(input: TokenTree) -> Self {
        match input {
            TokenTree::Group(g) => OchreTree::Group(
                g.span(),
                g.delimiter(),
                g.stream().into_iter().map(OchreTree::new).collect(),
            ),
            TokenTree::Ident(i) => OchreTree::Ident(i),
            TokenTree::Punct(p) => OchreTree::Punct(p),
            TokenTree::Literal(l) => OchreTree::Literal(l),
        }
    }

    fn get_span(&self) -> Span {
        match self {
            OchreTree::Group(span, _, _) => span.clone(),
            OchreTree::Ident(i) => i.span(),
            OchreTree::Punct(p) => p.span(),
            OchreTree::Literal(l) => l.span(),
        }
    }
}

impl Display for OchreTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

fn tok(t: &'static str) -> impl FnMut(&[OchreTree]) -> IResult<&[OchreTree], ()> {
    move |input| match input {
        [OchreTree::Ident(i), input @ ..] if i.to_string() == t => Ok((input, ())),
        _ => fail(input),
    }
}

fn punct(ch: &'static str) -> impl FnMut(&[OchreTree]) -> IResult<&[OchreTree], ()> {
    move |input| match input {
        [OchreTree::Punct(i), input @ ..] if i.to_string() == ch => Ok((input, ())),
        input => fail(input),
    }
}

fn liter(sym: &'static str) -> impl FnMut(&[OchreTree]) -> IResult<&[OchreTree], ()> {
    move |input| match input {
        [OchreTree::Literal(l), input @ ..] if l.to_string() == sym => Ok((input, ())),
        input => fail(input),
    }
}

fn ident(input: &[OchreTree]) -> IResult<&[OchreTree], String> {
    match input {
        [OchreTree::Ident(i), input @ ..] => Ok((input, i.to_string())),
        input => fail(input),
    }
}

fn ident_liter(id: &'static str) -> impl FnMut(&[OchreTree]) -> IResult<&[OchreTree], ()> {
    move |input| match input {
        [OchreTree::Ident(i), input @ ..] if i.to_string() == id => Ok((input, ())),
        input => fail(input),
    }
}

// fn ident_exact(input: &[OchreTree], id: &'static str) -> IResult<&[OchreTree], String> {
//     match input {
//         [OchreTree::Ident(i), input @ ..] if i.to_string() == id => Ok((input, i.to_string())),
//         input => fail(input),
//     }
// }

fn brackets(input: &[OchreTree], delimeter: Delimiter) -> IResult<&[OchreTree], Ast> {
    match input {
        [OchreTree::Group(_, d, g), input @ ..] if *d == delimeter => {
            Ok((input, all_consuming(parse(0))(&g[..])?.1))
        }
        _ => fail(input),
    }
}

const PREC_MAX: u8 = 4;

fn parse_data<'a>(prec: u8) -> impl Fn(&'a [OchreTree]) -> IResult<&'a [OchreTree], AstData> {
    move |input| {
        match prec {
            0 => alt((
                // Seq
                map(
                    all_consuming(tuple((parse(prec + 1), punct(";"), opt(parse(prec))))),
                    |(lhs, (), rhs)| AstData::Seq(lhs, rhs.unwrap_or(Ast::new(None, AstData::Top))),
                ),
                // (Dependent) Pair
                map(
                    tuple((parse(prec + 1), punct(","), parse(prec))),
                    |(l, (), r)| AstData::Pair(l, r.clone()),
                ),
                // Top
                map(all_consuming(tuple(())), |()| AstData::Top),
                parse_data(prec + 1),
            ))(input),
            1 => alt((
                // // Let
                // map(
                //     tuple((
                //         tok("let"),
                //         ident,
                //         opt(pair(punct(":"), parse(prec + 1))),
                //         punct("="),
                //         parse(prec + 1),
                //     )),
                //     |((), x, opt_ty, (), m)| {
                //         let ty = match opt_ty {
                //             Some(((), ty)) => ty,
                //             None => Ast::new(None, AstData::Top),
                //         };

                //         AstData::Let(x, ty, m)
                //     },
                // ),
                // Assignment
                map(
                    tuple((parse(prec + 1), punct("="), parse(prec + 1))),
                    |(lhs, (), rhs)| AstData::Ass(lhs, rhs),
                ),
                parse_data(prec + 1),
            ))(input),
            2 => alt((
                // Match
                |input| {
                    let (input, cond) = preceded(tok("match"), parse(0))(input)?;

                    let (g, input) = match input {
                        [OchreTree::Group(_, Delimiter::Brace, g), input @ ..] => (g, input),
                        _ => return fail(input),
                    };

                    let (_, branches) = all_consuming(many0(map(
                        tuple((parse(1), punct("="), punct(">"), parse(1), punct(","))),
                        |(case, (), (), branch, ())| (case, branch),
                    )))(g)?;

                    Ok((input, AstData::Match(cond, branches)))
                },
                // Comptime Function
                map(
                    tuple((parse(prec + 1), punct("-"), punct(">"), parse(prec))),
                    |(i, (), (), o)| AstData::ComptimeFun(i, o),
                ),
                // Runtime Function
                map(
                    tuple((
                        parse(prec + 1),
                        opt(preceded(pair(punct("-"), punct(">")), parse(prec))),
                        |i| brackets(i, Delimiter::Brace),
                    )),
                    |(i, ret, body)| {
                        AstData::RuntimeFun(i, ret.unwrap_or(Ast::new(None, AstData::Top)), body)
                    },
                ),
                parse_data(prec + 1),
            ))(input),
            3 => alt((
                // Repeatedly try parsers on the tail
                |input| {
                    let (mut input, mut head) = parse(prec + 1)(input)?;

                    loop {
                        // Application
                        if let Ok((i, next)) = parse(prec + 1)(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::App(head, next));
                            continue;
                        }

                        // Left pair
                        if let Ok((i, _)) = pair(punct("."), liter("0"))(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::PairLeft(head));
                            continue;
                        }

                        // Right pair
                        if let Ok((i, _)) = pair(punct("."), liter("1"))(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::PairRight(head));
                            continue;
                        }

                        // Type union
                        if let Ok((i, (_, rhs))) = pair(punct("|"), parse(prec))(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::Union(head, rhs))
                        }

                        // Type annotation
                        if let Ok((i, (_, rhs))) = pair(punct(":"), parse(prec))(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::Annot(head, rhs))
                        }

                        // Type Question
                        if let Ok((i, _)) = punct("?")(input) {
                            input = i;
                            head = Ast::new(head.span, AstData::TypeQuestion(head));
                        }

                        break;
                    }

                    Ok((input, (*head.data).clone()))
                },
                // map(
                //     pair(parse(prec + 1), many0(parse(prec + 1))),
                //     |(mut f, args)| {
                //         for arg in args {
                //             f = AstData::App(Rc::new(f), Rc::new(arg));
                //         }
                //         f
                //     },
                // ),
            ))(input),
            PREC_MAX => alt((
                // Deref
                map(preceded(punct("*"), parse(prec)), AstData::Deref),
                // Top
                map(punct("*"), |_| AstData::Top),
                map(ident_liter("_"), |()| AstData::Top),
                // MutRef
                map(
                    tuple((punct("&"), tok("mut"), parse(prec))),
                    |((), (), m)| AstData::MutRef(m),
                ),
                // Ref
                map(preceded(punct("&"), parse(prec)), AstData::Ref),
                // Variable
                map(ident, |input| match input.chars().next().unwrap() {
                    'a'..'z' => AstData::RuntimeVar(input),
                    'A'..'Z' => AstData::ComptimeVar(input),
                    _ => panic!("invalid identifier"),
                }),
                // Atom
                map(preceded(punct("'"), ident), AstData::Atom),
                // Brackets
                |i| {
                    let (i, inner) = brackets(i, Delimiter::Parenthesis)?;
                    Ok((i, (*inner.data).clone()))
                },
            ))(input),
            _ => panic!("parse error, input = {:?}", input),
        }
    }
}

fn parse<'a>(prec: u8) -> impl Fn(&'a [OchreTree]) -> IResult<&'a [OchreTree], Ast> {
    move |input| {
        let (remaining_input, ast_data) = parse_data(prec)(input)?;

        let consumed_input = &input[..(input.len() - remaining_input.len())];

        let span = match consumed_input {
            [] => None,
            [only] => Some(only.get_span()),
            [first, .., last] => first.get_span().join(last.get_span()),
        };

        Ok((remaining_input, Ast::new(span, ast_data)))
    }
}

pub fn parse_stream(input: TokenStream) -> Result<Ast, Span> {
    // Convert input from stream to vec of tokens
    let input = input.into_iter().map(OchreTree::new).collect::<Vec<_>>();
    // Leak input so returned errors can reference parts of the input
    // parse the insides
    let res = all_consuming(parse(0))(&input);
    match res {
        Ok((_, ast)) => Ok(ast),
        Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
            println!("{:?}", e.input);
            let span = if e.input.len() > 0 {
                e.input[0].get_span()
            } else {
                Span::call_site()
            };
            Err(span)
        }
        Err(nom::Err::Incomplete(_)) => panic!("incomplete hit somehow"),
    }
}
