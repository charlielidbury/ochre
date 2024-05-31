use std::fmt;
use std::{fmt::Display, rc::Rc};

use crate::ast::{Ast, AstData};
use nom::{
    branch::alt,
    combinator::{all_consuming, fail, map, opt},
    multi::many0,
    sequence::{pair, preceded, terminated, tuple},
    IResult,
};
use proc_macro2::{Delimiter, Ident, Literal, Punct, Span, TokenStream, TokenTree};
// use syn::{parse_macro_input, Ident, LitStr};

#[derive(Debug)]
enum OchreTree {
    Group(Delimiter, Vec<OchreTree>),
    Ident(Ident),
    Punct(Punct),
    Literal(Literal),
}

impl OchreTree {
    fn new(input: TokenTree) -> Self {
        match input {
            TokenTree::Group(g) => OchreTree::Group(
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
            OchreTree::Group(_, g) => g.get(0).expect("empty group").get_span(),
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

fn brackets(input: &[OchreTree]) -> IResult<&[OchreTree], AstData> {
    match input {
        [OchreTree::Group(Delimiter::Parenthesis, g), input @ ..] => {
            Ok((input, all_consuming(parse(0))(&g[..])?.1))
        }
        _ => fail(input),
    }
}

const PREC_MAX: u8 = 4;

fn parse<'a>(prec: u8) -> impl Fn(&'a [OchreTree]) -> IResult<&'a [OchreTree], AstData> {
    move |input| {
        match prec {
            0 => alt((
                // Seq
                map(
                    tuple((parse(prec + 1), punct(";"), parse(prec))),
                    |(lhs, (), rhs)| AstData::Seq(Rc::new(lhs), Rc::new(rhs)),
                ),
                // (Dependent) Pair
                map(
                    tuple((parse(prec + 1), punct(","), parse(prec))),
                    |(l, (), r)| AstData::Pair(Rc::new(l), Rc::new(r.clone())),
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
                            None => AstData::Top,
                        };

                        AstData::Let(x, Rc::new(ty), Rc::new(m))
                    },
                ),
                // Assignment
                map(
                    tuple((parse(prec + 1), punct("="), parse(prec + 1))),
                    |(lhs, (), rhs)| AstData::Ass(Rc::new(lhs), Rc::new(rhs)),
                ),
                parse(prec + 1),
            ))(input),
            2 => alt((
                // Case
                |input| {
                    let (input, cond) = preceded(tok("case"), parse(0))(input)?;

                    let (g, input) = match input {
                        [OchreTree::Group(Delimiter::Brace, g), input @ ..] => (g, input),
                        _ => return fail(input),
                    };

                    let (_, branches) = all_consuming(many0(map(
                        tuple((
                            punct("'"),
                            ident,
                            punct("="),
                            punct(">"),
                            parse(1),
                            punct(","),
                        )),
                        |((), atom, (), (), branch, ())| (atom, Rc::new(branch)),
                    )))(&g)?;

                    Ok((input, AstData::Case(Rc::new(cond), branches)))
                },
                // Dependent Function
                |input: &'a [OchreTree]| {
                    // parses (x: M) -> N
                    match input {
                        [OchreTree::Group(Delimiter::Brace, g), input @ ..] => {
                            // parses (x: M)
                            let (_, (x, (), m)) =
                                all_consuming(tuple((ident, punct(":"), parse(0))))(&g)?;

                            // parses -> N
                            let (input, ((), (), n)) =
                                tuple((punct("-"), punct(">"), parse(prec)))(input)?;

                            Ok((input, AstData::Fun(x, Rc::new(m), Rc::new(n))))
                        }
                        input => fail(input),
                    }
                },
                // Function
                map(
                    // TODO: disallow space between - and > by enforcing the - is spacing=Joint
                    tuple((parse(prec + 1), punct("-"), punct(">"), parse(prec))),
                    |(lhs, (), (), rhs)| AstData::Fun("_".to_string(), Rc::new(lhs), Rc::new(rhs)),
                ),
                parse(prec + 1),
            ))(input),
            3 => alt((
                // Type union
                map(
                    tuple((parse(prec + 1), punct("|"), parse(prec))),
                    |(lhs, (), rhs)| AstData::Union(Rc::new(lhs), Rc::new(rhs)),
                ),
                // Repeatedly try parsers on the tail
                |input| {
                    let (mut input, mut head) = parse(prec + 1)(input)?;

                    loop {
                        // Application
                        if let Ok((i, next)) = parse(prec + 1)(input) {
                            input = i;
                            head = AstData::App(Rc::new(head), Rc::new(next));
                            continue;
                        }

                        // Left pair
                        if let Ok((i, _)) = pair(punct("."), liter("0"))(input) {
                            input = i;
                            head = AstData::PairLeft(Rc::new(head));
                            continue;
                        }

                        // Right pair
                        if let Ok((i, _)) = pair(punct("."), liter("1"))(input) {
                            input = i;
                            head = AstData::PairRight(Rc::new(head));
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
                            f = AstData::App(Rc::new(f), Rc::new(arg));
                        }
                        f
                    },
                ),
            ))(input),
            PREC_MAX => alt((
                // Deref
                map(preceded(punct("*"), parse(prec)), |m| {
                    AstData::Deref(Rc::new(m))
                }),
                // Top
                map(punct("*"), |_| AstData::Top),
                // MutRef
                map(
                    tuple((punct("&"), tok("mut"), parse(prec))),
                    |((), (), m)| AstData::MutRef(Rc::new(m)),
                ),
                // Ref
                map(preceded(punct("&"), parse(prec)), |m| {
                    AstData::Ref(Rc::new(m))
                }),
                // Variable
                map(ident, AstData::Var),
                // Atom
                map(preceded(punct("'"), ident), |atom| AstData::Atom(atom)),
                // Brackets
                brackets,
            ))(input),
            _ => panic!("parse error, input = {:?}", input),
        }
    }
}

pub fn parse_stream(input: TokenStream) -> Result<Ast, Span> {
    // Convert input from stream to vec of tokens
    let input = input.into_iter().map(OchreTree::new).collect::<Vec<_>>();
    dbg!(&input);
    // Leak input so returned errors can reference parts of the input
    // parse the insides
    let res = all_consuming(parse(0))(&input);
    match res {
        Ok((_, ast)) => Ok(Rc::new(ast)),
        Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
            println!("{:?}", e.input);
            let span = e.input[0].get_span();
            Err(span.into())
        }
        Err(nom::Err::Incomplete(_)) => panic!("incomplete hit somehow"),
    }
}
