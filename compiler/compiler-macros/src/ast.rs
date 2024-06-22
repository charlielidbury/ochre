use std::rc::Rc;

use crate::abstract_::OchreType;
use std::fmt;

pub type OError = (Option<proc_macro2::Span>, String);

// pub type Atom = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AstData {
    RuntimeVar(String),
    ComptimeVar(String),
    PairLeft(Ast),
    PairRight(Ast),
    Deref(Ast),
    App(Ast, Ast),
    Fun(String, Ast, Ast),
    Pair(Ast, Ast),
    Let(String, Ast, Ast),
    Atom(String),
    Union(Ast, Ast),
    Annot(Ast, Ast),
    Seq(Ast, Ast),
    Case(Ast, Vec<(String, Ast)>),
    Ref(Ast),
    MutRef(Ast),
    Ass(Ast, Ast),
    Top,
    Type(OchreType),
}

impl AstData {
    pub fn runtime(&self) -> Option<bool> {
        match self {
            AstData::RuntimeVar(_) => Some(true),
            AstData::ComptimeVar(_) => Some(false),
            AstData::PairLeft(_) => todo!("runtime PairLeft"),
            AstData::PairRight(_) => todo!("runtime PairRight"),
            AstData::Deref(_) => todo!("runtime Deref"),
            AstData::App(_, _) => todo!("runtime App"),
            AstData::Fun(_, _, _) => todo!("runtime Fun"),
            AstData::Pair(_, _) => todo!("runtime Pair"),
            AstData::Let(_, _, _) => todo!("runtime Let"),
            AstData::Atom(_) => todo!("runtime Atom"),
            AstData::Union(_, _) => todo!("runtime Union"),
            AstData::Annot(_, _) => todo!("runtime Annot"),
            AstData::Seq(_, _) => todo!("runtime Seq"),
            AstData::Case(_, _) => todo!("runtime Case"),
            AstData::Ref(_) => todo!("runtime Ref"),
            AstData::MutRef(_) => todo!("runtime MutRef"),
            AstData::Ass(_, _) => todo!("runtime Ass"),
            AstData::Top => todo!("runtime Top"),
            AstData::Type(_) => todo!("runtime Type"),
        }
    }
}

impl fmt::Display for AstData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstData::RuntimeVar(var) => write!(f, "{}", var),
            AstData::ComptimeVar(var) => write!(f, "{}", var),
            AstData::PairLeft(ast) => write!(f, "{}.0", ast),
            AstData::PairRight(ast) => write!(f, "{}", ast),
            AstData::Deref(ast) => write!(f, "*{}", ast),
            AstData::App(ast1, ast2) => write!(f, "{} {}", ast1, ast2),
            AstData::Fun(param, body, ret) => write!(f, "fun {} -> {} : {}", param, body, ret),
            AstData::Pair(ast1, ast2) => write!(f, "({}, {})", ast1, ast2),
            AstData::Let(var, expr, body) => write!(f, "let {} = {} in {}", var, expr, body),
            AstData::Atom(atom) => write!(f, "'{}", atom),
            AstData::Union(ast1, ast2) => write!(f, "{} | {}", ast1, ast2),
            AstData::Annot(expr, ty) => write!(f, "{} : {}", expr, ty),
            AstData::Seq(expr1, expr2) => write!(f, "{}; {}", expr1, expr2),
            AstData::Case(expr, cases) => {
                write!(f, "case {} of ", expr)?;
                for (pattern, body) in cases {
                    write!(f, "{} -> {}; ", pattern, body)?;
                }
                Ok(())
            }
            AstData::Ref(ast) => write!(f, "&{}", ast),
            AstData::MutRef(ast) => write!(f, "&mut {}", ast),
            AstData::Ass(ast1, ast2) => write!(f, "{} = {}", ast1, ast2),
            AstData::Top => write!(f, "_"),
            AstData::Type(ochre_type) => write!(f, "{}", ochre_type),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub span: Option<proc_macro2::Span>,
    pub data: Rc<AstData>,
}

impl Ast {
    pub fn new(span: Option<proc_macro2::Span>, data: AstData) -> Self {
        Ast {
            span,
            data: Rc::new(data),
        }
    }

    pub fn error(&self, s: String) -> OError {
        (self.span, s)
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl PartialEq for Ast {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl Eq for Ast {}
