use std::backtrace::Backtrace;
use std::{
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use crate::{
    ast::{Ast, AstData},
    drop_op::drop_op,
};
use im_rc::{HashMap, HashSet};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;

type LoanId = usize;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Atom(pub String);

impl Atom {
    pub fn new(s: &str) -> Self {
        Atom(s.to_string())
    }

    pub fn hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.0.hash(&mut hasher);
        hasher.finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Atom(HashSet<Atom>),
    Func(Ast, Ast),
    Pair(OchreType, OchreType, Ast, Ast),
    BorrowS(LoanId, OchreType),
    BorrowM(LoanId, OchreType),
    LoanS(LoanId, OchreType),
    LoanM(LoanId),
    Top,
}

impl Type {
    pub fn subset(&self, other: &Type) -> bool {
        use Type::*;
        match (self, other) {
            (_, Top) => true,
            (Atom(sub_atoms), Atom(super_atoms)) => sub_atoms.is_subset(super_atoms),
            (Pair(sub_l, sub_r, a, b), Pair(sup_l, sup_r, c, d)) => {
                assert!(
                    matches!(
                        (&**a, &**b, &**c, &**d),
                        (AstData::Top, AstData::Top, AstData::Top, AstData::Top)
                    ),
                    "dep. pair subtype unimplemented"
                );
                sub_l.subset(sup_l) && sub_r.subset(sup_r)
            }
            (sub, sup) => unimplemented!(
                "subset between {:?} and {:?}, {}",
                sub,
                sup,
                Backtrace::capture()
            ),
        }
    }
}

impl From<Atom> for Type {
    fn from(atom: Atom) -> Self {
        Type::Atom(HashSet::new().update(atom))
    }
}

pub type OchreType = Rc<Type>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbstractValue {
    Runtime(OchreType),
    Comptime(OchreType),
}

#[derive(Debug)]
pub struct Env {
    pub state: HashMap<String, AbstractValue>,
    // pub atoms: HashMap<u64, String>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            state: HashMap::new(),
            // atoms: HashMap::new(),
        }
    }

    // Generates code and re-arranges the environment
    // such that {ast} can be written into
    // either using allocation or deallocation
    // ast -> bot guarenteed afterwards
    pub fn bot(&mut self, ast: Ast) -> Result<TokenStream, String> {
        match &*ast {
            AstData::Var(x) => {
                if let Some(AbstractValue::Runtime(ty)) = self.state.remove(x) {
                    drop_op(self, ty.clone())?;
                }

                self.state
                    .insert(x.clone(), AbstractValue::Runtime(Rc::new(Type::Top)));

                Ok(quote!())
            }
            AstData::PairLeft(_) => todo!("PairLeft"),
            AstData::PairRight(_) => todo!("PairRight"),
            AstData::Deref(_) => todo!("Deref"),
            AstData::App(_, _) => todo!("App"),
            AstData::Fun(_, _, _) => todo!("Fun"),
            AstData::Pair(_, _) => todo!("Pair"),
            AstData::Let(_, _, _) => todo!("Let"),
            AstData::Atom(_) => todo!("Atom"),
            AstData::Union(_, _) => todo!("Union"),
            AstData::Seq(_, _) => todo!("Seq"),
            AstData::Case(_, _) => todo!("Case"),
            AstData::Ref(_) => todo!("Ref"),
            AstData::MutRef(_) => todo!("MutRef"),
            AstData::Ass(_, _) => todo!("Ass"),
            AstData::Moved => todo!("Moved"),
            AstData::Top => todo!("Top"),
        }
    }

    pub fn narrow(&mut self, ast: Ast, ty: OchreType) -> Result<(), String> {
        match &*ast {
            AstData::Var(x) => match self.state.get_mut(x) {
                Some(AbstractValue::Runtime(v)) => {
                    if !ty.subset(v) {
                        return Err(format!("Attempting to narrow {:?} down to {:?}", v, ty));
                    }
                    *v = ty;
                    Ok(())
                }
                Some(AbstractValue::Comptime(_)) => Err(format!("attempt to narrow erased value")),
                None => Err(format!("Attempt to narrow unallocated value")),
            },
            AstData::PairLeft(_) => todo!("narrow PairLeft"),
            AstData::PairRight(_) => todo!("narrow PairRight"),
            AstData::Deref(_) => todo!("narrow Deref"),
            AstData::App(_, _) => todo!("narrow App"),
            AstData::Fun(_, _, _) => todo!("narrow Fun"),
            AstData::Pair(_, _) => todo!("narrow Pair"),
            AstData::Let(_, _, _) => todo!("narrow Let"),
            AstData::Atom(_) => todo!("narrow Atom"),
            AstData::Union(_, _) => todo!("narrow Union"),
            AstData::Seq(_, _) => todo!("narrow Seq"),
            AstData::Case(_, _) => todo!("narrow Case"),
            AstData::Ref(_) => todo!("narrow Ref"),
            AstData::MutRef(_) => todo!("narrow MutRef"),
            AstData::Ass(_, _) => todo!("narrow Ass"),
            AstData::Moved => todo!("narrow Moved"),
            AstData::Top => todo!("narrow Top"),
        }
    }
}
