use std::backtrace::Backtrace;
use std::{
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use crate::ast::OError;
use crate::{
    ast::{Ast, AstData},
    drop_op::drop_op,
};
use im_rc::{HashMap, HashSet};
use proc_macro2::{Ident, Span, TokenStream};
use quote::quote;
use std::fmt;

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
    Pair(OchreType, Ast, Ast),
    BorrowS(LoanId, OchreType),
    BorrowM(LoanId, OchreType),
    LoanS(LoanId, OchreType),
    LoanM(LoanId),
    Top,
}

impl Type {
    pub fn subtype(&self, other: &Type) -> bool {
        use Type::*;
        match (self, other) {
            (_, Top) => true,
            (Atom(sub_atoms), Atom(super_atoms)) => sub_atoms.is_subset(super_atoms),
            (Pair(sub_l, a, b), Pair(sup_l, c, d)) => {
                match (&*a.data, &*b.data, &*c.data, &*d.data) {
                    (AstData::Top, AstData::Type(sub_r), AstData::Top, AstData::Type(sup_r)) => {
                        sub_l.subtype(sup_l) && sub_r.subtype(sup_r)
                    }
                    _ => unimplemented!("dep. pair subtype"),
                }
            }
            (_, _) => false,
        }
    }

    pub fn union(&self, other: &Type) -> Result<Rc<Type>, OError> {
        match (self, other) {
            (Type::Atom(lhs), Type::Atom(rhs)) => {
                Ok(Rc::new(Type::Atom(lhs.clone().union(rhs.clone()))))
            }
            (lhs, rhs) => Err((None, format!("{} and {} have no union", lhs, rhs))),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Atom(atoms) => {
                let atoms_str: Vec<String> = atoms.iter().map(|atom| atom.0.clone()).collect();
                write!(f, "{{{}}}", atoms_str.join(", "))
            }
            Type::Func(_param, _ret) => write!(f, "Func"),
            Type::Pair(l, a, b) => write!(f, "({}, {} -> {})", l, a.data, b.data),
            Type::BorrowS(loan_id, ochre_type) => write!(f, "BorrowS({}, {})", loan_id, ochre_type),
            Type::BorrowM(loan_id, ochre_type) => write!(f, "BorrowM({}, {})", loan_id, ochre_type),
            Type::LoanS(loan_id, ochre_type) => write!(f, "LoanS({}, {})", loan_id, ochre_type),
            Type::LoanM(loan_id) => write!(f, "LoanM({})", loan_id),
            Type::Top => write!(f, "_"),
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
    pub fn bot(&mut self, ast: Ast) -> Result<TokenStream, OError> {
        match &*ast.data {
            AstData::RuntimeVar(x) => {
                if let Some(AbstractValue::Runtime(ty)) = self.state.remove(x) {
                    drop_op(self, ty.clone())?;
                }

                self.state
                    .insert(x.clone(), AbstractValue::Runtime(Rc::new(Type::Top)));

                Ok(quote!())
            }
            AstData::ComptimeVar(x) => {
                let old_val = self
                    .state
                    .insert(x.clone(), AbstractValue::Comptime(Rc::new(Type::Top)));

                if old_val.is_some() {
                    Err((None, format!("variable {} already exists", x)))
                } else {
                    Ok(quote!())
                }
            }
            AstData::PairLeft(_) => todo!("bot PairLeft"),
            AstData::PairRight(_) => todo!("bot PairRight"),
            AstData::Deref(_) => todo!("bot Deref"),
            AstData::App(_, _) => todo!("bot App"),
            AstData::Fun(_, _, _) => todo!("bot Fun"),
            AstData::Pair(_, _) => todo!("bot Pair"),
            AstData::Atom(_) => todo!("bot Atom"),
            AstData::Union(_, _) => todo!("bot Union"),
            AstData::Seq(_, _) => todo!("bot Seq"),
            AstData::Case(_, _) => todo!("bot Case"),
            AstData::Ref(_) => todo!("bot Ref"),
            AstData::MutRef(_) => todo!("bot MutRef"),
            AstData::Ass(_, _) => todo!("bot Ass"),
            AstData::Top => todo!("bot Top"),
            AstData::Annot(_, _) => todo!("bot Annot"),
            AstData::Type(_) => todo!("bot Type"),
        }
    }

    pub fn get(&mut self, ast: Ast) -> Result<OchreType, OError> {
        match &*ast.data {
            AstData::RuntimeVar(x) => match self.state.get(x) {
                Some(AbstractValue::Runtime(v)) => Ok(v.clone()),
                _ => Err((None, format!("Cannot get {:?}", ast))),
            },
            AstData::ComptimeVar(x) => match self.state.get(x) {
                Some(AbstractValue::Comptime(v)) => Ok(v.clone()),
                _ => Err((None, format!("Cannot get {:?}", ast))),
            },
            AstData::PairLeft(_) => todo!("narrow PairLeft"),
            AstData::PairRight(_) => todo!("narrow PairRight"),
            AstData::Deref(_) => todo!("narrow Deref"),
            AstData::App(_, _) => todo!("narrow App"),
            AstData::Fun(_, _, _) => todo!("narrow Fun"),
            AstData::Pair(_, _) => todo!("narrow Pair"),
            AstData::Atom(_) => todo!("narrow Atom"),
            AstData::Union(_, _) => todo!("narrow Union"),
            AstData::Seq(_, _) => todo!("narrow Seq"),
            AstData::Case(_, _) => todo!("narrow Case"),
            AstData::Ref(_) => todo!("narrow Ref"),
            AstData::MutRef(_) => todo!("narrow MutRef"),
            AstData::Ass(_, _) => todo!("narrow Ass"),
            AstData::Top => todo!("narrow Top"),
            AstData::Annot(_, _) => todo!("narrow Annot"),
            AstData::Type(_) => todo!("narrow Type"),
        }
    }

    pub fn narrow(&mut self, ast: Ast, ty: OchreType) -> Result<(), OError> {
        match &*ast.data {
            AstData::RuntimeVar(x) => match self.state.get_mut(x) {
                Some(AbstractValue::Runtime(v)) => {
                    if !ty.subtype(v) {
                        return Err((
                            None,
                            format!("Attempting to narrow {:?} down to {:?}", v, ty),
                        ));
                    }
                    *v = ty;
                    Ok(())
                }
                Some(AbstractValue::Comptime(_)) => {
                    Err((None, format!("attempt to narrow erased value")))
                }
                None => Err((None, format!("Attempt to narrow unallocated value"))),
            },
            AstData::ComptimeVar(x) => match self.state.get_mut(x) {
                Some(AbstractValue::Comptime(v)) => {
                    if !ty.subtype(v) {
                        return Err((
                            None,
                            format!("Attempting to narrow {:?} down to {:?}", v, ty),
                        ));
                    }
                    *v = ty;
                    Ok(())
                }
                Some(AbstractValue::Runtime(_)) => {
                    Err((None, format!("attempt to narrow runtime value")))
                }
                None => Err((None, format!("Attempt to narrow unallocated value"))),
            },
            AstData::PairLeft(_) => todo!("narrow PairLeft"),
            AstData::PairRight(_) => todo!("narrow PairRight"),
            AstData::Deref(_) => todo!("narrow Deref"),
            AstData::App(_, _) => todo!("narrow App"),
            AstData::Fun(_, _, _) => todo!("narrow Fun"),
            AstData::Pair(_, _) => todo!("narrow Pair"),
            AstData::Atom(_) => todo!("narrow Atom"),
            AstData::Union(_, _) => todo!("narrow Union"),
            AstData::Seq(_, _) => todo!("narrow Seq"),
            AstData::Case(_, _) => todo!("narrow Case"),
            AstData::Ref(_) => todo!("narrow Ref"),
            AstData::MutRef(_) => todo!("narrow MutRef"),
            AstData::Ass(_, _) => todo!("narrow Ass"),
            AstData::Top => todo!("narrow Top"),
            AstData::Annot(_, _) => todo!("narrow Annot"),
            AstData::Type(_) => todo!("narrow Type"),
        }
    }
}
