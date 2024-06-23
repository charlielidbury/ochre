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

    // Returns (new self, type extracted from loan)
    pub fn terminate_borrow(
        &self,
        loan_id: LoanId,
    ) -> Result<Option<(OchreType, OchreType)>, OError> {
        match self {
            Type::Atom(_) | Type::Func(_, _) | Type::Top => Ok(None),
            Type::Pair(l, l_term, r_term) => todo!("terminate_borrow Pair"),
            Type::BorrowM(l, t) | Type::BorrowS(l, t) if *l == loan_id => {
                Ok(Some((Rc::new(Type::Top), t.clone())))
            }
            Type::BorrowM(l, t) => {
                // no hit
                let Some((new_self, terminated_type)) = t.terminate_borrow(loan_id)? else {
                    return Ok(None);
                };

                Ok(Some((
                    Rc::new(Type::BorrowM(*l, new_self)),
                    terminated_type,
                )))
            }
            Type::LoanS(_, t) | Type::BorrowS(_, t) => {
                if let Some(_) = t.terminate_borrow(loan_id)? {
                    Err((
                        None,
                        format!("cannot terminate borrow through immutable reference"),
                    ))
                } else {
                    Ok(None)
                }
            }
            Type::LoanM(_) => Ok(None), // cannot terminate borrow through loanM
        }
    }

    // Returns (new self, type extracted from loan)
    pub fn terminate_loan(
        &self,
        loan_id: LoanId,
        val: Option<OchreType>, // none = immutable loan, some = mutable loan
    ) -> Result<Option<OchreType>, OError> {
        match self {
            Type::Atom(_) | Type::Func(_, _) | Type::Top => Ok(None),
            Type::Pair(l, l_term, r_term) => todo!("terminate_loan Pair"),
            Type::BorrowS(l, v) => {
                if *l == loan_id {
                    // loan cant be inside its own borrow (circular reference), so this must not do anything
                    if let Some(_) = v.terminate_loan(loan_id, val)? {
                        Err((None, format!("borrow referenced its own loan?!?!")))
                    } else {
                        Ok(None)
                    }
                } else {
                    let Some(new_self) = v.terminate_loan(loan_id, val.clone())? else {
                        return Ok(None);
                    };

                    // cannot terminate mutable loans through immutable references
                    if val.is_some() {
                        return Err((
                            None,
                            format!("attempt to terminate loan which has been immutably borrowed"),
                        ));
                    }

                    Ok(Some(Rc::new(Type::BorrowM(*l, new_self))))
                }
            }
            Type::BorrowM(l, v) => {
                if *l == loan_id {
                    // loan cant be inside its own borrow (circular reference), so this must not do anything
                    if let Some(_) = v.terminate_loan(loan_id, val)? {
                        Err((None, format!("borrow referenced its own loan?!?!")))
                    } else {
                        Ok(None)
                    }
                } else {
                    let Some(new_self) = v.terminate_loan(loan_id, val)? else {
                        return Ok(None);
                    };

                    Ok(Some(Rc::new(Type::BorrowM(*l, new_self))))
                }
            }
            Type::LoanS(l, v) => {
                if *l == loan_id && val.is_none() {
                    Ok(Some(v.clone()))
                } else {
                    Ok(None)
                }
            }
            Type::LoanM(l) => {
                if *l == loan_id && val.is_some() {
                    Ok(val)
                } else {
                    Ok(None)
                }
            }
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
            Type::Pair(l, a, b) => match &*a.data {
                AstData::Top => write!(f, "({}, {})", l, b.data),
                _ => write!(f, "({}, {} -> {})", l, a.data, b.data),
            },
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
    pub next_loan_id: LoanId,
}

impl Env {
    pub fn new() -> Self {
        Self {
            state: HashMap::new(),
            // atoms: HashMap::new(),
            next_loan_id: 0,
        }
    }

    pub fn make_loan_id(&mut self) -> LoanId {
        self.next_loan_id += 1;
        self.next_loan_id - 1
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

    pub fn terminate_borrow(&mut self, loan_id: LoanId) -> Result<OchreType, OError> {
        // scan through whole environment for loan :(
        for (x, value) in self.state.iter() {
            if let AbstractValue::Runtime(ty) = value {
                if let Some((new_self, extracted_ty)) = ty.terminate_borrow(loan_id)? {
                    self.state
                        .insert(x.clone(), AbstractValue::Runtime(new_self));
                    return Ok(extracted_ty);
                }
            }
        }

        panic!("could not find borrow associated with loan")
    }

    pub fn terminate_loan(
        &mut self,
        loan_id: LoanId,
        val: Option<OchreType>,
    ) -> Result<(), OError> {
        // scan through whole environment for loan :(
        for (x, value) in self.state.iter() {
            if let AbstractValue::Runtime(ty) = value {
                if let Some(new_self) = ty.terminate_loan(loan_id, val.clone())? {
                    self.state
                        .insert(x.clone(), AbstractValue::Runtime(new_self));
                    return Ok(());
                }
            }
        }

        panic!("could not find loan associated with borrow")
    }

    // POST: the type returned does not contain any loans
    pub fn get(&mut self, ast: Ast) -> Result<OchreType, OError> {
        let mut t = match &*ast.data {
            AstData::RuntimeVar(x) => match self.state.get(x) {
                Some(AbstractValue::Runtime(v)) => v.clone(),
                _ => return Err((None, format!("Use of undeclared variable {:?}", ast))),
            },
            AstData::ComptimeVar(x) => match self.state.get(x) {
                Some(AbstractValue::Comptime(v)) => v.clone(),
                _ => return Err((None, format!("Use of undeclared variable {:?}", ast))),
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
        };

        loop {
            // Terminate mutable loans
            if let Type::LoanM(loan_id) = &*t {
                t = self.terminate_borrow(*loan_id)?;
                continue;
            }

            break;
        }

        Ok(t)
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
