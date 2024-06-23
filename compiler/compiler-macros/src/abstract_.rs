use std::{
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
};

use crate::ast::OError;
use crate::erased_write_op;
use crate::{
    ast::{Ast, AstData},
    drop_op::drop_op,
    erased_read_op::erased_read_op,
    erased_write_op::erased_write_op,
};
use im_rc::{HashMap, HashSet};
use proc_macro2::TokenStream;
use quote::quote;
use std::fmt;

fn runtime(x: &str) -> bool {
    x.chars().nth(0).unwrap().is_ascii_lowercase()
}

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
pub struct Pair {
    pub l: OchreType,
    pub l_term: Ast,
    pub r_term: Ast,
}

impl Pair {
    pub fn get(&self, env: &Env) -> Result<(OchreType, OchreType), OError> {
        let env = &mut env.clone();
        erased_write_op(env, self.l_term.clone(), self.l.clone())?;
        let r = erased_read_op(env, self.r_term.clone())?;
        Ok((self.l.clone(), r))
    }

    pub fn new(l: OchreType, r: OchreType) -> Self {
        Pair {
            l: l,
            l_term: Ast::new(None, AstData::Top),
            r_term: Ast::new(None, AstData::Type(r)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Atom(HashSet<Atom>),
    RuntimeFunc(Ast, Ast, Ast),
    ComptimeFunc(Ast, Ast),
    Pair(Pair),
    BorrowS(LoanId, OchreType),
    BorrowM(LoanId, OchreType),
    LoanS(LoanId, OchreType),
    LoanM(LoanId),
    Top,
}
impl Type {
    pub fn subtype(&self, env: &Env, other: &Type) -> Result<bool, OError> {
        use Type::*;
        match (self, other) {
            // Top is widest
            (_, Top) => Ok(true),
            // Auto-remove Loans
            (LoanS(_, sub), sup) => sub.subtype(env, sup),
            (sub, LoanS(_, sup)) => sub.subtype(env, sup),

            (Atom(sub_atoms), Atom(super_atoms)) => Ok(sub_atoms.is_subset(super_atoms)),
            (Pair(sub_p), Pair(sup_p)) => {
                // eval sub-pair
                let (sub_l, sub_r) = sub_p.get(env)?;

                // check sub-pair is less than sup-pair on the left
                if !sub_l.subtype(env, &*sup_p.l)? {
                    return Ok(false);
                }

                // check sub-pair is less than sup-pair on the right
                let inner_env = &mut env.clone();
                erased_write_op(inner_env, sup_p.l_term.clone(), sub_l)?;
                let sup_r = erased_read_op(inner_env, sup_p.r_term.clone())?;
                if !sub_r.subtype(env, &*sup_r)? {
                    return Ok(false);
                }

                Ok(true)
            }
            (_, _) => Ok(false),
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
        env: &Env,
        loan_id: LoanId,
    ) -> Result<Option<(OchreType, OchreType)>, OError> {
        match self {
            Type::Atom(_) | Type::RuntimeFunc(_, _, _) | Type::ComptimeFunc(_, _) | Type::Top => {
                Ok(None)
            }
            Type::Pair(p) => {
                let (l, r) = p.get(env)?;
                match (
                    l.terminate_borrow(env, loan_id)?,
                    r.terminate_borrow(env, loan_id)?,
                ) {
                    (Some((new_l, terminated_type)), None) => Ok(Some((
                        Rc::new(Type::Pair(Pair::new(new_l, r))),
                        terminated_type,
                    ))),
                    (None, Some((new_r, terminated_type))) => Ok(Some((
                        Rc::new(Type::Pair(Pair::new(l, new_r))),
                        terminated_type,
                    ))),
                    (None, None) => Ok(None),
                    (Some(_), Some(_)) => {
                        unimplemented!("terminating borrow in left and right of pair")
                    }
                }
            }
            Type::BorrowM(l, t) | Type::BorrowS(l, t) if *l == loan_id => {
                Ok(Some((Rc::new(Type::Top), t.clone())))
            }
            Type::BorrowM(l, t) => {
                // no hit
                let Some((new_self, terminated_type)) = t.terminate_borrow(env, loan_id)? else {
                    return Ok(None);
                };

                Ok(Some((
                    Rc::new(Type::BorrowM(*l, new_self)),
                    terminated_type,
                )))
            }
            Type::LoanS(_, t) | Type::BorrowS(_, t) => {
                if let Some(_) = t.terminate_borrow(env, loan_id)? {
                    Err((
                        None,
                        "cannot terminate borrow through immutable reference".to_string(),
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
        env: &Env,
        loan_id: LoanId,
        val: Option<OchreType>, // none = immutable loan, some = mutable loan
    ) -> Result<Option<OchreType>, OError> {
        match self {
            Type::Atom(_) | Type::RuntimeFunc(_, _, _) | Type::ComptimeFunc(_, _) | Type::Top => {
                Ok(None)
            }
            Type::Pair(p) => {
                let (l, r) = p.get(env)?;
                match (
                    l.terminate_loan(env, loan_id, val.clone())?,
                    r.terminate_loan(env, loan_id, val)?,
                ) {
                    (Some(new_l), None) => Ok(Some(Rc::new(Type::Pair(Pair::new(new_l, r))))),
                    (None, Some(new_r)) => Ok(Some(Rc::new(Type::Pair(Pair::new(l, new_r))))),
                    (None, None) => Ok(None),
                    (Some(_), Some(_)) => {
                        unimplemented!("terminating borrow in left and right of pair")
                    }
                }
            }
            Type::BorrowS(l, v) => {
                if *l == loan_id {
                    // loan cant be inside its own borrow (circular reference), so this must not do anything
                    if let Some(_) = v.terminate_loan(env, loan_id, val)? {
                        Err((None, "borrow referenced its own loan?!?!".to_string()))
                    } else {
                        Ok(None)
                    }
                } else {
                    let Some(new_self) = v.terminate_loan(env, loan_id, val.clone())? else {
                        return Ok(None);
                    };

                    // cannot terminate mutable loans through immutable references
                    if val.is_some() {
                        return Err((
                            None,
                            "attempt to terminate loan which has been immutably borrowed"
                                .to_string(),
                        ));
                    }

                    Ok(Some(Rc::new(Type::BorrowM(*l, new_self))))
                }
            }
            Type::BorrowM(l, v) => {
                if *l == loan_id {
                    // loan cant be inside its own borrow (circular reference), so this must not do anything
                    if let Some(_) = v.terminate_loan(env, loan_id, val)? {
                        Err((None, "borrow referenced its own loan?!?!".to_string()))
                    } else {
                        Ok(None)
                    }
                } else {
                    let Some(new_self) = v.terminate_loan(env, loan_id, val)? else {
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
            Type::RuntimeFunc(_, _, _) => write!(f, "Func"),
            Type::ComptimeFunc(_, _) => write!(f, "Func"),
            Type::Pair(p) => match &*p.l_term.data {
                AstData::Top => write!(f, "({}, {})", p.l, p.r_term.data),
                _ => write!(f, "({}, {} -> {})", p.l, p.l_term.data, p.r_term.data),
            },
            Type::BorrowS(_, ochre_type) => write!(f, "&{}", ochre_type),
            Type::BorrowM(_, ochre_type) => write!(f, "&mut {}", ochre_type),
            Type::LoanS(_, ochre_type) => write!(f, "{}", ochre_type),
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

#[derive(Debug, Clone)]
pub struct Env {
    pub state: HashMap<String, OchreType>,
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
                if let Some(ty) = self.state.remove(x) {
                    drop_op(self, ty.clone())?;
                }

                self.state.insert(x.clone(), Rc::new(Type::Top));

                Ok(quote!())
            }
            AstData::ComptimeVar(x) => {
                let old_val = self.state.insert(x.clone(), Rc::new(Type::Top));

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
            AstData::RuntimeFun(_, _, _) => todo!("bot RuntimeFun"),
            AstData::ComptimeFun(_, _) => todo!("bot ComptimeFun"),
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
            AstData::TypeQuestion(_) => todo!("bot TypeQuestion"),
        }
    }

    pub fn terminate_borrow(&mut self, loan_id: LoanId) -> Result<OchreType, OError> {
        // scan through whole environment for loan :(
        for (x, ty) in self.state.iter() {
            if runtime(x) {
                if let Some((new_self, extracted_ty)) = ty.terminate_borrow(self, loan_id)? {
                    self.state.insert(x.clone(), new_self);
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
        for (x, ty) in self.state.iter() {
            if runtime(x) {
                if let Some(new_self) = ty.terminate_loan(self, loan_id, val.clone())? {
                    self.state.insert(x.clone(), new_self);
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
                Some(v) => v.clone(),
                _ => return Err((None, format!("Use of undeclared variable {}", ast))),
            },
            AstData::ComptimeVar(x) => match self.state.get(x) {
                Some(v) => v.clone(),
                _ => return Err((None, format!("Use of undeclared variable {}", ast))),
            },
            AstData::PairLeft(_) => todo!("narrow PairLeft"),
            AstData::PairRight(_) => todo!("narrow PairRight"),
            AstData::Deref(_) => todo!("narrow Deref"),
            AstData::App(_, _) => todo!("narrow App"),
            AstData::RuntimeFun(_, _, _) => todo!("narrow RuntimeFun"),
            AstData::ComptimeFun(_, _) => todo!("narrow ComptimeFun"),
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
            AstData::TypeQuestion(_) => todo!("narrow TypeQuestion"),
        };

        // Terminate mutable loans
        while let Type::LoanM(loan_id) = &*t {
            t = self.terminate_borrow(*loan_id)?;
        }

        Ok(t)
    }

    pub fn set(&mut self, ast: Ast, ty: OchreType) -> Result<OchreType, OError> {
        let mut t = match &*ast.data {
            AstData::RuntimeVar(x) => self.state.insert(x.clone(), ty),
            AstData::ComptimeVar(x) => self.state.insert(x.clone(), ty),
            AstData::PairLeft(_) => todo!("narrow PairLeft"),
            AstData::PairRight(_) => todo!("narrow PairRight"),
            AstData::Deref(_) => todo!("narrow Deref"),
            AstData::App(_, _) => todo!("narrow App"),
            AstData::RuntimeFun(_, _, _) => todo!("narrow RuntimeFun"),
            AstData::ComptimeFun(_, _) => todo!("narrow ComptimeFun"),
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
            AstData::TypeQuestion(_) => todo!("narrow TypeQuestion"),
        }
        .unwrap_or(Rc::new(Type::Top));

        // Terminate mutable loans
        while let Type::LoanM(loan_id) = &*t {
            t = self.terminate_borrow(*loan_id)?;
        }

        Ok(t)
    }
}
