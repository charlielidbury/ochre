use std::rc::Rc;

use crate::{
    abstract_::{Atom, Env, OchreType, Pair, Type},
    ast::{Ast, AstData, OError},
    erased_read_op::erased_read_op,
    erased_write_op::erased_write_op,
    write_op::write_op,
};

pub fn max_erased_write_op(env: &mut Env, ast: Ast) -> Result<OchreType, OError> {
    match &*ast.data {
        AstData::RuntimeVar(_) | AstData::ComptimeVar(_) => {
            env.set(ast, Rc::new(Type::Top))?;
            Ok(Rc::new(Type::Top))
        }
        AstData::PairLeft(_) => todo!("max_erased_write_op PairLeft"),
        AstData::PairRight(_) => todo!("max_erased_write_op PairRight"),
        AstData::Deref(_) => todo!("max_erased_write_op Deref"),
        AstData::App(_, _) => todo!("max_erased_write_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("max_erased_write_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("max_erased_write_op ComptimeFun"),
        AstData::Pair(l_term, r_term) => {
            let l_max = max_erased_write_op(env, l_term.clone())?;
            let r_max = max_erased_write_op(env, r_term.clone())?;
            Ok(Rc::new(Type::Pair(Pair::new(l_max, r_max))))
        }
        AstData::Atom(_) => todo!("max_erased_write_op Atom"),
        AstData::Union(_, _) => todo!("max_erased_write_op Union"),
        AstData::Annot(term, ty_term) => {
            let max_ty = erased_read_op(env, ty_term.clone())?;
            erased_write_op(env, term.clone(), max_ty.clone())?;
            Ok(max_ty)
        }
        AstData::Seq(_, _) => todo!("max_erased_write_op Seq"),
        AstData::Match(_, _) => todo!("max_erased_write_op Match"),
        AstData::Ref(_) => todo!("max_erased_write_op Ref"),
        AstData::MutRef(_) => todo!("max_erased_write_op MutRef"),
        AstData::Ass(_, _) => todo!("max_erased_write_op Ass"),
        AstData::Top => todo!("max_erased_write_op Top"),
        AstData::Type(_) => todo!("max_erased_write_op Type"),
        AstData::TypeQuestion(_) => todo!("max_erased_write_op TypeQuestion"),
    }
}

pub fn max_move_op(env: &mut Env, ast: Ast) -> Result<OchreType, OError> {
    match &*ast.data {
        AstData::RuntimeVar(_) => {
            env.set(ast, Rc::new(Type::Top))?;
            Ok(Rc::new(Type::Top))
        }
        AstData::ComptimeVar(_) => todo!("max_move_op ComptimeVar"),
        AstData::PairLeft(_) => todo!("max_move_op PairLeft"),
        AstData::PairRight(_) => todo!("max_move_op PairRight"),
        AstData::Deref(_) => todo!("max_move_op Deref"),
        AstData::App(_, _) => todo!("max_move_op App"),
        AstData::RuntimeFun(_, _, _) => todo!("max_move_op RuntimeFun"),
        AstData::ComptimeFun(_, _) => todo!("max_move_op ComptimeFun"),
        AstData::Pair(l_term, r_term) => {
            let l_max = max_erased_write_op(env, l_term.clone())?;
            let r_max = max_erased_write_op(env, r_term.clone())?;
            Ok(Rc::new(Type::Pair(Pair::new(l_max, r_max))))
        }
        AstData::Atom(_) => todo!("max_move_op Atom"),
        AstData::Union(_, _) => todo!("max_move_op Union"),
        AstData::Annot(term, ty_term) => {
            let max_ty = erased_read_op(env, ty_term.clone())?;
            write_op(env, term.clone(), max_ty.clone())?;
            Ok(max_ty)
        }
        AstData::Seq(_, _) => todo!("max_move_op Seq"),
        AstData::Match(_, _) => todo!("max_move_op Match"),
        AstData::Ref(_) => todo!("max_move_op Ref"),
        AstData::MutRef(_) => todo!("max_move_op MutRef"),
        AstData::Ass(_, _) => todo!("max_move_op Ass"),
        AstData::Top => todo!("max_move_op Top"),
        AstData::Type(_) => todo!("max_move_op Type"),
        AstData::TypeQuestion(_) => todo!("max_move_op TypeQuestion"),
    }
}
