use crate::abstract_::{Env, OchreType, Type};
use crate::ast::{Ast, AstData, OError};

pub fn erased_write_op(env: &mut Env, ast: Ast, val: OchreType) -> Result<(), OError> {
    match (&*ast.data, &*val) {
        (AstData::ComptimeVar(_), _) => {
            env.bot(ast.clone())?;
            let old_val = env.set(ast.clone(), val.clone())?;
            if !val.subtype(env, &*old_val)? {
                return Err(ast.error(format!(
                    "writes which widens type disallowed at compile time"
                )));
            }
            Ok(())
        }
        (AstData::Pair(_, _), Type::Pair(_)) => todo!("erased_write_op Pair"),
        (AstData::PairLeft(_p_ast), _val) => todo!("erased_write_op PairLeft"),
        (AstData::PairRight(_p_ast), _) => todo!("erased_write_op PairRight"),
        (AstData::Deref(_), _) => todo!("erased_write_op Deref"),
        (AstData::App(_, _), _) => todo!("erased_write_op App"),
        (AstData::RuntimeFun(_, _, _), _) => todo!("erased_write_op RuntimeFun"),
        (AstData::ComptimeFun(_, _), _) => todo!("erased_write_op ComptimeFun"),
        (AstData::Atom(_), _) => todo!("erased_write_op Atom"),
        (AstData::Union(_, _), _) => todo!("erased_write_op Union"),
        (AstData::Seq(_, _), _) => todo!("erased_write_op Seq"),
        (AstData::Match(_, _), _) => todo!("erased_write_op Match"),
        (AstData::Ref(_), _) => todo!("erased_write_op Ref"),
        (AstData::MutRef(_), _) => todo!("erased_write_op MutRef"),
        (AstData::Ass(_, _), _) => todo!("erased_write_op Ass"),
        (AstData::Top, _) => Ok(()),
        (syntax, val) => Err(ast.error(format!("Attempt to write {} to {}", val, syntax))),
    }
}
