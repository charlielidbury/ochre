use std::rc::Rc;

pub type AstB = Box<Ast>;

// pub type Atom = String;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AstData {
    Var(String),
    PairLeft(Ast),
    PairRight(Ast),
    Deref(Ast),
    App(Ast, Ast),
    Fun(String, Ast, Ast),
    Pair(Ast, Ast),
    Let(String, Ast, Ast),
    Atom(String),
    Union(Ast, Ast),
    Seq(Ast, Ast),
    Case(Ast, Vec<(String, Ast)>),
    Ref(Ast),
    MutRef(Ast),
    Ass(Ast, Ast),
    Moved,
    Top,
}

pub type Ast = Rc<AstData>;
