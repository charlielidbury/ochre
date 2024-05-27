

pub type AstB = Box<Ast>;

pub type Atom = String;

#[derive(Debug, Clone)]
pub enum Ast {
    Var(String),
    PairLeft(AstB),
    PairRight(AstB),
    Deref(AstB),
    App(AstB, AstB),
    Fun(String, AstB, AstB),
    Pair(String, AstB, AstB, AstB),
    Let(String, AstB, AstB),
    Atom(Atom),
    Union(AstB, AstB),
    Seq(AstB, AstB),
    Match(AstB, Vec<(Atom, Ast)>),
    Ref(AstB),
    MutRef(AstB),
    Ass(AstB, AstB),
    Moved,
    Top,
}
