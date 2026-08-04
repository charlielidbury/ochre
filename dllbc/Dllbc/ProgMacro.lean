import Dllbc.Uni

open Lean

namespace Dllbc

/-! ## `prog{ … }` — the program surface (§8)

    A program is a term, so its surface is the term surface: `ublk` in RUNTIME
    mode, elaborated in the empty context. There is no declaration form to write
    and nothing for this macro to assemble — which is the point. Compare
    `decl{ fn … }`, whose whole body is telescope-and-return-type bookkeeping.

    `pure{ … }` is the same grammar in ⇝ mode (a `let` there is a β-redex, not a
    slot); the two differ by exactly the `isTy` flag, which is this calculus's
    "one grammar, four arrows" showing up at the surface. -/

syntax "prog{" ublk "}" : term

macro_rules
  | `(prog{ $b:ublk }) => do let (t, _) ← Dllbc.DeclMacro.elabUBlk false [] [] 0 b; pure t

/-- `progWith [a, b] { … }` — a program elaborated with the given names already
    bound at the ids `900, 901, …`. The migration bridge: a program assembled
    from elaborated `Decl`s binds its callees at those ids (`FnMacro.progOf`),
    and a hand-written caller for one has to agree with it. -/
syntax "progWith" "[" ident,* "]" "{" ublk "}" : term

macro_rules
  | `(progWith [ $xs,* ] { $b:ublk }) => do
    let rctx := xs.getElems.toList.enum.map (fun p => (p.2.getId.toString, 900 + p.1))
    let (t, _) ← Dllbc.DeclMacro.elabUBlk false rctx [] 0 b
    pure t

end Dllbc
