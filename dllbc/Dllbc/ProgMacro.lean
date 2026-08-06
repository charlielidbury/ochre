import Dllbc.Uni
import Dllbc.FnMacro

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

/-! ### Two seeding conventions, and why neither subsumes the other

    A block whose free names are already bound needs to know *where* they are
    bound, and there are exactly two answers in this calculus because there are
    two kinds of pre-bound name:

      * **Globals** — the callees of an assembled program, which `FnMacro.progOf`
        binds at `progBase, progBase+1, …`, deliberately above every id a body
        mints. Locals of the block are then free to start at `0`, and must, since
        that is what an elaborated `FnDef` body does. This is `progWith`.
      * **Seeded slots** — Ω entries that exist before the block runs: a
        telescope parameter (`seedTelescope` puts argument `i` at id `i`) or a
        symbolic entry a test seeds by hand (`expectPaths [(⟨0,"n"⟩, .sym 0)]`).
        These sit at `0, 1, …, n-1`, so fresh binders have to start at `n` or
        they collide with them. This is `progSeed`.

    The conventions differ in both numbers, and the second is not the first with
    a different base: `progWith`'s locals start at 0 *because* its globals are out
    of the way, and `progSeed`'s cannot. Two forms, one grammar. -/

/-- `progWith [a, b] { … }` — a program elaborated with the given names already
    bound at the ids `progBase, progBase+1, …`, and its own binders minted from
    `0`. The migration bridge: a program assembled from elaborated `FnDef`s binds
    its callees at those ids (`FnMacro.progOf`), and a hand-written caller for one
    has to agree with it. -/
syntax "progWith" "[" ident,* "]" "{" ublk "}" : term

macro_rules
  | `(progWith [ $xs,* ] { $b:ublk }) => do
    let rctx := xs.getElems.toList.enum.map (fun p => (p.2.getId.toString, FnMacro.progBase + p.1))
    let (t, _) ← Dllbc.DeclMacro.elabUBlk false rctx [] 0 b
    pure t

/-- `progSeed [x, y] { … }` — a program elaborated with the given names already
    bound at the ids `0, 1, …` in listed order, its own binders minted from `n`
    onward so they never collide with the seeded slots.

    That is the convention of a function BODY, and `decl{}` elaborates one the
    same way (`elabUBlk false (names.zip (range n)) [] n`); `progSeed` is that
    body without the declaration around it. Its users are the corpus's
    hand-written `FnDef`s — whose `telescope` seeds ids positionally — and the §3.2
    symbolic tests, which seed Ω directly because a `sym` entry has no surface
    syntax. -/
syntax "progSeed" "[" ident,* "]" "{" ublk "}" : term

macro_rules
  | `(progSeed [ $xs,* ] { $b:ublk }) => do
    let names := xs.getElems.toList.map (fun nm => nm.getId.toString)
    let rctx := names.zip (List.range names.length)
    let (t, _) ← Dllbc.DeclMacro.elabUBlk false rctx [] names.length b
    pure t

end Dllbc
