import Dllbc.Uni

open Lean

namespace Dllbc

/-!
# `decl{ … }` — the TEST-HARNESS surface, and why it survives (M28 ο)

**This is not the language's surface any more, and it is not migration debt
either.** `fn` is a statement of the program grammar (Uni.lean, M28 θ) and the
corpus was rewritten onto it (M28 ν); what a reader should write is
`prog{ fn f (…) -> R { … }; … }`. `decl{ }` builds an `FnDef` **value**, and it
stays because a `FnDef` is the only thing some tests can be about.

This header exists so that a future simplification pass does not re-derive the
question from scratch and reach the wrong answer. The keep-core is four classes,
and none of them is a program:

  * **A property QUANTIFIED OVER A TELESCOPE.** `S8Diff`'s differential asserts
    "accepted ⟹ concrete-safe at every instantiation of the arguments", over 136
    generated bodies against three telescopes. It seeds `decl.telescope` with
    concrete argument values; a program takes no arguments, so it has nothing to
    instantiate. `decl{ fn f (…) = %body }` — the `%`-splice body — exists for
    exactly this generator.
  * **RECORD-UPDATE twins.** `S27Dispose` and `S26Migrate` build lie twins with
    `{ d with dec := … }` / `{ d with … }` — the same function, one field
    changed. That is a record operation, and a program has no fields.
  * **THE MACRO'S OWN SUBJECT.** `S26Fn` round-trips `fnElab`: it elaborates a
    declaration and compares the result against a hand-written term, by `alphaEq`.
    The input to a lowering cannot be its own output.
  * **CROSS-FILE PINNED SUBJECTS.** `S23Direct`'s declarations are read by seven
    other files (57 references — `S27Dispose`'s disposition ledger, `S26Migrate`'s
    survey, `S26Fn`'s round-trips). A subject named from elsewhere is a value, not
    a block of code somewhere.

Plus one class that is about `decl{ }` failing: the §B decliner residue
(`S27Dispose`), nineteen declarations the recursor lowering REFUSES, pinned by
name. They cannot be `fn` statements — being refused is the point.

`FnDef` therefore stays public API and is not internalized. What retired instead
was the bookkeeping *around* it: the corpus census (M28 μ) and the
`progEnvsOfT`/`progEnvOfT` inspectors (M28 ο), which had program counterparts.

## The surface itself
-/

declare_syntax_cat declParam
declare_syntax_cat declBody

syntax ident ":" uterm : declParam
syntax "{" ublk "}" : declBody              -- body: the unified grammar in term mode
syntax "=" "%" term : declBody              -- escape hatch: splice a raw `Term` body

-- §1.2's `[k]`, the decreasing-argument index. Written as the PARAMETER'S NAME
-- (`fn quicksort [fuel] (…)`) and resolved to its positional index here — the
-- kernel wants an index, but a name is what a reader can check. Required of any
-- function that calls itself; see `FnDef.dec` and the call rule's guard.
syntax "decl{" "fn" ident ("[" ident "]")? "(" declParam,* ")" "->" uterm declBody "}" : term

namespace DeclMacro
open Lean

/-- Shared assembly: build the `FnDef` term from its parsed pieces. -/
def assemble (name : Ident) (dec : Option Ident) (params : Array (TSyntax `declParam)) (ret : TSyntax `uterm)
    (bk : Option (TSyntax `uterm)) (body : TSyntax `declBody) : MacroM (TSyntax `term) := do
  let parsed ← params.toList.mapM fun (p : TSyntax `declParam) => match p with
    | `(declParam| $x:ident : $τ:uterm) => pure (x.getId.toString, τ)
    | _ => Macro.throwErrorAt p "decl: malformed parameter (expected `x : τ`)"
  let names := parsed.map (·.1)
  let n := names.length
  let fullRctx : List (String × Nat) := names.zip (List.range n)
  let teleSyns ← buildTele [] 0 parsed                      -- each entry sees only earlier params
  let (retT, _) ← elabUTerm true fullRctx [] 0 ret          -- retType (type mode) sees the whole telescope
  let bodyT ← match body with                               -- unified `ublk` block, or a `%` splice
    | `(declBody| { $b:ublk }) => do let (t, _) ← elabUBlk false fullRctx [] n b; pure t
    | `(declBody| = % $t:term) => pure ⟨t.raw⟩
    | _ => Macro.throwErrorAt body "decl: malformed body"
  let decT ← match dec with
    | none => `((none : Option Nat))
    | some d =>
      match idxOf? names.reverse d.getId.toString with     -- reverse: idxOf? is innermost-first
      | some i => `(some $(quote (n - 1 - i)))
      | none => Macro.throwErrorAt d s!"decl: decreasing argument '{d.getId}' is not a parameter of '{name.getId}'"
  -- `FnDef.mk` positionally (name, telescope, retType, body, dec). It was positional
  -- because the surface once reserved a `back` keyword that collided with the field
  -- name; the keyword and the field retired together in M27-P2, and the positional
  -- form is kept because that is what `progOf`'s round-trips are written against.
  `(Dllbc.FnDef.mk $(quote name.getId.toString) [$teleSyns,*] $retT $bodyT $decT)

end DeclMacro

open DeclMacro in
macro_rules
  | `(decl{ fn $name:ident $[[$dec:ident]]? ( $params,* ) -> $ret:uterm $body:declBody }) =>
    assemble name dec params.getElems ret none body

end Dllbc
