import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.FnMacro

/-!
# `Option T` — the second parametric type in the fixed basis

`Option` is `List`'s parameter and `Bool`'s shape, and every site it touches was
already occupied by one of those two. It is parametric, so its constructors read
their field types off the expected type's argument (`Nil`/`Cons`); it is NOT
recursive, so its `Some` arm binds the payload and no `ih` (`True`/`False`).
Nothing here is a new kind of rule — this file is the evidence that the kernel's
tables are the whole of what a type in the basis costs.

## What the type is

    Option : Type → Type
    None : Option A
    Some : A → Option A
    optRec : Π (A : Type) (P : Option A → Type)
           → P None → (Π (x : A) → P (Some x)) → Π (o : Option A) → P o

The spine order is `listRec`'s — element type, motive, base arm, step arm,
scrutinee — because the alternative is a second convention to remember.

## What `Option` tests that `List` never did

`List`'s two constructors differ in ARITY *and* in recursiveness at once, so
every site that reads a constructor's fields off the scrutinee's type was
exercised only in the shape "the recursive field has the scrutinee's own type".
`Some`'s single field is at the PARAMETER type, which is the case `Cons`' head
covers and `Cons`' tail hides. The two places where that distinction is real are
`Pure.ctorSig` (`Some` has a one-entry telescope, not a two-entry one ending in
the type former) and the arm contracts (`recArmPis`/`sealRec`), where `Some`'s
arm has no `ih` to type. Both are asserted below.
-/

namespace Dllbc.Tests.OptionT
open Dllbc Dllbc.Pure Dllbc.Surface

/-! ## The pure layer: ι under `nf`, and the tables

    The recursor computes at both constructors, stays stuck on a neutral, and the
    field-type/exhaustiveness tables answer for `Option` the way they answer for
    `List`. -/

-- `optSucc : Option Nat → Option Nat` — the smallest function that is not a
-- projection, written in the `elim` surface (§15b) so that the surface's own
-- `optRec` emission is what is under test and not a hand-built spine.
def OptSucc : Term := prog{
  λ (O : Option Nat). elim O return (λ (Om : Option Nat). Option Nat) {
    None => None,
    Some (X) => Some(S(X)) } }

-- `optOr : Nat → Option Nat → Nat` — a LARGE arm asymmetry: the two arms return
-- the same type by different routes, which is what a `getD` is.
def OptOr : Term := prog{
  λ (D : Nat). λ (O : Option Nat). elim O return (λ (Om : Option Nat). Nat) {
    None => D,
    Some (X) => X } }

-- ι at each constructor.
example : (Pure.nf 1000 prog{ OptSucc (Some(4)) } == prog{ Some(5) }) = true := by native_decide
example : (Pure.nf 1000 prog{ OptSucc None } == prog{ None }) = true := by native_decide
example : (Pure.nf 1000 prog{ OptOr 9 (Some(4)) } == Term.nat 4) = true := by native_decide
example : (Pure.nf 1000 prog{ OptOr 9 None } == Term.nat 9) = true := by native_decide

-- Stuck on a neutral scrutinee: the spine comes back with the scrutinee whnf'd
-- and nothing else done, which is what makes an `Option` σ behave like a `List`
-- one under a symbolic match.
-- (Stated on the SPINE rather than against a hand-written term: readback renames
-- every binder to its level, so a literal comparison would be asserting
-- `readbackName` and not the ι rule.)
example : (match Pure.collectSpineT (Pure.nf 1000 prog{ OptSucc %(Term.sym 3) }) with
  | (.const "optRec", args) => args.length == 5 && args.get? 4 == some (Term.sym 3)
  | _ => false) = true := by native_decide

-- The two tables, directly. `Some`'s telescope has ONE entry at the PARAMETER
-- type — the distinction `Cons` cannot state, since its second field is at the
-- type former itself.
example : ((Pure.ctorSig "Some").bind (fun s => s.fieldTypes prog{ Option Nat })
  == some [("_", prog{ Nat })]) = true := by native_decide
example : ((Pure.ctorSig "None").bind (fun s => s.fieldTypes prog{ Option Nat })
  == some []) = true := by native_decide
-- …and neither inhabits a type it does not belong to.
example : ((Pure.ctorSig "Some").bind (fun s => s.fieldTypes prog{ List Nat })).isNone = true := by
  native_decide
example : (Pure.typeCtors prog{ Option Nat } == some ["None", "Some"]) = true := by native_decide

/-! ## The spec-style equation

    `Id (Option Nat) x y` at equal concretes closes by `Refl` — the conversion
    that backs it is `nf`'s, so this is the ι rule above reached through the
    checker rather than through `native_decide` on `nf`. -/

example : progOk (prog{
  fn OptEq () -> Id (Option Nat) (OptSucc (Some(4))) (Some(5)) { Refl };
  () }) = true := by native_decide

-- The control: unequal concretes do NOT close, so the line above is a claim
-- about `optRec` computing and not about `Refl` being admitted anywhere.
example : progRejects (prog{
  fn OptEq () -> Id (Option Nat) (OptSucc (Some(4))) (Some(4)) { Refl };
  () }) "does not have return type" = true := by native_decide

end Dllbc.Tests.OptionT
