import Ochr.Test

/-! # 14. Universes

`Prop` is a type in `Type`, and that is all: there is no `Type : Type`, and universes are not
cumulative, so a proposition is not a `Type` (RULES preamble). Non-cumulativity matters for
erasure: with `Prop ≤ Type`, a function declared to return a `Type` could return a
proposition, and whether its calls are erased would depend on the value (D28).

Defined in the preamble of RULES and in P2. -/

open Ochr.Test

ochr Universes {
  -- `Prop` is a type ...
  def PropInType : Type := Prop

  -- ... but `Type` is not a `Type` ...
  reject def TypeInType : Type := Type

  -- ... and a proposition is not a `Type`.
  reject def NonCumul (P : Prop) : Type := P

  -- ## What goes wrong with borrows of types
  -- A borrow of a type would make `Type` impredicative (D48 (1)): `Impred` quantifies over all
  -- of `Type` and is itself in `Type`, and `SelfApp` applies the polymorphic identity to
  -- itself. An impredicative `Type` with the impredicative `Prop` inside it admits Hurkens'
  -- paradox, a proof of `False`, and has no set-theoretic model. So only data may be
  -- borrowed (switch `refData`; see `BorrowTypes`).
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  reject def PolyId (x : &Type) (a : *x) : *x := a

  reject def SelfApp (u : Unit) : Impred := {
    let T = Impred;
    PolyId(&T, PolyId)
  }

  reject def SelfAppEq (n : Nat) :
      Id Nat (let T = Impred; let f = PolyId(&T, PolyId); let N = Nat; f(&N, n)) n := refl

  reject def PolyTy : Type := Π(x : &Type) (a : Nat). Nat
}

#eval IO.println (run "Universes" Universes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Universes" Universes).allAsExpected
#guard (run "Universes" Universes).count == 8
