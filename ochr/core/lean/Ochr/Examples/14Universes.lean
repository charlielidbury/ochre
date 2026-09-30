import Ochr.Test

/-! # 14. Universes

`Prop` and `Type` both live in `Type₁`, side by side, as `Prop` and `Set` do in Coq (D66):
`Type` holds only types that exist at runtime, which is what lets every `A : Type` be
borrowed (`BorrowTypes`). There is no `Type : Type`, and universes are not cumulative, so a
proposition is not a `Type` (RULES preamble). Non-cumulativity matters for erasure: with
`Prop ≤ Type`, a function declared to return a `Type` could return a proposition, and whether
its calls are erased would depend on the value (D28).

Defined in the preamble of RULES, in P2 and in D66. -/

open Ochr.Test

ochr Universes {
  -- `Prop` and `Type` are types in `Type₁` ...
  def PropInType1 : Type₁ := Prop
  def TypeInType1 : Type₁ := Type

  -- ... but neither is a `Type`: `Prop` is not in `Type` (D66; switch `propUp`) ...
  reject def PropInType : Type := Prop
  reject def TypeInType : Type := Type

  -- ... and a proposition is not a `Type`.
  reject def NonCumul (P : Prop) : Type := P

  -- ## What goes wrong with borrows of types
  -- A borrow of a type would make `Type` impredicative (D48 (1)): `Impred` quantifies over all
  -- of `Type` and is itself in `Type`, and `SelfApp` applies the polymorphic identity to
  -- itself. An impredicative `Type` with the impredicative `Prop` beside it admits Hurkens'
  -- paradox, a proof of `False`, and has no set-theoretic model. So only what is in `Type`
  -- may be borrowed, and `Type` itself is in `Type₁` (switch `refData`; see `BorrowTypes`).
  reject def Impred : Type := Π(x : &Type) (a : *x). *x
  reject def PolyId (x : &Type) (a : *x) : *x := a

  reject def SelfApp (u : Unit) : Impred := (
    let T = Impred;
    PolyId(&T, PolyId)
  )

  reject def SelfAppEq (n : Nat) :
      Id Nat (let T = Impred; let f = PolyId(&T, PolyId); let N = Nat; f(&N, n)) n := refl

  reject def PolyTy : Type := Π(x : &Type) (a : Nat). Nat
}

#eval IO.println (run "Universes" Universes).show

-- every verdict as expected, and the exact number of declarations (a truncated file changes it)
#guard (run "Universes" Universes).allAsExpected
#guard (run "Universes" Universes).count == 10

/-! ## Sorts are syntactic

A term written where a type is expected must have a *declared* type that is a sort, read
from the declared types of its heads without normalising (D55). `T(Z)` computes to `⊤`, but
its declared type is `P(Z)`, which is a sort only by computation, so it cannot be written as a
type. Before D55 Ochr had two notions of "proposition", the declared sort (erasure) and the
computed one (conversion), and moving values between them gave closed proofs of `False`
(reviewer-4 W1: `Boom`, `Boom2`, `Boom4`) and a proposition with two distinguishable proofs
(W2: `TT`, `K1`, `K2`). The programs are reviewer-4's, verbatim except that `P` is declared in `Type₁`, where `Prop` lives since D66; with D55 each falls where
`T(Z)` is written as a type (switch `sortsSyntactic`; D54 alone already rejects `Boom`,
`Boom2`, `RunIs` and `Lie4` at their arguments).

Defined in RULES P2 ("Sorts are syntactic"). -/

ochr Sorts {
  def P (n : Nat) : Type₁ := match n { Z => Prop, S _ => Prop }
  def T (n : Nat) : P(n) := match n { Z => ⊤, S _ => ⊤ }
  reject def W (u : Unit) : T(Z) := refl
  reject def f (x : &Nat) : T(Z) := (*x := S Z; W(()))
  def RunK (k : Π(x : &Nat). ⊤) (x : &Nat) : Unit := (k(x); ())
  def Stmt (k : Π(x : &Nat). ⊤) (x : &Nat) : Id Unit (RunK(k, x)) () := refl
  reject def Boom : False := (let c = 0; Stmt(f, &c))

  def RunGen (k : Π(x : &Nat). ⊤) : Id Nat (let c = 0; RunK(k, &c); c) 0 := refl
  reject def Boom2 : False := RunGen(f)
  reject def RunIs : Id Nat (let c = 0; RunK(f, &c); c) 1 := refl

  reject def Lie4 (n : Nat) : Id Nat (let c = Z; match n {
      Z => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()),
      S _ => (let q : (Π(x : &Nat). ⊤) = f; q(&c); ()) }; c) 1 := match n { Z => refl, S _ => refl }
  reject def Boom4 : False := Lie4(0)

  reject def TT : Prop := Π(x : &Nat). T(Z)
  reject def g2 (x : &Nat) : T(Z) := W(())
  reject def k (h : Π(x : &Nat). T(Z)) : Nat := (let c = Z; h(&c); c)
  reject def K1 : Eq Nat (k(f)) 1 := refl
  reject def K2 : Eq Nat (k(g2)) 0 := refl
}

#eval IO.println (run "Sorts" Sorts).show

#guard (run "Sorts" Sorts).allAsExpected
#guard (run "Sorts" Sorts).count == 17
