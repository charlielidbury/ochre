import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Bool

/-!
# The existence lane's probe programs: the checker's verdicts (asserted by the build)

Each program below is checked when this file is elaborated (`def`, `inductive`: accepted;
`reject …`: rejected, the reason asserted by a `#guard`).

* `DMXFrame` (`StatementCE`, counterexample 3): a field type reading a TYPE parameter twice in
  sequence (`DL`, by `let`; `DT`, as two arguments of a data-returning call) is accepted, because
  `fieldTele` binds a parameter at its declared reading (`Type` reads as copy). A field or a `Nat`
  parameter read twice is rejected (`DD2`, `DP2`: they read by move).
* `DMXShapes`: the declaration shapes the construction must cover, all accepted. A self occurrence
  whose argument mentions the declaration (`DD`: `DD(DD(A))`); non-uniform nesting (`RN`:
  `List(RN(Pair(A, A)))`, `BB`: `Box(BB(Box(A)))`); nesting through two declarations (`RP`:
  `List(Pair(RP(A), Nat))`) and two levels (`NN`); a recursive `Prop`-sorted declaration used as a
  field (`Ev`, `WithEv`); a type function returning a data type (`TF`).
-/

open Ochr.Test

namespace Ochr.Meaning.DataModel.Exists.Probes

ochr DMXFrame uses Nats {
  inductive DL (A : Type) := MkDL(e : Eq(Nat, (let x = A; let y = A; 0), 0))
  def dl : DL(Nat) := MkDL[Nat](refl)
  def F2 (X : Type) (Y : Type) (n : Nat) : Nat := n
  inductive DT (A : Type) := MkDT(n : Nat, e : Eq(Nat, F2(A, A, n), n))
  def dt : DT(Nat) := MkDT[Nat](3, refl)
  def Two (a : Nat) (b : Nat) : Nat := a
  reject inductive DD2 := MkDD2(n : Nat, e : Eq(Nat, Two(n, n), n))
  reject inductive DP2 (n : Nat) := MkDP2(e : Eq(Nat, Two(n, n), n))
}

#guard (run "DMXFrame" DMXFrame).rejectedWith [
  ("DD2", "[Read] n was moved out or its borrow ended (reading ⊥)"),
  ("DP2", "[Read] n was moved out or its borrow ended (reading ⊥)")]

ochr DMXShapes uses Nats, Lists, Bools {
  inductive Duo (A : Type) (B : Type) := MkDuo(fst : A, snd : B)
  inductive DD (A : Type) := DLeaf | DNode(x : DD(DD(A)))
  inductive RN (A : Type) := NodeN(a : A, kids : List(RN(Duo(A, A))))
  inductive RP (A : Type) := NodeP(a : A, kids : List(Duo(RP(A), Nat)))
  inductive NN (A : Type) := NNode(kids : List(List(NN(A))))
  inductive Box (A : Type) := MkBox(x : A)
  inductive BB (A : Type) := BLeaf(a : A) | BNode(b : Box(BB(Box(A))))
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))
  inductive WithEv := MkWE(n : Nat, p : Ev(n))
  def EvT (b : Bool) : Type := (match b { false => Nat, true => List(Nat) })
  inductive TF := MkTF(b : Bool, x : EvT(b))
}

-- The boundary of the finding that a field's type can read a global's meaning (exists2,
-- 2026-11-21): a type function whose codomain is `Type₁` cannot type a field (`D1`); one returning
-- `Type₀` cannot be declared at `Type₁` (`G2`, universes are not cumulative) nor return `Type` at
-- `Type` (`TT`); an equation side calling a function (`Ev` with `S(S(m))`), a type function of the
-- declaration's own type parameter (`D3`), one that is a function type at some instances only (`D5`)
-- and a `Prop`-valued one (`D6`) are accepted; a type function applied to the declaration is not
-- (`D4`). So every global a field type calls has codomain `Prop` or `Type₀`.
ochr DMXBoundary uses Nats, Bools {
  def G (b : Bool) : Type₁ := (match b { false => Type, true => Type })
  reject inductive D1 := MkD1(b : Bool, x : G(b))
  reject def G2 (b : Bool) : Type₁ := (match b { false => Nat, true => Nat })
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))
  def F (X : Type) : Type := X
  inductive D3 (A : Type) := MkD3(x : F(A))
  reject inductive D4 (A : Type) := MkD4(x : F(D4(A)))
  def FB (X : Type) (b : Bool) : Type := (match b { true => (Π(x : X). Nat), false => Unit })
  inductive D5 (A : Type) := MkD5(b : Bool, y : FB(A, b))
  def PP (b : Bool) : Prop := (match b { true => True, false => False })
  inductive D6 := MkD6(b : Bool, h : PP(b))
  reject def TT (b : Bool) : Type := (match b { true => Type, false => Nat })
}

#guard (run "DMXBoundary" DMXBoundary).rejectedWith [
  ("D1", "field x of MkD1: its type must be in Prop or Type"),
  ("G2", "the body of G2 has type Type, but the goal is Type₁"),
  ("D4", "field x of MkD4 : F(D4(A)): fields are first-order data (inductive types, Nat, Unit, ×, earlier type functions) or parameters, D36"),
  ("TT", "the body of TT has type Type₁, but the goal is Type")]

end Ochr.Meaning.DataModel.Exists.Probes
