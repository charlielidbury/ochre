import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! Reviewer-6's A1 (notes/reviewer-6.md, W1): a closed proof of `False` accepted by the
default checker. A generalisation record minted in one arm (`⌈σg(())⌉ := σ3`, with the type
the family has at that arm) is re-derived by its program text in the other arm, where the
call has another type; an observation in the untyped machine types the place from σ3's type
and D59 (η for `Unit`) makes the comparison true.

`FuzzLie` is the fuzzer's shrunk form of the same leak (`--a1 100`, seed 1, case 5): the
statement's `Z` arm does not even call `g1`; the proof's `Z` arm mints the record by
splitting `g1(())`. `FuzzBoom` turns it into `False`.

These verdicts are the bug, recorded as they stand on ochr-core 305f1c77: every `def` below
is accepted. When A1 is fixed, `F`, `Boom`, `FuzzLie` and `FuzzBoom` become `reject`. -/
ochr A1Leak uses Std {
  def T (n : Nat) : Type := match n { Z => Box(Unit), S _ => Box(Bool) }
  def Cmp2 (b : Box(Bool)) : Prop := (let c = b; Id Unit (c := MkBox(true)) (c := MkBox(false)))
  def L2 (b : Box(Bool)) (h : Cmp2(b)) : False := h
  def G (n : Nat) : Prop := match n { Z => ⊤, S _ => False }
  def F (n : Nat) (g : Π(u : Unit). T(n)) : G(n) := (
    match n {
      Z => (let x = g(()); match x { MkBox(v) => refl }),
      S _ => (let y = g(()); L2(y, refl)),
    }
  )
  def Boom : False := F(1, λ(u : Unit) : T(1) => MkBox(true))
}
ochr A1Fuzz {
  inductive B2 := F | T
  inductive Bx (A : Type) := MkBx(v : A)
  def TF (n : Nat) : Type := match n { Z => Bx(Unit), S _ => Bx(B2) }
  def CmpBx (b : Bx(B2)) : Prop := (let c = b; Id Unit (c := MkBx[B2](T)) (c := MkBx[B2](F)))
  def FuzzLie (n0 : Nat) (g1 : Π (u : Unit). TF(n0)) : Id Prop (match n0 { Z => ⊤, S p7 => let y6 = g1(()); CmpBx(y6) }) ⊤ :=
    match n0 { Z => (let x5 = g1(()); match x5 { MkBx(v) => refl }), S _ => refl }
  def FuzzBoom : False := (
    let h = FuzzLie(1, λ(u : Unit) : TF(1) => MkBx[B2](T));
    J(Prop, ⊤, False, λ(P : Prop) : Prop => P, symm h, refl)
  )
}
#eval IO.println (run "A1Leak" A1Leak).show
#eval IO.println (run "A1Fuzz" A1Fuzz).show
