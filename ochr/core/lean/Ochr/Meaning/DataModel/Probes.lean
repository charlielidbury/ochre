import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Bool

/-!
# The data model's probe programs: the checker's verdicts (asserted by the build)

The checker's side of the data-model lane (docs/34): each program below is checked when this
file is elaborated, so a green build means every verdict is as marked (`def`: accepted;
`reject def`, `reject inductive`: rejected, the reason asserted by the `#guard`s).

* `CountF` (docs/34 §2.2): recursion over `List(Rose(Nat))` on a forest nested inside the head
  tree, at a strict subterm reached through `Rose`'s nested field. Accepted, and computes `3`.
  A rank each declaration gives its own elements does not decrease there; the height of the
  meaning does.
* `Single` at `Single(Nat, 0)` (§2.4): a field compared with a parameter, the parameter
  instantiated at the declaration itself. Accepted.
* `BW` (§2.4): a type-function field reading an earlier field of declared data type. `BH`: a
  type-function field that computes to a function type at an instance (functions occur in data
  as leaves). Accepted.
* `WT`, `WT2`: a field whose type is a function into the declared type (a W-type shape),
  directly or through a type function. Rejected (positivity, D36), so a data value is a finite
  tree and its height is a natural number.
* `TEq` (§2.3): an equation between parameters of a type of sort `Type₁`, at `Type` (`te`), at a
  function type (`te2`, two level-1 closures), a false instance rejected (`te3`); `te4` passes
  `TEq(Type, Word, Word)` through a universe parameter. `LP`: a type function taking a large
  parameter in a field type. `HL3`: a type function APPLYING a large parameter in a field type
  (the field's type is `f(Zero)`), `h3bad` rejected; `H`: the same with non-uniform recursion at
  the large parameter. All accepted, so a field's type may depend on a large parameter beyond
  equations, and what a data type's code keeps of its parameters must cover that (docs/34 §7).
* `RV` (the residual of docs/34 §3): a field type applying a function (`LenL`) to a field whose
  type mentions a parameter, at an instance mentioning the declaration itself (`rv1 : RV(RV(Nat))`).
  Accepted: the residual is real.
-/

open Ochr.Test

namespace Ochr.Meaning.DataModel.Probes

ochr DMProbeNest uses Nats, Lists, Bools {
  inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
  -- recursion on a forest through the head tree's own forest
  def CountF (f : List(Rose(Nat))) : Nat by f := (
    match f {
      Nil => 0,
      Cons(t, rest) => match t {
        Node(a, k) => S(CountF(k)),
      },
    }
  )
  def F3 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 3) := refl
  reject def F2 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 2) := refl
  -- a field compared with a parameter, at a parameter type, instantiated at itself
  inductive Single (A : Type) (a : A) := MkS(x : A, e : Eq(A, x, a))
  def S1 : Single(Nat, 0) := MkS(0, refl)
  def S2 : Single(Single(Nat, 0), S1) := MkS(S1, refl)
  -- a type-function field reading an earlier field of declared data type
  def BF (b : Bool) : Type := (match b { false => Nat, true => Unit })
  inductive BW := MkBW(b : Bool, x : BF(b))
  def BW1 : BW := MkBW(true, ())
  def BW0 : BW := MkBW(false, 5)
  -- a type-function field computing to a function type at an instance
  def BG (b : Bool) : Type := (match b { false => Nat, true => (Π(n : Nat). Nat) })
  inductive BH := MkBH(b : Bool, x : BG(b))
  -- W-type shapes: a field that is a function into the declared type (controls)
  reject inductive WT := WLeaf | WNode(f : Π(n : Nat). WT)
  def FnTy (A : Type) : Type := (Π(n : Nat). A)
  reject inductive WT2 := WLeaf2 | WNode2(f : FnTy(WT2))
}

#guard (run "DMProbeNest" DMProbeNest).rejectedWith [
  ("F2", "the body of F2 has type ⊤, but the goal is False"),
  ("WT", "field f of WNode : Π(n : Nat). WT: fields are first-order data"),
  ("WT2", "field f of WNode2 : FnTy(WT2): fields are first-order data")]

ochr DMProbeLarge uses Nats, Lists, WordType {
  -- an equation between parameters of a type of sort `Type₁`
  inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
  def te : TEq(Type, Word, Word) := MkTEq[Type, Word, Word](refl)
  def te2 : TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Word) :=
    MkTEq[Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Word](refl)
  reject def te3 : TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Unit) :=
    MkTEq[Π(x : Word). Type, λ(x : Word) : Type => Word, λ(y : Word) : Type => Unit](refl)
  -- a large type through a universe parameter
  def IdT (A : Type) (x : A) : A := x
  def te4 : TEq(Type, Word, Word) := IdT(TEq(Type, Word, Word), te)
  -- type functions taking, and applying, a large parameter in a field type
  def Pick (U : Type₁) (a : U) : Type := Word
  inductive LP (U : Type₁) (a : U) := MkLP(x : Pick(U, a))
  def App0 (f : Π(x : Word). Type) : Type := f(Zero)
  inductive HL3 (f : Π(x : Word). Type) := MkHL3(y : App0(f))
  def h3 : HL3(λ(x : Word) : Type => Word) := MkHL3[λ(x : Word) : Type => Word](Zero)
  reject def h3bad : HL3(λ(x : Word) : Type => Unit) := MkHL3[λ(x : Word) : Type => Unit](Zero)
  inductive H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λ(x : Word) : Type => f(Succ(x))))
  -- the residual: a field type applying a function to parameter-typed data, used at itself
  inductive RV (A : Type) := MkRV(xs : List(A), v : Eq(Word, LenL(A, xs), LenL(A, xs)))
  def rv0 : RV(Nat) := MkRV[Nat](Nil, refl)
  def rv1 : RV(RV(Nat)) := MkRV[RV(Nat)](Cons(rv0, Nil), refl)
}

#guard (run "DMProbeLarge" DMProbeLarge).rejectedWith [
  ("te3", "field h of MkTEq has type ⊤, expected Eq(Π(x : Word). Type"),
  ("h3bad", "field y of MkHL3 has type Word, expected Unit")]

/-! ## Where K3 could be wrong (docs/34 §13), and the residual made decisive (§12)

* `TagNe`, `ListNe`, `PHNe`, `TEqNe`, `TEqNe2`, `TagAB`: an equation between two different
  applications of type formers is stuck, never `False`: the checker does not decide that type
  formers are injective. So identifying types whose records agree (`Tag(Zero)` and
  `Tag(Succ(Zero))`, `PH(Type)` and `PH(Prop)`, which K3's records do) contradicts no verdict.
* `RE` (accepted; `re1 : RE(RE(Nat))` accepted, `reBad` rejected): the residual with a field type
  that the function's result decides.
* `RoseL` (rejected): applying a function to a NESTED field at the declaration itself is not
  first-order (its argument mentions the type being declared), so the residual has no nested form.
* `FP` (accepted): a function-valued parameter applied in an equation field.
* `H`, `hh` (accepted): non-uniform recursion at a large parameter that a field type applies.
* `LB` (rejected): a large parameter typing another, applied by a type function in a field type.
* `MM` (accepted; `mm0`, `mm1` accepted, `mm0Bad` rejected): a large function applied in a field
  type and its result matched.
-/

ochr DMProbeAdv uses Nats, Lists, WordType {
  inductive Tag (n : Word) := MkTag(x : Word)
  reject def TagNe (h : Eq(Type, Tag(Zero), Tag(Succ(Zero)))) : False := h
  reject def ListNe (h : Eq(Type, List(Word), List(Unit))) : False := h
  inductive PH (U : Type₁) := MkPH
  reject def PHNe (h : Eq(Type, PH(Type), PH(Prop))) : False := h
  inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
  reject def TEqNe (h : Eq(Type, TEq(Type, Word, Word), TEq(Type, Unit, Unit))) : False := h
  reject def TEqNe2 (h : Eq(Type, TEq(Type, Word, Word), TEq(Π(x : Word). Type, λ(x : Word) : Type => Word, λ(x : Word) : Type => Word))) : False := h
  inductive TagA (n : Word) := MkTA(x : Word)
  inductive TagB (n : Word) := MkTB(x : Word)
  reject def TagAB (h : Eq(Type, TagA(Zero), TagB(Zero))) : False := h
  inductive RE (A : Type) := MkRE(xs : List(A), v : Eq(Word, LenL(A, xs), Succ(Zero)))
  def re0 : RE(Nat) := MkRE[Nat](Cons(0, Nil), refl)
  def re1 : RE(RE(Nat)) := MkRE[RE(Nat)](Cons(re0, Nil), refl)
  reject def reBad : RE(Nat) := MkRE[Nat](Nil, refl)
  reject inductive RoseL (A : Type) := NodeL(kids : List(RoseL(A)), v : Eq(Word, LenL(RoseL(A), kids), LenL(RoseL(A), kids)))
  inductive FP (f : Π(x : Word). Word) := MkFP(y : Word, e : Eq(Word, f(y), y))
  def App0 (f : Π(x : Word). Type) : Type := f(Zero)
  inductive H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λ(x : Word) : Type => f(Succ(x))))
  def hh : H(λ(x : Word) : Type => Word) := HS[λ(x : Word) : Type => Word](Zero, HB)
  def AppU (U : Type₁) (F : Π(x : U). Type) (a : U) : Type := F(a)
  reject inductive LB (U : Type₁) (F : Π(x : U). Type) (a : U) := MkLB(y : AppU(U, F, a))
  def MG (G : Π(X : Type). Word) : Type := (match G(Word) { Zero => Word, Succ(k) => Unit })
  inductive MM (G : Π(X : Type). Word) := MkMM(y : MG(G))
  def mm0 : MM(λ(X : Type) : Word => Zero) := MkMM[λ(X : Type) : Word => Zero](Zero)
  reject def mm0Bad : MM(λ(X : Type) : Word => Zero) := MkMM[λ(X : Type) : Word => Zero](())
  def mm1 : MM(λ(X : Type) : Word => Succ(Zero)) := MkMM[λ(X : Type) : Word => Succ(Zero)](())
}

#guard (run "DMProbeAdv" DMProbeAdv).rejectedWith [
  ("TagNe", "the body of TagNe has type Eq(Type, Tag(Zero), Tag(Succ(Zero))), but the goal is False"),
  ("ListNe", "the body of ListNe has type Eq(Type, List(Word), List(Unit)), but the goal is False"),
  ("PHNe", "the body of PHNe has type Eq(Type, PH(Type), PH(Prop)), but the goal is False"),
  ("TEqNe", "the body of TEqNe has type Eq(Type, TEq(Type, Word, Word), TEq(Type, Unit, Unit)), but the goal is False"),
  ("TEqNe2", "the body of TEqNe2 has type Eq(Type, TEq(Type, Word, Word), TEq(Π(x : Word). Type"),
  ("TagAB", "the body of TagAB has type Eq(Type, TagA(Zero), TagB(Zero)), but the goal is False"),
  ("reBad", "field v of MkRE has type ⊤, expected False"),
  ("RoseL", "field v of NodeL : Eq(Word, LenL(RoseL(A), kids), LenL(RoseL(A), kids)): fields are first-order data"),
  ("LB", "κ is not a type: its declared type is not a sort"),
  ("mm0Bad", "field y of MkMM has type Unit, expected Word")]

end Ochr.Meaning.DataModel.Probes
