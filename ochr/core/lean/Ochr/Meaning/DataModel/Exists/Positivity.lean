import Ochr.Consistency
import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Bool

/-!
# Positivity: what the existence proof needs of an accepted declaration, and a battery (D107's input)

## The condition

**Semantic.** The canonical model builds a declaration `D`'s record at parameters path by path
(a record is a function of paths; the record of the data type at a position is the path's
continuation), and the carriers by stages from the records. The fixed point exists when `D`'s own
records reach `D`'s field types only at DATA positions: the entry at a path `k :: q` reads `D`'s
records only at paths no longer than `q`, and no leaf (a code that is not a data code at the
model's carrier: a function type, a proposition, a number) depends on `D`'s records. In set terms:
the functor sending the family of `D`'s carriers to the field types is polynomial in it (the
carriers occur only as positions of subtrees, never inside a leaf type). Every program below that
is accepted today and has no set model breaks exactly this: `D`'s carrier ends up inside a leaf
(`X → Void`).

**Syntactic (sufficient).** Let `N(M)`, the NESTABLE type parameters of an inductive `M`, be the
GREATEST set such that for each `i ∈ N(M)` every occurrence of `var i` in `M`'s field-type terms
(arguments of `M`'s own occurrences included) is either the whole field type, or an argument of an
inductive former `M'(…)` at a parameter `j ∈ N(M')` (`M' = M` included, at `N(M)` itself, so the
greatest fixed point). Then: every occurrence of the declaration `D` in its field types must be the
whole field type or an argument of a former `M'(…)` at a parameter `j ∈ N(M')`, **`M' = D`
included**, with `N(D)` computed from the field types being declared (during `checkInd`, Σ holds `D`
with no constructors, so `paramNestable` would find every parameter vacuously nestable). Today
`nestViolation` and `firstOrderArgs` require the second clause only for `M' ≠ D` (`m != n`): that
is the hole every paradox below goes through. Optional: the type of an `Eq` may count as a nestable
position (harmless for the model, which keys an equation by small readings), as may a value
parameter's argument (it cannot mention `D` anyway).

## The battery

* `SecondHole` below (the D107 agent's, independent of the first: the position a self occurrence
  gives a parameter was ignored when judging an EARLIER declaration's parameter nestable): accepted
  today with a proof of `False`; excluded by the greatest fixed point.
* `Curry` (`ConsistencyCE.lean`), `Chain`, `TyFn`, `PropRoute` below: accepted today, each with a
  closed proof of `False`, and no set model (`X ≅ (X → ⊥) × inhabited`, so `X` is inhabited iff it
  is empty). They go through a self occurrence `Q(Q(A, …), …)` at a parameter `A` that `Q` passes,
  directly or through another inductive or through a type-function parameter, to a type function
  that is a function type at some instances only (stuck at the generic one). Under the condition,
  `A ∉ N(Q)`, so each `Q` is rejected.
* `MustStay` below, and `DataModel/Probes.lean` (`Rose`, `CountF`, `Single`/`S2`, `BW`, `BH`,
  `TEq`, `HL3`, `H`, `RV`, `RE`, `FP`, `MM`), `Exists/Probes.lean` (`DMXShapes`): accepted, modelled
  by the construction, and accepted under the condition (each nesting is at a parameter used only as
  a field type or at nestable positions: `DD(DD(A))`, `List(RN(Duo(A, A)))`, `Box(BB(Box(A)))`,
  `List(Duo(RP(A), Nat))`, `List(List(NN(A)))`; `HN` nests itself at `A` while its large parameter
  takes the shifted function).
* Controls (`Controls` below), rejected today and to stay rejected: nesting a later declaration at
  a parameter passed to a type function (`E`), and the routes through `Prop` that large elimination
  would open (`D45`).
-/

open Ochr Ochr.Test Ochr.Surface Ochr.Consistency

namespace Ochr.Meaning.DataModel.Exists.Positivity

/-- A block's own declarations have a parameterless definition `Boom : False` and no hole, and the
library and the block are accepted at the default fuel: a counterexample to `consistency`. -/
def boomAccepted (q : Program) : Bool :=
  !q.any (·.hasHole) && accepts {} 2000000 (Prelude.decls ++ q) &&
    q.any fun d => d.ind?.isNone && d.params.isEmpty && d.name == "Boom" &&
      (match d.ret.unloc with | .ident "False" => true | _ => false)

-- Through a chain of two inductives: `Q` passes `A` to the inductive `P`, which passes it to the
-- type function `FB`.
ochr Chain {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def FB (X : Type) (b : Bit) : Type := (match b { B1 => (Π(x : X). Void), B0 => Unit })
  inductive P (A : Type) (b : Bit) := MkP(y : FB(A, b))
  inductive Q (A : Type) (b : Bit) := MkQ(p : P(A, b), z : OptB(Q(Q(A, b), B1), b))
  def Delta (x : Q(Unit, B0)) : Void := (
    match x {
      MkQ(p, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQ(p2, z2) => match p2 {
            MkP(f) => f(MkQ[Unit, B0](p, SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](MkP[Q(Unit, B0), B1](f), z2)))),
          },
        },
      },
    }
  )
  def Lem (g : Π(x : Q(Unit, B0)). Void) : False :=
    VF(g(MkQ[Unit, B0](MkP[Unit, B0](()), SomeB[Q(Q(Unit, B0), B1), B0](MkQ[Q(Unit, B0), B1](MkP[Q(Unit, B0), B1](g), NoneB[Q(Q(Q(Unit, B0), B1), B1), B1](()))))))
  def Boom : False := Lem(Delta)
}

#guard boomAccepted Chain.decls

-- Through a parameter that is a type function (a parameter of `Type₁`): `QG` passes `A` to the
-- global `AppB`, which applies the parameter `G`; at `G := Neg` the field is `QG(…) → Void`.
ochr TyFn {
  inductive Bit := B0 | B1
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def FF (b : Bit) : Type := (match b { B0 => Void, B1 => Unit })
  inductive OptB (X : Type) (b : Bit) := NoneB(h : FF(b)) | SomeB(x : X)
  def AppB (G : Π(X : Type). Type) (A : Type) (b : Bit) : Type := (match b { B1 => G(A), B0 => Unit })
  def Neg (X : Type) : Type := (Π(x : X). Void)
  inductive QG (G : Π(X : Type). Type) (A : Type) (b : Bit) := MkQG(y : AppB(G, A, b), z : OptB(QG(G, QG(G, A, b), B1), b))
  def Delta (x : QG(Neg, Unit, B0)) : Void := (
    match x {
      MkQG(y, z) => match z {
        NoneB(h) => h,
        SomeB(w) => match w {
          MkQG(f, z2) => f(MkQG[Neg, Unit, B0](y, SomeB[QG(Neg, QG(Neg, Unit, B0), B1), B0](MkQG[Neg, QG(Neg, Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  def Lem (g : Π(x : QG(Neg, Unit, B0)). Void) : False :=
    VF(g(MkQG[Neg, Unit, B0]((), SomeB[QG(Neg, QG(Neg, Unit, B0), B1), B0](MkQG[Neg, QG(Neg, Unit, B0), B1](g, NoneB[QG(Neg, QG(Neg, QG(Neg, Unit, B0), B1), B1), B1](()))))))
  def Boom : False := Lem(Delta)
}

#guard boomAccepted TyFn.decls

-- Through `Prop`: the negative occurrence is a proof field (`FBP(X, B1)` is `X → False`), and the
-- diagonal is itself a proof, so `Delta` applied to its own encoding is never run.
ochr PropRoute {
  inductive Bit := B0 | B1
  def FFP (b : Bit) : Prop := (match b { B0 => False, B1 => True })
  inductive OptP (X : Type) (b : Bit) := NoneP(h : FFP(b)) | SomeP(x : X)
  def FBP (X : Type) (b : Bit) : Prop := (match b { B1 => (Π(x : X). False), B0 => True })
  inductive QP (A : Type) (b : Bit) := MkQP(y : FBP(A, b), z : OptP(QP(QP(A, b), B1), b))
  def Delta (x : QP(Unit, B0)) : False := (
    match x {
      MkQP(y, z) => match z {
        NoneP(h) => h,
        SomeP(w) => match w {
          MkQP(f, z2) => f(MkQP[Unit, B0](y, SomeP[QP(QP(Unit, B0), B1), B0](MkQP[QP(Unit, B0), B1](f, z2)))),
        },
      },
    }
  )
  def Boom : False := Delta(MkQP[Unit, B0](I, SomeP[QP(QP(Unit, B0), B1), B0](MkQP[QP(Unit, B0), B1](Delta, NoneP[QP(QP(QP(Unit, B0), B1), B1), B1](I)))))
}

#guard boomAccepted PropRoute.decls

-- The second hole (found by the D107 agent; independent of the first): nestability of an already
-- declared inductive ignored where its own self occurrence puts a parameter. `E` passes `B` to `A`'s
-- position (`E(B, A, 1)`), and `A` goes to the type function `Neg`, so under the greatest fixed
-- point `B ∉ N(E)` (it occurs only at `E`'s parameter `A`, and `A ∉ N(E)`); `Bad` nests itself at
-- `B` and is rejected. Today `B` was judged nestable: `Bad ≅ E(Unit, Bad, 0) ≅ E(Bad, Unit, 1) ≅
-- (Bad → Void)`.
ochr SecondHole {
  inductive Void : Type
  def VF (v : Void) : False := (match v { })
  def Neg (X : Type) (n : Nat) : Type := (match n { Z => Void, S(k) => (Π(x : X). Void) })
  inductive E (A : Type) (B : Type) (n : Nat) := MkE(z : E(B, A, 1), e : Eq(Nat, n, 0)) | StopE(f : Neg(A, n))
  inductive Bad := MkBad(e : E(Unit, Bad, 0))
  def Lem (g : Π(x : Bad). Void) : False :=
    VF(g(MkBad(MkE[Unit, Bad, 0](StopE[Bad, Unit, 1](g), refl))))
  def Delta (x : Bad) : Void := (
    match x {
      MkBad(e) => match e {
        MkE(z, h) => match z {
          MkE(z2, h2) => match h2 { },
          StopE(f) => f(MkBad(MkE[Unit, Bad, 0](StopE[Bad, Unit, 1](f), h))),
        },
        StopE(f) => match f { },
      },
    }
  )
  def Boom : False := Lem(Delta)
}

#guard boomAccepted SecondHole.decls

-- Accepted today, modelled by the construction, and accepted under the condition.
ochr MustStay uses Nats, Lists, Bools {
  inductive Duo (A : Type) (B : Type) := MkDuo(fst : A, snd : B)
  inductive Box (A : Type) := MkBox(x : A)
  -- a self occurrence whose argument mentions the declaration, at a nestable parameter
  inductive DD (A : Type) := DLeaf | DNode(x : DD(DD(A)))
  -- non-uniform nesting
  inductive RN (A : Type) := NodeN(a : A, kids : List(RN(Duo(A, A))))
  inductive BB (A : Type) := BLeaf(a : A) | BNode(b : Box(BB(Box(A))))
  -- nesting through two declarations, and two levels
  inductive RP (A : Type) := NodeP(a : A, kids : List(Duo(RP(A), Nat)))
  inductive NN (A : Type) := NNode(kids : List(List(NN(A))))
  -- a large parameter shifted along the unfolding, with self-nesting at a nestable parameter
  def App0 (f : Π(x : Nat). Type) : Type := f(0)
  inductive HN (f : Π(x : Nat). Type) (A : Type) := HB(a : A) | HS(y : App0(f), r : HN(λ(x : Nat) : Type => f(S(x)), HN(f, A)))
  -- a recursive `Prop`-sorted declaration, used as a field; a type function returning data
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))
  inductive WithEv := MkWE(n : Nat, p : Ev(n))
  def EvT (b : Bool) : Type := (match b { false => Nat, true => List(Nat) })
  inductive TF := MkTF(b : Bool, x : EvT(b))
  -- a type function at a parameter that is NOT nested (so not affected by the condition)
  def FBB (X : Type) (b : Bool) : Type := (match b { true => (Π(x : X). Nat), false => Unit })
  inductive FBox (A : Type) (b : Bool) := MkFBox(y : FBB(A, b))
  -- the declaration at a type parameter that types a value parameter whose argument is a value of
  -- the declaration (D107's question 2; `Proto/ValueParams.lean` models the form with an equation)
  inductive G2 (A : Type) (a : A) := MkG2(x : A)
  inductive T2 := Leaf2 | Node2(t : T2, g : G2(T2, t))
}

-- Rejected today, and to stay rejected.
ochr Controls uses Nats, Bools {
  inductive Void : Type
  def FB (X : Type) (b : Bool) : Type := (match b { true => (Π(x : X). Void), false => Unit })
  inductive P (A : Type) (b : Bool) := MkP(y : FB(A, b))
  -- a later declaration nested at a parameter passed to a type function (K4)
  reject inductive E := MkE(p : P(E, true))
  -- large elimination from a proposition with two constructors, or a data field (D45)
  inductive POr : Prop := PL | PR
  reject def f (p : POr) : Bool := (match p { PL => false, PR => true })
  inductive PS : Prop := MkPS(n : Nat)
  reject def get (p : PS) : Nat := (match p { MkPS(n) => n })
}

#guard (run "Controls" Controls).rejectedWith [
  ("E", "field p of MkE : P(E, true): E occurs at the parameter A of P, which P passes to a type function"),
  ("f", "[D45] a match on a proof of POr returns a non-proof"),
  ("get", "[D45] a match on a proof of PS returns a non-proof")]

end Ochr.Meaning.DataModel.Exists.Positivity
