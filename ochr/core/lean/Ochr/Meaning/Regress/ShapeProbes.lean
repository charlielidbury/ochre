import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Box

/-!
# Checker verdicts for the structure of a function type (built: each verdict is asserted)

The checker's side of `Regress/ShapeAgree.lean` and `Regress/CodeRuns.lean` (docs/31 D22, D59):
programs the checker ACCEPTS on which the reference run went wrong while a type's structure was
carried beside its meaning (a Π-shape in the type the run returns), each beside a control it
REJECTS. Since D59 the model runs each to the checker's answer (`CodeRuns`). `UseAdder` (the
audit's A11) is in `Regress/AdequacyProbes.lean`.

* `UseFn` (A18): the parameter's type is a call of a type function. The checker computes it to a
  Π-type value and calls through the parameter; the reference bound the parameter at the call's
  result, which had no shape, so its run of `f(n)` failed (`CodeRuns.useFn`: now bound at the
  code the call computed). `UsePred` is the same through the usual idiom, a predicate type, at
  `Type₁` (`CodeRuns.usePred`).
* `Alias` (A19): the function type is bound by a `let`. The reference's binding of `T` carried the
  shape in its type, which the checker's `T : Type` read as a reference state had none of
  (`CodeRuns.alias`: the code is in the value).
* `BoxProof` (A17): a constructor's parameter is solved by the type of a field that is a proof.
  The reference did not run a proof and gave it no type, so the parameter stayed unsolved and its
  run failed (`CodeRuns.boxProof`: an erased place is typed at its stored type).
-/

open Ochr.Test

ochr ShapeProbes uses Nats, Lists, Boxes {
  -- A18: a function type computed by a call
  def Fn (A : Type) : Type := (Π(x : A). A)
  def UseFn (f : Fn(Nat)) (n : Nat) : Nat := f(n)
  def UseFnLet (f : Fn(Nat)) (n : Nat) : Nat := (let g = f; g(n))
  -- control: the computed type is read (the argument is checked against its domain)
  reject def UseFnBad (f : Fn(Unit)) (n : Nat) : Nat := f(n)
  -- A18 through the usual idiom: a predicate type computed by a call (at `Type₁`)
  def Pred (A : Type) : Type₁ := (Π(x : A). Prop)
  def UsePred (P : Pred(Nat)) (n : Nat) : Prop := P(n)
  -- control: the computed predicate type is read
  reject def UsePredBad (P : Pred(Unit)) (n : Nat) : Prop := P(n)

  -- A19: a function type bound by a `let`
  def Alias (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let T = (Π(n : Nat). Nat); let g : T = f; g(n))
  -- control: the alias is read (it is not a function type)
  reject def AliasBad (f : Π(n : Nat). Nat) (n : Nat) : Nat := (let T = Nat; let g : T = f; g(n))

  -- D61: a recursive declaration recursed over, and a nested one built and matched
  def Len (l : List(Nat)) : Nat by l := (
    match l {
      Nil => 0,
      Cons(x, t) => S(Len(t)),
    }
  )
  def LenTwo : Eq(Nat, Len(Cons(3, Cons(4, Nil))), 2) := refl
  -- control: the length is computed
  reject def LenThree : Eq(Nat, Len(Cons(3, Cons(4, Nil))), 3) := refl
  inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
  def Tree : Rose(Nat) := Node(1, Cons(Node(2, Nil), Nil))
  def Root (r : Rose(Nat)) : Nat := (
    match r {
      Node(a, k) => a,
    }
  )
  def RootOfTree : Eq(Nat, Root(Tree), 1) := refl
  -- control: the tree is read
  reject def RootOfTreeBad : Eq(Nat, Root(Tree), 2) := refl

  -- A17: a constructor's parameter solved by a proof field's type
  inductive PBox (A : Prop) := MkPBox(a : A)
  def BoxProof (h : True) (n : Nat) : Nat := (let b = MkPBox(h); n)
  -- control: the field is not a proof
  reject def BoxProofBad (n : Nat) : Nat := (let b = MkPBox(n); n)
}
