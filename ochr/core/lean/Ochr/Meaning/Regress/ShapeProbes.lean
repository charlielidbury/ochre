import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Box

/-!
# Checker verdicts for the shape of a function type (built: each verdict is asserted)

The checker's side of `Regress/ShapeAgree.lean` (docs/31 D22): three programs the checker ACCEPTS
on which the reference run has no Π-shape where the checker's stored type has one, or the other
way round, each beside a control it REJECTS. `UseAdder` (the audit's A11) is in
`Regress/AdequacyProbes.lean`.

* `UseFn` (A18): the parameter's type is a call of a type function. The checker computes it to a
  Π-type value and calls through the parameter; the reference binds the parameter at the call's
  result, which has no shape (`ShapeAgree.call_noShape`), so its run of `f(n)` fails. `UsePred`
  is the same through the usual idiom, a predicate type.
* `Alias` (A19): the function type is bound by a `let`. The reference's binding of `T` carries the
  shape (in its type, `ShapeAgree.pi_shape`); the checker's binding `T : Type`, read as a
  reference state, has none (`ShapeAgree.tyS_sort_shape`).
* `BoxProof` (A17): a constructor's parameter is solved by the type of a field that is a proof.
  The reference does not run a proof and gives it no type, so the parameter stays unsolved and its
  run fails.
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

  -- A17: a constructor's parameter solved by a proof field's type
  inductive PBox (A : Prop) := MkPBox(a : A)
  def BoxProof (h : True) (n : Nat) : Nat := (let b = MkPBox(h); n)
  -- control: the field is not a proof
  reject def BoxProofBad (n : Nat) : Nat := (let b = MkPBox(n); n)
}
