import Ochr.Examples.Nat
import Ochr.Examples.List
import Ochr.Examples.Option
open Ochr.Test

/-! # Probe (D94): well-typed programs whose join drops a place, aimed at the new rejection

D94 rejects a definition whose match's join names a place that does not exist and whose longest
existing prefix holds neither `⊥` nor `⋆`. Each program below is well typed, and its join drops a
place through a field, a type parameter, a computed type, a stuck call's result, a several-
constructor value, a returned borrow lent before the match (non-tail, and tail with no entry),
a statement's side, and a callee run at the generic call. All are accepted: none reaches the
rejection, which only ill-typed places in arms that are not run reach (`JoinPlaces.BadIdx`).
Run: `lake env lean ../probes/moved-place-exits/Adversarial.lean` from `ochr/core/lean`; silent.
-/
ochr AdvJ uses Nats, Lists, Options {
  inductive In := MkIn(a : List(Nat), b : List(Nat))
  inductive Out := MkOut(i : In, z : List(Nat))
  inductive Box (A : Type) := MkBox(v : A, w : List(Nat))
  def TF (n : Nat) : Type := match n { Z => In, S _ => In }
  def mk (u : Unit) : TF(0) := MkIn(Nil[Nat], Nil[Nat])
  def Stk (k : Nat) (x : In) : In := match k { Z => x, S _ => x }
  -- 1. a dead arm moves a field of a field (known value)
  def D1 (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : List(Nat) := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs);
    match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  -- 2. the same at an unknown value (the join's place through refined unknowns)
  def D2 (k : Nat) (c : Out) : List(Nat) := (match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  -- 3. through a type parameter (grain: whole)
  def D3 (A : Type) (k : Nat) (b : Box(A)) : List(Nat) := (match k { Z => (), S m => (let a = b.0; ()) }; b.1)
  -- 4. through a type computed by a match (grain: whole)
  def D4 (k : Nat) : List(Nat) := (let v = mk(()); match k { Z => (), S m => (let a = v.0; ()) }; Nil[Nat])
  -- 5. a field of a stuck program's result (a sealed parent of a one-constructor type)
  def D5 (j : Nat) (k : Nat) (x : In) : List(Nat) := (let v = Stk(j, x); match k { Z => (), S m => (let a = v.0; ()) }; v.1)
  -- 6. a pattern field of a several-constructor value (grain: whole)
  def D6 (k : Nat) (o : Opt(List(Nat))) : Unit := (match k { Z => (), S m => (match o { None => (), Some(w) => (let a = w; ()) }) }; ())
  -- 8. a field under a returned borrow, lent before the match (the entry ends it)
  def Whole (x : &Out) : &Out := x
  def D8 (k : Nat) (c : Out) : List(Nat) := (let rr = Whole(&c); match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  -- 9. the same in tail position at a known `k` (no entry)
  def D9 (xs : List(Nat)) (ys : List(Nat)) (zs : List(Nat)) : Unit := (
    let k = Z; let c = MkOut(MkIn(xs, ys), zs); let rr = Whole(&c);
    match k { Z => (), S m => (let a = (c.0).0; ()) })
  -- 10. a statement whose side's dead arm drops a field
  def D10 (c : Out) : Prop := Id(Unit, (let d = c; let k = Z; match k { Z => (), S m => (let a = (d.0).0; ()) }; ()), (let d = c; ()))
  -- 11. a callee with such a join, called at the generic call (an untyped run at an unknown)
  def G11 (k : Nat) (c : Out) : List(Nat) := (match k { Z => (), S m => (let a = (c.0).0; ()) }; (c.0).1)
  def D11 (k : Nat) (c : Out) : List(Nat) := G11(k, c)
  def D11r (c : Out) : List(Nat) := G11(Z, c)
}
