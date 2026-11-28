import Ochr.Meaning.Conv.Probe

/-!
# Attacks on conversion, on the real checker (conv1, 2026-11-28)

Each block's verdicts are asserted by the build (`def` accepted, `reject def` rejected), and the
reasons of the rejections that matter by `rejectedWith`. A `reject def` here is either a FALSE
statement that conversion must not accept (an acceptance would be a soundness finding) or a TRUE
statement that conversion, the least relation, does not reach (an incompleteness, marked so).

**Function comparisons** ([Conv-fun], `convFn`/`convFnRun`; hypothesis (H1)):
- bodies that write through a borrow parameter and return it, or a reborrow of it (`R12`, `R34`:
  the same function, accepted); a write to a second borrow parameter that the result does not show
  (`T12`, false: rejected, the cells differ);
- bodies that end stuck: two copies of one stuck body (`P12`, `S12`: true, rejected, the least
  relation: a function inspecting its argument is convertible only with itself); a wrapper that
  writes before the stuck call (`W12`, false: rejected);
- bodies that return a closure capturing the argument against one that does not (`C12`, false);
- bodies that differ only in an erased statement's writes (`E12`, true: accepted; the statement runs
  on its copy); a type-returning body that writes (`Ty12`: the write is observed, rejected; its calls
  are erased, so the two never differ at a call: an incompleteness, fail-safe).

**Equality at other types** (`mkEqM`; (H5) to (H8)):
- `Eq` at a borrow type is not formed (`&` only at the top of a declared type, D48);
- two proofs of a proposition with a data field are equal (`PI`), also inside erased matches on both
  (`PI2`, `PI3`): the scrutinee stays `⋆` there (D138: the fields are locals), so no constructor value
  of a `Prop` declaration reaches `Eq` (the side condition `NoProp` of `Strict.hwt_of_fit`);
- an equation at a type that is a type function of an unknown, refined later: stuck while the
  values are unknowns declared at the unrefined type (`K1`, true, rejected: η at `Unit` reads the
  declared type, D80); false at an instance where the type computes to `Nat` (`K3` rejected, `K4`
  uses it as `False`).
-/

open Ochr Ochr.Test Ochr.Meaning.Conv

ochr ConvAtkFn uses Nats, Fixtures {
  def R1 (x : &Nat) : &Nat := (*x := Z; &*x)
  def R2 (x : &Nat) : &Nat := (*x := Z; x)
  def R12 : Eq(Π(x : &Nat). &Nat, R1, R2) := refl
  def R3 (x : &Nat) : &Nat := (let y = &*x; *y := S(Z); x)
  def R4 (x : &Nat) : &Nat := (*x := S(Z); x)
  def R34 : Eq(Π(x : &Nat). &Nat, R3, R4) := refl
  def T1 (x : &Nat) (y : &Nat) : &Nat := (*y := Z; x)
  def T2 (x : &Nat) (y : &Nat) : &Nat := x
  reject def T12 : Eq(Π(x : &Nat) (y : &Nat). &Nat, T1, T2) := refl
  def P1 (x : &Nat) : &Nat := match *x { Z => x, S p => &p }
  def P2 (x : &Nat) : &Nat := match *x { Z => x, S p => &p }
  reject def P12 : Eq(Π(x : &Nat). &Nat, P1, P2) := refl
  def S1 (x : &Nat) (n : Nat) : Unit := (*x := Z; match n { Z => (), S _ => () })
  def S2 (x : &Nat) (n : Nat) : Unit := (*x := Z; match n { Z => (), S _ => () })
  reject def S12 : Eq(Π(x : &Nat) (n : Nat). Unit, S1, S2) := refl
  def W1 (x : &Nat) (n : Nat) : Unit := S1(x, n)
  def W2 (x : &Nat) (n : Nat) : Unit := (*x := S(Z); S1(x, n))
  reject def W12 : Eq(Π(x : &Nat) (n : Nat). Unit, W1, W2) := refl
  def C1 (n : Nat) : (Π(m : Nat). Nat) := λ(m : Nat) : Nat => clone(n)
  def C2 (n : Nat) : (Π(m : Nat). Nat) := λ(m : Nat) : Nat => m
  reject def C12 : Eq(Π(n : Nat). (Π(m : Nat). Nat), C1, C2) := refl
  def E1 (x : &Nat) : Unit := (let h : Id(Unit, *x := Z, *x := Z) = refl; ())
  def E2 (x : &Nat) : Unit := ()
  def E12 : Eq(Π(x : &Nat). Unit, E1, E2) := refl
  def Ty1 (x : &Nat) : Type := (*x := Z; Nat)
  def Ty2 (x : &Nat) : Type := Nat
  reject def Ty12 : Eq(Π(x : &Nat). Type, Ty1, Ty2) := refl
}

ochr ConvAtkEq uses Nats, Fixtures {
  inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
  reject def EB (x : &Nat) (y : &Nat) : Prop := Eq(&Nat, x, y)
  def PI (h : Ex) (k : Ex) : Eq(Ex, h, k) := refl
  def PI2 (h : Ex) (k : Ex) : True :=
    match h { Wit(w1, e1) => match k { Wit(w2, e2) => (let q : Eq(Ex, h, k) = PI(h, k); refl) } }
  def PI3 (h : Ex) (k : Ex) : True :=
    match h { Wit(w1, e1) => match k { Wit(w2, e2) => (let q : Eq(Ex, h, k) = refl; refl) } }
  def TF (n : Nat) : Type := match n { Z => Unit, S _ => Nat }
  reject def K1 (n : Nat) (x : TF(n)) (y : TF(n)) (h : Eq(TF(n), x, y)) : Eq(TF(n), y, x) :=
    match n { Z => refl, S _ => match h {} }
  def K2 (n : Nat) (x : TF(n)) (y : TF(n)) : Prop := Eq(TF(n), x, y)
  reject def K3 : K2(S(Z), Z, S(Z)) := refl
  def K4 (h : K2(S(Z), Z, S(Z))) : False := h
}

#guard (run "ConvAtkFn" ConvAtkFn).rejectedWith [
  ("T12", "the body of T12 has type ⊤, but the goal is Eq(Π(x : &Nat) (y : &Nat). &Nat, T1, T2)"),
  ("P12", "the body of P12 has type ⊤, but the goal is Eq(Π(x : &Nat). &Nat, P1, P2)"),
  ("S12", "the body of S12 has type ⊤, but the goal is Eq(Π(x : &Nat) (n : Nat). Unit, S1, S2)"),
  ("W12", "the body of W12 has type ⊤, but the goal is Eq(Π(x : &Nat) (n : Nat). Unit, W1, W2)"),
  ("C12", "the body of C12 has type ⊤, but the goal is Eq(Π(n : Nat). Π(m : Nat). Nat, C1, C2)"),
  ("Ty12", "the body of Ty12 has type ⊤, but the goal is Eq(Π(x : &Nat). Type, Ty1, Ty2)")]

#guard (run "ConvAtkEq" ConvAtkEq).rejectedWith [
  ("K1", "the body of K1 has type ⊤, but the goal is Eq(Unit, σ2, σ1)"),
  ("K3", "the body of K3 has type ⊤, but the goal is False")]
