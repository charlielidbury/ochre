import Ochr.Examples.E6

/-! # Regression tests: the round-1 unsoundness attacks must all be rejected

`Eq Nat 0 1` plays the role of `⊥`. Each attack is written as close to its source
note as the v1 syntax allows; where the attack cannot even be stated in v1 (because a
v1 rule forbids a step of it), the comment says which rule. -/

open Ochr.Test

ochr Attacks {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  -- deriver-e346 §E3.6 `Bad`: under [Join] reading J1 the stored type of h was taken
  -- from an arm. v1 closes the non-tail match off and continues from the unrefined
  -- state, so h keeps its pre-split type Eq Nat σ 0 (D15).
  reject def Bad (b : Nat) (h : Id Nat b 0) : Eq Nat 0 1 :=
    (match b { Z => () | S _ => () }); h

  -- deriver-e346 §E6.3 / meta-model C4 `Oops2`: a Π-typed hypothesis re-read after a
  -- mutation. v1: the Π-type captured x's value when it was formed (D13).
  reject def Oops2 (x : Nat) (h : Π(_ : Unit). Id Nat x 0) : Eq Nat 0 1 :=
    x := S x; h(())

  -- deriver-e346 §E6.3 `Loop` / `Bot'` (meta-model C3): write before the match, then
  -- recurse on the entry value. v1: [Rec] measures the entry value (D17).
  reject def Loop (x : &Nat) (y : Nat) : Eq Nat 0 1 by x :=
    match y {
      Z => *x := S *x; match *x { Z => refl | S p => let q = p; Loop(&p, q) }
    | S q => *x := S *x; match *x { Z => refl | S p => Loop(&p, q) } }
  reject def Bot' (n : Nat) : Eq Nat 0 1 := let a = n; Loop(&a, n)

  -- breaker-close A3(a): write before the match, owned version
  reject def Loop2 (x : Nat) : Eq Nat 0 1 by x :=
    match x { Z => x := S Z; match x { Z => refl | S y => Loop2(y) }
            | S p => x := S (S p); match x { Z => refl | S y => Loop2(y) } }

  -- breaker-close A3(b): write after the match through the alias pattern variable
  reject def Spin (x : Nat) : Eq Nat 0 1 by x :=
    match x { Z => x := S Z; match x { Z => refl | S y => Spin(y) }
            | S y => x := S x; Spin(y) }

  -- meta-model C1 / breaker-close A2: an effectful and an effect-free inhabitant of
  -- the proposition Π(x : &Nat). ⊤. v1: calls at a proposition are not run (P5, D14),
  -- so P2's write is invisible to every observation, and identifying P1 with P2 is sound.
  def P1 (x : &Nat) : ⊤ := refl
  def P2 (x : &Nat) : ⊤ := *x := 7; refl
  def F (h : Π(x : &Nat). ⊤) : Prop := Id Nat (let a = 0; h(&a); a) 0
  def FP2 : Id Nat (let a = 0; P2(&a); a) 0 := refl
  reject def Boom : Eq Nat 0 1 :=
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq (Π(x : &Nat). ⊤) P1 P2), refl)
  def BoomIsTrue : ⊤ :=
    J(Π(x : &Nat). ⊤, P1, P2, λ(g : Π(x : &Nat). ⊤) : Prop => F(g), (refl : Eq (Π(x : &Nat). ⊤) P1 P2), refl)
  -- breaker-close A2, the seal-conversion variant: under P2 both runs give c = 0, so T
  -- is true and its closed instance is not a proof of ⊥
  def p1 (x : &Nat) : Eq Nat 0 0 := refl
  def p2 (x : &Nat) : Eq Nat 0 0 := *x := S Z; refl
  def UseP (h : Π(x : &Nat). Eq Nat 0 0) (x : &Nat) (n : Nat) : Unit := match n { Z => h(x); () | S _ => h(x); () }
  def TA2 (n : Nat) : Id Nat (let c = 0; UseP(p1, &c, n); c) (let c = 0; UseP(p2, &c, n); c) := refl
  reject def TA2Z : Eq Nat 0 1 := TA2(0)

  -- breaker-close-v1 N1: a proposition-typed block that writes. Under v1.1 sealing then
  -- refining gave 0 and running directly gave 1, so N1Closed : Id Nat 1 0. Under v1.3's
  -- P2 the inline arm (a := S Z; refl) is a proof, runs on a private copy, and both give 0.
  def N1T (n : Nat) : Id Nat (let a = 0; let h = match n { Z => (a := S Z; refl) | S _ => refl }; a) 0 := refl
  reject def N1Closed : Id Nat 1 0 := N1T(0)

  -- meta-model-v1 R1 (= breaker-close-v1 N1, deriver-e346-v1 N12): a Prop-typed block
  -- that writes. Under v1.3's P2 the writes of a proof are erased, so Q is true and
  -- Q(0, 0) : ⊤; the closed proof of false below is rejected. Under v1's call-keyed P5,
  -- Q(0, 0) : Eq Nat 1 0 and QBoom is accepted (ledger row P2).
  def Q (b : Nat) (a : Nat) : Id ⊤ (match b { Z => (a := S Z; refl) | S _ => (a := S Z; refl) }) refl := refl
  reject def QBoom : (Π(P : Prop). P) :=
    J(Nat, S Z, Z, λ(n : Nat) : Prop => match n { Z => (Π(P : Prop). P) | S _ => ⊤ }, Q(0, 0), refl)

  reject def Boom' : Eq Nat 0 1 :=
    (λ(k : Π(h : Π(x : &Nat). ⊤). Nat) : Eq Nat (k(P1)) (k(P2)) => refl)(λ(h : Π(x : &Nat). ⊤) : Nat => let a = 0; h(&a); a)

  -- meta-model C2: a returned borrow from a two-borrow call leaves its hole in both
  -- owners. In v1 the attack's curried G cannot be stated: its result type
  -- Π(e : Id Unit (*z := 0) (*z := 1)). ⊥ is a closure that captures the borrow z,
  -- and closures capture no borrows (RULES §1). The owners-are-sets rule (D18) is
  -- tested directly in Ochr/Examples/Units.lean.
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x | S _ => y }
  reject def G (z : &Nat) : (Π(e : Id Unit (*z := 0) (*z := 1)). Eq Nat 0 1) :=
    λ(e : Id Unit (*z := 0) (*z := 1)) : Eq Nat 0 1 => e
  reject def BadC2 (n : Nat) (a : Nat) (b : Nat) : Id Nat n 0 :=
    let r = Pick(n, &a, &b); let h = G(r); match n { Z => refl | S m => h(refl) }

  -- breaker-close A1: [Close] must not copy a live loan into a sealed program. v1:
  -- moving b ends the reborrow r first ([Access] looks inside the content, D19).
  def G1 (x : &Nat) (n : Nat) : Unit := match n { Z => () | S _ => *x := 0 }
  reject def BadA1 (n : Nat) : Nat :=
    let a = S Z; (let b = &a; let r = &(*b).1; G1(b, n); *r := S Z); a

  -- lean-checker L1 (new): the function occurs in its own body as a value, not as the
  -- head of a call, so [Rec] never sees a recursive call. Without fix L1 both
  -- definitions below are accepted, and Knot(0) is a closed proof of Eq Nat 0 1.
  def Apply (f : Π(x : Nat). Eq Nat 0 1) (x : Nat) : Eq Nat 0 1 := f(x)
  reject def Knot (x : Nat) : Eq Nat 0 1 by x := Apply(Knot, x)
  reject def KnotBoom : Eq Nat 0 1 := Knot(0)

  -- lean-checker L3: the same through a nested closure. v1's [Rec] covers every
  -- recursive call in the body of fix f, including those inside a nested λ, and the
  -- λ is checked at its own generic call, so y is fresh: not a subterm of x's entry
  -- value. (An earlier version of this checker reset the [Rec] context when checking
  -- the nested λ and accepted both.)
  reject def KnotL (x : Nat) : Eq Nat 0 1 by x := let g = (λ(y : Nat) : Eq Nat 0 1 => KnotL(y)); g(x)
  reject def KnotLBoom : Eq Nat 0 1 := KnotL(0)
  -- a structural call through a closure is fine: the closure captures the entry
  -- value's predecessor, and the call is checked against the outer entry value
  def Add (x : Nat) (y : Nat) : Nat := AddM(&x, y); x
  def AddZeroC (x : Nat) : Id Nat (Add(x, 0)) x by x :=
    match x { Z => refl | S p => let q = p; cong S ((λ(u : Unit) : Id Nat (Add(q, 0)) q => AddZeroC(q))(())) }
}

#eval IO.println (run "Attacks" Attacks).show

-- every verdict as expected, and exactly 35 assertions (a truncated file changes the count)
#guard (run "Attacks" Attacks).allAsExpected
#guard (run "Attacks" Attacks).count == 35
