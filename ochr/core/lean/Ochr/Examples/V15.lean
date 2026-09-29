import Ochr.Examples.Probes

/-! # Rules v1.5 regressions: breaker-fresh F1–F5 (notes/breaker-fresh.md)

Each attack is rejected under v1.5; the counterfactual ledger (Registry.lean) shows the
v1.5 switch whose removal lets it through. -/

open Ochr.Test

ochr V15 {
  -- F1 (D28): erasure decided on a normal form. W's type U(n) computes to the universe
  -- Prop at n = Z but is a stuck ⌈U(σ)⌉ at the generic n, so under value-based erasure W
  -- ran for real generically and was erased at Z: Lie(Z) : Eq Nat 0 1. Under D28 W
  -- returns data (its declared codomain U(n) is neither a sort nor of sort Prop), so it
  -- runs at every instance, and MainW(0) really is 1, as compiled code computes.
  def U (n : Nat) : Type := match n { Z => Prop, S _ => Prop }
  def V (n : Nat) : U(n) := match n { Z => ⊤, S _ => ⊤ }
  def W (x : &Nat) (n : Nat) : U(n) := *x := S Z; V(n)
  def Lie (n : Nat) : Id Nat (let c = Z; W(&c, n); c) (S Z) := refl
  reject def Boom : Eq Nat Z (S Z) := Lie(Z)
  def MainW (n : Nat) : Nat := let c = Z; W(&c, n); c
  def MainW0 : Id Nat (MainW(0)) 1 := refl

  -- F2 (D29): a hole inside a sealed program at the head of a matched place. Matching
  -- ends it, so t is dead in arm Z, as in the concrete run.
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
  reject def Bad (x : &Nat) : Unit :=
    let t = TailM(&*x); match *x { Z => (*t := S Z; let h : Id Nat (*x) Z = refl; ()), S _ => () }
  reject def Main (n : Nat) : Nat := let c = n; Bad(&c); c
  reject def Main0 : Nat := Main(0)

  -- F3 (D30): closures compared by result only identified λx.() with λx.(*x := 1)
  def P (h : Π(x : &Nat). Unit) : Prop := Id Nat (let c = Z; h(&c); c) Z
  reject def Boom3 : Eq Nat (S Z) Z :=
    J(Π(x : &Nat). Unit, λ(x : &Nat) : Unit => (), λ(x : &Nat) : Unit => *x := S Z, P, refl, refl)
  -- ... and comparing by the observation of the generic call is complete where syntax is not
  def Conv : Eq (Π(x : &Nat). Unit) (λ(x : &Nat) : Unit => ()) (λ(x : &Nat) : Unit => let y = 0; ()) := refl
  def ConvW : Eq (Π(x : &Nat). Unit) (λ(x : &Nat) : Unit => *x := S *x) (λ(x : &Nat) : Unit => let y = S *x; *x := y) := refl

  -- F4 (D31): without `by`, f is not in scope in its body
  reject def Loop (x : Nat) : Eq Nat Z (S Z) := Loop(x)
  reject def Boom4 : Eq Nat Z (S Z) := Loop(Z)

  -- F5 (D32): a write through a pattern variable is a write to the scrutinee's place
  reject def Clear (x : &Nat) : Id Unit (match *x { Z => (), S p => p := Z }) () := refl
  reject def Boom5 : Eq Nat (S Z) (S (S Z)) := let c = S (S Z); Clear(&c)
}

#eval IO.println (run "V15" V15).show

-- every verdict as expected, and exactly 19 assertions (a truncated file changes the count)
#guard (run "V15" V15).allAsExpected
#guard (run "V15" V15).count == 19
