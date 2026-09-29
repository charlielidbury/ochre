import Ochr.Examples.V19

/-! # Rules v1.9: D44 (reviewer-2), and captured values that keep their types (program `D44`)

reviewer-2: a function type returning a borrow with no borrow parameter closes off into a
borrow whose hole is in no owner, so an `Id` about it observes nothing and computes to
⊤; `Q` then refutes `Π(n : Nat). &Nat`, which an opaque `leak` (Rust's `Box::leak`)
inhabits. D44 makes such function types ill-formed. The second group checks closures and
Π-types that capture neutral data or proofs (reviewer-2's "severe hidden restriction"). -/

open Ochr.Test

ochr D44 {
  inductive Empty := E(e : Empty)
  def M (n : Nat) : Type := match n { Z => Unit | S _ => Empty }
  def P (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : Empty := J(Nat, 0, 1, M, e, ())
  reject def Q (g : Π(n : Nat). &Nat) : Empty := P(g(5), refl)
  reject def Boom (leak : Π(n : Nat). &Nat) : Empty := Q(leak)
  reject def LeakT : Type := Π(n : Nat). &Nat
  -- the same with v2.0's False: the observation's Eq Nat 0 1 is False by D47
  def PF (x : &Nat) (e : Id Unit (*x := 0) (*x := 1)) : False := e
  reject def QF (g : Π(n : Nat). &Nat) : False := PF(g(5), refl)
  -- a returned borrow derives from a borrow argument: fine
  def Keep (x : &Nat) (n : Nat) : &Nat := x
  def KeepT : Type := Π(x : &Nat) (n : Nat). &Nat

  -- captured neutral data (a sealed program) and captured proofs have types
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
  def CapS (x : &Nat) : Nat := AddM(&*x, 1); let n = *x; let f = (λ(y : Nat) : Nat => n); f(0)
  def CapSId (x : &Nat) : Nat := AddM(&*x, 1); let n = *x; let f = (λ(y : Nat) : Id Nat n n => refl); 0
  def CapPi (x : &Nat) : Prop := AddM(&*x, 1); let n = *x; Π(y : Nat). Id Nat n y
  def CapP (h : Eq Nat Z Z) : Nat := let f = (λ(x : Nat) : Eq Nat Z Z => h); 0
  def CapP2 (h : Eq Nat Z Z) : Eq Nat Z Z := let f = (λ(x : Nat) : Eq Nat Z Z => h); f(0)
}

#eval IO.println (run "D44" D44).show

-- every verdict as expected, and exactly 16 assertions (a truncated file changes the count)
#guard (run "D44" D44).allAsExpected
#guard (run "D44" D44).count == 16
