import Ochr.Examples.More

/-! # Probes of v1 corners: types computed by programs, nested functions, snapshots,
pattern variables as places, effects in the arguments of calls that are not run,
and how stuck blocks pass borrow variables. -/

open Ochr.Test

ochr Probes {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  -- a type computed by a program, and dependent pattern matching through it: the
  -- split refines x's stored type T(σ) to T(0) ≡ Nat
  def T (b : Nat) : Type := match b { Z => Nat | S _ => Unit }
  def UseT0 (x : T(0)) : Nat := x
  def UseT (b : Nat) (x : T(b)) : T(b) := x
  def DepMatch (b : Nat) (x : T(b)) : Nat := match b { Z => x | S _ => 0 }
  reject def DepMatchWrong (b : Nat) (x : T(b)) : Nat := match b { Z => 0 | S _ => x }

  -- a local recursive fix, checked by [Def] at its own generic call
  def Outer (x : &Nat) : Unit := (fix go (y : &Nat) : Unit by y := match *y { Z => () | S p => go(&p) })(x)
  reject def OuterBad (x : Nat) : Eq Nat 0 1 := (fix go (y : Nat) : Eq Nat 0 1 by y := go(y))(x)

  -- closures capture values when formed (P2, D13)
  def Cap (n : Nat) : Id Nat ((λ(u : Unit) : Nat => S n)(())) (S n) := refl
  def CapMut (n : Nat) : Id Nat (let m = n; let f = (λ(u : Unit) : Nat => m); m := S m; f(())) n := refl

  -- a pattern variable is the sub-place p.1 (RULES §1): after a write it names the
  -- new tail, and after a write of Z it names nothing
  def AliasRead (x : Nat) : Id Nat (let m = x; match m { Z => 0 | S y => m := S (S 0); y }) (match x { Z => 0 | S _ => 1 }) :=
    match x { Z => refl | S _ => refl }
  reject def AliasDangling (x : Nat) : Nat := match x { Z => 0 | S y => x := 0; y }

  -- v1.3 P2: a proof call's argument evaluation runs on the private copy too, so
  -- W5's write inside the proof's argument leaves no trace (under v1 it persisted)
  def Lemma (u : Unit) : ⊤ := refl
  def W5 (x : &Nat) : Unit := *x := 5
  reject def EffArg (x : &Nat) : Id Unit (Lemma(W5(&*x)); ()) (*x := 5) := refl
  def EffArgErased (x : &Nat) : Id Unit (Lemma(W5(&*x)); ()) () := refl

  -- stuck blocks: a written owned variable is passed as &c, and a split later
  -- re-runs the block to each arm's value
  def WriteInBlock (b : Nat) : Id Nat (let c = b; (match c { Z => c := 1 | S _ => () }); c) (match b { Z => 1 | S m => S m }) :=
    match b { Z => refl | S _ => refl }

  -- stuck blocks: a borrow variable moved in some arm is moved into the block, so it
  -- is dead afterwards (C5); reborrowing it instead would let r and x1 alias in arm Z
  reject def AliasAfterBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit :=
    let r = match b { Z => x1 | S _ => x2 }; AddM(x1, 1); AddM(r, 2)
  -- the same with the use after r is gone: in arm Z, x1 was moved into r, so x1 is
  -- dead; reborrowing it into the block would accept this use after move
  reject def MovedByBlock (b : Nat) (x1 : &Nat) (x2 : &Nat) : Unit :=
    let r = match b { Z => x1 | S _ => x2 }; AddM(r, 1); AddM(x1, 2)
  -- one used but not moved in any arm is reborrowed, so it stays usable
  def ReborrowInBlock (b : Nat) (x : &Nat) : Unit :=
    (match b { Z => AddM(&*x, 1) | S _ => () }); AddM(x, 2)
}

#eval IO.println (run "Probes" Probes).show

-- every verdict as expected, and exactly 20 assertions (a truncated file changes the count)
#guard (run "Probes" Probes).allAsExpected
#guard (run "Probes" Probes).count == 20
