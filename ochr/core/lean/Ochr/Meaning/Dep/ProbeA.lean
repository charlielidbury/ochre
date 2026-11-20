-- Attack probes of the dependent-values lane, run with `lake env lean` against main 5a2106a9 (scratch
-- worktree). Not imported by any library root. Every declaration is `def`: an error is a rejection.
-- Verdicts are recorded in ../HANDOFF.md.
import Ochr.Examples.DependentFields
open Ochr.Test

-- every declaration is `def`: an error on a declaration means the checker rejected it
ochr PA uses DepFields {
  -- a dependent LEAF field: Nat at index Zero, Unit otherwise
  def NU (b : Word) : Type := match b { Zero => Nat, Succ(m) => Unit, }
  inductive DP := MkDP(b : Word, x : NU(b))
  def DP0 : DP := MkDP(Zero, 3)
  -- control: a wrong program
  def Ctl : Unit := (3 : Unit)
  -- index rewritten, leaf read, used at the new index's type (Unit): should be rejected
  def L1 : Unit := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let y = x; (y : Unit)), })
  -- the same used at its content's type (Nat)
  def L1Nat : Nat := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let y = x; y), })
  def L1NatRuns : Eq(Nat, L1Nat, 3) := refl
  -- generic
  def L2 (c0 : DP) : Unit := (let c = c0; match c { MkDP(b, x) => (b := Succ(Zero); let y = x; (y : Unit)), })
  def L2b (c0 : DP) : Unit := (let c = c0; match c { MkDP(b, x) => (b := Succ(Zero); let y = x; ()), })
  -- strong update of the leaf with the wrong type for the current index, then read
  def L3 : Nat := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (x := 5; let y = x; y), })
  def L3Runs : Eq(Nat, L3, 5) := refl
  -- write index then borrow the leaf: type of the borrow
  def L4 : Nat := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let r = &x; let y = clone(*r); y), })
  def L4u : Unit := (let c = MkDP(Zero, 3); match c { MkDP(b, x) => (b := Succ(Zero); let r = &x; *r := (); ()), })
  -- a leaf field written to Unit, index set to Zero: x holds () at declared Nat
  def L5 : Unit := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (b := Zero; let y = x; y), })
  def L5n : Nat := (let c = MkDP(Succ(Zero), ()); match c { MkDP(b, x) => (b := Zero; let y = x; (y : Nat)), })
  -- a Pi leaf
  def NF (b : Word) : Type := match b { Zero => Π(z : Nat). Nat, Succ(m) => Unit, }
  inductive DF := MkDF(b : Word, f : NF(b))
  def F1 : Nat := (let c = MkDF(Zero, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (b := Succ(Zero); let g = f; g(2)), })
  def F1Runs : Eq(Nat, F1, 3) := refl
  def F1u : Unit := (let c = MkDF(Zero, λ(z : Nat) : Nat => S(z)); match c { MkDF(b, f) => (b := Succ(Zero); let g = f; (g : Unit)), })
}
