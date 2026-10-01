import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! The merge's rule 4 (a move out of an Uninit place leaves the empty value) on ochr-core,
where statements read by copying: a move is observable to runtime code (the place can be read
afterwards) but never happens inside a statement, so a statement and the run of the same code
disagree. -/
set_option ochr.uninitTypes true in
set_option ochr.moveEmpty true in
ochr MoveEmptyProbe uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  -- rule 4: the moved-out place holds Empty, which runtime code may read
  def MoveThenRead (u : Uninit(Nat)) : Uninit(Nat) := (
    let y = u;
    u
  )
  def MT (n : Nat) (u : Uninit(Nat)) : Uninit(Nat) := (
    match n {
      Z => (
        let y = u;
        u
      ),
      S m => u,
    }
  )
  -- in a statement the read copies, the move does not happen, and this holds by `refl`
  def Claim (n : Nat) (u : Uninit(Nat)) : Eq(Uninit(Nat), MT(n, u), u) := (
    match n {
      Z => refl,
      S m => refl,
    }
  )
  -- the untagged match is justified by Claim, false at n = 0, where the run gives Empty
  def G (n : Nat) : Nat := (
    let r = MT(n, Full(0));
    let e = Claim(n, Full(0));
    let h : Init(Nat, r) = (rewrite ← e in refl);
    match r {
      Full(y) => y,
      Empty => match h {},
    }
  )
  def GRun : Nat := G(0)
  reject def GRunZero : Id(Nat, G(0), 0) := refl
  def MTRun : Id(Uninit(Nat), MoveThenRead(Full(0)), Empty[Nat]) := refl
}
#eval (run "MoveEmptyProbe" MoveEmptyProbe { uninitTypes := true, moveEmpty := true }).rows.map fun r => (r.name, r.verdict.ok, match r.verdict with | .accepted => "" | .rejected m _ => m)
#eval (run "MoveEmptyProbe" MoveEmptyProbe { uninitTypes := true, moveEmpty := true, trace := true }).showTrace "GRun"
