import Ochr.Examples.V18

/-! # Rules v1.9 regressions: D41, erased terms are confined (checked)

An erased term may not assign, borrow or move a place that outlives it, except by
passing it to an erased call. The ledger row `confine` (Registry.lean) shows these,
and N1T, Q, EffArgErased and LieP elsewhere, flip without it. -/

open Ochr.Test

ochr V19 {
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x := match *x { Z => refl, S p => AddMZero(&p) }
  -- a proof may mutate its own locals ...
  def Local (x : &Nat) : Nat := let h : ⊤ = (let y = 0; y := 1; refl); *x
  -- ... and hand an outer place to another proof (AddMZero's own recursion does this) ...
  def Pass (x : &Nat) : Nat := let h = AddMZero(&*x); *x
  -- ... but not write, borrow or move one itself
  reject def Write (x : &Nat) : Nat := let h : ⊤ = (*x := 5; refl); *x
  reject def Borrow (x : &Nat) : Nat := let h : ⊤ = (AddM(&*x, 0); refl); *x
  reject def Move (x : &Nat) : Nat := let h : ⊤ = (let y = x; refl); 0
  -- a proof in tail position is not an erased occurrence as a whole: its steps run (here
  -- a data call on the borrow parameter, as in E4's TwiceMZero')
  def TailSteps (x : &Nat) : ⊤ := AddM(&*x, 0); refl
}

#eval IO.println (run "V19" V19).show

-- every verdict as expected, and exactly 8 assertions (a truncated file changes the count)
#guard (run "V19" V19).allAsExpected
#guard (run "V19" V19).count == 8
