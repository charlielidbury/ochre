import Ochr.Examples.«00Std»
open Ochr.Test
/-! Sweep the S-arm use-sites of r that could read the leaked absType(σ_r). r : Slice(Sub(n,k))
so the Z-arm refinement (n:=Z) permanently rewrites absTy[σ_r], mirroring the Repro. Any
`def U*` that is ACCEPTED is a candidate false acceptance (its use of r is checked against the
leaked Slice(0)=SliceOf(CellsEnd) rather than the true Slice(Sub(S m, k))). -/
ochr LeakSweep uses Std {
  inductive SliceOf (R : Type) := MkSlice(c : R)
  inductive Cell (R : Type) := MkC(h : Nat, t : SliceOf(R))
  inductive CellsEnd := End
  inductive Boxx (A : Type) := MkB(v : A)
  def Sub (a : Nat) (b : Nat) : Nat by b := match b { Z => a, S b' => match a { Z => Z, S a' => Sub(a', b') } }
  def Cells (n : Nat) : Type by n := match n { Z => CellsEnd, S m => Cell(Cells(m)) }
  def Slice (n : Nat) : Type := SliceOf(Cells(n))
  def WantEnd (b : Boxx(Slice(0))) : Nat := 3
  def WantEndF (s : Slice(0)) : Nat := 3
  -- Each `reject def` below is rejected TODAY; a fix that restores absTy across arms would
  -- flip the ones whose use of r is against the leaked type. (a) pass r to a function wanting Slice(0), directly
  reject def Ua (n : Nat) (k : Nat) (r : Slice(Sub(n, k))) : Nat by n := match n { Z => WantEndF(r), S m => WantEndF(r) }
  -- (b) wrap r in a constructor and pass to a function wanting Boxx(Slice(0))
  reject def Ub (n : Nat) (k : Nat) (r : Slice(Sub(n, k))) : Nat by n := match n { Z => WantEnd(MkB(r)), S m => WantEnd(MkB(r)) }
  -- (c) infer the parameter of a box from r, then read the box's content type
  reject def Uc (n : Nat) (k : Nat) (r : Slice(Sub(n, k))) : Nat by n := match n { Z => 0, S m => match MkB(r) { MkB(s) => match s { MkSlice(c) => match c { End => 5 } } } }
  -- (d) split r's cell as if End
  reject def Ud (n : Nat) (k : Nat) (r : Slice(Sub(n, k))) : Nat by n := match n { Z => 0, S m => match r { MkSlice(c) => match c { End => 5 } } }
}
#eval IO.println (run "LeakSweep" LeakSweep).show
