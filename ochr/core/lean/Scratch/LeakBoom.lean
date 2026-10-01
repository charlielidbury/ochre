import Ochr.Examples.«00Std»
open Ochr.Test
/-! Make the use-site's EXPECTED type equal the leaked type `Slice(Sub(Z, k))`, so the S-arm's
`r` is accepted against it. At n=1, k=0 the leaked type is Slice(0) (empty) but r truly has
type Slice(1) (one cell). If the checker accepts, `WantEnd` treats a real cell as empty. -/
ochr LeakBoom uses Std {
  inductive SliceOf (R : Type) := MkSlice(c : R)
  inductive Cell (R : Type) := MkC(h : Nat, t : SliceOf(R))
  inductive CellsEnd := End
  def Sub (a : Nat) (b : Nat) : Nat by b := match b { Z => a, S b' => match a { Z => Z, S a' => Sub(a', b') } }
  def Cells (n : Nat) : Type by n := match n { Z => CellsEnd, S m => Cell(Cells(m)) }
  def Slice (n : Nat) : Type := SliceOf(Cells(n))
  -- a proof that any slice of length Sub(Z, k) is empty (true: Sub(Z,k) = 0)
  reject def IsEmpty (k : Nat) (s : Slice(Sub(Z, k))) : Id(Nat, match s { MkSlice(c) => match c { End => 0 } }, 0) := refl
  -- feed r (leaked type Slice(Sub(Z,k))) to IsEmpty in the S(arm)
  reject def Try (n : Nat) (k : Nat) (r : Slice(Sub(n, k))) : Nat by n := match n {
    Z => 0,
    S m => let h = IsEmpty(k, r); 1
  }
  reject def Boom : Nat := (let s = MkSlice(MkC(9, MkSlice(End))); Try(1, 0, s))
}
#eval IO.println (run "LeakBoom" LeakBoom).show
