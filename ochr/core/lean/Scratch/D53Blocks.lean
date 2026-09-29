import Ochr.Test
open Ochr Ochr.Test
/-! D53 acceptance: a stuck (closed-off) match hides its arms' moves from the rest of the
function, so the checker accepts functions that read moved data when run. Each `F` is
accepted; each `…Run` runs it on a ground input and is rejected (the `FAIL` lines are the finding). Found by the execution
oracle (fuzzer, ochr-core-lean 55977f8e). -/
ochr D53Blocks {
  -- M1: the arm moves a field its pattern exposed (q0.fst); `newHoles` compares against the
  -- unrefined abstract q0, which has no fields, so the move is not seen
  def A1 (q0 : Nat × Nat) : Nat × Nat := let a = match q0 { Mk(p, _) => p }; q0
  def A1Run : Nat × Nat := A1((0, 0))
  def A2 (n0 : Nat) : Nat := let a = match n0 { Z => 0, S p => p }; n0
  def A2Run : Nat := A2(1)
  -- M2: the arm moves a whole captured place that is not a variable (*x0); the block
  -- captures it as an in-place copy, so the borrow ends apparently whole
  def B1 (x0 : &Nat) (n1 : Nat) : Nat := let a = match n1 { Z => 0, S _ => *x0 }; a
  def B1Run : Nat := let m = 0; B1(&m, 1)
  def B2 (q0 : Nat × Nat) (x1 : &Nat) : Nat := S (match q0 { Mk(_, _) => *x1 })
  def B2Run : Nat := let m = 0; B2((0, 0), &m)
  def B3 (x0 : &Nat) (x1 : &Nat) : &Nat := match *x1 { Z => (), S _ => *x1 := *x0 }; x0
  def B3Run : Nat := let m = 0; let k = 1; let r = B3(&m, &k); *r
  -- M2b: one arm moves the borrow itself in (a whole read of x0), another moves out
  -- through it; the block owns the borrow, and nothing checks its content when it ends
  def B4 (x0 : &Nat) : Nat := S (match *x0 { Z => x0; 0, S _ => *x0 })
  def B4Run : Nat := let m = 1; B4(&m)
  -- M3: erased code in a run reads or writes a place moved at runtime. The definition is
  -- checked by the typed path, where it is erased; a call runs the body untyped:
  -- (i) the untyped J evaluates its endpoints under `onCopy` at runtime depth, not
  -- `confinedCopy`, so a moved endpoint is a runtime read
  def J1 (n : Nat) (h : Eq Nat n 1) : Nat := let m = n; J(Nat, n, 1, λ (z : Nat) : Type => Nat, h, m)
  def J1Run : Nat := J1(1, refl)
  -- (ii) an `Id` side writing a moved place fails to type the place's owner
  def I1 (n1 : Nat) : Nat := let m = n1; let a0 = Id Unit () (n1 := 0); 0
  def I1Run : Nat := I1(0)
  -- control: the same moves outside a stuck block are rejected at the definition
  reject def C1 (q0 : Nat × Nat) : Nat × Nat := match q0 { Mk(p, _) => let a = p; q0 }
  reject def C2 (x0 : &Nat) : Nat := *x0
}
#eval IO.println (run "D53Blocks" D53Blocks).show
