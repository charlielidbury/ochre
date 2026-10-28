import Ochr.Env

/-! Phase 1b probe: the same block with an explicit structurally decreasing `fuel`. -/
namespace Ochr.TotalProbe.Structural
open Ochr

mutual
def f0 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f3 fuel' (n - 1) ys.tail else f1 fuel' (n - 1) ys
termination_by structural fuel
def f1 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f10 fuel' (n - 1) ys.tail else f2 fuel' (n - 1) ys
termination_by structural fuel
def f2 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f17 fuel' (n - 1) ys.tail else f3 fuel' (n - 1) ys
termination_by structural fuel
def f3 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f24 fuel' (n - 1) ys.tail else f4 fuel' (n - 1) ys
termination_by structural fuel
def f4 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f31 fuel' (n - 1) ys.tail else f5 fuel' (n - 1) ys
termination_by structural fuel
def f5 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f38 fuel' (n - 1) ys.tail else f6 fuel' (n - 1) ys
termination_by structural fuel
def f6 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f5 fuel' (n - 1) ys.tail else f7 fuel' (n - 1) ys
termination_by structural fuel
def f7 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f12 fuel' (n - 1) ys.tail else f8 fuel' (n - 1) ys
termination_by structural fuel
def f8 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f19 fuel' (n - 1) ys.tail else f9 fuel' (n - 1) ys
termination_by structural fuel
def f9 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f26 fuel' (n - 1) ys.tail else f10 fuel' (n - 1) ys
termination_by structural fuel
def f10 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f33 fuel' (n - 1) ys.tail else f11 fuel' (n - 1) ys
termination_by structural fuel
def f11 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f0 fuel' (n - 1) ys.tail else f12 fuel' (n - 1) ys
termination_by structural fuel
def f12 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f7 fuel' (n - 1) ys.tail else f13 fuel' (n - 1) ys
termination_by structural fuel
def f13 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f14 fuel' (n - 1) ys.tail else f14 fuel' (n - 1) ys
termination_by structural fuel
def f14 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f21 fuel' (n - 1) ys.tail else f15 fuel' (n - 1) ys
termination_by structural fuel
def f15 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f28 fuel' (n - 1) ys.tail else f16 fuel' (n - 1) ys
termination_by structural fuel
def f16 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f35 fuel' (n - 1) ys.tail else f17 fuel' (n - 1) ys
termination_by structural fuel
def f17 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f2 fuel' (n - 1) ys.tail else f18 fuel' (n - 1) ys
termination_by structural fuel
def f18 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f9 fuel' (n - 1) ys.tail else f19 fuel' (n - 1) ys
termination_by structural fuel
def f19 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f16 fuel' (n - 1) ys.tail else f20 fuel' (n - 1) ys
termination_by structural fuel
def f20 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f23 fuel' (n - 1) ys.tail else f21 fuel' (n - 1) ys
termination_by structural fuel
def f21 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f30 fuel' (n - 1) ys.tail else f22 fuel' (n - 1) ys
termination_by structural fuel
def f22 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f37 fuel' (n - 1) ys.tail else f23 fuel' (n - 1) ys
termination_by structural fuel
def f23 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f4 fuel' (n - 1) ys.tail else f24 fuel' (n - 1) ys
termination_by structural fuel
def f24 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f11 fuel' (n - 1) ys.tail else f25 fuel' (n - 1) ys
termination_by structural fuel
def f25 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f18 fuel' (n - 1) ys.tail else f26 fuel' (n - 1) ys
termination_by structural fuel
def f26 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f25 fuel' (n - 1) ys.tail else f27 fuel' (n - 1) ys
termination_by structural fuel
def f27 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f32 fuel' (n - 1) ys.tail else f28 fuel' (n - 1) ys
termination_by structural fuel
def f28 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f39 fuel' (n - 1) ys.tail else f29 fuel' (n - 1) ys
termination_by structural fuel
def f29 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f6 fuel' (n - 1) ys.tail else f30 fuel' (n - 1) ys
termination_by structural fuel
def f30 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f13 fuel' (n - 1) ys.tail else f31 fuel' (n - 1) ys
termination_by structural fuel
def f31 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f20 fuel' (n - 1) ys.tail else f32 fuel' (n - 1) ys
termination_by structural fuel
def f32 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f27 fuel' (n - 1) ys.tail else f33 fuel' (n - 1) ys
termination_by structural fuel
def f33 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f34 fuel' (n - 1) ys.tail else f34 fuel' (n - 1) ys
termination_by structural fuel
def f34 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f1 fuel' (n - 1) ys.tail else f35 fuel' (n - 1) ys
termination_by structural fuel
def f35 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f8 fuel' (n - 1) ys.tail else f36 fuel' (n - 1) ys
termination_by structural fuel
def f36 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f15 fuel' (n - 1) ys.tail else f37 fuel' (n - 1) ys
termination_by structural fuel
def f37 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f22 fuel' (n - 1) ys.tail else f38 fuel' (n - 1) ys
termination_by structural fuel
def f38 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f29 fuel' (n - 1) ys.tail else f39 fuel' (n - 1) ys
termination_by structural fuel
def f39 (fuel : Nat) (n : Nat) (xs : List Nat) : M Nat := do
  let fuel' + 1 := fuel | err "out of fuel"
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f36 fuel' (n - 1) ys.tail else f0 fuel' (n - 1) ys
termination_by structural fuel
end
end Ochr.TotalProbe.Structural
