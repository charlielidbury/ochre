import Ochr.Env

/-! Phase 1b probe: a synthetic 40-function mutual block in `M`, `partial` (the baseline). -/
namespace Ochr.TotalProbe.Partial
open Ochr

mutual
partial def f0 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f3 (n - 1) ys.tail else f1 (n - 1) ys
partial def f1 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f10 (n - 1) ys.tail else f2 (n - 1) ys
partial def f2 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f17 (n - 1) ys.tail else f3 (n - 1) ys
partial def f3 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f24 (n - 1) ys.tail else f4 (n - 1) ys
partial def f4 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f31 (n - 1) ys.tail else f5 (n - 1) ys
partial def f5 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f38 (n - 1) ys.tail else f6 (n - 1) ys
partial def f6 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f5 (n - 1) ys.tail else f7 (n - 1) ys
partial def f7 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f12 (n - 1) ys.tail else f8 (n - 1) ys
partial def f8 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f19 (n - 1) ys.tail else f9 (n - 1) ys
partial def f9 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f26 (n - 1) ys.tail else f10 (n - 1) ys
partial def f10 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f33 (n - 1) ys.tail else f11 (n - 1) ys
partial def f11 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f0 (n - 1) ys.tail else f12 (n - 1) ys
partial def f12 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f7 (n - 1) ys.tail else f13 (n - 1) ys
partial def f13 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f14 (n - 1) ys.tail else f14 (n - 1) ys
partial def f14 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f21 (n - 1) ys.tail else f15 (n - 1) ys
partial def f15 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f28 (n - 1) ys.tail else f16 (n - 1) ys
partial def f16 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f35 (n - 1) ys.tail else f17 (n - 1) ys
partial def f17 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f2 (n - 1) ys.tail else f18 (n - 1) ys
partial def f18 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f9 (n - 1) ys.tail else f19 (n - 1) ys
partial def f19 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f16 (n - 1) ys.tail else f20 (n - 1) ys
partial def f20 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f23 (n - 1) ys.tail else f21 (n - 1) ys
partial def f21 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f30 (n - 1) ys.tail else f22 (n - 1) ys
partial def f22 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f37 (n - 1) ys.tail else f23 (n - 1) ys
partial def f23 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f4 (n - 1) ys.tail else f24 (n - 1) ys
partial def f24 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f11 (n - 1) ys.tail else f25 (n - 1) ys
partial def f25 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f18 (n - 1) ys.tail else f26 (n - 1) ys
partial def f26 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f25 (n - 1) ys.tail else f27 (n - 1) ys
partial def f27 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f32 (n - 1) ys.tail else f28 (n - 1) ys
partial def f28 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f39 (n - 1) ys.tail else f29 (n - 1) ys
partial def f29 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f6 (n - 1) ys.tail else f30 (n - 1) ys
partial def f30 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f13 (n - 1) ys.tail else f31 (n - 1) ys
partial def f31 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f20 (n - 1) ys.tail else f32 (n - 1) ys
partial def f32 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f27 (n - 1) ys.tail else f33 (n - 1) ys
partial def f33 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f34 (n - 1) ys.tail else f34 (n - 1) ys
partial def f34 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f1 (n - 1) ys.tail else f35 (n - 1) ys
partial def f35 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f8 (n - 1) ys.tail else f36 (n - 1) ys
partial def f36 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f15 (n - 1) ys.tail else f37 (n - 1) ys
partial def f37 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f22 (n - 1) ys.tail else f38 (n - 1) ys
partial def f38 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f29 (n - 1) ys.tail else f39 (n - 1) ys
partial def f39 (n : Nat) (xs : List Nat) : M Nat := do
  tick
  if n == 0 then return xs.length
  let ys ← xs.mapM (fun x => pure (x + 1))
  if n % 5 == 0 then f36 (n - 1) ys.tail else f0 (n - 1) ys
end
end Ochr.TotalProbe.Partial
