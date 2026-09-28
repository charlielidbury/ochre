/-!
# Fuzzer: a deterministic random source (SplitMix64) and the generator monad

Every random choice of the fuzzer goes through `Gen`, so a run is a pure function of
its seed: the same `--seed` and case index always give the same program.
-/

namespace Ochr.Fuzz

structure Rng where
  s : UInt64
deriving Inhabited

/-- SplitMix64 (Steele, Lea, Flood 2014). -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- The seed of case `i` of a run with seed `seed` (independent streams per case, so
a case can be regenerated alone from `(seed, i)`). -/
def caseRng (seed i : Nat) : Rng :=
  let (a, _) := (Rng.next ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + i.toUInt64⟩)
  let (b, _) := (Rng.next ⟨a ^^^ (i.toUInt64 * 0x9E3779B97F4A7C15)⟩)
  ⟨b⟩

structure GenSt where
  rng : Rng
  fresh : Nat := 0
  dead : List String := []     -- variables the generator will not use again (moved, or borrow ended)
deriving Inhabited

abbrev Gen := StateM GenSt

/-- Uniform in `[0, n)` (`0` when `n = 0`). -/
def rand (n : Nat) : Gen Nat := do
  if n == 0 then return 0
  let st ← get
  let (x, r) := st.rng.next
  set { st with rng := r }
  pure (x.toNat % n)

/-- True with probability `p` percent. -/
def chance (p : Nat) : Gen Bool := do pure ((← rand 100) < p)

def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := do
  pure (xs[← rand xs.length]!)

/-- A weighted choice among generators; weights of zero are never chosen. -/
def weighted {α : Type} [Inhabited α] (xs : List (Nat × Gen α)) : Gen α := do
  let total := xs.foldl (· + ·.1) 0
  if total == 0 then
    match xs.head? with
    | some (_, g) => return (← g)
    | none => return default
  let mut k ← rand total
  for (w, g) in xs do
    if k < w then return (← g)
    k := k - w
  match xs.getLast? with
  | some (_, g) => g
  | none => pure default

def freshName (pre : String) : Gen String := do
  let st ← get
  set { st with fresh := st.fresh + 1 }
  pure s!"{pre}{st.fresh}"

/-- Run a generator from a random source. -/
def Gen.run' {α : Type} (g : Gen α) (r : Rng) : α := (g.run { rng := r }).1

end Ochr.Fuzz
