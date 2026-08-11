import Dllbc.StageV
import Dllbc.Tests.Direct
import Dllbc.Tests.ArraySort

/-!
# M32 Stage V — bet (c)'s cost line

A COMPILED harness, per the house rule that a cost claim is made on a compiled
exe rather than an `#eval` (which the IR interpreter taxes ~30x). It answers one
question: what does conversion cost when a λ value rests as a raw closure and
must be cooked transiently, against today's cost when it rests cooked?

**Every value is a function of the loop index.** The first draft timed a
loop-invariant expression and measured 0 ms for 20000 iterations at every
variant — the compiler had hoisted the whole computation out. Indexing the σ's
by the iteration is what makes each call a fresh problem.
-/

open Dllbc Dllbc.StageV
open Dllbc.Tests.S25ArrSort


/-- Wall-clock `f` over `[0, n)`, returning milliseconds. -/
def timeIt (n : Nat) (label : String) (f : Nat → Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut ok := 0
  for i in [0:n] do
    if f i then ok := ok + 1
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms / {n} iters (hits={ok})"

/-- A builder deep enough that cooking is not a two-node toy: a λ whose body is a
    nested spine over four captured names, all of them indexed by `i`. -/
def deepBody : Val :=
  .app (.app (.const "Add")
    (.app (.app (.const "Add") (.app (.const "Len") (.pvar "S")))
      (.app (.app (.const "Add") (.pvar "A")) (.pvar "B"))))
    (.app (.app (.const "Add") (.pvar "C")) (.pvar "a"))

def deepRho (i : Nat) : Val.PEnv :=
  [("S", .sym (4 * i)), ("A", .sym (4 * i + 1)), ("B", .sym (4 * i + 2)),
   ("C", .app (.const "Len") (.sym (4 * i + 3)))]

/-- At rest as a RAW closure — what §2.3 wants stored. -/
def deepRaw (i : Nat) : Val := .lam "a" listNat (.closure (deepRho i) deepBody)

/-- At rest COOKED — what today's kernel stores for the same source, because
    `Pure.lean`'s exported entry points read back before the value escapes. -/
def deepCooked (i : Nat) : Val := cook (deepRaw i)

def main (argv : List String) : IO Unit := do
  IO.println "== M32 Stage V, bet (c): transient cooking at a comparison site =="
  IO.println s!"raw and cooked convert: {Val.convert 1000 (deepRaw 0) (deepCooked 0)}"
  let n := 20000
  -- The comparison site, both sides at rest in today's form.
  timeIt n "convert cooked-vs-cooked   " (fun i => Val.convert 1000 (deepCooked i) (deepCooked i))
  -- One side a raw closure: the transient cook R2 pays per comparison.
  timeIt n "convert raw-vs-cooked      " (fun i => Val.convert 1000 (deepRaw i) (deepCooked i))
  timeIt n "convert raw-vs-raw         " (fun i => Val.convert 1000 (deepRaw i) (deepRaw i))
  -- The other half of the trade: storing costs a readback today and nothing
  -- under raw closures. A comparison-site cost that is paid ONCE at store time
  -- is not saved by resting raw, it is moved.
  timeIt n "store cooked (readback)    " (fun i => (deepCooked i).symIds.length > 0)
  timeIt n "store raw    (no readback) " (fun i => (deepRaw i).symIds.length > 0)
  -- And the sweep, which is what R2's cooking schedule is actually about.
  timeIt n "sweep raw    (substSym)    "
    (fun i => (substSym (4 * i) (Val.nat 3) (deepRaw i)).symIds.length > 0)
  timeIt n "sweep cooked (substSym)    "
    (fun i => (substSym (4 * i) (Val.nat 3) (deepCooked i)).symIds.length > 0)

  -- === Bet (a)'s cost line: two real corpus workloads ===
  -- `lookupSlot` is the machine's hottest operation and name-keying changes it
  -- from a short-circuiting `find?` to a filter-and-last over the whole of Ω, so
  -- the number that matters is not a microbenchmark but a real check and a real
  -- execution. Run this binary on both keyings and compare.
  IO.println "-- bet (a): corpus workloads --"
  -- `lookupSlot` is the machine's hottest operation and name-keying changes it
  -- from a short-circuiting `find?` to a filter-and-last over the whole of Ω, so
  -- the number that matters is a real check and a real execution, not a
  -- microbenchmark. Run this binary on both keyings and compare.
  --
  -- The input is a function of the ITERATION, and that is load-bearing twice
  -- over: a first draft timing `progOk flagship` in a literal-count loop
  -- reported 0 ms for 20 reps, because a closed application is lifted to an
  -- initialized constant and computed once. Varying the input defeats it.
  let reps := (argv.head?.bind String.toNat?).getD 8
  timeIt reps "CHECK arrUnder+qsCallerA   "
    (fun i => progOk (arrUnder sHonest pHonest qHonest qSuffHonest
      (qsCallerA (List.range (2 + i % 2)).reverse)))
  timeIt reps "EXEC  runQsA (array sort)  "
    (fun i => (runQsA (List.range (7 + i % 3)).reverse).isSome)
