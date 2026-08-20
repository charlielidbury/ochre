import Dllbc
open Dllbc

/-!
# docs/17 §9 — the go/no-go harness for point-delta recording

**NOT in the default target.** Nothing imports this, so `lake build` does not
build it and the suite pays nothing; run it with
`lake build Dllbc.Tests.PointCost` (~30 s, dominated by the checks themselves).

It times the two flagships — the ARRAY one is the point, because recording hangs
off `refineSym` and `refineSym` fires during array place evaluation — with the
recording on and off, and reports the delta volume alongside.

**Why a harness and not per-module elaboration timings.** Those were tried first
and are uninformative on today's corpus: `Tests/HashMap` has 261
`prog defer_check` blocks against 18 checked ones, so its build time is
`native_decide` and compilation rather than elaboration-time checking, and the
whole module records 431 deltas. Timing it measures the wrong thing. This
measures the checker on a program that actually exercises it.

**`IO.lazyPure` is load-bearing.** A plain `let r := f ()` is a lazy binding, so
the first version of this harness timed an unevaluated thunk and reported 0 ms
for work that took twenty minutes. Anything that reports suspiciously round
zeros here is measuring nothing.
-/

def runN (n : Nat) (pt : Bool) (t : Term) : Nat := Id.run do
  let mut acc := 0
  for _ in [0:n] do
    acc := acc + (match checkProgramHover t none pt with
      | .ok (a, b) => a.length + b.length
      | .error _ => 0)
  return acc
-- `IO.lazyPure` is what FORCES the work inside the timed region. A plain
-- `let r := f ()` is a lazy binding: the earlier version of this harness timed
-- an unevaluated thunk and reported 0ms for work that actually took minutes.
def timeIt (label : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure (fun _ => f ())
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1-t0}ms  (sum {r})"
#eval show IO Unit from do
  let a := Tests.S25ArrSort.arrChain
  let l := Tests.S23Direct.flagship
  timeIt "arrChain x50 point=false" (fun _ => runN 50 false a)
  timeIt "arrChain x50 point=true " (fun _ => runN 50 true  a)
  timeIt "list     x50 point=false" (fun _ => runN 50 false l)
  timeIt "list     x50 point=true " (fun _ => runN 50 true  l)
