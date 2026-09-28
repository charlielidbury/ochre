import OchrMeta.WF
import OchrMeta.Interp

/-! # T1(b) fuzzing: eager vs lazy ends on small reachable states

Reachable states: BFS from `init` by `depth` atomic operations (assignments of borrows/reads of
small places, `p := 0`, discarded reads, matches).  For each state `s` and each `s'` reachable
from `s` by a nonempty sequence of ends of held borrows (`endsClosure`; the single-end variant
uses `(heldOf s).filterMap (endBorrow · s)`), run every test term from `s'` (eager) and from `s`
(lazy); when both succeed, classify:

* `value`   : the values differ (would refute T1(b));
* `resolve` : `endAll s₁ ≠ endAll s₂` (would refute T1(b));
* `notjoin1`: neither final state reaches the other by ends (a two-sided lag);
* `ok`      : otherwise.

Results recorded 2026-09-28 (interpreted `#eval`, a few minutes each):
* depth 2, single ops, multi-end `s'`: 31 014 both-ok pairs, 0 value/resolve, 0 notjoin1;
* depth 3, single ops, multi-end `s'`: 388 564 pairs, 0 value/resolve, 390 notjoin1;
* depth 3, single ops, single-end `s'`: 314 894 pairs, 0 value/resolve, 0 notjoin1;
* depth 2, two-op sequences, multi-end `s'`: 1 553 289 pairs, 0 value/resolve, 0 notjoin1.

Only the cheapest run is left enabled. -/

namespace OchrMeta.SchedFuzz
open OchrMeta

def vars : List Var := [.nm "a", .nm "b", .nm "x", .nm "y"]
def places : List Place := vars.flatMap fun v =>
  [.var v, .deref (.var v), .fst (.deref (.var v)), .fst (.var v), .snd (.deref (.var v))]
def ops : List Term :=
  (vars.flatMap fun v => places.flatMap fun p => [.assign (.var v) (.borrow p), .assign (.var v) (.read p)]) ++
  (places.flatMap fun p => [.assign p .zero, .seq (.read p) .unit, .mtch p .unit (.nm "q") .unit])
def tests2 : List Term := ops ++ (ops.flatMap fun t => ops.map fun u => .seq t u)

def init : St :=
  ⟨[[(.nm "y", .unit), (.nm "x", .unit), (.nm "b", .pair (.succ .zero) .zero), (.nm "a", .pair .zero .zero)]], 0⟩

def step (ss : List St) : List St :=
  (ss.flatMap fun s => ops.filterMap fun t => match exec [] 5 s t with | .ok s' _ => some s' | _ => none).eraseDups

def heldOf (s : St) : List Nat := s.env.flatten.filterMap fun b => match b.2 with | .borrow l _ => some l | _ => none

/-- Every state reachable from `s` by ends of held borrows (`s` included). -/
partial def endsClosure (s : St) : List St :=
  s :: (heldOf s).flatMap fun l => match endBorrow l s with | some s' => endsClosure s' | none => []

def classify (s : St) (single : Bool) (tests : List Term) : List (St × St × Term × String) :=
  let alts := if single then (heldOf s).filterMap fun l => endBorrow l s
    else ((endsClosure s).eraseDups).filter (· != s)
  alts.flatMap fun s' => tests.filterMap fun t =>
    match exec [] 8 s' t, exec [] 8 s t with
    | .ok s1 v1, .ok s2 v2 =>
      if v1 != v2 then some (s, s', t, "value")
      else if endAll s1 != endAll s2 then some (s, s', t, "resolve")
      else if !((endsClosure s1).contains s2 || (endsClosure s2).contains s1) then some (s, s', t, "notjoin1")
      else some (s, s', t, "ok")
    | _, _ => none

def main (depth : Nat) (single : Bool) (tests : List Term) : IO Unit := do
  let mut ss := [init]
  let mut all : List St := [init]
  for _ in [0:depth] do
    ss := step ss
    all := all ++ ss
  all := all.eraseDups
  let mut bad := 0
  let mut okc := 0
  let mut nj := 0
  for s in all do
    for (s, s', t, why) in classify s single tests do
      if why == "ok" then okc := okc + 1
      else if why == "notjoin1" then
        nj := nj + 1
        if nj ≤ 1 then IO.println s!"NOTJOIN1: {repr s} s'={repr s'} t={repr t}"
      else
        bad := bad + 1
        if bad ≤ 3 then IO.println s!"BAD {why}: {repr s} s'={repr s'} t={repr t}"
  IO.println s!"states {all.length}; both-ok pairs {okc + nj + bad}; value/resolve failures {bad}; notjoin1 {nj}"

#eval main 2 false ops
-- #eval main 3 false ops      -- 390 notjoin1, 0 failures
-- #eval main 3 true ops       -- 0 notjoin1, 0 failures
-- #eval main 2 false tests2   -- 0 notjoin1, 0 failures

end OchrMeta.SchedFuzz
