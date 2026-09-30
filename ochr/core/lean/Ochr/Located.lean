import Ochr.Obs

/-!
# Located evaluation (the editor, docs/07)

When the `ochr` command checks a block, the declaration being checked has a table of where its
terms are written (`MState.locs`, `Ochr/Loc.lean`). The machine enters `eval` and `checkTail`
through `located`, so an error is reported at the innermost located term being evaluated. The
table is empty in every other run, and then these functions do nothing.
-/

namespace Ochr

/-- Run `x`; an error escaping it that no inner term located is located at `l`. -/
def atLoc {α : Type} (l : Option Loc) (x : M α) : M α :=
  match l with
  | none => x
  | some l => tryCatch x fun e => match e with
    | .error m none => throw (.error m (some l))
    | e => throw e

/-- The evaluation `x` of the term `t`, located: an error escaping it is reported at `t`'s
source range, unless a term inside it already was (the innermost wins). Only in the checked
declaration's own code at this point: at call depth 0 (a callee's body and a sealed program's
re-run raise `depth`; their errors belong to the call, or the point, that started them). A call
also makes its arguments' ranges the ones `callType` reads. -/
@[inline] def located {α : Type} (t : Term) (x : M α) : M α := do
  let s ← get
  if s.locs.table.isEmpty then x else
  let a := termAddr t
  let here := s.depth == 0 && s.locs.on
  let saved := s.locs.callArgs
  set { s with locs.callArgs := if here then s.locs.args.getD a #[] else #[] }
  let r ← if here then atLoc (s.locs.table.get? a) x else x
  modify fun s => { s with locs.callArgs := saved }
  pure r

/-- Run `x` with no term located: it is not the declaration's own code at this point. -/
def unlocated {α : Type} (x : M α) : M α := do
  let on := (← get).locs.on
  modify fun s => { s with locs.on := false }
  let r ← x
  modify fun s => { s with locs.on := on }
  pure r

/-- After a call's `n`-th argument is evaluated (`ws` the `n` values as evaluated, the frame's
last `n` temporaries what they are now), the earlier arguments it turned to `⊥` (it ended
their borrows) record it as what broke them (the editor). -/
def noteEnders (ender : Array (Option Nat)) (ws : Array Value) : M (Array (Option Nat)) := do
  if (← get).locs.table.isEmpty then return ender
  let tmp := (← get).env.back!.temps
  let n := ws.size
  let mut e := ender.push none
  for i in [0:n - 1] do
    if e[i]!.isNone && tmp[tmp.size - n + i]! == .bot && ws[i]! != .bot then e := e.set! i (some (n - 1))
  pure e

/-- Where the argument is that ended the first `⊥` argument's borrow (the editor: [Call]'s
error that an argument is `⊥` is reported at the access that broke it). -/
def enderLoc (ender : Array (Option Nat)) (ws : Array Value) : M (Option Loc) := do
  let s ← get
  if s.locs.table.isEmpty then return none
  pure ((ws.findIdx? (· == .bot)).bind fun i => ender[i]?.join.bind fun j => s.locs.callArgs[j]?.join)

/-- `new` is `old` rebuilt with the same shape: its nodes get `old`'s ranges. -/
def relocate (old new : Term) : M Unit := do
  if !(← get).locs.table.isEmpty then modify fun s => { s with locs := s.locs.relocate old new }

end Ochr
