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
  let saved := (s.locs.callArgs, s.locs.here)
  let l := if here then s.locs.table.get? a else none
  set { s with locs.callArgs := if here then s.locs.args.getD a #[] else #[],
               locs.here := if l.isSome then l else s.locs.here }
  let r ← if here then atLoc l x else x
  modify fun s => { s with locs.callArgs := saved.1, locs.here := saved.2 }
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

/-! ## Notes: what the editor shows on hover (phase 3) -/

/-- Record `n` at the range `l`, labelled by the path's [Split] refinements, if this is the
declaration's own code at this point (as `located`). -/
def noteLoc (l : Option Loc) (n : Note) : M Unit := do
  let s ← get
  if s.depth != 0 then return
  if let some l := l then modifyThe (Array LogEntry) (·.push (.note l s.refs n))

/-- Record `n` at the term `t`, if it is located and this is the declaration's own code here. -/
def noteAt (t : Term) (n : Note) : M Unit := do
  let s ← get
  if s.locs.table.isEmpty || !s.locs.on then return
  noteLoc (s.locs.table.get? (termAddr t)) n

/-- The name of a position of Ω (its binding's name). -/
def posName (env : Env) : Pos → String
  | .bind f i => env[f]!.binds[i]!.hint.name
  | .temp _ _ => "a temporary"

/-- Run `x`, the evaluation of `t`, and note its value and type at `t`: for a borrow, where it
points to (the owners of its loan, RULES §4). -/
def noteValue (t : Term) (x : M (Value × Option Value)) : M (Value × Option Value) := do
  let r ← x
  let s ← get
  if !s.locs.table.isEmpty then
    let lenders := match r.1 with
      | .borrow l _ => (owners s.env l).map (posName s.env)
      | _ => []
    noteAt t (.value r.1 r.2 lenders)
  pure r

/-- The content of a place of the top frame, if it has one (as `Machine.content`). -/
def placeContent? (p : Place) : M (Option Value) := do
  let (i, ss) := p.steps
  let fr := (← get).env.back!
  if i < fr.binds.size then pure (fr.binds[fr.binds.size - 1 - i]!.val.follow ss) else pure none

/-- `checkTail t`'s entry, located (`located`): hovering `t` shows the goal it is checked
against, and a match's scrutinee shows its content on each path: before the split, and in
each arm, as that arm's refinement made it. -/
def locatedTail (t : Term) (x : M Unit) : M Unit := located t do
  let s ← get
  if !s.locs.table.isEmpty && s.depth == 0 && s.locs.on then
    if let some G := s.goal then noteAt t (.goal G)
    -- the first tail term under a split is an arm: its scrutinee's content on this path
    if let some (p, l) := s.locs.arm then
      if let some v ← placeContent? p then noteLoc (some l) (.value v none [])
      modify fun s => { s with locs.arm := none }
    match t with
    | .matchNat p .. | .matchInd p .. =>
      if let some l := s.locs.scruts.get? (termAddr t) then
        if let some v ← placeContent? p then noteLoc (some l) (.value v none [])
        modify fun s => { s with locs.arm := some (p, l) }
    | _ => pure ()
  x

/-- `new` is `old` rebuilt with the same shape: its nodes get `old`'s ranges. -/
def relocate (old new : Term) : M Unit := do
  if !(← get).locs.table.isEmpty then modify fun s => { s with locs := s.locs.relocate old new }

end Ochr
