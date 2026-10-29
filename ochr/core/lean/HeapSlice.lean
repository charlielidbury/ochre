import Ochr.Heap.Slice
import Ochr.Examples.Registry

/-! `lake exe heapslice`: the heap-based slice evaluator (`Ochr/Heap/Slice.lean`) against the
real machine, on every suite function inside the data slice (`notes/stability.md` §8). For each
such function it runs the call at the generic arguments, at ground arguments, and at one
unknown with the rest ground, through both, and compares; and, where the heap run never asks
about the unknown, it checks (P) on the real machine: the run at a ground value equals the
generic result with that value substituted. -/

open Ochr Ochr.Heap Ochr.Surface Ochr.Registry

/-- A first-order data type, closed (no parameter of the function in it). -/
partial def dataTy (inds : List IndDecl) : Term → Bool
  | .nat | .unit => true
  | .tind n as => match inds.find? (·.name == n) with
    | some d => d.sort != 0 && !d.abstract && !d.unsized &&
        (List.range d.ctors.length).all (!d.dependent ·) && as.all (dataTy inds)
    | none => false
  | _ => false

/-- The slice, syntactically: `fns` are the functions it may call, `k` the arity of the
function whose body this is (its `self` is variable `depth + k`). -/
partial def inSlice (inds : List IndDecl) (consts : List String) (fns : List String) (k : Nat) :
    Nat → Term → Bool
  | _, .zero | _, .tt => true
  | d, .succ u | d, .prim "clone" [u] => inSlice inds consts fns k d u
  | d, .ctor _ _ _ _ as => as.all (inSlice inds consts fns k d)
  | _, .place p => !(p.steps.2.any (· matches .deref))
  | _, .const n => consts.contains n
  | d, .letIn _ u w => inSlice inds consts fns k d u && inSlice inds consts fns k (d + 1) w
  | d, .seq u w => inSlice inds consts fns k d u && inSlice inds consts fns k d w
  | d, .matchNat p z s => !(p.steps.2.any (· matches .deref)) &&
      inSlice inds consts fns k d z && inSlice inds consts fns k d s
  | d, .matchInd p ty arms => !(p.steps.2.any (· matches .deref)) &&
      (match inds.find? (·.name == ty) with | some dd => dd.sort != 0 | none => false) &&
      arms.all (inSlice inds consts fns k d ·.2)
  | d, .call (.const n) as _ => fns.contains n && as.all (inSlice inds consts fns k d)
  | d, .call (.place (.var i)) as _ => i == d + k && as.all (inSlice inds consts fns k d)
  | _, _ => false

/-- Small ground values of a data type. -/
partial def ground (inds : List IndDecl) : Nat → Term → List Value
  | _, .nat => [.zero, .succ .zero, .succ (.succ .zero)]
  | _, .unit => [.unit]
  | 0, _ => []
  | dep + 1, .tind n as => match inds.find? (·.name == n) with
    | none => []
    | some d =>
      let np := d.params.length
      let inst : Term → Option Term := fun FT => match FT with
        | .place (.var j) => if j < np then as[np - 1 - j]? else none
        | t => some t
      let vals := d.ctors.zipIdx.flatMap fun ((cn, fields), c) =>
        let fieldVals : List (List Value) := fields.map fun (_, FT) =>
          match inst FT with
          | some T => (ground inds dep T).take 2
          | none => []
        let combos := fieldVals.foldr (fun vs acc => vs.flatMap fun v => acc.map (v :: ·)) [[]]
        combos.map fun fs => Value.ind n c ⟨cn⟩ [] fs
      vals.take 3
  | _, _ => []

inductive Out where
  | val (v : Value) | stuck | err (m : String) | undecided (m : String) | outside (m : String)

def Out.show : Out → String
  | .val v => s!"{v}"
  | .stuck => "stuck"
  | .err m => s!"error: {m}"
  | .undecided m => s!"undecided: {m}"
  | .outside m => s!"outside the slice: {m}"

def hasSealed (v : Value) : Bool := v.anyAtom fun | .sealed _ => true | _ => false

def realRun (st : MState) (t : Term) : Out :=
  match (runMachine (eval 200000 false t) st 2000000).1 with
  | .ok (v, _) _ => .val v
  | .fail (.stuck _) => .stuck
  | .fail (.error m _) => .err m
  | .exhausted m => .undecided m

def heapRun (S : Sig) (k : Nat) (t : Term) : Out × List Nat :=
  let H0 : Heap := { node := fun _ => none, next := k }
  let p := evalH S 200000 t []
  let (r, H) := exec p H0
  let qs := queries p H0
  (match r with
    | .ok h => .val (decode H 100000 h)
    | .stuck => .stuck
    | .err m => .err m
    | .outside m => .outside m, qs)

structure Tally where
  fns : Nat := 0
  runs : Nat := 0
  agree : Nat := 0
  bothStuck : Nat := 0
  bothErr : Nat := 0
  realUndecided : Nat := 0
  heapOutside : Nat := 0
  mismatch : Array String := #[]
  pChecks : Nat := 0
  pAgree : Nat := 0
  pMismatch : Array String := #[]
  pSkippedQueried : Nat := 0
  oneUnknownRuns : Nat := 0
  notAskedNoWalk : Nat := 0
  notAskedWalk : Nat := 0
  sliceFns : Array String := #[]

def compareRun (T : Tally) (what : String) (r : Out) (h : Out) : Tally :=
  let T := { T with runs := T.runs + 1 }
  match h, r with
  | .outside _, _ => { T with heapOutside := T.heapOutside + 1 }
  | _, .undecided _ => { T with realUndecided := T.realUndecided + 1 }
  | .val vh, .val vr =>
    if hasSealed vr then { T with mismatch := T.mismatch.push s!"{what}: heap {vh}, real closed off: {vr}" }
    else if vh == vr then { T with agree := T.agree + 1 }
    else { T with mismatch := T.mismatch.push s!"{what}: heap {vh}, real {vr}" }
  | .stuck, .stuck => { T with bothStuck := T.bothStuck + 1 }
  | .stuck, .val vr =>
    if hasSealed vr then { T with bothStuck := T.bothStuck + 1 }
    else { T with mismatch := T.mismatch.push s!"{what}: heap stuck, real {vr} (an inner call closed off and was discarded)" }
  | .err _, .err _ => { T with bothErr := T.bothErr + 1 }
  | h, r => { T with mismatch := T.mismatch.push s!"{what}: heap {h.show}, real {r.show}" }

def main : IO UInt32 := do
  let mut T : Tally := {}
  let mut seen : List String := []
  for (bname, b) in programs ++ caseStudies do
    let p := Ochr.Test.libOf {} 2000000 b ++ b.decls
    let items := p.filterMap fun d => (resolveProgram p d).toOption
    let (globals, inds) := globalsAfter {} items
    let own := b.decls.map (·.name)
    let consts := globals.filterMap fun g => if g.fn?.isNone && !(g.val matches .gfn _) then some g.name else none
    -- candidates: data parameters and codomain; then the fixpoint of "its body is in the slice"
    let cands := globals.filterMap fun g => match g.fn? with
      | some (.fix _ hs ds c _ body) =>
        if ds.all (dataTy inds) && dataTy inds c then some (g.name, hs.length, ds, body) else none
      | _ => none
    let mut fns := cands.map (·.1)
    let mut changed := true
    while changed do
      let keep := cands.filter fun (n, k, _, body) => fns.contains n && inSlice inds consts fns k 0 body
      changed := keep.length != fns.length
      fns := keep.map (·.1)
    let S : Sig := {
      fn := fun n => (cands.find? (·.1 == n)).bind fun (n', k, _, body) => if fns.contains n' then some (k, body) else none
      const := fun n => if consts.contains n then (globals.find? (·.name == n)).map (·.val) else none
      isProp := fun n => (inds.find? (·.name == n)).any (·.sort == 0) }
    for (n, k, ds, _) in cands do
      unless fns.contains n && own.contains n && !seen.contains n do continue
      seen := n :: seen
      T := { T with fns := T.fns + 1, sliceFns := T.sliceFns.push s!"{bname}.{n}" }
      -- the types of the unknowns: unknown `i` stands at parameter `i`
      let st0 : MState := { globals := globals, inds := inds }
      let tys := ds.map fun d => match runM (evalType 10000 d) st0 with
        | .ok v => v
        | .error _ => Value.bot
      let st : MState := { st0 with absTy := tys.toArray, nextAbs := k }
      let grounds := ds.map (ground inds 2)
      let call (args : List Value) : Term := .call (.const n) (args.map .val) false
      -- generic, every ground combination (capped), and one unknown with the rest ground
      let allGround := (grounds.foldr (fun vs acc => vs.flatMap fun v => acc.map (v :: ·)) [[]]).take 27
      let generic := (List.range k).map fun i => Value.abs i
      let mut runs : List (String × List Value) := [(s!"{n} generic", generic)]
      for args in allGround do runs := runs ++ [(s!"{n}{args}", args)]
      for i in List.range k do
        if let some base := allGround.head? then
          runs := runs ++ [(s!"{n} σ{i} at {base}", base.set i (.abs i))]
      for (what, args) in runs do
        let r := realRun st (call args)
        let (h, qs) := heapRun S k (call args)
        T := compareRun T s!"{bname}.{what}" r h
        -- (P) on the real machine: one unknown, not asked about by the heap run
        let unknowns := (List.range k).filter fun i => args[i]? == some (.abs i)
        if unknowns.length == 1 && k > 0 then
          let i := unknowns.head!
          let (_, qsWalk) := heapRun { S with walkOnRead := true } k (call args)
          T := { T with oneUnknownRuns := T.oneUnknownRuns + 1,
                        notAskedNoWalk := T.notAskedNoWalk + (if qs.contains i then 0 else 1),
                        notAskedWalk := T.notAskedWalk + (if qsWalk.contains i then 0 else 1) }
          if qs.contains i then
            T := { T with pSkippedQueried := T.pSkippedQueried + 1 }
          else if let .val vr := r then
            for v in (grounds[i]?.getD []).take 3 do
              let inst := realRun st (call (args.set i v))
              let sub := match runM (substV 100000 (.abs i) v vr) st with
                | .ok w => Out.val w
                | .error m => .err m
              T := { T with pChecks := T.pChecks + 1 }
              match inst, sub with
              | .val a, .val b2 =>
                if a == b2 then T := { T with pAgree := T.pAgree + 1 }
                else T := { T with pMismatch := T.pMismatch.push s!"{bname}.{what} at σ{i} := {v}: instance {a}, generic refined {b2}" }
              | a, b2 => T := { T with pMismatch := T.pMismatch.push s!"{bname}.{what} at σ{i} := {v}: instance {a.show}, generic refined {b2.show}" }
  IO.println s!"functions in the slice: {T.fns}"
  IO.println s!"  {", ".intercalate T.sliceFns.toList}"
  IO.println s!"runs: {T.runs}; same value: {T.agree}; both stuck (real closed off): {T.bothStuck}; both errors: {T.bothErr}; real undecided: {T.realUndecided}; heap outside the slice: {T.heapOutside}"
  IO.println s!"differences: {T.mismatch.size}"
  for m in T.mismatch.toList.take 40 do IO.println s!"  {m}"
  IO.println s!"(P) on the real machine, where the heap run did not ask about the unknown: {T.pChecks} checks, {T.pAgree} agree, {T.pMismatch.size} differ; runs skipped because the heap asked about the unknown: {T.pSkippedQueried}"
  for m in T.pMismatch.toList.take 40 do IO.println s!"  {m}"
  IO.println s!"runs with one unknown: {T.oneUnknownRuns}; the unknown never asked about: {T.notAskedNoWalk} with reads that look only where they go, {T.notAskedWalk} if every read walks the value read (as the real machine's hasHole and loan searches do)"
  pure (if T.mismatch.isEmpty && T.pMismatch.isEmpty then 0 else 1)
