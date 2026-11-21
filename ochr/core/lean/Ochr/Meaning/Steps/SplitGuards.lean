import Ochr.Meaning.Steps.SplitP
import Ochr.Meaning.Regress.TailJoin

/-!
# The checker at `P`'s split, pinned (lead16, 2026-11-21; compiled, not kernel-checked; docs/31 D131)

Every `#guard` runs the checker. `P`'s body is checked by `checkTail` from `Regress.TailJoin.stP` (the start
state `checkFix` makes, its kernel `ColumnP.stP`, in `checkFix`'s mode), with a continuation that records each
leaf: the state, the value and its type.

What is pinned: the two worlds in order (`Z` first); each world's refinement (`refine`'s change to the state:
the value at `n`, the record in `refs`, and in world `S` the fresh unknown's type and reading); the state at
each leaf before the join's drop (world `S`: `n ↦ S(⊥)` after the arm's move of `n.0`, recorded by the
checker itself at the arm's exit; world `Z`: the arm reads nothing, so `n ↦ Z`) and after it (`n ↦ ⊥`, the
leaf `k` runs at: `leafZ`, `leafS` exactly, on their kernels); where `k` runs (at each leaf, inside the
world, after the join's drop: the `[Join]` line precedes the leaf); what the check as a whole leaves
(`endP`: the snapshot, the counters and the fresh unknown's type kept); that it fails when `k` fails in
either world; the entry conditions (the leaves' kernels do not move with the tail flags, the typing flag,
a handed-down reading or the copying modes: in `clone`'s mode the arm's read COPIES `n.0`, but the join
drops `n` whole after it); and why `KeepsAtZ` is needed (a continuation that names an unknown in world `Z`
moves world `S`'s fresh unknown to `σ2`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnP.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt)
open Ochr.Meaning.Steps.Form.ParGuards (declIs)

/-- Two bindings agree on what the kernel and the relation read. -/
def bindEq (a b : Binding) : Bool :=
  a.hint.name == b.hint.name && a.val == b.val && a.ty == b.ty && declIs a.decl b.decl && a.proof == b.proof &&
    a.recUid == b.recUid && a.cap == b.cap && a.lazyTy.isNone && b.lazyTy.isNone

/-- Two frames agree but for their temporaries' stored types (`Frame.erase`). -/
def frameEq (a b : Frame) : Bool :=
  a.binds.size == b.binds.size && (a.binds.zip b.binds).all (fun (x, y) => bindEq x y) && a.temps == b.temps

/-- Two globals agree. -/
def gEq (a b : GDef) : Bool :=
  a.name == b.name && a.ty == b.ty && a.fn? == b.fn? && a.val == b.val && a.model == b.model &&
    a.absTys.isEmpty && b.absTys.isEmpty && a.absDecls.isEmpty && b.absDecls.isEmpty

/-- **Two states have the same kernel** (`Kern`: Ω but the temporaries' stored types, Σ, the declarations, the
counters, Δ and its readings, the records, the goal, the scope flag). -/
def kernEq (a b : MState) : Bool :=
  a.env.size == b.env.size && (a.env.zip b.env).all (fun (x, y) => frameEq x y) &&
    a.globals.length == b.globals.length && (a.globals.zip b.globals).all (fun (x, y) => gEq x y) &&
    a.inds.isEmpty && b.inds.isEmpty && a.nextLoan == b.nextLoan && a.nextAbs == b.nextAbs && a.absTy == b.absTy &&
    a.absDecl.size == b.absDecl.size && (a.absDecl.zip b.absDecl).all (fun (x, y) => declIs x y) &&
    a.refs == b.refs && a.etaRefs == b.etaRefs && a.neutrals == b.neutrals && a.goal == b.goal &&
    a.liveScope == b.liveScope

/-- A continuation that records the leaf it runs at: the state, the value, its type. -/
def kRecT (v T : Value) : M Unit := do
  let s ← get
  modifyThe (Array LogEntry) (·.push (.state default true (some (v, some T)) s))

/-- The leaves of a run of `checkTail` on `P`'s body with the continuation `k` from `st`. -/
def leavesOf (k : Value → Value → M Unit) (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 bodyP k) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none

/-- The leaves are `leafZ` with `Z : Nat`, then `leafS` with `σ1 : Nat`. -/
def leavesOk (st : MState) : Bool :=
  match leavesOf kRecT st with
  | [(sz, vz, Tz), (ss, vs, Ts)] =>
    kernEq sz leafZ && vz == .zero && Tz == some .tNat && kernEq ss leafS && vs == .abs 1 && Ts == some .tNat
  | _ => false

open Ochr.Meaning.Regress.TailJoin (stP)

-- the start state's kernel is `ColumnP.stP`
#guard kernEq stP ColumnP.stP
-- the run succeeds, with two leaves: world `Z` then world `S`, at `leafZ` and `leafS` exactly
#guard isOk (Ochr.checkTail 1000 bodyP kRecT) stP 100000
#guard leavesOk stP
-- after both worlds: the snapshot (`n ↦ σ0`, no refinement), the counters and `σ1 : Nat` kept
#guard kernEq (outSt (Ochr.checkTail 1000 bodyP kRecT) stP 100000) endP

/-! ## Each world's refinement (`refine`, run as `checkTailAt` runs it) -/

def nOf (st : MState) : Value := st.env[1]!.binds[1]!.val

-- world `Z`: `n ↦ Z`, the record `0 := Z`, no new unknown
#guard nOf (outSt (Ochr.refine 1000 0 .zero) stP 100000) == .zero
#guard (outSt (Ochr.refine 1000 0 .zero) stP 100000).refs == [(0, .zero)]
#guard (outSt (Ochr.refine 1000 0 .zero) stP 100000).nextAbs == 1
-- world `S`: the fresh `σ1 : Nat` read `.other`, `n ↦ S(σ1)`, the record `0 := S(σ1)`
def reS : M Unit := do let σ ← Ochr.freshAbsR 1000 .tNat; Ochr.refine 1000 0 (.succ (.abs σ))
#guard nOf (outSt reS stP 100000) == .succ (.abs 1)
#guard (outSt reS stP 100000).refs == [(0, .succ (.abs 1))]
#guard (outSt reS stP 100000).absTy == #[.tNat, .tNat] && (outSt reS stP 100000).nextAbs == 2
#guard (outSt reS stP 100000).absDecl.size == 2 && declIs (outSt reS stP 100000).absDecl[1]! .other

/-! ## The order of events, and the state before the join's drop -/

/-- The trace and derivation lines of the run, with the leaves marked. -/
def events (st : MState) : List String :=
  (runMachine (Ochr.checkTail 1000 bodyP kRecT) { st with cfg := { derivation := true, trace := true } } 100000).2.2.toList.filterMap
    fun
    | .line s => some s.trimLeft
    | .state _ _ (some (v, _)) _ => some s!"leaf {v}"
    | _ => none

-- world `Z`: split, the join drops `n`, the leaf; world `S`: split, the arm's read moves `n.0`, the join
-- drops `n`, the leaf
#guard events stP == ["[Split] σ0 := 0", "[Join] n dropped", "leaf 0", "[Split] σ0 := S σ1",
  "[Read] its declared type is not a copy type: moved out", "[Join] n dropped", "leaf σ1"]

/-- The states the checker records at the located terms' exits (`Config.recordStates`) in `P`'s check. -/
def exits : List (Value × MState) :=
  let r := Ochr.Test.runWith none "ParProbeP" ParProbeP { recordStates := true } (located := true)
  match r.rows.find? (·.name == "Pp") with
  | some row => row.trace.toList.filterMap fun
      | .state _ true (some (v, _)) st => some (v, st)
      | _ => none
  | none => []

-- world `S`'s arm exits with `σ1` and `n ↦ S(⊥)`: the state before the join's drop
#guard exits.any fun (v, st) => v == .abs 1 && st.env.size == 2 && nOf st == .succ .bot &&
  st.refs == [(0, .succ (.abs 1))]

/-! ## Entry conditions -/

-- the leaves do not move with the tail flags, the typing flag or a handed-down reading
#guard leavesOk { stP with tailNext := true } && leavesOk { stP with curTail := true } &&
  leavesOk { stP with typing := false } && leavesOk { stP with tailDecl := some .other }
-- in `clone`'s mode (or in place) the arm's read COPIES `n.0`, and the join drops `n` whole after it: the
-- same leaves (the mode is assumed anyway, as at `checkFix`'s entry)
#guard leavesOk { stP with copying := true } && leavesOk { stP with inPlace := true }
#guard !(events { stP with copying := true }).contains "[Read] its declared type is not a copy type: moved out"

-- `KeepsAtZ` is needed: a continuation that names an unknown in world `Z` moves world `S`'s fresh unknown
def kFresh (v T : Value) : M Unit := do
  if v == .zero then discard (Ochr.freshAbsR 100 .tNat)
  kRecT v T
#guard match leavesOf kFresh stP with
  | [_, (ss, vs, _)] => vs == .abs 2 && nOf ss == .bot && ss.refs == [(0, .succ (.abs 2))]
  | _ => false
-- the run fails where the continuation fails in either world
def kFailAt (w : Value) (v T : Value) : M Unit := do
  if v == w then Ochr.err "k fails"
  kRecT v T
#guard !isOk (Ochr.checkTail 1000 bodyP (kFailAt .zero)) stP 100000
#guard !isOk (Ochr.checkTail 1000 bodyP (kFailAt (.abs 1))) stP 100000

end Ochr.Meaning.Steps.Form.ColumnP.Guards
