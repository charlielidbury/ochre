import Ochr.Meaning.Steps.RecR
import Ochr.Meaning.Steps.SplitGuards

/-!
# The checker on the first recursive function, `R`, pinned (lead17, 2026-11-21; compiled, not kernel-checked; docs/31 D134)

Every `#guard` runs the checker. What is pinned: the program (the surface resolves to `bodyR`; `checkDef`
accepts it with `by n` and rejects it without, and rejects calls whose argument is not a strict subterm); the
body's start state as the checker records it (`stR`'s kernel, the mark on the function's binding of itself, the
[Rec] context); the recursion check (`recCheck`: what it compares, when, what it rejects); what the call of the
function's own name on the unknown `σ1` produces (the sealed program `⌈R(σ1)⌉ : Nat`, no new unknown, no label,
`n.0` moved, the [Rec] context kept); the leaves of both worlds (`leafZR` with `Z : Nat`, `leafSR` with
`⌈R(σ1)⌉ : Nat`) and the state after the split (`endR`); the entry conditions.
-/

open Ochr.Test

ochr RecProbe {
  def Rs (n : Nat) : Nat by n := match n { Z => Z, S m => Rs(m) }
}

namespace Ochr.Meaning.Steps.Form.ColumnR.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open Ochr.Meaning.Steps.Form.ParGuards (declIs bindOk globalOk)
open Ochr.Meaning.Steps.Form.ColumnP.Guards (kernEq kRecT)
open Ochr.Meaning.Steps.Form.ColumnI (piNat)

/-! ## The program -/

-- the surface resolves to `bodyR` (the self-call's head is the function's binding of itself, `#1`)
#guard ParGuards.bodyOf RecProbe "Rs" == .matchNat (.var 0) .zero (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false)
-- `checkDef` accepts `R` with `by n`, leaving exactly its global; without `by n` it rejects it
#guard isOk (checkDef defR) {} 100000
#guard match (outSt (checkDef defR) {} 100000).globals with
  | [g] => g.name == "R" && g.ty == piNat && g.fn? == some fixR && g.val == .gfn "R" && !g.model | _ => false
#guard !isOk (checkDef { defR with dec := none }) {} 100000
-- a call whose argument is not a strict subterm of the entry is rejected: `R(n)` (moved whole), `R(S(m))`, and a
-- call on the entry itself
#guard !isOk (checkDef { defR with body := .matchNat (.var 0) .zero (.call (.place (.var 1)) [.succ (.place (.proj 0 (.var 0)))] false) }) {} 100000
#guard !isOk (checkDef { defR with body := .call (.place (.var 1)) [.place (.var 0)] false }) {} 100000

/-- The trace of `checkDef defR`. -/
def linesOfR (cfg : Config) : List String :=
  match runMachine (checkDef defR) { cfg := cfg } 100000 with
  | (_, _, log) => log.toList.filterMap fun | .line s => some s | _ => none

-- one check of the body: world `Z`, world `S` with the call's type; the callee's body is not split (it closes off)
#guard linesOfR { trace := true } == ["[Def] R: goal Nat", "[Split] σ0 := 0",
  "[Def] R: path ends with type Nat against goal Nat", "[Split] σ0 := S σ1", "[Call-type] R(σ1) : Nat",
  "[Def] R: path ends with type Nat against goal Nat"]

/-! ## The body's start state, as the checker records it -/

/-- The checker's recorded states on entry to the located terms of `Rs`. -/
def entriesRs : List MState := ParGuards.entries RecProbe "Rs"

/-- `stR`'s kernel (renamed to `f`), and the mode `checkFix` starts the body in, with the [Rec] context of a
recursive function: the entry `σ0`, the decreasing candidate `0`, the uid the binding's mark names. -/
def startOk (f : String) (st : MState) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.isEmpty && st.env[0]!.temps.isEmpty && st.env[1]!.temps.isEmpty &&
  st.env[1]!.binds.size == 2 &&
  bindOk st.env[1]!.binds[0]! f (.gfn f) piNat (.pi .other) (some 0) &&
  bindOk st.env[1]!.binds[1]! "n" (.abs 0) .tNat .other none &&
  st.absTy == #[.tNat] && st.nextAbs == 1 && st.nextLoan == 0 && st.goal == some .tNat &&
  st.refs.isEmpty && st.etaRefs.isEmpty && st.neutrals.isEmpty && !st.liveScope &&
  st.typing && !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace &&
  st.privateDepth == 0 && st.nextRecUid == 1 &&
  (match st.recStack with
    | [r] => r.fn == .gfn f && r.entries == #[some 0] && r.cands == [0] && r.uid == 0
    | _ => false)

#guard entriesRs.head?.any (startOk "Rs")
#guard startOk "R" stRm
#guard kernEq stRm stR

/-! ## The split: the leaves of both worlds, and the state after -/

/-- The leaves of a run of `checkTail` on `R`'s body with the continuation `k` from `st`. -/
def leavesOf (k : Value → Value → M Unit) (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 bodyR k) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none

/-- The leaves are `leafZR` with `Z : Nat`, then `leafSR` with `⌈R(σ1)⌉ : Nat`; the [Rec] context is kept at
both. -/
def leavesOk (st : MState) : Bool :=
  match leavesOf kRecT st with
  | [(sz, vz, Tz), (ss, vs, Ts)] =>
    kernEq sz leafZR && vz == .zero && Tz == some .tNat && kernEq ss leafSR && vs == vR && Ts == some .tNat &&
      sz.recStack.map (·.cands) == st.recStack.map (·.cands) && ss.recStack.map (·.cands) == st.recStack.map (·.cands)
  | _ => false

#guard isOk (Ochr.checkTail 1000 bodyR kRecT) stRm 100000
#guard leavesOk stRm
#guard kernEq (outSt (Ochr.checkTail 1000 bodyR kRecT) stRm 100000) endR
-- the run fails when the continuation fails in either world
def kFailZ (v T : Value) : M Unit := do if v == .zero then Ochr.err "k" else kRecT v T
def kFailS (v T : Value) : M Unit := do if v == vR then Ochr.err "k" else kRecT v T
#guard !isOk (Ochr.checkTail 1000 bodyR kFailZ) stRm 100000 && !isOk (Ochr.checkTail 1000 bodyR kFailS) stRm 100000

/-! ## The call `R(n.0)` in world `S`, alone

From world `S`'s arm start (`armSR`'s kernel, in `checkFix`'s mode with `R`'s [Rec] context), the typed `eval` of
the call returns `⌈R(σ1)⌉ : Nat` and leaves `armSR'`'s kernel: `n.0` moved, nothing else changed (no unknown,
no label, the function's binding of itself kept), the [Rec] context kept. -/

def armSRm : MState := { armSR with typing := true, recStack := [rcR], nextRecUid := 1 }

#guard kernEq (outSt (Ochr.eval 1000 true callR (some .tNat)) armSRm 100000) armSR'
#guard outVal (Ochr.eval 1000 true callR (some .tNat)) armSRm 100000 == (vR, some .tNat)
#guard (outSt (Ochr.eval 1000 true callR (some .tNat)) armSRm 100000).recStack.map (·.cands) == [[0]]
-- at any hint, in tail position or not: the same
#guard [none, some .tNat].all fun h => [true, false].all fun tl =>
  outVal (Ochr.eval 1000 true callR h) { armSRm with tailNext := tl } 100000 == (vR, some .tNat) &&
  kernEq (outSt (Ochr.eval 1000 true callR h) { armSRm with tailNext := tl } 100000) armSR'

/-! ## The recursion check (`Machine.recCheck`)

It runs in a TYPED call only (after [Call-type]), before the callee: for each [Rec] context the call belongs to
(the head binding's mark is the context's uid, or the head value is the context's function), it keeps the
decreasing candidates whose argument is a strict subterm of the entry unknown as the records expand it, and
rejects if none was declared or none survives. -/

-- at world `S`'s arm start, `σ1` is a strict subterm of `σ0` expanded (`S(σ1)`): accepted, the candidate kept
#guard isOk (Ochr.recCheck (.gfn "R") #[.abs 1] (some 0)) armSRm 100000
#guard (outSt (Ochr.recCheck (.gfn "R") #[.abs 1] (some 0)) armSRm 100000).recStack.map (·.cands) == [[0]]
-- the entry itself, or `S(σ1)`, is not: rejected
#guard !isOk (Ochr.recCheck (.gfn "R") #[.abs 0] (some 0)) armSRm 100000
#guard !isOk (Ochr.recCheck (.gfn "R") #[.succ (.abs 1)] (some 0)) armSRm 100000
-- at the start state (no refinement) even `σ1` is not
#guard !isOk (Ochr.recCheck (.gfn "R") #[.abs 1] (some 0)) stRm 100000
-- with no candidate declared: rejected; with no [Rec] context for `R`: nothing is checked
#guard !isOk (Ochr.recCheck (.gfn "R") #[.abs 1] (some 0)) { armSRm with recStack := [{ rcR with cands := [] }] } 100000
#guard isOk (Ochr.recCheck (.gfn "R") #[.abs 0] none) { armSRm with recStack := [] } 100000
-- the untyped call skips it: the same value and kernel from a state with no candidate
#guard (outVal (Ochr.eval 1000 false callR none) { armSRm with recStack := [{ rcR with cands := [] }] } 100000).1 == vR

/-! ## Entry conditions -/

-- the leaves do not move with the tail flags, the typing flag or a handed-down reading
#guard leavesOk { stRm with tailNext := true } && leavesOk { stRm with curTail := true } &&
  leavesOk { stRm with tailDecl := some .other }
-- with no [Rec] context the run still succeeds with the same leaves (the check is skipped, not failed)
#guard leavesOk { stRm with recStack := [] }

end Ochr.Meaning.Steps.Form.ColumnR.Guards
