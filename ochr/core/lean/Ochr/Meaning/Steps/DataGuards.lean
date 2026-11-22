import Ochr.Meaning.Steps.DataNot
import Ochr.Meaning.Steps.SplitGuards

/-!
# The checker on the first data type that is not `Nat`, pinned (lead21, 2026-11-22; compiled, not kernel-checked; docs/31 D147)

Every `#guard` runs the checker. The column `Not` (`Steps/DataNot.lean`): `inductive B := T | F` and
`def Not(b : B) : B := match b { T => F, F => T }`.

What is pinned: the core body is the surface's; the declaration as `checkInd` stores it and the global as `checkDef`
pushes it; the body's start state (recorded by the checker for the surface program) has `stNot`'s kernel, in the
mode `checkFix` starts it in; the split: two worlds in constructor order, each refinement (`b ↦ T`, the record
`0 := T`; no fresh unknown, since `T` and `F` have no field), no join drop (no arm moves anything), the leaves
`leafT`/`leafF` exactly with `F`/`T` at `B`; the end state (`stNot`'s kernel); the entry conditions (the tail flags,
the typing flag, a handed-down reading, `clone`'s mode and in place: the same leaves, since nothing is read); why
`KeepsAtT` is needed; and that the run fails where `k` fails in either world.
-/

open Ochr.Test

ochr DataProbeNot {
  inductive B := T | F
  def Not(b : B) : B := match b { T => F, F => T }
}

namespace Ochr.Meaning.Steps.Form.ColumnNot.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt)
open Ochr.Meaning.Steps.Form.ParGuards (declIs bodyOf entries)
open Ochr.Meaning.Steps.Form.ColumnP.Guards (kRecT)

/-- A declaration with no parameter, compared on everything the kernel holds of it (field types exactly). -/
def indEq (a b : IndDecl) : Bool :=
  a.name == b.name && a.params.isEmpty && b.params.isEmpty && a.sort == b.sort && a.ctors.length == b.ctors.length &&
    (a.ctors.zip b.ctors).all (fun (x, y) => x.1 == y.1 && x.2.length == y.2.length &&
      (x.2.zip y.2).all fun (f, g) => f.1 == g.1 && f.2.exact g.2) &&
    a.copy == b.copy && a.abstract == b.abstract && a.unsized == b.unsized && a.nestable == b.nestable &&
    a.declaring == b.declaring

/-- Two bindings agree on what the kernel and the relation read, the values EXACTLY (constructor values' hints and
parameters included) and the readings by `DeclInfo`'s own equality. -/
def bindEqI (a b : Binding) : Bool :=
  a.hint.name == b.hint.name && a.val.exact b.val && (match a.ty, b.ty with
    | some x, some y => x.exact y | none, none => true | _, _ => false) && a.decl == b.decl && a.proof == b.proof &&
    a.recUid == b.recUid && a.cap == b.cap && a.lazyTy.isNone && b.lazyTy.isNone

def frameEqI (a b : Frame) : Bool :=
  a.binds.size == b.binds.size && (a.binds.zip b.binds).all (fun (x, y) => bindEqI x y) &&
    a.temps.size == b.temps.size && (a.temps.zip b.temps).all (fun (x, y) => x.exact y)

def gEqI (a b : GDef) : Bool :=
  a.name == b.name && a.ty.exact b.ty && (match a.fn?, b.fn? with
    | some x, some y => x.exact y | none, none => true | _, _ => false) && a.val.exact b.val && a.model == b.model &&
    a.absTys.isEmpty && b.absTys.isEmpty && a.absDecls.isEmpty && b.absDecls.isEmpty

/-- **Two states have the same kernel** (`Kern`), the declarations by `indEq`, values and types exactly. -/
def kernEqI (a b : MState) : Bool :=
  a.env.size == b.env.size && (a.env.zip b.env).all (fun (x, y) => frameEqI x y) &&
    a.globals.length == b.globals.length && (a.globals.zip b.globals).all (fun (x, y) => gEqI x y) &&
    a.inds.length == b.inds.length && (a.inds.zip b.inds).all (fun (x, y) => indEq x y) &&
    a.nextLoan == b.nextLoan && a.nextAbs == b.nextAbs && a.absTy.size == b.absTy.size &&
    (a.absTy.zip b.absTy).all (fun (x, y) => x.exact y) && a.absDecl == b.absDecl &&
    a.refs.length == b.refs.length && (a.refs.zip b.refs).all (fun (x, y) => x.1 == y.1 && x.2.exact y.2) &&
    a.etaRefs.length == b.etaRefs.length && (a.etaRefs.zip b.etaRefs).all (fun (x, y) => x.1 == y.1 && x.2.exact y.2) &&
    a.neutrals.isEmpty && b.neutrals.isEmpty &&
    (match a.goal, b.goal with | some x, some y => x.exact y | none, none => true | _, _ => false) &&
    a.liveScope == b.liveScope

/-! ## The program, the declaration, the global -/

#guard (bodyOf DataProbeNot "Not").exact bodyNot

/-- `Not` as a core definition. -/
def defNot : Def := { name := "Not", hs := [⟨"b"⟩], doms := [.tind "B" []], cod := .tind "B" [], body := bodyNot }

/-- `checkInd declB`, then `checkDef defNot`, from the empty state. -/
def declare : M Unit := do Ochr.checkInd declB; Ochr.checkDef defNot

#guard isOk declare {} 100000
#guard match (outSt declare {} 100000).inds with | [d] => indEq d declB | _ => false
#guard match (outSt declare {} 100000).globals with
  | [g] => g.name == "Not" && g.ty.exact piB && (g.fn?.map (·.exact fixNot)).getD false && g.val.exact (.gfn "Not") &&
      !g.model && g.absTys.isEmpty && g.absDecls.isEmpty
  | _ => false

/-! ## The body's start state -/

/-- The full start state: the kernel `stNot` in the mode `checkFix` starts it in (typed, one [Rec] context). -/
def stNotF : MState :=
  let rc : RecCtx := { fn := .gfn "Not", entries := #[some 0], cands := [], uid := 0 }
  { stNot with typing := true, recStack := [rc], nextRecUid := 1 }

/-- The mode `checkFix` starts the body in. -/
def modeOk (st : MState) : Bool :=
  st.typing && !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace && !st.headEval &&
  st.erasedDepth == 0 && st.privateDepth == 0 && st.depth == 0 && st.obsFrame.isNone && st.nextRecUid == 1 &&
  (match st.recStack with
    | [r] => r.fn == .gfn "Not" && r.entries == #[some 0] && r.cands.isEmpty && r.uid == 0
    | _ => false)

/-- The checker's recorded state at the entry of `Not`'s body (the first with the body's frame). -/
def recordedStart : Option MState :=
  ((entries DataProbeNot "Not").filter (fun st => st.env.size == 2 && st.env[1]!.binds.size == 2)).head?

#guard recordedStart.any fun st => kernEqI st stNot && modeOk st
#guard kernEqI stNotF stNot && modeOk stNotF

/-! ## The split -/

/-- The leaves of a run of `checkTail` on `Not`'s body with the continuation `k` from `st`. -/
def leavesOf (k : Value → Value → M Unit) (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 bodyNot k) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none

/-- The leaves are `leafT` with `F : B`, then `leafF` with `T : B`. -/
def leavesOk (st : MState) : Bool :=
  match leavesOf kRecT st with
  | [(st1, v1, T1), (st2, v2, T2)] =>
    kernEqI st1 leafT && v1.exact vF && (T1.map (·.exact tyB)).getD false &&
    kernEqI st2 leafF && v2.exact vT && (T2.map (·.exact tyB)).getD false
  | _ => false

#guard isOk (Ochr.checkTail 1000 bodyNot kRecT) stNotF 100000
#guard leavesOk stNotF
-- after both worlds: exactly the start's kernel (no unknown made, no refinement kept)
#guard kernEqI (outSt (Ochr.checkTail 1000 bodyNot kRecT) stNotF 100000) stNot

/-- The trace and derivation lines of the run, with the leaves marked. -/
def events (st : MState) : List String :=
  (runMachine (Ochr.checkTail 1000 bodyNot kRecT) { st with cfg := { derivation := true, trace := true } } 100000).2.2.toList.filterMap
    fun
    | .line s => some s.trimAsciiStart.toString
    | .state _ _ (some (v, _)) _ => some s!"leaf {v}"
    | _ => none

-- two worlds in constructor order; no `[Join]` line: the join drops nothing
#guard events stNotF == ["[Split] σ0 := T", "leaf F", "[Split] σ0 := F", "leaf T"]

-- each world's refinement, run as `checkTailAt` runs it: `b ↦ T`, the record `0 := T`, no new unknown
def bOf (st : MState) : Value := st.env[1]!.binds[1]!.val
def refineTo (c : Nat) : M Unit := do
  let r ← Ochr.ctorRefinement 1000 declB [] c
  Ochr.refine 1000 0 r
#guard (bOf (outSt (refineTo 0) stNotF 100000)).exact vT && (outSt (refineTo 0) stNotF 100000).nextAbs == 1
#guard (bOf (outSt (refineTo 1) stNotF 100000)).exact vF && (outSt (refineTo 1) stNotF 100000).nextAbs == 1

/-! ## Entry conditions -/

-- the leaves do not move with the tail flags, the typing flag or a handed-down reading
#guard leavesOk { stNotF with tailNext := true } && leavesOk { stNotF with curTail := true } &&
  leavesOk { stNotF with typing := false } && leavesOk { stNotF with tailDecl := some .other }
-- nor in `clone`'s mode or in place: the arms read nothing
#guard leavesOk { stNotF with copying := true } && leavesOk { stNotF with inPlace := true }

-- `KeepsAtT` is needed: a continuation that names an unknown in world `T` changes world `F`'s leaf's counters
def kFresh (v T : Value) : M Unit := do
  if v.exact vF then discard (Ochr.freshAbsR 100 tyB)
  kRecT v T
#guard match leavesOf kFresh stNotF with
  | [_, (st2, _, _)] => st2.nextAbs == 2 && !kernEqI st2 leafF
  | _ => false
-- the run fails where the continuation fails in either world
def kFailAt (w : Value) (v T : Value) : M Unit := do
  if v.exact w then Ochr.err "k fails"
  kRecT v T
#guard !isOk (Ochr.checkTail 1000 bodyNot (kFailAt vF)) stNotF 100000
#guard !isOk (Ochr.checkTail 1000 bodyNot (kFailAt vT)) stNotF 100000

end Ochr.Meaning.Steps.Form.ColumnNot.Guards
