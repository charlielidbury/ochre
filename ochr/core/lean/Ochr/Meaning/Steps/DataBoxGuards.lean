import Ochr.Meaning.Steps.DataBox
import Ochr.Meaning.Steps.DataGuards

/-!
# The checker on a data type with a field, pinned (lead21, 2026-11-22; compiled, not kernel-checked; docs/31 D148)

Every `#guard` runs the checker. The columns `Wrap` and `Unbox` (`Steps/DataBox.lean`).

What is pinned: the core bodies are the surface's; the declaration as `checkInd` stores it; each body's start state
(recorded by the checker for the surface program) has the kernel `stWrap`/`stUnbox`; each body's one leaf
(`endWrap` with `MkBox(σ0) : Box`; `leafUnbox` with `σ1 : Nat`) and the order of events (`Unbox`: the refinement in
place, then the read, no join); the state `checkTail` ends in (the leaf's: nothing is undone); the entry
conditions: the tail flags, the typing flag and a handed-down reading do not move the leaves; in `clone`'s mode
or in place the read COPIES (`n ↦ σ0` kept; `b ↦ MkBox(σ1)` kept), so the plain mode (`Mode`) is assumed; a
counter of unknowns at `2` on entry makes `Unbox`'s fresh unknown `σ2`.
-/

open Ochr.Test

ochr DataProbeWrap {
  inductive Box := MkBox(n : Nat)
  def Wrap(n : Nat) : Box := MkBox(n)
}

ochr DataProbeUnbox {
  inductive Box := MkBox(n : Nat)
  def Unbox(b : Box) : Nat := match b { MkBox(n) => n }
}

-- (c): a known scrutinee not ending a body. With `Box` (one constructor) there is no entry and no join (D93); with
-- a two-constructor type whose arm moves a field, there are both.
ochr DataProbeKnown {
  inductive Box := MkBox(n : Nat)
  inductive Opt := None | Some(n : Nat)
  def UseC : Nat := let b = MkBox(1); S(match b { MkBox(n) => n })
  def UseO : Nat := let o = Some(1); S(match o { None => Z, Some(n) => n })
}

namespace Ochr.Meaning.Steps.Form.ColumnBox.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt)
open Ochr.Meaning.Steps.Form.ParGuards (bodyOf entries)
open Ochr.Meaning.Steps.Form.ColumnP.Guards (kRecT)
open Ochr.Meaning.Steps.Form.ColumnNot.Guards (kernEqI indEq)

#guard (bodyOf DataProbeWrap "Wrap").exact bodyWrap
#guard (bodyOf DataProbeUnbox "Unbox").exact bodyUnbox

def defWrap : Def := { name := "Wrap", hs := [⟨"n"⟩], doms := [.nat], cod := .tind "Box" [], body := bodyWrap }
def defUnbox : Def := { name := "Unbox", hs := [⟨"b"⟩], doms := [.tind "Box" []], cod := .nat, body := bodyUnbox }

#guard isOk (do Ochr.checkInd declBox; Ochr.checkDef defWrap) {} 100000
#guard isOk (do Ochr.checkInd declBox; Ochr.checkDef defUnbox) {} 100000
#guard match (outSt (Ochr.checkInd declBox) {} 100000).inds with | [d] => indEq d declBox | _ => false

/-- The recorded state at the entry of a body (the first with the body's frame). -/
def recordedStart (b : Ochr.Surface.Block) (n : String) : Option MState :=
  ((entries b n).filter (fun st => st.env.size == 2 && st.env[1]!.binds.size == 2)).head?

/-- The mode `checkFix` starts a body in. -/
def modeOk (f : String) (st : MState) : Bool :=
  st.typing && !st.curTail && !st.tailNext && st.tailDecl.isNone && !st.copying && !st.inPlace && !st.headEval &&
  st.erasedDepth == 0 && st.privateDepth == 0 && st.depth == 0 && st.nextRecUid == 1 &&
  (match st.recStack with
    | [r] => r.fn == .gfn f && r.entries == #[some 0] && r.cands.isEmpty && r.uid == 0
    | _ => false)

#guard (recordedStart DataProbeWrap "Wrap").any fun st => kernEqI st stWrap && modeOk "Wrap" st
#guard (recordedStart DataProbeUnbox "Unbox").any fun st => kernEqI st stUnbox && modeOk "Unbox" st

/-- The full start states. -/
def stWrapF : MState :=
  { stWrap with
    typing := true, recStack := [{ fn := .gfn "Wrap", entries := #[some 0], cands := [], uid := 0 }], nextRecUid := 1 }
def stUnboxF : MState :=
  { stUnbox with
    typing := true, recStack := [{ fn := .gfn "Unbox", entries := #[some 0], cands := [], uid := 0 }], nextRecUid := 1 }

/-- The leaves of a run of `checkTail` on `t` with the continuation `k` from `st`. -/
def leavesOf (t : Term) (k : Value → Value → M Unit) (st : MState) : List (MState × Value × Option Value) :=
  (runMachine (Ochr.checkTail 1000 t k) st 100000).2.2.toList.filterMap fun
    | .state _ _ (some (v, T)) s => some (s, v, T)
    | _ => none

def wrapOk (st : MState) : Bool :=
  match leavesOf bodyWrap kRecT st with
  | [(s, v, T)] => kernEqI s endWrap && v.exact (mkBox (.abs 0)) && (T.map (·.exact tyBox)).getD false
  | _ => false

def unboxOk (st : MState) : Bool :=
  match leavesOf bodyUnbox kRecT st with
  | [(s, v, T)] => kernEqI s leafUnbox && v.exact (.abs 1) && (T.map (·.exact .tNat)).getD false
  | _ => false

#guard isOk (Ochr.checkTail 1000 bodyWrap kRecT) stWrapF 100000 && wrapOk stWrapF
#guard isOk (Ochr.checkTail 1000 bodyUnbox kRecT) stUnboxF 100000 && unboxOk stUnboxF
-- nothing is undone after the leaf: the run ends in the leaf's kernel
#guard kernEqI (outSt (Ochr.checkTail 1000 bodyWrap kRecT) stWrapF 100000) endWrap
#guard kernEqI (outSt (Ochr.checkTail 1000 bodyUnbox kRecT) stUnboxF 100000) leafUnbox

/-- The trace and derivation lines, with the leaves marked. -/
def events (t : Term) (st : MState) : List String :=
  (runMachine (Ochr.checkTail 1000 t kRecT) { st with cfg := { derivation := true, trace := true } } 100000).2.2.toList.filterMap
    fun
    | .line s => some s.trimAsciiStart.toString
    | .state _ _ (some (v, _)) _ => some s!"leaf {v}"
    | _ => none

#guard events bodyWrap stWrapF == ["[Read] its declared type is not a copy type: moved out", "leaf MkBox(σ0)"]
-- the refinement in place, the read; no join (one constructor)
#guard events bodyUnbox stUnboxF == ["[Split-one] σ0 := MkBox(σ1) (one constructor, in place)",
  "[Read] its declared type is not a copy type: moved out", "leaf σ1"]

/-! ## Entry conditions -/

#guard wrapOk { stWrapF with tailNext := true } && wrapOk { stWrapF with curTail := true } &&
  wrapOk { stWrapF with typing := false } && wrapOk { stWrapF with tailDecl := some .other }
#guard unboxOk { stUnboxF with tailNext := true } && unboxOk { stUnboxF with curTail := true } &&
  unboxOk { stUnboxF with typing := false } && unboxOk { stUnboxF with tailDecl := some .other }
-- in `clone`'s mode or in place the read copies: the leaves differ, so the plain mode is assumed
#guard !wrapOk { stWrapF with copying := true } && !wrapOk { stWrapF with inPlace := true }
#guard !unboxOk { stUnboxF with copying := true } && !unboxOk { stUnboxF with inPlace := true }
#guard match leavesOf bodyUnbox kRecT { stUnboxF with copying := true } with
  | [(s, _, _)] => (s.env[1]!.binds[1]!.val).exact (mkBox (.abs 1))
  | _ => false
-- the counter of unknowns on entry names the fresh unknown
#guard match leavesOf bodyUnbox kRecT
    { stUnboxF with nextAbs := 2, absTy := #[tyBox, .tNat], absDecl := #[.other, .other] } with
  | [(_, v, _)] => v.exact (.abs 2)
  | _ => false

/-! ## (c): a known scrutinee not ending a body -/

/-- The derivation lines of a declaration of a block. -/
def lines (b : Ochr.Surface.Block) (n : String) : List String :=
  let r := Ochr.Test.runWith none b.name b { derivation := true, trace := true } (located := false)
  match r.rows.find? (·.name == n) with
  | some row => row.trace.toList.filterMap fun | .line s => some s | _ => none
  | none => []

-- `Box`: one constructor, so no [Entry] and no [Join]: the join's drops after an arm are not exercised
#guard (lines DataProbeKnown "UseC").contains "[Return] UseC is defined as it: 2 : Nat, with 0 place(s) held by borrow"
#guard !(lines DataProbeKnown "UseC").any (fun l => l.startsWith "[Join]" || l.startsWith "[Entry]")
-- `Opt`: two constructors and an arm that moves a field: [Entry] at the match, the arm's move, [Join] drops `o`
#guard (lines DataProbeKnown "UseO").contains "[Entry] a place a stuck block would capture"
#guard (lines DataProbeKnown "UseO").contains "[Join] o dropped"
#guard (lines DataProbeKnown "UseO").contains "[Return] UseO is defined as it: 2 : Nat, with 0 place(s) held by borrow"

end Ochr.Meaning.Steps.Form.ColumnBox.Guards
