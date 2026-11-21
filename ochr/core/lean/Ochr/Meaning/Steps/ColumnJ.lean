import Ochr.Meaning.Steps.ColumnIRun
import Ochr.Meaning.Steps.CallGuards

/-!
# The column `J`: the first call (lead15, 2026-11-21; docs/31 D127)

`def I (n : Nat) : Nat := S(#0)` (column `I`), then `def J : Nat := I(Z)`, whose core body is the call
`.call (.const "I") [.zero] false` (what the surface `I(0)` resolves to; `Steps/CallGuards.lean` pins
what the checker does at it).

**The reference never runs the callee's body at a call.** `runT`'s `.call` clause runs the head (the
global's meaning, `K.C.global "I"`), the argument, and applies the head's MEANING (`callOf`). So the
step for the call has two halves, and they come from different places:

- *That the strict run succeeds* comes from the callee's meaning being a member of its function type
  (half (I), through the context: `FundCtx.globals`/`GlobalsOk.mem`): a member applied at member
  arguments reaching a data codomain gives a result (`ApplyMem.app_mem'`, `Closure.closure_apply'`).
  Nothing about the checker's run of the body is used for it.
- *That the result is what the checker computed*: `Out` asks the meaning of the checker's value, which
  the checker computed by its own UNTYPED run of the body in place, to be the reference's result,
  which is the meaning applied. Membership says only that it lies in `Nat`. Here the two are agreed
  by computing both: the meaning applied is `I`'s closure at `0` (`I`'s global means the closure the
  reference's `.fix` clause forms, `GlobalsOk.fn`; column `I` runs its body at every number,
  `fixBodyAt_I`, from the checker's typed generic run), which is `1`; the checker's value is `S(Z)`,
  stated as a fact about the checker (`CallJInv`). In general the agreement needs the untyped run
  simulated against the reference's run in place, and that run related to `callOf` by the frame
  property, whose relation does not hold at a call as stated (docs/31 D127).

What the column assumes: `CallJInv` (the checker's call, stated here, `#guard`ed), `VarNumAInv`,
`InvNumA` (column `I`'s body run; read and judged true, unproved). No frame property and nothing
about the model.
-/

namespace Ochr.Meaning.Steps.Form.ColumnJ

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open ColumnI
open Ochr.Meaning.Steps.Form.CallGuards (bodyJ stJ)

/-! ## A call with unlabelled arguments: the strict test passes, the state is kept -/

/-- `BorrowArgsTyped` holds where no argument carries a label (it asks only of labelled ones). -/
theorem borrowArgsTyped_unlabelled (R : DataRead) (fv : Res) (as : List Res) (s : SState)
    (h : ∀ a ∈ as, a.2.label = none) : BorrowArgsTyped R fv as s := by
  intro i l hi
  exfalso
  unfold refLabelsOf at hi
  rw [List.getElem?_map] at hi
  cases hx : ((as.zip (refsOf R fv.2.m (as.map (·.1)))).filter (·.2))[i]? with
  | none => rw [hx] at hi; cases hi
  | some x =>
    rw [hx] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    have hmem : x ∈ (as.zip (refsOf R fv.2.m (as.map (·.1)))).filter (·.2) := List.mem_of_getElem? hx
    have hx1 : x.1 ∈ as := (List.of_mem_zip (List.mem_filter.mp hmem).1).1
    rw [h _ hx1] at hi; cases hi

theorem mapVals_id (s : SState) : s.mapVals (fun _ v => v) = s := by
  cases s with
  | mk env shape nextLoan lent heldTy heldMem =>
    simp only [SState.mapVals, SState.mk.injEq, and_true]
    conv => rhs; rw [← List.zipIdx_map_fst 0 env]
    congr 1
    funext p
    obtain ⟨fr, fi⟩ := p
    cases fr with
    | mk binds temps =>
      simp only [SFrame.mk.injEq]
      exact ⟨List.zipIdx_map_fst 0 binds, List.zipIdx_map_fst 0 temps⟩

theorem callOfL_unlabelled_state.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) (args : List Res)
    (s s' : SState) (r : Res) (h : callOfL L t fv args s = some (r, s')) (hl : ∀ a ∈ args, a.2.label = none)
    (hr : r.2.label = none) : s' = s := by
  unfold callOfL at h
  have hrl : ∀ x ∈ ((args.zip (telRefsL L t (args.map (·.1)))).filter (·.2)).map (·.1.2.label), x = none := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hl _ (List.of_mem_zip (List.mem_filter.mp hy).1).1
  have hfm : (((args.zip (telRefsL L t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).filterMap id = [] :=
    List.filterMap_eq_nil_iff.mpr fun x hx => by rw [hrl x hx]; rfl
  simp only [hfm, List.foldl_nil] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hfx : ∀ fs : List Sem, ((((args.zip (telRefsL L t (args.map (·.1)))).filter (·.2)).map (·.1.2.label)).zip fs).filterMap
        (fun (lf : Option Nat × Sem) => lf.1.map (·, lf.2)) = [] := fun fs =>
      List.filterMap_eq_nil_iff.mpr fun x hx => by rw [hrl x.1 (List.of_mem_zip hx).1]; rfl
    simp only [hfx, Future.updList]
    exact mapVals_id s
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    cases hr
  · cases h

/-- **A call whose arguments carry no label and whose result carries none leaves the state as it
was**: no argument label is consumed, no final content fixed. -/
theorem callOf_unlabelled_state (R : DataRead) (fv : Res) (args : List Res) (s s' : SState) (r : Res)
    (h : callOf R fv args s = some (r, s')) (hl : ∀ a ∈ args, a.2.label = none) (hr : r.2.label = none) : s' = s := by
  unfold callOf at h
  split at h
  · exact callOfL_unlabelled_state _ _ _ _ _ _ _ h hl hr
  · exact callOfL_unlabelled_state _ _ _ _ _ _ _ h hl hr
  · exact callOfL_unlabelled_state _ _ _ _ _ _ _ h hl hr
  · cases h

/-! ## The reference's run of `J`'s body -/

/-- **The strict run of `I(Z)`** is the call of `I`'s meaning at `0`: the head `.const "I"` runs to the
context's global, `Z` to `0` (no hint read), the borrow test is vacuous, then `callOf`. At any context
whose decision for the call is "neither a statement nor a proof", at any tail flag and hint. -/
theorem runT_bodyJ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) (r : Res) (s' : SState)
    (hfl : K.D.flags (scopeOf s) bodyJ = (false, false))
    (hc : callOf K.dm.read (K.C.global "I") [(.el0 Nat 0, .plain TyM.nat)] s = some (r, s')) :
    runT K ρ φ tl h bodyJ s = some (r, s') := by
  unfold bodyJ
  rw [runT]
  unfold bodyJ at hfl
  simp only [hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have h1 : runT K ρ φ false (TyS.plain TyM.err) (Term.const "I") s = some (K.C.global "I", s) := by
    rw [runT]; rfl
  have h2 : runArgs K ρ φ false (K.C.global "I").2.m [] [Term.zero] s = some ([(.el0 Nat 0, .plain TyM.nat)], s) := by
    rw [runArgs]
    simp only [Bool.false_and]
    rw [runT]
    rfl
  simp only [SM.headOf, Bind.bind, h1]
  rw [h2]
  dsimp only
  rw [if_pos (borrowArgsTyped_unlabelled _ _ _ _ (fun a ha => by simp at ha; subst ha; rfl)), hc]

/-! ## `I`'s meaning: the closure column `I` forms, applied at `0` -/

section
variable {dm : DataModel} {D : Decisions} {ρ : Assignment} {φ : Future}

/-- The binders and codomain the `.fix` clause reads `I`'s signature at, from the empty state. -/
noncomputable def fbI (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : List PBind × PBind :=
  (bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat],
    fixCod (KI dm D φ) ρ φ (emptyState 0) (bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat]) .nat,
    (KI dm D φ).D.typeDecl ((KI dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat)

/-- `I`'s function: the body's run at each argument tuple (stage 1, rank 0: `I` does not recurse). -/
noncomputable def gIf (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : List Sem → Option BodyOut :=
  fixG (KI dm D φ) ρ φ (fbI dm D ρ φ) 1 (emptyState 0) psI outI (piTyAt dm.read 1 psI outI) 0 none bodyI

/-- **`I`'s meaning**: the closure the reference's `.fix` clause forms from the empty state, where a
global's function is formed (`Program.defMeaning`; `fixClo_I`). -/
noncomputable def fI (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ : Future) : Sem :=
  closureAt dm.read 1 φ psI outI (gIf dm D ρ φ)

/-- `fI` is the `.fix` clause's closure for `I` (`column_I_run` runs that clause to it). -/
theorem fixClo_I (hDI : DecTab D stI) :
    fixClo (KI dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat none bodyI = fI dm D ρ φ := by
  obtain ⟨hd1, hd2, hps, hfl⟩ := fixDecI hDI
  have hpd : (KI dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have hsort : fixSort (KI dm D φ) (emptyState 0) [⟨"n"⟩] [.nat] .nat = 1 := hps
  have hty : fixTy (KI dm D φ) ρ φ (emptyState 0) [⟨"n"⟩] [.nat] .nat = piTyAt dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, runDoms_nat _ ρ φ _ hpd, codOf_nat]; rfl
  unfold fixClo
  rw [hty, hsort, runDoms_nat _ ρ φ _ hpd, codOf_nat]
  rfl

/-- **`I`'s function at each number** (column `I`'s body run inside the `.fix` clause, `fixBodyAt_I`):
`S(a)` at `a`, no final. From the checker's successful typed run of `I`'s body at its generic call. -/
theorem gIf_run (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') (a : Nat) :
    ∃ o, gIf dm D ρ φ [.el0 Nat a] = some o ∧ o.result = .el0 Nat (a + 1) ∧ o.finals = [] := by
  obtain ⟨hd1, hd2, -, -⟩ := fixDecI hDI
  have hpd : (KI dm D φ).D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd1]
  have h1 : bindsOf (KI dm D φ) ρ φ (emptyState 0) [.nat] = [(fun _ => .plain TyM.nat, .other)] :=
    bindsOf_nat _ ρ φ _ hpd
  have h2 : (KI dm D φ).D.typeDecl ((KI dm D φ).D.teleDecls (scopeOf (emptyState 0)) [.nat]) .nat = .other := by
    show D.typeDecl (D.teleDecls [] [.nat]) .nat = .other
    simp [Decisions.teleDecls, hd1, hd2]
  exact fixBodyAt_I (dm := dm) (D := D) (ρ := ρ) (φ := φ) hE hS hI hV hN hlow (fbI dm D ρ φ) h1 h2 hDI hk hm htd hD h a

/-- **`I`'s function is total and good at member arguments** (what the closure lemmas ask; the same
argument as `column_I_run`'s membership). -/
theorem gIf_tot (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    ∀ args, DomMembers dm.read psI args →
      ∃ o, gIf dm D ρ φ args = some o ∧ OutGood dm.read psI outI args o ∧ o.finals.length = (psI.filter (·.isRef)).length := by
  intro args ha
  obtain ⟨hlen, hargs⟩ := ha
  match args, hlen with
  | [x], _ =>
    obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
    subst hx
    obtain ⟨o, ho, hr, hf⟩ := gIf_run (dm := dm) (ρ := ρ) (φ := φ) hE hS hI hV hN hlow hDI hk hm htd hD h m
    refine ⟨o, ho, ⟨?_, fun i d hi hd => ?_⟩, by rw [hf]; rfl⟩
    · rw [hr]; exact ⟨m + 1, rfl⟩
    · rcases i with _ | i
      · simp [psI] at hi; subst hi; cases hd
      · simp [psI] at hi

/-- **`I`'s meaning is a member of `Π(n : Nat). Nat`** (half (I)'s supply for the call's success). -/
theorem fI_mem (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') :
    fI dm D ρ φ ∈ₛ[dm.read] piTyAt dm.read 1 psI outI :=
  closure_mem_of_total' dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1)
    (gIf_tot hE hS hI hV hN hlow hDI hk hm htd hD h)

/-- **The call of `I`'s meaning at `Z`**: `1` at `Nat`, the state as it was (no argument is labelled,
the codomain is data). By the closure lemma's application half (`closure_apply'`), whose hypotheses
are those of `I`'s membership (`gIf_tot`), and the body's run at `0` (`gIf_run`). -/
theorem callOf_fI (hE : EvalInv) (hS : SuccInv) (hI : InvSteps) (hV : VarNumAInv) (hN : InvNumA) (hlow : EvalLow)
    (hDI : DecTab D stI) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stI st) (hm : Mode st) (htd : st.tailDecl = none) (hD : DecTab D st')
    (h : Runs (Ochr.eval n true bodyI hint) st bh (v, T?) st') (s : SState) :
    callOf dm.read (fI dm D ρ φ, .plain (piTyAt dm.read 1 psI outI)) [(.el0 Nat 0, .plain TyM.nat)] s =
      some ((.el0 Nat 1, .plain TyM.nat), s) := by
  obtain ⟨o, ho, hr, -⟩ := gIf_run (dm := dm) (ρ := ρ) (φ := φ) hE hS hI hV hN hlow hDI hk hm htd hD h 0
  obtain ⟨s', hs'⟩ := closure_apply' dm.read 1 φ psI outI (gIf dm D ρ φ) ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) (gIf_tot hE hS hI hV hN hlow hDI hk hm htd hD h) [(.el0 Nat 0, .plain TyM.nat)] s o
    ⟨rfl, fun i a d ha hd => by
      rcases i with _ | i
      · simp [psI] at ha hd; subst ha; subst hd; exact ⟨0, rfl⟩
      · simp at ha⟩
    (fun i d hd => by rcases i with _ | i <;> simp [psI] at hd; subst hd; exact Nat.le_refl 1)
    trivial ho
  have hss : s' = s := callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; rfl) rfl
  subst hss
  unfold fI
  rw [hs', hr]
  rfl

end

/-! ## The context of `J`'s body -/

/-- Every global means `f` at `Π(n : Nat). Nat` (only `I` is read); no sealed program, closure value
or deferred type is read through the context's own fields. -/
noncomputable def CJ (R : DataRead) (f : Sem) : CodeMeaning :=
  { global := fun _ => (f, .plain (piTyAt R 1 psI outI)), sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
    pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }

/-- The run's context for `J`'s body: no declarations, `I` meaning `f`, the decisions `D`. -/
noncomputable def KJ (dm : DataModel) (D : Decisions) (f : Sem) : RunCtx := { dm := dm, Γ := [], C := CJ dm.read f, D := D }

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

theorem ok_flags_bodyJ : isOk (ColumnC.Aux.flagsRun bodyJ) (scopeState stJ []) 1000 = true := by decide +kernel
theorem val_flags_bodyJ : outVal (ColumnC.Aux.flagsRun bodyJ) (scopeState stJ []) 1000 = (false, false) := by
  decide +kernel

end Aux

/-- The call is neither a statement nor a proof, at every table aligned with the checker at `stJ`. -/
theorem flags_bodyJ {D : Decisions} (hd : DecTab D stJ) : D.flags [] bodyJ = (false, false) := by
  rw [hd.flags 100 [] bodyJ _ 1000 _
    (Regress.GenNeutralContent.runs_out (ColumnC.Aux.flagsRun bodyJ) _ 1000 Aux.ok_flags_bodyJ), Aux.val_flags_bodyJ]

/-! ## The checker at the call: one fact -/

/-- **The checker's call of `I` at `Z` from `J`'s state** (a fact about the checker alone, assumed; the
machine lane's to read and prove): every successful typed run of `eval` on `I(Z)` from a state with
`stJ`'s kernel (one empty frame, `I`'s global in Σ, no unknown, no label), in the plain mode, not in
tail position, with no reading handed down, outside any private copy, returns `S(Z)` at `Nat` and
ends with `stJ`'s kernel. Inside: the head and the argument are evaluated typed and pushed as
temporaries of frame 0 (main's D115); `callType` gives `Nat` (the call's type: the body's own type is
discarded); `runBodyCore` moves them into a frame pushed on top (`I ↦ .gfn I` unmarked, `n ↦ Z` LAZILY
typed), runs `I`'s body UNTYPED in tail position (the read of `n` returns `Z` with no type and moves
it; `S` returns `S(Z)` at `Nat`), and pops the frame (`Steps/CallGuards.lean`). Its proof needs the
untyped read of a lazily typed binding, which `VarNumAInv` (`b.ty.isSome`) does not cover. -/
def CallJInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Kern stJ st → Mode st → st.tailNext = false → st.tailDecl = none → st.privateDepth = 0 →
    Runs (Ochr.eval n true bodyJ hint) st bh (v, T?) st' →
    v = .succ .zero ∧ T? = some .tNat ∧ Kern stJ st'

namespace Guards

open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk)
open Ochr.Meaning.Steps.Form.CallGuards (startOk)

/-- `CallJInv`'s conclusion at a state, at fuel 100, with the hint `h`. -/
def concl (st : MState) (h : Option Value) : Bool :=
  isOk (Ochr.eval 100 true bodyJ h) st 100000 &&
  outVal (Ochr.eval 100 true bodyJ h) st 100000 == (.succ .zero, some .tNat) &&
  startOk "I" (outSt (Ochr.eval 100 true bodyJ h) st 100000) &&
  (match (outSt (Ochr.eval 100 true bodyJ h) st 100000).globals with
    | [g] => ParGuards.globalOk g "I" bodyI | _ => false)

-- from `stJ`, at any hint (the call reads none); with the typing flag and the tail flag of the term
-- before (`curTail`, which `eval` resets) set either way; with a temporary of a type in frame 0's
-- stored types only (the kernel erases them)
#guard [none, some .tNat, some .tUnit, some (.tRef .tNat)].all fun h =>
  concl stJ h && concl { stJ with typing := true } h && concl { stJ with curTail := true } h
end Guards

/-! ## The step, in the form -/

/-- **The step for the call `I(Z)`, in the form** (`Steps/Form.lean`'s `Sim`): from every reference
state related to the checker's at `J`'s start and good, the strict run of `I(Z)` succeeds, with the
meaning of the checker's value, at its type, and the states after are related. At every context
whose global `I`, called at `0`, returns `1` and keeps the state (`hcall`: `callOf_fI` for `I`'s
meaning), and whose decisions are the checker's at `stJ`. Each conclusion's source:
- the run SUCCEEDS: `hcall` (from `I`'s membership in its type, `closure_apply'`) and the decision
  (`flags_bodyJ`); nothing about the checker's run of the body;
- the RESULT is the meaning of the checker's value: `hcall`'s `1` (the meaning applied, from column
  `I`'s body run at `0`) against `S(Z)` (`CallJInv`: the checker's untyped run of the body);
- the TYPE: `Nat` on both sides (`CallJInv`'s `T?`, `callType`; the reference's codomain at `0`);
- `Pre` and `Rel` after: the kernel is `stJ`'s again and the value in flight a number. -/
theorem callJ_sim (hC : CallJInv) (hI : InvSteps) (K : RunCtx) (ρ : Assignment) (φ : Future)
    (hcall : ∀ s, callOf K.dm.read (K.C.global "I") [(.el0 Nat 0, .plain TyM.nat)] s = some ((.el0 Nat 1, .plain TyM.nat), s))
    (hDJ : DecTab K.D stJ) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stJ st) (hm : Mode st) (htl : st.tailNext = false) (htd : st.tailDecl = none) (hpd : st.privateDepth = 0)
    (h : Runs (Ochr.eval n true bodyJ hint) st bh (v, T?) st') :
    Sim K ρ φ st st' (runT K ρ φ st.tailNext (hintM K ρ hint) bodyJ) v T? := by
  intro s π hp hr _
  obtain ⟨rfl, rfl, hk'⟩ := hC n hint st st' bh v T? hk hm htl htd hpd h
  have hkk : Kern st st' := hk.symm.trans hk'
  have hsc : scopeOf s = [] := by rw [scopeOf_rel hr, ← ColumnC.topReadings_kern hk]; rfl
  have hfl : K.D.flags (scopeOf s) bodyJ = (false, false) := by rw [hsc]; exact flags_bodyJ hDJ
  have hinv : Inv K.D K.Γ (st'.withTempT (.succ .zero) (some .tNat)).norm :=
    hI.pushInert K.D K.Γ st' _ _ (.inl (.succ .zero)) (by rw [← hkk.norm]; exact hp.inv)
  refine ⟨ρ, K.Δ, π, (.el0 Nat 1, .plain TyM.nat), s, ⟨?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩,
    runT_bodyJ K ρ φ _ _ s _ s hfl (hcall s), ?_, fun T hT => ?_, rfl, ?_, ?_⟩
  · rw [hkk.absTy]; exact Nat.le_refl _
  · rw [hkk.nextLoan]; exact Nat.le_refl _
  · show Sem.succ (.el0 Nat 0) = _
    rw [Sem.succ, Sem.asNat_el0]
  · cases hT; exact strAgree_tNat
  · exact (hp.of_kern hkk).withTempT_num (.succ .zero) _ hinv
  · exact rel_withTempT_num (hr.of_kern hkk) (.succ .zero) _

/-! ## The run theorem for `J` -/

/-- **The column `J` at the checker's own decisions**: for every successful typed run of the checker's
`eval` on `I`'s body at its generic call (a state with `stI`'s kernel, as `checkFix` starts it) and on
`J`'s body (a state with `stJ`'s kernel, as `checkDef` starts a constant), the strict run of `J`'s body
from `stJ` read as a reference state, under the fuel-free table at the end of `J`'s run and with `I`
meaning the closure the reference forms for it under the table at the end of `I`'s run, SUCCEEDS with
`1`, a member of `Nat`, at `Nat`; and the checker's value `S(Z)` at `Nat` means it. For every data
model, assignment and future. Assumes 3 facts about the checker: `CallJInv` (stated here), `VarNumAInv`,
`InvNumA` (read and judged true, unproved). -/
theorem column_J_ff (hC : CallJInv) (hV : VarNumAInv) (hN : InvNumA) (dm : DataModel) (ρ : Assignment) (φ : Future)
    {nI : Nat} {cI : Option Value} {sI sI' : MState} {bhI : Nat} {vI : Value} {TI : Option Value}
    (hkI : Kern stI sI) (hmI : Mode sI) (htdI : sI.tailDecl = none)
    (hrI : Runs (Ochr.eval nI true bodyI cI) sI bhI (vI, TI) sI')
    {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stJ st) (hm : Mode st) (htl : st.tailNext = false) (htd : st.tailDecl = none) (hpd : st.privateDepth = 0)
    (h : Runs (Ochr.eval n true bodyJ hint) st bh (v, T?) st') :
    ∃ r s', runT (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ st.tailNext
        (hintM (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ hint) bodyJ
        (SM' (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ stJ) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat ∧ v = .succ .zero ∧ T? = some .tNat ∧
      meanV (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ (.plain TyM.nat) v = r.1 := by
  have hDI' : DecTab (checkerDecisionsFF sI') sI' :=
    decTab_ff sI' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' sI')
  have hDI : DecTab (checkerDecisionsFF sI') stI :=
    DecTab.of_kern hkI.symm (Machine.decBack _ sI sI' hDI' (grows_eval _ _ _ _ sI bhI _ sI' hrI))
  have hD : DecTab (checkerDecisionsFF st') st' :=
    decTab_ff st' _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st')
  have hDJ : DecTab (checkerDecisionsFF st') stJ :=
    DecTab.of_kern hk.symm (Machine.decBack _ st st' hD (grows_eval _ _ _ _ st bh _ st' h))
  obtain ⟨rfl, rfl, -⟩ := hC n hint st st' bh v T? hk hm htl htd hpd h
  have hsc : scopeOf (SM' (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ stJ) = [] := by
    rw [scopeOf_sstate']; rfl
  refine ⟨_, _, runT_bodyJ _ ρ φ _ _ _ _ _ (by rw [hsc]; exact flags_bodyJ hDJ)
    (callOf_fI Machine.evalInvR succInv Machine.invSteps hV hN Machine.evalLow hDI hkI hmI htdI hDI' hrI _),
    rfl, ⟨1, rfl⟩, rfl, rfl, rfl, ?_⟩
  show Sem.succ (.el0 Nat 0) = _
  rw [Sem.succ, Sem.asNat_el0]

/-- **`checkDef`'s acceptance of the constant `J`, inverted down to its body's run** (a fact about the
checker, assumed; the machine lane's): where `checkDef defJ` succeeds from the state holding only Σ
with `I`'s global (as `ProgState.step` starts an item), it ran the body's typed `eval` at the goal
`Nat` (as the hint) from a state with `stJ`'s kernel, in the plain mode, not in tail position, with no
reading handed down, outside any private copy (`Steps/CallGuards.lean`: the start state recorded on
the surface probe, and the trace of `I` then `J`). -/
def ConstRunJ : Prop :=
  ∀ (fuel : Nat) (st₁ : MState), Runs (checkDef CallGuards.defJ) { globals := [ColumnI.gI] } fuel () st₁ →
    ∃ (n : Nat) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
      Kern stJ st ∧ Mode st ∧ st.tailNext = false ∧ st.tailDecl = none ∧ st.privateDepth = 0 ∧
        Runs (Ochr.eval n true bodyJ (some .tNat)) st bh (v, T?) st'

/-- **The column `J` from the checker's acceptance of `I` and of `J`**: where `checkDef defI` succeeds
from the empty state and `checkDef defJ` from the state holding `I`'s global, there are runs of the two
bodies such that the strict run of `J`'s body succeeds with `1`, a member of `Nat`, and the checker's
value means it. Assumes 5 facts about the checker: `FixRunI`, `ConstRunJ`, `CallJInv`, `VarNumAInv`,
`InvNumA`. -/
theorem column_J_def (hFI : FixRunI) (hFJ : ConstRunJ) (hC : CallJInv) (hV : VarNumAInv) (hN : InvNumA)
    (dm : DataModel) (ρ : Assignment) (φ : Future) {fuelI fuelJ : Nat} {st₁ st₂ : MState}
    (haccI : Runs (checkDef ParGuards.defI) {} fuelI () st₁) (haccJ : Runs (checkDef CallGuards.defJ) { globals := [ColumnI.gI] } fuelJ () st₂) :
    ∃ (sI' st' : MState) (v : Value) (r : Res) (s' : SState),
      runT (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ false
        (hintM (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ (some .tNat)) bodyJ
        (SM' (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ stJ) = some (r, s') ∧
      r.1 = .el0 Nat 1 ∧ r.1 ∈ₛ[dm.read] TyM.nat ∧ r.2.m = TyM.nat ∧ v = .succ .zero ∧
      meanV (KJ dm (checkerDecisionsFF st') (fI dm (checkerDecisionsFF sI') ρ φ)) ρ φ (.plain TyM.nat) v = r.1 := by
  obtain ⟨nI, sI, sI', bhI, vI, TI, hkI, hmI, htdI, hrI⟩ := hFI fuelI st₁ haccI
  obtain ⟨n, st, st', bh, v, T?, hk, hm, htl, htd, hpd, h⟩ := hFJ fuelJ st₂ haccJ
  obtain ⟨r, s', hx, h1, h2, h3, h4, -, h6⟩ := column_J_ff hC hV hN dm ρ φ hkI hmI htdI hrI hk hm htl htd hpd h
  rw [htl] at hx
  exact ⟨sI', st', v, r, s', hx, h1, h2, h3, h4, h6⟩

end Ochr.Meaning.Steps.Form.ColumnJ
