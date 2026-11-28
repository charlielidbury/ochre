import Ochr.Meaning.Steps.MasterSeq
import Ochr.Meaning.Steps.HintSites

/-!
# The master induction's UNTYPED `;` and `let`, in general, at every tail flag (lead25, lead26, 2026-11-22; docs/31 D176, D180)

An untyped run (a callee's body at a call, `runBody`; a type's computation) of `u; w` or `let x = u; w`. The checker's
untyped `evalCore` runs the first term with no hint, as the typed one does, and since main's D124 (merged by
machine9) hands the tail the hint in tail position only, as the reference does (`tailHint`, D156). The inversions
`SeqInvDU`, `LetInvDUn`, `LetCallInvU` were restated at the merge to run the tail at `if st.curTail then hint else none`,
so D124's facts at these sites (`HintSites.UntypedSeqTailNoHint`, `UntypedLetTailNoHint`, proved) are carried by the
inversions and no step uses them. In tail position the tail runs at the hint on both sides after the first sub-run's
extension of the assignment, and is moved back by `runT_congrA` with `hintM_congrA` (the hint's meaning is kept, since
`EvalAt` assumes its unknowns below the counter, `HintBelow`, D179).

* `seqInvDU` (a fact about the checker alone, PROVED here: `seqInvD`'s proof at an untyped run);
* `seq_coreU` / `stepSeq_untyped`, at every tail flag: ASSUMES the typed step's three (`SeqTailDecl`, `DropValueG`,
  `ValsCongrA`) and `FundCtx`;
* `letInvDUn` (PROVED: `letInvD`'s proof at an untyped run, the right-hand side not a call);
* `letIn_coreU` / `stepLetIn_untyped`, at every tail flag, the right-hand side not a call: ASSUMES the typed step's
  four (`LetTailDecl`, `LetPushG`, `LetDropG`, `ValsCongrA`) and `FundCtx`;
* `stepSeq_unerased`, `stepLetIn_unerased`: typed or untyped, the same facts;
* a call's right-hand side may have its type deferred (`lazyTy`, D82): its inversion `LetCallInvU` (checker) is PROVED
  (`letCallInvU`, restated at D183 to say the record the binding reads is the one the call's run ends with);
  `LetLazyPushG` as lead25 stated it was FALSE (D180), restated with the link `paramTy … = ru.2`, which the call's own
  `EvalAt` now concludes (`OutL`'s `LaterOk`, the lead's ruling, D183); `letCall_coreU` / `stepLetIn_untypedCall`
  PROVED from them (5 facts); `stepLetIn_unerasedAll`: every `let`, typed or untyped (5 facts).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- D124 (main, merged by machine9): the untyped run's tail hint, `if typed || !tail then none else hint` at an
untyped run, is the hint in tail position and none out of it. -/
theorem untypedTailHint_eq (c : Bool) (hint : Option Value) :
    (if (false || !c) = true then none else hint) = (if c = true then hint else none) := by
  cases c <;> rfl

/-- **`evalCore` of an UNTYPED `u; w`, the discard exposed**: as `SeqInvD`, the tail run at the hint. -/
def SeqInvDU : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value)
    (D : Decisions),
    DecTab D st' →
    Runs (Ochr.evalCore (n + 1) false (.seq u w) hint) st bh (v, T?) st' →
    ∃ (st₁ s₄ stW : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ bh₃ bh₂ : Nat),
      Runs (Ochr.eval n false u none) st bh₁ (v₀, T₀) st₁ ∧ DecTab D st₁ ∧
      Runs (Ochr.dropValue n v₀ T₀) st₁ bh₃ () s₄ ∧ DecTab D s₄ ∧
      Form.Kern s₄ stW ∧ Form.ModeEq s₄ stW ∧ stW.tailDecl = st.curDecl ∧ stW.tailNext = st.curTail ∧
      Runs (Ochr.eval n false w (if st.curTail then hint else none)) stW bh₂ (v, T?) st'

/-- **`SeqInvDU`, PROVED** (`seqInvD`'s proof). -/
theorem seqInvDU : SeqInvDU := by
  intro n u w hint st st' bh v T? D hD h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨⟨v₀, T₀⟩, s₃, b₃, hu, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨_, s₄, b₄, hdv, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  unfold demand at h₂
  peel h₂
  -- D124: the tail's hint is the sequence's only in tail position
  rw [untypedTailHint_eq] at h₂
  simp only at hdv
  have hD₄ : DecTab D s₄ := DecTab.back hD ((TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).trans
    (Runs.grows (grows_eval _ _ _ _) h₂))
  refine ⟨s₃, s₄, { s₄ with tailDecl := s₁.curDecl, tailNext := s₁.curTail, wantTy := s₁.wantHere }, v₀, T₀, _, _, b₄,
    hu, ?_, hdv, hD₄,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, h₂⟩
  exact DecTab.back hD₄ (Runs.grows (grows_dropValue _ _ _) hdv)

/-- **`evalCore` of an UNTYPED `let` whose right-hand side is not a call**: as `LetInvD`, `u` run untyped with no
hint, the tail at the hint. (A call's right-hand side may have its type deferred, `lazyTy`: `LetCallInvU`.) -/
def LetInvDUn : Prop :=
  ∀ (n : Nat) (h : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    (∀ f as hd, u ≠ .call f as hd) →
    st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) false (.letIn h u w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r : Value) (T₀ : Option Value) (p : Bool)
      (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Form.ModeEq st st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ stB.tailDecl = st.curDecl ∧
      Runs (Ochr.eval n false u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      D.declOf (DecideScope.topReadings st) u = du ∧
      Kern { st₁ with env := Env.pushBindE st₁.env h T₀ v₀ p du } stB ∧ Form.ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n false w (if st.curTail then hint else none)) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ Form.ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂ ∧ st₀.wantTy = true ∧ st₀.deferCallTy = st.deferCallTy

/-- A term that is not a call does not match `.call`. -/
theorem isCall_false {u : Term} (hnc : ∀ f as hd, u ≠ .call f as hd) :
    (match u with | .call _ _ _ => true | _ => false) = false := by
  cases u with
  | call f as hd => exact absurd rfl (hnc f as hd)
  | _ => rfl

set_option maxHeartbeats 4000000 in
/-- **`LetInvDUn`, PROVED** (`letInvD`'s proof; the right-hand side not a call, so no type is deferred). -/
theorem letInvDUn : LetInvDUn := by
  intro n x u w hint st st' bh v T? D hnc htn htd hD h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_evalCore _ _ _ _) h)
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨du, s₂, b₃, hdu, h₁⟩ := Runs.bind_inv h
  clear h
  have hs2 := runs_keep (keep_withLive _ ((decideKeep n).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdu
  subst hs2
  have hncall := isCall_false hnc
  unfold demand at h₁
  rw [runs_modify_bind] at h₁
  simp only [Bool.not_false, Bool.true_and] at h₁
  -- D132: the right-hand side is not an untyped call, so the pre-pass is not asked (`erasedU := false`)
  rw [if_pos (by simp [hncall])] at h₁
  peel h₁
  rw [if_neg (by simp [hncall])] at h₁
  peel h₁
  obtain ⟨⟨v₀, T₀⟩, s₃, b₄, hu, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  peel h₂
  obtain ⟨du', s₄, b₅, hrd, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  obtain ⟨rfl, rfl⟩ := runs_refineDecl_inv hrd
  obtain ⟨fl, s₅, b₆, hgf, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
  obtain ⟨_, s₆, b₇, hpb, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  have hs6 := runs_pushBind_inv hpb
  subst hs6
  simp only [Bool.false_eq_true, if_false, Bool.false_and] at h₅
  rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
  peel h₅
  try simp only [if_true, ite_true, Bool.false_eq_true, if_false] at h₅
  -- D124: the tail's hint is the `let`'s only in tail position
  rw [untypedTailHint_eq] at h₅
  obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
  clear h₅
  obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
  clear h₆
  obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
  obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
  clear h₇
  have hs9 := runs_pushTemp_inv hpt
  subst hs9
  obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
  clear h₈
  unfold setFlags at h₉
  rw [runs_modify_bind] at h₉
  obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
  clear h₉
  obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨rfl, rfl⟩ := hvt
  obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
  have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
  have hk3 := kern_popTemp_withTempT _ _ T? hback
  refine ⟨du', { s₂ with wantTy := true }, s₃,
    { s₃ with env := Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du', callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
    s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, b₃, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, ?_, ?_, rfl, hw',
    hdr, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact decTab_declOf_at hDst hdu
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
      ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
        (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
  · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))

/-- **An untyped deferred call that returns no type records a Π written as one** (checker, NEW, lead28, docs/31 D188,
D190; UNREAD): the gap under `LetCallInvU` (machine11's (a) and (b) together). From a state meeting the invariant, an
untyped run of a call with its type wanted and the deferral flag set (how an untyped `let` of a call starts it) that
returns no type ends with a record `(P, ws)`, `P` a Π-type written as one. (Restated at main's D130 by machine12: the
premise "the record clear" is gone; `evalAt` clears the record when the evaluation starts.) (a) `callFn` sets the record
on every path that returns no type (machine11, read TRUE); (b) the record is `funType fv fT` for the head's value and
the type its wanted run returned: a function value's by (K) at a stored type and by the deferred type's evaluation
otherwise (`EvalKindW`), a global's own by (K)'s part on globals, a closure's own `.tPi`; a neutral head (an unknown, a
sealed program) at a type not written as a Π is the one case (K) does not reach, which the typed check never calls
(`callType`) and no accepted program's run records (`lake exe sweep`: 70,742 states with a record, every one a Π). -/
def LaterPiG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (n : Nat) (f : Term) (as : List Term) (hd : Bool) (st₀ st₁ : MState) (bh : Nat)
    (v : Value),
    Pre K ρ st₀ → st₀.wantTy = true → st₀.deferCallTy = true →
    Runs (Ochr.eval n false (.call f as hd) none) st₀ bh (v, none) st₁ →
    ∃ caps hs ds cod rd ws, st₁.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws)

/-- The top frame's last binding with its type deferred, as the checker's untyped `let` records a call's type
(`lazyTy := (P, ws, |ds|)`, D82); `none` leaves the environment. -/
def _root_.Ochr.Env.setLazyTop (E : Env) : Option (Value × List Value × Nat) → Env
  | none => E
  | some z => E.modify (E.size - 1) fun fr =>
      { fr with binds := fr.binds.modify (fr.binds.size - 1) fun b => { b with lazyTy := some z } }

/-- **`evalCore` of an UNTYPED `let` whose right-hand side is a call** (a fact about the checker alone; PROVED,
`letCallInvU`): as `LetInvDUn`, except that, where the pre-pass does not erase the call, `u` runs
with the deferral flag set (`deferCallTy`, outside the kernel) and, where its
type comes back unknown, the new binding takes its type from the pair the call recorded (`lazyTy`, `setLazyTop`):
exactly where the record holds a Π-type (restated, lead26, D183: the record is read only right after the call, from
the state its run ends in, as the checker reads it). Restated at main's D130 and D132 (machine12): the `let` no longer
clears the record before the call (`evalAt` does, when the call's evaluation starts), so "the record clear at the
call's entry" is gone; and a call the pre-pass erases (one returning a type or a proof) is not deferred: it runs with
the flag as the `let` found it, and the binding takes the type the call returned (the second disjunct). -/
def LetCallInvU : Prop :=
  ∀ (n : Nat) (h : Hint) (f : Term) (as : List Term) (hd : Bool) (w : Term) (hint : Option Value) (st st' : MState)
    (bh : Nat) (v : Value) (T? : Option Value) (D : Decisions),
    st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) false (.letIn h (.call f as hd) w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r : Value) (T₀ : Option Value) (p : Bool)
      (lz : Option (Value × List Value × Nat)) (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Form.ModeEq st st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ stB.tailDecl = st.curDecl ∧
      Runs (Ochr.eval n false (.call f as hd) none) st₀ bh₁ (v₀, T₀) st₁ ∧
      D.declOf (DecideScope.topReadings st) (.call f as hd) = du ∧
      ((st₀.deferCallTy = true ∧
        ((lz = none ∧ ∀ caps hs ds cod rd ws, T₀ = none → st₁.callTyLater ≠ some (.tPi caps (.pi hs ds cod) rd, ws)) ∨
          ∃ caps hs ds cod rd ws, T₀ = none ∧ st₁.callTyLater = some (.tPi caps (.pi hs ds cod) rd, ws) ∧
          lz = some (.tPi caps (.pi hs ds cod) rd, ws, ds.length))) ∨
        (st₀.deferCallTy = st.deferCallTy ∧ lz = none)) ∧
      Kern { st₁ with env := (Env.pushBindE st₁.env h T₀ v₀ p du).setLazyTop lz } stB ∧ Form.ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n false w (if st.curTail then hint else none)) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ Form.ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂ ∧ st₀.wantTy = true

/-- The record the `let` reads is the call's. -/
theorem later_eq {α : Type} {T : Option Value} {a : Option α} {y : α}
    (h : (if T.isNone = true then a else none) = some y) : a = some y := by
  cases T with
  | none => exact h
  | some _ => simp at h

/-- A deferred type is recorded only where the call's value came back with no type. -/
theorem none_of_later {α : Type} {T : Option Value} {a : Option α} {y : α}
    (h : (if T.isNone = true then a else none) = some y) : T = none := by
  cases T with
  | none => rfl
  | some _ => simp at h

set_option maxHeartbeats 4000000 in
/-- **`LetCallInvU`, PROVED** (lead26; `letInvDUn`'s proof with the deferral: the flag set before the call, the type
recorded where the call's value came back with none and the recorded head is a Π-type, `setLazyTop`). -/
theorem letCallInvU : LetCallInvU := by
  intro n x f as hd w hint st st' bh v T? D htn htd hD h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_evalCore _ _ _ _) h)
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨du, s₂, b₃, hdu, h₁⟩ := Runs.bind_inv h
  clear h
  have hs2 := runs_keep (keep_withLive _ ((decideKeep n).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdu
  subst hs2
  unfold demand at h₁
  rw [runs_modify_bind] at h₁
  simp only [Bool.not_false, Bool.true_and] at h₁
  -- D132: whether the pre-pass erases the call (`erasedU`): asked only where the reading is not a conflict, and asking
  -- leaves the state as it was. Not erased (by the conflict or by the pre-pass): the deferred path below, the same in
  -- both; erased: not deferred, no record read, the binding at the type the call returned
  by_cases hcf : du = .conflict
  case' pos =>
    rw [if_pos (by simp [hcf])] at h₁
    peel h₁
  case' neg =>
    rw [if_neg (by clear h₁ hdu; cases du <;> first | exact absurd rfl hcf | simp)] at h₁
    obtain ⟨pf, s', b', hpf, h₁'⟩ := Runs.bind_inv h₁
    have := runs_keep (keep_preFlags _ _) hpf
    subst this
    clear h₁ hpf
    peel h₁'
    generalize (Option.map (fun x => x.fst) pf).getD false = eU at h₁'
    have h₁ := h₁'
    clear h₁'
    cases eU
    case true =>
      -- the pre-pass erases the call: not deferred (`isCall` false), no record read, the binding at the type returned
      rw [if_neg (by simp)] at h₁
      peel h₁
      obtain ⟨⟨v₀, T₀⟩, s₃, b₄, hu, h₂⟩ := Runs.bind_inv h₁
      clear h₁
      rw [runs_get_bind] at h₂
      rw [runs_modify_bind] at h₂
      obtain ⟨du', s₄, b₅, hrd, h₃⟩ := Runs.bind_inv h₂
      clear h₂
      obtain ⟨rfl, rfl⟩ := runs_refineDecl_inv hrd
      obtain ⟨fl, s₅, b₆, hgf, h₄⟩ := Runs.bind_inv h₃
      clear h₃
      obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
      obtain ⟨_, s₆, b₇, hpb, h₅⟩ := Runs.bind_inv h₄
      clear h₄
      have hs6 := runs_pushBind_inv hpb
      subst hs6
      simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false, ite_false] at h₅
      peel h₅
      rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
      peel h₅
      try simp only [if_true, ite_true, Bool.false_eq_true, if_false] at h₅
      rw [untypedTailHint_eq] at h₅
      obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
      clear h₅
      obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
      clear h₆
      obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
      obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
      clear h₇
      have hs9 := runs_pushTemp_inv hpt
      subst hs9
      obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
      clear h₈
      unfold setFlags at h₉
      rw [runs_modify_bind] at h₉
      obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
      clear h₉
      obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
      simp only [Prod.mk.injEq] at hvt
      obtain ⟨rfl, rfl⟩ := hvt
      obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
      have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
      have hk3 := kern_popTemp_withTempT _ _ T? hback
      refine ⟨du', { s₂ with wantTy := true }, s₃,
        { s₃ with env := (Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du').setLazyTop none, callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
        s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, none, _, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, (.inr ⟨rfl, rfl⟩), ?_, ?_,
        rfl, hw', hdr, ?_, ?_, ?_, ?_, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact decTab_declOf_at hDst hdu
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
          ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
            (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
      · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))
  all_goals (
    rw [if_pos (by simp)] at h₁
    rw [runs_modify_bind] at h₁
    obtain ⟨⟨v₀, T₀⟩, s₃, b₄, hu, h₂⟩ := Runs.bind_inv h₁
    clear h₁
    rw [runs_get_bind] at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨du', s₄, b₅, hrd, h₃⟩ := Runs.bind_inv h₂
    clear h₂
    obtain ⟨rfl, rfl⟩ := runs_refineDecl_inv hrd
    obtain ⟨fl, s₅, b₆, hgf, h₄⟩ := Runs.bind_inv h₃
    clear h₃
    obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
    obtain ⟨_, s₆, b₇, hpb, h₅⟩ := Runs.bind_inv h₄
    clear h₄
    have hs6 := runs_pushBind_inv hpb
    subst hs6
    simp only [Bool.not_false, Bool.true_and] at h₅
    generalize hL : (if (v₀, T₀).snd.isNone = true then s₃.callTyLater else none) = later at h₅
    rcases later with _ | ⟨P, ws⟩
    · simp only at h₅
      rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
      peel h₅
      try simp only [if_true, ite_true, Bool.false_eq_true, if_false] at h₅
      rw [untypedTailHint_eq] at h₅
      obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
      clear h₅
      obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
      clear h₆
      obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
      obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
      clear h₇
      have hs9 := runs_pushTemp_inv hpt
      subst hs9
      obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
      clear h₈
      unfold setFlags at h₉
      rw [runs_modify_bind] at h₉
      obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
      clear h₉
      obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
      simp only [Prod.mk.injEq] at hvt
      obtain ⟨rfl, rfl⟩ := hvt
      obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
      have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
      have hk3 := kern_popTemp_withTempT _ _ T? hback
      refine ⟨du', { s₂ with wantTy := true, deferCallTy := true }, s₃,
        { s₃ with env := (Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du').setLazyTop none, callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
        s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, none, _, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, (.inl ⟨rfl, .inl ⟨rfl, fun caps hs ds cod rd ws hT e => by subst hT; simp at hL; rw [hL] at e; cases e⟩⟩), ?_, ?_,
        rfl, hw', hdr, ?_, ?_, ?_, ?_, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact decTab_declOf_at hDst hdu
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
          ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
            (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
      · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))
    · have hT : T₀ = none := none_of_later hL
      simp only at h₅
      split at h₅
      · rename_i caps hs ds cod rd
        simp only [topIdx, modifyFrame, bind_assoc] at h₅
        peel h₅
        rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
        peel h₅
        try simp only [if_true, ite_true, Bool.false_eq_true, if_false] at h₅
        rw [untypedTailHint_eq] at h₅
        obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
        clear h₅
        obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
        clear h₆
        obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
        obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
        clear h₇
        have hs9 := runs_pushTemp_inv hpt
        subst hs9
        obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
        clear h₈
        unfold setFlags at h₉
        rw [runs_modify_bind] at h₉
        obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
        clear h₉
        obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
        simp only [Prod.mk.injEq] at hvt
        obtain ⟨rfl, rfl⟩ := hvt
        obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
        have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
        have hk3 := kern_popTemp_withTempT _ _ T? hback
        refine ⟨du', { s₂ with wantTy := true, deferCallTy := true }, s₃,
          { s₃ with env := (Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du').setLazyTop (some (Value.tPi caps (.pi hs ds cod) rd, ws, ds.length)), callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
          s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, some (Value.tPi caps (.pi hs ds cod) rd, ws, ds.length), _, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, (.inl ⟨rfl, .inr ⟨caps, hs, ds, cod, rd, ws, hT, later_eq hL, rfl⟩⟩), ?_, ?_,
          rfl, hw', hdr, ?_, ?_, ?_, ?_, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact decTab_declOf_at hDst hdu
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
            ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
              (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
        · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))
      · rename_i hnotPi
        rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
        peel h₅
        try simp only [if_true, ite_true, Bool.false_eq_true, if_false] at h₅
        rw [untypedTailHint_eq] at h₅
        obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
        clear h₅
        obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
        clear h₆
        obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
        obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
        clear h₇
        have hs9 := runs_pushTemp_inv hpt
        subst hs9
        obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
        clear h₈
        unfold setFlags at h₉
        rw [runs_modify_bind] at h₉
        obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
        clear h₉
        obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
        simp only [Prod.mk.injEq] at hvt
        obtain ⟨rfl, rfl⟩ := hvt
        obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
        have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
        have hk3 := kern_popTemp_withTempT _ _ T? hback
        refine ⟨du', { s₂ with wantTy := true, deferCallTy := true }, s₃,
          { s₃ with env := (Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du').setLazyTop none, callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
          s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, none, _, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, (.inl ⟨rfl, .inl ⟨rfl, fun caps hs ds cod rd ws hT e => by
            subst hT; simp at hL; rw [hL] at e; cases e
            first | exact hnotPi _ _ _ _ _ rfl | exact (hnotPi _ _ _ _ _ rfl).elim | simp_all⟩⟩), ?_, ?_,
          rfl, hw', hdr, ?_, ?_, ?_, ?_, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact decTab_declOf_at hDst hdu
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
            ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
              (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
        · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))))

end Ochr.Meaning.Steps.Machine

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- The tail's hint on both sides: the form's own in tail position, none out of it (the reference's `tailHint`,
D156; the checker's untyped run since main's D124). -/
theorem tailHint_hintM (K : RunCtx) (ρ : Assignment) (c : Bool) (hint : Option Value) :
    tailHint c (hintM K ρ hint) = hintM K ρ (if c then hint else none) := by
  cases c <;> rfl

theorem hintBelow_ite {hint : Option Value} {n : Nat} (c : Bool) (h : HintBelow hint n) :
    HintBelow (if c then hint else none) n := by
  cases c
  · exact hintBelow_none n
  · exact h

-- `hintM_of_none`, `hintM_of_some`, `hintM_congrA`: moved to `Master.lean` (lead48: the goal clause rests on them).

/-- **The push of a binding whose type is deferred** (mixed; STATED, not proved; with `LetCallInvU`, what the
untyped `let` of a call needs beyond `LetPushG`): as `LetPushG`, the value's type unknown (`T₀ = none`) and the new
binding recording the call's type (`lazyTy`), which the relation reads through `CodeMeaning.paramTy` (`Env.hintAt`).
RESTATED (lead26, docs/31 D180): as lead25 stated it, with no link between the recorded type `z` and the reference's
result type `ru.2`, it was FALSE (a recorded `P` that is not a Π-type reads `paramTy = err`, while `ru.2` is the
call's type; `Rel.skel` compares the binding's type code). The link `hz` is what the call's step must hand on (the
ruling asked in D180). RESTATED again (lead27, docs/31 D185): the value fits its reading at the new binding
(`FitsAt`), the hypothesis `LetPushG` lacked too. -/
def LetLazyPushG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ stB : MState) (v₀ : Value)
    (x : Hint) (p : Bool) (du : DeclInfo) (z : Value × List Value × Nat) (ru : Res) (s₁ : SState),
    K.M.paramTy ρ z.1 z.2.1 z.2.2 = ru.2 →
    0 < st₁.env.size →
    Pre K ρ (st₁.withTempT v₀ none) → Rel K ρ φ π (st₁.withTempT v₀ none) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1 → ru.2.label = (Value.heldLabel v₀).map π →
    Strict.GoodRes K.dm.read ru → Strict.LabOk K.dm s₁ ru → LoU s₁ ru.2.label →
    FitsAt K.D K.Γ (DecideScope.topReadings st₁) du v₀ →
    Kern { st₁ with env := (Env.pushBindE st₁.env x none v₀ p du).setLazyTop (some z) } stB →
    Pre K ρ stB ∧ Rel K ρ φ π stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })

section
variable {K : RunCtx} {φ : Future}

/-- **An untyped, unerased `u; w`, at `evalCore`, in general, at every tail flag** (docs/31 D180). The inversion
(`Machine.seqInvDU`, restated at the merge of main's D124) runs the tail at the hint in tail position and at none out
of it, which is the reference's `tailHint`; in tail position the tail's run is moved back across the first sub-run's
extension by `runT_congrA` and `hintM_congrA` (the hint's unknowns are below the counter, `HintBelow`). -/
theorem seq_coreU (hST : SeqTailDecl K.D) (hDV : DropValueG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {u w : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.seq u w) (fun st => 0 < st.env.size) (· = false) := by
  intro st st' typed hint v T? s π hne hty hm _ htn htd hcd hp hrt hr hS hv hab hhb hnh hfl hok hD bh h
  subst hty
  obtain ⟨st₁, s₄, stW, v₀, T₀, bh₁, bh₃, bh₂, hru, hD₁, hdv, -, hkW, hmeW, htdW, htnW, hrw⟩ :=
    Machine.seqInvDU m u w hint st st' bh v T? K.D hD h
  -- the tail's hint, on both sides: the sequence's in tail position, none out of it
  have hth := tailHint_hintM K ρ st.curTail hint
  have hHb := hintBelow_ite st.curTail hhb
  have habu : u.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have habw : w.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  -- the reference's run of the sequence succeeds (the untyped entry condition)
  have hok' := hok rfl
  rw [runT_seq _ _ u w s hfl] at hok'
  have hoku : (runT K ρ φ false (.plain TyM.err) u s).isSome := by
    revert hok'; simp only [bind, Option.bind]; cases runT K ρ φ false (.plain TyM.err) u s <;> simp
  -- the step for `u`, from the entry state itself
  have hOu := (ih m (by omega) K.Δ ρ).1 u st st₁ false none v₀ T₀ s π hm (fun e => by cases e) hne (.inl htd) hp hrt hr hS
    hv.1 habu (hintBelow_none _) hnhu (fun _ => by rw [htn]; exact hoku) hD₁ bh₁ hru
  replace hOu := outGK_of_outLK hOu
  rw [htn] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁, hglu⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  -- the discard, on both sides
  obtain ⟨hdok, ⟨hga, hgl⟩, hP₄, hR₄, hK₄, hg₄⟩ := hDV { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ s₄ v₀ T₀ ru s₁ m bh₃
    (by rw [hK₁.size]; exact hne) hp₁ hr₁ hS₁ hmu hlu hdv
  have hS₂ : Strict.SGood K.dm K.Γ φ (discardEnd ru.2 s₁) := by
    unfold discardEnd; unfold DiscardOk at hdok; split
    · rename_i l hl; rw [hl] at hdok; exact Strict.endLabel_sgood hS₁ _ hdok
    · exact hS₁
  -- the hint the tail is handed means the same at the extended context
  have hHM : hintM { K with Δ := Δ₁ } ρ₁ (if st.curTail then hint else none) =
      hintM K ρ (if st.curTail then hint else none) := hintM_congrA hHb he₁.agree
  -- the reference's tail succeeds
  have hokw : (runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w (discardEnd ru.2 s₁)).isSome := by
    revert hok'; simp only [bind, Option.bind]; rw [hxu']; simp only
    rw [SM.guardMod_of (show DiscardOk K φ ru.2 s₁ from hdok)]; simp only
    rw [hth]; exact id
  -- the step for `w`, at the extended context
  have hKW : Kept st stW := (hK₁.trans hK₄).trans (Kept.of_kern hkW hmeW)
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) :=
    .inr (by rw [htdW, hcd, hKW.top, hST])
  have habW : st.absTy.size ≤ stW.absTy.size := by
    rw [← hkW.absTy]; exact Nat.le_trans he₁.abs hga
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    obtain ⟨a, d⟩ := he₁.agree σ (habw σ hσ)
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stW st' false _ v T? (discardEnd ru.2 s₁) π₁
    (hm.of_modeEq hKW.mode) (fun e => by cases e) (by rw [hKW.size]; exact hne) htdW'
    (hP₄.of_kern hkW) (hrt.move hKW.stack habW fun σ hσ => (he₁.agree σ hσ).1) (hR₄.of_kern hkW) hS₂
    (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habW) (hHb.mono habW) hnhw
    (fun _ => by rw [htnW, hHM, ← runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hokw) hD bh₂ hrw
  replace hOw := outGK_of_outLK hOw
  rw [htnW, hHM] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, he₂, hxw, hmw, haw, hlw, hp₂, hr₂, hglw⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w (discardEnd ru.2 s₁) =
      some (rw', s₃) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    ((he₁.grow hga hgl).congr rfl rfl hkW.absTy hkW.nextLoan).trans he₂
  have hgoal : hintM { K with Δ := Δ₂ } ρ₂ st'.goal = hintM K ρ st.goal := by
    rw [hglw, ← hkW.goal, hg₄]; exact hglu
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hp₂, hr₂, hgoal⟩, hKW.trans hK₂⟩
  -- the reference's sequence: its tail runs at the tail's hint
  rw [runT_seq _ _ u w s hfl]
  simp only [bind, Option.bind]
  rw [hxu']
  simp only
  rw [SM.guardMod_of (show DiscardOk K φ ru.2 s₁ from hdok)]
  simp only
  rw [hth]; exact hxw'

/-- **The step for an untyped `;`, the table reading it as decided data, in general, at every tail flag**, with
what the run keeps (docs/31 D180). ASSUMES 3 facts: `SeqTailDecl` (table), `DropValueG` (part checker, part model),
`ValsCongrA` (model); and `Strict.FundCtx K`. The inversion (`Machine.seqInvDU`) is proved; D124's fact at this site
(`HintSites.UntypedSeqTailNoHint`, proved) is no longer used: the restated inversion carries it. -/
theorem stepSeq_untyped (hST : SeqTailDecl K.D) (hDV : DropValueG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.seq u w)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) (· = false) := by
  intro n ih Δ ρ u w
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.seq u w)
      (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) (· = false) :=
    fun st st' typed hint v T? s π hP => seq_coreU (K := { K with Δ := Δ }) hST hDV hVC ⟨hc.globals, hc.sorts⟩ ih
      st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk _ ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

/-- **An untyped, unerased `let` whose right-hand side is not a call, at `evalCore`, in general, at every tail
flag** (docs/31 D180; as `seq_coreU`). -/
theorem letIn_coreU (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFU : EvalFitsU) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {x : Hint} {u w : Term}
    (hnc : ∀ f as hd, u ≠ .call f as hd) (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.letIn x u w) (fun st => 0 < st.env.size ∧ st.deferCallTy = false) (· = false) := by
  intro st st' typed hint v T? s π ⟨hne, hflag⟩ hty hm _ htn htd hcd hp hrt hr hS hv hab hhb hnh hfl hok hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, hme₃', hD₁, hD₂, hwt₀⟩ := Machine.letInvDUn m x u w hint st st' bh v T? K.D hnc htn htd hD h
  -- the tail's hint, on both sides: the `let`'s in tail position, none out of it
  have hth := tailHint_hintM K ρ st.curTail hint
  have hHb := hintBelow_ite st.curTail hhb
  obtain ⟨habu, habw⟩ := absBelow_letIn hab
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  have hsz₀ : st₀.env.size = st.env.size := (ColumnC.size_of_erase hk₀.env).symm
  -- the reference's run of the `let` succeeds (the untyped entry condition)
  have hok' := hok rfl
  rw [runT_letIn _ _ x u w s hfl] at hok'
  have hoku : (runT K ρ φ false (.plain TyM.err) u s).isSome := by
    revert hok'; simp only [bind, Option.bind]; cases runT K ρ φ false (.plain TyM.err) u s <;> simp
  -- the step for `u`
  have hOu := (ih m (by omega) K.Δ ρ).1 u st₀ st₁ false none v₀ T₀ s π (hm.of_modeEq hm₀) (fun e => by cases e)
    (by omega) (.inl htd₀) (hp.of_kern hk₀) (hrt.of_kern hk₀) (hr.of_kern hk₀) hS hv.1 (by rw [← hk₀.absTy]; exact habu) (hintBelow_none _) hnhu
    (fun _ => by rw [htn₀]; exact hoku) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁, -, hwu, hglu⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  have hm₁ : ModeR st₁ := (hm.of_modeEq hm₀).of_modeEq hK₁.mode
  have hsz₁ := hK₁.size
  have htop₁ := hK₁.top
  have hne₁ : 0 < st₁.env.size := by omega
  -- the value fits its reading at the new binding (from the reference's success, `EvalFitsU`)
  have hfit := fitsAt_of_eval hk₀ htop₁ hdu
    (hFU K ρ φ π m u st₀ st₁ bh₁ v₀ T₀ s (hp.of_kern hk₀) (hr.of_kern hk₀) hS hD₁ (hm.of_modeEq hm₀) htn₀ htd₀ hoku hru)
  -- the push, on both sides
  obtain ⟨hpB, hrB⟩ := hPu { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ T₀ x p du ru s₁ hne₁ hp₁ hr₁ hS₁ hmu hau (hwu (.inr ⟨hwt₀.1, hwt₀.2.trans hflag⟩)) hlu
    hgu hlabu hlouu hfit (hEK K ρ m false u none st₀ st₁ bh₁ v₀ T₀ (hp.of_kern hk₀) (.inr hwt₀.1) hru) hkB
  have hSB : Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) := by
    by_cases hs₁ : s₁.env = []
    · rw [Strict.pushBindShaped_nil _ _ hs₁]; exact hS₁
    · exact Strict.sgood_pushBindShaped hS₁ _ rfl hgu hlabu hlouu hs₁
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du } := by
    rw [scopeOf_rel hr, hdu]
  -- the reference's tail succeeds
  have hokw : (runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })).isSome := by
    revert hok'; simp only [bind, Option.bind]; rw [hxu']; simp only; rw [hpb, hth]
    cases runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })
      <;> simp
  -- the hint the tail is handed means the same at the extended context
  have hHM : hintM { K with Δ := Δ₁ } ρ₁ (if st.curTail then hint else none) =
      hintM K ρ (if st.curTail then hint else none) :=
    hintM_congrA (n := st₀.absTy.size) (by rw [← hk₀.absTy]; exact hHb) he₁.agree
  -- the step for `w`, at the extended context
  have hszB : stB.env.size = st₁.env.size := by
    rw [← ColumnC.size_of_erase hkB.env]; exact size_pushBindE _ _ _ _ _ _
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st₁.env.size - 1 < st₁.env.size)⟩
  have htopB : DecideScope.topReadings stB = du :: DecideScope.topReadings st := by
    rw [← ColumnC.topReadings_kern hkB, ColumnC.topReadings_pushBindE hfr₁, htop₁, ColumnC.topReadings_kern hk₀.symm]
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) :=
    .inr (by rw [htdB, hcd, htopB, hLT, hdu])
  have habB : st.absTy.size ≤ stB.absTy.size := by
    have := he₁.abs; rw [← hkB.absTy]; rw [← hk₀.absTy] at this; exact this
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    have hσ' : σ < st₀.absTy.size := by rw [← hk₀.absTy]; exact habw σ hσ
    obtain ⟨a, d⟩ := he₁.agree σ hσ'
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stB st₂ false _ r T? _ π₁ (hm₁.of_modeEq hmeB)
    (fun e => by cases e) (by omega) htdB'
    hpB ((hrt.of_kern hk₀).move (by rw [← hkB.recStack]; exact hK₁.stack) (by rw [← hkB.absTy]; exact he₁.abs)
      fun σ hσ => (he₁.agree σ hσ).1) hrB hSB (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habB) (hHb.mono habB) hnhw
    (fun _ => by rw [htnB, hHM, ← runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hokw) hD₂ bh₂ hrw
  replace hOw := outGK_of_outLK hOw
  rw [htnB, hHM] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂, hglw⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) = some (rw', s₂) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  obtain ⟨-, -, -, hS₂⟩ := Strict.fund_all hc w hv.2 st.curTail _ _ s₂ rw' hSB hxw'
  have hsz₂ := hK₂.size
  have hne₂ : 0 < st₂.env.size := by omega
  -- the drop
  obtain ⟨s₃, hLD, htt, ⟨hga, hgl⟩, hP₃, hR₃, hme₃, hsz₃, htop₃, hrs₃, hgs₃⟩ := hDr { K with Δ := Δ₂ } ρ₂ φ π₂ (st₂.withTempT r T?) st₃ s₂ m bh₃
    (by rw [size_withTempT]; exact hne₂) hp₂ hr₂ hS₂ hrd
  obtain rfl : v = r := popped_of_topTemps hne₂ htt hk₃
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans
      ((he₂.grow hga hgl).congr rfl rfl (by rw [hk₃.absTy]; rfl) (by rw [hk₃.nextLoan]; rfl))
  have hW : ModeEq st₂ (st₂.withTempT v T?) := ⟨rfl, rfl, rfl, rfl⟩
  have hkept : Kept st st' := by
    refine ⟨hm₀.trans (hK₁.mode.trans (hmeB.trans (hK₂.mode.trans
      (hW.trans (hme₃.trans hme₃'))))), ?_, ?_, ?_⟩
    · have e1 := ColumnC.size_of_erase hk₃.env
      rw [size_withTempT] at e1 hsz₃
      omega
    · rw [← topReadings_withTempT st' v T?, ← ColumnC.topReadings_kern hk₃, htop₃, topReadings_withTempT,
        hK₂.top, htopB]
      rfl
    · show (st'.withTempT v T?).recStack = st.recStack
      rw [← hk₃.recStack, hrs₃]; show st₂.recStack = st.recStack
      rw [hK₂.stack, ← hkB.recStack]; show st₁.recStack = st.recStack
      rw [hK₁.stack, ← hk₀.recStack]
  -- the goal's meaning: kept by the drop and the push (equal goals), carried by the two sub-runs' clauses
  have hgoal : hintM { K with Δ := Δ₂ } ρ₂ st'.goal = hintM K ρ st.goal := by
    have e1 : st'.goal = st₂.goal := by
      show (st'.withTempT v T?).goal = (st₂.withTempT v T?).goal
      rw [← hk₃.goal, hgs₃]
    rw [e1, hglw, ← hkB.goal]
    show hintM { K with Δ := Δ₁ } ρ₁ st₁.goal = _
    rw [hglu, ← hk₀.goal]
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hP₃.of_kern hk₃, hR₃.of_kern hk₃, hgoal⟩, hkept⟩
  -- the reference's `let`: its tail runs at the tail's hint
  rw [runT_letIn _ _ x u w s hfl, hxu']
  simp only [bind, Option.bind]
  rw [hpb, hth, hxw']
  exact letDrop_eval hLD rw'

/-- Setting the top binding's deferred type keeps the frames. -/
theorem size_setLazyTop (E : Env) (lz : Option (Value × List Value × Nat)) : (E.setLazyTop lz).size = E.size := by
  cases lz <;> simp [Env.setLazyTop]

/-- Setting the top binding's deferred type keeps the top readings. -/
theorem topReadings_setLazyTop (st : MState) (E : Env) (lz : Option (Value × List Value × Nat)) :
    DecideScope.topReadings { st with env := E.setLazyTop lz } = DecideScope.topReadings { st with env := E } := by
  cases lz with
  | none => rfl
  | some z =>
    simp only [DecideScope.topReadings, Env.setLazyTop, Array.back?_eq_getElem?, Array.size_modify]
    rw [Array.getElem?_modify]
    split
    · congr 1
      cases E[E.size - 1]? with
      | none => rfl
      | some fr =>
        simp only [Option.map_some]
        congr 1
        refine congrArg some ?_
        apply List.ext_getElem
        · simp
        · intro i h₁ h₂
          simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
          split <;> rfl
    · simp

/-- **An untyped, unerased `let` whose right-hand side is a CALL, at `evalCore`, in general, at every tail flag**
(lead26, docs/31 D183): `letIn_coreU` with the deferral; the binding is pushed at the call's type (`LetPushG`) or,
where the call came back with none, at the pair it recorded (`LetLazyPushG`), whose meaning is the reference's result
type by the call's own conclusion (`OutL`'s `LaterOk`, the lead's ruling on D180). -/
theorem letCall_coreU (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW) (hLP : Machine.LaterPiG) (hPL : LetLazyPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFU : EvalFitsU) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {x : Hint} {f : Term} {as : List Term}
    {hd : Bool} {w : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.letIn x (.call f as hd) w) (fun st => 0 < st.env.size ∧ st.deferCallTy = false) (· = false) := by
  intro st st' typed hint v T? s π ⟨hne, hdfz⟩ hty hm _ htn htd hcd hp hrt hr hS hv hab hhb hnh hfl hok hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, lz, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hlz, hkB, hmeB, htnB, hrw, hrd, hk₃, hme₃', hD₁, hD₂, hwt₀⟩ :=
    Machine.letCallInvU m x f as hd w hint st st' bh v T? K.D htn htd hD h
  -- the tail's hint, on both sides: the `let`'s in tail position, none out of it
  have hth := tailHint_hintM K ρ st.curTail hint
  have hHb := hintBelow_ite st.curTail hhb
  obtain ⟨habu, habw⟩ := absBelow_letIn hab
  have hnhu : (Term.call f as hd).hasHolePrim = false := by
    have e := hnh; simp only [Term.hasHolePrim, Bool.or_eq_false_iff] at e ⊢; exact e.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  have hsz₀ : st₀.env.size = st.env.size := (ColumnC.size_of_erase hk₀.env).symm
  -- the reference's run of the `let` succeeds (the untyped entry condition)
  have hok' := hok rfl
  rw [runT_letIn _ _ x _ w s hfl] at hok'
  have hoku : (runT K ρ φ false (.plain TyM.err) (.call f as hd) s).isSome := by
    revert hok'; simp only [bind, Option.bind]; cases runT K ρ φ false (.plain TyM.err) (.call f as hd) s <;> simp
  -- the step for `u`
  have hOu := (ih m (by omega) K.Δ ρ).1 (.call f as hd) st₀ st₁ false none v₀ T₀ s π (hm.of_modeEq hm₀) (fun e => by cases e)
    (by omega) (.inl htd₀) (hp.of_kern hk₀) (hrt.of_kern hk₀) (hr.of_kern hk₀) hS hv.1 (by rw [← hk₀.absTy]; exact habu) (hintBelow_none _) hnhu
    (fun _ => by rw [htn₀]; exact hoku) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁, hlat, hwu, hglu⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) (.call f as hd) s = some (ru, s₁) := hxu
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc _ hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  have hm₁ : ModeR st₁ := (hm.of_modeEq hm₀).of_modeEq hK₁.mode
  have hsz₁ := hK₁.size
  have htop₁ := hK₁.top
  have hne₁ : 0 < st₁.env.size := by omega
  -- the value fits its reading at the new binding (from the reference's success, `EvalFitsU`)
  have hfit := fitsAt_of_eval hk₀ htop₁ hdu
    (hFU K ρ φ π m _ st₀ st₁ bh₁ v₀ T₀ s (hp.of_kern hk₀) (hr.of_kern hk₀) hS hD₁ (hm.of_modeEq hm₀) htn₀ htd₀ hoku hru)
  -- the push, on both sides: at the call's type, or at the type the call recorded for later, which means the
  -- reference's result type (the call's `LaterOk`, read where the checker reads the record)
  obtain ⟨hpB, hrB⟩ : Pre { K with Δ := Δ₁ } ρ₁ stB ∧
      Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) := by
    rcases hlz with ⟨hdf₀, ⟨rfl, hnr⟩ | ⟨caps, hs, ds, cod, rd, ws, rfl, hrec, rfl⟩⟩ | ⟨hdf₀, rfl⟩
    · -- no type came back only where the record is a Π-type (`LaterPiG`), which the `let` would have deferred
      have hT : T₀ = none → ru.2.m = TyM.err := fun e => by
        subst e
        obtain ⟨caps, hs, ds, cod, rd, ws, hrec⟩ := hLP K ρ m f as hd st₀ st₁ bh₁ v₀ (hp.of_kern hk₀) hwt₀ hdf₀ hru
        exact absurd hrec (hnr caps hs ds cod rd ws rfl)
      exact hPu { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ T₀ x p du ru s₁ hne₁ hp₁ hr₁ hS₁ hmu hau hT hlu
        hgu hlabu hlouu hfit (hEK K ρ m false _ none st₀ st₁ bh₁ v₀ T₀ (hp.of_kern hk₀) (.inr hwt₀) hru) hkB
    · have hz := hlat ⟨f, as, hd, rfl⟩ hdf₀ caps hs ds cod rd ws hrec
      exact hPL { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ x p du _ ru s₁ hz hne₁ hp₁ hr₁ hS₁ hmu hlu
        hgu hlabu hlouu hfit hkB
    · -- main's D132: a call the pre-pass erases is not deferred; it runs wanted with the flag clear, so a missing type
      -- reads as the reference's `err` (the call's own `OutL`)
      exact hPu { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ T₀ x p du ru s₁ hne₁ hp₁ hr₁ hS₁ hmu hau
        (hwu (.inr ⟨hwt₀, hdf₀.trans hdfz⟩)) hlu
        hgu hlabu hlouu hfit (hEK K ρ m false _ none st₀ st₁ bh₁ v₀ T₀ (hp.of_kern hk₀) (.inr hwt₀) hru) hkB
  have hSB : Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) := by
    by_cases hs₁ : s₁.env = []
    · rw [Strict.pushBindShaped_nil _ _ hs₁]; exact hS₁
    · exact Strict.sgood_pushBindShaped hS₁ _ rfl hgu hlabu hlouu hs₁
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) (.call f as hd) } =
      pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du } := by
    rw [scopeOf_rel hr, hdu]
  -- the reference's tail succeeds
  have hokw : (runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })).isSome := by
    revert hok'; simp only [bind, Option.bind]; rw [hxu']; simp only; rw [hpb, hth]
    cases runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })
      <;> simp
  -- the hint the tail is handed means the same at the extended context
  have hHM : hintM { K with Δ := Δ₁ } ρ₁ (if st.curTail then hint else none) =
      hintM K ρ (if st.curTail then hint else none) :=
    hintM_congrA (n := st₀.absTy.size) (by rw [← hk₀.absTy]; exact hHb) he₁.agree
  -- the step for `w`, at the extended context
  have hszB : stB.env.size = st₁.env.size := by
    rw [← ColumnC.size_of_erase hkB.env]; show (Env.setLazyTop _ lz).size = _
    rw [size_setLazyTop]; exact size_pushBindE _ _ _ _ _ _
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st₁.env.size - 1 < st₁.env.size)⟩
  have htopB : DecideScope.topReadings stB = du :: DecideScope.topReadings st := by
    rw [← ColumnC.topReadings_kern hkB, topReadings_setLazyTop, ColumnC.topReadings_pushBindE hfr₁, htop₁, ColumnC.topReadings_kern hk₀.symm]
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) :=
    .inr (by rw [htdB, hcd, htopB, hLT, hdu])
  have habB : st.absTy.size ≤ stB.absTy.size := by
    have := he₁.abs; rw [← hkB.absTy]; rw [← hk₀.absTy] at this; exact this
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    have hσ' : σ < st₀.absTy.size := by rw [← hk₀.absTy]; exact habw σ hσ
    obtain ⟨a, d⟩ := he₁.agree σ hσ'
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stB st₂ false _ r T? _ π₁ (hm₁.of_modeEq hmeB)
    (fun e => by cases e) (by omega) htdB'
    hpB ((hrt.of_kern hk₀).move (by rw [← hkB.recStack]; exact hK₁.stack) (by rw [← hkB.absTy]; exact he₁.abs)
      fun σ hσ => (he₁.agree σ hσ).1) hrB hSB (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habB) (hHb.mono habB) hnhw
    (fun _ => by rw [htnB, hHM, ← runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hokw) hD₂ bh₂ hrw
  replace hOw := outGK_of_outLK hOw
  rw [htnB, hHM] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂, hglw⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (hintM K ρ (if st.curTail then hint else none)) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) = some (rw', s₂) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  obtain ⟨-, -, -, hS₂⟩ := Strict.fund_all hc w hv.2 st.curTail _ _ s₂ rw' hSB hxw'
  have hsz₂ := hK₂.size
  have hne₂ : 0 < st₂.env.size := by omega
  -- the drop
  obtain ⟨s₃, hLD, htt, ⟨hga, hgl⟩, hP₃, hR₃, hme₃, hsz₃, htop₃, hrs₃, hgs₃⟩ := hDr { K with Δ := Δ₂ } ρ₂ φ π₂ (st₂.withTempT r T?) st₃ s₂ m bh₃
    (by rw [size_withTempT]; exact hne₂) hp₂ hr₂ hS₂ hrd
  obtain rfl : v = r := popped_of_topTemps hne₂ htt hk₃
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans
      ((he₂.grow hga hgl).congr rfl rfl (by rw [hk₃.absTy]; rfl) (by rw [hk₃.nextLoan]; rfl))
  have hW : ModeEq st₂ (st₂.withTempT v T?) := ⟨rfl, rfl, rfl, rfl⟩
  have hkept : Kept st st' := by
    refine ⟨hm₀.trans (hK₁.mode.trans (hmeB.trans (hK₂.mode.trans
      (hW.trans (hme₃.trans hme₃'))))), ?_, ?_, ?_⟩
    · have e1 := ColumnC.size_of_erase hk₃.env
      rw [size_withTempT] at e1 hsz₃
      omega
    · rw [← topReadings_withTempT st' v T?, ← ColumnC.topReadings_kern hk₃, htop₃, topReadings_withTempT,
        hK₂.top, htopB]
      rfl
    · show (st'.withTempT v T?).recStack = st.recStack
      rw [← hk₃.recStack, hrs₃]; show st₂.recStack = st.recStack
      rw [hK₂.stack, ← hkB.recStack]; show st₁.recStack = st.recStack
      rw [hK₁.stack, ← hk₀.recStack]
  -- the goal's meaning: kept by the drop and the push (equal goals), carried by the two sub-runs' clauses
  have hgoal : hintM { K with Δ := Δ₂ } ρ₂ st'.goal = hintM K ρ st.goal := by
    have e1 : st'.goal = st₂.goal := by
      show (st'.withTempT v T?).goal = (st₂.withTempT v T?).goal
      rw [← hk₃.goal, hgs₃]
    rw [e1, hglw, ← hkB.goal]
    show hintM { K with Δ := Δ₁ } ρ₁ st₁.goal = _
    rw [hglu, ← hk₀.goal]
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hP₃.of_kern hk₃, hR₃.of_kern hk₃, hgoal⟩, hkept⟩
  -- the reference's `let`: its tail runs at the tail's hint
  rw [runT_letIn _ _ x _ w s hfl, hxu']
  simp only [bind, Option.bind]
  rw [hpb, hth, hxw']
  exact letDrop_eval hLD rw'

/-- **The step for an untyped `let` whose right-hand side is not a call, the table reading it as decided data, in
general, at every tail flag**, with what the run keeps (docs/31 D180). ASSUMES 4 facts: `LetTailDecl` (table),
`LetPushG`, `LetDropG` (each part checker, part model), `ValsCongrA` (model); and `Strict.FundCtx K`. The inversion
(`Machine.letInvDUn`) is proved; D124's fact at this site (`HintSites.UntypedLetTailNoHint`, proved) is no longer
used: the restated inversion carries it. -/
theorem stepLetIn_untyped (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW)
    (hDr : LetDropG) (hVC : ValsCongrA) (hFU : EvalFitsU) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (u w : Term), (∀ f as hd, u ≠ .call f as hd) →
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x u w)
        (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false)
        (· = false) := by
  intro n ih Δ ρ x u w hnc
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.letIn x u w)
      (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) (· = false) :=
    fun st st' typed hint v T? s π hP => letIn_coreU (K := { K with Δ := Δ }) hLT hPu hEK hDr hVC hFU ⟨hc.globals, hc.sorts⟩
      hnc ih st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk hf ha => ⟨⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1.1, hf⟩,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

/-- A step proved for typed runs and for untyped runs on one class of states is the step for both. -/
theorem evalSimK_of_typed_untyped {K : RunCtx} {ρ : Assignment} {φ : Future} {n : Nat} {t : Term} {P : MState → Prop}
    (h₁ : EvalSimK K ρ φ n t P (· = true)) (h₂ : EvalSimK K ρ φ n t P (· = false)) : EvalSimK K ρ φ n t P := by
  intro st st' typed hint v T? s π hP _
  cases typed
  · exact h₂ st st' false hint v T? s π hP rfl
  · exact h₁ st st' true hint v T? s π hP rfl

/-- **The step for `u; w`, typed or untyped, at every tail flag, where the table reads it as decided data**
(docs/31 D180): `stepSeq_typed` with `stepSeq_untyped`. ASSUMES 3 facts: `SeqTailDecl` (table), `DropValueG`
(mixed), `ValsCongrA` (model); and `Strict.FundCtx K`. What `StepSeq` lacks beyond it is the erased wrapper (a
sequence the table reads as `.any`, a proof, or erased; D158). -/
theorem stepSeq_unerased (hST : SeqTailDecl K.D) (hDV : DropValueG) (hVC : ValsCongrA) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.seq u w)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) :=
  fun n ih Δ ρ u w => evalSimK_of_typed_untyped (stepSeq_typed hST hDV hVC hc n ih Δ ρ u w)
    (stepSeq_untyped hST hDV hVC hc n ih Δ ρ u w)

/-- **The step for `let x = u; w`, typed, or untyped with `u` not a call, at every tail flag, where the table reads
it as decided data** (docs/31 D180): `stepLetIn_typed` with `stepLetIn_untyped`. ASSUMES 4 facts: `LetTailDecl`
(table), `LetPushG`, `LetDropG` (mixed), `ValsCongrA` (model); and `Strict.FundCtx K`. What `StepLetIn` lacks beyond
it: the untyped `let` of a call (its deferred type, D180) and the erased wrapper (D158). -/
theorem stepLetIn_unerased (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW) (hDr : LetDropG) (hVC : ValsCongrA)
    (hFT : EvalFitsT) (hFU : EvalFitsU) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (u w : Term), (∀ f as hd, u ≠ .call f as hd) →
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x u w)
        (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) :=
  fun n ih Δ ρ x u w hnc => evalSimK_of_typed_untyped (stepLetIn_typed hLT hPu hEK hDr hVC hFT hc n ih Δ ρ x u w)
    (stepLetIn_untyped hLT hPu hEK hDr hVC hFU hc n ih Δ ρ x u w hnc)

/-- **The step for an untyped `let` whose right-hand side is a call, in general, at every tail flag** (docs/31 D183).
ASSUMES 5 facts: `LetTailDecl` (table), `LetPushG`, `LetLazyPushG`, `LetDropG` (mixed), `ValsCongrA` (model); and
`Strict.FundCtx K`. The inversion (`Machine.letCallInvU`) is proved; the deferred type's meaning is the call's own
conclusion (`OutL`). -/
theorem stepLetIn_untypedCall (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW) (hLP : Machine.LaterPiG) (hPL : LetLazyPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFU : EvalFitsU) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (f : Term) (as : List Term) (hd : Bool) (w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x (.call f as hd) w)
        (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x (.call f as hd) w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x (.call f as hd) w)).isProof = false)
        (· = false) := by
  intro n ih Δ ρ x f as hd w
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.letIn x (.call f as hd) w)
      (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x (.call f as hd) w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.letIn x (.call f as hd) w)).isProof = false) (· = false) :=
    fun st st' typed hint v T? s π hP => letCall_coreU (K := { K with Δ := Δ }) hLT hPu hEK hLP hPL hDr hVC hFU
      ⟨hc.globals, hc.sorts⟩ ih st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk hf ha => ⟨⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1.1, hf⟩,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

/-- **The step for every `let x = u; w`, typed or untyped, at every tail flag, where the table reads it as decided
data** (docs/31 D183): `stepLetIn_typed`, `stepLetIn_untyped` and `stepLetIn_untypedCall`. ASSUMES 7 facts (lead27,
D185, added the two fits): `LetTailDecl` (table), `LetPushG`, `LetLazyPushG`, `LetDropG` (mixed), `ValsCongrA`
(model), `EvalFitsT` (checker), `EvalFitsU` (mixed); and `Strict.FundCtx K`.
What `StepLetIn` lacks beyond it is the erased wrapper (D158). -/
theorem stepLetIn_unerasedAll (hLT : LetTailDecl K.D) (hPu : LetPushG) (hEK : EvalKindW) (hLP : Machine.LaterPiG) (hPL : LetLazyPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFT : EvalFitsT) (hFU : EvalFitsU) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x u w)
        (fun st => (0 < st.env.size ∧ st.deferCallTy = false) ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) := by
  intro n ih Δ ρ x u w
  by_cases hcall : ∃ f as hd, u = .call f as hd
  · obtain ⟨f, as, hd, rfl⟩ := hcall
    exact evalSimK_of_typed_untyped (stepLetIn_typed hLT hPu hEK hDr hVC hFT hc n ih Δ ρ x _ w)
      (stepLetIn_untypedCall hLT hPu hEK hLP hPL hDr hVC hFU hc n ih Δ ρ x f as hd w)
  · exact stepLetIn_unerased hLT hPu hEK hDr hVC hFT hFU hc n ih Δ ρ x u w (fun f as hd e => hcall ⟨f, as, hd, e⟩)

end

end Ochr.Meaning.Steps.Form.Master
