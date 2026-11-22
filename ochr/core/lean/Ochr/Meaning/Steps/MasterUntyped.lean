import Ochr.Meaning.Steps.MasterSeq
import Ochr.Meaning.Steps.HintSites

/-!
# The master induction's UNTYPED `;` and `let`, out of tail position, in general (lead25, 2026-11-22; docs/31 D176)

An untyped run (a callee's body at a call, `runBody`; a type's computation) of `u; w` or `let x = u; w`. The checker's
untyped `evalCore` runs the first term with no hint, as the typed one does, and since main's D124 (merged by
machine9) hands the tail the hint in tail position only, as the reference does (`tailHint`, D156); before the merge it
handed it at every tail flag. Each step states that site's named fact (`HintSites.UntypedSeqTailNoHint`,
`UntypedLetTailNoHint`), TRUE since the merge and PROVED (`Machine.untypedSeqTailNoHint`, `Machine.untypedLetTailNoHint`);
the inversions `SeqInvDU`, `LetInvDUn`, `LetCallInvU` were restated at the merge to run the tail at
`if st.curTail then hint else none`. In tail position the tail runs at
the hint on both sides, after the first sub-run's extension of the assignment; moving the tail's run back needs the
hint's unknowns below the counter, which `EvalAt` does not yet say (change of form asked): those halves wait.

* `seqInvDU` (a fact about the checker alone, PROVED here: `seqInvD`'s proof at an untyped run);
* the step `seq_coreU` / `stepSeq_untyped`, for states out of tail position: ASSUMES `UntypedSeqTailNoHint` (checker,
  proved: `Machine.untypedSeqTailNoHint`) and the typed step's three (`SeqTailDecl`, `DropValueG`, `ValsCongrA`) and `FundCtx`;
* `letInvDUn` (PROVED: `letInvD`'s proof at an untyped run, the right-hand side not a call);
* the step `letIn_coreU` / `stepLetIn_untyped`, out of tail position, the right-hand side not a call: ASSUMES
  `UntypedLetTailNoHint` (checker, proved: `Machine.untypedLetTailNoHint`) and the typed step's four (`LetTailDecl`, `LetPushG`, `LetDropG`,
  `ValsCongrA`) and `FundCtx`;
* a call's right-hand side may have its type deferred (`lazyTy`, D82): its inversion `LetCallInvU` (checker) and push
  `LetLazyPushG` (mixed) are STATED, the step for it not built.
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
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, h₂⟩
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
      DecTab D st₁ ∧ DecTab D st₂

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
  rw [if_neg (by simp)] at h₁
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
    { s₃ with env := Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du', deferCallTy := false, callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
    s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, b₃, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, ?_, ?_, rfl, hw',
    hdr, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact decTab_declOf_at hDst hdu
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
      ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
        (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
  · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))

/-- The top frame's last binding with its type deferred, as the checker's untyped `let` records a call's type
(`lazyTy := (P, ws, |ds|)`, D82); `none` leaves the environment. -/
def _root_.Ochr.Env.setLazyTop (E : Env) : Option (Value × List Value × Nat) → Env
  | none => E
  | some z => E.modify (E.size - 1) fun fr =>
      { fr with binds := fr.binds.modify (fr.binds.size - 1) fun b => { b with lazyTy := some z } }

/-- **`evalCore` of an UNTYPED `let` whose right-hand side is a call** (a fact about the checker alone; STATED, not
proved; the missing piece of the untyped `let` for a call's right-hand side): as `LetInvDUn`, except that `u` runs
with the deferral flag set (`deferCallTy`, outside the kernel) and, where its type comes back unknown, the new
binding records the call's type to be evaluated when read (`lazyTy`, `setLazyTop`). -/
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
      (lz = none ∨ T₀ = none) ∧
      Kern { st₁ with env := (Env.pushBindE st₁.env h T₀ v₀ p du).setLazyTop lz } stB ∧ Form.ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n false w (if st.curTail then hint else none)) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ Form.ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂

end Ochr.Meaning.Steps.Machine

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **`eval` around `evalCore` out of tail position**: `eval_of_coreK` for a class of states whose `eval`-level
tail flag is clear, which `eval` hands `evalCore` as its tail position (`EvalInvD`: `curTail = tailNext`). -/
theorem eval_of_coreK_notTail {K : RunCtx} {ρ : Assignment} {φ : Future} (hE : EvalInvD) {n : Nat} {t : Term}
    {P : MState → Prop} {TY : Bool → Prop}
    (hP : ∀ a b, Kern a b → P a → P b) (ht : ∀ w, t ≠ .val w) (hcall : ∀ f as h, t ≠ .call f as h)
    (hany : ∀ st, P st → K.D.declOf (DecideScope.topReadings st) t ≠ .any ∧
      (K.D.declOf (DecideScope.topReadings st) t).isProof = false)
    (hc : CoreSimK K ρ φ n t (fun st => P st ∧ st.curTail = false) TY) :
    EvalSimK K ρ φ (n + 2) t (fun st => P st ∧ st.tailNext = false) TY := by
  intro st st' typed hint v T? s π hPs hty hm htl htd hp hr hS hv hab hhb hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, bh', hk₀, hm₀, hct, htn, htd₀, hcd₀, h₀, hk₁, hm₁⟩ :=
    hE n typed t hint st st' bh v T? K.D hm hD ht hcall (hany st hPs.1).1 (hany st hPs.1).2 htd h
  obtain ⟨hc', hkp⟩ := hc st₀ st₁ typed hint v T? s π ⟨hP st st₀ hk₀ hPs.1, hct.trans hPs.2⟩ hty
    (hm.of_modeEq hm₀) (fun e => hct.trans (htl e)) htn htd₀ hcd₀ (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hv
    (by rw [← hk₀.absTy]; exact hab) (by rw [← hk₀.absTy]; exact hhb) hnh hfl (by rw [hct]; exact hok)
    (DecTab.of_kern hk₁.symm hD) bh' h₀
  rw [hct] at hc'
  exact ⟨Out.of_kern hk₀ hk₁ hc', ((Kept.of_kern hk₀ hm₀).trans hkp).trans (Kept.of_kern hk₁ hm₁)⟩


/-- **The push of a binding whose type is deferred** (mixed; STATED, not proved; with `LetCallInvU`, what the
untyped `let` of a call needs beyond `LetPushG`): as `LetPushG`, the value's type unknown (`T₀ = none`) and the new
binding recording the call's type (`lazyTy`), which the relation reads through `CodeMeaning.paramTy` (`Env.hintAt`). -/
def LetLazyPushG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ stB : MState) (v₀ : Value)
    (x : Hint) (p : Bool) (du : DeclInfo) (z : Value × List Value × Nat) (ru : Res) (s₁ : SState),
    0 < st₁.env.size →
    Pre K ρ (st₁.withTempT v₀ none) → Rel K ρ φ π (st₁.withTempT v₀ none) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1 → ru.2.label = (Value.heldLabel v₀).map π →
    Strict.GoodRes K.dm.read ru → Strict.LabOk K.dm s₁ ru → LoU s₁ ru.2.label →
    Kern { st₁ with env := (Env.pushBindE st₁.env x none v₀ p du).setLazyTop (some z) } stB →
    Pre K ρ stB ∧ Rel K ρ φ π stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })

section
variable {K : RunCtx} {φ : Future}

/-- **An untyped, unerased `u; w` out of tail position, at `evalCore`, in general.** -/
theorem seq_coreU (hNH : HintSites.UntypedSeqTailNoHint) (hST : SeqTailDecl K.D) (hDV : DropValueG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {u w : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.seq u w) (fun st => 0 < st.env.size ∧ st.curTail = false) (· = false) := by
  intro st st' typed hint v T? s π hP hty hm _ htn htd hcd hp hr hS hv hab hhb hnh hfl hok hD bh h
  subst hty
  obtain ⟨hne, hct⟩ := hP
  -- D124 at `;` (named; proved since the merge, `Machine.untypedSeqTailNoHint`): out of tail position the run at the hint is the run at none
  have h0 : Runs (Ochr.evalCore (m + 1) false (.seq u w) none) st bh (v, T?) st' := (hNH m u w hint st st' bh _ hct).1 h
  obtain ⟨st₁, s₄, stW, v₀, T₀, bh₁, bh₃, bh₂, hru, hD₁, hdv, -, hkW, hmeW, htdW, htnW, hrw⟩ :=
    Machine.seqInvDU m u w none st st' bh v T? K.D hD h0
  rw [ite_self] at hrw
  have habu : u.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have habw : w.absBelow st.absTy.size := fun σ hσ => hab σ (by simp [Term.anyAtom, hσ])
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  -- the reference's run of the sequence succeeds (the untyped entry condition), out of tail position
  have hok' := hok rfl
  rw [hct, runT_seq _ _ u w s hfl] at hok'
  have hoku : (runT K ρ φ false (.plain TyM.err) u s).isSome := by
    revert hok'; simp only [bind, Option.bind]; cases runT K ρ φ false (.plain TyM.err) u s <;> simp
  -- the step for `u`, from the entry state itself
  have hOu := (ih m (by omega) K.Δ ρ).1 u st st₁ false none v₀ T₀ s π hm (fun e => by cases e) hne (.inl htd) hp hr hS
    hv.1 habu (hintBelow_none _) hnhu (fun _ => by rw [htn]; exact hoku) hD₁ bh₁ hru
  rw [htn] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  -- the discard, on both sides
  obtain ⟨hdok, ⟨hga, hgl⟩, hP₄, hR₄, hK₄⟩ := hDV { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ s₄ v₀ T₀ ru s₁ m bh₃
    (by rw [hK₁.size]; exact hne) hp₁ hr₁ hS₁ hmu hlu hdv
  have hS₂ : Strict.SGood K.dm K.Γ φ (discardEnd ru.2 s₁) := by
    unfold discardEnd; unfold DiscardOk at hdok; split
    · rename_i l hl; rw [hl] at hdok; exact Strict.endLabel_sgood hS₁ _ hdok
    · exact hS₁
  -- the reference's tail succeeds, at no hint out of tail position
  have hth : tailHint st.curTail (hintM K ρ hint) = .plain TyM.err := by rw [hct]; rfl
  have hokw : (runT K ρ φ st.curTail (.plain TyM.err) w (discardEnd ru.2 s₁)).isSome := by
    revert hok'; simp only [bind, Option.bind]; rw [hxu']; simp only
    rw [SM.guardMod_of (show DiscardOk K φ ru.2 s₁ from hdok)]; simp only
    rw [show tailHint false (hintM K ρ hint) = .plain TyM.err from rfl, ← hct]; exact id
  -- the step for `w`, at the extended context
  have hKW : Kept st stW := (hK₁.trans hK₄).trans (Kept.of_kern hkW hmeW)
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) :=
    .inr (by rw [htdW, hcd, hKW.top, hST])
  have habW : st.absTy.size ≤ stW.absTy.size := by
    rw [← hkW.absTy]; exact Nat.le_trans he₁.abs hga
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    obtain ⟨a, d⟩ := he₁.agree σ (habw σ hσ)
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stW st' false none v T? (discardEnd ru.2 s₁) π₁
    (hm.of_modeEq hKW.mode) (fun e => by cases e) (by rw [hKW.size]; exact hne) htdW'
    (hP₄.of_kern hkW) (hR₄.of_kern hkW) hS₂ (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habW) (hintBelow_none _) hnhw
    (fun _ => by rw [htnW, ← runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hokw) hD bh₂ hrw
  rw [htnW] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w (discardEnd ru.2 s₁) = some (rw', s₃) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    ((he₁.grow hga hgl).congr rfl rfl hkW.absTy hkW.nextLoan).trans he₂
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hp₂, hr₂⟩, hKW.trans hK₂⟩
  -- the reference's sequence, out of tail position: its tail runs at no hint
  rw [runT_seq _ _ u w s hfl]
  simp only [bind, Option.bind]
  rw [hxu']
  simp only
  rw [SM.guardMod_of (show DiscardOk K φ ru.2 s₁ from hdok)]
  simp only
  rw [hth]; exact hxw'

/-- **The step for an untyped `;` out of tail position, the table reading it as decided data, in general**, with
what the run keeps. ASSUMES 4 facts: `HintSites.UntypedSeqTailNoHint` (checker, proved since main's
D124 was merged: `Machine.untypedSeqTailNoHint`), `SeqTailDecl` (table), `DropValueG` (part checker, part model), `ValsCongrA` (model); and `Strict.FundCtx K`.
The class: an `eval`-level state with a frame and its tail flag clear. -/
theorem stepSeq_untyped (hNH : HintSites.UntypedSeqTailNoHint) (hST : SeqTailDecl K.D) (hDV : DropValueG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.seq u w)
        (fun st => (0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) ∧ st.tailNext = false) (· = false) := by
  intro n ih Δ ρ u w
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.seq u w)
      (fun st => (0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.seq u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.seq u w)).isProof = false) ∧ st.curTail = false) (· = false) :=
    fun st st' typed hint v T? s π hP => seq_coreU (K := { K with Δ := Δ }) hNH hST hDV hVC ⟨hc.globals, hc.sorts⟩ ih
      st st' typed hint v T? s π ⟨hP.1.1, hP.2⟩
  exact eval_of_coreK_notTail (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'


/-- **An untyped, unerased `let` out of tail position whose right-hand side is not a call, at `evalCore`, in
general.** -/
theorem letIn_coreU (hNH : HintSites.UntypedLetTailNoHint) (hLT : LetTailDecl K.D) (hPu : LetPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {x : Hint} {u w : Term}
    (hnc : ∀ f as hd, u ≠ .call f as hd) (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.letIn x u w) (fun st => 0 < st.env.size ∧ st.curTail = false) (· = false) := by
  intro st st' typed hint v T? s π hP hty hm _ htn htd hcd hp hr hS hv hab hhb hnh hfl hok hD bh h
  subst hty
  obtain ⟨hne, hct⟩ := hP
  -- D124 at a `let` (named; proved since the merge, `Machine.untypedLetTailNoHint`): out of tail position the run at the hint is the run at none
  have h0 : Runs (Ochr.evalCore (m + 1) false (.letIn x u w) none) st bh (v, T?) st' :=
    (hNH m x u w hint st st' bh _ hct).1 h
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, hme₃', hD₁, hD₂⟩ := Machine.letInvDUn m x u w none st st' bh v T? K.D hnc htn htd hD h0
  rw [ite_self] at hrw
  obtain ⟨habu, habw⟩ := absBelow_letIn hab
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  have hsz₀ : st₀.env.size = st.env.size := (ColumnC.size_of_erase hk₀.env).symm
  -- the reference's run of the `let` succeeds (the untyped entry condition), out of tail position
  have hok' := hok rfl
  rw [hct, runT_letIn _ _ x u w s hfl] at hok'
  have hoku : (runT K ρ φ false (.plain TyM.err) u s).isSome := by
    revert hok'; simp only [bind, Option.bind]; cases runT K ρ φ false (.plain TyM.err) u s <;> simp
  -- the step for `u`
  have hOu := (ih m (by omega) K.Δ ρ).1 u st₀ st₁ false none v₀ T₀ s π (hm.of_modeEq hm₀) (fun e => by cases e)
    (by omega) (.inl htd₀) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv.1 (by rw [← hk₀.absTy]; exact habu) (hintBelow_none _) hnhu
    (fun _ => by rw [htn₀]; exact hoku) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  have hm₁ : ModeR st₁ := (hm.of_modeEq hm₀).of_modeEq hK₁.mode
  have hsz₁ := hK₁.size
  have htop₁ := hK₁.top
  have hne₁ : 0 < st₁.env.size := by omega
  -- the push, on both sides
  obtain ⟨hpB, hrB⟩ := hPu { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ T₀ x p du ru s₁ hne₁ hp₁ hr₁ hS₁ hmu hau hlu
    hgu hlabu hlouu hkB
  have hSB : Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) := by
    by_cases hs₁ : s₁.env = []
    · rw [Strict.pushBindShaped_nil _ _ hs₁]; exact hS₁
    · exact Strict.sgood_pushBindShaped hS₁ _ rfl hgu hlabu hlouu hs₁
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du } := by
    rw [scopeOf_rel hr, hdu]
  -- the reference's tail succeeds, at no hint out of tail position
  have hth : tailHint st.curTail (hintM K ρ hint) = .plain TyM.err := by rw [hct]; rfl
  have hokw : (runT K ρ φ st.curTail (.plain TyM.err) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })).isSome := by
    revert hok'; simp only [bind, Option.bind]; rw [hxu']; simp only; rw [hpb]
    rw [show tailHint false (hintM K ρ hint) = .plain TyM.err from rfl, ← hct]
    cases runT K ρ φ st.curTail (.plain TyM.err) w (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })
      <;> simp
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
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stB st₂ false none r T? _ π₁ (hm₁.of_modeEq hmeB)
    (fun e => by cases e) (by omega) htdB'
    hpB hrB hSB (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habB) (hintBelow_none _) hnhw
    (fun _ => by rw [htnB, ← runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hokw) hD₂ bh₂ hrw
  rw [htnB] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) = some (rw', s₂) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  obtain ⟨-, -, -, hS₂⟩ := Strict.fund_all hc w hv.2 st.curTail (.plain TyM.err) _ s₂ rw' hSB hxw'
  have hsz₂ := hK₂.size
  have hne₂ : 0 < st₂.env.size := by omega
  -- the drop
  obtain ⟨s₃, hLD, htt, ⟨hga, hgl⟩, hP₃, hR₃, hme₃, hsz₃, htop₃⟩ := hDr { K with Δ := Δ₂ } ρ₂ φ π₂ (st₂.withTempT r T?) st₃ s₂ m bh₃
    (by rw [size_withTempT]; exact hne₂) hp₂ hr₂ hS₂ hrd
  obtain rfl : v = r := popped_of_topTemps hne₂ htt hk₃
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans
      ((he₂.grow hga hgl).congr rfl rfl (by rw [hk₃.absTy]; rfl) (by rw [hk₃.nextLoan]; rfl))
  have hW : ModeEq st₂ (st₂.withTempT v T?) := ⟨rfl, rfl, rfl, rfl⟩
  have hkept : Kept st st' := by
    refine ⟨hm₀.trans (hK₁.mode.trans (hmeB.trans (hK₂.mode.trans
      (hW.trans (hme₃.trans hme₃'))))), ?_, ?_⟩
    · have e1 := ColumnC.size_of_erase hk₃.env
      rw [size_withTempT] at e1 hsz₃
      omega
    · rw [← topReadings_withTempT st' v T?, ← ColumnC.topReadings_kern hk₃, htop₃, topReadings_withTempT,
        hK₂.top, htopB]
      rfl
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hP₃.of_kern hk₃, hR₃.of_kern hk₃⟩, hkept⟩
  -- the reference's `let`, out of tail position: its tail runs at no hint
  rw [runT_letIn _ _ x u w s hfl, hxu']
  simp only [bind, Option.bind]
  rw [hpb, hth, hxw']
  exact letDrop_eval hLD rw'

/-- **The step for an untyped `let` out of tail position whose right-hand side is not a call, the table reading
it as decided data, in general**, with what the run keeps. ASSUMES 5 facts: `HintSites.UntypedLetTailNoHint`
(checker, proved since main's D124 was merged: `Machine.untypedLetTailNoHint`), `LetTailDecl` (table), `LetPushG`, `LetDropG` (each part checker,
part model), `ValsCongrA` (model); and `Strict.FundCtx K`. The inversion (`Machine.letInvDUn`) is proved. -/
theorem stepLetIn_untyped (hNH : HintSites.UntypedLetTailNoHint) (hLT : LetTailDecl K.D) (hPu : LetPushG)
    (hDr : LetDropG) (hVC : ValsCongrA) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (u w : Term), (∀ f as hd, u ≠ .call f as hd) →
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x u w)
        (fun st => (0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) ∧ st.tailNext = false)
        (· = false) := by
  intro n ih Δ ρ x u w hnc
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.letIn x u w)
      (fun st => (0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) ∧ st.curTail = false) (· = false) :=
    fun st st' typed hint v T? s π hP => letIn_coreU (K := { K with Δ := Δ }) hNH hLT hPu hDr hVC ⟨hc.globals, hc.sorts⟩
      hnc ih st st' typed hint v T? s π ⟨hP.1.1, hP.2⟩
  exact eval_of_coreK_notTail (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

end

end Ochr.Meaning.Steps.Form.Master
