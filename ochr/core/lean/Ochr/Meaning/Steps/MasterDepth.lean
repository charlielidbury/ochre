import Ochr.Meaning.Steps.Master
import Ochr.Meaning.Steps.Machine.StepInv

/-!
# The checker's facts the master's steps use, at any erased depth (lead23, 2026-11-22; docs/31 D155)

Ruling (b) of docs/31 D150: the master's statements (`EvalAt`, `TailAt`) leave the erased depth free (`ModeR`),
because the checker runs erased terms, the bodies of functions whose calls are erased and `clone`'s operand one
depth down, and the induction hypothesis must cover those sub-runs. So the facts about the checker a general
step uses are stated at any depth. The two the proved steps use are the machine lane's `EvalInvR` and `LetInvR`
with the depth free; their proofs are the machine lane's, unchanged but for the mode: the code they read
(`evalAt`'s pre-pass and dispatch, `evalCore`'s `let`) never reads the depth, and the machine lane's proofs
only carried the mode's fields through. PROVED here: `evalInvD`, `letInvD`. Nothing is assumed.

Where the checker does read the depth (`erasedDepth`, `Machine.lean`): `atRuntime` (K2's `unsizedCheck`, K3's
`abstractMatchCheck` and the constructor of an abstract type in `evalCtor`), `readPlace`'s capture-move check
and `capture`'s; `withErased`, `withRuntime`, `inStatement` write it (`Env.lean`). Each read rejects at depth `0`
only. The steps whose code reaches them (`place`, `assign`, `ctor`, `matchInd`, `fix`) state their facts at any
depth with the check skipped above depth `0`. The smallest programs accepted only above depth `0` are pinned in
`MasterGuards` (`DepthProbe`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

/-- The machine lane's mode equality is the form's. -/
theorem modeEq_form {a b : MState} (h : Machine.ModeEq a b) : Form.ModeEq a b :=
  ⟨h.headEval, h.copying, h.inPlace, h.erased⟩

/-- **`eval` around `evalCore`, at any erased depth** (`Master.EvalInvD`): `evalInvR`'s proof with the depth free. -/
theorem evalInvD : EvalInvD := by
  intro n typed t hint st st' bh v T? D hm hD hv hc hany hpr htd h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_eval _ _ _ _) h)
  rw [Ochr.eval.eq_1] at h
  obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
  obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
  have hka := hla.kern
  obtain ⟨hhe, htde, htne⟩ := hla.tail
  obtain ⟨st₀, st₁, bh', hk₀, hme₀, hct, htn, htd₀, hcd, hcore, hk₁, hme₁⟩ :=
    evalAt_inv (dd := D.declOf (DecideScope.topReadings st) t) (hhe ▸ hm.headEval) hv hc (htde ▸ htd)
      (fun s b d s' hks hr => by
        have := decTab_declOf_at (DecTab.of_kern (hka.trans hks) hDst) hr
        rw [← this, ColumnC.topReadings_kern (hka.trans hks)]) hany hpr hat
  have hk0 : Kern st st₀ := hka.trans hk₀
  have hsa : Form.ModeEq st { sa with headEval := false } :=
    ⟨hm.headEval, hla.modeEq.copying, hla.modeEq.inPlace, hla.modeEq.erased⟩
  refine ⟨st₀, st₁, bh', hk0, hsa.trans (modeEq_form hme₀).symm, by rw [hct, ← htne], htn, htd₀, ?_, hcore,
    hk₁.trans hlb.kern, (modeEq_form hme₁).trans (modeEq_form hlb.modeEq)⟩
  rw [hcd, ColumnC.topReadings_kern hk0]

/-- **`evalCore` of a typed `let`, at any erased depth**: the machine lane's `LetInvR` with no mode hypothesis
and the mode at `u`'s entry the `let`'s (`ModeEq`) where `LetInvR` concludes `Mode`. -/
def LetInvD : Prop :=
  ∀ (n : Nat) (h : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.letIn h u w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r : Value) (T₀ : Option Value) (p : Bool)
      (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Form.ModeEq st st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ stB.tailDecl = st.curDecl ∧
      Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      D.declOf (DecideScope.topReadings st) u = du ∧
      Kern { st₁ with env := Env.pushBindE st₁.env h T₀ v₀ p du } stB ∧ Form.ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ Form.ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂

set_option maxHeartbeats 4000000 in
/-- **`LetInvD`, PROVED**: `letInvR`'s proof; the mode at `u`'s entry is the `let`'s state with `wantTy` set. -/
theorem letInvD : LetInvD := by
  intro n x u w hint st st' bh v T? D htn htd hD h
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
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false] at h₅
  rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
  peel h₅
  simp only [if_true, ite_true] at h₅
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

end Ochr.Meaning.Steps.Machine
