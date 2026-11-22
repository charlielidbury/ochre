import Ochr.Meaning.Steps.MasterPlace

/-!
# `EvalInvDT`, proved (machine10)

`Master.EvalInvDT` (`Steps/MasterPlace.lean`, the lead lane's fact under `stepPlace_direct`) is `EvalInvD`
(`Machine.evalInvD`, `Steps/MasterDepth.lean`) with one more conjunct: the state `evalCore` starts from has the
typing flag of the run. `evalAt` sets `typing := typed` immediately before `evalCore` on the unerased path (the
hypotheses exclude the erased one: the reading is neither `.any` nor a proof, and the term is not a call), so the
conjunct is `rfl` at the point `evalAt_inv'` reaches `evalCore`. `evalAt_invT` is `evalAt_inv'` with that conjunct;
`evalInvDT` is `evalInvD`'s proof through it.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

set_option maxHeartbeats 4000000 in
/-- `evalAt_inv'`, with the typing flag at `evalCore`'s entry. -/
theorem evalAt_invT {n : Nat} {typed : Bool} {t : Term} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} {dd : DeclInfo}
    (hh : st.headEval = false) (hv : ∀ w, t ≠ .val w) (hc : ∀ f as h, t ≠ .call f as h)
    (htd : st.tailDecl = none ∨ st.tailDecl = some dd)
    (hdd : ∀ s b d s', Kern st s → Runs (withLive true (Ochr.declOf n false [] [] t)) s b d s' → d = dd)
    (hany : dd ≠ .any) (hpr : dd.isProof = false)
    (h : Runs (Ochr.evalAt (n + 1) typed t hint) st bh r st') :
    ∃ st₀ st₁ bh', Kern st st₀ ∧ ModeEq st₀ { st with headEval := false } ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some dd ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' r st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' ∧ st'.tailDecl = st₁.tailDecl ∧ st₀.typing = typed := by
  unfold Ochr.evalAt at h
  peel h
  rw [if_pos] at h
  rotate_left
  · rw [hh]; cases t <;> first | rfl | exact absurd rfl (hv _)
  rcases htd with htd | htd <;> rw [htd] at h
  case' inl =>
    obtain ⟨d?, s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
    clear h
    obtain ⟨d, hd', rfl⟩ := Runs.map_inv hd
    clear hd
    have hs := runs_keep (keep_withLive _ ((decideKeep n).2.2.2.2.2.2.2.2.1 _ _ _ _)) hd'
    subst hs
    obtain rfl := hdd _ _ _ _ (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hd'
    clear hd'
    peel h₁
    have h := h₁; clear h₁
  all_goals peel h
  all_goals obtain ⟨pre, s₂, b₂, hp, h₁⟩ := Runs.bind_inv h
  all_goals clear h
  all_goals obtain ⟨rfl, rfl⟩ := preFlags_inv hp hany hpr hc
  all_goals clear hp
  all_goals rw [runs_get_bind] at h₁
  all_goals rw [runs_modify_bind] at h₁
  all_goals obtain ⟨r', s₃, b₃, hcore, h₂⟩ := Runs.bind_inv h₁
  all_goals clear h₁
  all_goals replace hcore := Runs.onFail_inv hcore
  all_goals rw [if_neg (by decide)] at hcore
  all_goals rw [runs_modify_bind] at h₂
  all_goals split at h₂
  all_goals first | exact absurd rfl (hc _ _ _) | skip
  all_goals repeat first
    | (obtain ⟨x, s₄, b₄, hcl, h₃⟩ := Runs.bind_inv h₂
       refine (fun (hs : s₄ = _) => ?_) (runs_keep ?hk hcl)
       case hk =>
         keep_go
         all_goals first
           | exact keep_getFlags | exact keep_ctorIsProof _ | exact keep_jErased _ _
           | exact keep_leafProof _ _ _ | exact (decideKeep _).2.2.2.2.2.2.2.2.2.1 _ _ _ _ _ _
       subst hs
       clear hcl h₂
       have h₂ := h₃
       clear h₃)
  all_goals (
    repeat (any_goals first
      | (simp only [runs_modify_bind, runs_pure_bind', pure_bind,
           runs_err_bind, runs_err_iff, setFlags, Bool.false_eq_true, if_false, ite_false] at h₂)
      | (split at h₂))
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
         refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, hcore, ?_, ?_, ?_, ?_⟩
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl
         · rfl
         · rfl
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl)
      | skip)

/-- **`EvalInvDT`, PROVED**: `evalInvD`'s proof, through `evalAt_invT`. -/
theorem evalInvDT : Master.EvalInvDT := by
  intro n typed t hint st st' bh v T? D hm hD hv hc hany hpr htd h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_eval _ _ _ _) h)
  rw [Ochr.eval.eq_1] at h
  obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
  obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
  have hka := hla.kern
  obtain ⟨hhe, htde, htne⟩ := hla.tail
  obtain ⟨st₀, st₁, bh', hk₀, hme₀, hct, htn, htd₀, hcd, hcore, hk₁, hme₁, -, hty⟩ :=
    evalAt_invT (dd := D.declOf (DecideScope.topReadings st) t) (hhe ▸ hm.headEval) hv hc (htde ▸ htd)
      (fun s b d s' hks hr => by
        have := decTab_declOf_at (DecTab.of_kern (hka.trans hks) hDst) hr
        rw [← this, ColumnC.topReadings_kern (hka.trans hks)]) hany hpr hat
  have hk0 : Kern st st₀ := hka.trans hk₀
  have hsa : Form.ModeEq st { sa with headEval := false } :=
    ⟨hm.headEval, hla.modeEq.copying, hla.modeEq.inPlace, hla.modeEq.erased⟩
  refine ⟨st₀, st₁, bh', hk0, hsa.trans (modeEq_form hme₀).symm, by rw [hct, ← htne], htn, htd₀, ?_, hty, hcore,
    hk₁.trans hlb.kern, (modeEq_form hme₁).trans (modeEq_form hlb.modeEq)⟩
  rw [hcd, ColumnC.topReadings_kern hk0]

end Ochr.Meaning.Steps.Machine
