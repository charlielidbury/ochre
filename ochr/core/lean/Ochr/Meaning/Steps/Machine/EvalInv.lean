import Ochr.Meaning.Steps.Machine.Inv
import Ochr.Meaning.Steps.ColumnC

/-!
# `eval` around `evalCore` (the column's `EvalInv`, in the form proposed to the lead)

A successful run of `eval (n + 2)` on a term the pre-pass classifies as neither erased nor a proof is
a run of `evalCore n` between two states with the entry's and the exit's kernels: `located` and
`noteValue` move only the editor's locations and the log (`Runs.located_inv`, `Runs.noteValue_inv`),
and `evalAt` sets the one-shot fields, reads the reading and the pre-pass, runs `evalCore` on the
state itself (not on a private copy: the pre-pass says "not erased"), and after it restores the
typing flags and sets the erasure flags (the after-the-fact classification, which reads and writes
nothing else: `keep_getFlags`, `keep_leafProof`, …).

The pre-pass is pinned by the READING, not by `D.flags` (the lead's statement): where the context hands
the term its reading (`tailDecl`) no `declOf` runs, and the table's `flags` and `declOf` are tied only
by a run, so `D.flags = (false, false)` would not pin it. So the hypotheses are: the reading (handed or
computed) is `D.declOf` at the entry's top readings, it is neither `.any` (the pre-pass would defer to
the after-the-fact classification) nor a proof, and the term is neither an embedded value nor a call.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

/-- The mode's fields equal. -/
structure ModeEq (a b : MState) : Prop where
  headEval : a.headEval = b.headEval
  copying : a.copying = b.copying
  inPlace : a.inPlace = b.inPlace
  erased : a.erasedDepth = b.erasedDepth

set_option maxHeartbeats 4000000 in
theorem evalAt_inv {n : Nat} {typed : Bool} {t : Term} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} {dd : DeclInfo}
    (hh : st.headEval = false) (hv : ∀ w, t ≠ .val w) (hc : ∀ f as h, t ≠ .call f as h)
    (htd : st.tailDecl = none ∨ st.tailDecl = some dd)
    (hdd : ∀ s b d s', Kern st s → Runs (withLive true (Ochr.declOf n false [] [] t)) s b d s' → d = dd)
    (hany : dd ≠ .any) (hpr : dd.isProof = false)
    (h : Runs (Ochr.evalAt (n + 1) typed t hint) st bh r st') :
    ∃ st₀ st₁ bh', Kern st st₀ ∧ ModeEq st₀ { st with headEval := false } ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some dd ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' r st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' := by
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
         refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, hcore, ?_, ?_⟩
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl
         · rfl
         · rfl
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩)
      | skip)

set_option maxHeartbeats 4000000 in
/-- `evalAt_inv`, with the reading handed down kept across the classification after the run. -/
theorem evalAt_inv' {n : Nat} {typed : Bool} {t : Term} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} {dd : DeclInfo}
    (hh : st.headEval = false) (hv : ∀ w, t ≠ .val w) (hc : ∀ f as h, t ≠ .call f as h)
    (htd : st.tailDecl = none ∨ st.tailDecl = some dd)
    (hdd : ∀ s b d s', Kern st s → Runs (withLive true (Ochr.declOf n false [] [] t)) s b d s' → d = dd)
    (hany : dd ≠ .any) (hpr : dd.isProof = false)
    (h : Runs (Ochr.evalAt (n + 1) typed t hint) st bh r st') :
    ∃ st₀ st₁ bh', Kern st st₀ ∧ ModeEq st₀ { st with headEval := false } ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some dd ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' r st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' ∧ st'.tailDecl = st₁.tailDecl := by
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
         refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, hcore, ?_, ?_, ?_⟩
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl
         · rfl
         · rfl
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl)
      | skip)

/-! ## `eval` -/

theorem LocsEq.kern {a b : MState} (h : LocsEq a b) : Kern a b := by
  unfold LocsEq at h; rw [← h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LocsEq.modeEq {a b : MState} (h : LocsEq a b) : ModeEq a b := by
  unfold LocsEq at h; rw [← h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem LocsEq.tail {a b : MState} (h : LocsEq a b) :
    a.headEval = b.headEval ∧ a.tailDecl = b.tailDecl ∧ a.tailNext = b.tailNext := by
  unfold LocsEq at h; rw [← h]; exact ⟨rfl, rfl, rfl⟩

theorem Mode.of_modeEq {a b : MState} (hm : Mode a) (h : ModeEq a b) : Mode b :=
  ⟨h.headEval ▸ hm.headEval, h.copying ▸ hm.copying, h.inPlace ▸ hm.inPlace, h.erased ▸ hm.erased⟩

theorem ModeEq.symm {a b : MState} (h : ModeEq a b) : ModeEq b a :=
  ⟨h.headEval.symm, h.copying.symm, h.inPlace.symm, h.erased.symm⟩

theorem ModeEq.trans {a b c : MState} (h₁ : ModeEq a b) (h₂ : ModeEq b c) : ModeEq a c :=
  ⟨h₁.headEval.trans h₂.headEval, h₁.copying.trans h₂.copying, h₁.inPlace.trans h₂.inPlace, h₁.erased.trans h₂.erased⟩

/-- **`EvalInv` in the proposed form**: the lead's `EvalInv` with the pre-pass pinned by the reading
(`hany`, `hpr`) and the term not a call (`hc`) in place of `D.flags (topReadings st) t = (false, false)`. -/
def EvalInvR : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    Mode st → DecTab D st' → (∀ w, t ≠ .val w) → (∀ f as h, t ≠ .call f as h) →
    D.declOf (DecideScope.topReadings st) t ≠ .any → (D.declOf (DecideScope.topReadings st) t).isProof = false →
    (st.tailDecl = none ∨ st.tailDecl = some (D.declOf (DecideScope.topReadings st) t)) →
    Runs (Ochr.eval (n + 2) typed t hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ Mode st₀ ∧ st₀.curTail = st.tailNext ∧ st₀.tailNext = false ∧
      st₀.tailDecl = none ∧ st₀.curDecl = some (D.declOf (DecideScope.topReadings st₀) t) ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ (Mode st₁ → Mode st')

theorem evalInvR : EvalInvR := by
  intro n typed t hint st st' bh v T? D hm hD hv hc hany hpr htd h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_eval _ _ _ _) h)
  rw [Ochr.eval.eq_1] at h
  obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
  obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
  have hka := hla.kern
  obtain ⟨hhe, htde, htne⟩ := hla.tail
  have hra : DecideScope.topReadings sa = DecideScope.topReadings st := (ColumnC.topReadings_kern hka).symm
  obtain ⟨st₀, st₁, bh', hk₀, hme₀, hct, htn, htd₀, hcd, hcore, hk₁, hme₁⟩ :=
    evalAt_inv (dd := D.declOf (DecideScope.topReadings st) t) (hhe ▸ hm.headEval) hv hc (htde ▸ htd)
      (fun s b d s' hks hr => by
        have := decTab_declOf_at (DecTab.of_kern (hka.trans hks) hDst) hr
        rw [← this, ColumnC.topReadings_kern (hka.trans hks)]) hany hpr hat
  have hk0 : Kern st st₀ := hka.trans hk₀
  have hmA : Mode { sa with headEval := false } :=
    ⟨rfl, hla.modeEq.copying ▸ hm.copying, hla.modeEq.inPlace ▸ hm.inPlace, hla.modeEq.erased ▸ hm.erased⟩
  refine ⟨st₀, st₁, bh', hk0, Mode.of_modeEq hmA hme₀.symm, by rw [hct, ← htne], htn, htd₀, ?_, hcore,
    hk₁.trans hlb.kern, fun h1 => Mode.of_modeEq h1 (hme₁.trans hlb.modeEq)⟩
  rw [hcd, ColumnC.topReadings_kern hk0]

end Ochr.Meaning.Steps.Machine
