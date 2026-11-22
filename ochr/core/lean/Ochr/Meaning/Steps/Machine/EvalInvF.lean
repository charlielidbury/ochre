import Ochr.Meaning.Steps.Machine.EvalInv

/-!
# `eval` around `evalCore`, with the flags a run's type depends on (lead27, 2026-11-22; docs/31 D184)

`evalAt_invF` is machine10's `evalAt_invT` (`Machine/EvalInvT.lean`) with three more conjuncts, read off `evalAt`'s
code: the state `evalCore` starts from wants the result's type exactly when the run is typed or the context asked
for it (`wantHere := typed || wantTy`). The call-deferral flag (`deferCallTy`): since main's D130 (machine12's merge)
`evalAt` CONSUMES it when the evaluation starts, in the same update as the other one-shot flags: `evalCore` starts with
the flag clear, its copy `deferHere` holding the entry's flag (what `evalCall` reads), and the record of a deferred
call's type (`callTyLater`) cleared; at the exit the flag is the core's. (Before D130 `evalAt` never wrote the flag,
and this said `evalCore` started with the entry's flag.)
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

set_option maxHeartbeats 4000000 in
/-- **`evalAt_inv'`, with the typing flag and the type-wanted and deferral flags** (lead27; docs/31 D184; restated at
main's D130 by machine12): `evalAt` sets `wantHere := typed || wantTy` and the typing flag before `evalCore`, and
consumes the deferral flag: `evalCore` starts with `deferCallTy` clear, `deferHere` the entry's flag and the record
`callTyLater` cleared. -/
theorem evalAt_invF {n : Nat} {typed : Bool} {t : Term} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} {dd : DeclInfo}
    (hh : st.headEval = false) (hv : ∀ w, t ≠ .val w) (hc : ∀ f as h, t ≠ .call f as h)
    (htd : st.tailDecl = none ∨ st.tailDecl = some dd)
    (hdd : ∀ s b d s', Kern st s → Runs (withLive true (Ochr.declOf n false [] [] t)) s b d s' → d = dd)
    (hany : dd ≠ .any) (hpr : dd.isProof = false)
    (h : Runs (Ochr.evalAt (n + 1) typed t hint) st bh r st') :
    ∃ st₀ st₁ bh', Kern st st₀ ∧ ModeEq st₀ { st with headEval := false } ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.curDecl = some dd ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' r st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' ∧ st'.tailDecl = st₁.tailDecl ∧ st₀.typing = typed ∧
      st₀.wantHere = (typed || st.wantTy) ∧ st₀.deferCallTy = false ∧ st₀.deferHere = st.deferCallTy ∧
      st₀.callTyLater = none ∧ st'.deferCallTy = st₁.deferCallTy := by
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
         refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, hcore, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl
         · rfl
         · rfl
         · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
         · exact ⟨rfl, rfl, rfl, rfl⟩
         · rfl
         · rfl
         · rfl
         · rfl
         · rfl
         · rfl
         · rfl)
      | skip)

end Ochr.Meaning.Steps.Machine
