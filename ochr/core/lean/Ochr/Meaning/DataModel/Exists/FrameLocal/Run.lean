import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup

/-!
# Frame locality, part 5: the induction over the run (exists3; IN PROGRESS, outside the default build)

**`runT_qset`** (the restatement of `General.runT_frameLocal`, docs/34 §18.5): at a state where the
bindings at `Q` hold constant whole values the strict test admits (`Adm`), for a term none of whose
free variables names a position of `Q` (`VarsAvoid`), under local decisions (`DecLocal`), the run at
`qset Q β' s` is the run at `s` with `qset Q β'` applied to its final state. Its use: the canonical
frame of a record key and the actual frame differ only at earlier fields no field type mentions
(`IndDecl.indexFields`), whose `teleFrame` bindings are constant (`faithBind`).

Assumes, besides `DecLocal`: the globals carry no label (`hK`, as every run lemma does) and
`capOrder`'s indices are free variables (`hcap`; true, `Array.qsort` permutes, but its recursion is
private in Lean core: a ruling is asked to sort with `List.mergeSort`).

Each clause: rewrite the scope (`Adm.scope`), then the clause's primitives' `Comm` lemmas
(`Prims.lean`, `Join.lean`), the subterms' by the induction; the state after a subterm is `Adm` again
by `Adm.next`, its fix read off the induction at `β' := β` (`fix_of_comm`), its layout by
`runT_rinv`.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- After a subterm: the next state is admissible, from the equation at `β` and the run's layout. -/
theorem Adm.after (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {tl : Bool} {hint : TyS} {u : Term} {a : Res} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : runT K ρ φ tl hint u s = some (a, s₁))
    (hc : Comm Q β (runT K ρ φ tl hint u) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  obtain ⟨hR₁, -, he, -⟩ := runT_rinv K ρ φ _ hK tl u hint s s₁ a hR hu
  exact ⟨hA.next he (fix_of_comm hc hA.twin.fix hu), hR₁, he⟩

mutual
theorem runT_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
    (hcap : ∀ t i, i ∈ capOrder t → i ∈ t.freeVars) :
    ∀ (tl : Bool) (t : Term) (hint : TyS) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → VarsAvoid Q s t → RInv (fun _ => True) s → Comm Q β' (runT K ρ φ tl hint t) s
  | tl, .place p, hint, s, Q, β, β', hA, hV, _ => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    exact comm_erasedIf (comm_guarded (contentOk_qset K φ hA.twin.pre' p)
      (fun _ => readPlace_qset K φ hA.twin.pre' (rAvoid_of_vars hV (root_mem_place p)) _))
  | tl, .const n, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .sort l, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .nat, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .unit, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .zero, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .tt, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .val v, hint, s, Q, β, β', _, _, _ => by
    unfold Comm; rw [runT_val_def, runT_val_def]
    cases v <;> first
      | rfl
      | (simp only [strictVal, SM.strictS, pure]; split <;> (try split) <;> rfl)
  | tl, .succ u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD hcap false u _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .ref A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD hcap false A _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .seq u w, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVw : VarsAvoid Q s w := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_bind (runT_qset hK hD hcap false u _ s Q β β' hA hVu hR) fun a s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD hcap false u _ s Q β β hA.self hVu hR)
    refine comm_bind (comm_guardMod (discardOk_qset K φ hA₁.twin.pre' a.2)
      (fun _ => discardEnd_qset hA₁.twin.pre' a.2)) fun _ s₂ h2 => ?_
    have e₂ : s₂ = discardEnd a.2 s₁ := (SM.guardMod_some h2).2
    subst e₂
    have hfix₂ : qset Q β (discardEnd a.2 s₁) = discardEnd a.2 s₁ := by
      rw [← discardEnd_qset hA₁.twin.pre a.2, hA₁.twin.fix]
    obtain ⟨hR₂, he₂, -⟩ := discardEnd_props (fun _ => True) hR₁ a.2
    have hA₂ := hA₁.next (s₁ := discardEnd a.2 s₁) he₂ hfix₂
    exact runT_qset hK hD hcap tl w _ _ Q β β' hA₂ ((hVw.of_envLe he₁).of_envLe he₂) hR₂
  | _, _, _, _, _, _, _, _, _, _ => sorry
termination_by structural tl t => t
end

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
