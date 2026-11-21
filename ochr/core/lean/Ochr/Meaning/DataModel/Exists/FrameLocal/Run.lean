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

theorem mem_placeOccsList {a : Term} {as : List Term} (ha : a ∈ as) {c : Nat} {x : Nat × Place × PKind}
    (hx : x ∈ a.placeOccs c) : x ∈ Term.placeOccsList c as := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
    rw [Term.placeOccsList, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact .inl hx
    · exact .inr (ih h)

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
  | tl, .eq A a b, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVa : VarsAvoid Q s a := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVb : VarsAvoid Q s b := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_onCopy (comm_bind (runT_qset hK hD hcap false A _ s Q β β' hA hVA hR) fun x s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD hcap false A _ s Q β β hA.self hVA hR)
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD hcap false a _ s₁ Q β β' hA₁ (hVa.of_envLe he₁) hR₁))
      fun y s₂ h2 => ?_
    have e₂ := SM.onCopy_state h2; subst e₂
    obtain ⟨va, _⟩ := y
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD hcap false b _ s₂ Q β β' hA₁ (hVb.of_envLe he₁) hR₁))
      fun z s₃ h3 => ?_
    have e₃ := SM.onCopy_state h3; subst e₃
    obtain ⟨vb, _⟩ := z
    unfold Comm; dsimp only; split <;> rfl
  | tl, .cong c h, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVh : VarsAvoid Q s h := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    exact comm_onCopy (comm_bind (runT_qset hK hD hcap false h _ s Q β β' hA hVh hR) fun _ _ _ => comm_pure _ _)
  | tl, .ascribe u A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_strictS (comm_bind (comm_onCopy (runT_qset hK hD hcap false A _ s Q β β' hA hVA hR))
      fun x s₁ h1 => ?_))
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (runT_qset hK hD hcap false u _ s₁ Q β β' hA hVu hR) fun y s₂ _ => ?_
    obtain ⟨v, R⟩ := y
    exact comm_ite (P := fun s => labTyOk s R.label TA.asTy) Iff.rfl (fun _ => rfl) (fun _ => rfl)
  | tl, .tind n args, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    cases hd : List.find? (fun x => x.name == n) K.Γ with
    | none => rfl
    | some d =>
      dsimp only
      refine comm_bind (runParams_qset hK hD hcap _ args 0 [] s Q β β' hA
        (fun a ha => hV.sub fun x hx => by simpa [Term.placeOccs] using mem_placeOccsList ha hx) hR) fun _ _ _ => ?_
      unfold Comm; dsimp only; split <;> rfl
  | _, _, _, _, _, _, _, _, _, _ => sorry

theorem runParams_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
    (hcap : ∀ t i, i ∈ capOrder t → i ∈ t.freeVars) (d : IndDecl) :
    ∀ (as : List Term) (i : Nat) (earlier : List Sem) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → (∀ a ∈ as, VarsAvoid Q s a) → RInv (fun _ => True) s →
      Comm Q β' (runParams K ρ φ d i earlier as) s
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runParams]
    refine comm_bind (comm_onCopy (runT_qset hK hD hcap false a _ s Q β β' hA (hV a (by simp)) hR)) fun x s₁ h1 => ?_
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨v, _⟩ := x
    dsimp only
    exact comm_bind (runParams_qset hK hD hcap d as (i + 1) (earlier ++ [v]) s₁ Q β β' hA
      (fun b hb => hV b (by simp [hb])) hR) fun _ _ _ => comm_pure _ _
end

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
