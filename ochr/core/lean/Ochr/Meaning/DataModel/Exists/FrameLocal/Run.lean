import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup

/-!
# Frame locality, part 5: the induction over the run (exists3; IN PROGRESS, outside the default build)

**`runT_qset`** (the restatement of `General.runT_frameLocal`, docs/34 §18.5): at a state where the
bindings at `Q` hold constant whole values the strict test admits (`Adm`), for a term none of whose
free variables names a position of `Q` (`VarsAvoid`), under local decisions (`DecLocal`), the run at
`qset Q β' s` is the run at `s` with `qset Q β'` applied to its final state. Its use: the canonical
frame of a record key and the actual frame differ only at earlier fields no field type mentions
(`IndDecl.indexFields`), whose `teleFrame` bindings are constant (`faithBind`).

Assumes, besides `DecLocal`: the globals carry no label (`hK`, as every run lemma does).
(`capOrder`'s indices are free variables by `mem_capOrder`, since `capOrder` became an insertion
sort, exists4.)

Each clause: rewrite the scope (`Adm.scope`), then the clause's primitives' `Comm` lemmas
(`Prims.lean`, `Join.lean`), the subterms' by the induction; the state after a subterm is `Adm` again
by `Adm.next`, its fix read off the induction at `β' := β` (`fix_of_comm`), its layout by
`runT_rinv`.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

section
variable {Q : Pos → Prop} {β β' : Pos → SBinding}

theorem envLe_obsStep (ws : List Sem) (s : SState) (qi : Place × Nat) : EnvLe s (obsStep ws s qi) := by
  unfold obsStep
  split
  · exact envLe_setAt _ _ _
  · exact EnvLe.refl _

theorem envLe_foldl_obsStep (ws : List Sem) : ∀ (l : List (Place × Nat)) (s : SState), EnvLe s (l.foldl (obsStep ws) s)
  | [], s => EnvLe.refl s
  | a :: l, s => (envLe_obsStep ws s a).trans (envLe_foldl_obsStep ws l _)

theorem envLe_obsEnd (reps : List Place) (ws : List Sem) (s : SState) : EnvLe s (obsEnd reps ws s) :=
  (envLe_foldl_obsStep ws _ s).trans (envLe_foldl_endLabel _ _)

/-- `Id`'s typing of the written values reads the types at the re-pointed places, outside `Q`. -/
theorem obsTyped_qset (R : DataRead) {reps : List Place} (ws : List Sem) {s : SState}
    (hq : ∀ q ∈ reps, RAvoid Q s q) : obsTyped R reps ws (qset Q β s) ↔ obsTyped R reps ws s := by
  unfold obsTyped
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun q => forall_congr' fun w =>
    imp_congr_right fun hi => imp_congr_right fun _ => ?_)
  rw [qset_resolve]
  cases hr : resolve s q with
  | none => exact Iff.rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    rw [qset_tyAt_not s (hq q (List.mem_of_getElem? hi) pos steps hr)]

/-- **`Id`'s comparison across the transform.** Two sides' end states, each fixed by `qset Q β`,
compared at the start's positions: the comparison at `qset Q β'` of each is the comparison of the
two. Off `Q` the transform changes nothing; at `Q` both sides read the same constant, `β`'s on one
side and `β'`'s on the other. -/
theorem observation_qset_iff (φ : Future) (reps : List Place) (ws : List Sem) {s X₁ X₂ : SState}
    (h₁ : Pre Q β' X₁) (h₁' : Pre Q β X₁) (f₁ : qset Q β X₁ = X₁) (e₁ : EnvLe s X₁)
    (h₂ : Pre Q β' X₂) (h₂' : Pre Q β X₂) (f₂ : qset Q β X₂ = X₂) (e₂ : EnvLe s X₂)
    (hq : ∀ q ∈ reps, RAvoid Q s q) (r₁ r₂ : Res) :
    observation φ reps ws s.positions r₁ (qset Q β' X₁) = observation φ reps ws s.positions r₂ (qset Q β' X₂) ↔
      observation φ reps ws s.positions r₁ X₁ = observation φ reps ws s.positions r₂ X₂ := by
  rw [observation_eq, observation_eq, observation_eq, observation_eq,
    obsEnd_qset reps ws h₁ (fun q hq' => (hq q hq').of_envLe e₁),
    obsEnd_qset reps ws h₂ (fun q hq' => (hq q hq').of_envLe e₂)]
  have F₁ : qset Q β (obsEnd reps ws X₁) = obsEnd reps ws X₁ := by
    rw [← obsEnd_qset reps ws h₁' (fun q hq' => (hq q hq').of_envLe e₁), f₁]
  have F₂ : qset Q β (obsEnd reps ws X₂) = obsEnd reps ws X₂ := by
    rw [← obsEnd_qset reps ws h₂' (fun q hq' => (hq q hq').of_envLe e₂), f₂]
  have E₁ := e₁.trans (envLe_obsEnd reps ws X₁)
  have E₂ := e₂.trans (envLe_obsEnd reps ws X₂)
  simp only [List.cons.injEq, List.map_inj_left]
  refine and_congr Iff.rfl (forall_congr' fun p => imp_congr_right fun hp => ?_)
  by_cases hQ : Q p
  · obtain ⟨f, i, rfl⟩ := pos_bind h₁ hQ
    rw [qset_valAt_of _ hQ (E₁.mem hp), qset_valAt_of _ hQ (E₂.mem hp), fix_valAt F₁ hQ (E₁.mem hp),
      fix_valAt F₂ hQ (E₂.mem hp)]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [qset_valAt_not _ hQ, qset_valAt_not _ hQ]

end

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

/-- The join's drop names only places outside `Q`: the entry's moved places (a whole binding has
none) and places rooted at the match's free variables (`DecLocal.join`). -/
theorem joinMoves_avoid (hD : DecLocal K.D) {Q : Pos → Prop} {β β' : Pos → SBinding} {mt : Term} {S₁ : SState}
    (hA₁ : Adm K Q β β' S₁) (hVm : VarsAvoid Q S₁ mt) (sc : List DeclInfo) :
    ∀ q ∈ K.D.joinMoves sc (movedPlaces φ S₁) mt, RAvoid Q S₁ q := fun q hq =>
  (hD.join _ _ _ _ hq).elim (rAvoid_of_moved hA₁.twin.pre hA₁.twin.fix hA₁.good) (rAvoid_of_vars hVm)

/-- [Entry]'s captures name only places outside `Q` (`DecLocal.caps`). -/
theorem blockCaps_avoid (hD : DecLocal K.D) {Q : Pos → Prop} {β β' : Pos → SBinding} {mt : Term} {s : SState}
    (hA : Adm K Q β β' s) (hVm : VarsAvoid Q s mt) (sc : List DeclInfo) :
    ∀ qk ∈ (K.D.blockCaps sc (movedPlaces φ s) mt).2, RAvoid Q s qk.1 := fun qk hq =>
  (hD.caps _ _ _ _ hq).elim (rAvoid_of_moved hA.twin.pre hA.twin.fix hA.good) (rAvoid_of_vars hVm)

/-- After an arm: as `Adm.after`. -/
theorem Adm.afterArm (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {tl : Bool} {hint : TyS} {c : Nat} {arms : List (Hint × Term)} {a : Res} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : runArm K ρ φ tl hint c arms s = some (a, s₁))
    (hc : Comm Q β (runArm K ρ φ tl hint c arms) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  obtain ⟨hR₁, -, he, -⟩ := runArm_rinv K ρ φ _ hK tl arms hint c s s₁ a hR hu
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

theorem mem_placeOccsArms {a : Hint × Term} {as : List (Hint × Term)} (ha : a ∈ as) {c : Nat}
    {x : Nat × Place × PKind} (hx : x ∈ a.2.placeOccs c) : x ∈ Term.placeOccsArms c as := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
    obtain ⟨h, t⟩ := b
    rw [Term.placeOccsArms, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h'
    · exact .inl hx
    · exact .inr (ih h')

theorem root_mem_matchNat (p : Place) (z u : Term) : p.root ∈ (Term.matchNat p z u).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .scrut, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

theorem root_mem_matchInd (p : Place) (n : String) (arms : List (Hint × Term)) :
    p.root ∈ (Term.matchInd p n arms).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .scrut, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

mutual
theorem runT_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
 :
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
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD false u _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .ref A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD false A _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .seq u w, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVw : VarsAvoid Q s w := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_bind (runT_qset hK hD false u _ s Q β β' hA hVu hR) fun a s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false u _ s Q β β hA.self hVu hR)
    refine comm_bind (comm_guardMod (discardOk_qset K φ hA₁.twin.pre' a.2)
      (fun _ => discardEnd_qset hA₁.twin.pre' a.2)) fun _ s₂ h2 => ?_
    have e₂ : s₂ = discardEnd a.2 s₁ := (SM.guardMod_some h2).2
    subst e₂
    have hfix₂ : qset Q β (discardEnd a.2 s₁) = discardEnd a.2 s₁ := by
      rw [← discardEnd_qset hA₁.twin.pre a.2, hA₁.twin.fix]
    obtain ⟨hR₂, he₂, -⟩ := discardEnd_props (fun _ => True) hR₁ a.2
    have hA₂ := hA₁.next (s₁ := discardEnd a.2 s₁) he₂ hfix₂
    exact runT_qset hK hD tl w _ _ Q β β' hA₂ ((hVw.of_envLe he₁).of_envLe he₂) hR₂
  | tl, .eq A a b, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVa : VarsAvoid Q s a := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVb : VarsAvoid Q s b := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_onCopy (comm_bind (runT_qset hK hD false A _ s Q β β' hA hVA hR) fun x s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false A _ s Q β β hA.self hVA hR)
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD false a _ s₁ Q β β' hA₁ (hVa.of_envLe he₁) hR₁))
      fun y s₂ h2 => ?_
    have e₂ := SM.onCopy_state h2; subst e₂
    obtain ⟨va, _⟩ := y
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD false b _ s₂ Q β β' hA₁ (hVb.of_envLe he₁) hR₁))
      fun z s₃ h3 => ?_
    have e₃ := SM.onCopy_state h3; subst e₃
    obtain ⟨vb, _⟩ := z
    unfold Comm; dsimp only; split <;> rfl
  | tl, .cong c h, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVh : VarsAvoid Q s h := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    exact comm_onCopy (comm_bind (runT_qset hK hD false h _ s Q β β' hA hVh hR) fun _ _ _ => comm_pure _ _)
  | tl, .ascribe u A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_strictS (comm_bind (comm_onCopy (runT_qset hK hD false A _ s Q β β' hA hVA hR))
      fun x s₁ h1 => ?_))
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (runT_qset hK hD false u _ s₁ Q β β' hA hVu hR) fun y s₂ _ => ?_
    obtain ⟨v, R⟩ := y
    exact comm_ite (P := fun s => labTyOk s R.label TA.asTy) Iff.rfl (fun _ => rfl) (fun _ => rfl)
  | tl, .tind n args, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    cases hd : List.find? (fun x => x.name == n) K.Γ with
    | none => rfl
    | some d =>
      dsimp only
      refine comm_bind (runParams_qset hK hD _ args 0 [] s Q β β' hA
        (fun a ha => hV.sub fun x hx => by simpa [Term.placeOccs] using mem_placeOccsList ha hx) hR) fun _ _ _ => ?_
      unfold Comm; dsimp only; split <;> rfl
  | tl, .id A t u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVt : VarsAvoid Q s t := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have cA := comm_onCopy (runT_qset hK hD false A (.plain TyM.err) s Q β β' hA hVA hR)
    unfold Comm at cA
    rw [cA, hA.scope]
    cases hx : (runT K ρ φ false (TyS.plain TyM.err) A).onCopy s with
    | none => rfl
    | some x =>
      obtain ⟨⟨TA, RA⟩, sA⟩ := x
      dsimp only [qmap, Option.map_some]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have ct := runT_qset hK hD false t (.plain TA.asTy) s Q β β' hA hVt hR
      have cu := runT_qset hK hD false u (.plain TA.asTy) s Q β β' hA hVu hR
      unfold Comm qmap at ct cu
      rw [ct, cu]
      cases h1 : runT K ρ φ false (.plain TA.asTy) t s with
      | none => rfl
      | some o₁ =>
        cases h2 : runT K ρ φ false (.plain TA.asTy) u s with
        | none => simp
        | some o₂ =>
          obtain ⟨r₁, X₁⟩ := o₁
          obtain ⟨r₂, X₂⟩ := o₂
          obtain ⟨hA₁, -, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false t _ s Q β β hA.self hVt hR)
          obtain ⟨hA₂, -, he₂⟩ := Adm.after K ρ φ hK hA hR h2 (runT_qset hK hD false u _ s Q β β hA.self hVu hR)
          have hq : ∀ q ∈ K.D.rePointed (scopeOf s) t, RAvoid Q s q := fun q hq =>
            rAvoid_of_vars hVt (hD.rep _ _ _ hq)
          have key : (∀ ws : List Sem, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws (qset Q β' s) →
              observation φ (K.D.rePointed (scopeOf s) t) ws (qset Q β' s).positions r₁ (qset Q β' X₁) =
                observation φ (K.D.rePointed (scopeOf s) t) ws (qset Q β' s).positions r₂ (qset Q β' X₂)) =
              (∀ ws : List Sem, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws s →
                observation φ (K.D.rePointed (scopeOf s) t) ws s.positions r₁ X₁ =
                  observation φ (K.D.rePointed (scopeOf s) t) ws s.positions r₂ X₂) := by
            rw [qset_positions]
            exact propext (forall_congr' fun ws => imp_congr (obsTyped_qset _ ws hq)
              (observation_qset_iff φ _ ws hA₁.twin.pre' hA₁.twin.pre hA₁.twin.fix he₁
                hA₂.twin.pre' hA₂.twin.pre hA₂.twin.fix he₂ hq r₁ r₂))
          simp only [Option.map_some, Option.bind_some]
          rw [key]
          split <;> rfl
  | tl, .matchNat p z u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVz : VarsAvoid Q s z := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_matchNat p z u)
    have ct := comm_guarded (tagOk_qset K φ hA.twin.pre' p) fun _ => tagOf_qset K φ hA.twin.pre' hp natTag
    unfold Comm at ct ⊢
    dsimp only
    rw [ct]
    cases h1 : SM.guarded (TagOk K φ p) (tagOf K φ p natTag) s with
    | none => rfl
    | some y =>
      obtain ⟨tg, s₀⟩ := y
      have ht := (SM.guarded_some h1).2
      have ct0 := comm_guarded (Q := Q) (β := β) (tagOk_qset K φ hA.twin.pre p) fun _ => tagOf_qset K φ hA.twin.pre hp natTag
      obtain ⟨hR₀, e₀, -⟩ := tagOf_rinv K φ _ ht hR
      have hA₀ : Adm K Q β β' s₀ := hA.next e₀ (fix_of_comm ct0 hA.twin.fix h1)
      simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      obtain ⟨hR₁, e₁', -⟩ := matchEntry_props K φ (fun _ => True) (!tl) (.matchNat p z u) hR₀
      generalize hme : matchEntry K φ (!tl) (.matchNat p z u) s₀ = me at hR₁ e₁'
      obtain ⟨S₁, L⟩ := me
      obtain ⟨L', hme', hT₁, hL, -, hok⟩ := matchEntry_qset K φ hA₀.decl hD.inv hA₀.twin hA₀.good hA₀.good' (!tl) _
        (blockCaps_avoid K φ hD hA₀ (hV.of_envLe e₀) _) hme
      rw [hme', propext hok]
      dsimp only at hR₁ e₁' ⊢
      have hA₁ : Adm K Q β β' S₁ := hA₀.next e₁' hT₁.fix
      have e₁ := e₀.trans e₁'
      rw [movedPlaces_qset K φ hT₁.pre' hT₁.fix hA.good hA.good']
      by_cases hm : MatchEntryOk K φ (!tl) (Term.matchNat p z u) s₀
      rotate_left
      · simp [optCheck, hm]
      simp only [optCheck, if_pos hm, Option.bind_some]
      have arm : ∀ w : Term, VarsAvoid Q s w →
          Comm Q β' (runT K ρ φ tl (TyS.plain TyM.err) w) S₁ → Comm Q β (runT K ρ φ tl (TyS.plain TyM.err) w) S₁ →
          (do
            let a ← runT K ρ φ tl (TyS.plain TyM.err) w (qset Q β' S₁)
            optCheck (JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd)
            some ((a.1.fst, a.1.snd), L' a.1.snd.label (joinDrop K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd))) =
          Option.map (fun x => (x.fst, qset Q β' x.snd)) (do
            let a ← runT K ρ φ tl (TyS.plain TyM.err) w S₁
            optCheck (JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd)
            some ((a.1.fst, a.1.snd), L a.1.snd.label (joinDrop K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd))) := by
        intro w hVw cw cw0
        unfold Comm qmap at cw
        rw [cw]
        cases h2 : runT K ρ φ tl (.plain TyM.err) w S₁ with
        | none => rfl
        | some a =>
          obtain ⟨⟨r, R⟩, X⟩ := a
          obtain ⟨hA₂, -, e₂⟩ := Adm.after K ρ φ hK hA₁ hR₁ h2 cw0
          obtain ⟨ej, -, ok⟩ := joinDrop_qset K φ hA₁.decl ⟨hA₂.twin.pre, hA₂.twin.pre', hA₂.twin.fix, e₂⟩
            (movedPlaces φ S₁) (Term.matchNat p z u) (joinMoves_avoid K φ hD hA₁ (hV.of_envLe e₁) _)
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [propext ok, ej, hL]
          by_cases hj : JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) X
          · simp [optCheck, hj]
          · simp [optCheck, hj]
      have az := arm z hVz (runT_qset hK hD tl z _ S₁ Q β β' hA₁ (hVz.of_envLe e₁) hR₁)
        (runT_qset hK hD tl z _ S₁ Q β β hA₁.self (hVz.of_envLe e₁) hR₁)
      have au := arm u hVu (runT_qset hK hD tl u _ S₁ Q β β' hA₁ (hVu.of_envLe e₁) hR₁)
        (runT_qset hK hD tl u _ S₁ Q β β hA₁.self (hVu.of_envLe e₁) hR₁)
      cases tg.asNat with
      | none => rfl
      | some k =>
        cases k with
        | zero => exact az
        | succ k => exact au
  | tl, .matchInd p n arms, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVa : ∀ a ∈ arms, VarsAvoid Q s a.2 := fun a ha => hV.sub fun x hx => by
      simp only [Term.placeOccs, List.mem_cons]; exact .inr (mem_placeOccsArms ha hx)
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_matchInd p n arms)
    have ct := comm_guarded (tagOk_qset K φ hA.twin.pre' p) fun _ => tagOf_qset K φ hA.twin.pre' hp indTag
    unfold Comm at ct ⊢
    dsimp only
    rw [ct]
    cases h1 : SM.guarded (TagOk K φ p) (tagOf K φ p indTag) s with
    | none => rfl
    | some y =>
      obtain ⟨tg, s₀⟩ := y
      have ht := (SM.guarded_some h1).2
      have ct0 := comm_guarded (Q := Q) (β := β) (tagOk_qset K φ hA.twin.pre p) fun _ => tagOf_qset K φ hA.twin.pre hp indTag
      obtain ⟨hR₀, e₀, -⟩ := tagOf_rinv K φ _ ht hR
      have hA₀ : Adm K Q β β' s₀ := hA.next e₀ (fix_of_comm ct0 hA.twin.fix h1)
      simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      generalize (!tl && !tg.isProof && !oneCtor K.Γ n) = ent
      obtain ⟨hR₁, e₁', -⟩ := matchEntry_props K φ (fun _ => True) ent (.matchInd p n arms) hR₀
      generalize hme : matchEntry K φ ent (.matchInd p n arms) s₀ = me at hR₁ e₁'
      obtain ⟨S₁, L⟩ := me
      obtain ⟨L', hme', hT₁, hL, -, hok⟩ := matchEntry_qset K φ hA₀.decl hD.inv hA₀.twin hA₀.good hA₀.good' ent _
        (blockCaps_avoid K φ hD hA₀ (hV.of_envLe e₀) _) hme
      rw [hme', propext hok]
      dsimp only at hR₁ e₁' ⊢
      have hA₁ : Adm K Q β β' S₁ := hA₀.next e₁' hT₁.fix
      have e₁ := e₀.trans e₁'
      rw [movedPlaces_qset K φ hT₁.pre' hT₁.fix hA.good hA.good']
      by_cases hm : MatchEntryOk K φ ent (Term.matchInd p n arms) s₀
      rotate_left
      · simp [optCheck, hm]
      simp only [optCheck, if_pos hm, Option.bind_some]
      split
      · rename_i c hc
        have ca := runArm_qset hK hD tl (.plain TyM.err) c arms S₁ Q β β' hA₁ (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        have ca0 := runArm_qset hK hD tl (.plain TyM.err) c arms S₁ Q β β hA₁.self (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        unfold Comm qmap at ca
        rw [ca]
        cases h2 : runArm K ρ φ tl (.plain TyM.err) c arms S₁ with
        | none => rfl
        | some a =>
          obtain ⟨⟨r, R⟩, X⟩ := a
          obtain ⟨hA₂, -, e₂⟩ := Adm.afterArm K ρ φ hK hA₁ hR₁ h2 ca0
          obtain ⟨ej, -, ok⟩ := joinDrop_qset K φ hA₁.decl ⟨hA₂.twin.pre, hA₂.twin.pre', hA₂.twin.fix, e₂⟩
            (movedPlaces φ S₁) (Term.matchInd p n arms) (joinMoves_avoid K φ hD hA₁ (hV.of_envLe e₁) _)
          simp only [Option.map_some, Option.bind_some]
          rw [propext ok, ej, hL]
          by_cases hj : tg.isProof = true ∨ oneCtor K.Γ n = true ∨ JoinDropOk K φ (movedPlaces φ S₁) (Term.matchInd p n arms) X
          · simp only [if_pos hj, Option.bind_some, Option.map_some]
            cases tg <;> dsimp only <;> (try split) <;> rfl
          · simp only [if_neg hj, Option.bind_none, Option.map_none]
      · cases tg
        case proof =>
          dsimp only
          exact comm_anyArm fun c => runArm_qset hK hD tl (.plain TyM.err) c arms S₁ Q β β' hA₁
            (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        all_goals rfl
  | _, _, _, _, _, _, _, _, _, _ => sorry

theorem runArm_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) :
    ∀ (tl : Bool) (hint : TyS) (c : Nat) (arms : List (Hint × Term)) (s : SState) (Q : Pos → Prop)
      (β β' : Pos → SBinding), Adm K Q β β' s → (∀ a ∈ arms, VarsAvoid Q s a.2) → RInv (fun _ => True) s →
      Comm Q β' (runArm K ρ φ tl hint c arms) s
  | _, _, _, [], _, _, _, _, _, _, _ => by unfold Comm; rw [runArm]; rfl
  | tl, hint, c, (h, t) :: rest, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runArm]
    by_cases hc : c = 0
    · simp only [hc, if_true]
      exact runT_qset hK hD tl t hint s Q β β' hA (hV (h, t) (by simp)) hR
    · simp only [hc, if_false]
      exact runArm_qset hK hD tl hint (c - 1) rest s Q β β' hA (fun a ha => hV a (by simp [ha])) hR

theorem runParams_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
    (d : IndDecl) :
    ∀ (as : List Term) (i : Nat) (earlier : List Sem) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → (∀ a ∈ as, VarsAvoid Q s a) → RInv (fun _ => True) s →
      Comm Q β' (runParams K ρ φ d i earlier as) s
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runParams]
    refine comm_bind (comm_onCopy (runT_qset hK hD false a _ s Q β β' hA (hV a (by simp)) hR)) fun x s₁ h1 => ?_
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨v, _⟩ := x
    dsimp only
    exact comm_bind (runParams_qset hK hD d as (i + 1) (earlier ++ [v]) s₁ Q β β' hA
      (fun b hb => hV b (by simp [hb])) hR) fun _ _ _ => comm_pure _ _
end

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
