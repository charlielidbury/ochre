import Ochr.Meaning.RunPresInd

/-!
# Part (E) of the locality induction: the run at two futures

Two futures `φ`, `φ'` that agree on `L`; a state with `RInv L` (part (P), `RunPresInd.lean`). The
run reads the future only through [Access] (after which the accessed position factors through
`L`, `access_FT`), through the closed future (fixed at every live label, `closedFuture_read`),
after ending every borrow (`endAll_FT`), at a loan of the term (in `L`), and through a closure's
finals (`closureAt_congr`, with `FinalsIn` from the cells' order, `RunOrd.lean`). So the run at
`φ` is the run at `φ'`.

This file: the primitives. Each congruence holds at a state with `RInv L`.
-/

namespace Ochr.Meaning

open SState

section
variable (K : RunCtx) {φ φ' : Future} {L : Nat → Prop}

theorem contentOf_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    contentOf K φ p s = contentOf K φ' p s := by
  unfold contentOf
  cases resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    rw [access_FT hi.1 hi.2.1 pos φ φ' hφ]

theorem setContent_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos)
    (steps : List Step) (v : Sem) : setContent K φ pos steps v s = setContent K φ' pos steps v s := by
  unfold setContent
  dsimp only
  rw [closedFuture_read hi.1 hi.2.1 hφ pos]

theorem readPlace_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) (copy : Bool) :
    readPlace K φ p copy s = readPlace K φ' p copy s := by
  unfold readPlace
  rw [← contentOf_congr K hφ hi p]
  cases hc : contentOf K φ p s with
  | none => rfl
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    have hi₁ := (contentOf_rinv K φ L hc hi).1
    simp only [Bind.bind, Option.bind]
    rw [setContent_congr K hφ hi₁]

theorem borrowPlace_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    borrowPlace K φ p s = borrowPlace K φ' p s := by
  unfold borrowPlace
  rw [contentOf_congr K hφ hi p]

theorem movedPlaces_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) :
    movedPlaces φ s = movedPlaces φ' s := by
  unfold movedPlaces
  split
  · congr 1
    funext i
    split
    · rename_i pos _
      rw [closedFuture_read hi.1 hi.2.1 hφ pos]
    · rfl
  · rfl

theorem foldl_inv {α : Type} (P : SState → Prop) (F : SState → α → SState) (h : ∀ s a, P s → P (F s a)) :
    ∀ (qs : List α) (s : SState), P s → P (qs.foldl F s)
  | [], _, hs => hs
  | q :: qs, s, hs => foldl_inv P F h qs _ (h s q hs)

theorem foldl_congr_inv {α : Type} (P : SState → Prop) (F F' : SState → α → SState)
    (h : ∀ s a, P s → F s a = F' s a ∧ P (F s a)) : ∀ (qs : List α) (s : SState), P s → qs.foldl F s = qs.foldl F' s
  | [], _, _ => rfl
  | q :: qs, s, hs => by
    simp only [List.foldl_cons]
    rw [← (h s q hs).1]
    exact foldl_congr_inv P F F' h qs _ (h s q hs).2

/-- The join's drop is the same at both futures. -/
theorem joinDrop_congr (hφ : ∀ l, L l → φ l = φ' l) (t : Term) {s : SState} (hi : RInv L s) :
    joinDrop K φ t s = joinDrop K φ' t s := by
  unfold joinDrop
  rw [movedPlaces_congr hφ hi]
  apply foldl_congr_inv (RInv L) _ _ _ _ s hi
  intro s q hi
  refine ⟨?_, ?_⟩
  · dsimp only
    split
    · rfl
    · split
      · rename_i pos steps _
        rw [closedFuture_read (access_rinv hi pos).1 (access_rinv hi pos).2.1 hφ pos]
      · rfl
  · dsimp only
    split
    · exact hi
    · split
      · rename_i pos steps hr
        have hia := access_rinv hi pos
        split
        · exact hia
        · exact hia
        · exact hia
        · have hie : RInv L (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) := by
            split
            · split
              · exact endLabel_rinv hia _
              · exact hia
            · exact hia
          generalize (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) = s₂ at hie ⊢
          exact setAt_rinv hie pos _
            ((hie.1 pos).comp (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err))
            (fun x hx => by
              by_cases hp : pos ∈ s₂.positions
              · exact (hie.2.1 pos x hp hx).comp
                  (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err)
              · exact absurd (hie.2.2 pos x hx).1 hp)
      · exact hi

/-- An `Id`'s observation is the same at both futures: after every borrow ends, every position
factors through `L` (R3). -/
theorem observation_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (reps : List Place)
    (ws : List Sem) (r : Res) : observation φ reps ws r s = observation φ' reps ws r s := by
  unfold observation
  dsimp only
  have hiS := foldl_inv (RInv L) (fun s (x : Place × Nat) => match resolve s x.1, ws[x.2]? with
      | some (pos, []), some w => s.setAt pos fun _ => w
      | _, _ => s) (fun s x hs => by
        split
        · exact setAt_rinv hs _ _ (FT.const _ _) (fun _ _ => FT.const _ _)
        · exact hs) reps.zipIdx s hi
  congr 1
  apply List.map_congr_left
  intro p _
  exact endAll_FT hiS.1 hiS.2.1 p φ φ' hφ

theorem SM.bind_congr {α β : Type 3} {m m' : SM α} {k k' : α → SM β} {s : SState} (hm : m s = m' s)
    (hk : ∀ a s₁, m s = some (a, s₁) → k a s₁ = k' a s₁) : (m >>= k) s = (m' >>= k') s := by
  simp only [Bind.bind, Monad.toBind, instMonadSM]
  rw [← hm]
  cases h : m s with
  | none => rfl
  | some p => exact hk p.1 p.2 h

theorem Option.bind_congr' {α β : Type _} {x x' : Option α} {f f' : α → Option β} (hx : x = x')
    (hf : ∀ a, x = some a → f a = f' a) : x.bind f = x'.bind f' := by
  rw [← hx]
  cases h : x with
  | none => rfl
  | some a => exact hf a h

/-- A state whose positions hold constants and whose shape is empty has the invariant. -/
theorem rinv_of_const {s : SState} (hc : ∀ p, ∃ c, s.valAt p = fun _ => c) (hsh : ∀ p, s.shape p = none) :
    RInv L s := by
  refine ⟨fun p => ?_, (fun r x _ hs => by rw [hsh] at hs; cases hs), (fun p x hs => by rw [hsh] at hs; cases hs)⟩
  obtain ⟨c, e⟩ := hc p; rw [e]; exact FT.const _ _

theorem rinv_emptyState (n : Nat) : RInv L (emptyState n) :=
  rinv_of_const (fun p => ⟨.err, by
    have : p ∉ (emptyState n).positions := by simp [SState.positions, emptyState]
    rw [valAt_of_not_mem _ _ this]⟩) (fun _ => rfl)

theorem rinv_stateOf (n : Nat) (vs : List Sem) (tys : List (DeclInfo × TyS)) :
    RInv L (stateOf n (capsState vs tys)) := by
  apply rinv_of_const _ (fun _ => rfl)
  intro p
  cases p with
  | temp f i => exact ⟨.err, by simp [SState.valAt, stateOf]; cases f <;> simp⟩
  | bind f i =>
    simp only [SState.valAt, stateOf]
    split
    · rename_i b hb
      cases f with
      | succ f => simp at hb
      | zero =>
        simp only [List.getElem?_cons_zero, Option.bind_some, capsState, List.getElem?_map] at hb
        cases hz : (vs.zip tys)[i]? with
        | none => rw [hz] at hb; cases hb
        | some x => rw [hz] at hb; cases hb; exact ⟨x.1, rfl⟩
    · exact ⟨.err, rfl⟩

theorem rinv_extendBy {s : SState} (hi : RInv L s) : ∀ acc : List Sem, RInv L (extendBy s acc)
  | [] => hi
  | a :: acc => by
    unfold extendBy
    simp only [List.foldl_cons]
    exact rinv_extendBy (pushBind_rinv hi _ a rfl) acc

end

theorem anyAtomList_of_mem {P : Value → Bool} {t : Term} : ∀ {ts : List Term}, t ∈ ts → t.anyAtom P = true →
    Term.anyAtomList P ts = true
  | a :: as, hm, h => by
    rw [List.mem_cons] at hm
    rcases hm with e | hm
    · subst e; simp [Term.anyAtomList, h]
    · simp [Term.anyAtomList, anyAtomList_of_mem hm h]

/-- The type an embedded value's run carries (`run`'s `.val` clause). -/
noncomputable def valT (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) : Value → TyS
  | .clo caps t rd => { hint with shape := ((piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps)
      (capsTys K ρ φ rd))) t).map fun sh => (sh.ps, sh.out)) }
  | .tPi caps t rd => { hint with shape := ((piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps)
      (capsTys K ρ φ rd))) t).map fun sh => (sh.ps, sh.out)) }
  | .gfn n => (K.C.global n).2
  | .abs σ => { hint with shape := (K.Δ σ).shape, data := (K.Δ σ).data }
  | .loan l => match (K.Λ l).shape with
    | some sh => { hint with shape := some sh }
    | none => hint
  | .sealed t => match run K ρ φ hint t (emptyState (t.loans.foldl max 0 + 1)) with
    | some ((_, R), _) => { hint with shape := R.shape }
    | none => hint
  | _ => hint

theorem run_val_def (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (v : Value) (s : SState) :
    run K ρ φ hint (.val v) s = some ((meanV K ρ φ hint v, { valT K ρ φ hint v with label := none }), s) := by
  cases v <;> rfl

theorem SM.onCopy_congr {α : Type 3} {x x' : SM α} {s : SState} (h : x s = x' s) :
    SM.onCopy x s = SM.onCopy x' s := by
  unfold SM.onCopy; rw [h]

section
variable (K : RunCtx) (ρ : Assignment) (φ φ' : Future)

mutual
/-- **Part (E)**: the run at two futures that agree on `L`, from a state with `RInv L`, of a term
whose loans are in `L`, is the same. -/
theorem run_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (t : Term) (hint : TyS) (s : SState)
    (L : Nat → Prop), (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s →
    run K ρ φ hint t s = run K ρ φ' hint t s
  | .place p, hint, s, L, hφ, ht, hi => by
    rw [run, run]; exact readPlace_congr K hφ hi p _
  | .borrow p, hint, s, L, hφ, ht, hi => by
    rw [run, run]; exact borrowPlace_congr K hφ hi p
  | .seq u w, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.bind_congr (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ h1
    exact run_congrE hK w hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h]))
      (run_rinv K ρ φ L hK u _ s s₁ a hi h1).1
  | .succ u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.bind_congr (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | .ref A, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.bind_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | .const n, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .sort l, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .nat, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .unit, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .zero, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .tt, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .cong f g, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .val v, hint, s, L, hφ, ht, hi => by
    have hv : ∀ l, v.hasLoan l = true → φ l = φ' l := fun l h => hφ l (ht l h)
    rw [run_val_def, run_val_def, meanV_congrE hK v hint hv]
    cases v with
    | clo caps t rd =>
      simp only [valT]
      rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        piShapeOf_congrE hK t _ (fun l => φ l = φ' l) (fun _ h => h)
          (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
    | tPi caps t rd =>
      simp only [valT]
      rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        piShapeOf_congrE hK t _ (fun l => φ l = φ' l) (fun _ h => h)
          (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
    | sealed t =>
      simp only [valT]
      rw [run_congrE hK t hint _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_emptyState _)]
    | _ => rfl
  | .ascribe u A, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (run_congrE hK u _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro _ _ _; rfl
  | .eq A a b, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.onCopy_congr
    apply SM.bind_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨TA, _⟩ s₁ h1
    have hi₁ := (run_rinv K ρ φ L hK A _ s s₁ _ hi h1).1
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK a _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK b _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    intro _ _ _; rfl
  | .id A t u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply Option.bind_congr' (SM.onCopy_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (run_congrE hK t _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₁, s₁'⟩ h2
    apply Option.bind_congr' (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₂, s₂'⟩ h3
    have hi₁ := (run_rinv K ρ φ L hK t _ s s₁' r₁ hi h2).1
    have hi₂ := (run_rinv K ρ φ L hK u _ s s₂' r₂ hi h3).1
    simp only [observation_congr hφ hi₁, observation_congr hφ hi₂]
  | .tind n args, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    cases hd : K.Γ.find? (·.name == n) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d args 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro _ _ _; rfl
  | .call f args hd, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    dsimp only
    split
    · apply SM.onCopy_congr
      refine SM.bind_congr ?_ (fun _ _ _ => rfl)
      apply SM.bind_congr (run_congrE hK f _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro fv s₁ h1
      apply SM.bind_congr (runArgs_congrE hK _ args 0 [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h]))
        (run_rinv K ρ φ L hK f _ s s₁ fv hi h1).1)
      intro _ _ _; rfl
    · apply SM.bind_congr (run_congrE hK f _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro fv s₁ h1
      apply SM.bind_congr (runArgs_congrE hK _ args 0 [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h]))
        (run_rinv K ρ φ L hK f _ s s₁ fv hi h1).1)
      intro _ _ _; rfl
  | .matchNat p z u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    dsimp only
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' rfl
    rintro ⟨⟨v, T, pos, steps⟩, s₁⟩ h1
    have hi₁ := (contentOf_rinv K φ' L h1 hi).1
    dsimp only
    split
    · apply Option.bind_congr' (run_congrE hK z hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ (run_rinv K ρ φ L hK z hint s₁ s₂ _ hi₁ h2).1]
    · apply Option.bind_congr' (run_congrE hK u hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ (run_rinv K ρ φ L hK u hint s₁ s₂ _ hi₁ h2).1]
    · rfl
  | .matchInd p n arms, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    dsimp only
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' rfl
    rintro ⟨⟨v, T, pos, steps⟩, s₁⟩ h1
    have hi₁ := (contentOf_rinv K φ' L h1 hi).1
    dsimp only
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrE hK arms hint c s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ (runArm_rinv K ρ φ L hK arms hint c s₁ s₂ _ hi₁ h2).1]
    · rfl
  | .letIn x u w, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply Option.bind_congr' (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨⟨v, T⟩, s₁⟩ h1
    obtain ⟨hi₁, hy₁, -, -⟩ := run_rinv K ρ φ L hK u _ s s₁ (v, T) hi h1
    have hi₂ := pushBindShaped_rinv hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s₁) u } v rfl
      fun l hl => by
        rcases hy₁ l hl with ⟨h' | h', hn⟩
        · exact ⟨.inl h', hn⟩
        · exact ⟨.inr (.inr h'), hn⟩
    dsimp only
    apply Option.bind_congr' (run_congrE hK w hint _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₂)
    intro _ _; rfl
  | .assign p u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    dsimp only
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' rfl
    rintro ⟨⟨w, T, pos, steps⟩, s₁⟩ h1
    have hi₁ := (contentOf_rinv K φ' L h1 hi).1
    dsimp only
    apply Option.bind_congr' (run_congrE hK u T s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
    rintro ⟨⟨v, R⟩, s₂⟩ h2
    have hi₂ := (run_rinv K ρ φ L hK u T s₁ s₂ _ hi₁ h2).1
    dsimp only
    refine Option.bind_congr' (setContent_congr K hφ ?_ pos steps v) (fun _ _ => rfl)
    split
    · split
      · exact endLabel_rinv hi₂ _
      · exact hi₂
    · exact hi₂
  | .pi hs ds c, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    have hds := runDoms_congrE hK s L hφ hi ds (fun l h => ht l (by simp [Term.anyAtom, h]))
    have hc : ∀ acc, run K ρ φ (.plain .err) c (extendBy s acc) = run K ρ φ' (.plain .err) c (extendBy s acc) :=
      fun acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
    dsimp only
    rw [hds]
    cases c with
    | ref U =>
      have hU : ∀ acc, run K ρ φ (.plain .err) U (extendBy s acc) = run K ρ φ' (.plain .err) U (extendBy s acc) :=
        fun acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
      simp only [hU]
    | _ => simp only [hc]
  | .ctor ty c hh ps args, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d ps 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro psM s₁ h1
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      have cont : ∀ ps' : List Sem, (if d.sort == 0 then
            (do let _ ← SM.onCopy (runFields K ρ φ d ps' c 0 [] args)
                pure ((.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))
          else
            (do let fs ← runFields K ρ φ d ps' c 0 [] args
                pure ((K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))) s₁
          = (if d.sort == 0 then
            (do let _ ← SM.onCopy (runFields K ρ φ' d ps' c 0 [] args)
                pure ((.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))
          else
            (do let fs ← runFields K ρ φ' d ps' c 0 [] args
                pure ((K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))) s₁ := by
        intro ps'
        have hF := runFields_congrE hK d ps' c args 0 [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi
        by_cases hs0 : (d.sort == 0) = true
        · rw [if_pos hs0, if_pos hs0]
          exact SM.bind_congr (SM.onCopy_congr hF) (fun _ _ _ => rfl)
        · rw [if_neg hs0, if_neg hs0]
          exact SM.bind_congr hF (fun _ _ _ => rfl)
      by_cases hc : (ps.isEmpty && !d.params.isEmpty) = true
      · rw [if_pos hc]
        cases hdata : hint.data with
        | none => rfl
        | some np =>
          obtain ⟨n', ps''⟩ := np
          dsimp only
          by_cases hn : n' = ty
          · rw [if_pos hn]; exact cont ps''
          · rw [if_neg hn]
      · rw [if_neg hc]
        exact cont psM
  | .prim n args, hint, s, L, hφ, ht, hi => by
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState), RInv L s →
        run K ρ φ hint t s = run K ρ φ' hint t s := fun t hm hint s hi =>
      runAll_congrE hK args t hm hint s L hφ
        (fun l h => ht l (by simp only [Term.anyAtom]; exact anyAtomList_of_mem hm h)) hi
    by_cases h1 : n = "symm"
    · subst h1; rw [run, run]
    by_cases h2 : n = "trans"
    · subst h2; rw [run, run]
    by_cases h3 : n = "rewrite"
    · subst h3; rw [run, run]
    by_cases h4 : n = "rewriteR"
    · subst h4; rw [run, run]
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, hargs⟩ := hJ
      have hm : ∀ x, x ∈ [A, a, b, P, h', t] → x ∈ args := fun x hx => by rw [hargs]; exact hx
      rw [hargs, run, run]
      apply SM.bind_congr (SM.onCopy_congr (hall A (hm A (by simp)) _ s hi))
      intro _ s₁ e1; have e := SM.onCopy_state e1; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall a (hm a (by simp)) _ _ hi))
      intro _ s₂ e2; have e := SM.onCopy_state e2; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall b (hm b (by simp)) _ _ hi))
      intro _ s₃ e3; have e := SM.onCopy_state e3; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall P (hm P (by simp)) _ _ hi))
      intro _ s₄ e4; have e := SM.onCopy_state e4; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall h' (hm h' (by simp)) _ _ hi))
      intro _ s₅ e5; have e := SM.onCopy_state e5; subst e
      exact hall t (hm t (by simp)) _ _ hi
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl
      · by_cases hp : ∃ p, u = .place p
        · obtain ⟨p, rfl⟩ := hp
          rw [hargs, run, run]; exact readPlace_congr K hφ hi p true
        · rw [hargs, run.eq_37 _ _ _ _ _ (fun p e => hp ⟨p, e⟩), run.eq_37 _ _ _ _ _ (fun p e => hp ⟨p, e⟩)]
          exact hall u hu _ _ hi
      · by_cases hp : ∃ p, u = .place p
        · obtain ⟨p, rfl⟩ := hp
          rw [hargs, run, run]; exact readPlace_congr K hφ hi p true
        · rw [hargs, run.eq_39 _ _ _ _ _ (fun p e => hp ⟨p, e⟩), run.eq_39 _ _ _ _ _ (fun p e => hp ⟨p, e⟩)]
          exact hall u hu _ _ hi
      · rw [hargs, run, run]; exact hall u hu _ _ hi
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    rw [run.eq_41 K ρ φ hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3,
      run.eq_41 K ρ φ' hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3]
  | _, _, _, _, _, _, _ => sorry

theorem meanV_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (v : Value) (hint : TyS),
    (∀ l, v.hasLoan l = true → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v
  | .loan l, hint, hv => hv l (by
      show (Value.loan l).anyAtom (· == .loan l) = true
      unfold Value.anyAtom
      show (Value.beq (.loan l) (.loan l) || _) = true
      simp [Value.beq])
  | .succ w, hint, hv => by
    show (meanV K ρ φ _ w).succ = (meanV K ρ φ' _ w).succ
    rw [meanV_congrE hK w _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom] at h ⊢; simp [h])]
  | .borrow _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV K ρ φ' hint w
    exact meanV_congrE hK w hint fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])
  | .tRef A, hint, hv => by
    show meanV K ρ φ _ A = meanV K ρ φ' _ A
    exact meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])
  | .tEq A a b, hint, hv => by
    rw [meanV, meanV]
    rw [meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK a _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK b _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])]
  | .clo caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .tPi caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .sealed t, hint, hv => by
    rw [meanV, meanV]
    rw [run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_emptyState _)]
  | .ind ty c h ps fs, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      dsimp only
      rw [meanParams_congrE hK d ps _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
      split
      · rename_i ps' _
        rw [meanFields_congrE hK d ps' c fs _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
      · rfl
    · rfl
  | .tInd n args, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      rw [meanParams_congrE hK d args _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
    · rfl
  | .zero, _, _ => rfl
  | .unit, _, _ => rfl
  | .gfn _, _, _ => rfl
  | .bot, _, _ => rfl
  | .abs _, _, _ => rfl
  | .proof, _, _ => rfl
  | .tNat, _, _ => rfl
  | .tUnit, _, _ => rfl
  | .sort _, _, _ => rfl

theorem runAll_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (ts : List Term) (t : Term), t ∈ ts →
    ∀ (hint : TyS) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s → run K ρ φ hint t s = run K ρ φ' hint t s
  | [], t, h, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, hint, s, L, hφ, ht, hi => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ht ⊢; exact run_congrE hK a hint s L hφ ht hi
    · exact runAll_congrE hK as t h hint s L hφ ht hi

theorem runDoms_congrE (hK : ∀ n, (K.C.global n).2.label = none) (s : SState) (L : Nat → Prop)
    (hφ : ∀ l, L l → φ l = φ' l) (hi : RInv L s) : ∀ (ds : List Term),
    (∀ l, Term.anyAtomList (· == .loan l) ds = true → L l) → runDoms K ρ φ s ds = runDoms K ρ φ' s ds
  | [], _ => rfl
  | d :: ds, ht => by
    have hds := runDoms_congrE hK s L hφ hi ds (fun l h => ht l (by simp [Term.anyAtomList, h]))
    have hd : ∀ acc, run K ρ φ (.plain .err) d (extendBy s acc) = run K ρ φ' (.plain .err) d (extendBy s acc) :=
      fun acc => run_congrE hK d _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) (rinv_extendBy hi acc)
    cases d with
    | ref A =>
      have hA : ∀ acc, run K ρ φ (.plain .err) A (extendBy s acc) = run K ρ φ' (.plain .err) A (extendBy s acc) :=
        fun acc => run_congrE hK A _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, Term.anyAtom, h]))
          (rinv_extendBy hi acc)
      simp only [runDoms, hA, hds]
    | _ => simp only [runDoms, hd, hds]

theorem runArgs_congrE (hK : ∀ n, (K.C.global n).2.label = none) (shape : Option (List PiParam × PiOut)) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runArgs K ρ φ shape i earlier args s = runArgs K ρ φ' shape i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runArgs]
    apply SM.bind_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi)
    intro r s₁ h1
    apply SM.bind_congr (runArgs_congrE hK shape as _ _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h]))
      (run_rinv K ρ φ L hK a _ s s₁ r hi h1).1)
    intro _ _ _; rfl

theorem runFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runFields K ρ φ d ps c i earlier args s = runFields K ρ φ' d ps c i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runFields]
    apply SM.bind_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi)
    intro r s₁ h1
    apply SM.bind_congr (runFields_congrE hK d ps c as _ _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h]))
      (run_rinv K ρ φ L hK a _ s s₁ r hi h1).1)
    intro _ _ _; rfl

theorem runParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runParams K ρ φ d i earlier args s = runParams K ρ φ' d i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrE hK d as _ _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi)
    intro _ _ _; rfl

theorem runArm_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (arms : List (Hint × Term)) (hint : TyS)
    (c : Nat) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomArms (· == .loan l) arms = true → L l) → RInv L s →
    runArm K ρ φ hint c arms s = runArm K ρ φ' hint c arms s
  | [], _, _, _, _, _, _, _ => rfl
  | (_, t) :: rest, hint, c, s, L, hφ, ht, hi => by
    simp only [runArm]
    split
    · exact run_congrE hK t hint s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi
    · exact runArm_congrE hK rest hint (c - 1) s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi

theorem capsVals_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (vs : List Value),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) → capsVals K ρ φ vs = capsVals K ρ φ' vs
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [capsVals]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      capsVals_congrE hK vs (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem capsTys_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (rd : List (DeclInfo × Value)),
    (∀ l, Value.anyAtomRd (· == .loan l) rd = true → φ l = φ' l) → capsTys K ρ φ rd = capsTys K ρ φ' rd
  | [], _ => rfl
  | (d, T) :: rest, hv => by
    simp only [capsTys]
    rw [meanV_congrE hK T _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomRd, h])),
      capsTys_congrE hK rest (fun l h => hv l (by simp [Value.anyAtomRd, h]))]

theorem meanFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanFields K ρ φ d ps c i earlier vs = meanFields K ρ φ' d ps c i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanFields]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      meanFields_congrE hK d ps c vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem meanParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanParams K ρ φ d i earlier vs = meanParams K ρ φ' d i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanParams]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      meanParams_congrE hK d vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]


theorem piShapeOf_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (t : Term) (s : SState) (L : Nat → Prop),
    (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s →
    piShapeOf K ρ φ s t = piShapeOf K ρ φ' s t
  | t, s, L, hφ, ht, hi => by
    cases t with
    | pi hs ds c =>
      have hds := runDoms_congrE hK s L hφ hi ds (fun l h => ht l (by simp [Term.anyAtom, h]))
      have hc : ∀ acc, run K ρ φ (.plain .err) c (extendBy s acc) = run K ρ φ' (.plain .err) c (extendBy s acc) :=
        fun acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
      cases c with
      | ref U =>
        have hU : ∀ acc, run K ρ φ (.plain .err) U (extendBy s acc) = run K ρ φ' (.plain .err) U (extendBy s acc) :=
          fun acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
        simp only [piShapeOf, hU, hds]
      | _ => simp only [piShapeOf, hc, hds]
    | fix self hs ds c dec body =>
      have hds := runDoms_congrE hK s L hφ hi ds (fun l h => ht l (by simp [Term.anyAtom, h]))
      have hc : ∀ acc, run K ρ φ (.plain .err) c (extendBy s acc) = run K ρ φ' (.plain .err) c (extendBy s acc) :=
        fun acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
      cases c with
      | ref U =>
        have hU : ∀ acc, run K ρ φ (.plain .err) U (extendBy s acc) = run K ρ φ' (.plain .err) U (extendBy s acc) :=
          fun acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi acc)
        simp only [piShapeOf, hU, hds]
      | _ => simp only [piShapeOf, hc, hds]
    | _ => simp only [piShapeOf]

end

end

end Ochr.Meaning
