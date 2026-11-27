import Ochr.Meaning.RunPresInd
import Ochr.Meaning.Under

/-!
# Part (E) of the locality induction: the run at two futures

Two futures `φ`, `φ'` that agree on `L`; a state with `RInv L` (part (P), `RunPresInd.lean`). The
run reads a place's content at the typed future (each live label its record, which no future
changes, `typedFuture_read`, docs/31 D68; [Access] reads sites only, docs/31 D29),
after ending every borrow (`endAll_FT`), at a loan of the term (in `L`), and through a closure's
finals (`closureAt_congr`, with `FinalsIn` from the cells' order, `RunOrd.lean`). So the run at
`φ` is the run at `φ'`.

This file: the primitives. Each congruence holds at a state with `RInv L`.
-/

namespace Ochr.Meaning

open SState
open Classical

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
    have hi' := access_rinv hi pos (dataHit steps)
    rw [typedFuture_read hi'.1 hφ pos]

/-- A match's tag is the same at both futures: it is read at the typed future. -/
theorem tagOf_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) (tag : Sem → TyS → Sem) :
    tagOf K φ p tag s = tagOf K φ' p tag s := by
  unfold tagOf
  cases resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    have hi' := access_rinv hi pos (tagHit steps)
    rw [typedFuture_read hi'.1 hφ pos]

/-- A test over every typed future of a position's meaning reads the run's future only on `L`. -/
theorem typedFut_forall_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos)
    (P : Sem → Prop) :
    (∀ ψ, TypedFut K φ s ψ → P (s.valAt pos ψ)) ↔ (∀ ψ, TypedFut K φ' s ψ → P (s.valAt pos ψ)) := by
  have key : ∀ {φ₁ φ₂ : Future}, (∀ l, L l → φ₁ l = φ₂ l) →
      (∀ ψ, TypedFut K φ₁ s ψ → P (s.valAt pos ψ)) → (∀ ψ, TypedFut K φ₂ s ψ → P (s.valAt pos ψ)) := by
    intro φ₁ φ₂ h12 hp ψ hψ
    let ψ' : Future := fun l => if l ∈ s.liveLabels then ψ l else φ₁ l
    have hψ' : TypedFut K φ₁ s ψ' :=
      ⟨fun l hl => by simp [ψ', hl], fun l hl => by simpa [ψ', hl] using hψ.2 l hl⟩
    have e : s.valAt pos ψ' = s.valAt pos ψ := hi.1 pos ψ' ψ (fun l hl => by
      by_cases hm : l ∈ s.liveLabels
      · simp [ψ', hm]
      · rcases hl with hL | hlive
        · simp only [ψ', hm, if_false]; rw [h12 l hL, hψ.1 l hm]
        · exact absurd hlive hm)
    rw [← e]; exact hp ψ' hψ'
  exact ⟨key hφ, key (fun l hl => (hφ l hl).symm)⟩

theorem setContent_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos)
    (steps : List Step) (v : Sem) : setContent K φ pos steps v s = setContent K φ' pos steps v s := by
  unfold setContent
  dsimp only
  have hiff := typedFut_forall_congr K hφ hi pos
    (fun x => (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps x).isSome = true)
  by_cases hc : ∀ ψ, TypedFut K φ s ψ → (Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps (s.valAt pos ψ)).isSome = true
  · rw [if_pos hc, if_pos (hiff.1 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]

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
      have e : s.valAt pos (s.lentFuture φ) = s.valAt pos (s.lentFuture φ') :=
        hi.1 pos _ _ fun l hl => by
          unfold SState.lentFuture
          by_cases hlive : l ∈ s.liveLabels
          · rw [if_pos hlive, if_pos hlive]
          · rw [if_neg hlive, if_neg hlive]
            rcases hl with hl | hl
            · exact hφ l hl
            · exact absurd hl hlive
      rw [e]
    · rfl
  · rfl

theorem invalidateOne_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (q : Place) :
    invalidateOne K φ s q = invalidateOne K φ' s q := by
  unfold invalidateOne
  split
  · rename_i pos steps _
    dsimp only
    rw [setContent_congr K hφ (access_rinv hi pos _) pos steps .moved]
  · rfl

theorem invalidate_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    invalidate K φ p s = invalidate K φ' p s := by
  unfold invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rw [invalidateOne_congr K hφ hi q]
    exact ih (invalidateOne_props K φ' L q hi).1

theorem entryCap_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (qk : Place × Nat) :
    entryCap K φ s qk = entryCap K φ' s qk := by
  have hi₁ : RInv L (match resolve s qk.1 with | some (pos, steps) => s.access pos (dataHit steps) | none => s) := by
    split
    · exact access_rinv hi _ _
    · exact hi
  unfold entryCap
  dsimp only
  split
  · exact invalidate_congr K hφ hi₁ qk.1
  · rfl

theorem entryAccess_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s)
    (bc : List Place × List (Place × Nat)) : entryAccess K φ bc s = entryAccess K φ' bc s := by
  unfold entryAccess
  have hi₁ := (entryAccess_props K φ' L (bc.1, []) hi).1
  simp only [entryAccess, List.foldl_nil] at hi₁
  generalize bc.1.foldl entryReroot s = s₁ at hi₁ ⊢
  generalize bc.2 = qs
  induction qs generalizing s₁ with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rw [entryCap_congr K hφ hi₁ q]
    exact ih _ (entryCap_props K φ' L _ q hi₁).1

/-- A position's open membership at every typed future reads the run's future only on `L`. -/
theorem posOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos) :
    PosOk K φ s pos ↔ PosOk K φ' s pos := by
  have key : ∀ {φ₁ φ₂ : Future}, (∀ l, L l → φ₁ l = φ₂ l) → PosOk K φ₁ s pos → PosOk K φ₂ s pos := by
    intro φ₁ φ₂ h12 hp ψ hψ
    let ψ' : Future := fun l => if l ∈ s.liveLabels then ψ l else φ₁ l
    have hψ' : TypedFut K φ₁ s ψ' :=
      ⟨fun l hl => by simp [ψ', hl], fun l hl => by simpa [ψ', hl] using hψ.2 l hl⟩
    have e : s.valAt pos ψ' = s.valAt pos ψ := hi.1 pos ψ' ψ (fun l hl => by
      by_cases hm : l ∈ s.liveLabels
      · simp [ψ', hm]
      · rcases hl with hL | hlive
        · simp only [ψ', hm, if_false]; rw [h12 l hL, hψ.1 l hm]
        · exact absurd hlive hm)
    rw [← e]; exact hp ψ' hψ'
  exact ⟨key hφ, key (fun l hl => (hφ l hl).symm)⟩

/-- The whole state's open membership at every typed future reads the run's future only on `L`. -/
theorem stateOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) :
    StateOk K φ s ↔ StateOk K φ' s := by
  have key : ∀ {φ₁ φ₂ : Future}, (∀ l, L l → φ₁ l = φ₂ l) → StateOk K φ₁ s → StateOk K φ₂ s := by
    intro φ₁ φ₂ h12 hp ψ hψ
    let ψ' : Future := fun l => if l ∈ s.liveLabels then ψ l else φ₁ l
    have hψ' : TypedFut K φ₁ s ψ' :=
      ⟨fun l hl => by simp [ψ', hl], fun l hl => by simpa [ψ', hl] using hψ.2 l hl⟩
    have e : ∀ q, s.valAt q ψ' = s.valAt q ψ := fun q => hi.1 q ψ' ψ (fun l hl => by
      by_cases hm : l ∈ s.liveLabels
      · simp [ψ', hm]
      · rcases hl with hL | hlive
        · simp only [ψ', hm, if_false]; rw [h12 l hL, hψ.1 l hm]
        · exact absurd hlive hm)
    obtain ⟨hb, hh⟩ := hp ψ' hψ'
    exact ⟨fun f i hm => by rw [← e]; exact hb f i hm, fun q l hl => by rw [← e]; exact hh q l hl⟩
  exact ⟨key hφ, key (fun l hl => (hφ l hl).symm)⟩

theorem lentOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    lentOk K φ p s ↔ lentOk K φ' p s := by
  unfold lentOk
  split
  · exact or_congr Iff.rfl (or_congr Iff.rfl (stateOk_congr K hφ hi))
  · exact Iff.rfl

theorem assignAt_congr (hφ : ∀ l, L l → φ l = φ' l) {s₁ : SState} (hi₁ : RInv L s₁) (p : Place) (v : Sem)
    (lab : Option Nat) : assignAt K φ p v lab s₁ = assignAt K φ' p v lab s₁ := by
  unfold assignAt
  cases hr : resolve s₁ p with
  | none => rfl
  | some ps =>
  obtain ⟨pos, steps⟩ := ps
  dsimp only
  have hi₂ : RInv L (if (steps.isEmpty && (s₁.shape pos).isSome) = true then s₁
      else s₁.access pos (dataHit steps)) := by
    split
    · exact hi₁
    · exact access_rinv hi₁ pos _
  generalize (if (steps.isEmpty && (s₁.shape pos).isSome) = true then s₁
      else s₁.access pos (dataHit steps)) = s₂ at hi₂ ⊢
  rw [setContent_congr K hφ ?_ pos steps v]
  split
  · split
    · exact endLabel_rinv hi₂ _
    · exact hi₂
  · exact hi₂

/-- [Entry] reads the future only through the places then moved. -/
theorem matchEntry_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (ent : Bool) (mt : Term) :
    matchEntry K φ ent mt s = matchEntry K φ' ent mt s := by
  unfold matchEntry
  rw [movedPlaces_congr hφ hi]
  split
  · simp only [entryAccess_congr K hφ hi]
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

theorem accessLentPrefix_congr (pos : Pos) (steps : List Step) (s : SState) :
    accessLentPrefix pos steps s = accessLentPrefix pos steps s := rfl

theorem dropAt_congr (hφ : ∀ l, L l → φ l = φ' l) (q : Place) (pos : Pos) (steps : List Step) {s : SState}
    (hi : RInv L s) : dropAt K φ q pos steps s = dropAt K φ' q pos steps s := by
  unfold dropAt
  have hi' := access_rinv hi pos (dataHit steps)
  dsimp only
  have hiff := typedFut_forall_congr K hφ hi' pos
    (fun x => (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps x).isSome = true)
  rw [propext hiff]

/-- The join's drop is the same at both futures. -/
theorem joinDrop_congr (hφ : ∀ l, L l → φ l = φ' l) (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) :
    joinDrop K φ entry t s = joinDrop K φ' entry t s := by
  unfold joinDrop
  apply foldl_congr_inv (RInv L) _ _ _ _ s hi
  intro s q hi
  refine ⟨?_, ?_⟩
  · split
    · exact dropAt_congr K hφ q _ _ (accessLentPrefix_rinv L hi)
    · rfl
  · split
    · exact dropAt_rinv K φ L q _ _ (accessLentPrefix_rinv L hi)
    · exact hi

/-! ### The strict ends' tests (ruling (A)) read the run's future only on `L` -/

theorem endOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (l : Nat) :
    EndOk K φ s l ↔ EndOk K φ' s l := by
  unfold EndOk
  exact forall_congr' fun r => imp_congr_right fun _ =>
    typedFut_forall_congr K hφ hi r (· ∈ₛ[K.dm.read] s.heldTy l)

/-- A fold's per-step test, compared at two futures along an invariant both folds keep. -/
theorem foldOk_congr {α : Type} (P : SState → Prop) {f f' : SState → α → SState} {ok ok' : SState → α → Prop}
    (hf : ∀ s a, P s → f s a = f' s a) (hP : ∀ s a, P s → P (f s a)) (hok : ∀ s a, P s → (ok s a ↔ ok' s a)) :
    ∀ (xs : List α) {s : SState}, P s → (FoldOk f ok xs s ↔ FoldOk f' ok' xs s)
  | [], _, _ => Iff.rfl
  | a :: as, s, hs => by
    unfold FoldOk
    rw [← hf s a hs]
    exact and_congr (hok s a hs) (foldOk_congr P hf hP hok as (hP s a hs))

theorem endsOk_congr (hφ : ∀ l, L l → φ l = φ' l) (ls : List Nat) {s : SState} (hi : RInv L s) :
    EndsOk K φ ls s ↔ EndsOk K φ' ls s :=
  foldOk_congr (RInv L) (fun _ _ _ => rfl) (fun _ a h => endLabel_rinv h a) (fun _ a h => endOk_congr K hφ h a) ls hi

theorem rinv_accRounds {s : SState} (hi : RInv L s) (p : Pos) (hit : List Step → Bool) (k : Nat) :
    RInv L ((List.range k).foldl (fun t _ => accRound p hit t) s) :=
  foldl_inv (RInv L) (fun t _ => accRound p hit t)
    (fun t _ ht => foldl_inv (RInv L) SState.endLabel (fun t a ht => endLabel_rinv ht a) _ _ ht) _ _ hi

theorem accessOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Pos) (hit : List Step → Bool) :
    AccessOk K φ s p hit ↔ AccessOk K φ' s p hit := by
  unfold AccessOk
  exact forall_congr' fun k => imp_congr_right fun _ => endsOk_congr K hφ _ (rinv_accRounds hi p hit k)

theorem contentOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    ContentOk K φ p s ↔ ContentOk K φ' p s := by
  unfold ContentOk; split
  · exact accessOk_congr K hφ hi _ _
  · exact Iff.rfl

theorem tagOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    TagOk K φ p s ↔ TagOk K φ' p s := by
  unfold TagOk; split
  · exact accessOk_congr K hφ hi _ _
  · exact Iff.rfl

theorem assignOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    AssignOk K φ p s ↔ AssignOk K φ' p s := by
  unfold AssignOk
  cases hr : resolve s p with
  | none => exact Iff.rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    have hi' : RInv L (if steps.isEmpty && (s.shape pos).isSome then s else s.access pos (dataHit steps)) := by
      split
      · exact hi
      · exact access_rinv hi _ _
    exact and_congr (imp_congr_right fun _ => accessOk_congr K hφ hi _ _)
      (imp_congr_right fun _ => forall_congr' fun l => imp_congr_right fun _ => endOk_congr K hφ hi' l)

theorem invalidateOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    InvalidateOk K φ p s ↔ InvalidateOk K φ' p s := by
  unfold InvalidateOk
  refine foldOk_congr (RInv L) (fun s q hs => invalidateOne_congr K hφ hs q)
    (fun s q hs => (invalidateOne_props K φ L q hs).1) (fun s q hs => ?_) _ hi
  unfold InvalOneOk; split
  · exact accessOk_congr K hφ hs _ _
  · exact Iff.rfl

theorem letLendersOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) :
    LetLendersOk K φ s ↔ LetLendersOk K φ' s := by
  unfold LetLendersOk; split
  · exact accessOk_congr K hφ hi _ _
  · exact Iff.rfl

theorem discardOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (R : TyS) :
    DiscardOk K φ R s ↔ DiscardOk K φ' R s := by
  unfold DiscardOk; split
  · exact endOk_congr K hφ hi _
  · exact Iff.rfl

theorem lentPrefixOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos) (steps : List Step) :
    LentPrefixOk K φ pos steps s ↔ LentPrefixOk K φ' pos steps s := by
  unfold LentPrefixOk; split
  · exact accessOk_congr K hφ hi _ _
  · exact Iff.rfl

theorem dropOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (q : Place) (pos : Pos)
    (steps : List Step) : DropOk K φ q pos steps s ↔ DropOk K φ' q pos steps s := by
  unfold DropOk
  have hi' := access_rinv hi pos (dataHit steps)
  have h2 := imp_congr_right (a := K.D.copy (K.D.placeDecl (scopeOf s) q) = false) fun _ => imp_congr
      (typedFut_forall_congr K hφ hi' pos
        (fun x => (Sem.updAt K.dm K.Γ ((s.access pos (dataHit steps)).tyAt pos) (fun _ => .moved) steps x).isSome = true))
      (accessOk_congr K hφ hi pos (dataHit steps))
  cases steps with
  | nil =>
    cases hsh : s.shape pos with
    | none => simp only [hsh]; exact h2
    | some l => simp only [hsh]; exact endOk_congr K hφ hi _
  | cons st sts => exact h2

theorem joinDropOk_congr (hφ : ∀ l, L l → φ l = φ' l) (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) :
    JoinDropOk K φ entry t s ↔ JoinDropOk K φ' entry t s := by
  unfold JoinDropOk
  refine foldOk_congr (RInv L) (fun s q hs => ?_) (fun s q hs => ?_) (fun s q hs => ?_) _ hi
  · split
    · exact dropAt_congr K hφ q _ _ (accessLentPrefix_rinv L hs)
    · rfl
  · split
    · exact dropAt_rinv K φ L q _ _ (accessLentPrefix_rinv L hs)
    · exact hs
  · unfold JoinStepOk; split
    · exact and_congr (lentPrefixOk_congr K hφ hs _ _) (dropOk_congr K hφ (accessLentPrefix_rinv L hs) _ _ _)
    · exact Iff.rfl

theorem entryAccessOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s)
    (bc : List Place × List (Place × Nat)) : EntryAccessOk K φ bc s ↔ EntryAccessOk K φ' bc s := by
  unfold EntryAccessOk
  have hR : ∀ (s : SState) (q : Place), RInv L s → RInv L (entryReroot s q) := fun s q hs => by
    unfold entryReroot; split
    · exact accessLentPrefix_rinv L hs
    · exact hs
  refine and_congr (foldOk_congr (RInv L) (fun _ _ _ => rfl) hR (fun s q hs => ?_) _ hi)
    (foldOk_congr (RInv L) (fun s qk hs => entryCap_congr K hφ hs qk) (fun s qk hs => (entryCap_props K φ L s qk hs).1)
      (fun s qk hs => ?_) _ (foldl_inv (RInv L) entryReroot hR _ _ hi))
  · unfold EntryRerootOk; split
    · exact lentPrefixOk_congr K hφ hs _ _
    · exact Iff.rfl
  · have hi₁ : RInv L (match resolve s qk.1 with | some (pos, steps) => s.access pos (dataHit steps) | none => s) := by
      split
      · exact access_rinv hs _ _
      · exact hs
    unfold EntryCapOk
    refine and_congr ?_ (imp_congr_right fun _ => invalidateOk_congr K hφ hi₁ _)
    split
    · exact accessOk_congr K hφ hs _ _
    · exact Iff.rfl

theorem matchEntryOk_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (ent : Bool) (mt : Term) :
    MatchEntryOk K φ ent mt s ↔ MatchEntryOk K φ' ent mt s := by
  unfold MatchEntryOk
  rw [movedPlaces_congr hφ hi]
  exact imp_congr_right fun _ => entryAccessOk_congr K hφ hi _

theorem capsOk_congr (hφ : ∀ l, L l → φ l = φ' l) (is : List Nat) {s : SState} (hi : RInv L s) :
    FoldOk (capStep K) (CapOk K φ) is s ↔ FoldOk (capStep K) (CapOk K φ') is s := by
  refine foldOk_congr (RInv L) (fun _ _ _ => rfl) (fun s i hs => ?_) (fun s i hs => ?_) _ hi
  · unfold capStep; split
    · dsimp only; split
      · exact access_rinv hs _ _
      · exact setAt_rinv (access_rinv hs _ _) _ _ (FT.const _ _) (fun _ _ => FT.const _ _)
    · exact hs
  · unfold CapOk; split
    · exact accessOk_congr K hφ hs _ _
    · exact Iff.rfl

/-- An `Id`'s observation is the same at both futures: after every borrow ends, every position
factors through `L` (R3). -/
theorem observation_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (reps : List Place)
    (ws : List Sem) (ps₀ : List Pos) (r : Res) : observation φ reps ws ps₀ r s = observation φ' reps ws ps₀ r s := by
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

theorem rinv_foldl_pushBind : ∀ (bl : List SBinding), (∀ b ∈ bl, ∃ c, b.val = fun _ => c) → ∀ {s : SState},
    RInv L s → RInv L (bl.foldl (fun s b => s.pushBind b) s)
  | [], _, _, hi => hi
  | b :: bl, hb, _, hi => by
    obtain ⟨c, hc⟩ := hb b (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    exact rinv_foldl_pushBind bl (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) (pushBind_rinv hi b c hc)

end

theorem anyAtomList_of_mem {P : Value → Bool} {t : Term} : ∀ {ts : List Term}, t ∈ ts → t.anyAtom P = true →
    Term.anyAtomList P ts = true
  | a :: as, hm, h => by
    rw [List.mem_cons] at hm
    rcases hm with e | hm
    · subst e; simp [Term.anyAtomList, h]
    · simp [Term.anyAtomList, anyAtomList_of_mem hm h]

/-! ## The fix clause, named

`run`'s `.fix` clause is a block of `let`s; these definitions name its pieces (copied from it,
`run_fix_def` checks they are the same), so the clause's congruence can be stated and proved
outside the mutual induction, with the body's congruence as a hypothesis. -/

section FixDefs
variable (K : RunCtx) (ρ : Assignment) (φ : Future) (fb : List PBind × PBind)

/-- A borrow parameter's or a plain parameter's push into the closure's frame. -/
noncomputable def fixStep (sa : SState × List Sem × List Pos) (ap : Sem × PiDom) : SState × List Sem × List Pos :=
  let (s, acc, cells) := sa
  let T : TyS := match fb.1[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
  let d : DeclInfo := match fb.1[acc.length]? with | some b => b.2 | none => .other
  if ap.2.isRef then
    let (l, s) := s.freshLoan
    -- docs/31 D126: the cell is a binding of frame 0, `x° ↦ loan l` at the content type, as the
    -- checker's `checkFix` makes it
    let cell : Pos := .bind 0 (((s.env[0]?).map (·.binds.length)).getD 0)
    -- docs/31 D138: the cell is the label's one loan site, as the checker's `loan l` is
    let s := (s.pushCell { ty := .plain T.m, val := fun ψ => ψ l, decl := .other }).setLent l [⟨cell, [], false⟩]
    -- the argument is recorded as the label's member (docs/31 D68: where a label is made)
    let s := pushBindShaped ((s.setHeldMem l ap.1).setHeldTy l T.m) { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
    (s, acc ++ [ap.1], cells ++ [cell])
  else
    (s.pushBind { ty := { T with label := none }, val := fun _ => ap.1, decl := d }, acc ++ [ap.1], cells)

/-- The closure's body run, at a meaning of `self` and arguments (`bodyAt`). -/
noncomputable def fixBodyAt (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat) (body : Term)
    (selfM : Sem) (args : List Sem) : Option BodyOut :=
  let s₁ := s.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }
  let (s₂, _, cells) := (args.zip ps).foldl (fixStep fb) (s₁, [], [])
  match runT K ρ φ true (fb.2.1 args) body s₂ with
  | some ((r, R), s₃) =>
    let keep : Option Nat := if out.isRef then R.label else none
    if EndsOk K φ (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep) s₃ then
      let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
      let finals := cells.map fun c => s₄.valAt c
      some ⟨r, finals, R.label⟩
    else none
  | none => none

/-- The decreasing argument's rank (φ-free). -/
noncomputable def fixRank (dec : Option Nat) (args : List Sem) : Nat := match dec with
  | some j =>
    match args[j]? with
    | some a => semRank a
    | none => 0
  | none => 0

/-- The stages of a recursive closure: stage `k + 1` binds `self` to stage `k`'s closure at the
weakened function type (the true codomain below rank `k`, `Unit` above; docs/34). -/
noncomputable def fixStage (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (dec : Option Nat) (start : Nat)
    (body : Term) : Nat → List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
    (fun k gk => fixBodyAt K ρ φ fb s ps out (piTyAt K.dm.read l ps (weakCod l (fixRank dec) k out)) start body
      (closureAt K.dm.read l φ ps (weakCod l (fixRank dec) k out) (stageFn l ps (fixRank dec) k gk)))

/-- The closure's function: the guarded fixpoint by stages; without a decreasing parameter, stage 1 at
rank `0` (`self` the weakened stage 0, never read). `piT` is no longer read (kept for the callers). -/
noncomputable def fixG (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod) (piT : TyM) (start : Nat)
    (dec : Option Nat) (body : Term) : List Sem → Option BodyOut :=
  fun args => fixStage K ρ φ fb l s ps out dec start body (fixRank dec args + 1) args

/-- Forming the closure accesses each capture, oldest first, and moves the non-copy ones. -/
noncomputable def fixMoves (t : Term) (s : SState) : SState :=
  (capOrder t).foldl (capStep K) s

theorem run_fix_def (tl : Bool) (hint : TyS) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat)
    (body : Term) (s : SState) :
    runT K ρ φ tl hint (.fix self hs ds c dec body) s =
      SM.erasedIf (K.D.flags (scopeOf s) (.fix self hs ds c dec body)) (fun _ =>
        if FoldOk (capStep K) (CapOk K φ) (capOrder (.fix self hs ds c dec body)) s then
        SM.strictS K.dm.read (fun s' => some ((closureAt K.dm.read (K.D.piSort (scopeOf s) (.pi hs ds c)) φ (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)
          (fixG K ρ φ (bindsOf K ρ φ s ds, fixCod K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c) (K.D.piSort (scopeOf s) (.pi hs ds c)) s (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)
            (piTyAt K.dm.read (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c)) s.nextLoan dec body),
        .plain (piTyAt K.dm.read (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ s ds) (codOf K ρ φ s (bindsOf K ρ φ s ds) (ds.map Term.isRefTy) c))),
        s')) (fixMoves K (.fix self hs ds c dec body) s)
        else none) s := by
  rw [runT]
  apply SM.erasedIf_congr
  dsimp only
  rfl

/-! ### The head call of a sealed program at a closure value (docs/31 D233, ruled)

No closure is formed: the closure's function is asked at the call's arguments only (`cloPt`: the function at them, the
trivial output elsewhere, typed at the codomain weakened off them), the body run as the `.fix` clause runs it, from the
closure value's forming state (`cloForm`), its own binding the placeholder `⋆` with no type (ruling (alpha)). -/

/-- The closure value's forming state (`meanV`'s `.clo` clause). -/
noncomputable def cloForm (caps : List Value) (rd : List (DeclInfo × Value)) : SState :=
  stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))

/-- Its binders, body hint and codomain reading, as the `.fix` clause reads them there. -/
noncomputable def cloFb (s₀ : SState) (ds : List Term) (c : Term) : List PBind × PBind :=
  (bindsOf K ρ φ s₀ ds, fixCod K ρ φ s₀ (bindsOf K ρ φ s₀ ds) (ds.map Term.isRefTy) c,
    K.D.typeDecl (K.D.teleDecls (scopeOf s₀) ds) c)

/-- The rank that is `0` exactly at the arguments given. -/
noncomputable def ptRank (a : List Sem) : List Sem → Nat := fun acc => if acc = a then 0 else 1

/-- The closure's function: its body's run at the arguments, its own binding the placeholder. -/
noncomputable def cloG (s₀ : SState) (ds : List Term) (c : Term) (body : Term) : List Sem → Option BodyOut :=
  fixBodyAt K ρ φ (cloFb K ρ φ s₀ ds c) s₀ (runDoms K ρ φ s₀ ds)
    (codOf K ρ φ s₀ (bindsOf K ρ φ s₀ ds) (ds.map Term.isRefTy) c) TyM.err s₀.nextLoan body .proof

/-- The callee the head call applies at `a`: the closure of the function at `a` and the trivial output elsewhere. -/
noncomputable def cloPt (s₀ : SState) (hs : List Hint) (ds : List Term) (c : Term) (body : Term) (a : List Sem) : Res :=
  (closureAt K.dm.read (K.D.piSort (scopeOf s₀) (.pi hs ds c)) φ (runDoms K ρ φ s₀ ds)
      (weakCod (K.D.piSort (scopeOf s₀) (.pi hs ds c)) (ptRank a) 1 (codOf K ρ φ s₀ (bindsOf K ρ φ s₀ ds) (ds.map Term.isRefTy) c))
      (stageFn (K.D.piSort (scopeOf s₀) (.pi hs ds c)) (runDoms K ρ φ s₀ ds) (ptRank a) 1 (cloG K ρ φ s₀ ds c body)),
    .plain (piTyAt K.dm.read (K.D.piSort (scopeOf s₀) (.pi hs ds c)) (runDoms K ρ φ s₀ ds)
      (weakCod (K.D.piSort (scopeOf s₀) (.pi hs ds c)) (ptRank a) 1 (codOf K ρ φ s₀ (bindsOf K ρ φ s₀ ds) (ds.map Term.isRefTy) c))))

/-- The type the arguments are run at: the closure's function type. -/
noncomputable def cloTy (s₀ : SState) (hs : List Hint) (ds : List Term) (c : Term) : TyM :=
  piTyAt K.dm.read (K.D.piSort (scopeOf s₀) (.pi hs ds c)) (runDoms K ρ φ s₀ ds)
    (codOf K ρ φ s₀ (bindsOf K ρ φ s₀ ds) (ds.map Term.isRefTy) c)

/-- **The clause, named.** -/
theorem run_cloCall_def (tl : Bool) (hint : TyS) (caps : List Value) (self : Hint) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) (rd : List (DeclInfo × Value)) (args : List Term) :
    runT K ρ φ tl hint (.call (.val (.clo caps (.fix self hs ds c dec body) rd)) args true) = fun s =>
      SM.erasedIf (K.D.flags (scopeOf s) (.call (.val (.clo caps (.fix self hs ds c dec body) rd)) args true)) (fun s' =>
        match runArgs K ρ φ (K.D.flags (scopeOf s) (.call (.val (.clo caps (.fix self hs ds c dec body) rd)) args true)).1
            (cloTy K ρ φ (cloForm K ρ φ caps rd) hs ds c) [] args s' with
        | some (as, s₁) =>
          if CapsOk K.dm.read (capsVals K ρ φ caps) (capsTys K ρ φ rd) ∧
              (cloPt K ρ φ (cloForm K ρ φ caps rd) hs ds c body (as.map (·.1))).1 ∈ₛ[K.dm.read]
                (cloPt K ρ φ (cloForm K ρ φ caps rd) hs ds c body (as.map (·.1))).2.m ∧
              BorrowArgsTyped K.dm.read (cloPt K ρ φ (cloForm K ρ φ caps rd) hs ds c body (as.map (·.1))) as s₁
          then callOf K.dm.read (cloPt K ρ φ (cloForm K ρ φ caps rd) hs ds c body (as.map (·.1))) as s₁ else none
        | none => none) s := by
  rw [runT]
  rfl

end FixDefs

/-! ## Forming the closure's frame: the cells are ordered at the start -/

section FixProps
variable {L : Nat → Prop} {fb : List PBind × PBind}

/-- A label added to `L` can be dropped again when it is live or read by no one. -/
theorem rinv_drop_one {s : SState} {n : Nat} (h : RInv (fun y => L y ∨ y = n) s)
    (hn : s.Live n ∨ ∀ q, Indep n (s.valAt q)) : RInv L s := by
  obtain ⟨h1, h2, hsa⟩ := h
  rcases hn with hn | hn
  · refine ⟨fun p => (h1 p).mono fun y hy => ?_, fun r x hr hs => (h2 r x hr hs).mono fun y hy => ?_, hsa⟩
    · rcases hy with (hy | rfl) | hy
      · exact .inl hy
      · exact .inr hn
      · exact .inr hy
    · rcases hy with ⟨hy | rfl, hl⟩ | hy
      · exact .inl ⟨hy, hl⟩
      · exact absurd hn hl
      · exact .inr hy
  · refine ⟨fun p => ((h1 p).remove (hn p)).mono fun y ⟨hy, hne⟩ => ?_,
      fun r x hr hs => ((h2 r x hr hs).remove (hn r)).mono fun y ⟨hy, hne⟩ => ?_, hsa⟩
    · rcases hy with (hy | hy) | hy
      · exact .inl hy
      · exact absurd hy hne
      · exact .inr hy
    · rcases hy with ⟨hy | hy, hl⟩ | hy
      · exact .inl ⟨hy, hl⟩
      · exact absurd hy hne
      · exact .inr hy

theorem live_pushTemp {s : SState} (hsa : ShapeAt s) (v : SVal) (y : Nat) : (s.pushTemp v).Live y ↔ s.Live y := by
  rw [live_iff, live_iff]
  constructor
  · rintro ⟨q, _, hs⟩; exact ⟨q, (hsa q y hs).1, hs⟩
  · rintro ⟨q, hq, hs⟩; exact ⟨q, mem_positions_pushTemp s v hq, hs⟩

/-- A cell pushed: it reads `l`, so the invariant holds with `l` added to `L`. -/
theorem rinv_pushTemp_read {s : SState} (hi : RInv L s) (l : Nat) :
    RInv (fun y => L y ∨ y = l) (s.pushTemp fun ψ => ψ l) := by
  obtain ⟨h1, h2, hsa⟩ := hi
  have hlive := live_pushTemp hsa (fun ψ => ψ l)
  refine ⟨fun q => ?_, fun r x _ hs => ?_, fun q x hq => ?_⟩
  · rcases valAt_pushTemp s (fun ψ => ψ l) q with e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.elim (fun h => .inl (.inl h)) (fun h => .inr ((hlive y).mpr h))
    · rw [e]; intro ψ ψ' hψ; exact hψ l (.inl (.inr rfl))
  · have hs' : s.shape r = some x := hs
    have hr' := (hsa r x hs').1
    rw [valAt_pushTemp_old s _ hr']
    exact (h2 r x hr' hs').mono fun y hy => by
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
      · exact .inl ⟨.inl hL, fun h => hn ((hlive y).mp h)⟩
      · exact .inr ⟨(hlive y).mpr hy, hxy⟩
  · have hq' : s.shape q = some x := hq
    exact ⟨mem_positions_pushTemp s _ (hsa q x hq').1, (hsa q x hq').2⟩

theorem pushTemp_last (s : SState) (v : SVal) (hne : s.env ≠ []) :
    Pos.temp (s.pushTemp v).topIdx ((((s.pushTemp v).env.getLast?).map (·.temps.length)).getD 1 - 1)
      ∈ (s.pushTemp v).positions ∧
    (s.pushTemp v).valAt (Pos.temp (s.pushTemp v).topIdx ((((s.pushTemp v).env.getLast?).map (·.temps.length)).getD 1 - 1)) = v := by
  obtain ⟨fr0, e⟩ : ∃ fr0, s.env.getLast? = some fr0 := by
    cases h : s.env.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some fr0 => exact ⟨fr0, rfl⟩
  have e2 : s.env[s.topIdx]? = some fr0 := by
    rw [List.getLast?_eq_getElem?] at e; simpa [SState.topIdx] using e
  rw [pushTemp_getLast, e, pushTemp_topIdx]
  simp only [Option.map_some, Option.getD_some, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  constructor
  · rw [mem_positions]
    simp only [lookup, SState.pushTemp, List.getElem?_modify, e2]
    simp
  · simp [SState.valAt, SState.pushTemp, List.getElem?_modify, e2]

/-- The forming invariant: the frame's state has the invariant, the counter is past the start, the
closure's frame is above frame 0, and every cell is a cell of the state (a binding of frame 0, docs/31
D126) ordered at the start. -/
def FormInv (L : Nat → Prop) (start : Nat) (sa : SState × List Sem × List Pos) : Prop :=
  RInv L sa.1 ∧ start ≤ sa.1.nextLoan ∧ 0 < sa.1.topIdx ∧
    ∀ c ∈ sa.2.2, IsCell sa.1 c ∧ c ∈ sa.1.positions ∧ Ordered L sa.1 start (sa.1.valAt c)

theorem valAt_pushBind_old (s : SState) (b : SBinding) {q : Pos} (hq : q ∈ s.positions) :
    (s.pushBind b).valAt q = s.valAt q := by
  rw [valAt_eq, valAt_eq, lookup_pushBind_old s b q ((mem_positions s q).mp hq)]

theorem nextLoan_pushBindShaped (s : SState) (b : SBinding) : (pushBindShaped s b).nextLoan = s.nextLoan := by
  unfold pushBindShaped
  split
  · dsimp only; split <;> exact (shapeSub_takeLabel s _).2
  · rfl

theorem env_nil_of_envLe {s s' : SState} (h : EnvLe s s') (he : s.env = []) : s'.env = [] :=
  List.eq_nil_of_length_eq_zero (by rw [h.1, he]; rfl)

theorem indep_of_env_nil {s : SState} (he : s.env = []) (y : Nat) (q : Pos) : Indep y (s.valAt q) := by
  have : q ∉ s.positions := by rw [positions_eq, he]; simp
  rw [valAt_of_not_mem _ _ this]; intro _ _; rfl

/-- The record of a label is read by nothing the forming invariant reads. -/
theorem formInv_setHeldMem {start : Nat} {s : SState} {l : Nat} {v : Sem} {acc : List Sem} {cells : List Pos} :
    FormInv L start (s.setHeldMem l v, acc, cells) ↔ FormInv L start (s, acc, cells) := Iff.rfl

theorem setAt_setHeldMem (s : SState) (l : Nat) (v : Sem) (p : Pos) (g : SVal) :
    (s.setHeldMem l v).setAt p g = (s.setAt p g).setHeldMem l v := by
  cases p <;> rfl

theorem takeLabel_setHeldMem (s : SState) (l : Nat) (v : Sem) (k : Nat) :
    (s.setHeldMem l v).takeLabel k = (s.takeLabel k).setHeldMem l v := by
  unfold SState.takeLabel
  have hh : (s.setHeldMem l v).holderOf k = s.holderOf k := rfl
  rw [hh]
  cases h : s.holderOf k with
  | none => rfl
  | some r => dsimp only; rw [setAt_setHeldMem]; rfl

theorem pushBindShaped_setHeldMem (s : SState) (l : Nat) (v : Sem) (b : SBinding) :
    pushBindShaped (s.setHeldMem l v) b = (pushBindShaped s b).setHeldMem l v := by
  unfold pushBindShaped
  cases b.ty.label with
  | none => rfl
  | some k =>
    dsimp only
    rw [takeLabel_setHeldMem]
    have he : (((s.takeLabel k).setHeldMem l v).pushBind b) = ((s.takeLabel k).pushBind b).setHeldMem l v := rfl
    rw [he]
    simp only [SState.setHeldMem_env]
    cases h : ((s.takeLabel k).pushBind b).env.getLast? <;> rfl

theorem formInv_setHeldTy {start : Nat} {s : SState} {l : Nat} {T : TyM} {acc : List Sem} {cells : List Pos} :
    FormInv L start (s.setHeldTy l T, acc, cells) ↔ FormInv L start (s, acc, cells) := Iff.rfl

theorem setAt_setHeldTy (s : SState) (l : Nat) (T : TyM) (p : Pos) (g : SVal) :
    (s.setHeldTy l T).setAt p g = (s.setAt p g).setHeldTy l T := by
  cases p <;> rfl

theorem takeLabel_setHeldTy (s : SState) (l : Nat) (T : TyM) (k : Nat) :
    (s.setHeldTy l T).takeLabel k = (s.takeLabel k).setHeldTy l T := by
  unfold SState.takeLabel
  have hh : (s.setHeldTy l T).holderOf k = s.holderOf k := rfl
  rw [hh]
  cases h : s.holderOf k with
  | none => rfl
  | some r => dsimp only; rw [setAt_setHeldTy]; rfl

theorem pushBindShaped_setHeldTy (s : SState) (l : Nat) (T : TyM) (b : SBinding) :
    pushBindShaped (s.setHeldTy l T) b = (pushBindShaped s b).setHeldTy l T := by
  unfold pushBindShaped
  cases b.ty.label with
  | none => rfl
  | some k =>
    dsimp only
    rw [takeLabel_setHeldTy]
    have he : (((s.takeLabel k).setHeldTy l T).pushBind b) = ((s.takeLabel k).pushBind b).setHeldTy l T := rfl
    rw [he]
    simp only [SState.setHeldTy_env]
    cases h : ((s.takeLabel k).pushBind b).env.getLast? <;> rfl

/-- The loan sites are read by nothing the forming invariant reads (docs/31 D138: the cell is its label's site). -/
theorem formInv_setLent {start : Nat} {s : SState} {l : Nat} {xs : List Site} {acc : List Sem} {cells : List Pos} :
    FormInv L start (s.setLent l xs, acc, cells) ↔ FormInv L start (s, acc, cells) := Iff.rfl

theorem setAt_setLent (s : SState) (l : Nat) (xs : List Site) (p : Pos) (g : SVal) :
    (s.setLent l xs).setAt p g = (s.setAt p g).setLent l xs := by
  cases p <;> rfl

theorem takeLabel_setLent (s : SState) (l : Nat) (xs : List Site) (k : Nat) :
    (s.setLent l xs).takeLabel k = (s.takeLabel k).setLent l xs := by
  unfold SState.takeLabel
  have hh : (s.setLent l xs).holderOf k = s.holderOf k := rfl
  rw [hh]
  cases h : s.holderOf k with
  | none => rfl
  | some r => dsimp only; rw [setAt_setLent]; rfl

theorem pushBindShaped_setLent (s : SState) (l : Nat) (xs : List Site) (b : SBinding) :
    pushBindShaped (s.setLent l xs) b = (pushBindShaped s b).setLent l xs := by
  unfold pushBindShaped
  cases b.ty.label with
  | none => rfl
  | some k =>
    dsimp only
    rw [takeLabel_setLent]
    have he : (((s.takeLabel k).setLent l xs).pushBind b) = ((s.takeLabel k).pushBind b).setLent l xs := rfl
    rw [he]
    simp only [SState.setLent_env]
    cases h : ((s.takeLabel k).pushBind b).env.getLast? <;> rfl

theorem topIdx_pushBindShaped (s : SState) (b : SBinding) : (pushBindShaped s b).topIdx = s.topIdx := by
  unfold SState.topIdx; rw [(envPush_pushBindShaped s b).1]

theorem topIdx_pushBind' (s : SState) (b : SBinding) : (s.pushBind b).topIdx = s.topIdx := by
  simp [SState.pushBind, SState.topIdx]

theorem fixStep_inv {start : Nat} {sa : SState × List Sem × List Pos} (h : FormInv L start sa) (ap : Sem × PiDom) :
    FormInv L start (fixStep fb sa ap) := by
  obtain ⟨s, acc, cells⟩ := sa
  obtain ⟨hi, hst, htop, hcells⟩ := h
  dsimp only at hi hst htop hcells
  unfold fixStep
  dsimp only
  split
  · simp only [SState.freshLoan, pushBindShaped_setHeldTy, pushBindShaped_setHeldMem, pushBindShaped_setLent]
    rw [formInv_setHeldTy, formInv_setHeldMem, formInv_setLent]
    generalize hs₀ : ({ s with nextLoan := s.nextLoan + 1 } : SState) = s₀
    have hi₀ : RInv L s₀ := by rw [← hs₀]; exact freshLoan_rinv hi
    have hpos₀ : s₀.positions = s.positions := by rw [← hs₀]; rfl
    have hval₀ : ∀ q, s₀.valAt q = s.valAt q := by intro q; rw [← hs₀]; rfl
    have hlive₀ : ∀ y, s₀.Live y ↔ s.Live y := by intro y; rw [← hs₀]; rfl
    have hshape₀ : s₀.shape = s.shape := by rw [← hs₀]
    have hnl₀ : s₀.nextLoan = s.nextLoan + 1 := by rw [← hs₀]
    have henv₀ : s₀.env = s.env := by rw [← hs₀]
    have htop₀ : s₀.topIdx = s.topIdx := by unfold SState.topIdx; rw [henv₀]
    obtain ⟨fr0, h0⟩ : ∃ fr0, s₀.env[0]? = some fr0 := by
      rw [henv₀]
      cases e : s.env with
      | nil => simp [SState.topIdx, e] at htop
      | cons fr0 _ => exact ⟨fr0, rfl⟩
    have h0' : s.env[0]? = some fr0 := by rw [← henv₀]; exact h0
    simp only [h0', Option.map_some, Option.getD_some]
    generalize hcb : ({ ty := TyS.plain (match fb.1[acc.length]? with | some b => b.1 acc | none => TyS.plain (ap.2.dom acc)).m, val := fun ψ => ψ s.nextLoan, decl := DeclInfo.other } : SBinding) = cb
    have hcbv : cb.val = fun ψ => ψ s.nextLoan := by rw [← hcb]
    generalize hT : s₀.pushCell cb = T
    have hiT : RInv (fun y => L y ∨ y = s.nextLoan) T := by rw [← hT]; exact rinv_pushCell_read hi₀ cb _ hcbv
    have hliveT : ∀ y, T.Live y ↔ s.Live y := by
      intro y; rw [← hT, live_pushCell hi₀.2.2, hlive₀]
    have hshapeT : T.shape = s.shape := by rw [← hT, ← hshape₀]; rfl
    have hnlT : T.nextLoan = s.nextLoan + 1 := by rw [← hT, ← hnl₀]; rfl
    have htopT : T.topIdx = s.topIdx := by rw [← hT, pushCell_topIdx, htop₀]
    obtain ⟨hmT, hvT⟩ := pushCell_last s₀ cb fr0 h0
    rw [hT] at hmT hvT
    generalize hb : ({ ty := { (match fb.1[acc.length]? with | some b => b.1 acc | none => TyS.plain (ap.2.dom acc)) with label := some s.nextLoan }, val := fun _ => ap.1, decl := (match fb.1[acc.length]? with | some b => b.2 | none => DeclInfo.other) } : SBinding) = b
    have hbl : b.ty.label = some s.nextLoan := by rw [← hb]
    have hi'' : RInv (fun y => L y ∨ y = s.nextLoan) (pushBindShaped T b) :=
      pushBindShaped_rinv hiT b ap.1 (by rw [← hb]) fun l hl => by
        rw [hbl] at hl; cases hl
        refine ⟨.inr (.inl fun q x hq => ?_), by rw [hnlT]; exact Nat.lt_succ_self _⟩
        rw [hshapeT] at hq; exact (hi.2.2 q x hq).2
    have hneT : T.env ≠ [] := by
      intro he
      have : Pos.bind 0 fr0.binds.length ∈ T.positions := hmT
      rw [positions_eq, he] at this; simp at this
    have hlive' : ∀ y, (pushBindShaped T b).Live y ↔ s.Live y ∨ y = s.nextLoan := by
      intro y
      rw [live_pushBindShaped hiT.2.2 b hneT y, hliveT, hbl]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (Option.some.inj h).symm
      · rintro (h | h)
        · exact .inl h
        · exact .inr (by rw [h])
    have htop' : (pushBindShaped T b).topIdx = s.topIdx := by rw [topIdx_pushBindShaped, htopT]
    refine ⟨rinv_drop_one hi'' (.inl ((hlive' _).mpr (.inr rfl))), ?_, by rw [htop']; exact htop, fun c hc => ?_⟩
    · rw [nextLoan_pushBindShaped, hnlT]; exact Nat.le_succ_of_le hst
    · have hmemT : ∀ q ∈ s.positions, q ∈ T.positions := fun q hq => by
        rw [← hT]; exact mem_positions_pushCell _ _ (by rw [hpos₀]; exact hq)
      have hvalT : ∀ q ∈ s.positions, T.valAt q = s.valAt q := fun q hq => by
        rw [← hT, valAt_pushCell_old _ _ (by rw [hpos₀]; exact hq), hval₀]
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨hcell, hcm, ho⟩ := hcells c hc
        refine ⟨by unfold IsCell; rw [htop']; exact hcell, mem_positions_pushBindShaped b (hmemT c hcm), ?_⟩
        refine ordered_step ho ?_ (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
        · rcases valAt_pushBindShaped_old b (hmemT c hcm) with e | e
          · exact .inl (by rw [e, hvalT c hcm])
          · exact .inr ⟨_, e⟩
        · rcases (hlive' y).mp h1 with h | rfl
          · exact absurd h h2
          · exact .inl hst
        · exact absurd ((hlive' y).mpr (.inl h1)) h2
      · simp only [List.mem_singleton] at hc
        subst hc
        refine ⟨.inr (by rw [htop']; exact htop), mem_positions_pushBindShaped b hmT, ?_⟩
        rcases valAt_pushBindShaped_old b hmT with e | e
        · rw [e, hvT, hcbv]
          intro ψ ψ' hψ
          exact hψ s.nextLoan (.inr ⟨(hlive' _).mpr (.inr rfl), hst⟩)
        · rw [e]; exact FT.const _ _
  · refine ⟨pushBind_rinv hi _ ap.1 rfl, hst, by rw [topIdx_pushBind']; exact htop, fun c hc => ?_⟩
    obtain ⟨hcell, hcm, ho⟩ := hcells c hc
    refine ⟨by unfold IsCell; rw [topIdx_pushBind']; exact hcell, mem_positions_pushBind _ _ hcm, ?_⟩
    rw [valAt_pushBind_old _ _ hcm]
    exact ordered_step ho (.inl rfl)
      (fun y h1 h2 => absurd ((live_pushBind hi.2.2 _ y).mp h1) h2)
      (fun y h1 h2 => absurd ((live_pushBind hi.2.2 _ y).mpr h1) h2)

theorem foldl_fixStep_inv {start : Nat} : ∀ (xs : List (Sem × PiDom)) (sa : SState × List Sem × List Pos),
    FormInv L start sa → FormInv L start (xs.foldl (fixStep fb) sa)
  | [], _, h => h
  | x :: xs, sa, h => foldl_fixStep_inv xs _ (fixStep_inv h x)

/-- The bodyAt step is `paramPush` (`Run.lean`): one step binds a parameter in a closure's body frame and in the frame a
later domain or the codomain is read in (docs/31 D210). -/
theorem fixStep_eq_paramPush (fb : List PBind × PBind) : fixStep fb = paramPush fb.1 := rfl

/-- The frame a later domain or the codomain is read in (`extendBy`: under a fresh bottom frame, the parameters bound as
[Def] binds them, a borrow parameter at a fresh label with a cell) keeps the invariant. -/
theorem rinv_extendBy {s : SState} (hi : RInv L s) (bs : List PBind) (rs : List Bool) (acc : List Sem) :
    RInv L (extendBy s bs rs acc) := by
  have h0 : FormInv L s.nextLoan (s.under, [], []) :=
    ⟨rinv_under hi, Nat.le_refl _, under_topIdx_pos s, fun _ hc => by cases hc⟩
  exact (foldl_fixStep_inv (fb := (bs, ((fun _ => .plain TyM.err), DeclInfo.other))) (acc.zip (refDoms rs)) _ h0).1

end FixProps

/-! ## The closure's body at two futures, and its finals -/

section FixCongr
variable (K : RunCtx) (ρ : Assignment) {φ φ' : Future} {L : Nat → Prop} {fb : List PBind × PBind}

theorem formInv_init {s : SState} (hi : RInv L s) (ht : 0 < s.topIdx) (b : SBinding) (c : Sem) (hb : b.val = fun _ => c) :
    FormInv L s.nextLoan (s.pushBind b, [], []) :=
  ⟨pushBind_rinv hi b c hb, Nat.le_refl _, by rw [topIdx_pushBind']; exact ht, fun _ hc => by cases hc⟩

theorem fixBodyAt_congr {body : Term} (hK : ∀ n, (K.C.global n).2.label = none) (hφ : ∀ l, L l → φ l = φ' l)
    (hb : ∀ hint s₂, RInv L s₂ → runT K ρ φ true hint body s₂ = runT K ρ φ' true hint body s₂)
    {s : SState} (hi : RInv L s) (ps : List PiDom) (out : PiCod) (piT : TyM) (selfM : Sem) (args : List Sem) :
    fixBodyAt K ρ φ fb s ps out piT s.nextLoan body selfM args = fixBodyAt K ρ φ' fb s ps out piT s.nextLoan body selfM args := by
  unfold fixBodyAt
  dsimp only
  have hF := foldl_fixStep_inv (fb := fb) (args.zip ps) _
    (formInv_init (L := L) (rinv_under hi) (under_topIdx_pos s) { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } selfM rfl)
  generalize (args.zip ps).foldl (fixStep fb) (s.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], []) = F at hF ⊢
  obtain ⟨s₂, acc, cells⟩ := F
  dsimp only
  rw [hb _ s₂ hF.1]
  cases hr : runT K ρ φ' true (fb.2.1 args) body s₂ with
  | none => rfl
  | some y =>
    obtain ⟨⟨r, R⟩, s₃⟩ := y
    have hi₃ := (runT_rinv K ρ φ' L hK true body _ s₂ s₃ (r, R) hF.1 hr).1
    dsimp only
    rw [propext (endsOk_congr K hφ _ hi₃)]

/-- After the pop, a cell reads `L` and the kept label (`ordered_after_pop`; a state with no frame
has no positions). -/
theorem finals_of_pop {s₂ s₃ : SState} {start : Nat} (hi₃ : RInv L s₃) (e₃ : EnvLe s₂ s₃) (o₃ : OrdKeep L s₂ s₃)
    (hst₂ : start ≤ s₂.nextLoan) {cells : List Pos}
    (hcells : ∀ c ∈ cells, IsCell s₂ c ∧ c ∈ s₂.positions ∧ Ordered L s₂ start (s₂.valAt c))
    (keep : Option Nat) : ∀ c ∈ cells, FT (fun y => L y ∨ some y = keep)
      (((s₃.liveLabels.filter fun l => decide (l ≥ start ∧ some l ≠ keep)).foldl endLabel s₃).valAt c) := by
  intro c hc
  obtain ⟨ht, hcm, ho⟩ := hcells c hc
  exact ordered_after_pop hi₃.1 hi₃.2.1 _ _ (o₃.2 _ c hst₂ ht hcm ho)

theorem fixBodyAt_finals (hK : ∀ n, (K.C.global n).2.label = none) {s : SState} (hi : RInv L s)
    (ps : List PiDom) (out : PiCod) (piT : TyM) (body : Term) (selfM : Sem) (args : List Sem) (o : BodyOut)
    (h : fixBodyAt K ρ φ fb s ps out piT s.nextLoan body selfM args = some o) : FinalsIn L out.isRef o := by
  have hF := foldl_fixStep_inv (fb := fb) (args.zip ps) _
    (formInv_init (L := L) (rinv_under hi) (under_topIdx_pos s) { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } selfM rfl)
  unfold fixBodyAt at h
  dsimp only at h
  generalize hFF : (args.zip ps).foldl (fixStep fb) (s.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], []) = F at hF h
  obtain ⟨s₂, acc, cells⟩ := F
  obtain ⟨hi₂, hst₂, -, hcells⟩ := hF
  dsimp only at h hi₂ hst₂ hcells
  split at h
  · rename_i r R s₃ hrun
    obtain ⟨-, h⟩ := ite_none_some h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hi₃, -, e₃, o₃⟩ := runT_rinv K ρ φ L hK true body _ s₂ s₃ (r, R) hi₂ hrun
    have hcell := finals_of_pop hi₃ e₃ o₃ hst₂ hcells (if out.isRef then R.label else none)
    obtain ⟨b, cod⟩ := out
    cases b
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (hcell c₀ hc₀).mono fun y hy => hy.resolve_right (by simp)
    · intro c hc k hk
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (hcell c₀ hc₀).mono fun y hy => hy.imp_right fun e => by
        simp only [if_true] at e; simp only at hk; rw [hk] at e; exact Option.some.inj e
  · cases h

/-- **The stages of a recursive closure** agree at the two futures, and every stage's finals read
only `L` and the returned label: by induction on the stage, with `closureAt_congr` for `self` (the
weakened stage closure; above the bound its finals are constant). -/
theorem fixStage_congr {body : Term} (hK : ∀ n, (K.C.global n).2.label = none) (hφ : ∀ l, L l → φ l = φ' l)
    (hb : ∀ hint s₂, RInv L s₂ → runT K ρ φ true hint body s₂ = runT K ρ φ' true hint body s₂)
    {s : SState} (hi : RInv L s) (l : Nat) (ps : List PiDom) (out : PiCod) (dec : Option Nat) :
    ∀ k, fixStage K ρ φ fb l s ps out dec s.nextLoan body k = fixStage K ρ φ' fb l s ps out dec s.nextLoan body k ∧
      ∀ args o, fixStage K ρ φ fb l s ps out dec s.nextLoan body k args = some o → FinalsIn L out.isRef o
  | 0 => ⟨rfl, fun _ _ h => by cases h⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := fixStage_congr hK hφ hb hi l ps out dec k
    have hfin : ∀ args o, stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec s.nextLoan body k) args = some o →
        FinalsIn L (weakCod l (fixRank dec) k out).isRef o := by
      intro args o h
      unfold stageFn at h
      split at h
      · exact ih2 args o h
      · cases h
        intro c hc
        obtain ⟨a, rfl⟩ := refFinals_const ps args c hc
        show match out.isRef with
          | false => FT L (fun _ => a)
          | true => ∀ k', some 0 = some k' → FT (fun y => L y ∨ y = k') (fun _ => a)
        cases out.isRef
        · exact FT.const _ _
        · exact fun _ _ => FT.const _ _
    have hcl : closureAt K.dm.read l φ ps (weakCod l (fixRank dec) k out)
          (stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec s.nextLoan body k))
        = closureAt K.dm.read l φ' ps (weakCod l (fixRank dec) k out)
          (stageFn l ps (fixRank dec) k (fixStage K ρ φ' fb l s ps out dec s.nextLoan body k)) := by
      rw [← ih1]; exact closureAt_congr K.dm.read hφ l ps _ _ hfin
    refine ⟨?_, fun args o h => ?_⟩
    · show fixBodyAt K ρ φ fb s ps out (piTyAt K.dm.read l ps (weakCod l (fixRank dec) k out)) s.nextLoan body
          (closureAt K.dm.read l φ ps (weakCod l (fixRank dec) k out)
            (stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec s.nextLoan body k)))
        = fixBodyAt K ρ φ' fb s ps out (piTyAt K.dm.read l ps (weakCod l (fixRank dec) k out)) s.nextLoan body
          (closureAt K.dm.read l φ' ps (weakCod l (fixRank dec) k out)
            (stageFn l ps (fixRank dec) k (fixStage K ρ φ' fb l s ps out dec s.nextLoan body k)))
      rw [hcl]
      funext args
      exact fixBodyAt_congr K ρ hK hφ hb hi ps out _ _ args
    · exact fixBodyAt_finals K ρ hK hi ps out _ body _ args o h

theorem fixG_congr {body : Term} (hK : ∀ n, (K.C.global n).2.label = none) (hφ : ∀ l, L l → φ l = φ' l)
    (hb : ∀ hint s₂, RInv L s₂ → runT K ρ φ true hint body s₂ = runT K ρ φ' true hint body s₂)
    {s : SState} (hi : RInv L s) (l : Nat) (ps : List PiDom) (out : PiCod) (piT : TyM) (dec : Option Nat) :
    fixG K ρ φ fb l s ps out piT s.nextLoan dec body = fixG K ρ φ' fb l s ps out piT s.nextLoan dec body ∧
      ∀ args o, fixG K ρ φ fb l s ps out piT s.nextLoan dec body args = some o → FinalsIn L out.isRef o := by
  refine ⟨funext fun args => ?_, fun args o h => ?_⟩
  · exact congrFun (fixStage_congr K ρ hK hφ hb hi l ps out dec (fixRank dec args + 1)).1 args
  · exact (fixStage_congr K ρ hK hφ hb hi l ps out dec (fixRank dec args + 1)).2 args o h

end FixCongr

/-- The type an embedded value's run carries (`run`'s `.val` clause). -/
noncomputable def valT (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) : Value → TyS
  | .zero | .succ _ => .plain TyM.nat
  | .unit => .plain TyM.unit
  | .ind ty _ _ ps _ => match K.Γ.find? (·.name == ty) with
    | some d =>
      let r? : Option Rec := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, r) => if n = ty then some r else none | none => none)
        else some (K.dm.recOf d (meanParams K ρ φ d 0 [] ps))
      match r? with
      | some r => .plain (K.dm.tyR d r)
      | none => hint
    | none => hint
  | .clo caps t rd => match runT K ρ φ false (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) with
    | some ((_, R), _) => R
    | none => hint
  | .gfn n => (K.C.global n).2
  | .abs σ => K.Δ σ
  | .loan l => if (K.Λ l).m.isPi then K.Λ l else hint
  | .sealed t => match runT K ρ φ false hint t (emptyState 0) with
    | some ((_, R), _) => if R.m.isPi then R else hint
    | none => hint
  | _ => hint

theorem runT_val_def (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (v : Value) (s : SState) {tl : Bool} :
    runT K ρ φ tl hint (.val v) s = strictVal K.dm.read v (meanV K ρ φ hint v, { valT K ρ φ hint v with label := none }) s := by
  cases v <;> rfl

theorem run_val_def (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (v : Value) (s : SState) :
    run K ρ φ hint (.val v) s = strictVal K.dm.read v (meanV K ρ φ hint v, { valT K ρ φ hint v with label := none }) s :=
  runT_val_def K ρ φ hint v s

/-- A strict `.val` decides from its result alone: the state is passed through. -/
theorem strictVal_state (R : DataRead) (v : Value) (x : Res) (s s' : SState) :
    strictVal R v x s = (strictVal R v x s').map (fun p => (p.1, s)) := by
  cases v <;> simp only [strictVal, SM.strictS, pure] <;> (try split) <;> (try split) <;> simp_all

theorem SM.strictS_congr {R : DataRead} {x x' : SM Res} {s : SState} (h : x s = x' s) :
    SM.strictS R x s = SM.strictS R x' s := by
  simp only [SM.strictS, h]

/-- The four equality rules' premises, run in sequence: the same in two contexts where each premise's
run is (congruence and substitution lemmas share it). -/
theorem premises_congr_all {K K' : RunCtx} {ρ ρ' : Assignment} {φ φ' : Future} :
    ∀ (xs : List Term), (∀ x ∈ xs, ∀ s, runT K ρ φ false (.plain .err) x s = runT K' ρ' φ' false (.plain .err) x s) →
    ∀ s, (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
        (pure ((.proof, .plain (TyM.prop True)) : Res))) s =
      (xs.foldr (fun t k => runT K' ρ' φ' false (.plain TyM.err) t >>= fun _ => k)
        (pure ((.proof, .plain (TyM.prop True)) : Res))) s
  | [], _, _ => rfl
  | x :: xs, hx, s => by
    simp only [List.foldr_cons]
    apply SM.bind_congr (hx x (by simp) s)
    intro _ s₁ _
    exact premises_congr_all xs (fun y hy => hx y (by simp [hy])) s₁

theorem SM.onCopy_congr {α : Type 3} {x x' : SM α} {s : SState} (h : x s = x' s) :
    SM.onCopy x s = SM.onCopy x' s := by
  unfold SM.onCopy; rw [h]

section
variable (K : RunCtx) (ρ : Assignment) (φ φ' : Future)

/-- The four equality rules' premises, run in sequence (on one copy): the same at both futures, each
premise's run being. -/
theorem premises_congr (hK : ∀ n, (K.C.global n).2.label = none) {L : Nat → Prop} :
    ∀ (xs : List Term) (s : SState), RInv L s →
    (∀ x ∈ xs, ∀ s, RInv L s → runT K ρ φ false (.plain .err) x s = runT K ρ φ' false (.plain .err) x s) →
    (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k) (pure ((.proof, .plain (TyM.prop True)) : Res))) s =
    (xs.foldr (fun t k => runT K ρ φ' false (.plain TyM.err) t >>= fun _ => k) (pure ((.proof, .plain (TyM.prop True)) : Res))) s
  | [], _, _, _ => rfl
  | x :: xs, s, hi, hx => by
    simp only [List.foldr_cons]
    apply SM.bind_congr (hx x (by simp) s hi)
    intro a s₁ h1
    exact premises_congr hK xs s₁ (runT_rinv K ρ φ L hK false x _ s s₁ a hi h1).1 (fun y hy => hx y (by simp [hy]))

mutual
/-- **Part (E)**: the run at two futures that agree on `L`, from a state with `RInv L`, of a term
whose loans are in `L`, is the same. -/
theorem runT_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (tl : Bool) (t : Term) (hint : TyS) (s : SState)
    (L : Nat → Prop), (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s →
    runT K ρ φ tl hint t s = runT K ρ φ' tl hint t s
  | tl, .place p, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    exact SM.erasedIf_congr (SM.guarded_congr (contentOk_congr K hφ hi p) (readPlace_congr K hφ hi p _))
  | tl, .borrow p, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    show (match SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
      | some (r, s₁) => if InvalidateOk K φ p s₁ ∧ lentOk K φ p (invalidate K φ p s₁) then some (r, invalidate K φ p s₁) else none
      | none => none) = (match SM.strictS K.dm.read (SM.guarded (ContentOk K φ' p) (borrowPlace K φ' p)) s with
      | some (r, s₁) => if InvalidateOk K φ' p s₁ ∧ lentOk K φ' p (invalidate K φ' p s₁) then some (r, invalidate K φ' p s₁) else none
      | none => none)
    rw [SM.strictS_congr (SM.guarded_congr (contentOk_congr K hφ hi p) (borrowPlace_congr K hφ hi p))]
    cases hb : SM.strictS K.dm.read (SM.guarded (ContentOk K φ' p) (borrowPlace K φ' p)) s with
    | none => rfl
    | some y =>
      obtain ⟨r, s₁⟩ := y
      have hi₁ : RInv L s₁ := (borrowPlace_rinv K φ' L (SM.guarded_some (SM.strictS_some hb).1).2 hi).1
      dsimp only
      rw [invalidate_congr K hφ hi₁ p, propext (invalidateOk_congr K hφ hi₁ p),
        lentOk_congr K hφ (invalidate_props K φ' L p hi₁).1 p]
  | tl, .seq u w, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (runT_congrE hK false u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ h1
    apply SM.bind_congr (SM.guardMod_congr (discardOk_congr K hφ (runT_rinv K ρ φ L hK false u _ s s₁ a hi h1).1 a.2))
    intro _ s₂ h2
    have es : s₂ = discardEnd a.2 s₁ := (SM.guardMod_some h2).2
    subst es
    exact runT_congrE hK tl w (tailHint tl hint) _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h]))
      (discardEnd_props L (runT_rinv K ρ φ L hK false u _ s s₁ a hi h1).1 a.2).1
  | tl, .succ u, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrE hK false u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | tl, .ref A, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (runT_congrE hK false A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | tl, .const n, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .sort l, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .nat, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .unit, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .zero, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .tt, hint, s, L, hφ, ht, hi => by rw [runT, runT]
  | tl, .cong f g, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    have hg : ∀ s', RInv L s' → runT K ρ φ false (.plain .err) g s' = runT K ρ φ' false (.plain .err) g s' :=
      fun s' hi' => runT_congrE hK false g _ s' L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi'
    exact SM.onCopy_congr (premises_congr K ρ φ φ' hK [g] s hi (fun y hy => by
      rw [List.mem_singleton.mp hy]; exact hg))
  | tl, .val v, hint, s, L, hφ, ht, hi => by
    have hv : ∀ l, v.hasLoanM l = true → φ l = φ' l := fun l h => hφ l (ht l h)
    rw [runT_val_def, runT_val_def, meanV_congrE hK v hint hv]
    cases v with
    | clo caps t rd =>
      simp only [valT]
      rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
        capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
        runT_congrE hK false t _ _ (fun l => φ l = φ' l) (fun _ h => h)
          (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
    | sealed t =>
      simp only [valT]
      rw [runT_congrE hK false t hint _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])) (rinv_emptyState _)]
    | ind ty c h ps fs =>
      simp only [valT]
      have hP : ∀ d, meanParams K ρ φ d 0 [] ps = meanParams K ρ φ' d 0 [] ps := fun d =>
        meanParams_congrE hK d ps 0 [] (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]))
      simp only [hP]
    | _ => rfl
  | tl, .ascribe u A, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    refine SM.strictS_congr ?_
    apply SM.bind_congr (SM.onCopy_congr (runT_congrE hK false A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runT_congrE hK false u _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro _ _ _; rfl
  | tl, .eq A a b, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    apply SM.onCopy_congr
    apply SM.bind_congr (runT_congrE hK false A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨TA, _⟩ s₁ h1
    have hi₁ := (runT_rinv K ρ φ L hK false A _ s s₁ _ hi h1).1
    apply SM.bind_congr (SM.onCopy_congr (runT_congrE hK false a _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (runT_congrE hK false b _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    intro _ _ _; rfl
  | tl, .id A t u, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    apply Option.bind_congr' (SM.onCopy_congr (runT_congrE hK false A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (runT_congrE hK false t _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₁, s₁'⟩ h2
    apply Option.bind_congr' (runT_congrE hK false u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₂, s₂'⟩ h3
    have hi₁ := (runT_rinv K ρ φ L hK false t _ s s₁' r₁ hi h2).1
    have hi₂ := (runT_rinv K ρ φ L hK false u _ s s₂' r₂ hi h3).1
    simp only [observation_congr hφ hi₁, observation_congr hφ hi₂]
  | tl, .tind n args, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    cases hd : K.Γ.find? (·.name == n) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d args 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro _ _ _; rfl
  | tl, .call f args hd, hint, s, L, hφ, ht, hi => by
    rcases call_cases f hd with hsp | hold
    · -- docs/31 D233: a sealed closure head; the closure's runs at the futures agreeing on its own loans. Taken apart by
      -- `cases` on the head (not a substitution), so that the recursive calls below are on its parts
      cases f
      all_goals try (obtain ⟨_, _, _, _, _, _, _, _, h1, -⟩ := hsp; cases h1; done)
      rename_i v
      cases v
      all_goals try (obtain ⟨_, _, _, _, _, _, _, _, h1, -⟩ := hsp; cases h1; done)
      rename_i caps t rd
      cases t
      all_goals try (obtain ⟨_, _, _, _, _, _, _, _, h1, -⟩ := hsp; cases h1; done)
      rename_i self hs ds c dec body
      obtain ⟨_, _, _, _, _, _, _, _, -, rfl⟩ := hsp
      have hv : ∀ l, (Value.clo caps (.fix self hs ds c dec body) rd).hasLoanM l = true → φ l = φ' l :=
        fun l h => hφ l (ht l (by simp [Value.hasLoanM] at h; simp [Term.anyAtom, h]))
      have hfs : cloForm K ρ φ caps rd = cloForm K ρ φ' caps rd := by
        unfold cloForm
        rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
          capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])]
      have hcv := capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])
      have hct := capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])
      have hi₀ : RInv (fun l => φ l = φ' l) (cloForm K ρ φ' caps rd) := rinv_stateOf _ _ _
      have hta : ∀ l, Term.anyAtom (· == .loan l) (.fix self hs ds c dec body) = true → φ l = φ' l :=
        fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])
      have hbs : bindsOf K ρ φ (cloForm K ρ φ' caps rd) ds = bindsOf K ρ φ' (cloForm K ρ φ' caps rd) ds :=
        runBinds_congrE hK _ _ (fun _ h => h) hi₀ _ ds [] [] (fun l h => hta l (by simp [Term.anyAtom, h]))
      have hds : runDoms K ρ φ (cloForm K ρ φ' caps rd) ds = runDoms K ρ φ' (cloForm K ρ φ' caps rd) ds := by
        unfold runDoms; rw [hbs]
      have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy (cloForm K ρ φ' caps rd) bs rs acc) =
          runT K ρ φ' false (.plain .err) c (extendBy (cloForm K ρ φ' caps rd) bs rs acc) :=
        fun bs rs acc => runT_congrE hK false c _ _ _ (fun _ h => h) (fun l h => hta l (by simp [Term.anyAtom, h]))
          (rinv_extendBy hi₀ bs rs acc)
      have hout : ∀ bs rs, codOf K ρ φ (cloForm K ρ φ' caps rd) bs rs c = codOf K ρ φ' (cloForm K ρ φ' caps rd) bs rs c := by
        intro bs rs
        cases c with
        | ref U =>
          have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy (cloForm K ρ φ' caps rd) bs rs acc) =
              runT K ρ φ' false (.plain .err) U (extendBy (cloForm K ρ φ' caps rd) bs rs acc) :=
            fun bs rs acc => runT_congrE hK false U _ _ _ (fun _ h => h) (fun l h => hta l (by simp [Term.anyAtom, h]))
              (rinv_extendBy hi₀ bs rs acc)
          simp only [codOf, hU]
        | _ => simp only [codOf, hc]
      have hb : ∀ (hint : TyS) (s₂ : SState), RInv (fun l => φ l = φ' l) s₂ →
          runT K ρ φ true hint body s₂ = runT K ρ φ' true hint body s₂ :=
        fun hint s₂ hi₂ => runT_congrE hK true body hint s₂ _ (fun _ h => h) (fun l h => hta l (by simp [Term.anyAtom, h])) hi₂
      have hfb : cloFb K ρ φ (cloForm K ρ φ' caps rd) ds c = cloFb K ρ φ' (cloForm K ρ φ' caps rd) ds c := by
        unfold cloFb fixCod; rw [hbs, hout]
      have hG : cloG K ρ φ (cloForm K ρ φ' caps rd) ds c body = cloG K ρ φ' (cloForm K ρ φ' caps rd) ds c body := by
        unfold cloG; rw [hfb, hds, hbs, hout]
        funext a
        exact fixBodyAt_congr K ρ hK (fun _ h => h) hb hi₀ _ _ _ _ a
      have hpt : ∀ a, cloPt K ρ φ (cloForm K ρ φ' caps rd) hs ds c body a = cloPt K ρ φ' (cloForm K ρ φ' caps rd) hs ds c body a := by
        intro a
        unfold cloPt
        rw [hG, hds, hbs, hout]
        congr 1
        refine closureAt_congr K.dm.read (L := fun l => φ l = φ' l) (fun _ h => h) _ _ _ _ ?_
        intro args o h
        unfold stageFn at h
        split at h
        · exact fixBodyAt_finals K ρ hK hi₀ _ _ _ body _ args o h
        · cases h
          intro c' hc
          obtain ⟨x, rfl⟩ := refFinals_const _ args c' hc
          show match (codOf K ρ φ' (cloForm K ρ φ' caps rd) (bindsOf K ρ φ' (cloForm K ρ φ' caps rd) ds) (ds.map Term.isRefTy) c).isRef with
            | false => FT (fun l => φ l = φ' l) (fun _ => x)
            | true => ∀ k', some 0 = some k' → FT (fun y => (fun l => φ l = φ' l) y ∨ y = k') (fun _ => x)
          cases (codOf K ρ φ' (cloForm K ρ φ' caps rd) (bindsOf K ρ φ' (cloForm K ρ φ' caps rd) ds) (ds.map Term.isRefTy) c).isRef
          · exact FT.const _ _
          · exact fun _ _ => FT.const _ _
      have hty : cloTy K ρ φ (cloForm K ρ φ' caps rd) hs ds c = cloTy K ρ φ' (cloForm K ρ φ' caps rd) hs ds c := by
        unfold cloTy; rw [hds, hbs, hout]
      rw [run_cloCall_def, run_cloCall_def, hfs, hcv, hct]
      dsimp only
      refine SM.erasedIf_congr ?_
      rw [hty, runArgs_congrE hK _ _ args [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi]
      split
      · rename_i as s₁ _
        rw [hpt]
      · rfl
    rw [runT_call_old K ρ φ tl hint f args hd hold, runT_call_old K ρ φ' tl hint f args hd hold]
    dsimp only
    refine SM.erasedIf_congr ?_
    -- the head: a place in place, anything else by its run
    have hhead : SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false (.plain .err) f) s
        = SM.headOf f (fun p => SM.guarded (ContentOk K φ' p) (readPlace K φ' p true)) (runT K ρ φ' false (.plain .err) f) s :=
      SM.headOf_congr (fun p => SM.guarded_congr (contentOk_congr K hφ hi p) (readPlace_congr K hφ hi p true))
        (runT_congrE hK false f _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    apply SM.bind_congr hhead
    intro fv s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.headOf_some h1 with ⟨p, h1⟩ | h1
      · exact (readPlace_rinv K φ L (SM.guarded_some h1).2 hi).1
      · exact (runT_rinv K ρ φ L hK false f _ s s₁ fv hi h1).1
    apply SM.bind_congr (runArgs_congrE hK _ _ args [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
    intro _ _ _; rfl
  | tl, .matchNat p z u, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    dsimp only
    rw [SM.guarded_congr (tagOk_congr K hφ hi p) (tagOf_congr K hφ hi p natTag)]
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₀⟩ h1
    have hi₀ := (tagOf_rinv K φ' L (SM.guarded_some h1).2 hi).1
    dsimp only
    rw [optCheck_congr (matchEntryOk_congr K hφ hi₀ _ _)]
    apply Option.bind_congr' rfl
    intro _ _
    rw [matchEntry_congr K hφ hi₀]
    have hi₁' := (matchEntry_props K φ' L (!tl) (.matchNat p z u) hi₀).1
    generalize matchEntry K φ' (!tl) (.matchNat p z u) s₀ = me at hi₁' ⊢
    obtain ⟨s₁, lend⟩ := me
    have hi₁ : RInv L s₁ := hi₁'
    dsimp only
    rw [movedPlaces_congr hφ hi₁]
    split
    · apply Option.bind_congr' (runT_congrE hK tl z (tailHint tl hint) s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      have hi₂ := (runT_rinv K ρ φ L hK tl z (tailHint tl hint) s₁ s₂ _ hi₁ h2).1
      rw [optCheck_congr (joinDropOk_congr K hφ _ _ hi₂)]
      apply Option.bind_congr' rfl
      intro _ _
      rw [joinDrop_congr K hφ _ _ hi₂]
    · apply Option.bind_congr' (runT_congrE hK tl u (tailHint tl hint) s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      have hi₂ := (runT_rinv K ρ φ L hK tl u (tailHint tl hint) s₁ s₂ _ hi₁ h2).1
      rw [optCheck_congr (joinDropOk_congr K hφ _ _ hi₂)]
      apply Option.bind_congr' rfl
      intro _ _
      rw [joinDrop_congr K hφ _ _ hi₂]
    · rfl
  | tl, .matchInd p n arms, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    dsimp only
    rw [SM.guarded_congr (tagOk_congr K hφ hi p) (tagOf_congr K hφ hi p indTag)]
    apply Option.bind_congr' rfl
    rintro ⟨tg, s₀⟩ h1
    have hi₀ := (tagOf_rinv K φ' L (SM.guarded_some h1).2 hi).1
    dsimp only
    rw [optCheck_congr (matchEntryOk_congr K hφ hi₀ _ _)]
    apply Option.bind_congr' rfl
    intro _ _
    rw [matchEntry_congr K hφ hi₀]
    have hi₁' := (matchEntry_props K φ' L (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) hi₀).1
    generalize matchEntry K φ' (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) s₀ = me at hi₁' ⊢
    obtain ⟨s₁, lend⟩ := me
    have hi₁ : RInv L s₁ := hi₁'
    dsimp only
    rw [movedPlaces_congr hφ hi₁]
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrE hK tl arms (tailHint tl hint) c s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      have hi₂ := (runArm_rinv K ρ φ L hK tl arms (tailHint tl hint) c s₁ s₂ _ hi₁ h2).1
      rw [optCheck_congr (or_congr Iff.rfl (or_congr Iff.rfl (joinDropOk_congr K hφ _ _ hi₂)))]
      apply Option.bind_congr' rfl
      intro _ _
      rw [joinDrop_congr K hφ _ _ hi₂]
    · -- an erased match on a proof with other than one arm: each arm's run on the copy agrees; on a proof of a
      -- non-subsingleton no arm runs (docs/31 D229)
      split
      · split
        · exact SM.anyArm_congr fun c =>
            runArm_congrE hK tl arms (tailHint tl hint) c s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁
        · rfl
      · rfl
  | tl, .letIn x u w, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    apply Option.bind_congr' (runT_congrE hK false u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨⟨v, T⟩, s₁⟩ h1
    obtain ⟨hi₁, hy₁, -, -⟩ := runT_rinv K ρ φ L hK false u _ s s₁ (v, T) hi h1
    have hi₂ := pushBindShaped_rinv hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } v rfl
      fun l hl => by
        rcases hy₁ l hl with ⟨h' | h', hn⟩
        · exact ⟨.inl h', hn⟩
        · exact ⟨.inr (.inr h'), hn⟩
    dsimp only
    apply Option.bind_congr' (runT_congrE hK tl w (tailHint tl hint) _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₂)
    rintro ⟨⟨r, R⟩, s₃⟩ h3
    have hi₃ := (runT_rinv K ρ φ L hK tl w (tailHint tl hint) _ s₃ _ hi₂ h3).1
    dsimp only
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    split
    · exact endOk_congr K hφ hi₃ _
    · exact letLendersOk_congr K hφ hi₃
  | tl, .assign p u, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    -- the place's type (read on a discarded copy), then the right-hand side, then the access
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' (runT_congrE hK false u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨⟨v, R⟩, s₁⟩ h2
    have hi₁ := (runT_rinv K ρ φ L hK false u _ s s₁ _ hi h2).1
    dsimp only
    have hpt : placeTy K φ p s₁ = placeTy K φ' p s₁ := by unfold placeTy; rw [contentOf_congr K hφ hi₁ p]
    rw [hpt]
    by_cases hcnd : v ∈ₛ[K.dm.read] (placeTy K φ' p s₁).m ∧ labTyOk s₁ R.label (placeTy K φ' p s₁).m
    rotate_left
    · rw [if_neg hcnd, if_neg hcnd]
    rw [if_pos hcnd, if_pos hcnd, SM.guarded_congr (assignOk_congr K hφ hi₁ p) (assignAt_congr K hφ hi₁ p v R.label)]
    cases ha : SM.guarded (AssignOk K φ' p) (assignAt K φ' p v R.label) s₁ with
    | none => rfl
    | some y =>
      obtain ⟨r₀, s₃⟩ := y
      have hy₁ := (runT_rinv K ρ φ L hK false u _ s s₁ _ hi h2).2.1
      obtain ⟨hi₃, -, -, -⟩ := assignAt_rinv K φ' L (SM.guarded_some ha).2 hi₁ hy₁
      dsimp only
      rw [invalidate_congr K hφ hi₃ p, propext (invalidateOk_congr K hφ hi₃ p),
        lentOk_congr K hφ (invalidate_props K φ' L p hi₃).1 p]
  | tl, .pi hs ds c, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    have hbs := runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds [] []
      (fun l h => ht l (by simp [Term.anyAtom, h]))
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT K ρ φ' false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrE hK false c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs rs acc)
    dsimp only
    rw [hbs]
    cases c with
    | ref U =>
      have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT K ρ φ' false (.plain .err) U (extendBy s bs rs acc) :=
        fun bs rs acc => runT_congrE hK false U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs rs acc)
      simp only [hU]
    | _ => simp only [hc]
  | tl, .ctor ty c hh ps args, hint, s, L, hφ, ht, hi => by
    rw [runT, runT]
    refine SM.erasedIf_congr ?_
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d ps 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro psM s₁ h1
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      dsimp only
      exact SM.bind_congr (runFields_congrE hK _ d c args 0 _ _ [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
        (fun _ _ _ => rfl)
  | tl, .prim n args, hint, s, L, hφ, ht, hi => by
    have hallT : ∀ t ∈ args, ∀ (tl' : Bool) (hint : TyS) (s : SState), RInv L s →
        runT K ρ φ tl' hint t s = runT K ρ φ' tl' hint t s := fun t hm tl' hint s hi =>
      runAll_congrE hK args t hm tl' hint s L hφ
        (fun l h => ht l (by simp only [Term.anyAtom]; exact anyAtomList_of_mem hm h)) hi
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState), RInv L s →
        run K ρ φ hint t s = run K ρ φ' hint t s := fun t hm hint s hi => hallT t hm false hint s hi
    have hprem : ∀ xs : List Term, (∀ x ∈ xs, x ∈ args) →
        SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s =
        SM.onCopy (xs.foldr (fun t k => runT K ρ φ' false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s := fun xs hxs =>
      SM.onCopy_congr (premises_congr K ρ φ φ' hK xs s hi (fun x hx s' hi' => hall x (hxs x hx) _ s' hi'))
    by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
    · obtain ⟨h0, rfl, hargs⟩ := e1; subst hargs; rw [runT, runT]; exact hprem [h0] (by simp)
    by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
    · obtain ⟨h0, k0, rfl, hargs⟩ := e2; subst hargs; rw [runT, runT]; exact hprem [h0, k0] (by simp)
    by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, hargs⟩ := e3; subst hargs; rw [runT, runT]; exact hprem [h0, u0] (by simp)
    by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, hargs⟩ := e4; subst hargs; rw [runT, runT]; exact hprem [h0, u0] (by simp)
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, hargs⟩ := hJ
      have hm : ∀ x, x ∈ [A, a, b, P, h', t] → x ∈ args := fun x hx => by rw [hargs]; exact hx
      rw [hargs, runT, runT]
      refine SM.erasedIf_congr ?_
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
      apply SM.bind_congr rfl
      intro _ s₆ e6; have e := SM.onCopy_state e6; subst e
      dsimp only
      rw [propext (matchEntryOk_congr K hφ hi true t), matchEntry_congr K hφ hi]
      have hi₁ := (matchEntry_props K φ' L true t hi).1
      rw [movedPlaces_congr hφ hi₁]
      rw [show runT K ρ φ false _ t _ = runT K ρ φ' false _ t _ from hall t (hm t (by simp)) _ _ hi₁]
      split
      · split
        · rename_i r₁ R₁ s₆ h6
          have hi₆ := (runAll_rinv K ρ φ' L hK args t (hm t (by simp)) _ _ _ _ hi₁ h6).1
          rw [propext (joinDropOk_congr K hφ _ _ hi₆), joinDrop_congr K hφ _ _ hi₆]
        · rfl
      · rfl
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl <;>
        (rw [hargs, runT, runT]
         exact SM.erasedIf_congr (SM.headOf_congr (fun p => SM.guarded_congr (contentOk_congr K hφ hi p)
           (readPlace_congr K hφ hi p true)) (hall u hu _ _ hi)))
    by_cases hsp : ∃ f u, n = "split" ∧ args = [.const f, u]
    · obtain ⟨f, u, rfl, hargs⟩ := hsp
      have hu : u ∈ args := by rw [hargs]; simp
      rw [hargs, runT, runT]
      exact SM.erasedIf_congr (hallT u hu tl hint s hi)
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    have hs' : ∀ f u, n = "split" → args = [.const f, u] → False := fun f u e1 e2 => hsp ⟨f, u, e1, e2⟩
    have f1 : ∀ h, n = "symm" → args = [h] → False := fun h0 a b => e1 ⟨h0, a, b⟩
    have f2 : ∀ h k, n = "trans" → args = [h, k] → False := fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
    have f3 : ∀ h u, n = "rewrite" → args = [h, u] → False := fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
    have f4 : ∀ h u, n = "rewriteR" → args = [h, u] → False := fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
    rw [runT, runT]
    all_goals first | rfl | exact f1 | exact f2 | exact f3 | exact f4 | exact hJ' | exact hc1 | exact hc2 | exact hc3 | exact hs'
  | tl, .fix self hs ds c dec body, hint, s, L, hφ, ht, hi => by
    have hbs : bindsOf K ρ φ s ds = bindsOf K ρ φ' s ds :=
      runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds [] [] (fun l h => ht l (by simp [Term.anyAtom, h]))
    have hds : runDoms K ρ φ s ds = runDoms K ρ φ' s ds := by unfold runDoms; rw [hbs]
    have hc : ∀ bs rs acc, runT K ρ φ false (.plain .err) c (extendBy s bs rs acc) = runT K ρ φ' false (.plain .err) c (extendBy s bs rs acc) :=
      fun bs rs acc => runT_congrE hK false c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs rs acc)
    have hb : ∀ (hint : TyS) (s₂ : SState), RInv L s₂ → runT K ρ φ true hint body s₂ = runT K ρ φ' true hint body s₂ :=
      fun hint s₂ hi₂ => runT_congrE hK true body hint s₂ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₂
    have hout : ∀ bs rs, codOf K ρ φ s bs rs c = codOf K ρ φ' s bs rs c := by
      intro bs rs
      cases c with
      | ref U =>
        have hU : ∀ bs rs acc, runT K ρ φ false (.plain .err) U (extendBy s bs rs acc) = runT K ρ φ' false (.plain .err) U (extendBy s bs rs acc) :=
          fun bs rs acc => runT_congrE hK false U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs rs acc)
        simp only [codOf, hU]
      | _ => simp only [codOf, hc]
    have hcod : ∀ bs rs, fixCod K ρ φ s bs rs c = fixCod K ρ φ' s bs rs c := fun bs rs => by unfold fixCod; rw [hout]
    rw [run_fix_def, run_fix_def, hds, hbs, hout, hcod, propext (capsOk_congr K hφ _ hi)]
    obtain ⟨hg1, hg2⟩ := fixG_congr K ρ hK hφ hb hi (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ' s ds)
      (codOf K ρ φ' s (bindsOf K ρ φ' s ds) (ds.map Term.isRefTy) c)
      (piTyAt K.dm.read (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ' s ds) (codOf K ρ φ' s (bindsOf K ρ φ' s ds) (ds.map Term.isRefTy) c)) dec
    rw [← hg1, closureAt_congr K.dm.read hφ _ _ _ _ hg2]

theorem meanV_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (v : Value) (hint : TyS),
    (∀ l, v.hasLoanM l = true → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v
  | .loan l, hint, hv => hv l (by
      show (Value.loan l).anyAtom (· == .loan l) = true
      unfold Value.anyAtom
      show (Value.beq (.loan l) (.loan l) || _) = true
      simp [Value.beq])
  | .succ w, hint, hv => by
    show (meanV K ρ φ _ w).succ = (meanV K ρ φ' _ w).succ
    rw [meanV_congrE hK w _ fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom] at h ⊢; simp [h])]
  | .borrow _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV K ρ φ' hint w
    exact meanV_congrE hK w hint fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h])
  | .gloan _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV K ρ φ' hint w
    exact meanV_congrE hK w hint fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h])
  | .tRef A, hint, hv => by
    show meanV K ρ φ _ A = meanV K ρ φ' _ A
    exact meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h])
  | .tEq A a b, hint, hv => by
    rw [meanV, meanV]
    rw [meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK a _ fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK b _ fun l h => hv l (by simp [Value.hasLoanM] at h ⊢; simp [Value.anyAtom, h])]
  | .clo caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
      runT_congrE hK false t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .tPi caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h]),
      runT_congrE hK false t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .sealed t, hint, hv => by
    rw [meanV, meanV]
    rw [runT_congrE hK false t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])) (rinv_emptyState _)]
  | .ind ty c h ps fs, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      dsimp only
      rw [meanParams_congrE hK d ps _ _ fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])]
      split
      · rename_i r' _
        rw [meanFields_congrE hK d r' c fs _ _ fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])]
      · rfl
    · rfl
  | .tInd n args, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      rw [meanParams_congrE hK d args _ _ fun l h => hv l (by simp [Value.hasLoanM, Value.anyAtom, h])]
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
    ∀ (tl : Bool) (hint : TyS) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s → runT K ρ φ tl hint t s = runT K ρ φ' tl hint t s
  | [], t, h, _, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, tl, hint, s, L, hφ, ht, hi => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ht ⊢; exact runT_congrE hK tl a hint s L hφ ht hi
    · exact runAll_congrE hK as t h tl hint s L hφ ht hi

theorem runBinds_congrE (hK : ∀ n, (K.C.global n).2.label = none) (s : SState) (L : Nat → Prop)
    (hφ : ∀ l, L l → φ l = φ' l) (hi : RInv L s) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind) (rs : List Bool),
    (∀ l, Term.anyAtomList (· == .loan l) ds = true → L l) →
    runBinds K ρ φ s dcs pre rs ds = runBinds K ρ φ' s dcs pre rs ds
  | [], _, _, _ => rfl
  | d :: ds, pre, rs, ht => by
    have hds := fun pre' rs' => runBinds_congrE hK s L hφ hi dcs ds pre' rs' (fun l h => ht l (by simp [Term.anyAtomList, h]))
    have hd : (fun acc => runT K ρ φ false (.plain .err) d (extendBy s pre rs acc))
        = (fun acc => runT K ρ φ' false (.plain .err) d (extendBy s pre rs acc)) :=
      funext fun acc => runT_congrE hK false d _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) (rinv_extendBy hi pre rs acc)
    cases d with
    | ref A =>
      have hA : (fun acc => runT K ρ φ false (.plain .err) A (extendBy s pre rs acc))
          = (fun acc => runT K ρ φ' false (.plain .err) A (extendBy s pre rs acc)) :=
        funext fun acc => runT_congrE hK false A _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, Term.anyAtom, h]))
          (rinv_extendBy hi pre rs acc)
      simp only [runBinds, hA, hds]
    | _ => simp only [runBinds, hd, hds]

theorem runArgs_congrE (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runArgs K ρ φ stmt fT earlier args s = runArgs K ρ φ' stmt fT earlier args s
  | [], _, _, _, _, _, _ => rfl
  | a :: as, earlier, s, L, hφ, ht, hi => by
    simp only [runArgs]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrE hK false a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · exact (runT_rinv K ρ φ L hK false a _ s s₁ r hi h1).1
      · exact hi
    apply SM.bind_congr (runArgs_congrE hK stmt fT as _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi₁)
    intro _ _ _; rfl

theorem runFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem) (s : SState) (L : Nat → Prop),
    (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runFields K ρ φ stmt d c i rh sol earlier args s = runFields K ρ φ' stmt d c i rh sol earlier args s
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | a :: as, i, rh, sol, earlier, s, L, hφ, ht, hi => by
    simp only [runFields]
    apply SM.bind_congr (SM.stmtIf_congr (runT_congrE hK false a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · exact (runT_rinv K ρ φ L hK false a _ s s₁ r hi h1).1
      · exact hi
    apply SM.bind_congr (runFields_congrE hK stmt d c as _ _ _ _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi₁)
    intro _ _ _; rfl

theorem runParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runParams K ρ φ d i earlier args s = runParams K ρ φ' d i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (runT_congrE hK false a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrE hK d as _ _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi)
    intro _ _ _; rfl

theorem runArm_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (tl : Bool) (arms : List (Hint × Term)) (hint : TyS)
    (c : Nat) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomArms (· == .loan l) arms = true → L l) → RInv L s →
    runArm K ρ φ tl hint c arms s = runArm K ρ φ' tl hint c arms s
  | _, [], _, _, _, _, _, _, _ => rfl
  | tl, (_, t) :: rest, hint, c, s, L, hφ, ht, hi => by
    simp only [runArm]
    split
    · exact runT_congrE hK tl t hint s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi
    · exact runArm_congrE hK tl rest hint (c - 1) s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi

theorem capsVals_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (vs : List Value),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) → capsVals K ρ φ vs = capsVals K ρ φ' vs
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [capsVals]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoanM] at h; simp [Value.anyAtomList, h])),
      capsVals_congrE hK vs (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem capsTys_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (rd : List (DeclInfo × Value)),
    (∀ l, Value.anyAtomRd (· == .loan l) rd = true → φ l = φ' l) → capsTys K ρ φ rd = capsTys K ρ φ' rd
  | [], _ => rfl
  | (d, T) :: rest, hv => by
    simp only [capsTys]
    rw [meanV_congrE hK T _ (fun l h => hv l (by simp [Value.hasLoanM] at h; simp [Value.anyAtomRd, h])),
      capsTys_congrE hK rest (fun l h => hv l (by simp [Value.anyAtomRd, h]))]

theorem meanFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanFields K ρ φ d r c i earlier vs = meanFields K ρ φ' d r c i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanFields]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoanM] at h; simp [Value.anyAtomList, h])),
      meanFields_congrE hK d r c vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem meanParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanParams K ρ φ d i earlier vs = meanParams K ρ φ' d i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanParams]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoanM] at h; simp [Value.anyAtomList, h])),
      meanParams_congrE hK d vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]


end

/-- `runT_congrE` at a position that is not a tail. -/
theorem run_congrE (hK : ∀ n, (K.C.global n).2.label = none) (t : Term) (hint : TyS) (s : SState)
    (L : Nat → Prop) (hφ : ∀ l, L l → φ l = φ' l) (ht : ∀ l, t.anyAtom (· == .loan l) = true → L l)
    (hi : RInv L s) : run K ρ φ hint t s = run K ρ φ' hint t s :=
  runT_congrE K ρ φ φ' hK false t hint s L hφ ht hi

end

end Ochr.Meaning
