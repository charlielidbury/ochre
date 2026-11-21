import Ochr.Meaning.Strict.Clauses

/-!
# The state operations of a match, `J` and a closure's formation keep the invariant

A match's tag read and its block entry are accesses; the drop at its join ends a borrow held at a
dropped root, or accesses the place and writes `⊥` there (at a root: `sgood_setAt_pmem`; at a FIELD
path: the dependent-values guess `setContent_field_moved_sgood`); the lending after the join only
records sites. Forming a closure accesses each capture and moves the non-copy ones (at a root).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {φ : Future}

theorem sgood_setLent {s : SState} (hs : SGood K.dm K.Γ φ s) (l : Nat) (xs : List Site) :
    SGood K.dm K.Γ φ (s.setLent l xs) :=
  ⟨hs.bind, hs.holder, hs.held, hs.holderTy, hs.acyc, hs.fresh, hs.read⟩

/-- An operation that is the identity or an access keeps the invariant, folded. -/
theorem sgood_foldl_access {α : Type} (g : SState → α → SState)
    (hg : ∀ s a, g s a = s ∨ ∃ pos hit, g s a = s.access pos hit) :
    ∀ (xs : List α) {s : SState}, SGood K.dm K.Γ φ s → SGood K.dm K.Γ φ (xs.foldl g s)
  | [], _, h => h
  | x :: xs, s, h => by
    rw [List.foldl_cons]
    apply sgood_foldl_access g hg xs
    rcases hg s x with e | ⟨pos, hit, e⟩
    · rw [e]; exact h
    · rw [e]; exact access_sgood h pos hit

theorem accessLentPrefix_cases (pos : Pos) (steps : List Step) (s : SState) :
    accessLentPrefix pos steps s = s ∨ ∃ pos' hit, accessLentPrefix pos steps s = s.access pos' hit := by
  unfold accessLentPrefix; split
  · exact .inr ⟨_, _, rfl⟩
  · exact .inl rfl

/-- A block's entry: accesses. -/
theorem sgood_matchEntry {s : SState} (hs : SGood K.dm K.Γ φ s) (ent : Bool) (mt : Term) :
    SGood K.dm K.Γ φ (matchEntry K φ ent mt s).1 := by
  unfold matchEntry
  split
  · dsimp only
    unfold entryAccess
    refine sgood_foldl_access (entryCap) (fun s qk => ?_) _ (sgood_foldl_access entryReroot (fun s q => ?_) _ hs)
    · unfold entryCap; split
      · exact .inr ⟨_, _, rfl⟩
      · exact .inl rfl
    · unfold entryReroot; split
      · exact accessLentPrefix_cases _ _ _
      · exact .inl rfl
  · exact hs

theorem sgood_tagOf {p : Place} {tag : Sem → TyS → Sem} {s s' : SState} {tg : Sem} (hs : SGood K.dm K.Γ φ s)
    (h : tagOf K φ p tag s = some (tg, s')) : SGood K.dm K.Γ φ s' := by
  obtain ⟨pos, steps, -, rfl⟩ := tagOf_some K φ h
  exact access_sgood hs pos _

/-- The drop's write: the place accessed and written `⊥`, unless it is a copy or the write fails (at a
root or through `*`, `sgood_setAt_pmem`; at a field path, the dependent-values guess
`setContent_field_moved_sgood`). -/
theorem sgood_dropAt_write (hMR : MemReads K.dm K.Γ) {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) {f i : Nat}
    (hpos : Pos.bind f i ∈ s.positions) (steps : List Step) :
    SGood K.dm K.Γ φ (let s' := s.access (.bind f i) (dataHit steps)
      if K.D.copy (K.D.placeDecl (scopeOf s) q) = true then s else
      match Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps (s'.valAt (.bind f i) (s'.typedFuture φ)) with
      | none => s
      | some _ => s'.setAt (.bind f i) fun φ' =>
          (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps (s'.valAt (.bind f i) φ')).getD .err) := by
  dsimp only
  split
  · exact hs
  · have hs' := access_sgood hs (Pos.bind f i) (dataHit steps)
    have hpos' : Pos.bind f i ∈ (s.access (Pos.bind f i) (dataHit steps)).positions := by
      rw [access_positions]; exact hpos
    generalize s.access (Pos.bind f i) (dataHit steps) = s' at hs' hpos' ⊢
    split
    · exact hs
    · rename_i hu
      by_cases hst : steps = [] ∨ steps = [Step.deref]
      · have e : (fun φ' => (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps
            (s'.valAt (.bind f i) φ')).getD .err) = fun _ => .moved := by
          funext φ'; rcases hst with rfl | rfl <;> rfl
        rw [e]
        exact sgood_setAt_pmem hMR hs' hpos' (fun _ _ _ => .inl rfl) (fun _ _ => .inl rfl)
      · have hsc : setContent K φ (.bind f i) steps .moved s' = some (⟨⟩, s'.setAt (.bind f i) fun φ' =>
            (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps (s'.valAt (.bind f i) φ')).getD .err) := by
          unfold setContent; dsimp only; rw [hu]
        exact setContent_field_moved_sgood hs' ⟨fun e => hst (.inl e), fun e => hst (.inr e)⟩ hsc

/-- The drop of one place at a join: a borrow held at a root ends; otherwise the write. -/
theorem sgood_dropAt (hMR : MemReads K.dm K.Γ) {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) {f i : Nat}
    (hpos : Pos.bind f i ∈ s.positions) (steps : List Step) : SGood K.dm K.Γ φ (dropAt K φ q (.bind f i) steps s) := by
  unfold dropAt
  split
  · exact endLabel_sgood hs _
  · exact sgood_dropAt_write hMR hs q hpos _

/-- **The drop at a join** keeps the invariant: a fold of drops, each after its lent prefix's access. -/
theorem sgood_joinDrop (hMR : MemReads K.dm K.Γ) {s : SState} (hs : SGood K.dm K.Γ φ s) (entry : List Place)
    (t : Term) : SGood K.dm K.Γ φ (joinDrop K φ entry t s) := by
  unfold joinDrop
  generalize K.D.joinMoves (scopeOf s) entry t = qs
  induction qs generalizing s with
  | nil => exact hs
  | cons q qs ih =>
    rw [List.foldl_cons]
    apply ih
    split
    · rename_i pos steps hres
      obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
        have := resolve_bind hres
        cases pos with
        | bind f i => exact ⟨f, i, rfl⟩
        | temp => exact absurd this (by simp [IsTemp])
      have hs₁ : SGood K.dm K.Γ φ (accessLentPrefix (.bind f i) steps s) := by
        rcases accessLentPrefix_cases (.bind f i) steps s with e | ⟨p', hit, e⟩
        · rw [e]; exact hs
        · rw [e]; exact access_sgood hs p' hit
      have hp₁ : Pos.bind f i ∈ (accessLentPrefix (.bind f i) steps s).positions := by
        rcases accessLentPrefix_cases (.bind f i) steps s with e | ⟨p', hit, e⟩
        · rw [e]; exact resolve_mem hres
        · rw [e, access_positions]; exact resolve_mem hres
      exact sgood_dropAt hMR hs₁ q hp₁ steps
    · exact hs

end

end Ochr.Meaning.Strict
