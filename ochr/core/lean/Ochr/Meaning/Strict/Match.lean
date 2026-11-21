import Ochr.Meaning.Strict.Clauses

/-!
# The state operations of a match, `J` and a closure's formation keep the invariant

A match's tag read and its block entry are accesses (and, for a capture by `&`, D112's invalidation,
`invalidate_sgood`); the drop at its join ends a borrow held at a dropped root, or accesses the place
and writes `⊥` there (at a root: `sgood_setAt_pmem`; at a FIELD path: the dependent-values guess
`setContent_field_moved_sgood`); the lending after the join only records sites. Forming a closure accesses each capture and moves the non-copy ones (at a root).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {φ : Future}

theorem sgood_setLent {s : SState} (hs : SGood K.dm K.Γ φ s) (l : Nat) (xs : List Site) :
    SGood K.dm K.Γ φ (s.setLent l xs) :=
  ⟨hs.bind, hs.holder, hs.held, hs.holderTy, hs.acyc, hs.fresh, hs.uniq⟩

/-- An operation that keeps the invariant where its test holds, folded with the fold's tests. -/
theorem sgood_foldOk {α : Type} (g : SState → α → SState) (ok : SState → α → Prop)
    (hg : ∀ s a, SGood K.dm K.Γ φ s → ok s a → SGood K.dm K.Γ φ (g s a)) :
    ∀ (xs : List α) {s : SState}, SGood K.dm K.Γ φ s → FoldOk g ok xs s → SGood K.dm K.Γ φ (xs.foldl g s)
  | [], _, h, _ => h
  | x :: xs, s, h, hok => by
    rw [List.foldl_cons]
    exact sgood_foldOk g ok hg xs (hg s x h hok.1) hok.2

/-- The access of a lent prefix, where its ends are strict. -/
theorem sgood_accessLentPrefix {s : SState} (hs : SGood K.dm K.Γ φ s) {pos : Pos} {steps : List Step}
    (hok : LentPrefixOk K φ pos steps s) : SGood K.dm K.Γ φ (accessLentPrefix pos steps s) := by
  unfold accessLentPrefix
  unfold LentPrefixOk at hok
  split
  · rename_i ψ hψ
    rw [hψ] at hok
    exact access_sgood hs _ _ hok
  · exact hs

theorem sgood_entryReroot {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) (hok : EntryRerootOk K φ s q) :
    SGood K.dm K.Γ φ (entryReroot s q) := by
  unfold entryReroot
  unfold EntryRerootOk at hok
  split
  · rename_i pos steps hres
    rw [hres] at hok
    exact sgood_accessLentPrefix hs hok
  · exact hs

/-- A capture's access at a block's entry, and for a capture by `&`, D112's invalidation. -/
theorem sgood_entryCap {s : SState} (hs : SGood K.dm K.Γ φ s) (qk : Place × Nat) (hok : EntryCapOk K φ s qk) :
    SGood K.dm K.Γ φ (entryCap K φ s qk) := by
  unfold entryCap
  dsimp only
  have h1 : SGood K.dm K.Γ φ (match resolve s qk.1 with
      | some (pos, steps) => s.access pos (dataHit steps)
      | none => s) := by
    have h0 := hok.1
    split
    · rename_i pos steps hres
      rw [hres] at h0
      exact access_sgood hs _ _ h0
    · exact hs
  split
  · rename_i hm
    exact invalidate_sgood _ h1 (hok.2 hm)
  · exact h1

theorem accessLentPrefix_cases (pos : Pos) (steps : List Step) (s : SState) :
    accessLentPrefix pos steps s = s ∨ ∃ pos' hit, accessLentPrefix pos steps s = s.access pos' hit := by
  unfold accessLentPrefix; split
  · exact .inr ⟨_, _, rfl⟩
  · exact .inl rfl

/-- A block's entry: accesses, and D112's invalidation for the captures by `&`, where their ends are
strict (`MatchEntryOk`). -/
theorem sgood_matchEntry {s : SState} (hs : SGood K.dm K.Γ φ s) (ent : Bool) (mt : Term)
    (hok : MatchEntryOk K φ ent mt s) : SGood K.dm K.Γ φ (matchEntry K φ ent mt s).1 := by
  unfold matchEntry
  split
  · rename_i he
    have h := hok he
    dsimp only
    unfold entryAccess
    exact sgood_foldOk (entryCap K φ) (EntryCapOk K φ) (fun s qk hs h => sgood_entryCap hs qk h) _
      (sgood_foldOk entryReroot (EntryRerootOk K φ) (fun s q hs h => sgood_entryReroot hs q h) _ hs h.1) h.2
  · exact hs

theorem sgood_tagOf {p : Place} {tag : Sem → TyS → Sem} {s s' : SState} {tg : Sem} (hs : SGood K.dm K.Γ φ s)
    (hok : TagOk K φ p s) (h : tagOf K φ p tag s = some (tg, s')) : SGood K.dm K.Γ φ s' := by
  obtain ⟨pos, steps, hres, rfl⟩ := tagOf_some K φ h
  unfold TagOk at hok; rw [hres] at hok
  exact access_sgood hs pos _ hok

open Classical in
/-- The drop's write: the place accessed and written `⊥`, unless it is a copy or the write is undefined
at some typed future (at a root or through `*`, `sgood_setAt_pmem`; at a field path,
`setContent_field_moved_sgood`, whose strict test is this one); the access's ends strict where kept. -/
theorem sgood_dropAt_write {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) {f i : Nat}
    (hpos : Pos.bind f i ∈ s.positions) (steps : List Step)
    (hok : K.D.copy (K.D.placeDecl (scopeOf s) q) = false →
      (∀ ψ, TypedFut K φ (s.access (.bind f i) (dataHit steps)) ψ →
        (Sem.updAt K.dm K.Γ ((s.access (.bind f i) (dataHit steps)).tyAt (.bind f i)) (fun _ => .moved) steps
          ((s.access (.bind f i) (dataHit steps)).valAt (.bind f i) ψ)).isSome) →
      AccessOkF K.dm K.Γ φ s (.bind f i) (dataHit steps)) :
    SGood K.dm K.Γ φ (let s' := s.access (.bind f i) (dataHit steps)
      if K.D.copy (K.D.placeDecl (scopeOf s) q) = true then s else
      if ∀ ψ, TypedFut K φ s' ψ → (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps
          (s'.valAt (.bind f i) ψ)).isSome then
        s'.setAt (.bind f i) fun φ' =>
          (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps (s'.valAt (.bind f i) φ')).getD .err
      else s) := by
  dsimp only
  split
  · exact hs
  · rename_i hc
    split
    · rename_i hu
      have hs' := access_sgood hs (Pos.bind f i) (dataHit steps) (hok (by simpa using hc) hu)
      have hpos' : Pos.bind f i ∈ (s.access (Pos.bind f i) (dataHit steps)).positions := by
        rw [access_positions]; exact hpos
      generalize s.access (Pos.bind f i) (dataHit steps) = s' at hs' hpos' hu ⊢
      by_cases hst : steps = [] ∨ steps = [Step.deref]
      · have e : (fun φ' => (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps
            (s'.valAt (.bind f i) φ')).getD .err) = fun _ => .moved := by
          funext φ'; rcases hst with rfl | rfl
          · rw [Sem.updAt.eq_def]; rfl
          · rw [Sem.updAt.eq_def]; dsimp only; rw [Sem.updAt.eq_def]; rfl
        rw [e]
        exact sgood_setAt_pmem hs' hpos' (fun _ _ _ => .moved _) (fun _ _ => .moved _)
      · have hsc : setContent K φ (.bind f i) steps .moved s' = some (⟨⟩, s'.setAt (.bind f i) fun φ' =>
            (Sem.updAt K.dm K.Γ (s'.tyAt (.bind f i)) (fun _ => .moved) steps (s'.valAt (.bind f i) φ')).getD .err) := by
          unfold setContent; dsimp only; rw [if_pos hu]
        exact setContent_field_moved_sgood hs' hpos' hsc
    · exact hs

/-- The drop of one place at a join: a borrow held at a root ends; otherwise the write; strict ends. -/
theorem sgood_dropAt {s : SState} (hs : SGood K.dm K.Γ φ s) (q : Place) {f i : Nat}
    (hpos : Pos.bind f i ∈ s.positions) (steps : List Step) (hok : DropOk K φ q (.bind f i) steps s) :
    SGood K.dm K.Γ φ (dropAt K φ q (.bind f i) steps s) := by
  unfold dropAt
  unfold DropOk at hok
  cases steps with
  | nil =>
    cases hsh : s.shape (.bind f i) with
    | none => simp only [hsh] at hok ⊢; exact sgood_dropAt_write hs q hpos _ hok
    | some l => simp only [hsh] at hok ⊢; exact endLabel_sgood hs _ hok
  | cons st sts => exact sgood_dropAt_write hs q hpos _ hok

/-- **The drop at a join** keeps the invariant where its ends are strict (`JoinDropOk`): a fold of
drops, each after its lent prefix's access. -/
theorem sgood_joinDrop {s : SState} (hs : SGood K.dm K.Γ φ s) (entry : List Place)
    (t : Term) (hok : JoinDropOk K φ entry t s) : SGood K.dm K.Γ φ (joinDrop K φ entry t s) := by
  unfold joinDrop
  unfold JoinDropOk at hok
  refine sgood_foldOk _ (JoinStepOk K φ) (fun s q hs hq => ?_) _ hs hok
  unfold JoinStepOk at hq
  split
  · rename_i pos steps hres
    rw [hres] at hq
    obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
      have := resolve_bind hres
      cases pos with
      | bind f i => exact ⟨f, i, rfl⟩
      | temp => exact absurd this (by simp [IsTemp])
    have hs₁ := sgood_accessLentPrefix hs hq.1
    have hp₁ : Pos.bind f i ∈ (accessLentPrefix (.bind f i) steps s).positions := by
      rcases accessLentPrefix_cases (.bind f i) steps s with e | ⟨p', hit, e⟩
      · rw [e]; exact resolve_mem hres
      · rw [e, access_positions]; exact resolve_mem hres
    exact sgood_dropAt hs₁ q hp₁ steps hq.2
  · exact hs

end

end Ochr.Meaning.Strict
