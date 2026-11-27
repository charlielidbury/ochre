import Ochr.Meaning.DataModel.Exists.FrameLocal.Prims

/-!
# Frame locality, part 3: the join's drop, [Entry], captures (exists3, 2026-11-21)

The primitives that act at places the decisions give. Each is a fold over those places; a step
commutes with the transform where its place is outside `Q`, and keeps `Twin`: the state fixed by
`qset Q β` (the bindings at `Q` are `β`'s, so the scope reads the same declared readings at both),
with the layout of the state the term started at (so a place resolves where it did then).
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

/-- The invariant of a fold: `Pre` for both, fixed by `qset Q β`, the layout of `s₀`. -/
structure Twin (Q : Pos → Prop) (β β' : Pos → SBinding) (s₀ s : SState) : Prop where
  pre : Pre Q β s
  pre' : Pre Q β' s
  fix : qset Q β s = s
  env : EnvLe s₀ s

theorem foldl_inv' {α : Type} (g : SState → α → SState) (P : SState → Prop) (A : α → Prop)
    (hP : ∀ s a, P s → A a → P (g s a)) : ∀ (as : List α) (s : SState), P s → (∀ a ∈ as, A a) → P (as.foldl g s)
  | [], _, h, _ => h
  | a :: as, s, h, ha => foldl_inv' g P A hP as _ (hP s a h (ha a (by simp))) fun b hb => ha b (by simp [hb])

section
variable (K : RunCtx) (φ : Future) {Q : Pos → Prop} {β β' : Pos → SBinding}

/-- A step that commutes at both `β` and `β'` and keeps the layout keeps `Twin`. -/
theorem Twin.step {s₀ s : SState} (h : Twin Q β β' s₀ s) {g : SState → SState}
    (hg : g (qset Q β s) = qset Q β (g s)) (hp : Pre Q β (g s)) (hp' : Pre Q β' (g s)) (he : EnvLe s (g s)) :
    Twin Q β β' s₀ (g s) := ⟨hp, hp', by rw [← hg, h.fix], h.env.trans he⟩

/-- One step of the join's drop (`joinDrop`'s fold). -/
noncomputable def joinStep (s : SState) (q : Place) : SState := match resolve s q with
  | some (pos, steps) => dropAt K φ q pos steps (accessLentPrefix pos steps s)
  | none => s

theorem joinDrop_eq (entry : List Place) (t : Term) (s : SState) :
    joinDrop K φ entry t s = (K.D.joinMoves (scopeOf s) entry t).foldl (joinStep K φ) s := rfl

theorem joinDropOk_eq (entry : List Place) (t : Term) (s : SState) :
    JoinDropOk K φ entry t s ↔ FoldOk (joinStep K φ) (JoinStepOk K φ) (K.D.joinMoves (scopeOf s) entry t) s := Iff.rfl

theorem joinStep_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl) {s₀ s : SState} (h : Twin Q β β' s₀ s)
    {q : Place} (hq : RAvoid Q s₀ q) :
    joinStep K φ (qset Q β' s) q = qset Q β' (joinStep K φ s q) ∧ Twin Q β β' s₀ (joinStep K φ s q) ∧
      (JoinStepOk K φ (qset Q β' s) q ↔ JoinStepOk K φ s q) := by
  unfold joinStep JoinStepOk
  rw [qset_resolve]
  cases hr : resolve s q with
  | none => exact ⟨rfl, h, Iff.rfl⟩
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hn : ¬ Q pos := (hq.of_envLe h.env) pos steps hr
    dsimp only
    have ea := accessLentPrefix_qset h.pre' pos steps
    have ea0 := accessLentPrefix_qset h.pre pos steps
    have hA : Twin Q β β' s₀ (accessLentPrefix pos steps s) :=
      h.step ea0 (h.pre.accessLentPrefix _ _) (h.pre'.accessLentPrefix _ _) (accessLentPrefix_envLe _ _ _)
    have hsc : scopeOf (qset Q β' (accessLentPrefix pos steps s)) = scopeOf (accessLentPrefix pos steps s) :=
      scopeOf_qset hA.fix hd
    have hsc0 : scopeOf (qset Q β (accessLentPrefix pos steps s)) = scopeOf (accessLentPrefix pos steps s) := by
      rw [hA.fix]
    obtain ⟨e', p'⟩ := dropAt_qset K φ hA.pre' hn hsc q steps
    obtain ⟨e0, p0⟩ := dropAt_qset K φ hA.pre hn hsc0 q steps
    refine ⟨by rw [ea, e'], hA.step e0 p0 p' (dropAt_envLe K φ _ _ _ _), ?_⟩
    rw [lentPrefixOk_qset K φ h.pre', ea, dropOk_qset K φ hA.pre' hn hsc]

theorem joinDrop_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl) {s₀ s : SState} (h : Twin Q β β' s₀ s)
    (entry : List Place) (t : Term) (hA : ∀ q ∈ K.D.joinMoves (scopeOf s) entry t, RAvoid Q s₀ q) :
    joinDrop K φ entry t (qset Q β' s) = qset Q β' (joinDrop K φ entry t s) ∧
      Twin Q β β' s₀ (joinDrop K φ entry t s) ∧
      (JoinDropOk K φ entry t (qset Q β' s) ↔ JoinDropOk K φ entry t s) := by
  rw [joinDrop_eq, joinDrop_eq, joinDropOk_eq, joinDropOk_eq, scopeOf_qset h.fix hd]
  exact ⟨foldl_qset _ (Twin Q β β' s₀) (RAvoid Q s₀) (fun s a h ha => (joinStep_qset K φ hd h ha).2.1)
      (fun s a h ha => (joinStep_qset K φ hd h ha).1) _ _ h hA,
    foldl_inv' (joinStep K φ) (Twin Q β β' s₀) (RAvoid Q s₀) (fun s a h ha => (joinStep_qset K φ hd h ha).2.1) _ _ h hA,
    foldOk_qset _ _ (Twin Q β β' s₀) (RAvoid Q s₀) (fun s a h ha => (joinStep_qset K φ hd h ha).2.1)
      (fun s a h ha => (joinStep_qset K φ hd h ha).1) (fun s a h ha => (joinStep_qset K φ hd h ha).2.2) _ _ h hA⟩

theorem rAvoid_root {s : SState} {p q : Place} (hp : RAvoid Q s p) (h : q.root = p.root) : RAvoid Q s q := by
  refine rAvoid_of_root fun pos hv hq => ?_
  rw [h] at hv
  have : resolve s p = some (pos, p.steps.2) := by simp [resolve, steps_fst, hv]
  exact hp pos _ this hq

theorem entryReroot_qset {s₀ s : SState} (h : Twin Q β β' s₀ s) (q : Place) :
    entryReroot (qset Q β' s) q = qset Q β' (entryReroot s q) ∧ Twin Q β β' s₀ (entryReroot s q) ∧
      (EntryRerootOk K φ (qset Q β' s) q ↔ EntryRerootOk K φ s q) := by
  unfold entryReroot EntryRerootOk
  rw [qset_resolve]
  cases resolve s q with
  | none => exact ⟨rfl, h, Iff.rfl⟩
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    exact ⟨accessLentPrefix_qset h.pre' pos steps,
      h.step (accessLentPrefix_qset h.pre pos steps) (h.pre.accessLentPrefix _ _) (h.pre'.accessLentPrefix _ _)
        (accessLentPrefix_envLe _ _ _), lentPrefixOk_qset K φ h.pre' pos steps⟩

theorem Twin.access {s₀ s : SState} (h : Twin Q β β' s₀ s) (pos : Pos) (hit : List Step → Bool) :
    Twin Q β β' s₀ (s.access pos hit) :=
  h.step (g := fun s => s.access pos hit) (qset_access' h.pre pos hit) (h.pre.access _ _) (h.pre'.access _ _)
    (envLe_access _ _ _)

theorem Twin.invalidate (hd : ∀ p, Q p → (β' p).decl = (β p).decl) {s₀ s : SState} (h : Twin Q β β' s₀ s) {p : Place}
    (hq : ∀ q ∈ K.D.invalidated (scopeOf s) p, RAvoid Q s₀ q) :
    invalidate K φ p (qset Q β' s) = qset Q β' (invalidate K φ p s) ∧ Twin Q β β' s₀ (invalidate K φ p s) ∧
      (InvalidateOk K φ p (qset Q β' s) ↔ InvalidateOk K φ p s) := by
  obtain ⟨e', i', o'⟩ := invalidate_qset K φ ⟨h.pre', h.env⟩ hq (scopeOf_qset h.fix hd)
  obtain ⟨e0, i0, -⟩ := invalidate_qset K φ ⟨h.pre, h.env⟩ hq (by rw [h.fix])
  refine ⟨e', ⟨i0.1, i'.1, ?_, i'.2⟩, o'⟩
  rw [← e0, h.fix]

theorem Twin.setLent {s₀ s : SState} (h : Twin Q β β' s₀ s) (k : Nat) (xs : List Site) :
    Twin Q β β' s₀ (s.setLent k xs) :=
  ⟨h.pre.of_env rfl rfl, h.pre'.of_env rfl rfl, by rw [← qset_setLent, h.fix], h.env.trans (EnvLe.of_env rfl)⟩

theorem entryCap_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl)
    (hinv : ∀ sc p q, q ∈ K.D.invalidated sc p → q.root = p.root) {s₀ s : SState} (h : Twin Q β β' s₀ s)
    {qk : Place × Nat} (hq : RAvoid Q s₀ qk.1) :
    entryCap K φ (qset Q β' s) qk = qset Q β' (entryCap K φ s qk) ∧ Twin Q β β' s₀ (entryCap K φ s qk) ∧
      (EntryCapOk K φ (qset Q β' s) qk ↔ EntryCapOk K φ s qk) := by
  have hI : ∀ X, Twin Q β β' s₀ X →
      (if (qk.2 == 1) = true then invalidate K φ qk.1 (qset Q β' X) else qset Q β' X) =
        qset Q β' (if (qk.2 == 1) = true then invalidate K φ qk.1 X else X) ∧
      Twin Q β β' s₀ (if (qk.2 == 1) = true then invalidate K φ qk.1 X else X) ∧
      ((qk.2 == 1) = true → (InvalidateOk K φ qk.1 (qset Q β' X) ↔ InvalidateOk K φ qk.1 X)) := by
    intro X hX
    by_cases hb : (qk.2 == 1) = true
    · obtain ⟨e, t, o⟩ := hX.invalidate K φ hd (p := qk.1) (fun q hq' => rAvoid_root hq (hinv _ _ _ hq'))
      rw [if_pos hb, if_pos hb]
      exact ⟨e, t, fun _ => o⟩
    · rw [if_neg hb, if_neg hb]
      exact ⟨rfl, hX, fun h => absurd h hb⟩
  unfold entryCap EntryCapOk
  rw [qset_resolve]
  cases hr : resolve s qk.1 with
  | none =>
    obtain ⟨e, t, o⟩ := hI s h
    exact ⟨e, t, and_congr Iff.rfl (imp_congr_right o)⟩
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    rw [qset_access' h.pre']
    obtain ⟨e, t, o⟩ := hI _ (h.access pos (dataHit steps))
    exact ⟨e, t, and_congr (accessOk_qset K φ h.pre' _ _) (imp_congr_right o)⟩

theorem entryAccess_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl)
    (hinv : ∀ sc p q, q ∈ K.D.invalidated sc p → q.root = p.root) {s₀ s : SState} (h : Twin Q β β' s₀ s)
    (bc : List Place × List (Place × Nat)) (hA : ∀ qk ∈ bc.2, RAvoid Q s₀ qk.1) :
    entryAccess K φ bc (qset Q β' s) = qset Q β' (entryAccess K φ bc s) ∧ Twin Q β β' s₀ (entryAccess K φ bc s) ∧
      (EntryAccessOk K φ bc (qset Q β' s) ↔ EntryAccessOk K φ bc s) := by
  unfold entryAccess EntryAccessOk
  have hR := foldl_qset entryReroot (Twin Q β β' s₀) (fun _ => True)
    (fun s a h _ => (entryReroot_qset K φ h a).2.1) (fun s a h _ => (entryReroot_qset K φ h a).1) bc.1 s h (fun _ _ => trivial)
  have hR' := foldl_inv' entryReroot (Twin Q β β' s₀) (fun _ => True)
    (fun s a h _ => (entryReroot_qset K φ h a).2.1) bc.1 s h (fun _ _ => trivial)
  have hRo := foldOk_qset entryReroot (EntryRerootOk K φ) (Twin Q β β' s₀) (fun _ => True)
    (fun s a h _ => (entryReroot_qset K φ h a).2.1) (fun s a h _ => (entryReroot_qset K φ h a).1)
    (fun s a h _ => (entryReroot_qset K φ h a).2.2) bc.1 s h (fun _ _ => trivial)
  rw [hR]
  have A := fun s a (h : Twin Q β β' s₀ s) (ha : RAvoid Q s₀ (Prod.fst a)) => entryCap_qset K φ hd hinv h ha
  refine ⟨foldl_qset (entryCap K φ) (Twin Q β β' s₀) (fun a => RAvoid Q s₀ a.1) (fun s a h ha => (A s a h ha).2.1)
      (fun s a h ha => (A s a h ha).1) bc.2 _ hR' hA,
    foldl_inv' (entryCap K φ) (Twin Q β β' s₀) (fun a => RAvoid Q s₀ a.1) (fun s a h ha => (A s a h ha).2.1) bc.2 _ hR' hA,
    and_congr hRo (foldOk_qset (entryCap K φ) (EntryCapOk K φ) (Twin Q β β' s₀) (fun a => RAvoid Q s₀ a.1)
      (fun s a h ha => (A s a h ha).2.1) (fun s a h ha => (A s a h ha).1) (fun s a h ha => (A s a h ha).2.2) bc.2 _ hR' hA)⟩

theorem entrySnapshot_qset {s : SState} (h : Pre Q β s) (bc : List Place × List (Place × Nat)) :
    entrySnapshot bc (qset Q β s) = entrySnapshot bc s := by
  unfold entrySnapshot; simp only [qset_resolve, qset_shape_eq h.shape, qset_lent]

theorem entryLend_qset (bc : List Place × List (Place × Nat)) (snap : List Site) (lab : Option Nat) (s : SState)
    (hsh : ∀ p, Q p → s.shape p = none) :
    entryLend bc snap lab (qset Q β s) = qset Q β (entryLend bc snap lab s) := by
  unfold entryLend; cases lab with
  | none => rfl
  | some k =>
    -- lead35 (docs/31 D222): only a live label is lent; `qset` keeps the live labels where `Q` holds no borrow
    rw [qset_liveLabels hsh]
    by_cases hk : k ∈ s.liveLabels
    · dsimp only; rw [if_pos hk, if_pos hk]; simp only [qset_resolve, qset_lent]; rfl
    · dsimp only; rw [if_neg hk, if_neg hk]

theorem Twin.entryLend {s₀ s : SState} (h : Twin Q β β' s₀ s) (bc : List Place × List (Place × Nat)) (snap : List Site)
    (lab : Option Nat) : Twin Q β β' s₀ (entryLend bc snap lab s) := by
  unfold Ochr.Meaning.entryLend; cases lab with
  | none => exact h
  | some k =>
    dsimp only
    split
    · exact h.setLent _ _
    · exact h

theorem matchEntry_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl)
    (hinv : ∀ sc p q, q ∈ K.D.invalidated sc p → q.root = p.root) {s : SState} (h : Twin Q β β' s s)
    (hg : ∀ p, Q p → Good K (β p)) (hg' : ∀ p, Q p → Good K (β' p)) (ent : Bool) (mt : Term)
    (hA : ∀ qk ∈ (K.D.blockCaps (scopeOf s) (movedPlaces φ s) mt).2, RAvoid Q s qk.1)
    {S₁ : SState} {L : Option Nat → SState → SState} (he : matchEntry K φ ent mt s = (S₁, L)) :
    ∃ L', matchEntry K φ ent mt (qset Q β' s) = (qset Q β' S₁, L') ∧ Twin Q β β' s S₁ ∧
      (∀ lab s₂, (∀ p, Q p → s₂.shape p = none) → L' lab (qset Q β' s₂) = qset Q β' (L lab s₂)) ∧
      (∀ lab s₂, Twin Q β β' s s₂ → Twin Q β β' s (L lab s₂)) ∧
      (MatchEntryOk K φ ent mt (qset Q β' s) ↔ MatchEntryOk K φ ent mt s) := by
  unfold matchEntry at he ⊢
  unfold MatchEntryOk
  rw [scopeOf_qset h.fix hd, movedPlaces_qset K φ h.pre' h.fix hg hg']
  cases ent
  · simp only [Bool.false_eq_true, if_false, Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, ⟨rfl, rfl⟩, h, fun _ _ _ => rfl, fun _ _ h => h, ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩⟩
  · obtain ⟨e, t, o⟩ := entryAccess_qset K φ hd hinv h _ hA
    simp only [if_true, Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    rw [e, scopeOf_qset t.fix hd, entrySnapshot_qset t.pre']
    refine ⟨_, ⟨rfl, rfl⟩, t, fun lab s₂ hsh => ?_, fun lab s₂ h₂ => ?_, imp_congr_right fun _ => o⟩
    · dsimp only
      split
      · exact entryLend_qset _ _ _ _ hsh
      · rfl
    · dsimp only
      split
      · exact h₂.entryLend _ _ _
      · exact h₂

theorem capStep_qset (hd : ∀ p, Q p → (β' p).decl = (β p).decl) {s₀ s : SState} (h : Twin Q β β' s₀ s) {i : Nat}
    (hi : ∀ pos, s₀.varPos i = some pos → ¬ Q pos) :
    capStep K (qset Q β' s) i = qset Q β' (capStep K s i) ∧ Twin Q β β' s₀ (capStep K s i) ∧
      (CapOk K φ (qset Q β' s) i ↔ CapOk K φ s i) := by
  unfold capStep CapOk
  rw [qset_varPos]
  cases hv : s.varPos i with
  | none => exact ⟨rfl, h, Iff.rfl⟩
  | some pos =>
    have hn : ¬ Q pos := hi pos (by rw [← varPos_of_envLe h.env]; exact hv)
    dsimp only
    have ha := h.access pos (dataHit [])
    rw [qset_access' h.pre', scopeOf_qset ha.fix hd]
    refine ⟨?_, ?_, accessOk_qset K φ h.pre' _ _⟩
    · split
      · rfl
      · exact qset_setAt _ hn _
    · split
      · exact ha
      · exact ha.step (g := fun s => s.setAt pos fun _ => .moved) (qset_setAt _ hn _) (ha.pre.setAt _ _)
          (ha.pre'.setAt _ _) (envLe_setAt _ _ _)

/-- One write of `Id`'s observation. -/
noncomputable def obsStep (ws : List Sem) (s : SState) (qi : Place × Nat) : SState :=
  match resolve s qi.1, ws[qi.2]? with
  | some (pos, []), some w => s.setAt pos fun _ => w
  | _, _ => s

/-- The state `Id`'s observation reads: the writes, then every borrow ended. -/
noncomputable def obsEnd (reps : List Place) (ws : List Sem) (s : SState) : SState :=
  (reps.zipIdx.foldl (obsStep ws) s).liveLabels.foldl SState.endLabel (reps.zipIdx.foldl (obsStep ws) s)

theorem observation_eq (reps : List Place) (ws : List Sem) (ps₀ : List Pos) (r : Res) (s : SState) :
    observation φ reps ws ps₀ r s = r.1 :: ps₀.map fun p => (obsEnd reps ws s).valAt p φ := rfl

theorem obsStep_qset (ws : List Sem) {s₀ s : SState} (h : Pre Q β s ∧ EnvLe s₀ s) {qi : Place × Nat}
    (hq : RAvoid Q s₀ qi.1) : obsStep ws (qset Q β s) qi = qset Q β (obsStep ws s qi) ∧
      (Pre Q β (obsStep ws s qi) ∧ EnvLe s₀ (obsStep ws s qi)) := by
  unfold obsStep
  rw [qset_resolve]
  cases hr : resolve s qi.1 with
  | none => exact ⟨rfl, h⟩
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    have hn : ¬ Q pos := (hq.of_envLe h.2) pos steps hr
    cases steps with
    | cons _ _ => exact ⟨rfl, h⟩
    | nil =>
      cases ws[qi.2]? with
      | none => exact ⟨rfl, h⟩
      | some w => exact ⟨qset_setAt _ hn _, h.1.setAt _ _, h.2.trans (envLe_setAt _ _ _)⟩

theorem obsEnd_qset (reps : List Place) (ws : List Sem) {s : SState} (h : Pre Q β s)
    (hq : ∀ q ∈ reps, RAvoid Q s q) : obsEnd reps ws (qset Q β s) = qset Q β (obsEnd reps ws s) := by
  unfold obsEnd
  have hA : ∀ qi ∈ reps.zipIdx, RAvoid Q s qi.1 := fun qi hqi => by
    obtain ⟨h1, h2⟩ := List.mem_zipIdx' hqi
    exact hq _ (h2 ▸ List.getElem_mem h1)
  have e := foldl_qset (obsStep ws) (fun t => Pre Q β t ∧ EnvLe s t) (fun qi => RAvoid Q s qi.1)
    (fun t a h ha => (obsStep_qset ws h ha).2) (fun t a h ha => (obsStep_qset ws h ha).1) reps.zipIdx s
    ⟨h, EnvLe.refl s⟩ hA
  have p := foldl_inv' (obsStep ws) (fun t => Pre Q β t ∧ EnvLe s t) (fun qi => RAvoid Q s qi.1)
    (fun t a h ha => (obsStep_qset ws h ha).2) reps.zipIdx s ⟨h, EnvLe.refl s⟩ hA
  rw [e, qset_liveLabels p.1.shape, qset_foldl_endLabel p.1.temp p.1.const _ _ p.1.shape]

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
