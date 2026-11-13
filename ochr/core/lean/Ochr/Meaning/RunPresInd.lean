import Ochr.Meaning.RunOrd

/-!
# Part (P) of the locality induction: the run keeps the invariant

`run_rinv`: a successful run from a state with `RInv L` ends in one, its result's label is live or
unread (`LoU`), the frames keep their bindings, only gaining temporaries (`EnvLe`, so an
assignment's target is still a position after its right-hand side runs), and every temporary
ordered at a bound below the counter stays so (`OrdKeep`, for a closure's cells: `RunOrd.lean`). By induction on the
term, mutually with the arms, the fields, the arguments and a primitive's arguments; each clause
composes the primitives' lemmas of `RunPres.lean` and `RunEnv.lean`. A statement position
(`SM.onCopy`) leaves the state as it was. The globals carry no label (`hK`).
-/

namespace Ochr.Meaning

open SState

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future) (L : Nat → Prop)

/-- A statement position (`onCopy`) leaves the state as it was. -/
theorem SM.onCopy_state {α : Type 3} {x : SM α} {s s' : SState} {a : α} (h : SM.onCopy x s = some (a, s')) :
    s' = s := by
  unfold SM.onCopy at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p => rw [hx] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm

theorem run_val_eq (hint : TyS) (v : Value) (s : SState) :
    ∃ T : TyS, run K ρ φ hint (.val v) s = some ((meanV K ρ φ hint v, T), s) ∧ T.label = none := by
  cases v <;> exact ⟨_, rfl, rfl⟩

/-- An inductive's parameters are statements: the state is unchanged. -/
theorem runParams_state (d : IndDecl) : ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s s' : SState)
    (ps : List Sem), runParams K ρ φ d i earlier args s = some (ps, s') → s' = s
  | [], i, earlier, s, s', ps, h => by
    simp only [runParams] at h
    have := SM.pure_some h
    simp only [Prod.mk.injEq] at this
    exact this.2
  | a :: as, i, earlier, s, s', ps, h => by
    simp only [runParams] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    have e1 := SM.onCopy_state h1
    subst e1
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    have e2 := runParams_state d as _ _ _ _ _ h3
    subst e2
    have := SM.pure_some h4
    simp only [Prod.mk.injEq] at this
    exact this.2

theorem SM.onCopy_result {α : Type 3} {x : SM α} {s s' : SState} {a : α} (h : SM.onCopy x s = some (a, s')) :
    ∃ s₁, x s = some (a, s₁) := by
  unfold SM.onCopy at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p => rw [hx] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              exact ⟨p.2, by rw [← h.1]⟩

theorem rinv_ret {s s₁ : SState} (hi : RInv L s₁) (he : EnvLe s s₁) (ho : OrdKeep L s s₁) {r : Res}
    (hl : r.2.label = none) : RInv L s₁ ∧ LoU s₁ r.2.label ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ :=
  ⟨hi, (fun l h' => by rw [hl] at h'; cases h'), he, ho⟩

theorem rinv_pure {s : SState} (hi : RInv L s) {r : Res} (hl : r.2.label = none) :
    RInv L s ∧ LoU s r.2.label ∧ EnvLe s s ∧ OrdKeep L s s :=
  rinv_ret L hi (EnvLe.refl s) (OrdKeep.refl s) hl

/-- A primitive's run: a proof (no state change, no label), one of its arguments' runs (`J`,
`clone`/`peek` of a non-place, `inplace`), or a copying read. -/
theorem run_prim_cases (K : RunCtx) (ρ : Assignment) (φ : Future) {hint : TyS} {n : String} {args : List Term}
    {s s' : SState} {r : Res} (h : run K ρ φ hint (.prim n args) s = some (r, s')) :
    (s' = s ∧ r.2.label = none) ∨
    (∃ t, t ∈ args ∧ run K ρ φ hint t s = some (r, s')) ∨
    (∃ p, readPlace K φ p true s = some (r, s')) := by
  by_cases h1 : n = "symm"
  · subst h1; rw [run] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); exact .inl ⟨rfl, rfl⟩
  by_cases h2 : n = "trans"
  · subst h2; rw [run] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); exact .inl ⟨rfl, rfl⟩
  by_cases h3 : n = "rewrite"
  · subst h3; rw [run] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); exact .inl ⟨rfl, rfl⟩
  by_cases h4 : n = "rewriteR"
  · subst h4; rw [run] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); exact .inl ⟨rfl, rfl⟩
  have fail : ∀ (hJ : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False)
      (hc : ∀ u, n = "clone" → args = [u] → False) (hp : ∀ u, n = "peek" → args = [u] → False)
      (hi : ∀ u, n = "inplace" → args = [u] → False), False := by
    intro hJ hc hp hi
    rw [run.eq_39 K ρ φ hint n args h1 h2 h3 h4 hJ hc hp hi] at h
    cases h
  by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
  · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact .inl ⟨rfl, hl⟩
    obtain ⟨_, s₁, e1, h⟩ := SM.bind_some h
    obtain ⟨_, s₂, e2, h⟩ := SM.bind_some h
    obtain ⟨_, s₃, e3, h⟩ := SM.bind_some h
    obtain ⟨_, s₄, e4, h⟩ := SM.bind_some h
    obtain ⟨_, s₅, e5, h⟩ := SM.bind_some h
    rw [SM.onCopy_state e1] at e2; rw [SM.onCopy_state e2] at e3; rw [SM.onCopy_state e3] at e4
    rw [SM.onCopy_state e4] at e5; rw [SM.onCopy_state e5] at h
    exact .inr (.inl ⟨t, by simp, h⟩)
  by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
  · obtain ⟨u, hn, rfl⟩ := hc
    have key : ∀ b : Bool, SM.stmtIf b (SM.headOf u (fun p => readPlace K φ p true) (run K ρ φ hint u)) s = some (r, s') →
        (s' = s ∧ r.2.label = none) ∨ (∃ t, t ∈ [u] ∧ run K ρ φ hint t s = some (r, s')) ∨
        (∃ p, readPlace K φ p true s = some (r, s')) := by
      intro b h
      rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
      · rcases SM.headOf_some h with ⟨p, h⟩ | h
        · exact .inr (.inr ⟨p, h⟩)
        · exact .inr (.inl ⟨u, by simp, h⟩)
      · exact .inl ⟨rfl, hl⟩
    rcases hn with rfl | rfl | rfl <;> (rw [run] at h; exact key _ h)
  exfalso
  exact fail (fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩)
    (fun u e1 e2 => hc ⟨u, .inl e1, e2⟩) (fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩)
    (fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩)

/-- The position a `let`'s drop removes is the same after a pointwise change of the values. -/
theorem dropped_mapVals (s : SState) (g : Pos → SVal → SVal) : (s.mapVals g).dropped = s.dropped := by
  unfold dropped
  simp only [SState.mapVals, topIdx, List.length_map, List.length_zipIdx, List.getLast?_eq_getElem?,
    List.getElem?_map, List.getElem?_zipIdx]
  cases s.env[s.env.length - 1]? <;> simp [SState.topIdx]

theorem dropped_endLabel (s : SState) (l : Nat) : (s.endLabel l).dropped = s.dropped := by
  cases e : s.holderOf l with
  | none => rw [endLabel_of_none e]
  | some r => rw [endLabel_eq e]; unfold endAt; rw [dropped_mapVals]; rfl

/-- **The `let`'s drop**: the borrow the binding holds now ends, then the binding is forgotten;
the invariant is kept and the body's result label stays live or unread. -/
theorem letDrop_rinv {s : SState} (hi : RInv L s) {lab : Option Nat} (hy : LoU s lab) (held : Option Nat)
    (hheld : held = match s.dropped with | some r => s.shape r | none => none) :
    RInv L (match held with | some l => s.endLabel l | none => s).dropLast ∧
    LoU (match held with | some l => s.endLabel l | none => s).dropLast lab ∧
    OrdKeep L s (match held with | some l => s.endLabel l | none => s).dropLast := by
  have hind : ∀ r x, (match held with | some l => s.endLabel l | none => s).dropped = some r →
      (match held with | some l => s.endLabel l | none => s).shape r = some x →
      ∀ p, Indep x ((match held with | some l => s.endLabel l | none => s).valAt p) := by
    intro r x hr hx
    cases held with
    | none =>
      simp only at hr hx ⊢
      rw [hr] at hheld; simp only at hheld; rw [hx] at hheld; cases hheld
    | some l =>
      simp only at hr hx ⊢
      rw [dropped_endLabel] at hr
      rw [hr] at hheld; simp only at hheld
      have hrpos : r ∈ s.positions := (hi.2.2 r l hheld.symm).1
      obtain ⟨r', hr'⟩ := holderOf_of_live (live_of_shape hrpos hheld.symm)
      obtain ⟨hr'pos, hr'shape⟩ := holderOf_spec hr'
      rw [endLabel_eq hr'] at hx ⊢
      rw [endAt_shape] at hx
      simp only at hx
      split at hx
      · cases hx
      · rw [← hheld] at hx; cases hx
        exact endAt_indep hi.2.1 hr'pos hr'shape
  have hi₄ : RInv L (match held with | some l => s.endLabel l | none => s) := by
    cases held with
    | none => exact hi
    | some l => exact endLabel_rinv hi l
  have hy₄ : LoU (match held with | some l => s.endLabel l | none => s) lab := by
    intro y hl
    cases held with
    | none => exact hy y hl
    | some l => exact lou_endLabel L hi.2.1 (hy y hl) l
  have ho₄ : OrdKeep L s (match held with | some l => s.endLabel l | none => s) ∧
      EnvLe s (match held with | some l => s.endLabel l | none => s) := by
    cases held with
    | none => exact ⟨OrdKeep.refl s, EnvLe.refl s⟩
    | some l => exact ⟨ordKeep_endLabel hi.2.1 l, envLe_endLabel s l⟩
  exact ⟨dropLast_rinv hi₄ hind, fun y hl => lou_dropLast (hy₄ y hl) hind,
    ho₄.1.trans ho₄.2 (ordKeep_dropLast hind)⟩

/-- **An assignment's hold**: the borrow written at a root makes the place its holder (the label
taken from its old holder). The place's meaning is constant, any label it held is read by no one,
and the label is live or read by no one. -/
theorem hold_rinv {s : SState} (hi : RInv L s) (pos : Pos) (hpos : pos ∈ s.positions)
    (hc : ∀ ψ ψ', s.valAt pos ψ = s.valAt pos ψ') {l : Nat} (hl : LoU1 s l)
    (hold : ∀ x, s.shape pos = some x → ∀ q, Indep x (s.valAt q)) :
    RInv L { s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q } := by
  obtain ⟨h1, h2, hsa⟩ := hi
  generalize hF : ({ s.takeLabel l with shape := fun q => if q = pos then some l else (s.takeLabel l).shape q }
    : SState) = F
  have hposF : F.positions = s.positions := by rw [← hF, ← takeLabel_positions s l]; rfl
  have hvalF : ∀ q, F.valAt q = s.valAt q ∨ F.valAt q = fun _ => .moved := by
    intro q; rw [← hF]; exact takeLabel_valAt s l q
  have hshF : ∀ q, F.shape q = if q = pos then some l else (s.takeLabel l).shape q := by
    intro q; rw [← hF]
  have hnlF : F.nextLoan = s.nextLoan := by rw [← hF]; exact (shapeSub_takeLabel s l).2
  have hlF : F.Live l := (live_iff F l).mpr ⟨pos, by rw [hposF]; exact hpos, by rw [hshF]; simp⟩
  have hliveF_rev : ∀ y, F.Live y → s.Live y ∨ y = l := by
    intro y hy
    obtain ⟨q, hq, hs⟩ := (live_iff F y).mp hy
    rw [hshF] at hs
    split at hs
    · cases hs; exact .inr rfl
    · exact .inl (live_of_shape (by rw [← hposF]; exact hq) (takeLabel_shape_some hs))
  have hliveF : ∀ y, s.Live y → (∀ x, s.shape pos = some x → y ≠ x) → F.Live y := by
    intro y hy hX
    by_cases hyl : y = l
    · rw [hyl]; exact hlF
    obtain ⟨q, hq, hs⟩ := (live_iff _ y).mp (takeLabel_live hy hyl)
    by_cases hqp : q = pos
    · subst hqp; exact absurd rfl (hX y (takeLabel_shape_some hs))
    · refine (live_iff F y).mpr ⟨q, by rw [hposF, ← takeLabel_positions s l]; exact hq, ?_⟩
      rw [hshF, if_neg hqp]; exact hs
  -- the label the place held, and `l` if not live, are read by no one: a reading of them is dropped
  have hremX : ∀ q (S : Nat → Prop), FT S (s.valAt q) →
      FT (fun y => S y ∧ ∀ x, s.shape pos = some x → y ≠ x) (s.valAt q) := by
    intro q S hf
    cases hX : s.shape pos with
    | none => exact hf.mono fun y hy => ⟨hy, fun x hx => by cases hx⟩
    | some x =>
      exact (hf.remove (hold x hX q)).mono fun y ⟨hy, hne⟩ =>
        ⟨hy, fun x' hx' => by cases hx'; exact hne⟩
  have hremL : ∀ q (S : Nat → Prop), FT S (s.valAt q) → FT (fun y => S y ∧ (¬ s.Live l → y ≠ l)) (s.valAt q) := by
    intro q S hf
    by_cases hL : s.Live l
    · exact hf.mono fun y hy => ⟨hy, fun h => absurd hL h⟩
    · exact (hf.remove ((hl.1.resolve_left hL) q)).mono fun y ⟨hy, hne⟩ => ⟨hy, fun _ => hne⟩
  refine ⟨fun q => ?_, fun r x hr hs => ?_, fun q x hq => ?_⟩
  · rcases hvalF q with e | e
    · rw [e]
      exact (hremX q _ (h1 q)).mono fun y ⟨hy, hX⟩ => hy.imp_right fun h => hliveF y h hX
    · rw [e]; exact FT.const _ _
  · rw [hshF] at hs
    rw [hposF] at hr
    split at hs
    · rename_i hrp
      subst hrp
      rcases hvalF r with e | e
      · rw [e]; exact fun ψ ψ' _ => hc ψ ψ'
      · rw [e]; exact FT.const _ _
    · rename_i hrp
      rcases hvalF r with e | e
      · rw [e]
        exact (hremL r _ (hremX r _ (h2 r x hr (takeLabel_shape_some hs)))).mono fun y ⟨⟨hy, hX⟩, hL⟩ => by
          rcases hy with ⟨hLy, hn⟩ | ⟨hy, hxy⟩
          · by_cases hF' : F.Live y
            · rcases hliveF_rev y hF' with h' | h'
              · exact absurd h' hn
              · subst h'; exact absurd rfl (hL hn)
            · exact .inl ⟨hLy, hF'⟩
          · exact .inr ⟨hliveF y hy hX, hxy⟩
      · rw [e]; exact FT.const _ _
  · rw [hshF] at hq
    rw [hposF, hnlF]
    split at hq
    · rename_i hqp
      cases hq; exact ⟨by rw [hqp]; exact hpos, hl.2⟩
    · obtain ⟨hq1, hq2⟩ := takeLabel_shapeAt hsa l q x hq
      rw [takeLabel_positions] at hq1
      exact ⟨hq1, by rw [← (shapeSub_takeLabel s l).2]; exact hq2⟩

/-- Forming a closure moves its non-copy captures: a fold of writes of the constant `moved`. -/
theorem fixMoves_rinv (g : SState → Nat → SState)
    (hg : ∀ s i, g s i = s ∨ ∃ pos, g s i = s.setAt pos fun _ => .moved) :
    ∀ (vs : List Nat) {s : SState}, RInv L s → RInv L (vs.foldl g s)
  | [], _, hi => hi
  | v :: vs, s, hi => by
    simp only [List.foldl_cons]
    apply fixMoves_rinv g hg vs
    rcases hg s v with e | ⟨pos, e⟩
    · rw [e]; exact hi
    · rw [e]; exact setAt_rinv hi pos _ (FT.const _ _) (fun _ _ => FT.const _ _)

/-- **An assignment's middle**: the borrow the target root held ends (at a root), then the content
is written. The target stays a position; at a root, its meaning is then the constant written, and
a label it still records (another holder was found first) is read by no one. -/
theorem assign_mid {s₂ s₄ : SState} (hi₂ : RInv L s₂) {pos : Pos} (hpos₂ : pos ∈ s₂.positions)
    (hp : ¬ IsTemp pos) {lab : Option Nat} (hy₂ : LoU s₂ lab) {steps : List Step} {v : Sem}
    (h3 : setContent K φ pos steps v (if steps.isEmpty = true then
        (match s₂.shape pos with | some l => s₂.endLabel l | none => s₂) else s₂) = some (⟨⟩, s₄)) :
    RInv L s₄ ∧ EnvLe s₂ s₄ ∧ OrdKeep L s₂ s₄ ∧ pos ∈ s₄.positions ∧ LoU s₄ lab ∧
      (steps = [] → (∀ ψ ψ', s₄.valAt pos ψ = s₄.valAt pos ψ') ∧
        ∀ x, s₄.shape pos = some x → ∀ q, Indep x (s₄.valAt q)) := by
  have gen : ∀ s₃ : SState, RInv L s₃ → EnvLe s₂ s₃ → OrdKeep L s₂ s₃ → pos ∈ s₃.positions → LoU s₃ lab →
      setContent K φ pos steps v s₃ = some (⟨⟩, s₄) →
      RInv L s₄ ∧ EnvLe s₂ s₄ ∧ OrdKeep L s₂ s₄ ∧ pos ∈ s₄.positions ∧ LoU s₄ lab ∧ s₄.shape = s₃.shape ∧
        (∀ q, q ≠ pos → s₄.valAt q = s₃.valAt q) ∧ (steps = [] → ∀ ψ, s₄.valAt pos ψ = v) := by
    intro s₃ hi₃ e₃ o₃ hpos₃ hy₃ h3
    obtain ⟨hi₄, hsh, hps⟩ := setContent_rinv K φ L h3 hi₃
    have e := setContent_eq K φ h3
    refine ⟨hi₄, e₃.trans (setContent_envLe K φ h3), o₃.trans e₃ (setContent_ordKeep K φ hp h3),
      by rw [hps]; exact hpos₃, fun y hy => ?_, hsh,
      fun q hq => by rw [e]; exact valAt_setAt_ne _ _ _ _ (fun e' => hq e'.symm), fun hnil ψ => ?_⟩
    · rw [e]
      exact lou_setAt (hy₃ y hy) pos _ fun hu ψ c => by
        show (Sem.updAt K.dm K.Γ (s₃.tyAt pos).m (fun _ => v) steps (s₃.valAt pos (ψ.upd y c))).getD .err
          = (Sem.updAt K.dm K.Γ (s₃.tyAt pos).m (fun _ => v) steps (s₃.valAt pos ψ)).getD .err
        rw [hu pos ψ c]
    · subst hnil
      rw [e, valAt_setAt_self _ _ _ hpos₃]; rfl
  by_cases hst : steps.isEmpty = true
  · rw [if_pos hst] at h3
    cases hsh : s₂.shape pos with
    | none =>
      rw [hsh] at h3
      dsimp only at h3
      obtain ⟨hi₄, e₄, o₄, hpos₄, hy₄, hsh₄, _, hc₄⟩ := gen s₂ hi₂ (EnvLe.refl _) (OrdKeep.refl _) hpos₂ hy₂ h3
      refine ⟨hi₄, e₄, o₄, hpos₄, hy₄, fun hn => ⟨fun ψ ψ' => by rw [hc₄ hn, hc₄ hn], fun x hx => ?_⟩⟩
      rw [hsh₄, hsh] at hx; cases hx
    | some l₀ =>
      rw [hsh] at h3
      dsimp only at h3
      obtain ⟨r', hr'⟩ := holderOf_of_live (live_of_shape hpos₂ hsh)
      obtain ⟨hr'pos, hr'sh⟩ := holderOf_spec hr'
      obtain ⟨hi₄, e₄, o₄, hpos₄, hy₄, hsh₄, hval₄, hc₄⟩ := gen (s₂.endLabel l₀) (endLabel_rinv hi₂ l₀)
        (envLe_endLabel _ _) (ordKeep_endLabel hi₂.2.1 l₀) (by rw [endLabel_positions]; exact hpos₂)
        (fun y hy => lou_endLabel L hi₂.2.1 (hy₂ y hy) l₀) h3
      refine ⟨hi₄, e₄, o₄, hpos₄, hy₄, fun hn => ⟨fun ψ ψ' => by rw [hc₄ hn, hc₄ hn], fun x hx q => ?_⟩⟩
      rw [hsh₄, endLabel_eq hr', endAt_shape] at hx
      simp only at hx
      split at hx
      · cases hx
      · rw [hsh] at hx; cases hx
        by_cases hq : q = pos
        · rw [hq]; intro ψ c; rw [hc₄ hn, hc₄ hn]
        · rw [hval₄ q hq, endLabel_eq hr']; exact endAt_indep hi₂.2.1 hr'pos hr'sh q
  · rw [if_neg hst] at h3
    obtain ⟨hi₄, e₄, o₄, hpos₄, hy₄, -, -, -⟩ := gen s₂ hi₂ (EnvLe.refl _) (OrdKeep.refl _) hpos₂ hy₂ h3
    exact ⟨hi₄, e₄, o₄, hpos₄, hy₄, fun hn => absurd (by rw [hn]; rfl) hst⟩

/-- [Access] keeps a label live or unread (`lou_access`): for the right-hand side's label across the
access an assignment makes after it (the run evaluates the right-hand side first, D19 R5). -/
theorem contentOf_lou {p : Place} {s s' : SState} {x : Sem × TyS × Pos × List Step}
    (h : contentOf K φ p s = some (x, s')) (hi : RInv L s) {lab : Option Nat} (hy : LoU s lab) : LoU s' lab := by
  unfold contentOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun l hl => lou_access L hi (hy l hl) pos
    · cases h

mutual
/-- **Part (P)**: the run keeps `RInv L`, its result's label is live or unread, and it keeps the
frames' bindings, only adding temporaries (`EnvLe`). -/
theorem run_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (t : Term) (hint : TyS) (s s' : SState) (r : Res), RInv L s →
    run K ρ φ hint t s = some (r, s') → RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | .place p, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    exact ⟨(readPlace_rinv K φ L h hi).1, (readPlace_rinv K φ L h hi).2, readPlace_envLe K φ h,
      readPlace_ordKeep K φ h hi⟩
  | .borrow p, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    exact ⟨(borrowPlace_rinv K φ L h hi).1, (borrowPlace_rinv K φ L h hi).2, borrowPlace_envLe K φ h,
      borrowPlace_ordKeep K φ h hi⟩
  | .val v, hint, s, s', r, hi, h => by
    obtain ⟨T, e, hT⟩ := run_val_eq K ρ φ hint v s
    rw [e] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rinv_pure L hi hT
  | .const n, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi (hK n)
  | .sort l, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .nat, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .unit, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .zero, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .tt, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .cong f g, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | .seq u w, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK u _ s s₁ x hi h1
    obtain ⟨hi₂, hy₂, e₂, o₂⟩ := run_rinv hK w hint s₁ s' r hi₁ h2
    exact ⟨hi₂, hy₂, e₁.trans e₂, o₁.trans e₁ o₂⟩
  | .succ u, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
    obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK u _ s _ x hi h1
    exact rinv_ret L hi₁ e₁ o₁ rfl
  | .ref A, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
    obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK A _ s _ x hi h1
    exact rinv_ret L hi₁ e₁ o₁ rfl
  | .eq A a b, hint, s, s', r, hi, h => by
    rw [run] at h
    have e := SM.onCopy_state h
    subst e
    obtain ⟨s₁, h1⟩ := SM.onCopy_result h
    obtain ⟨x, s₂, _, h2⟩ := SM.bind_some h1
    obtain ⟨y, s₃, _, h3⟩ := SM.bind_some h2
    obtain ⟨z, s₄, _, h4⟩ := SM.bind_some h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    exact rinv_pure L hi rfl
  | .id A t u, hint, s, s', r, hi, h => by
    rw [run] at h
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, h⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rinv_pure L hi rfl
  | .ascribe u A, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    have e := SM.onCopy_state h1
    subst e
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    exact run_rinv hK u _ _ _ y hi h3
  | .letIn x u w, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, T⟩, s₁⟩, h1, ⟨⟨r', R⟩, s₃⟩, h2, h3⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h3)
    obtain ⟨hi₁, hy₁, e₁, o₁⟩ := run_rinv hK u _ s s₁ (v, T) hi h1
    have hi₂ := pushBindShaped_rinv hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s₁) u } v rfl
      fun l hl => by
        rcases hy₁ l hl with ⟨h' | h', hn⟩
        · exact ⟨.inl h', hn⟩
        · exact ⟨.inr (.inr h'), hn⟩
    have o₂ := ordKeep_pushBindShaped hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s₁) u } hy₁
    obtain ⟨hi₃, hy₃, e₃, o₃⟩ := run_rinv hK w hint _ s₃ (r', R) hi₂ h2
    dsimp only
    refine ⟨(letDrop_rinv L hi₃ hy₃ _ ?_).1, (letDrop_rinv L hi₃ hy₃ _ ?_).2.1,
      e₁.trans (envLe_letDrop ((envPush_pushBindShaped _ _).trans_le e₃) _),
      o₁.trans e₁ (o₂.trans' (fun _ hq => mem_positions_pushBindShaped _ hq)
        (o₃.trans' (fun _ hq => e₃.mem hq) (letDrop_rinv L hi₃ hy₃ _ ?_).2.2))⟩
    all_goals (unfold dropped; cases s₃.env.getLast? <;> rfl)
  | .matchNat p z u, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, h⟩ := h
    obtain ⟨hi₁, _⟩ := contentOf_rinv K φ L h1 hi
    have e₁ := contentOf_envLe K φ h1
    have o₁ := (contentOf_ordKeep K φ hi h1).1
    split at h
    · dsimp only at h
      cases h2 : run K ρ φ hint z s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := run_rinv hK z hint _ s₂ (r', R) hi₁ h2
        exact ⟨joinDrop_rinv K φ L _ hi₂, fun y hl => joinDrop_lou K φ L _ hi₂ (hy₂ y hl),
          e₁.trans (e₂.trans (joinDrop_envLe K φ _ _)),
          o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ hi₂))⟩
    · dsimp only at h
      cases h2 : run K ρ φ hint u s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := run_rinv hK u hint _ s₂ (r', R) hi₁ h2
        exact ⟨joinDrop_rinv K φ L _ hi₂, fun y hl => joinDrop_lou K φ L _ hi₂ (hy₂ y hl),
          e₁.trans (e₂.trans (joinDrop_envLe K φ _ _)),
          o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ hi₂))⟩
    · cases h
  | .matchInd p n arms, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, h⟩ := h
    obtain ⟨hi₁, _⟩ := contentOf_rinv K φ L h1 hi
    have e₁ := contentOf_envLe K φ h1
    have o₁ := (contentOf_ordKeep K φ hi h1).1
    split at h
    · rename_i c _
      dsimp only at h
      cases h2 : runArm K ρ φ hint c arms s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runArm_rinv hK arms hint _ _ s₂ (r', R) hi₁ h2
        exact ⟨joinDrop_rinv K φ L _ hi₂, fun y hl => joinDrop_lou K φ L _ hi₂ (hy₂ y hl),
          e₁.trans (e₂.trans (joinDrop_envLe K φ _ _)),
          o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ hi₂))⟩
    · cases h
  | .call f args hd, hint, s, s', r, hi, h => by
    rw [run] at h
    dsimp only at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨fv, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨as, s₂, h3, h4⟩ := SM.bind_some h2
    have hf : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.headOf_some h1 with ⟨p, h1⟩ | h1
      · exact ⟨(readPlace_rinv K φ L h1 hi).1, readPlace_envLe K φ h1, readPlace_ordKeep K φ h1 hi⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK f _ s s₁ fv hi h1
        exact ⟨hi₁, e₁, o₁⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hf
    obtain ⟨hi₂, e₂, o₂⟩ := runArgs_rinv hK _ _ args 0 [] s₁ s₂ as hi₁ h3
    split at h4
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
      refine rinv_ret L hi₂ (e₁.trans e₂) (o₁.trans e₁ o₂) ?_
      dsimp only
      split
      · split <;> rfl
      · rfl
    · unfold callOf at h4
      split at h4
      · split at h4
        · exact ⟨(callOfL_rinv L _ _ _ _ _ hi₂ h4).1, (callOfL_rinv L _ _ _ _ _ hi₂ h4).2,
            e₁.trans (e₂.trans (callOfL_envLe _ _ _ _ _ h4)),
            o₁.trans e₁ (o₂.trans e₂ (callOfL_ordKeep _ _ _ _ _ hi₂ h4))⟩
        · exact ⟨(callOfL_rinv L _ _ _ _ _ hi₂ h4).1, (callOfL_rinv L _ _ _ _ _ hi₂ h4).2,
            e₁.trans (e₂.trans (callOfL_envLe _ _ _ _ _ h4)),
            o₁.trans e₁ (o₂.trans e₂ (callOfL_ordKeep _ _ _ _ _ hi₂ h4))⟩
        · exact ⟨(callOfL_rinv L _ _ _ _ _ hi₂ h4).1, (callOfL_rinv L _ _ _ _ _ hi₂ h4).2,
            e₁.trans (e₂.trans (callOfL_envLe _ _ _ _ _ h4)),
            o₁.trans e₁ (o₂.trans e₂ (callOfL_ordKeep _ _ _ _ _ hi₂ h4))⟩
        · cases h4
      · cases h4
  | .pi hs ds c, hint, s, s', r, hi, h => by
    rw [run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact rinv_pure L hi rfl
  | .tind n args, hint, s, s', r, hi, h => by
    rw [run] at h
    cases hd : K.Γ.find? (·.name == n) with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      obtain ⟨ps, s₁, h1, h2⟩ := SM.bind_some h
      have e := runParams_state K ρ φ d args 0 [] s s₁ ps h1
      subst e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
      exact rinv_pure L hi rfl
  | .ctor ty c hh ps args, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      obtain ⟨psM, s₁, h1, h2⟩ := SM.bind_some h
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      have cont : ∀ ps' : List Sem, (if d.sort == 0 then
            (do let _ ← runFields K ρ φ true d ps' c 0 [] args
                pure ((.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))
          else
            (do let fs ← runFields K ρ φ false d ps' c 0 [] args
                pure ((K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))) s₁
            = some (r, s') → RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s₁ s' ∧ OrdKeep L s₁ s' := by
        intro ps' h2
        by_cases hs0 : (d.sort == 0) = true
        · rw [if_pos hs0] at h2
          obtain ⟨fs, s₂, h3, h4⟩ := SM.bind_some h2
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
          obtain ⟨hi₂, e₂, o₂⟩ := runFields_rinv hK _ d _ c args 0 [] _ _ fs hi h3
          exact rinv_ret L hi₂ e₂ o₂ rfl
        · rw [if_neg hs0] at h2
          obtain ⟨fs, s₂, h3, h4⟩ := SM.bind_some h2
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
          obtain ⟨hi₂, e₂, o₂⟩ := runFields_rinv hK _ d _ c args 0 [] _ _ fs hi h3
          exact rinv_ret L hi₂ e₂ o₂ rfl
      by_cases hc : (ps.isEmpty && !d.params.isEmpty) = true
      · rw [if_pos hc] at h2
        cases hdata : hint.data with
        | none => rw [hdata] at h2; cases h2
        | some np =>
          obtain ⟨n', ps''⟩ := np
          rw [hdata] at h2
          dsimp only at h2
          by_cases hn : n' = ty
          · rw [if_pos hn] at h2; exact cont ps'' h2
          · rw [if_neg hn] at h2; cases h2
      · rw [if_neg hc] at h2
        exact cont psM h2
  | .fix self hs ds c dec body, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨?_, (fun l hl => by cases hl), ?_, ?_⟩
    · apply fixMoves_rinv L _ _ _ hi
      intro s i
      split
      · exact .inl rfl
      · split
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
    · apply envLe_foldl _ _ _ s
      intro s i
      split
      · exact EnvLe.refl s
      · split
        · exact envLe_setAt _ _ _
        · exact EnvLe.refl s
    · apply ordKeep_foldl_moves _ _ _ s
      intro s i
      split
      · exact .inl rfl
      · split
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
  | .prim n args, hint, s, s', r, hi, h => by
    rcases run_prim_cases K ρ φ h with ⟨rfl, hl⟩ | ⟨t, ht, h'⟩ | ⟨p, h'⟩
    · exact rinv_pure L hi hl
    · exact runAll_rinv hK args t ht hint s s' r hi h'
    · exact ⟨(readPlace_rinv K φ L h' hi).1, (readPlace_rinv K φ L h' hi).2, readPlace_envLe K φ h',
        readPlace_ordKeep K φ h' hi⟩
  | .assign p u, hint, s, s', r, hi, h => by
    rw [run] at h
    rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, rfl, hl, -⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, R⟩, s₁⟩, h2, ⟨⟨w, T, pos, steps⟩, s₂⟩, h1, ⟨⟨⟩, s₄⟩, h3, h4⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h4)
    dsimp only at h1 h2 h3 ⊢
    -- the right-hand side runs first, then the place is accessed
    obtain ⟨hi₁, hy₁, e₁, o₁⟩ := run_rinv hK u _ s s₁ (v, R) hi h2
    obtain ⟨hi₂, hpos₂⟩ := contentOf_rinv K φ L h1 hi₁
    have e₂ := contentOf_envLe K φ h1
    obtain ⟨o₂, hpb⟩ := contentOf_ordKeep K φ hi₁ h1
    have hy₂ : LoU s₂ R.label := contentOf_lou K φ L h1 hi₁ hy₁
    obtain ⟨hi₄, e₄, o₄, hpos₄, hy₄, hroot⟩ := assign_mid K φ L hi₂ hpos₂ hpb hy₂ h3
    split
    · rename_i _ _ l hR
      obtain ⟨hc, hold⟩ := hroot rfl
      refine ⟨hold_rinv L hi₄ pos hpos₄ hc (hy₄ l hR) hold, (fun _ hl => by cases hl), ?_, ?_⟩
      · exact e₁.trans (e₂.trans (e₄.trans (envLe_hold _ _ _)))
      · exact o₁.trans e₁ (o₂.trans e₂ (o₄.trans e₄ (ordKeep_hold hpos₄ (hy₄ l hR) hold)))
    · exact ⟨hi₄, (fun _ hl => by cases hl), e₁.trans (e₂.trans e₄), o₁.trans e₁ (o₂.trans e₂ o₄)⟩

theorem runAll_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (ts : List Term) (t : Term), t ∈ ts →
    ∀ (hint : TyS) (s s' : SState) (r : Res), RInv L s → run K ρ φ hint t s = some (r, s') →
      RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], t, ht, _, _, _, _, _, _ => absurd ht List.not_mem_nil
  | a :: as, t, ht, hint, s, s', r, hi, h => by
    rw [List.mem_cons] at ht
    rcases ht with e | ht'
    · rw [e] at h; exact run_rinv hK a hint s s' r hi h
    · exact runAll_rinv hK as t ht' hint s s' r hi h

theorem runArgs_rinv (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (shape : Option (List PiParam × PiOut)) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s s' : SState) (rs : List Res), RInv L s →
      runArgs K ρ φ stmt shape i earlier args s = some (rs, s') → RInv L s' ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], i, earlier, s, s', rs, hi, h => by
    simp only [runArgs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | a :: as, i, earlier, s, s', rs, hi, h => by
    simp only [runArgs] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    -- a statement argument runs on its own copy: the state is as it was
    have hx : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK a _ s s₁ x hi h1
        exact ⟨hi₁, e₁, o₁⟩
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hx
    obtain ⟨hi₂, e₂, o₂⟩ := runArgs_rinv hK stmt shape as _ _ s₁ _ y hi₁ h3
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

theorem runFields_rinv (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s s' : SState) (fs : List Sem), RInv L s →
      runFields K ρ φ stmt d ps c i earlier args s = some (fs, s') → RInv L s' ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], i, earlier, s, s', fs, hi, h => by
    simp only [runFields] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | a :: as, i, earlier, s, s', fs, hi, h => by
    simp only [runFields] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hx : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := run_rinv hK a _ s s₁ x hi h1
        exact ⟨hi₁, e₁, o₁⟩
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hx
    obtain ⟨hi₂, e₂, o₂⟩ := runFields_rinv hK stmt d ps c as _ _ s₁ _ y hi₁ h3
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

theorem runArm_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (arms : List (Hint × Term)) (hint : TyS) (c : Nat)
    (s s' : SState) (r : Res), RInv L s → runArm K ρ φ hint c arms s = some (r, s') →
      RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], hint, c, s, s', r, hi, h => by
    simp only [runArm, SM.fail] at h; cases h
  | (_, t) :: rest, hint, c, s, s', r, hi, h => by
    simp only [runArm] at h
    split at h
    · exact run_rinv hK t hint s s' r hi h
    · exact runArm_rinv hK rest hint (c - 1) s s' r hi h
end

end

end Ochr.Meaning
