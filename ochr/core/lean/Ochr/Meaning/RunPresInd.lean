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

theorem run_val_eq (hint : TyS) (v : Value) (s : SState) {tl : Bool} :
    ∃ T : TyS, runT K ρ φ tl hint (.val v) s = strictVal K.dm.read v (meanV K ρ φ hint v, T) s ∧ T.label = none := by
  cases v <;> exact ⟨_, rfl, rfl⟩

/-- A strict `.val`'s run: the value and the state unchanged, or a failure. -/
theorem strictVal_some {R : DataRead} {v : Value} {x r : Res} {s s' : SState} (h : strictVal R v x s = some (r, s')) :
    r = x ∧ s' = s := by
  cases v
  case ind =>
    unfold strictVal SM.strictS at h
    simp only [pure] at h
    split at h
    · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
  case clo =>
    simp only [strictVal] at h
    by_cases he : x.1 = Sem.err
    · rw [if_pos he] at h; cases h
    · rw [if_neg he] at h; cases h; exact ⟨rfl, rfl⟩
  case sealed =>
    simp only [strictVal] at h
    by_cases he : x.1 = Sem.err
    · rw [if_pos he] at h; cases h
    · rw [if_neg he] at h; cases h; exact ⟨rfl, rfl⟩
  all_goals (simp only [strictVal, pure, Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩)

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

/-- The [Drop] of a discarded value keeps the invariant, the environment's order and the
temporaries' order. -/
theorem discardEnd_props {s : SState} (hi : RInv L s) (R : TyS) :
    RInv L (discardEnd R s) ∧ EnvLe s (discardEnd R s) ∧ OrdKeep L s (discardEnd R s) := by
  unfold discardEnd
  split
  · exact ⟨endLabel_rinv hi _, envLe_endLabel _ _, ordKeep_endLabel hi.2.1 _⟩
  · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩

theorem SM.modify_some {f : SState → SState} {s : SState} {r : PUnit × SState} (h : SM.modify f s = some r) :
    r.2 = f s := by
  cases h; rfl

theorem rinv_pure {s : SState} (hi : RInv L s) {r : Res} (hl : r.2.label = none) :
    RInv L s ∧ LoU s r.2.label ∧ EnvLe s s ∧ OrdKeep L s s :=
  rinv_ret L hi (EnvLe.refl s) (OrdKeep.refl s) hl

theorem SM.strictS_some {R : DataRead} {x : SM Res} {s s' : SState} {r : Res}
    (h : SM.strictS R x s = some (r, s')) : x s = some (r, s') ∧ r.1 ∈ₛ[R] r.2.m := by
  unfold SM.strictS at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p =>
    rw [hx] at h
    obtain ⟨r0, s0⟩ := p
    simp only at h
    by_cases hm : r0.1 ∈ₛ[R] r0.2.m
    · rw [if_pos hm] at h; cases h; exact ⟨rfl, hm⟩
    · rw [if_neg hm] at h; cases h

theorem ite_none_some {α : Type _} {p : Prop} [Decidable p] {a : Option α} {b : α}
    (h : (if p then a else none) = some b) : p ∧ a = some b := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact ⟨hp, h⟩
  · rw [if_neg hp] at h; cases h

theorem foldr_premises_label : ∀ (xs : List Term) {s s₁ : SState} {r : Res},
    (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
      (pure (.proof, .plain (TyM.prop True)))) s = some (r, s₁) → r.2.label = none
  | [], _, _, _, h => by obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); rfl
  | _ :: ts, _, _, _, h => by
    obtain ⟨_, s₂, -, h2⟩ := SM.bind_some h
    exact foldr_premises_label ts h2

/-- The four equality rules' run (premises on a copy, `⋆` at `prop True`): the state unchanged, the
result label-free. -/
theorem premises_some (xs : List Term) {s s' : SState} {r : Res}
    (h : (SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
      (pure (.proof, .plain (TyM.prop True))))) s = some (r, s')) : s' = s ∧ r.2.label = none := by
  refine ⟨SM.onCopy_state h, ?_⟩
  obtain ⟨s₁, h1⟩ := SM.onCopy_result h
  exact foldr_premises_label K ρ φ xs h1

/-- A primitive's run: a proof (no state change, no label), one of its arguments' runs (`J`,
`clone`/`peek` of a non-place, `inplace`, `split f in u` at the form's tail flag: docs/31 D175), or a copying read. -/
theorem run_prim_cases (K : RunCtx) (ρ : Assignment) (φ : Future) {tl : Bool} {hint : TyS} {n : String} {args : List Term}
    {s s' : SState} {r : Res} (h : runT K ρ φ tl hint (.prim n args) s = some (r, s')) :
    (s' = s ∧ r.2.label = none) ∨
    (∃ t tl', t ∈ args ∧ runT K ρ φ tl' hint t s = some (r, s')) ∨
    (∃ p, readPlace K φ p true s = some (r, s')) ∨
    -- `J`: its transported term's entry, its run (at the hint `P(a)`, main's D124), its join
    (∃ t hJ s₂, t ∈ args ∧ run K ρ φ hJ t (matchEntry K φ true t s).1 = some (r, s₂) ∧
      s' = joinDrop K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim n args) s₂) := by
  have prem : ∀ (xs : List Term), (SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
      (pure (.proof, .plain (TyM.prop True))))) s = some (r, s') → s' = s ∧ r.2.label = none :=
    fun xs h => premises_some K ρ φ xs h
  by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
  · obtain ⟨h0, rfl, rfl⟩ := e1; rw [runT] at h; exact .inl (prem [h0] h)
  by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
  · obtain ⟨h0, k0, rfl, rfl⟩ := e2; rw [runT] at h; exact .inl (prem [h0, k0] h)
  by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
  · obtain ⟨h0, u0, rfl, rfl⟩ := e3; rw [runT] at h; exact .inl (prem [h0, u0] h)
  by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
  · obtain ⟨h0, u0, rfl, rfl⟩ := e4; rw [runT] at h; exact .inl (prem [h0, u0] h)
  have fail : ∀ (hJ : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False)
      (hc : ∀ u, n = "clone" → args = [u] → False) (hp : ∀ u, n = "peek" → args = [u] → False)
      (hi : ∀ u, n = "inplace" → args = [u] → False) (hs : ∀ f u, n = "split" → args = [.const f, u] → False),
      False := by
    intro hJ hc hp hi hs
    rw [runT] at h
    · cases h
    · exact fun h0 a b => e1 ⟨h0, a, b⟩
    · exact fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
    · exact fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
    · exact fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
    · exact hJ
    · exact hc
    · exact hp
    · exact hi
    · exact hs
  by_cases hsp : ∃ f u, n = "split" ∧ args = [.const f, u]
  · obtain ⟨f, u, rfl, rfl⟩ := hsp
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    · exact .inr (.inl ⟨u, tl, by simp, h⟩)
    · exact .inl ⟨rfl, hl⟩
  by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
  · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact .inl ⟨rfl, hl⟩
    obtain ⟨_, s₁, e1, h⟩ := SM.bind_some h
    obtain ⟨_, s₂, e2, h⟩ := SM.bind_some h
    obtain ⟨_, s₃, e3, h⟩ := SM.bind_some h
    obtain ⟨_, s₄, e4, h⟩ := SM.bind_some h
    obtain ⟨_, s₅, e5, h⟩ := SM.bind_some h
    obtain ⟨_, s₆, e6, h⟩ := SM.bind_some h
    rw [SM.onCopy_state e1] at e2; rw [SM.onCopy_state e2] at e3; rw [SM.onCopy_state e3] at e4
    rw [SM.onCopy_state e4] at e5; rw [SM.onCopy_state e5] at e6; rw [SM.onCopy_state e6] at h
    dsimp only at h
    split at h
    · split at h
      · rename_i r₁ R₁ s₂ h2
        split at h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact .inr (.inr (.inr ⟨t, _, s₂, by simp, h2, rfl⟩))
        · cases h
      · cases h
    · cases h
  by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
  · obtain ⟨u, hn, rfl⟩ := hc
    have key : ∀ b : Bool × Bool, SM.erasedIf b (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (run K ρ φ hint u)) s = some (r, s') →
        (s' = s ∧ r.2.label = none) ∨ (∃ t tl', t ∈ [u] ∧ runT K ρ φ tl' hint t s = some (r, s')) ∨
        (∃ p, readPlace K φ p true s = some (r, s')) := by
      intro b h
      rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
      · rcases SM.headOf_some h with ⟨p, h⟩ | h
        · exact .inr (.inr ⟨p, (SM.guarded_some h).2⟩)
        · exact .inr (.inl ⟨u, false, by simp, h⟩)
      · exact .inl ⟨rfl, hl⟩
    have key' : ∀ b : Bool × Bool, SM.erasedIf b (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (run K ρ φ hint u)) s = some (r, s') →
        (s' = s ∧ r.2.label = none) ∨ (∃ t tl', t ∈ [u] ∧ runT K ρ φ tl' hint t s = some (r, s')) ∨
        (∃ p, readPlace K φ p true s = some (r, s')) ∨
        (∃ t hJ s₂, t ∈ [u] ∧ run K ρ φ hJ t (matchEntry K φ true t s).1 = some (r, s₂) ∧
          s' = joinDrop K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim n [u]) s₂) :=
      fun b h => (key b h).imp_right (Or.imp_right Or.inl)
    rcases hn with rfl | rfl | rfl <;> (rw [runT] at h; exact key' _ h)
  exfalso
  exact fail (fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩)
    (fun u e1 e2 => hc ⟨u, .inl e1, e2⟩) (fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩)
    (fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩) (fun f u e1 e2 => hsp ⟨f, u, e1, e2⟩)

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
theorem dropped_foldl_endLabel : ∀ (ls : List Nat) (s : SState), (ls.foldl endLabel s).dropped = s.dropped
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, dropped_foldl_endLabel ls, dropped_endLabel]

theorem dropped_access (s : SState) (p : Pos) (hit : List Step → Bool) : (s.access p hit).dropped = s.dropped := by
  rw [access_eq, foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => rfl
  | succ k ih => exact (dropped_foldl_endLabel _ _).trans ih

/-- The D65 ends at a `let`'s drop keep the invariant, results' labels live or unread, the
temporaries' order and the frames; they end only (the position dropped and the holders stay). -/
theorem letLenders_props {s : SState} (hi : RInv L s) :
    RInv L (letLenders s) ∧ (∀ lab, LoU s lab → LoU (letLenders s) lab) ∧ OrdKeep L s (letLenders s) ∧
      EnvLe s (letLenders s) ∧ (letLenders s).dropped = s.dropped ∧
      ∀ p x, (letLenders s).shape p = some x → s.shape p = some x := by
  unfold letLenders
  split
  · exact ⟨access_rinv hi _ _, fun lab hy y hl => lou_access L hi (hy y hl) _ _, ordKeep_access hi _ _,
      envLe_access _ _ _, dropped_access _ _ _, fun p x h => (SState.shapeSub_access s _ _).1 p x h⟩
  · exact ⟨hi, fun _ h => h, OrdKeep.refl s, EnvLe.refl s, rfl, fun _ _ h => h⟩

theorem letDrop_rinv {s : SState} (hi : RInv L s) {lab : Option Nat} (hy : LoU s lab) (held : Option Nat)
    (hheld : held = match s.dropped with | some r => s.shape r | none => none) :
    RInv L (match held with | some l => s.endLabel l | none => letLenders s).dropLast ∧
    LoU (match held with | some l => s.endLabel l | none => letLenders s).dropLast lab ∧
    OrdKeep L s (match held with | some l => s.endLabel l | none => letLenders s).dropLast := by
  have hind : ∀ r x, (match held with | some l => s.endLabel l | none => letLenders s).dropped = some r →
      (match held with | some l => s.endLabel l | none => letLenders s).shape r = some x →
      ∀ p, Indep x ((match held with | some l => s.endLabel l | none => letLenders s).valAt p) := by
    intro r x hr hx
    cases held with
    | none =>
      simp only at hr hx ⊢
      rw [(letLenders_props L hi).2.2.2.2.1] at hr
      rw [hr] at hheld; simp only at hheld
      rw [(letLenders_props L hi).2.2.2.2.2 r x hx] at hheld; cases hheld
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
  have hi₄ : RInv L (match held with | some l => s.endLabel l | none => letLenders s) := by
    cases held with
    | none => exact (letLenders_props L hi).1
    | some l => exact endLabel_rinv hi l
  have hy₄ : LoU (match held with | some l => s.endLabel l | none => letLenders s) lab := by
    intro y hl
    cases held with
    | none => exact (letLenders_props L hi).2.1 lab hy y hl
    | some l => exact lou_endLabel L hi.2.1 (hy y hl) l
  have ho₄ : OrdKeep L s (match held with | some l => s.endLabel l | none => letLenders s) ∧
      EnvLe s (match held with | some l => s.endLabel l | none => letLenders s) := by
    cases held with
    | none => exact ⟨(letLenders_props L hi).2.2.1, (letLenders_props L hi).2.2.2.1⟩
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

/-- Forming a closure accesses each capture and moves the non-copy ones: a fold of accesses, each
maybe followed by a write of the constant `moved` at the accessed position. -/
theorem capMoves_props (g : SState → Nat → SState)
    (hg : ∀ s i, g s i = s ∨ ∃ pos, g s i = s.access pos (dataHit []) ∨
      g s i = (s.access pos (dataHit [])).setAt pos fun _ => .moved) :
    ∀ (vs : List Nat) {s : SState}, RInv L s →
      RInv L (vs.foldl g s) ∧ EnvLe s (vs.foldl g s) ∧ OrdKeep L s (vs.foldl g s)
  | [], s, hi => ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | v :: vs, s, hi => by
    simp only [List.foldl_cons]
    have h1 : RInv L (g s v) ∧ EnvLe s (g s v) ∧ OrdKeep L s (g s v) := by
      rcases hg s v with e | ⟨pos, e | e⟩ <;> rw [e]
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
      · exact ⟨access_rinv hi pos _, envLe_access _ _ _, ordKeep_access hi pos _⟩
      · have ha := access_rinv hi pos (dataHit [])
        exact ⟨setAt_rinv ha pos _ (FT.const _ _) (fun _ _ => FT.const _ _),
          (envLe_access _ _ _).trans (envLe_setAt _ _ _),
          (ordKeep_access hi pos _).trans (envLe_access _ _ _) (ordKeep_setAt_const pos _)⟩
    obtain ⟨hi₁, e₁, o₁⟩ := h1
    obtain ⟨hi₂, e₂, o₂⟩ := capMoves_props g hg vs hi₁
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

/-- **An assignment's middle**: the borrow the target root held ends (at a root), then the content
is written. The target stays a position; at a root, its meaning is then the constant written, and
a label it still records (another holder was found first) is read by no one. -/
theorem assign_mid {s₂ s₄ : SState} (hi₂ : RInv L s₂) {pos : Pos} (hpos₂ : pos ∈ s₂.positions)
    (hp : IsTop s₂ pos) {lab : Option Nat} (hy₂ : LoU s₂ lab) {steps : List Step} {v : Sem}
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
    refine ⟨hi₄, e₃.trans (setContent_envLe K φ h3), o₃.trans e₃ (setContent_ordKeep K φ (hp.envLe e₃).notCell h3),
      by rw [hps]; exact hpos₃, fun y hy => ?_, hsh,
      fun q hq => by rw [e]; exact valAt_setAt_ne _ _ _ _ (fun e' => hq e'.symm), fun hnil ψ => ?_⟩
    · rw [e]
      exact lou_setAt (hy₃ y hy) pos _ fun hu ψ c => by
        show (Sem.updAt K.dm K.Γ (s₃.tyAt pos) (fun _ => v) steps (s₃.valAt pos (ψ.upd y c))).getD .err
          = (Sem.updAt K.dm K.Γ (s₃.tyAt pos) (fun _ => v) steps (s₃.valAt pos ψ)).getD .err
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
      exact fun l hl => lou_access L hi (hy l hl) pos _
    · cases h

/-- A match's [Access] for the tag: the state after is the accessed one. -/
theorem tagOf_some {p : Place} {tag : Sem → TyS → Sem} {s s' : SState} {tg : Sem}
    (h : tagOf K φ p tag s = some (tg, s')) :
    ∃ pos steps, resolve s p = some (pos, steps) ∧ s' = s.access pos (tagHit steps) := by
  unfold tagOf at h
  cases hr : resolve s p with
  | none => rw [hr] at h; cases h
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨pos, steps, rfl, h.2.symm⟩

theorem tagOf_rinv {p : Place} {tag : Sem → TyS → Sem} {s s' : SState} {tg : Sem}
    (h : tagOf K φ p tag s = some (tg, s')) (hi : RInv L s) : RInv L s' ∧ EnvLe s s' ∧ OrdKeep L s s' := by
  obtain ⟨pos, steps, -, rfl⟩ := tagOf_some K φ h
  exact ⟨access_rinv hi pos _, envLe_access s pos _, ordKeep_access hi pos _⟩

/-- A fold whose every step is nothing or an access keeps the invariant. -/
theorem foldAccess_props {α : Type} (g : SState → α → SState)
    (hg : ∀ s a, g s a = s ∨ ∃ pos hit, g s a = s.access pos hit) :
    ∀ (xs : List α) {s : SState}, RInv L s →
      RInv L (xs.foldl g s) ∧ EnvLe s (xs.foldl g s) ∧ OrdKeep L s (xs.foldl g s)
  | [], s, hi => ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | x :: xs, s, hi => by
    simp only [List.foldl_cons]
    have h1 : RInv L (g s x) ∧ EnvLe s (g s x) ∧ OrdKeep L s (g s x) := by
      rcases hg s x with e | ⟨pos, hit, e⟩ <;> rw [e]
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
      · exact ⟨access_rinv hi pos _, envLe_access _ _ _, ordKeep_access hi pos _⟩
    obtain ⟨hi₁, e₁, o₁⟩ := h1
    obtain ⟨hi₂, e₂, o₂⟩ := foldAccess_props g hg xs hi₁
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

/-- D112's invalidation keeps the invariant: each step an access and a write of `⊥`. -/
theorem invalidateOne_props (q : Place) {s : SState} (hi : RInv L s) :
    RInv L (invalidateOne K φ s q) ∧ EnvLe s (invalidateOne K φ s q) ∧ OrdKeep L s (invalidateOne K φ s q) := by
  unfold invalidateOne
  split
  · rename_i pos steps hr
    have hia := access_rinv hi pos (dataHit steps)
    have hea := envLe_access s pos (dataHit steps)
    have hoa := ordKeep_access hi pos (dataHit steps)
    have hpb : IsTop (s.access pos (dataHit steps)) pos := (resolve_top hr).envLe hea
    dsimp only
    split
    · rename_i u s'' hs
      obtain ⟨hi₂, -, -⟩ := setContent_rinv K φ L hs hia
      exact ⟨hi₂, hea.trans (setContent_envLe K φ hs), hoa.trans hea (setContent_ordKeep K φ hpb.notCell hs)⟩
    · exact ⟨hia, hea, hoa⟩
  · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩

theorem invalidate_props (p : Place) {s : SState} (hi : RInv L s) :
    RInv L (invalidate K φ p s) ∧ EnvLe s (invalidate K φ p s) ∧ OrdKeep L s (invalidate K φ p s) := by
  unfold invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | cons q qs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hi₁, e₁, o₁⟩ := invalidateOne_props K φ L q hi
    obtain ⟨hi₂, e₂, o₂⟩ := ih hi₁
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

theorem lou_setContent {pos : Pos} {steps : List Step} {v : Sem} {s s' : SState}
    (h : setContent K φ pos steps v s = some (⟨⟩, s')) {y : Nat} (hy : LoU1 s y) : LoU1 s' y := by
  unfold setContent at h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact lou_setAt hy pos _ fun hu ψ x => by simp only [hu pos ψ x]
  · cases h

theorem lou_invalidateOne (q : Place) {s : SState} (hi : RInv L s) {y : Nat} (hy : LoU1 s y) :
    LoU1 (invalidateOne K φ s q) y := by
  unfold invalidateOne
  split
  · rename_i pos steps _
    have hya := lou_access L hi hy pos (dataHit steps)
    dsimp only
    split
    · rename_i u s'' hs
      exact lou_setContent K φ hs hya
    · exact hya
  · exact hy

theorem lou_invalidate (p : Place) {s : SState} (hi : RInv L s) {y : Nat} (hy : LoU1 s y) :
    LoU1 (invalidate K φ p s) y := by
  unfold invalidate
  generalize K.D.invalidated (scopeOf s) p = qs
  induction qs generalizing s with
  | nil => exact hy
  | cons q qs ih =>
    simp only [List.foldl_cons]
    exact ih (invalidateOne_props K φ L q hi).1 (lou_invalidateOne K φ L q hi hy)

/-- [Assign]'s write keeps the invariant (the `.assign` clause's tail before D112's invalidation). -/
theorem assignAt_rinv {p : Place} {v : Sem} {lab : Option Nat} {s₁ s' : SState} {r : Res}
    (h : assignAt K φ p v lab s₁ = some (r, s')) (hi₁ : RInv L s₁) (hy₁ : LoU s₁ lab) :
    RInv L s' ∧ r.2.label = none ∧ EnvLe s₁ s' ∧ OrdKeep L s₁ s' := by
    unfold assignAt at h
    cases hr : resolve s₁ p with
    | none => rw [hr] at h; cases h
    | some ps =>
    obtain ⟨pos, steps⟩ := ps
    rw [hr] at h
    dsimp only at h
    have mid : ∀ s₂ : SState, s₂ = s₁ ∨ s₂ = s₁.access pos (dataHit steps) →
        RInv L s₂ ∧ pos ∈ s₂.positions ∧ EnvLe s₁ s₂ ∧ OrdKeep L s₁ s₂ ∧ LoU s₂ lab := by
      rintro s₂ (rfl | rfl)
      · exact ⟨hi₁, resolve_mem hr, EnvLe.refl _, OrdKeep.refl _, hy₁⟩
      · exact ⟨access_rinv hi₁ pos _, by rw [access_positions]; exact resolve_mem hr, envLe_access _ _ _,
          ordKeep_access hi₁ pos _, fun l hl => lou_access L hi₁ (hy₁ l hl) pos _⟩
    generalize hs₂ : (if (steps.isEmpty && (s₁.shape pos).isSome) = true then s₁
      else s₁.access pos (dataHit steps)) = s₂ at h
    obtain ⟨hi₂, hpos₂, e₂, o₂, hy₂⟩ := mid s₂ (by rw [← hs₂]; split <;> simp)
    have hpb : IsTop s₂ pos := (resolve_top hr).envLe e₂
    split at h
    · cases h
    rename_i s₄ h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    dsimp only
    obtain ⟨hi₄, e₄, o₄, hpos₄, hy₄, hroot⟩ := assign_mid K φ L hi₂ hpos₂ hpb hy₂ h3
    split
    · rename_i l
      obtain ⟨hc, hold⟩ := hroot rfl
      refine ⟨hold_rinv L hi₄ pos hpos₄ hc (hy₄ l rfl) hold, rfl, ?_, ?_⟩
      · exact e₂.trans (e₄.trans (envLe_hold _ _ _))
      · exact o₂.trans e₂ (o₄.trans e₄ (ordKeep_hold hpos₄ (hy₄ l rfl) hold))
    · exact ⟨hi₄, rfl, e₂.trans e₄, o₂.trans e₂ o₄⟩

/-- A fold whose every step keeps the invariant. -/
theorem fold_props {α : Type} (g : SState → α → SState)
    (hg : ∀ s a, RInv L s → RInv L (g s a) ∧ EnvLe s (g s a) ∧ OrdKeep L s (g s a)) :
    ∀ (xs : List α) (s : SState), RInv L s → RInv L (xs.foldl g s) ∧ EnvLe s (xs.foldl g s) ∧ OrdKeep L s (xs.foldl g s)
  | [], s, hi => ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | x :: xs, s, hi => by
    simp only [List.foldl_cons]
    obtain ⟨hi₁, e₁, o₁⟩ := hg s x hi
    obtain ⟨hi₂, e₂, o₂⟩ := fold_props g hg xs _ hi₁
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

/-- One capture at a block's entry: its access, and D112's invalidation for a capture by `&`. -/
theorem entryCap_props (s : SState) (qk : Place × Nat) (hi : RInv L s) :
    RInv L (entryCap K φ s qk) ∧ EnvLe s (entryCap K φ s qk) ∧ OrdKeep L s (entryCap K φ s qk) := by
  have hacc : ∀ (o : Option (Pos × List Step)),
      RInv L (match o with | some (pos, steps) => s.access pos (dataHit steps) | none => s) ∧
      EnvLe s (match o with | some (pos, steps) => s.access pos (dataHit steps) | none => s) ∧
      OrdKeep L s (match o with | some (pos, steps) => s.access pos (dataHit steps) | none => s) := by
    intro o
    rcases o with _ | ⟨pos, steps⟩
    · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
    · exact ⟨access_rinv hi pos _, envLe_access _ _ _, ordKeep_access hi pos _⟩
  unfold entryCap
  dsimp only
  obtain ⟨hi₁, e₁, o₁⟩ := hacc (resolve s qk.1)
  split
  · obtain ⟨hi₂, e₂, o₂⟩ := invalidate_props K φ L qk.1 hi₁
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩
  · exact ⟨hi₁, e₁, o₁⟩

/-- [Entry]'s accesses keep the invariant. -/
theorem entryAccess_props (bc : List Place × List (Place × Nat)) {s : SState} (hi : RInv L s) :
    RInv L (entryAccess K φ bc s) ∧ EnvLe s (entryAccess K φ bc s) ∧ OrdKeep L s (entryAccess K φ bc s) := by
  unfold entryAccess
  obtain ⟨hi₁, e₁, o₁⟩ := foldAccess_props L entryReroot (fun s q => by
    unfold entryReroot
    split
    · rename_i pos steps _
      unfold accessLentPrefix
      split
      · exact .inr ⟨pos, _, rfl⟩
      · exact .inl rfl
    · exact .inl rfl) bc.1 hi
  obtain ⟨hi₂, e₂, o₂⟩ := fold_props L (entryCap K φ) (fun s qk hi => entryCap_props K φ L s qk hi) bc.2 _ hi₁
  exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

/-- **[Entry] at a match** keeps the invariant, and its lending only adds sites. -/
theorem matchEntry_props (ent : Bool) (mt : Term) {s : SState} (hi : RInv L s) :
    RInv L (matchEntry K φ ent mt s).1 ∧ EnvLe s (matchEntry K φ ent mt s).1 ∧
      OrdKeep L s (matchEntry K φ ent mt s).1 := by
  unfold matchEntry
  split
  · exact entryAccess_props K φ L _ hi
  · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩

theorem matchEntry_lend (ent : Bool) (mt : Term) (s : SState) (lab : Option Nat) (s₂ : SState) :
    (matchEntry K φ ent mt s).2 lab s₂ = s₂ ∨ ∃ k xs, (matchEntry K φ ent mt s).2 lab s₂ = s₂.setLent k xs := by
  unfold matchEntry
  split
  · dsimp only
    split
    · unfold entryLend
      split
      · split
        · exact .inr ⟨_, _, rfl⟩
        · exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- A lending that only adds sites keeps what the run's invariant says of a state. -/
theorem lend_post {s₀ s₂ : SState} {lab : Option Nat} (x : SState)
    (hx : x = s₂ ∨ ∃ k xs, x = s₂.setLent k xs)
    (h : RInv L s₂ ∧ (∀ y, lab = some y → LoU1 s₂ y) ∧ EnvLe s₀ s₂ ∧ OrdKeep L s₀ s₂) :
    RInv L x ∧ (∀ y, lab = some y → LoU1 x y) ∧ EnvLe s₀ x ∧ OrdKeep L s₀ x := by
  rcases hx with rfl | ⟨k, xs, rfl⟩
  · exact h
  · exact h

mutual
/-- **Part (P)**: the run keeps `RInv L`, its result's label is live or unread, and it keeps the
frames' bindings, only adding temporaries (`EnvLe`). -/
theorem runT_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (tl : Bool) (t : Term) (hint : TyS) (s s' : SState) (r : Res), RInv L s →
    runT K ρ φ tl hint t s = some (r, s') → RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | tl, .place p, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    have h := (SM.guarded_some h).2
    exact ⟨(readPlace_rinv K φ L h hi).1, (readPlace_rinv K φ L h hi).2, readPlace_envLe K φ h,
      readPlace_ordKeep K φ h hi⟩
  | tl, .borrow p, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    cases hb : SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
    | none => rw [hb] at h; cases h
    | some y =>
      obtain ⟨r₀, s₁⟩ := y
      rw [hb] at h
      dsimp only at h
      obtain ⟨-, h⟩ := open Classical in ite_none_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb' := (SM.guarded_some (SM.strictS_some hb).1).2
      obtain ⟨hi₁, hy₁⟩ := borrowPlace_rinv K φ L hb' hi
      obtain ⟨hi₂, e₂, o₂⟩ := invalidate_props K φ L p hi₁
      refine ⟨hi₂, fun l hl => ?_, (borrowPlace_envLe K φ hb').trans e₂,
        (borrowPlace_ordKeep K φ hb' hi).trans (borrowPlace_envLe K φ hb') o₂⟩
      exact lou_invalidate K φ L p hi₁ (hy₁ l hl)
  | tl, .val v, hint, s, s', r, hi, h => by
    obtain ⟨T, e, hT⟩ := run_val_eq K ρ φ hint v s
    rw [e] at h
    obtain ⟨rfl, rfl⟩ := strictVal_some h
    exact rinv_pure L hi hT
  | tl, .const n, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi (hK n)
  | tl, .sort l, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | tl, .nat, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | tl, .unit, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | tl, .zero, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | tl, .tt, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact rinv_pure L hi rfl
  | tl, .cong f g, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨rfl, hl⟩ := premises_some K ρ φ [g] h
    exact rinv_pure L hi hl
  | tl, .seq u w, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false u _ s s₁ x hi h1
    obtain ⟨u', s₂, h2a, h2⟩ := SM.bind_some h2
    have es : s₂ = discardEnd x.2 s₁ := (SM.guardMod_some h2a).2
    subst es
    obtain ⟨hi₁', e₁', o₁'⟩ := discardEnd_props L hi₁ x.2
    obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runT_rinv hK tl w (tailHint tl hint) _ s' r hi₁' h2
    exact ⟨hi₂, hy₂, e₁.trans (e₁'.trans e₂), o₁.trans e₁ (o₁'.trans e₁' o₂)⟩
  | tl, .succ u, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨⟨v, R⟩, s₁, h1, h2⟩ := SM.bind_some (SM.strictS_some h).1
    dsimp only at h2
    cases hl : R.label with
    | some _ => rw [hl] at h2; cases h2
    | none =>
      rw [hl] at h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
      obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false u _ s _ (v, R) hi h1
      exact rinv_ret L hi₁ e₁ o₁ rfl
  | tl, .ref A, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some (SM.strictS_some h).1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
    obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false A _ s _ x hi h1
    exact rinv_ret L hi₁ e₁ o₁ rfl
  | tl, .eq A a b, hint, s, s', r, hi, h => by
    rw [runT] at h
    have e := SM.onCopy_state h
    subst e
    obtain ⟨s₁, h1⟩ := SM.onCopy_result h
    obtain ⟨x, s₂, _, h2⟩ := SM.bind_some h1
    obtain ⟨y, s₃, _, h3⟩ := SM.bind_some h2
    obtain ⟨z, s₄, _, h4⟩ := SM.bind_some h3
    obtain ⟨-, h4⟩ := open Classical in ite_none_some h4
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h4)
    exact rinv_pure L hi rfl
  | tl, .id A t u, hint, s, s', r, hi, h => by
    rw [runT] at h
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, h⟩ := h
    obtain ⟨-, h⟩ := open Classical in ite_none_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact rinv_pure L hi rfl
  | tl, .ascribe u A, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some (SM.strictS_some h).1
    have e := SM.onCopy_state h1
    subst e
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨-, h4⟩ := open Classical in ite_none_some h4
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h4)
    exact runT_rinv hK false u _ _ _ y hi h3
  | tl, .letIn x u w, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, T⟩, s₁⟩, h1, ⟨⟨r', R⟩, s₃⟩, h2, h3⟩ := h
    obtain ⟨-, h3⟩ := open Classical in ite_none_some h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h3)
    obtain ⟨hi₁, hy₁, e₁, o₁⟩ := runT_rinv hK false u _ s s₁ (v, T) hi h1
    have hi₂ := pushBindShaped_rinv hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } v rfl
      fun l hl => by
        rcases hy₁ l hl with ⟨h' | h', hn⟩
        · exact ⟨.inl h', hn⟩
        · exact ⟨.inr (.inr h'), hn⟩
    have o₂ := ordKeep_pushBindShaped hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } hy₁
    obtain ⟨hi₃, hy₃, e₃, o₃⟩ := runT_rinv hK tl w (tailHint tl hint) _ s₃ (r', R) hi₂ h2
    dsimp only
    refine ⟨(letDrop_rinv L hi₃ hy₃ _ ?_).1, (letDrop_rinv L hi₃ hy₃ _ ?_).2.1,
      e₁.trans (envLe_letDrop ((envPush_pushBindShaped _ _).trans_le e₃) _),
      o₁.trans e₁ (o₂.trans' (fun _ hq => mem_positions_pushBindShaped _ hq)
        (Nat.le_of_eq (by unfold SState.topIdx; rw [(envPush_pushBindShaped _ _).1]))
        (o₃.trans' (fun _ hq => e₃.mem hq) (Nat.le_of_eq (topIdx_envLe e₃).symm) (letDrop_rinv L hi₃ hy₃ _ ?_).2.2))⟩
    all_goals (unfold dropped; cases s₃.env.getLast? <;> rfl)
  | tl, .matchNat p z u, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨tg, s₀⟩, h1, h⟩ := h
    have h1 := (SM.guarded_some h1).2
    obtain ⟨_, -, h⟩ := h
    obtain ⟨hi₀, e₀, o₀⟩ := tagOf_rinv K φ L h1 hi
    obtain ⟨hi₁', e₁', o₁'⟩ := matchEntry_props K φ L (!tl) (.matchNat p z u) hi₀
    have hlend := matchEntry_lend K φ (!tl) (.matchNat p z u) s₀
    generalize matchEntry K φ (!tl) (.matchNat p z u) s₀ = me at h hi₁' e₁' o₁' hlend
    obtain ⟨s₁, lend⟩ := me
    dsimp only at h hi₁' e₁' o₁' hlend
    have hi₁ := hi₁'
    have e₁ := e₀.trans e₁'
    have o₁ := o₀.trans e₀ o₁'
    split at h
    · try dsimp only at h
      cases h2 : runT K ρ φ tl (tailHint tl hint) z s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        simp only [Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runT_rinv hK tl z (tailHint tl hint) _ s₂ (r', R) hi₁ h2
        exact lend_post L _ (hlend _ _) ⟨joinDrop_rinv K φ L _ _ hi₂, fun y hl => joinDrop_lou K φ L _ _ hi₂ (hy₂ y hl),
          e₁.trans (e₂.trans (joinDrop_envLe K φ _ _ _)),
          o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ _ hi₂))⟩
    · try dsimp only at h
      cases h2 : runT K ρ φ tl (tailHint tl hint) u s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        simp only [Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runT_rinv hK tl u (tailHint tl hint) _ s₂ (r', R) hi₁ h2
        exact lend_post L _ (hlend _ _) ⟨joinDrop_rinv K φ L _ _ hi₂, fun y hl => joinDrop_lou K φ L _ _ hi₂ (hy₂ y hl),
          e₁.trans (e₂.trans (joinDrop_envLe K φ _ _ _)),
          o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ _ hi₂))⟩
    · cases h
  | tl, .matchInd p n arms, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨tg, s₀⟩, h1, h⟩ := h
    have h1 := (SM.guarded_some h1).2
    obtain ⟨_, -, h⟩ := h
    obtain ⟨hi₀, e₀, o₀⟩ := tagOf_rinv K φ L h1 hi
    obtain ⟨hi₁', e₁', o₁'⟩ := matchEntry_props K φ L (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) hi₀
    have hlend := matchEntry_lend K φ (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) s₀
    generalize matchEntry K φ (!tl && !tg.isProof && !oneCtor K.Γ n) (.matchInd p n arms) s₀ = me at h hi₁' e₁' o₁' hlend
    obtain ⟨s₁, lend⟩ := me
    dsimp only at h hi₁' e₁' o₁' hlend
    have hi₁ := hi₁'
    have e₁ := e₀.trans e₁'
    have o₁ := o₀.trans e₀ o₁'
    split at h
    · rename_i c _
      try dsimp only at h
      cases h2 : runArm K ρ φ tl (tailHint tl hint) c arms s₁ with
      | none => rw [h2] at h; cases h
      | some a =>
        rw [h2] at h
        obtain ⟨⟨r', R⟩, s₂⟩ := a
        simp only [Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runArm_rinv hK tl arms (tailHint tl hint) _ _ s₂ (r', R) hi₁ h2
        have hj : ∀ sj, sj = lend R.label (joinDrop K φ (movedPlaces φ s₁) (.matchInd p n arms) s₂) ∨ sj = s₂ →
            RInv L sj ∧ (∀ y, R.label = some y → LoU1 sj y) ∧ EnvLe s sj ∧ OrdKeep L s sj := by
          rintro sj (rfl | rfl)
          · exact lend_post L _ (hlend _ _) ⟨joinDrop_rinv K φ L _ _ hi₂, fun y hl => joinDrop_lou K φ L _ _ hi₂ (hy₂ y hl),
              e₁.trans (e₂.trans (joinDrop_envLe K φ _ _ _)),
              o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ _ hi₂))⟩
          · exact ⟨hi₂, hy₂, e₁.trans e₂, o₁.trans e₁ o₂⟩
        refine hj _ ?_
        cases tg <;> first | exact .inr rfl | (dsimp only; split; exact .inr rfl; exact .inl rfl)
    · -- an erased match on a proof with other than one arm, or on a proof of a non-subsingleton (docs/31 D229):
      -- the state as it was, no label
      split at h
      · split at h
        · obtain ⟨c, R, s₂, -, -, hr, hs'⟩ := SM.anyArm_some h
          subst hr hs'
          refine ⟨hi₁, ?_, e₁, o₁⟩
          intro y hl
          cases hl
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          refine ⟨hi₁, ?_, e₁, o₁⟩
          intro y hl
          cases hl
      · cases h
  | tl, .call f args hd, hint, s, s', r, hi, h => by
    rw [runT] at h
    dsimp only at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    obtain ⟨fv, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨as, s₂, h3, h4⟩ := SM.bind_some h2
    have hf : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.headOf_some h1 with ⟨p, h1⟩ | h1
      · have h1 := (SM.guarded_some h1).2
        exact ⟨(readPlace_rinv K φ L h1 hi).1, readPlace_envLe K φ h1, readPlace_ordKeep K φ h1 hi⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false f _ s s₁ fv hi h1
        exact ⟨hi₁, e₁, o₁⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hf
    obtain ⟨hi₂, e₂, o₂⟩ := runArgs_rinv hK _ _ args [] s₁ s₂ as hi₁ h3
    obtain ⟨-, h4⟩ := open Classical in ite_none_some h4
    unfold callOf at h4
    split at h4 <;> first
      | exact ⟨(callOfL_rinv L _ _ _ _ hi₂ h4).1, (callOfL_rinv L _ _ _ _ hi₂ h4).2,
          e₁.trans (e₂.trans (callOfL_envLe _ _ _ _ h4)),
          o₁.trans e₁ (o₂.trans e₂ (callOfL_ordKeep _ _ _ _ hi₂ h4))⟩
      | cases h4
  | tl, .pi hs ds c, hint, s, s', r, hi, h => by
    rw [runT] at h
    obtain ⟨-, h⟩ := open Classical in ite_none_some h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact rinv_pure L hi rfl
  | tl, .tind n args, hint, s, s', r, hi, h => by
    rw [runT] at h
    cases hd : K.Γ.find? (·.name == n) with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      obtain ⟨ps, s₁, h1, h2⟩ := SM.bind_some h
      have e := runParams_state K ρ φ d args 0 [] s s₁ ps h1
      subst e
      obtain ⟨-, h2⟩ := open Classical in ite_none_some h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
      exact rinv_pure L hi rfl
  | tl, .ctor ty c hh ps args, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      obtain ⟨psM, s₁, h1, h2⟩ := SM.bind_some h
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      dsimp only at h2
      obtain ⟨⟨fs, sol⟩, s₂, h3, h4⟩ := SM.bind_some h2
      obtain ⟨hi₂, e₂, o₂⟩ := runFields_rinv hK _ d c args 0 _ _ [] _ _ _ hi h3
      obtain ⟨-, h4⟩ := open Classical in ite_none_some h4
      obtain ⟨rfl, _, -, rfl⟩ := ctorOut_inv (SM.strictS_some h4).1
      exact rinv_ret L hi₂ e₂ o₂ rfl
  | tl, .fix self hs ds c dec body, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    dsimp only at h
    obtain ⟨-, h⟩ := open Classical in ite_none_some h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (SM.strictS_some h).1)
    obtain ⟨hi', e', o'⟩ := capMoves_props L (capStep K) (fun s i => by
      unfold capStep
      split
      · rename_i pos _
        dsimp only
        split
        · exact .inr ⟨pos, .inl rfl⟩
        · exact .inr ⟨pos, .inr rfl⟩
      · exact .inl rfl) _ hi
    exact ⟨hi', (fun l hl => by cases hl), e', o'⟩
  | tl, .prim n args, hint, s, s', r, hi, h => by
    rcases run_prim_cases K ρ φ h with ⟨rfl, hl⟩ | ⟨t, tl', ht, h'⟩ | ⟨p, h'⟩ | ⟨t, hJ, s₂, ht, h', rfl⟩
    · exact rinv_pure L hi hl
    · exact runAll_rinvT hK args t ht tl' hint s s' r hi h'
    · exact ⟨(readPlace_rinv K φ L h' hi).1, (readPlace_rinv K φ L h' hi).2, readPlace_envLe K φ h',
        readPlace_ordKeep K φ h' hi⟩
    · obtain ⟨hi₁, e₁, o₁⟩ := matchEntry_props K φ L true t hi
      obtain ⟨hi₂, hy₂, e₂, o₂⟩ := runAll_rinv hK args t ht hJ _ s₂ r hi₁ h'
      exact ⟨joinDrop_rinv K φ L _ _ hi₂, fun y hl => joinDrop_lou K φ L _ _ hi₂ (hy₂ y hl),
        e₁.trans (e₂.trans (joinDrop_envLe K φ _ _ _)),
        o₁.trans e₁ (o₂.trans e₂ (joinDrop_ordKeep K φ _ _ hi₂))⟩
  | tl, .assign p u, hint, s, s', r, hi, h => by
    rw [runT] at h
    rcases SM.erasedIf_some h with h | ⟨rfl, hl⟩
    rotate_left
    · exact rinv_pure L hi hl
    simp only [Bind.bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨v, R⟩, s₁⟩, h2, h⟩ := h
    dsimp only at h
    obtain ⟨-, h⟩ := open Classical in ite_none_some h
    obtain ⟨hi₁, hy₁, e₁, o₁⟩ := runT_rinv hK false u _ s s₁ (v, R) hi h2
    cases ha : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) s₁ with
    | none => rw [ha] at h; cases h
    | some y =>
      obtain ⟨r₀, s₃⟩ := y
      rw [ha] at h
      dsimp only at h
      obtain ⟨-, h⟩ := open Classical in ite_none_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hi₃, hl₃, e₃, o₃⟩ := assignAt_rinv K φ L (SM.guarded_some ha).2 hi₁ hy₁
      obtain ⟨hi₄, e₄, o₄⟩ := invalidate_props K φ L p hi₃
      exact ⟨hi₄, (fun l hl => by rw [hl₃] at hl; cases hl), e₁.trans (e₃.trans e₄),
        o₁.trans e₁ (o₃.trans e₃ o₄)⟩

theorem runAll_rinvT (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (ts : List Term) (t : Term), t ∈ ts →
    ∀ (tl' : Bool) (hint : TyS) (s s' : SState) (r : Res), RInv L s → runT K ρ φ tl' hint t s = some (r, s') →
      RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], t, ht, _, _, _, _, _, _, _ => absurd ht List.not_mem_nil
  | a :: as, t, ht, tl', hint, s, s', r, hi, h => by
    rw [List.mem_cons] at ht
    rcases ht with e | ht'
    · rw [e] at h; exact runT_rinv hK tl' a hint s s' r hi h
    · exact runAll_rinvT hK as t ht' tl' hint s s' r hi h

theorem runAll_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (ts : List Term) (t : Term), t ∈ ts →
    ∀ (hint : TyS) (s s' : SState) (r : Res), RInv L s → run K ρ φ hint t s = some (r, s') →
      RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], t, ht, _, _, _, _, _, _ => absurd ht List.not_mem_nil
  | a :: as, t, ht, hint, s, s', r, hi, h => by
    rw [List.mem_cons] at ht
    rcases ht with e | ht'
    · rw [e] at h; exact runT_rinv hK false a hint s s' r hi h
    · exact runAll_rinv hK as t ht' hint s s' r hi h

theorem runArgs_rinv (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem) (s s' : SState) (rs : List Res), RInv L s →
      runArgs K ρ φ stmt fT earlier args s = some (rs, s') → RInv L s' ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], earlier, s, s', rs, hi, h => by
    simp only [runArgs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | a :: as, earlier, s, s', rs, hi, h => by
    simp only [runArgs] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    -- a statement argument runs on its own copy: the state is as it was
    have hx : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false a _ s s₁ x hi h1
        exact ⟨hi₁, e₁, o₁⟩
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hx
    obtain ⟨hi₂, e₂, o₂⟩ := runArgs_rinv hK stmt fT as _ s₁ _ y hi₁ h3
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

theorem runFields_rinv (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem) (s s' : SState)
      (fs : List Sem × List (Option Sem)), RInv L s →
      runFields K ρ φ stmt d c i rh sol earlier args s = some (fs, s') → RInv L s' ∧ EnvLe s s' ∧ OrdKeep L s s'
  | [], i, rh, sol, earlier, s, s', fs, hi, h => by
    simp only [runFields] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
  | a :: as, i, rh, sol, earlier, s, s', fs, hi, h => by
    simp only [runFields] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hx : RInv L s₁ ∧ EnvLe s s₁ ∧ OrdKeep L s s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · obtain ⟨hi₁, _, e₁, o₁⟩ := runT_rinv hK false a _ s s₁ x hi h1
        exact ⟨hi₁, e₁, o₁⟩
      · exact ⟨hi, EnvLe.refl _, OrdKeep.refl _⟩
    obtain ⟨hi₁, e₁, o₁⟩ := hx
    obtain ⟨hi₂, e₂, o₂⟩ := runFields_rinv hK stmt d c as _ _ _ _ s₁ _ y hi₁ h3
    exact ⟨hi₂, e₁.trans e₂, o₁.trans e₁ o₂⟩

theorem runArm_rinv (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (tl : Bool) (arms : List (Hint × Term)) (hint : TyS) (c : Nat)
    (s s' : SState) (r : Res), RInv L s → runArm K ρ φ tl hint c arms s = some (r, s') →
      RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s'
  | _, [], hint, c, s, s', r, hi, h => by
    simp only [runArm, SM.fail] at h; cases h
  | tl, (_, t) :: rest, hint, c, s, s', r, hi, h => by
    simp only [runArm] at h
    split at h
    · exact runT_rinv hK tl t hint s s' r hi h
    · exact runArm_rinv hK tl rest hint (c - 1) s s' r hi h
end

/-- `runT_rinv` at a position that is not a tail. -/
theorem run_rinv (hK : ∀ n, (K.C.global n).2.label = none) (t : Term) (hint : TyS) (s s' : SState) (r : Res)
    (hi : RInv L s) (h : run K ρ φ hint t s = some (r, s')) :
    RInv L s' ∧ LoU s' r.2.label ∧ EnvLe s s' ∧ OrdKeep L s s' :=
  runT_rinv K ρ φ L hK false t hint s s' r hi h

end

end Ochr.Meaning
