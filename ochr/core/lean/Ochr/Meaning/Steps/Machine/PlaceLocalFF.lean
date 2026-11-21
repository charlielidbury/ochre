import Ochr.Meaning.Steps.Machine.DecBack
import Ochr.Meaning.Steps.Machine.DecideFuelFF
import Ochr.Meaning.Steps.Machine.Inv
import Ochr.Meaning.Steps.Machine.PlaceLocal

/-!
# The fuel-free table is local to the root (`placeLocal_ff`; machine lane)

`Decide.placeDecl` reads the frame only at the place's root variable (`liveDecl`, in the live mode);
the rest of its run reads the tables (`fieldIsProof`, `lookupInd`, `fieldAt` through `fieldDecl` in
the dead mode). So a run on `p` and a run on `p` re-rooted, from states whose tables agree and whose
roots read alike, succeed together with one answer (`Fwd2`, a two-computation `Fwd`); the fuel-free
table, which reads the answer at any succeeding fuel, is then the same at the two (`placeLocal_ff`).
Under a root read `.other` or `.ref .other` every run's answer is one of `.other`, `.prop`, `.ref
.other` (no field of either is an inductive), so no place reads an inductive there.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- Two computations: `x` keeps the state, and every success of `x` from `s₁` is one of `y` from each
`R`-related `s₂` (same value, budget, log), ending at `s₂`. -/
def Fwd2 (R : MState → MState → Prop) {α : Type} (x y : M α) : Prop :=
  Keep x ∧ ∀ s₁ s₂, R s₁ s₂ → ∀ f l a s' f' l', runAll x s₁ f l = ((.ok (.ok (a, s')), f'), l') →
    runAll y s₂ f l = ((.ok (.ok (a, s₂)), f'), l')

theorem Fwd.keep {R : MState → MState → Prop} {α : Type} {x : M α} (h : Fwd R x) : Keep x := h.1

theorem Fwd.two {R : MState → MState → Prop} {α : Type} {x : M α} (h : Fwd R x) : Fwd2 R x x := ⟨h.1, h.2⟩

theorem fwd2_bind {R : MState → MState → Prop} {α β : Type} {x y : M α} {k k' : α → M β} (hx : Fwd2 R x y)
    (hk : ∀ a, Fwd2 R (k a) (k' a)) : Fwd2 R (x >>= k) (y >>= k') := by
  refine ⟨keep_bind hx.1 fun a => (hk a).1, fun s₁ s₂ h f l b s' f' l' e => ?_⟩
  rw [runAll_bind] at e ⊢
  revert e
  rcases e₀ : runAll x s₁ f l with ⟨⟨e₁ | e₁ | ⟨a, s₁'⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    have hs : s₁' = s₁ := hx.1 s₁ f l a s₁' f₁ l₁ e₀
    subst hs
    rw [hx.2 s₁' s₂ h f l a s₁' f₁ l₁ e₀]
    exact (hk a).2 s₁' s₂ h f₁ l₁ b s' f' l' e

/-- The tables, the mode, and the two roots read alike. -/
structure RootRel (i i' : Nat) (s₁ s₂ : MState) : Prop where
  tab : TabLe s₁ s₂
  live : s₁.liveScope = s₂.liveScope
  root : s₁.liveScope = true → liveVal s₁ i = liveVal s₂ i'

instance (i i' : Nat) : TabRelation (RootRel i i') := ⟨RootRel.tab⟩

theorem fwd_fieldAt_tab (n : Nat) (r : DeclInfo) (nm : String) (c j : Nat) : Fwd TabLe (fieldAt n r nm c j) := by
  cases n with
  | zero => unfold fieldAt; fwd_go
  | succ m =>
    unfold fieldAt; (try dsimp only); fwd_go
    all_goals exact (decideFwd m).fieldDecl _ _ _ _

/-- The root of `placeDecl` read at two indices. -/
theorem fwd2_liveBranch (i i' : Nat) :
    Fwd2 (RootRel i i') (get >>= fun s => if s.liveScope = true then liveDecl i else pure DeclInfo.other)
      (get >>= fun s => if s.liveScope = true then liveDecl i' else pure DeclInfo.other) := by
  refine ⟨keep_get_bind fun s => ?_, fun s₁ s₂ h f l a s' f' l' e => ?_⟩
  · split
    · exact keep_liveDecl i s
    · exact keep_pure _ s
  · show runAll (if s₂.liveScope = true then liveDecl i' else pure DeclInfo.other) s₂ f l = _
    change runAll (if s₁.liveScope = true then liveDecl i else pure DeclInfo.other) s₁ f l = _ at e
    have hl2 := h.live
    by_cases hl : s₁.liveScope = true
    · have hv := h.root hl
      rw [← hl2]
      simp only [hl, if_true] at e ⊢
      change ((Except.ok (Except.ok (liveVal s₁ i, s₁)), f), l) = _ at e
      change ((Except.ok (Except.ok (liveVal s₂ i', s₂)), f), l) = _
      simp only [Prod.mk.injEq, Except.ok.injEq] at e
      obtain ⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩ := e
      rw [hv]
    · rw [← hl2]
      simp only [hl, if_false, Bool.false_eq_true] at e ⊢
      exact (fwd_pure (R := RootRel i i') _).2 s₁ s₂ h f l a s' f' l' e

/-- **`placeDecl` on a place and on it re-rooted**: from states with one table and the two roots read
alike, the runs succeed together with one answer. -/
theorem placeDecl_fwd2 (i i' : Nat) : ∀ (p : Place) (n : Nat),
    Fwd2 (RootRel i i') (placeDecl n [] (p.mapRoot fun _ => .var i)) (placeDecl n [] (p.mapRoot fun _ => .var i'))
  | p, 0 => by
    unfold placeDecl; exact (fwd_exhausted _).two
  | .var _, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    simp only [List.length_nil, Nat.not_lt_zero, dite_false, Nat.sub_zero]
    exact fwd2_liveBranch i i'
  | .deref q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    exact fwd2_bind (placeDecl_fwd2 i i' q n) fun r => (by split <;> exact fwd_pure _ : Fwd _ _).two
  | .field g q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    refine fwd2_bind (fwd_fieldIsProof g).two fun c => ?_
    split
    · exact (fwd_pure _).two
    · exact fwd2_bind (placeDecl_fwd2 i i' q n) fun r => ((fwd_fieldAt_tab _ _ _ _ _).mono fun _ _ h => h.tab).two
  | .proj j q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    refine fwd2_bind (placeDecl_fwd2 i i' q n) fun r => Fwd.two ?_
    fwd_go
    all_goals exact (fwd_fieldAt_tab _ _ _ _ _).mono fun _ _ h => h.tab

theorem fwd2At_get_bind {α : Type} {k k' : MState → M α} {s₁ s₂ : MState}
    (h : ∀ f l a s' f' l', runAll (k s₁) s₁ f l = ((.ok (.ok (a, s')), f'), l') →
      runAll (k' s₂) s₂ f l = ((.ok (.ok (a, s₂)), f'), l')) :
    ∀ f l a s' f' l', runAll (get >>= k) s₁ f l = ((.ok (.ok (a, s')), f'), l') →
      runAll (get >>= k') s₂ f l = ((.ok (.ok (a, s₂)), f'), l') := h

/-- `withLive true` around two computations `Fwd2`-related at the roots `i`, `i'`. -/
theorem fwd2_withLive_true {i i' : Nat} {α : Type} {x y : M α} (hx : Fwd2 (RootRel i i') x y) {s₁ s₂ : MState}
    (ht : TabLe s₁ s₂) (hr : liveVal s₁ i = liveVal s₂ i') :
    ∀ f l a s' f' l', runAll (withLive true x) s₁ f l = ((.ok (.ok (a, s')), f'), l') →
      runAll (withLive true y) s₂ f l = ((.ok (.ok (a, s₂)), f'), l') := by
  have hR : RootRel i i' { s₁ with liveScope := true } { s₂ with liveScope := true } :=
    ⟨⟨ht.globals, ht.inds, ht.absDecl⟩, rfl, fun _ => hr⟩
  unfold withLive
  refine fwd2At_get_bind fun f l a s' f' l' e => ?_
  simp only [runAll_bind, runAll_modify] at e ⊢
  rcases e₀ : runAll (onFail x (modify fun s₀ => { s₀ with liveScope := s₁.liveScope })) { s₁ with liveScope := true } f l
    with ⟨⟨e₁ | e₁ | ⟨r, t₁⟩, f₁⟩, l₁⟩
  · rw [e₀] at e; cases e
  · rw [e₀] at e; cases e
  · rw [e₀] at e
    have hx₁ := runAll_onFail_ok e₀
    have ht₁ : t₁ = { s₁ with liveScope := true } := hx.1 _ f l r t₁ f₁ l₁ hx₁
    have hx₂ := hx.2 _ _ hR f l r t₁ f₁ l₁ hx₁
    rw [runAll_onFail_of_ok (c := modify fun s₀ => { s₀ with liveScope := s₂.liveScope }) hx₂]
    change ((Except.ok (Except.ok (r, { t₁ with liveScope := s₁.liveScope })), f₁), l₁) =
      ((Except.ok (Except.ok (a, s')), f'), l') at e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩ := e
    change ((Except.ok (Except.ok (r, { { s₂ with liveScope := true } with liveScope := s₂.liveScope })), f₁), l₁) = _
    cases s₂; rfl

theorem topReadings_scopeState (st : MState) (sc : List DeclInfo) : topReadings (scopeState st sc) = sc := by
  simp only [topReadings, scopeState, Array.back?, List.size_toArray, List.length_reverse, List.length_map]
  simp [List.map_reverse]
  exact List.map_id' sc

theorem liveVal_scopeState (st : MState) (sc : List DeclInfo) (i : Nat) :
    liveVal (scopeState st sc) i = sc.getD i .other := by
  rw [liveVal_eq, topReadings_scopeState]
  by_cases h : i < sc.length
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]; rfl

theorem _root_.Ochr.Place.eq_of_steps : ∀ {p q : Place}, p.steps = q.steps → p = q
  | .var i, .var j, h => by simp [Place.steps] at h; rw [h]
  | .var _, .deref q, h | .var _, .proj _ q, h | .var _, .field _ q, h => by
    simp only [Place.steps, Prod.mk.injEq] at h; exact absurd h.2 (by simp)
  | .deref p, .var _, h | .proj _ p, .var _, h | .field _ p, .var _, h => by
    simp only [Place.steps, Prod.mk.injEq] at h; exact absurd h.2.symm (by simp)
  | .deref p, .deref q, h => by
    simp only [Place.steps] at h
    have := List.append_inj' (Prod.mk.inj h).2 rfl
    rw [Place.eq_of_steps (Prod.ext (Prod.mk.inj h).1 this.1)]
  | .proj i p, .proj j q, h => by
    simp only [Place.steps] at h
    have := List.append_inj' (Prod.mk.inj h).2 rfl
    simp only [List.cons.injEq, Step.proj.injEq, and_true] at this
    rw [Place.eq_of_steps (Prod.ext (Prod.mk.inj h).1 this.1), this.2]
  | .field g p, .field g' q, h => by
    simp only [Place.steps] at h
    have := List.append_inj' (Prod.mk.inj h).2 rfl
    simp only [List.cons.injEq, Step.field.injEq, and_true] at this
    rw [Place.eq_of_steps (Prod.ext (Prod.mk.inj h).1 this.1), this.2]
  | .deref _, .proj _ _, h | .deref _, .field _ _, h | .proj _ _, .deref _, h | .proj _ _, .field _ _, h
  | .field _ _, .deref _, h | .field _ _, .proj _ _, h => by
    simp only [Place.steps] at h
    have := (List.append_inj' (Prod.mk.inj h).2 rfl).2
    simp at this

theorem succeeds_reroot (st : MState) (q : Place) (i i' : Nat) (sc sc' : List DeclInfo)
    (hr : sc.getD i .other = sc'.getD i' .other) (a : DeclInfo)
    (h : SucceedsAt (placeDeclD (q.reroot i)) (scopeState st sc) a) :
    SucceedsAt (placeDeclD (q.reroot i')) (scopeState st sc') a := by
  obtain ⟨f, b, s', hrun⟩ := h
  obtain ⟨L, f', l', e⟩ := runs_runAll hrun
  have ht : TabLe (scopeState st sc) (scopeState st sc') := ⟨rfl, rfl, fun _ _ h => h⟩
  have hl : liveVal (scopeState st sc) i = liveVal (scopeState st sc') i' := by
    rw [liveVal_scopeState, liveVal_scopeState]; exact hr
  exact ⟨f, b, scopeState st sc', runs_of_runAll (fwd2_withLive_true (placeDecl_fwd2 i i' q f) ht hl _ _ _ _ _ _ e)⟩

theorem ff_reroot (st : MState) (q : Place) (i i' : Nat) (sc sc' : List DeclInfo)
    (hr : sc.getD i .other = sc'.getD i' .other) :
    readDecisionFF (scopeState st sc) DeclInfo.other (placeDeclD (q.reroot i)) =
      readDecisionFF (scopeState st sc') DeclInfo.other (placeDeclD (q.reroot i')) := by
  by_cases h : ∃ a, SucceedsAt (placeDeclD (q.reroot i)) (scopeState st sc) a
  · obtain ⟨a, f, b, s', hrun⟩ := h
    obtain ⟨f2, b2, s2, hrun2⟩ := succeeds_reroot st q i i' sc sc' hr a ⟨f, b, s', hrun⟩
    rw [readDecisionFF_of_runs ((decide_fuel_agree' _).2.1 _) hrun,
      readDecisionFF_of_runs ((decide_fuel_agree' _).2.1 _) hrun2]
  · have h2 : ¬ ∃ a, SucceedsAt (placeDeclD (q.reroot i')) (scopeState st sc') a := fun ⟨a, ha⟩ =>
      h ⟨a, succeeds_reroot st q i' i sc' sc hr.symm a ha⟩
    unfold readDecisionFF; rw [dif_neg h, dif_neg h2]

/-- **The fuel-free table reads a place by its root's reading and its steps.** -/
theorem placeDecl_ff_root (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat))
    (sc sc' : List DeclInfo) (p p' : Place) (hs : p.steps.2 = p'.steps.2)
    (hr : sc.getD p.steps.1 .other = sc'.getD p'.steps.1 .other) :
    (checkerDecisionsFF st bc).placeDecl sc p = (checkerDecisionsFF st bc).placeDecl sc' p' := by
  have e1 : p.reroot p.steps.1 = p := Place.eq_of_steps (by rw [Place.steps_reroot])
  have e2 : p.reroot p'.steps.1 = p' := Place.eq_of_steps (by rw [Place.steps_reroot, hs])
  have := ff_reroot st p p.steps.1 p'.steps.1 sc sc' hr
  rw [e1, e2] at this
  exact this

/-! ## Under a root read `.other` or `.ref .other` no place reads an inductive -/

/-- The readings a place under a root read `.other`, `.ref .other` or `.unit` can have. -/
def InS (d : DeclInfo) : Prop := d = .other ∨ d = .prop ∨ d = .ref .other ∨ d = .unit

/-- `x` keeps the state, and from a state meeting `Q` every success answers `P`. -/
def ResIn {α : Type} (P : α → Prop) (Q : MState → Prop) (x : M α) : Prop :=
  Keep x ∧ ∀ s, Q s → ∀ f l a s' f' l', runAll x s f l = ((.ok (.ok (a, s')), f'), l') → P a

section
variable {Q : MState → Prop}

theorem resIn_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : ResIn P Q (pure a : M α) := by
  refine ⟨keep_pure a, fun s _ f l b s' f' l' e => ?_⟩
  simp only [runAll, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at e
  cases e; exact h

theorem resIn_exhausted {α : Type} {P : α → Prop} (m : String) : ResIn P Q (exhausted m : M α) :=
  ⟨keep_exhausted m, fun _ _ _ _ _ _ _ _ h => by cases h⟩

theorem resIn_bind {α β : Type} {P : α → Prop} {P' : β → Prop} {x : M α} {k : α → M β} (hx : ResIn P Q x)
    (hk : ∀ a, P a → ResIn P' Q (k a)) (hk' : ∀ a, Keep (k a)) : ResIn P' Q (x >>= k) := by
  refine ⟨keep_bind hx.1 hk', fun s hs f l b s' f' l' e => ?_⟩
  rw [runAll_bind] at e
  revert e
  rcases e₀ : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    have hs₁ : s₁ = s := hx.1 s f l a s₁ f₁ l₁ e₀
    subst hs₁
    exact (hk a (hx.2 s₁ hs f l a s₁ f₁ l₁ e₀)).2 s₁ hs f₁ l₁ b s' f' l' e

theorem resIn_true {α : Type} {x : M α} (h : Keep x) : ResIn (fun _ => True) Q x :=
  ⟨h, fun _ _ _ _ _ _ _ _ _ => trivial⟩

end

theorem fieldAt_inS {Q : MState → Prop} (n : Nat) {r : DeclInfo} (hr : InS r) (nm : String) (c j : Nat) :
    ResIn InS Q (fieldAt n r nm c j) := by
  cases n with
  | zero => unfold fieldAt; exact resIn_exhausted _
  | succ m =>
    rcases hr with rfl | rfl | rfl | rfl <;>
    · unfold fieldAt
      simp only [List.filterMap_cons, List.filterMap_nil, List.isEmpty_nil, if_true]
      exact resIn_pure (.inl rfl)

theorem placeDecl_inS (i : Nat) : ∀ (p : Place) (n : Nat),
    ResIn InS (fun s => s.liveScope = true ∧ InS (liveVal s i)) (placeDecl n [] (p.mapRoot fun _ => .var i))
  | p, 0 => by unfold placeDecl; exact resIn_exhausted _
  | .var _, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    simp only [List.length_nil, Nat.not_lt_zero, dite_false, Nat.sub_zero]
    refine ⟨(fwd2_liveBranch i i).1, fun s hs f l a s' f' l' e => ?_⟩
    change runAll (if s.liveScope = true then liveDecl i else pure DeclInfo.other) s f l = _ at e
    simp only [hs.1, if_true] at e
    change ((Except.ok (Except.ok (liveVal s i, s)), f), l) = _ at e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := e
    exact hs.2
  | .deref q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    refine resIn_bind (placeDecl_inS i q n) (fun r hr => ?_) (fun r => (by split <;> exact keep_pure _))
    rcases hr with rfl | rfl | rfl | rfl
    · exact resIn_pure (.inl rfl)
    · exact resIn_pure (.inl rfl)
    · exact resIn_pure (.inl rfl)
    · exact resIn_pure (.inl rfl)
  | .field g q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    refine resIn_bind (resIn_true (fwd_fieldIsProof (R := TabLe) g).1) (fun c _ => ?_) (fun c => ?_)
    · split
      · exact resIn_pure (.inr (.inl rfl))
      · exact resIn_bind (placeDecl_inS i q n) (fun r hr => fieldAt_inS n hr _ _ _)
          (fun r => (fwd_fieldAt_tab _ _ _ _ _).1)
    · split
      · exact keep_pure _
      · exact keep_bind (placeDecl_inS i q n).1 fun r => (fwd_fieldAt_tab _ _ _ _ _).1
  | .proj j q, n + 1 => by
    simp only [Place.mapRoot]
    unfold placeDecl
    (try dsimp only)
    refine resIn_bind (placeDecl_inS i q n) (fun r hr => ?_) (fun r => ?_)
    · rcases hr with rfl | rfl | rfl | rfl <;> (simp [DeclInfo.isProof]; exact resIn_pure (by simp [InS]))
    · refine Fwd.keep (R := TabLe) ?_
      fwd_go
      all_goals exact (fwd_fieldAt_tab _ _ _ _ _)

theorem runAll_get_bind' {α : Type} {k : MState → M α} {s : MState} {f : Fuel} {l : Array LogEntry} :
    runAll (get >>= k) s f l = runAll (k s) s f l := rfl

theorem runAll_withLive_inv {α : Type} {b : Bool} {x : M α} {s : MState} {f : Fuel} {l : Array LogEntry} {a : α}
    {s' : MState} {f' : Fuel} {l' : Array LogEntry}
    (e : runAll (withLive b x) s f l = ((.ok (.ok (a, s')), f'), l')) :
    ∃ t f₁ l₁, runAll x { s with liveScope := b } f l = ((.ok (.ok (a, t)), f₁), l₁) := by
  unfold withLive at e
  rw [runAll_get_bind'] at e
  simp only [runAll_bind, runAll_modify] at e
  rcases e₀ : runAll (onFail x (modify fun s₀ => { s₀ with liveScope := s.liveScope })) { s with liveScope := b } f l
    with ⟨⟨e₁ | e₁ | ⟨r, t₁⟩, f₁⟩, l₁⟩
  · rw [e₀] at e; cases e
  · rw [e₀] at e; cases e
  · rw [e₀] at e
    change ((Except.ok (Except.ok (r, { t₁ with liveScope := s.liveScope })), f₁), l₁) =
      ((Except.ok (Except.ok (a, s')), f'), l') at e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := e
    exact ⟨t₁, f₁, l₁, runAll_onFail_ok e₀⟩

/-- Under a one-reading scope whose every index reads in `InS`, the fuel-free table reads every place
in `InS`. -/
theorem placeDecl_ff_inS (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat))
    (r : DeclInfo) (hr : ∀ i, InS ([r].getD i .other)) (p : Place) :
    InS ((checkerDecisionsFF st bc).placeDecl [r] p) := by
  show InS (readDecisionFF (scopeState st [r]) .other (placeDeclD p))
  unfold readDecisionFF
  split
  · rename_i h
    obtain ⟨f, b, s', hrun⟩ := h.choose_spec
    obtain ⟨L, f', l', e⟩ := runs_runAll hrun
    obtain ⟨t, f₁, l₁, e'⟩ := runAll_withLive_inv e
    have e1 : p.reroot p.steps.1 = p := Place.eq_of_steps (by rw [Place.steps_reroot])
    have hin := placeDecl_inS p.steps.1 p f
    rw [show (p.mapRoot fun _ => Place.var p.steps.1) = p from e1] at hin
    exact hin.2 _ ⟨rfl, by rw [show liveVal { scopeState st [r] with liveScope := true } p.steps.1 =
      liveVal (scopeState st [r]) p.steps.1 from rfl, liveVal_scopeState]; exact hr _⟩ _ _ _ _ _ _ e'
  · exact .inl rfl

theorem InS.not_ind {d : DeclInfo} (h : InS d) (n : String) (args : List DeclInfo) : d ≠ .ind n args := by
  rcases h with rfl | rfl | rfl | rfl <;> exact fun e => by cases e

/-- **The fuel-free table is local to the root** (`PlaceLocal`; its `unit` field: a root read `.unit`
reads `.unit` itself, `.other` under a dereference or a field (`fieldAt` finds no inductive), `.other`
under a projection). -/
theorem placeLocal_ff (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat)) :
    PlaceLocal (checkerDecisionsFF st bc) where
  root := placeDecl_ff_root st bc
  other p n args := (placeDecl_ff_inS st bc .other (fun i => by cases i <;> exact .inl rfl) p).not_ind n args
  ref p n args := (placeDecl_ff_inS st bc (.ref .other)
    (fun i => by cases i with | zero => exact .inr (.inr (.inl rfl)) | succ k => exact .inl rfl) p).not_ind n args
  unit p n args := (placeDecl_ff_inS st bc .unit
    (fun i => by cases i with | zero => exact .inr (.inr (.inr rfl)) | succ k => exact .inl rfl) p).not_ind n args

end Ochr.Meaning.Steps.Machine
