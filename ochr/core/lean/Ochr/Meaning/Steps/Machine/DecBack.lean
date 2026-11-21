import Ochr.Meaning.Steps.Machine.DecideFuel
import Ochr.Meaning.Steps.Machine.Defs

/-!
# Alignment at a larger table is alignment at a smaller one (`DecTab.back`)

A decision procedure's successful run at `st` reads only the tables (`globals`, `inds`, the frozen
readings `absDecl`), the reading mode `liveScope` and, when that is set, the top frame's readings
(`liveDecl`). Where `st'` extends `st`'s tables (`TablesGrow st st'`), every old entry of `absDecl` is
in `st'` at the same index; a reading past `st`'s end FAILS at `st` (`absReading`), so a successful
run at `st` never meets one. Hence the same run succeeds at `st'` with the same answer: a ONE-WAY
simulation (`Fwd`), the converse failing exactly where `st` lacks an entry.

`Fwd R x`: `x` keeps the state (`Slice.Keep`: the decision procedures write nothing) and every
success from `s₁` is one from every `R`-related `s₂`, with the same value, budget and log. Keeping
the state is part of the property so that a bind needs the relation at the start states only: the
state after a sub-run is the state before it. The relations: `TabLe` (the tables only, what
`declCopy` needs from the raw checker states, whose frames and mode differ), `LiveLe` (and the mode,
and the top frame's readings where the mode reads them), `EnvTab` (the tables and the frames, what
`scopeState st sc` and `scopeState st' sc` share).

Nothing in this file mentions the model.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

/-- `s₁`'s tables are inside `s₂`'s: the same globals and declarations, every frozen reading of
`s₁` at the same index in `s₂`. -/
structure TabLe (s₁ s₂ : MState) : Prop where
  globals : s₁.globals = s₂.globals
  inds : s₁.inds = s₂.inds
  absDecl : ∀ (σ : Nat) (d : DeclInfo), s₁.absDecl[σ]? = some d → s₂.absDecl[σ]? = some d

/-- `TabLe`, the same reading mode, and, where the mode reads the frame, the same top readings. -/
structure LiveLe (s₁ s₂ : MState) : Prop extends TabLe s₁ s₂ where
  liveScope : s₁.liveScope = s₂.liveScope
  live : s₁.liveScope = true → ∀ i, liveVal s₁ i = liveVal s₂ i

/-- `TabLe` and the same frames (`scopeState st sc` against `scopeState st' sc`). -/
structure EnvTab (s₁ s₂ : MState) : Prop extends TabLe s₁ s₂ where
  env : s₁.env = s₂.env

/-- A relation that relates the tables. -/
class TabRelation (R : MState → MState → Prop) : Prop where
  tab : ∀ {s₁ s₂ : MState}, R s₁ s₂ → TabLe s₁ s₂

instance : TabRelation TabLe := ⟨id⟩
instance : TabRelation LiveLe := ⟨LiveLe.toTabLe⟩
instance : TabRelation EnvTab := ⟨EnvTab.toTabLe⟩

/-- Every success of `x` from `s₁` is one from `s₂`, ending at `s₂`, with the same value, budget and log. -/
def FwdAt {α : Type} (x : M α) (s₁ s₂ : MState) : Prop :=
  ∀ f l a s' f' l', runAll x s₁ f l = ((.ok (.ok (a, s')), f'), l') → runAll x s₂ f l = ((.ok (.ok (a, s₂)), f'), l')

/-- **The one-way simulation**: `x` keeps the state, and succeeds from every `R`-related state where it
succeeds from the first. -/
def Fwd (R : MState → MState → Prop) {α : Type} (x : M α) : Prop :=
  Keep x ∧ ∀ s₁ s₂, R s₁ s₂ → FwdAt x s₁ s₂

variable {R : MState → MState → Prop}

theorem fwd_pure {α : Type} (a : α) : Fwd R (pure a : M α) := by
  refine ⟨keep_pure a, fun s₁ s₂ _ f l b s' f' l' h => ?_⟩
  simp only [runAll, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h ⊢
  cases h; rfl

theorem fwd_err {α : Type} (m : String) : Fwd R (err m : M α) :=
  ⟨keep_err m, fun _ _ _ _ _ _ _ _ _ h => by cases h⟩

theorem fwd_exhausted {α : Type} (m : String) : Fwd R (exhausted m : M α) :=
  ⟨keep_exhausted m, fun _ _ _ _ _ _ _ _ _ h => by cases h⟩

theorem fwd_bind {α β : Type} {x : M α} {k : α → M β} (hx : Fwd R x) (hk : ∀ a, Fwd R (k a)) :
    Fwd R (x >>= k) := by
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

/-- A read of the state whose continuation, at related states, is one computation. -/
theorem fwd_get_bind {α : Type} {k : MState → M α} (hk : ∀ s, Fwd R (k s))
    (heq : ∀ s₁ s₂, R s₁ s₂ → k s₁ = k s₂) : Fwd R (get >>= k) := by
  refine ⟨keep_get_bind fun s => (hk s).1 s, fun s₁ s₂ h f l a s' f' l' e => ?_⟩
  show runAll (k s₂) s₂ f l = _
  rw [← heq s₁ s₂ h]
  exact (hk s₁).2 s₁ s₂ h f l a s' f' l' e

theorem fwd_ite {α : Type} {c : Prop} {_ : Decidable c} {x y : M α} (hx : Fwd R x) (hy : Fwd R y) :
    Fwd R (if c then x else y) := by
  split <;> assumption

theorem fwd_dite {α : Type} {c : Prop} {_ : Decidable c} {x : c → M α} {y : ¬ c → M α}
    (hx : ∀ h, Fwd R (x h)) (hy : ∀ h, Fwd R (y h)) : Fwd R (if h : c then x h else y h) := by
  split <;> rename_i h <;> first | exact hx h | exact hy h

theorem fwd_map {α β : Type} (g : α → β) {x : M α} (hx : Fwd R x) : Fwd R (g <$> x) := by
  rw [map_eq_pure_bind]
  exact fwd_bind hx fun a => fwd_pure _

theorem fwd_discard {α : Type} {x : M α} (hx : Fwd R x) : Fwd R (discard x) := by
  show Fwd R (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact fwd_map _ hx

theorem fwd_forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Fwd R (body a b)) : Fwd R (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact fwd_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact fwd_bind (hb a b) (fun r => by cases r with
      | done b' => exact fwd_pure b'
      | yield b' => exact ih b')

theorem fwd_mapM {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a, Fwd R (f a)) : Fwd R (xs.mapM f) := by
  induction xs with
  | nil => exact fwd_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact fwd_bind (hf a) (fun b => fwd_bind ih (fun bs => fwd_pure _))

theorem fwd_allM {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, Fwd R (f a)) : Fwd R (xs.allM f) := by
  induction xs with
  | nil => exact fwd_pure true
  | cons a as ih =>
    unfold List.allM
    exact fwd_bind (hf a) (fun b => by cases b <;> first | exact ih | exact fwd_pure _)

/-- A relation weaker than `R'` simulates what `R'` does. -/
theorem Fwd.mono {R' : MState → MState → Prop} {α : Type} {x : M α} (hx : Fwd R' x)
    (h : ∀ s₁ s₂, R s₁ s₂ → R' s₁ s₂) : Fwd R x :=
  ⟨hx.1, fun s₁ s₂ hr => hx.2 s₁ s₂ (h s₁ s₂ hr)⟩

theorem Fwd.live {α : Type} {x : M α} (hx : Fwd TabLe x) : Fwd LiveLe x := hx.mono fun _ _ h => h.toTabLe

/-! ## The reads of the state -/

theorem fwd_lookupInd [TabRelation R] (n : String) : Fwd R (lookupInd n) := by
  unfold lookupInd
  refine fwd_get_bind (fun s => ?_) (fun s₁ s₂ h => by rw [(TabRelation.tab h).inds])
  split
  · exact fwd_pure _
  · exact fwd_err _

theorem fwd_lookupGlobal [TabRelation R] (n : String) : Fwd R (lookupGlobal n) := by
  unfold lookupGlobal
  refine fwd_get_bind (fun s => ?_) (fun s₁ s₂ h => by rw [(TabRelation.tab h).globals])
  split
  · exact fwd_pure _
  · exact fwd_err _

/-- D96: a frozen reading `s₁` has is `s₂`'s; one `s₁` lacks fails at `s₁`. -/
theorem fwd_absReading [TabRelation R] (σ : Nat) : Fwd R (absReading σ) := by
  refine ⟨keep_absReading σ, fun s₁ s₂ h f l a s' f' l' e => ?_⟩
  have ht := TabRelation.tab h
  unfold absReading at e ⊢
  change runAll (match s₁.absDecl[σ]? with
    | some d => pure d
    | none => err _) s₁ f l = _ at e
  change runAll (match s₂.absDecl[σ]? with
    | some d => pure d
    | none => err _) s₂ f l = _
  rcases hd : s₁.absDecl[σ]? with _ | d
  · rw [hd] at e; cases e
  · rw [hd] at e
    rw [ht.absDecl σ d hd]
    exact (fwd_pure (R := R) d).2 s₁ s₂ h f l a s' f' l' e

theorem fwd_capReadings (cs : List Value) (rd : List (DeclInfo × Value)) : Fwd R (capReadings cs rd) := by
  unfold capReadings
  by_cases h : rd.length < cs.length
  · simp only [h, if_true]
    exact fwd_bind (fwd_err _) fun _ => fwd_pure _
  · simp only [h, if_false]
    exact fwd_bind (fwd_pure _) fun _ => fwd_pure _

/-! ## The reading mode -/

theorem runAll_onFail_ok {α : Type} {x : M α} {c : M Unit} {s : MState} {f : Fuel} {l : Array LogEntry} {a : α}
    {s' : MState} {f' : Fuel} {l' : Array LogEntry}
    (h : runAll (onFail x c) s f l = ((.ok (.ok (a, s')), f'), l')) : runAll x s f l = ((.ok (.ok (a, s')), f'), l') := by
  unfold onFail at h
  rw [runAll_tryCatch] at h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨b, s₁⟩, f₁⟩, l₁⟩
  · rw [e] at h; cases h
  · rw [e] at h; exact absurd h (runAll_cleanup_throw c e₁ s f₁ l₁ a s' f' l')
  · rw [e] at h; exact h

theorem runAll_onFail_of_ok {α : Type} {x : M α} {c : M Unit} {s : MState} {f : Fuel} {l : Array LogEntry} {a : α}
    {s' : MState} {f' : Fuel} {l' : Array LogEntry}
    (h : runAll x s f l = ((.ok (.ok (a, s')), f'), l')) : runAll (onFail x c) s f l = ((.ok (.ok (a, s')), f'), l') := by
  unfold onFail
  rw [runAll_tryCatch, h]

/-- A read of the state, at two given states, by its continuations there. -/
theorem fwdAt_get_bind {α : Type} {k : MState → M α} {s₁ s₂ : MState}
    (h : ∀ f l a s' f' l', runAll (k s₁) s₁ f l = ((.ok (.ok (a, s')), f'), l') →
      runAll (k s₂) s₂ f l = ((.ok (.ok (a, s₂)), f'), l')) : FwdAt (get >>= k) s₁ s₂ := h

/-- `withLive b`: from states that, with the mode set to `b`, are `LiveLe`-related. -/
theorem fwd_withLive {R' : MState → MState → Prop} {α : Type} (b : Bool) {x : M α}
    (hR : ∀ s₁ s₂, R' s₁ s₂ → LiveLe { s₁ with liveScope := b } { s₂ with liveScope := b })
    (hx : Fwd LiveLe x) : Fwd R' (withLive b x) := by
  refine ⟨keep_withLive b hx.1, fun s₁ s₂ h => ?_⟩
  unfold withLive
  refine fwdAt_get_bind fun f l a s' f' l' e => ?_
  simp only [runAll_bind, runAll_modify] at e ⊢
  rcases e₀ : runAll (onFail x (modify fun s₀ => { s₀ with liveScope := s₁.liveScope })) { s₁ with liveScope := b } f l
    with ⟨⟨e₁ | e₁ | ⟨r, t₁⟩, f₁⟩, l₁⟩
  · rw [e₀] at e; cases e
  · rw [e₀] at e; cases e
  · rw [e₀] at e
    have hx₁ := runAll_onFail_ok e₀
    have ht : t₁ = { s₁ with liveScope := b } := hx.1 _ f l r t₁ f₁ l₁ hx₁
    have hx₂ := hx.2 _ _ (hR s₁ s₂ h) f l r t₁ f₁ l₁ hx₁
    rw [runAll_onFail_of_ok (c := modify fun s₀ => { s₀ with liveScope := s₂.liveScope }) hx₂]
    change ((Except.ok (Except.ok (r, { t₁ with liveScope := s₁.liveScope })), f₁), l₁) =
      ((Except.ok (Except.ok (a, s')), f'), l') at e
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩ := e
    change ((Except.ok (Except.ok (r, { { s₂ with liveScope := b } with liveScope := s₂.liveScope })), f₁), l₁) = _
    cases s₂; rfl

/-- `withLive false`: the mode then reads no frame, so the tables suffice. -/
theorem fwd_withLive_false [TabRelation R] {α : Type} {x : M α} (hx : Fwd LiveLe x) : Fwd R (withLive false x) :=
  fwd_withLive false (fun _ _ h => ⟨⟨(TabRelation.tab h).globals, (TabRelation.tab h).inds, (TabRelation.tab h).absDecl⟩,
    rfl, fun e => by cases e⟩) hx

/-- `withLive true` from states with the same frames. -/
theorem fwd_withLive_true {α : Type} {x : M α} (hx : Fwd LiveLe x) : Fwd EnvTab (withLive true x) :=
  fwd_withLive true (fun _ _ h => ⟨⟨h.globals, h.inds, h.absDecl⟩, rfl, fun _ i => by simp only [liveVal, h.env]⟩) hx

/-- `placeDecl`'s read of a variable past its scope: the frame's reading only in the live mode. -/
theorem fwd_liveBranch (j : Nat) :
    Fwd LiveLe (get >>= fun s => if s.liveScope = true then liveDecl j else pure DeclInfo.other) := by
  refine ⟨keep_get_bind fun s => ?_, fun s₁ s₂ h => fwdAt_get_bind fun f l a s' f' l' e => ?_⟩
  · split
    · exact keep_liveDecl j s
    · exact keep_pure _ s
  · have hl2 := h.liveScope
    by_cases hl : s₁.liveScope = true
    · have hv := h.live hl j
      rw [← hl2] at ⊢
      simp only [hl, if_true] at e ⊢
      change ((Except.ok (Except.ok (liveVal s₁ j, s₁)), f), l) = _ at e
      change ((Except.ok (Except.ok (liveVal s₂ j, s₂)), f), l) = _
      simp only [Prod.mk.injEq, Except.ok.injEq] at e
      obtain ⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩ := e
      rw [hv]
    · rw [← hl2] at ⊢
      simp only [hl, if_false, Bool.false_eq_true] at e ⊢
      exact (fwd_pure (R := LiveLe) _).2 s₁ s₂ h f l a s' f' l' e

/-! ## The decision procedures -/

set_option hygiene false in
/-- One step of a `Fwd` proof, by the shape of the computation; a read of the state is split into its
continuation at any state and the continuations' equality at related states (`fwd_get_bind`). -/
macro "fwd_step" : tactic => `(tactic| first
  | with_reducible exact fwd_pure _
  | with_reducible exact fwd_err _
  | with_reducible exact fwd_exhausted _
  | with_reducible exact fwd_lookupInd _
  | with_reducible exact fwd_lookupGlobal _
  | with_reducible exact fwd_absReading _
  | with_reducible exact fwd_capReadings _ _
  | with_reducible exact fwd_liveBranch _
  | rfl
  | (simp only [(TabRelation.tab h).globals, (TabRelation.tab h).inds]; done)
  | (simp only [(TabRelation.tab h).globals, (TabRelation.tab h).inds, LiveLe.liveScope h]; done)
  | (with_reducible refine fwd_get_bind (fun s => ?_) (fun s₁ s₂ h => ?_))
  | (with_reducible refine fwd_bind ?_ (fun _ => ?_))
  | (with_reducible refine fwd_withLive_false ?_)
  | (with_reducible refine fwd_map _ ?_)
  | (with_reducible refine fwd_discard ?_)
  | (with_reducible refine fwd_forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine fwd_mapM _ (fun _ => ?_))
  | (with_reducible refine fwd_allM _ (fun _ => ?_))
  | split
  | (dsimp only))

macro "fwd_go" : tactic => `(tactic| repeat (any_goals fwd_step))

section
variable [TabRelation R]
theorem fwd_fieldTermIsProp (d : IndDecl) (FT : Term) : Fwd R (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp; fwd_go
theorem fwd_fieldIsProof (g : FieldRef) : Fwd R (fieldIsProof g) := by
  unfold fieldIsProof; fwd_go
  all_goals exact fwd_fieldTermIsProp _ _
theorem fwd_ctorIsProof (ty : String) : Fwd R (ctorIsProof ty) := by unfold ctorIsProof; fwd_go
theorem fwd_preFlags (t : Term) (d : DeclInfo) : Fwd R (preFlags t d) := by unfold preFlags; fwd_go
theorem fwd_refineDecl (d : DeclInfo) : Fwd R (refineDecl d) := by unfold refineDecl; fwd_go
theorem fwd_sealedSort (t : Term) : Fwd R (sealedSort? t) := by unfold sealedSort?; fwd_go
end

/-- The seventeen functions of `Decide.lean`'s block the decisions reach, at `n`: `declCopy` and
`fieldDecl` at the tables only (`declCopy` is asked at the raw checker states, and reaches a frame
only through `fieldDecl`'s `withLive false`), the rest with the mode and the live readings. -/
structure DecideFwd (n : Nat) : Prop where
  placeDecl : ∀ sc p, Fwd LiveLe (placeDecl n sc p)
  fieldAt : ∀ r nm c i, Fwd LiveLe (fieldAt n r nm c i)
  fieldDecl : ∀ d args c i, Fwd TabLe (fieldDecl n d args c i)
  declCopy : ∀ r, Fwd TabLe (declCopy n r)
  callDecl : ∀ F as sc ns, Fwd LiveLe (callDecl n F as sc ns)
  closedTypeDecl : ∀ T, Fwd LiveLe (closedTypeDecl n T)
  sortOf : ∀ T, Fwd LiveLe (sortOf n T)
  declSort : ∀ sc ns T, Fwd LiveLe (declSort n sc ns T)
  declOf : ∀ chk sc ns t, Fwd LiveLe (declOf n chk sc ns t)
  typeDecl : ∀ chk sc ns T vis tsc, Fwd LiveLe (typeDecl n chk sc ns T vis tsc)
  typeFnDecl : ∀ F vis sc ns tsc as dflt, Fwd LiveLe dflt → Fwd LiveLe (typeFnDecl n F vis sc ns tsc as dflt)
  typePos : ∀ chk sc ns T, Fwd LiveLe (typePos n chk sc ns T)
  telescope : ∀ chk sc ns hs ds, Fwd LiveLe (telescope n chk sc ns hs ds)
  valueDecl : ∀ v, Fwd LiveLe (valueDecl n v)
  valTypeDecl : ∀ T, Fwd LiveLe (valTypeDecl n T)
  isPropV : ∀ T, Fwd LiveLe (isPropV n T)
  fnClass : ∀ T, Fwd LiveLe (fnClass n T)

set_option hygiene false in
/-- A `Fwd` proof whose leaves are the induction hypothesis `ih` or the helpers. -/
macro "fwd_ih" : tactic => `(tactic| repeat (any_goals first
  | with_reducible exact ih.placeDecl _ _ | with_reducible exact ih.fieldAt _ _ _ _
  | with_reducible exact ih.fieldDecl _ _ _ _ | with_reducible exact (ih.fieldDecl _ _ _ _).live
  | with_reducible exact ih.declCopy _ | with_reducible exact (ih.declCopy _).live
  | with_reducible exact ih.callDecl _ _ _ _ | with_reducible exact ih.closedTypeDecl _
  | with_reducible exact ih.sortOf _ | with_reducible exact ih.declSort _ _ _
  | with_reducible exact ih.declOf _ _ _ _ | with_reducible exact ih.typeDecl _ _ _ _ _ _
  | with_reducible exact ih.typePos _ _ _ _ | with_reducible exact ih.telescope _ _ _ _ _
  | with_reducible exact ih.valueDecl _ | with_reducible exact ih.valTypeDecl _
  | with_reducible exact ih.isPropV _ | with_reducible exact ih.fnClass _
  | with_reducible exact fwd_fieldIsProof _ | with_reducible exact fwd_fieldTermIsProp _ _
  | with_reducible exact fwd_ctorIsProof _ | with_reducible exact fwd_preFlags _ _
  | with_reducible exact fwd_refineDecl _ | with_reducible exact fwd_sealedSort _
  | assumption
  | (with_reducible refine ih.typeFnDecl _ _ _ _ _ _ _ ?_)
  | fwd_step))

theorem decideFwd_zero : DecideFwd 0 := by
  constructor <;> intros <;>
    first
    | (unfold placeDecl; (try dsimp only); fwd_go; done)
    | (unfold fieldAt; (try dsimp only); fwd_go; done)
    | (unfold fieldDecl; (try dsimp only); fwd_go; done)
    | (unfold declCopy; (try dsimp only); fwd_go; done)
    | (unfold callDecl; (try dsimp only); fwd_go; done)
    | (unfold closedTypeDecl; (try dsimp only); fwd_go; done)
    | (unfold sortOf; (try dsimp only); fwd_go; done)
    | (unfold declSort; (try dsimp only); fwd_go; done)
    | (unfold declOf; (try dsimp only); fwd_go; done)
    | (unfold typeDecl; (try dsimp only); fwd_go; done)
    | (unfold typeFnDecl; (try dsimp only); fwd_go; done)
    | (unfold typePos; (try dsimp only); fwd_go; done)
    | (unfold telescope; (try dsimp only); fwd_go; done)
    | (unfold valueDecl; (try dsimp only); fwd_go; done)
    | (unfold valTypeDecl; (try dsimp only); fwd_go; done)
    | (unfold isPropV; (try dsimp only); fwd_go; done)
    | (unfold fnClass; (try dsimp only); fwd_go; done)

set_option maxHeartbeats 4000000 in
theorem decideFwd_succ (n : Nat) (ih : DecideFwd n) : DecideFwd (n + 1) := by
  constructor
  · intro sc p; unfold placeDecl; (try dsimp only); fwd_ih
  · intro r n' c i; unfold fieldAt; (try dsimp only); fwd_ih
  · intro d args c i; unfold fieldDecl; (try dsimp only); fwd_ih
  · intro r; unfold declCopy; (try dsimp only); fwd_ih
  · intro F as sc ns; unfold callDecl; (try dsimp only); fwd_ih
  · intro T; unfold closedTypeDecl; (try dsimp only); fwd_ih
  · intro T; unfold sortOf; (try dsimp only); fwd_ih
  · intro sc ns T; unfold declSort; (try dsimp only); fwd_ih
  · intro chk sc ns t
    cases t <;> (unfold declOf; (try dsimp only); fwd_ih)
  · intro chk sc ns T vis tsc; unfold typeDecl; (try dsimp only); fwd_ih
  · intro F vis sc ns tsc as dflt hd; unfold typeFnDecl; (try dsimp only); fwd_ih
  · intro chk sc ns T; unfold typePos; (try dsimp only); fwd_ih
  · intro chk sc ns hs ds; unfold telescope; (try dsimp only); fwd_ih
  · intro v; unfold valueDecl; (try dsimp only); fwd_ih
  · intro T; unfold valTypeDecl; (try dsimp only); fwd_ih
  · intro T; unfold isPropV; (try dsimp only); fwd_ih
  · intro T; unfold fnClass; (try dsimp only); fwd_ih

/-- **The decision procedures simulate forward to larger tables**, every function the decisions
reach, at every fuel. -/
theorem decideFwd : ∀ n, DecideFwd n
  | 0 => decideFwd_zero
  | n + 1 => decideFwd_succ n (decideFwd n)

/-! ## D84's join set and [Id-typestate]'s -/

set_option hygiene false in
/-- Close the calls of the decisions' block left by a `fwd_go`, at any fuel. -/
macro "fwd_dec" : tactic => `(tactic| first
  | exact (decideFwd _).placeDecl _ _
  | exact (decideFwd _).declCopy _ |>.live
  | exact (decideFwd _).declOf _ _ _ _
  | exact fwd_preFlags _ _
  | exact fwd_lookupInd _)

theorem fwd_jdGrain (n : Nat) (m : Place) : Fwd LiveLe (jdGrain n m) := by
  unfold jdGrain; (try dsimp only); fwd_go
  all_goals fwd_dec

theorem fwd_jdFns (n : Nat) (sc : List DeclInfo) (t : Term) (acc : List Place) : Fwd LiveLe (jdFns n sc t acc) := by
  unfold jdFns; (try dsimp only); fwd_go
  all_goals fwd_dec

/-- `Decide.jdMoves`' mutual block. -/
structure JdFwd (n : Nat) : Prop where
  jdMoves : ∀ sc al t acc, Fwd LiveLe (jdMoves n sc al t acc)
  jdMovesList : ∀ sc al ts acc, Fwd LiveLe (jdMovesList n sc al ts acc)
  jdMatch : ∀ sc al t arms acc, Fwd LiveLe (jdMatch n sc al t arms acc)

set_option maxHeartbeats 4000000 in
theorem jdFwd : ∀ n, JdFwd n
  | 0 => ⟨fun _ _ _ _ => by unfold jdMoves; (try dsimp only); fwd_go,
      fun _ _ ts _ => by cases ts <;> (unfold jdMovesList; (try dsimp only); fwd_go),
      fun _ _ _ _ _ => by unfold jdMatch; (try dsimp only); fwd_go⟩
  | n + 1 => by
    have ih := jdFwd n
    refine ⟨fun sc al t acc => ?_, fun sc al ts acc => ?_, fun sc al t arms acc => ?_⟩
    · unfold jdMoves; (try dsimp only); fwd_go
      all_goals first
        | fwd_dec
        | exact ih.jdMoves _ _ _ _
        | exact ih.jdMovesList _ _ _ _
        | exact ih.jdMatch _ _ _ _ _
        | exact fwd_jdFns _ _ _ _
    · cases ts with
      | nil => unfold jdMovesList; (try dsimp only); fwd_go
      | cons t ts =>
        unfold jdMovesList; (try dsimp only); fwd_go
        all_goals first
          | exact ih.jdMoves _ _ _ _
          | exact ih.jdMovesList _ _ _ _
    · unfold jdMatch; (try dsimp only); fwd_go
      all_goals first
        | fwd_dec
        | exact ih.jdMoves _ _ _ _
        | exact fwd_jdFns _ _ _ _
        | exact fwd_jdGrain _ _

/-- `Decide.jdAssigns`' mutual block. -/
structure JaFwd (n : Nat) : Prop where
  jdAssigns : ∀ sc t acc, Fwd LiveLe (jdAssigns n sc t acc)
  jdAssignsList : ∀ sc ts acc, Fwd LiveLe (jdAssignsList n sc ts acc)

set_option maxHeartbeats 4000000 in
theorem jaFwd : ∀ n, JaFwd n
  | 0 => ⟨fun _ _ _ => by unfold jdAssigns; (try dsimp only); fwd_go,
      fun _ ts _ => by cases ts <;> (unfold jdAssignsList; (try dsimp only); fwd_go)⟩
  | n + 1 => by
    have ih := jaFwd n
    refine ⟨fun sc t acc => ?_, fun sc ts acc => ?_⟩
    · unfold jdAssigns; (try dsimp only); fwd_go
      all_goals first
        | fwd_dec
        | exact ih.jdAssigns _ _ _
        | exact ih.jdAssignsList _ _ _
    · cases ts with
      | nil => unfold jdAssignsList; (try dsimp only); fwd_go
      | cons t ts =>
        unfold jdAssignsList; (try dsimp only); fwd_go
        all_goals first
          | exact ih.jdAssigns _ _ _
          | exact ih.jdAssignsList _ _ _

theorem fwd_typeState (n : Nat) (t : Term) : Fwd LiveLe (typeState n t) := by
  unfold typeState; (try dsimp only); fwd_go
  all_goals first
    | fwd_dec
    | exact (jdFwd _).jdMoves _ _ _ _
    | exact (jaFwd _).jdAssigns _ _ _

/-! ## The transfer -/

theorem runs_fwd {α : Type} {x : M α} {s₁ s₂ : MState} (hx : FwdAt x s₁ s₂) {b : Nat} {a : α} {s₁' : MState}
    (h : Steps.Runs x s₁ b a s₁') : Steps.Runs x s₂ b a s₂ := by
  obtain ⟨L, f', l', e⟩ := runs_runAll h
  exact runs_of_runAll (hx _ _ _ _ _ _ e)

theorem tabLe_of_grows {st st' : MState} (hg : Steps.TablesGrow st st') : TabLe st st' :=
  ⟨hg.globals.symm, hg.inds.symm, fun σ d h => by
    have hσ : σ < st.absDecl.size := by
      rcases Nat.lt_or_ge σ st.absDecl.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h; cases h
    rw [hg.old σ hσ]; exact h⟩

theorem envTab_scopeState {st st' : MState} (hg : Steps.TablesGrow st st') (sc : List DeclInfo) :
    EnvTab (scopeState st sc) (scopeState st' sc) :=
  ⟨⟨(tabLe_of_grows hg).globals, (tabLe_of_grows hg).inds, (tabLe_of_grows hg).absDecl⟩, rfl⟩

/-- **(b) Alignment at a larger table is alignment at a smaller one** (`MachineMono.DecTab.back`):
each decision's successful run at the smaller tables is one at the larger, with the same answer. -/
theorem decTab_back {D : Decisions} {st st' : MState} (hd : Steps.DecTab D st') (hg : Steps.TablesGrow st st') :
    Steps.DecTab D st where
  flags := fun fuel sc t fl b _ h => hd.flags fuel sc t fl b _ (runs_fwd ((fwd_bind
      (fwd_withLive_true ((decideFwd fuel).declOf false [] [] t)) fun d =>
      fwd_bind (fwd_preFlags t d) fun _ => fwd_pure _).2 _ _ (envTab_scopeState hg sc)) h)
  placeDecl := fun fuel sc p d b _ h => hd.placeDecl fuel sc p d b _
    (runs_fwd ((fwd_withLive_true ((decideFwd fuel).placeDecl [] p)).2 _ _ (envTab_scopeState hg sc)) h)
  declOf := fun fuel sc t d b _ h => hd.declOf fuel sc t d b _
    (runs_fwd ((fwd_withLive_true ((decideFwd fuel).declOf false [] [] t)).2 _ _ (envTab_scopeState hg sc)) h)
  copy := fun fuel r c b _ h => hd.copy fuel r c b _
    (runs_fwd (((decideFwd fuel).declCopy r).2 _ _ (tabLe_of_grows hg)) h)
  piSort := fun fuel sc t l b _ h => hd.piSort fuel sc t l b _
    (runs_fwd ((fwd_withLive_true ((decideFwd fuel).sortOf _)).2 _ _ (envTab_scopeState hg sc)) h)
  joinMoves := fun fuel sc entry t ms b _ h => hd.joinMoves fuel sc entry t ms b _
    (runs_fwd ((fwd_withLive_true ((jdFwd fuel).jdMoves [] [] t entry)).2 _ _ (envTab_scopeState hg sc)) h)
  rePointed := fun fuel sc t ts b _ h => hd.rePointed fuel sc t ts b _
    (runs_fwd ((fwd_withLive_true (fwd_typeState fuel t)).2 _ _ (envTab_scopeState hg sc)) h)
  typeDecl := fun fuel sc T d b _ h => hd.typeDecl fuel sc T d b _
    (runs_fwd ((fwd_withLive_true ((decideFwd fuel).typeDecl false [] [] T [] [])).2 _ _ (envTab_scopeState hg sc)) h)

/-! ## The decisions at a checker state are the table's at its own readings -/

/-- `TabLe` and the same live readings (a state against `scopeState` at its own readings). -/
structure LiveEq (s₁ s₂ : MState) : Prop extends TabLe s₁ s₂ where
  live : ∀ i, liveVal s₁ i = liveVal s₂ i

theorem fwd_withLive_true' {α : Type} {x : M α} (hx : Fwd LiveLe x) : Fwd LiveEq (withLive true x) :=
  fwd_withLive true (fun _ _ h => ⟨⟨h.globals, h.inds, h.absDecl⟩, rfl, fun _ i => h.live i⟩) hx

theorem liveEq_scopeState (st : MState) : LiveEq st (scopeState st (topReadings st)) :=
  ⟨⟨rfl, rfl, fun _ _ h => h⟩, fun i => ((envRel_scopeState st).live i).symm⟩

/-- The machine's own reading of a term (`withLive true (declOf …)`, at a state the table is aligned
at) is the table's at the state's top readings. -/
theorem decTab_declOf_at {D : Decisions} {st st' : MState} {fuel : Nat} {t : Term} {d : DeclInfo} {b : Nat}
    (hd : Steps.DecTab D st) (h : Steps.Runs (withLive true (Ochr.declOf fuel false [] [] t)) st b d st') :
    D.declOf (topReadings st) t = d :=
  hd.declOf fuel _ t d b _
    (runs_fwd ((fwd_withLive_true' ((decideFwd fuel).declOf false [] [] t)).2 _ _ (liveEq_scopeState st)) h)

/-- The same for a place's reading (`withLive true (placeDecl …)`). -/
theorem decTab_placeDecl_at {D : Decisions} {st st' : MState} {fuel : Nat} {p : Place} {d : DeclInfo} {b : Nat}
    (hd : Steps.DecTab D st) (h : Steps.Runs (withLive true (Ochr.placeDecl fuel [] p)) st b d st') :
    D.placeDecl (topReadings st) p = d :=
  hd.placeDecl fuel _ p d b _
    (runs_fwd ((fwd_withLive_true' ((decideFwd fuel).placeDecl [] p)).2 _ _ (liveEq_scopeState st)) h)

end Ochr.Meaning.Steps.Machine
