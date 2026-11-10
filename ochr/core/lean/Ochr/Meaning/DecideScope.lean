import Ochr.Meaning.DecisionsInst

/-!
# Decisions read the state only through Σ, Δ, the caches and the top frame's readings

`DecisionsInst.lean` reads each decision in `scopeState st sc`: the checker state `st` with its
frames replaced by one frame of readings. The checker reads it in `st` itself. This file proves
the two agree when `sc` is the top frame's readings, which is what the restated `*_aligned`
theorems (`Steps/Decisions.lean`) use.

The proof is a simulation. `Sim R x`: run from `R`-related states, `x` gives the same value and
`R`-related final states, or a failure of the same layer, with the fuel and the log equal. The
monad's primitives respect any `R` (`sim_pure`, `sim_bind`, `sim_err`, `sim_exhausted`,
`sim_onFail`, loops, `mapM`, `allM`). The state's projections respect `EnvRel`, the relation
"equal but for the frames, which agree on what `liveDecl` reads". So every function the
decisions call respects `EnvRel`, by one induction on the fuel over `Decide.lean`'s mutual block
(`decideSim`: 17 fuel-recursive functions plus their helpers; a tactic `sim_ih` walks each body
with every match at reducible transparency).

## What is proved (no `sorry`)

`checkerDecisions_placeDecl`, `_declOf`, `_flags`, `_piSort`. At the checker state `st`, the
instance at the top frame's readings (`topReadings st`, which is `Steps.scopeOf_sstate`'s right-hand
side) gives exactly what the machine's own call gives at `st`, in the live form `Machine.lean` uses
(`withLive true (… [] …)`). So no live/explicit-scope bridge is needed: the `*_aligned`
statements should be stated in this live form.

## Not covered here (obligations)

* `copy` reads at `scopeState st []`, whose top frame is empty, so `EnvRel` does not relate it
  to `st`. `declCopy` never reads a frame, but that needs a second relation (or the instance
  reading `copy` at `scopeState st (topReadings st)`, a one-line change).
* `joinMoves` (`Decide.jdMoves`) and `rePointed` (`Decide.typeState`), added with main's D84, are
  outside the 17-function closure. They need their own conjuncts in `DecideSim`.
* Cross-state alignment (one `K.D` for a whole run, built at one state and used at later states
  of the same check) needs the caches to be consistent, and Δ's readings to be stable under
  refinement. For the readings: the branch `probe-valuedecl-stability` finds the flip of
  `valueDecl (.abs σ)` (a stuck type function's `.other`, the later Π-type's `.pi r`)
  unreachable. Typing rejects every consumer while the type is stuck ("not a function type"),
  and refinement keeps a concrete head.
* Fuel: the instance's fuel against the checker's (monotonicity, not proved).
-/

namespace Ochr.Meaning.DecideScope

open Ochr

abbrev Out (α : Type) := ((Except Exhausted (Except Fail (α × MState))) × Fuel) × Array LogEntry
def runAll {α : Type} (x : M α) (s : MState) (f : Fuel) (l : Array LogEntry) : Out α := x s f l

theorem runAll_bind {α β : Type} (x : M α) (k : α → M β) (s : MState) (f : Fuel) (l : Array LogEntry) :
    runAll (x >>= k) s f l = (match runAll x s f l with
      | ((.ok (.ok (a, s')), f'), l') => runAll (k a) s' f' l'
      | ((.ok (.error e), f'), l') => ((.ok (.error e), f'), l')
      | ((.error e, f'), l') => ((.error e, f'), l')) := by
  unfold runAll
  simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]
  generalize x s f l = o
  rcases o with ⟨⟨e, f'⟩, l'⟩
  rcases e with e | e
  · rfl
  · rcases e with e | ⟨a, s'⟩ <;> rfl

def OutRel {α : Type} (R : MState → MState → Prop) : Out α → Out α → Prop
  | ((.ok (.ok (a, s₁)), f₁), l₁), ((.ok (.ok (b, s₂)), f₂), l₂) => a = b ∧ R s₁ s₂ ∧ f₁ = f₂ ∧ l₁ = l₂
  | ((.ok (.error _), f₁), l₁), ((.ok (.error _), f₂), l₂) => f₁ = f₂ ∧ l₁ = l₂
  | ((.error _, f₁), l₁), ((.error _, f₂), l₂) => f₁ = f₂ ∧ l₁ = l₂
  | _, _ => False

def Sim (R : MState → MState → Prop) {α : Type} (x : M α) : Prop :=
  ∀ s₁ s₂ f l, R s₁ s₂ → OutRel R (runAll x s₁ f l) (runAll x s₂ f l)

variable {R : MState → MState → Prop}

theorem sim_bind {α β : Type} {x : M α} {k : α → M β} (hx : Sim R x) (hk : ∀ a, Sim R (k a)) :
    Sim R (x >>= k) := by
  intro s₁ s₂ f l h
  rw [runAll_bind, runAll_bind]
  have hr := hx s₁ s₂ f l h
  revert hr
  generalize runAll x s₁ f l = o₁
  generalize runAll x s₂ f l = o₂
  intro hr
  rcases o₁ with ⟨⟨e₁ | e₁ | ⟨a, s₁'⟩, f₁⟩, l₁⟩ <;> rcases o₂ with ⟨⟨e₂ | e₂ | ⟨b, s₂'⟩, f₂⟩, l₂⟩ <;>
    simp only [OutRel] at hr
  · exact hr
  · exact hr
  · obtain ⟨rfl, hs, rfl, rfl⟩ := hr
    exact hk a s₁' s₂' f₁ l₁ hs

theorem sim_err {α : Type} (m : String) : Sim R (err m : M α) := by
  intro s₁ s₂ f l _
  exact ⟨rfl, rfl⟩

theorem sim_exhausted {α : Type} (m : String) : Sim R (exhausted m : M α) := by
  intro s₁ s₂ f l _
  exact ⟨rfl, rfl⟩

theorem sim_pure {α : Type} (a : α) : Sim R (pure a : M α) := by
  intro s₁ s₂ f l h
  exact ⟨rfl, h, rfl, rfl⟩

theorem sim_get_proj {α β : Type} (g : MState → β) (hg : ∀ s₁ s₂, R s₁ s₂ → g s₁ = g s₂)
    (k : β → M α) (hk : ∀ b, Sim R (k b)) : Sim R (get >>= fun s => k (g s)) := by
  intro s₁ s₂ f l h
  show OutRel R (runAll (k (g s₁)) s₁ f l) (runAll (k (g s₂)) s₂ f l)
  rw [hg s₁ s₂ h]
  exact hk _ s₁ s₂ f l h

theorem sim_ite {α : Type} {c : Prop} {_ : Decidable c} {x y : M α} (hx : Sim R x) (hy : Sim R y) :
    Sim R (if c then x else y) := by
  split <;> assumption

theorem sim_dite {α : Type} {c : Prop} {_ : Decidable c} {x : c → M α} {y : ¬ c → M α}
    (hx : ∀ h, Sim R (x h)) (hy : ∀ h, Sim R (y h)) : Sim R (if h : c then x h else y h) := by
  split <;> rename_i h <;> first | exact hx h | exact hy h

theorem runAll_tryCatch {α : Type} (x : M α) (h : Fail → M α) (s : MState) (f : Fuel) (l : Array LogEntry) :
    runAll (tryCatch x h) s f l = (match runAll x s f l with
      | ((.ok (.error e), f'), l') => runAll (h e) s f' l'
      | o => o) := by
  unfold runAll
  simp only [tryCatch, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe,
    ExceptT.tryCatch, ExceptT.mk, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont]
  generalize x s f l = o
  rcases o with ⟨⟨e | e | ⟨a, s'⟩, f'⟩, l'⟩ <;> rfl

theorem sim_onFail {α : Type} {x : M α} {c : M Unit} (hx : Sim R x) (hc : Sim R c) :
    Sim R (onFail x c) := by
  intro s₁ s₂ f l h
  unfold onFail
  rw [runAll_tryCatch, runAll_tryCatch]
  have hr := hx s₁ s₂ f l h
  revert hr
  generalize runAll x s₁ f l = o₁
  generalize runAll x s₂ f l = o₂
  intro hr
  rcases o₁ with ⟨⟨e₁ | e₁ | ⟨a, s₁'⟩, f₁⟩, l₁⟩ <;> rcases o₂ with ⟨⟨e₂ | e₂ | ⟨b, s₂'⟩, f₂⟩, l₂⟩ <;>
    simp only [OutRel] at hr
  · exact hr
  · -- both Fail errors: the cleanup runs from the start states, then the error is rethrown
    obtain ⟨rfl, rfl⟩ := hr
    dsimp only
    rw [runAll_bind, runAll_bind]
    have hc' := hc s₁ s₂ f₁ l₁ h
    revert hc'
    generalize runAll c s₁ f₁ l₁ = c₁
    generalize runAll c s₂ f₁ l₁ = c₂
    intro hc'
    rcases c₁ with ⟨⟨d₁ | d₁ | ⟨u, t₁⟩, g₁⟩, m₁⟩ <;> rcases c₂ with ⟨⟨d₂ | d₂ | ⟨v, t₂⟩, g₂⟩, m₂⟩ <;>
      simp only [OutRel] at hc'
    · exact hc'
    · exact hc'
    · obtain ⟨_, _, rfl, rfl⟩ := hc'
      exact ⟨rfl, rfl⟩
  · exact hr

theorem sim_modify {g : MState → MState} (hg : ∀ s₁ s₂, R s₁ s₂ → R (g s₁) (g s₂)) : Sim R (modify g) := by
  intro s₁ s₂ f l h
  exact ⟨rfl, hg s₁ s₂ h, rfl, rfl⟩

theorem sim_forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Sim R (body a b)) : Sim R (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact sim_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact sim_bind (hb a b) (fun r => by cases r with
      | done b' => exact sim_pure b'
      | yield b' => exact ih b')

theorem sim_mapM {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a, Sim R (f a)) : Sim R (xs.mapM f) := by
  induction xs with
  | nil => exact sim_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact sim_bind (hf a) (fun b => sim_bind ih (fun bs => sim_pure _))

theorem sim_allM {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, Sim R (f a)) : Sim R (xs.allM f) := by
  induction xs with
  | nil => exact sim_pure true
  | cons a as ih =>
    unfold List.allM
    exact sim_bind (hf a) (fun b => by cases b <;> first | exact ih | exact sim_pure _)

theorem sim_map {α β : Type} (g : α → β) {x : M α} (hx : Sim R x) : Sim R (g <$> x) := by
  rw [map_eq_pure_bind]
  exact sim_bind hx fun a => sim_pure _

theorem sim_discard {α : Type} {x : M α} (hx : Sim R x) : Sim R (discard x) := by
  show Sim R (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact sim_map _ hx

/-! ## The relation: equal but for the frames, which agree on what `liveDecl` reads -/

/-- What `liveDecl i` reads: the top frame's binding `i` (innermost first) reading. -/
def liveVal (s : MState) (i : Nat) : DeclInfo :=
  let bs := s.env[s.env.size - 1]!.binds
  if i < bs.size then bs[bs.size - 1 - i]!.decl else .other

/-- Two states agree on everything a decision reads: equal but for the frames, whose top frame
has the same readings. -/
structure EnvRel (s₁ s₂ : MState) : Prop where
  rest : { s₁ with env := #[] } = { s₂ with env := #[] }
  live : ∀ i, liveVal s₁ i = liveVal s₂ i

theorem EnvRel.globals {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.globals = s₂.globals := by
  have := congrArg MState.globals h.rest; exact this
theorem EnvRel.inds {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.inds = s₂.inds := by
  have := congrArg MState.inds h.rest; exact this
theorem EnvRel.absTy {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.absTy = s₂.absTy := by
  have := congrArg MState.absTy h.rest; exact this
theorem EnvRel.constDecls {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.constDecls = s₂.constDecls := by
  have := congrArg MState.constDecls h.rest; exact this
theorem EnvRel.classCache {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.classCache = s₂.classCache := by
  have := congrArg MState.classCache h.rest; exact this
theorem EnvRel.liveScope {s₁ s₂ : MState} (h : EnvRel s₁ s₂) : s₁.liveScope = s₂.liveScope := by
  have := congrArg MState.liveScope h.rest; exact this

theorem EnvRel.setLive {s₁ s₂ : MState} (h : EnvRel s₁ s₂) (b : Bool) :
    EnvRel { s₁ with liveScope := b } { s₂ with liveScope := b } :=
  ⟨congrArg (fun s => { s with liveScope := b }) h.rest, h.live⟩

theorem EnvRel.consConst {s₁ s₂ : MState} (h : EnvRel s₁ s₂) (c : String × DeclInfo) :
    EnvRel { s₁ with constDecls := c :: s₁.constDecls } { s₂ with constDecls := c :: s₂.constDecls } := by
  refine ⟨?_, h.live⟩
  have := congrArg (fun s => { s with constDecls := c :: s.constDecls }) h.rest
  exact this

theorem EnvRel.consClass {s₁ s₂ : MState} (h : EnvRel s₁ s₂) (c : Value × Nat) :
    EnvRel { s₁ with classCache := c :: s₁.classCache } { s₂ with classCache := c :: s₂.classCache } := by
  refine ⟨?_, h.live⟩
  have := congrArg (fun s => { s with classCache := c :: s.classCache }) h.rest
  exact this

theorem sim_liveDecl (i : Nat) : Sim EnvRel (liveDecl i) := by
  intro s₁ s₂ f l h
  exact ⟨h.live i, h, rfl, rfl⟩

/-- A read of the whole state, by its continuation's behaviour on related states. -/
theorem sim_get_bind {R : MState → MState → Prop} {α : Type} {k : MState → M α}
    (hk : ∀ s₁ s₂, R s₁ s₂ → ∀ f l, OutRel R (runAll (k s₁) s₁ f l) (runAll (k s₂) s₂ f l)) :
    Sim R (get >>= k) := fun s₁ s₂ f l h => hk s₁ s₂ h f l

theorem sim_withLive {α : Type} (b : Bool) {x : M α} (hx : Sim EnvRel x) : Sim EnvRel (withLive b x) := by
  unfold withLive
  refine sim_get_bind fun s₁ s₂ h f l => ?_
  dsimp only
  rw [show s₁.liveScope = s₂.liveScope from h.liveScope]
  generalize s₂.liveScope = old
  refine (?_ : Sim EnvRel _) s₁ s₂ f l h
  refine sim_bind (sim_modify fun _ _ h => h.setLive b) fun _ => ?_
  refine sim_bind (sim_onFail hx (sim_modify fun _ _ h => h.setLive old)) fun r => ?_
  exact sim_bind (sim_modify fun _ _ h => h.setLive old) fun _ => sim_pure r

theorem sim_lookupInd (n : String) : Sim EnvRel (lookupInd n) :=
  sim_get_proj (R := EnvRel) (fun s => s.inds) (fun _ _ h => h.inds)
    (fun is => match List.find? (fun x => x.name == n) is with
      | some d => pure d
      | none => err (toString "unknown inductive type " ++ toString n))
    (fun is => by split <;> first | exact sim_pure _ | exact sim_err _)

theorem sim_lookupGlobal (n : String) : Sim EnvRel (lookupGlobal n) :=
  sim_get_proj (R := EnvRel) (fun s => s.globals) (fun _ _ h => h.globals)
    (fun gs => match List.find? (fun x => x.name == n) gs with
      | some g => pure g
      | none => err (toString "unknown constant " ++ toString n))
    (fun gs => by split <;> first | exact sim_pure _ | exact sim_err _)

theorem sim_absType (σ : Nat) : Sim EnvRel (absType σ) :=
  sim_get_proj (R := EnvRel) (fun s => s.absTy) (fun _ _ h => h.absTy)
    (fun ts => match ts[σ]? with
      | some T => pure T
      | none => err (toString "unknown abstract value σ" ++ toString σ))
    (fun ts => by split <;> first | exact sim_pure _ | exact sim_err _)

/-! ## Reading the state in a proof -/

set_option hygiene false in
/-- Start a proof about a read of the state: the two runs' states `s₁`, `s₂`, related by `h`. -/
macro "sim_read" : tactic => `(tactic| (refine sim_get_bind fun s₁ s₂ h f l => ?_; try dsimp only))

set_option hygiene false in
/-- Finish one: once the first run's reads are rewritten to the second's, the two runs are one
computation from related states. -/
macro "sim_close" : tactic => `(tactic| refine (?_ : Sim EnvRel _) s₁ s₂ f l h)

set_option hygiene false in
/-- One step of a simulation proof, by the shape of the computation: a primitive, a bind (at
reducible transparency, so that no named function is unfolded), a read of the state (its
projections rewritten from the first run's state to the second's), a modification of the
caches or of `liveScope`, `withLive`, a loop, a `mapM`/`allM`, or a branch. -/
macro "sim_step" : tactic => `(tactic| first
  | with_reducible exact sim_pure _
  | with_reducible exact sim_err _
  | with_reducible exact sim_exhausted _
  | with_reducible exact sim_liveDecl _
  | with_reducible exact sim_lookupInd _
  | with_reducible exact sim_lookupGlobal _
  | with_reducible exact sim_absType _
  | with_reducible exact sim_modify fun _ _ h => h.consConst _
  | with_reducible exact sim_modify fun _ _ h => h.consClass _
  | (with_reducible refine sim_get_bind fun s₁ s₂ h f l => ?_
     try dsimp only
     try simp only [EnvRel.globals h, EnvRel.inds h, EnvRel.absTy h, EnvRel.constDecls h,
       EnvRel.classCache h, EnvRel.liveScope h]
     sim_close)
  | (with_reducible refine sim_bind ?_ (fun _ => ?_))
  | (with_reducible refine sim_withLive _ ?_)
  | (with_reducible refine sim_map _ ?_)
  | (with_reducible refine sim_discard ?_)
  | (with_reducible refine sim_forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine sim_mapM _ (fun _ => ?_))
  | (with_reducible refine sim_allM _ (fun _ => ?_))
  | split
  | (dsimp only))

/-- A whole simulation proof, step by step; what is left is a call of a function of the
recursion, for the induction hypothesis. -/
macro "sim_go" : tactic => `(tactic| repeat (any_goals sim_step))

/-! ## The helpers outside the fuel recursion -/

theorem sim_fieldTermIsProp (d : IndDecl) (FT : Term) : Sim EnvRel (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp; sim_go

theorem sim_fieldIsProof (g : FieldRef) : Sim EnvRel (fieldIsProof g) := by
  unfold fieldIsProof; sim_go
  all_goals exact sim_fieldTermIsProp _ _

theorem sim_ctorIsProof (ty : String) : Sim EnvRel (ctorIsProof ty) := by
  unfold ctorIsProof; sim_go

theorem sim_preFlags (t : Term) (d : DeclInfo) : Sim EnvRel (preFlags t d) := by
  unfold preFlags; sim_go

theorem sim_refineDecl (d : DeclInfo) : Sim EnvRel (refineDecl d) := by
  unfold refineDecl; sim_go

theorem sim_sealedSort (t : Term) : Sim EnvRel (sealedSort? t) := by
  unfold sealedSort?; sim_go

/-! ## The fuel recursion -/

/-- Every function of `Decide.lean`'s mutual block the decisions reach respects `EnvRel`, at
`fuel`. -/
def DecideSim (fuel : Nat) : Prop :=
  (∀ sc p, Sim EnvRel (placeDecl fuel sc p)) ∧
  (∀ r n c i, Sim EnvRel (fieldAt fuel r n c i)) ∧
  (∀ d args c i, Sim EnvRel (fieldDecl fuel d args c i)) ∧
  (∀ r, Sim EnvRel (declCopy fuel r)) ∧
  (∀ F as sc ns, Sim EnvRel (callDecl fuel F as sc ns)) ∧
  (∀ T, Sim EnvRel (closedTypeDecl fuel T)) ∧
  (∀ T, Sim EnvRel (sortOf fuel T)) ∧
  (∀ sc ns T, Sim EnvRel (declSort fuel sc ns T)) ∧
  (∀ chk sc ns t, Sim EnvRel (declOf fuel chk sc ns t)) ∧
  (∀ chk sc ns T vis tsc, Sim EnvRel (typeDecl fuel chk sc ns T vis tsc)) ∧
  (∀ F vis sc ns tsc as dflt, Sim EnvRel dflt → Sim EnvRel (typeFnDecl fuel F vis sc ns tsc as dflt)) ∧
  (∀ chk sc ns T, Sim EnvRel (typePos fuel chk sc ns T)) ∧
  (∀ chk sc ns hs ds, Sim EnvRel (telescope fuel chk sc ns hs ds)) ∧
  (∀ v, Sim EnvRel (valueDecl fuel v)) ∧
  (∀ T, Sim EnvRel (valTypeDecl fuel T)) ∧
  (∀ T, Sim EnvRel (isPropV fuel T)) ∧
  (∀ T, Sim EnvRel (fnClass fuel T))

theorem decideSim_zero : DecideSim 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (unfold placeDecl; exact sim_exhausted _)
    | (unfold fieldAt; exact sim_exhausted _)
    | (unfold fieldDecl; exact sim_exhausted _)
    | (unfold declCopy; exact sim_exhausted _)
    | (unfold callDecl; exact sim_exhausted _)
    | (unfold closedTypeDecl; exact sim_exhausted _)
    | (unfold sortOf; exact sim_exhausted _)
    | (unfold declSort; exact sim_exhausted _)
    | (unfold declOf; exact sim_exhausted _)
    | (unfold typeDecl; exact sim_exhausted _)
    | (unfold typeFnDecl; exact sim_exhausted _)
    | (unfold typePos; exact sim_exhausted _)
    | (unfold telescope; exact sim_exhausted _)
    | (unfold valueDecl; exact sim_withLive _ (sim_exhausted _))
    | (unfold valTypeDecl; exact sim_withLive _ (sim_exhausted _))
    | (unfold isPropV; exact sim_exhausted _)
    | (unfold fnClass; exact sim_exhausted _)

set_option hygiene false in
/-- Name the seventeen induction hypotheses. -/
macro "intro_ih" : tactic => `(tactic| obtain ⟨ihP, ihFA, ihFD, ihDC, ihCD, ihCT, ihSO, ihDS, ihDO, ihTD, ihTF,
  ihTP, ihTel, ihVD, ihVT, ihPV, ihFC⟩ := ih)

set_option hygiene false in
/-- A simulation proof whose leaves are the induction hypotheses or the helpers above (every
match is at reducible transparency, so no recursive function is unfolded by unification). -/
macro "sim_ih" : tactic => `(tactic| repeat (any_goals first
  | with_reducible exact ihP _ _ | with_reducible exact ihFA _ _ _ _ | with_reducible exact ihFD _ _ _ _
  | with_reducible exact ihDC _ | with_reducible exact ihCD _ _ _ _
  | with_reducible exact ihCT _ | with_reducible exact ihSO _ | with_reducible exact ihDS _ _ _
  | with_reducible exact ihDO _ _ _ _ | with_reducible exact ihTD _ _ _ _ _ _
  | with_reducible exact ihTP _ _ _ _ | with_reducible exact ihTel _ _ _ _ _ | with_reducible exact ihVD _
  | with_reducible exact ihVT _ | with_reducible exact ihPV _ | with_reducible exact ihFC _
  | with_reducible exact sim_fieldIsProof _ | with_reducible exact sim_fieldTermIsProp _ _
  | with_reducible exact sim_ctorIsProof _
  | with_reducible exact sim_preFlags _ _ | with_reducible exact sim_refineDecl _
  | with_reducible exact sim_sealedSort _
  | assumption
  | with_reducible apply ihTF
  | sim_step))

set_option maxHeartbeats 2000000 in
theorem decideSim_succ (n : Nat) (ih : DecideSim n) : DecideSim (n + 1) := by
  intro_ih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc p; unfold placeDecl; (try dsimp only); sim_ih
  · intro r n' c i; unfold fieldAt; (try dsimp only); sim_ih
  · intro d args c i; unfold fieldDecl; (try dsimp only); sim_ih
  · intro r; unfold declCopy; (try dsimp only); sim_ih
  · intro F as sc ns; unfold callDecl; (try dsimp only); sim_ih
  · intro T; unfold closedTypeDecl; (try dsimp only); sim_ih
  · intro T; unfold sortOf; (try dsimp only); sim_ih
  · intro sc ns T; unfold declSort; (try dsimp only); sim_ih
  · intro chk sc ns t
    cases t <;> (unfold declOf; (try dsimp only); sim_ih)
  · intro chk sc ns T vis tsc; unfold typeDecl; (try dsimp only); sim_ih
  · intro F vis sc ns tsc as dflt hd; unfold typeFnDecl; (try dsimp only); sim_ih
  · intro chk sc ns T; unfold typePos; (try dsimp only); sim_ih
  · intro chk sc ns hs ds; unfold telescope; (try dsimp only); sim_ih
  · intro v; unfold valueDecl; (try dsimp only); sim_ih
  · intro T; unfold valTypeDecl; (try dsimp only); sim_ih
  · intro T; unfold isPropV; (try dsimp only); sim_ih
  · intro T; unfold fnClass; (try dsimp only); sim_ih

/-- **Decisions respect `EnvRel`**: every function the decisions reach, at every fuel. -/
theorem decideSim : ∀ fuel, DecideSim fuel
  | 0 => decideSim_zero
  | n + 1 => decideSim_succ n (decideSim n)

/-! ## The instance at the state's own readings is the checker -/

/-- `liveDecl`'s reading of a frame's bindings, as the reversed list of their readings. -/
theorem liveRead_eq (bs : Array Binding) (i : Nat) :
    (if i < bs.size then bs[bs.size - 1 - i]!.decl else .other) =
      (if h : i < ((bs.toList.map (·.decl)).reverse).length then ((bs.toList.map (·.decl)).reverse)[i] else .other) := by
  by_cases hi : i < bs.size
  · have hlen : i < ((bs.toList.map (·.decl)).reverse).length := by simpa using hi
    rw [if_pos hi, dif_pos hlen]
    rw [List.getElem_reverse, List.getElem_map]
    have hk : bs.size - 1 - i < bs.size := by omega
    rw [getElem!_pos bs (bs.size - 1 - i) hk]
    simp
  · have hlen : ¬ i < ((bs.toList.map (·.decl)).reverse).length := by simpa using hi
    rw [if_neg hi, dif_neg hlen]

/-- The top frame's readings, innermost first (the run's `scopeOf` of `MState.sstate`,
`Steps.scopeOf_sstate`). -/
def topReadings (st : MState) : List DeclInfo :=
  ((st.env.back?.map (·.binds.toList.map (·.decl))).getD []).reverse

theorem liveVal_eq (s : MState) (i : Nat) :
    liveVal s i = (if h : i < (topReadings s).length then (topReadings s)[i] else .other) := by
  unfold liveVal
  rw [liveRead_eq]
  have : (s.env[s.env.size - 1]!.binds.toList.map (·.decl)) =
      (s.env.back?.map (·.binds.toList.map (·.decl))).getD [] := by
    by_cases he : s.env.size = 0
    · have hb : s.env.back? = none := by simp [Array.back?, he]
      rw [hb]
      have : s.env[s.env.size - 1]! = default := by
        rw [getElem!_neg]; omega
      rw [this]
      rfl
    · have hk : s.env.size - 1 < s.env.size := by omega
      rw [getElem!_pos s.env (s.env.size - 1) hk]
      simp [Array.back?, hk]
  unfold topReadings
  rw [this]

theorem liveVal_scopeState (st : MState) (sc : List DeclInfo) (i : Nat) :
    liveVal (scopeState st sc) i = (if h : i < sc.length then sc[i] else .other) := by
  unfold liveVal
  rw [liveRead_eq]
  have : (((scopeState st sc).env[(scopeState st sc).env.size - 1]!).binds.toList.map (·.decl)) = sc.reverse := by
    show ((sc.reverse.map fun d => ({ hint := ⟨"_"⟩, ty := none, val := .bot, decl := d } : Binding)).toArray.toList.map (·.decl)) = _
    simp only [List.map_map, List.map_reverse]
    congr 1
    induction sc with
    | nil => rfl
    | cons d ds ih => simp only [List.map_cons, Function.comp]; rw [ih]
  rw [this, List.reverse_reverse]

/-- The scope state at the top frame's readings agrees with the state itself. -/
theorem envRel_scopeState (st : MState) : EnvRel (scopeState st (topReadings st)) st :=
  ⟨rfl, fun i => by rw [liveVal_scopeState, liveVal_eq]⟩

theorem runMachine_fst {α : Type} (x : M α) (s : MState) (fuel : Nat) :
    (runMachine x s fuel).1 = (match runAll x s ⟨fuel⟩ #[] with
      | ((.error e, _), _) => Outcome.exhausted e.msg
      | ((.ok (.error f), _), _) => .fail f
      | ((.ok (.ok (a, st')), _), _) => .ok a st') := by
  unfold runMachine runAll
  simp only [StateT.run, ExceptT.run]
  generalize x s ⟨fuel⟩ #[] = o
  rcases o with ⟨⟨e | e | ⟨a, s'⟩, f'⟩, l'⟩ <;> rfl

/-- A decision that respects `EnvRel` reads the same in related states. -/
theorem readDecision_congr {α : Type} {x : M α} (hx : Sim EnvRel x) {s₁ s₂ : MState} (h : EnvRel s₁ s₂)
    (fuel : Nat) (dflt : α) : readDecision s₁ fuel dflt x = readDecision s₂ fuel dflt x := by
  unfold readDecision
  rw [runMachine_fst, runMachine_fst]
  have hr := hx s₁ s₂ ⟨fuel⟩ #[] h
  revert hr
  generalize runAll x s₁ ⟨fuel⟩ #[] = o₁
  generalize runAll x s₂ ⟨fuel⟩ #[] = o₂
  intro hr
  rcases o₁ with ⟨⟨e₁ | e₁ | ⟨a, s₁'⟩, f₁⟩, l₁⟩ <;> rcases o₂ with ⟨⟨e₂ | e₂ | ⟨b, s₂'⟩, f₂⟩, l₂⟩ <;>
    simp only [OutRel] at hr
  · rfl
  · rfl
  · obtain ⟨rfl, -, -, -⟩ := hr; rfl

section
variable (st : MState) (fuel : Nat)

/-- **`placeDecl` is aligned at the checker's state**: the instance at the top frame's readings
gives what the checker's own call (`Machine.copyRead`'s) gives at `st`. -/
theorem checkerDecisions_placeDecl (p : Place) :
    (checkerDecisions st fuel).placeDecl (topReadings st) p =
      readDecision st fuel .other (withLive true (Ochr.placeDecl fuel [] p)) :=
  readDecision_congr (sim_withLive _ ((decideSim fuel).1 _ _)) (envRel_scopeState st) _ _

/-- `declOf` likewise (`Machine.evalAt`, `letIn`). -/
theorem checkerDecisions_declOf (t : Term) :
    (checkerDecisions st fuel).declOf (topReadings st) t =
      readDecision st fuel .other (withLive true (Ochr.declOf fuel false [] [] t)) :=
  readDecision_congr (sim_withLive _ ((decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _)) (envRel_scopeState st) _ _

/-- `flags` likewise (`Machine.evalAt`'s pre-pass). -/
theorem checkerDecisions_flags (t : Term) :
    (checkerDecisions st fuel).flags (topReadings st) t =
      readDecision st fuel (false, false) (do
        let d ← withLive true (Ochr.declOf fuel false [] [] t)
        pure ((← preFlags t d).getD (false, false))) :=
  readDecision_congr
    (sim_bind (sim_withLive _ ((decideSim fuel).2.2.2.2.2.2.2.2.1 _ _ _ _)) fun d =>
      sim_bind (sim_preFlags t d) fun _ => sim_pure _)
    (envRel_scopeState st) _ _

/-- `piSort` likewise, against `Decide.sortOf` of the uncaptured Π-term (the capture-scope
difference to the machine's `sortOf (tPi cs t' rd)` is the separate obligation of
`DecisionsInst.lean`). -/
theorem checkerDecisions_piSort (t : Term) :
    (checkerDecisions st fuel).piSort (topReadings st) t =
      readDecision st fuel 1 (withLive true (sortOf fuel (.tPi [] t []))) :=
  readDecision_congr (sim_withLive _ ((decideSim fuel).2.2.2.2.2.2.1 _)) (envRel_scopeState st) _ _

end

end Ochr.Meaning.DecideScope
