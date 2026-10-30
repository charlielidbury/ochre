import Lean.Elab.Tactic
import Ochr.StabilityDecide

/-!
# Refinement keeps the signature

Every decision in `Decide.lean` that reads declarations reads them from the signature, the
state's inductive types and globals. For those decisions to commute with refinement, a
refinement must leave the signature as it was. Nothing in the machine writes either field (only
`Check.lean` does, between definitions), but a refinement re-runs sealed programs, compares
values and computes field types, so the fact has to be shown of every function a refinement
can reach. This file does that: `SigPres x` says a successful run of `x` ends with the
signature it started with, and `onState_sig` is the result.

Computations that run arbitrary code (a sealed program's re-run, a private copy, a statement)
restore the state they saved, signature included, so they keep the signature without anything
being known about the code they run (`EndsAt`, `sigPres_privately`, `sigPres_inStatement`). The
rest is a fuel induction over what a refinement reaches: the declared-type readers of
`Decide.lean` (`DecSP`) and, in `Machine.lean`, substitution, re-normalisation, conversion,
`Eq` and field types (`RefSP`). The `sp` tactic takes a `do` block apart into its primitives
(join points once each, `sp_let`), using the induction hypotheses in scope (`sp_assumption`)
and the lemmas registered for it (`sp_ext`).

The last part states what this proves of `DecisionsCommute` and gives `stability` with those
fields filled in and the others `sorry`, each saying what it needs.
-/

namespace Ochr.Stability
open Ochr

theorem step_tryCatch {α} (x : M α) (h : Fail → M α) Ω fl lg :
    step (tryCatch x h) Ω fl lg =
      match step x Ω fl lg with
      | ((.ok (.error e), fl'), lg') => step (h e) Ω fl' lg'
      | r => r := by
  simp only [step, tryCatch, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
    ExceptT.tryCatch, StateT.run, ExceptT.run, ExceptT.mk, bind, ExceptT.bind,
    ExceptT.bindCont, StateT.bind, pure, ExceptT.pure]
  rcases x Ω fl lg with ⟨⟨r, fl'⟩, lg'⟩
  rcases r with e | (e | ⟨a, Ω'⟩) <;> rfl

theorem SigAgree.refl (Ω : MState) : SigAgree Ω Ω := ⟨rfl, rfl⟩

theorem SigAgree.trans {Ω₁ Ω₂ Ω₃ : MState} (h₁ : SigAgree Ω₁ Ω₂) (h₂ : SigAgree Ω₂ Ω₃) : SigAgree Ω₁ Ω₃ :=
  ⟨h₁.inds.trans h₂.inds, h₁.globals.trans h₂.globals⟩

/-- A successful run of `x` ends with the signature it started with. -/
def SigPres {α : Type} (x : M α) : Prop :=
  ∀ Ω fl lg a Ω' fl' lg', step x Ω fl lg = ((.ok (.ok (a, Ω')), fl'), lg') → SigAgree Ω Ω'

theorem SigPres.pure {α} (a : α) : SigPres (pure a : M α) := by
  intro Ω fl lg b Ω' fl' lg' h
  simp only [step_pure, Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ SigAgree.refl Ω

theorem SigPres.bind {α β} {x : M α} {f : α → M β} (hx : SigPres x) (hf : ∀ a, SigPres (f a)) :
    SigPres (x >>= f) := by
  intro Ω fl lg b Ω' fl' lg' hs
  rw [step_bind] at hs
  revert hs
  rcases hr : step x Ω fl lg with ⟨⟨r, fl₁⟩, lg₁⟩
  rcases r with e | (e | ⟨a, Ω₁⟩) <;> simp only [cont] <;> intro hs
  · cases hs
  · cases hs
  · exact (hx Ω fl lg a Ω₁ fl₁ lg₁ hr).trans (hf a Ω₁ fl₁ lg₁ b Ω' fl' lg' hs)

theorem SigPres.get : SigPres (get : M MState) := by
  intro Ω fl lg a Ω' fl' lg' h
  simp only [step_get, Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ SigAgree.refl Ω

theorem SigPres.modify (g : MState → MState) (hg : ∀ s, SigAgree s (g s)) : SigPres (modify g : M Unit) := by
  intro Ω fl lg a Ω' fl' lg' h
  simp only [step_modify, Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ hg Ω

theorem SigPres.exhausted {α} (m : String) : SigPres (exhausted m : M α) := by
  intro Ω fl lg a Ω' fl' lg' h; cases h

theorem SigPres.err {α} (m : String) : SigPres (err m : M α) := by
  intro Ω fl lg a Ω' fl' lg' h; cases h

theorem SigPres.throw {α} (e : Fail) : SigPres (throw e : M α) := by
  intro Ω fl lg a Ω' fl' lg' h; cases h

theorem SigPres.ite {α} (c : Prop) [Decidable c] {x y : M α} (hx : SigPres x) (hy : SigPres y) :
    SigPres (if c then x else y) := by
  by_cases h : c <;> simp [h, hx, hy]

theorem SigPres.tryCatch {α} {x : M α} {h : Fail → M α} (hx : SigPres x) (hh : ∀ e, SigPres (h e)) :
    SigPres (tryCatch x h) := by
  intro Ω fl lg a Ω' fl' lg' hs
  rw [step_tryCatch] at hs
  revert hs
  rcases hr : step x Ω fl lg with ⟨⟨r, fl₁⟩, lg₁⟩
  rcases r with e | (e | ⟨b, Ω₁⟩) <;> simp only <;> intro hs
  · cases hs
  · exact hh e Ω fl₁ lg₁ a Ω' fl' lg' hs
  · rw [hs] at hr; exact hx Ω fl lg a Ω' fl' lg' hr

/-- `onFail`: the cleanup runs only on the way to rethrowing, so only `x`'s success matters. -/
theorem SigPres.onFail {α} {x : M α} (c : M Unit) (hx : SigPres x) : SigPres (onFail x c) := by
  unfold Ochr.onFail
  refine SigPres.tryCatch hx fun e => ?_
  intro Ω fl lg a Ω' fl' lg' hs
  rw [step_bind] at hs
  revert hs
  rcases step c Ω fl lg with ⟨⟨r, fl₁⟩, lg₁⟩
  rcases r with e' | (e' | ⟨b, Ω₁⟩) <;> simp only [cont, step_throwFail] <;> intro hs <;> cases hs

theorem SigPres.catchStuck {α} {x : M α} {h : Option Value → M α} (hx : SigPres x) (hh : ∀ v, SigPres (h v)) :
    SigPres (catchStuck x h) := by
  unfold Ochr.catchStuck tryCatchThe
  refine SigPres.tryCatch hx fun e => ?_
  split
  · exact hh _
  · exact SigPres.throw _

theorem SigPres.getFuel : SigPres (getThe Fuel : M Fuel) := by
  intro Ω fl lg a Ω' fl' lg' h
  have : step (getThe Fuel : M Fuel) Ω fl lg = ((.ok (.ok (fl, Ω)), fl), lg) := rfl
  rw [this] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ SigAgree.refl Ω

theorem SigPres.modifyFuel (g : Fuel → Fuel) : SigPres (modifyThe Fuel g : M Unit) := by
  intro Ω fl lg a Ω' fl' lg' h
  have : step (modifyThe Fuel g : M Unit) Ω fl lg = ((.ok (.ok ((), Ω)), g fl), lg) := rfl
  rw [this] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ SigAgree.refl Ω

theorem SigPres.modifyLog (g : Array LogEntry → Array LogEntry) : SigPres (modifyThe (Array LogEntry) g : M Unit) := by
  intro Ω fl lg a Ω' fl' lg' h
  have : step (modifyThe (Array LogEntry) g : M Unit) Ω fl lg = ((.ok (.ok ((), Ω)), fl), g lg) := rfl
  rw [this] at h; simp only [Prod.mk.injEq, Except.ok.injEq] at h
  exact h.1.1.2 ▸ SigAgree.refl Ω

theorem SigPres.forIn_list {α β} (l : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, SigPres (f a b)) : SigPres (forIn l b f) := by
  induction l generalizing b with
  | nil => exact SigPres.pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    exact SigPres.bind (hf a b) fun r => by
      cases r with
      | done b' => exact SigPres.pure b'
      | yield b' => exact ih b'

theorem SigPres.forIn_range {β} (r : Std.Legacy.Range) (b : β) (f : Nat → β → M (ForInStep β))
    (hf : ∀ a b, SigPres (f a b)) : SigPres (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact SigPres.forIn_list _ b f hf

theorem SigPres.mapM {α β} (f : α → M β) (hf : ∀ a, SigPres (f a)) : ∀ l : List α, SigPres (l.mapM f)
  | [] => by simpa using SigPres.pure ([] : List β)
  | a :: l => by
    rw [List.mapM_cons]
    exact SigPres.bind (hf a) fun _ => SigPres.bind (SigPres.mapM f hf l) fun _ => SigPres.pure _

theorem SigPres.forM {α} (f : α → M PUnit) (hf : ∀ a, SigPres (f a)) : ∀ l : List α, SigPres (l.forM f)
  | [] => by simpa [List.forM] using SigPres.pure PUnit.unit
  | a :: l => by
    unfold List.forM
    exact SigPres.bind (hf a) fun _ => SigPres.forM f hf l

theorem SigPres.foldlM {α β} (f : β → α → M β) (hf : ∀ b a, SigPres (f b a)) : ∀ (l : List α) (b : β),
    SigPres (l.foldlM f b)
  | [], b => by simpa [List.foldlM] using SigPres.pure b
  | a :: l, b => by
    simp only [List.foldlM]
    exact SigPres.bind (hf b a) fun b' => SigPres.foldlM f hf l b'

theorem SigPres.anyM {α} (p : α → M Bool) (hp : ∀ a, SigPres (p a)) : ∀ l : List α, SigPres (l.anyM p)
  | [] => by simpa [List.anyM] using SigPres.pure false
  | a :: l => by
    simp only [List.anyM]
    exact SigPres.bind (hp a) fun b => by
      cases b
      · exact SigPres.anyM p hp l
      · exact SigPres.pure true

theorem SigPres.allM {α} (p : α → M Bool) (hp : ∀ a, SigPres (p a)) : ∀ l : List α, SigPres (l.allM p)
  | [] => by simpa [List.allM] using SigPres.pure true
  | a :: l => by
    simp only [List.allM]
    exact SigPres.bind (hp a) fun b => by
      cases b
      · exact SigPres.pure false
      · exact SigPres.allM p hp l

theorem SigPres.map {α β} (f : α → β) {x : M α} (hx : SigPres x) : SigPres (f <$> x) := by
  rw [map_eq_pure_bind]; exact SigPres.bind hx fun _ => SigPres.pure _

theorem SigPres.discard {α} {x : M α} (hx : SigPres x) : SigPres (discard x) := by
  unfold Functor.discard; rw [Functor.mapConst]; exact SigPres.map _ hx

theorem SigPres.set_get {β} (g : MState → MState) (k : MState → M β) (hg : ∀ s, SigAgree s (g s))
    (hk : ∀ s, SigPres (k s)) : SigPres (MonadState.get >>= fun s => set (g s) >>= fun _ => k s) := by
  intro Ω fl lg a Ω' fl' lg' h
  rw [step_bind] at h
  simp only [step_get, cont] at h
  have hset : step (set (g Ω) : M PUnit) Ω fl lg = ((.ok (.ok (PUnit.unit, g Ω)), fl), lg) := rfl
  rw [step_bind, hset] at h
  simp only [cont] at h
  exact (hg Ω).trans (hk Ω (g Ω) fl lg a Ω' fl' lg' h)

attribute [irreducible] SigPres

/-- A `do` block's join point: prove the continuation once for any join point that keeps the
signature, rather than inlining the join point into every branch. -/
theorem SigPres.jp {α β γ : Type} (j : γ → M β) (k : (γ → M β) → M α) (hj : ∀ c, SigPres (j c))
    (hk : ∀ j' : γ → M β, (∀ c, SigPres (j' c)) → SigPres (k j')) : SigPres (k j) :=
  hk j hj

open Lean Meta Elab Tactic in
/-- `SigPres (let x := v; b)`: a join point (`v : γ → M β`) by `SigPres.jp`, anything else by
substituting it. -/
elab "sp_let" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless ty.isAppOfArity ``SigPres 2 do throwError "not a SigPres goal"
  let e := ty.appArg!.cleanupAnnotations
  let (n, t, v, b) ← match e with
    | .letE n t v b _ => pure (n, t, v, b)
    | _ => throwError "not a let"
  let isJp ← forallTelescope t fun xs r => pure (xs.size == 1 && r.cleanupAnnotations.isAppOf ``Ochr.M)
  if isJp then
    let k := Expr.lam n t b .default
    let pf ← mkAppOptM ``SigPres.jp #[none, none, none, some v, some k]
    let gs ← g.apply pf
    replaceMainGoal gs
  else
    replaceMainGoal [← g.replaceTargetDefEq (mkApp ty.appFn! (b.instantiate1 v))]

/-- Lemmas `sp` may use, registered with `macro_rules | `(tactic| sp_ext) => ...`. -/
syntax "sp_ext" : tactic
macro_rules | `(tactic| sp_ext) => `(tactic| fail "no registered SigPres lemma applies")

open Lean Meta Elab Tactic in
/-- Apply a hypothesis whose conclusion is a `SigPres` (an induction hypothesis), reducibly. -/
elab "sp_assumption" : tactic => withMainContext do
  let g ← getMainGoal
  unless (← instantiateMVars (← g.getType)).cleanupAnnotations.isAppOf ``SigPres do
    throwError "not a SigPres goal"
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    if let some gs ← observing? (withReducible (g.apply d.toExpr)) then
      replaceMainGoal gs
      return
  throwError "no SigPres hypothesis applies"

/-- The generic step for `SigPres`: unfold a `do` block into its primitives. -/
macro "sp" : tactic => `(tactic| repeat' (first
  | (intro)
  | sp_let | sp_assumption | sp_ext
  | (with_reducible apply SigPres.map) | (with_reducible apply SigPres.discard)
  | (with_reducible apply SigPres.set_get)
  | (with_reducible apply SigPres.bind)
  | (with_reducible exact SigPres.pure _) | (with_reducible exact SigPres.get)
  | (with_reducible exact SigPres.err _) | (with_reducible exact SigPres.exhausted _)
  | (with_reducible exact SigPres.throw _)
  | (with_reducible exact SigPres.getFuel) | (with_reducible exact SigPres.modifyFuel _)
  | (with_reducible exact SigPres.modifyLog _)
  | (with_reducible exact SigPres.modify _ (fun _ => ⟨rfl, rfl⟩))
  | (with_reducible apply SigPres.onFail) | (with_reducible apply SigPres.catchStuck)
  | (with_reducible apply SigPres.tryCatch)
  | (with_reducible apply SigPres.forIn_list) | (with_reducible apply SigPres.forIn_range)
  | (with_reducible apply SigPres.mapM) | (with_reducible apply SigPres.forM)
  | (with_reducible apply SigPres.anyM) | (with_reducible apply SigPres.allM)
  | (with_reducible apply SigPres.foldlM)
  | (exact ⟨rfl, rfl⟩)
  | (simp (config := { zeta := false }) only [])
  | split))

theorem sigPres_topIdx : SigPres topIdx := by unfold topIdx; sp
theorem sigPres_modifyFrame (f : Nat) (g : Frame → Frame) : SigPres (modifyFrame f g) := by unfold modifyFrame; sp
theorem sigPres_pushFrame (fr : Frame) : SigPres (pushFrame fr) := by unfold pushFrame; sp
theorem sigPres_pushBind (h : Hint) (ty : Option Value) (v : Value) (p : Bool) (d : DeclInfo) :
    SigPres (pushBind h ty v p d) := by
  unfold pushBind; exact SigPres.bind sigPres_topIdx fun _ => sigPres_modifyFrame _ _
theorem sigPres_popFrameRaw : SigPres popFrameRaw := by
  unfold SigPres popFrameRaw
  intro Ω fl lg a Ω' fl' lg' h
  rw [step_bind] at h
  simp only [step_get, cont] at h
  split at h
  · have hset : step (set { Ω with env := Ω.env.pop } : M PUnit) Ω fl lg =
        ((.ok (.ok (PUnit.unit, { Ω with env := Ω.env.pop })), fl), lg) := rfl
    rw [step_bind, hset] at h
    simp only [cont, step_pure, Prod.mk.injEq, Except.ok.injEq] at h
    exact h.1.1.2 ▸ ⟨rfl, rfl⟩
  · cases h
theorem sigPres_getAt (p : Pos) : SigPres (getAt p) := by unfold getAt; sp
theorem sigPres_setAt (p : Pos) (v : Value) : SigPres (setAt p v) := by
  unfold setAt; split <;> exact sigPres_modifyFrame _ _
theorem sigPres_tyAt (p : Pos) : SigPres (tyAt p) := by unfold tyAt; sp
theorem sigPres_freshLoan : SigPres freshLoan := by unfold freshLoan; sp
theorem sigPres_freshAbs (T : Value) : SigPres (freshAbs T) := by unfold freshAbs; sp
theorem sigPres_absType (σ : Nat) : SigPres (absType σ) := by unfold absType; sp
theorem sigPres_lookupInd (n : String) : SigPres (lookupInd n) := by unfold lookupInd; sp
theorem sigPres_lookupGlobal (n : String) : SigPres (lookupGlobal n) := by unfold lookupGlobal; sp
theorem sigPres_fuelLeft : SigPres fuelLeft := by unfold fuelLeft; sp
theorem sigPres_fire (r : Rule) (m : Unit → String) : SigPres (fire r m) := by unfold fire; sp
theorem sigPres_withErased {α} (x : M α) (hx : SigPres x) : SigPres (withErased x) := by
  unfold withErased
  exact SigPres.bind (SigPres.modify _ fun _ => ⟨rfl, rfl⟩) fun _ => SigPres.bind (SigPres.onFail _ hx) fun _ =>
    SigPres.bind (SigPres.modify _ fun _ => ⟨rfl, rfl⟩) fun _ => SigPres.pure _
theorem sigPres_withLive {α} (b : Bool) (x : M α) (hx : SigPres x) : SigPres (withLive b x) := by
  unfold withLive
  exact SigPres.bind SigPres.get fun _ => SigPres.bind (SigPres.modify _ fun _ => ⟨rfl, rfl⟩) fun _ =>
    SigPres.bind (SigPres.onFail _ hx) fun _ => SigPres.bind (SigPres.modify _ fun _ => ⟨rfl, rfl⟩) fun _ => SigPres.pure _

open Lean Meta Elab Tactic in
/-- Unfold the private definitions in the goal (`onCopy`, behind `privately`). -/
elab "delta_private" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← deltaExpand (← instantiateMVars (← g.getType)) isPrivateName
  replaceMainGoal [← g.replaceTargetDefEq t]


theorem ReadsSig.sigPres {α} {x : M α} (h : ReadsSig x) : SigPres x := by
  obtain ⟨f, hf⟩ := h
  unfold SigPres
  intro Ω fl lg a Ω' fl' lg' hs
  rw [hf] at hs
  unfold sigRes at hs
  split at hs
  · simp only [Prod.mk.injEq, Except.ok.injEq] at hs; exact hs.1.1.2 ▸ SigAgree.refl Ω
  · cases hs

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_topIdx)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_modifyFrame)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_pushFrame)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_pushBind)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_popFrameRaw)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_getAt)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_setAt)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_tyAt)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_freshLoan)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_freshAbs)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_absType)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_lookupInd)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_lookupGlobal)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_fuelLeft)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_fire)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_withErased)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_withLive)

theorem sigPres_absOf (T : Value) : SigPres (absOf T) := by unfold absOf; sp
theorem sigPres_sealedSort? (t : Term) : SigPres (sealedSort? t) := by unfold sealedSort?; sp
theorem sigPres_liveDecl (i : Nat) : SigPres (liveDecl i) := by unfold liveDecl; sp
theorem sigPres_ctorIsProof (ty : String) : SigPres (ctorIsProof ty) := (readsSig_ctorIsProof ty).sigPres
theorem sigPres_fieldIsProof (g : FieldRef) : SigPres (fieldIsProof g) := (readsSig_fieldIsProof g).sigPres
theorem sigPres_fieldTermIsProp (d : IndDecl) (FT : Term) : SigPres (fieldTermIsProp d FT) :=
  (readsSig_fieldTermIsProp d FT).sigPres
theorem sigPres_refineDecl (d : DeclInfo) : SigPres (refineDecl d) := (readsSig_refineDecl d).sigPres

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_absOf)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_sealedSort?)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_liveDecl)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_ctorIsProof)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_fieldIsProof)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_fieldTermIsProp)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_refineDecl)

theorem sigPres_placeDecl (sc : List DeclInfo) : (p : Place) → SigPres (placeDecl sc p)
  | .deref q => by unfold placeDecl; have := sigPres_placeDecl sc q; sp
  | .var _ | .fst _ | .snd _ | .field _ _ => by unfold placeDecl; sp

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_placeDecl)

/-- The declared-type readers keep the signature, at fuel `n`. -/
structure DecSP (n : Nat) : Prop where
  sortOf? : ∀ T, SigPres (sortOf? n T)
  sortOf : ∀ T, SigPres (sortOf n T)
  declSort : ∀ sc ns T, SigPres (declSort n sc ns T)
  declOf : ∀ chk sc ns t, SigPres (declOf n chk sc ns t)
  typeDecl : ∀ chk sc ns T vis tsc, SigPres (typeDecl n chk sc ns T vis tsc)
  typeFnDecl : ∀ F vis sc ns tsc as dflt, SigPres dflt → SigPres (typeFnDecl n F vis sc ns tsc as dflt)
  typePos : ∀ chk sc ns T, SigPres (typePos n chk sc ns T)
  telescope : ∀ chk sc ns hs ds, SigPres (telescope n chk sc ns hs ds)
  valueDecl : ∀ v, SigPres (valueDecl n v)
  valTypeDecl : ∀ T, SigPres (valTypeDecl n T)
  isPropV : ∀ T, SigPres (isPropV n T)
  fnClass : ∀ P, SigPres (fnClass n P)
  kindOf : ∀ B, SigPres (kindOf n B)
  declKind : ∀ P, SigPres (declKind n P)

theorem decSP_zero : DecSP 0 := by
  constructor <;> intros <;>
    first
    | (unfold sortOf?; sp) | (unfold sortOf; sp) | (unfold declSort; sp) | (unfold declOf; sp)
    | (unfold typeDecl; sp) | (unfold typeFnDecl; sp) | (unfold typePos; sp) | (unfold telescope; sp)
    | (unfold valueDecl; sp) | (unfold valTypeDecl; sp) | (unfold isPropV; sp) | (unfold fnClass; sp)
    | (unfold kindOf; sp) | (unfold declKind; sp)

theorem decSP_succ (n : Nat) (ih : DecSP n) : DecSP (n + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ih
  constructor
  · intro T; unfold sortOf?; sp
  · intro T; unfold sortOf; sp
  · intro sc ns T; unfold declSort; sp
  · intro chk sc ns t; unfold declOf; sp
  · intro chk sc ns T vis tsc; unfold typeDecl; sp
  · intro F vis sc ns tsc as dflt hd; unfold typeFnDecl; sp
  · intro chk sc ns T; unfold typePos; sp
  · intro chk sc ns hs ds; unfold telescope; sp
  · intro v; unfold valueDecl; sp
  · intro T; unfold valTypeDecl; sp
  · intro T; unfold isPropV; sp
  · intro P; unfold fnClass; sp
  · intro B; unfold kindOf; sp
  · intro P; unfold declKind; sp


theorem decSP : ∀ n, DecSP n
  | 0 => decSP_zero
  | n + 1 => decSP_succ n (decSP n)

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply (decSP _).sortOf)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply (decSP _).typeDecl)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply (decSP _).fnClass)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply (decSP _).declKind)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply (decSP _).isPropV)

/-! ### Runs that restore the state they saved -/

/-- Successful runs of `x`, from anywhere, end with the signature of `s₀`. -/
def EndsAt {α : Type} (s₀ : MState) (x : M α) : Prop :=
  ∀ Ω fl lg a Ω' fl' lg', step x Ω fl lg = ((.ok (.ok (a, Ω')), fl'), lg') → SigAgree s₀ Ω'

theorem EndsAt.bind_any {α β} {s₀ : MState} (x : M α) {f : α → M β} (hf : ∀ a, EndsAt s₀ (f a)) :
    EndsAt s₀ (x >>= f) := by
  intro Ω fl lg b Ω' fl' lg' hs
  rw [step_bind] at hs
  revert hs
  rcases hr : step x Ω fl lg with ⟨⟨r, fl₁⟩, lg₁⟩
  rcases r with e | (e | ⟨a, Ω₁⟩) <;> simp only [cont] <;> intro hs
  · cases hs
  · cases hs
  · exact hf a Ω₁ fl₁ lg₁ b Ω' fl' lg' hs

theorem EndsAt.restoreKeep_bind {β} {s₀ : MState} {k : Unit → M β} (hk : ∀ u, SigPres (k u)) :
    EndsAt s₀ (restoreKeep s₀ >>= k) := by
  intro Ω fl lg b Ω' fl' lg' hs
  rw [step_bind] at hs
  unfold restoreKeep at hs
  rw [step_modify] at hs
  simp only [cont] at hs
  have h := hk ()
  unfold SigPres at h
  have := h _ fl lg b Ω' fl' lg' hs
  exact ⟨this.inds, this.globals⟩

theorem SigPres.get_ends {β} {k : MState → M β} (hk : ∀ s, EndsAt s (k s)) :
    SigPres (MonadState.get >>= k) := by
  unfold SigPres
  intro Ω fl lg b Ω' fl' lg' hs
  rw [step_bind] at hs
  simp only [step_get, cont] at hs
  exact hk Ω Ω fl lg b Ω' fl' lg' hs

attribute [irreducible] EndsAt

/-- A private copy keeps the signature, whatever runs on it: it restores the state it saved. -/
theorem sigPres_privately {α} (x : M α) : SigPres (privately x) := by
  unfold privately
  delta_private
  refine SigPres.get_ends fun s => ?_
  refine EndsAt.bind_any _ fun _ => ?_
  refine EndsAt.bind_any _ fun r => ?_
  exact EndsAt.restoreKeep_bind fun _ => SigPres.pure r

theorem sigPres_inStatement {α} (x : M α) : SigPres (inStatement x) := sigPres_privately (withErased x)

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_privately)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_inStatement)

/- `evalType` and `sealedType?` wrap their whole body, so they keep the signature at every fuel;
their equation lemmas are too costly to generate, so the wrapper is exposed by `rfl` per fuel. -/
theorem sigPres_evalType : ∀ (n : Nat) (t : Term), SigPres (evalType n t)
  | 0, _ => (show SigPres (inStatement _) from sigPres_inStatement _)
  | _ + 1, _ => (show SigPres (inStatement _) from sigPres_inStatement _)

theorem sigPres_sealedType? : ∀ (n : Nat) (t : Term), SigPres (sealedType? n t)
  | 0, _ => (show SigPres (privately _) from sigPres_privately _)
  | _ + 1, _ => (show SigPres (privately _) from sigPres_privately _)

theorem sigPres_expandRefsF (refs : List (Nat × Value)) : ∀ n v, SigPres (expandRefsF refs n v)
  | 0, v => by unfold expandRefsF; sp
  | n + 1, v => by
    have := sigPres_expandRefsF refs n
    cases v <;> simp only [expandRefsF] <;> sp

theorem sigPres_expandRefs (refs : List (Nat × Value)) (v : Value) : SigPres (expandRefs refs v) := by
  unfold expandRefs; have := sigPres_expandRefsF refs; sp

theorem sigPres_canonNeutral (v : Value) : SigPres (canonNeutral v) := by
  unfold canonNeutral; have := sigPres_expandRefs; sp

theorem sigPres_mapState (f : Value → M Value) (hf : ∀ v, SigPres (f v)) (types : Bool) :
    SigPres (mapState f types) := by
  unfold mapState; sp

/-! ### The functions a refinement reaches -/

macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_evalType)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_sealedType?)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_canonNeutral)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_expandRefs)
macro_rules | `(tactic| sp_ext) => `(tactic| with_reducible apply sigPres_mapState)

/-- The functions a refinement reaches keep the signature, at fuel `n`. -/
structure RefSP (n : Nat) : Prop where
  substV : ∀ x r v, SigPres (substV n x r v)
  substT : ∀ x r t, SigPres (substT n x r t)
  substEnv : ∀ x r b, SigPres (substEnv n x r b)
  nfSealed : ∀ t, SigPres (nfSealed n t)
  mkEqM : ∀ A a b, SigPres (mkEqM n A a b)
  conv : ∀ v w, SigPres (conv n v w)
  convList : ∀ l l', SigPres (convList n l l')
  convTList : ∀ l l', SigPres (convTList n l l')
  convT : ∀ t u, SigPres (convT n t u)
  convPi : ∀ P Q, SigPres (convPi n P Q)
  convFn : ∀ f g, SigPres (convFn n f g)
  convFnRun : ∀ f g pf cs hs ds c, SigPres (convFnRun n f g pf cs hs ds c)
  funType? : ∀ fv fT, SigPres (funType? n fv fT)
  funType : ∀ fv fT, SigPres (funType n fv fT)
  valType? : ∀ v, SigPres (valType? n v)
  indValType? : ∀ t c fs, SigPres (indValType? n t c fs)
  fieldTele : ∀ d ps c val upto, (∀ j T, SigPres (val j T)) → SigPres (fieldTele n d ps c val upto)
  fieldTypesOf : ∀ d ps c fs upto, SigPres (fieldTypesOf n d ps c fs upto)
  refine : ∀ σ r, SigPres (refine n σ r)
  renormAll : SigPres (renormAll n)
  renormV : ∀ v, SigPres (renormV n v)
  renormT : ∀ t, SigPres (renormT n t)

theorem refSP_zero : RefSP 0 := by
  constructor <;> intros <;>
    first
    | (unfold substV; sp) | (unfold substT; sp) | (unfold substEnv; sp) | (unfold nfSealed; sp)
    | (unfold mkEqM; sp) | (unfold conv; sp) | (unfold convList; sp) | (unfold convTList; sp)
    | (unfold convT; sp) | (unfold convPi; sp) | (unfold convFn; sp) | (unfold convFnRun; sp)
    | (unfold funType?; sp) | (unfold funType; sp) | (unfold valType?; sp) | (unfold indValType?; sp)
    | (unfold fieldTele; sp) | (unfold fieldTypesOf; sp) | (unfold refine; sp) | (unfold renormAll; sp)
    | (unfold renormV; sp) | (unfold renormT; sp)

theorem refSP_succ (n : Nat) (ih : RefSP n) : RefSP (n + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22⟩ := ih
  constructor
  · intro x r v; unfold substV; sp
  · intro x r t; unfold substT; sp
  · intro x r b; unfold substEnv; sp
  · intro t; unfold nfSealed; simp only []
    refine SigPres.get_ends fun saved => ?_
    repeat' (first | (intro) | (with_reducible apply EndsAt.restoreKeep_bind) | (with_reducible apply EndsAt.bind_any) | split)
    all_goals sp
  · intro A a b; unfold mkEqM; sp
  · intro v w; unfold conv; sp
  · intro l l'; unfold convList; sp
  · intro l l'; unfold convTList; sp
  · intro t u; unfold convT; sp
  · intro P Q; unfold convPi; sp
  · intro f g; unfold convFn; sp
  · intro f g pf cs hs ds c; unfold convFnRun; sp
  · intro fv fT; unfold funType?; sp
  · intro fv fT; unfold funType; sp
  · intro v; unfold valType?; sp
  · intro t c fs; unfold indValType?; sp
  · intro d ps c val upto hval; unfold fieldTele; sp
  · intro d ps c fs upto; unfold fieldTypesOf; sp
  · intro σ r; unfold refine; sp
  · unfold renormAll; sp
  · intro v; unfold renormV; sp
  · intro t; unfold renormT; sp

theorem refSP : ∀ n, RefSP n
  | 0 => refSP_zero
  | n + 1 => refSP_succ n (refSP n)

/-! ### Refinement keeps the signature -/

theorem sigPres_onState (α : Refinement) (fuel : Nat) : SigPres (α.onState fuel) := by
  unfold Refinement.onState
  exact SigPres.forM _ (fun p => (refSP fuel).refine p.1 p.2) α

theorem sigPres_onValue (α : Refinement) (fuel : Nat) (v : Value) : SigPres (α.onValue fuel v) := by
  unfold Refinement.onValue
  exact SigPres.foldlM _ (fun _ p => (refSP fuel).substV _ p.2 _) α v

theorem sigPres_onTerm (α : Refinement) (fuel : Nat) (t : Term) : SigPres (α.onTerm fuel t) := by
  unfold Refinement.onTerm
  exact SigPres.foldlM _ (fun _ p => (refSP fuel).substT _ p.2 _) α t

theorem SigPres.run? {α} {x : M α} (hx : SigPres x) {Ω : MState} {fuel : Nat} {a : α} {Ω' : MState}
    (h : run? x Ω fuel = some (a, Ω')) : SigAgree Ω Ω' := by
  unfold SigPres at hx
  rw [run?_eq] at h
  revert h
  rcases hs : step x Ω ⟨fuel⟩ #[] with ⟨⟨r, fl⟩, lg⟩
  rcases r with e | (e | ⟨b, Ω₁⟩)
  · simp
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq]
    rintro ⟨rfl, rfl⟩
    exact hx Ω ⟨fuel⟩ #[] b Ω₁ fl lg hs

/-- **Refinement keeps the signature** (assumption A1 of `StabilityDecide.lean`, now proved): the
refined state has the declared inductive types and globals the state had. -/
theorem onState_sig {α : Refinement} {Ω Ωα : MState} {fuel : Nat}
    (h : run? (α.onState fuel) Ω fuel = some ((), Ωα)) : SigAgree Ω Ωα :=
  (sigPres_onState α fuel).run? h

/-- So every decision that reads only the signature is the same at the refined state. -/
theorem ReadsSig.commutes {β} {x : M β} (hx : ReadsSig x) {α : Refinement} {Ω Ωα : MState} {fuel : Nat}
    (h : run? (α.onState fuel) Ω fuel = some ((), Ωα)) (fuel' : Nat) :
    (run? x Ωα fuel').map (·.1) = (run? x Ω fuel').map (·.1) :=
  (hx.agree (onState_sig h) fuel').symm

/-! ### What this proves of `DecisionsCommute`

Each theorem below is a field of `DecisionsCommute`, whole or for the cases named. -/

/-- Field `byType`, whole (site 11): the decision reads the arms' constructors and the
scrutinee's declaration, never the arms' bodies. -/
theorem decisionsCommute_byType : ∀ (Ω : MState) (ty : String) (arms : List (Hint × Term))
    (g : Term → Term) (fuel : Nat),
    (run? (byTypeMatch ty (arms.map fun a => (a.1, g a.2))) Ω fuel).map (·.1) =
      (run? (byTypeMatch ty arms) Ω fuel).map (·.1) := by
  intro Ω ty arms g fuel
  rw [byTypeMatch_arms]

/-- The decisions that read only the signature (sites 1 and 11 for constructors and fields: D42,
D45, D71) are the same at the refined state, whatever the refinement. -/
theorem sigDecisions_commute {α : Refinement} {Ω Ωα : MState} {fuel : Nat}
    (h : run? (α.onState fuel) Ω fuel = some ((), Ωα)) (fuel' : Nat) :
    (∀ ty, (run? (ctorIsProof ty) Ωα fuel').map (·.1) = (run? (ctorIsProof ty) Ω fuel').map (·.1)) ∧
    (∀ g, (run? (fieldIsProof g) Ωα fuel').map (·.1) = (run? (fieldIsProof g) Ω fuel').map (·.1)) ∧
    (∀ d FT, (run? (fieldTermIsProp d FT) Ωα fuel').map (·.1) =
      (run? (fieldTermIsProp d FT) Ω fuel').map (·.1)) ∧
    (∀ d, (run? (largeElim d) Ωα fuel').map (·.1) = (run? (largeElim d) Ω fuel').map (·.1)) ∧
    (∀ ty arms, (run? (byTypeMatch ty arms) Ωα fuel').map (·.1) =
      (run? (byTypeMatch ty arms) Ω fuel').map (·.1)) :=
  ⟨fun ty => (readsSig_ctorIsProof ty).commutes h fuel', fun g => (readsSig_fieldIsProof g).commutes h fuel',
    fun d FT => (readsSig_fieldTermIsProp d FT).commutes h fuel', fun d => (readsSig_largeElim d).commutes h fuel',
    fun ty arms => (readsSig_byTypeMatch ty arms).commutes h fuel'⟩

theorem declKind_notPi (fuel : Nat) (cs : List Value) (t : Term) (ht : ∀ hs ds c, t ≠ .pi hs ds c)
    (Ω : MState) : (run? (declKind fuel (.tPi cs t)) Ω fuel).map (·.1) = none := by
  cases fuel with
  | zero => rw [run?_eq]; unfold declKind; rfl
  | succ n =>
    rw [run?_eq]; unfold declKind
    cases t <;> first | rfl | exact absurd rfl (ht _ _ _)

/-- Field `closeRow` (site 8) for every Π-type value but a stuck block's function, whose codomain
is an embedded value (the match's type) and whose row reads that type's declared sort. -/
theorem decisionsCommute_closeRow (Ω : MState) (α : Refinement) (cs : List Value) (t : Term) (Pα : Value)
    (fuel : Nat) (hblock : ∀ hs ds B, t ≠ .pi hs ds (.val B))
    (hP : (run? (α.onValue fuel (.tPi cs t)) Ω fuel).map (·.1) = some Pα)
    (Ωα : MState) (k : Kind) (hk : (run? (declKind fuel (.tPi cs t)) Ω fuel).map (·.1) = some k) :
    (run? (declKind fuel Pα) Ωα fuel).map (·.1) = some k := by
  by_cases ht : ∃ hs ds c, t = .pi hs ds c
  · obtain ⟨hs, ds, c, rfl⟩ := ht
    have hc : rowOf c ≠ 3 := by
      cases c <;> simp only [rowOf] <;> first | decide | exact absurd rfl (hblock hs ds _)
    rw [closeRow_fn Ω α cs hs ds c hc Pα fuel hP Ωα]
    exact hk
  · rw [declKind_notPi fuel cs t (fun hs ds c h => ht ⟨hs, ds, c, h⟩) Ω] at hk
    cases hk

/-- Field `fnClass` (site 3) for the Π-types whose codomain's shape fixes the class (a sort; a
stuck block's function), at states whose class caches are sound (`ClassCacheSound`). -/
theorem decisionsCommute_fnClass_shape (Ω : MState) (α : Refinement) (cs : List Value) (hs : List Hint)
    (ds : List Term) (c : Term) (K : Nat) (hK : shapeClass (rowOf c) = some K) (Pα : Value) (fuel : Nat)
    (hP : (run? (α.onValue fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) = some Pα) (Ωα : MState)
    (hΩ : ClassCacheSound Ω (.tPi cs (.pi hs ds c))) (hΩα : ClassCacheSound Ωα Pα) (k : Nat)
    (hk : (run? (fnClass fuel (.tPi cs (.pi hs ds c))) Ω fuel).map (·.1) = some k) :
    (run? (fnClass fuel Pα) Ωα fuel).map (·.1) = some k := by
  rw [fnClass_shape Ω α cs hs ds c K hK Pα fuel hP Ωα hΩ hΩα]
  exact hk

/-! ### Why a stuck block's row is excluded

A stuck block's function has the match's type as its codomain, an embedded value, and
refining an unknown match type to `Unit` changes the row `declKind` reads from data to `Unit`
(η at `Unit`, D59). Checked here against the real `declKind`, with a function as control. -/

/-- A state with one unknown, `σ0 : Type`. -/
def probeΩ : MState := { (default : MState) with absTy := #[.sort 1] }

theorem probe_blockRow_refined :
    (run? (Refinement.onValue [(0, .tUnit)] 5 (.tPi [] (.pi [] [] (.val (.abs 0))))) probeΩ 5).map (·.1) =
      some (.tPi [] (.pi [] [] (.val .tUnit))) := by rfl
theorem probe_blockRow_generic :
    (run? (declKind 5 (.tPi [] (.pi [] [] (.val (.abs 0))))) probeΩ 5).map (·.1) = some .data := by rfl
theorem probe_blockRow_instance :
    (run? (declKind 5 (.tPi [] (.pi [] [] (.val .tUnit)))) probeΩ 5).map (·.1) = some .unit := by rfl
/-- Control: a function, whose codomain is a term, keeps its row. -/
theorem probe_fnRow : (run? (declKind 5 (.tPi [] (.pi [] [] (.place (.var 0))))) probeΩ 5).map (·.1) =
    some .data := by rfl

/-! ### Conjecture 2, as far as it is proved -/

/-- **Conjecture 2.** The fields of `DecisionsCommute` proved above are used; each `sorry` says
what it needs (`notes/stability.md` §9). -/
theorem stability : Conjecture2 :=
  ⟨{ -- needs the declared readings of embedded values to commute (`valueDecl`, evaluation
     -- preserves declared types, D55) and the live scope's readings to be kept: typing (M)
     erasure := sorry
     byType := decisionsCommute_byType
     -- proved for codomains whose shape fixes the class (`decisionsCommute_fnClass_shape`, given
     -- class-cache soundness); the general case reads captured values' declared readings (D55)
     fnClass := sorry
     closeRow := fun Ω α cs t Pα fuel hblock _ hP Ωα _ k hk =>
       decisionsCommute_closeRow Ω α cs t Pα fuel hblock hP Ωα k hk
     -- `closeBlock` runs the arms at both states: `RunsCorrespond`
     captures := sorry
     -- `placeType` reads the place's value: `RunsCorrespond` and typing (M)
     observedType := sorry
     -- needs refinement to keep the environment's shape (as `onState_sig` keeps the signature);
     -- not done
     footprint := sorry },
   -- symbolic naturality (N) and typed/untyped agreement (M)
   sorry⟩

end Ochr.Stability
