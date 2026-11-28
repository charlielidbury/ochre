import Ochr.Meaning.Steps.Machine.FuelDefs

/-!
# The decision procedures at one fuel and at the next (`Decide.lean`)

`DecideFuelLe n`: every function of `Decide.lean`'s mutual block that the decisions reach (the
seventeen of `DecideScope.DecideSim`) at fuel `n` is `FuelLe` the same function at `n + 1`. By
induction on `n`, each body walked step for step against itself one fuel up (`fuel_go`), the
recursive calls closed by the hypothesis.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope

set_option hygiene false in
/-- One step of a `FuelLe` proof, by the shape of the two computations (the same shape). -/
macro "fuel_step" : tactic => `(tactic| first
  | with_reducible exact fuelLe_pure _
  | with_reducible exact fuelLe_err _ _
  | with_reducible exact fuelLe_exhausted _ _
  | with_reducible exact fuelLe_liveDecl _
  | with_reducible exact fuelLe_lookupInd _
  | with_reducible exact fuelLe_lookupGlobal _
  | with_reducible exact fuelLe_absReading _
  | with_reducible exact fuelLe_capReadings _ _
  | with_reducible exact fuelLe_fieldTermIsProp _ _
  | with_reducible exact fuelLe_fieldIsProof _
  | with_reducible exact fuelLe_ctorIsProof _
  | with_reducible exact fuelLe_preFlags _ _
  | with_reducible exact fuelLe_refineDecl _
  | with_reducible exact fuelLe_sealedSort _
  | with_reducible exact fuelLe_codomainWritten _ _ _ _
  | (with_reducible refine fuelLe_get_bind fun _ => ?_)
  | (with_reducible refine fuelLe_bind ?_ (fun _ => ?_))
  | (with_reducible refine fuelLe_withLive _ ?_)
  | (with_reducible refine fuelLe_ite ?_ ?_)
  | (with_reducible refine fuelLe_dite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine fuelLe_map _ ?_)
  | (with_reducible refine fuelLe_discard ?_)
  | (with_reducible refine fuelLe_forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine fuelLe_mapM _ (fun _ => ?_))
  | (with_reducible refine fuelLe_allM _ (fun _ => ?_))
  | split
  | (dsimp only))

macro "fuel_go" : tactic => `(tactic| repeat (any_goals fuel_step))

/-! ## The helpers outside the fuel recursion: each is `FuelLe` itself (it never reads the fuel) -/

theorem fuelLe_liveDecl (i : Nat) : FuelLe (liveDecl i) (liveDecl i) := by unfold liveDecl; fuel_go
theorem fuelLe_lookupInd (n : String) : FuelLe (lookupInd n) (lookupInd n) := by unfold lookupInd; fuel_go
theorem fuelLe_lookupGlobal (n : String) : FuelLe (lookupGlobal n) (lookupGlobal n) := by
  unfold lookupGlobal; fuel_go
theorem fuelLe_absReading (σ : Nat) : FuelLe (absReading σ) (absReading σ) := by unfold absReading; fuel_go
theorem fuelLe_capReadings (cs : List Value) (rd : List (DeclInfo × Value)) :
    FuelLe (capReadings cs rd) (capReadings cs rd) := by unfold capReadings; fuel_go
theorem fuelLe_fieldTermIsProp (d : IndDecl) (FT : Term) : FuelLe (fieldTermIsProp d FT) (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp; fuel_go
theorem fuelLe_fieldIsProof (g : FieldRef) : FuelLe (fieldIsProof g) (fieldIsProof g) := by
  unfold fieldIsProof; fuel_go
theorem fuelLe_ctorIsProof (ty : String) : FuelLe (ctorIsProof ty) (ctorIsProof ty) := by
  unfold ctorIsProof; fuel_go
theorem fuelLe_preFlags (t : Term) (d : DeclInfo) : FuelLe (preFlags t d) (preFlags t d) := by
  unfold preFlags; fuel_go
theorem fuelLe_refineDecl (d : DeclInfo) : FuelLe (refineDecl d) (refineDecl d) := by
  unfold refineDecl; fuel_go
theorem fuelLe_sealedSort (t : Term) : FuelLe (sealedSort? t) (sealedSort? t) := by
  unfold sealedSort?; fuel_go
/-- D143's test of a written codomain (main's merge, lead49). -/
theorem fuelLe_codomainWritten (what : Unit → String) (c : Term) (ns : List String) (cd : DeclInfo) :
    FuelLe (codomainWritten what c ns cd) (codomainWritten what c ns cd) := by
  unfold codomainWritten; fuel_go

/-! ## The fuel recursion -/

/-- The seventeen functions of `Decide.lean`'s block the decisions reach, at `n` against `n + 1`. -/
structure DecideFuelLe (n : Nat) : Prop where
  placeDecl : ∀ sc p, FuelLe (placeDecl n sc p) (placeDecl (n + 1) sc p)
  fieldAt : ∀ r nm c i, FuelLe (fieldAt n r nm c i) (fieldAt (n + 1) r nm c i)
  fieldDecl : ∀ d args c i, FuelLe (fieldDecl n d args c i) (fieldDecl (n + 1) d args c i)
  declCopy : ∀ r, FuelLe (declCopy n r) (declCopy (n + 1) r)
  callDecl : ∀ F as sc ns, FuelLe (callDecl n F as sc ns) (callDecl (n + 1) F as sc ns)
  closedTypeDecl : ∀ T, FuelLe (closedTypeDecl n T) (closedTypeDecl (n + 1) T)
  sortOf : ∀ T, FuelLe (sortOf n T) (sortOf (n + 1) T)
  declSort : ∀ sc ns T, FuelLe (declSort n sc ns T) (declSort (n + 1) sc ns T)
  declOf : ∀ chk sc ns t, FuelLe (declOf n chk sc ns t) (declOf (n + 1) chk sc ns t)
  typeDecl : ∀ chk sc ns T vis tsc, FuelLe (typeDecl n chk sc ns T vis tsc) (typeDecl (n + 1) chk sc ns T vis tsc)
  typeFnDecl : ∀ F vis sc ns tsc as dflt dflt', FuelLe dflt dflt' →
    FuelLe (typeFnDecl n F vis sc ns tsc as dflt) (typeFnDecl (n + 1) F vis sc ns tsc as dflt')
  typePos : ∀ chk sc ns T, FuelLe (typePos n chk sc ns T) (typePos (n + 1) chk sc ns T)
  telescope : ∀ chk sc ns hs ds, FuelLe (telescope n chk sc ns hs ds) (telescope (n + 1) chk sc ns hs ds)
  valueDecl : ∀ v, FuelLe (valueDecl n v) (valueDecl (n + 1) v)
  valTypeDecl : ∀ T, FuelLe (valTypeDecl n T) (valTypeDecl (n + 1) T)
  isPropV : ∀ T, FuelLe (isPropV n T) (isPropV (n + 1) T)
  fnClass : ∀ T, FuelLe (fnClass n T) (fnClass (n + 1) T)

set_option hygiene false in
/-- A `FuelLe` proof whose leaves are the induction hypothesis `ih` or the helpers. -/
macro "fuel_ih" : tactic => `(tactic| repeat (any_goals first
  | with_reducible exact ih.placeDecl _ _ | with_reducible exact ih.fieldAt _ _ _ _
  | with_reducible exact ih.fieldDecl _ _ _ _ | with_reducible exact ih.declCopy _
  | with_reducible exact ih.callDecl _ _ _ _ | with_reducible exact ih.closedTypeDecl _
  | with_reducible exact ih.sortOf _ | with_reducible exact ih.declSort _ _ _
  | with_reducible exact ih.declOf _ _ _ _ | with_reducible exact ih.typeDecl _ _ _ _ _ _
  | with_reducible exact ih.typePos _ _ _ _ | with_reducible exact ih.telescope _ _ _ _ _
  | with_reducible exact ih.valueDecl _ | with_reducible exact ih.valTypeDecl _
  | with_reducible exact ih.isPropV _ | with_reducible exact ih.fnClass _
  | assumption
  | (with_reducible refine ih.typeFnDecl _ _ _ _ _ _ _ _ ?_)
  | fuel_step))

theorem decideFuelLe_zero : DecideFuelLe 0 := by
  constructor <;> intros <;>
    first
    | (unfold placeDecl; dsimp only; fuel_go)
    | (unfold fieldAt; dsimp only; fuel_go)
    | (unfold fieldDecl; dsimp only; fuel_go)
    | (unfold declCopy; dsimp only; fuel_go)
    | (unfold callDecl; dsimp only; fuel_go)
    | (unfold closedTypeDecl; dsimp only; fuel_go)
    | (unfold sortOf; dsimp only; fuel_go)
    | (unfold declSort; dsimp only; fuel_go)
    | (unfold declOf; dsimp only; fuel_go)
    | (unfold typeDecl; dsimp only; fuel_go)
    | (unfold typeFnDecl; dsimp only; fuel_go)
    | (unfold typePos; dsimp only; fuel_go)
    | (unfold telescope; dsimp only; fuel_go)
    | (unfold valueDecl; dsimp only; fuel_go)
    | (unfold valTypeDecl; dsimp only; fuel_go)
    | (unfold isPropV; dsimp only; fuel_go)
    | (unfold fnClass; dsimp only; fuel_go)

set_option maxHeartbeats 4000000 in
theorem decideFuelLe_succ (n : Nat) (ih : DecideFuelLe n) : DecideFuelLe (n + 1) := by
  constructor
  · intro sc p; unfold placeDecl; (try dsimp only); fuel_ih
  · intro r n' c i; unfold fieldAt; (try dsimp only); fuel_ih
  · intro d args c i; unfold fieldDecl; (try dsimp only); fuel_ih
  · intro r; unfold declCopy; (try dsimp only); fuel_ih
  · intro F as sc ns; unfold callDecl; (try dsimp only); fuel_ih
  · intro T; unfold closedTypeDecl; (try dsimp only); fuel_ih
  · intro T; unfold sortOf; (try dsimp only); fuel_ih
  · intro sc ns T; unfold declSort; (try dsimp only); fuel_ih
  · intro chk sc ns t
    cases t <;> (unfold declOf; (try dsimp only); fuel_ih)
  · intro chk sc ns T vis tsc; unfold typeDecl; (try dsimp only); fuel_ih
  · intro F vis sc ns tsc as dflt dflt' hd; unfold typeFnDecl; (try dsimp only); fuel_ih
  · intro chk sc ns T; unfold typePos; (try dsimp only); fuel_ih
  · intro chk sc ns hs ds; unfold telescope; (try dsimp only); fuel_ih
  · intro v; unfold valueDecl; (try dsimp only); fuel_ih
  · intro T; unfold valTypeDecl; (try dsimp only); fuel_ih
  · intro T; unfold isPropV; (try dsimp only); fuel_ih
  · intro T; unfold fnClass; (try dsimp only); fuel_ih

/-- **The decision procedures at `n` are `FuelLe` at `n + 1`**, every function the decisions reach. -/
theorem decideFuelLe : ∀ n, DecideFuelLe n
  | 0 => decideFuelLe_zero
  | n + 1 => decideFuelLe_succ n (decideFuelLe n)

/-! ## D84's join set and [Id-typestate]'s -/

set_option hygiene false in
/-- Close the calls of the decisions' block left by a `fuel_go`, at any fuel. -/
macro "fuel_dec" : tactic => `(tactic| first
  | exact (decideFuelLe _).placeDecl _ _
  | exact (decideFuelLe _).declCopy _
  | exact (decideFuelLe _).declOf _ _ _ _
  | exact fuelLe_preFlags _ _)

theorem fuelLe_jdGrain (n : Nat) (m : Place) : FuelLe (jdGrain n m) (jdGrain (n + 1) m) := by
  unfold jdGrain; (try dsimp only); fuel_go
  all_goals fuel_dec

theorem fuelLe_jdFns (n : Nat) (sc : List DeclInfo) (t : Term) (acc : List Place) :
    FuelLe (jdFns n sc t acc) (jdFns (n + 1) sc t acc) := by
  unfold jdFns; (try dsimp only); fuel_go
  all_goals fuel_dec

/-- `Decide.jdMoves`' mutual block, at `n` against `n + 1`. -/
structure JdFuelLe (n : Nat) : Prop where
  jdMoves : ∀ sc al t acc, FuelLe (jdMoves n sc al t acc) (jdMoves (n + 1) sc al t acc)
  jdMovesList : ∀ sc al ts acc, FuelLe (jdMovesList n sc al ts acc) (jdMovesList (n + 1) sc al ts acc)
  jdMatch : ∀ sc al t arms acc, FuelLe (jdMatch n sc al t arms acc) (jdMatch (n + 1) sc al t arms acc)

set_option maxHeartbeats 4000000 in
theorem jdFuelLe : ∀ n, JdFuelLe n
  | 0 => ⟨fun _ _ _ _ => by unfold jdMoves; dsimp only; fuel_go,
      fun _ _ ts _ => by cases ts <;> (unfold jdMovesList; (try dsimp only); fuel_go),
      fun _ _ _ _ _ => by unfold jdMatch; dsimp only; fuel_go⟩
  | n + 1 => by
    have ih := jdFuelLe n
    refine ⟨fun sc al t acc => ?_, fun sc al ts acc => ?_, fun sc al t arms acc => ?_⟩
    · unfold jdMoves; (try dsimp only); fuel_go
      all_goals first
        | fuel_dec
        | exact ih.jdMoves _ _ _ _
        | exact ih.jdMovesList _ _ _ _
        | exact ih.jdMatch _ _ _ _ _
        | exact fuelLe_jdFns _ _ _ _
    · cases ts with
      | nil => unfold jdMovesList; (try dsimp only); fuel_go
      | cons t ts =>
        unfold jdMovesList; (try dsimp only); fuel_go
        all_goals first
          | exact ih.jdMoves _ _ _ _
          | exact ih.jdMovesList _ _ _ _
    · unfold jdMatch; (try dsimp only); fuel_go
      all_goals first
        | fuel_dec
        | exact ih.jdMoves _ _ _ _
        | exact fuelLe_jdFns _ _ _ _
        | exact fuelLe_jdGrain _ _

/-- `Decide.jdAssigns`' mutual block, at `n` against `n + 1`. -/
structure JaFuelLe (n : Nat) : Prop where
  jdAssigns : ∀ sc t acc, FuelLe (jdAssigns n sc t acc) (jdAssigns (n + 1) sc t acc)
  jdAssignsList : ∀ sc ts acc, FuelLe (jdAssignsList n sc ts acc) (jdAssignsList (n + 1) sc ts acc)

set_option maxHeartbeats 4000000 in
theorem jaFuelLe : ∀ n, JaFuelLe n
  | 0 => ⟨fun _ _ _ => by unfold jdAssigns; dsimp only; fuel_go,
      fun _ ts _ => by cases ts <;> (unfold jdAssignsList; (try dsimp only); fuel_go)⟩
  | n + 1 => by
    have ih := jaFuelLe n
    refine ⟨fun sc t acc => ?_, fun sc ts acc => ?_⟩
    · unfold jdAssigns; (try dsimp only); fuel_go
      all_goals first
        | fuel_dec
        | exact ih.jdAssigns _ _ _
        | exact ih.jdAssignsList _ _ _
    · cases ts with
      | nil => unfold jdAssignsList; (try dsimp only); fuel_go
      | cons t ts =>
        unfold jdAssignsList; (try dsimp only); fuel_go
        all_goals first
          | exact ih.jdAssigns _ _ _
          | exact ih.jdAssignsList _ _ _

theorem fuelLe_typeState (n : Nat) (t : Term) : FuelLe (typeState n t) (typeState (n + 1) t) := by
  unfold typeState; (try dsimp only); fuel_go
  all_goals first
    | fuel_dec
    | exact (jdFuelLe _).jdMoves _ _ _ _
    | exact (jaFuelLe _).jdAssigns _ _ _

/-! ## Successful runs at different fuels agree: one statement per decision of `Decisions`

`FuelMono x`: a success of `x n` is a success of `x m` for every `m ≥ n`, with the same value and
final state, from the same state and any budget. `FuelAgree x`: two successes of the family, at any
two fuels and budgets, from the same state, give the same value (and the same final state). So
"the checker's answer at any fuel at which the decision succeeds" is well defined. Each decision is
stated in the form `DecisionsInst.checkerDecisions₀` and `Statements.DecTab` read it. -/

open Ochr.Meaning.Steps in
theorem runs_runAll {α : Type} {x : M α} {st s' : MState} {b : Nat} {a : α} (h : Runs x st b a s') :
    ∃ L f' l', runAll x st ⟨b⟩ L = ((.ok (.ok (a, s')), f'), l') := by
  obtain ⟨L, left, log, h⟩ := h
  have key : runMachineL x st b L = (match runAll x st ⟨b⟩ L with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) := rfl
  rw [key] at h
  rcases e : runAll x st ⟨b⟩ L with ⟨⟨e₁ | e₁ | ⟨a', s₁⟩, f₁⟩, l₁⟩ <;> rw [e] at h
  · simp at h
  · simp at h
  · simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨L, f₁, l₁, e⟩

open Ochr.Meaning.Steps in
theorem runs_of_runAll {α : Type} {x : M α} {st s' : MState} {b : Nat} {a : α} {L : Array LogEntry} {f' : Fuel}
    {l' : Array LogEntry} (h : runAll x st ⟨b⟩ L = ((.ok (.ok (a, s')), f'), l')) : Runs x st b a s' := by
  refine ⟨L, f'.left, l', ?_⟩
  show (match runAll x st ⟨b⟩ L with
      | ((r, fl), log) => ((match r with
        | .error e => Outcome.exhausted e.msg
        | .ok (.error f) => .fail f
        | .ok (.ok (a, st')) => .ok a st'), fl.left, log)) = _
  rw [h]

open Ochr.Meaning.Steps in
/-- A success at fuel `n` is a success at every larger fuel, from any budget, with the same value and
final state. -/
def FuelMono {α : Type} (x : Nat → M α) : Prop :=
  ∀ (st : MState) (n m b : Nat) (a : α) (s₁ : MState), n < m → Runs (x n) st b a s₁ → ∀ b', Runs (x m) st b' a s₁

open Ochr.Meaning.Steps in
/-- Two successes of the family, at any fuels and budgets, from the same state, agree. -/
def FuelAgree {α : Type} (x : Nat → M α) : Prop :=
  ∀ (st : MState) (n m b b' : Nat) (a a' : α) (s₁ s₂ : MState), Runs (x n) st b a s₁ → Runs (x m) st b' a' s₂ →
    a = a' ∧ s₁ = s₂

theorem fuelLe_chain {α : Type} {x : Nat → M α} (h : ∀ n, FuelLe (x n) (x (n + 1))) :
    ∀ n m, n < m → FuelLe (x n) (x m) := by
  intro n m hnm
  induction hnm with
  | refl => exact h n
  | step _ ih => exact ih.trans (h _)

theorem fuelMono_of_step {α : Type} {x : Nat → M α} (h : ∀ n, FuelLe (x n) (x (n + 1))) : FuelMono x := by
  intro st n m b a s₁ hnm hr b'
  obtain ⟨L, f', l', e⟩ := runs_runAll hr
  obtain ⟨g', l₂', e'⟩ := fuelLe_chain h n m hnm st ⟨b⟩ L a s₁ f' l' ⟨b'⟩ #[] e
  exact runs_of_runAll e'

theorem fuelAgree_of_step {α : Type} {x : Nat → M α} (h : ∀ n, FuelLe (x n) (x (n + 1))) : FuelAgree x := by
  intro st n m b b' a a' s₁ s₂ h₁ h₂
  obtain ⟨L₁, f₁, l₁, e₁⟩ := runs_runAll h₁
  obtain ⟨L₂, f₂, l₂, e₂⟩ := runs_runAll h₂
  obtain ⟨g₁, k₁, e₁'⟩ := fuelLe_chain h n (max n m + 1) (by omega) st ⟨b⟩ L₁ a s₁ f₁ l₁ ⟨0⟩ #[] e₁
  obtain ⟨g₂, k₂, e₂'⟩ := fuelLe_chain h m (max n m + 1) (by omega) st ⟨b'⟩ L₂ a' s₂ f₂ l₂ ⟨0⟩ #[] e₂
  rw [e₁'] at e₂'
  simp only [Prod.mk.injEq, Except.ok.injEq] at e₂'
  exact ⟨e₂'.1.1.1, e₂'.1.1.2⟩

/-! ### The decisions, as `DecisionsInst.checkerDecisions₀` reads each -/

theorem fuelAgree_flags (t : Term) : FuelAgree (fun n => do
    let d ← withLive true (Ochr.declOf n false [] [] t)
    pure ((← preFlags t d).getD (false, false))) :=
  fuelAgree_of_step fun n => fuelLe_bind (fuelLe_withLive _ ((decideFuelLe n).declOf _ _ _ _)) fun _ =>
    fuelLe_bind (fuelLe_preFlags _ _) fun _ => fuelLe_pure _

theorem fuelAgree_placeDecl (p : Place) : FuelAgree (fun n => withLive true (Ochr.placeDecl n [] p)) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ ((decideFuelLe n).placeDecl _ _)

theorem fuelAgree_declOf (t : Term) : FuelAgree (fun n => withLive true (Ochr.declOf n false [] [] t)) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ ((decideFuelLe n).declOf _ _ _ _)

theorem fuelAgree_copy (r : DeclInfo) : FuelAgree (fun n => Ochr.declCopy n r) :=
  fuelAgree_of_step fun n => (decideFuelLe n).declCopy _

theorem fuelAgree_piSort (t : Term) : FuelAgree (fun n => withLive true (Ochr.sortOf n (.tPi [] t []))) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ ((decideFuelLe n).sortOf _)

theorem fuelAgree_joinMoves (entry : List Place) (t : Term) :
    FuelAgree (fun n => withLive true (Ochr.jdMoves n [] [] t entry)) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ ((jdFuelLe n).jdMoves _ _ _ _)

theorem fuelAgree_rePointed (t : Term) :
    FuelAgree (fun n => do pure (← withLive true (Ochr.typeState n t)).repointed) :=
  fuelAgree_of_step fun n => fuelLe_bind (fuelLe_withLive _ (fuelLe_typeState _ _)) fun _ => fuelLe_pure _

theorem fuelAgree_typeDecl (T : Term) : FuelAgree (fun n => withLive true (Ochr.typeDecl n false [] [] T)) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ ((decideFuelLe n).typeDecl _ _ _ _ _ _)

theorem fuelAgree_typeState (t : Term) : FuelAgree (fun n => withLive true (Ochr.typeState n t)) :=
  fuelAgree_of_step fun n => fuelLe_withLive _ (fuelLe_typeState _ _)

open Ochr.Meaning.Steps in
/-- `DecisionsFF.decide_fuel_agree` in the form that file states it (`SucceedsAt`: some fuel, some
budget), for any family whose successes agree across fuels (`FuelAgree` here). `DecisionsFF.lean`
imports only `Statements`, so it can import this file and close its leaf with this lemma, one
field of `DecideFuelAgree` per `fuelAgree_*` above (`flagsD t` is `fun f => …` definitionally). -/
theorem fuelAgreeFF_of {α : Type} {x : Nat → M α} (h : FuelAgree x) (st : MState) :
    ∀ a a', (∃ f b st', Runs (x f) st b a st') → (∃ f b st', Runs (x f) st b a' st') → a = a' := by
  rintro a a' ⟨f, b, s₁, h₁⟩ ⟨f', b', s₂, h₂⟩
  exact (h st f f' b b' a a' s₁ s₂ h₁ h₂).1

end Ochr.Meaning.Steps.Machine
