import Ochr.Meaning.Steps.Statements

/-!
# A run of the decision procedures leaves the state as it was (the slice)

Main's D95: the decision procedures write no cache; the one field they set, `liveScope`, is set
only inside `withLive`, which restores it. So a run of any function of `Decide.lean`'s mutual
block that the decisions reach ends in the state it started from (`Keep`). The proof is the
induction of `DecideScope.decideSim` with a unary property in place of its relation: `Keep x` says
every successful run of `x` returns its start state.

Used by `copyRead_aligned` (the copy decision leaves the state unchanged) and
`runs_valTypeDecl_keep` (the reading `freshAbsR` freezes, D96).
-/

namespace Ochr.Meaning.Steps.Slice

open Ochr Ochr.Meaning Ochr.Meaning.DecideScope

/-- Every successful run of `x` from `s` ends in `s`. -/
def KeepAt {α : Type} (x : M α) (s : MState) : Prop :=
  ∀ f l a s' f' l', runAll x s f l = ((.ok (.ok (a, s')), f'), l') → s' = s

/-- Every successful run of `x` ends in its start state. -/
def Keep {α : Type} (x : M α) : Prop := ∀ s, KeepAt x s

theorem keep_bind {α β : Type} {x : M α} {k : α → M β} (hx : Keep x) (hk : ∀ a, Keep (k a)) :
    Keep (x >>= k) := by
  intro s f l b s' f' l' h
  rw [runAll_bind] at h
  revert h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h; cases h
  · intro h
    have h1 := hx s f l a s₁ f₁ l₁ e
    have h2 := hk a s₁ f₁ l₁ b s' f' l' h
    rw [h2, h1]

theorem keep_pure {α : Type} (a : α) : Keep (pure a : M α) := by
  intro s f l b s' f' l' h
  simp only [runAll, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
  cases h; rfl

theorem keep_err {α : Type} (m : String) : Keep (err m : M α) := by
  intro s f l b s' f' l' h
  cases h

theorem keep_exhausted {α : Type} (m : String) : Keep (exhausted m : M α) := by
  intro s f l b s' f' l' h
  cases h

theorem keep_get_bind {α : Type} {k : MState → M α} (hk : ∀ s, KeepAt (k s) s) : Keep (get >>= k) := by
  intro s f l b s' f' l' h
  exact hk s f l b s' f' l' h

theorem keep_ite {α : Type} {c : Prop} {_ : Decidable c} {x y : M α} (hx : Keep x) (hy : Keep y) :
    Keep (if c then x else y) := by
  split <;> assumption

theorem keep_map {α β : Type} (g : α → β) {x : M α} (hx : Keep x) : Keep (g <$> x) := by
  rw [map_eq_pure_bind]
  exact keep_bind hx fun a => keep_pure _

theorem keep_discard {α : Type} {x : M α} (hx : Keep x) : Keep (discard x) := by
  show Keep (Functor.mapConst PUnit.unit x)
  rw [LawfulFunctor.map_const]
  exact keep_map _ hx

theorem keep_forIn {α β : Type} (xs : List α) (b : β) {body : α → β → M (ForInStep β)}
    (hb : ∀ a b, Keep (body a b)) : Keep (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact keep_pure b
  | cons a as ih =>
    rw [List.forIn_cons]
    exact keep_bind (hb a b) (fun r => by cases r with
      | done b' => exact keep_pure b'
      | yield b' => exact ih b')

theorem keep_mapM {α β : Type} (xs : List α) {f : α → M β} (hf : ∀ a, Keep (f a)) : Keep (xs.mapM f) := by
  induction xs with
  | nil => exact keep_pure []
  | cons a as ih =>
    rw [List.mapM_cons]
    exact keep_bind (hf a) (fun b => keep_bind ih (fun bs => keep_pure _))

theorem keep_allM {α : Type} (xs : List α) {f : α → M Bool} (hf : ∀ a, Keep (f a)) : Keep (xs.allM f) := by
  induction xs with
  | nil => exact keep_pure true
  | cons a as ih =>
    unfold List.allM
    exact keep_bind (hf a) (fun b => by cases b <;> first | exact ih | exact keep_pure _)

theorem KeepAt.of_keep {α : Type} {x : M α} (h : Keep x) (s : MState) : KeepAt x s := h s

theorem runAll_modify (g : MState → MState) (s : MState) (f : Fuel) (l : Array LogEntry) :
    runAll (modify g : M Unit) s f l = ((.ok (.ok ((), g s)), f), l) := rfl

theorem runAll_throw {α : Type} (e : Fail) (s : MState) (f : Fuel) (l : Array LogEntry) :
    runAll (throw e : M α) s f l = ((.ok (.error e), f), l) := rfl

/-- A cleanup then a rethrow never succeeds. -/
theorem runAll_cleanup_throw {α : Type} (c : M Unit) (e : Fail) (s : MState) (f : Fuel) (l : Array LogEntry)
    (a : α) (s' : MState) (f' : Fuel) (l' : Array LogEntry) :
    runAll (do c; throw e : M α) s f l ≠ ((.ok (.ok (a, s')), f'), l') := by
  rw [runAll_bind]
  rcases runAll c s f l with ⟨⟨e₁ | e₁ | ⟨u, s₁⟩, f₁⟩, l₁⟩
  · simp
  · simp
  · simp [runAll_throw]

theorem keepAt_onFail {α : Type} {x : M α} {c : M Unit} {s : MState} (hx : KeepAt x s) :
    KeepAt (onFail x c) s := by
  intro f l a s' f' l' h
  unfold onFail at h
  rw [runAll_tryCatch] at h
  rcases e : runAll x s f l with ⟨⟨e₁ | e₁ | ⟨b, s₁⟩, f₁⟩, l₁⟩
  · rw [e] at h; cases h
  · rw [e] at h; exact absurd h (runAll_cleanup_throw c e₁ s f₁ l₁ a s' f' l')
  · rw [e] at h
    simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := h
    exact hx f l _ _ f₁ l₁ e

/-- `withLive` restores the reading mode it set. -/
theorem keep_withLive {α : Type} (b : Bool) {x : M α} (hx : Keep x) : Keep (withLive b x) := by
  unfold withLive
  refine keep_get_bind fun s => ?_
  intro f l a s' f' l' h
  simp only [runAll_bind, runAll_modify] at h
  rcases e : runAll (onFail x (modify fun s₀ => { s₀ with liveScope := s.liveScope })) { s with liveScope := b } f l
    with ⟨⟨e₁ | e₁ | ⟨r, s₁⟩, f₁⟩, l₁⟩
  · rw [e] at h; cases h
  · rw [e] at h; cases h
  · rw [e] at h
    have h1 := keepAt_onFail (hx _) f l r s₁ f₁ l₁ e
    subst h1
    change ((Except.ok (Except.ok (r, { { s with liveScope := b } with liveScope := s.liveScope })), f₁), l₁) =
      ((Except.ok (Except.ok (a, s')), f'), l') at h
    simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨⟨⟨-, rfl⟩, -⟩, -⟩ := h
    cases s; rfl

/-! ## The decision procedures keep the state -/

theorem keep_get_proj {α β : Type} (g : MState → β) (k : β → M α) (hk : ∀ b, Keep (k b)) :
    Keep (get >>= fun s => k (g s)) :=
  keep_get_bind fun s => hk (g s) s

set_option hygiene false in
/-- One step of a `Keep` proof, by the shape of the computation (`DecideScope.sim_step`'s cases,
with a read of the state continuing at the state read). -/
macro "keep_step" : tactic => `(tactic| first
  | with_reducible exact keep_pure _
  | with_reducible exact keep_err _
  | with_reducible exact keep_exhausted _
  | with_reducible exact keep_liveDecl _
  | with_reducible exact keep_lookupInd _
  | with_reducible exact keep_lookupGlobal _
  | with_reducible exact keep_absReading _
  | with_reducible exact keep_capReadings _ _
  | (with_reducible refine keep_get_bind fun s => KeepAt.of_keep ?_ s
     try dsimp only)
  | (with_reducible refine keep_bind ?_ (fun _ => ?_))
  | (with_reducible refine keep_withLive _ ?_)
  | (with_reducible refine keep_map _ ?_)
  | (with_reducible refine keep_discard ?_)
  | (with_reducible refine keep_forIn _ _ (fun _ _ => ?_))
  | (with_reducible refine keep_mapM _ (fun _ => ?_))
  | (with_reducible refine keep_allM _ (fun _ => ?_))
  | split
  | (dsimp only))

macro "keep_go" : tactic => `(tactic| repeat (any_goals keep_step))

theorem keep_liveDecl (i : Nat) : Keep (liveDecl i) := by unfold liveDecl; keep_go
theorem keep_lookupInd (n : String) : Keep (lookupInd n) := by unfold lookupInd; keep_go
theorem keep_lookupGlobal (n : String) : Keep (lookupGlobal n) := by unfold lookupGlobal; keep_go
theorem keep_absReading (σ : Nat) : Keep (absReading σ) := by unfold absReading; keep_go
theorem keep_capReadings (cs : List Value) (rd : List (DeclInfo × Value)) : Keep (capReadings cs rd) := by
  unfold capReadings; keep_go
theorem keep_fieldTermIsProp (d : IndDecl) (FT : Term) : Keep (fieldTermIsProp d FT) := by
  unfold fieldTermIsProp; keep_go
theorem keep_fieldIsProof (g : FieldRef) : Keep (fieldIsProof g) := by
  unfold fieldIsProof; keep_go
  all_goals first | exact keep_fieldTermIsProp _ _ | exact keep_lookupInd _
theorem keep_ctorIsProof (ty : String) : Keep (ctorIsProof ty) := by unfold ctorIsProof; keep_go
theorem keep_preFlags (t : Term) (d : DeclInfo) : Keep (preFlags t d) := by unfold preFlags; keep_go
theorem keep_refineDecl (d : DeclInfo) : Keep (refineDecl d) := by unfold refineDecl; keep_go
theorem keep_sealedSort (t : Term) : Keep (sealedSort? t) := by unfold sealedSort?; keep_go
/-- D143's test of a written codomain (main's merge, lead49). -/
theorem keep_codomainWritten (what : Unit → String) (c : Term) (ns : List String) (cd : DeclInfo) :
    Keep (codomainWritten what c ns cd) := by unfold codomainWritten; keep_go

/-! ## The fuel recursion (the shape of `DecideScope.decideSim`) -/

def DecideKeep (fuel : Nat) : Prop :=
  (∀ sc p, Keep (placeDecl fuel sc p)) ∧
  (∀ r n c i, Keep (fieldAt fuel r n c i)) ∧
  (∀ d args c i, Keep (fieldDecl fuel d args c i)) ∧
  (∀ r, Keep (declCopy fuel r)) ∧
  (∀ F as sc ns, Keep (callDecl fuel F as sc ns)) ∧
  (∀ T, Keep (closedTypeDecl fuel T)) ∧
  (∀ T, Keep (sortOf fuel T)) ∧
  (∀ sc ns T, Keep (declSort fuel sc ns T)) ∧
  (∀ chk sc ns t, Keep (declOf fuel chk sc ns t)) ∧
  (∀ chk sc ns T vis tsc, Keep (typeDecl fuel chk sc ns T vis tsc)) ∧
  (∀ F vis sc ns tsc as dflt, Keep dflt → Keep (typeFnDecl fuel F vis sc ns tsc as dflt)) ∧
  (∀ chk sc ns T, Keep (typePos fuel chk sc ns T)) ∧
  (∀ chk sc ns hs ds, Keep (telescope fuel chk sc ns hs ds)) ∧
  (∀ v, Keep (valueDecl fuel v)) ∧
  (∀ T, Keep (valTypeDecl fuel T)) ∧
  (∀ T, Keep (isPropV fuel T)) ∧
  (∀ T, Keep (fnClass fuel T))

theorem decideKeep_zero : DecideKeep 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (unfold placeDecl; exact keep_exhausted _)
    | (unfold fieldAt; exact keep_exhausted _)
    | (unfold fieldDecl; exact keep_withLive _ (keep_exhausted _))
    | (unfold fieldDecl; exact keep_exhausted _)
    | (unfold declCopy; exact keep_exhausted _)
    | (unfold callDecl; exact keep_exhausted _)
    | (unfold closedTypeDecl; exact keep_exhausted _)
    | (unfold closedTypeDecl; exact keep_withLive _ (keep_exhausted _))
    | (unfold sortOf; exact keep_exhausted _)
    | (unfold declSort; exact keep_exhausted _)
    | (unfold declOf; exact keep_exhausted _)
    | (unfold typeDecl; exact keep_exhausted _)
    | (unfold typeFnDecl; exact keep_exhausted _)
    | (unfold typePos; exact keep_exhausted _)
    | (unfold telescope; exact keep_exhausted _)
    | (unfold valueDecl; exact keep_withLive _ (keep_exhausted _))
    | (unfold valTypeDecl; exact keep_withLive _ (keep_exhausted _))
    | (unfold isPropV; exact keep_exhausted _)
    | (unfold fnClass; exact keep_exhausted _)

set_option hygiene false in
macro "intro_kih" : tactic => `(tactic| obtain ⟨ihP, ihFA, ihFD, ihDC, ihCD, ihCT, ihSO, ihDS, ihDO, ihTD, ihTF,
  ihTP, ihTel, ihVD, ihVT, ihPV, ihFC⟩ := ih)

set_option hygiene false in
macro "keep_ih" : tactic => `(tactic| repeat (any_goals first
  | with_reducible exact ihP _ _ | with_reducible exact ihFA _ _ _ _ | with_reducible exact ihFD _ _ _ _
  | with_reducible exact ihDC _ | with_reducible exact ihCD _ _ _ _
  | with_reducible exact ihCT _ | with_reducible exact ihSO _ | with_reducible exact ihDS _ _ _
  | with_reducible exact ihDO _ _ _ _ | with_reducible exact ihTD _ _ _ _ _ _
  | with_reducible exact ihTP _ _ _ _ | with_reducible exact ihTel _ _ _ _ _ | with_reducible exact ihVD _
  | with_reducible exact ihVT _ | with_reducible exact ihPV _ | with_reducible exact ihFC _
  | with_reducible exact keep_fieldIsProof _ | with_reducible exact keep_fieldTermIsProp _ _
  | with_reducible exact keep_ctorIsProof _
  | with_reducible exact keep_preFlags _ _ | with_reducible exact keep_refineDecl _
  | with_reducible exact keep_sealedSort _
  | with_reducible exact keep_codomainWritten _ _ _ _
  | assumption
  | with_reducible apply ihTF
  | keep_step))

set_option maxHeartbeats 2000000 in
theorem decideKeep_succ (n : Nat) (ih : DecideKeep n) : DecideKeep (n + 1) := by
  intro_kih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sc p; unfold placeDecl; (try dsimp only); keep_ih
  · intro r n' c i; unfold fieldAt; (try dsimp only); keep_ih
  · intro d args c i; unfold fieldDecl; (try dsimp only); keep_ih
  · intro r; unfold declCopy; (try dsimp only); keep_ih
  · intro F as sc ns; unfold callDecl; (try dsimp only); keep_ih
  · intro T; unfold closedTypeDecl; (try dsimp only); keep_ih
  · intro T; unfold sortOf; (try dsimp only); keep_ih
  · intro sc ns T; unfold declSort; (try dsimp only); keep_ih
  · intro chk sc ns t
    cases t <;> (unfold declOf; (try dsimp only); keep_ih)
  · intro chk sc ns T vis tsc; unfold typeDecl; (try dsimp only); keep_ih
  · intro F vis sc ns tsc as dflt hd; unfold typeFnDecl; (try dsimp only); keep_ih
  · intro chk sc ns T; unfold typePos; (try dsimp only); keep_ih
  · intro chk sc ns hs ds; unfold telescope; (try dsimp only); keep_ih
  · intro v; unfold valueDecl; (try dsimp only); keep_ih
  · intro T; unfold valTypeDecl; (try dsimp only); keep_ih
  · intro T; unfold isPropV; (try dsimp only); keep_ih
  · intro T; unfold fnClass; (try dsimp only); keep_ih

/-- **The decision procedures keep the state**: every function of `Decide.lean`'s mutual block the
decisions reach, at every fuel. -/
theorem decideKeep : ∀ fuel, DecideKeep fuel
  | 0 => decideKeep_zero
  | n + 1 => decideKeep_succ n (decideKeep n)

/-- A run of a computation that keeps the state ends where it started. -/
theorem runs_keep {α : Type} {x : M α} (hk : Keep x) {st st' : MState} {b : Nat} {a : α}
    (h : Runs x st b a st') : st' = st := by
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
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hk st ⟨b⟩ L a' s₁ f₁ l₁ e

/-- **`valTypeDecl` leaves the state as it was** (the reading `freshAbsR` freezes, D96). -/
theorem runs_valTypeDecl_keep' {fuel : Nat} {T : Value} {st st' : MState} {b : Nat} {d : DeclInfo}
    (h : Runs (Ochr.valTypeDecl fuel T) st b d st') : st' = st :=
  runs_keep ((decideKeep fuel).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T) h

/-- `withLive true (placeDecl …)`, the declared reading of a place as the machine asks it, leaves
the state as it was. -/
theorem runs_placeDecl_keep {fuel : Nat} {sc : List DeclInfo} {p : Place} {st st' : MState} {b : Nat} {d : DeclInfo}
    (h : Runs (withLive true (Ochr.placeDecl fuel sc p)) st b d st') : st' = st :=
  runs_keep (keep_withLive _ ((decideKeep fuel).1 sc p)) h

/-- `declCopy` leaves the state as it was. -/
theorem runs_declCopy_keep {fuel : Nat} {r : DeclInfo} {st st' : MState} {b : Nat} {c : Bool}
    (h : Runs (Ochr.declCopy fuel r) st b c st') : st' = st :=
  runs_keep ((decideKeep fuel).2.2.2.1 r) h

end Ochr.Meaning.Steps.Slice
