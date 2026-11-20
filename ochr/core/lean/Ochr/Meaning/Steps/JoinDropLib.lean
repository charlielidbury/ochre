import Ochr.Meaning.Steps.IH
import Ochr.Meaning.RunLib

/-!
# The drop at the join, compositionally (docs/31 D29, task C)

The checker's drop at the join is a loop over the join's list (`Machine.joinDrop`:
`for q in drops do dropAtJoin (← movedPlace q)`), the reference's a fold over the same list
(`joinDrop`, one `joinDropOne` per place). This file takes the loop apart into its steps (a run of
the loop is a run of its first body and a run of the rest, from the state and budget it left) and
shows the reference's drop of one place keeps the declared readings, so the scope the join's list
is read in is the same at every step.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-! ## The loop, taken apart -/

/-- The checker's drop loop. -/
abbrev dropLoop (fuel : Nat) (qs : List Place) : M Unit :=
  do for q in qs do Ochr.dropAtJoin fuel (← Ochr.movedPlace fuel q)

/-- The checker's drop of one place. -/
abbrev dropBody (fuel : Nat) (q : Place) : M Unit :=
  do Ochr.dropAtJoin fuel (← Ochr.movedPlace fuel q)

/-- The body of the loop: the drop of one place, then `yield`. -/
abbrev loopBody (fuel : Nat) : Place → Unit → M (ForInStep Unit) := fun q _ => do
  let d ← Ochr.movedPlace fuel q; Ochr.dropAtJoin fuel d; pure (ForInStep.yield ())

theorem dropLoop_eq (fuel : Nat) (qs : List Place) :
    dropLoop fuel qs = (forIn qs () (loopBody fuel) >>= fun _ => pure ()) := rfl

theorem loopBody_eq (fuel : Nat) (q : Place) :
    loopBody fuel q () = (dropBody fuel q >>= fun _ => pure (ForInStep.yield ())) := by
  simp only [loopBody, dropBody, bind_assoc]

/-- `x >>= fun _ => pure y` succeeds exactly where `x` does, with `y`. -/
theorem runMachineL_bind_pure_ok {α β : Type} {x : M α} {y : β} {st st' : MState} {b b' : Nat}
    {L L' : Array LogEntry} {z : β}
    (h : runMachineL (x >>= fun _ => pure y) st b L = (.ok z st', b', L')) :
    ∃ a, runMachineL x st b L = (.ok a st', b', L') ∧ z = y := by
  rw [runMachineL_bind] at h
  rcases e : runMachineL x st b L with ⟨o, b₁, L₁⟩
  rw [e] at h
  rcases o with ⟨a, st₁⟩ | f | m
  · simp only [runMachineL_pure, Prod.mk.injEq, Outcome.ok.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    exact ⟨a, rfl, rfl⟩
  · cases h
  · cases h

/-- A run of the loop on a nonempty list is a run of its first body and a run of the rest. -/
theorem runs_dropLoop_cons {fuel : Nat} {q : Place} {qs : List Place} {st st' : MState} {b : Nat}
    (h : Runs (dropLoop fuel (q :: qs)) st b () st') :
    ∃ st₁ b₁, Runs (dropBody fuel q) st b () st₁ ∧ Runs (dropLoop fuel qs) st₁ b₁ () st' := by
  obtain ⟨L, left, log, h⟩ := h
  rw [dropLoop_eq] at h
  obtain ⟨u, hf, -⟩ := runMachineL_bind_pure_ok h
  rw [List.forIn_cons, runMachineL_bind] at hf
  rcases e : runMachineL (loopBody fuel q ()) st b L with ⟨o, b₁, L₁⟩
  rw [e] at hf
  rcases o with ⟨r, st₁⟩ | f | m
  · rw [loopBody_eq] at e
    obtain ⟨u', hb, rfl⟩ := runMachineL_bind_pure_ok e
    refine ⟨st₁, b₁, ⟨L, b₁, L₁, hb⟩, ⟨L₁, left, log, ?_⟩⟩
    rw [dropLoop_eq, runMachineL_bind]
    simp only at hf
    rw [hf]
    rfl
  · cases hf
  · cases hf

/-- A run of the loop on the empty list leaves the state. -/
theorem runs_dropLoop_nil {fuel : Nat} {st st' : MState} {b : Nat} (h : Runs (dropLoop fuel []) st b () st') :
    st' = st := by
  obtain ⟨L, left, log, h⟩ := h
  have e : runMachineL (dropLoop fuel []) st b L = (.ok () st, b, L) := rfl
  rw [e] at h
  simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
  exact h.1.2.symm

/-! ## The reference's drop keeps the declared readings -/

/-- The declared readings of every frame's bindings (what `scopeOf` reads). -/
def declsOf (s : SState) : List (List DeclInfo) := s.env.map fun fr => fr.binds.map (·.decl)

theorem scopeOf_of_declsOf {s s' : SState} (h : declsOf s = declsOf s') : scopeOf s = scopeOf s' := by
  unfold scopeOf
  have e : (s.env.getLast?).map (fun fr => fr.binds.map (·.decl)) = (s'.env.getLast?).map (fun fr => fr.binds.map (·.decl)) := by
    rw [← List.getLast?_map, ← List.getLast?_map]; exact congrArg List.getLast? h
  cases h1 : s.env.getLast? <;> cases h2 : s'.env.getLast? <;> rw [h1, h2] at e <;> simp_all

theorem map_modify_eq {α β : Type _} {g : α → β} {f : α → α} (hf : ∀ x, g (f x) = g x) (l : List α) (i : Nat) :
    (l.modify i f).map g = l.map g := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_modify]
  by_cases h : i = j <;> cases l[j]? <;> simp [h, hf]

theorem map_zipIdx_eq {α β γ : Type _} {h : β → γ} {F : α → Nat → β} {g : α → γ} (hF : ∀ x i, h (F x i) = g x)
    (l : List α) : (l.zipIdx.map fun p => F p.1 p.2).map h = l.map g := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  cases l[j]? <;> simp [hF]

theorem declsOf_setAt (s : SState) (p : Pos) (v : SVal) : declsOf (s.setAt p v) = declsOf s := by
  cases p with
  | bind f i =>
    simp only [declsOf, SState.setAt]
    apply map_modify_eq
    intro fr
    show (fr.binds.modify i _).map _ = _
    apply map_modify_eq
    intro _; rfl
  | temp f i =>
    simp only [declsOf, SState.setAt]
    apply map_modify_eq
    intro _; rfl

theorem declsOf_mapVals (s : SState) (g : Pos → SVal → SVal) : declsOf (s.mapVals g) = declsOf s := by
  unfold declsOf SState.mapVals
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  cases s.env[j]? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, Option.some.injEq]
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_map, List.getElem?_zipIdx]
    cases fr.binds[k]? <;> rfl

theorem declsOf_endLabel (s : SState) (l : Nat) : declsOf (s.endLabel l) = declsOf s := by
  cases h : s.positions.find? (fun p => decide (s.shape p = some l)) with
  | none => rw [SState.endLabel_of_find_none s l h]
  | some r => rw [SState.endLabel_of_find s l r h, declsOf_mapVals]; rfl

theorem declsOf_foldl_endLabel : ∀ (ls : List Nat) (s : SState), declsOf (ls.foldl SState.endLabel s) = declsOf s
  | [], _ => rfl
  | l :: ls, s => by rw [List.foldl_cons, declsOf_foldl_endLabel ls, declsOf_endLabel]

theorem declsOf_access (s : SState) (p : Pos) (hit : List Step → Bool) : declsOf (s.access p hit) = declsOf s := by
  rw [SState.access_eq, SState.foldl_range_iterR]
  generalize s.liveLabels.length = k
  induction k with
  | zero => rfl
  | succ k ih => exact (declsOf_foldl_endLabel _ _).trans ih

theorem declsOf_joinDropOne (K : RunCtx) (φ : Future) (s : SState) (q : Place) :
    declsOf (joinDropOne K φ s q) = declsOf s := by
  unfold joinDropOne
  split
  · rename_i pos steps _
    have h₁ : declsOf (accessLentPrefix pos steps s) = declsOf s := by
      unfold accessLentPrefix; split
      · exact declsOf_access _ _ _
      · rfl
    refine Eq.trans ?_ h₁
    generalize accessLentPrefix pos steps s = s₁
    unfold dropAt
    split
    · exact declsOf_endLabel _ _
    · split
      all_goals first
        | rfl
        | (split
           · rfl
           · exact (declsOf_setAt _ _ _).trans (declsOf_access _ _ _))
  · rfl

theorem scopeOf_joinDropOne (K : RunCtx) (φ : Future) (s : SState) (q : Place) :
    scopeOf (joinDropOne K φ s q) = scopeOf s :=
  scopeOf_of_declsOf (declsOf_joinDropOne K φ s q)

end Ochr.Meaning.Steps
