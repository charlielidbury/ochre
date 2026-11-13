import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib

/-!
# Runs of the machine, compositionally

`Runs x st fuel a st'` (`Statements.lean`) forgets the fuel left and the log, so it does not
compose: the second half of `x >>= k` starts with the fuel the first half left. `runMachineL`
keeps the whole state of the stack (the outcome, the fuel left, the log, from a starting log),
and `runMachineL_bind` is the law provers thread a `do` block with; `Runs` is its `#[]` case.
-/

namespace Ochr.Meaning.Steps

open Ochr

/-- `runMachine` from a given log. -/
def runMachineL {α : Type} (x : M α) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    Outcome α × Nat × Array LogEntry :=
  let ((r, fl), log) := (((((x.run st).run).run).run ⟨fuel⟩).run L)
  let o := match r with
    | .error e => Outcome.exhausted e.msg
    | .ok (.error f) => .fail f
    | .ok (.ok (a, st')) => .ok a st'
  (o, fl.left, log)

theorem runMachine_eq_L {α : Type} (x : M α) (st : MState) (fuel : Nat) :
    runMachine x st fuel = runMachineL x st fuel #[] := rfl

theorem runs_iff_L {α : Type} (x : M α) (st : MState) (fuel : Nat) (a : α) (st' : MState) :
    Runs x st fuel a st' ↔ ∃ left log, runMachineL x st fuel #[] = (.ok a st', left, log) := Iff.rfl

/-- The bind law of the stack. -/
theorem runMachineL_bind {α β : Type} (x : M α) (k : α → M β) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (x >>= k) st fuel L =
      match runMachineL x st fuel L with
      | (.ok a st', left, log) => runMachineL (k a) st' left log
      | (.fail f, left, log) => (.fail f, left, log)
      | (.exhausted m, left, log) => (.exhausted m, left, log) := by
  simp only [runMachineL]
  rw [StateT.run_bind, ExceptT.run_bind, ExceptT.run_bind, StateT.run_bind, StateT.run_bind]
  generalize hx : StateT.run ((StateT.run x st).run.run.run { left := fuel }) L = p
  obtain ⟨⟨r, fl⟩, log⟩ := p
  rcases r with e | f | ⟨a, st'⟩
  all_goals first | rfl | (simp [runMachineL])

/-! ## The primitives -/

section
variable {α : Type} (st : MState) (fuel : Nat) (L : Array LogEntry)

theorem runMachineL_pure (a : α) : runMachineL (pure a : M α) st fuel L = (.ok a st, fuel, L) := rfl
theorem runMachineL_get : runMachineL (get : M MState) st fuel L = (.ok st st, fuel, L) := rfl
theorem runMachineL_set (st' : MState) : runMachineL (set st' : M Unit) st fuel L = (.ok () st', fuel, L) := rfl
theorem runMachineL_modify (g : MState → MState) :
    runMachineL (modify g : M Unit) st fuel L = (.ok () (g st), fuel, L) := rfl
theorem runMachineL_err (msg : String) :
    runMachineL (err msg : M α) st fuel L = (.fail (.error msg), fuel, L) := rfl
theorem runMachineL_exhausted (msg : String) :
    runMachineL (exhausted msg : M α) st fuel L = (.exhausted msg, fuel, L) := rfl

end

/-! ## Loops over a list (the checker's `for p in allPos … do`) -/

theorem runMachineL_forIn_nil {β : Type} (body : Pos → β → M (ForInStep β)) (b : β)
    (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (forIn ([] : List Pos) b body) st fuel L = (.ok b st, fuel, L) := rfl

/-- One step of a loop: the body, then the rest on its state and fuel. -/
theorem runMachineL_forIn_cons {β : Type} (p : Pos) (ps : List Pos) (body : Pos → β → M (ForInStep β)) (b : β)
    (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (forIn (p :: ps) b body) st fuel L =
      match runMachineL (body p b) st fuel L with
      | (.ok (.yield b') st', left, log) => runMachineL (forIn ps b' body) st' left log
      | (.ok (.done b') st', left, log) => (.ok b' st', left, log)
      | (.fail f, left, log) => (.fail f, left, log)
      | (.exhausted m, left, log) => (.exhausted m, left, log) := by
  rw [List.forIn_cons, runMachineL_bind]
  cases runMachineL (body p b) st fuel L with
  | mk o rest =>
    obtain ⟨left, log⟩ := rest
    cases o with
    | ok r st' => cases r <;> rfl
    | fail f => rfl
    | exhausted m => rfl

/-! ## `mapState` without types: the loop over the positions -/

theorem runMachineL_getAt (p : Pos) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (getAt p) st fuel L = (.ok (valAt st.env p) st, fuel, L) := by
  cases p <;> rfl

theorem runMachineL_setAt (p : Pos) (v : Value) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (Ochr.setAt p v) st fuel L = (.ok () { st with env := Env.setAtE st.env p v }, fuel, L) := by
  cases p <;> rfl

/-- The body of `mapState`'s loop at a position, without types. -/
def mapBody (f : Value → M Value) (p : Pos) (_ : PUnit) : M (ForInStep PUnit) := do
  Ochr.setAt p (← f (← getAt p))
  pure (ForInStep.yield ⟨⟩)

/-- Loops whose bodies run the same run the same. -/
theorem forIn_congr_run {β : Type} (body₁ body₂ : Pos → β → M (ForInStep β))
    (h : ∀ p b st fuel L, runMachineL (body₁ p b) st fuel L = runMachineL (body₂ p b) st fuel L) :
    ∀ (l : List Pos) (b : β) (st : MState) (fuel : Nat) (L : Array LogEntry),
      runMachineL (forIn l b body₁) st fuel L = runMachineL (forIn l b body₂) st fuel L
  | [], b, st, fuel, L => rfl
  | p :: l, b, st, fuel, L => by
    rw [runMachineL_forIn_cons, runMachineL_forIn_cons, h]
    cases runMachineL (body₂ p b) st fuel L with
    | mk o rest =>
      obtain ⟨left, log⟩ := rest
      cases o with
      | ok r st' => cases r <;> simp only [forIn_congr_run body₁ body₂ h l]
      | fail e => rfl
      | exhausted m => rfl

/-- A `Bool` test that is `false` runs its else branch. -/
theorem runMachineL_ite_false {α : Type} (A B : M α) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (if false = true then A else B) st fuel L = runMachineL B st fuel L := by
  simp

/-- One position of the walk: `f` on the position's value, then the position set to its result. -/
theorem runMachineL_mapBody (f : Value → M Value) (p : Pos) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (mapBody f p ⟨⟩) st fuel L =
      match runMachineL (f (valAt st.env p)) st fuel L with
      | (.ok v' s', left, log) => (.ok (.yield ⟨⟩) { s' with env := Env.setAtE s'.env p v' }, left, log)
      | (.fail e, left, log) => (.fail e, left, log)
      | (.exhausted m, left, log) => (.exhausted m, left, log) := by
  simp only [mapBody]
  rw [runMachineL_bind, runMachineL_getAt]
  simp only
  rw [runMachineL_bind]
  cases runMachineL (f (valAt st.env p)) st fuel L with
  | mk o rest =>
    obtain ⟨left, log⟩ := rest
    cases o with
    | ok v' s' => dsimp only; rw [runMachineL_bind, runMachineL_setAt]; rfl
    | fail e => rfl
    | exhausted m => rfl

/-- `mapState f false` runs as the loop over the positions with `mapBody` (the `types` branches
are off). -/
theorem runMachineL_mapState_false (f : Value → M Value) (st : MState) (fuel : Nat) (L : Array LogEntry) :
    runMachineL (mapState f false) st fuel L = runMachineL (forIn (allPos st.env) ⟨⟩ (mapBody f)) st fuel L := by
  unfold mapState
  rw [runMachineL_bind, runMachineL_get]
  dsimp only
  rw [runMachineL_bind]
  rw [forIn_congr_run _ (mapBody f) ?hb]
  · cases runMachineL (forIn (allPos st.env) ⟨⟩ (mapBody f)) st fuel L with
    | mk o rest =>
      obtain ⟨left, log⟩ := rest
      cases o with
      | ok r s' => cases r; dsimp only; rw [runMachineL_ite_false, runMachineL_pure]
      | fail e => rfl
      | exhausted m => rfl
  · -- the actual loop body runs as `mapBody`: its `types` branches are off
    intro p b st fuel L
    cases b
    simp only [mapBody]
    rw [runMachineL_bind, runMachineL_bind, runMachineL_getAt]
    dsimp only
    rw [runMachineL_bind, runMachineL_bind]
    cases runMachineL (f (valAt st.env p)) st fuel L with
    | mk o rest =>
      obtain ⟨left, log⟩ := rest
      cases o with
      | ok y s' =>
        dsimp only
        rw [runMachineL_bind, runMachineL_bind, runMachineL_setAt]
        dsimp only
        rw [runMachineL_ite_false]
      | fail e => rfl
      | exhausted m => rfl

/-! ## The walk's specification: a fold of per-position outputs -/

theorem foldl_congr_mem {α β : Type _} (g g' : β → α → β) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b, g b x = g' b x) → l.foldl g b = l.foldl g' b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h x (List.mem_cons_self ..) b]
    exact foldl_congr_mem g g' l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **The walk as a fold.** Over distinct positions, with `f` leaving the environment as it
found it, a successful loop writes at each position an output of `f` on that position's
original value (run from some intermediate state), and nothing else: the final environment is
the fold of the outputs. -/
theorem loop_spec (f : Value → M Value)
    (hf : ∀ (v : Value) (s s' : MState) (fuel left : Nat) (L log : Array LogEntry) (v' : Value),
      runMachineL (f v) s fuel L = (.ok v' s', left, log) → s'.env = s.env) :
    ∀ (ps : List Pos) (st st' : MState) (fuel left : Nat) (L log : Array LogEntry),
      ps.Nodup →
      runMachineL (forIn ps ⟨⟩ (mapBody f)) st fuel L = (.ok ⟨⟩ st', left, log) →
      ∃ out : Pos → Value,
        st'.env = ps.foldl (fun e p => Env.setAtE e p (out p)) st.env ∧
        ∀ p ∈ ps, ∃ (s s' : MState) (fuel' left' : Nat) (L' log' : Array LogEntry),
          runMachineL (f (valAt st.env p)) s fuel' L' = (.ok (out p) s', left', log')
  | [], st, st', fuel, left, L, log, _, h => by
    rw [runMachineL_forIn_nil] at h
    simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
    exact ⟨fun _ => .zero, by simp [← h.1.2], fun p hp => by cases hp⟩
  | p :: ps, st, st', fuel, left, L, log, hnd, h => by
    rw [runMachineL_forIn_cons, runMachineL_mapBody] at h
    revert h
    cases hr : runMachineL (f (valAt st.env p)) st fuel L with
    | mk o rest =>
      obtain ⟨left₁, log₁⟩ := rest
      cases o with
      | fail e => intro h; simp at h
      | exhausted m => intro h; simp at h
      | ok v' s₁ =>
        intro h
        dsimp only at h
        have henv := hf _ _ _ _ _ _ _ _ hr
        have hnd' := List.nodup_cons.mp hnd
        obtain ⟨out', hfold, hpos⟩ := loop_spec f hf ps { s₁ with env := Env.setAtE s₁.env p v' } st' left₁ left log₁ log hnd'.2 h
        refine ⟨fun q => if q = p then v' else out' q, ?_, ?_⟩
        · rw [hfold]
          simp only [List.foldl_cons, if_true, henv]
          apply foldl_congr_mem
          intro q hq e
          have : q ≠ p := fun h => hnd'.1 (h ▸ hq)
          simp [this]
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact ⟨st, s₁, fuel, left₁, L, log₁, by simp [hr]⟩
          · have hqp : q ≠ p := fun h => hnd'.1 (h ▸ hq')
            obtain ⟨s, s', fuel', left', L', log', hrun⟩ := hpos q hq'
            refine ⟨s, s', fuel', left', L', log', ?_⟩
            simp only [henv, valAt_setAtE_other _ _ _ _ hqp] at hrun
            simpa [hqp] using hrun

end Ochr.Meaning.Steps
