import Ochr.Meaning.Steps.Statements

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

end Ochr.Meaning.Steps
