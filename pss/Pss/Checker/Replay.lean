import Pss.Checker.Term
import Pss.Checker.PathSelector
import Pss.Checker.Reduction
import Pss.Checker.Subtyping
import Pss.Checker.OrSplit
import Pss.Checker.MacroExpand
import Pss.Checker.Refl

/-! # `Pss.Checker.Replay` — Replay interpreter for proof traces

Verbatim port of `pss/checker-artifact/src/replay.el`.

The replay action language:
* `start-term <t>`           : initialize the start term.
* `start-goal <t>`           : initialize the start objective.
* `rewrite <action> [opts]`  : apply a rewrite action.  The `:on-objectives`
  flag chooses term vs goal; `:path` is the path within the chosen side.
* `qed`                      : assert α-equivalence and discharge the current
  goal.
* `commit`                   : checkpoint (no semantics).
* `focus <i>`                : switch to goal `i`.

Rewrite actions:
* `beta-substitute`        — single β-step at path
* `beta-substitute-all`    — full β-normalisation at path
* `macro-expand`           — expand the macro at path
* `macro-collapse`         — collapse to a macro reference at path (no-op if none)
* `promote`                — promote at path
* `split-or-all`           — split an OR into alternatives, creating new goals
* `(objective-or-split n)` — substitute the n-th alternative directly
-/

namespace Pss.Checker

/-- The set of rewrite operations replicating `*action-function-map*`. -/
inductive RewriteOp where
  | betaSubstitute
  | betaSubstituteAll
  | macroExpand
  | macroCollapse
  | promote
  | splitOrAll
  | objectiveOrSplit (n : Nat)
  deriving Repr, BEq

namespace Replay

open Pss.Checker.Term

/-- Where a rewrite acts: on the current term or the current objective. -/
inductive Side where | onTerm | onGoal
  deriving Repr, BEq

/-- A single replay action. -/
inductive Act where
  | startTerm (t : Term)
  | startGoal (t : Term)
  | rewrite (op : RewriteOp) (side : Side) (path : Term.Path)
  | qed
  | commit
  | focus (i : Nat)
  deriving Repr

/-- A single proof goal: a term and its objective. -/
structure Goal where
  term : Term
  objective : Term
  deriving Repr

/-- Replay state: list of goals (head is current focus), focus index, plus the
    initial seeds. -/
structure State where
  startTerm : Option Term := none
  startGoal : Option Term := none
  goals : List Goal := []
  focus : Nat := 0
  deriving Repr

/-- Errors produced during replay. -/
inductive Error where
  | noGoals
  | focusOutOfBounds (i : Nat) (len : Nat)
  | termAlreadyInit
  | goalAlreadyInit
  | invalidPath (path : Term.Path) (term : Term)
  | reductionFailed (op : RewriteOp) (path : Term.Path) (term : Term)
  | qedNotAlphaEquivalent (term goal : Term)
  deriving Repr

/-- Apply a single primitive rewrite to a term at a path. -/
def applyOp (defs : Term.Defs) (op : RewriteOp) (target : Term) (path : Term.Path) :
    Option (Term ⊕ List Term) :=
  match op with
  | .betaSubstitute =>
    (Term.betaSubstituteAtPath target path).map Sum.inl
  | .betaSubstituteAll =>
    (Term.betaSubstituteAllAtPath target path).map Sum.inl
  | .macroExpand =>
    (Term.macroExpandAtPath defs target path).map Sum.inl
  | .macroCollapse =>
    (Term.macroCollapseAtPath defs target path).map Sum.inl
  | .promote =>
    (Term.promoteAtPath target path).map Sum.inl
  | .splitOrAll =>
    -- `splitOrAtPathAll` already returns the list of substituted super-terms.
    (Term.splitOrAtPathAll target path).map Sum.inr
  | .objectiveOrSplit n =>
    (Term.splitOrAtPath target path n).map Sum.inl

/-- Replace the current goal's term-or-objective. -/
def updateCurrent (st : State) (side : Side) (newVal : Term) : State :=
  { st with
    goals :=
      st.goals.mapIdx (fun i g =>
        if i == st.focus then
          match side with
          | .onTerm => { g with term := newVal }
          | .onGoal => { g with objective := newVal }
        else g) }

/-- Insert additional goals (from a split) immediately after the focus. -/
def insertGoalsAfter (st : State) (extra : List Goal) : State :=
  let head := st.goals.take (st.focus + 1)
  let tail := st.goals.drop (st.focus + 1)
  { st with goals := head ++ extra ++ tail }

/-- Initialize the goals if both the start-term and start-goal are present. -/
def initGoalsIfReady (s : State) : State :=
  match s.startTerm, s.startGoal with
  | some t, some g => { s with goals := [{ term := t, objective := g }], focus := 0 }
  | _, _ => s

/-- Process a single replay action. -/
def step (defs : Term.Defs) (st : State) (act : Act) : Except Error State := do
  match act with
  | .startTerm t =>
    if st.startTerm.isSome then throw .termAlreadyInit
    pure (initGoalsIfReady { st with startTerm := some t })
  | .startGoal t =>
    if st.startGoal.isSome then throw .goalAlreadyInit
    pure (initGoalsIfReady { st with startGoal := some t })
  | .rewrite op side path =>
    if st.goals.isEmpty then throw .noGoals
    if h : st.focus < st.goals.length then
      let g := st.goals[st.focus]
      let target := match side with | .onTerm => g.term | .onGoal => g.objective
      match applyOp defs op target path with
      | none => throw (.reductionFailed op path target)
      | some (Sum.inl newVal) =>
        pure (updateCurrent st side newVal)
      | some (Sum.inr (first :: rest)) =>
        let stUpdated := updateCurrent st side first
        let extras : List Goal := rest.map (fun newVal =>
          match side with
          | .onTerm => { term := newVal, objective := g.objective }
          | .onGoal => { term := g.term, objective := newVal })
        pure (insertGoalsAfter stUpdated extras)
      | some (Sum.inr []) =>
        throw (.reductionFailed op path target)
    else
      throw (.focusOutOfBounds st.focus st.goals.length)
  | .qed =>
    if st.goals.isEmpty then throw .noGoals
    if h : st.focus < st.goals.length then
      let g := st.goals[st.focus]
      if Term.alphaEquivalentP g.term g.objective then
        let newGoals := (st.goals.take st.focus) ++ (st.goals.drop (st.focus + 1))
        let newFocus :=
          if newGoals.isEmpty then 0
          else if st.focus < newGoals.length then st.focus
          else newGoals.length - 1
        pure { st with goals := newGoals, focus := newFocus }
      else
        throw (.qedNotAlphaEquivalent g.term g.objective)
    else
      throw (.focusOutOfBounds st.focus st.goals.length)
  | .commit => pure st
  | .focus i =>
    if i >= st.goals.length then throw (.focusOutOfBounds i st.goals.length)
    pure { st with focus := i }

/-- Replay a list of actions starting from the empty state. -/
def run (defs : Term.Defs) (acts : List Act) : Except Error State :=
  acts.foldlM (step defs) {}

/-- True iff the replay terminates with all goals discharged. -/
def runOk (defs : Term.Defs) (acts : List Act) : Bool :=
  match run defs acts with
  | .ok st => st.goals.isEmpty
  | .error _ => false

end Replay
end Pss.Checker
