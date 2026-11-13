import Ochr.Meaning.Sem
import Ochr.Meaning.Data
import Ochr.Meaning.DataGeneric
import Ochr.Meaning.Future
import Ochr.Meaning.Value
import Ochr.Meaning.Pi
import Ochr.Meaning.SState
import Ochr.Meaning.Apply
import Ochr.Meaning.Apply1
import Ochr.Meaning.Places
import Ochr.Meaning.Run
import Ochr.Meaning.Subst
import Ochr.Meaning.Lemmas
import Ochr.Meaning.HintIndep
import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.PosLib
import Ochr.Meaning.RunLib
import Ochr.Meaning.Steps.IH
import Ochr.Meaning.Steps.Borrow
import Ochr.Meaning.Steps.Subst
import Ochr.Meaning.Steps.Eq
import Ochr.Meaning.Steps.Call
import Ochr.Meaning.Steps.Match
import Ochr.Meaning.Steps.Obs
import Ochr.Meaning.Steps.Types
import Ochr.Meaning.Steps.WF
import Ochr.Meaning.Steps.Eval
import Ochr.Meaning.Steps.Tail
import Ochr.Meaning.Steps.Decisions
import Ochr.Meaning.Steps.Knot
import Ochr.Meaning.Attack.CloseCall
import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Attack.CloseCallFwd
import Ochr.Meaning.Attack.CloseCallBack
import Ochr.Meaning.Consistency
import Ochr.Meaning.State
import Ochr.Meaning.WF
import Ochr.Meaning.Sanity
import Ochr.Meaning.Bounded
import Ochr.Meaning.Mono
import Ochr.Meaning.MonoHolders
import Ochr.Meaning.Program
import Ochr.Meaning.DecisionsInst
import Ochr.Meaning.DecideScope
import Ochr.Meaning.Regress.CE5_flipped
import Ochr.Meaning.Regress.CloseCallStmt
import Ochr.Meaning.Regress.CE4_flipped

/-!
# The consistency spine (`ochr/docs/18`, `ochr/docs/31`)

The meaning of the checker's types, values and states in a set-like model built from Lean's own
types, the reference run, and the statements of the step lemmas. `Ochr/docs/31-meaning-spine.md`
is the design note. Milestone 1 (this import list): the domain `Sem`/`TyM`, the data-type model,
assignments and futures, the meaning of every `Value` form, the meaning of an `MState`, the
well-formedness invariant and membership, sanity theorems, and the bounded-universe form of the
consistency statement (Q1).
-/
