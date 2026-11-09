import Ochr.Meaning.Sem
import Ochr.Meaning.Data
import Ochr.Meaning.Future
import Ochr.Meaning.Value
import Ochr.Meaning.Pi
import Ochr.Meaning.SState
import Ochr.Meaning.Apply
import Ochr.Meaning.Places
import Ochr.Meaning.Run
import Ochr.Meaning.Subst
import Ochr.Meaning.Lemmas
import Ochr.Meaning.State
import Ochr.Meaning.WF
import Ochr.Meaning.Sanity
import Ochr.Meaning.Bounded

/-!
# The consistency spine (`ochr/docs/18`, `ochr/docs/31`)

The meaning of the checker's types, values and states in a set-like model built from Lean's own
types, the reference run, and the statements of the step lemmas. `Ochr/docs/31-meaning-spine.md`
is the design note. Milestone 1 (this import list): the domain `Sem`/`TyM`, the data-type model,
assignments and futures, the meaning of every `Value` form, the meaning of an `MState`, the
well-formedness invariant and membership, sanity theorems, and the bounded-universe form of the
consistency statement (Q1).
-/
