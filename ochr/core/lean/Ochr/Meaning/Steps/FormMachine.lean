import Ochr.Meaning.Steps.FormKern

/-!
# Facts about the checker alone that the column of `Steps/Form.lean` uses (lead7; for the machine lane)

Each is a statement about the checker's runs with no model in it (`Kern`, `Mode`, `Inv` and `DecTab`
are the checker's), stated here as a `Prop` and taken as a hypothesis by the column's lemmas; none is
proved here. They are of three kinds:

* **inversions**: a successful run of a checker function is made of the sub-runs its code makes, at
  states whose kernel (`Kern`) is given (the bookkeeping fields between them are not);
* **preservation**: the checker's syntactic invariant (`Inv`) holds after a run that started from it;
* **alignment**: where the checker reads a decision (the erasure pre-pass, a binding's reading, the
  copy decision), the answer is the aligned table's (`DecTab`).

Every one is read off `Machine.lean` at `spine` 3347196b; the docstring of each says which code.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **The mode of an evaluation's entry**: not a call's head (`headEval`: the pre-pass classifies the
term), not inside `clone`/`peek` (`copying`) or in place (`inPlace`), not inside an erased term
(`erasedDepth`): where the checker's read moves exactly when the strict run's does. A step statement
without it is false: inside `clone(x)` the checker's read of `x` copies where the strict run's
`.place` clause moves. -/
structure Mode (st : MState) : Prop where
  headEval : st.headEval = false
  copying : st.copying = false
  inPlace : st.inPlace = false
  erased : st.erasedDepth = 0

/-- **`eval` around `evalCore`** (`Machine.eval`, `evalAt`), for a term the pre-pass does not erase:
`eval (n + 2)` runs `evalCore n` from a state with the same kernel, the one-shot tail flag moved to
`curTail` and cleared, in the same mode, and ends with the kernel `evalCore` left (the after-the-fact
classification agrees with the pre-pass and restores nothing). "Does not erase" is read from the
aligned table: where it classifies the term as neither a statement nor a proof at the top frame's
readings, so does the checker's pre-pass, at the term's own reading or at the one its context hands
it (`tailDecl`). The table is the one aligned at the end of the run (`DecTab.back` carries it to
the start). -/
def EvalInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    Mode st → DecTab D st' → D.flags (DecideScope.topReadings st) t = (false, false) → (∀ w, t ≠ .val w) →
    Runs (Ochr.eval (n + 2) typed t hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (bh' : Nat), Kern st st₀ ∧ Mode st₀ ∧ st₀.curTail = st.tailNext ∧ st₀.tailNext = false ∧
      Runs (Ochr.evalCore n typed t hint) st₀ bh' (v, T?) st₁ ∧ Kern st₁ st' ∧ (Mode st₁ → Mode st')

/-- **`evalCore` of `Z`**: the value `Z` at `Nat`, the kernel and the mode as they were. -/
def ZeroInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Runs (Ochr.evalCore (n + 1) typed .zero hint) st bh (v, T?) st' →
    v = .zero ∧ T? = some .tNat ∧ Kern st st' ∧ (Mode st → Mode st')

/-- **The invariant is kept by `evalCore`, its result counted** (part (c), for the forms of the column):
from a state meeting `Inv` at decisions aligned with the checker at the end, a successful run of
`evalCore` ends at one meeting `Inv` with its value in flight at its stored type. -/
def InvCore : Prop :=
  ∀ (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions) (Γ : List IndDecl),
    Inv D Γ st.norm → DecTab D st' → Runs (Ochr.evalCore n typed t hint) st bh (v, T?) st' →
    Inv D Γ (st'.withTempT v T?).norm

end Ochr.Meaning.Steps.Form
