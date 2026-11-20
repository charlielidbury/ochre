import Ochr.Meaning.Rules.Conv

/-!
# The rules trial, part B: a successful run of the machine gives a derivation

No assignment, no model: a statement about the checker's code and the relations of `Rules/Conv`.
Each conclusion is a derivation in the machine's instance of the untyped parts (`Syn.machine`) and
the machine's instance of the premises (`machPremises`), plus the machine-side fact about the state
after (`KeptAfter`).

**The premises' instance mentions `MState`.** [Conv-fun]'s and [Conv-pi]'s premise is "the
machine's run of exactly that sub-computation succeeded", and that run starts from a state the
comparison reached, not from the comparison's start: earlier sub-comparisons (the Π-types before
the observations, the codomain after the parameters) are private computations that grow the
tables, and a later one runs from what they left. So the instance names the state the
sub-computation starts from (`Reach`), and the premises' soundness, which part A assumes, is a
statement about machine runs from such states.

**`KeptAfter` of a private computation needs a machine-wide fact**: `restoreKeep` keeps the copy's
label counter, so the counter after is the inner run's, and `KeptAfter` asks it not to have gone
down: the whole machine (every function a generic call can reach) never lowers `nextLoan`
(`closeBlock`'s re-check of an arm's return `set`s an earlier state and then restores a later one).
That is a statement about all of `Machine.lean`, model-free; it is a named hypothesis here.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning.Steps

/-- A sub-computation of a comparison starts from the comparison's start with its tables grown by
the private sub-computations before it: Ω, the goal, the refinements, the declarations, Σ and the
comparison stack kept. -/
def Reach (st st₁ : MState) : Prop :=
  KeptAfter st st₁ ∧ st₁.globals = st.globals ∧ st₁.convStack = st.convStack

/-- The premises, instantiated with the machine's successful runs of exactly those
sub-computations, from a state `R`-related to the comparison's start (`R` is `Reach` for the
checker as it is; equality for a checker whose comparisons restore their start state). -/
def machPremisesR (R : MState → MState → Prop) (st : MState) : Premises where
  fn f g := ∃ (st₁ st₂ : MState) (fuel bh : Nat) (pf : Value) (cs : List Value) (hs : List Hint)
      (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)),
    R st st₁ ∧ fnTyOf st.globals f = some pf ∧ pf = .tPi cs (.pi hs ds c) rd ∧
      Runs (Ochr.convFnRun fuel f g pf cs hs ds c) st₁ bh true st₂
  pi P Q := ∃ (st₁ st₂ : MState) (fuel bh : Nat), R st st₁ ∧ Runs (Ochr.convPi fuel P Q) st₁ bh true st₂
  fieldTys d args c fs Ts := ∃ (st₁ st₂ : MState) (fuel bh : Nat) (Ts' : List (String × Value)),
    R st st₁ ∧ Runs (Ochr.fieldTypesOf fuel d args c fs) st₁ bh Ts' st₂ ∧ Ts = Ts'.map (·.2)

/-- The checker as it is: sub-computations start from states the comparison reached. -/
abbrev machPremises (st : MState) : Premises := machPremisesR Reach st

/-- A computation that never lowers the label counter. -/
def CounterMonoOf {α : Type} (x : M α) : Prop :=
  ∀ (st st' : MState) (bh : Nat) (a : α), Runs x st bh a st' → st.nextLoan ≤ st'.nextLoan

/-- The machine-wide fact `KeptAfter` needs: no run of the checker lowers the label counter, for
the computations a comparison runs privately (the generic calls, which reach the whole machine,
and the types). A hypothesis of every statement below (open; model-free). -/
def CounterMono : Prop :=
  (∀ fuel typed t hint, CounterMonoOf (Ochr.eval fuel typed t hint)) ∧
  (∀ fuel typed fv fT ws ts head cls rec res fills want defer,
    CounterMonoOf (Ochr.callFn fuel typed fv fT ws ts head cls rec res fills want defer))

/-- **(B) `conv`**: a successful comparison is a derivation of the machine's instance, and leaves
the state as a private computation does. -/
theorem conv_refine (hmono : CounterMono) (fuel : Nat) (st st' : MState) (v w : Value) (bh : Nat)
    (h : Runs (Ochr.conv fuel v w) st bh true st') :
    ConvV Syn.machine (machPremises st) st.globals v w ∧ KeptAfter st st' := by
  sorry

/-- (B) `convFn`: [Conv-fun]'s conclusion. -/
theorem convFn_refine (hmono : CounterMono) (fuel : Nat) (st st' : MState) (f g : Value) (bh : Nat)
    (h : Runs (Ochr.convFn fuel f g) st bh true st') :
    ConvH Syn.machine (machPremises st) st.globals f g ∧ KeptAfter st st' := by
  sorry

/-- (B) `convPi`: its own premise, and the state after. -/
theorem convPi_refine (hmono : CounterMono) (fuel : Nat) (st st' : MState) (P Q : Value) (bh : Nat)
    (h : Runs (Ochr.convPi fuel P Q) st bh true st') :
    (machPremises st).pi P Q ∧ KeptAfter st st' := by
  sorry

/-- **(B) `mkEqM`**: the proposition it builds is one `Eq` computes to by the rules. -/
theorem mkEqM_refine (hmono : CounterMono) (fuel : Nat) (st st' : MState) (A a b P : Value) (bh : Nat)
    (h : Runs (Ochr.mkEqM fuel A a b) st bh P st') :
    EqTo Syn.machine (machPremises st) st.globals st.inds A a b P ∧ KeptAfter st st' := by
  sorry

end Ochr.Meaning.Rules
