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

**`KeptAfter` of a private computation** is assumed only of the generic sub-computations
(`RefineConv.GenericKept`, `RefineEq.EqKept`); everything else is proved.
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

/-! The statements first written here (`conv_refine`, `convFn_refine`, `convPi_refine`,
`mkEqM_refine`, under a machine-wide `CounterMono`) are superseded by the proved
`RefineConv.conv_refine'`, `RefineConv.conv_refine_same` and `RefineEq.mkEqM_refine'`, whose one
assumption is narrower: the generic sub-computations (`convPi`, `convFnRun`) and [Eq-inj]'s field
types (`fieldTypesOf`) keep the state as a private computation does (`GenericKept`, `EqKept`). The
induction threads the relation through every sub-call from the comparison's start, so no
machine-wide monotonicity of the label counter is needed. -/

end Ochr.Meaning.Rules
