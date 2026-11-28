import Ochr.Meaning.Conv.Rules
import Ochr.Meaning.Strict.Typed
import Ochr.Meaning.Steps.Form

/-!
# N3, the soundness of conversion, stated on the proof line (conv1, 2026-11-28)

Whenever the checker identifies two things they mean the same: if `conv` answers "equal" for two
values, both hereditarily well typed at one type and read at one hint, their meanings are equal at
every assignment meeting the state; if `mkEqM` computes `Eq(A, a, b)` to `P`, then `P` means the
proposition `⟦a⟧ = ⟦b⟧` at `⟦A⟧` (the paper's `<sec-n3>`, docs/18 principle 2).

**Who consumes it** (each typed step of (II) that compares, `Steps/Master*.lean` and docs/31 D153):
- a type checked against a type (`expectTy`, a match's arms, [Def]'s leaf against the goal, `trans`'s
  middle type, the domains inside [Conv-pi]): `ConvTypeStmt`, equality of the two types' meanings
  read at the error hint, from which the strict clause's membership test at the expected type follows
  (`.ascribe`, `assignAt`, `ctorOut`, `callOf`'s decoding, `S`'s argument (`SuccStrictG`), `Eq`'s and
  `J`'s sides, `Id`'s sides, the result at the goal);
- two values compared at a type (`Eq`'s [Eq-refl] inside `mkEqM`, `J`'s endpoints, `trans`'s middle
  point): `ConvValStmt`, equality of meanings at the hint of their type;
- `Eq` computed (`.eq`, `Id`'s conjuncts, a re-normalised stored `Eq` in `substV`/`renormV`, `J`'s
  equation, `symm`, `trans`): `EqStmt`.
Each needs equality of meanings under every assignment the step's `Pre` admits, at the future the
step reads (the step's `φ`), and that the comparison changed only names (`NamesKept`, D103), so that
the step's relation to the reference state survives it.

**The typing hypothesis.** Membership of a value says nothing of the parts that do not decide it
(`Eq(Nat, And(True, Nat), Nat)` is a proposition; `Strict/Typed.eq_types_not_hwt`), and conversion
compares part by part, so the claim is about values hereditarily well typed, `Strict.HWT`. At a
consumer it comes from `Strict.hwt_of_fit`: the meaning fits (from (I) and (II): the checker's value
means the reference's result, a member) and the value holds no constructor value of a `Prop`
declaration (`NoProp`, a checker invariant: D42).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The claim** carried by every proof below: two values are alike when, read at any one hint,
holding no constructor value of a `Prop` declaration (`NoProp`, a checker invariant: D42) and both
fitting any one type there (`Fit`: `⊥`, a member, or at the error type a type value with a level),
they mean the same. One form for values at a type (hint `.plain T`) and for type values (hint and
type `err`: the type values a check compares). This is the form consumers hold: (I) and (II) give
the fit (the checker's value means the reference's result, which fits its type), the checker's
invariant gives `NoProp`; `Strict.hwt_of_fit` turns the two into "hereditarily well typed". -/
def Alike (v w : Value) : Prop :=
  ∀ (h : TyS) (T : TyM), NoProp K v → NoProp K w → Fit K.dm.read T (meanV K ρ φ h v) →
    Fit K.dm.read T (meanV K ρ φ h w) → meanV K ρ φ h v = meanV K ρ φ h w

/-- Alike, pointwise on two lists. -/
def AlikeL : List Value → List Value → Prop
  | [], [] => True
  | v :: vs, w :: ws => Alike K ρ φ v w ∧ AlikeL vs ws
  | _, _ => False

end

/-- **A comparison changed only names** (main's D103: `conv`, `convPi`, `convFn` put back the state
they started from, keeping only the fresh names made inside, `Env.restoreNames`): the state after
is the state before but for the name counters, which only grow, and the tables of unknowns' types
and frozen readings, which only grow at their ends. -/
def NamesKept (st st' : MState) : Prop :=
  st' = { st with nextAbs := st'.nextAbs, nextLoan := st'.nextLoan, nextRecUid := st'.nextRecUid,
                  absTy := st'.absTy, absDecl := st'.absDecl } ∧
  st.nextAbs ≤ st'.nextAbs ∧ st.nextLoan ≤ st'.nextLoan ∧
  st.absTy.size ≤ st'.absTy.size ∧ (∀ σ, σ < st.absTy.size → st'.absTy[σ]? = st.absTy[σ]?) ∧
  st.absDecl.size ≤ st'.absDecl.size ∧ (∀ σ, σ < st.absDecl.size → st'.absDecl[σ]? = st.absDecl[σ]?)

/-- The premises of the function rules, instantiated with the machine's own runs of exactly those
sub-computations, from a state `R`-related to the comparison's start (`R` is `NamesKept` for the
checker as it is: under D103 every sub-computation of a comparison starts from a state that differs
from the comparison's start only in names). -/
def machPremisesR (R : MState → MState → Prop) (st : MState) : Premises where
  fn f g := ∃ (st₁ st₂ : MState) (fuel bh : Nat) (pf : Value) (cs : List Value) (hs : List Hint)
      (ds : List Term) (c : Term) (rd : List (DeclInfo × Value)),
    R st st₁ ∧ fnTyOf st.globals f = some pf ∧ pf = .tPi cs (.pi hs ds c) rd ∧
      Steps.Runs (Ochr.convFnRun fuel f g pf cs hs ds c) st₁ bh true st₂
  pi P Q := ∃ (st₁ st₂ : MState) (fuel bh : Nat), R st st₁ ∧
    Steps.Runs (Ochr.convPi fuel P Q) st₁ bh true st₂
  fieldTys d args c fs Ts := ∃ (st₁ st₂ : MState) (fuel bh : Nat) (Ts' : List (String × Value)),
    R st st₁ ∧ Steps.Runs (Ochr.fieldTypesOf fuel d args c fs) st₁ bh Ts' st₂ ∧
      Ts = Ts'.map (·.2)

/-- The premises of a comparison started at `st`. -/
abbrev machPremises (st : MState) : Premises := machPremisesR NamesKept st

end Ochr.Meaning.Conv
