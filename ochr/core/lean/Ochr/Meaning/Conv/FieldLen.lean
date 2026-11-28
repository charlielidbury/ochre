import Ochr.Meaning.Conv.CtorEq
import Ochr.Meaning.Conv.Refine

/-!
# `FieldTysOk.len`, proved (conv2, 2026-11-28)

`fieldTele` fails unless the parameters it is given have the declaration's length, so every
successful `fieldTypesOf` run, hence every field-type premise of the machine's instance
(`machPremisesR`), is at parameters of the declaration's length. A fact about the checker alone.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem fieldTele_len {fuel : Nat} {d : IndDecl} {ps : List Value} {c : Nat} {val : Nat → Value → M Value}
    {upto : Option Nat} {st st' : MState} {bh : Nat} {r : List (String × Value × Value)}
    (h : Runs (Ochr.fieldTele fuel d ps c val upto) st bh r st') : ps.length = d.params.length := by
  refine Classical.byContradiction fun hne => ?_
  cases fuel with
  | zero => unfold Ochr.fieldTele at h; exact runs_exhausted_false h
  | succ fuel' =>
    unfold Ochr.fieldTele at h
    split at h
    · have hc : (ps.length != d.params.length) = true := by simpa using hne
      simp only [hc, ↓reduceIte] at h
      obtain ⟨a, st₁, b₁, h1, -⟩ := Runs.bind_inv h
      exact runs_err_false h1
    · exact runs_err_false h

theorem fieldTypesOf_len {fuel : Nat} {d : IndDecl} {ps : List Value} {c : Nat} {fs : List Value}
    {st st' : MState} {bh : Nat} {Ts : List (String × Value)}
    (h : Runs (Ochr.fieldTypesOf fuel d ps c fs) st bh Ts st') : ps.length = d.params.length := by
  cases fuel with
  | zero => unfold Ochr.fieldTypesOf at h; exact (runs_exhausted_false h).elim
  | succ fuel' =>
    unfold Ochr.fieldTypesOf at h
    obtain ⟨a, st₁, b₁, h1, -⟩ := Runs.bind_inv h
    exact fieldTele_len h1

/-- **`FieldTysOk.len` holds of the machine's instance** (checker; PROVED). -/
theorem machPremises_len (R : MState → MState → Prop) (st : MState) :
    ∀ d args c fs Ts, (machPremisesR R st).fieldTys d args c fs Ts → args.length = d.params.length := by
  rintro d args c fs Ts ⟨st₁, st₂, fuel, bh, Ts', -, hrun, -⟩
  exact fieldTypesOf_len hrun

end Ochr.Meaning.Conv
