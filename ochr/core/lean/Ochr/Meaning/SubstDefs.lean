import Ochr.Meaning.Run
import Ochr.Meaning.Subst

/-!
# The substitution lemmas' hypotheses (moved from `Lemmas.lean`, unchanged)

`HintFree`, `DecInvariant`, `FillShape` and `StateFreeOf` are the hypotheses of
`Lemmas.meanV_substLoan` and `Lemmas.run_substLoan`. They live here so the proofs
(`RunSubst.lean`, which `Lemmas.lean` imports) can state them.
-/

namespace Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- `w`'s meaning does not depend on the type it is read at (a value that records its
parameters, or holds none). -/
def HintFree (φ : Future) (w : Value) : Prop := ∀ h h', meanV K ρ φ h w = meanV K ρ φ h' w

/-- **Hint-freeness from recorded parameters.** The hint reaches a value's meaning only through a
borrow's content, a constructor with no parameters recorded (`hint.data`) and a sealed program
(its run at the hint); fields and parameters are read at the declaration's own hints. So a value
with its parameters recorded (D88/D89, (WF10)) and no sealed program means the same at every
hint. (A sealed content stays hint-dependent by design, D89: the residual for [End] on a borrow
of a sealed program, docs/31.) -/
theorem hintFree_of_recorded (φ : Future) :
    ∀ (w : Value), w.anyAtom (Value.bareCtor K.Γ) = false → w.anyAtom Value.isSealed = false →
      HintFree K ρ φ w
  | .borrow l w, hb, hs => by
    intro h h'
    simp only [Value.anyAtom, Value.bareCtor, Value.isSealed, Bool.false_or] at hb hs
    exact hintFree_of_recorded φ w hb hs h h'
  | .ind ty c hd ps fs, hb, _ => by
    intro h h'
    simp only [meanV]
    cases ps with
    | nil =>
      simp only [Value.anyAtom, Value.bareCtor] at hb
      split
      · next d hd' =>
        rw [hd'] at hb
        have hpe : d.params.isEmpty = true := by
          cases h : d.params.isEmpty <;> simp [h] at hb ⊢
        simp [hpe]
      · rfl
    | cons p ps => simp
  | .sealed _, _, hs => by simp [Value.anyAtom, Value.isSealed] at hs
  | .zero, _, _ | .unit, _, _ | .gfn _, _, _ | .clo _ _ _, _, _ | .loan _, _, _ | .bot, _, _
  | .abs _, _, _ | .proof, _, _ | .tNat, _, _ | .tUnit, _, _ | .tEq _ _ _, _, _ | .tRef _, _, _
  | .tPi _ _ _, _, _ | .sort _, _, _ | .tInd _ _, _, _ | .succ _, _, _ => fun _ _ => rfl

/-- The decisions do not see the substitution (m2-proofs' C): every `Decisions` field answers the
same on `t[loan l := w]` as on `t`, in every scope and for every place. The real `Decide` has this
for data fills (a loan and a constructor value both read `.other`), not for proofs, sorts, type
values, closures, globals or borrows. -/
def DecInvariant (D : Decisions) (l : Nat) (w : Value) : Prop :=
  (∀ sc t, D.flags sc (Term.substLoan l w t) = D.flags sc t) ∧
  (∀ sc t, D.declOf sc (Term.substLoan l w t) = D.declOf sc t) ∧
  (∀ sc t, D.piSort sc (Term.substLoan l w t) = D.piSort sc t) ∧
  (∀ sc e t, D.joinMoves sc e (Term.substLoan l w t) = D.joinMoves sc e t) ∧
  -- m2-proofs' 5a: `Id` reads the re-pointed bindings off its first side's text
  (∀ sc t, D.rePointed sc (Term.substLoan l w t) = D.rePointed sc t) ∧
  -- D19, R3: a closure's frame binds its parameters at their domain terms' readings
  (∀ sc t, D.typeDecl sc (Term.substLoan l w t) = D.typeDecl sc t)

/-- The filler's type, as the run reads an embedded value, is the loan's (P1, replacing m2-proofs'
`NotCode`: a borrowed function value is real). At every hint, `.val w` and `.val (loan ℓ)` give
the same `TyS`: for a data filler and a loan with no declared shape both are the hint; for a
closure or Π-closure filler the loan's declared shape (`K.Λ ℓ`) is the filler's, which typing
gives. (A global or abstract filler carries its own `TyS` rather than the hint's, so it satisfies
this only when the loan's declared type is that `TyS`: a residual, should one be met.) -/
def FillShape (φ : Future) (l : Nat) (w : Value) : Prop :=
  ∀ hint s, (run K ρ φ hint (.val w) s).map (·.1.2) = (run K ρ φ hint (.val (.loan l)) s).map (·.1.2)

/-- The state does not read label `l`, and `l` is below its label counter (m2-proofs' B: fresh
labels never collide with `l`). -/
def StateFreeOf (s : SState) (l : Nat) : Prop :=
  (∀ p ψ x, s.valAt p (ψ.upd l x) = s.valAt p ψ) ∧ l < s.nextLoan

end

end Ochr.Meaning
