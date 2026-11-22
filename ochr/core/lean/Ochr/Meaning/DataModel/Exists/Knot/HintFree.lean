import Ochr.Meaning.Run

/-!
# A term whose run does not read its hint (exists7)

Out of tail position (`tl = false`) the reference run hands a sequencing form's tail and a match's
arms no hint (`tailHint false _ = err`), and every other clause runs its subterms at hints of its own
(a call's arguments at the parameter types, a constructor's fields at the field types, an ascription
at its annotation). Only three clauses read the hint they are given: a constructor whose parameters
are not written (of a declaration that has some), which takes its record from the hint; an embedded
value; and `clone`, `peek`, `inplace`, which hand it to their argument. A term headed by none of these
(`hintFreeB`) runs the same at every hint (`runT_hintFree`).

This is what weakens the grammar's condition (B2) (docs/34 §18.10): a value argument at
a parameter whose declared type mentions a varying argument (`NF(DF, 0, ())`, with
`NF (A : Type) (n : Nat) (f : NegF(A, n))`) is run at a hint that varies with the knot's records, and
its value is the same at both when it does not read its hint.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning

/-- **A term whose run out of tail position does not read its hint**: its head is not a constructor
with its parameters left to the hint (written parameters, or a declaration without parameters, or no
declaration of that name), not an embedded value, and not `clone`, `peek` or `inplace`. -/
def hintFreeB (Γ : List IndDecl) : Term → Bool
  | .ctor ty _ _ ps _ => !ps.isEmpty || (match Γ.find? (·.name == ty) with
    | some M => M.params.isEmpty
    | none => true)
  | .val _ => false
  | .prim n _ => !(n == "clone" || n == "peek" || n == "inplace")
  | _ => true

theorem runT_hintFree (K : RunCtx) (ρ : Assignment) (φ : Future) (H H' : TyS) :
    ∀ (t : Term), hintFreeB K.Γ t = true → runT K ρ φ false H t = runT K ρ φ false H' t := by
  intro t ht
  cases t with
  | ctor ty c x ps args =>
    funext s
    rw [runT, runT]
    dsimp only
    cases hM : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some M =>
      simp only [hintFreeB, hM, Bool.or_eq_true, Bool.not_eq_true'] at ht
      have : (!ps.isEmpty || M.params.isEmpty) = true := by
        rcases ht with h | h <;> simp [h]
      simp only [this, if_true]
  | val v => simp [hintFreeB] at ht
  | prim n args =>
    simp only [hintFreeB, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    rw [runT.eq_def, runT.eq_def]
    split <;> simp_all
  | _ => rw [runT, runT] <;> simp only [tailHint_false]

end Ochr.Meaning.DataModel.Exists.Knot
