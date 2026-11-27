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

/-- **A term whose run out of tail position does not read its hint**: its head, after any `clone`,
`peek` or `inplace` (which hand the hint to their argument), is not a constructor with its parameters
left to the hint (written parameters, or a declaration without parameters, or no declaration of that
name, are fine) and not an embedded value; a `split` (which runs its term at the hint, docs/31 D175) is counted
hint-reading (no field type holds one). -/
def hintFreeB (Γ : List IndDecl) : Term → Bool
  | .ctor ty _ _ ps _ => !ps.isEmpty || (match Γ.find? (·.name == ty) with
    | some M => M.params.isEmpty
    | none => true)
  | .val _ => false
  | .prim n [u] => if n == "clone" || n == "peek" || n == "inplace" then hintFreeB Γ u else true
  | .prim n _ => !(n == "clone" || n == "peek" || n == "inplace" || n == "split")
  | _ => true

theorem runT_hintFree (K : RunCtx) (ρ : Assignment) (φ : Future) (H H' : TyS) :
    ∀ (t : Term), hintFreeB K.Γ t = true → runT K ρ φ false H t = runT K ρ φ false H' t
  | .ctor ty c x ps args, ht => by
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
  | .val v, ht => by simp [hintFreeB] at ht
  | .prim n [u], ht => by
    by_cases hn : (n == "clone" || n == "peek" || n == "inplace") = true
    · have hu : hintFreeB K.Γ u = true := by simpa [hintFreeB, hn] using ht
      have ih := runT_hintFree K ρ φ H H' u hu
      simp only [Bool.or_eq_true, beq_iff_eq] at hn
      rcases hn with (rfl | rfl) | rfl <;> (funext s; rw [runT, runT, ih])
    · simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      rw [runT.eq_def, runT.eq_def]
      split <;> simp_all
  | .prim n [], ht | .prim n (_ :: _ :: _), ht => by
    simp only [hintFreeB, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at ht
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
    rw [runT.eq_def, runT.eq_def]
    split <;> simp_all
  | .place _, _ | .borrow _, _ | .assign _ _, _ | .letIn _ _ _, _ | .seq _ _, _ | .matchNat _ _ _, _
  | .matchInd _ _ _, _ | .tind _ _, _ | .const _, _ | .sort _, _ | .pi _ _ _, _ | .fix _ _ _ _ _ _, _
  | .nat, _ | .unit, _ | .zero, _ | .tt, _ | .succ _, _ | .eq _ _ _, _ | .cong _ _, _
  | .ref _, _ | .id _ _ _, _ | .ascribe _ _, _ => by
    rw [runT, runT] <;> simp only [tailHint_false]
  -- the call clause reads no hint, at a sealed closure head (docs/31 D233) as elsewhere
  | .call f args hd, _ => by
    rcases call_cases f hd with ⟨caps, self, hs, ds, c, dec, body, rd, rfl, rfl⟩ | hold
    · rw [runT, runT]
    · rw [runT_call_old K ρ φ false H f args hd hold, runT_call_old K ρ φ false H' f args hd hold]

end Ochr.Meaning.DataModel.Exists.Knot
