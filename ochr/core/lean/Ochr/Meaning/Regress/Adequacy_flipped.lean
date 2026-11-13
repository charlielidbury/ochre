import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Regress.CE4_flipped

/-!
# D19's batch, flipped: positive checks for the fixed reference run (built)

`Regress/Adequacy_1d94e4eb.lean` (unbuilt) records the run of 1d94e4eb failing on `f(f(a))` and on
`(let y = x; ()); x`. With D19's fixes:

* `head_in_place`: a call's head, when it is a place, is read in place: the value comes back and
  the state is as it was, whatever the place's declared reading (R2). So the inner call of
  `f(f(a))` finds `f` where the outer one read it.
* `stmt_keeps`: a term the decisions classify as a statement (`Decisions.flags`) leaves the state
  as it was and returns no label, whatever it reads or writes (R1), for the sequencing forms, a
  place, an assignment and a call. So `x` is still there after `let h : True = (let y = x; refl)`.

Axioms: propext, Classical.choice, Quot.sound.
-/

namespace Ochr.Meaning.Regress.AdequacyFlip
open Ochr Ochr.Meaning Ochr.Meaning.Attack Ochr.Meaning.Regress.CE4flip

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- One frame holding one binding, no holder. -/
def one (b : SBinding) (k : Nat) : SState := { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }

/-- R2: the head of a call, a place, is read in place. -/
theorem head_in_place (b : SBinding) (k : Nat) (rn : SM Res) (hw : (b.val φ).whole) :
    SM.headOf (.place (.var 0)) (fun p => readPlace K φ p true) rn (one b k)
      = some ((b.val φ, { b.ty with label := none }), one b k) := by
  show readPlace K φ (.var 0) true (one b k) = _
  rw [readPlace_of φ K (.var 0) true (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
  simp [hw, one]

/-- R1: a statement leaves the state as it was. -/
theorem stmt_keeps (t : Term) (hint : TyS) (s : SState) (hfl : (K.D.flags (scopeOf s) t).1 = true)
    (r : Res) (s' : SState) (h : run K ρ φ hint t s = some (r, s'))
    (ht : t matches .letIn .. | .seq .. | .matchNat .. | .matchInd .. | .assign .. | .place .. | .call ..) :
    s' = s ∧ r.2.label = none := by
  cases t <;> simp at ht <;>
    (rw [run] at h
     obtain ⟨hb, -⟩ | ⟨-, e, hl, -⟩ := SM.stmtIf_some h
     · rw [hfl] at hb; cases hb
     · exact ⟨e, hl⟩)

end Ochr.Meaning.Regress.AdequacyFlip
