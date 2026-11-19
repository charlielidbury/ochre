import Ochr.Meaning.SState

/-!
# What the relation does not pin: a reference state at other values of an early-ended label (built)

docs/31 D25 (third lead, 2026-11-19; OPEN). `Rel` compares the checker's state with the reference
state AFTER the borrows the checker ended early (`E`) are ended in it. Ending a label fixes its
final content to what its holder holds (`Mean.semEnd`), so the comparison reads the reference's
meanings only at futures that give each label of `E` its holder's content. What the reference
state means at OTHER values of those labels is not constrained.

But the reference run reads them: [Access] ends a label when SOME future, changed at that label
alone, changes what is observed (`SState.obsDep`), and it ranges over every future.

The core of it, on meanings alone: `f₁` and `f₂` agree once the label `l` is fixed to any content
but `err` (`agree_after_end`), `f₂` reads no label, and `f₁` depends on the label `k`
(`f₁_dep`, `f₂_indep`). So two reference states that hold `f₁` and `f₂` at a position, with `l`
held by a borrow whose content is not `err`, are related to the same checker state with
`E = [l]`, and a read of that position ends `k` from the one and not from the other, where the
checker, whose state holds the constant, ends nothing. From the first the reference is then
AHEAD of the checker, which `Rel` cannot express, so a step statement quantified over every
related reference state is false there.

`f₁` is not the meaning of any value the run builds (a value that reads one label only when
another has a given content needs a sealed program with two holes, which (WF5) excludes), so this
is a fault of the STATEMENT's quantifier, not of a reachable state. The fix is open (docs/31
D25): `Rel` must say enough of the reference state itself, at every future, for [Access] from it
to be determined.
-/

namespace Ochr.Meaning.Regress.EarlyUnpinned
open Ochr Ochr.Meaning

/-- Reads `k` only where `l` reads `err`; the constant `c` elsewhere. -/
noncomputable def f₁ (l k : Nat) (c : Sem) : SVal := fun ψ =>
  open Classical in if ψ l = .err then ψ k else c

/-- The constant. -/
def f₂ (c : Sem) : SVal := fun _ => c

/-- Once `l` is fixed to a content other than `err`, as ending its borrow fixes it, the two agree
at every future. -/
theorem agree_after_end (l k : Nat) (c a : Sem) (ha : a ≠ .err) (ψ : Future) :
    f₁ l k c (ψ.upd l a) = f₂ c (ψ.upd l a) := by
  unfold f₁ f₂
  rw [Future.upd_same, if_neg ha]

/-- `f₁` depends on `k`. -/
theorem f₁_dep (l k : Nat) (c : Sem) (hlk : k ≠ l) :
    ∃ (ψ : Future) (x : Sem), f₁ l k c ψ ≠ f₁ l k c (ψ.upd k x) := by
  refine ⟨fun _ => .err, .proof, ?_⟩
  unfold f₁
  rw [Future.upd_other _ _ (Ne.symm hlk), Future.upd_same]
  simp

/-- `f₂` depends on nothing. -/
theorem f₂_indep (c : Sem) (k : Nat) (ψ : Future) (x : Sem) : f₂ c (ψ.upd k x) = f₂ c ψ := rfl

end Ochr.Meaning.Regress.EarlyUnpinned
