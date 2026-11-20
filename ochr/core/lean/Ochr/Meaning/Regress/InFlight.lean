import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.Attack.RunEqs

/-!
# A value in flight must be counted (docs/31 D71; kernel-checked)

The simulation-form step statements compared the checker's state after a step with the reference's,
without the value the step returns. The reference parks a borrow it returns in a temporary (D14:
`borrowPlace` ends with `pushTempShaped`), and the relation matches temporaries by the borrows they
hold, in both directions (`SimEq`'s last clause): every borrow a temporary of the reference holds is
held by some temporary of the checker's state, in the same frame (`rel_temp_matched`). The checker's
`borrowPlace` returns `borrow_ℓ v` and pushes nothing (`Machine.borrowPlace`: `setPlace p (.loan l);
pure (.borrow l v)`). So after `&x` the relation as stated could not hold: the reference's
parked borrow matched no temporary of the checker. The statements now relate the checker's state
with the value counted as a temporary (`MState.withTemp`, as the borrow statements already read a
result), and type its label (`GoodF`, `flightOf`).
-/

namespace Ochr.Meaning.Regress.InFlight
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **The relation needs a checker temporary for every borrow a reference temporary holds.** -/
theorem rel_temp_matched (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState)
    (hs : Rel K ρ φ π st s) {f j l' : Nat} (hl : s.shape (.temp f j) = some l') :
    ∃ i l, Env.shape st.env (.temp f i) = some l ∧ π l = l' :=
  hs.sim.2.2.2.2 f j l' hl

/-- **After `&y` the reference's state is not related to a checker state without the borrow in
flight**: the reference's state after `let y = c; &y` (`Attack.S₂`, `borrowPlace`'s output, its borrow
`k` parked at temporary `0` of frame `0`) is related to no checker state whose frame `0` has no
temporary holding a borrow, which is the checker's state after its `borrowPlace` (it pushes nothing). -/
theorem not_rel_without_flight (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState)
    (b : SBinding) (k : Nat) (c : Sem) (hno : ∀ i, Env.shape st.env (.temp 0 i) = none) :
    ¬ Rel K ρ φ π st (Attack.S₂ b k c) := by
  intro hs
  obtain ⟨i, l, hl, -⟩ := rel_temp_matched K ρ φ π st _ hs (f := 0) (j := 0) (l' := k) (by simp [Attack.S₂])
  rw [hno i] at hl
  cases hl

end Ochr.Meaning.Regress.InFlight
