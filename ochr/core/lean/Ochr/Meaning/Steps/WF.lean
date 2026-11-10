import Ochr.Meaning.Steps.IH

/-!
# Step lemmas, well-formedness preservation (milestone 3; docs/18 part (c), the fifth of the
five lemmas)

`Good` is kept by every step; the step lemmas state it per step. This file gathers the
*clause-wise* preservation facts the proofs share, one per clause and step family, so a
prover can discharge the `Good` conjunct of a step lemma from them:
* (WF1) borrows stay whole values of positions: made by [Borrow] at a position, moved only whole
  (a borrow is never inside data: constructor arguments, captures and fills are loan-free or
  `⊥`-free by the checks);
* (WF2) a loan's borrow is in Ω until [End] substitutes it away, and a label is lent once:
  [Borrow] creates a fresh label (`nextLoan`) and [End] removes every occurrence (WF3 orders
  the ends);
* (WF3) acyclicity: a new loan's content holds no live loan after [Access] (so no cycle), and
  [End] carries a reborrow's loan up to the lender, which is above it;
* (WF4) captures are loan-free and `⊥`-free by [Access] and the capture check; sealed programs
  are closed by (C1);
* (WF6) names: every step allocates below the counters and only the counters;
* (WF7) `&` only at `Type₀`: D66's checks at `.ref` and `.borrow`;
* (WF8) `&` only at the top of a type: D48's `refTopOk`/`refsOk` on the program, and no step
  builds a type value with `&` inside.
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- [Borrow] keeps (WF1)–(WF3): the fresh label is held once, at the destination; the lent
place's content holds no live loan (after [Access]), so the borrow relation stays acyclic. -/
theorem borrow_wf (fuel : Nat) (ih : StepsIH K ρ φ fuel) : borrow_wf_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [End] keeps (WF1)–(WF3): the ended label leaves Ω; a reborrow's loan in its content moves
to the lender, above it in the borrow relation. (WF2) needs (WF3) here (docs/18 §"Well-formedness"). -/
theorem end_wf (fuel : Nat) (ih : StepsIH K ρ φ fuel) : end_wf_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Assign] keeps (WF1)–(WF3): D67 ends the loans in the overwritten owned part, and the old
content's borrows end ([Drop]). -/
theorem assign_wf (fuel : Nat) (ih : StepsIH K ρ φ fuel) : assign_wf_stmt K ρ φ (fuel + 1) := by
  sorry

/-- [Close] keeps (WF1)–(WF4): the fills are closed sealed programs (C1), the arguments were
loan-free (C8), and a returned borrow's fresh label is held once. -/
theorem close_wf (fuel : Nat) (ih : StepsIH K ρ φ fuel) : close_wf_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Closure formation keeps (WF4): the captures are read after [Access] (loan-free) and may not
hold `⊥` (the capture check), and a Π-closure captures no borrow (D48). -/
theorem capture_wf (fuel : Nat) (ih : StepsIH K ρ φ fuel) : capture_wf_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Every step of `evalCore` keeps (WF6): names are allocated at and below the counters, which
only grow. -/
theorem eval_wf6 (fuel : Nat) (ih : StepsIH K ρ φ fuel) : eval_wf6_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Every step of `evalCore` keeps (WF7) and (WF8): the only places a borrow type is formed
check D66 and D48, and no step puts `&` below the top of a type. -/
theorem eval_wf78 (fuel : Nat) (ih : StepsIH K ρ φ fuel) : eval_wf78_stmt K ρ φ (fuel + 1) := by
  sorry

/-- Types are hole-free at every reachable state (docs/27 Lemma 5): no stored type, type of an
unknown, record or goal holds a live loan. Stated as the invariant the step lemmas carry; it is
what lets types be read under `noFuture`. -/
theorem types_holeFree (fuel : Nat) (ih : StepsIH K ρ φ fuel) : types_holeFree_stmt K ρ φ (fuel + 1) := by
  sorry

end

end Ochr.Meaning.Steps
