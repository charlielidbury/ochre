import Ochr.Meaning.Steps.Borrow

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
theorem borrow_wf (st st' : MState) (fuel : Nat) (p : Place) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (h : Runs (Ochr.borrowPlace fuel p) st fuel v st') :
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env := by
  sorry

/-- [End] keeps (WF1)–(WF3): the ended label leaves Ω; a reborrow's loan in its content moves
to the lender, above it in the borrow relation. (WF2) needs (WF3) here (docs/18 §"Well-formedness"). -/
theorem end_wf (st st' : MState) (fuel l : Nat)
    (hwf : WF K.dm K.C K.Γ ρ st) (h : Runs (Ochr.endBorrow fuel l) st fuel () st') :
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env := by
  sorry

/-- [Assign] keeps (WF1)–(WF3): D67 ends the loans in the overwritten owned part, and the old
content's borrows end ([Drop]). -/
theorem assign_wf (st st' : MState) (fuel : Nat) (p : Place) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (h : Runs (Ochr.assignPlace fuel p v) st fuel () st') :
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env := by
  sorry

/-- [Close] keeps (WF1)–(WF4): the fills are closed sealed programs (C1), the arguments were
loan-free (C8), and a returned borrow's fresh label is held once. -/
theorem close_wf (st st' : MState) (fuel : Nat) (fv : Value) (ws : Array Value) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) (v : Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hargs : ArgsLoanFree st.env ws)
    (h : Runs (Ochr.closeCall fuel fv ws kind res fills tys) st fuel v st') :
    WF1 st'.env ∧ WF2 st'.env ∧ WF3 st'.env ∧ WF4 st'.env := by
  sorry

/-- Closure formation keeps (WF4): the captures are read after [Access] (loan-free) and may not
hold `⊥` (the capture check), and a Π-closure captures no borrow (D48). -/
theorem capture_wf (st st' : MState) (fuel : Nat) (t : Term) (cs : List Value) (t' : Term)
    (rd : List (DeclInfo × Value))
    (hwf : WF K.dm K.C K.Γ ρ st) (h : Runs (Ochr.capture fuel t) st fuel (cs, t', rd) st') :
    ¬ (Value.clo cs t' rd).anyAtom Value.badCapture ∧ WF4 st'.env := by
  sorry

/-- Every step of `evalCore` keeps (WF6): names are allocated at and below the counters, which
only grow. -/
theorem eval_wf6 (st st' : MState) (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st') :
    WF6 st' ∧ st.nextAbs ≤ st'.nextAbs ∧ st.nextLoan ≤ st'.nextLoan := by
  sorry

/-- Every step of `evalCore` keeps (WF7) and (WF8): the only places a borrow type is formed
check D66 and D48, and no step puts `&` below the top of a type. -/
theorem eval_wf78 (st st' : MState) (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value)
    (v : Value) (T? : Option Value)
    (hwf : WF K.dm K.C K.Γ ρ st) (hprog : t.refsOk = true)
    (h : Runs (Ochr.evalCore fuel typed t hint) st fuel (v, T?) st') :
    WF7 K.dm K.C K.Γ ρ st' ∧ WF8 st' := by
  sorry

/-- Types are hole-free at every reachable state (docs/27 Lemma 5): no stored type, type of an
unknown, record or goal holds a live loan. Stated as the invariant the step lemmas carry; it is
what lets types be read under `noFuture`. -/
theorem types_holeFree (st : MState) (hg : Good K.dm K.C K.Γ ρ st) :
    (∀ (f i : Nat) (b : Binding), st.env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b →
      ∀ T : Value, b.ty = some T → ∀ l ∈ T.loans, liveLoan st.env l = false) ∧
    (∀ T ∈ st.absTy.toList, ∀ l ∈ T.loans, liveLoan st.env l = false) ∧
    (∀ G, st.goal = some G → ∀ l ∈ G.loans, liveLoan st.env l = false) := by
  sorry

end

end Ochr.Meaning.Steps
