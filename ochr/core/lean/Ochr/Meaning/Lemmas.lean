import Ochr.Meaning.Run
import Ochr.Meaning.Subst

/-!
# The two lemmas that close milestone 2 (statements; docs/27 Lemma 3, docs/31 §Milestone 2)

* The **sealed-substitution lemma**: filling a loan is fixing the future. For `w` not mentioning
  `ℓ`, `⟦v[loan ℓ := w]⟧_{ρ,φ} = ⟦v⟧_{ρ, φ[ℓ ↦ ⟦w⟧_{ρ,φ}]}`, and the same for a term's run: the
  run at `φ` of the substituted term is the run at `φ[ℓ ↦ ⟦w⟧]` of the term (D10: the run is
  per-future, and a free label is read from the future). It is what makes the checker's [End]
  (a substitution plus re-normalisation) equal to `Mean.semEnd`, and a fill's re-run equal to
  the fill read at the fixed future (docs/27 §7, N3). Re-normalisation keeping the meaning is
  the run's own `.sealed` clause.
* **Dependence**: a meaning reads the future only at the loans of the value, where "loans"
  includes those inside a closure's recorded capture types (`Value.hasLoan`, which looks inside
  `rd`, where `Value.loans` does not: m2-proofs' counterexample).

Both are proved by induction on the value or term, through the mutual block of `Run.lean`. The
counterexamples that refuted the earlier statements are in the scratchpad file `CE.lean` of the
session that found them (m2-proofs, 2026-11-09); they should become regression checks once the
run is decidable on them.
-/

namespace Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment)

/-- `w`'s meaning does not depend on the type it is read at (a value that records its
parameters, or holds none). -/
def HintFree (φ : Future) (w : Value) : Prop := ∀ h h', meanV K ρ φ h w = meanV K ρ φ h' w

/-- The decisions do not see the substitution (m2-proofs' C): every `Decisions` field answers the
same on `t[loan l := w]` as on `t`, in every scope and for every place. The real `Decide` has this
for data fills (a loan and a constructor value both read `.other`), not for proofs, sorts, type
values, closures, globals or borrows. -/
def DecInvariant (D : Decisions) (l : Nat) (w : Value) : Prop :=
  (∀ sc t, D.flags sc (Term.substLoan l w t) = D.flags sc t) ∧
  (∀ sc t, D.declOf sc (Term.substLoan l w t) = D.declOf sc t) ∧
  (∀ sc t, D.piSort sc (Term.substLoan l w t) = D.piSort sc t) ∧
  (∀ sc e t, D.joinMoves sc e (Term.substLoan l w t) = D.joinMoves sc e t)

/-- `w` is not code: not a closure, a Π-closure or a global (m2-proofs' E: an embedded one
carries a shape that an embedded loan does not). -/
def NotCode : Value → Prop
  | .clo .. | .tPi .. | .gfn _ => False
  | _ => True

/-- The state does not read label `l`, and `l` is below its label counter (m2-proofs' B: fresh
labels never collide with `l`). -/
def StateFreeOf (s : SState) (l : Nat) : Prop :=
  (∀ p ψ x, s.valAt p (ψ.upd l x) = s.valAt p ψ) ∧ l < s.nextLoan

/-- Filling a loan is fixing the future, for values. The hypotheses are m2-proofs' C and E. -/
theorem meanV_substLoan (φ : Future) (hint : TyS) (l : Nat) (w v : Value)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : NotCode w) :
    meanV K ρ φ hint (Value.substLoan l w v) = meanV K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint v := by
  sorry

/-- Filling a loan is fixing the future, for a term's run: the run at `φ` of the substituted term
from a state is the run at the fixed future of the term from the same state (hypotheses B, C, E). -/
theorem run_substLoan (φ : Future) (hint : TyS) (l : Nat) (w : Value) (t : Term) (s : SState)
    (hw : ¬ w.hasLoan l) (hf : HintFree K ρ φ w) (hD : DecInvariant K.D l w) (hc : NotCode w)
    (hs : StateFreeOf s l) :
    run K ρ φ hint (Term.substLoan l w t) s
      = run K ρ (φ.upd l (meanV K ρ φ (.plain .err) w)) hint t s := by
  sorry

/-- A value's meaning depends on the future only at the loans it holds anywhere, its closures'
recorded capture types included. (With D13's fixes every borrow the run makes is ended before
it is read or when it is discarded, so no fresh label leaks into a meaning.) -/
theorem meanV_congr (φ φ' : Future) (hint : TyS) (v : Value)
    (h : ∀ l, v.hasLoan l → φ l = φ' l) : meanV K ρ φ hint v = meanV K ρ φ' hint v := by
  sorry

/-- Future-locality of the run (m2-proofs' form): if the future changes only at labels outside
`L`, where `L` holds of every loan of the term and the state factors through `L` (each position's
meaning depends only on the future restricted to `L`), the run is unchanged. "Factors through"
rather than pointwise `dependsOn`: a value can change when infinitely many labels change together
while depending on no single one. No live-label clause is needed, since `access` fixes the
future only at live labels; it holds because every borrow the run makes is ended before it is
read or when it is discarded (D13). -/
theorem run_congr (φ φ' : Future) (hint : TyS) (t : Term) (s : SState) (L : Nat → Prop)
    (hφ : ∀ l, L l → φ l = φ' l) (ht : ∀ l, t.anyAtom (· == .loan l) → L l)
    (hs : ∀ p ψ ψ', (∀ l, L l → ψ l = ψ' l) → s.valAt p ψ = s.valAt p ψ') :
    run K ρ φ hint t s = run K ρ φ' hint t s := by
  sorry

/-- The run's result does not depend on the starting label counter, as long as it is above every
loan of the term and of the state (m2-proofs' D): fresh labels are names. Needed because a
sealed program's counter, `emptyState (t.loans.foldl max 0 + 1)`, changes under substitution. Only the
result's meaning is compared: a returned borrow's label and the state's labels are the counter. -/
theorem run_counter_indep (φ : Future) (hint : TyS) (t : Term) (s : SState) (n n' : Nat)
    (hn : ∀ l ∈ t.loans, l < n) (hn' : ∀ l ∈ t.loans, l < n') (hs : ∀ l ∈ s.positions.filterMap s.shape, l < min n n') :
    (run K ρ φ hint t { s with nextLoan := n }).map (·.1.1)
      = (run K ρ φ hint t { s with nextLoan := n' }).map (·.1.1) := by
  sorry

end

end Ochr.Meaning
