import Pss.Semantic.WeakHead
import Pss.Semantic.Standardization
import Pss.Semantic.Model
import Pss.Semantic.Fundamental

/-!
# Safety and the recovered lemmas

§7 of `pss/docs/03-revised-proof.md`: Theorem 7.1 (type safety) and
Corollaries 7.2–7.4 — progress, semantic inversion (the content of the
paper's Lemma 5.2), and "Top is not a function". This is where
closedness enters (Fact 1.1 needs the program closed — `wfI_closedUnder`)
and where the empty context instantiates the fundamental theorem:
`semCtx_nil` puts `γ = Term.var` in `⟦∅⟧ₖ`, and `Term.subst_var` cleans
`t.subst Term.var` back to `t`.

Proof route for `safety` (doc §7.1): a reachable normal non-value is a
spine (`fact_1_1_step_normal`); shape standardization
(`steps_spine_standard`) makes `t` itself weak-head converge to a spine
— a non-value weak-head normal form (`Spine.not_value`); but
`fundamental_wf` gives `Mem k t t` at every `k`, whose (m1) at any `k`
above the evaluation length says `t`'s weak-head normal form is a value.
Contradiction.

Implementer note for `wfI_closedUnder`: mutual inductive predicates have
no `.brecOn`, so use the mutual recursor `WfI.rec` directly with
closedness motives (cf. `Fundamental.lean` for the 17-case pattern);
`Ctx.Bound`'s shift discipline and `closedUnder_subst1`-style kit from
`WeakHead.lean` cover the binder cases.
-/

namespace Pss.Semantic

open Term (Value ClosedUnder)

/-- Well-formed terms are closed under their context (Figure 1's
`fv(t) ⊆ dom(Γ)` discipline, recovered from the instrumented system;
feeds Fact 1.1, which needs closed programs). -/
theorem wfI_closedUnder {Γ : Ctx} {t : Term} (h : WfI Γ t) :
    ClosedUnder Γ.length t := by
  sorry

/-- **Theorem 7.1 (type safety)** (doc §7): a well-formed closed program
never goes wrong — every reduct is a value or reduces. Preservation of
safety is built in: the statement quantifies over all reducts, so it is
closed under `⟶` by construction. -/
theorem safety {t s : Term} (hwf : WfI [] t) (hsteps : Steps t s) :
    Value s ∨ ∃ s', Step s s' := by
  sorry

/-- **Corollary 7.2 (progress)** (doc §7): `safety` at the empty
reduction sequence. -/
theorem progress {t : Term} (hwf : WfI [] t) :
    Value t ∨ ∃ t', Step t t' := by
  sorry

/-- **Corollary 7.3 (semantic inversion — the paper's Lemma 5.2's
content)** (doc §7): related λs have `=β` bounds, and their bodies are
related — membership and inclusion — at every depth, on every good
argument of the supertype's bound. (Both λs `⇓⁰`; unfold
`fundamental_wellSub`'s conclusion at every index; `γ = Term.var`.) -/
theorem semantic_inversion {a b a' b' : Term}
    (h : WellSubI [] (.lam a b) .le (.lam a' b')) :
    Beta a a' ∧
    ∀ j c, Good j a' c →
      Mem j (b.subst1 c) (b'.subst1 c) ∧
      ∀ s, Mem j s (b.subst1 c) → Mem j s (b'.subst1 c) := by
  sorry

/-- **Corollary 7.4 (Top is not a function)** (doc §7):
`∅ ⊢ Top ≤wf λx≤s.Top` is underivable — it would put `Top` in
`⟦λx≤s.Top⟧₁`, whose (m3) demands a λ on the member side. The paper
needed this for progress; here it is a one-line consequence of the
model. -/
theorem top_not_fn {s : Term} : ¬ WellSubI [] .top .le (.lam s .top) := by
  sorry

/-- **Corollary 7.4, generalized** (doc §7): the model refutes
non-derivability statements wholesale — any `t ≤wf λx≤s.b` with
`t ⇓ Top` is contradictory. -/
theorem top_le_lam_refuted {t s b : Term}
    (h : WellSubI [] t .le (.lam s b)) (htop : ConvergesTo t .top) :
    False := by
  sorry

end Pss.Semantic
