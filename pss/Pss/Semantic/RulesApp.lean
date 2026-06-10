import Pss.Semantic.Model
import Pss.Semantic.ModelLemmas
import Pss.Semantic.Conversion

/-!
# Per-rule soundness: the application rules

§6 of `pss/docs/03-revised-proof.md`, W-APP and DS-APP — the cases with
exact step/depth accounting (`j = j₁ + 1 + j₂` paying for tier depth
`k − j₁ − 1`; doc §9 calls the off-by-ones here the likeliest mechanical
bug, and `converges_app_factor` / `converges_app_beta` in
`WeakHead.lean` fix the arithmetic once).

Hypotheses match the `Instrumented` constructors under the fundamental
theorem's motives. `SubI.app` carries its endpoints' W-APP
instrumentations *unpacked* as four `WellSubI` premises; their motive
images are the four `And`-triples below, passed verbatim by
`Fundamental.lean` — every component is available, none may be dropped.

**Note for the implementer of `sound_app_le` — the bound-conversion
chain (c).** The doc's chain `S =β A =β A′ =β S′` connects the bounds of
the two independent W-APP instrumentations through (a) the unprimed
head's converged bound, (b) the `MATCH_∀(w_T, w_{T′})` bound clause, and
(a′) the primed head's converged bound. It has no clean γ-free
standalone statement: every link lives under the local convergence
analysis of `T(U)`'s member (the factorization witnesses `A`, `A′` are
existentially produced inside the case). Build it as an explicit `have`
chain inside the proof, per the §9 watchpoint, rather than as a lemma.
-/

namespace Pss.Semantic

/-- **W-APP** (doc §6): a converging member of `⟦T(U)⟧` factors through
`T ⇓ w_T` (`converges_app_factor`); `w_T` is a λ with bound `=β S` by
the `t ≤ λx≤s.Top` premise's (m3) (*were it `Top`, the member side of
MATCH would fail — the progress-critical step*); `U` is good at every
depth from the `u ≤ s` premise's membership and **inclusion** halves;
the head's self-MATCH tier at `j′ = k − j₁ − 1` self-describes the
contractum, and `⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ` by Lemma 4.3. Matches `WfI.app`
(premise triples projected by `Fundamental.lean`). -/
theorem sound_wapp {Γ : Ctx} {t u s : Term}
    (h₁ : SemLe Γ t (.lam s .top)) (h₂ : SemLe Γ u s)
    (hwt : SemWf Γ t) (hwu : SemWf Γ u) :
    SemWf Γ (.app t u) := by
  sorry

/-- **DS-APP, ≤-form** (doc §6, steps (a)–(g)): both applications
weak-head factor (4.3), the function values MATCH at every index, `U` is
∀-good at `A′` via member conversion (4.5, ∀-index available) and the
bound chain (c), the strengthened tier at `c = U` gives the inclusion at
`k`, and primed conversion (substitutivity + 4.4) closes the chain
`⟦T(U)⟧ₖ = ⟦[x↦U]B⟧ₖ ⊆ ⟦[x↦U]B′⟧ₖ = ⟦[x↦U′]B′⟧ₖ = ⟦T′(U′)⟧ₖ`.
Membership half via Lemma 3.3 from the unprimed instrumentation's wf
(`sound_wapp` on `hi₁`/`hi₂`). Matches `SubI.app` at `r = .le`; the four
triples are the motive images of its four `WellSubI` premises. -/
theorem sound_app_le {Γ : Ctx} {t t' u u' s s' : Term}
    (h₁ : SemLe Γ t t') (h₂ : SemEq Γ u u')
    (hi₁ : SemWf Γ t ∧ SemWf Γ (.lam s .top) ∧ SemLe Γ t (.lam s .top))
    (hi₂ : SemWf Γ u ∧ SemWf Γ s ∧ SemLe Γ u s)
    (hi₃ : SemWf Γ t' ∧ SemWf Γ (.lam s' .top) ∧ SemLe Γ t' (.lam s' .top))
    (hi₄ : SemWf Γ u' ∧ SemWf Γ s' ∧ SemLe Γ u' s') :
    SemLe Γ (.app t u) (.app t' u') := by
  sorry

/-- **DS-APP, ≡-form** (doc §6): conversion by congruence, wf of both
applications from their W-APP instrumentations. Matches `SubI.app` at
`r = .eq`. -/
theorem sound_app_eq {Γ : Ctx} {t t' u u' s s' : Term}
    (h₁ : SemEq Γ t t') (h₂ : SemEq Γ u u')
    (hi₁ : SemWf Γ t ∧ SemWf Γ (.lam s .top) ∧ SemLe Γ t (.lam s .top))
    (hi₂ : SemWf Γ u ∧ SemWf Γ s ∧ SemLe Γ u s)
    (hi₃ : SemWf Γ t' ∧ SemWf Γ (.lam s' .top) ∧ SemLe Γ t' (.lam s' .top))
    (hi₄ : SemWf Γ u' ∧ SemWf Γ s' ∧ SemLe Γ u' s') :
    SemEq Γ (.app t u) (.app t' u') :=
  ⟨Beta.app h₁.1 h₂.1,
   sound_wapp hi₁.2.2 hi₂.2.2 hi₁.1 hi₂.1,
   sound_wapp hi₃.2.2 hi₄.2.2 hi₃.1 hi₄.1⟩

end Pss.Semantic
