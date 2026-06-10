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
  intro k γ hγ
  rw [Mem_unfold]
  intro j v hj hconv
  obtain ⟨j₁, w, hj₁le, hconvT, hcase⟩ := converges_app_factor hconv
  -- (1) The head's value is a λ whose bound is β-convertible to `S`, by the
  -- `t ≤ λx≤s.Top` premise at index `j₁ + 1 ≤ k` — were it `Top`, the member
  -- side of (m3) would fail: the progress-critical step.
  have hlam : ∃ A B, w = .lam A B ∧ Beta A (s.subst γ) := by
    have hmem : Mem (j₁ + 1) (t.subst γ) ((Term.lam s .top).subst γ) :=
      (h₁ (j₁ + 1) γ (semCtx_antitone (by omega) hγ)).1
    rw [Mem_unfold] at hmem
    obtain ⟨-, w', hw'conv, -, hmatch⟩ := hmem j₁ w (by omega) hconvT
    obtain ⟨i', hw'c⟩ := hw'conv
    have hself : Converges 0 ((Term.lam s .top).subst γ) ((Term.lam s .top).subst γ) :=
      ⟨.refl, whNormal_of_value (.lam _ _)⟩
    obtain ⟨-, rfl⟩ := Converges.deterministic hw'c hself
    rw [Match_unfold] at hmatch
    rcases hmatch with htop | ⟨a, b, α, β, hweq, hveq, hβ, -⟩
    · exact Term.noConfusion htop
    · injection hweq with ha hb
      exact ⟨α, β, hveq, ha ▸ hβ⟩
  rcases hcase with ⟨A, B, rfl, j₂, hjeq, hconvB⟩ | ⟨hnotlam, -, -⟩
  · -- λ branch: `j = j₁ + 1 + j₂`, `Converges j₂ ([U]B) v`.
    obtain ⟨A', B', heq, hAS⟩ := hlam
    injection heq with hA hB
    subst hA; subst hB
    -- (2) Self-MATCH of the head's value at the ambient index `k`, from `hwt`.
    have hmemTT : Mem k (t.subst γ) (t.subst γ) := hwt k γ hγ
    rw [Mem_unfold] at hmemTT
    obtain ⟨-, w'', hw''conv, -, hmatchTT⟩ := hmemTT j₁ (.lam A B) (by omega) hconvT
    obtain ⟨i'', hw''c⟩ := hw''conv
    obtain ⟨-, rfl⟩ := Converges.deterministic hw''c hconvT
    rw [Match_unfold] at hmatchTT
    rcases hmatchTT with htop | ⟨a, b, α, β, hweq, hveq, -, htier⟩
    · exact Term.noConfusion htop
    · injection hweq with ha hb
      subst ha; subst hb
      injection hveq with hα hβ
      subst hα; subst hβ
      -- (3) `U` is a good argument of `A` at depth `k - j₁ - 1`: memberships
      -- and inclusions from the `u ≤ s` premise (indices ≤ k), transported
      -- across `Beta A S` by Lemma 4.4.
      have hgood : Good (k - j₁ - 1) A (u.subst γ) := by
        rw [Good_unfold]
        refine ⟨?_, ?_, ?_⟩
        · exact (mem_beta_type hAS).mpr
            (h₂ (k - j₁ - 1) γ (semCtx_antitone (by omega) hγ)).1
        · exact hwu (k - j₁ - 1) γ (semCtx_antitone (by omega) hγ)
        · intro i s' hi hmem
          exact (mem_beta_type hAS).mpr
            ((h₂ i γ (semCtx_antitone (by omega) hγ)).2 s' hmem)
      -- (4) The tier at depth `j' = k - j₁ - 1` self-describes the contractum.
      have hmemB := (htier (k - j₁ - 1) (u.subst γ) (by omega) hgood).1
      -- (5) Run the contractum's membership on `[U]B ⇓^{j₂} v`; its (m3) value
      -- is `v` itself by determinism, and `(k-j₁-1) - j₂ = k - j` exactly.
      rw [Mem_unfold] at hmemB
      obtain ⟨hvval, w₃, hw₃conv, -, hmatchv⟩ := hmemB j₂ v (by omega) hconvB
      obtain ⟨i₃, hw₃c⟩ := hw₃conv
      obtain ⟨-, rfl⟩ := Converges.deterministic hconvB hw₃c
      refine ⟨hvval, v, ⟨j, hconv⟩, hvval, ?_⟩
      have harith : k - j₁ - 1 - j₂ = k - j := by omega
      rwa [harith] at hmatchv
  · -- Stuck branch refuted: the head's value is a λ by (1).
    obtain ⟨A, B, heq, -⟩ := hlam
    exact absurd heq (hnotlam A B)

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
