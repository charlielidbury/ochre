import Pss.Semantic.Instrumented
import Pss.Semantic.ParRed

/-!
# The ≡-fragment is conversion

§6 of `pss/docs/03-revised-proof.md`, Lemma 6.1: every instrumented
`≡`-derivation collapses to raw β-conversion. Every ≡-rule — DS-EAPP,
the ≡-instances of DS-FUN/DS-APP/DS-TRANS, DS-SYM, DS-VAR, DS-TOP — is
valid for `=β`; DS-EQ produces only `≤`, and no rule produces `≡` from
`≤`, so ≡-derivations contain only these (induction with motive
`r = .eq → Beta t u`; the `.le`-only rules are vacuous).

This is the doc's paper-fidelity statement of bound invariance's payoff
(doc §8): the fundamental theorem itself does not consume it — `SemEq`
carries its `Beta` component rule-locally — but it is a deliverable of
§6 in its own right.
-/

namespace Pss.Semantic

/-- **Lemma 6.1 (the ≡-fragment is conversion)**: `Γ ⊢ t ≡wf u ⟹ t =β u`
(stated for the bare instrumented subtyping; `WellSubI`'s ≡-form follows
by projection). -/
theorem subI_eq_beta {Γ : Ctx} {t u : Term}
    (h : SubI Γ t .eq u) : Beta t u := by
  sorry

end Pss.Semantic
