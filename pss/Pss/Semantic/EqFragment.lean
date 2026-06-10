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
  -- The `SubI` family is mutual; mutual inductive predicates have no
  -- `brecOn`, so we apply the raw recursor directly (cf. `Fundamental.lean`).
  -- Motives: `True` for the wf/ctx/well-sub layers; for `SubI` the
  -- implication `r = .eq → Beta t u` (doc §6 Lemma 6.1: the `.le`-only
  -- rules — DS-EQ, DS-ETOP, DS-EVAR — are vacuous).
  -- Each case lambda receives all raw premise values first, then all
  -- motive images in the same order (the layout `Fundamental.lean` uses).
  exact
    SubI.rec (motive_1 := fun _ _ => True)
      (motive_2 := fun _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ => True)
      (motive_4 := fun _ t r u _ => r = .eq → Beta t u)
      -- CtxWfI.nil / CtxWfI.cons
      trivial
      (fun _ _ _ _ => trivial)
      -- WfI.var / WfI.top / WfI.fn / WfI.app
      (fun _ _ _ => trivial)
      (fun _ _ => trivial)
      (fun _ _ => trivial)
      (fun _ _ _ _ => trivial)
      -- WellSubI.sub
      (fun _ _ _ _ _ _ => trivial)
      -- DS-TRANS: `Beta.trans` of the two IHs (both at `.eq`).
      (fun _ _ _ ih₁ ih₂ _ heq => Beta.trans (ih₁ heq) (ih₂ heq))
      -- DS-SYM: `Beta.symm` of the IH.
      (fun _ ih heq => Beta.symm (ih heq))
      -- DS-EQ: concludes `.le`, so `r = .eq` is impossible.
      (fun _ _ heq => by cases heq)
      -- DS-VAR / DS-TOP: reflexivity.
      (fun _ _ _ _ => Beta.refl _)
      (fun _ _ _ => Beta.refl _)
      -- DS-FUN: `Beta.lam` — bound IH at `.eq`, body IH applied to `r = .eq`.
      (fun _ _ _ _ ih₁ ih₂ _ _ heq =>
        Beta.lam (ih₁ rfl) (ih₂ heq))
      -- DS-APP: `Beta.app` — function IH applied to `r = .eq`, argument
      -- IH at `.eq`.
      (fun _ _ _ _ _ _ ih₁ ih₂ _ _ _ _ heq =>
        Beta.app (ih₁ heq) (ih₂ rfl))
      -- DS-EAPP: one β-step, `(λx≤t.u)(s) ⟶ [x↦s]u`.
      (fun _ _ _ _ _ => Beta.of_step Step.eapp)
      -- DS-ETOP / DS-EVAR: conclude `.le`, vacuous.
      (fun _ _ heq => by cases heq)
      (fun _ _ _ heq => by cases heq)
      h rfl

end Pss.Semantic
