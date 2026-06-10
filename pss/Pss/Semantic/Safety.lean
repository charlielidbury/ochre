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

/-- All bounds in a context are closed under their respective suffixes.
The `WfI.fn` rule (Figure 1's W-FUN) carries no separate well-formedness
premise for the bound `t`; the bound's closedness is enforced *only*
indirectly, through the `CtxWfI (t :: Γ)` premise that every leaf rule
(`WfI.var`/`WfI.top`/`WfI.app`) of a non-vacuous body derivation carries.
Threading this structural invariant through the recursor is what lets the
`fn` case recover `ClosedUnder Γ.length t` for the bound. -/
private def CtxClosed : Ctx → Prop
  | [] => True
  | t :: Γ => ClosedUnder Γ.length t ∧ CtxClosed Γ

/-- A well-formed term is closed under its context, and that context's
bounds are themselves closed (the strengthened invariant the recursor
needs — see `CtxClosed`). -/
private theorem wfI_closedUnder_aux {Γ : Ctx} {t : Term} (h : WfI Γ t) :
    CtxClosed Γ ∧ ClosedUnder Γ.length t :=
  WfI.rec (motive_1 := fun Γ _ => CtxClosed Γ)
    (motive_2 := fun Γ t _ => CtxClosed Γ ∧ ClosedUnder Γ.length t)
    (motive_3 := fun Γ t _ u _ =>
      CtxClosed Γ ∧ ClosedUnder Γ.length t ∧ ClosedUnder Γ.length u)
    (motive_4 := fun Γ _ _ _ _ => CtxClosed Γ)
    -- CtxWfI.nil, CtxWfI.cons
    trivial
    (fun _ _ _ ih => ⟨ih.2, ih.1⟩)
    -- WfI.var: x < Γ.length, context closed from CtxWfI IH
    (fun _ hx ihc => ⟨ihc, ClosedUnder.var hx⟩)
    -- WfI.top
    (fun _ ihc => ⟨ihc, ClosedUnder.top⟩)
    -- WfI.fn: body IH gives CtxClosed (t :: Γ), whose head is the bound
    (fun _ ih => ⟨ih.1.2, ClosedUnder.lam ih.1.1 ih.2⟩)
    -- WfI.app: context + both endpoints from the two WellSub IHs
    (fun _ _ ih₁ ih₂ => ⟨ih₁.1, ClosedUnder.app ih₁.2.1 ih₂.2.1⟩)
    -- WellSubI.sub: context, t (from WfI t IH), u (from WfI u IH)
    (fun _ _ _ ihw₁ ihw₂ _ => ⟨ihw₁.1, ihw₁.2, ihw₂.2⟩)
    -- SubI cases: motive_4 = CtxClosed Γ, threaded from sub-derivations
    -- trans: SubI s t, SubI t u, WfI t + 3 IHs
    (fun _ _ _ ih₁ _ _ => ih₁)
    -- symm: SubI u eq t + ih
    (fun _ ih => ih)
    -- eq: SubI t eq u + ih
    (fun _ ih => ih)
    -- var: CtxWfI Γ, x<len + CtxWfI-IH (CtxClosed Γ)
    (fun _ _ ihc => ihc)
    -- top: CtxWfI Γ + CtxWfI-IH
    (fun _ ihc => ihc)
    -- fn: SubI t eq t', SubI u u', WfI λ, WfI λ' + 4 IHs (ih₁ = eq IH)
    (fun _ _ _ _ ih₁ _ _ _ => ih₁)
    -- app: SubI t t', SubI u eq u', 4 WellSubI + 6 IHs (ih₁ at pos 7)
    (fun _ _ _ _ _ _ ih₁ _ _ _ _ _ => ih₁)
    -- eapp: WfI redex, WfI contractum + 2 IHs (ih₁ = redex motive_2 pair)
    (fun _ _ ih₁ _ => ih₁.1)
    -- etop: WfI t + ih (motive_2 pair)
    (fun _ ih => ih.1)
    -- evar: Ctx.Bound, CtxWfI Γ + CtxWfI-IH
    (fun _ _ ihc => ihc)
    h

/-- Well-formed terms are closed under their context (Figure 1's
`fv(t) ⊆ dom(Γ)` discipline, recovered from the instrumented system;
feeds Fact 1.1, which needs closed programs). -/
theorem wfI_closedUnder {Γ : Ctx} {t : Term} (h : WfI Γ t) :
    ClosedUnder Γ.length t :=
  (wfI_closedUnder_aux h).2

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
