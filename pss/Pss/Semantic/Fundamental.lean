import Pss.Semantic.Instrumented
import Pss.Semantic.Model
import Pss.Semantic.RulesEasy
import Pss.Semantic.RulesFun
import Pss.Semantic.RulesApp

/-!
# The fundamental theorem

§6 of `pss/docs/03-revised-proof.md`, Theorem 6.2: every instrumented
judgement is sound for the model. Mutual induction on derivations with
motives

- `CtxWfI Γ ↦ True` (no rule consumes a context derivation semantically),
- `WfI Γ t ↦ SemWf Γ t`,
- `WellSubI Γ t r u ↦ SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u`,
- `SubI Γ t r u ↦ SemRel r Γ t u`.

Mutual inductive *predicates* get no `brecOn`, so the equation compiler
cannot do mutual structural recursion here; the three theorems are
direct applications of the auto-generated mutual recursors
(`WfI.rec` / `WellSubI.rec` / `SubI.rec`), sharing one set of case
terms: each case is a `sound_*` lemma (RulesEasy/Fun/App), Model.lean's
proven glue (`SemLe.trans` — Theorem 5.1 — for DS-TRANS ≤), or trivial
packaging; the `⊲`-indexed rules dispatch on `Rel` in the private
`case_*` adapters. This file is **fully proven**: it is the integration
test that the per-rule statements compose into the recursor — it
compiling means the phase-B architecture type-checks end-to-end.
-/

namespace Pss.Semantic

/-- DS-TRANS, dispatching `⊲`: ≤ is Theorem 5.1, ≡ composes `=β` and wf.
(The instrumented middle-wf IH is dropped — doc §6: "not even needed
semantically".) -/
private theorem case_trans {Γ : Ctx} {s t u : Term} {r : Rel}
    (ih₁ : SemRel r Γ s t) (ih₂ : SemRel r Γ t u) : SemRel r Γ s u :=
  match r with
  | .le => SemLe.trans ih₁ ih₂
  | .eq => sound_trans_eq ih₁ ih₂

/-- DS-FUN, dispatching `⊲`. -/
private theorem case_fn {Γ : Ctx} {t t' u u' : Term} {r : Rel}
    (ih₁ : SemEq Γ t t') (ih₂ : SemRel r (t :: Γ) u u')
    (ihw₁ : SemWf Γ (.lam t u)) (ihw₂ : SemWf Γ (.lam t' u')) :
    SemRel r Γ (.lam t u) (.lam t' u') :=
  match r with
  | .le => sound_fn_le ih₁ ih₂ ihw₁ ihw₂
  | .eq => sound_fn_eq ih₁ ih₂ ihw₁ ihw₂

/-- DS-APP, dispatching `⊲`; the four triples are the motive images of
the four unpacked `WellSubI` instrumentations. -/
private theorem case_app {Γ : Ctx} {t t' u u' s s' : Term} {r : Rel}
    (ih₁ : SemRel r Γ t t') (ih₂ : SemEq Γ u u')
    (hi₁ : SemWf Γ t ∧ SemWf Γ (.lam s .top) ∧ SemLe Γ t (.lam s .top))
    (hi₂ : SemWf Γ u ∧ SemWf Γ s ∧ SemLe Γ u s)
    (hi₃ : SemWf Γ t' ∧ SemWf Γ (.lam s' .top) ∧ SemLe Γ t' (.lam s' .top))
    (hi₄ : SemWf Γ u' ∧ SemWf Γ s' ∧ SemLe Γ u' s') :
    SemRel r Γ (.app t u) (.app t' u') :=
  match r with
  | .le => sound_app_le ih₁ ih₂ hi₁ hi₂ hi₃ hi₄
  | .eq => sound_app_eq ih₁ ih₂ hi₁ hi₂ hi₃ hi₄

/-- **Theorem 6.2(1)** (doc §6): `Γ ⊢ t wf ⟹ Γ ⊨ t wf`. -/
theorem fundamental_wf {Γ : Ctx} {t : Term} (h : WfI Γ t) : SemWf Γ t :=
  WfI.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t _ => SemWf Γ t)
    (motive_3 := fun Γ t r u _ => SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u)
    (motive_4 := fun Γ t r u _ => SemRel r Γ t u)
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ hx _ => sound_wvar hx)
    (fun _ _ => sound_wtop)
    (fun _ ih => sound_wfun ih)
    (fun _ _ ih₁ ih₂ => sound_wapp ih₁.2.2 ih₂.2.2 ih₁.1 ih₂.1)
    (fun _ _ _ ihw₁ ihw₂ ihs => ⟨ihw₁, ihw₂, ihs⟩)
    (fun _ _ _ ih₁ ih₂ _ => case_trans ih₁ ih₂)
    (fun _ ih => sound_sym ih)
    (fun _ ih => sound_eq ih)
    (fun _ hx _ => sound_var hx)
    (fun _ _ => sound_top)
    (fun _ _ _ _ ih₁ ih₂ ihw₁ ihw₂ => case_fn ih₁ ih₂ ihw₁ ihw₂)
    (fun _ _ _ _ _ _ ih₁ ih₂ hi₁ hi₂ hi₃ hi₄ =>
      case_app ih₁ ih₂ hi₁ hi₂ hi₃ hi₄)
    (fun _ _ ih₁ ih₂ => sound_eapp ih₁ ih₂)
    (fun _ ih => sound_etop ih)
    (fun hb _ _ => sound_evar hb)
    h

/-- **Theorem 6.2(2,3)** packaged for W-SUB: a well-subtyping yields wf
of both endpoints plus the semantic relation. -/
theorem fundamental_wellSub {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSubI Γ t r u) : SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u :=
  WellSubI.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t _ => SemWf Γ t)
    (motive_3 := fun Γ t r u _ => SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u)
    (motive_4 := fun Γ t r u _ => SemRel r Γ t u)
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ hx _ => sound_wvar hx)
    (fun _ _ => sound_wtop)
    (fun _ ih => sound_wfun ih)
    (fun _ _ ih₁ ih₂ => sound_wapp ih₁.2.2 ih₂.2.2 ih₁.1 ih₂.1)
    (fun _ _ _ ihw₁ ihw₂ ihs => ⟨ihw₁, ihw₂, ihs⟩)
    (fun _ _ _ ih₁ ih₂ _ => case_trans ih₁ ih₂)
    (fun _ ih => sound_sym ih)
    (fun _ ih => sound_eq ih)
    (fun _ hx _ => sound_var hx)
    (fun _ _ => sound_top)
    (fun _ _ _ _ ih₁ ih₂ ihw₁ ihw₂ => case_fn ih₁ ih₂ ihw₁ ihw₂)
    (fun _ _ _ _ _ _ ih₁ ih₂ hi₁ hi₂ hi₃ hi₄ =>
      case_app ih₁ ih₂ hi₁ hi₂ hi₃ hi₄)
    (fun _ _ ih₁ ih₂ => sound_eapp ih₁ ih₂)
    (fun _ ih => sound_etop ih)
    (fun hb _ _ => sound_evar hb)
    h

/-- **Theorem 6.2(2,3)**, the rule cases: `Γ ⊢ t ⊲ u ⟹ Γ ⊨ t ⊲ u`. -/
theorem fundamental_sub {Γ : Ctx} {t u : Term} {r : Rel}
    (h : SubI Γ t r u) : SemRel r Γ t u :=
  SubI.rec (motive_1 := fun _ _ => True)
    (motive_2 := fun Γ t _ => SemWf Γ t)
    (motive_3 := fun Γ t r u _ => SemWf Γ t ∧ SemWf Γ u ∧ SemRel r Γ t u)
    (motive_4 := fun Γ t r u _ => SemRel r Γ t u)
    trivial
    (fun _ _ _ _ => trivial)
    (fun _ hx _ => sound_wvar hx)
    (fun _ _ => sound_wtop)
    (fun _ ih => sound_wfun ih)
    (fun _ _ ih₁ ih₂ => sound_wapp ih₁.2.2 ih₂.2.2 ih₁.1 ih₂.1)
    (fun _ _ _ ihw₁ ihw₂ ihs => ⟨ihw₁, ihw₂, ihs⟩)
    (fun _ _ _ ih₁ ih₂ _ => case_trans ih₁ ih₂)
    (fun _ ih => sound_sym ih)
    (fun _ ih => sound_eq ih)
    (fun _ hx _ => sound_var hx)
    (fun _ _ => sound_top)
    (fun _ _ _ _ ih₁ ih₂ ihw₁ ihw₂ => case_fn ih₁ ih₂ ihw₁ ihw₂)
    (fun _ _ _ _ _ _ ih₁ ih₂ hi₁ hi₂ hi₃ hi₄ =>
      case_app ih₁ ih₂ hi₁ hi₂ hi₃ hi₄)
    (fun _ _ ih₁ ih₂ => sound_eapp ih₁ ih₂)
    (fun _ ih => sound_etop ih)
    (fun hb _ _ => sound_evar hb)
    h

end Pss.Semantic
