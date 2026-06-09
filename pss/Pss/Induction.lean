import Pss.Declarative
import Pss.Algorithmic

/-!
# Joint induction principles for the mutual judgments

Lean's `induction` tactic does not support mutually inductive predicates
("the eliminator has multiple motives"), so this file provides hand-rolled
joint induction principles for

* the declarative block `CtxWf / Wf / WellSub / Sub` (Figure 1), and
* the algorithmic block `Red / ASub / ATSub` (Figure 2),

proved once from the auto-generated recursors. All later metatheory should
use `decl_induction` / `alg_induction` (or the per-judgment `.induct`
projections) instead of raw `.rec` plumbing.

Each hypothesis corresponds to one inference rule of the paper and is named
after it; premises come first, then the induction hypotheses, in rule order.
-/

namespace Pss

/-! ## Declarative block (Figure 1) -/

section DeclInduction

variable {motC : Ctx → Prop}
variable {motW : Ctx → Term → Prop}
variable {motWS : Ctx → Term → Rel → Term → Prop}
variable {motS : Ctx → Term → Rel → Term → Prop}

variable
  (ctx_nil : motC [])
  (ctx_cons : ∀ {Γ : Ctx} {t : Term},
    CtxWf Γ → Wf Γ t → motC Γ → motW Γ t → motC (t :: Γ))
  (wf_var : ∀ {Γ : Ctx} {x : Nat},
    CtxWf Γ → x < Γ.length → motC Γ → motW Γ (.var x))
  (wf_top : ∀ {Γ : Ctx}, CtxWf Γ → motC Γ → motW Γ .top)
  (wf_fn : ∀ {Γ : Ctx} {t u : Term},
    Wf (t :: Γ) u → motW (t :: Γ) u → motW Γ (.lam t u))
  (wf_app : ∀ {Γ : Ctx} {t u s : Term},
    WellSub Γ t .le (.lam s .top) → WellSub Γ u .le s →
    motWS Γ t .le (.lam s .top) → motWS Γ u .le s → motW Γ (.app t u))
  (wsub_sub : ∀ {Γ : Ctx} {t u : Term} {r : Rel},
    Wf Γ t → Wf Γ u → Sub Γ t r u →
    motW Γ t → motW Γ u → motS Γ t r u → motWS Γ t r u)
  (sub_trans : ∀ {Γ : Ctx} {s t u : Term} {r : Rel},
    Sub Γ s r t → Sub Γ t r u → Wf Γ t →
    motS Γ s r t → motS Γ t r u → motW Γ t → motS Γ s r u)
  (sub_symm : ∀ {Γ : Ctx} {t u : Term},
    Sub Γ u .eq t → motS Γ u .eq t → motS Γ t .eq u)
  (sub_eq : ∀ {Γ : Ctx} {t u : Term},
    Sub Γ t .eq u → motS Γ t .eq u → motS Γ t .le u)
  (sub_var : ∀ {Γ : Ctx} {x : Nat}, motS Γ (.var x) .eq (.var x))
  (sub_top : ∀ {Γ : Ctx}, motS Γ .top .eq .top)
  (sub_fn : ∀ {Γ : Ctx} {t t' u u' : Term} {r : Rel},
    Sub Γ t .eq t' → Sub (t :: Γ) u r u' →
    motS Γ t .eq t' → motS (t :: Γ) u r u' →
    motS Γ (.lam t u) r (.lam t' u'))
  (sub_app : ∀ {Γ : Ctx} {t t' u u' : Term} {r : Rel},
    Sub Γ t r t' → Sub Γ u .eq u' →
    motS Γ t r t' → motS Γ u .eq u' →
    motS Γ (.app t u) r (.app t' u'))
  (sub_eapp : ∀ {Γ : Ctx} {t u s : Term},
    motS Γ (.app (.lam t u) s) .eq (u.subst1 s))
  (sub_etop : ∀ {Γ : Ctx} {t : Term}, motS Γ t .le .top)
  (sub_evar : ∀ {Γ : Ctx} {x : Nat} {t : Term},
    Ctx.Bound Γ x t → motS Γ (.var x) .le t)

include ctx_nil ctx_cons wf_var wf_top wf_fn wf_app wsub_sub sub_trans
  sub_symm sub_eq sub_var sub_top sub_fn sub_app sub_eapp sub_etop sub_evar

/-- Joint induction over the declarative block (Figure 1). -/
theorem decl_induction :
    (∀ Γ, CtxWf Γ → motC Γ)
    ∧ (∀ Γ t, Wf Γ t → motW Γ t)
    ∧ (∀ Γ t r u, WellSub Γ t r u → motWS Γ t r u)
    ∧ (∀ Γ t r u, Sub Γ t r u → motS Γ t r u) := by
  refine ⟨fun Γ h => ?_, fun Γ t h => ?_, fun Γ t r u h => ?_, fun Γ t r u h => ?_⟩
  · exact CtxWf.rec (motive_1 := fun Γ _ => motC Γ)
      (motive_2 := fun Γ t _ => motW Γ t)
      (motive_3 := fun Γ t r u _ => motWS Γ t r u)
      (motive_4 := fun Γ t r u _ => motS Γ t r u)
      ctx_nil
      (fun a a1 ih1 ih2 => ctx_cons a a1 ih1 ih2)
      (fun a a1 ih => wf_var a a1 ih)
      (fun a ih => wf_top a ih)
      (fun a ih => wf_fn a ih)
      (fun a a1 ih1 ih2 => wf_app a a1 ih1 ih2)
      (fun a a1 a2 ih1 ih2 ih3 => wsub_sub a a1 a2 ih1 ih2 ih3)
      (fun a a1 a2 ih1 ih2 ih3 => sub_trans a a1 a2 ih1 ih2 ih3)
      (fun a ih => sub_symm a ih)
      (fun a ih => sub_eq a ih)
      sub_var
      sub_top
      (fun a a1 ih1 ih2 => sub_fn a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => sub_app a a1 ih1 ih2)
      sub_eapp
      sub_etop
      (fun a => sub_evar a)
      h
  · exact Wf.rec (motive_1 := fun Γ _ => motC Γ)
      (motive_2 := fun Γ t _ => motW Γ t)
      (motive_3 := fun Γ t r u _ => motWS Γ t r u)
      (motive_4 := fun Γ t r u _ => motS Γ t r u)
      ctx_nil
      (fun a a1 ih1 ih2 => ctx_cons a a1 ih1 ih2)
      (fun a a1 ih => wf_var a a1 ih)
      (fun a ih => wf_top a ih)
      (fun a ih => wf_fn a ih)
      (fun a a1 ih1 ih2 => wf_app a a1 ih1 ih2)
      (fun a a1 a2 ih1 ih2 ih3 => wsub_sub a a1 a2 ih1 ih2 ih3)
      (fun a a1 a2 ih1 ih2 ih3 => sub_trans a a1 a2 ih1 ih2 ih3)
      (fun a ih => sub_symm a ih)
      (fun a ih => sub_eq a ih)
      sub_var
      sub_top
      (fun a a1 ih1 ih2 => sub_fn a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => sub_app a a1 ih1 ih2)
      sub_eapp
      sub_etop
      (fun a => sub_evar a)
      h
  · exact WellSub.rec (motive_1 := fun Γ _ => motC Γ)
      (motive_2 := fun Γ t _ => motW Γ t)
      (motive_3 := fun Γ t r u _ => motWS Γ t r u)
      (motive_4 := fun Γ t r u _ => motS Γ t r u)
      ctx_nil
      (fun a a1 ih1 ih2 => ctx_cons a a1 ih1 ih2)
      (fun a a1 ih => wf_var a a1 ih)
      (fun a ih => wf_top a ih)
      (fun a ih => wf_fn a ih)
      (fun a a1 ih1 ih2 => wf_app a a1 ih1 ih2)
      (fun a a1 a2 ih1 ih2 ih3 => wsub_sub a a1 a2 ih1 ih2 ih3)
      (fun a a1 a2 ih1 ih2 ih3 => sub_trans a a1 a2 ih1 ih2 ih3)
      (fun a ih => sub_symm a ih)
      (fun a ih => sub_eq a ih)
      sub_var
      sub_top
      (fun a a1 ih1 ih2 => sub_fn a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => sub_app a a1 ih1 ih2)
      sub_eapp
      sub_etop
      (fun a => sub_evar a)
      h
  · exact Sub.rec (motive_1 := fun Γ _ => motC Γ)
      (motive_2 := fun Γ t _ => motW Γ t)
      (motive_3 := fun Γ t r u _ => motWS Γ t r u)
      (motive_4 := fun Γ t r u _ => motS Γ t r u)
      ctx_nil
      (fun a a1 ih1 ih2 => ctx_cons a a1 ih1 ih2)
      (fun a a1 ih => wf_var a a1 ih)
      (fun a ih => wf_top a ih)
      (fun a ih => wf_fn a ih)
      (fun a a1 ih1 ih2 => wf_app a a1 ih1 ih2)
      (fun a a1 a2 ih1 ih2 ih3 => wsub_sub a a1 a2 ih1 ih2 ih3)
      (fun a a1 a2 ih1 ih2 ih3 => sub_trans a a1 a2 ih1 ih2 ih3)
      (fun a ih => sub_symm a ih)
      (fun a ih => sub_eq a ih)
      sub_var
      sub_top
      (fun a a1 ih1 ih2 => sub_fn a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => sub_app a a1 ih1 ih2)
      sub_eapp
      sub_etop
      (fun a => sub_evar a)
      h

/-- Induction over `Γ wf` derivations (projection of `decl_induction`). -/
theorem CtxWf.induct {Γ : Ctx} (h : CtxWf Γ) : motC Γ :=
  (decl_induction ctx_nil ctx_cons wf_var wf_top wf_fn wf_app wsub_sub
    sub_trans sub_symm sub_eq sub_var sub_top sub_fn sub_app sub_eapp
    sub_etop sub_evar).1 Γ h

/-- Induction over `Γ ⊢ t wf` derivations (projection of `decl_induction`). -/
theorem Wf.induct {Γ : Ctx} {t : Term} (h : Wf Γ t) : motW Γ t :=
  (decl_induction ctx_nil ctx_cons wf_var wf_top wf_fn wf_app wsub_sub
    sub_trans sub_symm sub_eq sub_var sub_top sub_fn sub_app sub_eapp
    sub_etop sub_evar).2.1 Γ t h

/-- Induction over `Γ ⊢ t ⊲wf u` derivations (projection of `decl_induction`). -/
theorem WellSub.induct {Γ : Ctx} {t u : Term} {r : Rel} (h : WellSub Γ t r u) :
    motWS Γ t r u :=
  (decl_induction ctx_nil ctx_cons wf_var wf_top wf_fn wf_app wsub_sub
    sub_trans sub_symm sub_eq sub_var sub_top sub_fn sub_app sub_eapp
    sub_etop sub_evar).2.2.1 Γ t r u h

/-- Induction over `Γ ⊢ t ⊲ u` derivations (projection of `decl_induction`). -/
theorem Sub.induct {Γ : Ctx} {t u : Term} {r : Rel} (h : Sub Γ t r u) :
    motS Γ t r u :=
  (decl_induction ctx_nil ctx_cons wf_var wf_top wf_fn wf_app wsub_sub
    sub_trans sub_symm sub_eq sub_var sub_top sub_fn sub_app sub_eapp
    sub_etop sub_evar).2.2.2 Γ t r u h

end DeclInduction

/-! ## Algorithmic block (Figure 2) -/

section AlgInduction

variable {motR : Ctx → Term → Rel → Term → Prop}
variable {motA : Ctx → Term → Rel → Term → Prop}
variable {motT : Ctx → Term → Rel → Term → Prop}

variable
  (red_prom : ∀ {Γ : Ctx} {x : Nat} {t : Term},
    Prevalid Γ → Ctx.Bound Γ x t → motR Γ (.var x) .le t)
  (red_rtop : ∀ {Γ : Ctx} {t : Term}, Prevalid Γ → motR Γ t .le .top)
  (red_beta : ∀ {Γ : Ctx} {t u s : Term},
    ATSub Γ s .le t → motT Γ s .le t →
    motR Γ (.app (.lam t u) s) .eq (u.subst1 s))
  (red_topApp : ∀ {Γ : Ctx} {t : Term},
    Prevalid Γ → motR Γ (.app .top t) .eq .top)
  (red_cong : ∀ {Γ : Ctx} {t t' : Term} {r : Rel} (E : ECtx r),
    Red Γ t r t' → motR Γ t r t' → motR Γ (E.fill t) r (E.fill t'))
  (red_fn : ∀ {Γ : Ctx} {t u u' : Term} {r : Rel},
    Red (t :: Γ) u r u' → motR (t :: Γ) u r u' →
    motR Γ (.lam t u) r (.lam t u'))
  (red_eq : ∀ {Γ : Ctx} {t t' : Term},
    Red Γ t .eq t' → motR Γ t .eq t' → motR Γ t .le t')
  (asub_refl : ∀ {Γ : Ctx} {t : Term} {r : Rel}, Prevalid Γ → motA Γ t r t)
  (asub_left : ∀ {Γ : Ctx} {t t' u : Term} {r : Rel},
    Red Γ t r t' → ASub Γ t' r u →
    motR Γ t r t' → motA Γ t' r u → motA Γ t r u)
  (asub_right : ∀ {Γ : Ctx} {t u u' : Term} {r : Rel},
    Red Γ u .eq u' → ASub Γ t r u' →
    motR Γ u .eq u' → motA Γ t r u' → motA Γ t r u)
  (atsub_sub : ∀ {Γ : Ctx} {s u : Term} {r : Rel},
    ASub Γ s r u → motA Γ s r u → motT Γ s r u)
  (atsub_trans : ∀ {Γ : Ctx} {s t u : Term} {r : Rel},
    ATSub Γ s r t → ATSub Γ t r u →
    motT Γ s r t → motT Γ t r u → motT Γ s r u)

include red_prom red_rtop red_beta red_topApp red_cong red_fn red_eq
  asub_refl asub_left asub_right atsub_sub atsub_trans

/-- Joint induction over the algorithmic block (Figure 2). -/
theorem alg_induction :
    (∀ Γ t r t', Red Γ t r t' → motR Γ t r t')
    ∧ (∀ Γ t r u, ASub Γ t r u → motA Γ t r u)
    ∧ (∀ Γ t r u, ATSub Γ t r u → motT Γ t r u) := by
  refine ⟨fun Γ t r t' h => ?_, fun Γ t r u h => ?_, fun Γ t r u h => ?_⟩
  · exact Red.rec (motive_1 := fun Γ t r t' _ => motR Γ t r t')
      (motive_2 := fun Γ t r u _ => motA Γ t r u)
      (motive_3 := fun Γ t r u _ => motT Γ t r u)
      (fun a a1 => red_prom a a1)
      (fun a => red_rtop a)
      (fun a ih => red_beta a ih)
      (fun a => red_topApp a)
      (fun E a ih => red_cong E a ih)
      (fun a ih => red_fn a ih)
      (fun a ih => red_eq a ih)
      (fun a => asub_refl a)
      (fun a a1 ih1 ih2 => asub_left a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => asub_right a a1 ih1 ih2)
      (fun a ih => atsub_sub a ih)
      (fun a a1 ih1 ih2 => atsub_trans a a1 ih1 ih2)
      h
  · exact ASub.rec (motive_1 := fun Γ t r t' _ => motR Γ t r t')
      (motive_2 := fun Γ t r u _ => motA Γ t r u)
      (motive_3 := fun Γ t r u _ => motT Γ t r u)
      (fun a a1 => red_prom a a1)
      (fun a => red_rtop a)
      (fun a ih => red_beta a ih)
      (fun a => red_topApp a)
      (fun E a ih => red_cong E a ih)
      (fun a ih => red_fn a ih)
      (fun a ih => red_eq a ih)
      (fun a => asub_refl a)
      (fun a a1 ih1 ih2 => asub_left a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => asub_right a a1 ih1 ih2)
      (fun a ih => atsub_sub a ih)
      (fun a a1 ih1 ih2 => atsub_trans a a1 ih1 ih2)
      h
  · exact ATSub.rec (motive_1 := fun Γ t r t' _ => motR Γ t r t')
      (motive_2 := fun Γ t r u _ => motA Γ t r u)
      (motive_3 := fun Γ t r u _ => motT Γ t r u)
      (fun a a1 => red_prom a a1)
      (fun a => red_rtop a)
      (fun a ih => red_beta a ih)
      (fun a => red_topApp a)
      (fun E a ih => red_cong E a ih)
      (fun a ih => red_fn a ih)
      (fun a ih => red_eq a ih)
      (fun a => asub_refl a)
      (fun a a1 ih1 ih2 => asub_left a a1 ih1 ih2)
      (fun a a1 ih1 ih2 => asub_right a a1 ih1 ih2)
      (fun a ih => atsub_sub a ih)
      (fun a a1 ih1 ih2 => atsub_trans a a1 ih1 ih2)
      h

/-- Induction over `⊲→` derivations (projection of `alg_induction`). -/
theorem Red.induct {Γ : Ctx} {t t' : Term} {r : Rel} (h : Red Γ t r t') :
    motR Γ t r t' :=
  (alg_induction red_prom red_rtop red_beta red_topApp red_cong red_fn red_eq
    asub_refl asub_left asub_right atsub_sub atsub_trans).1 Γ t r t' h

/-- Induction over `⊲` derivations (projection of `alg_induction`). -/
theorem ASub.induct {Γ : Ctx} {t u : Term} {r : Rel} (h : ASub Γ t r u) :
    motA Γ t r u :=
  (alg_induction red_prom red_rtop red_beta red_topApp red_cong red_fn red_eq
    asub_refl asub_left asub_right atsub_sub atsub_trans).2.1 Γ t r u h

/-- Induction over `⊲*` derivations (projection of `alg_induction`). -/
theorem ATSub.induct {Γ : Ctx} {t u : Term} {r : Rel} (h : ATSub Γ t r u) :
    motT Γ t r u :=
  (alg_induction red_prom red_rtop red_beta red_topApp red_cong red_fn red_eq
    asub_refl asub_left asub_right atsub_sub atsub_trans).2.2 Γ t r u h

end AlgInduction

end Pss
