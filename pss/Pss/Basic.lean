import Pss.Reduction
import Pss.Declarative
import Pss.Algorithmic
import Pss.Induction

/-!
# Basic metatheory of System λ⊲

Elementary consequences of the Figure 1 / Figure 2 systems used throughout
the development:

* reflexivity of declarative `≡` (hence of `⊲`),
* the arrow-type sugar `t → u` of §3,
* prevalidity extraction for the algorithmic judgments,
* multi-step congruence helpers for `⊲→*`,
* the §6.1 (p. 294) characterization of algorithmic subtyping as joins:
  `Γ ⊢A t ⊲ u` iff `t ⊲→* s *←≡ u` for some `s`.
-/

namespace Pss

/-! ## Arrow sugar (§3) -/

namespace Term

/-- `t → u` is sugar for `λx ≤ t. u` with `x` fresh (§3); freshness is the
de Bruijn shift of the body. -/
def arrow (t u : Term) : Term := .lam t (u.shift 1)

end Term

/-! ## Reflexivity of declarative subtyping -/

/-- `Γ ⊢ t ≡ t` is derivable for every term (DS-VAR, DS-TOP, DS-FUN, DS-APP). -/
theorem Sub.refl_eq (t : Term) : ∀ (Γ : Ctx), Sub Γ t .eq t := by
  induction t with
  | var x => intro Γ; exact .var
  | top => intro Γ; exact .top
  | lam t u iht ihu => intro Γ; exact .fn (iht Γ) (ihu (t :: Γ))
  | app t u iht ihu => intro Γ; exact .app (iht Γ) (ihu Γ)

/-- `≡` entails `⊲` for either relation (identity at `≡`, DS-EQ at `≤`). -/
theorem Sub.of_eq {Γ : Ctx} {t u : Term} (h : Sub Γ t .eq u) :
    ∀ r, Sub Γ t r u
  | .le => .eq h
  | .eq => h

/-- `Γ ⊢ t ⊲ t` for every term and either relation. -/
theorem Sub.refl (t : Term) (Γ : Ctx) (r : Rel) : Sub Γ t r t :=
  (Sub.refl_eq t Γ).of_eq r

/-! ## Prevalidity extraction

Every algorithmic judgment is rooted in a `Prevalid` leaf in the same
context (rules only ever *extend* the context, and `Prevalid` is closed
under restriction). -/

theorem Prevalid.tail {Γ : Ctx} {t : Term} (h : Prevalid (t :: Γ)) :
    Prevalid Γ := by
  cases h with
  | cons h _ => exact h

private theorem alg_prevalid :
    (∀ Γ t r t', Red Γ t r t' → Prevalid Γ)
    ∧ (∀ Γ t r u, ASub Γ t r u → Prevalid Γ)
    ∧ (∀ Γ t r u, ATSub Γ t r u → Prevalid Γ) :=
  alg_induction
    (motR := fun Γ _ _ _ => Prevalid Γ)
    (motA := fun Γ _ _ _ => Prevalid Γ)
    (motT := fun Γ _ _ _ => Prevalid Γ)
    (red_prom := fun h _ => h)
    (red_rtop := fun h => h)
    (red_beta := fun _ ih => ih)
    (red_topApp := fun h => h)
    (red_cong := fun _ _ ih => ih)
    (red_fn := fun _ ih => ih.tail)
    (red_eq := fun _ ih => ih)
    (asub_refl := fun h => h)
    (asub_left := fun _ _ ih _ => ih)
    (asub_right := fun _ _ ih _ => ih)
    (atsub_sub := fun _ ih => ih)
    (atsub_trans := fun _ _ ih _ => ih)

/-- A reduction step `Γ ⊢A t ⊲→ t'` presupposes a prevalid context. -/
theorem Red.prevalid {Γ : Ctx} {t t' : Term} {r : Rel} (h : Red Γ t r t') :
    Prevalid Γ := alg_prevalid.1 Γ t r t' h

/-- `Γ ⊢A t ⊲ u` presupposes a prevalid context. -/
theorem ASub.prevalid {Γ : Ctx} {t u : Term} {r : Rel} (h : ASub Γ t r u) :
    Prevalid Γ := alg_prevalid.2.1 Γ t r u h

/-- `Γ ⊢A t ⊲* u` presupposes a prevalid context. -/
theorem ATSub.prevalid {Γ : Ctx} {t u : Term} {r : Rel} (h : ATSub Γ t r u) :
    Prevalid Γ := alg_prevalid.2.2 Γ t r u h

/-! ## Multi-step reduction helpers -/

/-- `≡→*` sequences are `≤→*` sequences (pointwise SR-EQ). -/
theorem RedStar.of_eq {Γ : Ctx} {t t' : Term} (h : RedStar Γ t .eq t') :
    RedStar Γ t .le t' :=
  h.mono fun hs => .eq hs

/-- SR-CONG lifted to reduction sequences. -/
theorem RedStar.cong {Γ : Ctx} {t t' : Term} {r : Rel} (E : ECtx r)
    (h : RedStar Γ t r t') : RedStar Γ (E.fill t) r (E.fill t') :=
  h.map E.fill fun hs => .cong E hs

/-- SR-FUN lifted to reduction sequences. -/
theorem RedStar.fn {Γ : Ctx} {t u u' : Term} {r : Rel}
    (h : RedStar (t :: Γ) u r u') : RedStar Γ (.lam t u) r (.lam t u') :=
  h.map (Term.lam t) fun hs => .fn hs

/-! ## Algorithmic subtyping as joins (§6.1, p. 294)

> `Γ ⊢A t ≡ u` iff `Γ ⊢A t ≡→* s *←≡ u` for some `s`.
> `Γ ⊢A t ≤ u` iff `Γ ⊢A t ≤→* s *←≡ u` for some `s`.
-/

/-- Forward direction: a `⊲` derivation yields a join. -/
theorem ASub.to_join {Γ : Ctx} {t u : Term} {r : Rel} (h : ASub Γ t r u) :
    ∃ s, RedStar Γ t r s ∧ RedStar Γ u .eq s :=
  h.induct
    (motR := fun _ _ _ _ => True)
    (motA := fun Γ t r u => ∃ s, RedStar Γ t r s ∧ RedStar Γ u .eq s)
    (motT := fun _ _ _ _ => True)
    (red_prom := fun _ _ => trivial)
    (red_rtop := fun _ => trivial)
    (red_beta := fun _ _ => trivial)
    (red_topApp := fun _ => trivial)
    (red_cong := fun _ _ _ => trivial)
    (red_fn := fun _ _ => trivial)
    (red_eq := fun _ _ => trivial)
    (asub_refl := fun _ => ⟨_, .refl, .refl⟩)
    (asub_left := fun hred _ _ ih => by
      obtain ⟨s, h1, h2⟩ := ih
      exact ⟨s, .head hred h1, h2⟩)
    (asub_right := fun hred _ _ ih => by
      obtain ⟨s, h1, h2⟩ := ih
      exact ⟨s, h1, .head hred h2⟩)
    (atsub_sub := fun _ _ => trivial)
    (atsub_trans := fun _ _ _ _ => trivial)

/-- Backward direction: a join yields a `⊲` derivation (the context must be
prevalid to seed AS-REFL). -/
theorem ASub.of_join {Γ : Ctx} {t u s : Term} {r : Rel} (hΓ : Prevalid Γ)
    (h1 : RedStar Γ t r s) (h2 : RedStar Γ u .eq s) : ASub Γ t r u := by
  revert h2
  induction h1 with
  | refl =>
    intro h2
    induction h2 with
    | refl => exact .refl hΓ
    | head hstep _ ih => exact .right hstep ih
  | head hstep _ ih =>
    intro h2
    exact .left hstep (ih h2)

/-- The p. 294 characterization, packaged. -/
theorem asub_iff_join {Γ : Ctx} {t u : Term} {r : Rel} (hΓ : Prevalid Γ) :
    ASub Γ t r u ↔ ∃ s, RedStar Γ t r s ∧ RedStar Γ u .eq s :=
  ⟨ASub.to_join, fun ⟨_, h1, h2⟩ => ASub.of_join hΓ h1 h2⟩

/-- Algorithmic `≡` entails algorithmic `≤` (join transport along SR-EQ). -/
theorem ASub.le_of_eq {Γ : Ctx} {t u : Term} (h : ASub Γ t .eq u) :
    ASub Γ t .le u :=
  have ⟨_, h1, h2⟩ := h.to_join
  ASub.of_join h.prevalid h1.of_eq h2

end Pss
