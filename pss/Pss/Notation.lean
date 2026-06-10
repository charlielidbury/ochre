import Pss.Reduction
import Pss.Declarative
import Pss.Algorithmic

/-!
# Paper notation

Scoped notation mirroring the judgments of Figures 1 and 2. Symbolic tokens
only (alphabetic atoms like `wf` would become reserved keywords for every
importer, breaking `wf` as an identifier); the well-formedness judgments
`Γ wf` / `Γ ⊢ t wf` / `Γ prevalid` therefore stay as named predicates
`CtxWf Γ` / `Wf Γ t` / `Prevalid Γ`.

Open `Pss` (the notations are `scoped`) to use.
-/

namespace Pss

/-! ## Reduction (Figure 1) -/

@[inherit_doc Step] scoped notation:50 t:51 " ⟶ " t':51 => Step t t'
@[inherit_doc Steps] scoped notation:50 t:51 " ⟶* " t':51 => Steps t t'

/-! ## Declarative subtyping (Figure 1) -/

@[inherit_doc Sub] scoped notation:50 Γ:51 " ⊢ " t:51 " ≤ " u:51 => Sub Γ t Rel.le u
@[inherit_doc Sub] scoped notation:50 Γ:51 " ⊢ " t:51 " ≡ " u:51 => Sub Γ t Rel.eq u
@[inherit_doc WellSub] scoped notation:50 Γ:51 " ⊢ " t:51 " ≤wf " u:51 => WellSub Γ t Rel.le u
@[inherit_doc WellSub] scoped notation:50 Γ:51 " ⊢ " t:51 " ≡wf " u:51 => WellSub Γ t Rel.eq u

/-! ## Algorithmic subtyping (Figure 2) -/

@[inherit_doc Red] scoped notation:50 Γ:51 " ⊢A " t:51 " ≤→ " t':51 => Red Γ t Rel.le t'
@[inherit_doc Red] scoped notation:50 Γ:51 " ⊢A " t:51 " ≡→ " t':51 => Red Γ t Rel.eq t'
@[inherit_doc RedStar] scoped notation:50 Γ:51 " ⊢A " t:51 " ≤→* " t':51 => RedStar Γ t Rel.le t'
@[inherit_doc RedStar] scoped notation:50 Γ:51 " ⊢A " t:51 " ≡→* " t':51 => RedStar Γ t Rel.eq t'
@[inherit_doc ASub] scoped notation:50 Γ:51 " ⊢A " t:51 " ≤ " u:51 => ASub Γ t Rel.le u
@[inherit_doc ASub] scoped notation:50 Γ:51 " ⊢A " t:51 " ≡ " u:51 => ASub Γ t Rel.eq u
@[inherit_doc ATSub] scoped notation:50 Γ:51 " ⊢A " t:51 " ≤* " u:51 => ATSub Γ t Rel.le u
@[inherit_doc ATSub] scoped notation:50 Γ:51 " ⊢A " t:51 " ≡* " u:51 => ATSub Γ t Rel.eq u

/-! Parse checks: each notation elaborates to the intended judgment. -/

example {t u s : Term} : (Term.app (.lam t u) s) ⟶ (u.subst1 s) := .eapp
example {Γ : Ctx} {t : Term} : Γ ⊢ t ≤ .top := .etop
example {Γ : Ctx} {t u s : Term} : Γ ⊢ (Term.app (.lam t u) s) ≡ (u.subst1 s) := .eapp
example {Γ : Ctx} {t u : Term} (h1 : Wf Γ t) (h2 : Wf Γ u) (h3 : Γ ⊢ t ≤ u) :
    Γ ⊢ t ≤wf u := .sub h1 h2 h3
example {Γ : Ctx} {t : Term} (h : Prevalid Γ) : Γ ⊢A t ≤→ .top := .rtop h
example {Γ : Ctx} {t : Term} (h : Prevalid Γ) : Γ ⊢A t ≤* t := .sub (.refl h)
