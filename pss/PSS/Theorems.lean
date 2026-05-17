import PSS.Syntax
import PSS.Reduction
import PSS.Declarative
import PSS.Algorithmic

/-!
# Theorem Statements

All theorem, lemma, and conjecture statements from the PSS paper (Sections 5–6).
Bodies are `sorry` — the user intends to prove these with a different method.

## Section 5: Type Safety

Type safety is proved via progress and preservation, conditional on
transitivity elimination (Conjecture 5.1).

## Section 6: Transitivity Elimination

Transitivity elimination is formulated via confluence and commutativity
of the algorithmic reduction relations.
-/

open Expr

namespace PSS

/-!
## Section 5: Type Safety
-/

/-- **Conjecture 5.1 (Transitivity elimination)**

    If `Γ ⊢ v ≤_wf w`, then there exists a proof of `Γ ⊢ v ≤ w` that
    ends in either DS-FUN or DS-ETOP (i.e., transitivity is admissible). -/
theorem transitivity_elimination {Γ : Ctx} {v w : Expr}
    (h : WfSub Γ v w) :
    DeclRel .sub Γ v w :=
  sorry

/-- **Lemma 5.2 (Inversion of subtyping — declarative version)**

    If `Γ ⊢ (λt.u) ≤_wf (λt'.u')` then `Γ ⊢ t ≡ t'`. -/
theorem inversion_of_subtyping {Γ : Ctx} {dom dom' body body' : Expr}
    (h : WfSub Γ (.lam dom body) (.lam dom' body')) :
    DeclRel .equiv Γ dom dom' :=
  sorry

/-- **Lemma 5.3 (Reduction implies equivalence)**

    If `t ⟶ t'` then `Γ ⊢ t ≡ t'`. -/
theorem reduction_implies_equiv {Γ : Ctx} {t t' : Expr}
    (h : Step t t') :
    DeclRel .equiv Γ t t' :=
  sorry

/-- **Lemma 5.4 (Substitution)**

    If `Γ, x ≤ t, Γ' ⊢ u ◁_wf s` and `Γ ⊢ t' ≤_wf t`
    then `Γ, [x ↦ t']Γ' ⊢ [x ↦ t']u ◁_wf [x ↦ t']s`.

    Stated here for the subtype case; the equivalence case is analogous.
    In de Bruijn, this is substitution at position `j` in the context. -/
theorem substitution {Γ : Ctx} {t t' u s : Expr} {j : Nat}
    (hsub : WfSub (t :: Γ) u s)
    (harg : WfSub Γ t' t) :
    DeclRel .sub Γ (u.subst 0 t') (s.subst 0 t') :=
  sorry

/-- **Theorem 5.5 (Progress)**

    If `∅ ⊢ t wf` then either `t` is a value, or there exists `t'`
    such that `t ⟶ t'`. -/
theorem progress {t : Expr}
    (hwf : Wf [] t) :
    t.IsValue ∨ ∃ t', Step t t' :=
  sorry

/-- **Theorem 5.6 (Preservation)**

    If `Γ ⊢ t ≤_wf u` and `t ⟶ t'` then `Γ ⊢ t' ≤_wf u`. -/
theorem preservation {Γ : Ctx} {t t' u : Expr}
    (hwf : WfSub Γ t u)
    (hstep : Step t t') :
    WfSub Γ t' u :=
  sorry

/-!
## Section 6: Transitivity Elimination via Confluence
-/

/-- **Theorem 6.1 (≡→ is confluent)**

    If `Γ ⊢_A t₀ ≡→ t₁` and `Γ ⊢_A t₀ ≡→ t₂`, then there exists `t₃`
    such that `Γ ⊢_A t₁ ≡→* t₃` and `Γ ⊢_A t₂ ≡→* t₃`. -/
theorem equiv_red_confluent {Γ : Ctx} {t₀ t₁ t₂ : Expr}
    (h₁ : EquivRedStep Γ t₀ t₁)
    (h₂ : EquivRedStep Γ t₀ t₂) :
    ∃ t₃, EquivRedSteps Γ t₁ t₃ ∧ EquivRedSteps Γ t₂ t₃ :=
  sorry

/-- **Conjecture 6.2 (≡→ commutes with ≤→)**

    If `Γ ⊢_A t₀ ≡→ t₁` and `Γ ⊢_A t₀ ≤→ t₂`, then there exists `t₃`
    such that `Γ ⊢_A t₂ ≡→* t₃` and `Γ ⊢_A t₁ ≤→* t₃`.

    This is the key open conjecture from the paper — the "almost, but
    not quite" result discussed in Section 6.6.3. -/
theorem equiv_sub_commute {Γ : Ctx} {t₀ t₁ t₂ : Expr}
    (h₁ : EquivRedStep Γ t₀ t₁)
    (h₂ : SubRedStep Γ t₀ t₂) :
    ∃ t₃, EquivRedSteps Γ t₂ t₃ ∧ TransSub Γ t₁ t₃ :=
  sorry

/-- **Lemma 6.3 (Commutativity implies transitivity)**

    If ≡→ commutes with ≤→, then transitivity is admissible in the
    algorithmic system. -/
theorem commutativity_implies_transitivity
    (comm : ∀ {Γ : Ctx} {t₀ t₁ t₂ : Expr},
      EquivRedStep Γ t₀ t₁ → SubRedStep Γ t₀ t₂ →
      ∃ t₃, EquivRedSteps Γ t₂ t₃ ∧ TransSub Γ t₁ t₃)
    {Γ : Ctx} {s t u : Expr}
    (h₁ : AlgSub .sub Γ s t)
    (h₂ : AlgSub .sub Γ t u) :
    AlgSub .sub Γ s u :=
  sorry

/-- **Lemma 6.4 (≤→ and ≡→ commute locally)**

    If `Γ ⊢_A t₀ ≡→ t₁` and `Γ ⊢_A t₀ ≤→ t₂`, then there exists `t₃`
    such that `Γ ⊢_A t₂ ≡→^(=) t₃` and `Γ ⊢_A t₁ ≤* t₃`.

    This is the local version that the paper proves — it falls short of
    the full commutativity conjecture because the completing edge on the
    right is `≤*` (transitive closure) rather than a single `≤→` step. -/
theorem local_commute {Γ : Ctx} {t₀ t₁ t₂ : Expr}
    (h₁ : EquivRedStep Γ t₀ t₁)
    (h₂ : SubRedStep Γ t₀ t₂) :
    ∃ t₃, EquivRedSteps Γ t₂ t₃ ∧ TransSub Γ t₁ t₃ :=
  sorry

/-!
## Section 4: Embedding (statement only)

The embedding of a PTS (System λ*) into System λ_◁ is stated here at
the term level. The full PTS typing judgment is not mechanised; these
statements record the *shape* of the preservation theorems.
-/

/-- Translation from a PTS term to a PSS term.
    `⟨x⟩ = x`, `⟨*⟩ = Top`, `⟨λx:t.u⟩ = ⟨Πx:t.u⟩ = λ⟨t⟩.⟨u⟩`,
    `⟨t(u)⟩ = ⟨t⟩(⟨u⟩)`.

    Since PTS λ-abstraction and Π-types map to the same PSS form,
    a PTS term is just an Expr (with no Π constructor needed). -/
def ptsTranslate : Expr → Expr := id

/-- **Lemma 4.1 (Substitution is preserved under translation)**

    `⟨[x ↦ t]u⟩ = [x ↦ ⟨t⟩]⟨u⟩` -/
theorem pts_subst_preserved {u : Expr} {j : Nat} {t : Expr} :
    ptsTranslate (u.subst j t) = (ptsTranslate u).subst j (ptsTranslate t) :=
  sorry

/-- **Theorem 4.2 (Reduction is preserved under translation)**

    If `t ⟶ u` then `⟨t⟩ ⟶ ⟨u⟩`. -/
theorem pts_reduction_preserved {t u : Expr}
    (h : Step t u) :
    Step (ptsTranslate t) (ptsTranslate u) :=
  sorry

end PSS
