import Pss.Embedding.LambdaStar
import Pss.Basic

/-!
# §4 Embedding of a Pure Type System

Hutchins, *Pure Subtype Systems* (POPL 2010), §4: System λ* is embedded
into System λ⊲ by the translation

```
⟨x⟩ = x   ⟨∗⟩ = Top   ⟨λx:t. u⟩ = λx ≤ ⟨t⟩. ⟨u⟩
⟨Πx:t. u⟩ = λx ≤ ⟨t⟩. ⟨u⟩   ⟨t(u)⟩ = ⟨t⟩(⟨u⟩)
⟨∅⟩ = ∅   ⟨Γ, x:t⟩ = ⟨Γ⟩, x ≤ ⟨t⟩
```

This file proves Lemma 4.1 (substitution is preserved under translation)
and Theorem 4.2 (reduction is preserved under translation), states
Theorem 4.3 (typing is preserved under translation) as
`Pss.Statements.thm_4_3`, and wires Theorem 4.4 (System λ⊲ is not strongly
normalizing) as an honest conditional: Girard's paradox (`GirardsParadox`,
a stated Prop — its mechanization is out of scope) plus Theorem 4.3 yield a
well-formed λ⊲ term with an infinite reduction sequence.
-/

namespace Pss.Embedding

open LambdaStar

/-- The §4 translation `⟨·⟩` on terms. `λ` and `Π` translate identically:
λ⊲ unifies functions and function types (§2.4–§2.5). -/
def transTm : Tm → Term
  | .var x => .var x
  | .star => .top
  | .lam t u => .lam (transTm t) (transTm u)
  | .pi t u => .lam (transTm t) (transTm u)
  | .app t u => .app (transTm t) (transTm u)

/-- The §4 translation on contexts: `⟨∅⟩ = ∅`, `⟨Γ, x:t⟩ = ⟨Γ⟩, x ≤ ⟨t⟩`. -/
def transCtx : LambdaStar.Ctx → Ctx := List.map transTm

@[simp] theorem transCtx_nil : transCtx [] = [] := rfl

@[simp] theorem transCtx_cons (t : Tm) (Γ : LambdaStar.Ctx) :
    transCtx (t :: Γ) = transTm t :: transCtx Γ := rfl

/-! ## Lemma 4.1, via the σ-calculus: translation commutes with renaming,
then with simultaneous substitution, then specialized to `subst1`. -/

/-- The two systems' `liftRen` are the same function. -/
private theorem liftRen_eq (ρ : Nat → Nat) :
    Tm.liftRen ρ = Term.liftRen ρ := by
  funext n; cases n <;> rfl

/-- Translation commutes with renaming. -/
theorem transTm_rename (ρ : Nat → Nat) (t : Tm) :
    transTm (t.rename ρ) = (transTm t).rename ρ := by
  induction t generalizing ρ with
  | var x => rfl
  | star => rfl
  | lam t u iht ihu =>
    simp [Tm.rename, transTm, Term.rename, iht, ihu, liftRen_eq]
  | pi t u iht ihu =>
    simp [Tm.rename, transTm, Term.rename, iht, ihu, liftRen_eq]
  | app t u iht ihu => simp [Tm.rename, transTm, Term.rename, iht, ihu]

/-- Translation maps `⇑σ` to `⇑(⟨·⟩ ∘ σ)`. -/
private theorem transTm_liftSubst (σ : Nat → Tm) :
    transTm ∘ Tm.liftSubst σ = Term.liftSubst (transTm ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact transTm_rename (· + 1) (σ n)

/-- Translation commutes with simultaneous substitution. -/
theorem transTm_subst (σ : Nat → Tm) (t : Tm) :
    transTm (t.subst σ) = (transTm t).subst (transTm ∘ σ) := by
  induction t generalizing σ with
  | var x => rfl
  | star => rfl
  | lam t u iht ihu =>
    simp [Tm.subst, transTm, Term.subst, iht, ihu, transTm_liftSubst]
  | pi t u iht ihu =>
    simp [Tm.subst, transTm, Term.subst, iht, ihu, transTm_liftSubst]
  | app t u iht ihu => simp [Tm.subst, transTm, Term.subst, iht, ihu]

/-- **Lemma 4.1** (Substitution is preserved under translation):
`⟨[x ↦ t]u⟩ = [x ↦ ⟨t⟩]⟨u⟩`. -/
theorem lemma_4_1 (u t : Tm) :
    transTm (u.subst1 t) = (transTm u).subst1 (transTm t) := by
  show transTm (u.subst (Tm.scons t Tm.var))
      = (transTm u).subst (Term.scons (transTm t) Term.var)
  rw [transTm_subst]
  congr 1
  funext n; cases n <;> rfl

/-- **Theorem 4.2** (Reduction is preserved under translation):
if `t ⟶β u` then `⟨t⟩ ⟶ ⟨u⟩` (a single λ⊲ step). The β base case is
Lemma 4.1 landing on E-APP; each congruence case lands on the matching
`Step.Compat` congruence (in particular both `λ`- and `Π`-congruences land
on the `lam` congruences, since the translation identifies the binders). -/
theorem thm_4_2 {t u : Tm} (h : Beta t u) : Step (transTm t) (transTm u) := by
  rw [Step.step_iff_compat]
  induction h with
  | beta => rw [lemma_4_1]; exact .eapp
  | appL u _ ih => exact .appL _ ih
  | appR t _ ih => exact .appR _ ih
  | lamDom u _ ih => exact .lamBound _ ih
  | lamBody t _ ih => exact .lamBody _ ih
  | piDom u _ ih => exact .lamBound _ ih
  | piBody t _ ih => exact .lamBody _ ih

end Pss.Embedding

namespace Pss.Statements

/-- **Theorem 4.3** (Typing is preserved under translation):
if `Γ ⊢ t : u` in λ* then `⟨Γ⟩ ⊢ ⟨t⟩ ≤wf ⟨u⟩` in λ⊲.

STATUS: stated only, per a descope of the §4 milestone; no proof attempt
was made. The paper proves it "by induction on the derivation of `t : u`"
with full details deferred to the author's PhD thesis [19]. The known hard
cases for a mechanization are (a) **conversion**: a λ* `=β` chain must
become a λ⊲ `≡` chain glued by DS-TRANS, whose middle terms must be
*well-formed* — but λ* conversion provides no typing for the intermediate
terms (the thesis-level gap); and (b) **application**: the well-formedness
of the translated contractum `⟨[x ↦ s]u⟩` required by W-SUB needs the λ⊲
substitution lemma (the paper's Lemma 5.4). -/
def thm_4_3 : Prop :=
  ∀ (Γ : LambdaStar.Ctx) (t u : LambdaStar.Tm),
    LambdaStar.Typing Γ t u →
    WellSub (Embedding.transCtx Γ) (Embedding.transTm t) .le
      (Embedding.transTm u)

end Pss.Statements

namespace Pss.Embedding

/-- §4.2: System λ* admits Girard's paradox — there is a well-typed closed
λ* term with an infinite β-reduction sequence. Established by
Girard/Barendregt [4][16][17]; mechanizing the paradox itself is out of
scope here, so Theorem 4.4 takes this Prop as a hypothesis. -/
def GirardsParadox : Prop :=
  ∃ (t T : LambdaStar.Tm), LambdaStar.Typing [] t T ∧
    ∃ f : Nat → LambdaStar.Tm,
      f 0 = t ∧ ∀ n, LambdaStar.Beta (f n) (f (n + 1))

/-- **Theorem 4.4** (System λ⊲ is not strongly normalizing), as the honest
conditional wiring of the paper's proof: Girard's paradox gives a well-typed
λ* term `t` with an infinite reduction sequence; by Theorem 4.3 (stated
only, hence an explicit hypothesis here) `⟨t⟩` is well-formed, and by
Theorem 4.2 (proved above, applied pointwise) its translated reduction
sequence is infinite. -/
theorem thm_4_4 (hG : GirardsParadox) (h43 : Statements.thm_4_3) :
    ∃ t : Term, Wf [] t ∧ ∃ g : Nat → Term, g 0 = t ∧ InfiniteReduction g := by
  obtain ⟨t, T, hty, f, hf0, hstep⟩ := hG
  refine ⟨transTm t, ?_, fun n => transTm (f n), congrArg transTm hf0, fun n => thm_4_2 (hstep n)⟩
  have h := h43 [] t T hty
  rw [transCtx_nil] at h
  cases h with
  | sub hwf _ _ => exact hwf

end Pss.Embedding
