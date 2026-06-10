import Pss.Star

/-!
# System λ* — the pure type system embedded in §4

Hutchins, *Pure Subtype Systems* (POPL 2010), §4: "System λ* is a PTS
described by Barendregt [4], which supports polymorphism, type operators,
and dependent types. It has a single sort ∗, and the typing relation ∗ : ∗."

This module is a self-contained mechanization of λ* (the λ-cube member with
axiom `∗ : ∗`, i.e. all four rule classes collapse onto the single sort):

* terms `x | ∗ | λx:t. u | Πx:t. u | t(u)` in de Bruijn style, with the same
  σ-calculus substitution library as `Pss.Syntax` (same lemma list);
* full β one-step reduction `Beta`, presented as the per-constructor
  compatible closure — the same relation as λ⊲'s E-CONG presentation, up to
  the equivalence proven in `Pss.Step.step_iff_compat`, so the translation
  theorem (4.2) can target `Step.Compat` directly;
* β-conversion `Conv` (`=β`), the reflexive-symmetric-transitive closure
  of `Beta`, built from `Pss.Star` / `Pss.Sym`;
* PTS typing `Typing` in Barendregt's presentation: axiom, start ("var"),
  weakening, product, application, abstraction, conversion.

De Bruijn conventions mirror `Pss.Syntax`: in `lam t u` / `pi t u` the
domain `t` is scoped *outside* the binder and the body `u` binds one
variable; contexts are lists with the innermost binding first.
-/

namespace Pss.LambdaStar

/-- Terms of System λ*: `var x | ∗ | λx:t. u | Πx:t. u | t(u)`. -/
inductive Tm : Type where
  | var : Nat → Tm
  | star : Tm
  | lam : Tm → Tm → Tm
  | pi : Tm → Tm → Tm
  | app : Tm → Tm → Tm
deriving Repr, DecidableEq

namespace Tm

/-! ## Renaming and substitution (σ-calculus, mirroring `Pss.Syntax`) -/

/-- Lift a renaming under one binder (`⇑ρ`). -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply a renaming to the free variables of a term. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | var x => var (ρ x)
  | star => star
  | lam t u => lam (t.rename ρ) (u.rename (liftRen ρ))
  | pi t u => pi (t.rename ρ) (u.rename (liftRen ρ))
  | app t u => app (t.rename ρ) (u.rename ρ)

/-- Shift all free variables up by `d`. -/
def shift (t : Tm) (d : Nat := 1) : Tm := t.rename (· + d)

/-- Cons a term onto a substitution. -/
def scons (s : Tm) (σ : Nat → Tm) : Nat → Tm
  | 0 => s
  | n + 1 => σ n

/-- Lift a substitution under one binder (`⇑σ`). -/
def liftSubst (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | n + 1 => (σ n).rename (· + 1)

/-- Apply a simultaneous substitution to the free variables of a term. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | var x => σ x
  | star => star
  | lam t u => lam (t.subst σ) (u.subst (liftSubst σ))
  | pi t u => pi (t.subst σ) (u.subst (liftSubst σ))
  | app t u => app (t.subst σ) (u.subst σ)

/-- `[x ↦ s]u`: substitution of `s` for the outermost bound variable. -/
def subst1 (u s : Tm) : Tm := u.subst (scons s var)

/-! ## The substitution lemma library (same list as `Pss.Syntax`) -/

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n; cases n <;> rfl

theorem liftRen_comp (ρ ρ' : Nat → Nat) :
    liftRen (ρ' ∘ ρ) = liftRen ρ' ∘ liftRen ρ := by
  funext n; cases n <;> rfl

@[simp] theorem rename_id (t : Tm) : t.rename id = t := by
  induction t with
  | var x => rfl
  | star => rfl
  | lam t u iht ihu => simp [rename, iht, ihu]
  | pi t u iht ihu => simp [rename, iht, ihu]
  | app t u iht ihu => simp [rename, iht, ihu]

theorem rename_rename (ρ ρ' : Nat → Nat) (t : Tm) :
    (t.rename ρ).rename ρ' = t.rename (ρ' ∘ ρ) := by
  induction t generalizing ρ ρ' with
  | var x => rfl
  | star => rfl
  | lam t u iht ihu => simp [rename, iht, ihu, liftRen_comp]
  | pi t u iht ihu => simp [rename, iht, ihu, liftRen_comp]
  | app t u iht ihu => simp [rename, iht, ihu]

@[simp] theorem liftSubst_var : liftSubst var = var := by
  funext n; cases n <;> rfl

@[simp] theorem subst_var (t : Tm) : t.subst var = t := by
  induction t with
  | var x => rfl
  | star => rfl
  | lam t u iht ihu => simp [subst, iht, ihu]
  | pi t u iht ihu => simp [subst, iht, ihu]
  | app t u iht ihu => simp [subst, iht, ihu]

end Tm

/-! ## β-reduction and conversion -/

/-- Full β one-step reduction `t ⟶β u`, as the per-constructor compatible
closure of the β-axiom `(λx:t. u)(s) ⟶ [x ↦ s]u`. This is the same
presentation as λ⊲'s `Pss.Step.Compat`, which `Pss.Step.step_iff_compat`
proves equal to the paper's one-hole-context E-CONG formulation — so
Theorem 4.2 maps each constructor here onto a `Step.Compat` constructor.

Only λ-applications are redexes (standard PTS β); Π-applications are stuck
as raw terms. Since `⟨Πx:t. u⟩ = ⟨λx:t. u⟩ = λx ≤ ⟨t⟩. ⟨u⟩`, a Π-redex
congruence case, had we included one, would land on λ⊲'s E-APP all the
same — the translation cannot tell the two binders apart. -/
inductive Beta : Tm → Tm → Prop where
  | beta {t u s : Tm} : Beta (.app (.lam t u) s) (u.subst1 s)
  | appL {t t' : Tm} (u : Tm) : Beta t t' → Beta (.app t u) (.app t' u)
  | appR (t : Tm) {u u' : Tm} : Beta u u' → Beta (.app t u) (.app t u')
  | lamDom {t t' : Tm} (u : Tm) : Beta t t' → Beta (.lam t u) (.lam t' u)
  | lamBody (t : Tm) {u u' : Tm} : Beta u u' → Beta (.lam t u) (.lam t u')
  | piDom {t t' : Tm} (u : Tm) : Beta t t' → Beta (.pi t u) (.pi t' u)
  | piBody (t : Tm) {u u' : Tm} : Beta u u' → Beta (.pi t u) (.pi t u')

/-- β-conversion `t =β u`: the reflexive-symmetric-transitive closure of
`Beta` (`Pss.Star` of `Pss.Sym`). -/
abbrev Conv : Tm → Tm → Prop := EqClosure Beta

namespace Conv

theorem refl {t : Tm} : Conv t t := .refl

theorem of_beta {t u : Tm} (h : Beta t u) : Conv t u := .single (.fwd h)

theorem symm {t u : Tm} (h : Conv t u) : Conv u t := by
  induction h with
  | refl => exact .refl
  | head s _ ih =>
    refine ih.trans (.single ?_)
    cases s with
    | fwd s => exact .bwd s
    | bwd s => exact .fwd s

theorem trans {s t u : Tm} (h₁ : Conv s t) (h₂ : Conv t u) : Conv s u :=
  Star.trans h₁ h₂

end Conv

/-! ## PTS typing

Barendregt's presentation for the single-sorted system: the axiom lives in
the empty context, the start rule introduces variable 0, and the explicit
weakening rule shifts a judgment under a fresh binding. `x : A ∈ Γ` with the
de Bruijn shift (as in `Pss.Ctx.Bound`) is admissible from start + weakening.
-/

/-- Typing contexts: innermost binding first; entry `i` is the type of de
Bruijn variable `i`, scoped in the tail of the list (cf. `Pss.Ctx`). -/
abbrev Ctx := List Tm

/-- `x : A ∈ Γ` (de Bruijn context lookup with shifting, mirroring
`Pss.Ctx.Bound`): the looked-up type is shifted into whole-context scope. -/
inductive Lookup : Ctx → Nat → Tm → Prop where
  | here {Γ : Ctx} {A : Tm} : Lookup (A :: Γ) 0 (A.shift 1)
  | there {Γ : Ctx} {B A : Tm} {x : Nat} :
      Lookup Γ x A → Lookup (B :: Γ) (x + 1) (A.shift 1)

/-- PTS typing `Γ ⊢ t : T` for λ* (single sort `∗`, axiom `∗ : ∗`). -/
inductive Typing : Ctx → Tm → Tm → Prop where
  /-- `⊢ ∗ : ∗` (the λ* axiom, in the empty context). -/
  | ax : Typing [] .star .star
  /-- Start rule: `Γ ⊢ A : ∗ ⟹ Γ, x:A ⊢ x : A` (de Bruijn: variable 0,
  type shifted under the new binder). -/
  | var {Γ : Ctx} {A : Tm} :
      Typing Γ A .star → Typing (A :: Γ) (.var 0) (A.shift 1)
  /-- Weakening: `Γ ⊢ t : T, Γ ⊢ A : ∗ ⟹ Γ, x:A ⊢ t : T` (shifted). -/
  | weaken {Γ : Ctx} {t T A : Tm} :
      Typing Γ t T → Typing Γ A .star →
      Typing (A :: Γ) (t.shift 1) (T.shift 1)
  /-- Product: `Γ ⊢ t : ∗, Γ, x:t ⊢ u : ∗ ⟹ Γ ⊢ Πx:t. u : ∗`. -/
  | pi {Γ : Ctx} {t u : Tm} :
      Typing Γ t .star → Typing (t :: Γ) u .star →
      Typing Γ (.pi t u) .star
  /-- Application: `Γ ⊢ f : Πx:t. u, Γ ⊢ s : t ⟹ Γ ⊢ f(s) : [x ↦ s]u`. -/
  | app {Γ : Ctx} {f s t u : Tm} :
      Typing Γ f (.pi t u) → Typing Γ s t →
      Typing Γ (.app f s) (u.subst1 s)
  /-- Abstraction: `Γ, x:t ⊢ u : U, Γ ⊢ Πx:t. U : ∗ ⟹
  Γ ⊢ λx:t. u : Πx:t. U`. -/
  | abs {Γ : Ctx} {t u U : Tm} :
      Typing (t :: Γ) u U → Typing Γ (.pi t U) .star →
      Typing Γ (.lam t u) (.pi t U)
  /-- Conversion: `Γ ⊢ t : T, T =β T', Γ ⊢ T' : ∗ ⟹ Γ ⊢ t : T'`. -/
  | conv {Γ : Ctx} {t T T' : Tm} :
      Typing Γ t T → Conv T T' → Typing Γ T' .star →
      Typing Γ t T'

end Pss.LambdaStar
