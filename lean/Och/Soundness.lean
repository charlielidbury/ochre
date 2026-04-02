import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity

/-!
# Soundness

If abstract evaluation says `e` has type `τ`, and concrete evaluation
produces value `v`, then `v ⊑ τ` (in Subtype').

## Status

**SORRY'D (1 sorry).** soundness_gen is sorry'd because WellTyped changed
from Prop-valued (with SubtypeCore) to Bool-valued (with subCheckNF).

The previous sorry-free proof is in git (commit f7c40a1), but it was
vacuously true for mu programs — WellTyped was unsatisfiable for any
program with `(e : mu_type)` ascriptions.

## Architecture

WellTyped is now **Bool-valued** and uses `subCheckNF` (the decidable
checker) in the ascription case. This makes WellTyped:
1. **Decidable** — testable via `native_decide`
2. **Satisfiable** — subCheckNF handles self-intro via equi-recursive unfolding
3. **Testable** — witness tests prove WellTyped holds for milestone programs

soundness_gen still takes SubtypeCore for h_sub and returns SubtypeCore.
The sorry is the missing "checker soundness" bridge: when WellTyped's
subCheckNF accepts a ⊑ b, what SubtypeCore properties can we derive?

## What the next agent needs to prove

The key missing lemma for the asc case:
```
  subCheckNF fuel Γ [] σ τ' = true →
    SubtypeCore v σ → SubtypeCore v τ'
```

This is "checker transitivity": if the checker says σ ⊑ τ' and we
have SubtypeCore v σ from the IH, we need SubtypeCore v τ'.

Options:
(a) Prove subCheckNF implies a semantic relation that composes with SubtypeCore
(b) Strengthen SubtypeCore with equi-recursive rules
(c) Use step-indexed logical relations
-/

open Expr

def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∃ v, γ.lookup x = some v ∧ SubtypeCore v τ

/-- Well-typedness: all ascriptions encountered during evaluation are sound.

    **Bool-valued** for decidability. Uses `subCheckNF` (the decidable subtype
    checker) instead of `SubtypeCore` in the ascription case, so that WellTyped
    is satisfiable for programs with mu types. Previously used `SubtypeCore`,
    which has no `self_intro` constructor and thus was unsatisfiable for any
    program with `(e : mu_type)` ascriptions — making the soundness theorem
    vacuously true.

    The `Γ` parameter serves double duty: it's the absEval environment AND
    the subCheckNF typing context. For lambda-bound variables, Γ maps x to
    `var x` (neutral); for mu-bound variables, Γ maps x to the mu value.
    This works because subCheckNF's inferType uses the context to look up
    variable types, and for neutral variables, it returns the binding itself. -/
def WellTyped (fuel : Nat) (Γ : Env) (e : Expr) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match e with
    | .var _ => true
    | .lam x _ body => WellTyped fuel ((x, .var x) :: Γ) body
    | .type => true
    | .asc term ty =>
        WellTyped fuel Γ term && WellTyped fuel Γ ty &&
        match absEval fuel Γ term, absEval fuel Γ ty with
        | some σ, some τ' => subCheckNF fuel Γ [] σ τ'
        | _, _ => false
    | .mu x ann body =>
        WellTyped fuel ((x, .mu x ann body) :: Γ) body
    | .app f a =>
        WellTyped fuel Γ f && WellTyped fuel Γ a &&
        match absEval fuel Γ f, absEval fuel Γ a with
        | some (.lam x _ body), some aVal => WellTyped fuel ((x, aVal) :: Γ) body
        | some (.mu _x_mu ann body_mu), some aVal =>
          -- mu-app: absEval uses annotation when both are lambdas,
          -- body otherwise. Check WellTyped of the sub-term that
          -- absEval will actually evaluate (matching absEval's logic).
          match ann, body_mu with
          | .lam y_ann _dom_ann retBody, .lam _y_body _dom_body _bodyRes =>
              -- Both lambdas: absEval uses annotation's return body.
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody
          | .lam y_ann _dom_ann retBody, _ =>
              -- Ann is lam, body isn't: absEval still uses annotation.
              -- (Wait — actually absEval's joint match gives (_, lam) priority
              --  over (lam, _) when body is lam. But here body ISN'T lam.)
              WellTyped fuel ((y_ann, aVal) :: Γ) retBody
          | _, .lam y_body _dom_body bodyRes =>
              -- Body is lam, ann isn't: absEval uses body directly.
              WellTyped fuel ((y_body, aVal) :: Γ) bodyRes
          | _, _ => true
        | _, _ => true

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (x : Name) (v : Expr) :
    EnvConsistent ((x, v) :: γ) ((x, v) :: Γ) := by
  intro y τ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeCore.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ h_lookup

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    (x : Name) {v τ : Expr} (hv : SubtypeCore v τ) :
    EnvConsistent ((x, v) :: γ) ((x, τ) :: Γ) := by
  intro y σ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y σ h_lookup

/-- **Generalized soundness.** If abstract evaluation gives type `τ`
    and concrete evaluation gives value `v`, then `SubtypeCore v τ`.

    Uses SubtypeCore (Subtype' without self_intro) for both input and output.
    The main `soundness` theorem converts via `toSubtype'`.

    **STATUS: SORRY'D.** WellTyped is now Bool-valued with `subCheckNF`
    instead of `SubtypeCore`. The proof needs "checker soundness" lemmas:
    when subCheckNF says a ⊑ b, what can we conclude about SubtypeCore?
    The key missing lemma (for the asc case):

      subCheckNF fuel ctx [] σ τ' = true →
        SubtypeCore v σ → SubtypeCore v τ'

    This is essentially: the checker's acceptance implies transitivity
    through the checked pair. Proving this requires relating subCheckNF's
    equi-recursive unfolding to SubtypeCore's structural rules, which may
    need a richer semantic relation.

    The previous sorry-free proof is preserved in git history (commit f7c40a1).
    It worked because WellTyped used SubtypeCore directly — but that made
    WellTyped unsatisfiable for mu programs (vacuous soundness). -/
theorem soundness_gen
    (fuel : Nat) (Γ : Env) (γ : Env) (e_a e_c τ v : Expr)
    (h_sub : SubtypeCore e_c e_a)
    (h_abs : absEval fuel Γ e_a = some τ)
    (h_conc : concEval fuel γ e_c = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e_a = true)
    : SubtypeCore v τ := by
  sorry

/-- **Soundness theorem.**

    If abstract evaluation gives type `τ` and concrete evaluation gives value `v`,
    then `Subtype' v τ`.

    Uses SubtypeCore internally (which avoids the self_intro case entirely),
    then converts to Subtype' via toSubtype'.

    **STATUS: SORRY'D** (depends on sorry'd soundness_gen). -/
theorem soundness
    (Γ : Env) (γ : Env) (e τ v : Expr) (fuel : Nat)
    (h_abs : absEval fuel Γ e = some τ)
    (h_conc : concEval fuel γ e = some v)
    (h_env : EnvConsistent γ Γ)
    (h_wt : WellTyped fuel Γ e = true)
    : Subtype' v τ :=
  (soundness_gen fuel Γ γ e e τ v (SubtypeCore.refl e)
    h_abs h_conc h_env h_wt).toSubtype'
