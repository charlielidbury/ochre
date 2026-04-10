import Och.Simple.Syntax
import Och.Simple.Eval
import Och.Simple.Bidir

/-!
# Check-Primary Architecture (Phase 1)

## Architecture shift

Previously, soundness of Simple Och was formulated against the inductive
`Sub` relation:

    Sub Γ e τ → Compatible γ Γ → eval of closingSubst γ e and closingSubst γ τ
                                → Sub [] v_e v_τ

That is, the *declarative* `Sub` was the primary judgment, and the
algorithmic checker was meant to be shown sound against it.

In this file we flip the roles: **the bidirectional checker in
`Och.Simple.Bidir` is the type system**. The statement of soundness
becomes "check is preserved under evaluation":

    check Γ e τ = true → Compatible γ Γ →
      eval (closingSubst γ e) = some v_e →
      eval (closingSubst γ τ) = some v_τ →
      check [] v_e v_τ = true

### Why move away from the inductive `Sub`?

The inductive `Sub` can express Refl, Top, Var, Lam, App, Asc-L, Asc-R, Mu
(8 rules) but **cannot** directly express self-type introduction (the muR
rule we want): any attempt to add it produces a rule whose left and right
premises are not structurally smaller, breaking transitivity. We explored
this in the `research-*` branches.

Cycle detection in the *checker* handles this cleanly: the `seen` set plays
the role of a coinductive hypothesis. So we adopt the checker as primary.

### Roadmap

This is **Phase 1** of a multi-phase migration:

* **Phase 1 (this file)**: introduce `Compatible` on top of `check`, state
  the preservation-style soundness theorem, and discharge the trivial
  [Refl] and [Top] cases. Everything else is `sorry`ed.
* **Phase 2**: more base rules (Var, Lam, Asc-L, Asc-R).
* **Phase 3**: App (requires inversion on `check` for lambdas).
* **Phase 4**: Mu-L, and the key muR / cycle-detection case using a
  coinductive argument on the `seen` set.
* Eventually: delete the legacy inductive `Sub`, `Properties`, and
  `Soundness` files.

### Constraints during migration

* The inductive `Sub` in `Subtype.lean` stays at exactly 8 rules, zero
  sorrys. It remains the legacy formalization until we're confident in the
  check-primary approach.
* Any `sorry` in this file is deliberate and documented — all other
  modules must continue to build with zero sorrys.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Closing substitution (copied from Soundness.lean)
--
-- We intentionally do NOT import Soundness.lean to keep CheckPrimary
-- independent of the legacy Sub-based machinery.
-- ============================================================

/-- Apply a list of closed values as a closing substitution.
    `γ = [v₀, v₁, …]` replaces `var 0 ↦ v₀`, `var 1 ↦ v₁`, …. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- Compatible (γ ⊨ Γ) — check-based definition
-- ============================================================

/-- A closing substitution `γ` is *compatible* with context `Γ` when each
    value in `γ` check-types against its corresponding type in `Γ` at the
    **empty** context.

    NOTE: we check at `[]`, not at the remaining `Γ`, because by the time
    we consult a binding the earlier bindings have already been substituted
    away. Values therefore must already be closed (which the check at `[]`
    enforces structurally). -/
inductive Compatible : List Expr → Ctx → Prop where
  | nil : Compatible [] []
  | cons {v T : Expr} {γ : List Expr} {Γ : Ctx} :
      Compatible γ Γ →
      (∃ fuel, check fuel [] v T = true) →
      Compatible (v :: γ) (T :: Γ)

-- ============================================================
-- The new soundness theorem
-- ============================================================

/-- **Check-preservation soundness** (statement only, full proof deferred).

    If `Γ ⊢ e ⊑ τ` in the checker and `γ` is compatible with `Γ`, then
    after closing both `e` and `τ` and evaluating them, the resulting
    closed values still check-subtype at the empty context. -/
theorem soundness
    {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    {fuel_check : Nat}
    (hcheck : check fuel_check Γ e τ = true)
    (hcompat : Compatible γ Γ)
    {fuel : Nat} {v_e v_τ : Expr}
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ τ) = some v_τ) :
    ∃ fuel', check fuel' [] v_e v_τ = true := by
  -- The full proof is deferred to subsequent phases. We discharge only
  -- the very first cases below (Refl and Top) as a sanity check.
  sorry

-- ============================================================
-- Easy cases: direct-style lemmas
--
-- These are stand-alone lemmas that do NOT go through the full soundness
-- statement above; they are intended to show that the *computational*
-- architecture can dispatch the simple cases with zero effort, as
-- evidence that the approach is viable.
-- ============================================================

-- ============================================================
-- Joint fuel monotonicity: synth, check, subCheck, subCheckApp, subCheckMuL
--
-- These five functions are defined by mutual well-founded recursion on
-- `fuel`. Proving monotonicity of any one of them individually does not
-- work, because `subCheckApp`/`subCheckMuL` recurse into `subCheck` and
-- `synth` at the SAME fuel (they don't decrement); that is the reason the
-- monotonicity proof is packaged as a single joint statement.
--
-- `mono_step n` says: each of the five functions takes any successful
-- answer at fuel `n` to the same answer at fuel `n + 1`. The proof is by
-- induction on `n`. Within the successor case we must order the sub-
-- lemmas so that later ones can invoke earlier ones at the **current**
-- level (`n + 1 → n + 2`), not just the IH (`n → n + 1`):
--
--   1. `subCheck`  — needs only IH.
--   2. `synth`     — needs only IH.
--   3. `check`     — trivially from IH's `subCheck`.
--   4. `subCheckApp` — calls `synth`/`subCheck` at the same fuel, so
--                     needs the just-proved `synth`/`subCheck` mono at
--                     level n + 1 → n + 2 (not IH).
--   5. `subCheckMuL` — calls `subCheck` at the same fuel, so likewise
--                     needs the just-proved level n + 1 → n + 2 mono.
-- ============================================================

/-- Joint monotonicity step: all five mutually-recursive functions turn a
    success at fuel `n` into the same success at fuel `n + 1`. -/
private structure MonoState (n : Nat) : Prop where
  sub : ∀ seen Γ a b, subCheck n seen Γ a b = true → subCheck (n+1) seen Γ a b = true
  syn : ∀ Γ e t, synth n Γ e = some t → synth (n+1) Γ e = some t
  chk : ∀ Γ e τ, check n Γ e τ = true → check (n+1) Γ e τ = true
  app : ∀ seen Γ f a b, subCheckApp n seen Γ f a b = true → subCheckApp (n+1) seen Γ f a b = true
  muL : ∀ seen Γ A bd b, subCheckMuL n seen Γ A bd b = true → subCheckMuL (n+1) seen Γ A bd b = true

/-- At fuel 0, `subCheckApp` always returns `false` because every branch
    eventually calls `subCheck 0 = false` or looks at `synth 0 = none`. -/
private theorem subCheckApp_zero_false (seen : List (Expr × Expr)) (Γ : Ctx) (f arg b : Expr) :
    subCheckApp 0 seen Γ f arg b = false := by
  unfold subCheckApp subCheckApp_tryApp subCheckApp_tryBeta
  cases f with
  | lam _ _ => simp [subCheck, synth]
  | mu A bodyF => simp only [synth]; split <;> simp [subCheck]
  | _ => simp [synth]

private theorem mono_step : ∀ n, MonoState n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intros seen Γ a b h
      unfold subCheck at h; exact absurd h (by simp)
    · intros Γ e t h
      unfold synth at h; exact absurd h (by simp)
    · intros Γ e τ h
      unfold check at h; exact absurd h (by simp)
    · intros seen Γ f arg b h
      rw [subCheckApp_zero_false] at h
      exact absurd h (by simp)
    · -- At fuel 0, the only way subCheckMuL succeeds is via the
      -- cycle-detection `seenMember` branch (the three recursive subCheck
      -- calls all fail at fuel 0). That branch is always accessible, so
      -- it also succeeds at fuel 1.
      intros seen Γ A body b h
      unfold subCheckMuL at h ⊢
      simp only [subCheck, Bool.and_false, Bool.false_or, Bool.or_false] at h
      cases b with
      | mu A' body' =>
        by_cases hs : seenMember seen (.mu A body) (.mu A' body') = true
        · simp [hs]
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      | _ => simp at h
  | succ n ih =>
    obtain ⟨P, Q, R, S, T⟩ := ih
    -- Step 1: subCheck (n+1) → subCheck (n+2). Uses only IH.
    have new_sub : ∀ seen Γ a b,
        subCheck (n+1) seen Γ a b = true → subCheck (n+2) seen Γ a b = true := by
      intros seen Γ a b h
      unfold subCheck at h ⊢
      by_cases hab : a = b
      · simp [hab]
      simp only [hab, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      split at h
      · exact h
      · rw [Bool.and_eq_true] at h ⊢
        exact ⟨P _ _ _ _ h.1, P _ _ _ _ h.2⟩
      · split at h
        · exact T _ _ _ _ _ h
        · split at h
          · rename_i hs; simp [hs]
          · rename_i hs; simp only [hs, Bool.false_eq_true, ↓reduceIte]
            rw [Bool.and_eq_true] at h ⊢
            exact ⟨P _ _ _ _ h.1, P _ _ _ _ h.2⟩
      · split at h
        · split at h
          · exact P _ _ _ _ h
          · exact absurd h (by simp)
        · split at h
          · rw [Bool.and_eq_true] at h ⊢
            exact ⟨P _ _ _ _ h.1, P _ _ _ _ h.2⟩
          · exact absurd h (by simp)
        · exact S _ _ _ _ _ h
        · rw [Bool.and_eq_true] at h ⊢
          exact ⟨P _ _ _ _ h.1, P _ _ _ _ h.2⟩
        · exact T _ _ _ _ _ h
        · exact absurd h (by simp)
    -- Step 2: synth (n+1) → synth (n+2). Uses only IH.
    have new_syn : ∀ Γ e t,
        synth (n+1) Γ e = some t → synth (n+2) Γ e = some t := by
      intros Γ e t h
      unfold synth at h ⊢
      cases e with
      | top => exact h
      | var x => exact h
      | lam D body =>
        simp only at h ⊢
        cases h1 : synth n Γ D with
        | none => simp [h1] at h
        | some _ =>
          cases h2 : synth n (D :: Γ) body with
          | none => simp [h1, h2] at h
          | some _ =>
            rw [Q _ _ _ h1, Q _ _ _ h2]
            simp [h1, h2] at h
            simp; exact h
      | asc ee τ =>
        simp only at h ⊢
        cases h1 : synth n Γ τ with
        | none => simp [h1] at h
        | some _ =>
          rw [Q _ _ _ h1]
          simp [h1] at h
          by_cases hc : check n Γ ee τ = true
          · rw [R _ _ _ hc]; simp; simp [hc] at h; exact h
          · simp [hc] at h
      | app f a =>
        simp only at h ⊢
        cases h1 : synth n Γ f with
        | none => simp [h1] at h
        | some val =>
          rw [Q _ _ _ h1]
          simp [h1] at h
          cases val with
          | lam D Rs =>
            simp only at h ⊢
            by_cases hc : check n Γ a D = true
            · rw [R _ _ _ hc]; simp; simp [hc] at h; exact h
            · simp [hc] at h
          | _ => exact absurd h (by simp)
      | mu A body =>
        simp only at h ⊢
        cases h1 : synth n Γ A with
        | none => simp [h1] at h
        | some _ =>
          rw [Q _ _ _ h1]
          simp [h1] at h
          by_cases hc : check n (A :: Γ) body (A.shift 0 1) = true
          · rw [R _ _ _ hc]; simp; simp [hc] at h; exact h
          · simp [hc] at h
    -- Step 3: check is trivially subCheck one fuel below.
    have new_chk : ∀ Γ e τ,
        check (n+1) Γ e τ = true → check (n+2) Γ e τ = true := by
      intros Γ e τ h
      unfold check at h ⊢
      exact P _ _ _ _ h
    -- Step 4: subCheckApp uses new_syn/new_sub (SAME level).
    have new_app : ∀ seen Γ f a b,
        subCheckApp (n+1) seen Γ f a b = true →
        subCheckApp (n+2) seen Γ f a b = true := by
      intros seen Γ f arg b h
      unfold subCheckApp at h ⊢
      rw [Bool.or_eq_true] at h ⊢
      cases h with
      | inl h =>
        left
        unfold subCheckApp_tryApp at h ⊢
        cases h1 : synth (n+1) Γ f with
        | none => rw [h1] at h; exact absurd h (by simp)
        | some val =>
          rw [h1] at h; rw [new_syn _ _ _ h1]
          cases val with
          | lam D Rs =>
            simp only at h ⊢
            rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
            exact ⟨⟨new_sub _ _ _ _ h.1.1, new_sub _ _ _ _ h.1.2⟩, new_sub _ _ _ _ h.2⟩
          | _ => exact absurd h (by simp)
      | inr h =>
        right
        unfold subCheckApp_tryBeta at h ⊢
        cases f with
        | lam _ body => exact new_sub _ _ _ _ h
        | mu A bodyF =>
          simp only at h ⊢
          split at h
          · exact new_sub _ _ _ _ h
          · exact new_sub _ _ _ _ h
        | _ => exact absurd h (by simp)
    -- Step 5: subCheckMuL uses new_sub (SAME level).
    have new_muL : ∀ seen Γ A bd b,
        subCheckMuL (n+1) seen Γ A bd b = true →
        subCheckMuL (n+2) seen Γ A bd b = true := by
      intros seen Γ A body b h
      unfold subCheckMuL at h ⊢
      rw [Bool.or_eq_true, Bool.or_eq_true] at h ⊢
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          left; left
          rw [Bool.and_eq_true] at h ⊢
          exact ⟨new_sub _ _ _ _ h.1, new_sub _ _ _ _ h.2⟩
        | inr h =>
          left; right
          exact new_sub _ _ _ _ h
      | inr h =>
        right
        split at h
        · rename_i A' body'
          by_cases hs : seenMember seen (.mu A body) (.mu A' body') = true
          · simp [hs]
          · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
            simp only [hs, Bool.false_eq_true, ↓reduceIte]
            rw [Bool.and_eq_true] at h ⊢
            exact ⟨new_sub _ _ _ _ h.1, new_sub _ _ _ _ h.2⟩
        · exact absurd h (by simp)
    exact ⟨new_sub, new_syn, new_chk, new_app, new_muL⟩

/-- Fuel monotonicity of `subCheck`. Giving the checker more fuel never
    turns a `true` into a `false`. Proved by iterating the single-step
    monotonicity `mono_step`. -/
theorem subCheck_mono_fuel
    (fuel fuel' : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr)
    (h : subCheck fuel seen Γ a b = true) (hle : fuel ≤ fuel') :
    subCheck fuel' seen Γ a b = true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (mono_step _).sub _ _ _ _ ih

/-- Fuel monotonicity of `check`. -/
theorem check_mono_fuel
    (fuel fuel' : Nat) (Γ : Ctx) (e τ : Expr)
    (h : check fuel Γ e τ = true) (hle : fuel ≤ fuel') :
    check fuel' Γ e τ = true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (mono_step _).chk _ _ _ ih

/-- Fuel monotonicity of `synth`. -/
theorem synth_mono_fuel
    (fuel fuel' : Nat) (Γ : Ctx) (e t : Expr)
    (h : synth fuel Γ e = some t) (hle : fuel ≤ fuel') :
    synth fuel' Γ e = some t := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (mono_step _).syn _ _ _ ih

-- ============================================================
-- Substitution lemma for the checker
--
-- The algorithmic analog of `Sub.subst_lemma` from Properties.lean.
-- It says: substituting a value that check-types against the binder
-- preserves checker acceptance.
-- ============================================================

/-- Substitute into each entry of a context prefix. Mirrors the
    `substCtx` helper in Properties.lean so this file does not depend
    on the Sub-based machinery. -/
def checkSubstCtx : Ctx → Expr → Ctx
  | [], _ => []
  | A :: rest, v => (A.subst rest.length (v.shift 0 rest.length)) :: checkSubstCtx rest v

/-- Substitute into each pair of a seen set. Needed because the seen
    set travels through `subCheck` recursions that happen inside
    contexts whose bindings are being substituted away. -/
def checkSubstSeen (d : Nat) (v : Expr) :
    List (Expr × Expr) → List (Expr × Expr)
  | [] => []
  | (a, b) :: rest =>
    (a.subst d v, b.subst d v) :: checkSubstSeen d v rest

/-- **Substitution lemma for `check`** (Phase 2 / Step 2 deliverable).

    If `a ⊑ b` in context `(T :: Γ)` and `v ⊑ T` in context `Γ`, then
    after substituting `v` for the bound variable `0`, we still have
    `a[0:=v] ⊑ b[0:=v]` in context `Γ`. The fuel of the conclusion is
    existentially quantified — use `check_mono_fuel` to bump it as
    needed when composing this lemma.

    **Status: deferred to Phase 3.** The proof is genuinely subtle
    because:

    1. `subCheck` carries a `seen` set for cycle detection. Under
       substitution, every pair in `seen` must be pushed through the
       same substitution, which means the generalized lemma has the
       shape

           subCheck f seen (Δ ++ T :: Γ) a b = true →
           check fv Γ v T = true →
           ∃ f', subCheck f' (checkSubstSeen |Δ| v' seen)
                              (checkSubstCtx Δ v ++ Γ)
                              (a.subst |Δ| v') (b.subst |Δ| v')
             = true
         where `v' = v.shift 0 |Δ|`.

       One then has to show that cycle-detection `seenMember` commutes
       with substitution (true, because substitution is injective up
       to `v`'s free variables).

    2. The `app` branch of `subCheck` calls `subCheckApp`, which in
       turn calls `synth` on `f`. That forces a *synth substitution
       lemma* — a separate mutual-recursive companion statement — so
       that synth results on `a` at context `(T :: Γ)` translate into
       synth results on `a.subst 0 v` at context `Γ`.

    3. The `mu` branch of `subCheck` calls `subCheckMuL`, which tries
       three strategies (annotation, unfolding, self-type/muR). The
       muR cycle-detection branch is where the `seen` set grows, so
       careful bookkeeping is required.

    The clean approach is to mirror `Sub.subst_gen_aux` from
    Properties.lean in its generalized form with a `Δ` prefix, and
    simultaneously prove a corresponding `synth_subst_gen` for the
    synth side. Each of the nine `subCheck` case splits and the five
    `synth` cases must be handled, plus the helpers
    `subCheckApp_tryApp`, `subCheckApp_tryBeta`, `subCheckMuL`. We
    estimate roughly 400–600 lines of tactic proof mirroring the
    structure of `Properties.lean`'s substitution section. -/
theorem check_subst_lemma (Γ : Ctx) (T a b v : Expr)
    (hab : ∃ fab, check fab (T :: Γ) a b = true)
    (hv : ∃ fv, check fv Γ v T = true)
    : ∃ f, check f Γ (a.subst 0 v) (b.subst 0 v) = true := by
  sorry

/-- **Easy case: [Refl]-like.** `check` at fuel 2 accepts any reflexive
    pair in the empty context.

    The [Refl] branch at the top of `subCheck` fires because the `if decide
    (a = b)` guard is `true`, short-circuiting all subsequent matches. -/
theorem check_refl (v : Expr) : check 2 [] v v = true := by
  unfold check
  unfold subCheck
  simp

/-- **Easy case: [Top]-like.** `check` at fuel 2 accepts any LHS against
    `⊤` in the empty context.

    Either the [Refl] branch fires (if `v = .top`) or the outer `match b`
    on `.top` fires its first arm. Both return `true`. -/
theorem check_top (v : Expr) : check 2 [] v .top = true := by
  unfold check
  unfold subCheck
  by_cases h : v = .top
  · subst h; simp
  · simp [h]

end Och.Simple
