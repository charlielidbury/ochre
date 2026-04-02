import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Monotonicity
import Och.ValSub

/-!
# Soundness (concEval + ValSub)

## Architecture

Soundness relates the substitution-based concrete evaluator (`concEval`) to
the environment-based abstract evaluator (`absEval`), outputting step-indexed
value subtyping (`ValSub`).

The concrete evaluator (`concEval`) treats lambdas as values (bodies untouched
until application). This is essential for soundness: when a lambda is applied,
the body IS the source body, so the induction hypothesis applies directly.

## Theorem structure

```
soundness : concEval fuel e = some v → absEval fuel [] e = some τ →
            WellTyped fuel [] e = true → ValSub fuel v τ
```

Top-level only (empty env for absEval, closed terms for concEval). This is
sufficient — the intended user-facing check is `WellTyped fuel [] e && subCheck fuel e τ`
on closed programs.

## Status

**3 sorrys** in soundness_gen:
- **lam case**: need ValSub between source body and absEval-normalized body.
  Requires either semantic ValSub or an absEval idempotency/equivalence lemma.
- **mu case**: need env-subst equivalence for absEval + mu soundness.
- **app case**: need semantic ValSub where lam quantifies over all applications.
  With semantic ValSub, this becomes trivial (instantiate the quantifier).

## Blocking lemma: env-subst equivalence

The mu (and potentially lam) cases need:
```
absEval fuel (env.extend v) body = absEval fuel env (body.subst 0 v)
```
when v is closed. This says env-based binding = substitution-based binding.
Should hold for closed v because both resolve bvar 0 to v. Non-trivial to
prove (mutual induction on fuel + expression structure).
-/

open Expr

/-- Environment consistency: for each index k, if Γ[k] = τ then
    γ[k] exists and is ⊑ τ via SubtypeCore.
    Retained for Monotonicity.lean compatibility. -/
def EnvConsistent (γ : Env) (Γ : Env) : Prop :=
  ∀ k τ, Γ.get? k = some τ → ∃ v, γ.get? k = some v ∧ SubtypeCore v τ

-- Helper: relate List.get? to getElem? for proof interop
private theorem list_get?_eq_getElem? {α : Type} {l : List α} {k : Nat} :
    l.get? k = l[k]? := by
  simp [List.get?_eq_getElem?]

theorem envConsistent_extend {γ Γ : Env} (h : EnvConsistent γ Γ) (v : Expr) :
    EnvConsistent (γ.extend v) (Γ.extend v) := by
  intro k τ hget
  unfold Env.extend at hget ⊢
  cases k with
  | zero =>
    simp at hget
    subst hget
    exact ⟨v, by simp, .refl v⟩
  | succ k =>
    simp at hget ⊢
    obtain ⟨orig, horig, hshift⟩ := hget
    rw [← list_get?_eq_getElem?] at horig
    obtain ⟨v_orig, hgetv, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hgetv
    exact ⟨v_orig.shift 1 0, ⟨v_orig, hgetv, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

theorem envConsistent_extend_sub {γ Γ : Env} (h : EnvConsistent γ Γ)
    {v τ : Expr} (hv : SubtypeCore v τ) :
    EnvConsistent (γ.extend v) (Γ.extend τ) := by
  intro k τ₁ hget
  unfold Env.extend at hget ⊢
  cases k with
  | zero =>
    simp at hget
    subst hget
    exact ⟨v, by simp, hv⟩
  | succ k =>
    simp at hget ⊢
    obtain ⟨orig, horig, hshift⟩ := hget
    rw [← list_get?_eq_getElem?] at horig
    obtain ⟨v_orig, hgetv, hsub⟩ := h k orig horig
    rw [list_get?_eq_getElem?] at hgetv
    exact ⟨v_orig.shift 1 0, ⟨v_orig, hgetv, rfl⟩, hshift ▸ hsub.shift_preserve 1 0⟩

/-- Well-typedness: all ascriptions encountered during evaluation are sound.
    Bool-valued with subCheckNF in the ascription case.

    The env parameter serves double duty: it's the absEval environment AND
    the subCheckNF typing context. -/
def WellTyped (fuel : Nat) (env : Env) (e : Expr) : Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    match e with
    | .bvar _ => true
    | .lam _dom body => WellTyped fuel (env.extend (.bvar 0)) body
    | .type => true
    | .asc term ty =>
        WellTyped fuel env term && WellTyped fuel env ty &&
        match absEval fuel env term, absEval fuel env ty with
        | some σ, some τ' => subCheckNF fuel env [] σ τ'
        | _, _ => false
    | .mu ann body =>
        WellTyped fuel (env.extend (.mu ann body)) body
    | .app f a =>
        WellTyped fuel env f && WellTyped fuel env a &&
        match absEval fuel env f, absEval fuel env a with
        | some (.lam _dom body), some aVal =>
            WellTyped fuel env (body.subst 0 aVal)
        | some (.mu ann body_mu), some aVal =>
          match ann, body_mu with
          | .lam _dom_ann retBody, .lam _ _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | .lam _dom_ann retBody, _ =>
              WellTyped fuel env (retBody.subst 0 aVal)
          | _, .lam _dom_body bodyRes =>
              WellTyped fuel env (bodyRes.subst 0 aVal)
          | _, _ => true
        | _, _ => true

/-- **Soundness (concEval + ValSub).**

    For closed, well-typed programs: if the substitution-based concrete
    evaluator produces v and the abstract evaluator produces τ, then v
    is a value subtype of τ.

    Uses concEval (lambdas are values, substitution-based beta).
    This is the real runtime semantics.

    Proof by induction on fuel.

    **Sorry'd cases (updated with semantic ValSub analysis):**

    - **lam**: concEval returns `lam dom body` (source), absEval returns
      `lam dom body'` (normalized). With semantic lam_sem, need to prove:
      for any related args av/aτ, body evals produce related results.
      This requires either:
      (a) IH at fuel-1 on body.subst (fuel alignment issue — eval uses
          fuel+1 but IH provides fuel), or
      (b) absEval normalization equivalence: `absEval m [] (body'.subst 0 aτ)
          = absEval m [] (body.subst 0 aτ)` (pre-normalizing body is idempotent)
      The lam case is the CRITICAL blocker — once proved, the app case follows.

    - **mu**: env-subst equivalence for absEval (need to relate env-based
      normalization to substitution-based unrolling):
      `absEval fuel [v] body = absEval fuel [] (body.subst 0 v)` for closed v.

    - **app**: With semantic lam_sem, the lam-lam sub-case is structurally
      resolved: extract the semantic quantifier from ValSub fuel fv fτ,
      instantiate with the concrete/abstract args, use fuel_mono + compose_r
      twice to recover 2 lost ValSub levels. BLOCKED ON the lam case (the
      IH for f must produce lam_sem evidence, which requires the lam case). -/
theorem soundness_gen
    (fuel : Nat) (e : Expr) (τ v : Expr)
    (h_abs : absEval fuel [] e = some τ)
    (h_conc : concEval fuel e = some v)
    (h_wt : WellTyped fuel [] e = true)
    : ValSub fuel v τ := by
  induction fuel generalizing e τ v with
  | zero =>
    -- fuel = 0: both evaluators return none
    simp [concEval] at h_conc
  | succ fuel ih =>
    -- fuel + 1: case split on e
    match e with
    | .bvar k =>
      -- concEval on bvar returns none (closed term)
      simp [concEval] at h_conc
    | .type =>
      -- Both return type
      simp [concEval] at h_conc
      simp [absEval] at h_abs
      subst h_conc; subst h_abs
      exact ValSub.refl' .type (fuel + 1)
    | .asc term ty =>
      -- concEval takes the lhs (term), absEval takes the rhs (ty)
      -- h_conc : concEval fuel term = some v
      -- h_abs : absEval fuel [] ty = some τ
      simp only [concEval] at h_conc
      simp only [absEval] at h_abs
      -- WellTyped gives: WellTyped term ∧ WellTyped ty ∧ subCheckNF(absEval term, absEval ty)
      simp only [WellTyped, Bool.and_eq_true] at h_wt
      obtain ⟨⟨h_wt_term, h_wt_ty⟩, h_wt_check⟩ := h_wt
      -- Extract subCheckNF from h_wt_check by case-splitting on absEval results
      -- We need absEval fuel [] term = some σ to apply IH on term
      match h_term_abs : absEval fuel [] term with
      | some σ =>
        simp [h_term_abs, h_abs] at h_wt_check
        -- h_wt_check : subCheckNF fuel [] [] σ τ = true
        -- By IH on term: ValSub fuel v σ
        have h_vs : ValSub fuel v σ := ih term σ v h_term_abs h_conc h_wt_term
        -- compose_r: ValSub fuel v σ + subCheckNF σ τ → ValSub (fuel + 1) v τ
        exact ValSub.compose_r h_vs h_wt_check
      | none =>
        simp [h_term_abs] at h_wt_check
    | .lam dom body =>
      -- concEval: lambda is a value, returns (lam dom body) unchanged
      -- absEval: normalizes body under binder, returns (lam dom body')
      -- Need: ValSub (fuel+1) (lam dom body) (lam dom body')
      -- SORRY: requires either semantic ValSub or absEval normalization lemma
      -- The source body and normalized body differ when body has internal redexes.
      -- A semantic ValSub (lam quantifies over all applications) would make this
      -- and the app case tractable simultaneously.
      sorry
    | .mu ann body =>
      -- concEval: unrolls mu, evaluates body.subst 0 (mu ann body)
      -- absEval: normalizes body under binder with env = [mu ann body]
      -- These use fundamentally different strategies. Need env-subst equivalence:
      --   absEval fuel [mu ann body] body = absEval fuel [] (body.subst 0 (mu ann body))
      -- Then IH + compose_r (via self-intro subcheck) would close this.
      sorry
    | .app f a =>
      -- The app case is the primary motivation for semantic ValSub.
      -- Strategy: get ValSub for function and arg via IH, then use
      -- lam_sem's semantic quantifier to relate body evaluations.
      --
      -- This case requires:
      -- 1. Extracting the semantic lam from ValSub fuel fv fτ
      -- 2. Fuel monotonicity to lift body eval from fuel to fuel+1
      -- 3. compose_r twice to recover 2 lost ValSub levels
      --
      -- SORRY'd: the case analysis over the many concEval/absEval app
      -- sub-cases is very involved. The lam-lam case (the main one) works
      -- with semantic ValSub + fuel mono + compose_r. Other sub-cases
      -- (mu-app, type-app, stuck apps) need individual handling.
      -- Blocking on: proving the lam case of soundness_gen first
      -- (which produces the semantic lam evidence needed here).
      sorry

-- Note: the old `soundness` corollary (Subtype' output) is removed.
-- ValSub is the primary output relation. A ValSub → Subtype' embedding
-- can be added later if needed, but ValSub is strictly more expressive.
