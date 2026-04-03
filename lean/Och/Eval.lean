import Och.Syntax

/-!
# Och Evaluation (de Bruijn)

Two evaluators:
- **`concEval` (concrete/runtime):** Substitution-based CBV. Lambdas are
  values (bodies not evaluated until applied). `(e : τ)` takes the lhs `e`.
- **`absEval` (abstract/compile-time):** Environment-based normalizer.
  Normalizes under binders. `(e : τ)` takes the rhs `τ`.

## Environment (absEval only)

The environment is a positional list: `env[k]` is the value for bvar k.
When entering a binder, we extend with a new entry and shift existing
entries up by 1 (so their free variable indices stay correct at the new depth).

## Beta-reduction

Both evaluators use substitution for beta-reduction. When a lambda is applied,
substitute the argument for bvar 0 in the body, then re-evaluate.
-/

open Expr

/-- Evaluation environment: positional list of values.
    env[k] is the value for bvar k. -/
abbrev Env := List Expr

/-- Extend env for a new binder. Adds the new binding at position 0 and shifts
    existing entries so their free variables adjust for the new depth. -/
def Env.extend (env : Env) (v : Expr) : Env :=
  v :: env.map (Expr.shift 1 0)

/-- Abstract evaluation (typing) with normalization under binders.

    Lambda bodies are normalized under the binder (with the bound variable
    as neutral). This ensures that beta-redexes created by substitution are
    reduced, so e.g. `succ 2` has precise type `3`.

    Domains are NOT normalized, to preserve monotonicity: normalizing
    domains would make them vary with the environment, breaking the
    contravariant domain requirement of function subtyping. -/
def absEval (fuel : Nat) (env : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar k       => env.get? k
    | .lam dom body =>
      -- Normalize body under the binder: bvar 0 is treated as neutral
      match absEval fuel (env.extend (.bvar 0)) body with
      | some body' => some (.lam dom body')
      | none => none
    | .type         => some .type
    | .asc _term ty => absEval fuel env ty  -- compile-time: take the rhs
    | .mu ann body =>
      -- Evaluate body with bvar 0 bound to the mu value itself.
      -- The mu value is NOT shifted because its bvars are already at
      -- the correct depth (mu body scope = mu binder scope).
      match absEval fuel (env.extend (.mu ann body)) body with
      | some body' => some (.mu ann body')
      | none => none
    | .app f a      =>
      match absEval fuel env f, absEval fuel env a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        absEval fuel env (body.subst 0 aVal)
      | some (.mu _ann body), some aVal =>
        -- mu in function position. Strategy depends on ann AND body shape.
        -- Uses the annotation (via subst) for return type when both are lambdas.
        match _ann, body with
        | .lam _dom retBody, .lam _ _ =>
          absEval fuel env (retBody.subst 0 aVal)
        | _, .lam _dom retBody =>
          absEval fuel env (retBody.subst 0 aVal)
        | _, .type => some .type
        | _, _ => some (.app body aVal)
      | some .type, some _ => some .type
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-- Concrete evaluator. Standard call-by-value lambda calculus with substitution.

    Lambdas are values — their bodies are NOT evaluated until applied.
    Uses substitution for beta-reduction. Operates on closed terms only
    (free bvars return None). -/
def concEval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEval fuel term  -- runtime: erase ascription
    | .mu ann body =>
      -- Unroll: substitute self-reference into body, then evaluate
      concEval fuel (body.subst 0 (.mu ann body))
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        concEval fuel (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- mu in function position: unroll and retry
        match concEval fuel (.mu ann body) with
        | some (.lam _dom lamBody) => concEval fuel (lamBody.subst 0 aVal)
        | some .type => some .type
        | some fVal => some (.app fVal aVal)
        | none => none
      | some .type, some _ => some .type
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none

/-- Environment-based concrete evaluator. Structurally parallel to absEval.

    The ONLY difference from absEval is the ascription case:
    - absEval takes the rhs (type annotation) — compile-time semantics
    - concEvalE takes the lhs (term value) — runtime semantics

    Used as a proof auxiliary for soundness_gen_sr. The env-based structure
    makes the induction hypothesis apply directly (both evaluators normalize
    under binders, so outputs are SoundRel by IH). -/
def concEvalE (fuel : Nat) (env : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar k       => env.get? k
    | .lam dom body =>
      match concEvalE fuel (env.extend (.bvar 0)) body with
      | some body' => some (.lam dom body')
      | none => none
    | .type         => some .type
    | .asc term _   => concEvalE fuel env term  -- runtime: take the lhs
    | .mu ann body =>
      match concEvalE fuel (env.extend (.mu ann body)) body with
      | some body' => some (.mu ann body')
      | none => none
    | .app f a      =>
      match concEvalE fuel env f, concEvalE fuel env a with
      | some (.lam _dom body), some aVal =>
        concEvalE fuel env (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- Match on ann AND body, mirroring absEval's mu-app case.
        -- When both are lam, use annotation's return type (prevents divergence
        -- for recursive functions, matching absEval's behavior).
        match ann, body with
        | .lam _dom retBody, .lam _ _ =>
          concEvalE fuel env (retBody.subst 0 aVal)
        | _, .lam _dom lamBody =>
          concEvalE fuel env (lamBody.subst 0 aVal)
        | _, .type => some .type
        | _, _ => some (.app body aVal)
      | some .type, some _ => some .type
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-! ## Asc-free expressions and evaluator equivalence

Both evaluators strip ascription from their outputs. On asc-free inputs,
concEvalE and absEval are identical (they differ ONLY at the asc case).
This is the key insight for the soundness_gen app case: after beta-reduction,
both sides effectively use the same evaluator. -/

/-- An expression is asc-free if it contains no `.asc` constructor. -/
def Expr.ascFree : Expr → Prop
  | .bvar _ => True
  | .lam dom body => dom.ascFree ∧ body.ascFree
  | .app f a => f.ascFree ∧ a.ascFree
  | .asc _ _ => False
  | .type => True
  | .mu ann body => ann.ascFree ∧ body.ascFree

/-- Bool-valued version for native_decide. -/
def Expr.ascFreeB : Expr → Bool
  | .bvar _ => true
  | .lam dom body => dom.ascFreeB && body.ascFreeB
  | .app f a => f.ascFreeB && a.ascFreeB
  | .asc _ _ => false
  | .type => true
  | .mu ann body => ann.ascFreeB && body.ascFreeB

theorem Expr.ascFree_iff_ascFreeB (e : Expr) : e.ascFree ↔ e.ascFreeB = true := by
  induction e with
  | bvar _ => simp [ascFree, ascFreeB]
  | type => simp [ascFree, ascFreeB]
  | asc _ _ => simp [ascFree, ascFreeB]
  | lam dom body ih_d ih_b => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_d, ih_b]
  | app f a ih_f ih_a => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_f, ih_a]
  | mu ann body ih_a ih_b => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_a, ih_b]

/-- Shifting preserves asc-free. -/
theorem Expr.ascFree_shift {e : Expr} {d c : Nat}
    (he : e.ascFree) : (e.shift d c).ascFree := by
  induction e generalizing c with
  | bvar _ => simp [shift]; split <;> simp [ascFree]
  | type => simp [shift, ascFree]
  | asc _ _ => exact absurd he (by simp [ascFree])
  | lam _ _ ih_d ih_b =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_d he.1, ih_b he.2⟩
  | app _ _ ih_f ih_a =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_f he.1, ih_a he.2⟩
  | mu _ _ ih_a ih_b =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_a he.1, ih_b he.2⟩

/-- Substitution preserves asc-free. -/
theorem Expr.ascFree_subst {e : Expr} {j : Nat} {s : Expr}
    (he : e.ascFree) (hs : s.ascFree) : (e.subst j s).ascFree := by
  induction e generalizing j s with
  | bvar k =>
    simp [subst]
    split
    · exact hs  -- k == j: result is s
    · split
      · simp [ascFree]  -- k > j: bvar (k-1)
      · simp [ascFree]  -- k < j: bvar k
  | type => simp [subst, ascFree]
  | asc _ _ => exact absurd he (by simp [ascFree])
  | lam dom body ih_d ih_b =>
    simp [ascFree] at he; obtain ⟨hd, hb⟩ := he
    simp [subst, ascFree]
    exact ⟨ih_d hd hs, ih_b hb (ascFree_shift hs)⟩
  | app f a ih_f ih_a =>
    simp [ascFree] at he; obtain ⟨hf, ha⟩ := he
    simp [subst, ascFree]; exact ⟨ih_f hf hs, ih_a ha hs⟩
  | mu ann body ih_a ih_b =>
    simp [ascFree] at he; obtain ⟨ha, hb⟩ := he
    simp [subst, ascFree]
    exact ⟨ih_a ha hs, ih_b hb (ascFree_shift hs)⟩

/-- Env.extend with an asc-free value preserves the env asc-free invariant. -/
theorem Env.extend_ascFree {env : Env} {v : Expr}
    (henv : ∀ k e, env.get? k = some e → e.ascFree)
    (hv : v.ascFree)
    : ∀ k e, (Env.extend env v).get? k = some e → e.ascFree := by
  intro k e hk
  simp [Env.extend] at hk
  cases k with
  | zero =>
    simp at hk; subst hk; exact hv
  | succ j =>
    simp [List.get?] at hk
    obtain ⟨a, ha_lookup, ha_shift⟩ := hk
    subst ha_shift
    have := henv j a
    exact Expr.ascFree_shift (this (by rwa [List.get?_eq_getElem?]))

/-- On asc-free inputs, concEvalE and absEval produce the same result.
    They differ ONLY at the asc case: concEvalE takes the lhs, absEval
    takes the rhs. If there is no asc, they are identical. -/
theorem ascFree_eval_equiv {fuel : Nat} {env : Env} {e : Expr}
    (he : e.ascFree)
    (henv : ∀ k v, env.get? k = some v → v.ascFree)
    : concEvalE fuel env e = absEval fuel env e := by
  induction fuel generalizing env e with
  | zero => simp [concEvalE, absEval]
  | succ k ih =>
    cases e with
    | bvar j => simp [concEvalE, absEval]
    | type => simp [concEvalE, absEval]
    | asc _ _ => exact absurd he (by simp [Expr.ascFree])
    | lam dom body =>
      simp [Expr.ascFree] at he; obtain ⟨_, hb⟩ := he
      simp only [concEvalE, absEval]
      have hbvar : Expr.ascFree (.bvar 0) := trivial
      rw [ih hb (Env.extend_ascFree henv hbvar)]
    | mu ann body =>
      simp [Expr.ascFree] at he; obtain ⟨ha, hb⟩ := he
      simp only [concEvalE, absEval]
      have hmu : Expr.ascFree (.mu ann body) := ⟨ha, hb⟩
      rw [ih hb (Env.extend_ascFree henv hmu)]
    | app f a =>
      simp [Expr.ascFree] at he; obtain ⟨hf, ha⟩ := he
      simp only [concEvalE, absEval]
      rw [ih hf henv, ih ha henv]
      -- After rewrite, the match on absEval results still has concEvalE in
      -- sub-branches (beta-reduction, mu-app). These need the asc-free property
      -- of the intermediate expressions to continue the equivalence.
      sorry

/-- Evaluator outputs are asc-free: neither concEvalE nor absEval produces
    asc nodes in their output (both evaluate asc away). -/
theorem concEvalE_ascFree {fuel : Nat} {env : Env} {e v : Expr}
    (h : concEvalE fuel env e = some v)
    (henv : ∀ k e, env.get? k = some e → e.ascFree)
    : v.ascFree := by
  sorry  -- by induction on fuel, cases on e; asc case forwards

theorem absEval_ascFree {fuel : Nat} {env : Env} {e v : Expr}
    (h : absEval fuel env e = some v)
    (henv : ∀ k e, env.get? k = some e → e.ascFree)
    : v.ascFree := by
  sorry  -- identical structure to concEvalE_ascFree

/-! ## Fuel monotonicity

If evaluation succeeds with n fuel, it also succeeds with n+1 fuel to the
same result. This is because extra fuel is unused — the evaluation already
terminated within n steps. -/

theorem concEval_fuel_mono {n : Nat} {e v : Expr}
    (h : concEval n e = some v) : concEval (n + 1) e = some v := by
  induction n generalizing e v with
  | zero => simp [concEval] at h
  | succ k ih =>
    -- h : concEval (k+1) e = some v
    -- goal : concEval (k+2) e = some v
    match e with
    | .bvar _ => simp [concEval] at h
    | .lam dom body =>
      simp [concEval] at h ⊢; exact h
    | .type =>
      simp [concEval] at h ⊢; exact h
    | .asc term _ =>
      simp only [concEval] at h ⊢; exact ih h
    | .mu ann body =>
      simp only [concEval] at h ⊢; exact ih h
    | .app f a =>
      -- Both sides unfold to a match on concEval k/k+1 of f and a.
      -- We show they align by lifting each sub-result via ih.
      unfold concEval at h ⊢
      -- Split on concEval k f
      match hf : concEval k f with
      | none => simp [hf] at h
      | some fv =>
        have hf' := ih hf
        -- Split on concEval k a
        match ha : concEval k a with
        | none => simp [hf, ha] at h
        | some av =>
          have ha' := ih ha
          simp only [hf, ha] at h
          simp only [hf', ha']
          -- Now match on fv
          match fv with
          | .lam _dom body => exact ih h
          | .mu ann body_mu =>
            match hmu : concEval k (.mu ann body_mu) with
            | none => simp [hmu] at h
            | some muv =>
              have hmu' := ih hmu
              simp only [hmu] at h
              simp only [hmu']
              match muv with
              | .lam _dom lamBody => exact ih h
              | .type => exact h
              | .bvar _ | .app _ _ | .asc _ _ | .mu _ _ => exact h
          | .type => exact h
          | .bvar _ | .app _ _ | .asc _ _ => exact h

theorem absEval_fuel_mono {n : Nat} {env : Env} {e v : Expr}
    (h : absEval n env e = some v) : absEval (n + 1) env e = some v := by
  induction n generalizing env e v with
  | zero => simp [absEval] at h
  | succ k ih =>
    match e with
    | .bvar _ => simp [absEval] at h ⊢; exact h
    | .type => simp [absEval] at h ⊢; exact h
    | .asc _term ty => simp only [absEval] at h ⊢; exact ih h
    | .lam dom body =>
      unfold absEval at h ⊢
      match hb : absEval k (Env.extend env (.bvar 0)) body with
      | none => simp [hb] at h
      | some body' =>
        simp only [hb] at h
        simp only [ih hb]
        exact h
    | .mu ann body =>
      unfold absEval at h ⊢
      match hb : absEval k (Env.extend env (.mu ann body)) body with
      | none => simp [hb] at h
      | some body' =>
        simp only [hb] at h
        simp only [ih hb]
        exact h
    | .app f a =>
      unfold absEval at h ⊢
      match hf : absEval k env f with
      | none => simp [hf] at h
      | some fv =>
        have hf' := ih hf
        match ha : absEval k env a with
        | none => simp [hf, ha] at h
        | some av =>
          have ha' := ih ha
          simp only [hf, ha] at h
          simp only [hf', ha']
          match fv with
          | .lam _dom body => exact ih h
          | .mu _ann body_mu =>
            -- Nested match on _ann × body_mu mirrors absEval's mu-app case.
            -- Each sub-case is either a recursive absEval call (ih) or direct.
            cases _ann <;> cases body_mu <;> (first | exact ih h | exact h)
          | .type => exact h
          | .bvar _ => exact h
          | .app _ _ => exact h
          | .asc _ _ => exact h
