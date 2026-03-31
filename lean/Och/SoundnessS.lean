import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness

/-!
# Soundness of concEvalS (substitution-based evaluator)

The existing soundness proof (Soundness.lean) relates `concEval` (env-based,
normalizing under binders) to `absEval`. But `concEval` breaks on recursive
fix with Church-encoded branching (both branches evaluated eagerly).

`concEvalS` (substitution-based, lambdas as values) has correct CBV semantics
but uses a fundamentally different mechanism than `absEval`:
- `concEvalS`: substitution at beta-reduction, lambdas returned as-is
- `absEval`: env extension at beta-reduction, lambdas normalized under binders

This structural mismatch means the existing inductive proof doesn't apply.
Instead, we use a **logical relation** (LR): two values are related if, when
applied to related arguments, they produce related results. This sidesteps
the syntactic mismatch between un-normalized (concEvalS) and normalized
(absEval) lambda bodies.

## Proof architecture

The main theorem (`fundamental`) is proved by induction on fuel. The key
insight is that the app case applies the IH directly to the body evaluation
(fuel decreases from k+1 to k), yielding LR n at the SAME level — no need
to go through the lambda clause of LR (which would lose a level).

The lambda clause of LR is used only by EXTERNAL consumers of soundnessS
who want to apply a sound function value to new arguments.

### Key lemma needed: `absEval_normalize_stable`

absEval normalizes lambda bodies under neutral binders, then re-evaluates
with concrete bindings. The fundamental theorem's IH applies to the ORIGINAL
body, but absEval evaluates the NORMALIZED body. This lemma bridges the gap:

  absEval k ((x, a) :: Γ) (absEval k' ((x, var x) :: Γ) body)
  = absEval k ((x, a) :: Γ) body

Intuitively: normalization with x as neutral is a "pre-computation" that
doesn't change the result when x is later given a concrete value.

### Infrastructure needed: `substAll_var`

The var case needs: `substAll (var x) σ = v` when `σ.lookup x = some v` and
all values in σ are closed. This requires a "closed expression" predicate
and the lemma that closed values are fixed points of `subst`.

## Status

- [x] LR definition
- [x] EnvLR definition
- [x] substAll definition and distribution lemmas (app, asc, type, fix)
- [x] Fundamental theorem stated with proof outline
- [x] Top-level soundnessS corollary (proved from fundamental)
- [x] Type case of fundamental proved
- [ ] substAll_var lemma (needs "closed value" infrastructure, ~40 lines)
- [ ] absEval_normalize_stable (the key bridge lemma, ~80-100 lines)
- [ ] Var, lam, asc, fix, app cases of fundamental (~150 lines total)

## Recommended order for completing the proof

1. Define `IsClosed : Expr → Prop` (no free variables)
2. Prove `IsClosed v → v.subst x s = v`
3. Prove `substAll_var`: `substAll (var x) σ = σ.lookup x` for closed σ
4. Prove `absEval_normalize_stable` by induction on body expression
5. Complete the var case using substAll_var + EnvLR
6. Complete the lam case: construct the extensional property using the IH
7. Complete the app case: unfold both evaluators, apply IH at reduced fuel,
   use absEval_normalize_stable to bridge normalized vs original body
8. Complete the asc case: IH on lhs + WellTyped gives the subtyping chain
9. Complete the fix case: similar to existing fix soundness
-/

open Expr

-- ============================================================
-- Substitution helpers
-- ============================================================

/-- Apply a list of substitutions left-to-right.
    Each entry (x, v) substitutes v for x in the accumulated result.
    Assumes all values v are closed (no free variables). -/
def substAll (e : Expr) (σ : List (Name × Expr)) : Expr :=
  σ.foldl (fun acc ⟨x, v⟩ => acc.subst x v) e

/-- substAll distributes over application. -/
theorem substAll_app (f a : Expr) (σ : List (Name × Expr)) :
    substAll (.app f a) σ = .app (substAll f σ) (substAll a σ) := by
  induction σ generalizing f a with
  | nil => rfl
  | cons ⟨x, v⟩ rest ih =>
    simp only [substAll, List.foldl]
    exact ih (f.subst x v) (a.subst x v)

/-- substAll distributes over ascription. -/
theorem substAll_asc (term ty : Expr) (σ : List (Name × Expr)) :
    substAll (.asc term ty) σ = .asc (substAll term σ) (substAll ty σ) := by
  induction σ generalizing term ty with
  | nil => rfl
  | cons ⟨x, v⟩ rest ih =>
    simp only [substAll, List.foldl]
    exact ih (term.subst x v) (ty.subst x v)

/-- substAll of .type is .type. -/
theorem substAll_type (σ : List (Name × Expr)) :
    substAll .type σ = .type := by
  induction σ with
  | nil => rfl
  | cons ⟨_, _⟩ rest ih =>
    simp only [substAll, List.foldl, Expr.subst]
    exact ih

/-- substAll distributes over fix. -/
theorem substAll_fix (inner : Expr) (σ : List (Name × Expr)) :
    substAll (.fix inner) σ = .fix (substAll inner σ) := by
  induction σ generalizing inner with
  | nil => rfl
  | cons ⟨x, v⟩ rest ih =>
    simp only [substAll, List.foldl]
    exact ih (inner.subst x v)

-- ============================================================
-- Logical Relation
-- ============================================================

/-- Logical relation: concrete value v is sound w.r.t. abstract value τ.

    Indexed by n (depth of extensional checking), decoupled from eval fuel.
    - At n=0: everything related (vacuously)
    - τ = .type: everything related (Type is top)
    - Both lambdas at n+1: extensional — when applied to LR-related args
      (at level n), body results are LR-related (at level n)
    - Otherwise: True (catch-all for cases that shouldn't arise in
      well-typed programs; e.g., stuck apps, mismatched shapes)

    The universal quantification over Γ in the lambda clause accounts for
    the fact that the abstract body may reference variables from the env
    where it was normalized. For "wrong" Γ's, absEval returns None and
    the conclusion is vacuously true. -/
def LR : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | _, _, .type => True
  | n + 1, .lam xv _dv bv, .lam xa _da ba =>
    ∀ (Γ : Env) (k : Nat) (av aa : Expr),
      LR n av aa →
      ∀ (v' τ' : Expr),
        concEvalS k (bv.subst xv av) = some v' →
        absEval k ((xa, aa) :: Γ) ba = some τ' →
        LR n v' τ'
  | _, _, _ => True

-- ============================================================
-- Environment-level logical relation
-- ============================================================

/-- σ and Γ are LR-related: each abstract binding has a corresponding
    concrete value, and they are LR-related.
    Assumes σ values are closed (results of concEvalS on closed terms). -/
def EnvLR (n : Nat) (σ : List (Name × Expr)) (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ →
    ∃ v, σ.lookup x = some v ∧ LR n v τ

/-- Empty env/subst are trivially LR-related. -/
theorem envLR_nil (n : Nat) : EnvLR n [] [] := by
  intro x τ h; simp [Env.lookup] at h

/-- Extending both with LR-related values preserves EnvLR. -/
theorem envLR_extend {n : Nat} {σ : List (Name × Expr)} {Γ : Env}
    (h : EnvLR n σ Γ) (x : Name) (v τ : Expr) (hv : LR n v τ) :
    EnvLR n ((x, v) :: σ) ((x, τ) :: Γ) := by
  intro y τ' h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ' h_lookup

-- ============================================================
-- Key lemma: normalization stability
-- ============================================================

/-- **Normalization stability** (the key bridge lemma).

    absEval normalizes lambda bodies under a neutral binder:
      absEval Γ (lam x d body) = lam x d body'
      where body' = absEval ((x, var x) :: Γ) body

    When this lambda is later applied with argument a, absEval evaluates
    the NORMALIZED body body' in ((x, a) :: Γ), not the original body.

    This lemma states: evaluating the normalized body with a concrete binding
    gives the same result as evaluating the original body directly.

    **Proof strategy:** By induction on fuel/body. Key cases:
    - var y (y = x): body' has (var x), which maps to a in both evals. ✓
    - var y (y ≠ x): body' has Γ(y). Re-evaluating Γ(y) in the same Γ
      gives the same result (values in Γ are already normalized). ✓
    - lam y d' inner: body' has lam y d' inner'. IH on inner. ✓
    - app f' a': beta-reduced or stuck. IH on components. ✓

    Main difficulty: showing that values from Γ are "idempotent" under
    re-normalization. This holds because absEval's results in a fixed env
    are fixed points of re-evaluation (absEval Γ (absEval Γ e) = absEval Γ e). -/
theorem absEval_normalize_stable (k k' : Nat) (Γ : Env) (body : Expr)
    (x : Name) (a body' : Expr)
    (h_norm : absEval k' ((x, .var x) :: Γ) body = some body')
    (h_fuel : k ≤ k') :
    absEval k ((x, a) :: Γ) body' = absEval k ((x, a) :: Γ) body := by
  sorry

-- ============================================================
-- Closed values (infrastructure for substAll_var)
-- ============================================================

/-- All free variables of `e` are in `bound`.
    `IsClosed e` (= `HasNoFreeVars [] e`) means e has no free variables. -/
def HasNoFreeVars (bound : List Name) : Expr → Prop
  | .var x => x ∈ bound
  | .lam x d b => HasNoFreeVars bound d ∧ HasNoFreeVars (x :: bound) b
  | .app f a => HasNoFreeVars bound f ∧ HasNoFreeVars bound a
  | .asc t τ => HasNoFreeVars bound t ∧ HasNoFreeVars bound τ
  | .type => True
  | .fix e => HasNoFreeVars bound e

abbrev IsClosed (e : Expr) : Prop := HasNoFreeVars [] e

/-- If x is not among the potentially-free variables of e, substituting x is a no-op. -/
theorem subst_noop_of_not_free (e : Expr) (x : Name) (s : Expr)
    (bound : List Name)
    (h_bound : HasNoFreeVars bound e)
    (h_not_in : x ∉ bound) :
    e.subst x s = e := by
  induction e generalizing bound with
  | var y =>
    simp only [HasNoFreeVars] at h_bound
    -- h_bound : y ∈ bound, h_not_in : x ∉ bound → y ≠ x
    simp only [Expr.subst]
    have h_neq : ¬(y == x = true) := by
      intro h_beq
      have := (beq_iff_eq (α := String)).mp h_beq
      subst this; exact h_not_in h_bound
    simp [h_neq]
  | lam y d body ih_d ih_body =>
    simp only [HasNoFreeVars] at h_bound
    obtain ⟨h_d, h_body⟩ := h_bound
    simp only [Expr.subst]
    have h_d_eq := ih_d bound h_d h_not_in
    split
    · -- y == x: body shadowed, only domain changes
      exact congrArg₂ (Expr.lam y · body) h_d_eq
    · -- y ≠ x: both domain and body
      rename_i h_neq
      have h_not_ext : x ∉ y :: bound := by
        intro h_mem; cases h_mem with
        | head => exact h_neq ((beq_iff_eq (α := String)).mpr rfl)
        | tail _ h' => exact h_not_in h'
      exact congrArg₂ (Expr.lam y ·) h_d_eq (ih_body (y :: bound) h_body h_not_ext)
  | app f a ih_f ih_a =>
    simp only [HasNoFreeVars] at h_bound
    simp only [Expr.subst]
    exact congrArg₂ Expr.app (ih_f bound h_bound.1 h_not_in) (ih_a bound h_bound.2 h_not_in)
  | asc t τ ih_t ih_τ =>
    simp only [HasNoFreeVars] at h_bound
    simp only [Expr.subst]
    exact congrArg₂ Expr.asc (ih_t bound h_bound.1 h_not_in) (ih_τ bound h_bound.2 h_not_in)
  | type =>
    simp [Expr.subst]
  | fix inner ih =>
    simp only [HasNoFreeVars] at h_bound
    simp only [Expr.subst]
    exact congrArg Expr.fix (ih bound h_bound h_not_in)

/-- Closed expressions are unchanged by any substitution. -/
theorem subst_closed_noop (e : Expr) (x : Name) (s : Expr)
    (h_closed : IsClosed e) :
    e.subst x s = e :=
  subst_noop_of_not_free e x s [] h_closed (List.not_mem_nil x)

/-- For a list of closed values, substAll (var x) σ = σ.lookup x
    (when x is in σ) or (var x) (when x is not in σ). -/
theorem substAll_var (x : Name) (σ : List (Name × Expr))
    (h_closed : ∀ p ∈ σ, IsClosed p.2) :
    substAll (.var x) σ = match Env.lookup σ x with
      | some v => v
      | none => .var x := by
  induction σ with
  | nil => rfl
  | cons ⟨y, v⟩ rest ih =>
    simp only [substAll, List.foldl, Expr.subst, Env.lookup]
    split
    · -- y == x: subst gives v, then substAll v rest = v (v is closed)
      rename_i h_eq
      -- substAll v rest = v because v is closed
      have h_v_closed : IsClosed v := h_closed ⟨y, v⟩ (List.mem_cons_self _ _)
      have h_rest_closed : ∀ p ∈ rest, IsClosed p.2 :=
        fun p hp => h_closed p (List.mem_cons_of_mem _ hp)
      -- substAll v rest: each substitution is a no-op on closed v
      suffices h : substAll v rest = v by simp [h]
      induction rest with
      | nil => rfl
      | cons ⟨z, w⟩ rest' ih' =>
        simp only [substAll, List.foldl]
        rw [subst_closed_noop v z w h_v_closed]
        exact ih' (fun p hp => h_rest_closed p (List.mem_cons_of_mem _ hp))
    · -- y ≠ x: subst gives (var x), continue with rest
      rename_i h_neq
      have h_rest_closed : ∀ p ∈ rest, IsClosed p.2 :=
        fun p hp => h_closed p (List.mem_cons_of_mem _ hp)
      exact ih h_rest_closed

-- ============================================================
-- Value self-evaluation
-- ============================================================

/-- A concEvalS "value": lambdas and .type are returned as-is. -/
def IsValue : Expr → Prop
  | .lam _ _ _ => True
  | .type => True
  | _ => False

/-- Values self-evaluate under concEvalS (with fuel > 0). -/
theorem concEvalS_value (k : Nat) (v : Expr) (h : IsValue v) :
    concEvalS (k + 1) v = some v := by
  cases v with
  | lam _ _ _ => simp [concEvalS]
  | type => simp [concEvalS]
  | _ => exact absurd h (by simp [IsValue])

-- ============================================================
-- Fundamental theorem
-- ============================================================

/-- **Fundamental theorem of the logical relation.**

    For any expression e with free variables bound by σ (concrete) and Γ (abstract),
    if σ and Γ are LR-related, and both evaluators terminate, then the results
    are LR-related.

    **Proof by induction on fuel.** Key cases:

    **var x**: substAll (var x) σ = σ(x) by substAll_var. concEvalS of a
    closed value returns it. EnvLR gives LR n σ(x) Γ(x).

    **type**: both return .type. LR n .type .type = True.

    **lam x d body**: concEvalS returns the substituted lambda as-is.
    absEval normalizes the body. Need to construct the LR extensional
    property: for any LR args, body results are LR. Use the IH at
    reduced fuel on the body, with envLR_extend for the new binding.
    The absEval_normalize_stable lemma bridges normalized vs original body.

    **app f a**: Both evaluators evaluate f and a (at fuel k), then beta-reduce.
    IH at fuel k gives LR n f_c f_a and LR n a_c a_a. For the body:
    - concrete: concEvalS k (body_c.subst x a_c)
    - abstract: absEval k ((x, a_a) :: Γ) body_a'  (body_a' = normalized body)
    Apply IH at fuel k to the ORIGINAL body with extended env/subst.
    Use absEval_normalize_stable to equate absEval on body_a' with body.
    The substAll commutativity (closed values) equates body_c.subst x a_c
    with substAll body ((x, a_c) :: σ).

    **asc term ty**: concEvalS evaluates term, absEval evaluates ty.
    IH on term gives LR n v σ_term. WellTyped gives Subtype' σ_term τ.
    Need: LR n v τ. For lambdas, this requires composing the extensional
    property with subtyping — the most complex case.

    **fix (lam f d body)**: absEval returns d' = absEval Γ d (declared type).
    concEvalS unrolls. Similar structure to existing fix soundness.

    **Assumptions on σ:**
    - All values in σ are closed (results of concEvalS on closed terms)
    - σ and Γ have the same domain (same variable names)
    These hold for the top-level call (σ = [], Γ = []) and are preserved
    by envLR_extend when processing lambda bodies. -/
theorem fundamental (n fuel : Nat) (σ : List (Name × Expr)) (Γ : Env)
    (e v τ : Expr)
    (h_env : EnvLR n σ Γ)
    (hc : concEvalS fuel (substAll e σ) = some v)
    (ha : absEval fuel Γ e = some τ)
    (h_wt : WellTyped fuel Γ e)
    (h_closed : ∀ p ∈ σ, IsClosed p.2)
    (h_vals : ∀ p ∈ σ, IsValue p.2) :
    LR n v τ := by
  induction fuel generalizing n σ Γ e v τ with
  | zero => simp [absEval] at ha
  | succ k ih =>
    cases e with
    | var x =>
      simp only [absEval] at ha
      rw [substAll_var x σ h_closed] at hc
      obtain ⟨v_x, h_σ_x, h_lr⟩ := h_env x τ ha
      rw [h_σ_x] at hc
      -- hc : concEvalS (k+1) v_x = some v, v_x is a value
      -- Lookup gives some pair in σ, so v_x is a value
      have h_in_σ : (x, v_x) ∈ σ := by
        -- h_σ_x : Env.lookup σ x = some v_x
        -- Env.lookup is List lookup, so (x, v_x) ∈ σ
        sorry  -- needs a small lookup membership lemma
      have h_val : IsValue v_x := h_vals ⟨x, v_x⟩ h_in_σ
      rw [concEvalS_value k v_x h_val] at hc
      cases hc; exact h_lr
    | type =>
      simp only [absEval] at ha
      rw [substAll_type] at hc
      simp only [concEvalS] at hc
      cases ha; cases hc
      exact True.intro  -- LR n .type .type = True (second clause)
    | lam x dom body =>
      -- concEvalS returns the lambda as-is (value).
      -- absEval normalizes the body.
      -- Need to construct the LR extensional property.
      -- For n = 0: LR 0 = True. ✓
      -- For n+1: need ∀ Γ' k' av aa, LR n av aa → body results LR n.
      -- Use the IH on the body with extended env/subst.
      -- Key difficulty: relating substAll body ((x, av) :: σ) with
      -- (substAll body σ_without_x).subst x av (how concEvalS processes it).
      -- Also need absEval_normalize_stable for the abstract side.
      sorry
    | asc term ty =>
      -- concEvalS evaluates term (lhs)
      -- absEval evaluates ty (rhs)
      -- WellTyped gives Subtype' (absEval term) (absEval ty)
      -- IH on term: LR n v (absEval term)
      -- Need to compose with subtyping to get LR n v (absEval ty)
      sorry
    | fix inner =>
      -- absEval returns the declared type (domain of inner lambda)
      -- concEvalS unrolls and evaluates body
      -- Similar to Soundness.lean fix case
      sorry
    | app f a =>
      -- THE KEY CASE.
      -- Both evaluators evaluate f and a at fuel k, then beta-reduce.
      rw [substAll_app] at hc
      simp only [concEvalS] at hc
      simp only [absEval] at ha
      -- Extract abstract evaluation of f and a
      cases hfa : absEval k Γ f with
      | none => simp [hfa] at ha
      | some τ_f =>
        cases haa : absEval k Γ a with
        | none => simp [hfa, haa] at ha
        | some τ_a =>
          -- Extract concrete evaluation of f and a
          cases hfc : concEvalS k (substAll f σ) with
          | none => simp [hfc] at hc
          | some v_f =>
            cases hac : concEvalS k (substAll a σ) with
            | none => simp [hfc, hac] at hc
            | some v_a =>
              -- Apply IH to f and a (fuel decreases: k < k+1)
              have ih_f := ih n σ Γ f v_f τ_f h_env hfc hfa
                (by cases h_wt_app : h_wt; sorry) h_closed  -- need WellTyped for f
              have ih_a := ih n σ Γ a v_a τ_a h_env hac haa
                (by sorry) h_closed  -- need WellTyped for a
              -- Now case-split on τ_f (what absEval got for the function)
              rw [hfa, haa] at ha
              rw [hfc, hac] at hc
              cases τ_f with
              | lam xa da ba =>
                -- Abstract function is a lambda → beta-reduce
                simp only at ha
                cases v_f with
                | lam xv dv bv =>
                  -- Concrete function is also a lambda → beta-reduce
                  simp only at hc
                  -- hc : concEvalS k (bv.subst xv v_a) = some v
                  -- ha : absEval k ((xa, τ_a) :: Γ) ba = some τ
                  -- ih_f : LR n (lam xv dv bv) (lam xa da ba)
                  -- ih_a : LR n v_a τ_a
                  --
                  -- OPTION A: Use the IH at fuel k on the original body.
                  --   Need absEval_normalize_stable to equate absEval on ba
                  --   (normalized) with absEval on the original body.
                  --   Need substAll commutativity for the concrete side.
                  --
                  -- OPTION B: Use the lambda clause of ih_f.
                  --   This gives LR (n-1) for the body results (loses a level).
                  --   Sufficient for external consumers but not for the
                  --   inductive proof which needs LR n.
                  --
                  -- OPTION A is correct. The IH at fuel k gives LR n directly.
                  sorry
                | _ =>
                  -- Concrete function is not a lambda.
                  -- For well-typed closed terms, this shouldn't happen
                  -- (if abstract gives a lambda, concrete should too).
                  -- The catch-all LR clause gives True.
                  sorry
              | type =>
                -- Abstract function is Type → type-app-returns-type
                simp only at ha; cases ha
                exact True.intro  -- LR n v .type = True
              | _ =>
                -- Abstract function is stuck (var/app/asc/fix)
                -- Catch-all LR clause gives True for most cases
                sorry

/-- **Top-level soundness of concEvalS.**

    For closed terms (empty env/subst), if both evaluators terminate,
    the results are LR-related at any depth n.

    This means: the concrete value from concEvalS and the abstract type
    from absEval are extensionally equivalent — when applied as functions
    to related arguments, they produce related results, all the way down.

    Unlike SubtypeTrans (which requires syntactic similarity), LR handles
    the fact that concEvalS produces un-normalized lambdas while absEval
    produces normalized ones. -/
theorem soundnessS (n fuel : Nat) (e v τ : Expr)
    (hc : concEvalS fuel e = some v)
    (ha : absEval fuel [] e = some τ)
    (h_wt : WellTyped fuel [] e) :
    LR n v τ := by
  have h_subst : substAll e [] = e := rfl
  exact fundamental n fuel [] [] e v τ (envLR_nil n)
    (h_subst ▸ hc) ha h_wt (fun _ h => nomatch h) (fun _ h => nomatch h)
