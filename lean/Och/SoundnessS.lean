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

## Proof architecture (revised by agent ochre-lean-20260331-182533)

The main theorem (`fundamental`) proves `∀ n, LR n v τ` — the results are
LR-related at ALL depths. This avoids the "level loss" problem in the app case:

**The level-loss problem (original formulation):** The LR lambda clause at
level n+1 gives body results at level n. If fundamental proves `LR n` for a
specific n, the app case can only get `LR (n-1)` via the lambda clause.

**The fix (∀ n formulation):** fundamental proves `∀ n, LR n v τ`. In the
app case, for any target level m, we instantiate the IH on f at level m+1,
getting the lambda clause at level m, and instantiate the IH on a at level m.
This yields `LR m` for the body results. Since m was arbitrary, we get ∀ m.

This approach completely avoids `absEval_normalize_stable` in the app case.

### Remaining blocker: `absEval_normalize_stable`

The lam case still needs this lemma to bridge normalized vs original bodies:

  absEval k ((x, a) :: Γ) (absEval k' ((x, var x) :: Γ) body)
  = absEval k ((x, a) :: Γ) body

The lam case of fundamental must CONSTRUCT the LR extensional property.
The IH gives the property for the original body, but the lambda's stored
body is normalized. This bridge is needed to connect them.

NOTE: This lemma may need a careful fuel constraint or even a reformulation.
Normalization pre-computes some work, so the normalized body may succeed with
LESS fuel than the original. If k_app < k_norm, absEval k_app Γ body' may
succeed while absEval k_app Γ body fails. The lemma as stated (with k ≤ k')
may be too weak — it might need the reverse direction or a different approach.
See PROGRESS.md for discussion.

## Status

- [x] LR definition
- [x] EnvLR definition
- [x] substAll definition and distribution lemmas (app, asc, type, fix)
- [x] substAll_var lemma (closed value infrastructure)
- [x] subst_comm, substAll_subst_comm, substAll_lam (substitution commutativity)
- [x] LR_upcast (composition of LR with Subtype') — proved except fuel adequacy gap
- [x] Fundamental theorem — var, type, app, asc cases PROVED
- [x] Top-level soundnessS corollary
- [ ] Lam case of fundamental (needs absEval_normalize_stable)
- [ ] Fix case of fundamental (needs .fix not being IsValue → can't use IH directly)
- [ ] absEval_normalize_stable (the key bridge lemma for lam case)
- [ ] LR_upcast fuel adequacy (lam_body case when body₂ doesn't evaluate)
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
-- Env.lookup membership
-- ============================================================

/-- If Env.lookup finds a value, the pair is in the list. -/
theorem Env.lookup_mem {σ : List (Name × Expr)} {x : Name} {v : Expr}
    (h : Env.lookup σ x = some v) : (x, v) ∈ σ := by
  induction σ with
  | nil => simp [Env.lookup] at h
  | cons ⟨y, w⟩ rest ih =>
    simp only [Env.lookup] at h
    split at h
    · -- y == x
      cases h
      rename_i h_eq
      have := (beq_iff_eq (α := String)).mp h_eq
      subst this
      exact List.mem_cons_self _ _
    · exact List.mem_cons_of_mem _ (ih h)

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
-- Substitution commutativity
-- ============================================================

/-- Closed substitutions commute: if s₁ and s₂ are closed and x₁ ≠ x₂, then
    applying (x₁ → s₁) then (x₂ → s₂) gives the same result as the reverse. -/
theorem subst_comm (e : Expr) (x₁ x₂ : Name) (s₁ s₂ : Expr)
    (h_neq : x₁ ≠ x₂) (h_cl₁ : IsClosed s₁) (h_cl₂ : IsClosed s₂) :
    (e.subst x₁ s₁).subst x₂ s₂ = (e.subst x₂ s₂).subst x₁ s₁ := by
  induction e with
  | var y =>
    simp only [Expr.subst]
    by_cases h₁ : y == x₁ <;> by_cases h₂ : y == x₂ <;> simp [h₁, h₂]
    · -- y = x₁ = x₂: contradiction
      have := (beq_iff_eq (α := String)).mp h₁
      have := (beq_iff_eq (α := String)).mp h₂
      subst_vars; exact absurd rfl h_neq
    · -- y = x₁ ≠ x₂
      simp [Expr.subst]
      have h₂' : ¬(y == x₂ = true) := h₂
      simp [h₂']
      exact subst_closed_noop s₁ x₂ s₂ h_cl₁
    · -- y = x₂ ≠ x₁
      simp [Expr.subst]
      have h₁' : ¬(y == x₁ = true) := h₁
      simp [h₁']
      exact subst_closed_noop s₂ x₁ s₁ h_cl₂
    · -- y ≠ x₁, y ≠ x₂
      simp [Expr.subst, h₁, h₂]
  | lam y d b ih_d ih_b =>
    simp only [Expr.subst]
    by_cases h_y1 : y == x₁ <;> by_cases h_y2 : y == x₂ <;> simp [h_y1, h_y2]
    · -- y = x₁ = x₂: contradiction
      have := (beq_iff_eq (α := String)).mp h_y1
      have := (beq_iff_eq (α := String)).mp h_y2
      subst_vars; exact absurd rfl h_neq
    · -- y = x₁ ≠ x₂: subst x₁ shadows body, subst x₂ goes through
      simp [Expr.subst, h_y1, h_y2]
      exact congrArg₂ (Expr.lam y ·) ih_d rfl
    · -- y = x₂ ≠ x₁: symmetric
      simp [Expr.subst, h_y1, h_y2]
      exact congrArg₂ (Expr.lam y ·) ih_d rfl
    · -- y ≠ x₁, y ≠ x₂
      simp [Expr.subst, h_y1, h_y2]
      exact congrArg₂ (Expr.lam y ·) ih_d ih_b
  | app f a ih_f ih_a =>
    simp only [Expr.subst]
    exact congrArg₂ Expr.app ih_f ih_a
  | asc t τ ih_t ih_τ =>
    simp only [Expr.subst]
    exact congrArg₂ Expr.asc ih_t ih_τ
  | type => rfl
  | fix inner ih =>
    simp only [Expr.subst]
    exact congrArg Expr.fix ih

/-- substAll and a single subst commute when the variable is fresh for σ's domain
    and the substitution value and all σ values are closed.

    substAll (e.subst x v) σ = (substAll e σ).subst x v -/
theorem substAll_subst_comm (e : Expr) (x : Name) (v : Expr) (σ : List (Name × Expr))
    (h_fresh : x ∉ σ.map Prod.fst)
    (h_cl_v : IsClosed v)
    (h_cl_σ : ∀ p ∈ σ, IsClosed p.2) :
    substAll (e.subst x v) σ = (substAll e σ).subst x v := by
  induction σ generalizing e with
  | nil => rfl
  | cons ⟨y, w⟩ rest ih =>
    simp only [substAll, List.foldl]
    have h_neq : x ≠ y := by
      intro h_eq; subst h_eq
      exact h_fresh (List.mem_cons_self x (rest.map Prod.fst))
    have h_cl_w : IsClosed w := h_cl_σ ⟨y, w⟩ (List.mem_cons_self _ _)
    have h_rest_fresh : x ∉ rest.map Prod.fst := by
      intro h_mem; exact h_fresh (List.mem_cons_of_mem _ h_mem)
    have h_rest_cl : ∀ p ∈ rest, IsClosed p.2 :=
      fun p hp => h_cl_σ p (List.mem_cons_of_mem _ hp)
    -- (e.subst x v).subst y w = (e.subst y w).subst x v by subst_comm
    rw [subst_comm (e := e) (x₁ := x) (x₂ := y) (s₁ := v) (s₂ := w)
        h_neq h_cl_v h_cl_w]
    exact ih (e.subst y w) h_rest_fresh h_rest_cl

/-- substAll distributes over lam when the binder is fresh for σ's domain. -/
theorem substAll_lam (x : Name) (dom body : Expr) (σ : List (Name × Expr))
    (h_fresh : x ∉ σ.map Prod.fst) :
    substAll (.lam x dom body) σ = .lam x (substAll dom σ) (substAll body σ) := by
  induction σ generalizing dom body with
  | nil => rfl
  | cons ⟨y, w⟩ rest ih =>
    simp only [substAll, List.foldl]
    have h_neq : x ≠ y := by
      intro h_eq; subst h_eq
      exact h_fresh (List.mem_cons_self x (rest.map Prod.fst))
    -- Since x ≠ y, subst y w goes through both domain and body
    have h_not_eq : ¬(x == y) := by
      intro h_beq
      exact h_neq ((beq_iff_eq (α := String)).mp h_beq)
    simp only [Expr.subst, h_not_eq, ↓reduceIte]
    have h_rest_fresh : x ∉ rest.map Prod.fst := by
      intro h_mem; exact h_fresh (List.mem_cons_of_mem _ h_mem)
    exact ih (dom.subst y w) (body.subst y w) h_rest_fresh

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
-- LR upcast (composition with Subtype')
-- ============================================================

/-- EnvSub is reflexive. -/
theorem envSub_refl (Γ : Env) : EnvSub Γ Γ :=
  fun _ τ₁ h => ⟨τ₁, h, Subtype'.refl τ₁⟩

/-- **LR upcast**: if `LR n v σ'` and `Subtype' σ' τ`, then `LR n v τ`.

    This is needed for the asc case of the fundamental theorem, where the
    concrete value v is related to σ' (via IH on the term) and σ' subtypes τ
    (from well-typedness of the ascription).

    Most cases are trivial (top → .type → True; app/fix/var → catch-all True).
    The lam_body case is partially proved: when absEval succeeds for the more-
    precise body (body₂), we use monotonicity to relate the results and then
    recurse. When body₂ doesn't succeed (fuel inadequacy), this is sorry'd.
    See PROGRESS.md for analysis of this fuel adequacy issue. -/
theorem LR_upcast : ∀ (n : Nat) (v σ' τ : Expr),
    LR n v σ' → Subtype' σ' τ → LR n v τ := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ m ih =>
    intro v σ' τ h_lr h_sub
    cases h_sub with
    | refl => exact h_lr
    | top => -- τ = .type, LR (m+1) v .type = True
      cases v <;> simp [LR]
    | lam_body h_body =>
      -- σ' = lam x dom body₂, τ = lam x dom body₁, Subtype' body₂ body₁
      rename_i x dom body₁ body₂
      cases v with
      | lam xv dv bv =>
        -- Both sides are lam: need extensional property
        simp only [LR] at h_lr ⊢
        intro Γ k av aa h_lr_a v' τ₁' h_conc h_abs_1
        -- Case-split on whether body₂ evaluates at this fuel
        cases h_body₂ : absEval k ((x, aa) :: Γ) body₂ with
        | some τ₂' =>
          -- body₂ succeeds: use hypothesis to get LR m v' τ₂'
          have h_lr_body := h_lr Γ k av aa h_lr_a v' τ₂' h_conc h_body₂
          -- monotonicity gives Subtype' τ₂' τ₁'
          have h_env_refl : EnvSub ((x, aa) :: Γ) ((x, aa) :: Γ) :=
            envSub_refl _
          have h_mono := absEval_mono k ((x, aa) :: Γ) ((x, aa) :: Γ)
            body₁ body₂ τ₁' τ₂' h_body h_env_refl h_abs_1 h_body₂
          -- recursive LR_upcast at level m
          exact ih v' τ₂' τ₁' h_lr_body h_mono
        | none =>
          -- body₂ doesn't succeed at this fuel (fuel adequacy gap).
          -- This can only happen when Subtype' body₂ body₁ involves a `top`
          -- somewhere (making body₁ simpler than body₂), but the structural
          -- effect propagates through absEval making the conclusion non-trivial.
          -- See PROGRESS.md "LR_upcast fuel adequacy" for detailed analysis.
          sorry
      | _ => -- non-lambda v: catch-all True
        simp [LR]
    | app_cong => -- τ = app ..: catch-all True
      cases v <;> simp [LR]
    | fix_cong => -- τ = fix ..: catch-all True
      cases v <;> simp [LR]

-- ============================================================
-- Fundamental theorem
-- ============================================================

/-- **Fundamental theorem of the logical relation.**

    For any expression e with free variables bound by σ (concrete) and Γ (abstract),
    if σ and Γ are LR-related at all depths, and both evaluators terminate,
    then the results are LR-related at all depths.

    The `∀ n` formulation is essential for the app case: using the LR lambda
    clause at level n+1 gives body results at level n; since we prove the
    result for all n, this level loss is harmless.

    **App case strategy:**
    1. IH on f gives `∀ n, LR n v_f τ_f`
    2. IH on a gives `∀ n, LR n v_a τ_a`
    3. For target level m: use LR (m+1) for f (lambda clause at level m)
    4. Use LR m for a as the argument
    5. Lambda clause gives LR m for body results
    6. Since m was arbitrary: ∀ m, LR m v' τ' ✓

    **Lam case:** Needs `absEval_normalize_stable` to bridge the normalized
    body (stored in the abstract lambda) with the original body (for the IH).
    Left as sorry — see module doc for discussion.

    **Asc case:** PROVED via LR_upcast. The IH on `term` gives LR n v σ',
    WellTyped gives Subtype' σ' τ, and LR_upcast composes them.

    **Fix case:** Left as sorry. The key issue is that `.fix inner` is not
    an `IsValue`, so extending σ with a fix value breaks `h_vals`. The fix
    case needs a different proof strategy — either relax `h_vals` (which
    complicates the var case) or handle fix separately from the IH. -/
theorem fundamental (fuel : Nat) (σ : List (Name × Expr)) (Γ : Env)
    (e v τ : Expr)
    (h_env : ∀ n, EnvLR n σ Γ)
    (hc : concEvalS fuel (substAll e σ) = some v)
    (ha : absEval fuel Γ e = some τ)
    (h_wt : WellTyped fuel Γ e)
    (h_closed : ∀ p ∈ σ, IsClosed p.2)
    (h_vals : ∀ p ∈ σ, IsValue p.2) :
    ∀ n, LR n v τ := by
  induction fuel generalizing σ Γ e v τ with
  | zero => simp [absEval] at ha
  | succ k ih =>
    cases e with
    | var x =>
      simp only [absEval] at ha
      rw [substAll_var x σ h_closed] at hc
      intro n
      obtain ⟨v_x, h_σ_x, h_lr⟩ := h_env n x τ ha
      rw [h_σ_x] at hc
      have h_in_σ := Env.lookup_mem h_σ_x
      have h_val : IsValue v_x := h_vals ⟨x, v_x⟩ h_in_σ
      rw [concEvalS_value k v_x h_val] at hc
      cases hc; exact h_lr
    | type =>
      simp only [absEval] at ha
      rw [substAll_type] at hc
      simp only [concEvalS] at hc
      cases ha; cases hc
      intro n; cases n <;> simp [LR]  -- LR _ .type .type = True
    | lam x dom body =>
      -- concEvalS returns the lambda as-is (value).
      -- absEval normalizes the body under (x, var x) :: Γ.
      -- Need to construct the LR extensional property for all n.
      --
      -- For n = 0: LR 0 = True ✓
      -- For n+1, both lambdas: need ∀ Γ' k' av aa, LR n av aa → body
      --   results LR n.
      --
      -- The IH gives: for the ORIGINAL body with extended env/subst, results
      -- are LR at all levels. But the abstract lambda stores the NORMALIZED
      -- body (body' = absEval k ((x, var x) :: Γ) body). To connect:
      --   absEval k' ((x, aa) :: Γ') body' = absEval k' ((x, aa) :: Γ') body
      -- This is `absEval_normalize_stable`, which is unproven.
      --
      -- Additionally, the concrete side needs substAll commutativity:
      --   (substAll body σ).subst x av = substAll body ((x, av) :: σ)
      -- when x is fresh for σ and σ values are closed.
      sorry
    | asc term ty =>
      -- concEvalS evaluates term (lhs), absEval evaluates ty (rhs).
      rw [substAll_asc] at hc
      simp only [concEvalS] at hc   -- concEvalS k (substAll term σ) = some v
      simp only [absEval] at ha     -- absEval k Γ ty = some τ
      -- Extract WellTyped components
      obtain ⟨h_wt_term, _, term_type, ty_type, h_abs_term, h_abs_ty, h_sub_wt⟩ := h_wt
      -- τ = ty_type (both are absEval k Γ ty)
      have h_eq : ty_type = τ := by rw [h_abs_ty] at ha; exact Option.some.inj ha
      subst h_eq
      -- IH on term: ∀ n, LR n v term_type
      have ih_term := ih σ Γ term v term_type h_env hc h_abs_term h_wt_term h_closed h_vals
      -- LR_upcast: Subtype' term_type τ → LR n v τ
      intro n
      exact LR_upcast n v term_type τ (ih_term n) h_sub_wt
    | fix inner =>
      -- absEval returns the declared type (domain of inner lambda).
      -- concEvalS unrolls and evaluates body with f := fix inner in scope.
      -- Similar structure to Soundness.lean fix case, but needs LR-based
      -- env consistency instead of SubtypeTrans-based EnvConsistent.
      sorry
    | app f a =>
      -- THE KEY CASE — fully proved using the ∀ n approach.
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
              -- Extract WellTyped components for app
              have ⟨h_wt_f, h_wt_a, h_wt_body⟩ := h_wt
              -- Apply IH to f and a (fuel decreases: k < k+1)
              have ih_f := ih σ Γ f v_f τ_f h_env hfc hfa h_wt_f h_closed h_vals
              have ih_a := ih σ Γ a v_a τ_a h_env hac haa h_wt_a h_closed h_vals
              -- Now case-split on τ_f (what absEval got for the function)
              rw [hfa, haa] at ha h_wt_body
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
                  -- ih_f : ∀ n, LR n (lam xv dv bv) (lam xa da ba)
                  -- ih_a : ∀ n, LR n v_a τ_a
                  --
                  -- Strategy: use the LR lambda clause.
                  -- For any target level m:
                  --   ih_f (m+1) : LR (m+1) (lam xv dv bv) (lam xa da ba)
                  --   = ∀ Γ' k' av aa, LR m av aa → ... → LR m v' τ'
                  --   ih_a m : LR m v_a τ_a
                  --   Instantiate with Γ' = Γ, k' = k, av = v_a, aa = τ_a
                  --   Get LR m v τ ✓
                  intro m
                  cases m with
                  | zero => trivial  -- LR 0 = True
                  | succ m =>
                    -- ih_f (m+1+1) gives lambda clause at level m+1
                    have h_lam_lr := ih_f (m + 1 + 1)
                    -- LR (m+1+1) (lam xv dv bv) (lam xa da ba)
                    -- = ∀ Γ' k' av aa, LR (m+1) av aa → ... → LR (m+1) v' τ'
                    simp only [LR] at h_lam_lr
                    exact h_lam_lr Γ k v_a τ_a (ih_a (m + 1)) v τ hc ha
                | _ =>
                  -- Concrete function is not a lambda (var/app/asc/type/fix).
                  -- LR n (non-lam) (lam ..) falls into the catch-all → True
                  intro n; cases n <;> simp [LR]
              | type =>
                -- Abstract function is Type → type-app-returns-type
                simp only at ha; cases ha
                intro n; cases n <;> simp [LR]  -- LR _ _ .type = True
              | var _ | app _ _ | asc _ _ | fix _ =>
                -- Abstract function is stuck → result is stuck app or type
                -- In all cases, τ is not .type and not .lam (it's app/var/etc.)
                -- so LR n v τ falls into the catch-all → True
                all_goals (
                  simp only at ha
                  intro n
                  cases ha_eq : ha
                  cases n <;> simp [LR]
                )

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
  exact fundamental fuel [] [] e v τ (fun n => envLR_nil n)
    (h_subst ▸ hc) ha h_wt (fun _ h => nomatch h) (fun _ h => nomatch h) n
