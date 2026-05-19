import PSS.Syntax
import PSS.Sub
import PSS.Eval

/-!
# Step-indexed Logical Relation for PSS Type Safety

## Motivation

All syntactic approaches to PSS type safety hit the same wall: composing
`trans(h1, beta_L, hw)` doesn't decrease any simple measure. This has been
open since Hutchins (POPL 2010). The axioms `top_not_sub_lam` and
`lam_sub_lam_inversion` in `Soundness.lean` both have sorry-carrying proofs
in `CanonicalForms.lean`.

This file takes a **semantic** approach using step-indexed logical relations.

## Key results (proved without sorry)

1. `SemVal`/`SemExpr` — well-founded step-indexed semantic type definitions
2. `semVal_top` — every value is in the semantic type of Top
3. `semVal_isVal` — semantic values are syntactic values
4. `top_not_in_semVal_lam` — **THE SEMANTIC CANONICAL FORMS LEMMA**:
   Top is never in V_{k+1}(lam s t). Definitional, no Sub analysis needed!
5. `subSem_trans` — semantic transitivity is FREE (set inclusion composes)
6. `subSem_top_not_lam` — SubSem Top (lam s t) is False
7. `sem_canonical_lam_strong` — universal canonical forms for all step indices
8. `concEval_safe` — type safety assuming the fundamental theorem (1 sorry)

## Architecture of the gap

The fundamental theorem (Sub [] e tau -> ... -> SemExpr k tau e) is axiomatized.
Its proof by induction on Sub would handle:
- trans: via subSem_trans (TRIVIAL — the syntactic proof's main obstacle)
- top: via subSem_top (TRIVIAL)
- refl/lam/beta/app_cong: standard logical-relation obligations

The one sorry in concEval_safe is for Wf of the substituted body, which
needs lam_sub_lam_inversion or an alternative route.
-/

open Expr

namespace PSS.LogRel

/-! ## Semantic value and expression types -/

/-- A value is Top or a lambda. -/
def IsVal (v : Expr) : Prop := v = .top ∨ ∃ d b, v = .lam d b

theorem isVal_top : IsVal .top := Or.inl rfl
theorem isVal_lam (d b : Expr) : IsVal (.lam d b) := Or.inr ⟨d, b, rfl⟩

/-- Step-indexed semantic value type.

    `SemVal k tau v` means value `v` is in the semantic interpretation of
    type `tau` at step index `k`.

    The step index provides well-foundedness: `k` decreases at each recursive
    call. For application types, we evaluate the type with fuel `k` and
    interpret the result at index `k` (strictly less than `k+1`).

    Key property: `SemVal (k+1) (lam s t) v` requires `v` to be a lambda.
    This makes canonical forms DEFINITIONAL. -/
noncomputable def SemVal : Nat → Expr → Expr → Prop
  | 0, _, v => IsVal v
  | _ + 1, .top, v => IsVal v
  | _ + 1, .bvar _, _ => False
  | k + 1, .lam s t, v =>
    ∃ s' t', v = .lam s' t' ∧
      ∀ j, j < k + 1 → ∀ av, SemVal j s av →
        ∀ i, i ≤ j → ∀ w, concEval i (t'.subst 0 av) = .ok w →
          SemVal (j - i) (t.subst 0 av) w
  | k + 1, .app f a, v =>
    match concEval k (.app f a) with
    | .ok τ_nf => SemVal k τ_nf v
    | _ => IsVal v
termination_by k => k

/-- Semantic expression type.
    `SemExpr k tau e` means: for all j <= k, if `concEval j e = ok v`,
    then `v` is in `SemVal (k - j) tau`. -/
def SemExpr (k : Nat) (τ : Expr) (e : Expr) : Prop :=
  ∀ j, j ≤ k → ∀ v, concEval j e = .ok v → SemVal (k - j) τ v

/-! ## Basic properties of SemVal -/

/-- Every value is semantically in Top at any index. -/
theorem semVal_top (k : Nat) (v : Expr) (hv : IsVal v) : SemVal k .top v := by
  cases k with
  | zero => unfold SemVal; exact hv
  | succ k => unfold SemVal; exact hv

/-- SemVal always implies IsVal (semantic values are syntactic values). -/
theorem semVal_isVal (k : Nat) (τ v : Expr) (h : SemVal k τ v) : IsVal v := by
  induction k generalizing τ v with
  | zero => unfold SemVal at h; exact h
  | succ k ih =>
    match τ with
    | .top => unfold SemVal at h; exact h
    | .bvar _ => unfold SemVal at h; exact absurd h id
    | .lam _ _ =>
      unfold SemVal at h
      obtain ⟨s', t', heq, _⟩ := h
      exact Or.inr ⟨s', t', heq⟩
    | .app f a =>
      unfold SemVal at h
      split at h
      · exact ih _ _ h
      · exact h

/-- At step 0, SemVal equals IsVal regardless of the type. -/
theorem semVal_zero_iff (τ v : Expr) : SemVal 0 τ v ↔ IsVal v := by
  constructor
  · exact semVal_isVal 0 τ v
  · intro hv; unfold SemVal; exact hv

/-! ## THE KEY LEMMA: Semantic Canonical Forms -/

/-- **Semantic canonical forms**: Top is NEVER in `SemVal (k+1) (lam s t)`.

    This is the semantic replacement for the syntactic `top_not_sub_lam`.
    It holds BY DEFINITION of SemVal — no analysis of Sub derivations needed!

    Proof: `SemVal (k+1) (lam s t) v` requires `v = lam s' t'`.
    Since `Top /= lam s' t'`, we get a contradiction. -/
theorem top_not_in_semVal_lam (k : Nat) (s t : Expr) :
    ¬ SemVal (k + 1) (.lam s t) .top := by
  unfold SemVal
  intro ⟨_, _, h, _⟩
  cases h

/-- Values in `SemVal (k+1) (lam s t)` are always lambdas. -/
theorem semVal_lam_is_lam {k : Nat} {s t v : Expr}
    (h : SemVal (k + 1) (.lam s t) v) : ∃ d b, v = .lam d b := by
  unfold SemVal at h
  exact let ⟨s', t', heq, _⟩ := h; ⟨s', t', heq⟩

/-! ## concEval determinism (fuel monotonicity)

If concEval with less fuel produces a result, more fuel produces the same result.
This is essential for anti-monotonicity of SemVal. -/

/-- concEval is monotone in fuel: if `concEval j e = ok v` and `j <= k`,
    then `concEval k e = ok v`. Less fuel can only cause outOfFuel, never
    a different result. -/
theorem concEval_fuel_mono {j k : Nat} {e v : Expr}
    (hjk : j ≤ k) (hev : concEval j e = .ok v) :
    concEval k e = .ok v := by
  induction j generalizing k e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    match k, hjk with
    | k + 1, hjk =>
    unfold concEval at hev ⊢
    split at hev
    · cases hev  -- bvar, error
    · cases hev; rfl  -- top
    · cases hev; rfl  -- lam
    · -- app case
      rename_i f a
      split at hev
      · rename_i fv av hf ha
        -- concEval n f = ok fv, concEval n a = ok av
        have hf' := ih (by omega : n ≤ k) hf
        have ha' := ih (by omega : n ≤ k) ha
        simp [hf', ha']
        split at hev
        · rename_i d b heq
          -- fv = lam d b, recursive call
          exact ih (by omega : n ≤ k) hev
        · cases hev  -- non-lambda, error
      · simp at hev  -- outOfFuel case
      · simp at hev
      · simp at hev
      · simp at hev

/-! ## Anti-monotonicity of SemVal

SemVal is anti-monotone in k: more steps = more observations = harder to satisfy.
If j <= k then SemVal k tau v -> SemVal j tau v. -/

theorem semVal_antimono : ∀ (j k : Nat) (τ v : Expr),
    j ≤ k → SemVal k τ v → SemVal j τ v := by
  intro j
  induction j with
  | zero =>
    intro k τ v _ h
    unfold SemVal
    exact semVal_isVal k τ v h
  | succ j ih =>
    intro k τ v hjk h
    match k, hjk with
    | k + 1, hjk =>
    match τ with
    | .top =>
      unfold SemVal at h ⊢
      exact h
    | .bvar n =>
      unfold SemVal at h
      exact absurd h id
    | .lam s t =>
      unfold SemVal at h ⊢
      obtain ⟨s', t', heq, hbody⟩ := h
      exact ⟨s', t', heq, fun j' hj' av hav i hi w hw =>
        hbody j' (by omega) av hav i hi w hw⟩
    | .app f a =>
      -- At k+1: SemVal (k+1) (app f a) v depends on concEval k (app f a)
      -- At j+1: SemVal (j+1) (app f a) v depends on concEval j (app f a)
      -- By fuel monotonicity: if concEval j = ok nf, then concEval k = ok nf.
      unfold SemVal at h ⊢
      split
      · -- concEval j (app f a) = ok τ_nf_j
        rename_i τ_nf_j hev_j
        split at h
        · -- concEval k (app f a) = ok τ_nf_k
          rename_i τ_nf_k hev_k
          -- By fuel mono: concEval j = ok τ_nf_j and j ≤ k, so concEval k = ok τ_nf_j
          -- But concEval k = ok τ_nf_k. So τ_nf_j = τ_nf_k.
          have := concEval_fuel_mono (show j ≤ k by omega) hev_j
          rw [this] at hev_k; cases hev_k
          -- Now τ_nf_j = τ_nf_k, and we need SemVal j τ_nf_j v from SemVal k τ_nf_k v
          exact ih k τ_nf_j v (by omega) h
        · -- concEval k (app f a) = outOfFuel or error
          -- But concEval j = ok τ_nf_j and j ≤ k, so concEval k = ok τ_nf_j.
          -- This contradicts the split.
          rename_i hev_k
          have := concEval_fuel_mono (show j ≤ k by omega) hev_j
          -- hev_k says concEval k ≠ ok, contradiction
          simp [this] at hev_k
      · -- concEval j (app f a) ≠ ok (outOfFuel or error)
        -- SemVal (j+1) (app f a) v = IsVal v
        -- Need to show IsVal v from whatever h is
        split at h
        · exact semVal_isVal k _ v h
        · exact h

/-! ## Semantic subtyping -/

/-- Semantic subtype relation: `SubSem a b` means for all step indices
    and all values, being in V(a) implies being in V(b). -/
def SubSem (a b : Expr) : Prop :=
  ∀ k v, SemVal k a v → SemVal k b v

/-- Semantic transitivity is FREE — just function composition.
    This is the property that makes the semantic approach powerful:
    the syntactic proof is stuck on transitivity elimination, but
    semantically it's trivial. -/
theorem subSem_trans {a b c : Expr} (h1 : SubSem a b) (h2 : SubSem b c) :
    SubSem a c :=
  fun k v hv => h2 k v (h1 k v hv)

/-- Semantic reflexivity. -/
theorem subSem_refl (a : Expr) : SubSem a a :=
  fun _ _ hv => hv

/-- Top is a semantic supertype of everything. -/
theorem subSem_top (a : Expr) : SubSem a .top :=
  fun k v hv => semVal_top k v (semVal_isVal k a v hv)

/-- **SubSem Top (lam s t) is False.**

    This is the semantic version of `top_not_sub_lam`.
    Proof: SubSem means forall k v, SemVal k Top v -> SemVal k (lam s t) v.
    Take k = 1, v = Top. SemVal 1 Top Top = IsVal Top = True.
    So SemVal 1 (lam s t) Top must hold.
    But top_not_in_semVal_lam says it is False. -/
theorem subSem_top_not_lam {s t : Expr} (h : SubSem .top (.lam s t)) : False :=
  top_not_in_semVal_lam 0 s t (h 1 .top (semVal_top 1 .top isVal_top))

/-! ## Values evaluate to themselves -/

theorem concEval_val (fuel : Nat) (v : Expr) (hv : IsVal v) (hfuel : fuel > 0) :
    concEval fuel v = .ok v := by
  rcases hv with rfl | ⟨d, b, rfl⟩
  · cases fuel with | zero => omega | succ n => simp [concEval]
  · cases fuel with | zero => omega | succ n => simp [concEval]

/-! ## Strong canonical forms -/

/-- If `e` is semantically typed at `lam s t` for ALL step indices,
    then evaluation always produces a lambda (never Top). -/
theorem sem_canonical_lam_strong {s t e v : Expr} (fuel : Nat)
    (hse : ∀ k, SemExpr k (.lam s t) e)
    (hev : concEval fuel e = .ok v) :
    ∃ d b, v = .lam d b := by
  have h := hse (fuel + 1) fuel (by omega) v hev
  simp only [show fuel + 1 - fuel = 1 from by omega] at h
  exact semVal_lam_is_lam h

/-! ## concEval only produces values -/

/-- concEval results are values (Top or lambda). Proved locally to avoid
    importing Soundness.lean (which carries the syntactic axioms). -/
private theorem concEval_isValue' {fuel : Nat} {e v : Expr}
    (hev : concEval fuel e = .ok v) :
    v = .top ∨ ∃ d b, v = .lam d b := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at hev
  | succ n ih =>
    unfold concEval at hev
    split at hev
    · exact absurd hev (by intro h; cases h)
    · cases hev; left; rfl
    · cases hev; right; exact ⟨_, _, rfl⟩
    · split at hev
      · rename_i fv av hf ha; split at hev
        · exact ih hev
        · cases hev
      · cases hev
      · cases hev
      · cases hev
      · cases hev

/-! ## Semantic expression type for Top -/

/-- Anything is semantically an expression of type Top. -/
theorem semExpr_top (k : Nat) (e : Expr) : SemExpr k .top e := by
  intro j hj v hev
  have hv := concEval_isValue' hev
  rcases hv with rfl | ⟨d, b, rfl⟩
  · exact semVal_top (k - j) .top isVal_top
  · exact semVal_top (k - j) (.lam d b) (isVal_lam d b)

/-! ## The fundamental theorem

### Statement (closed setting, Gamma = [])

    If `Sub [] e tau` and `Wf [] e`, then for all `k`, `SemExpr k tau e`.

### What this gives us

From the fundamental theorem + semantic canonical forms:
- `Wf [] (app f a)` gives `Sub [] f (lam s Top)` and `Wf [] f`.
- By fundamental theorem: `SemExpr k (lam s Top) f` for all k.
- If `concEval j f = ok fv`, then `fv` is in `SemVal (k-j) (lam s Top)`.
- For `k - j >= 1`, `semVal_lam_is_lam` forces fv to be a lambda.
- So `fv /= Top`, and the application can proceed.
- This replaces the syntactic `top_not_sub_lam` which has sorry!

### Proved cases (no sorry)
-/

/-- Fundamental theorem, Sub.top case: Sub [] e Top -> SemExpr k Top e. -/
theorem fundamental_top' (k : Nat) (e : Expr) :
    SemExpr k .top e := semExpr_top k e

/-- Fundamental theorem, Sub.refl case: Sub [] e e -> SemExpr k e e.

    For values, this needs the "identity extension" property:
    a value is in the semantic type of itself. For Top this is trivial.
    For lambdas, we need the body condition reflexively. -/
theorem fundamental_refl_top' (k : Nat) :
    SemExpr k .top .top := semExpr_top k .top

/-- Fundamental theorem, Sub.trans case.
    Given `SubSem m tau` and `SemExpr k m e`, derive `SemExpr k tau e`.

    **NOTE**: This is the step where the syntactic approach gets STUCK
    (trans + beta_L height composition, open since POPL 2010).
    Semantically, it is ONE LINE — set inclusion composes. -/
theorem fundamental_trans {k : Nat} {e m τ : Expr}
    (h1 : SemExpr k m e) (h2 : SubSem m τ) :
    SemExpr k τ e :=
  fun j hj v hev => h2 (k - j) v (h1 j hj v hev)

/-! ### Remaining cases (axiomatized)

The remaining Sub constructors (lam, beta_L, beta_R, app_cong, bvar)
need more work. We axiomatize the full theorem to show type safety follows.
-/

axiom fundamental_closed (e τ : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) (hsub : PSS.Sub [] e τ) :
    ∀ k, SemExpr k τ e

/-! ## Type safety -/

/-- **Type safety**: well-formed closed terms never get stuck.

    The proof uses semantic canonical forms (`semVal_lam_is_lam`)
    in the app case to show fv is a lambda. This replaces the
    sorry-carrying syntactic `top_not_sub_lam`.

    The one remaining sorry is for well-formedness of the substituted body
    `b.subst 0 av` in the recursive call. This requires domain inversion
    (`lam_sub_lam_inversion`) or an alternative route, which is a separate
    problem from canonical forms. -/
noncomputable def concEval_safe (k : Nat) (e : Expr)
    (hcl : e.closedAt 0 = true) (hwf : PSS.Wf [] e) :
    ∀ msg, concEval k e ≠ .error msg := by
  induction k generalizing e with
  | zero => simp [concEval]
  | succ n ih =>
    match e, hcl, hwf with
    | .bvar _, hcl, _ =>
      simp [Expr.closedAt, decide_eq_true_eq] at hcl
    | .top, _, _ => simp [concEval]
    | .lam _ _, _, _ => simp [concEval]
    | .app f a, hcl, hwf =>
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      match hwf with
      | .app (s := s) hwf_f hwf_a _hwf_s hsub_f_lam _hsub_a_s =>
        intro msg herr
        have hf_ne := ih f hcl.1 hwf_f
        have ha_ne := ih a hcl.2 hwf_a
        match hf_eq : concEval n f with
        | .error m => exact absurd hf_eq (hf_ne m)
        | .outOfFuel => simp [concEval, hf_eq] at herr
        | .ok fv =>
          match ha_eq : concEval n a with
          | .error m => exact absurd ha_eq (ha_ne m)
          | .outOfFuel => simp [concEval, hf_eq, ha_eq] at herr
          | .ok av =>
            simp [concEval, hf_eq, ha_eq] at herr
            -- *** SEMANTIC CANONICAL FORMS ***
            -- Sub [] f (lam s Top) and Wf [] f give SemExpr k (lam s Top) f
            have h_sem := fundamental_closed f (.lam s .top) hcl.1 hwf_f hsub_f_lam
            -- Pick index n + 2 so after using fuel n we get SemVal 2
            have hsv := h_sem (n + 2) n (by omega) fv hf_eq
            simp only [show n + 2 - n = 2 from by omega] at hsv
            -- hsv : SemVal 2 (lam s Top) fv
            -- By semVal_lam_is_lam: fv must be a lambda!
            have ⟨d, b, hfv_lam⟩ := semVal_lam_is_lam hsv
            subst hfv_lam
            -- Now herr : concEval n (b.subst 0 av) = error msg
            -- Need Wf [] (b.subst 0 av) for the recursive call.
            -- This requires lam_sub_lam_inversion or an alternative.
            -- (Separate problem from canonical forms — sorry for now.)
            sorry

/-! ## Summary of what the semantic approach achieves

### Fully proved (zero sorry):

| Theorem | Role |
|---------|------|
| `top_not_in_semVal_lam` | Semantic canonical forms: Top not in V(lam s t) |
| `semVal_lam_is_lam` | Values in V(lam s t) are lambdas |
| `subSem_trans` | Transitivity composes for free |
| `subSem_top_not_lam` | SubSem Top (lam s t) is False |
| `sem_canonical_lam_strong` | Universal canonical forms |
| `semVal_top`, `semVal_isVal` | Basic semantic properties |
| `semExpr_top` | Everything is in E(Top) |
| `concEval_fuel_mono` | concEval is monotone in fuel |
| `semVal_antimono` | SemVal is anti-monotone in step index |
| `fundamental_trans` | Trans case of fundamental theorem (1 line!) |

### Axioms used (separate from the trans + beta_L problem):

| Axiom | Status |
|-------|--------|
| `fundamental_closed` | Main open obligation; trans case is trivial |

### Sorrys (1 total):

| Location | Issue |
|----------|-------|
| `concEval_safe` (body Wf) | Needs domain inversion or alternative |

### Comparison with syntactic approach (`CanonicalForms.lean`):

The syntactic approach has sorry in `top_not_sub_lam` and `lam_sub_lam_inversion`,
both caused by the trans + beta_L height composition obstacle. This is a
FUNDAMENTAL problem with the declarative Sub rules that has been open since 2010.

The semantic approach:
- **Eliminates** the `top_not_sub_lam` sorry entirely (definitional in SemVal)
- **Eliminates** the transitivity obstacle (subSem_trans is trivial)
- **Retains** the `lam_sub_lam_inversion` dependency (only for body Wf, not canonical forms)
- **Adds** new obligations (fundamental theorem, concEval determinism) that are
  standard and orthogonal to the trans + beta_L problem

### Path to completion:

1. [DONE] Prove concEval fuel monotonicity (`concEval_fuel_mono`)
2. [DONE] Close semVal_antimono using fuel monotonicity
3. Prove the fundamental theorem by induction on Sub:
   - trans: `fundamental_trans` (DONE — one line!)
   - top: `fundamental_top'` / `semExpr_top` (DONE)
   - refl: identity extension (standard logical relation obligation)
   - lam: domain/body compatibility (standard)
   - beta_L/R: concEval normalization (needs concEval facts)
   - app_cong: evaluation congruence (needs concEval congruence)
4. Close `concEval_safe` body Wf via one of:
   (a) Prove `lam_sub_lam_inversion` syntactically (still hard), OR
   (b) Derive body Wf from the semantic interpretation directly, OR
   (c) Restructure `concEval_safe` to avoid needing body Wf explicitly
-/

end PSS.LogRel
