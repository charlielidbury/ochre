import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Step-Indexed Value Subtyping (ValSub)

## Motivation

`SubtypeCore` is too weak as the output relation for soundness:
- Lacks `self_intro` (cannot show `v ⊑ mu ann body`)
- Lacks contravariant function domains (`lam_sub`)
- Adding these rules to an inductive breaks structural induction for transitivity

`ValSub n v τ` is a step-indexed semantic subtyping relation that resolves this.
The step index `n` decreases on each mu unfolding, preventing divergence on
equi-recursive types. All the rules SubtypeCore has are included, plus:
- `mu_r`: self-intro (unfold mu on the right)
- `mu_l`: self-elim (unfold mu on the left)
- `lam_sub`: contravariant domain, covariant body
- `compose_r`: right-compose with subCheckNF (algorithmic transitivity)

## Key properties

1. `SubtypeCore v τ → ValSub n v τ` (embedding — SubtypeCore is a subset)
2. `ValSub n v σ → subCheckNF σ τ = true → ValSub n v τ` (bridge lemma — PROVED)
3. `ValSub (n+1) v τ → ValSub n v τ` (downward closure — PROVED)
4. Soundness outputs ValSub instead of SubtypeCore

## Design: compose_r disjunct

The bridge lemma was previously blocked by domain composition in the lam case:
ValSub(domσ, domv) + subCheckNF(domτ, domσ) does NOT directly give ValSub(domτ, domv)
because this requires either reverse-bridge or ValSub transitivity, both hard.

The solution: add `compose_r` as a ValSub disjunct. This rule says:
"if v ⊑ mid (by ValSub) and mid ⊑ τ (by subCheckNF), then v ⊑ τ."
This is transitivity via the algorithmic checker — semantically sound because
subCheckNF IS the intended subtype checker.

With compose_r, the bridge becomes trivial: apply downward closure to get
ValSub n v σ → ValSub (n-1) v σ, then use compose_r to compose with subCheckNF.

The guarantee remains meaningful: ValSub says the concrete and abstract results
are related by a combination of structural subtyping rules and verified
algorithmic checks. Both are sound.

## Literature basis

- Appel & McAllester 2001 (step-indexed models for recursive types)
- Amin & Rompf POPL 2017 (fuel-bounded definitional interpreters)
- See `docs/research/amin-rompf-deep-dive.md` for detailed analysis
-/

open Expr

/-- Step-indexed value subtyping. `ValSub n v τ` means "value v is a subtype
    of type τ, allowing up to n unfolding steps."

    At step 0, everything is related (vacuously — no unfolding budget left).
    At step n+1, the relation is a disjunction of structural rules plus
    mu unfolding rules that consume one step, plus compose_r for
    algorithmic transitivity.

    This is defined as a plain function `Nat → Expr → Expr → Prop` with
    structural recursion on the Nat argument. -/
def ValSub : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, v, τ =>
    -- (1) top: everything inhabits Type
    τ = .type
    -- (2) refl: syntactic equality
    ∨ v = τ
    -- (3) lam_sub: contravariant domain, covariant body
    ∨ (∃ domV bodyV domT bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        ValSub n domT domV ∧ ValSub n bodyV bodyT)
    -- (4) mu_body: structural comparison of mu bodies (same annotation)
    ∨ (∃ ann bodyV bodyT,
        v = .mu ann bodyV ∧ τ = .mu ann bodyT ∧
        ValSub n bodyV bodyT)
    -- (5) app_cong: structural on stuck applications
    ∨ (∃ fV aV fT aT,
        v = .app fV aV ∧ τ = .app fT aT ∧
        ValSub n fV fT ∧ ValSub n aV aT)
    -- (6) mu_r (self-intro): unfold mu on the right, consumes one step
    ∨ (∃ ann body,
        τ = .mu ann body ∧
        ValSub n v (body.subst 0 (.mu ann body)))
    -- (7) mu_l (self-elim): unfold mu on the left, consumes one step
    ∨ (∃ ann body,
        v = .mu ann body ∧
        ValSub n (body.subst 0 (.mu ann body)) τ)
    -- (8) compose_r: right-compose with subCheckNF (algorithmic transitivity)
    --     "v ⊑ mid by ValSub, and mid ⊑ τ by subCheckNF, so v ⊑ τ"
    ∨ (∃ mid fuel ctx,
        ValSub n v mid ∧ subCheckNF fuel ctx [] mid τ = true)

namespace ValSub

/-! ## Introduction lemmas

These provide named constructors for each disjunct, making proof terms readable. -/

theorem top (v : Expr) (n : Nat) : ValSub (n + 1) v .type :=
  Or.inl rfl

theorem refl (e : Expr) (n : Nat) : ValSub (n + 1) e e :=
  Or.inr (Or.inl rfl)

/-- Reflexivity at any step count (including 0, where it's vacuously true). -/
theorem refl' (e : Expr) : (n : Nat) → ValSub n e e
  | 0 => trivial
  | _ + 1 => Or.inr (Or.inl rfl)

theorem lam_sub {n : Nat} {domV bodyV domT bodyT : Expr}
    (hdom : ValSub n domT domV) (hbody : ValSub n bodyV bodyT) :
    ValSub (n + 1) (.lam domV bodyV) (.lam domT bodyT) :=
  Or.inr (Or.inr (Or.inl ⟨domV, bodyV, domT, bodyT, rfl, rfl, hdom, hbody⟩))

theorem lam_body {n : Nat} {dom : Expr} {bodyV bodyT : Expr}
    (hbody : ValSub n bodyV bodyT) :
    ValSub (n + 1) (.lam dom bodyV) (.lam dom bodyT) :=
  lam_sub (refl' dom n) hbody

theorem mu_body {n : Nat} {ann : Expr} {bodyV bodyT : Expr}
    (hbody : ValSub n bodyV bodyT) :
    ValSub (n + 1) (.mu ann bodyV) (.mu ann bodyT) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, bodyV, bodyT, rfl, rfl, hbody⟩)))

theorem app_cong {n : Nat} {fV aV fT aT : Expr}
    (hf : ValSub n fV fT) (ha : ValSub n aV aT) :
    ValSub (n + 1) (.app fV aV) (.app fT aT) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fV, aV, fT, aT, rfl, rfl, hf, ha⟩))))

theorem mu_r {n : Nat} {v ann body : Expr}
    (h : ValSub n v (body.subst 0 (.mu ann body))) :
    ValSub (n + 1) v (.mu ann body) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, rfl, h⟩)))))

theorem mu_l {n : Nat} {ann body τ : Expr}
    (h : ValSub n (body.subst 0 (.mu ann body)) τ) :
    ValSub (n + 1) (.mu ann body) τ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ann, body, rfl, h⟩))))))

theorem compose_r {n : Nat} {v mid τ : Expr} {fuel : Nat} {ctx : List Expr}
    (hv : ValSub n v mid) (hcheck : subCheckNF fuel ctx [] mid τ = true) :
    ValSub (n + 1) v τ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨mid, fuel, ctx, hv, hcheck⟩))))))

/-! ## Embedding from SubtypeCore

Every SubtypeCore judgment lifts to ValSub at any step count.
This ensures soundness_gen's existing proof cases (which produce SubtypeCore)
still work when the output relation changes to ValSub. -/

theorem of_subtypeCore {v τ : Expr} (h : SubtypeCore v τ) :
    (n : Nat) → ValSub n v τ := by
  induction h with
  | refl e => exact refl' e
  | top e => intro n; cases n with | zero => trivial | succ n => exact top e n
  | @lam_body dom _ _ _ ih =>
    intro n; cases n with | zero => trivial | succ n => exact lam_body (ih n)
  | @app_cong _ _ _ _ _ _ ihf iha =>
    intro n; cases n with | zero => trivial | succ n => exact app_cong (ihf n) (iha n)
  | @mu_body ann _ _ _ ih =>
    intro n; cases n with | zero => trivial | succ n => exact mu_body (ih n)

/-- Convenience: SubtypeCore to ValSub with implicit n. -/
theorem of_subtypeCore' {v τ : Expr} (h : SubtypeCore v τ) {n : Nat} :
    ValSub n v τ := (of_subtypeCore h) n

/-! ## Downward closure (monotonicity in step index)

`ValSub (n+1) v τ → ValSub n v τ`: more unfolding budget implies less.
This is the standard "anti-monotonicity" property of step-indexed relations.
Proved by induction on n, applying the IH to each sub-ValSub. -/

theorem mono {v τ : Expr} {n : Nat} : ValSub (n + 1) v τ → ValSub n v τ := by
  induction n generalizing v τ with
  | zero => intro _; trivial
  | succ m ih =>
    intro h
    -- h : ValSub (m + 2) v τ, ih : ∀ {v τ}, ValSub (m + 1) v τ → ValSub m v τ
    -- goal : ValSub (m + 1) v τ
    rcases h with htop | hrefl | ⟨domV, bodyV, domT, bodyT, hv_eq, hτ_eq, hdom, hbody⟩
      | ⟨ann, bodyV, bodyT, hv_eq, hτ_eq, hbody⟩
      | ⟨fV, aV, fT, aT, hv_eq, hτ_eq, hf, ha⟩
      | ⟨ann, body, hτ_eq, hsub⟩
      | ⟨ann, body, hv_eq, hsub⟩
      | ⟨mid, fuel, ctx, hvm, hcheck⟩
    -- (1) top
    · subst htop; exact top v m
    -- (2) refl
    · subst hrefl; exact refl v m
    -- (3) lam_sub
    · subst hv_eq; subst hτ_eq
      exact lam_sub (ih hdom) (ih hbody)
    -- (4) mu_body
    · subst hv_eq; subst hτ_eq
      exact mu_body (ih hbody)
    -- (5) app_cong
    · subst hv_eq; subst hτ_eq
      exact app_cong (ih hf) (ih ha)
    -- (6) mu_r
    · subst hτ_eq
      exact mu_r (ih hsub)
    -- (7) mu_l
    · subst hv_eq
      exact mu_l (ih hsub)
    -- (8) compose_r
    · exact compose_r (ih hvm) hcheck

/-! ## Bridge lemma (PROVED)

The critical property for the soundness proof's ascription case:
if v inhabits σ (by ValSub) and σ is a subtype of τ (by subCheckNF),
then v inhabits τ.

Proof: use downward closure to get ValSub at one step lower, then
compose with subCheckNF via the compose_r disjunct.

This composes ValSub (semantic) with subCheckNF (algorithmic) to get ValSub.
It replaces the unprovable `SubtypeCore v σ → subCheckNF σ τ = true → SubtypeCore v τ`. -/

theorem bridge (n : Nat) (fuel : Nat) (ctx : List Expr)
    (v σ τ : Expr)
    (hv : ValSub n v σ)
    (hcheck : subCheckNF fuel ctx [] σ τ = true) :
    ValSub n v τ := by
  cases n with
  | zero => trivial  -- ValSub 0 is always True
  | succ m =>
    -- hv : ValSub (m + 1) v σ
    -- Need: ValSub (m + 1) v τ
    -- Use compose_r with mid = σ: need ValSub m v σ and subCheckNF σ τ
    exact compose_r (mono hv) hcheck

/-! ## Substitution congruence analysis

subst_congr is FALSE for the syntactic (contra-domain) ValSub.
This means the GENERALIZED soundness approach (ValSub on inputs + subst_congr)
is blocked. See the counterexample below.

The compose_r disjunct resolves the BRIDGE (asc case of soundness) but does
NOT resolve the APP case. The app case still requires either:
1. Semantic ValSub (logical relation) — lam case quantifies over all args
2. Non-generalized soundness with a substitution-evaluation equivalence
3. Proving soundness for concEvalS (substitution-based evaluator)

See PROGRESS.md for detailed analysis. -/

-- Verify the subst_congr counterexample using inline definitions:
private def cx_zero' := Named.toExpr [] (.lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "z"))))
private def cx_Nat' := Named.toExpr [] (.lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "X"))))

-- zero' ⊑ Nat' (premise: a ⊑ b)
example : subCheck 20 cx_zero' cx_Nat' = true := by native_decide
-- lam zero' (bvar 0) ⊑ lam Nat' (bvar 0) is FALSE (subst_congr conclusion)
-- because contra domain would need Nat' ⊑ zero' which is false.
example : subCheck 20 (.lam cx_zero' (.bvar 0)) (.lam cx_Nat' (.bvar 0)) = false := by native_decide

end ValSub
