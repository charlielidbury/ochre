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

## Key properties

1. `SubtypeCore v τ → ValSub n v τ` (embedding — SubtypeCore is a subset)
2. `ValSub n v σ → subCheckNF σ τ = true → ValSub n' v τ` (bridge lemma — TODO)
3. Soundness outputs ValSub instead of SubtypeCore

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
    mu unfolding rules that consume one step.

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
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ann, body, rfl, h⟩)))))

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

/-! ## Bridge lemma (TODO)

The critical property for the soundness proof's ascription case:
if v inhabits σ (by ValSub) and σ is a subtype of τ (by subCheckNF),
then v inhabits τ.

This composes ValSub (semantic) with subCheckNF (algorithmic) to get ValSub.
It replaces the unprovable `SubtypeCore v σ → subCheckNF σ τ = true → SubtypeCore v τ`.

Proof strategy: by induction on n (the ValSub step index), case-splitting on
how subCheckNF establishes σ ⊑ τ. Each subCheckNF case (lam, mu-unfold,
equality, top) corresponds to a ValSub rule. The step index decreases on
mu unfolding, preventing divergence. -/

/-
ANALYSIS OF WHY THE BRIDGE IS HARD (2026-04-02):

The lam case requires composing ValSub with subCheckNF in BOTH directions:
- Bodies (covariant): ValSub bodyv bodyσ + subCheckNF bodyσ bodyτ → ValSub bodyv bodyτ
  This IS a recursive bridge call. ✓
- Domains (contravariant): ValSub domσ domv + subCheckNF domτ domσ → ValSub domτ domv
  This requires a REVERSE bridge: subCheckNF(a,b) + ValSub(b,c) → ValSub(a,c)
  OR: transitivity of ValSub + soundness of subCheckNF into ValSub.
  Both are research-level problems.

The mu cases should work: mu unfolding consumes a step index, and subCheckNF
also unfolds mus, so the recursive structure aligns.

POSSIBLE ALTERNATIVE: Semantic ValSub (logical relation approach)
Instead of syntactic disjunction, define the lam case as:
  ValSub n (lam domv bodyv) (lam domτ bodyτ) :=
    ∀ m < n, ∀ av aτ, ValSub m av domτ → ValSub m av domv →
      ∀ rv, concEval m [] (bodyv.subst 0 av) = some rv →
      ∀ rτ, absEval m [] (bodyτ.subst 0 aτ) = some rτ →
      ValSub m rv rτ
This makes the app case trivial (just instantiate the quantifier) and
the bridge's lam case becomes: "if an arg satisfies domτ, it satisfies
domσ (since domτ ⊑ domσ), so we can use the ValSub v σ quantifier."
The downside: requires evaluator in the relation definition.
See docs/research/amin-rompf-deep-dive.md §7 for discussion.
-/

-- The bridge lemma is sorry'd pending resolution of the domain composition
-- problem described above. Future agents should consider the semantic
-- approach (logical relation) as an alternative to the syntactic bridge.
--
-- Easy cases (σ=τ, τ=Type) work. The lam case is the blocker.
-- See the analysis above for details.
theorem bridge (n : Nat) (fuel : Nat) (ctx : List Expr)
    (v σ τ : Expr)
    (hv : ValSub n v σ)
    (hcheck : subCheckNF fuel ctx [] σ τ = true) :
    ValSub n v τ := by
  -- Easy case: if σ = τ, we already have ValSub n v σ = ValSub n v τ
  -- subCheckNF handles this via the `if a == b` check.
  -- Hard cases: lam (domain composition), mu (mu unfolding), inferType
  sorry

/-! ## Substitution congruence (TODO)

Needed for the generalized soundness theorem. If v ⊑ τ and a ⊑ b,
then e[j:=v] ⊑ e[j:=τ] (congruence under substitution).

This is the step-indexed analogue of the substitution lemma that
SubtypeCore cannot prove (because lam_body requires equal domains). -/

/-
SUBST_CONGR IS FALSE for the syntactic (contra-domain) ValSub.

Counterexample:
  e = lam (bvar 0) (bvar 1)     — lambda whose domain is the substituted variable
  a = zero'                       — a concrete value
  b = Nat'                        — a type (zero' ⊑ Nat')
  ValSub n a b holds (zero ⊑ Nat).

  e.subst 0 a = lam zero' (bvar 0)
  e.subst 0 b = lam Nat'  (bvar 0)

  For lam zero' bdy ⊑ lam Nat' bdy, lam_sub requires Nat' ⊑ zero' (contra domain).
  But Nat' is NOT ⊑ zero' — it's the wrong direction. So the conclusion is FALSE.

This means the GENERALIZED soundness approach (ValSub on inputs + subst_congr)
is blocked. The generalized soundness needs a different proof technique.

Options:
1. Semantic ValSub (logical relation) — lam case quantifies over all args,
   avoiding substitution congruence entirely
2. Return to env-based beta (requires closures for de Bruijn)
3. Prove non-generalized soundness with a different treatment of the app case

See the bridge lemma analysis above for more details.
-/

-- Verify the subst_congr counterexample using inline definitions:
private def cx_zero' := Named.toExpr [] (.lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "z"))))
private def cx_Nat' := Named.toExpr [] (.lam "X" .type (.lam "z" (.var "X") (.lam "s" (.lam "_" (.var "X") (.var "X")) (.var "X"))))

-- zero' ⊑ Nat' (premise: a ⊑ b)
example : subCheck 20 cx_zero' cx_Nat' = true := by native_decide
-- lam zero' (bvar 0) ⊑ lam Nat' (bvar 0) is FALSE (subst_congr conclusion)
-- because contra domain would need Nat' ⊑ zero' which is false.
example : subCheck 20 (.lam cx_zero' (.bvar 0)) (.lam cx_Nat' (.bvar 0)) = false := by native_decide

end ValSub
