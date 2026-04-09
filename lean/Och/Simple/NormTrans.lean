import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Properties

/-!
# Normalization-based transitivity exploration

Research file exploring whether transitivity of Sub can be proved via
normalization, enabling Mu-R and BetaR.

## The problem

Current transitivity proof uses cut-formula elimination — induction on
the complexity of the middle term `b`. This breaks with muR and muUnfoldL
because `b.subst 0 (mu A b)` can have arbitrarily larger complexity than `mu A b`.

## Approach 1: Normalize then compare

Define `nf : Fuel → Expr → Expr` that reduces:
- Beta-redexes: `(lam D body) a → body.subst 0 a`
- μ-unfolding: `mu A body → body.subst 0 (mu A body)`
- Ascription erasure: `asc e ty → e`

Then prove: `Sub Γ a b → NfSub Γ (nf n a) (nf n b)` where NfSub is a
trivially-transitive structural comparison on normal forms.

## Approach 2: Direct transitivity via fuel

Prove: `Sub Γ a b → Sub Γ b c → Sub Γ a c` by well-founded induction on
something OTHER than complexity — e.g., a fuel-indexed measure that
accounts for mu unfolding depth.

## Approach 3: Semantic model

Interpret types as sets, Sub as subset inclusion. Transitivity follows
from the model. Recover Sub from the semantic relation.
-/

set_option autoImplicit false

namespace Och.Simple.NormTrans

open Expr

-- ============================================================
-- Approach 1: Normalization to weak head normal form
-- ============================================================

/-- Normalize to weak head normal form. This is essentially the same as `eval`
    but applied to the subtyping problem rather than runtime execution.
    The key operations:
    - Unfold mu: mu A body → body.subst 0 (mu A body)
    - Beta-reduce: app (lam D body) a → body.subst 0 a
    - Erase ascriptions: asc e ty → e
    Variables, lambdas, top, and stuck applications are already in WHNF. -/
def whnf (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e  -- out of fuel, return as-is
  | fuel + 1 =>
    match e with
    | .var n => .var n
    | .top => .top
    | .lam dom body => .lam dom body  -- lambdas are values
    | .app f a =>
      let f' := whnf fuel f
      match f' with
      | .lam _dom body => whnf fuel (body.subst 0 a)
      | _ => .app f' a
    | .asc e _ty => whnf fuel e
    | .mu ann body => whnf fuel (body.subst 0 (.mu ann body))

-- ============================================================
-- Structural comparison on WHNF (NfSub)
-- ============================================================

/-- Structural subtyping on expressions assumed to be in WHNF.
    This relation is trivially transitive because it only compares
    structural components (no computation steps). -/
inductive NfSub : Ctx → Expr → Expr → Prop where
  /-- Syntactic equality implies structural subtyping -/
  | refl (Γ : Ctx) (a : Expr) : NfSub Γ a a
  /-- Everything is a subtype of top -/
  | top (Γ : Ctx) (a : Expr) : NfSub Γ a .top
  /-- Variable lookup -/
  | var (Γ : Ctx) (x : Nat) (T b : Expr) :
      Ctx.get? Γ x = some T →
      NfSub Γ T b →
      NfSub Γ (.var x) b
  /-- Lambda structural comparison (contravariant domain, covariant body) -/
  | lam (Γ : Ctx) (A B b₁ b₂ : Expr) :
      NfSub Γ B A →
      NfSub (B :: Γ) b₁ b₂ →
      NfSub Γ (.lam A b₁) (.lam B b₂)

-- ============================================================
-- Transitivity of NfSub (should be straightforward)
-- ============================================================

/-- Transitivity of NfSub.
    This should be provable by the SAME technique as the current Sub.trans
    (lexicographic on b.complexity + derivation sizes), since NfSub has no
    rules that inflate complexity (no app, no mu, no asc). -/
theorem NfSub.trans {Γ : Ctx} {a b c : Expr}
    (hab : NfSub Γ a b) (hbc : NfSub Γ b c) : NfSub Γ a c := by
  sorry  -- TODO: prove this. Should be easy given the simple structure.

-- ============================================================
-- The hard part: connecting Sub to NfSub via normalization
-- ============================================================

/-- If Sub Γ a b holds, then after normalizing both sides, the
    structural comparison holds. -/
theorem sub_implies_nfsub_of_whnf {Γ : Ctx} {a b : Expr}
    (hsub : Sub Γ a b) (fuel : Nat) :
    NfSub Γ (whnf fuel a) (whnf fuel b) := by
  sorry  -- This is the main research question

-- ============================================================
-- Alternative: Direct fuel-based transitivity
-- ============================================================

-- An alternative approach: prove transitivity directly by induction on
-- a fuel parameter that bounds the number of mu-unfoldings needed.
--
-- The idea: if Sub Γ a b uses at most n mu-unfoldings on b,
-- and Sub Γ b c uses at most m mu-unfoldings on b,
-- then Sub Γ a c can be derived (potentially with more unfoldings).
--
-- This avoids the complexity measure entirely.

-- First question: can we even define a useful "unfolding depth" for Sub?
-- The mu rule: mu A b ⊑ c requires A ⊑ c (no unfolding) and A::Γ ⊢ b ⊑ A↑
-- The muUnfoldL rule: mu A b ⊑ c requires body.subst 0 (mu A b) ⊑ c (one unfolding)
-- The muR rule: a ⊑ mu A b requires a ⊑ body.subst 0 a (one unfolding)

-- The challenge with transitivity:
-- hab = muR: a ⊑ body.subst 0 a, so b = mu A body
-- hbc = mu: mu A body ⊑ c via A ⊑ c
-- We need: a ⊑ c
-- We have: a ⊑ body.subst 0 a (from muR)
-- We need: body.subst 0 a ⊑ something ⊑ c
-- From mu's body premise: A :: Γ ⊢ body ⊑ A↑
-- By subst with a: body.subst 0 a ⊑ A (when a ⊑ A)
-- But we don't know a ⊑ A directly...

-- Actually, from mu we have A ⊑ c. And from the body premise of mu,
-- we can derive (with substitution lemma): body.subst 0 (mu A body) ⊑ A.
-- But we need body.subst 0 a ⊑ A, which requires a ⊑ mu A body (circular!)

-- This suggests the direct approach doesn't work either.
-- The normalization approach might be the only way.

-- ============================================================
-- Exploration: What exactly breaks in the sorry'd cases?
-- ============================================================

-- Let's catalog the sorry'd transitivity cases:
--
-- 1. trans(top, muR):
--    hab: a ⊑ top (so b = top)
--    hbc: top ⊑ mu A body (muR, so body.subst 0 top ⊑ mu A body... wait no)
--    hbc: top ⊑ body.subst 0 top, c = mu A body
--    Need: a ⊑ mu A body
--    We could try: a ⊑ top ⊑ body.subst 0 top (by transitivity on body.subst 0 top)
--    But body.subst 0 top has larger complexity than top = b, so we can't recurse!
--
-- 2. trans(lam, muR):
--    hab: lam A body_a ⊑ lam B body_b (so b = lam B body_b)
--    hbc: lam B body_b ⊑ body_mu.subst 0 (lam B body_b), c = mu A_mu body_mu
--    Need: lam A body_a ⊑ mu A_mu body_mu
--    Similar issue: can't recurse on body_mu.subst 0 (lam A body_a)
--
-- 3. trans(muR, mu):
--    hab: a ⊑ body.subst 0 a (muR, b = mu A body)
--    hbc: mu A body ⊑ c (mu rule, A ⊑ c)
--    Need: a ⊑ c
--    If we could show a ⊑ A, we'd be done (by trans on A ⊑ c).
--    From mu's body premise: A::Γ ⊢ body ⊑ A↑
--    Substituting: body.subst 0 a ⊑ A (if a ⊑ A, which is what we want...)
--
-- 4. trans(muR, muUnfoldL):
--    hab: a ⊑ body.subst 0 a (muR, b = mu A body)
--    hbc: body.subst 0 (mu A body) ⊑ c (muUnfoldL)
--    Need: a ⊑ c
--    We'd need: body.subst 0 a ⊑ body.subst 0 (mu A body) ⊑ c
--    But the first step requires "monotonicity of body.subst 0 _" which isn't free.
--
-- 5. trans(muR, muR):
--    hab: a ⊑ body1.subst 0 a (b = mu A1 body1)
--    hbc: mu A1 body1 ⊑ body2.subst 0 (mu A1 body1) (c = mu A2 body2)
--    Need: a ⊑ mu A2 body2
--    Would need: a ⊑ body2.subst 0 a (to use muR again)
--
-- ALL of these cases involve the fundamental problem:
-- substitution is not monotone with respect to ⊑ in general.
-- That is, a ⊑ b does NOT imply body.subst 0 a ⊑ body.subst 0 b.
--
-- Wait, actually substitution IS monotone — that's the subst_lemma!
-- Sub.subst_lemma: Sub (T::Γ) a b → Sub Γ v T → Sub Γ (a.subst 0 v) (b.subst 0 v)
-- This substitutes the SAME value into both sides.
--
-- What we actually need is: a ⊑ b → body.subst 0 a ⊑ body.subst 0 b
-- i.e., substitution is COVARIANT in the substituted value.
-- This is NOT the subst_lemma! The subst_lemma substitutes the same v into a and b.
-- We want to substitute DIFFERENT values (a vs b) into the same body.
--
-- This is a separate lemma: "substitution respects Sub in the value"
-- Sub Γ a b → Sub (T::Γ) body body → Sub Γ (body.subst 0 a) (body.subst 0 b)
-- But this requires body ⊑ body (which is just refl) and more importantly
-- it requires a ⊑ b (which we have from transitivity's premise).
-- Actually, the right formulation: given body in context T::Γ,
-- if a ⊑ T and b ⊑ T and a ⊑ b, then body.subst 0 a ⊑ body.subst 0 b.
-- This is NOT obviously true because body might use var 0 in contravariant position!
-- Example: body = lam (var 0) top. Then body.subst 0 a = lam a top, body.subst 0 b = lam b top.
-- Sub (lam a top) (lam b top) requires b ⊑ a (contravariant!).
-- So if a ⊑ b, we'd need b ⊑ a, which is only true if a = b.
-- Therefore: substitution is NOT covariant in the value in general.
--
-- This means the normalization approach needs to be more careful.
-- We can't just "normalize both sides and compare" because the
-- normalization of different sides may require different substitutions.

-- ============================================================
-- Key insight: the problem is fundamentally about COINDUCTION
-- ============================================================

-- The mu/self-type pattern is inherently coinductive:
-- mu A body ≈ body.subst 0 (mu A body) (infinite unfolding)
-- This is like a greatest fixpoint.
--
-- Transitivity for coinductive types typically requires a
-- BISIMULATION argument, not a simple structural induction.
--
-- Idea: define a "simulation relation" R such that:
-- 1. Sub Γ a b implies (a, b) ∈ R
-- 2. R is closed under one-step unfolding on both sides
-- 3. R implies Sub
--
-- This is essentially the "step-indexed logical relation" approach.

end Och.Simple.NormTrans
