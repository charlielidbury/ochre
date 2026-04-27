import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.EvalSubst
import Och.Std.Unit
import Och.Std.DBool

/-!
# Soundness (Phase 2 — sorry-preserved scaffolds)

Top-level theorem statements that record the soundness goal for
the algorithmic subtype-checking pipeline. All bodies are
`sorry`d; the engine-collapse refactor (2026-04-27,
`docs/ideas/engine-collapse.md`) shelved the env-NbE substrate
that the previous proof attempt (`SoundnessProof.lean`,
~6K LOC, deleted) was built on.

Re-proving against the substitution-based engine
(`SubstEval.subCheckT`) is a separate research effort. The
statements here are the *targets* — phrased against the public
API and the declarative `Subtype'` relation in
`Subtyping.lean`, both of which are substrate-agnostic.

## Architecture (target)

  algorithmic       declarative
  `subCheckT`   ⟶   `Subtype'`

The algorithmic side is `SubstEval.subCheckT` — the production
entry point post-engine-collapse. The declarative side is the
inductive-up-to (seen-indexed) `Subtype'` defined in
`Subtyping.lean`.

## Open design questions

- **A2 (type-in-type)**: the model takes `⟦Type⟧` to be the
  full value universe, accepting `Type : Type`. A predicative
  variant would index `Subtype'` and the model by a level.
  Deferred — Och is a core calculus, not a foundation.

- **Coinduction**: the seen-set discipline is Brandt-Henglein
  style. The declarative counterpart is a coinductive
  `Subtype'` (or an inductive one quotiented by the gfp). Lean
  4's coinductive support is limited; the inductive-up-to
  encoding from `Simple/` may port directly.
-/

namespace Och.Soundness

/-!
## Top-level statements

These are *targets*, not yet proofs. Each `sorry` here is a
soundness obligation. They are stated against the public API
so that downstream work can quantify over them.
-/

/-- The soundness theorem: if the substitution-based subtype
check accepts `e ⊑ τ`, then `e ⊑ τ` declaratively (against the
substrate-agnostic `Subtype'` relation in `Subtyping.lean`).

The previous env-NbE-based proof attempt (`SoundnessProof.lean`,
deleted in the engine-collapse refactor) built on a Val-level
intermediate relation `SubV` and an RC predicate substrate; both
hit structural walls that don't transfer to the substitution
substrate. Substitution-based proofs build on different lemmas
(substitution lemmas, not reducibility candidates), so this is
a fresh proof effort. -/
theorem subCheckT_sound
    {fuel : Nat} {e τ : Expr}
    (h : SubstEval.subCheckT fuel e τ = .ok true) :
    Subtype' [] [] e τ := sorry

/-- `concEval` (the reference evaluator) preserves declarative
subtyping. If `e ⊑ τ` holds and `e` evaluates to `e'`, then
`e' ⊑ τ` too. Standard preservation, phrased against the
substrate-agnostic `Subtype'`. -/
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ := sorry

/-- End-to-end soundness: a well-checked term evaluates to
something that still inhabits its declared type. Combines
`subCheckT_sound` and `concEval_preservation`. -/
theorem soundness
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hcheck : SubstEval.subCheckT fuel e τ = .ok true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ := sorry

section Witnesses
open Std

/-- `unit_ ⊑ Unit_`. Same shape: `unit_ = λX. λu:X. u`,
`Unit_ = λX. λu:X. X`, body `u ⊑ X` via `.bvar`. -/
example : Subtype' [] [] unit_ Unit_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 0) (τ := .bvar 0) rfl

/-!
The flagship coinductive case (SoundnessAudit A4): `dtrue ⊑ dBool`
fully derived. With the very-dependent encoding (no per-constructor
`fix`), the derivation is shorter than the `e08bce9` form: `dtrue`
is already an `.iota`, so there's no `.unfold_fix_L` step, and after
`unfold_iota_L` substitutes `self ↦ dtrue` the LHS `t`-domain is
already `P dtrue` (matching the RHS by `.refl` — previously it was
`P dtrueIota` and needed `app_cong` + two fix-unfolds).
-/

private def dBoolIota : Expr :=
  .iota dBool
    (.lam (.lam dBool .type)
      (.lam (.app (.bvar 0) dtrue)
        (.lam (.app (.bvar 1) dfalse)
          (.app (.bvar 2) (.bvar 3)))))

private def bodyRHS : Expr :=
  .lam (.lam dBool .type)
    (.lam (.app (.bvar 0) dtrue)
      (.lam (.app (.bvar 1) dfalse)
        (.app (.bvar 2) dtrue)))

private def dtrueLam : Expr :=
  .lam (.lam dtrue .type)
    (.lam (.app (.bvar 0) dtrue)
      (.lam .type (.bvar 1)))

/-- `dtrue ⊑ dBool`. Constructor path:

  `unfold_fix_R` → `iota_intro` (annotation via `.hyp`) →
  `unfold_iota_L` → `lam`³ →
    P-domain contra: `lam`(`.hyp`, `.refl`)
    t-domain contra: `.refl`         ← was app_cong + 2 fix-unfolds
    f-domain contra: `.top`
    body: `.bvar`

Both `.hyp` uses discharge `dtrue ⊑ dBool` from the seen-set entry
added by the very first `unfold_fix_R`; without seen-indexing
this was the unbreakable cycle. -/
example : Subtype' [] [] dtrue dBool := by
  unfold dBool
  apply Subtype'.unfold_fix_R
  change Subtype' _ [] dtrue dBoolIota
  apply Subtype'.iota_intro
  · -- annotation: dtrue ⊑ dBool, found at S[1]
    exact Subtype'.hyp_here (List.Mem.tail _ (List.Mem.head _))
  · -- body: dtrue ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    change Subtype' _ [] dtrue bodyRHS
    unfold dtrue
    apply Subtype'.unfold_iota_L
    change Subtype' _ [] dtrueLam bodyRHS
    -- λP:(dtrue→Type). λt:(P dtrue). λf:Type. t
    --   ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    apply Subtype'.lam
    · -- (dBool→Type) ⊑ (dtrue→Type): contra dtrue⊑dBool via .hyp at S[2]
      apply Subtype'.lam
      · exact Subtype'.hyp_here
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · exact Subtype'.refl _
    · apply Subtype'.lam
      · -- (P dtrue) ⊑ (P dtrue): refl
        exact Subtype'.refl _
      · apply Subtype'.lam
        · -- (P dfalse) ⊑ Type
          exact Subtype'.top _
        · -- t ⊑ P dtrue, i.e. bvar 1 ⊑ (bvar 2) dtrue.
          show Subtype' _ _ (.bvar 1) ((Expr.app (.bvar 0) dtrue).shift 2 0)
          exact Subtype'.bvar (k := 1) (τ := .app (.bvar 0) dtrue) rfl

end Witnesses

end Och.Soundness
