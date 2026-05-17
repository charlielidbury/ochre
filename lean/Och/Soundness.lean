import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.EvalSubst
import Och.API
import Och.Soundness.ConcEvalPreservation
import Och.Soundness.SynthProgress
import Och.Soundness.SubCheckSubstSoundness
import Och.Soundness.SynthSound
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

Re-proving against the substitution-based engine (the
public `Och.synth` / `Och.subCheck` API in `Och/API.lean`) is a
separate research effort. The statements here are the *targets*
— phrased against the public API and the declarative `Subtype'`
relation in `Subtyping.lean`, both of which are substrate-agnostic.

## Architecture (target)

  algorithmic                 declarative
  `synth + subCheck`     ⟶    `Subtype'`

The algorithmic side is the public API: `Och.synth e` validates
the bidirectional walk, `Och.subCheck a b` runs the structural
engine on the validated WHNFs. The declarative side is the
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
  encoding ports directly (the old `Simple/` prototype used this).
-/

namespace Och.Soundness

/-!
## Top-level statements

These are *targets*, not yet proofs. Each `sorry` here is a
soundness obligation. They are stated against the public API
so that downstream work can quantify over them.
-/

/-- Synthesis soundness: if `Och.synth e` accepts `e`, then `e`
declaratively subtypes its synthesised WHNF.

**Strengthening note (2026-04-28, overnight Stage 1):** the
original statement was `∃ τ, Subtype' [] [] e τ`, which is trivially
discharged by `Subtype'.refl _` (any term subtypes itself, vacuously).
That form did not capture the real Och claim that synth's walk
produces a *meaningful* type-witness. The strengthened form below
ties the existential to `v.whnf` (the synth output), making it
a non-vacuous correspondence between algorithmic synth and
declarative subtype.

The previous env-NbE-based proof attempt (`SoundnessProof.lean`,
deleted in the engine-collapse refactor) built on a Val-level
intermediate relation `SubV` and an RC predicate substrate; both
hit structural walls that don't transfer to the substitution
substrate. Substitution-based proofs build on different lemmas
(substitution lemmas, not reducibility candidates), so this is
a fresh proof effort.

Delegates to `Och.Soundness.Och_synth_sound` in
`Soundness/SynthSound.lean`, which routes through a single named
opacity wall (`synthCore_opacity_WALL`) — the privacy + partial
nature of `synthCore` in `Och/API.lean` blocks structural
induction on synth's body.  See `Soundness/SynthSound.lean`'s
module docstring for the proof skeleton and the three paths
that lift the wall. -/
noncomputable def synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf :=
  Och_synth_sound h

/-- Subtype-check soundness: if `Och.subCheck a b` accepts the
two validated values, then `a.whnf ⊑ b.whnf` declaratively.

Delegates to `Och.Soundness.Och_subCheck_sound` in
`Soundness/SubCheckSubstSoundness.lean`, which composes the per-arm
soundness lemmas in `SubCheckSubst{Structural,Neutral,Fallback}.lean`.

The composition currently walls on (a) partial-def opacity for the
mutual `subCheckSubst` block (no `eq_def` available, so case-analysis
on `h` cannot extract sub-call witnesses) and (b) the v2 substitution
bridges in the fallback arms.  The arm-lemmas themselves are proven
modulo those internal sorries; the composition skeleton is in
`SubCheckSubstSoundness.lean`. -/
noncomputable def subCheck_sound
    {fuel : Nat} {a b : Och.WTValue}
    (h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf :=
  Och.Soundness.Och_subCheck_sound h

/-- `concEval` (the reference evaluator) preserves declarative
subtyping. If `e ⊑ τ` holds and `e` evaluates to `e'`, then
`e' ⊑ τ` too. Standard preservation, phrased against the
substrate-agnostic `Subtype'`.

Proof in `Soundness/ConcEvalPreservation.lean` via the strengthened
*bidirectional* equivalence `concEval_equiv` (`Subtype' [] [] e' e ∧
Subtype' [] [] e e'`). The single-direction form below falls out by
`Subtype'.trans` with the user's hypothesis. The bidirectional form is
needed because `app_cong` and `letE_cong` are not contravariant in their
right-hand subterms, so swapping `f`/`a` in/out of an application spine
requires both directions of `f ≡ fv` and `a ≡ av`. -/
noncomputable def concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ :=
  concEval_preservation_aux hcl hty hstep

/-- **Progress** (the missing half of soundness): a synth-accepted
term doesn't get stuck during evaluation. `concEval` may return
`.ok value` or `.outOfFuel` — both benign — but never `.error`.

Without this theorem, `concEval_preservation` is vacuously true
on stuck programs (the `.ok e'` hypothesis fails). The current
preservation-only theorem set lets a synth-accepted program
silently produce `.error "stuck"` at runtime, which violates
the practical reading of "synth gates concEval".

See `docs/ideas/soundness-strengthen.md` for the full discussion.
The Och-identity claim is: synth's structural walk is a
*sufficient guarantee* against stuckness — every state concEval
could get stuck in (free bvar, apply non-function, etc.) is
ruled out by synth's app-arm domain check, ascription check, and
binder validation. -/
theorem synth_progress
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    ∀ f, ∀ msg, concEval f e ≠ .error msg :=
  fun _ msg => concEval_no_error (synthCore_topLevel_closedAt h) msg

/-- **Headline soundness**: if `synth` accepts `e` with synthesised
type `a`, and `concEval` produces `e'`, then `e' ⊑ a.whnf`
declaratively. The runtime result subtypes the synthesised type. -/
noncomputable def soundness
    {fuel : Nat} {e e' : Expr} {a : Och.WTValue}
    (hsynth : Och.synth e fuel = .ok a)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' a.whnf :=
  let hcl : e.closedAt 0 = true := synthCore_topLevel_closedAt hsynth
  let hSynthA : Subtype' [] [] e a.whnf := synth_sound hsynth
  concEval_preservation hcl hSynthA hstep

/-- **General soundness**: if `synth` accepts, `subCheck` confirms
`a ⊑ b`, and `concEval` produces `e'`, then `e' ⊑ b.whnf`. This
is the widening form — the caller picks an expected type `b` that
may be wider than the synthesised `a`. -/
noncomputable def soundness_general
    {fuel : Nat} {e e' : Expr} {a b : Och.WTValue}
    (hsynthA : Och.synth e fuel = .ok a)
    (hcheck : Och.subCheck a b fuel = .ok true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' b.whnf :=
  let hCheck : Subtype' [] [] a.whnf b.whnf := subCheck_sound hcheck
  (soundness hsynthA hstep).trans hCheck

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
