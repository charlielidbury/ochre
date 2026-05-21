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

/-- Check soundness: if `Och.check e` accepts `e`, then `e`
declaratively subtypes itself (well-formedness). Since `check`
no longer produces a WHNF witness, the soundness statement is
that `e` is self-consistent. The stronger "e subtypes its WHNF"
property requires composing with `evalSubst_equiv` separately.

Delegates to `Och.Soundness.Och_check_sound` in
`Soundness/SynthSound.lean`. -/
noncomputable def check_sound
    {fuel : Nat} {e : Expr}
    (h : Och.check e fuel = .ok ()) :
    Subtype' [] [] e e :=
  Och_check_sound h

/-- Subtype-check soundness: if `Och.subCheck a b` accepts the
two expressions, then `a ⊑ b` declaratively.

Delegates to `Och.Soundness.Och_subCheck_sound` in
`Soundness/SubCheckSubstSoundness.lean`. -/
noncomputable def subCheck_sound
    {fuel : Nat} {a b : Expr}
    (h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a b :=
  Och.Soundness.Och_subCheck_sound h

/-- `concEval` (the reference evaluator) preserves declarative
subtyping. If `e ⊑ τ` holds and `e` evaluates to `e'`, then
`e' ⊑ τ` too. Standard preservation, phrased against the
substrate-agnostic `Subtype'`.

Proof in `Soundness/ConcEvalPreservation.lean` via the strengthened
*bidirectional* equivalence `concEval_equiv` (`Subtype' [] [] e' e ∧
Subtype' [] [] e e'`). The single-direction form below falls out by
`Subtype'.trans` with the user's hypothesis. The bidirectional form is
needed because `app_cong` is not contravariant in its
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
    {fuel : Nat} {e : Expr}
    (h : Och.check e fuel = .ok ()) :
    ∀ f, ∀ msg, concEval f e ≠ .error msg :=
  fun _ msg => concEval_no_error (check_topLevel_closedAt h) msg

/-- **Headline soundness**: if `check` accepts `e` and `concEval`
produces `e'`, then `e' ⊑ e` declaratively. The runtime result
subtypes the original expression. -/
noncomputable def soundness
    {fuel : Nat} {e e' : Expr}
    (hcheck : Och.check e fuel = .ok ())
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' e :=
  let hcl : e.closedAt 0 = true := check_topLevel_closedAt hcheck
  let hSelf : Subtype' [] [] e e := check_sound hcheck
  concEval_preservation hcl hSelf hstep

/-- **General soundness**: if `check` accepts, `subCheck` confirms
`e ⊑ b`, and `concEval` produces `e'`, then `e' ⊑ b`. This
is the widening form — the caller picks an expected type `b` that
may be wider than `e`. -/
noncomputable def soundness_general
    {fuel : Nat} {e e' b : Expr}
    (hcheckE : Och.check e fuel = .ok ())
    (hsub : Och.subCheck e b fuel = .ok true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' b :=
  let hSub : Subtype' [] [] e b := subCheck_sound hsub
  (soundness hcheckE hstep).trans hSub

/-- **Combined soundness + progress**: if `check` accepts `e`,
then at any fuel, `concEval` either produces a well-typed value
or runs out of fuel — it never gets stuck. -/
theorem soundness_and_progress
    {e : Expr} {fuel₁ fuel₂ : Nat}
    (hcheck : Och.check e fuel₁ = .ok ()) :
    (∃ e', concEval fuel₂ e = .ok e' ∧ Nonempty (Subtype' [] [] e' e))
    ∨ concEval fuel₂ e = .outOfFuel := by
  have hcl : e.closedAt 0 = true := check_topLevel_closedAt hcheck
  have hSub : Subtype' [] [] e e := check_sound hcheck
  match hout : concEval fuel₂ e with
  | .ok e' =>
      left; exact ⟨e', rfl, ⟨concEval_preservation hcl hSub hout⟩⟩
  | .outOfFuel => right; rfl
  | .error msg => exact absurd hout (synth_progress hcheck fuel₂ msg)

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
fully derived. With `dtrue` as a plain lambda (no ι wrapper), the
proof is straightforward: after `unfold_fix_R` and `iota_intro`
on the RHS, the LHS is already a 3-ary lambda that can be
compared structurally against the iota body. All contravariant
domain checks are trivial (`.top`) because `dtrue`'s domains are
all `Type`.
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

/-- `dtrue ⊑ dBool`. Constructor path:

  `unfold_fix_R` → `iota_intro` (annotation via `.hyp`) →
  `lam`³ (all contra-domain via `.top`) → body via `.bvar`

The `.hyp` discharges `dtrue ⊑ dBool` from the seen-set entry
added by the very first `unfold_fix_R`; without seen-indexing
this was the unbreakable cycle.

With `dtrue` now a plain lambda (`λP:Type. λt:Type. λf:Type. t`),
there is no `unfold_iota_L` step, and the contravariant domain
checks (`(dBool→Type) ⊑ Type`, `(P dtrue) ⊑ Type`,
`(P dfalse) ⊑ Type`) are all `.top`. -/
example : Subtype' [] [] dtrue dBool := by
  unfold dBool
  apply Subtype'.unfold_fix_R
  change Subtype' _ [] dtrue dBoolIota
  apply Subtype'.iota_intro
  · -- annotation: dtrue ⊑ dBool, found in seen-set
    exact Subtype'.hyp_here (List.Mem.tail _ (List.Mem.head _))
  · -- body: dtrue ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    change Subtype' _ [] dtrue bodyRHS
    unfold dtrue
    -- λP:Type. λt:Type. λf:Type. t
    --   ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    apply Subtype'.lam
    · -- (dBool→Type) ⊑ Type: top
      exact Subtype'.top _
    · apply Subtype'.lam
      · -- (P dtrue) ⊑ Type: top
        exact Subtype'.top _
      · apply Subtype'.lam
        · -- (P dfalse) ⊑ Type: top
          exact Subtype'.top _
        · -- t ⊑ P dtrue, i.e. bvar 1 ⊑ (bvar 2) dtrue.
          show Subtype' _ _ (.bvar 1) ((Expr.app (.bvar 0) dtrue).shift 2 0)
          exact Subtype'.bvar (k := 1) (τ := .app (.bvar 0) dtrue) rfl

end Witnesses

end Och.Soundness
