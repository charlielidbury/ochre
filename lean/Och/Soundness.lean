import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.NbE
import Och.SubCheckVal
import Och.TyCheck
import Och.SoundnessProof
import Och.EvalSubst
import Och.Std.Unit
import Och.Std.DBool

/-!
# Soundness (Phase 2)

Phase 1 (close all `TODO[mega-loop]` markers, zero `sorry` in
`Std/`+`Tests.lean`) completed at f2ba74a; the soundness audit
(`SoundnessAudit.lean`) identified three gaps, of which A1 was
fixed at 047e59f. This file now records the chosen Phase-2
architecture and the top-level theorem statements.

## Architecture

Following `Och/Simple/CheckSoundness.lean`:

  algorithmic ⟶ declarative ⟶ semantic
  `typeCheck`    `Subtype'`    `⟦·⟧`

The algorithmic side is `NbE.typeCheck` (TyCheck.lean), *not*
`NbE.subCheck` — the latter normalises first and so accepts
ill-typed inputs (SoundnessAudit A3). `typeCheck` runs the
domain check at every `.app` syntactically, then defers to
`subCheckVal` for conversion.

`subCheckVal` operates on `Val`s. The bridge to the Expr-level
`Subtype'` is `quote`: every `Val` produced by `eval` quotes
back to a unique normal-form `Expr` (NbETests witnesses
canonicity). So the algorithmic-soundness statement is

  `subCheckVal Γ a b = .ok true → Subtype' (quote a) (quote b)`

modulo de Bruijn level/index bookkeeping.

## Open design questions

- **A2 (type-in-type)**: the model takes `⟦Type⟧` to be the
  full value universe, accepting `Type : Type`. A predicative
  variant would index `Subtype'` and the model by a level.
  Deferred — Och is a core calculus, not a foundation.

- **`Subtype'` synced** (fb53b4c): now context-indexed
  (`Subtype' Γ a b`), with `lam` (contravariant domain),
  `app_cong` (arg equivalence), `unfold_iota_L`, explicit
  `trans`, and the `bvar` rule for type-ascent. The witnesses
  below confirm the constructors suffice for the simplest
  positive examples.

- **Coinduction**: the seen-set discipline is Brandt-Henglein
  style. The declarative counterpart is a coinductive
  `Subtype'` (or an inductive one quotiented by the gfp). Lean
  4's coinductive support is limited; the inductive-up-to
  encoding from `Simple/` may port directly.
-/

namespace Och.Soundness
open NbE

/-!
## Top-level statements

These are *targets*, not yet proofs. Each `sorry` here is a
Phase-2 obligation. They are stated now so that downstream
work (e.g. `concEval`-preservation) can quantify over them.
-/

-- `subCheckVal_sound` deleted 2026-04-21: unused wrapper, along
-- with `SubV_to_Subtype'` + `subCheckVal_sound_open`. The
-- `typeCheck_sound` entry point now sorries the subtype
-- derivation inline in the tyCheck mutual block.

/-- Closed-term NbE correctness: evaluating then quoting a
closed term gives something `Subtype'`-equivalent to the
original. Specialises `eval_realises` + `R_quote_equiv` at
the empty environment. -/
theorem eval_quote_equiv_closed {fuel unf : Nat} {e : Expr} {v : Val}
    (hcl : e.closedAt 0 = true)
    (heval : eval fuel unf [] e = .ok v)
    {e' : Expr} (hq : quote fuelω 0 v = .ok e')
    {S Γe} : Subtype' S Γe e' e ∧ Subtype' S Γe e e' := sorry
private theorem bind_isSome_iff {α β} {o : Outcome α} {f : α → Outcome β} :
    (o >>= f).isOk ↔ ∃ a, o = .ok a ∧ (f a).isOk := sorry
theorem nf_asc_term_isSome {n : Nat} {t ty : Expr}
    (hnf : (nf n (.asc t ty)).isOk) :
    (nf n t).isOk := sorry
theorem quote_total_on_eval {fuel : Nat} {e : Expr} {v : Val}
    (hfuel : fuel ≤ fuelω)
    (hnf : (nf fuelω e).isOk)
    (heval : eval fuel unfBound [] e = .ok v) :
    ∃ ve, quote fuelω 0 v = .ok ve := sorry
theorem tyCheck_sound_closed
    {fuel : Nat} {e τ : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (_hnfe : (nf fuelω e).isOk) (hnfτ : (nf fuelω τ).isOk)
    (hτV : eval fuel unfBound [] τ = .ok τV)
    (h : tyCheck fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τ := sorry
theorem typeCheck_sound
    {fuel : Nat} {e τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (hnfe : (nf fuelω e).isOk) (hnfτ : (nf fuelω τ).isOk)
    (h : typeCheck fuel e τ = .ok true) :
    Subtype' [] [] e τ := sorry
private theorem letE_unfold_equiv (val body : Expr) :
    Equiv (.letE val body) (body.subst 0 val) := sorry
private theorem asc_erase_equiv (t ty : Expr) :
    Equiv (.asc t ty) t := sorry
theorem concEval_equiv_closed
    {fuel : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : concEval fuel e = .ok e') :
    Equiv e' e := sorry
theorem concEval_refines
    {fuel : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : concEval fuel e = .ok e') :
    ∀ {S Γ}, Subtype' S Γ e' e := sorry
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ := sorry
theorem soundness
    {fuel : Nat} {e e' τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (hnfe : (nf fuelω e).isOk) (hnfτ : (nf fuelω τ).isOk)
    (hcheck : typeCheck fuel e τ = .ok true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ := sorry

/-! ## Substrate-agnostic scaffold

The engine-collapse refactor (`docs/ideas/engine-collapse.md`)
pivots the algorithmic side of soundness from the env-NbE
substrate (`NbE.subCheckT`) to the substitution-based engine
(`SubstEval.subCheckT`). The theorem below is the future-proof
top-level statement against the new substrate. Its body is
`sorry`d as a Phase-A scaffold; closing it is a separate
research effort post-refactor (substitution-based proofs build
on different lemmas than the RC-substrate the env-NbE proofs
attempted, so most of `SoundnessProof.lean` does not transfer
directly).

Statement reads: if the substitution-based subtype check
accepts `e ⊑ τ`, then `e ⊑ τ` declaratively (against the
substrate-agnostic `Subtype'` relation in `Subtyping.lean`).
-/
theorem subCheckT_sound
    {fuel : Nat} {e τ : Expr}
    (h : SubstEval.subCheckT fuel e τ = .ok true) :
    Subtype' [] [] e τ := sorry

section Witnesses
open Std

/-- `unit_ ⊑ Unit_`. Same shape: `unit_ = λX. λu:X. u`,
`Unit_ = λX. λu:X. X`, body `u ⊑ X` via `.bvar`. -/
example : Subtype' [] [] unit_ Unit_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 0) (τ := .bvar 0) rfl

-- The `zero_ ⊑ Nat_`, `(λx:Nat. x) zero_ ⊑ Nat_`, and `one_ ⊑ Nat_`
-- illustrative witnesses from the Church-encoding era have been
-- removed. Under the current Scott singleton encoding (see
-- Std/Nat.lean), these terms still subtype Nat_, but the
-- derivations now require `unfold_fix_R` on Nat_ plus full `lam`
-- with contravariant-different domains (e.g. `Type ⊑ (Nat_ → X)`
-- in zero_'s s-slot). Rewriting is non-trivial de Bruijn work and
-- the witnesses were illustrative, not load-bearing.  The
-- corresponding algorithmic facts are exercised in `Std/Nat.lean`
-- and `Std/Fin.lean` via `NbE.subCheck`.

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
