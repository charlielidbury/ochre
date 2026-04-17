import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.NbE
import Och.SubCheckVal
import Och.TyCheck
import Och.Std.Nat
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
`subCheckNF` — the latter normalises first and so accepts
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

/-- Algorithmic conversion is sound w.r.t. the declarative
relation. Stated over closed terms; the open-term version
threads `Γ` and a level-to-index map.

This requires `Subtype'` to be brought in sync with
`subCheckVal` first (it currently lacks several arms). -/
theorem subCheckVal_sound
    {fuel : Nat} {a b : Val}
    (h : subCheckVal fuel #[] [] a b = .ok true)
    {ae be : Expr}
    (hqa : quote fuel 0 a = some ae)
    (hqb : quote fuel 0 b = some be) :
    Subtype' [] [] ae be := by
  sorry

/-- The bidirectional checker is sound: if `typeCheck e τ`
accepts then `e` is well-typed at `τ` in the declarative system.

Bridges `tyCheck` (which operates on a `Val` expected type) to
the Expr-level `Subtype'` via `eval`/`quote`. The proof goes by
induction on `e`, using `subCheckVal_sound` for the conversion
leaves and the `.app` domain-check IH for the Π-elim rule. -/
theorem typeCheck_sound
    {fuel : Nat} {e τ : Expr}
    (h : typeCheck fuel e τ = .ok true) :
    Subtype' [] [] e τ := by
  sorry

/-- Type preservation under concrete evaluation: if `e : τ`
declaratively and `concEval` steps `e` to `e'`, then `e' : τ`.

This is the part that depends on the *semantic* model. For
`Simple/` it's a syntactic subject-reduction proof; for full
Och the equirecursive types make the inductive measure subtle.
The intended approach is step-indexed logical relations over
`Val` (the previous `VCompat` attempt grew unwieldy by working
over `Expr`; `Val` should be cleaner since closures avoid the
substitution lemmas). -/
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ := by
  sorry

/-- Composing the above: the user-facing guarantee. -/
theorem soundness
    {fuel : Nat} {e e' τ : Expr}
    (hcheck : typeCheck fuel e τ = .ok true)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ :=
  concEval_preservation (typeCheck_sound hcheck) hstep

/-!
## Witnesses

Hand-built `Subtype'` derivations for the simplest positive
tests, demonstrating the constructors are sufficient (i.e. the
algorithm's `.ok true` corresponds to a derivation).
-/

section Witnesses
open Std

/-- `zero_ ⊑ Nat_`. The body comparison `z ⊑ X` (= `bvar 1 ⊑
bvar 2` under `Γ = [X→X, X, Type]`) goes through `.bvar`:
`Γ[1] = .bvar 0` (the type of `z` is `X`, which at its binder
was `bvar 0`), shifted by 2 gives `bvar 2` = `X`. -/
example : Subtype' [] [] zero_ Nat_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 1) (τ := .bvar 0) rfl

/-- `unit_ ⊑ Unit_`. Same shape: `unit_ = λX. λu:X. u`,
`Unit_ = λX. λu:X. X`, body `u ⊑ X` via `.bvar`. -/
example : Subtype' [] [] unit_ Unit_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  exact Subtype'.bvar (k := 0) (τ := .bvar 0) rfl

/-- β-conversion: `(λx:Nat_. x) zero_ ⊑ Nat_` reduces via
`beta_L` to the `zero_ ⊑ Nat_` witness above. -/
example : Subtype' [] [] (.app (.lam Nat_ (.bvar 0)) zero_) Nat_ := by
  apply Subtype'.beta_L
  apply Subtype'.lam_body; apply Subtype'.lam_body; apply Subtype'.lam_body
  exact Subtype'.bvar (k := 1) (τ := .bvar 0) rfl

/-- `one_ ⊑ Nat_` (Church 1). Body is `s z ⊑ X` under
`Γ = [s:X→X, z:X, X:Type]`. Derives via `app_ascent`: `s` has
Π-type `X→X` from `.bvar`, so `s z` has the codomain `X`. -/
example : Subtype' [] [] one_ Nat_ := by
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  apply Subtype'.lam_body
  -- Γ = [.lam (.bvar 1) (.bvar 2), .bvar 0, .type]
  -- bvar 0 (=s) ⊑ Γ[0].shift 1 0 ; Γ[0] = `.lam (bvar 1) (bvar 2)`
  -- shift 1 0 → `.lam (bvar 2) (bvar 3)`. Then app_ascent with
  -- a := bvar 1 (=z) gives `(bvar 3).subst 0 (bvar 1) = bvar 2`.
  have hs := Subtype'.bvar (S := [])
                           (Γ := [.lam (.bvar 1) (.bvar 2), .bvar 0, .type])
                           (k := 0) (τ := .lam (.bvar 1) (.bvar 2)) rfl
  have ha := Subtype'.app_ascent (a := .bvar 1) hs
  simp only [Expr.shift, Expr.subst, Expr.shift] at ha
  exact ha

/-!
The flagship coinductive case (SoundnessAudit A4): `dtrue ⊑ dBool`
fully derived. The proof uses `change` to step through each
`subst`/`shift` computation by defeq (Lean's reducer crunches the
closed substitution; `simp only [Expr.subst]` alone leaves
half-evaluated `if`/`Nat.add` debris). The intermediate forms are
named so each `change` is one closed-form-to-closed-form step.
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

private def dtrueIota : Expr :=
  .iota dtrue
    (.lam (.lam dtrue .type)
      (.lam (.app (.bvar 0) (.bvar 1))
        (.lam .type (.bvar 1))))

private def dtrueLam : Expr :=
  .lam (.lam dtrue .type)
    (.lam (.app (.bvar 0) dtrueIota)
      (.lam .type (.bvar 1)))

/-- `dtrue ⊑ dBool`. Every `Subtype'` constructor is exercised:

  `unfold_fix_R` → `iota_intro` (annotation via `.hyp`) →
  `unfold_fix_L` → `unfold_iota_L` → `lam`³ →
    P-domain contra: `lam`(`.hyp`, `.refl`)
    t-domain contra: `app_cong`(`.refl`, fix-unfold↔refl, fix-unfold↔refl)
    f-domain contra: `.top`
    body: `.bvar`

The two `.hyp` uses discharge `dtrue ⊑ dBool` from the seen-set
(added by the very first `unfold_fix_R`); without seen-indexing
this was the unbreakable cycle. -/
example : Subtype' [] [] dtrue dBool := by
  unfold dBool
  apply Subtype'.unfold_fix_R
  change Subtype' _ [] dtrue dBoolIota
  apply Subtype'.iota_intro
  · -- annotation: dtrue ⊑ dBool, found at S[1]
    exact Subtype'.hyp (List.Mem.tail _ (List.Mem.head _))
  · -- body: dtrue ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    change Subtype' _ [] dtrue bodyRHS
    unfold dtrue
    apply Subtype'.unfold_fix_L
    change Subtype' _ [] dtrueIota bodyRHS
    unfold dtrueIota
    apply Subtype'.unfold_iota_L
    change Subtype' _ [] dtrueLam bodyRHS
    -- λP:(dtrue→Type). λt:(P dtrueIota). λf:Type. t
    --   ⊑ λP:(dBool→Type). λt:(P dtrue). λf:(P dfalse). P dtrue
    apply Subtype'.lam
    · -- (dBool→Type) ⊑ (dtrue→Type): contra dtrue⊑dBool via .hyp at S[3]
      apply Subtype'.lam
      · exact Subtype'.hyp (List.Mem.tail _ (List.Mem.tail _
                            (List.Mem.tail _ (List.Mem.head _))))
      · exact Subtype'.refl _
    · apply Subtype'.lam
      · -- (P dtrue) ⊑ (P dtrueIota): app_cong, args dtrue ≡ dtrueIota
        -- (each direction is one fix-unfold to refl)
        apply Subtype'.app_cong
        · exact Subtype'.refl _
        · unfold dtrue; apply Subtype'.unfold_fix_L
          change Subtype' _ _ dtrueIota dtrueIota; exact Subtype'.refl _
        · unfold dtrue; apply Subtype'.unfold_fix_R
          change Subtype' _ _ dtrueIota dtrueIota; exact Subtype'.refl _
      · apply Subtype'.lam
        · -- (P dfalse) ⊑ Type
          exact Subtype'.top _
        · -- t ⊑ P dtrue, i.e. bvar 1 ⊑ (bvar 2) dtrue.
          -- Γ[1] = `.app (.bvar 0) dtrue`; shift 2 0 → `.app (.bvar 2) dtrue`
          -- (dtrue closed ⇒ shift no-op). The `show` lets defeq compute
          -- the shift so `.bvar` matches directly.
          show Subtype' _ _ (.bvar 1) ((Expr.app (.bvar 0) dtrue).shift 2 0)
          exact Subtype'.bvar (k := 1) (τ := .app (.bvar 0) dtrue) rfl

end Witnesses

end Och.Soundness
