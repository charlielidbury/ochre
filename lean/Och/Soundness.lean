import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.NbE
import Och.SubCheckVal
import Och.TyCheck
import Och.SoundnessProof
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

/-- Algorithmic conversion is sound w.r.t. the declarative
relation. Stated over closed terms; the open-term version
threads `Γ` and a level-to-index map.

The proof factors as `subCheckVal → SubV → Subtype'`:
`subCheckVal_subV` is the algorithm-reflection step (fully
proven) and `SubV_to_Subtype'` is the readback bridge
(sorried in its closure-opening cases pending
`quote_open_subst` + `narrow`; see SoundnessProof). -/
theorem subCheckVal_sound
    {fuel : Nat} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckVal fuel #[] [] a b = .ok true)
    {ae be : Expr}
    (hqa : quote fuelω 0 a = some ae)
    (hqb : quote fuelω 0 b = some be) :
    Subtype' [] [] ae be :=
  SubV_to_Subtype'
    (subCheckVal_subV hfuel h)
    (fun _ hp => absurd hp (List.not_mem_nil _))
    ⟨rfl, fun _ _ hk => by simp at hk⟩
    (by simpa using hqa)
    (by simpa using hqb)

/-- Closed-term NbE correctness: evaluating then quoting a
closed term gives something `Subtype'`-equivalent to the
original. Specialises `eval_realises` + `R_quote_equiv` at
the empty environment. -/
theorem eval_quote_equiv_closed {fuel unf : Nat} {e : Expr} {v : Val}
    (hcl : e.closedAt 0 = true)
    (heval : eval fuel unf [] e = some v)
    {e' : Expr} (hq : quote fuelω 0 v = some e')
    {S Γe} : Subtype' S Γe e' e ∧ Subtype' S Γe e e' := by
  have henv : REnv 1 0 [] [] :=
    ⟨rfl, fun _ _ hk => by simp at hk⟩
  have hr : R 1 0 v (e.substEnv []) :=
    eval_realises heval henv (by simpa using hcl)
  rw [Expr.substEnv_nil] at hr
  exact R_quote_equiv Nat.one_pos hr hq

/-! ### Quote-totality

The unconditional form
`eval fuel unf [] e = some v → ∃ ve, quote fuelω 0 v = some ve`
is **false**: `eval 2 unf [] (.lam .type huge)` succeeds in
two fuel regardless of `huge`'s size, but `quoteClosure`
re-evaluates `huge` under a fresh neutral and that can need
arbitrarily much fuel. So quote-totality is a *side
condition on the input*, not a derived property.

The natural side condition is `(nf fuelω e).isSome` — `e`
normalises within `fuelω`. With that, the result is
immediate via `eval_fuel_mono` (the value at `fuel ≤ fuelω`
is the same as at `fuelω`, and `nf` says the latter quotes).
-/

/-- Helper: `(o.bind f).isSome` unpacks to a witness. -/
private theorem bind_isSome_iff {α β} {o : Option α} {f : α → Option β} :
    (o.bind f).isSome ↔ ∃ a, o = some a ∧ (f a).isSome := by
  cases o with
  | none => simp
  | some a => simp

/-- `nf` of `.asc t τ` succeeds iff `nf` of `t` does (A8:
ascription is computationally transparent; `eval` peels
the `.asc` in one fuel step, and `eval_fuel_mono` recovers
that step). -/
theorem nf_asc_term_isSome {n : Nat} {t ty : Expr}
    (hnf : (nf n (.asc t ty)).isSome) :
    (nf n t).isSome := by
  match n, hnf with
  | 0, hnf => simp [nf, eval_zero] at hnf
  | k + 1, hnf =>
    unfold nf at hnf ⊢
    simp only [Option.bind_eq_bind] at hnf ⊢
    simp only [eval] at hnf
    obtain ⟨v, hev, hq⟩ := bind_isSome_iff.mp hnf
    exact bind_isSome_iff.mpr
      ⟨v, eval_fuel_mono (Nat.le_succ k) hev, hq⟩

/-- Quote-totality, conditional on `nf fuelω e` succeeding.
With `fuel ≤ fuelω`, `eval fuel … e` and `eval fuelω … e`
agree (`eval_fuel_mono`), so the `nf` witness directly
gives the quote. -/
theorem quote_total_on_eval {fuel : Nat} {e : Expr} {v : Val}
    (hfuel : fuel ≤ fuelω)
    (hnf : (nf fuelω e).isSome)
    (heval : eval fuel unfBound [] e = some v) :
    ∃ ve, quote fuelω 0 v = some ve := by
  unfold nf at hnf
  simp only [Option.bind_eq_bind] at hnf
  rw [eval_fuel_mono hfuel heval] at hnf
  simp only [Option.some_bind] at hnf
  exact Option.isSome_iff_exists.mp hnf

/-- `whnfPi` is sound: each `.fix`/`.iota` step is one
declarative unfold, so the exposed head is `Equiv` to the
input. Closed-context corollary of `whnfPi_sound_open`
(SoundnessProof.lean) at `Γ = #[]`/`hΓ` vacuous. -/
theorem whnfPi_sound {fuel : Nat} {inhab τV τV' : Val}
    (hwh : whnfPi fuel inhab τV = some τV')
    {τe τe' : Expr}
    (hqτ : quote fuelω 0 τV = some τe)
    (hqτ' : quote fuelω 0 τV' = some τe') :
    ∀ {S Γe}, Subtype' S Γe τe' τe := by
  have heq : Equiv τe' τe :=
    whnfPi_sound_open (Γ := #[]) (Γe := [])
      ⟨rfl, fun _ _ hk => by simp at hk⟩ hwh
      (by simpa using hqτ) (by simpa using hqτ')
  exact fun {_ _} => heq.1

/-!
### `tyCheck`/`tyInfer` soundness (closed corollaries)

The mutual `(fuel, tag)` induction lives in
`SoundnessProof.lean` as `tyInfer_sound_open`/
`tyCheckFallback_sound_open`/`tyCheck_sound_open` at general
`OpenCtx Γ ρ Γe ρe`. The closed forms here specialise at
`OpenCtx.empty` (so `e.substEnv [] = e` via `substEnv_nil`)
and bridge the open form's `τe = quote τV` conclusion to
the source `τ` via `eval_quote_equiv_closed`.

The `hnfe`/`hnfτ` side conditions on the closed forms are
the user-facing operational preconditions ("`e` and `τ`
normalise within `fuelω`"); the open forms absorb the
analogous obligation into `openNf_holds` (sorried,
SoundnessProof.lean), so they're not threaded through
here.
-/

/-- Closed-context `tyInfer` soundness, by
`tyInfer_sound_open` at `OpenCtx.empty`. -/
theorem tyInfer_sound_closed
    {fuel : Nat} {e : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true)
    (h : tyInfer fuel #[] [] e = .ok (some τV)) :
    ∃ τe, quote fuelω 0 τV = some τe ∧ Subtype' [] [] e τe := by
  obtain ⟨τe, hqτ, hsub⟩ := tyInfer_sound_open hfuel OpenCtx.empty
    (by simpa using hcle) h
  exact ⟨τe, by simpa using hqτ, Expr.substEnv_nil e ▸ hsub⟩

/-- Closed-context `tyCheckFallback` soundness, by
`tyCheckFallback_sound_open` at `OpenCtx.empty`. -/
theorem tyCheckFallback_sound_closed
    {fuel : Nat} {e τ : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (_hnfe : (nf fuelω e).isSome) (hnfτ : (nf fuelω τ).isSome)
    (hτV : eval fuel unfBound [] τ = some τV)
    (h : tyCheckFallback fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τ := by
  obtain ⟨τe, hqτV⟩ := quote_total_on_eval hfuel hnfτ hτV
  have hopen := tyCheckFallback_sound_open hfuel OpenCtx.empty
    (by simpa using hcle) (by simpa using hqτV) h
  exact .trans (Expr.substEnv_nil e ▸ hopen)
    (eval_quote_equiv_closed hclτ hτV hqτV (S := []) (Γe := [])).1

/-- Closed-context `tyCheck` soundness, by
`tyCheck_sound_open` at `OpenCtx.empty`. -/
theorem tyCheck_sound_closed
    {fuel : Nat} {e τ : Expr} {τV : Val}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (_hnfe : (nf fuelω e).isSome) (hnfτ : (nf fuelω τ).isSome)
    (hτV : eval fuel unfBound [] τ = some τV)
    (h : tyCheck fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τ := by
  obtain ⟨τe, hqτV⟩ := quote_total_on_eval hfuel hnfτ hτV
  have hopen := tyCheck_sound_open hfuel OpenCtx.empty
    (by simpa using hcle) (by simpa using hqτV) h
  exact .trans (Expr.substEnv_nil e ▸ hopen)
    (eval_quote_equiv_closed hclτ hτV hqτV (S := []) (Γe := [])).1


/-- The bidirectional checker is sound: if `typeCheck e τ`
accepts then `e ⊑ τ` declaratively.

`typeCheck` evaluates `τ` to `τV`, then runs `tyCheck` at
`τV`; `tyCheck_sound_closed` does the rest.

The `hnfe`/`hnfτ` side conditions ("`e` and `τ` normalise
within `fuelω`") are what the proof needs to relate Vals
back to Exprs via `quote`. They are *not* derivable from
`typeCheck` succeeding (a closure body can be arbitrarily
large independent of the eval-fuel that built it), but
hold for any term whose syntactic depth is well under
`fuelω = 100000` — i.e., in practice, always; for concrete
inputs, `by native_decide`. -/
theorem typeCheck_sound
    {fuel : Nat} {e τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (hnfe : (nf fuelω e).isSome) (hnfτ : (nf fuelω τ).isSome)
    (h : typeCheck fuel e τ = .ok true) :
    Subtype' [] [] e τ := by
  unfold typeCheck at h
  split at h
  · next τV hτV =>
      exact tyCheck_sound_closed hfuel hcle hclτ hnfe hnfτ hτV h
  · simp_all

/-- One let-step is an `Equiv`. Both directions are single
`Subtype'` constructors with a `.refl` premise. -/
private theorem letE_unfold_equiv (val body : Expr) :
    Equiv (.letE val body) (body.subst 0 val) :=
  fun {_ _} => ⟨.letE_L (.refl _), .letE_R (.refl _)⟩

/-- One asc-erase is an `Equiv`. -/
private theorem asc_erase_equiv (t ty : Expr) :
    Equiv (.asc t ty) t :=
  fun {_ _} => ⟨.asc_L (.refl _), .asc_R (.refl _)⟩

-- One `.iota`-unfold step is `NbE.Equiv.iota_unfold`
-- (SoundnessProof.lean), enabled by `Subtype'.unfold_iota_R`.
-- The earlier `iota_unfold_equiv` (sorried — its backward
-- direction went via `.iota_intro` whose `body[ι] ⊑ ann`
-- premise is not derivable without a well-formedness
-- assumption) is removed.

/-- `concEval` produces a declarative *equivalent* of its
input (both directions). With `Equiv.subst_resp` (no leaf
sorry, SoundnessProof.lean) the `.letE` and `.app` cases
that previously needed only the forward direction now get
both from the IH. The `.app`-with-`.iota`-head case is the
sole residual, now closed via `Equiv.iota_unfold`.

`concEval_refines` (the forward half) and
`concEval_preservation` derive directly. -/
theorem concEval_equiv
    {fuel : Nat} {e e' : Expr}
    (hstep : concEval fuel e = some e') :
    Equiv e' e := by
  -- (Tactic-mode `match e` here makes the `Equiv`-def goal
  -- mis-elaborate against `Equiv.*` lemmas; `cases e` does
  -- not. Lean 4.16 quirk.)
  induction fuel generalizing e e' with
  | zero => simp [concEval] at hstep
  | succ n ih =>
    cases e with
    | bvar _ => simp [concEval] at hstep
    | type =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | lam _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | iota _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | «fix» _ _ =>
      simp only [concEval, Option.some.injEq] at hstep
      subst hstep; exact Equiv.refl _
    | asc t ty =>
      simp only [concEval] at hstep
      exact Equiv.trans (ih hstep) (Equiv.symm (asc_erase_equiv t ty))
    | letE val body =>
      simp only [concEval] at hstep
      split at hstep
      · next v' hval =>
        exact Equiv.trans (ih hstep)
          (Equiv.trans (Equiv.subst_resp body (ih hval) 0)
            (Equiv.symm (letE_unfold_equiv val body)))
      · simp at hstep
    | app f a =>
      simp only [concEval] at hstep
      split at hstep
      -- .lam head: β
      · next dom fbody a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.trans (Equiv.subst_resp fbody (ih ha) 0)
            (Equiv.trans (Equiv.symm (Equiv.beta dom fbody a))
              (Equiv.app (ih hf) (Equiv.refl a))))
      -- .iota head: via `Equiv.iota_unfold`
      · next ann ibody a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.app
            (Equiv.trans (Equiv.symm (Equiv.iota_unfold ann ibody))
                         (ih hf))
            (ih ha))
      -- .fix head: `Equiv.fix_unfold` (proven, SoundnessProof)
      · next ann fbody' a' hf ha =>
        exact Equiv.trans (ih hstep)
          (Equiv.app
            (Equiv.trans (Equiv.symm (Equiv.fix_unfold ann fbody'))
                         (ih hf))
            (ih ha))
      -- other head: just `.app_cong`
      · next fVal a' _ _ _ hf ha =>
        simp only [Option.some.injEq] at hstep; subst hstep
        exact Equiv.app (ih hf) (ih ha)
      -- failure cases
      · simp_all

/-- The forward-only half, kept for callers that don't need
the equivalence. Now derived. -/
theorem concEval_refines
    {fuel : Nat} {e e' : Expr}
    (hstep : concEval fuel e = some e') :
    ∀ {S Γ}, Subtype' S Γ e' e :=
  fun {_ _} => (concEval_equiv hstep).1

/-- Type preservation under concrete evaluation: if `e ⊑ τ`
declaratively and `concEval e ⇓ e'`, then `e' ⊑ τ`. Direct
from `concEval_refines` and transitivity. -/
theorem concEval_preservation
    {fuel : Nat} {e e' τ : Expr}
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ :=
  .trans (concEval_refines hstep) hty

/-- Composing the above: the user-facing guarantee. -/
theorem soundness
    {fuel : Nat} {e e' τ : Expr}
    (hfuel : fuel ≤ fuelω)
    (hcle : e.closedAt 0 = true) (hclτ : τ.closedAt 0 = true)
    (hnfe : (nf fuelω e).isSome) (hnfτ : (nf fuelω τ).isSome)
    (hcheck : typeCheck fuel e τ = .ok true)
    (hstep : concEval fuel e = some e') :
    Subtype' [] [] e' τ :=
  concEval_preservation
    (typeCheck_sound hfuel hcle hclτ hnfe hnfτ hcheck) hstep

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
