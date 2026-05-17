import Och.Syntax
import Och.Outcome
import Och.Eval
import Och.Subtyping

/-!
# Substitution-based evaluator and structural subtype check

This module provides Och's primary substitution-based evaluation pipeline:
a head-normal-form evaluator (`evalSubst`) and a structural subtype check
(`subCheck`) that operate directly on `Expr`, never lifting into a
`Val`/`Closure` ADT.

## Status

`evalSubst` is non-`partial` (Lean's elaborator accepts it via lex measure
on `(fuel, unf)`).

The `subCheckSubst` mutual block is non-`partial` as well, with each
function carrying a lex `(fuel, phase)` termination measure. `phase`
distinguishes `subCheckSubst` (phase 0) from `subCheckSubstMatch`
(phase 1): every `subCheckSubst → subCheckSubstMatch` call decrements
`fuel`, and every `subCheckSubstMatch → subCheckSubst` call decrements
phase at the same fuel. All other recursive calls in the block (spine,
ascent, synth, plus self-recursive ones) decrement `fuel` directly.
Equation lemmas (`subCheckSubst.eq_def` etc.) auto-generate, which
the soundness composition in `Soundness/SubCheckSubstSoundness.lean`
relies on.

## Design

- **Values are `Expr`.** No separate `Val`/`Closure` ADT. When applying
  a `λ` to an argument, we substitute the argument into the body. β
  substitutes; ι/fix unfolds substitute their own self-reference into
  their body, then reapply.

- **Free variables are plain `bvar k`** using standard de Bruijn indices.
  When the checker descends under a binder, it extends the context
  (`tyCtx.push domType`) and recurses on the raw body — no substitution
  is performed. Any `bvar k` encountered by `evalSubst` is a free
  variable in the current scope (since evalSubst never goes under
  binders) and is treated as neutral.

- **TyCtx indexing:** `tyCtx` is an Array where we push to the end when
  entering a binder. To look up the type of `bvar k` at the current
  depth, we access `tyCtx[tyCtx.size - 1 - k]`. This means:
    - `tyCtx[0]` = outermost binder's type
    - `tyCtx[tyCtx.size - 1]` = innermost binder's type
    - `bvar 0` (innermost) → `tyCtx[tyCtx.size - 1]`

- **HNF only.** `evalSubst` returns Expr's in head-normal form. It does
  not go under λ-binders during evaluation.

- **`unfBound`** caps fix/ι unfolds, mirroring `NbE.unfBound = 32`.

## Soundness

The previous level-var encoding required a `closeAll` translation to
bridge between the algorithmic level-var representation and the
declarative de Bruijn `Subtype'` relation. By using pure de Bruijn
indices throughout, the algorithmic and declarative representations
now share the same variable encoding, eliminating the `closeAll`
family and its associated sorries.
-/

namespace SubstEval

open Outcome

/-! ## Substitution-based open-term evaluator

Like `concEval` but treats free `bvar`s as neutral values. Carries an
`unf` budget for fix/ι unfolds, mirroring NbE's schedule.

Result is an `Expr` in head-normal form: lambda, iota, fix, type, bot,
or a neutral spine. -/

/-- True iff `e` is a "neutral" — its head is a free `bvar` or a
    stuck application thereof. Lambdas, iotas, fixes, type, bot are
    NOT neutral.

    Exposed (not `private`) so soundness proofs can refer to it. -/
def isNeutral : Expr → Bool
  | .bvar _ => true
  | .app f _ => isNeutral f
  | _ => false

/-- Default unfold bound. Match NbE for apples-to-apples behaviour. -/
def unfBound : Nat := 32

/-- Substitution-based head-normal-form evaluator. Decreasing on
    `(fuel, unf)` lex: every recursive call either decrements `fuel`
    (the outer `match fuel with | _+1 ⇒ …` consumes it) or holds
    `fuel` and decrements `unf` (the iota/fix unfold cases). -/
def evalSubst (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar _ =>
      -- All bvars are neutral (free in the current scope, since
      -- evalSubst never goes under binders).
      .ok e
    | .type => .ok .type
    | .bot => .ok .bot
    | .lam _ _ => .ok e
    | .iota _ _ => .ok e
    | .fix _ _ => .ok e
    | .asc t ty => do
        let t' ← evalSubst fuel unf t
        let ty' ← evalSubst fuel unf ty
        .ok (.asc t' ty')
    | .letE val body => do
        let v ← evalSubst fuel unf val
        evalSubst fuel unf (body.subst 0 v)
    | .app f a => do
        let f' ← evalSubst fuel unf f
        let a' ← evalSubst fuel unf a
        match f' with
        | .lam _dom body =>
            -- β: substitute argument into body.
            evalSubst fuel unf (body.subst 0 a')
        | .iota _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              -- ι unfold: substitute self with the ι-value, then re-apply.
              let unfolded := body.subst 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .fix _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              let unfolded := body.subst 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .asc inner _ =>
            evalSubst fuel unf (.app inner a')
        | _ => .ok (.app f' a')

/-! ## Subtype check on Expr

Mirrors `subCheckVal` arm-by-arm. Uses `Expr` structural equality
(`DecidableEq`-derived `==`). The type context `tyCtx` stores the
types of free variables: `tyCtx[tyCtx.size - 1 - k]` is the type of
`bvar k`. Used by `neutralAscent` to ascend an LHS neutral to its
type when the spine doesn't match.

The recursion mixes WHNF re-evaluation with structural descent through
binders. Termination is captured by a lex `(fuel, phase)` measure:
`subCheckSubst → subCheckSubstMatch` decrements `fuel`, the reverse
direction decrements phase, and all other recursive calls decrement
`fuel` directly. Equation lemmas auto-generate.
-/

/-- Engine-internal type-context. `Γ[k]` is the type of `bvar k`.
    Stored as `Ctx = List Expr` in de Bruijn order: `Γ[0]` =
    innermost binder, matching `Subtype'`'s context directly.
    When entering a binder, prepend: `domV :: Γ`.
    Exposed (not `private`) so soundness proofs can refer to it. -/
abbrev TyCtx := Ctx

/-- Internal: unfold a `.fix` / `.iota` wrapper in `ty` until a
    `.lam` is exposed. Used by `synthNeutralType` to walk a spine
    through types whose Π is wrapped in fix/iota (e.g. `Nat_`'s
    self-eliminator `fix N. ι self:N. λP:..`). The `inhab`
    argument is what to substitute for the ι-self when unfolding
    (typically the spine-head being applied). -/
def exposePi (fuel : Nat) (inhab : Expr) (ty : Expr) :
    Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  /-- Structurally recursive on the unfold budget `n : Nat`. -/
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

/-! ### Eval bridge and helpers for intrinsic derivation construction

These are needed by `subCheckSubst` to bridge between the original
inputs `a, b` and their WHNF forms `a', b'`. Defined here (not in
Soundness/) to break the circular import. -/

/-- `evalSubst` preserves subtype equivalence at arbitrary `S, Γ`.
    Computable (no `noncomputable` needed) — Lean accepts the tactic
    proof as kernel-reducible. -/
def evalSubst_equiv_open'
    {fuel unf : Nat} {e e' : Expr} (S : Seen) (Γ : Ctx)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' S Γ e' e × Subtype' S Γ e e' := by
  induction fuel generalizing unf e e' with
  | zero => rw [evalSubst.eq_1] at hstep; cases hstep
  | succ n ih =>
    match e, hstep with
    | .bvar k, h =>
      rw [evalSubst.eq_2] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .type, h =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, h =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .lam dom body, h =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .iota ann body, h =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .fix ann body, h =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, h =>
      rw [evalSubst.eq_8] at h
      match ht : evalSubst n unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        match hty : evalSubst n unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          rw [ht, hty] at h
          simp only [Outcome.ok_bind, Outcome.ok.injEq] at h; subst h
          have ⟨ht₁, ht₂⟩ := ih ht
          exact ⟨.asc_L (.asc_R ht₁), .asc_L (.asc_R ht₂)⟩
    | .letE val body, h =>
      rw [evalSubst.eq_9] at h
      match hvEv : evalSubst n unf val with
      | .outOfFuel => rw [hvEv] at h; cases h
      | .error _ => rw [hvEv] at h; cases h
      | .ok vv =>
        simp only [hvEv] at h
        have ⟨hvv₁, hvv₂⟩ := ih hvEv
        simp only [Outcome.ok_bind] at h
        have ⟨he₁, he₂⟩ := ih h
        exact ⟨.trans he₁ (.trans (.letE_R (.refl _)) (.letE_cong hvv₁ (.refl _))),
               .trans (.letE_cong hvv₂ (.refl _)) (.trans (.letE_L (.refl _)) he₂)⟩
    | .app f a, h =>
      rw [evalSubst.eq_10] at h
      match hfEv : evalSubst n unf f with
      | .outOfFuel => rw [hfEv] at h; cases h
      | .error _ => rw [hfEv] at h; cases h
      | .ok fv =>
        have ⟨hf₁, hf₂⟩ := ih hfEv
        match haEv : evalSubst n unf a with
        | .outOfFuel => rw [hfEv, haEv] at h; cases h
        | .error _ => rw [hfEv, haEv] at h; cases h
        | .ok av =>
          have ⟨ha₁, ha₂⟩ := ih haEv
          rw [hfEv, haEv] at h
          simp only [Outcome.ok_bind] at h
          cases fv with
          | bvar _ =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | type =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            simp only at h
            have ⟨he₁, he₂⟩ := ih h
            exact ⟨.trans he₁ (.trans (.beta_R (.refl _)) (.app_cong hf₁ ha₁ ha₂)),
              .trans (.app_cong hf₂ ha₂ ha₁) (.trans (.beta_L (.refl _)) he₂)⟩
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · have ⟨he₁, he₂⟩ := ih h
              exact ⟨.trans he₁ (.trans (.app_cong (.unfold_iota_R (.refl _)) (.refl _) (.refl _))
                  (.app_cong hf₁ ha₁ ha₂)),
                .trans (.app_cong hf₂ ha₂ ha₁)
                  (.trans (.app_cong (.unfold_iota_L (.refl _)) (.refl _) (.refl _)) he₂)⟩
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · have ⟨he₁, he₂⟩ := ih h
              exact ⟨.trans he₁ (.trans (.app_cong (.unfold_fix_R (.refl _)) (.refl _) (.refl _))
                  (.app_cong hf₁ ha₁ ha₂)),
                .trans (.app_cong hf₂ ha₂ ha₁)
                  (.trans (.app_cong (.unfold_fix_L (.refl _)) (.refl _) (.refl _)) he₂)⟩
          | asc inner _ =>
            simp only at h
            have ⟨he₁, he₂⟩ := ih h
            exact ⟨.trans he₁ (.app_cong (.trans (.asc_R (.refl _)) hf₁) ha₁ ha₂),
              .trans (.app_cong (.trans hf₂ (.asc_L (.refl _))) ha₂ ha₁) he₂⟩
          | letE vv b =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | app f' a' =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩

/-- Strip LHS ascription: extract the annotation type from `.asc`. -/
def stripAscL (e : Expr) : Expr :=
  match e with | .asc _ ty => ty | x => x

/-- Strip RHS ascription: extract the inner term from `.asc`. -/
def stripAscR (e : Expr) : Expr :=
  match e with | .asc inner _ => inner | x => x

/-- LHS asc strip: `a' ⊑ stripAscL a'`. -/
def stripAscL_super (S : Seen) (Γ : Ctx) (a' : Expr) :
    Subtype' S Γ a' (stripAscL a') :=
  match a' with
  | .asc _ _ => .asc_L_ann (.refl _)
  | .bvar _ | .lam _ _ | .app _ _ | .type | .bot | .iota _ _ | .fix _ _ | .letE _ _ => .refl _

/-- RHS asc strip: `stripAscR b' ⊑ b'`. -/
def stripAscR_sub (S : Seen) (Γ : Ctx) (b' : Expr) :
    Subtype' S Γ (stripAscR b') b' :=
  match b' with
  | .asc _ _ => .asc_R (.refl _)
  | .bvar _ | .lam _ _ | .app _ _ | .type | .bot | .iota _ _ | .fix _ _ | .letE _ _ => .refl _


/-! ### exposePi derivation helpers (computable)

These produce `Subtype'` derivations witnessing that `exposePi` (which
unfolds fix/iota wrappers to expose a Π) preserves subtyping. Used by
`synthNeutralWithDeriv` to construct the derivation for the `.app` case. -/

/-- Computable inner-loop derivation for `exposePi.go`: if `go n e = some piExpr`
and we have `Subtype' S Γ inhab e`, produce `Subtype' S Γ inhab piExpr`. -/
def exposePi_go_deriv (fuel : Nat) (inhab : Expr) (S : Seen) (Γ : Ctx)
    : (n : Nat) → (e piExpr : Expr) →
      Subtype' S Γ inhab e →
      exposePi.go fuel inhab n e = some piExpr →
      Subtype' S Γ inhab piExpr := by
  intro n
  induction n with
  | zero =>
    intro e piExpr hsub hgo
    simp only [exposePi.go] at hgo
    cases e <;> (simp only [Option.some.injEq] at hgo; subst hgo; exact hsub)
  | succ m ih =>
    intro e piExpr hsub hgo
    match e with
    | .lam dom body =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .fix ann body =>
      simp only [exposePi.go] at hgo
      match hev : evalSubst fuel 4 (body.subst 0 (.fix ann body)) with
      | .ok e' =>
        rw [hev] at hgo
        have ⟨_, hfwd⟩ := evalSubst_equiv_open' S Γ hev
        have step_unfold : Subtype' S Γ (.fix ann body)
            (body.subst 0 (.fix ann body)) :=
          .unfold_fix_L (.refl _)
        have hsub' : Subtype' S Γ inhab e' :=
          .trans hsub (.trans step_unfold hfwd)
        exact ih e' piExpr hsub' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .iota _ann _body =>
      simp only [exposePi.go] at hgo
      match hev : evalSubst fuel 4 (_body.subst 0 inhab) with
      | .ok e' =>
        rw [hev] at hgo
        have ⟨_, hfwd⟩ := evalSubst_equiv_open' S Γ hev
        have step_elim : Subtype' S Γ inhab (_body.subst 0 inhab) :=
          .iota_elim hsub
        have hsub' : Subtype' S Γ inhab e' :=
          .trans step_elim hfwd
        exact ih e' piExpr hsub' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .bot => simp only [exposePi.go] at hgo; cases hgo
    | .bvar _ =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .type =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .app _ _ =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .asc _ _ =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .letE _ _ =>
      simp only [exposePi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub

/-- Computable `exposePi` soundness: if `exposePi fuel inhab ty = some piExpr`
and `Subtype' S Γ inhab ty`, then `Subtype' S Γ inhab piExpr`. -/
def exposePi_deriv
    {fuel : Nat} {inhab ty piExpr : Expr} (S : Seen) (Γ : Ctx)
    (hsub_inhab : Subtype' S Γ inhab ty)
    (h : exposePi fuel inhab ty = some piExpr) :
    Subtype' S Γ inhab piExpr := by
  unfold exposePi at h
  match hev : evalSubst fuel unfBound ty with
  | .ok ty' =>
    rw [hev] at h
    have ⟨_, hfwd⟩ := evalSubst_equiv_open' S Γ hev
    exact exposePi_go_deriv fuel inhab S Γ
      unfBound ty' piExpr (.trans hsub_inhab hfwd) h
  | .outOfFuel => rw [hev] at h; cases h
  | .error _ => rw [hev] at h; cases h

/-! ### Structural subtype checker -/

mutual
  /-- Top-level subtype check. Forces WHNF on both sides, then
      delegates to `subCheckSubstMatch`. Returns a derivation on
      success (intrinsic typing). -/
  def subCheckSubst (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome (Subtype' seen tyCtx a b) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match h₁ : evalSubst (fuel + 1) unfBound a with
      | .ok a' =>
        match h₂ : evalSubst (fuel + 1) unfBound b with
        | .ok b' =>
          -- Strip ascriptions from WHNF forms
          let a'' := stripAscL a'
          let b'' := stripAscR b'
          -- Bridge proofs: a ⊑ a'' and b'' ⊑ b
          have ha : Subtype' seen tyCtx a a'' :=
            (evalSubst_equiv_open' seen tyCtx h₁).2.trans (stripAscL_super seen tyCtx a')
          have hb : Subtype' seen tyCtx b'' b :=
            (stripAscR_sub seen tyCtx b').trans (evalSubst_equiv_open' seen tyCtx h₂).1
          if heq : a'' = b'' then .ok (ha.trans (heq ▸ hb))
          else if hseen : seen.any (fun (d, av, bv) => d == tyCtx.length && a'' == av && b'' == bv)
          then .ok (ha.trans (.trans (.hyp_here (by
            have hany := List.any_eq_true.mp hseen
            obtain ⟨⟨d, av, bv⟩, hmem, hpred⟩ := hany
            simp only [Bool.and_eq_true, beq_iff_eq] at hpred
            obtain ⟨⟨hd, hav⟩, hbv⟩ := hpred
            subst hd; subst hav; subst hbv; exact hmem)) hb))
          else if htype : b'' = .type then .ok (ha.trans (.trans (.top a'') (htype ▸ hb)))
          else
            match subCheckSubstMatch fuel tyCtx seen a'' b'' with
            | .ok deriv => .ok (ha.trans (deriv.trans hb))
            | .outOfFuel => .outOfFuel
            | .error s => .error s
        | .outOfFuel => .outOfFuel
        | .error s => .error s
      | .outOfFuel => .outOfFuel
      | .error s => .error s
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Per-shape case-split on the WHNF-stripped forms `a`, `b`.
      Each arm constructs the `Subtype'` derivation explicitly. -/
  def subCheckSubstMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome (Subtype' seen tyCtx a b) :=
    match a, b with
    | .bot, _ => .ok .bot_L
    | .lam _domA _bodyA, .lam domB bodyB =>
        match subCheckSubst fuel tyCtx seen domB _domA with
        | .ok contra =>
            match subCheckSubst fuel (domB :: tyCtx) seen _bodyA bodyB with
            | .ok body => .ok (.lam contra body)
            | .outOfFuel => .outOfFuel
            | .error s => .error s
        | .outOfFuel => .outOfFuel
        | .error s => .error s
    | .iota _annA _bodyA, .iota annB bodyB =>
        let structural : Outcome (Subtype' seen tyCtx (.iota _annA _bodyA) (.iota annB bodyB)) :=
          match subCheckSubst fuel tyCtx seen _annA annB with
          | .ok annDeriv =>
              match subCheckSubst fuel (annB :: tyCtx) seen _bodyA bodyB with
              | .ok bodyDeriv => .ok (.iota_cong annDeriv bodyDeriv)
              | .outOfFuel => .outOfFuel
              | .error s => .error s
          | .outOfFuel => .outOfFuel
          | .error s => .error s
        match structural with
        | .ok deriv => .ok deriv
        | _ =>
          match subCheckSubst fuel tyCtx ((tyCtx.length, Expr.iota _annA _bodyA, Expr.iota annB bodyB) :: seen) (.iota _annA _bodyA) annB with
          | .ok annDeriv =>
              match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 (.iota _annA _bodyA)) with
              | .ok bodyB'' =>
                  match subCheckSubst fuel tyCtx ((tyCtx.length, Expr.iota _annA _bodyA, Expr.iota annB bodyB) :: seen) (.iota _annA _bodyA) bodyB'' with
                  | .ok bodyDeriv =>
                      have hbridge := (evalSubst_equiv_open' ((tyCtx.length, Expr.iota _annA _bodyA, Expr.iota annB bodyB) :: seen) tyCtx hev).1
                      .ok (.iota_intro annDeriv (bodyDeriv.trans hbridge))
                  | .outOfFuel => .outOfFuel
                  | .error s => .error s
              | .outOfFuel => .outOfFuel
              | .error _ => .error "iota fallback: eval body failed"
          | .outOfFuel => .outOfFuel
          | .error s => .error s
    | .fix _annA _bodyA, .fix annB bodyB =>
        let structural : Outcome (Subtype' seen tyCtx (.fix _annA _bodyA) (.fix annB bodyB)) :=
          match subCheckSubst fuel tyCtx seen _annA annB with
          | .ok annDeriv =>
              match subCheckSubst fuel (annB :: tyCtx) seen _bodyA bodyB with
              | .ok bodyDeriv => .ok (.fix_cong annDeriv bodyDeriv)
              | .outOfFuel => .outOfFuel
              | .error s => .error s
          | .outOfFuel => .outOfFuel
          | .error s => .error s
        match structural with
        | .ok deriv => .ok deriv
        | _ =>
          match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 (.fix annB bodyB)) with
          | .ok b' =>
              match subCheckSubst fuel tyCtx ((tyCtx.length, Expr.fix _annA _bodyA, Expr.fix annB bodyB) :: seen) (.fix _annA _bodyA) b' with
              | .ok deriv =>
                  have hbridge := (evalSubst_equiv_open' ((tyCtx.length, Expr.fix _annA _bodyA, Expr.fix annB bodyB) :: seen) tyCtx hev).1
                  .ok (.unfold_fix_R (deriv.trans hbridge))
              | .outOfFuel => .outOfFuel
              | .error s => .error s
          | .outOfFuel => .outOfFuel
          | .error _ => .error "fix fallback: eval failed"
    | a, .iota ann bodyB =>
        match subCheckSubst fuel tyCtx ((tyCtx.length, a, .iota ann bodyB) :: seen) a ann with
        | .ok annDeriv =>
            match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 a) with
            | .ok bodyB'' =>
                match subCheckSubst fuel tyCtx ((tyCtx.length, a, .iota ann bodyB) :: seen) a bodyB'' with
                | .ok bodyDeriv =>
                    have hbridge := (evalSubst_equiv_open' ((tyCtx.length, a, .iota ann bodyB) :: seen) tyCtx hev).1
                    .ok (.iota_intro annDeriv (bodyDeriv.trans hbridge))
                | .outOfFuel => .outOfFuel
                | .error s => .error s
            | .outOfFuel => .outOfFuel
            | .error _ => .error "iotaIntro: eval body failed"
        | .outOfFuel => .outOfFuel
        | .error s => .error s
    | a, .fix _ann bodyB =>
        -- Try neutral ascent: if `a` is neutral with synthesized type = target fix
        if isNeutral a then
          match synthNeutralWithDeriv fuel tyCtx seen a with
          | .ok (some ⟨ty, haDeriv⟩) =>
              if heq : ty = Expr.fix _ann bodyB then
                .ok (heq ▸ haDeriv)
              else
                match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 (.fix _ann bodyB)) with
                | .ok b' =>
                    match subCheckSubst fuel tyCtx ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) a b' with
                    | .ok deriv =>
                        have hbridge := (evalSubst_equiv_open' ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) tyCtx hev).1
                        .ok (.unfold_fix_R (deriv.trans hbridge))
                    | .outOfFuel => .outOfFuel
                    | .error s => .error s
                | .outOfFuel => .outOfFuel
                | .error _ => .error "unfoldFixR: eval failed"
          | _ =>
              match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 (.fix _ann bodyB)) with
              | .ok b' =>
                  match subCheckSubst fuel tyCtx ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) a b' with
                  | .ok deriv =>
                      have hbridge := (evalSubst_equiv_open' ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) tyCtx hev).1
                      .ok (.unfold_fix_R (deriv.trans hbridge))
                  | .outOfFuel => .outOfFuel
                  | .error s => .error s
              | .outOfFuel => .outOfFuel
              | .error _ => .error "unfoldFixR: eval failed"
        else
          match hev : evalSubst (fuel + 1) unfBound (bodyB.subst 0 (.fix _ann bodyB)) with
          | .ok b' =>
              match subCheckSubst fuel tyCtx ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) a b' with
              | .ok deriv =>
                  have hbridge := (evalSubst_equiv_open' ((tyCtx.length, a, Expr.fix _ann bodyB) :: seen) tyCtx hev).1
                  .ok (.unfold_fix_R (deriv.trans hbridge))
              | .outOfFuel => .outOfFuel
              | .error s => .error s
          | .outOfFuel => .outOfFuel
          | .error _ => .error "unfoldFixR: eval failed"
    | .fix _ann bodyA, b =>
        match hev : evalSubst (fuel + 1) unfBound (bodyA.subst 0 (.fix _ann bodyA)) with
        | .ok a' =>
            if a' == Expr.fix _ann bodyA then .error "unfoldFixL: fixpoint"
            else
              match subCheckSubst fuel tyCtx ((tyCtx.length, Expr.fix _ann bodyA, b) :: seen) a' b with
              | .ok deriv =>
                  have hbridge := (evalSubst_equiv_open' ((tyCtx.length, Expr.fix _ann bodyA, b) :: seen) tyCtx hev).2
                  .ok (.unfold_fix_L (hbridge.trans deriv))
              | .outOfFuel => .outOfFuel
              | .error s => .error s
        | .outOfFuel => .outOfFuel
        | .error _ => .error "unfoldFixL: eval failed"
    | .iota _ann bodyA, b =>
        match hev : evalSubst (fuel + 1) unfBound (bodyA.subst 0 (.iota _ann bodyA)) with
        | .ok a' =>
            if a' == Expr.iota _ann bodyA then .error "unfoldIotaL: fixpoint"
            else
              match subCheckSubst fuel tyCtx ((tyCtx.length, Expr.iota _ann bodyA, b) :: seen) a' b with
              | .ok deriv =>
                  have hbridge := (evalSubst_equiv_open' ((tyCtx.length, Expr.iota _ann bodyA, b) :: seen) tyCtx hev).2
                  .ok (.unfold_iota_L (hbridge.trans deriv))
              | .outOfFuel => .outOfFuel
              | .error s => .error s
        | .outOfFuel => .outOfFuel
        | .error _ => .error "unfoldIotaL: eval failed"
    | a, b =>
        -- Neutral handling: try spine comparison, then neutral ascent
        if isNeutral a then
          match subCheckSpine fuel tyCtx seen a b with
          | .ok deriv => .ok deriv
          | _ =>
            match neutralAscent fuel tyCtx seen a b with
            | .ok deriv => .ok deriv
            | .outOfFuel => .outOfFuel
            | .error s => .error s
        else .error "shape mismatch"
  termination_by (fuel, 1)
  decreasing_by all_goals (simp_wf; omega)

  /-- Compare two neutral spines structurally. -/
  def subCheckSpine (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome (Subtype' seen tyCtx a b) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a, b with
      | .bvar k1, .bvar k2 =>
          if h : k1 = k2 then .ok (h ▸ .refl _) else .error "spine: bvar mismatch"
      | .app f1 v1, .app f2 v2 =>
          match subCheckSpine fuel tyCtx seen f1 f2 with
          | .ok hdDeriv =>
              match subCheckSubst fuel tyCtx seen v1 v2 with
              | .ok fwdDeriv =>
                  match subCheckSubst fuel tyCtx seen v2 v1 with
                  | .ok bwdDeriv => .ok (.app_cong hdDeriv fwdDeriv bwdDeriv)
                  | .outOfFuel => .outOfFuel
                  | .error s => .error s
              | .outOfFuel => .outOfFuel
              | .error s => .error s
          | .outOfFuel => .outOfFuel
          | .error s => .error s
      | _, _ => .error "spine: shape mismatch"
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral spine and produce a derivation
      that the neutral is a subtype of that type. -/
  def synthNeutralWithDeriv (fuel : Nat) (tyCtx : TyCtx) (seen : Seen)
      (a : Expr) : Outcome (Option (Σ ty : Expr, Subtype' seen tyCtx a ty)) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a with
      | .bvar k =>
          match hget : tyCtx.get? k with
          | some ty => .ok (some ⟨ty.shift (k + 1) 0, .bvar hget⟩)
          | none => .ok none
      | .fix ann _ =>
          match hev : evalSubst (fuel + 1) unfBound ann with
          | .ok ann' =>
              let hbridge := (evalSubst_equiv_open' seen tyCtx hev).2
              .ok (some ⟨ann', .trans .fix_ann hbridge⟩)
          | _ => .ok none
      | .app f arg =>
          match synthNeutralWithDeriv fuel tyCtx seen f with
          | .ok (some ⟨fTy, hfDeriv⟩) =>
              match hwp : exposePi fuel f fTy with
              | some (.lam _dom retTy) =>
                  let retTy' := retTy.subst 0 arg
                  match hev : evalSubst (fuel + 1) unfBound retTy' with
                  | .ok r =>
                      let hfPi := exposePi_deriv seen tyCtx hfDeriv hwp
                      let hApp := Subtype'.app_elim hfPi
                      let hbridge := (evalSubst_equiv_open' seen tyCtx hev).2
                      .ok (some ⟨r, hApp.trans hbridge⟩)
                  | _ => .ok none
              | _ => .ok none
          | .ok none => .ok none
          | .outOfFuel => .outOfFuel
          | .error s => .error s
      | _ => .ok none
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral spine and check against `b`. -/
  def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome (Subtype' seen tyCtx a b) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match synthNeutralWithDeriv fuel tyCtx seen a with
      | .ok (some ⟨ty, haDeriv⟩) =>
          match subCheckSubst fuel tyCtx seen ty b with
          | .ok tyB => .ok (haDeriv.trans tyB)
          | .outOfFuel => .outOfFuel
          | .error s => .error s
      | .ok none => .error "neutralAscent: synth failed"
      | .outOfFuel => .outOfFuel
      | .error s => .error s
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral. Walks the spine, looking up
      head bvars in `tyCtx` (via de Bruijn index) and applying argument
      types to function types via `Expr.subst`. When the synthesised
      type at a spine step is a `.fix` or `.iota`, unfold it via
      `exposePi` to expose the underlying `.lam` and continue.
      A `.fix` at the spine head ascends to its annotation.
      Exposed for soundness proofs. -/
  def synthNeutralType (fuel : Nat) (tyCtx : TyCtx)
      (a : Expr) : Outcome (Option Expr) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a with
      | .bvar k =>
          match tyCtx.get? k with
          | some ty =>
              .ok (some (ty.shift (k + 1) 0))
          | none => .ok none
      | .fix ann _ =>
          match evalSubst (fuel + 1) unfBound ann with
          | .ok ann' => .ok (some ann')
          | _ => .ok none
      | .app f arg => do
          match (← synthNeutralType fuel tyCtx f) with
          | some ty =>
              match exposePi fuel f ty with
              | some (.lam _dom retTy) =>
                  let retTy' := retTy.subst 0 arg
                  match evalSubst (fuel + 1) unfBound retTy' with
                  | .ok r => .ok (some r)
                  | _ => .ok none
              | _ => .ok none
          | _ => .ok none
      | _ => .ok none
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)
end


/-- Structural subtype check on closed `Expr`s: WHNF both sides,
    then descend through `subCheckSubst`. Public so `TyCheck.typeCheck`
    can call it on conversion goals; the `subCheckSubst` mutual
    block stays private. -/
def subCheck (fuel : Nat) (a b : Expr) : Outcome Bool :=
  match subCheckSubst fuel [] [] a b with
  | .ok _ => .ok true
  | .outOfFuel => .outOfFuel
  | .error _ => .ok false

/-! ## Open-context API for `TyCheck` and `API`

The bidirectional type-checker and the synth walk need:

  - a way to substitute a value for the outermost binder (`substTop`),
  - a way to compare two types in a non-empty type context (`subCheckOpen`).

In the pure de Bruijn regime, binder-opening is trivial: we just recurse
on the raw body with an extended context. No fresh variable substitution
is needed. `freshLevelVar` is kept as a compatibility shim that returns
`bvar (depth)` — this represents the outermost free variable when the
context has `depth + 1` entries after a push.
-/

/-- Compatibility shim: in the old level-var regime, this returned
    `bvar (levelOffset + level)`. In pure de Bruijn, the "fresh variable"
    at depth `d` (after pushing to make context size `d+1`) is simply
    `bvar 0` — the innermost binder. This function is retained for
    callers that need to construct a reference to a specific context
    entry by its push-order index (level). The corresponding de Bruijn
    index is `currentDepth - 1 - level`. -/
def freshLevelVar (level : Nat) : Expr := .bvar level

/-- Substitute a value for the outermost binder of `body`. Uses
    standard de Bruijn substitution. -/
def substTop (body : Expr) (value : Expr) : Expr :=
  body.subst 0 value

/-- Subtype check in a non-empty type context. Forces WHNF on both
    sides, then delegates to the structural engine. -/
def subCheckOpen (fuel : Nat) (tyCtx : TyCtx) (a b : Expr) :
    Outcome Bool :=
  match subCheckSubst fuel tyCtx [] a b with
  | .ok _ => .ok true
  | .outOfFuel => .outOfFuel
  | .error _ => .ok false

/-- Walk a neutral spine to compute its declarative type, looking
up bvars in `tyCtx` and applying argument types through `Π` bodies
via `Expr.subst`. Public mirror of the internal `synthNeutralType`.

`Och.synth` calls this from its `.app` arm to recover the Π type
of a neutral function head.

- `.ok (some ty)` — neutral head ascended to type `ty` (in WHNF).
- `.ok none` — `a` is not a neutral, or its head is unbound.
- `.outOfFuel` — fuel exhausted. -/
def neutralType (fuel : Nat) (tyCtx : TyCtx) (a : Expr) :
    Outcome (Option Expr) :=
  synthNeutralType fuel tyCtx a

/-! ## Π-exposure helper

`Och.synth` (`Och/API.lean`) needs to destructure the synthesised
type/value of an applied head as a `.lam dom body` (a Π). When the
head is a `.fix`/`.iota`, we unfold the wrapper one or more times
to expose the underlying Π. -/

/-- Unfold a `.fix` / `.iota` wrapper in `ty` until a `.lam`
(Π) is exposed, returning the Π. The `inhab` argument is what
to substitute for the `ι`-self when unfolding `.iota` (= the
*inhabitant* whose type we're computing). For `.fix`, the self
is substituted with the fix itself (μ-unfold).

- `some (.lam dom body)` — Π exposed.
- `some other` — non-Π head after WHNF.
- `none` — `.bot` or evaluation failure. -/
def whnfPi (fuel : Nat) (inhab : Expr) (ty : Expr) : Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

/-- The `go` helper of `exposePi` computes the same result as `whnfPi.go`. -/
private theorem exposePi_go_eq_whnfPi_go (fuel : Nat) (inhab : Expr)
    : ∀ (n : Nat) (e : Expr),
      exposePi.go fuel inhab n e = whnfPi.go fuel inhab n e := by
  intro n
  induction n with
  | zero => intro e; cases e <;> rfl
  | succ m ih =>
    intro e
    match e with
    | .lam _ _ => rfl
    | .fix _ann body =>
      simp only [exposePi.go, whnfPi.go]
      match evalSubst fuel 4 (body.subst 0 (.fix _ann body)) with
      | .ok e' => exact ih e'
      | .outOfFuel => rfl
      | .error _ => rfl
    | .iota _ann body =>
      simp only [exposePi.go, whnfPi.go]
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => exact ih e'
      | .outOfFuel => rfl
      | .error _ => rfl
    | .bot => rfl
    | .bvar _ => rfl
    | .type => rfl
    | .app _ _ => rfl
    | .asc _ _ => rfl
    | .letE _ _ => rfl

/-- `exposePi` (private, used by `synthNeutralType`) computes the same
result as `whnfPi` (public). Proved inside the section where
`exposePi` is in scope, exposed for soundness proofs that need
to reason about `synthNeutralType`'s internal call to `exposePi`. -/
theorem exposePi_eq_whnfPi (fuel : Nat) (inhab ty : Expr) :
    exposePi fuel inhab ty = whnfPi fuel inhab ty := by
  unfold exposePi whnfPi
  match evalSubst fuel unfBound ty with
  | .ok ty' => exact exposePi_go_eq_whnfPi_go fuel inhab unfBound ty'
  | .outOfFuel => rfl
  | .error _ => rfl

end SubstEval
