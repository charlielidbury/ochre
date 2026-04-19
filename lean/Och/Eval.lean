import Och.Syntax

/-!
# Och concrete evaluation

`concEval` is the substitution-based CBV big-step evaluator for closed
terms. Lambdas and ι/fix binders are values (bodies not evaluated until
applied). `(e : τ)` erases to `e`. ι/fix unroll only when applied (the
mu-app dispatch: substitute the self-reference, then re-apply).

This is the *runtime* evaluator targeted by `concEval_preservation` in
`Soundness.lean`.

## Legacy checker removed

The Expr-domain abstract evaluator (`absEval`/`subCheckNF`/`neutralType`/
`subCheck`/`absEvalVal`/`NfExpr`/`TyCtx`) was removed at this commit. It
predated the NbE/Val-domain pipeline and was kept only for the
divergence sweep in `SoundnessAudit.lean`, which had served its purpose
(it found A1–A8; the only remaining divergence was the documented A6
incompleteness). The Phase-2 soundness theorem targets `NbE.subCheckVal`
(`SubCheckVal.lean`) via `NbE.typeCheck` (`TyCheck.lean`); maintaining a
parallel checker was a tax with no remaining benefit. The last revision
with the legacy checker is `38d1031`; the original combined fuel-mono
scaffold is at `f82fbfc`.
-/

open Expr

/-! ## Except instances for native_decide

These let `native_decide` discharge goals of the form
`NbE.subCheck … = .ok true` / `NbE.typeCheck … = .ok true`. Kept here
because most `Std/` modules import this file. -/

instance {ε : Type} {α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h2; cases h2; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h2; cases h2; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

instance {ε : Type} {α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a, b with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

instance {ε : Type} {α : Type} [Repr ε] [Repr α] : Repr (Except ε α) where
  reprPrec x n := match x with
    | .ok a => Repr.addAppParen (".ok " ++ reprPrec a 1) n
    | .error e => Repr.addAppParen (".error " ++ reprPrec e 1) n

/-! ## concEval -/

/-- Concrete evaluator. Standard call-by-value lambda calculus with substitution.

    Lambdas and ι/fix are values — their bodies are NOT evaluated until applied.
    Uses substitution for beta-reduction. Operates on closed terms only
    (free bvars return None). ι/fix is only unrolled when it appears in function
    position (substitute self-reference, then re-apply). -/
def concEval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEval fuel term  -- runtime: erase ascription
    | .iota _ _ => some e  -- iota is a value (only unrolled when applied)
    | .fix _ _ => some e   -- fix is a value (only unrolled when applied)
    | .letE val body =>
      match concEval fuel val with
      | some v => concEval fuel (body.subst 0 v)
      | none => none
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        concEval fuel (body.subst 0 aVal)
      | some (.iota ann body), some aVal =>
        -- iota in function position: unroll self-reference, then re-apply
        concEval fuel (.app (body.subst 0 (.iota ann body)) aVal)
      | some (.fix ann body), some aVal =>
        -- fix in function position: unroll self-reference, then re-apply
        concEval fuel (.app (body.subst 0 (.fix ann body)) aVal)
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none

/-! ## Fuel monotonicity -/

theorem concEval_fuel_mono {n : Nat} {e v : Expr}
    (h : concEval n e = some v) : concEval (n + 1) e = some v := by
  induction n generalizing e v with
  | zero => simp [concEval] at h
  | succ k ih =>
    match e with
    | .bvar _ => simp [concEval] at h
    | .lam dom body =>
      simp [concEval] at h ⊢; exact h
    | .type =>
      simp [concEval] at h ⊢; exact h
    | .asc term _ =>
      simp only [concEval] at h ⊢; exact ih h
    | .iota ann body =>
      simp [concEval] at h ⊢; exact h
    | .fix ann body =>
      simp [concEval] at h ⊢; exact h
    | .letE val body =>
      unfold concEval at h ⊢
      match hv : concEval k val with
      | none => simp [hv] at h
      | some vVal =>
        have hv' := ih hv
        simp only [hv] at h
        simp only [hv']
        exact ih h
    | .app f a =>
      unfold concEval at h ⊢
      match hf : concEval k f with
      | none => simp [hf] at h
      | some fv =>
        have hf' := ih hf
        match ha : concEval k a with
        | none => simp [hf, ha] at h
        | some av =>
          have ha' := ih ha
          simp only [hf, ha] at h
          simp only [hf', ha']
          match fv with
          | .lam _dom body => exact ih h
          | .iota ann body_mu => exact ih h
          | .fix ann body_mu => exact ih h
          | .type => exact h
          | .bvar _ | .app _ _ | .asc _ _ | .letE _ _ => exact h

/-! ## concEval shape lemmas

concEval never produces bvar/asc/letE at the top level. This is a structural
invariant: the base cases (lam, type, ι, fix) never produce them, and the
recursive cases just propagate inner results. The catch-all (neutral app)
produces app. -/

/-- concEval never produces a bare variable at the top level. -/
theorem concEval_not_bvar {fuel : Nat} {e : Expr} {k : Nat}
    (h : concEval fuel e = some (.bvar k)) : False := by
  induction fuel generalizing e with
  | zero => simp [concEval] at h
  | succ n ih =>
    cases e with
    | bvar => simp [concEval] at h
    | lam => simp [concEval] at h
    | type => simp [concEval] at h
    | asc term _ => unfold concEval at h; exact ih h
    | iota => simp [concEval] at h
    | fix => simp [concEval] at h
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match fVal with
        | .lam _ _ => exact ih h
        | .iota _ _ => exact ih h
        | .fix _ _ => exact ih h
        | .type | .bvar _ | .app _ _ | .asc _ _ | .letE _ _ =>
          injection h with h; cases h
    | letE val body =>
      unfold concEval at h
      match hv : concEval n val with
      | none => simp [hv] at h
      | some vVal => simp only [hv] at h; exact ih h

/-- concEval never produces an ascription at the top level. -/
theorem concEval_not_asc {fuel : Nat} {e : Expr} {t ty : Expr}
    (h : concEval fuel e = some (.asc t ty)) : False := by
  induction fuel generalizing e with
  | zero => simp [concEval] at h
  | succ n ih =>
    cases e with
    | bvar => simp [concEval] at h
    | lam => simp [concEval] at h
    | type => simp [concEval] at h
    | asc term _ => unfold concEval at h; exact ih h
    | iota => simp [concEval] at h
    | fix => simp [concEval] at h
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match fVal with
        | .lam _ _ => exact ih h
        | .iota _ _ => exact ih h
        | .fix _ _ => exact ih h
        | .type | .bvar _ | .app _ _ | .asc _ _ | .letE _ _ =>
          injection h with h; cases h
    | letE val body =>
      unfold concEval at h
      match hv : concEval n val with
      | none => simp [hv] at h
      | some vVal => simp only [hv] at h; exact ih h

theorem concEval_not_letE {fuel : Nat} {e v body : Expr}
    (h : concEval fuel e = some (.letE v body)) : False := by
  induction fuel generalizing e with
  | zero => simp [concEval] at h
  | succ n ih =>
    cases e with
    | bvar => simp [concEval] at h
    | lam => simp [concEval] at h
    | type => simp [concEval] at h
    | asc term _ => unfold concEval at h; exact ih h
    | iota => simp [concEval] at h
    | fix => simp [concEval] at h
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match fVal with
        | .lam _ _ => exact ih h
        | .iota _ _ => exact ih h
        | .fix _ _ => exact ih h
        | .type | .bvar _ | .app _ _ | .asc _ _ | .letE _ _ =>
          injection h with h; cases h
    | letE val body' =>
      unfold concEval at h
      match hv : concEval n val with
      | none => simp [hv] at h
      | some vVal => simp only [hv] at h; exact ih h

/-- Concrete normal form: the shape of concEval outputs.
    Values are lam/type/iota/fix (base values) or neutral applications where
    the function is not lam/iota/fix (not a redex) and sub-expressions are ConcNF. -/
inductive ConcNF : Expr → Prop
  | lam (dom body : Expr) : ConcNF (.lam dom body)
  | type : ConcNF .type
  | iota (ann body : Expr) : ConcNF (.iota ann body)
  | fix (ann body : Expr) : ConcNF (.fix ann body)
  | app (f a : Expr) : ConcNF f → ConcNF a →
      (match f with | .lam _ _ | .iota _ _ | .fix _ _ | .letE _ _ => False | _ => True) → ConcNF (.app f a)

/-- concEval always produces ConcNF values. -/
theorem concEval_ConcNF {fuel : Nat} {e v : Expr}
    (h : concEval fuel e = some v) : ConcNF v := by
  induction fuel generalizing e v with
  | zero => simp [concEval] at h
  | succ n ih =>
    cases e with
    | bvar => simp [concEval] at h
    | lam dom body => simp [concEval] at h; subst h; exact .lam dom body
    | type => simp [concEval] at h; subst h; exact .type
    | asc term _ => unfold concEval at h; exact ih h
    | iota ann body => simp [concEval] at h; subst h; exact .iota ann body
    | fix ann body => simp [concEval] at h; subst h; exact .fix ann body
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match hfv : fVal with
        | .lam _ _ => exact ih h
        | .iota _ _ => exact ih h
        | .fix _ _ => exact ih h
        | .type =>
          injection h with hv; subst hv
          exact ConcNF.app _ _ ConcNF.type (ih ha) True.intro
        | .bvar k => exact absurd hf (by intro h; exact concEval_not_bvar h)
        | .app f1 a1 =>
          injection h with hv; subst hv
          exact ConcNF.app _ _ (ih hf) (ih ha) True.intro
        | .asc t ty => exact absurd hf (by intro h; exact concEval_not_asc h)
        | .letE _ _ => exact absurd hf (by intro h; exact concEval_not_letE h)
    | letE val body =>
      unfold concEval at h
      match hv : concEval n val with
      | none => simp [hv] at h
      | some vVal => simp only [hv] at h; exact ih h

/-- ConcNF values are idempotent under concEval: if concEval succeeds on
    a ConcNF value, it returns the same value. This is because ConcNF values
    have no redexes (no beta-reducible lam-app or mu-app). -/
theorem ConcNF_concEval_idem {v v' : Expr} {fuel : Nat}
    (hv : ConcNF v) (h : concEval fuel v = some v') : v' = v := by
  induction hv generalizing fuel v' with
  | lam dom body =>
    cases fuel with
    | zero => simp [concEval] at h
    | succ n => simp [concEval] at h; exact h.symm
  | type =>
    cases fuel with
    | zero => simp [concEval] at h
    | succ n => simp [concEval] at h; exact h.symm
  | iota ann body =>
    cases fuel with
    | zero => simp [concEval] at h
    | succ n => simp [concEval] at h; exact h.symm
  | fix ann body =>
    cases fuel with
    | zero => simp [concEval] at h
    | succ n => simp [concEval] at h; exact h.symm
  | @app f a hf_nf ha_nf h_not_redex ih_f ih_a =>
    cases fuel with
    | zero => simp [concEval] at h
    | succ n =>
      unfold concEval at h
      match hcf : concEval n f, hca : concEval n a with
      | none, _ => simp [hcf] at h
      | some _, none => simp [hcf, hca] at h
      | some fVal, some aVal =>
        simp only [hcf, hca] at h
        have hf_eq : fVal = f := ih_f hcf
        have ha_eq : aVal = a := ih_a hca
        rw [hf_eq, ha_eq] at h
        -- f is not lam, iota, or fix (by h_not_redex), so the neutral app
        -- case fires. We need to show v' = app f a given h about concEval's
        -- match on f.
        revert h
        match f, h_not_redex with
        | .type, _ | .bvar _, _ | .app _ _, _ | .asc _ _, _ =>
          intro h; injection h with heq; exact heq.symm
        | .letE _ _, h_abs => exact h_abs.elim

/-- ConcNF implies the old isConcreteVal-or-app pattern: not bvar, not asc. -/
theorem ConcNF.not_bvar {v : Expr} (h : ConcNF v) : ∀ k, v ≠ .bvar k := by
  intro k; cases h <;> intro heq <;> cases heq

theorem ConcNF.not_asc {v : Expr} (h : ConcNF v) : ∀ t ty, v ≠ .asc t ty := by
  intro t ty; cases h <;> intro heq <;> cases heq
