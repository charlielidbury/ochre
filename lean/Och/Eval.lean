import Och.Syntax

/-!
# Och Evaluation (de Bruijn)

Two evaluators:
- **`concEval` (concrete/runtime):** Substitution-based CBV for closed terms.
  Lambdas and mus are values (bodies not evaluated until applied).
  `(e : τ)` takes the lhs `e`. Mu is only unrolled when applied (mu-app
  dispatch: substitute self-reference, then re-apply).
- **`absEval` (abstract/compile-time):** Combined normalizer + type checker.
  Uses a type context (TyCtx) instead of a value environment. Normalizes under
  binders, evaluates domains and annotations, validates ascriptions via
  subCheckNF, and checks callability for neutral applications. A term is
  well-typed iff absEval succeeds.

## Type Context (absEval)

The type context is a positional list: `ctx[k]` is the absEval'd domain type
of bvar k. When entering a lambda binder, we evaluate the domain and extend
with the evaluated form. The value env is eliminated entirely — with
mu-as-value, the value env was always the identity mapping (bvar k → bvar k).

## Beta-reduction

Both evaluators use substitution for beta-reduction. When a lambda is applied,
substitute the argument for bvar 0 in the body, then re-evaluate.
-/

open Expr

/-! ## Except instances for native_decide -/

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

/-! ## NfExpr: newtype for absEval output -/

/-- An expression that has been through absEval with some context.
    Invariants (not enforced by the type system, proved separately):
    - No `.asc` constructors (ascriptions erased)
    - No redexes (`.app (.lam ..) ..` does not occur) (normal form)
    - Well-scoped: all `.bvar k` satisfy `k < ctx.length`
    - All applications are callable: if `.app f a` occurs and `f`
      is neutral, then its synthesized type is a function type
    - All domains and mu annotations are themselves NfExprs

    This is a newtype wrapper around Expr. The safe direction (NfExpr → Expr)
    is provided via Coe. The unsafe direction (Expr → NfExpr) is only available
    via absEval, enforcing that NfExpr values are always normalized. -/
structure NfExpr where
  val : Expr
deriving DecidableEq, Repr, Inhabited

instance : BEq NfExpr where beq a b := a.val == b.val

/-- Type context: positional list of absEval'd domain types for bound variables.
    ctx[k] = absEval'd domain type of bvar k. -/
abbrev TyCtx := List NfExpr

/-- Extend a type context for a new binder. The domain type `ty` was computed
    at the outer depth; shift it by 1 so its free variable references are correct
    at the inner depth. Existing entries are also shifted. -/
def TyCtx.extend (ctx : TyCtx) (ty : NfExpr) : TyCtx :=
  ⟨ty.val.shift 1 0⟩ :: ctx.map (fun e => ⟨e.val.shift 1 0⟩)


/-! ## absEval + subCheckNF (mutual recursion)

absEval is a bidirectional normalizer + type checker. It returns both the
normal form and its synthesized type. subCheckNF is the structural subtype
checker. They are mutually recursive: absEval calls subCheckNF for ascription
and domain validation, and subCheckNF calls absEval for normalization.
Both use fuel-based termination with strictly decreasing fuel on mutual calls.

The synthesized type follows bidirectional typing:
- Variables: type from context lookup
- Lambdas/Type: self-typing (terms = types)
- Mu: annotation is the type
- Ascription: the ascribed type
- Application: return type from the function's type -/

mutual
  /-- Abstract evaluation (typing) with normalization under binders.

      Returns (value, type) — the normal form and its synthesized type.
      Lambda bodies and domains are normalized under the binder. Mu annotations
      are normalized. Ascriptions are validated via subCheckNF and erased.
      Lambda domain annotations are checked at application via subCheckNF.

      A term is well-typed iff absEval succeeds (returns some).

      The `seen` parameter (from subCheckNF) breaks cycles that arise when
      domain-checking let-bindings inside mu types.

      The `muSeen` parameter breaks cycles in mu-app normalization: when a
      mu-function's body contains (self arg) in a domain, normalizing under
      the binder would re-trigger the same mu-app indefinitely. When we detect
      a mu-app we're already normalizing, we return it as a neutral application
      instead of unfolding. This is sound because it only loses information
      (the neutral term's type is looked up from the mu annotation, which is
      always a valid over-approximation). -/
  def absEval (fuel : Nat) (ctx : TyCtx) (seen : List (Expr × Expr))
      (e : Expr) (muSeen : List (Expr × Expr) := [])
      : Except String (NfExpr × NfExpr) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match e with
      | .bvar k       =>
        let ty := match ctx.get? k with
          | some t => t
          | none => ⟨.bvar k⟩  -- out-of-scope: type is self (will fail callability)
        .ok (⟨.bvar k⟩, ty)
      | .lam dom body => do
        let (dom', _) ← absEval fuel ctx seen dom muSeen
        let (body', _) ← absEval fuel (TyCtx.extend ctx dom') seen body muSeen
        let v := ⟨.lam dom'.val body'.val⟩
        .ok (v, v)  -- self-typing: terms = types
      | .type         => .ok (⟨.type⟩, ⟨.type⟩)
      | .asc term ty  => do
        let (sigma, _) ← absEval fuel ctx seen term muSeen
        let (tau, _) ← absEval fuel ctx seen ty muSeen
        if subCheckNF fuel ctx seen sigma.val tau.val then .ok (tau, tau)
        else .error s!"ascription failed: {repr sigma} ⊄ {repr tau}"
      | .mu ann body  => do
        let (ann', _) ← absEval fuel ctx seen ann muSeen
        .ok (⟨.mu ann body⟩, ann')
      | .app f a      => do
        let (f', τ_f) ← absEval fuel ctx seen f muSeen
        let (a', _) ← absEval fuel ctx seen a muSeen
        match f'.val with
        | .lam dom body =>
          if subCheckNF fuel ctx seen a'.val dom then
            absEval fuel ctx seen (body.subst 0 a'.val) muSeen
          else .error s!"domain check failed: {repr a'} ⊄ {repr dom}"
        | .mu _ann body =>
          -- Check muSeen to break cycles in mu-app normalization.
          -- If we've already seen this (mu, arg) pair, return as neutral
          -- to avoid infinite unfolding.
          if muSeen.any (fun (m, a2) => Expr.mu _ann body == m && a'.val == a2) then
            -- Treat as neutral application: use annotation for return type
            match τ_f.val with
            | .lam _dom retTy =>
              .ok (⟨.app f'.val a'.val⟩, ⟨retTy.subst 0 a'.val⟩)
            | _ => .error s!"not callable (mu cycle): {repr f'}"
          else
            -- Fix-style unfold: (μs:A. b) a  →  b[s↦μs:A.b] a
            -- Record this mu-app in muSeen before recursing.
            let muSeen' := (Expr.mu _ann body, a'.val) :: muSeen
            absEval fuel ctx seen (.app (body.subst 0 (Expr.mu _ann body)) a'.val) muSeen'
        | .type => .error "Type is not callable"
        | _ =>
          -- Neutral application: use synthesized type of f' for callability
          -- and return type computation.
          match τ_f.val with
          | .lam _dom retTy =>
            .ok (⟨.app f'.val a'.val⟩, ⟨retTy.subst 0 a'.val⟩)
          | .mu _ann body =>
            -- mu type in function position: unfold to get return type
            let unfolded := body.subst 0 f'.val
            match unfolded with
            | .lam _dom retTy =>
              .ok (⟨.app f'.val a'.val⟩, ⟨retTy.subst 0 a'.val⟩)
            | _ => .error s!"not callable: {repr f'}"
          | _ => .error s!"not callable: {repr f'}"
  termination_by fuel

  /-- Structural subtype check on normalized terms.
      ctx: type context (positional list of domain types for bound variables).
      seen: assumed subtyping pairs for equi-recursive termination.

      Includes a variable rule: when the LHS is a bound variable, its context
      entry is looked up and the check recurses. This handles multi-hop type
      chains (e.g. b:a, a:not, not:Bool→Bool) naturally via recursion. -/
  def subCheckNF (fuel : Nat) (ctx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if a == b then true
      else if seen.any (fun (a', b') => a == a' && b == b') then true
      else match b with
      | .type => true
      | _ =>
        match a, b with
        | .lam domA bodyA, .lam domB bodyB =>
          subCheckNF fuel ctx [] domB domA
          && subCheckNF fuel (TyCtx.extend ctx ⟨domB⟩) [] bodyA bodyB
        | _, .mu _ann body =>
          let seen' := (a, b) :: seen
          let u := body.subst 0 a
          let self_intro := match absEval fuel ctx seen' u with
            | .ok (u', _) => subCheckNF fuel ctx seen' a u'.val
            | .error _ => false
          if self_intro then true
          else neutralType fuel ctx seen a b
        | .mu ann body, _ =>
          let seen' := (a, b) :: seen
          let ann_path :=
            if body != .bvar 0 then
              match absEval fuel ctx seen' ann with
              | .ok (ann', _) => subCheckNF fuel ctx seen' ann'.val b
              | .error _ => false
            else false
          if ann_path then true
          else
            let u := body.subst 0 (.mu ann body)
            match absEval fuel ctx seen' u with
            | .ok (u', _) => subCheckNF fuel ctx seen u'.val b
            | .error _ => false
        | .app f1 a1, .app f2 a2 =>
          if subCheckNF fuel ctx [] f1 f2 && subCheckNF fuel ctx [] a1 a2
          then true
          else neutralType fuel ctx seen a b
        | _, _ => neutralType fuel ctx seen a b
  termination_by fuel

  /-- Fallback for subCheckNF: look up the type of a neutral term and
      check that against b. Handles bvar (context lookup) and app (return
      type computation) with multi-hop chasing via fuel-bounded recursion. -/
  private def neutralType (fuel : Nat) (ctx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match a with
      | .bvar k =>
        match ctx.get? k with
        | some ty => subCheckNF fuel ctx seen ty.val b
        | none => false
      | .app f arg =>
        match neutralType fuel ctx seen f (.lam .type .type) with  -- dummy: just need the type
        | _ =>
          -- Compute the type of (f arg) by synthesizing f's type
          match absEval fuel ctx seen f with
          | .ok (_, τ_f) =>
            match τ_f.val with
            | .lam _dom retTy =>
              let resultTy := retTy.subst 0 arg
              subCheckNF fuel ctx seen resultTy b
            | .mu _ann body =>
              let unfolded := body.subst 0 f
              match unfolded with
              | .lam _dom retTy =>
                let resultTy := retTy.subst 0 arg
                subCheckNF fuel ctx seen resultTy b
              | _ => false
            | _ => false
          | .error _ => false
      | .mu ann _ => subCheckNF fuel ctx seen ann b
      | _ => false
  termination_by fuel
end

/-- Evaluate a closed term and return just the normal form.
    Convenience wrapper: always uses empty context and seen set. -/
def absEvalVal (e : Expr) (fuel : Nat := 10000) : Except String NfExpr :=
  (absEval fuel [] [] e).map (·.1)

/-! ## Decidable subtyping -/

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] [] a, absEval fuel [] [] b with
  | .ok (a', _), .ok (b', _) => subCheckNF fuel [] [] a'.val b'.val
  | _, _ => false

/-! ## Concrete evaluators -/

/-- Concrete evaluator. Standard call-by-value lambda calculus with substitution.

    Lambdas and mus are values — their bodies are NOT evaluated until applied.
    Uses substitution for beta-reduction. Operates on closed terms only
    (free bvars return None). Mu is only unrolled when it appears in function
    position (mu-app dispatch: substitute self-reference, then re-apply). -/
def concEval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEval fuel term  -- runtime: erase ascription
    | .mu _ _ => some e  -- mu is a value (only unrolled when applied)
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        concEval fuel (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- mu in function position: unroll self-reference, then re-apply
        concEval fuel (.app (body.subst 0 (.mu ann body)) aVal)
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
    | .mu ann body =>
      simp [concEval] at h ⊢; exact h
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
          | .mu ann body_mu => exact ih h
          | .type => exact h
          | .bvar _ | .app _ _ | .asc _ _ => exact h

/-! ## concEval shape lemmas

concEval never produces bvar or asc at the top level. This is a structural
invariant: the base cases (lam, type, mu) never produce bvar/asc, and the
recursive cases (asc-erasure, beta-reduction, mu-unrolling) just propagate
inner results. The catch-all (neutral app) produces app, not bvar/asc. -/

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
    | mu => simp [concEval] at h
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match fVal with
        | .lam _ _ => exact ih h
        | .mu _ _ => exact ih h
        | .type | .bvar _ | .app _ _ | .asc _ _ =>
          injection h with h; cases h

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
    | mu => simp [concEval] at h
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match fVal with
        | .lam _ _ => exact ih h
        | .mu _ _ => exact ih h
        | .type | .bvar _ | .app _ _ | .asc _ _ =>
          injection h with h; cases h

/-- Concrete normal form: the shape of concEval outputs.
    Values are lam/type/mu (base values) or neutral applications where
    the function is not lam/mu (not a redex) and sub-expressions are ConcNF. -/
inductive ConcNF : Expr → Prop
  | lam (dom body : Expr) : ConcNF (.lam dom body)
  | type : ConcNF .type
  | mu (ann body : Expr) : ConcNF (.mu ann body)
  | app (f a : Expr) : ConcNF f → ConcNF a →
      (match f with | .lam _ _ | .mu _ _ => False | _ => True) → ConcNF (.app f a)

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
    | mu ann body => simp [concEval] at h; subst h; exact .mu ann body
    | app f a =>
      unfold concEval at h
      match hf : concEval n f, ha : concEval n a with
      | none, _ => simp [hf] at h
      | some _, none => simp [hf, ha] at h
      | some fVal, some aVal =>
        simp only [hf, ha] at h
        match hfv : fVal with
        | .lam _ _ => exact ih h
        | .mu _ _ => exact ih h
        | .type =>
          injection h with hv; subst hv
          exact ConcNF.app _ _ ConcNF.type (ih ha) True.intro
        | .bvar k => exact absurd hf (by intro h; exact concEval_not_bvar h)
        | .app f1 a1 =>
          injection h with hv; subst hv
          exact ConcNF.app _ _ (ih hf) (ih ha) True.intro
        | .asc t ty => exact absurd hf (by intro h; exact concEval_not_asc h)

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
  | mu ann body =>
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
        -- f is not lam or mu (by h_not_redex), so the neutral app case fires
        -- We need to show v' = app f a given h about concEval's match on f
        revert h
        match f, h_not_redex with
        | .type, _ | .bvar _, _ | .app _ _, _ | .asc _ _, _ =>
          intro h; injection h with heq; exact heq.symm

/-- ConcNF implies the old isConcreteVal-or-app pattern: not bvar, not asc. -/
theorem ConcNF.not_bvar {v : Expr} (h : ConcNF v) : ∀ k, v ≠ .bvar k := by
  intro k; cases h <;> intro heq <;> cases heq

theorem ConcNF.not_asc {v : Expr} (h : ConcNF v) : ∀ t ty, v ≠ .asc t ty := by
  intro t ty; cases h <;> intro heq <;> cases heq

/-! ## Fuel monotonicity (sorryed — to be re-proved after bidirectional refactor) -/

theorem subCheckNF_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : subCheckNF n ctx seen a b = true) : subCheckNF (n + 1) ctx seen a b = true := by
  sorry

theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {v : NfExpr × NfExpr}
    (h : absEval n ctx seen e = .ok v) : absEval (n + 1) ctx seen e = .ok v := by
  sorry

theorem absEval_preserves_closedAt_d {fuel : Nat} {ctx : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {e : Expr} {τ : NfExpr × NfExpr}
    (h_abs : absEval fuel ctx seen e = .ok τ)
    (h_closed : e.closedAt d = true)
    (hctx : ctx.length = d)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    : τ.1.val.closedAt d = true := by
  sorry

theorem subCheckNF_ctx_irrelevant {fuel : Nat} {ctx ctx' : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {a b : Expr}
    (ha : a.closedAt d = true) (hb : b.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    : subCheckNF fuel ctx seen a b = subCheckNF fuel ctx' seen a b := by
  sorry

theorem absEval_ctx_irrelevant {fuel : Nat} {ctx ctx' : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {e : Expr}
    (he : e.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    : absEval fuel ctx seen e = absEval fuel ctx' seen e := by
  sorry

/-- Fuel monotonicity with ≤ for subCheckNF. -/
theorem subCheckNF_fuel_mono_le {n m : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : subCheckNF n ctx seen a b = true) (hle : n ≤ m) : subCheckNF m ctx seen a b = true := by
  induction m generalizing n with
  | zero => have := Nat.le_zero.mp hle; subst this; exact h
  | succ k ih =>
    by_cases heq : n = k + 1
    · subst heq; exact h
    · have hlt : n ≤ k := by omega
      exact subCheckNF_fuel_mono (ih h hlt)

theorem absEval_preserves_closedAt {fuel : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {τ : NfExpr × NfExpr}
    (h_abs : absEval fuel ctx seen e = .ok τ)
    (h_closed : e.closedAt ctx.length = true)
    : τ.1.val.closedAt ctx.length = true := by
  sorry
