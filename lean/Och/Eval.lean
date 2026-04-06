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
      is neutral, then `inferType ctx f` is a function type
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


/-! ## Type inference for neutral terms -/

/-- Infer the type of a neutral term from a typing context.
    ctx is a positional list: ctx[k] is the type/domain of bvar k.
    Operates on raw Expr (not NfExpr) — used for callability checks
    and subCheckNF's inferType fallback. -/
def inferType (ctx : TyCtx) : Expr → Option Expr
  | .bvar k => (ctx.get? k).map (·.val)
  | .mu ann _body => some ann
  | .app f a =>
    match inferType ctx f with
    | some (.lam _dom retTy) => some (retTy.subst 0 a)
    | some (.mu _ann body) =>
      -- Self-type elimination: unfold, then infer
      let unfolded := body.subst 0 f
      match unfolded with
      | .lam _dom retTy => some (retTy.subst 0 a)
      | _ => none
    | _ => none
  | _ => none

/-- Check that a normalized term in function position has a function type.
    Uses inferType to determine the type. Only lam and mu are considered callable.
    Type (top) means "unknown" and is rejected — calling something of
    unknown type is unsound. -/
def isCallableNF (ctx : TyCtx) (f : NfExpr) : Bool :=
  match f.val with
  | .lam _ _ => true
  | .mu _ _ => true
  | _ =>
    match inferType ctx f.val with
    | some (.lam _ _) => true
    | some (.mu _ _) => true
    | _ => false

/-! ## absEval + subCheckNF (mutual recursion)

absEval is a beta-normalizer with ascription erasure, validation, and
type checking. subCheckNF is the structural subtype checker. They are
mutually recursive: absEval calls subCheckNF for ascription validation,
and subCheckNF calls absEval for normalization. Both use fuel-based
termination with strictly decreasing fuel on mutual calls. -/

mutual
  /-- Abstract evaluation (typing) with normalization under binders.

      Lambda bodies and domains are normalized under the binder. Mu annotations
      are normalized. Ascriptions are validated via subCheckNF and erased.
      Lambda domain annotations are checked at application via subCheckNF.
      Neutral applications are validated for callability via inferType.

      A term is well-typed iff absEval succeeds (returns some).

      The `seen` parameter (from subCheckNF) breaks cycles that arise when
      domain-checking let-bindings inside mu types. E.g. checking
      `dtrue_val <: dBool` inside dBool's own body is already in `seen`
      from the outer subtype check. -/
  def absEval (fuel : Nat) (ctx : TyCtx) (seen : List (Expr × Expr))
      (e : Expr) (lenient : Bool := false) : Except String NfExpr :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match e with
      | .bvar k       => .ok ⟨.bvar k⟩
      | .lam dom body => do
        -- Evaluate domain (rejects ill-formed domains)
        let dom' ← absEval fuel ctx seen dom lenient
        -- Evaluate body under binder with evaluated domain in context
        let body' ← absEval fuel (TyCtx.extend ctx dom') seen body lenient
        .ok ⟨.lam dom'.val body'.val⟩
      | .type         => .ok ⟨.type⟩
      | .asc term ty  => do
        -- Type checking happens here:
        -- 1. Evaluate term → sigma
        -- 2. Evaluate ty → tau
        -- 3. Check sigma ⊑ tau via subCheckNF
        -- 4. Return tau (erase term)
        let sigma ← absEval fuel ctx seen term lenient
        let tau ← absEval fuel ctx seen ty lenient
        if subCheckNF fuel ctx seen sigma.val tau.val then .ok tau
        else .error s!"ascription failed: {repr sigma} ⊄ {repr tau}"
      | .mu ann body  => do
        -- Validate annotation is well-formed.
        let _ann' ← absEval fuel ctx seen ann lenient
        -- Check body under extended context in LENIENT mode.
        -- The body check provides soundness_open with body info (Phase 0).
        -- Lenient mode: domain/callability checks are optimistic for neutral
        -- terms, allowing the body to evaluate despite abstract lambda params.
        -- Only fires when lenient=false (top-level) to avoid double-checking.
        if !lenient then
          let _ ← absEval fuel (TyCtx.extend ctx ⟨.mu ann body⟩) [] body true
        .ok ⟨.mu ann body⟩
      | .app f a      => do
        let f' ← absEval fuel ctx seen f lenient
        let a' ← absEval fuel ctx seen a lenient
        match f'.val with
        | .lam dom body =>
          -- Check argument against domain annotation, then beta-reduce.
          -- `dom` is already normalized (it's a sub-expression of f', an absEval
          -- output), so re-normalization is unnecessary. Using it directly also
          -- makes fuel monotonicity provable without an idempotency lemma.
          -- In lenient mode, skip domain check for neutral args (bvar, app).
          -- This allows mu body checking to proceed with abstract lambda params.
          if subCheckNF fuel ctx seen a'.val dom || (lenient && a'.val.isNeutral) then
            absEval fuel ctx seen (body.subst 0 a'.val) lenient
          else .error s!"domain check failed: {repr a'} ⊄ {repr dom}"
        | .mu _ann body =>
          -- mu in function position. Strategy depends on ann AND body shape.
          match _ann, body with
          | .lam _dom retBody, .lam _ _ =>
            -- Annotation is a function type: use annotation's return type.
            -- This trusts the annotation as the type of the recursive function,
            -- avoiding normalization of the raw body (which may fail for
            -- abstract arguments due to domain checks on Church-encoded types).
            absEval fuel ctx seen (retBody.subst 0 a'.val) lenient
          | _, .lam _dom _retBody =>
            -- Annotation is not a function type: substitute self-reference
            -- into the body, then beta-reduce. Uses `seen` set to break
            -- infinite loops for recursive functions.
            let mu_expr := Expr.mu _ann body
            if seen.any (fun (a', _) => a' == mu_expr) then
              .ok ⟨.app mu_expr a'.val⟩
            else
              let seen' := (mu_expr, mu_expr) :: seen
              let unfolded := body.subst 0 mu_expr
              match unfolded with
              | .lam _dom2 retBody2 =>
                absEval fuel ctx seen' (retBody2.subst 0 a'.val) lenient
              | _ =>
                absEval fuel ctx seen' (.app unfolded a'.val) lenient
          | _, _ =>
            -- Non-lam body: substitute self-reference before extracting body.
            -- Without this, bvar 0 (self-reference) would dangle outside the mu scope.
            .ok ⟨.app (body.subst 0 (Expr.mu _ann body)) a'.val⟩
        | .type => .error "Type is not callable"
        | _ =>
          -- Neutral application: validate callability, return symbolic app.
          -- In lenient mode, accept all neutral apps optimistically.
          if isCallableNF ctx f' || lenient then .ok ⟨.app f'.val a'.val⟩
          else .error s!"not callable: {repr f'}"
  termination_by fuel

  /-- Structural subtype check on normalized terms.
      ctx: type context (positional list of domain types for bound variables).
      seen: assumed subtyping pairs for equi-recursive termination. -/
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
          -- Function subtyping: contravariant domain, covariant body.
          -- Domains are used directly (no re-normalization). When inputs come
          -- from absEval output, domains are already normalized. When inputs
          -- come from mu unfolding with fallback, domains may be raw but
          -- re-normalization was a no-op anyway (same expression goes in and
          -- out). Using domains directly makes fuel monotonicity provable:
          -- the inputs to recursive subCheckNF calls don't change with fuel.
          -- Uses empty seen for structural checks: equi-recursive assumptions
          -- from the outer context don't apply to structural sub-components,
          -- and this makes the adequacy proof tractable (seen callback is vacuous).
          subCheckNF fuel ctx [] domB domA
          && subCheckNF fuel (TyCtx.extend ctx ⟨domB⟩) [] bodyA bodyB
        | _, .mu _ann body =>
          -- Self-intro (self-type / iota): a ⊑ mu ann body  iff  a ⊑ body[0 := a]
          -- The self-reference is substituted with the VALUE being checked (a),
          -- not the type (mu ann body). This is what makes dependent elimination
          -- possible for Scott-encoded data.
          let seen' := (a, b) :: seen
          let u := body.subst 0 a
          match absEval fuel ctx seen' u with
          | .ok u' => subCheckNF fuel ctx seen' a u'.val
          | .error _ => false
        | .mu ann body, _ =>
          -- Self-elim: mu ann body ⊑ b  iff  ann ⊑ b  or  normalize(body[0:=mu]) ⊑ b.
          --
          -- ANNOTATION PATH: Normalize annotation on demand (since absEval's mu
          -- case keeps raw annotations for soundness). Only valid when the body
          -- is productive (not a pure self-reference). For non-productive bodies
          -- like `bvar 0`, the mu unfolds to itself, making it a "universal" type
          -- via self-intro. Trusting the annotation for such types creates
          -- transitivity violations: `a ⊑ mu ann (bvar 0) ⊑ ann` but `a ⋢ ann`.
          --
          -- BODY PATH: The final subCheckNF uses `seen` (not `seen'`) to prevent
          -- circular reasoning via the seen-set hit.
          let seen' := (a, b) :: seen
          let ann_path :=
            if body != .bvar 0 then
              match absEval fuel ctx seen' ann with
              | .ok ann' => subCheckNF fuel ctx seen' ann'.val b
              | .error _ => false
            else false
          if ann_path then true
          else
            let u := body.subst 0 (.mu ann body)
            match absEval fuel ctx seen' u with
            | .ok u' => subCheckNF fuel ctx seen u'.val b
            | .error _ => false
        | .app f1 a1, .app f2 a2 =>
          -- App congruence: f a ⊑ g b when f ⊑ g and a ⊑ b.
          -- Uses empty seen for structural checks: the outer equi-recursive
          -- assumptions don't apply to sub-components, and this makes the
          -- adequacy proof possible (seen callback is vacuous for []).
          if subCheckNF fuel ctx [] f1 f2 && subCheckNF fuel ctx [] a1 a2
          then true
          else
            match inferType ctx a with
            | some ty =>
              match absEval fuel ctx seen ty with
              | .ok ty' => subCheckNF fuel ctx seen ty'.val b
              | .error _ => false
            | none => false
        | _, _ =>
          match inferType ctx a with
          | some ty =>
            match absEval fuel ctx seen ty with
            | .ok ty' => subCheckNF fuel ctx seen ty'.val b
            | .error _ => false
          | none => false
  termination_by fuel
end

/-! ## Decidable subtyping -/

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] [] a, absEval fuel [] [] b with
  | .ok a', .ok b' => subCheckNF fuel [] [] a'.val b'.val
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

/-! ## Fuel monotonicity (mutual proof)

absEval and subCheckNF are mutually recursive, so their fuel monotonicity
proofs must be proved together. We prove a combined theorem by induction on
fuel, then extract the individual results. -/

/-- Helper for the mu-app case in absEval_fuel_mono: body' is lam and _ann is
    NOT lam. Parameterized by ih_abs (absEval at fuel k → k+1). -/
private theorem absEval_fuel_mono_mu_lam_body
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {_ann : Expr} {d1 b1 : Expr} {a'val : Expr} {v : NfExpr}
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr} {lenient : Bool},
          absEval k ctx seen e lenient = .ok v → absEval (k + 1) ctx seen e lenient = .ok v)
    {lenient : Bool}
    (h : (let mu_expr := Expr.mu _ann (Expr.lam d1 b1)
          if (seen.any fun x => x.fst == mu_expr) = true then
            Except.ok { val := mu_expr.app a'val }
          else
            match (Expr.lam d1 b1).subst 0 mu_expr with
            | .lam _d3 rB3 => absEval k ctx ((mu_expr, mu_expr) :: seen) (rB3.subst 0 a'val) lenient
            | _ => absEval k ctx ((mu_expr, mu_expr) :: seen)
                     (((Expr.lam d1 b1).subst 0 mu_expr).app a'val) lenient)
         = Except.ok v)
    : (let mu_expr := Expr.mu _ann (Expr.lam d1 b1)
       if (seen.any fun x => x.fst == mu_expr) = true then
         Except.ok { val := mu_expr.app a'val }
       else
         match (Expr.lam d1 b1).subst 0 mu_expr with
         | .lam _d3 rB3 => absEval (k + 1) ctx ((mu_expr, mu_expr) :: seen) (rB3.subst 0 a'val) lenient
         | _ => absEval (k + 1) ctx ((mu_expr, mu_expr) :: seen)
                  (((Expr.lam d1 b1).subst 0 mu_expr).app a'val) lenient)
      = Except.ok v := by
  simp only [] at h ⊢
  by_cases hc : (seen.any fun x => x.fst == Expr.mu _ann (Expr.lam d1 b1)) = true
  · simp only [hc] at h ⊢; exact h
  · simp only [hc, ite_false] at h ⊢
    generalize Expr.subst (Expr.lam d1 b1) 0 (Expr.mu _ann (Expr.lam d1 b1)) = u at h ⊢
    cases u <;> exact ih_abs h

/-- Helper for the "match absEval ... with | ok => subCheckNF | error => false"
    pattern. Takes both ih_sub and ih_abs as parameters. -/
private theorem subCheckNF_absEval_step
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {b : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (match absEval k ctx seen e with
          | .ok ty' => subCheckNF k ctx seen ty'.val b
          | .error _ => false) = true)
    : (match absEval (k + 1) ctx seen e with
       | .ok ty' => subCheckNF (k + 1) ctx seen ty'.val b
       | .error _ => false) = true := by
  match hae : absEval k ctx seen e with
  | .ok ty' =>
    simp only [hae] at h
    rw [show absEval (k + 1) ctx seen e = .ok ty' from ih_abs hae]
    exact ih_sub h
  | .error _ => simp [hae] at h

/-- Mirror of subCheckNF_absEval_step: absEval result goes to second position
    of subCheckNF (for the self-intro case: subCheckNF ... a u'.val). -/
private theorem subCheckNF_absEval_step_right
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {a : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (match absEval k ctx seen e with
          | .ok u' => subCheckNF k ctx seen a u'.val
          | .error _ => false) = true)
    : (match absEval (k + 1) ctx seen e with
       | .ok u' => subCheckNF (k + 1) ctx seen a u'.val
       | .error _ => false) = true := by
  match hae : absEval k ctx seen e with
  | .ok u' =>
    simp only [hae] at h
    rw [show absEval (k + 1) ctx seen e = .ok u' from ih_abs hae]
    exact ih_sub h
  | .error _ => simp [hae] at h

/-- Helper for the self-elim annotation path: normalize annotation, then subcheck. -/
private theorem subCheckNF_self_elim_ann_step
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {ann : Expr} {b : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (match absEval k ctx seen ann with
          | .ok ann' => subCheckNF k ctx seen ann'.val b
          | .error _ => false) = true)
    : (match absEval (k + 1) ctx seen ann with
       | .ok ann' => subCheckNF (k + 1) ctx seen ann'.val b
       | .error _ => false) = true := by
  match hae : absEval k ctx seen ann with
  | .ok ann' =>
    simp only [hae] at h
    rw [show absEval (k + 1) ctx seen ann = .ok ann' from ih_abs hae]
    exact ih_sub h
  | .error _ => simp [hae] at h

/-- Helper for the self-elim case: annotation path (with normalization) + body normalization. -/
private theorem subCheckNF_self_elim_step
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {ann body : Expr} {b : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (let seen' := (Expr.mu ann body, b) :: seen
          let ann_path :=
            if body != .bvar 0 then
              match absEval k ctx seen' ann with
              | .ok ann' => subCheckNF k ctx seen' ann'.val b
              | .error _ => false
            else false
          if ann_path then true
          else
            let u := body.subst 0 (Expr.mu ann body)
            match absEval k ctx seen' u with
            | .ok u' => subCheckNF k ctx seen u'.val b
            | .error _ => false) = true)
    : (let seen' := (Expr.mu ann body, b) :: seen
       let ann_path :=
         if body != .bvar 0 then
           match absEval (k + 1) ctx seen' ann with
           | .ok ann' => subCheckNF (k + 1) ctx seen' ann'.val b
           | .error _ => false
         else false
       if ann_path then true
       else
         let u := body.subst 0 (Expr.mu ann body)
         match absEval (k + 1) ctx seen' u with
         | .ok u' => subCheckNF (k + 1) ctx seen u'.val b
         | .error _ => false) = true := by
  -- Both annotation path and body path are monotone in fuel.
  -- Structure: if ann_path then true else body_path.
  -- Strategy: show body_path@(k+1) = true whenever body_path@k = true,
  -- and ann_path@(k+1) = true whenever ann_path@k = true.
  -- Then: at fuel k, either ann_path or body_path is true.
  -- If ann_path@k: ann_path@(k+1), so overall is true.
  -- If body_path@k: body_path@(k+1), and overall = if X then true else true = true.
  -- Key helper: if X then true else Y = Y || X (both give true when either is true).
  -- But we just need: if either the new ann_path or new body_path is true, overall is true.
  -- if ann_path then true else body_path = true ↔ ann_path = true ∨ body_path = true
  have ite_or : ∀ (a b : Bool), (if a then true else b) = true ↔ a = true ∨ b = true := by
    intro a b; cases a <;> simp
  -- Apply to h and goal
  rw [ite_or] at h ⊢
  -- Body path monotonicity
  have body_mono : (match absEval k ctx ((Expr.mu ann body, b) :: seen)
        (body.subst 0 (Expr.mu ann body)) with
      | .ok u' => subCheckNF k ctx seen u'.val b
      | .error _ => false) = true →
    (match absEval (k + 1) ctx ((Expr.mu ann body, b) :: seen)
        (body.subst 0 (Expr.mu ann body)) with
      | .ok u' => subCheckNF (k + 1) ctx seen u'.val b
      | .error _ => false) = true := by
    intro hb
    match hae : absEval k ctx ((Expr.mu ann body, b) :: seen) (body.subst 0 (Expr.mu ann body)) with
    | .ok ty' =>
      simp only [hae] at hb
      rw [ih_abs hae]; exact ih_sub hb
    | .error _ => simp [hae] at hb
  -- Annotation path monotonicity
  have ann_mono : (if (body != Expr.bvar 0) = true then
      match absEval k ctx ((Expr.mu ann body, b) :: seen) ann with
      | .ok ann' => subCheckNF k ctx ((Expr.mu ann body, b) :: seen) ann'.val b
      | .error _ => false
    else false) = true →
    (if (body != Expr.bvar 0) = true then
      match absEval (k + 1) ctx ((Expr.mu ann body, b) :: seen) ann with
      | .ok ann' => subCheckNF (k + 1) ctx ((Expr.mu ann body, b) :: seen) ann'.val b
      | .error _ => false
    else false) = true := by
    intro ha
    cases hbody : (body != Expr.bvar 0)
    · simp only [hbody, ite_false, Bool.false_eq_true] at ha
    · simp only [hbody, ite_true] at ha ⊢
      exact subCheckNF_self_elim_ann_step ih_sub ih_abs ha
  -- Main proof
  rcases h with hann | hbody_k
  · exact Or.inl (ann_mono hann)
  · exact Or.inr (body_mono hbody_k)

/-- Helper for inferType-based fallback (app-app else branch and catch-all). -/
private theorem subCheckNF_inferType_step
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a : Expr} {b : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (match inferType ctx a with
          | some ty =>
            match absEval k ctx seen ty with
            | .ok ty' => subCheckNF k ctx seen ty'.val b
            | .error _ => false
          | none => false) = true)
    : (match inferType ctx a with
       | some ty =>
         match absEval (k + 1) ctx seen ty with
         | .ok ty' => subCheckNF (k + 1) ctx seen ty'.val b
         | .error _ => false
       | none => false) = true := by
  match hinf : inferType ctx a with
  | some ty =>
    simp only [hinf] at h ⊢
    exact subCheckNF_absEval_step ih_sub ih_abs h
  | none => simp [hinf] at h

/-- Combined fuel monotonicity for absEval and subCheckNF. Both properties
    are proved together by induction on fuel because they are mutually
    dependent: absEval calls subCheckNF, and subCheckNF calls absEval. -/
private theorem fuel_mono (n : Nat) :
    (∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
      subCheckNF n ctx seen a b = true → subCheckNF (n + 1) ctx seen a b = true) ∧
    (∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr} {lenient : Bool},
      absEval n ctx seen e lenient = .ok v → absEval (n + 1) ctx seen e lenient = .ok v) := by
  induction n with
  | zero =>
    exact ⟨fun h => by simp [subCheckNF] at h, fun {_ _ _ _ _} h => by simp [absEval] at h⟩
  | succ k ih =>
    obtain ⟨ih_sub, ih_abs⟩ := ih
    constructor
    · -- subCheckNF_fuel_mono step: prove subCheckNF (k+1) → subCheckNF (k+2)
      intro ctx seen a b h
      unfold subCheckNF at h ⊢; dsimp only [] at h ⊢
      -- The initial checks (a==b, seen) are fuel-independent.
      -- Use by_cases to handle them in both h and goal simultaneously.
      by_cases hab : (a == b) = true
      · simp [hab]
      · simp only [if_neg hab] at h ⊢
        by_cases hseen : (seen.any fun (a', b') => a == a' && b == b') = true
        · simp [hseen]
        · simp only [if_neg hseen] at h ⊢
          -- Now both h and goal are at the match b / match (a, b) level
          -- Split the hypothesis's match structure
          split at h
          · -- b = .type → goal also matches .type → true
            simp
          · -- b ≠ .type → match (a, b) with ...
            split at h
            · -- lam, lam: covariant body + contravariant domain
              simp only [Bool.and_eq_true] at h ⊢
              exact ⟨ih_sub h.1, ih_sub h.2⟩
            · -- _, mu (self-intro): subCheckNF ... a u'.val
              exact subCheckNF_absEval_step_right ih_sub ih_abs h
            · -- mu, _ (self-elim)
              exact subCheckNF_self_elim_step ih_sub ih_abs h
            · -- app, app (congruence + inferType fallback)
              split at h
              · -- congruence succeeded
                rename_i hcong
                simp only [Bool.and_eq_true] at hcong
                simp only [show subCheckNF (k + 1) ctx [] _ _ = true from ih_sub hcong.1,
                           show subCheckNF (k + 1) ctx [] _ _ = true from ih_sub hcong.2,
                           Bool.and_self, ite_true]
              · -- congruence failed, inferType fallback
                -- At higher fuel, congruence might succeed
                split
                · simp  -- congruence succeeds at higher fuel: done
                · -- congruence still fails
                  exact subCheckNF_inferType_step ih_sub ih_abs h
            · -- catch-all: inferType
              exact subCheckNF_inferType_step ih_sub ih_abs h
    · -- absEval_fuel_mono step
      intro ctx seen e v lenient h
      match e with
      | .bvar _ =>
        unfold absEval at h ⊢; exact h
      | .type =>
        unfold absEval at h ⊢; exact h
      | .lam dom body =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match hd : absEval k ctx seen dom lenient with
        | .error _ => simp [hd, bind, Except.bind] at h
        | .ok dom' =>
          simp only [hd, bind, Except.bind] at h
          match hb : absEval k (TyCtx.extend ctx dom') seen body lenient with
          | .error _ => simp [hb, bind, Except.bind] at h
          | .ok body' =>
            simp only [hb, bind, Except.bind] at h
            rw [ih_abs hd]; simp only [bind, Except.bind]
            rw [ih_abs hb]; simp only [bind, Except.bind]
            exact h
      | .mu ann body =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match ha : absEval k ctx seen ann lenient with
        | .error _ => simp [ha, bind, Except.bind] at h
        | .ok ann' =>
          simp only [ha, bind, Except.bind] at h
          rw [ih_abs ha]; simp only [bind, Except.bind]
          -- Handle the `if !lenient` condition
          by_cases hlen : (!lenient) = true
          · simp only [hlen, ite_true] at h ⊢
            match hb : absEval k (TyCtx.extend ctx ⟨.mu ann body⟩) [] body true with
            | .error _ => simp [hb, bind, Except.bind] at h
            | .ok body' =>
              simp only [hb, bind, Except.bind] at h
              rw [ih_abs hb]; simp only [bind, Except.bind]
              exact h
          · simp only [Bool.not_eq_true] at hlen
            simp only [hlen, ite_false] at h ⊢
            exact h
      | .asc term ty =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match ht : absEval k ctx seen term lenient with
        | .error _ => simp [ht, bind, Except.bind] at h
        | .ok sigma =>
          simp only [ht, bind, Except.bind] at h ⊢
          match hty : absEval k ctx seen ty lenient with
          | .error _ => simp [hty, bind, Except.bind] at h
          | .ok tau =>
            simp only [hty, bind, Except.bind] at h
            rw [ih_abs ht]; simp only [bind, Except.bind]
            rw [ih_abs hty]; simp only [bind, Except.bind]
            split at h
            · rename_i hsub
              rw [show subCheckNF (k + 1) ctx seen sigma.val tau.val = true
                from ih_sub hsub]
              exact h
            · simp at h
      | .app f a =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match hf : absEval k ctx seen f lenient with
        | .error _ => simp [hf, bind, Except.bind] at h
        | .ok f' =>
          simp only [hf, bind, Except.bind] at h ⊢
          match ha : absEval k ctx seen a lenient with
          | .error _ => simp [ha, bind, Except.bind] at h
          | .ok a' =>
            simp only [ha, bind, Except.bind] at h
            rw [ih_abs hf]; simp only [bind, Except.bind]
            rw [ih_abs ha]; simp only [bind, Except.bind]
            match hfv : f'.val with
            | .lam dom body =>
              simp only [hfv] at h ⊢
              split at h
              · rename_i hsub
                -- Condition: subCheckNF || (lenient && isNeutral)
                -- If true at fuel k, true at fuel k+1
                cases Bool.or_eq_true_iff.mp hsub with
                | inl hsub_l =>
                  rw [show subCheckNF (k + 1) ctx seen a'.val dom = true
                    from ih_sub hsub_l]; simp; exact ih_abs h
                | inr hsub_r =>
                  simp [hsub_r]; exact ih_abs h
              · simp at h
            | .mu _ann body' =>
              simp only [hfv] at h ⊢
              cases body' with
              | lam d1 b1 =>
                cases _ann with
                | lam _ _ => exact ih_abs h
                | bvar _ | app _ _ | type | mu _ _ | asc _ _ =>
                  exact absEval_fuel_mono_mu_lam_body ih_abs h
              | bvar _ | app _ _ | type | mu _ _ | asc _ _ =>
                cases _ann <;> exact h
            | .type =>
              simp only [hfv] at h; simp at h
            | .bvar _ | .app _ _ | .asc _ _ =>
              simp only [hfv] at h ⊢
              exact h

/-- subCheckNF fuel monotonicity: if a subtype check passes at fuel n,
    it also passes at fuel n+1. -/
theorem subCheckNF_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : subCheckNF n ctx seen a b = true) : subCheckNF (n + 1) ctx seen a b = true :=
  (fuel_mono n).1 h

/-- absEval fuel monotonicity: if absEval succeeds at fuel n, it succeeds
    at fuel n+1 with the same result. Works for all lenient values. -/
theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {v : NfExpr} {lenient : Bool}
    (h : absEval n ctx seen e lenient = .ok v) : absEval (n + 1) ctx seen e lenient = .ok v :=
  (fuel_mono n).2 h

/-- Generalized closedAt preservation at any depth d (not just ctx.length).
    If the input is closedAt d, the output is closedAt d. -/
theorem absEval_preserves_closedAt_d {fuel : Nat} {ctx : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {e : Expr} {τ : NfExpr} {lenient : Bool}
    (h_abs : absEval fuel ctx seen e lenient = .ok τ)
    (h_closed : e.closedAt d = true)
    : τ.val.closedAt d = true := by
  induction fuel generalizing ctx seen e τ d lenient with
  | zero => simp [absEval] at h_abs
  | succ k ih =>
    cases e with
    | bvar j =>
      unfold absEval at h_abs; injection h_abs with heq; subst heq
      exact h_closed
    | type =>
      unfold absEval at h_abs; injection h_abs with heq; subst heq
      simp [Expr.closedAt]
    | lam dom body =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_dom_cl, h_body_cl⟩ := h_closed
      match h_dom : absEval k ctx seen dom lenient with
      | .error _ => simp [h_dom, bind, Except.bind] at h_abs
      | .ok dom' =>
        simp only [h_dom, bind, Except.bind] at h_abs
        match h_body : absEval k (TyCtx.extend ctx dom') seen body lenient with
        | .error _ => simp [h_body, bind, Except.bind] at h_abs
        | .ok body' =>
          simp only [h_body, bind, Except.bind] at h_abs
          injection h_abs with heq; subst heq
          simp [Expr.closedAt]
          exact ⟨ih h_dom h_dom_cl, ih h_body h_body_cl⟩
    | mu ann body =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_ann : absEval k ctx seen ann lenient with
      | .error _ => simp [h_ann, bind, Except.bind] at h_abs
      | .ok ann' =>
        simp only [h_ann, bind, Except.bind] at h_abs
        split at h_abs
        · match h_body : absEval k (TyCtx.extend ctx ⟨.mu ann body⟩) [] body true with
          | .error _ => simp [h_body, bind, Except.bind] at h_abs
          | .ok body' =>
            simp only [h_body, bind, Except.bind] at h_abs
            injection h_abs with heq; subst heq; exact h_closed
        · injection h_abs with heq; subst heq; exact h_closed
    | asc term ty =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_term_cl, h_ty_cl⟩ := h_closed
      match h_sigma : absEval k ctx seen term lenient with
      | .error _ => simp [h_sigma, bind, Except.bind] at h_abs
      | .ok sigma =>
        simp only [h_sigma, bind, Except.bind] at h_abs
        match h_tau : absEval k ctx seen ty lenient with
        | .error _ => simp [h_tau, bind, Except.bind] at h_abs
        | .ok tau =>
          simp only [h_tau, bind, Except.bind] at h_abs
          by_cases hsub : subCheckNF k ctx seen sigma.val tau.val = true
          · simp only [hsub, ite_true] at h_abs
            injection h_abs with heq; subst heq
            exact ih h_tau h_ty_cl
          · simp only [Bool.not_eq_true] at hsub; simp only [hsub] at h_abs; simp at h_abs
    | app f a =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_f_cl, h_a_cl⟩ := h_closed
      match h_f : absEval k ctx seen f lenient with
      | .error _ => simp [h_f, bind, Except.bind] at h_abs
      | .ok f' =>
        simp only [h_f, bind, Except.bind] at h_abs
        match h_a : absEval k ctx seen a lenient with
        | .error _ => simp [h_a, bind, Except.bind] at h_abs
        | .ok a' =>
          simp only [h_a, bind, Except.bind] at h_abs
          have h_f'_cl := ih h_f h_f_cl
          have h_a'_cl := ih h_a h_a_cl
          match hfv : f'.val with
          | .lam dom body =>
            simp only [hfv] at h_abs
            split at h_abs
            · have h_body_cl : body.closedAt (d + 1) = true := by
                rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.2
              exact ih h_abs (Expr.subst_closedAt h_body_cl h_a'_cl)
            · simp at h_abs
          | .mu _ann body =>
            simp only [hfv] at h_abs
            have h_mu_cl_ann : _ann.closedAt d = true := by
              rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.1
            have h_mu_cl_body : body.closedAt (d + 1) = true := by
              rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.2
            have h_mu_expr_cl : (Expr.mu _ann body).closedAt d = true := by
              rw [hfv] at h_f'_cl; exact h_f'_cl
            have h_unfolded_cl : (body.subst 0 (Expr.mu _ann body)).closedAt d = true :=
              Expr.subst_closedAt h_mu_cl_body h_mu_expr_cl
            split at h_abs
            · rename_i _dom retBody _ _
              have h_ret_cl : retBody.closedAt (d + 1) = true := by
                simp [Expr.closedAt] at h_mu_cl_ann; exact h_mu_cl_ann.2
              exact ih h_abs (Expr.subst_closedAt h_ret_cl h_a'_cl)
            · rename_i _dom_b _retBody_b _
              have h_retBody_b_cl : _retBody_b.closedAt (d + 2) = true := by
                simp [Expr.closedAt] at h_mu_cl_body; exact h_mu_cl_body.2
              by_cases h_seen : (seen.any fun p => p.1 == Expr.mu _ann (Expr.lam _dom_b _retBody_b)) = true
              · simp only [h_seen, ite_true] at h_abs
                injection h_abs with heq; subst heq
                simp only [Expr.closedAt, Bool.and_eq_true]
                exact ⟨by simp [Expr.closedAt] at h_mu_expr_cl; exact h_mu_expr_cl, h_a'_cl⟩
              · simp only [Bool.not_eq_true] at h_seen
                simp only [h_seen, ite_false] at h_abs
                simp only [Expr.subst] at h_abs
                have h_mu_shifted_cl : (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b))).closedAt (d + 1) = true :=
                  Expr.shift_closedAt _ d 1 0 (by omega) h_mu_expr_cl
                have h_ret_subst_cl : (_retBody_b.subst (0 + 1) (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b)))).closedAt (d + 1) = true := by
                  rw [show (0 : Nat) + 1 = 1 from rfl]
                  have := Expr.subst_closedAt_gen _retBody_b 1 d
                    (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b)))
                    (by rw [show 1 + d + 1 = d + 2 from by omega]; exact h_retBody_b_cl)
                    (by rw [show 1 + d = d + 1 from by omega]; exact h_mu_shifted_cl)
                  rwa [show 1 + d = d + 1 from by omega] at this
                exact ih h_abs (Expr.subst_closedAt h_ret_subst_cl h_a'_cl)
            · have h_eq : τ = ⟨.app (body.subst 0 (Expr.mu _ann body)) a'.val⟩ := by
                simp [Except.ok.injEq] at h_abs; exact h_abs.symm
              rw [h_eq]; simp [Expr.closedAt]
              exact ⟨h_unfolded_cl, h_a'_cl⟩
          | .type =>
            simp only [hfv] at h_abs; simp at h_abs
          | .bvar j =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have : (Expr.bvar j).closedAt d = true := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨this, h_a'_cl⟩
            · simp at h_abs
          | .app f₁ a₁ =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨⟨this.1, this.2⟩, h_a'_cl⟩
            · simp at h_abs
          | .asc t y =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨⟨this.1, this.2⟩, h_a'_cl⟩
            · simp at h_abs

/-! ## Context irrelevance for closed terms

For closedAt d expressions, only the first d entries of ctx are consulted.
Under binders, closedAt increases by 1 and ctx extends with the same entry
in both contexts, preserving the invariant. -/

/-- inferType depends only on the first d entries of ctx when e is closedAt d. -/
theorem inferType_ctx_irrelevant {ctx ctx' : TyCtx} {d : Nat} {e : Expr}
    (he : e.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    : inferType ctx e = inferType ctx' e := by
  induction e generalizing d with
  | bvar k =>
    unfold inferType
    simp [Expr.closedAt] at he
    rw [hctx k he]
  | mu ann body => rfl
  | app f a ih_f _ =>
    simp [Expr.closedAt] at he
    unfold inferType
    rw [ih_f he.1 hctx]
  | _ => rfl

/-- inferType output is closedAt d when the expression is closedAt d and ctx entries
    at positions < d are closedAt d. -/
theorem inferType_closedAt {ctx : TyCtx} {d : Nat} {e ty : Expr}
    (he : e.closedAt d = true)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    (h_inf : inferType ctx e = some ty)
    : ty.closedAt d = true := by
  induction e generalizing d ty with
  | bvar k =>
    simp only [Expr.closedAt, decide_eq_true_eq] at he
    simp only [inferType] at h_inf
    match hget : ctx.get? k with
    | some v =>
      simp only [hget, Option.map_some'] at h_inf
      injection h_inf with heq; subst heq
      exact hctx_wf k v hget he
    | none =>
      rw [hget] at h_inf; exact absurd h_inf (by simp)
  | mu ann _body _ _ =>
    unfold inferType at h_inf
    injection h_inf with heq; subst heq
    simp only [Expr.closedAt, Bool.and_eq_true] at he
    exact he.1
  | app f a ih_f _ =>
    unfold inferType at h_inf
    simp only [Expr.closedAt, Bool.and_eq_true] at he
    match hinf_f : inferType ctx f with
    | some (.lam _dom retTy) =>
      simp only [hinf_f] at h_inf
      injection h_inf with heq; subst heq
      -- retTy.closedAt (d+1) from IH on f
      have hf_ty_cl : (Expr.lam _dom retTy).closedAt d = true :=
        ih_f he.1 hctx_wf hinf_f
      simp only [Expr.closedAt, Bool.and_eq_true] at hf_ty_cl
      exact Expr.subst_closedAt hf_ty_cl.2 he.2
    | some (.mu _ann body) =>
      simp only [hinf_f] at h_inf
      match hunf : (body.subst 0 f) with
      | .lam _dom2 retTy2 =>
        simp only [hunf] at h_inf
        injection h_inf with heq; subst heq
        have hmu_cl : (Expr.mu _ann body).closedAt d = true :=
          ih_f he.1 hctx_wf hinf_f
        simp only [Expr.closedAt, Bool.and_eq_true] at hmu_cl
        have hbody_sub_cl : (body.subst 0 f).closedAt d = true :=
          Expr.subst_closedAt hmu_cl.2 he.1
        rw [hunf] at hbody_sub_cl
        simp only [Expr.closedAt, Bool.and_eq_true] at hbody_sub_cl
        exact Expr.subst_closedAt hbody_sub_cl.2 he.2
      | .bvar _ | .type | .mu _ _ | .app _ _ | .asc _ _ =>
        simp [hunf] at h_inf
    | some (.bvar _) | some .type | some (.app _ _) | some (.asc _ _) | none =>
      simp [hinf_f] at h_inf
  | lam _ _ _ _ | type | asc _ _ _ _ =>
    simp [inferType] at h_inf

/-- isCallableNF depends only on the first d entries of ctx when f.val is closedAt d. -/
theorem isCallableNF_ctx_irrelevant {ctx ctx' : TyCtx} {d : Nat} {f : NfExpr}
    (hf : f.val.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    : isCallableNF ctx f = isCallableNF ctx' f := by
  unfold isCallableNF
  match hfv : f.val with
  | .lam _ _ | .mu _ _ => rfl
  | .bvar _ | .type | .app _ _ | .asc _ _ =>
    -- In these cases, isCallableNF reduces to match on inferType ctx f.val
    -- We need: inferType ctx f.val = inferType ctx' f.val
    -- which follows from inferType_ctx_irrelevant since f.val.closedAt d
    rw [hfv] at hf
    have hinf_eq := inferType_ctx_irrelevant hf hctx
    simp only [hfv, hinf_eq]

/-- TyCtx.extend preserves the "first d entries match" invariant at depth d+1. -/
private theorem TyCtx_extend_ctx_irrelevant {ctx ctx' : TyCtx} {d : Nat} {ty : NfExpr}
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    : ∀ i, i < d + 1 → (TyCtx.extend ctx ty).get? i = (TyCtx.extend ctx' ty).get? i := by
  intro i hi
  unfold TyCtx.extend
  match i with
  | 0 => simp
  | .succ j =>
    simp only [List.get?_cons_succ, List.get?_map]
    have hj : j < d := by omega
    congr 1; exact hctx j hj

/-- TyCtx.extend preserves well-scopedness at d+1. -/
private theorem TyCtx_extend_wf {ctx : TyCtx} {d : Nat} {ty : NfExpr}
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    (hty : ty.val.closedAt d = true)
    : ∀ i (v : NfExpr), (TyCtx.extend ctx ty).get? i = some v → i < d + 1 → v.val.closedAt (d + 1) = true := by
  intro i v hget hi
  unfold TyCtx.extend at hget
  match i with
  | 0 =>
    -- hget : (⟨ty.val.shift 1 0⟩ :: ...).get? 0 = some v
    simp only [List.get?_cons_zero] at hget
    injection hget with heq; subst heq
    -- v = ⟨ty.val.shift 1 0⟩, need (ty.val.shift 1 0).closedAt (d+1)
    exact Expr.shift_closedAt ty.val d 1 0 (Nat.zero_le d) hty
  | .succ j =>
    -- hget : (extend ctx ty).get? (j+1) = some v
    simp only [List.get?_cons_succ, List.get?_map] at hget
    -- hget : (ctx.get? j).map (fun e => ⟨e.val.shift 1 0⟩) = some v
    have hj : j < d := by omega
    match hget2 : ctx.get? j with
    | some w =>
      rw [hget2] at hget
      simp only [Option.map_some'] at hget
      injection hget with heq; subst heq
      -- v = ⟨w.val.shift 1 0⟩, need (w.val.shift 1 0).closedAt (d+1)
      have hw_cl : w.val.closedAt d = true := hctx_wf j w hget2 hj
      exact Expr.shift_closedAt w.val d 1 0 (Nat.zero_le d) hw_cl
    | none =>
      rw [hget2] at hget; simp at hget

/-- Combined mutual proof of context irrelevance for subCheckNF and absEval.
    Requires well-scopedness: ctx entries at positions < d have closedAt d values.
    This is needed for inferType fallback cases where the output type depends on ctx. -/
private theorem ctx_irrelevant (fuel : Nat) :
    (∀ {ctx ctx' : TyCtx} {d : Nat} {seen : List (Expr × Expr)} {a b : Expr},
      a.closedAt d = true → b.closedAt d = true →
      (∀ i, i < d → ctx.get? i = ctx'.get? i) →
      (∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true) →
      subCheckNF fuel ctx seen a b = subCheckNF fuel ctx' seen a b) ∧
    (∀ {ctx ctx' : TyCtx} {d : Nat} {seen : List (Expr × Expr)} {e : Expr} {lenient : Bool},
      e.closedAt d = true →
      (∀ i, i < d → ctx.get? i = ctx'.get? i) →
      (∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true) →
      absEval fuel ctx seen e lenient = absEval fuel ctx' seen e lenient) := by
  induction fuel with
  | zero =>
    exact ⟨fun ha hb hctx _ => by simp [subCheckNF],
           fun {_ _ _ _ _ _} he hctx _ => by simp [absEval]⟩
  | succ k ih =>
    obtain ⟨ih_sub, ih_abs⟩ := ih
    constructor
    · -- subCheckNF ctx-irrelevant
      intro ctx ctx' d seen a b ha hb hctx hctx_wf
      -- Handle this by induction on the structure of (a, b)
      -- Using a shared helper for the inferType fallback
      have inferType_fallback : ∀ (ctx'' ctx''' : TyCtx) (a' b' : Expr),
          a'.closedAt d = true → b'.closedAt d = true →
          (∀ i, i < d → ctx''.get? i = ctx'''.get? i) →
          (∀ i (v : NfExpr), ctx''.get? i = some v → i < d → v.val.closedAt d = true) →
          (match inferType ctx'' a' with
            | some ty => match absEval k ctx'' seen ty with
              | .ok ty' => subCheckNF k ctx'' seen ty'.val b'
              | .error _ => false
            | none => false) =
          (match inferType ctx''' a' with
            | some ty => match absEval k ctx''' seen ty with
              | .ok ty' => subCheckNF k ctx''' seen ty'.val b'
              | .error _ => false
            | none => false) := by
        intro ctx'' ctx''' a' b' ha' hb' hctx' hctx_wf'
        have hctx_wf''' : ∀ i (v : NfExpr), ctx'''.get? i = some v → i < d → v.val.closedAt d = true := by
          intro i v hg hi; exact hctx_wf' i v ((hctx' i hi) ▸ hg) hi
        have hinf_eq : inferType ctx'' a' = inferType ctx''' a' := inferType_ctx_irrelevant ha' hctx'
        -- Match on inferType ctx'' a' and use hinf_eq to handle ctx'''
        match hinf : inferType ctx'' a' with
        | none =>
          have hinf''' : inferType ctx''' a' = none := hinf_eq ▸ hinf
          simp [hinf''']
        | some ty =>
          have hinf''' : inferType ctx''' a' = some ty := hinf_eq ▸ hinf
          have hty_cl := inferType_closedAt ha' hctx_wf''' hinf'''
          have habs_eq : absEval k ctx'' seen ty false = absEval k ctx''' seen ty false :=
            ih_abs (ctx := ctx'') (ctx' := ctx''') (seen := seen) (e := ty) (lenient := false)
              hty_cl hctx' hctx_wf'
          simp only [hinf, hinf''']
          rw [habs_eq]
          match habsty : absEval k ctx''' seen ty with
          | .error _ => rfl
          | .ok ty' =>
            have hty'_cl := absEval_preserves_closedAt_d habsty hty_cl
            exact ih_sub hty'_cl hb' hctx' hctx_wf'
      -- Shared helper for self-elim
      have self_elim : ∀ (ctx'' ctx''' : TyCtx) (ann body b' : Expr),
          ann.closedAt d = true → body.closedAt (d + 1) = true → b'.closedAt d = true →
          (∀ i, i < d → ctx''.get? i = ctx'''.get? i) →
          (∀ i (v : NfExpr), ctx''.get? i = some v → i < d → v.val.closedAt d = true) →
          (let mu_expr := Expr.mu ann body
           let seen_ext := (mu_expr, b') :: seen
           let ann_path :=
             if body != .bvar 0 then
               match absEval k ctx'' seen_ext ann with
               | .ok ann' => subCheckNF k ctx'' seen_ext ann'.val b'
               | .error _ => false
             else false
           let u := body.subst 0 mu_expr
           if ann_path then true
           else match absEval k ctx'' seen_ext u with
             | .ok u' => subCheckNF k ctx'' seen u'.val b'
             | .error _ => false) =
          (let mu_expr := Expr.mu ann body
           let seen_ext := (mu_expr, b') :: seen
           let ann_path :=
             if body != .bvar 0 then
               match absEval k ctx''' seen_ext ann with
               | .ok ann' => subCheckNF k ctx''' seen_ext ann'.val b'
               | .error _ => false
             else false
           let u := body.subst 0 mu_expr
           if ann_path then true
           else match absEval k ctx''' seen_ext u with
             | .ok u' => subCheckNF k ctx''' seen u'.val b'
             | .error _ => false) := by
        intro ctx'' ctx''' ann body b' hann_cl hbody_cl hb'_cl hctx' hctx_wf'
        have ha_full : (Expr.mu ann body).closedAt d = true := by
          simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨hann_cl, hbody_cl⟩
        have hu_cl : (body.subst 0 (Expr.mu ann body)).closedAt d = true :=
          Expr.subst_closedAt hbody_cl ha_full
        -- Show ann_path is equal for both contexts
        have ann_path_eq :
            (if body != .bvar 0 then
               match absEval k ctx'' ((Expr.mu ann body, b') :: seen) ann with
               | .ok ann' => subCheckNF k ctx'' ((Expr.mu ann body, b') :: seen) ann'.val b'
               | .error _ => false
             else false) =
            (if body != .bvar 0 then
               match absEval k ctx''' ((Expr.mu ann body, b') :: seen) ann with
               | .ok ann' => subCheckNF k ctx''' ((Expr.mu ann body, b') :: seen) ann'.val b'
               | .error _ => false
             else false) := by
          by_cases hbody_ne : body != Expr.bvar 0
          · simp only [hbody_ne, ite_true]
            have habs_eq := ih_abs (ctx := ctx'') (ctx' := ctx''') (seen := (Expr.mu ann body, b') :: seen)
              (e := ann) (lenient := false) hann_cl hctx' hctx_wf'
            rw [habs_eq]
            match habs_ann : absEval k ctx''' ((Expr.mu ann body, b') :: seen) ann with
            | .error _ => rfl
            | .ok ann' =>
              have hann'_cl := absEval_preserves_closedAt_d habs_ann hann_cl
              exact ih_sub hann'_cl hb'_cl hctx' hctx_wf'
          · simp only [Bool.not_eq_true] at hbody_ne
            simp [hbody_ne]
        dsimp only []
        rw [ann_path_eq]
        -- Now the goal has the same ann_path on both sides, just need to equate u-paths
        -- If ann_path = true, both sides are true
        -- If ann_path = false, both sides use u-path which needs ctx-irrelevance
        by_cases hap : (if body != .bvar 0 then
               match absEval k ctx''' ((Expr.mu ann body, b') :: seen) ann with
               | .ok ann' => subCheckNF k ctx''' ((Expr.mu ann body, b') :: seen) ann'.val b'
               | .error _ => false
             else false) = true
        · simp only [hap, ite_true]
        · simp only [Bool.not_eq_true] at hap
          simp only [hap, ite_false]
          have habs_eq := ih_abs (ctx := ctx'') (ctx' := ctx''') (seen := (Expr.mu ann body, b') :: seen)
            (e := body.subst 0 (Expr.mu ann body)) (lenient := false) hu_cl hctx' hctx_wf'
          rw [habs_eq]
          match habs_u : absEval k ctx''' ((Expr.mu ann body, b') :: seen) (body.subst 0 (Expr.mu ann body)) with
          | .error _ => rfl
          | .ok u' =>
            have hu'_cl := absEval_preserves_closedAt_d habs_u hu_cl
            exact ih_sub hu'_cl hb'_cl hctx' hctx_wf'
      -- Main proof: case split on a and b
      cases b with
      | type =>
        unfold subCheckNF; simp [Expr.closedAt]
      | bvar j =>
        -- b = bvar j: not .type, not .lam, not .mu, not .app
        -- Initial checks (a==b, seen) are ctx-independent
        -- Match falls through to: if a = .mu -> self-elim, else -> catch-all
        unfold subCheckNF; dsimp only []
        by_cases hab : (a == Expr.bvar j) = true
        · simp [hab]
        · simp only [if_neg hab]
          by_cases hseen : (seen.any fun p => a == p.1 && Expr.bvar j == p.2) = true
          · simp [hseen]
          · simp only [if_neg hseen]
            match a with
            | .mu annA bodyA =>
              simp only [Expr.closedAt, Bool.and_eq_true] at ha hb
              exact self_elim ctx ctx' annA bodyA (Expr.bvar j) ha.1 ha.2 hb hctx hctx_wf
            | .lam d1 b1 => exact inferType_fallback ctx ctx' (Expr.lam d1 b1) (Expr.bvar j) ha hb hctx hctx_wf
            | .bvar j2 => exact inferType_fallback ctx ctx' (Expr.bvar j2) (Expr.bvar j) ha hb hctx hctx_wf
            | .type => exact inferType_fallback ctx ctx' Expr.type (Expr.bvar j) ha hb hctx hctx_wf
            | .app f1 a1 => exact inferType_fallback ctx ctx' (Expr.app f1 a1) (Expr.bvar j) ha hb hctx hctx_wf
            | .asc t y => exact inferType_fallback ctx ctx' (Expr.asc t y) (Expr.bvar j) ha hb hctx hctx_wf
      | lam domB bodyB =>
        -- b = .lam domB bodyB
        unfold subCheckNF; dsimp only []
        simp only [Expr.closedAt, Bool.and_eq_true] at hb
        -- Initial a==b check is ctx-independent
        by_cases hab : (a == Expr.lam domB bodyB) = true
        · simp [hab]
        · simp only [if_neg hab]
          by_cases hseen : (seen.any fun p => a == p.1 && Expr.lam domB bodyB == p.2) = true
          · simp [hseen]
          · simp only [if_neg hseen]
            -- Handle a = .lam (lam-lam), a = .mu (self-elim), else inferType fallback
            match ha_shape : a with
            | .lam domA bodyA =>
              simp only [ha_shape, Expr.closedAt, Bool.and_eq_true] at ha ⊢
              congr 1
              · exact ih_sub hb.1 ha.1 hctx hctx_wf
              · exact ih_sub ha.2 hb.2 (TyCtx_extend_ctx_irrelevant hctx)
                  (TyCtx_extend_wf hctx_wf hb.1)
            | .mu annA bodyA =>
              simp only [Expr.closedAt, Bool.and_eq_true] at ha
              have hb_full : (Expr.lam domB bodyB).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
              exact self_elim ctx ctx' annA bodyA (Expr.lam domB bodyB) ha.1 ha.2 hb_full hctx hctx_wf
            | .bvar j =>
              have hb_full : (Expr.lam domB bodyB).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
              exact inferType_fallback ctx ctx' (Expr.bvar j) (Expr.lam domB bodyB) ha hb_full hctx hctx_wf
            | .type =>
              have hb_full : (Expr.lam domB bodyB).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
              exact inferType_fallback ctx ctx' Expr.type (Expr.lam domB bodyB) ha hb_full hctx hctx_wf
            | .app f1 a1 =>
              have hb_full : (Expr.lam domB bodyB).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
              exact inferType_fallback ctx ctx' (Expr.app f1 a1) (Expr.lam domB bodyB) ha hb_full hctx hctx_wf
            | .asc t y =>
              have hb_full : (Expr.lam domB bodyB).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
              exact inferType_fallback ctx ctx' (Expr.asc t y) (Expr.lam domB bodyB) ha hb_full hctx hctx_wf
      | mu _annB bodyB =>
        -- b = .mu _annB bodyB: self-intro
        simp only [Expr.closedAt, Bool.and_eq_true] at hb
        have hb_full : (Expr.mu _annB bodyB).closedAt d = true := by
          simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
        have hu_cl : (bodyB.subst 0 a).closedAt d = true :=
          Expr.subst_closedAt hb.2 ha
        unfold subCheckNF; dsimp only []
        by_cases hab : (a == Expr.mu _annB bodyB) = true
        · simp [hab]
        · simp only [if_neg hab]
          by_cases hseen : (seen.any fun p => a == p.1 && Expr.mu _annB bodyB == p.2) = true
          · simp [hseen]
          · simp only [if_neg hseen]
            -- self-intro: match absEval k ctx seen' u
            have habs_eq := ih_abs (ctx := ctx) (ctx' := ctx') (seen := (a, Expr.mu _annB bodyB) :: seen)
              (e := bodyB.subst 0 a) (lenient := false) hu_cl hctx hctx_wf
            rw [habs_eq]
            match habs : absEval k ctx' ((a, Expr.mu _annB bodyB) :: seen) (bodyB.subst 0 a) with
            | .error _ => rfl
            | .ok u' =>
              have hu'_cl := absEval_preserves_closedAt_d habs hu_cl
              exact ih_sub ha hu'_cl hctx hctx_wf
      | app f2 a2 =>
        -- b = .app f2 a2; hb : (Expr.app f2 a2).closedAt d
        unfold subCheckNF; dsimp only []
        by_cases hab : (a == Expr.app f2 a2) = true
        · simp [hab]
        · simp only [if_neg hab]
          by_cases hseen : (seen.any fun p => a == p.1 && Expr.app f2 a2 == p.2) = true
          · simp [hseen]
          · simp only [if_neg hseen]
            match a with
            | .mu annA bodyA =>
              simp only [Expr.closedAt, Bool.and_eq_true] at ha
              exact self_elim ctx ctx' annA bodyA (Expr.app f2 a2) ha.1 ha.2 hb hctx hctx_wf
            | .app f1 a1 =>
              -- app-app congruence or inferType fallback
              simp only [Expr.closedAt, Bool.and_eq_true] at ha hb
              have hf_eq := ih_sub (seen := []) ha.1 hb.1 hctx hctx_wf
              have ha_eq := ih_sub (seen := []) ha.2 hb.2 hctx hctx_wf
              simp only [hf_eq, ha_eq]
              split
              · rfl
              · have ha_full : (Expr.app f1 a1).closedAt d = true := by
                  simp only [Expr.closedAt, Bool.and_eq_true]; exact ha
                have hb_full : (Expr.app f2 a2).closedAt d = true := by
                  simp only [Expr.closedAt, Bool.and_eq_true]; exact hb
                exact inferType_fallback ctx ctx' (Expr.app f1 a1) (Expr.app f2 a2) ha_full hb_full hctx hctx_wf
            | .lam d1 b1 => exact inferType_fallback ctx ctx' (Expr.lam d1 b1) (Expr.app f2 a2) ha hb hctx hctx_wf
            | .bvar j => exact inferType_fallback ctx ctx' (Expr.bvar j) (Expr.app f2 a2) ha hb hctx hctx_wf
            | .type => exact inferType_fallback ctx ctx' Expr.type (Expr.app f2 a2) ha hb hctx hctx_wf
            | .asc t y => exact inferType_fallback ctx ctx' (Expr.asc t y) (Expr.app f2 a2) ha hb hctx hctx_wf
      | asc term2 ty2 =>
        -- b = .asc term2 ty2; hb : (Expr.asc term2 ty2).closedAt d
        unfold subCheckNF; dsimp only []
        by_cases hab : (a == Expr.asc term2 ty2) = true
        · simp [hab]
        · simp only [if_neg hab]
          by_cases hseen : (seen.any fun p => a == p.1 && Expr.asc term2 ty2 == p.2) = true
          · simp [hseen]
          · simp only [if_neg hseen]
            match a with
            | .mu annA bodyA =>
              simp only [Expr.closedAt, Bool.and_eq_true] at ha
              exact self_elim ctx ctx' annA bodyA (Expr.asc term2 ty2) ha.1 ha.2 hb hctx hctx_wf
            | .lam d1 b1 => exact inferType_fallback ctx ctx' (Expr.lam d1 b1) (Expr.asc term2 ty2) ha hb hctx hctx_wf
            | .bvar j => exact inferType_fallback ctx ctx' (Expr.bvar j) (Expr.asc term2 ty2) ha hb hctx hctx_wf
            | .type => exact inferType_fallback ctx ctx' Expr.type (Expr.asc term2 ty2) ha hb hctx hctx_wf
            | .app f1 a1 => exact inferType_fallback ctx ctx' (Expr.app f1 a1) (Expr.asc term2 ty2) ha hb hctx hctx_wf
            | .asc t y => exact inferType_fallback ctx ctx' (Expr.asc t y) (Expr.asc term2 ty2) ha hb hctx hctx_wf
    · -- absEval ctx-irrelevant
      intro ctx ctx' d seen e lenient he hctx hctx_wf
      match e with
      | .bvar j => unfold absEval; rfl
      | .type => unfold absEval; rfl
      | .lam dom body =>
        unfold absEval; dsimp only []
        simp only [Expr.closedAt, Bool.and_eq_true] at he
        obtain ⟨h_dom_cl, h_body_cl⟩ := he
        have h_dom := ih_abs (e := dom) (seen := seen) (lenient := lenient) h_dom_cl hctx hctx_wf
        rw [h_dom]
        match hd : absEval k ctx' seen dom lenient with
        | .error _ => rfl
        | .ok dom' =>
          simp only [bind, Except.bind]
          have h_dom'_cl := absEval_preserves_closedAt_d hd h_dom_cl
          have h_body := ih_abs (e := body) (seen := seen) (lenient := lenient) h_body_cl
            (TyCtx_extend_ctx_irrelevant hctx) (TyCtx_extend_wf hctx_wf h_dom'_cl)
          rw [h_body]
      | .mu ann body =>
        unfold absEval; dsimp only []
        simp only [Expr.closedAt, Bool.and_eq_true] at he
        obtain ⟨h_ann_cl, h_body_cl⟩ := he
        have h_ann := ih_abs (e := ann) (seen := seen) (lenient := lenient) h_ann_cl hctx hctx_wf
        rw [h_ann]
        match ha : absEval k ctx' seen ann lenient with
        | .error _ => rfl
        | .ok ann' =>
          simp only [bind, Except.bind]
          -- if !lenient then body check else .ok ⟨.mu ann body⟩
          have h_mu_cl : (Expr.mu ann body).closedAt d = true := by
            simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨h_ann_cl, h_body_cl⟩
          have h_body_check := ih_abs (e := body) (seen := []) (lenient := true) h_body_cl
            (TyCtx_extend_ctx_irrelevant hctx) (TyCtx_extend_wf hctx_wf h_mu_cl)
          cases lenient
          · -- lenient = false: body check runs
            simp only [Bool.not_false, ite_true, h_body_check]
          · -- lenient = true: body check skipped; both sides identical
            simp [Bool.not_true]
      | .asc term ty =>
        unfold absEval; dsimp only []
        simp only [Expr.closedAt, Bool.and_eq_true] at he
        obtain ⟨h_term_cl, h_ty_cl⟩ := he
        have h_term := ih_abs (e := term) (seen := seen) (lenient := lenient) h_term_cl hctx hctx_wf
        have h_ty := ih_abs (e := ty) (seen := seen) (lenient := lenient) h_ty_cl hctx hctx_wf
        rw [h_term, h_ty]
        match hs : absEval k ctx' seen term lenient with
        | .error _ => rfl
        | .ok sigma =>
          simp only [bind, Except.bind]
          match ht : absEval k ctx' seen ty lenient with
          | .error _ => rfl
          | .ok tau =>
            simp only [bind, Except.bind]
            have h_sigma_cl := absEval_preserves_closedAt_d hs h_term_cl
            have h_tau_cl := absEval_preserves_closedAt_d ht h_ty_cl
            rw [ih_sub h_sigma_cl h_tau_cl hctx hctx_wf]
      | .app f a =>
        unfold absEval; dsimp only []
        simp only [Expr.closedAt, Bool.and_eq_true] at he
        obtain ⟨h_f_cl, h_a_cl⟩ := he
        have h_f := ih_abs (e := f) (seen := seen) (lenient := lenient) h_f_cl hctx hctx_wf
        have h_a := ih_abs (e := a) (seen := seen) (lenient := lenient) h_a_cl hctx hctx_wf
        rw [h_f, h_a]
        match hf : absEval k ctx' seen f lenient with
        | .error _ => rfl
        | .ok f' =>
          simp only [bind, Except.bind]
          match ha : absEval k ctx' seen a lenient with
          | .error _ => rfl
          | .ok a' =>
            simp only [bind, Except.bind]
            have h_f'_cl := absEval_preserves_closedAt_d hf h_f_cl
            have h_a'_cl := absEval_preserves_closedAt_d ha h_a_cl
            match hfv : f'.val with
            | .lam dom body =>
              simp only [hfv]
              have h_dom_cl : dom.closedAt d = true := by
                rw [hfv] at h_f'_cl; simp only [Expr.closedAt, Bool.and_eq_true] at h_f'_cl; exact h_f'_cl.1
              have h_body_cl : body.closedAt (d + 1) = true := by
                rw [hfv] at h_f'_cl; simp only [Expr.closedAt, Bool.and_eq_true] at h_f'_cl; exact h_f'_cl.2
              rw [ih_sub h_a'_cl h_dom_cl hctx hctx_wf]
              split
              · exact ih_abs (Expr.subst_closedAt h_body_cl h_a'_cl) hctx hctx_wf
              · rfl
            | .mu _ann body =>
              simp only [hfv]
              have h_ann_cl : _ann.closedAt d = true := by
                rw [hfv] at h_f'_cl; simp only [Expr.closedAt, Bool.and_eq_true] at h_f'_cl; exact h_f'_cl.1
              have h_body_cl' : body.closedAt (d + 1) = true := by
                rw [hfv] at h_f'_cl; simp only [Expr.closedAt, Bool.and_eq_true] at h_f'_cl; exact h_f'_cl.2
              have h_mu_cl : (Expr.mu _ann body).closedAt d = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨h_ann_cl, h_body_cl'⟩
              -- Split following absEval's match structure
              split
              · -- Case 1: ann = .lam _dom retBody, body = .lam _ _
                rename_i _dom retBody _bodyDom _bodyRet
                have h_retBody_cl : retBody.closedAt (d + 1) = true := by
                  simp only [Expr.closedAt, Bool.and_eq_true] at h_ann_cl; exact h_ann_cl.2
                exact ih_abs (Expr.subst_closedAt h_retBody_cl h_a'_cl) hctx hctx_wf
              · -- Case 2: body = .lam _ _ (ann is wildcard, not .lam)
                -- body is now specialized to .lam _dom _retBody; use next to get names
                next _dom _retBody _ =>
                -- body = Expr.lam _dom _retBody in the goal
                split
                · rfl
                · have h_unfolded_cl : ((Expr.lam _dom _retBody).subst 0 (Expr.mu _ann (Expr.lam _dom _retBody))).closedAt d = true :=
                    Expr.subst_closedAt h_body_cl' h_mu_cl
                  match huf : (Expr.lam _dom _retBody).subst 0 (Expr.mu _ann (Expr.lam _dom _retBody)) with
                  | .lam _dom2 retBody2 =>
                    have h_retBody2_cl : retBody2.closedAt (d + 1) = true := by
                      rw [huf] at h_unfolded_cl
                      simp only [Expr.closedAt, Bool.and_eq_true] at h_unfolded_cl
                      exact h_unfolded_cl.2
                    exact ih_abs (Expr.subst_closedAt h_retBody2_cl h_a'_cl) hctx hctx_wf
                  | e =>
                    -- e is non-lam; need to resolve remaining match in goal
                    have he_cl : e.closedAt d = true := by rw [← huf]; exact h_unfolded_cl
                    -- The remaining match on e has: lam case → retBody.subst, other → e.app
                    split
                    · -- lam case: e was matched as lam (consistent since split sees e)
                      rename_i _dom3 retBody3
                      have he_lam_cl : (Expr.lam _dom3 retBody3).closedAt d = true := he_cl
                      simp only [Expr.closedAt, Bool.and_eq_true] at he_lam_cl
                      exact ih_abs (Expr.subst_closedAt he_lam_cl.2 h_a'_cl) hctx hctx_wf
                    · -- non-lam case
                      have h_app_cl : (Expr.app e a'.val).closedAt d = true := by
                        simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨he_cl, h_a'_cl⟩
                      exact ih_abs h_app_cl hctx hctx_wf
              · -- Case 3: body is not lam
                rfl
            | .type =>
              simp only [hfv]
            | .bvar _ | .app _ _ | .asc _ _ =>
              simp only [hfv]
              rw [isCallableNF_ctx_irrelevant h_f'_cl hctx]

/-- subCheckNF depends only on the first d entries of ctx when terms are closedAt d.
    Requires well-scopedness: ctx entries at positions < d have closedAt d values. -/
theorem subCheckNF_ctx_irrelevant {fuel : Nat} {ctx ctx' : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {a b : Expr}
    (ha : a.closedAt d = true) (hb : b.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    : subCheckNF fuel ctx seen a b = subCheckNF fuel ctx' seen a b :=
  (ctx_irrelevant fuel).1 ha hb hctx hctx_wf

/-- absEval depends only on the first d entries of ctx when the expression is closedAt d.
    Requires well-scopedness: ctx entries at positions < d have closedAt d values. -/
theorem absEval_ctx_irrelevant {fuel : Nat} {ctx ctx' : TyCtx} {d : Nat}
    {seen : List (Expr × Expr)} {e : Expr} {lenient : Bool}
    (he : e.closedAt d = true)
    (hctx : ∀ i, i < d → ctx.get? i = ctx'.get? i)
    (hctx_wf : ∀ i (v : NfExpr), ctx.get? i = some v → i < d → v.val.closedAt d = true)
    : absEval fuel ctx seen e lenient = absEval fuel ctx' seen e lenient :=
  (ctx_irrelevant fuel).2 he hctx hctx_wf

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

/-! ## absEval preserves closedAt

If the input expression is closedAt ctx.length and absEval succeeds, the output
is also closedAt ctx.length. -/

theorem absEval_preserves_closedAt {fuel : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {τ : NfExpr} {lenient : Bool}
    (h_abs : absEval fuel ctx seen e lenient = .ok τ)
    (h_closed : e.closedAt ctx.length = true)
    : τ.val.closedAt ctx.length = true := by
  induction fuel generalizing ctx seen e τ lenient with
  | zero => simp [absEval] at h_abs
  | succ k ih =>
    cases e with
    | bvar j =>
      unfold absEval at h_abs; injection h_abs with heq; subst heq
      simp [Expr.closedAt] at h_closed ⊢; exact h_closed
    | type =>
      unfold absEval at h_abs; injection h_abs with heq; subst heq
      simp [Expr.closedAt]
    | lam dom body =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_dom_cl, h_body_cl⟩ := h_closed
      match h_dom : absEval k ctx seen dom lenient with
      | .error _ => simp [h_dom, bind, Except.bind] at h_abs
      | .ok dom' =>
        simp only [h_dom, bind, Except.bind] at h_abs
        match h_body : absEval k (TyCtx.extend ctx dom') seen body lenient with
        | .error _ => simp [h_body, bind, Except.bind] at h_abs
        | .ok body' =>
          simp only [h_body, bind, Except.bind] at h_abs
          injection h_abs with heq; subst heq
          simp [Expr.closedAt]
          constructor
          · exact ih h_dom h_dom_cl
          · have h_ext_len : (TyCtx.extend ctx dom').length = ctx.length + 1 := by
              simp [TyCtx.extend, List.length_cons, List.length_map]
            rw [← h_ext_len]
            exact ih h_body (by rw [h_ext_len]; exact h_body_cl)
    | mu ann body =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      match h_ann : absEval k ctx seen ann lenient with
      | .error _ => simp [h_ann, bind, Except.bind] at h_abs
      | .ok ann' =>
        simp only [h_ann, bind, Except.bind] at h_abs
        -- Handle the `if !lenient` condition generically
        split at h_abs
        · -- Body check fires (!lenient = true)
          match h_body : absEval k (TyCtx.extend ctx ⟨.mu ann body⟩) [] body true with
          | .error _ => simp [h_body, bind, Except.bind] at h_abs
          | .ok body' =>
            simp only [h_body, bind, Except.bind] at h_abs
            injection h_abs with heq; subst heq
            exact h_closed
        · -- Body check skipped (!lenient = false)
          injection h_abs with heq; subst heq
          exact h_closed
    | asc term ty =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_term_cl, h_ty_cl⟩ := h_closed
      match h_sigma : absEval k ctx seen term lenient with
      | .error _ => simp [h_sigma, bind, Except.bind] at h_abs
      | .ok sigma =>
        simp only [h_sigma, bind, Except.bind] at h_abs
        match h_tau : absEval k ctx seen ty lenient with
        | .error _ => simp [h_tau, bind, Except.bind] at h_abs
        | .ok tau =>
          simp only [h_tau, bind, Except.bind] at h_abs
          by_cases hsub : subCheckNF k ctx seen sigma.val tau.val = true
          · simp only [hsub, ite_true] at h_abs
            injection h_abs with heq; subst heq
            exact ih h_tau h_ty_cl
          · simp only [Bool.not_eq_true] at hsub; simp only [hsub] at h_abs; simp at h_abs
    | app f a =>
      unfold absEval at h_abs; dsimp only [] at h_abs
      simp [Expr.closedAt] at h_closed
      obtain ⟨h_f_cl, h_a_cl⟩ := h_closed
      match h_f : absEval k ctx seen f lenient with
      | .error _ => simp [h_f, bind, Except.bind] at h_abs
      | .ok f' =>
        simp only [h_f, bind, Except.bind] at h_abs
        match h_a : absEval k ctx seen a lenient with
        | .error _ => simp [h_a, bind, Except.bind] at h_abs
        | .ok a' =>
          simp only [h_a, bind, Except.bind] at h_abs
          have h_f'_cl := ih h_f h_f_cl
          have h_a'_cl := ih h_a h_a_cl
          match hfv : f'.val with
          | .lam dom body =>
            simp only [hfv] at h_abs
            -- The condition includes `lenient && isNeutral` but h_abs has it
            -- resolved. Just split on the whole if-then-else.
            split at h_abs
            · rename_i hsub
              have h_body_cl : body.closedAt (ctx.length + 1) = true := by
                rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.2
              exact ih h_abs (Expr.subst_closedAt h_body_cl h_a'_cl)
            · simp at h_abs
          | .mu _ann body =>
            -- Mu-app: multiple sub-cases (annotation-trust, body path, catch-all).
            -- All preserve closedAt via subst_closedAt + IH.
            simp only [hfv] at h_abs
            have h_mu_cl_ann : _ann.closedAt ctx.length = true := by
              rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.1
            have h_mu_cl_body : body.closedAt (ctx.length + 1) = true := by
              rw [hfv] at h_f'_cl; simp [Expr.closedAt] at h_f'_cl; exact h_f'_cl.2
            have h_mu_expr_cl : (Expr.mu _ann body).closedAt ctx.length = true := by
              rw [hfv] at h_f'_cl; exact h_f'_cl
            have h_unfolded_cl : (body.subst 0 (Expr.mu _ann body)).closedAt ctx.length = true :=
              Expr.subst_closedAt h_mu_cl_body h_mu_expr_cl
            -- Follow absEval's match on (_ann, body) using split
            -- to handle the 3 match arms.
            split at h_abs
            · -- Annotation-trust: _ann = lam _dom retBody, body = lam _ _
              rename_i _dom retBody _ _
              have h_ret_cl : retBody.closedAt (ctx.length + 1) = true := by
                simp [Expr.closedAt] at h_mu_cl_ann; exact h_mu_cl_ann.2
              exact ih h_abs (Expr.subst_closedAt h_ret_cl h_a'_cl)
            · -- Body path: body is a lam, _ann is not a matching lam.
              -- After split, body is destructured into .lam components.
              -- The absEval code: seen-check then unfold+dispatch.
              -- (.lam _dom_b _retBody_b).subst 0 mu = .lam (...) (...) always,
              -- so the inner match resolves to the lam branch.
              -- All paths preserve closedAt via subst_closedAt + IH.
              rename_i _dom_b _retBody_b _h_not_ann_lam
              have h_retBody_b_cl : _retBody_b.closedAt (ctx.length + 2) = true := by
                simp [Expr.closedAt] at h_mu_cl_body; exact h_mu_cl_body.2
              -- Case split on the seen check
              by_cases h_seen : (seen.any fun p => p.1 == Expr.mu _ann (Expr.lam _dom_b _retBody_b)) = true
              · -- Seen hit: τ = app (mu ...) a'.val
                simp only [h_seen, ite_true] at h_abs
                injection h_abs with heq; subst heq
                simp only [Expr.closedAt, Bool.and_eq_true]
                exact ⟨by simp [Expr.closedAt] at h_mu_expr_cl; exact h_mu_expr_cl, h_a'_cl⟩
              · -- Not seen: unfold body then beta-reduce
                simp only [Bool.not_eq_true] at h_seen
                simp only [h_seen, ite_false] at h_abs
                -- (.lam _dom_b _retBody_b).subst 0 mu_expr = .lam (...) (...)
                -- Lean should reduce this in h_abs, resolving the inner match to lam
                simp only [Expr.subst] at h_abs
                -- h_abs now: absEval k ctx seen' (retBody2.subst 0 a'.val) = .ok τ
                have h_mu_shifted_cl : (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b))).closedAt (ctx.length + 1) = true :=
                  Expr.shift_closedAt (Expr.mu _ann (Expr.lam _dom_b _retBody_b)) ctx.length 1 0 (by omega) h_mu_expr_cl
                -- closedAt for the substituted retBody
                -- subst_closedAt_gen uses (j + n) ordering; bridge with Nat.add_comm
                have h_shifted_comm : (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b))).closedAt (1 + ctx.length) = true := by
                  rw [Nat.add_comm]; exact h_mu_shifted_cl
                have h_retBody_comm : _retBody_b.closedAt (1 + ctx.length + 1) = true := by
                  rw [show 1 + ctx.length + 1 = ctx.length + 2 from by omega]; exact h_retBody_b_cl
                have h_gen := Expr.subst_closedAt_gen _retBody_b 1 ctx.length
                    (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b)))
                    h_retBody_comm h_shifted_comm
                -- h_gen : closedAt (1 + ctx.length) (subst _retBody_b 1 (shift ...)) = true
                -- Goal needs closedAt (ctx.length + 1) (subst (0+1) ...) = true
                -- These are equal: 0+1=1 (definitional), 1+n = n+1 (Nat.add_comm)
                have h_ret_subst_cl : (_retBody_b.subst (0 + 1) (Expr.shift 1 0 (Expr.mu _ann (Expr.lam _dom_b _retBody_b)))).closedAt (ctx.length + 1) = true := by
                  rw [show (0 : Nat) + 1 = 1 from rfl, show ctx.length + 1 = 1 + ctx.length from by omega]
                  exact h_gen
                exact ih h_abs (Expr.subst_closedAt h_ret_subst_cl h_a'_cl)
            · -- Catch-all: body not lam
              -- After split, h_abs should be: .ok ⟨.app (body.subst 0 (mu _ann body)) a'.val⟩ = .ok τ
              have h_eq : τ = ⟨.app (body.subst 0 (Expr.mu _ann body)) a'.val⟩ := by
                simp [Except.ok.injEq] at h_abs; exact h_abs.symm
              rw [h_eq]; simp [Expr.closedAt]
              exact ⟨h_unfolded_cl, h_a'_cl⟩
          | .type =>
            simp only [hfv] at h_abs; simp at h_abs
          | .bvar j =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have : (Expr.bvar j).closedAt ctx.length = true := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨this, h_a'_cl⟩
            · simp at h_abs
          | .app f₁ a₁ =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have : (Expr.app f₁ a₁).closedAt ctx.length = true := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨⟨this.1, this.2⟩, h_a'_cl⟩
            · simp at h_abs
          | .asc t y =>
            simp only [hfv] at h_abs
            split at h_abs
            · injection h_abs with heq; subst heq
              simp [Expr.closedAt]
              have : (Expr.asc t y).closedAt ctx.length = true := by rw [hfv] at h_f'_cl; exact h_f'_cl
              simp [Expr.closedAt] at this
              exact ⟨⟨this.1, this.2⟩, h_a'_cl⟩
            · simp at h_abs

