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

/-! ## Type aliases and contexts -/

/-- An expression that has been through absEval with some context.
    Invariants (not enforced by the type system, proved separately):
    - No `.asc` constructors (ascriptions erased)
    - No redexes (`.app (.lam ..) ..` does not occur) (normal form)
    - Well-scoped: all `.bvar k` satisfy `k < ctx.length`
    - All applications are callable: if `.app f a` occurs and `f`
      is neutral, then `inferType ctx f` is a function type
    - All domains and mu annotations are themselves NfExprs -/
abbrev NfExpr := Expr

/-- Type context: positional list of absEval'd domain types for bound variables.
    ctx[k] = absEval'd domain type of bvar k. -/
abbrev TyCtx := List NfExpr

/-- Extend a type context for a new binder. The domain type `ty` was computed
    at the outer depth; shift it by 1 so its free variable references are correct
    at the inner depth. Existing entries are also shifted. -/
def TyCtx.extend (ctx : TyCtx) (ty : NfExpr) : TyCtx :=
  (ty.shift 1 0) :: ctx.map (Expr.shift 1 0)


/-! ## Type inference for neutral terms -/

/-- Infer the type of a neutral term from a typing context.
    ctx is a positional list: ctx[k] is the type/domain of bvar k. -/
def inferType (ctx : List Expr) : Expr → Option Expr
  | .bvar k => ctx.get? k
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
  match f with
  | .lam _ _ => true
  | .mu _ _ => true
  | _ =>
    match inferType ctx f with
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
      Neutral applications are validated for callability via inferType.

      A term is well-typed iff absEval succeeds (returns some).

      Key insight: with mu-as-value, the value env is always the identity
      mapping (bvar k → bvar k), so it's eliminated entirely. absEval uses
      only a type context — a list of domain annotations for bound variables. -/
  def absEval (fuel : Nat) (ctx : TyCtx) (e : Expr) : Except String NfExpr :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match e with
      | .bvar k       => .ok (.bvar k)
      | .lam dom body => do
        -- Evaluate domain (rejects ill-formed domains)
        let dom' ← absEval fuel ctx dom
        -- Evaluate body under binder with evaluated domain in context
        let body' ← absEval fuel (TyCtx.extend ctx dom') body
        .ok (.lam dom' body')
      | .type         => .ok .type
      | .asc term ty  => do
        -- Type checking happens here:
        -- 1. Evaluate term → sigma
        -- 2. Evaluate ty → tau
        -- 3. Check sigma ⊑ tau via subCheckNF
        -- 4. Return tau (erase term)
        let sigma ← absEval fuel ctx term
        let tau ← absEval fuel ctx ty
        if subCheckNF fuel ctx [] sigma tau then .ok tau
        else .error s!"ascription failed: {repr sigma} ⊄ {repr tau}"
      | .mu ann body  => do
        -- Evaluate annotation (rejects ill-formed annotations)
        let ann' ← absEval fuel ctx ann
        .ok (.mu ann' body)
      | .app f a      => do
        let f' ← absEval fuel ctx f
        let a' ← absEval fuel ctx a
        match f' with
        | .lam _dom body =>
          -- Beta-reduce via substitution
          absEval fuel ctx (body.subst 0 a')
        | .mu _ann body =>
          -- mu in function position. Strategy depends on ann AND body shape.
          match _ann, body with
          | .lam _dom retBody, .lam _ _ =>
            absEval fuel ctx (retBody.subst 0 a')
          | _, .lam _dom retBody =>
            absEval fuel ctx (retBody.subst 0 a')
          | _, _ => .ok (.app body a')
        | .type => .error "Type is not callable"
        | _ =>
          -- Neutral application: validate callability, return symbolic app
          if isCallableNF ctx f' then .ok (.app f' a')
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
      -- Normalize both sides to head form via absEval
      let a := match absEval fuel ctx a with | .ok x => x | .error _ => a
      let b := match absEval fuel ctx b with | .ok x => x | .error _ => b
      if a == b then true
      else if seen.any (fun (a', b') => a == a' && b == b') then true
      else match b with
      | .type => true
      | _ =>
        match a, b with
        | .lam domA bodyA, .lam domB bodyB =>
          -- Function subtyping: contravariant domain, covariant body
          let domA_norm := match absEval fuel ctx domA with | .ok x => x | .error _ => domA
          let domB_norm := match absEval fuel ctx domB with | .ok x => x | .error _ => domB
          subCheckNF fuel ctx seen domB_norm domA_norm
          -- TyCtx.extend shifts domB_norm automatically
          && subCheckNF fuel (TyCtx.extend ctx domB_norm) seen bodyA bodyB
        | .mu _annA bodyA, .mu _annB bodyB =>
          -- Mu subtyping: covariant in body
          let ctxA := TyCtx.extend ctx (.mu _annA bodyA)
          let bodyA' := match absEval fuel ctxA bodyA with | .ok x => x | .error _ => bodyA
          let bodyB' := match absEval fuel ctxA bodyB with | .ok x => x | .error _ => bodyB
          subCheckNF fuel ctxA seen bodyA' bodyB'
        | _, .mu _ann body =>
          -- Self-intro (equi-recursive): a ⊑ mu ann body  iff  a ⊑ body[0 := mu]
          let u := body.subst 0 b
          let u' := match absEval fuel ctx u with | .ok x => x | .error _ => u
          subCheckNF fuel ctx ((a, b) :: seen) a u'
        | .mu ann body, _ =>
          -- Self-elim: mu ann body ⊑ b  iff  body[0 := mu] ⊑ b
          let u := body.subst 0 (.mu ann body)
          let u' := match absEval fuel ctx u with | .ok x => x | .error _ => u
          subCheckNF fuel ctx ((a, b) :: seen) u' b
        | _, _ =>
          match inferType ctx a with
          | some ty => subCheckNF fuel ctx seen ty b
          | none => false
  termination_by fuel
end

/-! ## Decidable subtyping -/

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] a, absEval fuel [] b with
  | .ok a', .ok b' => subCheckNF fuel [] [] a' b'
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

/-- absEval fuel monotonicity. With the new mutual definition, this needs
    updating. Sorry'd for now. -/
theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {e v : Expr}
    (h : absEval n ctx e = .ok v) : absEval (n + 1) ctx e = .ok v := by
  sorry
