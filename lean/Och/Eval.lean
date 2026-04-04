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
      (e : Expr) : Except String NfExpr :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match e with
      | .bvar k       => .ok ⟨.bvar k⟩
      | .lam dom body => do
        -- Evaluate domain (rejects ill-formed domains)
        let dom' ← absEval fuel ctx seen dom
        -- Evaluate body under binder with evaluated domain in context
        let body' ← absEval fuel (TyCtx.extend ctx dom') seen body
        .ok ⟨.lam dom'.val body'.val⟩
      | .type         => .ok ⟨.type⟩
      | .asc term ty  => do
        -- Type checking happens here:
        -- 1. Evaluate term → sigma
        -- 2. Evaluate ty → tau
        -- 3. Check sigma ⊑ tau via subCheckNF
        -- 4. Return tau (erase term)
        let sigma ← absEval fuel ctx seen term
        let tau ← absEval fuel ctx seen ty
        if subCheckNF fuel ctx seen sigma.val tau.val then .ok tau
        else .error s!"ascription failed: {repr sigma} ⊄ {repr tau}"
      | .mu ann body  => do
        -- Evaluate annotation (rejects ill-formed annotations)
        let ann' ← absEval fuel ctx seen ann
        .ok ⟨.mu ann'.val body⟩
      | .app f a      => do
        let f' ← absEval fuel ctx seen f
        let a' ← absEval fuel ctx seen a
        match f'.val with
        | .lam dom body =>
          -- Check argument against domain annotation, then beta-reduce.
          -- `dom` is already normalized (it's a sub-expression of f', an absEval
          -- output), so re-normalization is unnecessary. Using it directly also
          -- makes fuel monotonicity provable without an idempotency lemma.
          if subCheckNF fuel ctx seen a'.val dom then
            absEval fuel ctx seen (body.subst 0 a'.val)
          else .error s!"domain check failed: {repr a'} ⊄ {repr dom}"
        | .mu _ann body =>
          -- mu in function position. Strategy depends on ann AND body shape.
          match _ann, body with
          | .lam _dom retBody, .lam _ _ =>
            -- Annotation is a function type: use annotation's return type.
            -- This trusts the annotation as the type of the recursive function,
            -- avoiding normalization of the raw body (which may fail for
            -- abstract arguments due to domain checks on Church-encoded types).
            absEval fuel ctx seen (retBody.subst 0 a'.val)
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
                absEval fuel ctx seen' (retBody2.subst 0 a'.val)
              | _ =>
                absEval fuel ctx seen' (.app unfolded a'.val)
          | _, _ => .ok ⟨.app body a'.val⟩
        | .type => .error "Type is not callable"
        | _ =>
          -- Neutral application: validate callability, return symbolic app
          if isCallableNF ctx f' then .ok ⟨.app f'.val a'.val⟩
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
          -- Self-intro (equi-recursive): a ⊑ mu ann body  iff  a ⊑ body[0 := mu]
          -- This also handles the mu-mu case via self-intro on the right side.
          let seen' := (a, b) :: seen
          let u := body.subst 0 b
          match absEval fuel ctx seen' u with
          | .ok u' => subCheckNF fuel ctx seen' a u'.val
          | .error _ => false
        | .mu ann body, _ =>
          -- Self-elim: mu ann body ⊑ b  iff  ann ⊑ b  or  normalize(body[0:=mu]) ⊑ b.
          -- Check annotation first (fuel-stable), then try body normalization.
          -- This ordering makes fuel monotonicity provable: the annotation check
          -- doesn't depend on absEval fuel, and the body check is stable because
          -- absEval_fuel_mono ensures normalization results don't change with fuel.
          -- The annotation is the declared type and was already normalized in
          -- absEval's .mu case.
          let seen' := (a, b) :: seen
          if subCheckNF fuel ctx seen' ann b then true
          else
            let u := body.subst 0 (.mu ann body)
            match absEval fuel ctx seen' u with
            | .ok u' => subCheckNF fuel ctx seen' u'.val b
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

/-! ## Fuel monotonicity (mutual proof)

absEval and subCheckNF are mutually recursive, so their fuel monotonicity
proofs must be proved together. We prove a combined theorem by induction on
fuel, then extract the individual results. -/

/-- Helper for the mu-app case in absEval_fuel_mono: body' is lam and _ann is
    NOT lam. Parameterized by ih_abs (absEval at fuel k → k+1). -/
private theorem absEval_fuel_mono_mu_lam_body
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {_ann : Expr} {d1 b1 : Expr} {a'val : Expr} {v : NfExpr}
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (let mu_expr := Expr.mu _ann (Expr.lam d1 b1)
          if (seen.any fun x => x.fst == mu_expr) = true then
            Except.ok { val := mu_expr.app a'val }
          else
            match (Expr.lam d1 b1).subst 0 mu_expr with
            | .lam _d3 rB3 => absEval k ctx ((mu_expr, mu_expr) :: seen) (rB3.subst 0 a'val)
            | _ => absEval k ctx ((mu_expr, mu_expr) :: seen)
                     (((Expr.lam d1 b1).subst 0 mu_expr).app a'val))
         = Except.ok v)
    : (let mu_expr := Expr.mu _ann (Expr.lam d1 b1)
       if (seen.any fun x => x.fst == mu_expr) = true then
         Except.ok { val := mu_expr.app a'val }
       else
         match (Expr.lam d1 b1).subst 0 mu_expr with
         | .lam _d3 rB3 => absEval (k + 1) ctx ((mu_expr, mu_expr) :: seen) (rB3.subst 0 a'val)
         | _ => absEval (k + 1) ctx ((mu_expr, mu_expr) :: seen)
                  (((Expr.lam d1 b1).subst 0 mu_expr).app a'val))
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

/-- Helper for the self-elim case: annotation-first, then body normalization. -/
private theorem subCheckNF_self_elim_step
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {ann body : Expr} {b : Expr}
    (ih_sub : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {a b : Expr},
          subCheckNF k ctx seen a b = true → subCheckNF (k + 1) ctx seen a b = true)
    (ih_abs : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
          absEval k ctx seen e = .ok v → absEval (k + 1) ctx seen e = .ok v)
    (h : (let seen' := (Expr.mu ann body, b) :: seen
          if subCheckNF k ctx seen' ann b then true
          else
            let u := body.subst 0 (Expr.mu ann body)
            match absEval k ctx seen' u with
            | .ok u' => subCheckNF k ctx seen' u'.val b
            | .error _ => false) = true)
    : (let seen' := (Expr.mu ann body, b) :: seen
       if subCheckNF (k + 1) ctx seen' ann b then true
       else
         let u := body.subst 0 (Expr.mu ann body)
         match absEval (k + 1) ctx seen' u with
         | .ok u' => subCheckNF (k + 1) ctx seen' u'.val b
         | .error _ => false) = true := by
  simp only [] at h ⊢
  split at h
  · rename_i hann
    rw [show subCheckNF (k + 1) _ _ ann b = true from ih_sub hann]; simp
  · rename_i hann
    -- h is already simplified to the else branch by split
    split
    · simp
    · rename_i hann'
      exact subCheckNF_absEval_step ih_sub ih_abs h

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
    (∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
      absEval n ctx seen e = .ok v → absEval (n + 1) ctx seen e = .ok v) := by
  induction n with
  | zero =>
    exact ⟨fun h => by simp [subCheckNF] at h, fun h => by simp [absEval] at h⟩
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
      intro ctx seen e v h
      match e with
      | .bvar _ =>
        simp [absEval] at h ⊢; exact h
      | .type =>
        simp [absEval] at h ⊢; exact h
      | .lam dom body =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match hd : absEval k ctx seen dom with
        | .error _ => simp [hd, bind, Except.bind] at h
        | .ok dom' =>
          simp only [hd, bind, Except.bind] at h
          match hb : absEval k (TyCtx.extend ctx dom') seen body with
          | .error _ => simp [hb, bind, Except.bind] at h
          | .ok body' =>
            simp only [hb, bind, Except.bind] at h
            rw [ih_abs hd]; simp only [bind, Except.bind]
            rw [ih_abs hb]; simp only [bind, Except.bind]
            exact h
      | .mu ann body =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match ha : absEval k ctx seen ann with
        | .error _ => simp [ha, bind, Except.bind] at h
        | .ok ann' =>
          simp only [ha, bind, Except.bind] at h
          rw [ih_abs ha]; simp only [bind, Except.bind]
          exact h
      | .asc term ty =>
        unfold absEval at h ⊢; dsimp only [] at h ⊢
        match ht : absEval k ctx seen term with
        | .error _ => simp [ht, bind, Except.bind] at h
        | .ok sigma =>
          simp only [ht, bind, Except.bind] at h ⊢
          match hty : absEval k ctx seen ty with
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
        match hf : absEval k ctx seen f with
        | .error _ => simp [hf, bind, Except.bind] at h
        | .ok f' =>
          simp only [hf, bind, Except.bind] at h ⊢
          match ha : absEval k ctx seen a with
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
                rw [show subCheckNF (k + 1) ctx seen a'.val dom = true
                  from ih_sub hsub]
                exact ih_abs h
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
              simp only [hfv] at h ⊢; exact h

/-- subCheckNF fuel monotonicity: if a subtype check passes at fuel n,
    it also passes at fuel n+1. -/
theorem subCheckNF_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : subCheckNF n ctx seen a b = true) : subCheckNF (n + 1) ctx seen a b = true :=
  (fuel_mono n).1 h

/-- absEval fuel monotonicity: if absEval succeeds at fuel n, it succeeds
    at fuel n+1 with the same result. -/
theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {v : NfExpr}
    (h : absEval n ctx seen e = .ok v) : absEval (n + 1) ctx seen e = .ok v :=
  (fuel_mono n).2 h
