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
          -- Function subtyping: contravariant domain, covariant body
          let domA_norm := match absEval fuel ctx seen domA with | .ok x => x.val | .error _ => domA
          let domB_norm := match absEval fuel ctx seen domB with | .ok x => x.val | .error _ => domB
          subCheckNF fuel ctx seen domB_norm domA_norm
          -- TyCtx.extend shifts domB_norm automatically
          && subCheckNF fuel (TyCtx.extend ctx ⟨domB_norm⟩) seen bodyA bodyB
        | _, .mu _ann body =>
          -- Self-intro (equi-recursive): a ⊑ mu ann body  iff  a ⊑ body[0 := mu]
          -- This also handles the mu-mu case via self-intro on the right side.
          let seen' := (a, b) :: seen
          let u := body.subst 0 b
          let u' := match absEval fuel ctx seen' u with | .ok x => x.val | .error _ => u
          subCheckNF fuel ctx seen' a u'
        | .mu ann body, _ =>
          -- Self-elim: mu ann body ⊑ b  iff  body[0 := mu] ⊑ b
          -- When normalization of the unfolded body fails (e.g. domain checks
          -- on Church-encoded types with abstract arguments), fall back to the
          -- mu annotation. The annotation is the declared type of the recursive
          -- function and has already been normalized (in absEval's .mu case).
          let seen' := (a, b) :: seen
          let u := body.subst 0 (.mu ann body)
          let u' := match absEval fuel ctx seen' u with
            | .ok x => x.val
            | .error _ => ann  -- annotation fallback
          subCheckNF fuel ctx seen' u' b
        | .app f1 a1, .app f2 a2 =>
          -- App congruence: f a ⊑ g b when f ⊑ g and a ⊑ b.
          -- Sound in the coinductive setting (Amadio-Cardelli style): the `seen`
          -- set ensures monotonicity is only assumed for pairs being verified.
          -- Needed for dependent self-types where e.g. P dtrue ⊑ P dBool
          -- decomposes into P ⊑ P (reflexivity) and dtrue ⊑ dBool (in `seen`).
          if subCheckNF fuel ctx seen f1 f2 && subCheckNF fuel ctx seen a1 a2
          then true
          else
            match inferType ctx a with
            | some ty =>
              let ty' := match absEval fuel ctx seen ty with | .ok x => x.val | .error _ => ty
              subCheckNF fuel ctx seen ty' b
            | none => false
        | _, _ =>
          match inferType ctx a with
          | some ty =>
            let ty' := match absEval fuel ctx seen ty with | .ok x => x.val | .error _ => ty
            subCheckNF fuel ctx seen ty' b
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

/-- Helper for absEval_fuel_mono: the mu-app case where body' is lam
    and _ann is NOT lam. The if-then-else and inner match only differ
    in fuel for recursive absEval calls. -/
private theorem absEval_fuel_mono_mu_lam_body
    {k : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {_ann : Expr} {d1 b1 : Expr} {a'val : Expr} {v : NfExpr}
    (ih : ∀ {ctx : TyCtx} {seen : List (Expr × Expr)} {e : Expr} {v : NfExpr},
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
    cases u <;> exact ih h

/-- subCheckNF fuel monotonicity: if a subtype check passes at fuel n,
    it passes at fuel n+1. Needed by absEval_fuel_mono for the .asc and
    domain-check cases. Sorry'd — the proof requires handling the
    normalization-with-fallback pattern in subCheckNF's lam and mu cases. -/
theorem subCheckNF_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {a b : Expr}
    (h : subCheckNF n ctx seen a b = true) : subCheckNF (n + 1) ctx seen a b = true := by
  sorry

/-- absEval fuel monotonicity: if absEval succeeds at fuel n, it succeeds
    at fuel n+1 with the same result. Uses subCheckNF_fuel_mono for the
    .asc and domain-check cases. -/
theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {seen : List (Expr × Expr)}
    {e : Expr} {v : NfExpr}
    (h : absEval n ctx seen e = .ok v) : absEval (n + 1) ctx seen e = .ok v := by
  induction n generalizing ctx seen e v with
  | zero => simp [absEval] at h
  | succ k ih =>
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
          rw [ih hd]; simp only [bind, Except.bind]; rw [ih hb]; simp only [bind, Except.bind]
          exact h
    | .mu ann body =>
      unfold absEval at h ⊢; dsimp only [] at h ⊢
      match ha : absEval k ctx seen ann with
      | .error _ => simp [ha, bind, Except.bind] at h
      | .ok ann' =>
        simp only [ha, bind, Except.bind] at h
        rw [ih ha]; simp only [bind, Except.bind]
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
          rw [ih ht]; simp only [bind, Except.bind]
          rw [ih hty]; simp only [bind, Except.bind]
          split at h
          · rename_i hsub
            rw [show subCheckNF (k + 1) ctx seen sigma.val tau.val = true
              from subCheckNF_fuel_mono hsub]
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
          rw [ih hf]; simp only [bind, Except.bind]
          rw [ih ha]; simp only [bind, Except.bind]
          -- Both h and goal match on f'.val with fuel k vs k+1 in recursive calls
          match hfv : f'.val with
          | .lam dom body =>
            simp only [hfv] at h ⊢
            split at h
            · rename_i hsub
              rw [show subCheckNF (k + 1) ctx seen a'.val dom = true
                from subCheckNF_fuel_mono hsub]
              exact ih h
            · simp at h
          | .mu _ann body' =>
            simp only [hfv] at h ⊢
            -- mu-app: case-split to reduce the term-level match.
            cases body' with
            | lam d1 b1 =>
              cases _ann with
              | lam _ _ => exact ih h  -- first arm: both lam
              | bvar _ | app _ _ | type | mu _ _ | asc _ _ =>
                -- second arm: _ann not lam, body' lam
                exact absEval_fuel_mono_mu_lam_body ih h
            | bvar _ | app _ _ | type | mu _ _ | asc _ _ =>
              -- third arm: body' not lam, catch-all
              cases _ann <;> exact h
          | .type =>
            simp only [hfv] at h; simp at h
          | .bvar _ | .app _ _ | .asc _ _ =>
            simp only [hfv] at h ⊢; exact h
