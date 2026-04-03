import Och.Syntax

/-!
# Och Evaluation (de Bruijn)

Three evaluators:
- **`concEval` (concrete/runtime):** Substitution-based CBV. Lambdas are
  values (bodies not evaluated until applied). `(e : τ)` takes the lhs `e`.
- **`concEvalE` (concrete/env-based):** Environment-based concrete evaluator,
  structurally parallel to the old absEval. Used for soundness proofs.
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

## Environment (concEvalE only)

The environment is a positional list: `env[k]` is the value for bvar k.
When entering a binder, we extend with a new entry and shift existing
entries up by 1 (so their free variable indices stay correct at the new depth).

## Beta-reduction

All evaluators use substitution for beta-reduction. When a lambda is applied,
substitute the argument for bvar 0 in the body, then re-evaluate.
-/

open Expr

/-! ## Type aliases and contexts -/

/-- An expression that has been through absEval with some context.
    Invariants (not enforced by the type system, proved separately):
    - No `.asc` constructors (ascriptions erased)
    - No redexes (`.app (.lam ..) ..` does not occur)
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

/-- Evaluation environment: positional list of values.
    env[k] is the value for bvar k. Used by concEvalE only. -/
abbrev Env := List Expr

/-- Extend env for a new binder. Adds the new binding at position 0 and shifts
    existing entries so their free variables adjust for the new depth. -/
def Env.extend (env : Env) (v : Expr) : Env :=
  v :: env.map (Expr.shift 1 0)

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
  def absEval (fuel : Nat) (ctx : TyCtx) (e : Expr) : Option NfExpr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match e with
      | .bvar k       => some (.bvar k)
      | .lam dom body =>
        -- Evaluate domain (rejects ill-formed domains)
        match absEval fuel ctx dom with
        | some dom' =>
          -- Evaluate body under binder with evaluated domain in context
          match absEval fuel (TyCtx.extend ctx dom') body with
          | some body' => some (.lam dom' body')
          | none => none
        | none => none
      | .type         => some .type
      | .asc term ty  =>
        -- Type checking happens here:
        -- 1. Evaluate term → sigma
        -- 2. Evaluate ty → tau
        -- 3. Check sigma ⊑ tau via subCheckNF
        -- 4. Return tau (erase term)
        match absEval fuel ctx term, absEval fuel ctx ty with
        | some sigma, some tau =>
          if subCheckNF fuel ctx [] sigma tau then some tau
          else none
        | _, _ => none
      | .mu ann body  =>
        -- Evaluate annotation (rejects ill-formed annotations)
        match absEval fuel ctx ann with
        | some ann' => some (.mu ann' body)
        | none => none
      | .app f a      =>
        match absEval fuel ctx f, absEval fuel ctx a with
        | some (.lam _dom body), some aVal =>
          -- Beta-reduce via substitution
          absEval fuel ctx (body.subst 0 aVal)
        | some (.mu _ann body), some aVal =>
          -- mu in function position. Strategy depends on ann AND body shape.
          match _ann, body with
          | .lam _dom retBody, .lam _ _ =>
            absEval fuel ctx (retBody.subst 0 aVal)
          | _, .lam _dom retBody =>
            absEval fuel ctx (retBody.subst 0 aVal)
          | _, _ => some (.app body aVal)
        | some .type, _ => none  -- Type is not callable
        | some f', some a' =>
          -- Neutral application: validate callability, return symbolic app
          if isCallableNF ctx f' then some (.app f' a')
          else none
        | _, _ => none
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
      let a := match absEval fuel ctx a with | some x => x | none => a
      let b := match absEval fuel ctx b with | some x => x | none => b
      if a == b then true
      else if seen.any (fun (a', b') => a == a' && b == b') then true
      else match b with
      | .type => true
      | _ =>
        match a, b with
        | .lam domA bodyA, .lam domB bodyB =>
          -- Function subtyping: contravariant domain, covariant body
          let domA_norm := match absEval fuel ctx domA with | some x => x | none => domA
          let domB_norm := match absEval fuel ctx domB with | some x => x | none => domB
          subCheckNF fuel ctx seen domB_norm domA_norm
          -- TyCtx.extend shifts domB_norm automatically
          && subCheckNF fuel (TyCtx.extend ctx domB_norm) seen bodyA bodyB
        | .mu _annA bodyA, .mu _annB bodyB =>
          -- Mu subtyping: covariant in body
          let ctxA := TyCtx.extend ctx (.mu _annA bodyA)
          let bodyA' := match absEval fuel ctxA bodyA with | some x => x | none => bodyA
          let bodyB' := match absEval fuel ctxA bodyB with | some x => x | none => bodyB
          subCheckNF fuel ctxA seen bodyA' bodyB'
        | _, .mu _ann body =>
          -- Self-intro (equi-recursive): a ⊑ mu ann body  iff  a ⊑ body[0 := mu]
          let u := body.subst 0 b
          let u' := match absEval fuel ctx u with | some x => x | none => u
          subCheckNF fuel ctx ((a, b) :: seen) a u'
        | .mu ann body, _ =>
          -- Self-elim: mu ann body ⊑ b  iff  body[0 := mu] ⊑ b
          let u := body.subst 0 (.mu ann body)
          let u' := match absEval fuel ctx u with | some x => x | none => u
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
  | some a', some b' => subCheckNF fuel [] [] a' b'
  | _, _ => false

/-! ## Concrete evaluators -/

/-- Concrete evaluator. Standard call-by-value lambda calculus with substitution.

    Lambdas are values — their bodies are NOT evaluated until applied.
    Uses substitution for beta-reduction. Operates on closed terms only
    (free bvars return None). -/
def concEval (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar _ => none  -- free variable = stuck (expects closed terms)
    | .lam _ _ => some e  -- lambda is a VALUE — body not evaluated
    | .type => some .type
    | .asc term _ => concEval fuel term  -- runtime: erase ascription
    | .mu ann body =>
      -- Unroll: substitute self-reference into body, then evaluate
      concEval fuel (body.subst 0 (.mu ann body))
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | some (.lam _dom body), some aVal =>
        -- Beta-reduce via substitution
        concEval fuel (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- mu in function position: unroll and retry
        match concEval fuel (.mu ann body) with
        | some (.lam _dom lamBody) => concEval fuel (lamBody.subst 0 aVal)
        | some fVal => some (.app fVal aVal)
        | none => none
      | some fVal, some aVal => some (.app fVal aVal)
      | _, _ => none

/-- Environment-based concrete evaluator. Structurally parallel to the old absEval.

    The ONLY difference from the old absEval is the ascription case:
    - old absEval takes the rhs (type annotation) — compile-time semantics
    - concEvalE takes the lhs (term value) — runtime semantics

    Used as a proof auxiliary for soundness_gen. The env-based structure
    makes the induction hypothesis apply directly (both evaluators normalize
    under binders, so outputs are related by IH). -/
def concEvalE (fuel : Nat) (env : Env) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .bvar k       => env.get? k
    | .lam dom body =>
      match concEvalE fuel (env.extend (.bvar 0)) body with
      | some body' => some (.lam dom body')
      | none => none
    | .type         => some .type
    | .asc term _   => concEvalE fuel env term  -- runtime: take the lhs
    | .mu _ann _body => some e  -- mu is a value, like lambda
    | .app f a      =>
      match concEvalE fuel env f, concEvalE fuel env a with
      | some (.lam _dom body), some aVal =>
        concEvalE fuel env (body.subst 0 aVal)
      | some (.mu ann body), some aVal =>
        -- Match on ann AND body, mirroring the old absEval's mu-app case.
        match ann, body with
        | .lam _dom retBody, .lam _ _ =>
          concEvalE fuel env (retBody.subst 0 aVal)
        | _, .lam _dom lamBody =>
          concEvalE fuel env (lamBody.subst 0 aVal)
        | _, _ => some (.app body aVal)
      | some f', some a' => some (.app f' a')
      | _, _ => none

/-! ## Asc-free expressions and evaluator equivalence

Both evaluators strip ascription from their outputs. On asc-free inputs,
concEvalE and the old absEval are identical (they differ ONLY at the asc case).
This is the key insight for the soundness_gen app case: after beta-reduction,
both sides effectively use the same evaluator.

NOTE: These properties were proved for the old env-based absEval. With the new
TyCtx-based absEval, the relationship between concEvalE and absEval changes
(absEval no longer takes an env). The asc-free equivalence may need to be
restated in terms of the new absEval. For now, the key properties are sorry'd
pending the updated proof strategy. -/

/-- An expression is asc-free if it contains no `.asc` constructor. -/
def Expr.ascFree : Expr → Prop
  | .bvar _ => True
  | .lam dom body => dom.ascFree ∧ body.ascFree
  | .app f a => f.ascFree ∧ a.ascFree
  | .asc _ _ => False
  | .type => True
  | .mu ann body => ann.ascFree ∧ body.ascFree

/-- Bool-valued version for native_decide. -/
def Expr.ascFreeB : Expr → Bool
  | .bvar _ => true
  | .lam dom body => dom.ascFreeB && body.ascFreeB
  | .app f a => f.ascFreeB && a.ascFreeB
  | .asc _ _ => false
  | .type => true
  | .mu ann body => ann.ascFreeB && body.ascFreeB

theorem Expr.ascFree_iff_ascFreeB (e : Expr) : e.ascFree ↔ e.ascFreeB = true := by
  induction e with
  | bvar _ => simp [ascFree, ascFreeB]
  | type => simp [ascFree, ascFreeB]
  | asc _ _ => simp [ascFree, ascFreeB]
  | lam dom body ih_d ih_b => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_d, ih_b]
  | app f a ih_f ih_a => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_f, ih_a]
  | mu ann body ih_a ih_b => simp [ascFree, ascFreeB, Bool.and_eq_true, ih_a, ih_b]

/-- Shifting preserves asc-free. -/
theorem Expr.ascFree_shift {e : Expr} {d c : Nat}
    (he : e.ascFree) : (e.shift d c).ascFree := by
  induction e generalizing c with
  | bvar _ => simp [shift]; split <;> simp [ascFree]
  | type => simp [shift, ascFree]
  | asc _ _ => exact absurd he (by simp [ascFree])
  | lam _ _ ih_d ih_b =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_d he.1, ih_b he.2⟩
  | app _ _ ih_f ih_a =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_f he.1, ih_a he.2⟩
  | mu _ _ ih_a ih_b =>
    simp [ascFree] at he; simp [shift, ascFree]
    exact ⟨ih_a he.1, ih_b he.2⟩

/-- Substitution preserves asc-free. -/
theorem Expr.ascFree_subst {e : Expr} {j : Nat} {s : Expr}
    (he : e.ascFree) (hs : s.ascFree) : (e.subst j s).ascFree := by
  induction e generalizing j s with
  | bvar k =>
    simp [subst]
    split
    · exact hs  -- k == j: result is s
    · split
      · simp [ascFree]  -- k > j: bvar (k-1)
      · simp [ascFree]  -- k < j: bvar k
  | type => simp [subst, ascFree]
  | asc _ _ => exact absurd he (by simp [ascFree])
  | lam dom body ih_d ih_b =>
    simp [ascFree] at he; obtain ⟨hd, hb⟩ := he
    simp [subst, ascFree]
    exact ⟨ih_d hd hs, ih_b hb (ascFree_shift hs)⟩
  | app f a ih_f ih_a =>
    simp [ascFree] at he; obtain ⟨hf, ha⟩ := he
    simp [subst, ascFree]; exact ⟨ih_f hf hs, ih_a ha hs⟩
  | mu ann body ih_a ih_b =>
    simp [ascFree] at he; obtain ⟨ha, hb⟩ := he
    simp [subst, ascFree]
    exact ⟨ih_a ha hs, ih_b hb (ascFree_shift hs)⟩

/-- Env.extend with an asc-free value preserves the env asc-free invariant. -/
theorem Env.extend_ascFree {env : Env} {v : Expr}
    (henv : ∀ k e, env.get? k = some e → e.ascFree)
    (hv : v.ascFree)
    : ∀ k e, (Env.extend env v).get? k = some e → e.ascFree := by
  intro k e hk
  simp [Env.extend] at hk
  cases k with
  | zero =>
    simp at hk; subst hk; exact hv
  | succ j =>
    simp [List.get?] at hk
    obtain ⟨a, ha_lookup, ha_shift⟩ := hk
    subst ha_shift
    have := henv j a
    exact Expr.ascFree_shift (this (by rwa [List.get?_eq_getElem?]))

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
      simp only [concEval] at h ⊢; exact ih h
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
          | .mu ann body_mu =>
            match hmu : concEval k (.mu ann body_mu) with
            | none => simp [hmu] at h
            | some muv =>
              have hmu' := ih hmu
              simp only [hmu] at h
              simp only [hmu']
              match muv with
              | .lam _dom lamBody => exact ih h
              | .type => exact h
              | .bvar _ | .app _ _ | .asc _ _ | .mu _ _ => exact h
          | .type => exact h
          | .bvar _ | .app _ _ | .asc _ _ => exact h

/-- absEval fuel monotonicity. With the new mutual definition, this needs
    updating. Sorry'd for now. -/
theorem absEval_fuel_mono {n : Nat} {ctx : TyCtx} {e v : Expr}
    (h : absEval n ctx e = some v) : absEval (n + 1) ctx e = some v := by
  sorry
