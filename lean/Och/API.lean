import Och.Syntax
import Och.Outcome
import Och.EvalSubst
import Och.TyCheck

/-!
# Och public typing/subtyping API

The single user-facing surface for Och's type-checking and
subtype-checking pipeline.

## Surface

```
structure Och.WTValue where
  private mk ::
  whnf : Expr      -- well-typed value (in WHNF) by construction

def Och.synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue
def Och.subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool
def Och.subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool
```

The `private mk` constructor is the API enforcement: a `WTValue`
can only be obtained via `synth`, which validates `e` end-to-end
(walks every binder/app/asc, domain-checks every application).
`subCheck` then runs the structural Expr-level engine on the
already-validated WHNFs.

## Design (synth = structural walk + the engine for typing questions)

`synth Γ e` is a structural walk that returns `e`'s WHNF (which
is its most-precise type via `Subtype'.refl`), validating
well-typedness at every node. All "is X well-typed at Y?"
questions are delegated to the existing complete structural
engine `SubstEval.subCheckOpen`.

```
synth Γ e
| .top           => ok .top
| .bot           => ok .bot
| .bvar k        => ok (Γ[k])      -- type-via-Refl for neutrals
| .lam A b       => synth Γ A; synth (Γ.push A) (open b);
                      ok (.lam A b)              -- canonical
| .iota A b      => synth Γ A; synth (Γ.push A) (open b);
                      ok (.iota A b)             -- canonical
| .fix A b       => synth Γ A; synth (Γ.push A) (open b);
                      ok (.fix A b)              -- canonical
| .app f a       => v_f ← synth Γ f
                    v_a ← synth Γ a
                    expose Π (.lam dom body) from v_f
                       (via fix/iota unfold if needed; FAIL if no Π)
                    subCheckOpen v_a dom         -- THE typing question
                    ok (whnf (.app v_f a))
| .asc e τ       => synth Γ τ
                    v ← synth Γ e
                    subCheckOpen v τV
                    ok v
| .letE val body => v_val ← synth Γ val
                    synth (Γ.push v_val) (open body)
                    ok (whnf (.letE val body))
```

Why this works (vs the previous tyInfer-based attempt):

- The previous `synth = tyInfer + evalSubst` was algorithmically
  incomplete: `TyCheck.tyInfer` is a bidirectional walk that
  stalls on the A6-family of well-formed Och programs (returns
  `.error` on `succ_`, `one_`, `mkVec`, `appendVec`, ...). The
  former pragmatic compromise — fall back to `evalSubst` on
  `.error` — silently accepted ill-typed terms whose WHNFs
  happened to match (A3, `appendVec_wrong`).

- The new synth bypasses the bidirectional dispatch and asks the
  *complete* structural engine (`subCheckOpen`) to decide each
  domain check directly. The engine is what the previous
  `subCheckT` fell back to, and it's the one piece of the stack
  that's actually complete on Och programs in practice.

## Soundness theorems

See `Och/Soundness.lean` for the (sorry'd) statements:

  - `synth_sound`: `(synth e).isOk → ∃ τ, Subtype' [] [] e τ`
  - `subCheck_sound`: `subCheck a b = .ok true → Subtype' [] [] a.whnf b.whnf`

Both are sorry-preserved scaffolds for future re-proving on the
substitution substrate.
-/

namespace Och

open SubstEval

/-- A well-typed value: `whnf` is an `Expr` in head-normal form
that has been validated by the structural walk in `synth`. The
`mk` constructor is `private`; the only public way to obtain a
`WTValue` is via `synth`. -/
structure WTValue where
  private mk ::
  /-- The validated expression in head-normal form. In Och, the
  natural type of a value is the value itself (per `Subtype'.refl`),
  so `whnf` doubles as both the value and a type witness. -/
  whnf : Expr
  deriving Repr

/-- Type context for `synth`: `Γ[k]` is the synthesised type of
the level-var `freshLevelVar k`. Mirrors `TyCheck.TyEnv` but
populated by the synth walk itself, never by `tyInfer`. -/
private abbrev TyEnv := Array Expr

/-! ## Synth core (private mutual block)

The walk takes an explicit type-environment `Γ` and threads
fuel through. Each node validates its sub-terms recursively and
calls `subCheckOpen` for the one typing question that arm asks
(domain check at app, ascription consistency at asc).

Termination is fuel-bounded; no `decreasing_by` clause beyond
fuel decrement. -/

/-- Synth helper: produce e's WHNF as a type-witness, validating
each node. See module doc.

Returns the *value* (WHNF) of `e` — for canonical forms (lam,
iota, fix, top, bot) that's `e` itself; for neutrals it's the
`Γ`-lookup type (which acts as the type-witness, since paper-B's
`~>` returns `Γ[k]` after the type-ascent step embedded in the
app rule). For `.app`, it's the WHNF of the β-reduced result.

- `.ok v` — `e` synthesised; `v` is its WHNF type-witness.
- `.outOfFuel` — fuel exhausted.
- `.error msg` — `e` is ill-typed (a domain check failed) or
  operationally stuck. -/
private partial def synthCore (fuel : Nat) (Γ : TyEnv) (e : Expr) :
    Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .type => .ok .type
    | .bot  => .ok .bot
    | .bvar k =>
        match asLevelVar e with
        | some lvl =>
            -- Per paper-B [I-Var]: `Γ ⊢ x ~> x`. The variable returns
            -- itself (Refl-typing convention: a value IS its own most-
            -- precise type). Γ stores ascent types for `subCheckOpen`
            -- to consult during structural compares; we don't return
            -- the looked-up type here.
            if lvl < Γ.size then
              .ok e
            else
              .error s!"synth: unbound level-var {lvl} (|Γ|={Γ.size})"
        | none =>
            .error s!"synth: unbound bvar {k} (closed-form input expected)"
    | .lam dom body => do
        -- Per paper-B [I-Lam]: `Γ ⊢ A <~ top`. The annotation must be
        -- a Type (not deep-walked). Using `subCheckOpen Γ A .type` lets
        -- the structural engine handle abstract dependencies via
        -- ascent (e.g. `(P zero_) ⊑ Type` under Γ ∋ P:(N→Type) closes
        -- via the engine's spine walk). Deep-walking would force
        -- domain checks like `zero_ ⊑ N` against an opaque `N` from
        -- a surrounding `fix` — impossible without unfolding the fix,
        -- which only the engine knows how to do.
        let okDom ← subCheckOpen fuel Γ dom .type
        if !okDom then
          .error s!"synth: lam domain annotation is not a type"
        else
          let domV ← evalSubst fuel SubstEval.unfBound dom
          -- Open the body under a fresh level-var typed `domV`.
          let depth := Γ.size
          let bodyOpen := openFreshTop body depth
          let _bodyTy ← synthCore fuel (Γ.push domV) bodyOpen
          -- Canonical: a lambda is its own most-precise type.
          evalSubst fuel SubstEval.unfBound e
    | .iota ann body => do
        let okAnn ← subCheckOpen fuel Γ ann .type
        if !okAnn then
          .error s!"synth: iota annotation is not a type"
        else
          let annV ← evalSubst fuel SubstEval.unfBound ann
          let depth := Γ.size
          let bodyOpen := openFreshTop body depth
          let _bodyTy ← synthCore fuel (Γ.push annV) bodyOpen
          evalSubst fuel SubstEval.unfBound e
    | .fix ann body => do
        let okAnn ← subCheckOpen fuel Γ ann .type
        if !okAnn then
          .error s!"synth: fix annotation is not a type"
        else
          let annV ← evalSubst fuel SubstEval.unfBound ann
          let depth := Γ.size
          let bodyOpen := openFreshTop body depth
          let _bodyTy ← synthCore fuel (Γ.push annV) bodyOpen
          evalSubst fuel SubstEval.unfBound e
    | .asc inner τ => do
        -- τ must itself be a type; check structurally rather than
        -- deep-walk (same reasoning as binder annotations).
        let okτ ← subCheckOpen fuel Γ τ .type
        if !okτ then
          .error s!"synth: ascription type is not a type"
        else
          let τV ← evalSubst fuel SubstEval.unfBound τ
          let vInner ← synthCore fuel Γ inner
          -- The single typing question: vInner ⊑ τV.
          let ok ← subCheckOpen fuel Γ vInner τV
          if !ok then
            .error s!"synth: ascription rejected (term ⊄ annotation)"
          else
            .ok vInner
    | .letE val body => do
        let valV ← synthCore fuel Γ val
        let depth := Γ.size
        let bodyOpen := openFreshTop body depth
        let _bodyTy ← synthCore fuel (Γ.push valV) bodyOpen
        -- The whole `let` β-reduces to `body[val/0]`; return its WHNF.
        evalSubst fuel SubstEval.unfBound e
    | .app f a => do
        let vF ← synthCore fuel Γ f
        let _vA ← synthCore fuel Γ a   -- validates `a` recursively
        let aV ← evalSubst fuel SubstEval.unfBound a
        let fV ← evalSubst fuel SubstEval.unfBound f
        -- Expose a Π for the function. Per paper-B's Refl-typing
        -- convention, `synthCore` returns the *value* for both
        -- canonical and neutral heads — for neutrals we must ascend
        -- via Γ to recover its declared type, which IS a Π. For
        -- canonical heads (lam / fix-of-lam / iota-of-lam) the
        -- value IS the Π.
        let piExpr ← do
          match whnfPi fuel fV vF with
          | some piLam@(.lam ..) => .ok piLam
          | _ =>
              match (← neutralType fuel Γ vF) with
              | some ty =>
                  match whnfPi fuel fV ty with
                  | some piLam@(.lam ..) => .ok piLam
                  | _ => .error s!"synth: applied non-Π head (ascended to non-Π)"
              | none =>
                  .error s!"synth: applied non-Π head (no ascent type)"
        match piExpr with
        | .lam dom _body =>
            -- THE typing question: argument-vs-domain.
            -- If aV is a neutral, we explicitly ascend it via
            -- `neutralType` and check the ascended type ⊑ dom —
            -- this works around an engine quirk where the dispatch
            -- order in `subCheckSubstMatch` prefers unfolding a
            -- fix-headed RHS (here `dom` may itself be `Nat_` etc.)
            -- before ascending an LHS neutral, missing the obvious
            -- Refl closure when ascended-type == dom.
            let okArg ← do
              match (← neutralType fuel Γ aV) with
              | some aTy =>
                  -- Try ascended-type vs dom first; if false,
                  -- fall back to the value-vs-dom check (e.g.
                  -- when dom is Top, or aV is canonical).
                  match (← subCheckOpen fuel Γ aTy dom) with
                  | true => .ok true
                  | false => subCheckOpen fuel Γ aV dom
              | none => subCheckOpen fuel Γ aV dom
            if !okArg then
              .error s!"synth: arg ⊄ dom at .app"
            else
              -- Codomain at the argument: β over the exposed Π.
              evalSubst fuel SubstEval.unfBound (.app piExpr aV)
        | _ =>
            .error s!"synth: internal: non-Π piExpr after exposure"

/-! ## Public surface -/

/-- Produce a `WTValue` for `e`. Validates well-typedness via a
structural walk that delegates each typing question to the
complete structural engine `SubstEval.subCheckOpen`.

- `.ok ⟨v⟩` — `e` is well-typed; `v` is its WHNF type-witness.
- `.outOfFuel` — fuel exhausted in walk or eval.
- `.error msg` — `e` is ill-typed (rejected at app/asc) or
  operationally stuck (e.g. unbound bare bvar, applied non-Π).
-/
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  let v ← synthCore fuel #[] e
  pure ⟨v⟩

/-- Structural subtype check on already-typed values. Internally
calls the substitution-based structural engine on the validated
WHNFs.

- `.ok true` — `a.whnf ⊑ b.whnf` structurally.
- `.ok false` — not a subtype.
- `.outOfFuel` / `.error` — propagated from the engine.

Because `a` and `b` are `WTValue`s, both have already passed
`synth`'s validation walk. The structural compare is therefore
running on well-typed inputs by construction. -/
def subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool :=
  SubstEval.subCheck fuel a.whnf b.whnf

/-- Convenience: run `synth` on both inputs, then `subCheck`.
Returns `.error` if either input fails to type-check, `.ok b`
otherwise. The standard way to express "is `e` a subtype of `τ`?"
on raw `Expr` inputs.

Argument order mirrors the legacy `SubstEval.subCheckT` (fuel
first) for migration ergonomics. -/
def subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool := do
  let a ← synth e fuel
  let b ← synth τ fuel
  subCheck a b fuel

end Och
