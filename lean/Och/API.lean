import Och.Syntax
import Och.Outcome
import Och.EvalSubst

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

## Design (synth = structural walk + the engine for typing questions)

`synth Γ e` is a structural walk that returns `e`'s WHNF (which
is its most-precise type via `Subtype'.refl`), validating
well-typedness at every node. All "is X well-typed at Y?"
questions are delegated to the existing complete structural
engine `SubstEval.subCheckOpen`.

In the pure de Bruijn regime, descending under a binder does NOT
substitute — we recurse on the raw body with the context extended.
`bvar 0` in the body naturally refers to the new innermost binder.
-/

namespace Och

open SubstEval

/-- A well-typed value: `whnf` is an `Expr` in head-normal form
that has been validated by the structural walk in `synth`. The
`mk` constructor is `private`; the only public way to obtain a
`WTValue` is via `synth`. -/
structure WTValue where
  private mk ::
  /-- The validated expression in head-normal form. -/
  whnf : Expr
  deriving Repr

/-- Type context for `synth`: stores the types of free variables.
`Γ[Γ.length - 1 - k]` is the type of `bvar k`. Push to the end
when entering a binder.

Public so soundness lemmas in `Soundness/SynthSound.lean` can
mention `Γ`'s type when stating per-arm helper lemmas. -/
abbrev TyEnv := List Expr

/-! ## Synth core (private mutual block)

The walk takes an explicit type-environment `Γ` and threads
fuel through. Each node validates its sub-terms recursively and
calls `subCheckOpen` for the one typing question that arm asks
(domain check at app, ascription consistency at asc).

Termination is fuel-bounded. -/

/-- Synth helper: produce e's WHNF as a type-witness, validating
each node.

Returns the *value* (WHNF) of `e` — for canonical forms (lam,
iota, fix, top, bot) that's `e` itself; for neutrals it's the
`Γ`-lookup type (which acts as the type-witness). For `.app`,
it's the WHNF of the β-reduced result.

**Visibility.** Public so that soundness proofs can name it.

**Termination.** Non-`partial`: `fuel` strictly decreases at every
recursive call. -/
def synthCore (fuel : Nat) (Γ : TyEnv) (e : Expr) :
    Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .type => .ok .type
    | .bot  => .ok .bot
    | .bvar k =>
        -- Pure de Bruijn: bvar k is valid if k < Γ.length.
        if k < Γ.length then
          .ok e
        else
          .error s!"synth: unbound bvar {k} (|Γ|={Γ.length})"
    | .lam dom body => do
        let okDom ← subCheckOpen fuel Γ dom .type
        if !okDom then
          .error s!"synth: lam domain annotation is not a type"
        else
          let domV ← evalSubst fuel SubstEval.unfBound dom
          -- Descend into body without substitution. bvar 0 in body
          -- refers to the lambda parameter; extend Γ with domV.
          let _bodyTy ← synthCore fuel (domV :: Γ) body
          -- Canonical: a lambda is its own most-precise type.
          evalSubst fuel SubstEval.unfBound e
    | .iota ann body => do
        let okAnn ← subCheckOpen fuel Γ ann .type
        if !okAnn then
          .error s!"synth: iota annotation is not a type"
        else
          let annV ← evalSubst fuel SubstEval.unfBound ann
          let _bodyTy ← synthCore fuel (annV :: Γ) body
          evalSubst fuel SubstEval.unfBound e
    | .fix ann body => do
        let okAnn ← subCheckOpen fuel Γ ann .type
        if !okAnn then
          .error s!"synth: fix annotation is not a type"
        else
          let annV ← evalSubst fuel SubstEval.unfBound ann
          let _bodyTy ← synthCore fuel (annV :: Γ) body
          evalSubst fuel SubstEval.unfBound e
    | .asc inner τ => do
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
        -- Descend into body without substitution.
        let _bodyTy ← synthCore fuel (valV :: Γ) body
        -- The whole `let` β-reduces to `body[val/0]`; return its WHNF.
        evalSubst fuel SubstEval.unfBound e
    | .app f a => do
        let vF ← synthCore fuel Γ f
        let _vA ← synthCore fuel Γ a   -- validates `a` recursively
        let aV ← evalSubst fuel SubstEval.unfBound a
        let fV ← evalSubst fuel SubstEval.unfBound f
        -- Expose a Π for the function.
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
            let okArg ← do
              match (← subCheckOpen fuel Γ aV dom) with
              | true => .ok true
              | false =>
                  match (← neutralType fuel Γ aV) with
                  | some aTy => subCheckOpen fuel Γ aTy dom
                  | none => .ok false
            if !okArg then
              .error s!"synth: arg ⊄ dom at .app"
            else
              -- Codomain at the argument: β over the exposed Π.
              evalSubst fuel SubstEval.unfBound (.app piExpr aV)
        | _ =>
            .error s!"synth: internal: non-Π piExpr after exposure"
  termination_by fuel
  decreasing_by all_goals first | (simp_wf; omega) | omega | simp_wf

/-! ## Public surface -/

/-- Produce a `WTValue` for `e`. Validates well-typedness via a
structural walk that delegates each typing question to the
complete structural engine `SubstEval.subCheckOpen`. -/
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  if !e.closedAt 0 then
    .error s!"synth: input contains unbound bvars (not closed)"
  else
    let v ← synthCore fuel [] e
    pure ⟨v⟩

/-- Structural subtype check on already-typed values. -/
def subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool :=
  SubstEval.subCheck fuel a.whnf b.whnf

/-- Convenience: run `synth` on both inputs, then `subCheck`. -/
def subCheckE (fuel : Nat) (e τ : Expr) : Outcome Bool := do
  let a ← synth e fuel
  let b ← synth τ fuel
  subCheck a b fuel

end Och
