import Och.Syntax
import Och.Outcome
import Och.EvalSubst

/-!
# Och public typing/subtyping API

The single user-facing surface for Och's type-checking and
subtype-checking pipeline.

## Surface

```
def Och.check (e : Expr) (fuel : Nat := 5000) (Γ : TyEnv := []) : Outcome Unit
def Och.subCheck (a b : Expr) (fuel : Nat := 5000) : Outcome Bool
def Och.checkSubtype (fuel : Nat) (e τ : Expr) : Outcome Bool
```

## Design (check = pure validation walk)

`Och.check e` is a structural walk that validates well-typedness
at every node, returning `Outcome Unit`. Callers that need a WHNF
call `evalSubst` separately. All "is X well-typed at Y?" questions
are delegated to the existing complete structural engine
`SubstEval.subCheckOpen`.

In the pure de Bruijn regime, descending under a binder does NOT
substitute — we recurse on the raw body with the context extended.
`bvar 0` in the body naturally refers to the new innermost binder.
-/

namespace Och

open SubstEval

/-- Type context for `check`: stores the types of free variables.
`Γ[Γ.length - 1 - k]` is the type of `bvar k`. Push to the end
when entering a binder.

Public so soundness lemmas in `Soundness/SynthSound.lean` can
mention `Γ`'s type when stating per-arm helper lemmas. -/
abbrev TyEnv := List Expr

/-- Pure validation walk: checks that `e` is well-typed under `Γ`,
returning `Outcome Unit`. Does NOT return a WHNF witness; callers
that need a WHNF should call `evalSubst` separately.

Top-level callers use the defaults: `Och.check e` checks a closed
term with `fuel = 5000` and `Γ = []`.

**Termination.** Non-`partial`: `fuel` strictly decreases at every
recursive call. -/
def check (e : Expr) (fuel : Nat := 5000) (Γ : TyEnv := []) :
    Outcome Unit :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .type => .ok ()
    | .bot  => .ok ()
    | .bvar k =>
        -- Pure de Bruijn: bvar k is valid if k < Γ.length.
        if k < Γ.length then
          .ok ()
        else
          .error s!"synth: unbound bvar {k} (|Γ|={Γ.length})"
    | .lam dom body => do
        let domV ← evalSubst fuel SubstEval.unfBound dom
        check body fuel (domV :: Γ)
    | .iota ann body => do
        let annV ← evalSubst fuel SubstEval.unfBound ann
        check body fuel (annV :: Γ)
    | .fix body =>
        check body fuel (.fix body :: Γ)
    | .app f a => do
        check f fuel Γ
        check a fuel Γ
        let aV ← evalSubst fuel SubstEval.unfBound a
        let fV ← evalSubst fuel SubstEval.unfBound f
        -- Expose a Π for the function.
        let piExpr ← do
          match whnfPi fuel fV fV with
          | some piLam@(.lam ..) => .ok piLam
          | _ =>
              match (← neutralType fuel Γ fV) with
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
              .ok ()
        | _ =>
            .error s!"synth: internal: non-Π piExpr after exposure"
  termination_by fuel
  decreasing_by all_goals first | (simp_wf; omega) | omega | simp_wf

/-- Structural subtype check on `Expr`s. -/
def subCheck (a b : Expr) (fuel : Nat := 5000) : Outcome Bool :=
  SubstEval.subCheck fuel a b

/-- Convenience: check `e ⊑ τ` structurally. The well-formedness walk
(`check`) is NOT invoked because the domain extraction via
`synthNeutralType` produces unreduced β-redexes inside lambda
bodies that the structural subtype checker cannot always close
(e.g. `succ_(add_ pred m)` inside `add_`'s body). The subtype
check `e ⊑ τ` provides the actual semantic guarantee. -/
def checkSubtype (fuel : Nat) (e τ : Expr) : Outcome Bool :=
  subCheck e τ fuel

end Och
