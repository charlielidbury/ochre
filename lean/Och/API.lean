import Och.Syntax
import Och.Outcome
import Och.EvalSubst
import Och.TyCheck

/-!
# Och public typing/subtyping API

The single user-facing surface for Och's type-checking and
subtype-checking pipeline. Replaces the layered
`TyCheck.typeCheck` / `SubstEval.subCheckT` / `SubstEval.subCheck`
public surface that grew during the engine-collapse refactor
phases A–F (`docs/ideas/engine-collapse.md`).

## Surface

```
structure Och.WTValue where
  private mk ::
  whnf : Expr      -- well-typed value (in WHNF) by construction

def Och.synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue
def Och.subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool
```

The `private mk` constructor is the API enforcement: a `WTValue`
can only be obtained via `synth`, which validates `e` end-to-end
(walks every binder/app/asc, domain-checks every application).
`subCheck` then runs the structural Expr-level engine on the
already-validated WHNFs.

## Usage patterns

| Question | Idiom |
|---|---|
| Is `e` well-formed? | `(Och.synth e).isOk` |
| Is `A` a subtype of `B`? | `do let a ← Och.synth A; let b ← Och.synth B; Och.subCheck a b` |
| Reject ill-typed app/binder | caught inside `Och.synth`'s walk |

## Why WTValue

Pre-refactor, the public surface had two pathways:

  - `TyCheck.typeCheck e τ` (sound: rejects ill-typed inputs)
  - `SubstEval.subCheck a b` (structural: only meaningful on
    *already-typed* inputs; β substitutes unconditionally and
    can structurally accept ill-typed terms whose normal forms
    happen to match — see SoundnessAudit A3).

`SubstEval.subCheckT` was an OR-wrapper that called `typeCheck`
first and fell back to `subCheck`. The fallback rescued cases
the syntactic walk couldn't handle (e.g. `let`-pinned constants
where conversion is the right tool), but it also rescued
*genuinely ill-typed* terms whose WHNFs happened to match the
target — a soundness bug, not a feature.

`WTValue` enforces the discipline that `subCheck` only ever
runs on validated inputs. The `private mk` is the only thing
preventing direct construction; users go through `synth`, which
runs the bidirectional walk.

## Soundness theorems

See `Och/Soundness.lean` for the (sorry'd) statements:

  - `synth_sound`: `(synth e).isOk → ∃ τ, Subtype' [] [] e τ`
  - `subCheck_sound`: `subCheck a b = .ok true → Subtype' [] [] a.whnf b.whnf`

Both are sorry-preserved scaffolds for future re-proving on
the substitution substrate.
-/

namespace Och

/-- A well-typed value: `whnf` is an `Expr` in head-normal form
that has been validated by the bidirectional walk in `synth`.
The `mk` constructor is `private`; the only public way to obtain
a `WTValue` is via `synth`. -/
structure WTValue where
  private mk ::
  /-- The validated expression in head-normal form. In Och, the
  natural type of a value is the value itself (per `Subtype'.refl`),
  so `whnf` doubles as both the value and a type witness. -/
  whnf : Expr
  deriving Repr

/-- Synthesise a type for `e`. Validates `e` end-to-end via the
bidirectional walk (every binder is opened, every application's
domain is checked, every ascription is verified), then evaluates
to head-normal form.

- `.ok ⟨v⟩` — `e` is well-typed; `v` is its WHNF.
- `.outOfFuel` — fuel exhausted; recoverable by re-running with
  more fuel.
- `.error msg` — `e` is ill-typed; `msg` carries diagnostic
  information.

This is the **sound** entry point: it rejects ill-typed inputs.
A bare `evalSubst`-based fallback would *not* be sound, because
β-reduction substitutes unconditionally (SoundnessAudit A3). -/
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  -- Validate via the bidirectional walk. `tyInfer` returns
  -- `.error` on genuine type errors (domain mismatches, unbound
  -- bvars in closed-form input) and walks every subterm. We
  -- discard the inferred type itself — the WHNF is the witness.
  let _ ← TyCheck.tyInfer fuel #[] e
  let v ← SubstEval.evalSubst fuel SubstEval.unfBound e
  pure ⟨v⟩

/-- Structural subtype check on already-typed values. Internally
calls the substitution-based structural engine on the validated
WHNFs.

- `.ok true` — `a.whnf ⊑ b.whnf` structurally.
- `.ok false` — not a subtype.
- `.outOfFuel` / `.error` — propagated from the engine.

Because `a` and `b` are `WTValue`s, both have already passed
`synth`'s validation walk. The structural compare is therefore
running on well-typed inputs by construction — no soundness
hazard from the β-substitutes-unconditionally issue. -/
def subCheck (a b : WTValue) (fuel : Nat := 5000) : Outcome Bool :=
  SubstEval.subCheck fuel a.whnf b.whnf

end Och
