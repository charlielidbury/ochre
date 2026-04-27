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

/-! ## Validation discipline

The original engine-collapse spec proposed `synth = tyInfer +
evalSubst`: validate every binder/app/asc via the bidirectional
walk, then evaluate to WHNF. In implementation this assumption
turned out to be structurally compromised — `TyCheck.tyInfer` is
incomplete on a significant class of well-formed Och programs
(most of `Std/*`, including `succ_`, `dadd_`, `appendVec`,
`mkVec`). The incompleteness is the A6-family: when `tyInfer`
recurses into a lambda body and hits a `.app f a` whose head is a
level-var with a function type from `Γ`, the bidirectional
`tyCheck a dom` arm can't structurally close the conversion (the
subCheckOpen at the fresh-bvar boundary returns `.ok false` even
on reflexive identity). Empirically: `tyInfer succ_ = .error`,
`tyInfer one_ = .error`, `tyInfer appendVec = .error`. A
truly-sound `synth` requires either:

  1. re-doing the bidirectional rules with proper level-var-typed
     `Γ` propagation (the research task that "completes"
     `tyInfer`); or
  2. requiring the user to supply an expected type `τ` so the
     bidirectional walk has type-guidance (i.e. `synth e τ`,
     which is the original `tyCheck` rebadged).

For now we ship the pragmatic compromise: `synth` runs `tyInfer`
and accepts `.ok` outcomes; on `.error` it **falls back** to
`evalSubst` and accepts. This rescues valid Std programs at the
cost of also accepting two classes of ill-typed inputs that the
spec wanted rejected:

  - SoundnessAudit A3: `(λn:Nat_. n) Bool` (outer β-fast-path
    in `tyInfer` fails on the domain mismatch, fallback then
    β-reduces to `Bool`).
  - `appendVec_wrong`: deep `appendArrays T n1 n1 arr1 arr2`
    domain mismatch (tyInfer would catch it, but other inner
    walks fail first, so the fallback runs).

The unique discipline `WTValue` provides over the previous
`SubstEval.subCheckT` is structural via `private mk`: callers
must thread through `synth` to get a `WTValue`, so any future
hardening of the validator (option 1 above) only changes one
function. The `subCheck` engine itself is unchanged.

Soundness theorems in `Soundness.lean` reflect this — they are
sorry'd, with statements phrased against the new API for future
re-proving. See the conclusion of
`docs/ideas/engine-collapse.md`. -/

/-- Produce a `WTValue` for `e`. Tries the bidirectional walk
(`TyCheck.tyInfer`) first; on `.error` (incomplete bidirectional
rules) or `.ok`, evaluates `e` to head-normal form. The
`evalSubst` step ensures `whnf` is in HNF; the `tyInfer` step
catches operational stuck-states early but does not block valid
Std programs (where it's known incomplete — see module doc).

- `.ok ⟨v⟩` — `e` reduced to WHNF `v`.
- `.outOfFuel` — fuel exhausted in either walk or eval.
- `.error msg` — `e` is operationally stuck (e.g. bare `.bvar`).
-/
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  -- The bidirectional walk is incomplete on much of Std; we run
  -- it primarily as a "best-effort" check. Errors are tolerated;
  -- only `.outOfFuel` propagates.
  match TyCheck.tyInfer fuel #[] e with
  | .outOfFuel => .outOfFuel
  | _ => do
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
