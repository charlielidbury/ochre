import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.API
import Och.Soundness.EvalSubstEquiv

/-!
# `synth_sound` — synthesis-soundness scaffold

The user-facing theorem (`Och.Soundness.synth_sound` in
`Och/Soundness.lean`) states:

```
Och.synth e fuel = .ok v → Subtype' [] [] e v.whnf
```

i.e. if `synth` accepts `e` and produces a WHNF type-witness `v`,
then `e` declaratively subtypes `v.whnf`.

## Why this isn't (yet) a closed proof

Och.API exposes `synth` as a thin wrapper:

```
def synth (e : Expr) (fuel : Nat := 5000) : Outcome WTValue := do
  let v ← synthCore fuel #[] e
  pure ⟨v⟩
```

But `synthCore` is `private partial def` inside `Och/API.lean`.  Two
consequences:

1. **Privacy.**  No file outside `API.lean` can name `synthCore` —
   we can't even *state* a helper lemma about its return value.

2. **Partial-def opacity.**  Even inside `API.lean`, `synthCore`
   is `partial def`, which means no auto-generated `eq_def` /
   `eq_1` / `eq_2` … equation lemmas (Lean 4 only generates these
   for defs whose termination is verified).  Case analysis on
   `synthCore`'s body — splitting on the `match e with | .lam ..
   => …` arms — is therefore impossible at the tactic level.

The composition wall in `SubCheckSubstSoundness.lean` is the
*twin* of this wall: there, `subCheckSubst` was a `partial def`
and the wall lifted only after the engine was rewritten to a
non-partial structural recursion (with a lex `(fuel, phase)`
measure).  The same migration would break this wall, but it's
non-trivial: `synthCore`'s recursion mixes structural descent
through binders with `evalSubst` calls (which themselves consume
fuel), and a uniform structural measure is not obvious.

## What approach 1 (synth ≈ evalSubst) would deliver if accessible

The synth's WHNF coincides with `evalSubst e` for every arm
*except* `.app` with a fix-headed function:

| arm           | synth WHNF                       | evalSubst e            |
|---------------|----------------------------------|------------------------|
| `.bvar`       | `e`                              | `e`                    |
| `.type/.bot`  | `e`                              | `e`                    |
| `.lam/.iota/.fix` | `evalSubst e` (= `e`)        | `e`                    |
| `.asc t _`    | `synthCore t` (recursive)        | `evalSubst t`          |
| `.letE`       | `evalSubst e`                    | `evalSubst e`          |
| `.app f a`    | `evalSubst (.app piExpr aV)`     | (β/unfold-bounded)     |

For the `.app` arm, `whnfPi` may unfold a fix-headed `vF` past
the `unf` budget that `evalSubst` allows directly, so the two
results can differ structurally — but they remain `Subtype'`-
equivalent via `unfold_fix_L/R` and `unfold_iota_L/R`.

So if synthCore's body were inspectable, the proof skeleton
would be:

```
induction e
| .bvar | .type | .bot | .lam | .iota | .fix
    => unfold synthCore at h; refl
| .asc inner τ
    => synthCore (.asc inner τ) = synthCore inner;
       IH on inner gives e ⊑ inner.whnf;
       asc_L composes
| .letE | .app
    => synthCore returns evalSubst (something);
       evalSubst_equiv on closedAt 0 inputs gives Subtype'
```

This file leaves the theorem `sorry`d behind a single named
top-level wall (`synthCore_opacity_WALL`) and delegates from
`Och/Soundness.lean`.

## When this wall lifts

Three independent paths would close this:

1. **De-private `synthCore`** in `API.lean` (or expose a typed
   re-export).  Mechanical; the theorem then closes via the
   `evalSubst_equiv` chain above.

2. **De-partialise `synthCore`** with a structural measure
   (analogous to the `subCheckSubst` migration).  Likely a
   lex `(e.depth, fuel)` measure — harder than the engine
   migration because synth interleaves evaluation steps.

3. **A surface lemma `synth e = .ok v → Subtype' [] [] e v.whnf`**
   bolted directly into `API.lean` (where privacy permits),
   then re-exported through this file.

Each closes the same target via the same `evalSubst_equiv`
backbone; the three differ only in scoping convenience.
-/

namespace Och.Soundness

open SubstEval
open Expr (closedAt)

/-- **WALL**: the synthCore opacity wall.  Inside `API.lean`,
`synthCore` is `private partial def`, so neither its name nor
its equation lemmas are accessible from this module.  See the
module docstring for the three independent paths that lift this
wall; each closes via `evalSubst_equiv`.

This stub is the single `sorry` in the synth-soundness chain;
all per-arm reasoning routes through `evalSubst_equiv` (already
proven, modulo the depth-budget WALL inside that file). -/
private theorem synthCore_opacity_WALL
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf :=
  -- The proof skeleton (under hypothetical access to `synthCore`'s
  -- structural body) is documented in the module preamble.  Each
  -- per-arm sub-goal closes via `evalSubst_equiv` (in
  -- `Soundness/EvalSubstEquiv.lean`) plus a shape-specific
  -- constructor (`Subtype'.refl` / `.asc_L` / `.unfold_fix_L/R` /
  -- `.unfold_iota_L/R`).
  sorry

/-- **synth-soundness**: if `Och.synth e fuel = .ok v`, then `e`
declaratively subtypes its synthesised WHNF `v.whnf`.

Currently delegated through the single named wall
`synthCore_opacity_WALL` above; see the module docstring for the
proof skeleton and the three paths that lift the wall. -/
theorem Och_synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf :=
  synthCore_opacity_WALL h

end Och.Soundness
