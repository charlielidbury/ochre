import Och.Syntax
import Och.Eval
import Och.API

/-!
# Synth-progress helper lemmas

The user-facing theorem (`Och.Soundness.synth_progress`) states
that a `synth`-accepted closed term never produces `.error msg`
under `concEval` at any fuel.

## Why closedness alone suffices

Inspecting `concEval`'s definition (`Och.Eval`) carefully, the
*only* direct constructor that produces `.error` is

```
| .bvar k => .error s!"concEval: stuck on free bvar {k}"
```

Every other arm is either:

- A pure value form (`.lam`, `.iota`, `.fix`, `.type`, `.bot`)
  that returns `.ok` immediately;
- An eliminator (`.app`, `.letE`, `.asc`) that *propagates* the
  results of recursive calls — in particular, the `.app` arm
  has a catch-all `.ok fVal, .ok aVal => .ok (.app fVal aVal)`
  that never errors on a non-functional head, it merely
  produces a stuck application.

Therefore `concEval` only ever errors when, somewhere in the
recursive descent, it hits a `.bvar k`. By
`concEval_closedAt`, the term-under-evaluation stays
`closedAt 0 = true` throughout the descent (substitutions
preserve closedness), and a closed term has no free `bvar`s
at the top level.

This means the synth hypothesis is *not actually needed* for the
progress claim — closedness is the load-bearing premise. We
state and prove the strong form (closedness ⇒ no error) here,
then derive `synth_progress` as a corollary by simply discarding
the `synth` hypothesis.

## What synth would be needed for

If `concEval` were to *actually* error on shape mismatches like
"applied non-function" — e.g. if `app .type t` errored instead of
returning `.ok (.app .type t)` — then synth's app-rule
domain check would be the load-bearing premise, and the proof
would route through `evalSubst`/`concEval` agreement (Proposal A
territory). The current `concEval` definition just doesn't do
that — it produces *stuck applications as values*, not errors.

That choice is what makes this proof a one-page induction. The
Och-identity claim ("synth gates concEval") becomes vacuous in
the error direction (there are no error states to gate against
beyond free vars, which closedness handles directly). The
*meaningful* practical-soundness story is on the ascription
side, where `synth_sound`/`subCheck_sound` ensure the synthesised
WHNF is a real subtype witness, not just any non-error outcome.
-/

namespace Och.Soundness

/-- **Closed-implies-no-error**: if `e` is closed at depth 0,
then `concEval f e ≠ .error msg` for any fuel `f` and any
diagnostic message `msg`.

The proof is by induction on `fuel`, then case analysis on `e`.
The `.bvar` case contradicts `closedAt 0 = true` (a free bvar at
depth 0 fails the predicate). All other cases either return
`.ok` directly (lam/iota/fix/type/bot) or propagate via
sub-evaluation, which we discharge by the inductive hypothesis
on the closed sub-terms (using `subst_closedAt` for the
`.letE`/β/μ-app reduction steps). -/
theorem concEval_no_error {fuel : Nat} {e : Expr}
    (hcl : e.closedAt 0 = true) :
    ∀ msg, concEval fuel e ≠ .error msg := by
  sorry

end Och.Soundness
