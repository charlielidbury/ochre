import Och.Syntax
import Och.Eval
import Och.Subtyping
import Och.Soundness.SubtypeSteps

/-!
# B3: `concEval` preservation

`concEval` is a CBV evaluator. It β-reduces and unfolds ι/fix/let/asc.
Each individual step is captured by the head-step preservation lemmas
in `Soundness/SubtypeSteps.lean` (B1+B2). What B3 needs in addition is
a way to relate the result of recursively evaluating sub-expressions
back to the source term.

## Strengthening to bidirectional equivalence

A direct attempt to prove `Subtype' [] [] e τ → Subtype' [] [] e' τ`
hits a wall in the `app` case: after evaluating both `f` and `a` to
`fv`/`av`, applying `app_cong` to swap them in/out of the spine
requires *both directions* of `f ≡ fv` (and `a ≡ av`), whereas
single-direction preservation only gives one.

The fix is to strengthen the induction to *bidirectional equivalence*:

```
concEval fuel e = .ok e' → Subtype' [] [] e' e ∧ Subtype' [] [] e e'
```

With both directions in hand, every sub-evaluation can be plugged
into `app_cong` (and `letE_cong`) freely. The single-direction
preservation falls out by `Subtype'.trans` with the user's hypothesis.

The closedness side-condition is needed to (a) rule out free `bvar`
(stuck in `concEval`), and (b) thread `concEval_closedAt` through the
recursive call on the β-redex body.
-/

namespace Och.Soundness

/-- The two-direction subtype equivalence between an expression and
the result of `concEval`. Strictly stronger than B3's
single-direction preservation; closing this also closes B3.

The "bidirectional" form is essential because `app_cong` and
`letE_cong` are not contravariant in their right-hand subterm: to
swap `f`/`a` for `fv`/`av` inside an application or let-binding
we need both `x ⊑ y` and `y ⊑ x` for each pair. -/
def concEval_equiv {fuel : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' e × Subtype' [] [] e e' := by
  sorry

/-- B3 — `concEval` preservation. Stated against the substrate-agnostic
declarative `Subtype'`. Falls out of `concEval_equiv` by `trans`. The
public-facing alias is `Och.Soundness.concEval_preservation` in
`lean/Och/Soundness.lean`. -/
def concEval_preservation_aux
    {fuel : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : concEval fuel e = .ok e') :
    Subtype' [] [] e' τ :=
  let ⟨he', _⟩ := concEval_equiv hcl hstep
  he'.trans hty

end Och.Soundness
