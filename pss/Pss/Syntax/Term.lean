import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

/-! # `Pss.Syntax.Term` — raw locally-nameless syntax of Och/PSS

A single syntactic category as in Hutchins 2010 / Pasquale & García-Pérez 2024:

```
t, u ::= x | Top | (λ x ≤ t. u) | (t u)
```

We use the **locally-nameless** representation: bound variables are de Bruijn
indices (`bvar`), free variables are strings (`fvar`). The bound variable in
the body of `abs` is `bvar 0`. The `bound` field of `abs` is the type/upper
bound annotation `t` in `λ x ≤ t. u`.

See `PLAN.md` §2 for the design rationale.
-/

namespace Pss

inductive Term where
  | bvar : Nat → Term
  | fvar : String → Term
  | top  : Term
  | abs  : (bound : Term) → (body : Term) → Term
  | app  : Term → Term → Term
  deriving DecidableEq, Repr

end Pss
