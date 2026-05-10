import Pss.Mpss.DeBruijnWellFormed

/-! # `Pss.Paper.Conjecture8` — paper Conjecture 8 (open).

Mechanizes Pasquale & García-Pérez 2024, Conjecture 8
(*Well-subtyping is context independent*, p. 9:13).

## Paper statement

> Let `Γ` be a logical context and `u, t` be terms such that
> `Γ ⊢ u ≤*_wf t`. Let `Co` be a covariant context such that both
> `Co[u]` and `Co[t]` are well-formed in `Γ`. We conjecture that
> `Γ ⊢ Co[u] ≤*_wf Co[t]`.

The paper acknowledges this as **open**: type safety (Theorems 4 and 5)
holds *under the assumption that Conjecture 8 holds* (paper p. 9:13).
We mirror that — Conjecture 8 is shipped as a Lean `axiom` declaration,
which appears in the `#print axioms` output of any theorem that
depends on it.

## Covariant contexts (paper p. 9:13)

Paper grammar:

```
Co ::= □ | (λx ≤ t.Co) | (Co t)
```

i.e. Co is either the hole, an abstraction whose body is Co (with the
binder annotation `t` outside Co), or an application whose function
position is Co (with the operand `t` outside Co). The application's
operand position is *not* a covariant context (it is contravariant for
the function-bound's purposes).

In de Bruijn the abstraction case binds an extra index, so filling Co's
hole with an outer term `u` requires shifting `u` by 1 when going under
the binder.
-/

namespace Pss
namespace DeBruijn
namespace Paper

/-- Paper's covariant contexts (p. 9:13). The hole is the placeholder;
`abs` puts a fresh binder above the hole; `app` puts the hole into the
function position of an application. -/
inductive CovariantContext : Type where
  | hole : CovariantContext
  | abs : Term → CovariantContext → CovariantContext
  | app : CovariantContext → Term → CovariantContext

/-- Fill the hole of a covariant context with the given term. The de
Bruijn variant shifts the filling term by 1 each time we descend under
an `abs` constructor. -/
def CovariantContext.fill : CovariantContext → Term → Term
  | .hole, u => u
  | .abs t body, u => .abs t (body.fill (Term.shift 0 u))
  | .app f t, u => .app (f.fill u) t

/-- **Conjecture 8** (Pasquale & García-Pérez 2024, p. 9:13).
*Well-subtyping is context independent.*

If `Γ ⊢ u ≤*_wf t`, and `Co` is a covariant context such that both
`Co[u]` and `Co[t]` are well-formed in `Γ`, then `Γ ⊢ Co[u] ≤*_wf Co[t]`.

Open in the paper. Type safety (Theorems 4, 5 via Lemma 7) is conditional
on this. Any Lean theorem that consumes this axiom will surface it in
its `#print axioms` output. -/
axiom Conjecture_8_WellSubtypingContextIndependent
    {Γ : Ctx} {u t : Term}
    (h : WSubMStar Γ u t)
    (Co : CovariantContext)
    (hCu : WfM Γ (Co.fill u))
    (hCt : WfM Γ (Co.fill t)) :
    WSubMStar Γ (Co.fill u) (Co.fill t)

end Paper
end DeBruijn
end Pss
