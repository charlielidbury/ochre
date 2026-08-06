import Lean
import Dllbc.Uni

/-!
# `pure{ … }` — named-binder surface syntax for the pure fragment (§15)

The M11 wall was mis-indexed de Bruijn failing silently across ~15 binder
contexts. The fix is not a unifier or case trees — it is *names and explicit
structure*, elaborated to the existing de Bruijn kernel `Term` by the macro
layer, in a resolve-or-error discipline. This is authoring sugar, nothing more:
every binder is named, every motive is written once and explicitly, and a wrong
motive fails at the use site with the existing conversion diagnostics.

**The whole file is now three lines of macro**, because `pure{ }` is the UNIFIED
grammar (`ublk`, Uni.lean) entered in ⇝ mode: `elabUBlk true`, against `prog{ }`'s
`elabUBlk false`. The two fragments' surfaces differ by exactly one boolean,
which is this calculus's "one grammar, four arrows" showing up at elaboration
time. What used to live here — a parallel `pterm` category with its own `elabP`,
`elabElim` and `elabGenElim` — was superseded when the unified grammar absorbed
them and was carried dead afterwards; it is gone (M28 ε).

Name resolution for a bare identifier `x` (`DeclMacro.resolveName`):
  * a **bound** name → its de Bruijn `pvar` (index = binders since it was bound);
  * an earlier telescope parameter → its absolute runtime `var`;
  * a known **constructor** (`Z`, `S`, `Cons`, `Refl`, `unit`, …) → `ctorApp`;
  * a kernel **constant** (`Nat`, `List`, `natRec`, `j`, …) → `const`;
  * a reified-function alias (`Le`, `len`, `add`, …) → its `…FnT` Term constant;
  * anything else → the **Lean identifier** of that name, which must denote a
    `Dllbc.Term` in scope (a library definition like `swapL`); an unbound name is
    a Lean elaboration error, never a silent fallback.

`%e` splices a Lean-level `Term` expression `e` directly (an escape hatch), and
the recursor sugar `elim … return …` / `elim … generalizing …` (§15b, §18) is
part of the unified grammar.
-/

open Lean

namespace Dllbc

syntax "pure{" ublk "}" : term

macro_rules
  | `(pure{ $b:ublk }) => do let (t, _) ← Dllbc.DeclMacro.elabUBlk true [] [] 0 b; pure t

end Dllbc
