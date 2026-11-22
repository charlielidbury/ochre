import Ochr.Meaning.Steps.RecGuards

/-!
# Guards for the master induction's findings (lead22, 2026-11-22; docs/31 D150)

Every `#guard` runs the checker.

**`clone` of a term that is not a place.** The surface produces `clone` only of a place (`Surface.lean`:
"clone takes a place"), but the core checker accepts `clone(u)` for every `u`: it runs `u` in copying
mode (`withCopying`), where every read of a place leaves it in place. The reference's `clone` clause
reads a place operand in place too, but runs any other operand by its plain run (`runT false hint u`),
whose read of a number variable MOVES it (the table's copy decision of a `let`-bound number is `.other`'s,
never a copy). So for `let x = S(Z); let y = clone(S(x)); x` the checker accepts and the reference's
strict run fails at the last read (`x` moved): the general `prim` step is false for `clone` of a
non-place unless the core checker rejects it or the reference copies inside it.
-/

namespace Ochr.Meaning.Steps.Form.MasterGuards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

/-- `let x = S(Z); let y = clone(S(x)); x` in the core (de Bruijn: `x` is `#0`, then `#1`). -/
def bodyCL : Term :=
  .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.succ (.place (.var 0))]) (.place (.var 1)))

def defCL : Def := { name := "CL", hs := [], doms := [], cod := .nat, dec := none, body := bodyCL }

-- the core checker accepts it: `S(x)` under `clone` copies `x`
#guard isOk (checkDef defCL) {} 100000

/-- The same without `clone`. -/
def bodyNC : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.succ (.place (.var 0))) (.place (.var 1)))

/-- `clone` of the place `x` itself. -/
def bodyCP : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.place (.var 0)]) (.place (.var 1)))

-- without `clone` the read of `x` in `S(x)` moves it, and the last read is rejected
#guard !isOk (checkDef { defCL with body := bodyNC }) {} 100000

-- `clone(x)` of the place itself is accepted (the case the reference reads in place)
#guard isOk (checkDef { defCL with body := bodyCP }) {} 100000

end Ochr.Meaning.Steps.Form.MasterGuards
