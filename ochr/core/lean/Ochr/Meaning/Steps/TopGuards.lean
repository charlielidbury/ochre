import Ochr.Meaning.Steps.ParGuards
import Ochr.Meaning.Steps.RecR
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# `Pre` at a check's start and throughout, under `GlobalsOk`'s three new clauses (lead43, 2026-11-28; docs/31 D253)

The orchestrator's condition (a) on the ruling that `GlobalsOk` carries `fixEq`, `accepted`, `retKind`: say how each
clause reads the function under check and a global whose check is in progress, so that `Pre` is TRUE at the start of a
recursive definition's body and throughout it.

**How the clauses read the definition under check.** Each of `FixEqG`, `AcceptedMeanG`, `RetKindG` is asked of every
global of the state with a `fix` code EXCEPT `K.cur`'s name. The top's context of a function's check names it as
`K.cur` (at its stage bound; a non-recursive one too), so of it `GlobalsOk` asks only `memBelow`, as before. No other
global is in progress: the checker checks one item at a time, `checkDef` appends a function's entry to Σ before its
body's check (so that recursive calls find it) and a constant's after its body's check, and nothing else writes Σ
(`Machine.lean` never assigns `globals`; a nested `fix`'s check adds no global, D136). So at the start of a function's
body and at every state of its check the globals are the earlier items' plus the function's own entry, and the three
clauses are asked of the earlier items only: what the top supplies from their knots. A constant is not in Σ during its
check, and after it has no `fix` code, so no clause ever asks anything of a constant.

**Guarded here** (the checker's side, on the real checker): a recursive `R`, then a recursive `RR` calling the earlier
`R`, then a constant `C` calling `R`. Each item ends with Σ the earlier entries UNCHANGED (the same codes, so the clauses
about them read the same) plus its own entry, the [Rec] stack empty, every code value-free (`GlobalsOk.codeValFree`).
-/

namespace Ochr.Meaning.Steps.Form.TopGuards

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt)
open Ochr.Meaning.Steps.Form.ColumnR (defR fixR)

/-- `RR (n : Nat) : Nat by n := match n { Z => R(Z), S m => RR(m) }`: recursive, calling the earlier recursive `R`. -/
def bodyRR : Term := .matchNat (.var 0) (.call (.const "R") [.zero] false) (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false)
def fixRR : Term := .fix ⟨"RR"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyRR
def defRR : Def := { name := "RR", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, dec := some 0, body := bodyRR }
/-- `C : Nat := R(S(Z))`: a constant calling `R`. -/
def defC : Def := { name := "C", hs := [], doms := [], cod := .nat, body := .call (.const "R") [.succ .zero] false }

/-- Σ after `R`. -/
def st1 : MState := outSt (checkItem (.defn defR)) {} 100000
/-- Σ after `R`, `RR`. -/
def st2 : MState := outSt (checkItem (.defn defRR)) { globals := st1.globals, inds := st1.inds } 100000
/-- Σ after `R`, `RR`, `C`. -/
def st3 : MState := outSt (checkItem (.defn defC)) { globals := st2.globals, inds := st2.inds } 100000

def codes (st : MState) : List (String × Option Term) := st.globals.map fun g => (g.name, g.fn?)

-- each item is accepted from the Σ of the earlier ones
#guard isOk (checkItem (.defn defR)) {} 100000
#guard isOk (checkItem (.defn defRR)) { globals := st1.globals, inds := st1.inds } 100000
#guard isOk (checkItem (.defn defC)) { globals := st2.globals, inds := st2.inds } 100000
-- Σ grows by the item's own entry only, the earlier entries unchanged (same codes); functions have a `fix` code,
-- the constant none
#guard codes st1 == [("R", some fixR)]
#guard codes st2 == [("R", some fixR), ("RR", some fixRR)]
#guard codes st3 == [("R", some fixR), ("RR", some fixRR), ("C", none)]
#guard codes (st2.globals.take 1 |>.foldl (fun (a : MState) g => { a with globals := a.globals ++ [g] }) {}) == codes st1
-- no [Rec] entry survives an item
#guard st1.recStack.isEmpty && st2.recStack.isEmpty && st3.recStack.isEmpty
-- every code is value-free (`GlobalsOk.codeValFree`)
#guard Term.valFree fixR && Term.valFree fixRR

end Ochr.Meaning.Steps.Form.TopGuards
