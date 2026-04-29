import Pss.Checker.Term
import Pss.Checker.PathSelector

/-! # `Pss.Checker.OrSplit` — Variant splitting

Verbatim port of `pss/checker-artifact/src/or-split.el`.

`splitOrAtPath super path n` substitutes the `n`-th alternative of an
`(OR a₀ a₁ ...)` subterm for the whole `OR`.  `splitOrAtPathAll` returns
the list of all such substitutions (one per alternative), modelling the
case-split that creates multiple proof goals.
-/

namespace Pss.Checker
namespace Term

/-- True if the subterm at `path` is an `(OR ...)` with at least 2 alternatives. -/
def isOrExpressionAtPath (super : Term) (path : Path) : Bool :=
  match getAt super path with
  | some (.or alts) => alts.length ≥ 2
  | _ => false

/-- Replace the OR at `path` with its `n`-th alternative.  Returns `none` if
    the path doesn't point to an OR or `n` is out of bounds. -/
def splitOrAtPath (super : Term) (path : Path) (n : Nat) : Option Term :=
  match getAt super path with
  | some (.or alts) =>
    match alts[n]? with
    | some alt => replaceAt super path alt
    | none => none
  | _ => none

/-- One result per alternative — used when the rewriter creates multiple
    proof obligations (`split-or-at-path-all`). -/
def splitOrAtPathAll (super : Term) (path : Path) : Option (List Term) :=
  match getAt super path with
  | some (.or alts) =>
    let n := alts.length
    let indices := (List.range n)
    let results := indices.filterMap (fun i => splitOrAtPath super path i)
    if results.length == n then some results else none
  | _ => none

end Term
end Pss.Checker
