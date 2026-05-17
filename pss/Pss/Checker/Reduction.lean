import Pss.Checker.Term
import Pss.Checker.PathSelector

/-! # `Pss.Checker.Reduction` — β-substitution, Y-unfolding, top-application

Verbatim port of `pss/checker-artifact/src/reduction.el`.

The three reductions:
* `(top body) → top`              — top is absorbing under application.
* `(y f) → (f (y f))`             — fixed-point unfolding.
* `((FUN x t b) arg) → b[arg/x]`  — β-reduction.

All shadowing-aware: `substituteInTerm body x arg` does **not** descend into
the body of an inner `(FUN x' t' b')` when `x' = x`, but **does** still rewrite
inside the type annotation `t'` (the type is in scope of the outer binder).
This matches lines 130-149 of `reduction.el`.
-/

namespace Pss.Checker
namespace Term

/-- Substitute `arg` for free occurrences of variable `x` in `body`,
    respecting shadowing.  Mirrors `substitute-in-term-internal` in
    `reduction.el`. -/
def substituteInTerm (body : Term) (x : String) (arg : Term) : Term :=
  match body with
  | .var y => if x == y then arg else .var y
  | .top => .top
  | .macroRef s => .macroRef s
  | .fun_ y type b =>
    if x == y then
      -- Shadowing: substitute only in the type annotation.
      .fun_ y (substituteInTerm type x arg) b
    else
      .fun_ y (substituteInTerm type x arg) (substituteInTerm b x arg)
  | .app rator rand =>
    .app (substituteInTerm rator x arg) (substituteInTerm rand x arg)
  | .yfix f =>
    .yfix (substituteInTerm f x arg)
  | .or alts =>
    .or (substInList alts x arg)
where
  substInList (alts : List Term) (x : String) (arg : Term) : List Term :=
    match alts with
    | [] => []
    | a :: rest => substituteInTerm a x arg :: substInList rest x arg

/-- Single-step reduction at a path.  Mirrors `beta-substitute-at-path`.
    Returns `none` if the term at the path is not in a reducible form. -/
def betaSubstituteAtPath (super : Term) (path : Path) : Option Term :=
  match getAt super path with
  | none => none
  | some term =>
    match reduceOne term with
    | none => none
    | some result => replaceAt super path result
where
  /-- One-step head reduction (without path traversal). -/
  reduceOne : Term → Option Term
    | .app .top _ => some .top
    | .yfix f => some (.app f (.yfix f))
    | .app (.fun_ x _ body) arg => some (substituteInTerm body x arg)
    | _ => none

/-- Recursively perform every β-reduction in `term`.  Mirrors
    `beta-substitute-all-in-term`.

    The artifact has a special heuristic: if the argument contains an OR
    expression and the function uses its variable multiple times, **don't**
    substitute — instead recurse into both halves. We replicate that
    bookkeeping using the helpers in this file (without macro expansion, since
    that requires a definitions map; the strict reading of the Lisp uses
    macroexpand, but for replay we simply check the syntactic form).
-/
partial def betaSubstituteAllInTerm : Term → Term
  | .app .top _ => .top
  | .app (.fun_ x _ body) arg =>
    if hasOr arg && multipleOccursIn x body then
      -- Cannot duplicate an OR — recurse without substituting.
      .app (.fun_ x .top (betaSubstituteAllInTerm body)) (betaSubstituteAllInTerm arg)
    else
      betaSubstituteAllInTerm (substituteInTerm body x arg)
  | .app rator rand => .app (betaSubstituteAllInTerm rator) (betaSubstituteAllInTerm rand)
  | .fun_ x type body =>
      .fun_ x (betaSubstituteAllInTerm type) (betaSubstituteAllInTerm body)
  | .yfix f => .yfix (betaSubstituteAllInTerm f)
  | .or alts => .or (alts.map betaSubstituteAllInTerm)
  | t => t
where
  hasOr : Term → Bool
    | .or _ => true
    | .app a b => hasOr a || hasOr b
    | .fun_ _ t b => hasOr t || hasOr b
    | .yfix f => hasOr f
    | _ => false
  multipleOccursIn (x : String) : Term → Bool := fun t => countOccurs x t > 1
  countOccurs (x : String) : Term → Nat
    | .var y => if x == y then 1 else 0
    | .app a b => countOccurs x a + countOccurs x b
    | .fun_ y _ b => if x == y then 0 else countOccurs x b  -- shadowing
    | .yfix f => countOccurs x f
    | .or alts => alts.foldl (fun acc t => acc + countOccurs x t) 0
    | _ => 0

/-- Iterate `betaSubstituteAllInTerm` to a fixed point at the given path.
    Mirrors `beta-substitute-all-at-path`. -/
partial def betaSubstituteAllAtPath (super : Term) (path : Path) : Option Term :=
  match getAt super path with
  | none => none
  | some term =>
    let reduced := iterate term
    if (reduced == term : Bool) then some super  -- no change
    else replaceAt super path reduced
where
  iterate (t : Term) : Term :=
    let next := betaSubstituteAllInTerm t
    if (next == t : Bool) then t else iterate next

end Term
end Pss.Checker
