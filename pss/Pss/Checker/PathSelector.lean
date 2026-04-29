import Pss.Checker.Term

/-! # `Pss.Checker.PathSelector` — Path navigation over terms

Verbatim port of the path operations in `pss/checker-artifact/src/path-management.el`,
lines 100–130 (`get-subexpression-at-path` and `replace-subexpression-at-path`).

A `Path` is a list of zero-based indices.  In the original Lisp code, each term
is a list, so the indices select list positions:

* `(FUN var type body)` — index 0 is the keyword `FUN`, 1 is the var, 2 is the
  type, 3 is the body.
* `(rator rand)` — 0 selects rator, 1 selects rand.
* `(y f)` — 0 is the keyword `y`, 1 is `f`.
* `(OR a₁ a₂ ...)` — 0 is the keyword `OR`, 1 is `a₁`, etc.

We replicate this exactly so paths copied from the artifact's proof scripts
work without translation.  Indices that point at the keyword (`FUN`, `y`, `OR`)
or at the var-binding/type slot of a `FUN` cannot be replaced — those produce
an error, matching the Lisp behaviour (see `subtype.el`'s `promote-at-path`
pre-check).
-/

namespace Pss.Checker
namespace Term

/-- Get the immediate child at index `i`, returning `none` if out of bounds or
    if the index points at a non-replaceable position (e.g. a keyword slot).
    Returns `some` of either:
    * `Sum.inl t` for a real subterm `t` (replaceable),
    * `Sum.inr s` for a "tag" — a string keyword like `FUN`, `y`, `OR`, or a
      variable-binding name.

    For navigation purposes (`getAt`) we treat both as opaque; for
    replacement (`replaceAt`) we forbid descending into a tag. -/
def childAt : Term → Nat → Option (Sum Term String)
  | .top, _ => none
  | .var _, _ => none  -- atoms have no children
  | .macroRef _, _ => none
  | .fun_ x type body, i =>
    match i with
    | 0 => some (Sum.inr "FUN")
    | 1 => some (Sum.inr x)
    | 2 => some (Sum.inl type)
    | 3 => some (Sum.inl body)
    | _ => none
  | .app rator rand, i =>
    match i with
    | 0 => some (Sum.inl rator)
    | 1 => some (Sum.inl rand)
    | _ => none
  | .yfix f, i =>
    match i with
    | 0 => some (Sum.inr "y")
    | 1 => some (Sum.inl f)
    | _ => none
  | .or alts, i =>
    match i with
    | 0 => some (Sum.inr "OR")
    | k + 1 => (alts[k]?).map Sum.inl

/-- Replace the immediate child at index `i` with `replacement`.  Returns
    `none` if `i` is out of bounds or points at a tag/keyword slot.

    Crucially, replacing inside an `or alts` at index `k+1` overwrites the
    `k`-th alternative. -/
def replaceChildAt : Term → Nat → Term → Option Term
  | .top, _, _ => none
  | .var _, _, _ => none
  | .macroRef _, _, _ => none
  | .fun_ x type body, i, repl =>
    match i with
    | 0 => none  -- cannot replace keyword
    | 1 => none  -- cannot replace var name
    | 2 => some (.fun_ x repl body)
    | 3 => some (.fun_ x type repl)
    | _ => none
  | .app rator rand, i, repl =>
    match i with
    | 0 => some (.app repl rand)
    | 1 => some (.app rator repl)
    | _ => none
  | .yfix _, i, repl =>
    match i with
    | 0 => none
    | 1 => some (.yfix repl)
    | _ => none
  | .or alts, i, repl =>
    match i with
    | 0 => none
    | k + 1 =>
      if k < alts.length then
        some (.or (alts.set k repl))
      else
        none

/-- Walk down a path, returning the subterm at the end. -/
def getAt : Term → Path → Option Term
  | t, [] => some t
  | t, i :: rest =>
    match childAt t i with
    | some (Sum.inl child) => getAt child rest
    | _ => none

/-- Replace the subterm at `path` with `replacement`. -/
def replaceAt : Term → Path → Term → Option Term
  | _, [], repl => some repl
  | t, i :: rest, repl =>
    match childAt t i with
    | some (Sum.inl child) =>
      match replaceAt child rest repl with
      | some newChild => replaceChildAt t i newChild
      | none => none
    | _ => none

/-- Get the parent term and the index within the parent that the path lands at.
    Returns `(parentTerm, lastIndex)` where the subterm at `path` is at index
    `lastIndex` of `parentTerm`.  Used by `find-binding-type-in-sexp`. -/
def parentOf (super : Term) (path : Path) : Option (Term × Nat) :=
  match path.reverse with
  | [] => none
  | last :: revPrefix =>
    let parentPath := revPrefix.reverse
    match getAt super parentPath with
    | some parent => some (parent, last)
    | none => none

/-- All proper prefixes of `path` from longest down to empty (in that order),
    used by `find-binding-type-in-sexp` to walk upward.  E.g. for `[1,2,3]`
    yields `[[1,2], [1], []]`. -/
def properPrefixesDescending (path : Path) : List Path :=
  go path.reverse []
where
  go : List Nat → List Path → List Path
    | [], acc => acc.reverse
    | _ :: rest, acc => go rest (rest.reverse :: acc)

end Term
end Pss.Checker
