import Pss.Checker.Term
import Pss.Checker.PathSelector

/-! # `Pss.Checker.Subtyping` — Promotion and subtype primitives

Verbatim port of `pss/checker-artifact/src/subtype.el`.

The key operation is `promoteAtPath`: it walks up from the path to find the
nearest enclosing `(FUN x type body)` whose binder name matches the variable
under consideration, and replaces the variable with the binder's `type`.  If
no such binder exists, the variable becomes `top`.  Anything else (a
function, an application, etc.) is also promoted to `top`.

Forbidden: promoting at a path that points at a `FUN` keyword, the var-name
slot, or the type slot of an enclosing `FUN`.
-/

namespace Pss.Checker
namespace Term

/-- `findBindingTypeInSexp x super path` — search upward from `path` within
    `super` for the innermost `(FUN x type body)` binding `x`, and return its
    `type`.  Mirrors `find-binding-type-in-sexp` in `subtype.el`. -/
def findBindingTypeInSexp (x : String) (super : Term) (path : Path) : Option Term :=
  -- Walk upward from `path.dropLast` to `[]` looking for a FUN binding x.
  -- We try each proper-prefix path in order, longest first.
  let rec go : List Path → Option Term
    | [] =>
      -- Finally check the root.
      match super with
      | .fun_ y type _ => if x == y then some type else none
      | _ => none
    | p :: rest =>
      match getAt super p with
      | some (.fun_ y type _) => if x == y then some type else go rest
      | _ => go rest
  -- properPrefixesDescending of [a, b, c] = [[a, b], [a], []]
  -- We must also try the path that is `[]` (the root), which is included.
  go (Term.properPrefixesDescending path)

/-- `promoteAtPath super path` — promote the subterm at `path`.

    Rules (from `subtype.el`):
    1. `'x` (variable) → its binding's type, or `top` if free.
    2. Any other term (FUN, app, etc.) → `top`.
    3. `top` itself → error (cannot promote top).
    4. Forbidden parents: cannot promote at a path that points at the `FUN`
       keyword, var binding, or type slot.

    Returns `none` on error/invalid path; `some new_super` otherwise. -/
def promoteAtPath (super : Term) (path : Path) : Option Term :=
  -- Pre-check: forbid promoting at index 0/1/2 of an enclosing FUN.
  let parentForbidden : Bool :=
    match parentOf super path with
    | some (.fun_ _ _ _, idx) => idx == 0 || idx == 1 || idx == 2
    | _ => false
  if parentForbidden then none
  else
    match getAt super path with
    | none => none
    | some term =>
      match term with
      | .top => none  -- cannot promote top
      | .var x =>
        let replacement := (findBindingTypeInSexp x super path).getD .top
        replaceAt super path replacement
      | _ => replaceAt super path .top

end Term
end Pss.Checker
