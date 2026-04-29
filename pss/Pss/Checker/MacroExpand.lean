import Pss.Checker.Term
import Pss.Checker.PathSelector

/-! # `Pss.Checker.MacroExpand` — Term-definition lookup

Verbatim port of `pss/checker-artifact/src/macroexpand.el`.

The Lisp version uses a global mutable alist `*term-definitions*` that maps
unquoted symbols to their definitions.  Here we represent it functionally as
a `Defs` (alist), threaded as a parameter.
-/

namespace Pss.Checker
namespace Term

/-- A definition map: pairs of `(name, expansion)`, in the order they were
    defined.  Earlier entries shadow later ones. -/
abbrev Defs := List (String × Term)

namespace Defs

/-- Look up a symbol's definition. -/
def lookup (defs : Defs) (name : String) : Option Term :=
  match defs with
  | [] => none
  | (n, t) :: rest => if n == name then some t else lookup rest name

/-- Reverse-lookup: find a name whose definition is structurally equal to
    `term`. Used by `macroCollapseAtPath`.  Returns the **first** matching
    name (order matters: earlier definitions take priority, matching the
    behaviour of `dolist` over the alist in `macroexpand.el`). -/
def reverseLookup (defs : Defs) (term : Term) : Option String :=
  defs.foldl (fun acc (name, def_) =>
    match acc with
    | some _ => acc
    | none => if (def_ == term : Bool) then some name else none) none

/-- Add a new definition, removing any prior entry for that name. -/
def define (defs : Defs) (name : String) (def_ : Term) : Defs :=
  (name, def_) :: defs.filter (fun (n, _) => n != name)

end Defs

/-- Recursively expand a term that **starts with** a macro reference, until it
    no longer does.  Mirrors `macro-expand-term`.

    To prevent loops on cyclic definitions we track visited names. -/
partial def macroExpandTerm (defs : Defs) : Term → Term :=
  fun t => go [] t
where
  go (visited : List String) : Term → Term
    | .macroRef name =>
      if visited.contains name then .macroRef name
      else match Defs.lookup defs name with
        | some def_ => go (name :: visited) def_
        | none => .macroRef name
    | t => t  -- only expand at the head

/-- Expand the macro at `path` to its definition.  Mirrors
    `macro-expand-at-path`.  Returns `none` if the term at the path is not a
    macro reference, or its definition is missing. -/
def macroExpandAtPath (defs : Defs) (super : Term) (path : Path) : Option Term :=
  match getAt super path with
  | some (.macroRef name) =>
    match Defs.lookup defs name with
    | some def_ => replaceAt super path def_
    | none => none
  | _ => none

/-- Collapse the subterm at `path` to a macro reference if it matches a known
    definition.  Mirrors `macro-collapse-at-path`.  Returns the original
    `super` unchanged if no match. -/
def macroCollapseAtPath (defs : Defs) (super : Term) (path : Path) : Option Term :=
  match getAt super path with
  | some term =>
    match Defs.reverseLookup defs term with
    | some name => replaceAt super path (.macroRef name)
    | none => some super  -- no change
  | none => none

end Term
end Pss.Checker
