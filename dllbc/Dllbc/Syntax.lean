/-!
# DLLBC Syntax (concrete runtime, §2)

One inductive `Term` for the whole grammar of the doc (§1.1), but we declare
only the forms the §2 concrete machine needs right now:

  * variable occurrence,
  * `let x = t ; rest`,
  * `t := t' ; rest` (assignment),
  * constructor application (constructor names as `String` for now —
    `inductive` declarations arrive in a later milestone),
  * `&mut t` (mutable borrow),
  * `*t` (dereference),
  * a unit / terminal form for statement sequences.

The λ / application / Π / `Type` / `match` forms of §1.1 join in later
milestones (§3 match, §5 boundaries, §7 inductives).

## Runtime variables carry globally-unique ids

A runtime variable is a `Nat` id (globally unique, minted by the `dllbc{…}`
macro at elaboration time) paired with a display `String`. There is **no**
de Bruijn indexing in the machine layer and **no** shifting anywhere — the
macro resolves names to ids while elaborating, and an unresolved name is an
elaboration-time error (mirroring `Och/Macro.lean`'s discipline that killed
the silent-999 sentinel bug). The environment Ω is then keyed by these ids,
so shadowing is a fresh id, never a name clash.
-/

namespace Dllbc

/-- A runtime variable: a globally-unique `id` plus a display `name`. -/
structure Var where
  id : Nat
  name : String
deriving DecidableEq, BEq, Repr, Inhabited

/-! Core term syntax of DLLBC's concrete fragment (§2 forms plus §3 `match`).

    Constructor names are `String`s (a placeholder until `inductive`
    declarations arrive). Numeric literals are macro-level sugar for
    `S (S (… Z))` and so need no dedicated term form.

    `Term` is mutual with `Branch` for the `match` case. The scrutinee of a
    match is a `Var` (grammar-enforced, §3: "the scrutinee must be a
    variable"); patterns are one constructor deep. -/
mutual
inductive Term where
  /-- Variable occurrence. Under ⇒ this is a *move*. -/
  | var    : Var → Term
  /-- `let x = rhs ; rest` — bind `x` to the ⇒-value of `rhs`, then run `rest`. -/
  | letIn  : Var → Term → Term → Term
  /-- `place := rhs ; rest` — ⇒-read `rhs`, ⇐-write it into `place`, then `rest`.
      `place` is syntactically an arbitrary `Term`; ⇐ is only *defined* on
      place shapes (a variable under zero or more `*` peels). -/
  | assign : Term → Term → Term → Term
  /-- Constructor application `C(a, b, …)`; nullary `C` is `ctorApp C []`. -/
  | ctorApp : String → List Term → Term
  /-- `&mut t` — mint a loan; `&mut *x` is reborrow. -/
  | borrow : Term → Term
  /-- `*t` — the peel. Arrow-generic in the doc; here used under ⇒ (take)
      and ⇐ (write-through / locate). -/
  | deref  : Term → Term
  /-- `match x { … }` — one-constructor-deep pattern match on a variable
      scrutinee (§3). Owned or borrow mode is chosen at runtime by what the
      scrutinee's slot holds. -/
  | matchE : Var → List Branch → Term
  /-- `e ; rest` — expression statement: ⇒-evaluate `e` for effect, discard
      its value, then run `rest`. Sequences a `match` (or any effectful term)
      used in statement position without binding a throwaway slot. -/
  | seq    : Term → Term → Term
  /-- Terminal form, the value a statement sequence returns when it has no
      final expression. -/
  | unit   : Term
/-- A match branch: a constructor name, one-level-deep field binders (display
    names carrying fresh runtime ids), and a body term. -/
inductive Branch where
  | mk : (ctor : String) → (binders : List Var) → (body : Term) → Branch
end

-- Manual instances: `deriving` can't cross the `List Term`/`List Branch`
-- nesting, and nothing in the machine needs term equality (the macro produces
-- terms; tests compare *values*).
instance : Inhabited Term := ⟨.unit⟩
instance : Inhabited Branch := ⟨.mk "" [] .unit⟩

/-- The branch's constructor name. -/
def Branch.ctor : Branch → String | .mk c _ _ => c
/-- The branch's field binders. -/
def Branch.binders : Branch → List Var | .mk _ b _ => b
/-- The branch's body. -/
def Branch.body : Branch → Term | .mk _ _ t => t

end Dllbc
