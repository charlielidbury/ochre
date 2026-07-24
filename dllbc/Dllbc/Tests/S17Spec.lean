import Dllbc.Boundary
import Dllbc.Macro

/-!
# §17 test suite — declared backward specs (spec group-ends)

The sound reincarnation of the `constrained` wire removed in M8: unsound then
because INFERRED from a signature (`through` and `advance` share one), sound now
because DECLARED on the function and CHECKED against its body. A borrow-returning
function may carry `Decl.back` — a pure function from the issued borrows'
surrendered values to the captured borrow's release value. Two consequences:

* **Callee check**: at return, the captured borrow's payload with the issued
  markers replaced by fresh hole variables — the suspension tree with holes IS
  the backward function the body implements — must convert with the declared
  spec applied to those holes. A spec that lies about the body is rejected.
* **Caller side**: on group end, each captured loan releases the COMPUTED value
  (the spec applied to the surrendered values) instead of a fresh existential.
  Precision recovered soundly — the M8 arc completed.

A spec-less call behaves exactly as before (opaque, a fresh existential); nothing
regresses (see the M9 `through`/`choose` in S7Group, still opaque).
-/

open Dllbc

namespace Dllbc.Tests.S17Spec

def listNatT : Term := .app (.const "List") (.const "Nat")

/-! ## `through` with a declared identity spec — the M8 arc closed -/

-- `through (b) = b`, `back (r) = r`: the release IS the surrendered value.
def throughOk : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b },
    back := some (.lam listNatT (.pvar 0)) }
example : checkFnOk throughOk = true := by native_decide

-- The caller now recovers the WRITTEN value, not a fresh existential: after
-- `*r := Cons(9, Nil)` and demanding the owner, `y = Cons(9, Nil)`. Contrast the
-- spec-less `through` in S7Group, whose `y` is a fresh σ (§6.2 precision loss).
def caller : Decl :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Nil); let b = &mut x;
      let r = through(b);
      *r := Cons(9, Nil);
      let y = x;
      () } }
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match runFn [throughOk, caller] caller with
  | [.ok env] => env.lookup "y" == some vlist9
  | _ => false) = true := by native_decide

/-! ## A lying spec is rejected -/

-- `through (b) = b` but `back (r) = Cons(1, Nil)` — claims a constant release the
-- body does not implement. The callee check converts the body's tree (`#0`, the
-- hole) against the spec's `Cons(1, Nil)` and fails.
def throughLie : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b },
    back := some (.lam listNatT (.ctorApp "Cons" [.ctorApp "S" [.ctorApp "Z" []], .ctorApp "Nil" []])) }
example : checkFnErr throughLie "does not match the body" = true := by native_decide

/-! ## Spec-less stays opaque (no regression) -/

-- Same body, no `back`: the caller's recovery is a fresh existential (a `sym`),
-- exactly as in M9 — the spec-carrying end is opt-in.
def throughOpaque : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b } }
example : (match runFn [throughOpaque, { caller with name := "c2" }] { caller with name := "c2" } with
  | [.ok env] => match env.lookup "y" with | some (.sym _) => true | _ => false
  | _ => false) = true := by native_decide

end Dllbc.Tests.S17Spec
