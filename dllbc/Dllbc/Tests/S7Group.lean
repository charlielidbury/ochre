import Dllbc.Boundary
import Dllbc.Macro

/-!
# §6.1 test suite — entangled calls and loan groups

Some functions break the wire correspondence: `choose` returns a borrow into
`x` OR `y` depending on a runtime bool, so no per-loan promise can say where a
written value lands. A call mints a **loan group** tying the loans it captured
to the borrows it issued, and the ending discipline is the group's whole
content — every issued borrow ends first, then the group ends atomically,
releasing each captured loan. The ordering *is* the soundness argument: a
captured owner cannot recover while an issued borrow lives.

The headline is the pair: the opaque group **forgets** (choose → distinct
fresh σ's; `z = 7` is not provable, and that is the cost, §6.2), while the
identity wire **remembers** (through → the owner recovers the written value).
M5/M6's wires are now the degenerate `issued = []` group.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S7Group

def natT : Term := .const "Nat"
def boolT : Term := .const "Bool"
def listNatT : Term := .app (.const "List") natT

/-! ## `choose`: the entangled call -/

-- choose (c : Bool, x : &mut Nat, y : &mut Nat) → &mut Nat = match c { … }.
-- The callee checks under the borrow-returning audit: each branch consumes one
-- argument borrow into the result (exempt) and audits the other.
def choose : Decl :=
  { name := "choose", retType := .borrowT natT natT,
    telescope := [("c", boolT), ("x", .borrowT natT natT), ("y", .borrowT natT natT)],
    body := dllbcWith [c, x, y] { match c { True => x, False => y } } }

example : checkFnOk choose = true := by native_decide

-- The §6.1 trace verbatim. After `*r := 7`, demanding `a` (via `let z = a`)
-- forces the cascade: End ℓᵣ first (its 7 surrendered and DISCARDED — the
-- ordering as soundness, r ↦ ⊥ and 7 never reaches a or b), then the group
-- ends ATOMICALLY (b's fresh existential arrives too, though only a was
-- demanded). a and b hold DISTINCT fresh σ's; z holds a's. The imprecision is
-- the point: z = 7 is not provable (§6.2's cost).
def chooseCaller : Decl :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      *r := 7;
      let z = a;
      () } }

example : expectFnEnv [choose, chooseCaller] chooseCaller
  [("a", .bot), ("b", .sym 0), ("pa", .bot), ("pb", .bot), ("r", .bot), ("z", .sym 1)]
  = true := by native_decide

/-! ## The identity wire: constrained precision -/

-- through (b : &mut List Nat) → &mut List Nat = b. One captured, one issued,
-- backward flow the identity — so the group is `constrained` and the captured
-- loan releases the issued borrow's surrendered payload, not a fresh σ.
def through : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b } }

example : checkFnOk through = true := by native_decide

-- The caller writes `Cons(9, Nil)` through r and ends the wire: the owner
-- recovers exactly the WRITTEN value (`Cons 9 Nil`), not a fresh σ. Contrast
-- with `choose` above — the degenerate-wire sentence of §6.1, mechanized.
def throughCaller : Decl :=
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Nil); let b = &mut x;
      let r = through(b);
      *r := Cons(9, Nil);
      let y = x;
      () } }

example : expectFnEnv [through, throughCaller] throughCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", cons (nat 9) nil)] = true := by native_decide

/-! ## Rejections -/

-- The group cannot end because an issued borrow cannot surrender: `*r` was
-- taken, leaving its payload a hole (⊥), and then a captured owner is demanded.
example : checkFnErr
  { name := "caller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
      let r = choose(True, pa, pb);
      let tk = *r;
      let z = a;
      () } }
  "nothing surrendered" [choose] = true := by native_decide

-- A borrow-returning body whose returned payload fails its owed type:
-- `bad (b : &mut Nat) → &mut Bool = b` returns a Nat borrow as a Bool borrow.
example : checkFnErr
  { name := "bad", retType := .borrowT boolT boolT,
    telescope := [("b", .borrowT natT natT)],
    body := dllbcWith [b] { b } }
  "owed type" = true := by native_decide

end Dllbc.Tests.S7Group
