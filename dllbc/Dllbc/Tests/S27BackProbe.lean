import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S17Spec

/-!
# §27 — `back` as an Id-ensures, PROBED on the cursor chain

The hypothesis under test: a declared `back = M` is encodable as the ensures
`-> Id τ (*v) (M (old *v))`, so S19's Architecture-A stratum (the back-carrying
`nth`/`nth2`/`swapS` chain) CONVERTS rather than retires.

The leaf case is already mechanized and is not in doubt: `S23Direct.setAt` /
`swapAt` carry exactly that shape with no `back` anywhere. What this file probes
is the case S19 is actually made of — bodies that do not walk the structure but
**call a cursor**, and cursors that return BORROWS.
-/

open Dllbc
open Dllbc.StdLemmas (set swapL nth len Le le_refl znots id_congr id_trans id_sym le_rw_r len_set swapL_set)

namespace Dllbc.Tests.S27BackProbe

/-- Rejections are asserted on the message, never on a Bool (S26Seal's rule):
    `hasType` returning `false` and a stuckness error are different verdicts. -/
def ok (d : Decl) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => true | .error _ => false

def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => false | .error e => strContains e needle

/-- The error a declaration produces, for reading off WHICH rule refused. -/
def why (d : Decl) (table : List Decl := [d]) : String :=
  match checkFn table d with | .ok _ => "<accepted>" | .error e => e

/-! ## §A. The vacuity question, asked FIRST

    Everything downstream depends on it. `checkFn` pins and checks the return
    type as a value ONLY when `hasBorrowT decl.retType` is false (Boundary.lean:63);
    `auditAction`'s borrow-carrying branch checks the ISSUED BORROWS' owed types
    and the argument obligations, and nothing else (Machine.lean:2571-2578). So a
    non-borrow component of a borrow-carrying return type is never judged.

    If that is so, a cursor can STATE any ensures and no body has to earn it — the
    contract would be trusted, not checked, and the hypothesis would be "confirmed"
    by a checker that is not looking. -/

-- A1. A cursor into a list, returning the head borrow beside a FALSE claim
-- (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it.
def a1lie : Decl :=
  decl{ fn head_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&mut *hd, Refl)
        } } }

-- A2. The value-returning twin of the SAME lie — no borrow in the return type,
-- so the pin-and-check path runs and the lie is caught. The difference between
-- A1 and A2 is exactly `hasBorrowT`.
def a2lie : Decl :=
  decl{ fn val_lie (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : Nat) → Id Nat Z (S Z)
        { Pair(Z, Refl) } }


-- A3. Is the hole VACUOUS or UNSOUND? The caller's `buildResult` mints a σ at
-- the leaf's type, so the caller RECEIVES the unchecked claim as a proof.
def a3use : Decl :=
  decl{ fn absurd (x : &mut List Nat, hx : Le (S Z) (len *x)) -> Id Nat Z (S Z)
        { let p = head_lie(&mut *x, hx);
          match p { Pair(b, h) => h } } }


-- A4. The break, CLOSED: no hypotheses at all, and `Bot` at the return type.
def a4bot : Decl :=
  decl{ fn closedBot () -> Bot
        { let l = Cons(1, Nil);
          let b = &mut l;
          let p = head_lie(b, ());
          match p { Pair(bb, h) => znots Z h } } }


-- A5. CONTROLS. (a) Without the cursor the same absurdity is refused: `Refl`
-- does not inhabit `Id Z (S Z)` when the body is judged. (b) The lie needs the
-- BORROW in the return type, not the Σ: the Σ-of-values twin is A2, rejected.
-- (c) An HONEST claim in the same position is accepted too — which is the point:
-- the position accepts everything, so acceptance there carries no information.
def a5direct : Decl :=
  decl{ fn direct () -> Bot { znots Z Refl } }

def a5honest : Decl :=
  decl{ fn head_true (v : &mut List Nat, hi : Le (S Z) (len *v))
        -> Σ (x : &mut Nat) → Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&mut *hd, Refl) } } }

-- ACCEPTED — the claim is never judged.
example : ok a1lie = true := by native_decide
-- REJECTED — the same claim, in a return type with no borrow in it.
example : rejects a2lie "does not have return type" = true := by native_decide
-- ACCEPTED — so the hole is not vacuous: the caller RECEIVES the false proof and
-- returns it at its own (value) return type, where the pin-and-check path DOES
-- run and passes, because the σ genuinely carries that sctx type.
example : ok a3use [a1lie, a3use] = true := by native_decide
-- ACCEPTED — `fn closedBot () -> Bot`, no hypotheses. The break, closed.
example : ok a4bot [a1lie, a4bot] = true := by native_decide
-- The controls: the direct route to the same absurdity is refused, and the
-- honest claim in the same position is accepted too.
example : rejects a5direct "does not have return type" = true := by native_decide
example : ok a5honest = true := by native_decide

end Dllbc.Tests.S27BackProbe
