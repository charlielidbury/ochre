import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Tests.S9Diff

/-!
# §13 test suite — the two-cursor swap (the naturalness gate)

In-place element swap through mutable borrows: the pattern that makes an
imperative quicksort possible, and DLLBC's answer to why Rust needs
`split_at_mut`. Two sequential cursor calls CANNOT hand out two live element
borrows — the first call captures `v` into a group that lives until its result
dies. The calculus's own solution is one function that returns both cursors at
once: `nth2 : … → Pair (&mut Nat) (&mut Nat)`, a **multi-issued group** (one
captured loan, two issued borrows), built by a single nested walk. This is the
first exercise of M7's `endGroup` on a multi-issued group, and of the callee
audit on a borrow-carrying product return.

Three machine additions serve it: the `advance` pattern — returning a reborrow
of a FIELD of an argument borrow — is now audited (the captured owner is exempt,
following the reborrow/group chain to the result); `buildResult` issues one loan
per borrow in the return type (so a `Pair` of borrows is multi-issued); and
`collectResultBorrows` audits each issued borrow's payload on the callee side.

Out-of-bounds is handled with a **default-element parameter** this milestone
(`nth`/`nth2` take spare `&mut Nat`s, returned when the index runs off the list).
It keeps bodies total with no proof machinery, at the cost of threading the
defaults through every call — the naturalness memo weighs this against the
dependent bounds-proof alternative.
-/

open Dllbc

namespace Dllbc.Tests.S13Swap

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
def mutNat : Term := .borrowT natT natT
def pairMut : Term := .sigmaT mutNat mutNat

-- Expected concrete result values (Ω holds `Val`s).
def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val
  | [] => .ctor "Nil" []
  | h :: t => .ctor "Cons" [vnat h, vlist t]

/-! ## `nth` — the single cursor (recursive borrow-return, the `advance` pattern) -/

-- `nth (v : &mut List Nat, i : Nat, d : &mut Nat) → &mut Nat`: Z reborrows the
-- head, S recurses into the tail reborrow, Nil returns the default. A recursive
-- borrow-returning function: wires and groups doing real work.
def nth : Decl :=
  { name := "nth", retType := mutNat,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("d", mutNat)],
    body := dllbcWith [v, i, d] {
      match v {
        Nil => d,
        Cons(hd, tl) => match i { Z => &mut *hd, S(k) => nth(&mut *tl, k, d) }
      } } }
example : checkFnOk nth = true := by native_decide

-- Caller: `let e = nth(bb, 1, dd); *e := 9;` then demand the owner. In CHECKING
-- mode the recovered owner is a fresh opaque existential (§6.2 — the precision
-- loss; a spec milestone recovers it), so `y` is a `sym`, not `[1,9,3]`.
def nthCaller : Decl :=
  { name := "nthCaller", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let dz = 0; let dd = &mut dz;
      let e = nth(bb, 1, dd);
      *e := 9;
      let y = x;
      () } }
example : checkFnOk nthCaller ([nth, nthCaller]) = true := by native_decide

-- CONCRETELY (executing mode runs the actual bodies): the write lands, `y = [1,9,3]`.
def nthCallerBody : Term := dllbcWith [] {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  let dz = 0; let dd = &mut dz;
  let e = nth(bb, 1, dd);
  *e := 9;
  let y = x;
  () }
example :
    (match Dllbc.Tests.S9Diff.runExec [nth] nthCallerBody with
     | .ok env => env.lookup "y" == some (vlist [1,9,3])
     | .error _ => false) = true := by native_decide

/-! ## `nth2` — two cursors at once (the multi-issued group) -/

-- `nth2 (v, i, j, d1, d2) → Pair (&mut Nat) (&mut Nat)` (i < j by convention).
-- Walks to i (holding the head reborrow), then to j through the disjoint tail;
-- returns both. The two element borrows are disjoint by the suspension tree.
def nth2 : Decl :=
  { name := "nth2", retType := pairMut,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT), ("d1", mutNat), ("d2", mutNat)],
    body := dllbcWith [v, i, j, d1, d2] {
      match i {
        Z => match v {
          Nil => Pair(d1, d2),
          Cons(hd, tl) => match j {
            Z => Pair(d1, d2),
            S(jj) => Pair(&mut *hd, nth(&mut *tl, jj, d2))
          } },
        S(k) => match v {
          Nil => Pair(d1, d2),
          Cons(hd, tl) => match j {
            Z => Pair(d1, d2),
            S(jj) => nth2(&mut *tl, k, jj, d1, d2)
          } }
      } } }
example : checkFnOk nth2 ([nth, nth2]) = true := by native_decide

/-! ## `swap` — the exchange through both cursors -/

-- `swap (v, i, j, d1, d2)` = grab both element borrows, then take-and-fill across
-- them (M2 machinery: `let t = *ei; *ei := *ej; *ej := t`).
def swap : Decl :=
  { name := "swap", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT), ("d1", mutNat), ("d2", mutNat)],
    body := dllbcWith [v, i, j, d1, d2] {
      let p = nth2(v, i, j, d1, d2);
      match p { Pair(ei, ej) => { let t = *ei; *ei := *ej; *ej := t; () } }
    } }
example : checkFnOk swap ([nth, nth2, swap]) = true := by native_decide

-- Caller checks (opaque recovery in checking mode).
def swapBody : Term := dllbcWith [] {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  let z1 = 0; let dd1 = &mut z1;
  let z2 = 0; let dd2 = &mut z2;
  swap(bb, 0, 2, dd1, dd2);
  let y = x;
  () }
example : checkFnOk { name := "sc", retType := .const "Unit", telescope := [], body := swapBody }
  ([nth, nth2, swap, { name := "sc", retType := .const "Unit", telescope := [], body := swapBody }]) = true := by
  native_decide

-- CONCRETELY: `swap(v, 0, 2)` on `[1,2,3]` yields `[3,2,1]`.
example :
    (match Dllbc.Tests.S9Diff.runExec [nth, nth2, swap] swapBody with
     | .ok env => env.lookup "y" == some (vlist [3,2,1])
     | .error _ => false) = true := by native_decide

/-! ## The multi-issued `endGroup` cascade, and a rejection -/

-- Both cursors live, then the owner is demanded: `endGroup` ends BOTH issued
-- borrows (in list order) before releasing the captured `v`. The first exercise
-- of M7's multi-issued end.
def cascade : Decl :=
  { name := "cascade", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let z1 = 0; let dd1 = &mut z1;
      let z2 = 0; let dd2 = &mut z2;
      let pp = nth2(bb, 0, 2, dd1, dd2);
      match pp { Pair(ei, ej) => { *ei := 9; *ej := 8; let y = x; () } } } }
example : checkFnOk cascade ([nth, nth2, cascade]) = true := by native_decide

-- Take a cursor's payload (leaving a hole) then demand the owner: the group
-- cannot end because an issued borrow has nothing to surrender. REJECTED.
def rejectProbe : Decl :=
  { name := "reject", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let z1 = 0; let dd1 = &mut z1;
      let z2 = 0; let dd2 = &mut z2;
      let pp = nth2(bb, 0, 2, dd1, dd2);
      match pp { Pair(ei, ej) => { let taken = *ei; let y = x; () } } } }
example : checkFnErr rejectProbe "nothing surrendered" ([nth, nth2, rejectProbe]) = true := by native_decide

/-! ## Differential coverage — the multi-issued group under the simulation relation

    The swap program's concrete run (executing mode) is an instance of some
    accepted symbolic path (checking mode). This gives the multi-issued group
    end simulation-relation coverage, not just golden observation. -/

example : Dllbc.Tests.S9Diff.diffV2 false [nth, nth2, swap] swapBody = true := by native_decide

end Dllbc.Tests.S13Swap
