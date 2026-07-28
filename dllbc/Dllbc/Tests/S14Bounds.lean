import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff

/-!
# §14 test suite — bounds-proof cursors

The M13 swap worked but paid for out-of-bounds with a default-element parameter,
threaded through every call and every caller — the dominant contortion by the
naturalness memo's numbers. This milestone replaces it with the dependent option
(now expressible after M10–M12): a cursor carries a **bounds proof**, its
out-of-range branch is a ⊥-conflict discharge, and an out-of-bounds call is
rejected *at the call site* because no proof of the false bound exists.

The prerequisite — that borrow-mode symbolic match refines the payload snapshot,
so a parameter type mentioning `len *v` computes per branch — was verified
standalone before building any of this (M3 refinement at the payload + the M10
"refinement reaches all σ-bearing state" invariant, confirmed by a probe whose
`Nil` branch discharges `Le (S i) 0 = ⊥` and whose negative controls fail).

Shape decision for `nth2`: `(pij : Le (S i) j, p2 : Le (S j) (len *v))` with
`i < j` from `pij`. Chosen over `(p1 : Le (S i) (len *v), p2 : …)` because it
needs no third proof and no `le_trans`: `p2` discharges `Nil` (`Le (S j) 0 = ⊥`),
`pij` discharges the `j ≤ i` branches (`Le (S i) j = ⊥` there), the valid branch
needs no proof for the head element, and both proofs pass to the recursive call
*definitionally* (`Le (S(S k)) (S j') ≡ Le (S k) j'`). At concrete calls the
proofs are `()` (the ⊤ inhabitant); at symbolic calls they are parameters.
-/

open Dllbc

namespace Dllbc.Tests.S14Bounds

-- Expected concrete result Vals (test subjects).
def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]

/-! ## The segment vocabulary computes (`len`/`take`/`drop`) -/

example : (Val.nfV 1000 (Dllbc.Std.len (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3])) == vnat 3) = true := by
  native_decide
example : (Val.nfV 1000 (Dllbc.Std.take (Std.ofNat 2) (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]))
    == vlist [1, 2]) = true := by native_decide
example : (Val.nfV 1000 (Dllbc.Std.drop (Std.ofNat 2) (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]))
    == vlist [3]) = true := by native_decide

/-! ## Bounds-proof `nth` — Nil discharged, recursive proof passed down -/

-- `nth (v, i, p : Le (S i) (len *v)) → &mut Nat`. Nil: `p : Le (S i) 0 = ⊥`,
-- discharged. Cons/S(k): the recursive call takes `p` unchanged — `Le (S(S k))
-- (S (len *tl)) ≡ Le (S k) (len *tl)` definitionally, no lemma.
def nth : Decl :=
  decl{ fn nth (v : &mut List Nat, i : Nat, p : Le (S i) (len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &mut *hd,
        S(k) => nth(&mut *tl, k, p)
      }
    } } }
example : checkFnOk nth = true := by native_decide

/-! ## Bounds-proof `nth2` — the multi-issued group, two bounds proofs -/

def nth2 : Decl :=
  decl{ fn nth2 (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Σ (x : &mut Nat) → &mut Nat {
    match v {
      Nil => botElim Unit p2,
      Cons(hd, tl) => match i {
        Z => match j {
          Z => botElim Unit pij,
          S(jjv) => Pair(&mut *hd, nth(&mut *tl, jjv, p2))
        },
        S(k) => match j {
          Z => botElim Unit pij,
          S(jj2) => nth2(&mut *tl, k, jj2, pij, p2)
        }
      }
    } } }
example : checkFnOk nth2 ([nth, nth2]) = true := by native_decide

/-! ## Bounds-proof `swap` -/

def swap : Decl :=
  decl{ fn swap (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (len *v)) -> Unit {
    let pr = nth2(v, i, j, pij, p2);
    match pr { Pair(ei, ej) => {
      let t = *ei;
      *ei := *ej;
      *ej := t;
      () } } } }
example : checkFnOk swap ([nth, nth2, swap]) = true := by native_decide

/-! ## Callers — concrete proofs are `()`, OOB is a call-site rejection -/

-- `swap(bb, 0, 2, (), ())`: `Le 1 2` and `Le 3 3` both whnf to ⊤, inhabited by `()`.
def swapBody : Term := dllbcWith [] {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 2, (), ());
  let y = x;
  () }
example : checkFnOk { name := "sc", retType := .const "Unit", telescope := [], body := swapBody }
  ([nth, nth2, swap, { name := "sc", retType := .const "Unit", telescope := [], body := swapBody }]) = true := by
  native_decide

-- CONCRETELY: `swap(v, 0, 2)` on `[1,2,3]` yields `[3,2,1]`.
example :
    (match Dllbc.Tests.S9Diff.runExec [nth, nth2, swap] swapBody with
     | .ok env => env.lookup "y" == some (vlist [3, 2, 1])
     | .error _ => false) = true := by native_decide

-- OUT OF BOUNDS is rejected at the CALL SITE: `swap(bb, 0, 4, (), ())` needs
-- `p2 : Le (S 4) (len [1,2,3]) = Le 5 3 = ⊥`, and `()` cannot inhabit ⊥.
def oobBody : Term := dllbcWith [] {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &mut x;
  swap(bb, 0, 4, (), ());
  let y = x;
  () }
example : checkFnErr { name := "oob", retType := .const "Unit", telescope := [], body := oobBody }
  "does not have its parameter type"
  ([nth, nth2, swap, { name := "oob", retType := .const "Unit", telescope := [], body := oobBody }]) = true := by
  native_decide

/-! ## The multi-issued `endGroup` cascade, and a rejection (re-shaped from §13) -/

-- Both cursors live, then the owner is demanded: `endGroup` ends both issued
-- borrows in list order, then releases `v`.
def cascade : Decl :=
  { name := "cascade", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { *ei := 9; *ej := 8; let y = x; () } } } }
example : checkFnOk cascade ([nth, nth2, cascade]) = true := by native_decide

-- Take a cursor's payload (hole) then demand the owner: the group cannot end.
def rejectProbe : Decl :=
  { name := "reject", retType := .const "Unit", telescope := [],
    body := dllbcWith [] {
      let x = Cons(1, Cons(2, Cons(3, Nil)));
      let bb = &mut x;
      let pp = nth2(bb, 0, 2, (), ());
      match pp { Pair(ei, ej) => { let taken = *ei; let y = x; () } } } }
example : checkFnErr rejectProbe "nothing surrendered" ([nth, nth2, rejectProbe]) = true := by native_decide

/-! ## Differential coverage — bounds-proof pool, concrete proofs by computation -/

example : Dllbc.Tests.S9Diff.diffV2 false [nth, nth2, swap] swapBody = true := by native_decide

end Dllbc.Tests.S14Bounds
