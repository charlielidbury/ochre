import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
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
open Dllbc.Std (LeT lenT)

namespace Dllbc.Tests.S14Bounds

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
def mutNat : Term := .borrowT natT natT
def pairMut : Term := .sigmaT mutNat mutNat
def tS (t : Term) : Term := .ctorApp "S" [t]
def bE (x : Term) : Term := .app (.app (.const "botElim") (.const "Unit")) x   -- ex-falso marker
def rb (x : Var) : Term := .borrow (.deref (.var x))                           -- &mut *x

def vv : Var := ⟨0, "v"⟩
def ii : Var := ⟨1, "i"⟩
def jj : Var := ⟨2, "j"⟩

-- Expected concrete result Vals.
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
  { name := "nth", retType := mutNat,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT),
                  ("p", (LeT (tS (.var ii)) (lenT (.deref (.var vv)))))],
    body := .matchE vv [
      .mk "Nil" [] (bE (.var ⟨2, "p"⟩)),
      .mk "Cons" [⟨3, "hd"⟩, ⟨4, "tl"⟩] (
        .matchE ii [
          .mk "Z" [] (rb ⟨3, "hd"⟩),
          .mk "S" [⟨5, "k"⟩] (.call "nth" [rb ⟨4, "tl"⟩, .var ⟨5, "k"⟩, .var ⟨2, "p"⟩]) ]) ] }
example : checkFnOk nth = true := by native_decide

/-! ## Bounds-proof `nth2` — the multi-issued group, two bounds proofs -/

def nth2 : Decl :=
  { name := "nth2", retType := pairMut,
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
                  ("pij", (LeT (tS (.var ii)) (.var jj))),
                  ("p2", (LeT (tS (.var jj)) (lenT (.deref (.var vv)))))],
    body := .matchE vv [
      .mk "Nil" [] (bE (.var ⟨4, "p2"⟩)),
      .mk "Cons" [⟨5, "hd"⟩, ⟨6, "tl"⟩] (
        .matchE ii [
          .mk "Z" [] (.matchE jj [
            .mk "Z" [] (bE (.var ⟨3, "pij"⟩)),
            .mk "S" [⟨7, "jjv"⟩] (.ctorApp "Pair" [rb ⟨5, "hd"⟩, .call "nth" [rb ⟨6, "tl"⟩, .var ⟨7, "jjv"⟩, .var ⟨4, "p2"⟩]]) ]),
          .mk "S" [⟨8, "k"⟩] (.matchE jj [
            .mk "Z" [] (bE (.var ⟨3, "pij"⟩)),
            .mk "S" [⟨9, "jj2"⟩] (.call "nth2" [rb ⟨6, "tl"⟩, .var ⟨8, "k"⟩, .var ⟨9, "jj2"⟩, .var ⟨3, "pij"⟩, .var ⟨4, "p2"⟩]) ]) ]) ] }
example : checkFnOk nth2 ([nth, nth2]) = true := by native_decide

/-! ## Bounds-proof `swap` -/

def swap : Decl :=
  { name := "swap", retType := .const "Unit",
    telescope := [("v", .borrowT listNatT listNatT), ("i", natT), ("j", natT),
                  ("pij", (LeT (tS (.var ii)) (.var jj))),
                  ("p2", (LeT (tS (.var jj)) (lenT (.deref (.var vv)))))],
    body := .letIn ⟨5, "pr"⟩ (.call "nth2" [.var vv, .var ii, .var jj, .var ⟨3, "pij"⟩, .var ⟨4, "p2"⟩])
      (.matchE ⟨5, "pr"⟩ [ .mk "Pair" [⟨6, "ei"⟩, ⟨7, "ej"⟩]
        (.letIn ⟨8, "t"⟩ (.deref (.var ⟨6, "ei"⟩))
          (.assign (.deref (.var ⟨6, "ei"⟩)) (.deref (.var ⟨7, "ej"⟩))
            (.assign (.deref (.var ⟨7, "ej"⟩)) (.var ⟨8, "t"⟩) .unit))) ]) }
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
