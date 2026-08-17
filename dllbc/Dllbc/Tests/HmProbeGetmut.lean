import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# PROBE — `get_mut` : a returned borrow that crosses an ARRAY CARVE

A viability probe, not a milestone. The question is whether the Aeneas ICFP'22
hashmap's `get_mut(&mut self, key) -> &mut T` has a DLLBC shape today.

The op decomposes into three steps, of which only the first two are tested
anywhere in the corpus:

  1. carve the slots array at the hashed index          (`Arrays` §(ii)/§(iii))
  2. walk the bucket list in the carved cell            (`Boundaries` §14 `Nth`)
  3. **return a borrow that points inside the carve**   ← never tested

Step 3 is the new ground. §6.1's loan groups give DLLBC return-borrows
(`Choose`/`Through`/`Lend`), and §14's `Nth` returns `&mut Nat` out of a list —
but every borrow ever returned in this corpus points at a place the callee
reached by PEELING (`&m *hd`), never at a place the callee CARVED.

Sections G1–G4 below; G1 is the green baseline, G2–G4 are the new questions.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeTrans)

namespace Dllbc.Tests.HmProbeGetmut

/-! ## Reading helpers (borrowed from `ArraySort` §vi) -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]
def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tarrT (l : List Nat) : Term := .ctorApp "Arr" (l.map tnatT)

/-- The verbatim checker message, for the failure reports. -/
def why (t : Term) (retType : Term := prog{ Unit }) : String :=
  match checkProgram t retType with
  | .ok _ => "ACCEPTED"
  | .error e => e

/-- The verbatim EXECUTING message. -/
def whyExec (t : Term) : String :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok _ => "RAN"
  | .error e => e

/-! ## G1 — CONTROL: a list cursor returning `&mut Nat`

    §14's `Nth`, re-declared here so this file has its own green baseline. A
    borrow-returning callee, a bounds-evidence parameter, and a caller that writes
    through the returned borrow and then demands the owner. -/

def withNth (rest : Term) : Term := prog{
  fn Nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => Nth(&m *tl, k, p)
      }
    } };
  %rest }

example : progOk (withNth prog{ () }) = true := by native_decide

/-- The caller: borrow, cursor to index 1, write 9 through it, demand the owner. -/
def g1Caller : Term := withNth prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  let e = Nth(b, 1, ());
  *e := 9;
  let y = x;
  () }

example : progOk g1Caller = true := by native_decide

-- CHECKING: the owner comes back a FRESH σ — §6.1 opacity, the write forgotten.
example : tailEnv g1Caller
  [("x", .bot), ("b", .bot), ("e", .bot), ("y", .sym 0)] = true := by native_decide

-- EXECUTING: the write really landed, at the right index.
example : (match Dllbc.Tests.S9Diff.runExec g1Caller with
           | .ok env => env.lookup "y" == some (vlist [1, 9])
           | .error _ => false) = true := by native_decide

/-! ## G2 — THE NEW GROUND: a returned borrow that points INTO a carve

    Nat payload first, to isolate the carve question from the payload question.
    Two candidate handles for "the element at index k", and both are probed,
    because ¶2.1's "`a[i]` is not `a[i ; 1]`" makes them genuinely different
    things: an element borrow's payload is the element at `T`, a width-1 segment
    borrow's payload is an `Array 1 T`. -/

/-! ### G2.a — CONCRETE index, element handle: `&mut Nat` -/

def g2ElemC : Term := prog{
  fn ElemC (a : &mut (Array 3 Nat)) -> &mut Nat { &m (*a)[1] };
  () }
#eval why g2ElemC

/-! ### G2.b — CONCRETE index, width-1 SEGMENT handle: `&mut (Array 1 Nat)` -/

def g2SegC : Term := prog{
  fn SegC (a : &mut (Array 3 Nat)) -> &mut (Array 1 Nat) { &m (*a)[1 ; 1] };
  () }
#eval why g2SegC

/-! ### G2.c — the carve-then-return, concrete: carve a THREE-WAY split and
      return the middle cell, which is the shape `get_mut` actually needs (the
      left and right parts stay behind in the callee and must be audited). -/

def g2CarveRetC : Term := prog{
  fn CarveRetC (a : &mut (Array 3 Nat)) -> &mut (Array 1 Nat) {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    c };
  () }
#eval why g2CarveRetC

/-! ### G2.d — the same, but returning an ELEMENT borrow taken inside the carve -/

def g2CarveElemC : Term := prog{
  fn CarveElemC (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
#eval why g2CarveElemC

/-! ### G2.e — SYMBOLIC index, `quicksortA`'s cited three-way carve form -/

def g2CarveRetS : Term := prog{
  fn CarveRetS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                a : &mut (Array n Nat)) -> &mut (Array 1 Nat) {
    let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    c };
  () }
#eval why g2CarveRetS

def g2CarveElemS : Term := prog{
  fn CarveElemS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                 a : &mut (Array n Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    let e = &m (*c)[0];
    e };
  () }
#eval why g2CarveElemS

/-! ### G2.f — NEGATIVE CONTROLS, so the six acceptances above are not vacuous

    Each keeps the carve and breaks exactly one thing. If the exit audit were
    simply not looking at a returned carve borrow, these would pass too. -/

-- Wrong owed type on the element handle: a Nat borrow returned as a Bool borrow.
def g2BadTyElem : Term := prog{
  fn BadTyElem (a : &mut (Array 3 Nat)) -> &mut Bool {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
#eval why g2BadTyElem

-- Wrong WIDTH on the segment handle: a width-1 carve returned as `Array 2 Nat`.
def g2BadWidth : Term := prog{
  fn BadWidth (a : &mut (Array 3 Nat)) -> &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    c };
  () }
#eval why g2BadWidth

-- A HOLE left in a SIBLING leaf the callee does not return: the RANGE read
-- `(*l)[0 ; 1]` takes the run out (§2.2's take-and-refill) and never refills it,
-- so `l`'s payload is not whole at the exit audit.
--
-- Note it must be the RANGE form: `(*l)[0]` is an INDEX read of a `Nat`, which is
-- index-kind, so §2.1's copy-on-read leaves the array intact and no hole exists.
-- That variant is accepted, and correctly so.
def g2SiblingHole : Term := prog{
  fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0 ; 1];
    let e = &m (*c)[0];
    e };
  () }
#eval why g2SiblingHole

def g2SiblingCopy : Term := prog{
  fn SiblingCopy (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0];
    let e = &m (*c)[0];
    e };
  () }
#eval why g2SiblingCopy

-- A hole in the RETURNED cell itself: `*e` taken, then `e` returned.
def g2RetHole : Term := prog{
  fn RetHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let c = &m (*a)[1 ; 1];
    let e = &m (*c)[0];
    let t = *e;
    e };
  () }
#eval why g2RetHole

/-! ## G3 — CALLER SIDE: write through the returned borrow, end the group

    The pair `throughCaller` asserts, now with a carve underneath: the CHECKER
    hands the owner a fresh σ (opacity), and the MACHINE really mutates the slot. -/

def withGetSlot (rest : Term) : Term := prog{
  fn GetSlot (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  %rest }

def g3Caller : Term := withGetSlot prog{
  let z = Arr(3, 1, 2);
  let b = &m z;
  let e = GetSlot(b);
  *e := 7;
  let y = z;
  () }

#eval why g3Caller
#eval tailEnvs g3Caller
#eval whyExec g3Caller
#eval (match Dllbc.Tests.S9Diff.runExec g3Caller with
       | .ok env => toString (env.lookup "y")
       | .error e => "ERR " ++ e.take 300)

/-! ## G4 — THE COMPOSITE `get_mut` SHAPE

    `slots : &mut (Array n (List Nat))`. Carve the cell at the hashed index, walk
    the bucket list inside the carved cell, return `&mut Nat` at a list element.
    Two borrow layers: the carve, then the list reborrow.

    Bisected from the bottom, because the payload is no longer index-kind and that
    is a second variable: G4.a asks only whether an array of LISTS is a value at
    all, G4.b adds the carve, G4.c the list reborrow, G4.d the local write, and
    only G4.e returns. -/

/-! ### G4.a — is `Array n (List Nat)` a thing? -/

def g4Lit : Term := prog{
  let s = Arr(Cons(1, Nil), Cons(2, Nil), Nil);
  let y = s;
  () }
#eval why g4Lit
#eval whyExec g4Lit

def g4LitTy : Term := prog{
  fn TakeSlots (s : &mut (Array 3 (List Nat))) -> Unit { () };
  () }
#eval why g4LitTy

/-! ### G4.b — carve a cell out of an array of lists -/

def g4Carve : Term := prog{
  fn CarveL (s : &mut (Array 3 (List Nat))) -> Unit {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    () };
  () }
#eval why g4Carve

/-! ### G4.c — the list reborrow INSIDE the carved cell (no call, no return) -/

def g4Reborrow : Term := prog{
  fn ReborrowL (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    () };
  () }
#eval why g4Reborrow

/-! ### G4.d — WRITE through the two-layer borrow, locally (still no return) -/

def g4LocalWrite : Term := prog{
  fn PushL (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    let t = *bk;
    *bk := Cons(9, t);
    () };
  () }
#eval why g4LocalWrite

/-! ### G4.e — RETURN the two-layer borrow: carve, then element-of-array reborrow.

    `&mut (List Nat)` first, because that is the borrow that actually crosses both
    layers; the list WALK on top of it is a third layer and a separate question. -/

def g4Ret2 : Term := prog{
  fn Bucket (s : &mut (Array 3 (List Nat))) -> &mut (List Nat) {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    bk };
  () }
#eval why g4Ret2

/-! ### G4.f — three layers: carve, element-of-array reborrow, then the LIST walk.

    The bucket walk needs a bounds proof, and the bound is over a place the callee
    reaches rather than over a parameter — `Len` of the bucket at slot 1. Two
    spellings are tried: the bound over the INDEX PLACE of the borrow payload, and
    the bound handed in already-instantiated. -/

def g4Ret3Place : Term := withNth prog{
  fn GetMutP (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len ((*s)[1]))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    Nth(bk, i, p) };
  () }
#eval why g4Ret3Place

/-! ### G4.g — CALLER for the three-layer return, both sides asserted -/

def g4Caller : Term := withNth prog{
  fn GetMutP (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len ((*s)[1]))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    Nth(bk, i, p) };
  let z = Arr(Cons(1, Nil), Cons(2, Cons(3, Nil)), Nil);
  let b = &m z;
  let e = GetMutP(b, 1, ());
  *e := 8;
  let y = z;
  () }
#eval why g4Caller
#eval tailEnvs g4Caller
#eval whyExec g4Caller
#eval (match Dllbc.Tests.S9Diff.runExec g4Caller with
       | .ok env => toString (env.lookup "y")
       | .error e => "ERR " ++ e.take 300)

/-! ## The sibling-hole acceptance, chased to the caller

    `g2SiblingHole` above is ACCEPTED, and the reason matters: when a callee
    returns a borrow derived from a parameter borrow, that parameter is EXEMPT
    from the exit audit (§6.1 — the caller cannot recover it until the group
    ends). So a hole the callee left in a leaf it does NOT return is not looked
    at. In checking mode §6.2's opacity then re-mints the owner as a fresh σ at
    the declared type, which REPAIRS it. The question is what the machine does. -/

def holeCaller2 : Term := prog{
  fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0 ; 1];
    let e = &m (*c)[0];
    e };
  let z = Arr(3, 1, 2);
  let b = &m z;
  let e = SiblingHole(b);
  *e := 7;
  let y = z;
  () }
#eval why holeCaller2
#eval tailEnvs holeCaller2
#eval whyExec holeCaller2
#eval (match Dllbc.Tests.S9Diff.runExec holeCaller2 with
       | .ok env => toString (env.lookup "y")
       | .error e => "ERR " ++ e.take 300)

/-! ### Bisecting the sibling hole: is the RETURN what buys the exemption? -/

-- Same hole, nothing returned. If the audit catches it here, the exemption
-- granted to a returned borrow's parent is the mechanism.
def holeNoRet : Term := prog{
  fn HoleNoRet (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let t = (*l)[0 ; 1];
    () };
  () }
#eval why holeNoRet

-- Two parameters: the hole is left in `a2`, the returned borrow comes out of `a1`.
-- If THIS is rejected, the exemption is per-parameter (and the finding is that it
-- is whole-parameter rather than per-place).
def holeOtherParam : Term := prog{
  fn HoleOther (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let t = (*l)[0 ; 1];
    let e = &m (*a1)[1];
    e };
  () }
#eval why holeOtherParam

-- …and the control: same two parameters, no hole anywhere.
def holeOtherOk : Term := prog{
  fn HoleOtherOk (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let e = &m (*a1)[1];
    e };
  () }
#eval why holeOtherOk

/-! ### Bisecting G4.f: is it the RETURN, the CARVE, or the PLACE-TYPED BOUND? -/

-- (1) The place-typed parameter alone, no carve, no return.
def f1PlaceOnly : Term := prog{
  fn P1 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit
    { () };
  () }
#eval why f1PlaceOnly

-- (2) The place-typed parameter PLUS the carve at the same index. No return.
def f2PlaceCarve : Term := prog{
  fn P2 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit {
    let c = &m (*s)[1 ; 1];
    () };
  () }
#eval why f2PlaceCarve

-- (3) The carve at a DIFFERENT index from the one the type mentions.
def f3PlaceCarveElsewhere : Term := prog{
  fn P3 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[0]))) -> Unit {
    let c = &m (*s)[1 ; 1];
    () };
  () }
#eval why f3PlaceCarveElsewhere

-- (4) The place-typed parameter plus an ELEMENT borrow instead of a segment carve.
def f4PlaceElem : Term := prog{
  fn P4 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit {
    let bk = &m (*s)[1];
    () };
  () }
#eval why f4PlaceElem

-- (5) …and the same, RETURNING the element borrow — the three-layer shape with the
-- carve replaced by a direct element borrow (`a[i]` is not `a[i ; 1]`, ¶2.1).
def f5PlaceElemRet : Term := withNth prog{
  fn P5 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> &mut Nat {
    let bk = &m (*s)[1];
    Nth(bk, i, p) };
  () }
#eval why f5PlaceElemRet

/-! ### The `aget` route — the surface `[i]` is a STATE operation, `aget` is the
      comptime former, and `Arrays` §(i.c) says it is "a legal neutral either way,
      so a type may mention `aget i (*v)` while `i` is unknown". -/

-- (6) The bound stated with `aget` instead of the surface index place.
def f6AgetOnly : Term := prog{
  fn P6 (s : &mut (Array 3 (List Nat)), i : Nat,
         p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> Unit
    { () };
  () }
#eval why f6AgetOnly

-- (7) …plus the carve.
def f7AgetCarve : Term := prog{
  fn P7 (s : &mut (Array 3 (List Nat)), i : Nat,
         p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    () };
  () }
#eval why f7AgetCarve

-- (8) THE FULL SHAPE: carve, list reborrow, walk, return — with the `aget` bound.
def f8AgetGetMut : Term := withNth prog{
  fn GetMutA (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    Nth(bk, i, p) };
  () }
#eval why f8AgetGetMut

-- (9) …and the same with the direct element borrow in place of the carve.
def f9AgetElem : Term := withNth prog{
  fn GetMutE (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> &mut Nat {
    let bk = &m (*s)[1];
    Nth(bk, i, p) };
  () }
#eval why f9AgetElem

/-! ### What exactly is lost: does an element borrow's payload KNOW it is `aget i`?

    (8) and (9) both fail at the CALL SITE rather than at the carve — the bound
    reflects, the carve runs, and then `Nth`'s `Le (S i) (Len *bk)` is not
    satisfied by a proof of `Le (S i) (Len (aget … 1 (*s)))`. So the question is
    whether the two are the same term. Asked directly with `Refl`. -/

def agetTransport : Term := prog{
  fn AgetId (s : &mut (Array 3 (List Nat))) -> Unit {
    let bk = &m (*s)[1];
    let h = (Refl : Id (List Nat) (aget (List Nat) 3 1 (old *s)) (*bk));
    () };
  () }
#eval why agetTransport

-- …and through the carve as well.
def agetTransportCarve : Term := prog{
  fn AgetIdC (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    let h = (Refl : Id (List Nat) (aget (List Nat) 3 1 (old *s)) (*bk));
    () };
  () }
#eval why agetTransportCarve

/-! ## The TOTAL route — `or_insert`, which needs no bounds proof at all

    The bound is only needed because the walk is partial. Rust's own
    `entry(k).or_insert(v)` is total: on `Nil` it WRITES a fresh cell and returns a
    borrow into what it just wrote. That removes the precondition entirely, so
    nothing has to transport past the carve — and it is a real hashmap operation,
    not a probe artifact.

    Depth 1 first (no recursion), because the question here is the BORROW
    STRUCTURE and not the walk. -/

-- (a) List only, no array: does the re-match after a concrete write typecheck?
def orInsertL : Term := prog{
  fn OrInsertL (v : &mut List Nat) -> &mut Nat {
    match v {
      Nil => { *v := Cons(0, Nil);
               match v { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  () }
#eval why orInsertL

-- (b) …the same, composed under the carve: THE `get_mut` SHAPE, total.
def orInsertA : Term := prog{
  fn OrInsertA (s : &mut (Array 3 (List Nat))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    match bk {
      Nil => { *bk := Cons(0, Nil);
               match bk { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  () }
#eval why orInsertA

end Dllbc.Tests.HmProbeGetmut
