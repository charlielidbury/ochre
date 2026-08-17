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

## What the probe found

**Step 3 works, and it was never the problem.** A returned borrow may point into
a carve, at either granularity, at a concrete or a symbolic index, through as many
layers as you care to stack — carve, then list reborrow, then a recursive callee's
own group. `getMutOrCaller` at the bottom is all three at once, checking green and
executing correctly. Four negative controls keep the acceptances honest.

**What does not work is stating a PRECONDITION about what the callee will find
inside its own carve.** A partial bucket walk needs `Le (S i) (Len bucket)`, and
`bucket` is a place the callee reaches rather than a parameter. Written with the
surface index place the parameter type is refused before the body is read; written
with the `aget` former it reflects, and then the proof will not convert at the
call site, because an element borrow's payload is a fresh σ with no equation tying
it to `aget i` of the array. Both are stated below with minimal repros.

**The way through is to make the walk TOTAL**, which is what Rust's own
`entry(k).or_insert(v)` does — no precondition, so nothing has to transport.

A second, unrelated finding fell out: the exit audit exempts a whole parameter
when a borrow derived from it is returned, rather than exempting only the returned
sub-place, so a callee may leave a hole in a sibling leaf and be accepted.

Sections G1–G5 below; G1 is the green baseline, G2–G5 are the new questions.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeTrans SortedA)

namespace Dllbc.Tests.HmProbeGetmut

/-! ## Reading helpers (borrowed from `ArraySort` §vi) -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]
def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def varrL (ls : List (List Nat)) : Val := .ctor "Arr" (ls.map vlist)

def tnatT : Nat → Term | 0 => .ctorApp "Z" [] | k + 1 => .ctorApp "S" [tnatT k]
def tarrT (l : List Nat) : Term := .ctorApp "Arr" (l.map tnatT)

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

/-- Succeeds only on a FOLDED run of plain naturals — so a leftover segmentation or
    a ⊥ in a slot makes it `none`, which is how the hole below is asserted. -/
def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 2000)
    | _ => none

/-- What the executing machine left in `y`. -/
def runY (t : Term) : Option Val :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok env => env.lookup "y"
  | .error _ => none

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
example : progOk g2ElemC = true := by native_decide

/-! ### G2.b — CONCRETE index, width-1 SEGMENT handle: `&mut (Array 1 Nat)` -/

def g2SegC : Term := prog{
  fn SegC (a : &mut (Array 3 Nat)) -> &mut (Array 1 Nat) { &m (*a)[1 ; 1] };
  () }
example : progOk g2SegC = true := by native_decide

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
example : progOk g2CarveRetC = true := by native_decide

/-! ### G2.d — the same, but returning an ELEMENT borrow taken inside the carve -/

def g2CarveElemC : Term := prog{
  fn CarveElemC (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
example : progOk g2CarveElemC = true := by native_decide

/-! ### G2.e — SYMBOLIC index, `quicksortA`'s cited three-way carve form -/

def g2CarveRetS : Term := prog{
  fn CarveRetS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                a : &mut (Array n Nat)) -> &mut (Array 1 Nat) {
    let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    c };
  () }
example : progOk g2CarveRetS = true := by native_decide

def g2CarveElemS : Term := prog{
  fn CarveElemS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                 a : &mut (Array n Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*a)[k ; 1 ; jj];
    let r = &m (*a)[S k ; ..];
    let e = &m (*c)[0];
    e };
  () }
example : progOk g2CarveElemS = true := by native_decide

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
example : progRejects g2BadTyElem
  "returned borrow's payload (σ8) does not have its owed type (Bool)" = true := by
  native_decide

-- Wrong WIDTH on the segment handle: a width-1 carve returned as `Array 2 Nat`.
def g2BadWidth : Term := prog{
  fn BadWidth (a : &mut (Array 3 Nat)) -> &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    c };
  () }
example : progRejects g2BadWidth
  "does not have its owed type (Array (S (S Z)) Nat)" = true := by native_decide

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
-- ACCEPTED — see "the sibling hole, chased to the caller" below. This is FINDING 2.
example : progOk g2SiblingHole = true := by native_decide

def g2SiblingCopy : Term := prog{
  fn SiblingCopy (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0];
    let e = &m (*c)[0];
    e };
  () }
example : progOk g2SiblingCopy = true := by native_decide

-- A hole in the RETURNED cell itself: `*e` taken, then `e` returned.
def g2RetHole : Term := prog{
  fn RetHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let c = &m (*a)[1 ; 1];
    let e = &m (*c)[0];
    let t = *e;
    e };
  () }
example : progRejects g2RetHole "cannot type value ⊥" = true := by native_decide

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

example : progOk g3Caller = true := by native_decide

-- CHECKING: the owner is re-minted as a fresh σ — the write is forgotten, exactly
-- as in `throughCaller`, and the carve underneath changes none of it.
example : tailEnv g3Caller
  [("z", .bot), ("b", .bot), ("e", .bot), ("y", .sym 0)] = true := by native_decide

-- EXECUTING: the write really landed, in the carved slot.
example : runY g3Caller == some (varr [3, 7, 2]) := by native_decide

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
example : progOk g4Lit = true := by native_decide
example : runY g4Lit == some (varrL [[1], [2], []]) := by native_decide

def g4LitTy : Term := prog{
  fn TakeSlots (s : &mut (Array 3 (List Nat))) -> Unit { () };
  () }
example : progOk g4LitTy = true := by native_decide

/-! ### G4.b — carve a cell out of an array of lists -/

def g4Carve : Term := prog{
  fn CarveL (s : &mut (Array 3 (List Nat))) -> Unit {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    () };
  () }
example : progOk g4Carve = true := by native_decide

/-! ### G4.c — the list reborrow INSIDE the carved cell (no call, no return) -/

def g4Reborrow : Term := prog{
  fn ReborrowL (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    () };
  () }
example : progOk g4Reborrow = true := by native_decide

/-! ### G4.d — WRITE through the two-layer borrow, locally (still no return) -/

def g4LocalWrite : Term := prog{
  fn PushL (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    let t = *bk;
    *bk := Cons(9, t);
    () };
  () }
example : progOk g4LocalWrite = true := by native_decide

/-! ### G4.e — RETURN the two-layer borrow: carve, then element-of-array reborrow.

    `&mut (List Nat)` first, because that is the borrow that actually crosses both
    layers; the list WALK on top of it is a third layer and a separate question. -/

def g4Ret2 : Term := prog{
  fn Bucket (s : &mut (Array 3 (List Nat))) -> &mut (List Nat) {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    bk };
  () }
example : progOk g4Ret2 = true := by native_decide

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
-- REJECTED, and NOT for any reason this section is about — see the bisection below.
example : progRejects g4Ret3Place "the place was never carved there" = true := by
  native_decide

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
example : progRejects g4Caller "the place was never carved there" = true := by
  native_decide

-- …while the MACHINE runs the whole thing and gets the right answer. The rejection
-- is about a spelling in a TYPE, not about anything the program does.
example : runY g4Caller == some (varrL [[1], [2, 8], []]) := by native_decide

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
-- The caller CHECKS…
example : progOk holeCaller2 = true := by native_decide
-- …and the owner comes back a well-typed fresh σ : Array 3 Nat.
example : tailEnv holeCaller2
  [("z", .bot), ("b", .bot), ("e", .bot), ("y", .sym 0)] = true := by native_decide

-- …but the machine hands back an array that is NOT a run of three naturals: leaf 0
-- still holds the hole the callee left, and the segmentation never rejoined.
-- (`arrOfV` succeeds only on a folded `Arr` of plain naturals.)
example : ((runY holeCaller2).bind arrOfV).isNone = true := by native_decide
-- It does RUN, so this is a divergence and not a stuck machine.
example : (runY holeCaller2).isSome = true := by native_decide

/-! ### Bisecting the sibling hole: is the RETURN what buys the exemption? -/

-- Same hole, nothing returned. If the audit catches it here, the exemption
-- granted to a returned borrow's parent is the mechanism.
def holeNoRet : Term := prog{
  fn HoleNoRet (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let t = (*l)[0 ; 1];
    () };
  () }
example : progRejects holeNoRet "holds ⊥" = true := by native_decide

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
example : progRejects holeOtherParam "holds ⊥" = true := by native_decide

-- …and the control: same two parameters, no hole anywhere.
def holeOtherOk : Term := prog{
  fn HoleOtherOk (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let e = &m (*a1)[1];
    e };
  () }
example : progOk holeOtherOk = true := by native_decide

/-! ### Bisecting G4.f: is it the RETURN, the CARVE, or the PLACE-TYPED BOUND? -/

-- (1) The place-typed parameter alone, no carve, no return.
def f1PlaceOnly : Term := prog{
  fn P1 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit
    { () };
  () }
-- THE HEADLINE OF THE BISECTION: no carve, no return, no body at all — and the
-- parameter type alone is refused.
example : progRejects f1PlaceOnly
  "array: no segment at [S Z ; S Z] in σ0 (the place was never carved there)"
  = true := by native_decide

-- (2) The place-typed parameter PLUS the carve at the same index. No return.
def f2PlaceCarve : Term := prog{
  fn P2 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit {
    let c = &m (*s)[1 ; 1];
    () };
  () }
example : progRejects f2PlaceCarve "the place was never carved there" = true := by
  native_decide

-- (3) The carve at a DIFFERENT index from the one the type mentions.
def f3PlaceCarveElsewhere : Term := prog{
  fn P3 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[0]))) -> Unit {
    let c = &m (*s)[1 ; 1];
    () };
  () }
-- The index in the TYPE is the one that fails, not the one in the body: this
-- rejection names `[Z ; S Z]`, the type's index, while the body carves at 1.
example : progRejects f3PlaceCarveElsewhere
  "array: no segment at [Z ; S Z] in σ0" = true := by native_decide

-- (4) The place-typed parameter plus an ELEMENT borrow instead of a segment carve.
def f4PlaceElem : Term := prog{
  fn P4 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> Unit {
    let bk = &m (*s)[1];
    () };
  () }
example : progRejects f4PlaceElem "the place was never carved there" = true := by
  native_decide

-- (5) …and the same, RETURNING the element borrow — the three-layer shape with the
-- carve replaced by a direct element borrow (`a[i]` is not `a[i ; 1]`, ¶2.1).
def f5PlaceElemRet : Term := withNth prog{
  fn P5 (s : &mut (Array 3 (List Nat)), i : Nat, p : Le (S i) (Len ((*s)[1]))) -> &mut Nat {
    let bk = &m (*s)[1];
    Nth(bk, i, p) };
  () }
example : progRejects f5PlaceElemRet "the place was never carved there" = true := by
  native_decide

/-! ### The `aget` route — the surface `[i]` is a STATE operation, `aget` is the
      comptime former, and `Arrays` §(i.c) says it is "a legal neutral either way,
      so a type may mention `aget i (*v)` while `i` is unknown". -/

-- (6) The bound stated with `aget` instead of the surface index place.
def f6AgetOnly : Term := prog{
  fn P6 (s : &mut (Array 3 (List Nat)), i : Nat,
         p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> Unit
    { () };
  () }
example : progOk f6AgetOnly = true := by native_decide

-- (7) …plus the carve.
def f7AgetCarve : Term := prog{
  fn P7 (s : &mut (Array 3 (List Nat)), i : Nat,
         p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    () };
  () }
example : progOk f7AgetCarve = true := by native_decide

-- (8) THE FULL SHAPE: carve, list reborrow, walk, return — with the `aget` bound.
def f8AgetGetMut : Term := withNth prog{
  fn GetMutA (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    Nth(bk, i, p) };
  () }
-- The type reflects and the body checks; the CALL SITE is where it stops.
example : progRejects f8AgetGetMut
  "call: argument (σ17) does not have its parameter type" = true := by native_decide

-- (9) …and the same with the direct element borrow in place of the carve.
def f9AgetElem : Term := withNth prog{
  fn GetMutE (s : &mut (Array 3 (List Nat)), i : Nat,
              p : Le (S i) (Len (aget (List Nat) 3 1 (*s)))) -> &mut Nat {
    let bk = &m (*s)[1];
    Nth(bk, i, p) };
  () }
-- …and with no carve in the function at all, the same failure — so the carve is
-- not what loses the bound.
example : progRejects f9AgetElem
  "call: argument (σ17) does not have its parameter type" = true := by native_decide

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
-- THE ANSWER: an element borrow's payload is a fresh σ, with no equation tying it
-- to `aget i` of the array it came out of.
example : progRejects agetTransport
  "does not have its ascribed type (Id (aget (List Nat) (S (S (S Z))) (S Z) σ0) σ5)"
  = true := by native_decide

-- …and through the carve as well.
def agetTransportCarve : Term := prog{
  fn AgetIdC (s : &mut (Array 3 (List Nat))) -> Unit {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    let h = (Refl : Id (List Nat) (aget (List Nat) 3 1 (old *s)) (*bk));
    () };
  () }
-- The SAME σ names and the same message with the carve present, which is how we
-- know the carve is not implicated.
example : progRejects agetTransportCarve
  "does not have its ascribed type (Id (aget (List Nat) (S (S (S Z))) (S Z) σ0) σ5)"
  = true := by native_decide

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
example : progOk orInsertL = true := by native_decide

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
-- **THE PROBE'S ANSWER.** A returned borrow that crossed a CARVE and a list
-- reborrow and a match peel, with no precondition to transport.
example : progOk orInsertA = true := by native_decide

/-! ### (c) The caller, both sides — the G3 pair, now over the composite shape -/

def orInsertCaller : Term := prog{
  fn OrInsertA (s : &mut (Array 3 (List Nat))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    match bk {
      Nil => { *bk := Cons(0, Nil);
               match bk { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  let z = Arr(Cons(1, Nil), Cons(2, Cons(3, Nil)), Nil);
  let b = &m z;
  let e = OrInsertA(b);
  *e := 8;
  let y = z;
  () }
example : progOk orInsertCaller = true := by native_decide
example : tailEnv orInsertCaller
  [("z", .bot), ("b", .bot), ("e", .bot), ("y", .sym 0)] = true := by native_decide
-- The write landed at the head of the bucket in slot 1, and nowhere else.
example : runY orInsertCaller == some (varrL [[1], [8, 3], []]) := by native_decide

-- …and the branch that INSERTS: slot 1 empty, so the callee writes the cell and
-- returns a borrow into what it just wrote.
def orInsertCallerNil : Term := prog{
  fn OrInsertA (s : &mut (Array 3 (List Nat))) -> &mut Nat {
    let c = &m (*s)[1 ; 1];
    let bk = &m (*c)[0];
    match bk {
      Nil => { *bk := Cons(0, Nil);
               match bk { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  let z = Arr(Cons(1, Nil), Nil, Nil);
  let b = &m z;
  let e = OrInsertA(b);
  *e := 8;
  let y = z;
  () }
example : progOk orInsertCallerNil = true := by native_decide
example : runY orInsertCallerNil == some (varrL [[1], [8], []]) := by native_decide

/-! ### (d) A SYMBOLIC slot index — which is what a hash actually gives you.

    `quicksortA`'s cited three-way carve, with the bucket work on the middle cell. -/

def orInsertS : Term := prog{
  fn OrInsertS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                s : &mut (Array n (List Nat))) -> &mut Nat {
    let l = &m (*s)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*s)[k ; 1 ; jj];
    let r = &m (*s)[S k ; ..];
    let bk = &m (*c)[0];
    match bk {
      Nil => { *bk := Cons(0, Nil);
               match bk { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  () }
example : progOk orInsertS = true := by native_decide

def orInsertSCaller : Term := prog{
  fn OrInsertS (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)),
                s : &mut (Array n (List Nat))) -> &mut Nat {
    let l = &m (*s)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*s)[k ; 1 ; jj];
    let r = &m (*s)[S k ; ..];
    let bk = &m (*c)[0];
    match bk {
      Nil => { *bk := Cons(0, Nil);
               match bk { Nil => (), Cons(hd, tl) => &m *hd } },
      Cons(hd, tl) => &m *hd
    } };
  let z = Arr(Cons(1, Nil), Cons(2, Cons(3, Nil)), Nil);
  let b = &m z;
  let e = OrInsertS(3, 1, 1, Refl, b);
  *e := 8;
  let y = z;
  () }
example : progOk orInsertSCaller = true := by native_decide
example : runY orInsertSCaller == some (varrL [[1], [8, 3], []]) := by native_decide

/-! ### (e) The RECURSIVE bucket walk — fuel-threaded, total, and it returns a
      borrow it got back FROM ITS OWN RECURSIVE CALL. -/

def withWalk (rest : Term) : Term := prog{
  fn Walk [f] (f : Nat, v : &mut List Nat) -> &mut Nat {
    match f {
      Z => { *v := Cons(0, Nil);
             match v { Nil => (), Cons(hd, tl) => &m *hd } },
      S(f2) => match v {
        Nil => { *v := Cons(0, Nil);
                 match v { Nil => (), Cons(hd, tl) => &m *hd } },
        Cons(hd, tl) => Walk(f2, &m *tl)
      }
    } };
  %rest }
example : progOk (withWalk prog{ () }) = true := by native_decide

/-! ### (f) THE WHOLE THING — the recursive walk composed under the symbolic carve.

    The returned borrow now crosses all three: a CARVE, a list reborrow, and an
    inner call's loan group (`Walk`'s result is a borrow `GetMutOr` never took
    itself). This is `get_mut`'s borrow structure, entire. -/

def withGetMutOr (rest : Term) : Term := withWalk prog{
  fn GetMutOr (n : Nat, k : Nat, jj : Nat, Heq : Id Nat n (Add k (S jj)), f : Nat,
               s : &mut (Array n (List Nat))) -> &mut Nat {
    let l = &m (*s)[Z ; k ; S jj | LeAdd k (S jj) | Heq];
    let c = &m (*s)[k ; 1 ; jj];
    let r = &m (*s)[S k ; ..];
    let bk = &m (*c)[0];
    Walk(f, bk) };
  %rest }
example : progOk (withGetMutOr prog{ () }) = true := by native_decide

def getMutOrCaller : Term := withGetMutOr prog{
  let z = Arr(Cons(1, Nil), Cons(2, Cons(3, Nil)), Nil);
  let b = &m z;
  let e = GetMutOr(3, 1, 1, Refl, 1, b);
  *e := 8;
  let y = z;
  () }
example : progOk getMutOrCaller = true := by native_decide
example : tailEnv getMutOrCaller
  [("z", .bot), ("b", .bot), ("e", .bot), ("y", .sym 0)] = true := by native_decide
-- Fuel 1, so `Walk` descends one cell: the write lands at bucket 1's SECOND
-- element, and the rest of the map is untouched.
example : runY getMutOrCaller == some (varrL [[1], [2, 8], []]) := by native_decide

/-! ## G5 — what a caller still knows, when the type packs its own invariant

    The opacity is stated as a loss, and for FUNCTIONAL facts it is total: after
    the group ends the owner is a fresh σ, so `*e := 8` is unprovable at the caller
    and so is any frame fact about the slots nobody touched. §6.1's reason is that
    `through` and `advance` share a signature and differ in exactly the claim a
    precise release would make, so inferring one from a signature would be unsound.

    But the fresh σ is minted **at the owed type**, and that is the whole of what
    survives — so it is worth being precise about how much that is. If the map's
    type PACKS its invariant, inhabiting the type IS the invariant, and the caller
    gets it back for free at every boundary, with no declared-back mechanism and no
    debt attached to the loan. Probed rather than asserted: below, a value whose
    type carries a `Σ0`-packed sortedness proof is lent to a callee, recovered
    after the group ends, and then passed to a function that DEMANDS the packed
    type. If the recovered σ were merely "an array", the second call would fail. -/

def g5Packed : Term := prog{
  fn Bump (m : &mut (Σ (k : Nat) → Σ0 (H : Le k 3) → Unit)) -> Unit { () };
  fn Needs (m : Σ (k : Nat) → Σ0 (H : Le k 3) → Unit) -> Unit { () };
  let z = Pair(2, Pair((), ()));
  let b = &m z;
  Bump(b);
  let y = z;
  Needs(y);
  () }
-- The packed invariant crosses the boundary: `y` is a fresh σ, and it is a fresh σ
-- AT THE PACKED TYPE, so `Needs` accepts it.
example : progOk g5Packed = true := by native_decide

/-- The control that makes it mean something: the SAME recovered σ handed to a
    function demanding a STRONGER packed invariant. If the recovery carried no
    dependent content — if it were merely "a pair" — this would pass too. -/
def g5PackedBad : Term := prog{
  fn Bump (m : &mut (Σ (k : Nat) → Σ0 (H : Le k 3) → Unit)) -> Unit { () };
  fn NeedsOther (m : Σ (k : Nat) → Σ0 (H : Le k 1) → Unit) -> Unit { () };
  let z = Pair(2, Pair((), ()));
  let b = &m z;
  Bump(b);
  let y = z;
  NeedsOther(y);
  () }
example : progRejects g5PackedBad
  "call: argument (σ5) does not have its parameter type" = true := by native_decide

/-! ### G5, stated

    A caller that calls `get_mut`, writes through the borrow, and lets the group
    end keeps exactly one thing: **the map is still a map**. If the map's type
    packs its invariant — a `Σ` of the slots array with a `Σ0` well-hashedness
    proof — then the fresh σ the group mints is minted at that type, and
    inhabiting the type IS the invariant, so well-formedness survives the boundary
    with no mechanism at all. The two probes above are that claim and its control:
    the recovered σ satisfies the invariant its type declares, and does not satisfy
    a stronger one. Nothing about this depends on `get_mut` in particular; it is
    what §6.1's "release a fresh existential AT THE DECLARED TYPE" buys, and it is
    why a packed representation is worth the packing.

    Everything else is gone, and the loss is not partial. The caller cannot prove
    the value it just wrote is in the map — `*e := 8` then `find(k) = 8` is exactly
    the inference §6.2 forbids. Nor can it prove the FRAME: that the buckets it did
    not touch are unchanged, that the map's size is what it was, that a key it
    inserted three calls ago is still there. All of those are relations between the
    fresh σ and the old one, and the whole content of opacity is the refusal to
    state such a relation from a signature — §6.1's `through`/`advance` pair being
    the proof that inferring one would be unsound.

    So the split is clean, and it is the same split Aeneas's hashmap case study
    draws: SAFETY and INVARIANT PRESERVATION are reachable today, because both are
    properties of the post-state alone and a packed type states properties of the
    post-state alone. FUNCTIONAL CORRECTNESS is not, because it is a relation, and
    a relation needs the debt to travel with the loan rather than with the
    signature — SUGGESTIONS.md's "borrow types re-founded: shape/contract split,
    loan-attached debts", whose acceptance test (`split_at_mut` as an ordinary
    library function) is the same missing capability seen from a different angle. -/

end Dllbc.Tests.HmProbeGetmut
