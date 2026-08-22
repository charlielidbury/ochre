import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# The hashmap with the proofs taken out

`Tests/HashMap.lean` writes a resizable hashmap whose invariant is packed into
the container's type and whose every operation carries its full specification.
This file writes THE SAME RUNTIME PROGRAM with all of that removed: no packed
invariant, no proof parameters, no evidence returns, no spec functions. Same
data layout, same control flow, same allocation shape, same answers.

It exists to measure the proof overhead, and to say by a concrete differential
rather than by assertion that the two programs compute the same thing: the
callers at the bottom are `HashMap.lean`'s executing differential ported over
verbatim, asserting the same expected values — including the post-resize
bucket order `[(9,90),(1,10)]`, which is the single-allocation rotation's
prepend showing through.

## The measurement

Lines per `fn`, verified → erased, over the whole of `hmS1Under` in its own
order:

    InsertInList    46 →  11        SlotPush       113 → 22
    RemoveL         47 →  13        MoveBktR        72 → 12
    SlotOfE          3 →   3        MoveOne        166 → 10
    NewHM           13 →   3        MoveSlots       84 → 10
    SlotUpd        141 →  11        InsertHM       236 → 22
    SlotRem         98 →  14        RemoveHM        89 → 16
    ----------------------------------------------------------
    TOTAL         1108 → 147                              7.5x

and over the borrow-returning layer, which was already nearly proof-free:

    WalkVal         11 →  11        ContainsWalk     9 →  9
    GetMutRaw       20 →  19        ContainsHM      20 → 19
    GetMutHM         6 →   4        GetMutOrInsert  11 →  9
    ----------------------------------------------------------
    TOTAL           77 →  71                              1.1x

7.5x understates it, because the verified chain rests on a corpus the erased
one does not need at all: 193 pure definitions and 106 checked assertions
across 2913 lines of `HashMap.lean` — the spec functions, the packed
invariant and its five projections, the crossing lemmas for the carve, the
bucket walk's evidence, the resize fold's pointwise algebra. The erased
program's entire supporting vocabulary is 8 definitions in 42 lines, and 7 of
them are data or a Bool test the program branches on. Whole file: 7980 lines
against 735, of which 200 here are this comment and the erasure notes.

The two op-chain columns are the honest like-for-like number. The 2913-line
figure is a span, not a dependency analysis: it contains a few shape probes
and the assertions that check the lemmas, and it does not include
`StdLemmas.lean`, which both programs use.

Cold `lake build` of the module, same machine, warm dependency cache: 105 s
for `Tests/HashMap.lean`, 2.3 s for this one. Read that as the cost of the
FILE and not of the program — the verified file also checks 106 lemma
assertions, the lying twins and the pinned probes, none of which this file
has a counterpart for. Attempts to time the two chains' checks against each
other directly did not produce numbers worth quoting, so none are.

## What did NOT erase: nine bounds citations and two helpers

DLLBC has no unchecked indexing. `a[i]` without a citation elaborates only
when the bound COMPUTES, and at a symbolic capacity it does not — so every
route to a bucket keeps its witness. What is left after the erasure is:

  * `SlotPackE` (6 lines) and `SlotOfE` (3 lines) — the residue minter and the
    fn that carries it across a call boundary. Both verbatim from the verified
    file.
  * six citations at the three-way slot carve — `| LeAdd i (S r) | hd` in
    `SlotUpd`, `SlotRem` and `SlotPush`;
  * one at the move loop's source carve — `| LebTrueLe (S j) capF e` in
    `MoveOne`;
  * two at the single-index carve — `| NatRw … (ModLtN …)` in `GetMutRaw` and
    `ContainsHM`.

`SlotOfE` is irreducible for two separate reasons, both measured against the
checker rather than assumed. It supplies the DECOMPOSITION the three-way carve
needs, which at a symbolic extent nothing computes; and it supplies a VARIABLE
index, which the single-index carve needs — writing the same carve at the
expression `Mod key c` is refused ("the leaf's extent … is a compound neutral,
not a flexible σ") because premise (3) then has nothing to solve.

## Where a runtime check replaced a proof

Six sites, each one an invariant fact the verified program read off the pack:

  * `SlotUpd`, `SlotRem`: `if e : Leb 1 cap` for `InvLe1`'s `cap ≥ 1`;
  * `SlotPush`: `if e : Leb 1 cap2`, for `Le1Mul2 cap HLe1` at the doubled
    capacity;
  * `MoveOne`: `if e : Leb (S j) capF`, for the `Hj : Id Nat capF (Add j m)`
    decomposition that `MoveSlots` threaded down;
  * `GetMutRaw`, `ContainsHM`: `if e : Leb 1 c`, for `PackLe1 (*self)`.

It is a `Leb` TEST and not a `match cap`, and that is the whole shape of the
erased program rather than a style choice. Matching refines the extent to
`S c`, a compound neutral, and the carve then has no flexible σ to solve
against — refused. Supplying the full decomposition from `SlotOfE` so premise
(3) has nothing to solve is refused one step later ("Refl: both endpoints are
rigid"). A Bool test does not refine `cap`, so the extent stays the flexible
telescope σ the carve wants, and `LebTrueLe` turns the test back into the
`Le`. Had either of the first two worked, `Le (S Z) cap` would still have had
to be threaded as a parameter through six fns and this program would have kept
six proof arguments; with the test, it keeps none.

## Fuel: the erased program is partial where the verified one proved totality

Every `Z => botElim Unit Hf` arm became a default, because nothing proves the
fuel sufficient any more: `InsertInList` returns `False` leaving the bucket
alone, `RemoveL` returns the list unchanged, `MoveBktR` stops draining (and
the entries still in `src` are then dropped by `MoveOne`'s take-out),
`SlotPush` no-ops on a `Nil` source, and `RemoveHM` leaves `n` at zero where
`Znots` ruled the case out. The `else` arm of each `Leb` test is the same
kind of hole: a zero-capacity map silently does nothing. The callers pass the
same generous fuel the verified callers do, so no concrete test reaches one.

## What the overhead actually is

Almost none of the 7.5x is forced. What the type system genuinely demands of a
program that indexes an array at a hash is the nine citations and the two
helpers above — nine lines of helper plus the citations, call it twenty of the
147, and they would be there whether or not anything was being verified.
Everything else the verified version carries, it carries because it is proving
a specification: the packed invariant and its five projections, the pointwise
`FindL` equation threaded through every op, the size ledger, and the crossing
lemmas that move all of that across a carve. That is a choice about what to
state, not a tax the checker imposes, and the shape of the ratio says so — the
fns that grow most (`MoveOne` 16.6x, `SlotUpd` 12.8x, `InsertHM` 10.7x) are
exactly the ones whose specification has to survive an array carve or a
resize, while `SlotOfE` (1.0x) and the whole borrow-returning layer (1.1x)
barely move, because they were never proving much.

Two things keep this from reading as "proofs cost 7.5x". The erased program is
PARTIAL where the verified one is total, so some of the extra lines buy not
the specification but the absence of the silent no-ops listed above. And the
overhead is not only lines: the packed invariant makes `GetMutHM`,
`ContainsHM` and `GetMutOrInsertHM` unwritable today — the erased chain checks
and the verified one does not — which the probe at the end of this file
isolates to a comptime component whose type depends on the array's value.
Against that, the verified program is the one whose `InsertHM` cannot forget
to bump the count, and `HashMap.lean`'s lying twins are the standing evidence
that the checker notices when it does.
-/

section
open Dllbc
open Dllbc.StdLemmas (Mod ModLtN ModDec LeAdd LebTrueLe Mul NatRw IdSym)

namespace Dllbc.Tests.HashMapErased

/-! ## The runtime vocabulary

    Everything here is data or a Bool test that the program branches on — it
    survives the erasure because the RUNTIME reads it, not because a proof
    does. There is deliberately no import of `Tests/HashMap.lean`: the erased
    program needs none of that file's ~3000 lines of pure lemmas, and an
    import would hide that. -/

/-- The option payload, and the Σ(Bool) option type standing in for a native
    `Option` the kernel does not have. -/
def OptP : Term := prog defer_check {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

def Opt : Term := prog defer_check { λ (T : Type). Σ (b : Bool). OptP b T }
def OptN : Term := prog defer_check { Σ (bb : Bool). OptP bb Nat }
def SomeN : Term := prog defer_check { λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog defer_check { Pair(False, unit) }

/-- Bucket emptiness as a Bool, so the drain loop can test `src` without
    matching it — matching a borrow reborrows its payload and the rotation
    below could then not move the node. -/
def IsNilB : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Bool) {
      Nil => True,
      Cons (E) (T) Rec => False } }

/-- `n` empty buckets — the only allocation a resize performs. -/
def MkSlots : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List (Σ (k : Nat). Nat))) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }

/-- **The one piece of proof that does not erase.** DLLBC has no unchecked
    indexing: a carve of `Array n T` at a symbolic index has to hand premise
    (3) a decomposition `n = i + (1 + r)`, and at a symbolic `n` no such
    decomposition computes. This mints one from `i < n`: the residue `r`, the
    equation, and the identity tying `i` to the hash.

    Verbatim from `HashMap.lean`'s `SlotPack`, which is where it is explained.
    See the erasure notes below for why it is irreducible. -/
def SlotPackE : Term := prog defer_check {
  λ (H : Nat). λ (N : Nat). λ (Hne : Le (S Z) N).
    elim (ModDec (Mod H N) N (ModLtN H N Hne)) return
        (λ (Q : Σ (R : Nat). Id Nat N (Add (Mod H N) (S R))).
          Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N)) {
      Pair (R0) (Hd0) => Pair(Mod H N, Pair(R0, Pair(Hd0, Refl))) } }

/-! ## The erased program

    One `fn` per verified `fn`, same name, same order, same body shape. What
    changed, systematically:

    * the container is `Σ cap. Σ load. Σ n. Array cap Bucket` — no `Σ0`
      invariant component;
    * every proof parameter and every evidence return is gone, so each fn
      returns the runtime value it actually computes (`Bool`, the `Opt`, or
      `Unit`);
    * a `Z => botElim Unit Hf` fuel arm becomes a harmless default, since
      nothing proves the fuel sufficient any more;
    * `cap ≥ 1` came from the packed invariant (`InvLe1`); here every fn that
      carves tests it itself with `Leb 1 cap` and turns the test into the
      `Le` that `SlotOfE` wants. The test is a `Leb`, deliberately, and NOT a
      `match cap`: matching refines the extent to `S c`, and a compound extent
      is rigid, which is exactly what the carve cannot have (¶8.4). -/

def hmErasedUnder (tail : Term) : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, key : Nat, val : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)))
      -> Bool
      { match b {
          Nil => { *b := Cons(Pair(key, val), Nil); False },
          Cons(Pair(kk, vv), tl) => match fuel {
            Z => False,
            S(f2) =>
              if Eqb *kk key { *vv := val; True }
              else { InsertInList(f2, key, val, &m *tl) }
          } } };
  fn RemoveL [fuel] (fuel : Nat, key : Nat, l : List (Σ (k : Nat). Nat))
      -> Σ (ret : OptN). List (Σ (k : Nat). Nat)
      { match l {
          Nil => Pair(NoneN, Nil),
          Cons(Pair(kk, vv), tl2) => match fuel {
            Z => Pair(NoneN, Cons(Pair(kk, vv), tl2)),
            S(f2) =>
              if Eqb kk key { Pair(Pair(True, vv), tl2) }
              else {
                let Pair(rr2, l3) = RemoveL(f2, key, tl2);
                Pair(rr2, Cons(Pair(kk, vv), l3))
              }
          } } };
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPackE h n Hne };
  fn NewHM (cap : Nat)
      -> Σ (c : Nat). Σ (load : Nat). Σ (n : Nat). Array c (List (Σ (k : Nat). Nat)) {
    Pair(cap, Pair(Mul 4 cap, Pair(Z, MkSlots cap))) };
  fn SlotUpd (fuel : Nat, cap : Nat, key : Nat, val : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))))
      -> Bool
      { if e : Leb 1 cap {
          let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, LebTrueLe 1 cap e);
          let pre = &m (*b)[Z ; i ; S r | LeAdd i (S r) | hd];
          let cell = &m (*b)[i ; 1 ; r];
          let hic = &m (*b)[S i ; r];
          let bb = &m (*cell)[0];
          InsertInList(fuel, key, val, &m *bb)
        } else { False } };
  fn SlotRem (fuel : Nat, cap : Nat, key : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))))
      -> OptN
      { if e : Leb 1 cap {
          let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, LebTrueLe 1 cap e);
          let pre = &m (*b)[Z ; i ; S r | LeAdd i (S r) | hd];
          let cell = &m (*b)[i ; 1 ; r];
          let hic = &m (*b)[S i ; r];
          let bb = &m (*cell)[0];
          let bcur = *bb;
          let Pair(rr2, l3) = RemoveL(fuel, key, bcur);
          *bb := l3;
          rr2
        } else { NoneN } };
  fn SlotPush (cap2 : Nat,
               src : &mut (List (Σ (k : Nat). Nat)),
               dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { match src {
          Nil => (),
          Cons(Pair(kk, vv), tail) => {
            let k0 = *kk;
            *kk := k0;
            if e : Leb 1 cap2 {
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(k0, cap2, LebTrueLe 1 cap2 e);
              let pre = &m (*dst)[Z ; i ; S r | LeAdd i (S r) | hd];
              let cell = &m (*dst)[i ; 1 ; r];
              let hic = &m (*dst)[S i ; r];
              let bb = &m (*cell)[0];
              let tmp = *tail;
              *tail := *bb;
              *bb := *src;
              *src := tmp;
              ()
            } else { () }
          } } };
  fn MoveBktR [fuel] (fuel : Nat, cap2 : Nat,
                      src : &mut (List (Σ (k : Nat). Nat)),
                      dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { if IsNilB (*src) { () } else {
          match fuel {
            Z => (),
            S(f2) => {
              SlotPush(cap2, &m *src, &m *dst);
              MoveBktR(f2, cap2, &m *src, &m *dst)
            } }
        } };
  fn MoveOne (tfuel : Nat, capF : Nat, cap2 : Nat, j : Nat,
              src : &mut (Array capF (List (Σ (k : Nat). Nat))),
              dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { if e : Leb (S j) capF {
          let bbs = &m (*src)[j | LebTrueLe (S j) capF e];
          let bl = *bbs;
          *bbs := Nil;
          MoveBktR(tfuel, cap2, &m bl, &m *dst)
        } else { () } };
  fn MoveSlots [m] (m : Nat, j : Nat, tfuel : Nat, capF : Nat, cap2 : Nat,
                    src : &mut (Array capF (List (Σ (k : Nat). Nat))),
                    dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))))
      -> Unit
      { match m {
          Z => (),
          S(m2) => {
            MoveOne(tfuel, capF, cap2, j, &m *src, &m *dst);
            MoveSlots(m2, S j, tfuel, capF, cap2, &m *src, &m *dst)
          } } };
  fn InsertHM (fuel : Nat, key : Nat, val : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Array cap (List (Σ (k : Nat). Nat))))
      -> Unit
      {
        let Pair(cap, Pair(load, Pair(nn, slots))) = *self;
        let sb = &m slots;
        let hit2 = SlotUpd(fuel, cap, key, val, &m *sb);
        match hit2 {
          True => { *self := Pair(cap, Pair(load, Pair(nn, slots))); () },
          False =>
            if Leb (Mul 5 (S nn)) load {
              *self := Pair(cap, Pair(load, Pair(S(nn), slots)));
              ()
            } else {
              let nslots = MkSlots (Mul 2 cap);
              let db = &m nslots;
              MoveSlots(cap, Z, fuel, cap, Mul 2 cap, &m *sb, &m *db);
              *self := Pair(Mul 2 cap, Pair(Mul 4 (Mul 2 cap), Pair(S(nn), nslots)));
              ()
            }
        } };
  fn RemoveHM (fuel : Nat, key : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Array cap (List (Σ (k : Nat). Nat))))
      -> OptN
      {
        let Pair(cap, Pair(load, Pair(nn, slots))) = *self;
        let sb = &m slots;
        let rr = SlotRem(fuel, cap, key, &m *sb);
        match rr {
          Pair(tg, pv) => match tg {
            True => match nn {
              Z => { *self := Pair(cap, Pair(load, Pair(Z, slots))); Pair(True, pv) },
              S(m2) => { *self := Pair(cap, Pair(load, Pair(m2, slots))); Pair(True, pv) }
            },
            False => { *self := Pair(cap, Pair(load, Pair(nn, slots))); Pair(False, pv) }
          } } };
  %tail }

/-- The erased chain, with nothing after it, type-checks. -/
example : progOk (hmErasedUnder prog defer_check { () }) = true := by native_decide

/-! ## The differential

    `HashMap.lean`'s executing differential, ported to the erased program:
    the same callers, the same key/value sequences, and THE SAME EXPECTED
    VALUES — including the post-resize bucket order `[(9,90),(1,10)]`, which
    is the rotation's prepend showing through. Proofs deleted, answers
    identical.

    The decoders are `HashMap.lean`'s, with one change: `hmOfVE` stops after
    three pairs because the erased pack has no invariant component to skip. -/

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

def pairOfV : Val → Option (Val × Val)
  | v => match Val.asCtor? v with
    | some ("Pair", [a, b]) => some (a, b)
    | _ => none

def entryOfV : Val → Option (Nat × Nat)
  | v => match pairOfV v with
    | some (a, b) =>
      match natOfV 4000 a, natOfV 4000 b with
      | some k, some w => some (k, w)
      | _, _ => none
    | none => none

def bktOfV : Nat → Val → Option (List (Nat × Nat))
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Nil", []), _ => some []
    | some ("Cons", [h, t]), f' + 1 =>
      match entryOfV h, bktOfV f' t with
      | some e, some es => some (e :: es)
      | _, _ => none
    | _, _ => none

def slotsOfV : Val → Option (List (List (Nat × Nat)))
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (bktOfV 2000)
    | _ => none

/-- Decode an erased pack into (cap, load, n, buckets). Three pairs, not four:
    the erased container's last component IS the array. -/
def hmOfVE (v : Val) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) := do
  let (c, r1) ← pairOfV v
  let (l, r2) ← pairOfV r1
  let (n, s) ← pairOfV r2
  let cap ← natOfV 4000 c
  let load ← natOfV 4000 l
  let nn ← natOfV 4000 n
  let bs ← slotsOfV s
  pure (cap, load, nn, bs)

/-- `runProgram` with a caller-chosen step budget (`HashMap.lean`'s). -/
def runProgramF (fuel : Nat) (t : Term) : Except String Env :=
  match (do let _ ← readR fuel (atBoundary t); endScope fuel).run
      { initSt with executing := true } with
  | .ok _ st => .ok (canonicalize st.env)
  | .error e _ => .error e

def runHME (t : Term) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) :=
  match runProgramF 2000000 t with
  | .ok env => (env.lookup "y").bind hmOfVE
  | .error _ => none

/-- A freshly created map: every bucket empty, `n = 0`, `load = 4·cap`. -/
def eNewCaller : Term := hmErasedUnder prog defer_check {
  let m0 = NewHM(3);
  let y = m0;
  () }

example : (runHME eNewCaller == some (3, 12, 0, [[], [], []])) = true := by
  native_decide

/-- Five inserts at cap 4: keys 5, 1, 9 all collide in slot 1 (the middle one
    walks past a miss), key 5 re-inserted mid-sequence must OVERWRITE in
    place, key 2 lands alone. The fifth distinct-key insert trips the load
    threshold, so the map resizes to 8 and rehashes.

    Byte-for-byte `HashMap.lean`'s `s1RunCaller` expectation, including the
    post-resize order `[(9,90),(1,10)]` — the rotation prepends, so same-slot
    survivors come out reversed. -/
def eRunCaller : Term := hmErasedUnder prog defer_check {
  let m0 = NewHM(4);
  let b1 = &m m0;
  InsertHM(9, 5, 70, b1);
  let b2 = &m m0;
  InsertHM(9, 1, 10, b2);
  let b3 = &m m0;
  InsertHM(9, 5, 71, b3);
  let b4 = &m m0;
  InsertHM(9, 9, 90, b4);
  let b5 = &m m0;
  InsertHM(9, 2, 20, b5);
  let y = m0;
  () }

example : (runHME eRunCaller ==
    some (8, 32, 4, [[], [(9, 90), (1, 10)], [(2, 20)], [], [], [(5, 71)], [], []]))
    = true := by native_decide

/-- The insert sequence followed by three removes: key 5 (a hit), key 7 (a
    miss — nothing changes), key 1 (mid-bucket unlink). -/
def eRemCaller : Term := hmErasedUnder prog defer_check {
  let m0 = NewHM(4);
  let b1 = &m m0;
  InsertHM(9, 5, 70, b1);
  let b2 = &m m0;
  InsertHM(9, 1, 10, b2);
  let b3 = &m m0;
  InsertHM(9, 5, 71, b3);
  let b4 = &m m0;
  InsertHM(9, 9, 90, b4);
  let b5 = &m m0;
  InsertHM(9, 2, 20, b5);
  let b6 = &m m0;
  RemoveHM(9, 5, b6);
  let b7 = &m m0;
  RemoveHM(9, 7, b7);
  let b8 = &m m0;
  RemoveHM(9, 1, b8);
  let y = m0;
  () }

example : (runHME eRemCaller ==
    some (8, 32, 2, [[], [(9, 90)], [(2, 20)], [], [], [], [], []]))
    = true := by native_decide

/-- From capacity 1 (threshold 0), four inserts force THREE doubling resizes:
    1 → 2 → 4 → 8, every entry re-slotted by the move fold each time. -/
def eGrowCaller : Term := hmErasedUnder prog defer_check {
  let m0 = NewHM(1);
  let b1 = &m m0;
  InsertHM(9, 1, 10, b1);
  let b2 = &m m0;
  InsertHM(9, 2, 20, b2);
  let b3 = &m m0;
  InsertHM(9, 3, 30, b3);
  let b4 = &m m0;
  InsertHM(9, 4, 40, b4);
  let y = m0;
  () }

example : (runHME eGrowCaller ==
    some (8, 32, 4, [[], [(1, 10)], [(2, 20)], [(3, 30)], [(4, 40)], [], [], []]))
    = true := by native_decide

/-! ## The borrow-returning ops, erased

    `GetMutHM`/`ContainsHM`/`GetMutOrInsertHM`, ported from `HashMap.lean`'s
    `hmGmUnder`. That layer was already almost proof-free — it carried
    `PackLe1 (*self)`, `GetMutHM`'s `Hin`, `GetMutOrInsertHM`'s `Hfuel` and one
    bound citation — so it is where the erasure changes least.

    The checker rejects this chain, and rejects the ERASED one for the same
    reason and with the same message: returning a borrow needs a `~>`/`*res`
    contract the kernel does not have yet. That rejection is a missing
    feature, not a missing proof — which is exactly what the erased twin
    below demonstrates, since there are no proofs left in it to blame. -/

def hmErasedGmUnder (tail2 : Term) : Term := hmErasedUnder prog{
  fn WalkVal [fuel] (fuel : Nat, key : Nat, dflt : Nat,
                     b : &mut (List (Σ (k : Nat). Nat))) -> &mut Nat {
    match fuel {
      Z => { *b := Cons(Pair(key, dflt), Nil);
             match b { Nil => (), Cons(Pair(kk, vv), tl) => &m *vv } },
      S(f2) => match b {
        Nil => { *b := Cons(Pair(key, dflt), Nil);
                 match b { Nil => (), Cons(Pair(kk, vv), tl) => &m *vv } },
        Cons(Pair(kk, vv), tl) =>
          if Eqb *kk key { &m *vv } else { WalkVal(f2, key, dflt, &m *tl) }
      } } };
  fn GetMutRaw (fuel : Nat, key : Nat, dflt : Nat,
                self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Array cap (List (Σ (k : Nat). Nat)))) -> &mut Nat {
    match self {
      Pair(cap, r1) => match r1 {
        Pair(load, r2) => match r2 {
          Pair(nn, slots) => {
            let c = *cap;
            *cap := c;
            let C0 = c;
            if e : Leb 1 c {
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, LebTrueLe 1 c e);
              let Him0 = him;
              let bb = &m (*slots)[i | NatRw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSym Nat i (Mod key C0) Him0)
                (ModLtN key C0 (LebTrueLe 1 C0 e))];
              WalkVal(fuel, key, dflt, bb)
            } else { &m *nn }
          } } } } };
  fn GetMutHM (fuel : Nat, key : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Array cap (List (Σ (k : Nat). Nat)))) -> &mut Nat {
    GetMutRaw(fuel, key, Z, &m *self) };
  fn ContainsWalk [fuel] (fuel : Nat, key : Nat,
                          b : &mut (List (Σ (k : Nat). Nat))) -> Bool {
    match fuel {
      Z => False,
      S(f2) => match b {
        Nil => False,
        Cons(Pair(kk, vv), tl) =>
          if Eqb *kk key { True } else { ContainsWalk(f2, key, &m *tl) }
      } } };
  fn ContainsHM (fuel : Nat, key : Nat,
                 self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                   Array cap (List (Σ (k : Nat). Nat)))) -> Bool {
    match self {
      Pair(cap, r1) => match r1 {
        Pair(load, r2) => match r2 {
          Pair(nn, slots) => {
            let c = *cap;
            *cap := c;
            let C0 = c;
            if e : Leb 1 c {
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, LebTrueLe 1 c e);
              let Him0 = him;
              let bb = &m (*slots)[i | NatRw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSym Nat i (Mod key C0) Him0)
                (ModLtN key C0 (LebTrueLe 1 C0 e))];
              ContainsWalk(fuel, key, bb)
            } else { False }
          } } } } };
  fn GetMutOrInsertHM (fuel : Nat, key : Nat, dflt : Nat,
                       self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                         Array cap (List (Σ (k : Nat). Nat)))) -> &mut Nat {
    if ContainsHM(fuel, key, &m *self) {
      GetMutRaw(fuel, key, dflt, &m *self)
    } else {
      InsertHM(fuel, key, dflt, &m *self);
      GetMutRaw(fuel, key, dflt, &m *self)
    } };
  %tail2 }

/-- **The erased borrow-returning chain is ACCEPTED**, where `HashMap.lean`
    pins its verified twin as rejected ("does not have its owed type"). The
    bodies are the same walk; what the erased one does not have is the
    container's comptime invariant component. The probe below says that is
    the difference. -/
example : progOk (hmErasedGmUnder prog defer_check { () }) = true := by native_decide

/-- A stand-in invariant: comptime, trivially true, and DEPENDENT ON THE ARRAY
    VALUE. The dependence is the whole point — `λ C A. Unit` mentions the
    array too, and a container carrying that one is accepted, because
    re-typing `Unit` never has to look at the array. -/
def InvE : Term := prog defer_check {
  λ (C : Nat). λ (A : Array C (List (Σ (k : Nat). Nat))).
    Id (Array C (List (Σ (k : Nat). Nat))) A A }

/-- **Localizing the gap.** `GetMutRawInv` is the accepted `GetMutRaw` above
    with ONE change: its container carries a `Σ0` component whose type is
    `Id … slots slots`. Nothing else moves — same walk, same carve, same
    citation — and the component asserts nothing, so a caller builds it from
    `Refl`.

    It is rejected, with the message `HashMap.lean` pins for its verified
    chain. The audit's complaint names the reason exactly: it recovers the
    payload with the CARVE'S SEGMENTATION still in the slots position
    (`Arr⟨σ ▷ σ, (S Z) ▷ [σ], σ ▷ σ⟩`), and re-typing the tail wants the whole
    array back. §6.1 exempts the sub-place the returned borrow points at, not
    the rest of the parameter.

    So the borrow-returning ops are not blocked by returning a borrow. Two
    controls say so: this container without the array-dependent tail is
    accepted (the chain above), and so is the same op given a proof parameter
    that mentions `*self` (`gmSelfEvProbe`). What blocks them is a comptime
    component whose type needs the array's VALUE. That reproduces
    `HashMap.lean`'s own diagnosis of the gap from the other side, and it is
    the part of the proof overhead that is not measured in lines: with the
    invariant packed, these three ops cannot be written at all today. -/
def gmInvProbe : Term := hmErasedGmUnder prog defer_check {
  fn GetMutRawInv (fuel : Nat, key : Nat, dflt : Nat,
                   self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                     Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). InvE cap slots))
      -> &mut Nat {
    match self {
      Pair(cap, r1) => match r1 {
        Pair(load, r2) => match r2 {
          Pair(nn, r3) => match r3 {
            Pair(slots, HInv) => {
              let c = *cap;
              *cap := c;
              let C0 = c;
              if e : Leb 1 c {
                let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, LebTrueLe 1 c e);
                let Him0 = him;
                let bb = &m (*slots)[i | NatRw (λ (W : Nat). Le (S W) C0)
                  (Mod key C0) i (IdSym Nat i (Mod key C0) Him0)
                  (ModLtN key C0 (LebTrueLe 1 C0 e))];
                WalkVal(fuel, key, dflt, bb)
              } else { &m *nn }
            } } } } } };
  () }

example : progRejects gmInvProbe "does not have its owed type" = true := by
  native_decide

/-- The control for the probe above: a borrow-returning op whose signature
    carries a proof parameter mentioning `*self` is ACCEPTED. Evidence about
    the container is not what the audit objects to — a comptime component
    inside it is. -/
def gmSelfEvProbe : Term := hmErasedGmUnder prog defer_check {
  fn GetMutPinned (fuel : Nat, key : Nat,
                   self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                     Array cap (List (Σ (k : Nat). Nat))),
                   Hin : Id (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                     Array cap (List (Σ (k : Nat). Nat))) (*self) (*self))
      -> &mut Nat {
    GetMutRaw(fuel, key, Z, &m *self) };
  () }

example : progOk gmSelfEvProbe = true := by native_decide

/-- Keys 0, 16, 64 and 80 all reduce to slot 0 at capacity 8, so they chain in
    one bucket. Overwrite key 64's value through `GetMutHM`, then remove key
    64. `HashMap.lean`'s `gmTest1` expectation, unchanged. -/
def eGmTest1 : Term := hmErasedGmUnder prog defer_check {
  let m0 = NewHM(8);
  let b1 = &m m0;
  InsertHM(64, 0, 42, b1);
  let b2 = &m m0;
  InsertHM(64, 16, 18, b2);
  let b3 = &m m0;
  InsertHM(64, 64, 138, b3);
  let b4 = &m m0;
  InsertHM(64, 80, 256, b4);
  let b5 = &m m0;
  let e1 = GetMutHM(64, 64, b5);
  *e1 := 56;
  let b6 = &m m0;
  RemoveHM(64, 64, b6);
  let y = m0;
  () }

example : (runHME eGmTest1 ==
    some (8, 32, 3,
      (List.replicate 8 ([] : List (Nat × Nat))).set 0
        [(0, 42), (16, 18), (80, 256)])) = true := by native_decide

/-- Both arms of the or_insert path: key 5 absent (inserts the default 7, so
    `n` is accounted for) then written through the returned borrow; then key 5
    again, present, written again. `HashMap.lean`'s `gmTest2` expectation,
    unchanged. -/
def eGmTest2 : Term := hmErasedGmUnder prog defer_check {
  let m0 = NewHM(4);
  let b1 = &m m0;
  InsertHM(9, 1, 10, b1);
  let b2 = &m m0;
  let e1 = GetMutOrInsertHM(9, 5, 7, b2);
  *e1 := 9;
  let b3 = &m m0;
  let e2 = GetMutOrInsertHM(9, 5, 7, b3);
  *e2 := 11;
  let y = m0;
  () }

example : (runHME eGmTest2 ==
    some (4, 16, 2, [[], [(1, 10), (5, 11)], [], []])) = true := by native_decide

end Dllbc.Tests.HashMapErased
end
