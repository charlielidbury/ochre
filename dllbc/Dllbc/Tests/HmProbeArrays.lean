import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# HM PROBE — arrays whose payload is STRUCTURED

A viability probe for a planned hashmap flagship: `slots : Array cap (List (Σ k. T))`,
i.e. the Aeneas ICFP'22 case study's shape (buckets = association lists in the slots
of an array). Every existing array test in the tree uses `Array n Nat`; the question
this file answers is what changes when the payload is a list, a pair, or a list of
pairs.

Each section is one probe question. Verdicts are asserted, not narrated — a `= true`
is a WORKS and a `= false` (or a `progRejects` needle) is a FAILS with the error
pinned in the assertion itself.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  LebTrueLe LebFalseGt AddSucc AddZero IdTrans IdCongr IdSym)

namespace Dllbc.Tests.HmProbeArrays

/-- Type-check a closed term against a closed type in the pure seed (as ArraySort's). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000 t

/-! ## A1 — array literals of structured payload

    `ctorSig "Arr"` builds its field telescope as `T` repeated `n` times, generic in
    `T` (Pure.lean ~498), so the question is whether anything downstream is
    Nat-specific. -/

-- (a) An array of LISTS.
example : chkL prog{ Arr(Nil, Cons(1, Nil)) } prog{ Array 2 (List Nat) } = true := by
  native_decide

-- …and it is not vacuous: the payload type is checked elementwise.
example : chkL prog{ Arr(Nil, Cons(True, Nil)) } prog{ Array 2 (List Nat) } = false := by
  native_decide
example : chkL prog{ Arr(Nil, 3) } prog{ Array 2 (List Nat) } = false := by native_decide

-- (b) An array of PAIRS — the association-list entry shape, non-dependently.
example : chkL prog{ Arr(Pair(1, 2), Pair(3, 4)) } prog{ Array 2 (Σ (k : Nat) → Nat) } = true := by
  native_decide
example : chkL prog{ Arr(Pair(1, True), Pair(3, 4)) } prog{ Array 2 (Σ (k : Nat) → Nat) }
    = false := by native_decide

-- (c) THE HASHMAP SHAPE: an array of lists of pairs.
example : chkL prog{ Arr(Nil, Cons(Pair(5, 7), Nil), Cons(Pair(1, 2), Cons(Pair(3, 4), Nil))) }
               prog{ Array 3 (List (Σ (k : Nat) → Nat)) } = true := by native_decide

-- (d) Empty and singleton, and the length index is enforced.
example : chkL prog{ Arr() } prog{ Array 0 (List Nat) } = true := by native_decide
example : chkL prog{ Arr(Nil) } prog{ Array 2 (List Nat) } = false := by native_decide

/-! ## A2 — carving an `&mut (Array n (List Nat))`

    The carve is `docs/design-arrays-slices.md`'s one semantic addition. It splits an
    array VALUE into segments; nothing in the split reads the payload type, so the
    prediction is that it transfers. Both forms the hashmap needs are probed: the
    concrete index (a slot known at write time) and the symbolic one with cited
    evidence (a slot computed by a hash). -/

-- (a) A CONCRETE index into a symbolic-length array of lists — the head peel, which
-- is the shape `splitA` opens with, at a structured payload.
def carveConcL : Term := prog{
  fn CarveConcL (n : Nat, slots : &mut (Array n (List Nat))) -> Unit {
    match n {
      Z => (),
      S(m) => {
        let hd = &m (*slots)[Z ; 1 ; m];
        let tl = &m (*slots)[S Z ; m];
        () } } };
  () }
example : progOk carveConcL = true := by native_decide

-- (b) A SYMBOLIC index with cited evidence — quicksortA's three-way carve, with the
-- payload changed and nothing else. `i` is the hash bucket; `Heq` is the caller's
-- proof that it is in range, in the decomposed form premise (3) wants.
def carveSymL : Term := prog{
  fn CarveSymL (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let hi = &m (*slots)[S i ; j];
    () };
  () }
example : progOk carveSymL = true := by native_decide

-- …and the citation is load-bearing at this payload too, exactly as at `Nat`:
-- drop `LeAdd` and the carve has nothing to select a leaf with.
def carveSymLNoEv : Term := prog{
  fn CarveSymLNoEv (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                    slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j];
    let cell = &m (*slots)[i ; 1 ; j];
    () };
  () }
example : progRejects carveSymLNoEv "may not impose it by refining" = true := by native_decide

-- (c) The full hashmap payload — a list of PAIRS in every slot.
def carveSymEntry : Term := prog{
  fn CarveSymEntry (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                    slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let hi = &m (*slots)[S i ; j];
    () };
  () }
example : progOk carveSymEntry = true := by native_decide

/-! ## A3 — element read and write at a structured payload

    At `Array n Nat` the element read `(*cell)[0]` is a COPY (the index-kind copy the
    ledger keeps). The question the hashmap turns on is what it does when the element
    is a LIST: a copy leaves the slot intact and the take-and-rebuild idiom becomes
    optional; a move leaves a hole that §5.4's audit will refuse unless it is refilled. -/

-- (a) Read a list OUT of a slot and never write it back. If this checks, the element
-- read is a copy at structured payload too, and the slot was never emptied.
def readListNoRefill : Term := prog{
  fn ReadListNoRefill (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                       slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let b = (*cell)[0];
    () };
  () }
example : progRejects readListNoRefill
  "a suspended array has no value of its type" = true := by native_decide

-- (b) A plain write of a structured literal into a slot.
def writeList : Term := prog{
  fn WriteList (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    (*cell)[0] := Cons(Pair(5, 7), Nil);
    () };
  () }
example : progOk writeList = true := by native_decide

-- …and the write is typed: a bare Nat where a list of entries is owed is REFUSED.
def writeListBad : Term := prog{
  fn WriteListBad (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                   slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    (*cell)[0] := 3;
    () };
  () }
example : progOk writeListBad = false := by native_decide

/-- **(c) THE COMPOSITE — `insert`'s core.** Read the bucket out of the slot, cons a
    fresh entry onto it, write it back. This is `Boundaries.pushList`'s take-and-rebuild
    (`let tail = *v; *v := Cons(e, tail)`) with the plain `&mut` replaced by an array
    element, and it is the one statement sequence a hashmap insert cannot do without. -/
def bucketPush : Term := prog{
  fn BucketPush (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                 k : Nat, v : Nat,
                 slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let b = (*cell)[0];
    (*cell)[0] := Cons(Pair(k, v), b);
    () };
  () }
example : progRejects bucketPush "is not owned (it carries a hole)" = true := by native_decide

-- The same at the simpler `List Nat` payload, so a failure above could be localized.
def bucketPushNat : Term := prog{
  fn BucketPushNat (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)), e : Nat,
                    slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let b = (*cell)[0];
    (*cell)[0] := Cons(e, b);
    () };
  () }
example : progRejects bucketPushNat "is not owned (it carries a hole)" = true := by
  native_decide

/-! ### A3 diagnosis — the move is by design, and the REFILL is what is missing

    `indexKindT` (Machine.lean ~511) decides copy-or-move by value shape, and its
    `.ctorApp _ _ => false` line is deliberate: "Data proper (`Cons`-trees, pairs,
    user constructors) MOVES even when marker-free… the calculus keeps Rust's line
    (§2.1)". So the read above is not a bug; it is the documented rule arriving at a
    payload no existing test has.

    What IS surprising is that the refill does not close it. `carveAt`'s degenerate
    short-circuit (Machine.lean ~2126) reads

        if degenerate.isSome && !isIdx then pure ()

    and its own comment says the ownership test is skipped there precisely so that
    "¶2.2's take-and-refill work[s] at a range place, since between the take and the
    refill the segment holds a hole and the ⇐-fill is its one legal successor" — then
    excludes index places, "An INDEX request still has to reach an element, so it
    falls through." Falling through reaches the `!Val.segOwned body` test at ~2139,
    which the holed body fails. Take-and-refill therefore exists at a RANGE place and
    not at an ELEMENT place. -/

-- The Nat control, at the identical carve shape: the read is a copy, so no hole is
-- made and the very same statement pair checks. The payload type is the ONLY variable.
def bucketPushNatCtl : Term := prog{
  fn BucketPushNatCtl (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)), e : Nat,
                       slots : &mut (Array n Nat)) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let b = (*cell)[0];
    (*cell)[0] := S(b);
    () };
  () }
example : progOk bucketPushNatCtl = true := by native_decide

-- The minimal repro, with the read's result UNUSED in the write: it is the hole, not
-- the dependency on `b`, that the write trips over.
def refillAfterMove : Term := prog{
  fn RefillAfterMove (slots : &mut (Array 1 (List Nat))) -> Unit {
    let b = (*slots)[0];
    (*slots)[0] := Nil;
    () };
  () }
example : progRejects refillAfterMove "is not owned (it carries a hole)" = true := by
  native_decide

-- …and the RANGE form of the same take-and-refill, which the comment above says is
-- the exempt one. At width one over a length-one array the take is DEGENERATE — it
-- empties the root rather than holing a leaf — and the refill cannot even find an
-- extent to write against.
def refillRangeWhole : Term := prog{
  fn RefillRangeWhole (slots : &mut (Array 1 (List Nat))) -> Unit {
    let r = (*slots)[Z ; 1];
    (*slots)[Z ; 1] := r;
    () };
  () }
example : progRejects refillRangeWhole "is not an array value (no extent to read)" = true := by
  native_decide

-- A PROPER sub-run of a longer array, so the take holes a leaf instead of the root:
-- this is the exemption the comment describes, and it does hold.
def refillRangePart : Term := prog{
  fn RefillRangePart (slots : &mut (Array 2 (List Nat))) -> Unit {
    let r = (*slots)[Z ; 1];
    (*slots)[Z ; 1] := r;
    () };
  () }
example : progOk refillRangePart = true := by native_decide

-- The range take-and-refill is where a bucket could be REPLACED wholesale — but the
-- value taken is an `Array 1 (List Nat)`, not the list, and an array cannot be matched
-- (`typeCtors` gives `Arr` only at a concrete length, and no program writes `Arr` of a
-- symbolic one). Refilling with a DIFFERENT run therefore needs a literal.
def refillRangeNew : Term := prog{
  fn RefillRangeNew (e : Nat, slots : &mut (Array 2 (List Nat))) -> Unit {
    let r = (*slots)[Z ; 1];
    (*slots)[Z ; 1] := Arr(Cons(e, Nil));
    () };
  () }
example : progOk refillRangeNew = true := by native_decide

-- (d) Can the slot's bucket be borrowed IN PLACE instead — `&m (*cell)[0]` — so a
-- callee could push onto it without the read/rebuild round trip?
def bucketBorrow : Term := prog{
  fn BucketBorrow (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)), e : Nat,
                   slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    let tail = *bb;
    *bb := Cons(e, tail);
    () };
  () }
example : progOk bucketBorrow = true := by native_decide

/-- **THE WORKAROUND, at the hashmap's own payload.** Borrowing the element hands back
    an ordinary `&mut (List (Σ k. Nat))`, and take-and-rebuild through THAT is
    `Boundaries.pushList` verbatim — the borrow never moves the list out of the slot,
    so no hole is ever made and the ownership test the direct form fails never runs.
    This is `insert`'s core, written the way the calculus supports. -/
def bucketBorrowEntry : Term := prog{
  fn BucketBorrowEntry (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                        k : Nat, v : Nat,
                        slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    let tail = *bb;
    *bb := Cons(Pair(k, v), tail);
    () };
  () }
example : progOk bucketBorrowEntry = true := by native_decide

-- And the element borrow may be handed to a CALLEE, which is what makes the bucket
-- operations separable functions rather than one inlined body.
def bucketCallee : Term := prog{
  fn PushEntry (e : (Σ (k : Nat) → Nat), b : &mut (List (Σ (k : Nat) → Nat))) -> Unit {
    let tail = *b;
    *b := Cons(e, tail);
    () };
  fn BucketCallee (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                   k : Nat, v : Nat,
                   slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    PushEntry(Pair(k, v), bb);
    () };
  () }
example : progOk bucketCallee = true := by native_decide

/-! ## A4 — does it EXECUTE?

    Acceptance is half the claim; the other half is that the concrete machine agrees.
    ArraySort §(vi) is the precedent, and its finding is the reason this section is not
    a formality: the executing side found three `Drop-empty` bugs the symbolic side
    could never reach, because a residue σ is never known to be zero symbolically and
    is routinely zero concretely. A bucket push is exactly that kind of program —
    every carve it performs has a residue that is zero in some slot. -/

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

/-- Decode a `List Nat` bucket. -/
def bucketOfV : Nat → Val → Option (List Nat)
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Nil", []), _ => some []
    | some ("Cons", [h, t]), f' + 1 =>
      match natOfV 2000 h, bucketOfV f' t with
      | some x, some xs => some (x :: xs)
      | _, _ => none
    | _, _ => none

/-- Decode a `List (Σ k. Nat)` bucket — the association list itself. -/
def entriesOfV : Nat → Val → Option (List (Nat × Nat))
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Nil", []), _ => some []
    | some ("Cons", [h, t]), f' + 1 =>
      match Val.asCtor? h, entriesOfV f' t with
      | some ("Pair", [a, b]), some xs =>
        match natOfV 2000 a, natOfV 2000 b with
        | some k, some v => some ((k, v) :: xs)
        | _, _ => none
      | _, _ => none
    | _, _ => none

/-- Decode the slot array, elementwise, through whichever bucket decoder applies. -/
def slotsOfV {β : Type} (dec : Val → Option β) : Val → Option (List β)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM dec
    | _ => none

/-- The `List Nat`-payload chain, with its caller spliced in as the tail (ArraySort's
    M28 D3 shape: the program that runs is the program that was checked). -/
def hmChainNat (rest : Term) : Term := prog{
  fn BucketPushA (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)), e : Nat,
                  slots : &mut (Array n (List Nat))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    let tl = *bb;
    *bb := Cons(e, tl);
    () };
  %rest }
example : progOk (hmChainNat prog{ () }) = true := by native_decide

/-- Push `e` into slot `i` of a two-slot array whose buckets start empty, then read
    the owner back. `Refl : Id Nat 2 (Add i (S j))` computes at each concrete `(i, j)`. -/
def pushCaller (i j e : Nat) : Term :=
  hmChainNat (prog{
    let z = Arr(Nil, Nil);
    let b = &m z;
    BucketPushA(2, %(Term.nat i), %(Term.nat j), Refl, %(Term.nat e), b);
    let y = z;
    () })

def runPush (i j e : Nat) : Option (List (List Nat)) :=
  match Dllbc.Tests.S9Diff.runExec (pushCaller i j e) with
  | .ok env => (env.lookup "y").bind (slotsOfV (bucketOfV 2000))
  | .error _ => none

-- Both slots reachable, and the push lands in the RIGHT one — slot 0 has residue 1,
-- slot 1 has residue 0, which is the zero-residue path ArraySort's §(vi) warns about.
example : runPush 0 1 7 == some [[7], []] := by native_decide
example : runPush 1 0 7 == some [[], [7]] := by native_decide

-- The caller type-checks as well as runs, at both indices.
example : progOk (pushCaller 0 1 7) = true := by native_decide
example : progOk (pushCaller 1 0 7) = true := by native_decide

-- Two pushes into the same slot: the second sees the first, so the bucket really is
-- being updated in place rather than rebuilt from the entry value.
def pushTwice : Term := hmChainNat prog{
  let z = Arr(Nil, Nil);
  let b = &m z;
  BucketPushA(2, 1, 0, Refl, 7, b);
  let b2 = &m z;
  BucketPushA(2, 1, 0, Refl, 8, b2);
  let y = z;
  () }
example : progOk pushTwice = true := by native_decide
example : (match Dllbc.Tests.S9Diff.runExec pushTwice with
           | .ok env => (env.lookup "y").bind (slotsOfV (bucketOfV 2000))
           | .error _ => none) == some [[], [8, 7]] := by native_decide

/-- The same at the hashmap's own payload: buckets of key/value pairs. -/
def hmChainEntry (rest : Term) : Term := prog{
  fn InsertAt (n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)), k : Nat, v : Nat,
               slots : &mut (Array n (List (Σ (k : Nat) → Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    let tl = *bb;
    *bb := Cons(Pair(k, v), tl);
    () };
  %rest }
example : progOk (hmChainEntry prog{ () }) = true := by native_decide

def insertCaller : Term := hmChainEntry prog{
  let z = Arr(Nil, Nil, Nil);
  let b = &m z;
  InsertAt(3, 1, 1, Refl, 5, 7, b);
  let b2 = &m z;
  InsertAt(3, 1, 1, Refl, 6, 8, b2);
  let b3 = &m z;
  InsertAt(3, 2, 0, Refl, 9, 1, b3);
  let y = z;
  () }
example : progOk insertCaller = true := by native_decide
example : (match Dllbc.Tests.S9Diff.runExec insertCaller with
           | .ok env => (env.lookup "y").bind (slotsOfV (entriesOfV 2000))
           | .error _ => none)
    == some [[], [(6, 8), (5, 7)], [(9, 1)]] := by native_decide

-- M9's simulation property over the same program: the checking and executing sides
-- agree about it, which is the assertion ArraySort's §(vi.c) makes for quicksortA.
example : Dllbc.Tests.S9Diff.diffV2 insertCaller = true := by native_decide

/-! ## A5 — the fuel-threaded walk over a bucket of PAIRS

    `Boundaries.zeroAll` records why this must carry fuel: `[v]` payload-decrease has
    no recursor form, §9's borrow-mode eliminator is filed rather than built, and §12
    decision 8 blessed fuel-threading instead. `S26Fuel.zeroAllF` is the paid twin at
    `&mut List Nat`. The question here is whether the same shape survives the element
    becoming a pair, since the body must now reborrow THROUGH the pair to reach the
    value field.

    `Std.lenFn` is monomorphic at `List Nat`, so the fuel bound needs its own length
    at this payload — one `elim`, spliced into the signature. -/

def lenEFn : Term := prog{
  λ (L : List (Σ (k : Nat) → Nat)). elim L return (λ (Lm : List (Σ (k : Nat) → Nat)). Nat) {
    Nil => Z,
    Cons (H) (T) Rec => S(Rec) } }

/-- (a) `zeroAllF` with the element a pair: reach the VALUE field of each entry through
    a two-step match (`Cons(hd, tl)` then `hd` as `Pair(kk, vv)`) and zero it. -/
def clearVals : Term := prog{
  fn ClearVals [fuel] (fuel : Nat, v : &mut (List (Σ (k : Nat) → Nat)),
                       Hf : Le (%lenEFn (*v)) fuel) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd { Pair(kk, vv) => { *vv := 0; ClearVals(f2, tl, Hf); () } }
      } } };
  () }
example : progOk clearVals = true := by native_decide

/-! (b) The NESTED pattern is NOT AVAILABLE, and the refusal is at the PARSER, not at
    the checker. Writing the two matches as one —

        Cons(Pair(kk, vv), tl) => match fuel { … }

    — does not compile the Lean file at all:

        error: Dllbc/Tests/HmProbeArrays.lean:501:15: unexpected token '('; expected ')'

    A pattern's arguments are binder names, so a constructor in argument position has
    nowhere to go. It cannot be written as an assertion here for the same reason: a
    parse error is not a term this file could name. The two-step match above is
    therefore FORCED, not a style choice — which is a cost the hashmap pays at every
    site that touches an entry, but a bounded and mechanical one. -/

/-- (c) **`insert_in_list` — the Aeneas case study's own leaf.** Walk the bucket; if a
    key matches, overwrite its value in place; otherwise recurse, and cons a fresh
    entry at the end. It needs everything at once: the two-step reborrow, a COPY read
    of the key field out of a `&mut Nat`, a decidable test on it, an in-place write to
    the sibling field, and a refill at `Nil`. -/
def insertInList : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat) → Nat)),
                          Hf : Le (%lenEFn (*b)) fuel) -> Unit {
    match b {
      Nil => { *b := Cons(Pair(k, v), Nil); () },
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd {
          Pair(kk, vv) => {
            if e : Eqb *kk k { *vv := v; () }
            else { InsertInList(f2, k, v, tl, Hf); () } } }
      } } };
  () }
example : progOk insertInList = true := by native_decide

/-! ## A5' — THE COMPOSITE: the bucket walk called through an array element borrow

    A1–A5 each answer a piece. This is the piece they are for: `hm_insert` = carve the
    slot, borrow the element, hand that borrow to the fuel-threaded list walk. If it
    composes, the flagship is a matter of writing invariants rather than of finding a
    program shape.

    THE ONE THING THAT DOES NOT COMPOSE CLEANLY is the fuel bound. `InsertInList` owes
    `Le (len *b) fuel`, and `*b` is the bucket — which the caller cannot name, because
    it does not exist until the carve inside the body has happened. The bound must
    therefore be stated over ALL buckets and instantiated at the one the carve
    produced, which is what `HfAll` is below. That is a real design constraint on the
    flagship and not a probe artifact: the honest version is an array-level invariant
    (`every bucket is shorter than fuel`) that the carve must be shown to preserve. -/

def hmFullChain (rest : Term) : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat) → Nat)),
                          Hf : Le (%lenEFn (*b)) fuel) -> Unit {
    match b {
      Nil => { *b := Cons(Pair(k, v), Nil); () },
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd {
          Pair(kk, vv) => {
            if e : Eqb *kk k { *vv := v; () }
            else { InsertInList(f2, k, v, tl, Hf); () } } }
      } } };
  fn HmInsert (fuel : Nat, n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
               k : Nat, v : Nat,
               slots : &mut (Array n (List (Σ (k : Nat) → Nat))),
               HfAll : Π (B : List (Σ (k : Nat) → Nat)) → Le (%lenEFn B) fuel) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    -- STAGED, and the staging is forced: `InsertInList(…, bb, HfAll (*bb))` consumes
    -- `bb` as the fourth argument and then reads it for the fifth, which fails with
    -- "readC (⇝): bb#11 holds ⊥ (use-after-move or uninitialized in a comptime read)".
    -- Capitalised, so this is a comptime snapshot — ArraySort's `let A0 = *a` idiom,
    -- arriving here for the same capture-before-consume reason.
    let Hb = HfAll (*bb);
    InsertInList(fuel, k, v, bb, Hb);
    () };
  %rest }
example : progOk (hmFullChain prog{ () }) = true := by native_decide

/-- …and it RUNS. At a concrete slot array the caller can discharge `HfAll` itself,
    because every bucket it built is shorter than the fuel it passes — but only as a
    λ that ignores its argument, which is the same admission the paragraph above makes.
    What the run establishes is that the machine really performs the composite: carve,
    element borrow, cross a call boundary, walk, and write back into the slot. -/
def hmInsertCaller : Term := hmFullChain prog{
  let z = Arr(Nil, Nil, Nil);
  let b1 = &m z;
  HmInsert(4, 3, 1, 1, Refl, 5, 7, b1, λ (B : List (Σ (k : Nat) → Nat)). unit);
  let b2 = &m z;
  HmInsert(4, 3, 1, 1, Refl, 6, 8, b2, λ (B : List (Σ (k : Nat) → Nat)). unit);
  let b3 = &m z;
  HmInsert(4, 3, 1, 1, Refl, 5, 9, b3, λ (B : List (Σ (k : Nat) → Nat)). unit);
  let b4 = &m z;
  HmInsert(4, 3, 2, 0, Refl, 1, 2, b4, λ (B : List (Σ (k : Nat) → Nat)). unit);
  let y = z;
  () }

def hmRun : Option (List (List (Nat × Nat))) :=
  match Dllbc.Tests.S9Diff.runExec hmInsertCaller with
  | .ok env => (env.lookup "y").bind (slotsOfV (entriesOfV 2000))
  | .error _ => none

-- Insert (5,7) then (6,8) into slot 1, then RE-insert key 5 with value 9 — which must
-- OVERWRITE in place rather than prepend, since `insert_in_list` found the key. Then
-- one entry into slot 2. That is the whole hashmap insert, end to end.
example : hmRun == some [[], [(5, 9), (6, 8)], [(1, 2)]] := by native_decide

-- Read that answer slot by slot, because it is the whole claim. Slot 0 was never
-- touched and stayed `Nil`. Slot 1 took (5,7), then (6,8) APPENDED at the tail (the
-- `Nil` refill at the end of the walk), then (5,9) OVERWROTE the head's value field in
-- place — the key was found, so no entry was added. Slot 2 took its one entry. That is
-- `insert_in_list`'s specified behaviour, and the array around it is the same array.

-- The caller checks as well as runs, and the two sides agree about it.
-- THE CALLER RUNS BUT DOES NOT CHECK, and the rejection is the right one. Execution
-- does not verify proofs, so `λ B. unit` gets through the machine; the checker sees
-- that `Le (len B) 4` at a SYMBOLIC `B` is a stuck `listRec` under `Le`, not `Unit`,
-- and refuses the argument. The Π-quantified bound is unprovable — a bucket may be
-- longer than the fuel — so this is the probe admitting its own shortcut, at the
-- boundary where the flagship will have to do the real thing instead.
example : progRejects hmInsertCaller
  "comptime argument" = true := by native_decide

/-! ## A6 — can the missing invariant even be STATED?

    A5' leaves one gap, and it is the flagship's whole remaining design: the fuel bound
    `Le (len *b) fuel` is about a bucket that does not exist until the carve has run, so
    it has to descend from an ARRAY-level invariant instead. `SortedA` is the precedent
    — an `arrRec` fold into `Type` over the cons view — and the question is whether
    `arrRec` is as generic in its element type as `Arr` turned out to be in A1.

    It is: `arrRec` takes the element type as its first argument, and nothing about the
    fold cares that the element is a list. -/

/-- `AllShortA f n a` — every bucket of `a` has at most `f` entries. `SortedA`'s shape
    with the element type changed and `BoundA` replaced by the length bound. -/
def AllShortA : Term := prog{
  λ (F : Nat). λ (N : Nat). λ (A : Array N (List (Σ (k : Nat) → Nat))).
    arrRec (List (Σ (k : Nat) → Nat))
      (λ (M : Nat). λ (B : Array M (List (Σ (k : Nat) → Nat))). Type) Unit
      (λ (K : Nat). λ (H : List (Σ (k : Nat) → Nat)).
       λ (T : Array K (List (Σ (k : Nat) → Nat))). λ (Ih : Type).
        Σ (Hh : Le (%lenEFn H) F) → Ih) N A }

-- It COMPUTES on a concrete slot array: three buckets of sizes 0, 1, 2 are all ≤ 2, and
-- the inhabitant is the nested unit pair the fold builds.
example : chkL prog{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog{ %AllShortA 2 3 Arr(Nil, Cons(Pair(5, 7), Nil),
                                        Cons(Pair(1, 2), Cons(Pair(3, 4), Nil))) }
    = true := by native_decide

-- …and it is not vacuous: the same array does not satisfy the bound at 1, because the
-- third bucket has two entries.
example : chkL prog{ Pair(unit, Pair(unit, Pair(unit, unit))) }
               prog{ %AllShortA 1 3 Arr(Nil, Cons(Pair(5, 7), Nil),
                                        Cons(Pair(1, 2), Cons(Pair(3, 4), Nil))) }
    = false := by native_decide

-- It is STUCK at an opaque payload, exactly as `SortedA Z` is (there is no η at length
-- zero), which is what makes it a real predicate rather than a computation.
example : (Pure.nf 2000 prog{ %AllShortA 2 Z Arr() } == .const "Unit") = true := by
  native_decide

-- And it can be carried in a signature over a symbolic array — the form the flagship's
-- `HmInsert` would take.
def hmInsertInv : Term := prog{
  fn HmInsertInv (fuel : Nat, n : Nat, i : Nat, j : Nat, Heq : Id Nat n (Add i (S j)),
                  k : Nat, v : Nat,
                  slots : &mut (Array n (List (Σ (k : Nat) → Nat))),
                  Hinv : %AllShortA fuel n (*slots)) -> Unit {
    let lo = &m (*slots)[Z ; i ; S j | LeAdd i (S j) | Heq];
    let cell = &m (*slots)[i ; 1 ; j];
    let bb = &m (*cell)[0];
    () };
  () }
example : progOk hmInsertInv = true := by native_decide

end Dllbc.Tests.HmProbeArrays
end
