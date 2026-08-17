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

/-- The checker's message for a rejected program — probe scaffolding. -/
def hmMsg (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "OK" | .error e => e

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
example : progOk readListNoRefill = false := by native_decide
#eval hmMsg readListNoRefill

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
example : progOk bucketPush = false := by native_decide
#eval hmMsg bucketPush

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
example : progOk bucketPushNat = false := by native_decide
#eval hmMsg bucketPushNat

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

end Dllbc.Tests.HmProbeArrays
end
