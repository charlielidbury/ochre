import Dllbc.ElabCheck
import Dllbc.Tests.HashMap

/-!
# The hashmap flagship's EXECUTING layer

The runtime differential (decoders, the trusted Lean-side model, the callers)
and the borrow-returning ops' executing chain — split from `HashMap.lean` so
that iterating on the verified chain does not re-run the cap-32 concrete
executions (the interpreter evaluates the comptime layer too, and Aeneas'
test1 at capacity 32 is the module's dominant build cost).
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  LebTrueLe LebFalseGt AddSucc AddZero AddComm AddAssoc IdTrans IdCongr IdSym
  NatRw LeZeroEq LeAntisym BoolFT BoolTF Znots SInj Pred
  LeRwL LeRwR LeAddMonoL EqbRefl
  NextR NextC NextQ ModC Mod DivC Div ModLtN ModDec
  Mul MulSucc LeAddMonoR LeAddMono LeMulR
  LeLebTrue EqbTrueEq EqbSym IfDec LedgerGrow)

namespace Dllbc.Tests.HashMap


/-! ## (xvi) The S1 EXECUTING DIFFERENTIAL

    The same declarations the checker accepted, run on concrete maps and
    compared against a trusted Lean-side reference (`runQsA`-style). The
    callers here are runtime-only: their proof arguments are `unit`, which the
    machine ignores — E2E rule, runs-to-X assertions only. (A checker-accepted
    caller needs the size facts threaded through the ensures; S1's `Hroom`
    additionally needs cap/load knowledge New's fixed ensures does not export,
    which S2's resize removes — so the checked caller ships with S2.) -/

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

/-- Decode a concrete pack: (cap, load, n, buckets). The invariant component is
    ignored (erased in spirit; the interpreter carries it). -/
def hmOfV (v : Val) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) := do
  let (c, r1) ← pairOfV v
  let (l, r2) ← pairOfV r1
  let (n, r3) ← pairOfV r2
  let (s, _) ← pairOfV r3
  let cap ← natOfV 4000 c
  let load ← natOfV 4000 l
  let nn ← natOfV 4000 n
  let bs ← slotsOfV s
  pure (cap, load, nn, bs)

/-- The trusted model: overwrite in place on hit, append at the bucket's end
    on miss — `insert_in_list`'s specified behavior. -/
def modelInsB (k v : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(k, v)]
  | (k2, v2) :: t => if k2 == k then (k, v) :: t else (k2, v2) :: modelInsB k v t

def modelIns (cap : Nat) (bs : List (List (Nat × Nat))) (k v : Nat)
    : List (List (Nat × Nat)) :=
  bs.mapIdx (fun i b => if i == k % cap then modelInsB k v b else b)

def modelRun (cap : Nat) (ops : List (Nat × Nat))
    : Nat × List (List (Nat × Nat)) :=
  ops.foldl (fun (acc : Nat × List (List (Nat × Nat))) (kv : Nat × Nat) =>
      let present := (acc.2.getD (kv.1 % cap) []).any (fun e => e.1 == kv.1)
      ((if present then acc.1 else acc.1 + 1),
       modelIns cap acc.2 kv.1 kv.2))
    (0, List.replicate cap [])

/-- `runProgram` with a caller-chosen step budget: a cap-32 concrete run
    evaluates the comptime layer too (the interpreter tax) and blows the
    default 1000-step fuel. -/
def runProgramF (fuel : Nat) (t : Term) : Except String Env :=
  match (do let _ ← readR fuel (atBoundary t); endScope fuel).run
      { initSt with executing := true } with
  | .ok _ st => .ok (canonicalize st.env)
  | .error e _ => .error e

def runHM (t : Term) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) :=
  match runProgramF 2000000 t with
  | .ok env => (env.lookup "y").bind hmOfV
  | .error _ => none

/-- Five inserts at cap 4: keys 5, 1, 9 all collide in slot 1 (the middle one
    walks past a miss), key 5 re-inserted mid-sequence must OVERWRITE in place,
    key 2 lands alone. -/
def s1RunCaller : Term := hmS1Under newRetHonest insRetHonest remRetHonest prog defer_check {
  let Pair(m0, Ev0) = NewHM(4, unit);
  let b1 = &m m0;
  InsertHM(9, 5, 70, b1, unit);
  let b2 = &m m0;
  InsertHM(9, 1, 10, b2, unit);
  let b3 = &m m0;
  InsertHM(9, 5, 71, b3, unit);
  let b4 = &m m0;
  InsertHM(9, 9, 90, b4, unit);
  let b5 = &m m0;
  InsertHM(9, 2, 20, b5, unit);
  let y = m0;
  () }

def s1Expected : Nat × List (List (Nat × Nat)) :=
  modelRun 4 [(5, 70), (1, 10), (5, 71), (9, 90), (2, 20)]

-- The fifth distinct-key insert trips the ledger (5·4 > 16), so the map
-- RESIZES to cap 8 and rehashes: 5 leaves the 1/9 collision chain, order of
-- the survivors preserved by the move fold.
example : (runHM s1RunCaller ==
    some (8, 32, 4, [[], [(1, 10), (9, 90)], [(2, 20)], [], [], [(5, 71)], [], []]))
    = true := by native_decide

-- …and the pre-resize model still pins the cap-4 semantics (two-sided).
example : (s1Expected == (4, [[], [(5, 71), (1, 10), (9, 90)], [(2, 20)], []]))
    = true := by native_decide

/-- The insert sequence followed by three removes: key 5 (bucket-1 head, a
    hit), key 7 (a miss — nothing changes), key 1 (mid-bucket unlink). -/
def s1RemCaller : Term := hmS1Under newRetHonest insRetHonest remRetHonest prog defer_check {
  let Pair(m0, Ev0) = NewHM(4, unit);
  let b1 = &m m0;
  InsertHM(9, 5, 70, b1, unit);
  let b2 = &m m0;
  InsertHM(9, 1, 10, b2, unit);
  let b3 = &m m0;
  InsertHM(9, 5, 71, b3, unit);
  let b4 = &m m0;
  InsertHM(9, 9, 90, b4, unit);
  let b5 = &m m0;
  InsertHM(9, 2, 20, b5, unit);
  let b6 = &m m0;
  RemoveHM(9, 5, b6, unit);
  let b7 = &m m0;
  RemoveHM(9, 7, b7, unit);
  let b8 = &m m0;
  RemoveHM(9, 1, b8, unit);
  let y = m0;
  () }

example : (runHM s1RemCaller ==
    some (8, 32, 2, [[], [(9, 90)], [(2, 20)], [], [], [], [], []]))
    = true := by native_decide

/-- From capacity 1 (threshold 0), four inserts force THREE doubling resizes:
    1 → 2 → 4 → 8, every entry re-slotted by the move fold each time. -/
def s1GrowCaller : Term := hmS1Under newRetHonest insRetHonest remRetHonest prog defer_check {
  let Pair(m0, Ev0) = NewHM(1, unit);
  let b1 = &m m0;
  InsertHM(9, 1, 10, b1, unit);
  let b2 = &m m0;
  InsertHM(9, 2, 20, b2, unit);
  let b3 = &m m0;
  InsertHM(9, 3, 30, b3, unit);
  let b4 = &m m0;
  InsertHM(9, 4, 40, b4, unit);
  let y = m0;
  () }

example : (runHM s1GrowCaller ==
    some (8, 32, 4, [[], [(1, 10)], [(2, 20)], [(3, 30)], [(4, 40)], [], [], []]))
    = true := by native_decide

-- The empty map runs and decodes: all buckets Nil, n = 0, load = 4·cap.
def s1NewCaller : Term := hmS1Under newRetHonest insRetHonest remRetHonest prog defer_check {
  let Pair(m0, Ev0) = NewHM(3, unit);
  let y = m0;
  () }
example : (runHM s1NewCaller == some (3, 12, 0, [[], [], []])) = true := by
  native_decide




/-! ## (xix) GetMut / GetMutOrInsert — executing, with the check status pinned

    The ops in the shape the wall analysis selects: total or_insert-style walk,
    index-place element borrow, presence via a Bool walk, GetMutOrInsert as
    contains-then-Insert-then-walk so the packed accounting stays TRUE at
    runtime (the absent-key insert goes through the verified InsertHM). The
    extended chain is progRejects-pinned (the audit wall above) and exercised
    by the executing differential below — Aeneas' own test1. -/

def hmGmUnder (tail2 : Term) : Term :=
  hmS1Under newRetHonest insRetHonest remRetHonest prog{
  fn WalkVal [fuel] (fuel : Nat, key : Nat, dflt : Nat,
                     b : &mut (List (Σ (k : Nat). Nat))) -> &mut Nat {
    match fuel {
      Z => { *b := Cons(Pair(key, dflt), Nil);
             match b { Nil => (), Cons(Pair(kk, vv), tl) => &m *vv } },
      S(f2) => match b {
        Nil => { *b := Cons(Pair(key, dflt), Nil);
                 match b { Nil => (), Cons(Pair(kk, vv), tl) => &m *vv } },
        Cons(Pair(kk, vv), tl) =>
          if e : Eqb *kk key { &m *vv } else { WalkVal(f2, key, dflt, &m *tl) }
      } } };
  fn GetMutRaw (fuel : Nat, key : Nat, dflt : Nat,
                self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))).
                    HMInvT cap load n slots)) -> &mut Nat {
    let HLe1 = PackLe1 (*self);
    match self {
      Pair(cap, r1) => match r1 {
        Pair(load, r2) => match r2 {
          Pair(nn, r3) => match r3 {
            Pair(slots, HInv) => {
              let c = *cap;
              *cap := c;
              let C0 = c;
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, HLe1);
              let Him0 = him;
              let bb = &m (*slots)[i | NatRw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSym Nat i (Mod key C0) Him0)
                (ModLtN key C0 HLe1)];
              WalkVal(fuel, key, dflt, bb)
            } } } } } };
  fn GetMutHM (fuel : Nat, key : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))).
                   HMInvT cap load n slots),
               Hin : Id Bool (HitHM key (*self)) True) -> &mut Nat {
    GetMutRaw(fuel, key, Z, &m *self) };
  fn ContainsWalk [fuel] (fuel : Nat, key : Nat,
                          b : &mut (List (Σ (k : Nat). Nat))) -> Bool {
    match fuel {
      Z => False,
      S(f2) => match b {
        Nil => False,
        Cons(Pair(kk, vv), tl) =>
          if e : Eqb *kk key { True } else { ContainsWalk(f2, key, &m *tl) }
      } } };
  fn ContainsHM (fuel : Nat, key : Nat,
                 self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                   Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))).
                     HMInvT cap load n slots)) -> Bool {
    let HLe1 = PackLe1 (*self);
    match self {
      Pair(cap, r1) => match r1 {
        Pair(load, r2) => match r2 {
          Pair(nn, r3) => match r3 {
            Pair(slots, HInv) => {
              let c = *cap;
              *cap := c;
              let C0 = c;
              let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, HLe1);
              let Him0 = him;
              let bb = &m (*slots)[i | NatRw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSym Nat i (Mod key C0) Him0)
                (ModLtN key C0 HLe1)];
              ContainsWalk(fuel, key, bb)
            } } } } } };
  fn GetMutOrInsertHM (fuel : Nat, key : Nat, dflt : Nat,
                       self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                         Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))).
                           HMInvT cap load n slots),
                       Hfuel : Le (S (S (SizeHM (*self)))) fuel) -> &mut Nat {
    if ContainsHM(fuel, key, &m *self) {
      GetMutRaw(fuel, key, dflt, &m *self)
    } else {
      InsertHM(fuel, key, dflt, &m *self, Hfuel);
      GetMutRaw(fuel, key, dflt, &m *self)
    } };
  %tail2 }

-- The extended chain's check status, pinned with the audit's needle.
example : progRejects (hmGmUnder prog defer_check { () }) "does not have its owed type"
    = true := by native_decide

/-- AENEAS' test1 (icfp22/hashmap.rs), the differential the doc fixes: keys
    that all collide in slot 0 by construction and exceed the capacity;
    overwrite via the get_mut path; remove; re-check the survivors.

    It used to be cap 32 with keys 0/128/1024/1056 to line up with Aeneas
    verbatim, but numerals are unary, and that run cost 970s of every fresh
    build (~16 of its 24 minutes, profiled 2026-08-20: the normalizer's spine
    walk over the giant S-chains). Cap 8 with keys 0/16/64/80 is the same test
    — same collision structure, same op sequence — at 1.5s; lining up with
    Aeneas' literal constants will only be possible once we have non-unary
    numbers. -/
def gmTest1 : Term := hmGmUnder prog defer_check {
  let Pair(m0, Ev0) = NewHM(8, unit);
  let b1 = &m m0;
  InsertHM(64, 0, 42, b1, unit);
  let b2 = &m m0;
  InsertHM(64, %(Term.nat 16), 18, b2, unit);
  let b3 = &m m0;
  InsertHM(64, %(Term.nat 64), %(Term.nat 138), b3, unit);
  let b4 = &m m0;
  InsertHM(64, %(Term.nat 80), %(Term.nat 256), b4, unit);
  let b5 = &m m0;
  let e1 = GetMutHM(64, %(Term.nat 64), b5, unit);
  *e1 := 56;
  let b6 = &m m0;
  RemoveHM(64, %(Term.nat 64), b6, unit);
  let y = m0;
  () }

example : (runHM gmTest1 ==
    some (8, 32, 3,
      (List.replicate 8 ([] : List (Nat × Nat))).set 0
        [(0, 42), (16, 18), (80, 256)])) = true := by native_decide

/-- The or_insert path, both arms: key 5 absent (inserts default 7 through the
    verified InsertHM, so n is accounted), then written through the returned
    borrow; key 5 again (present — no insert), written again. -/
def gmTest2 : Term := hmGmUnder prog defer_check {
  let Pair(m0, Ev0) = NewHM(4, unit);
  let b1 = &m m0;
  InsertHM(9, 1, 10, b1, unit);
  let b2 = &m m0;
  let e1 = GetMutOrInsertHM(9, 5, 7, b2, unit);
  *e1 := 9;
  let b3 = &m m0;
  let e2 = GetMutOrInsertHM(9, 5, 7, b3, unit);
  *e2 := 11;
  let y = m0;
  () }

example : (runHM gmTest2 ==
    some (4, 16, 2, [[], [(1, 10), (5, 11)], [], []])) = true := by native_decide


end Dllbc.Tests.HashMap
end
