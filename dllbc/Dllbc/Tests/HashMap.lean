import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship — a verified, resizable, in-place hashmap

`docs/13-hashmap-flagship.md` is the problem statement; this is the artifact. The
shape mirrors the Aeneas ICFP'22 case study (`competitors/aeneas-hashmap/`) closely
enough that the two can be compared side by side: slots are an array of
association-list buckets, the hash is the identity, the slot is `Mod key cap`, the
load factor is 4/5, and a full table doubles its capacity and re-inserts everything.

**The invariant is packed in the type.** A `HashMap` value cannot exist broken, so
every operation's invariant-preservation proof is just returning a well-typed pack —
and, per `HmProbeGetmut`'s G5, it survives even the opaque group ends that lose every
functional fact, because §6.1 re-mints a caller's payload as a fresh σ AT THE DECLARED
TYPE and inhabiting the type IS the invariant.

The file reads bottom-up: the pure vocabulary the specs are written in, then the
invariant library, then the programs, then the twins and the executing differential.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL LeRwL LeRwR
  LebTrueLe LebFalseGt AddSucc AddZero AddAssoc AddComm IdTrans IdCongr IdSym Znots SInj
  EqbRefl EqbGtFalse EqbLtFalse ModLtN ModLtNTy ModDec ModDecTy ModCLt ModCLtTy
  StepInv StepInvTy NatRw NatRwTy LeZeroEq LeZeroEqTy)

namespace Dllbc.Tests.HashMap

/-- Type-check a closed term against a closed type in the pure seed (as ArraySort's). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- The same, keeping the message — for pinning a rejection while developing. -/
def chkLMsg (tm ty : Term) : String :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

def pv (t : Term) : Term := Pure.nf 200000 t

def chkProg (t : Term) : String :=
  match checkProgram t prog{ Unit } with | .ok _ => "ACCEPTED" | .error e => "REJECTED: " ++ e

/-! ## 1. The `Option`, as `Σ (b : Bool). OptP b T`

    The kernel's constructor basis is fixed (Unit/Bool/Nat/List/Σ/Array/Id) and has no
    `Option`; `hm-option-kernel` is the parked road not taken. The encoding is a
    Bool-tagged pair whose PAYLOAD TYPE is computed from the tag by an ordinary
    type-valued `boolRec` — so `Pair(True, unit)` and `Pair(False, 5)` are both
    ill-typed, which is what makes it an Option rather than a pair with a flag.

    `Some`/`None`/`Opt` are comptime definitions, not constructors, and that is the
    whole ergonomic claim: a spec reads `Id (Opt Nat) (FindHM q hm) (Some v)`. -/

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

def Opt : Term := prog{ λ (T : Type). Σ (b : Bool). OptP b T }
def Some : Term := prog{ λ (T : Type). λ (V : T). Pair(True, V) }
def None : Term := prog{ λ (T : Type). Pair(False, unit) }

-- The tag really does control the payload's type, in both directions.
example : chkL prog{ Some Nat 5 } prog{ Opt Nat } = true := by native_decide
example : chkL prog{ None Nat } prog{ Opt Nat } = true := by native_decide
example : chkL prog{ Pair(True, unit) } prog{ Opt Nat } = false := by native_decide
example : chkL prog{ Pair(False, 5) } prog{ Opt Nat } = false := by native_decide

-- …and `Id` at the `Opt` type separates the three interesting cases.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (Some Nat 5) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (Some Nat 6) } = false := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (Some Nat 5) (None Nat) } = false := by
  native_decide

-- The payload type is a parameter, so the encoding survives a hashmap generic in `V`.
example : chkL prog{ Some (List Nat) Cons(1, Nil) } prog{ Opt (List Nat) } = true := by
  native_decide

/-! ## 2. Entries and buckets

    An entry is `Σ (k : Nat). Nat` — a key beside its value — and a bucket is a list of
    them, which is `AList<T>` in the Rust and `list (usize × T)` in the F*.

    These are Lean-level `Term`s spliced by name into `prog{ … }`: `resolveName`'s raw
    fallthrough answers a Lean identifier for any name the surface does not otherwise
    know, so `Entry` and `Bucket` read as ordinary vocabulary at every use site while
    being written once here. -/

def Entry : Term := prog{ Σ (k : Nat). Nat }
def Bucket : Term := prog{ List (Σ (k : Nat). Nat) }

/-! ### The bucket layer, and the one elaborator change this file rests on

    Every function below recurses over a `List (Σ (k : Nat). Nat)`. Until this branch
    the SURFACE's `elim` wrote its list element type as the literal `Nat` in the three
    places `listRec` needs it, so an `elim` over a bucket checked only when the
    recursor spine was written out by hand — five lines instead of three, at every
    bucket function and every induction over one. `Uni.elabUElim` now reads the
    element type out of the motive's binder type, exactly as its `Pair` branch twenty
    lines below has always read `A`/`B` out of `Σ (y : A). B`. It is an ELABORATOR
    change, not a kernel one: the kernel's `listRec` rule took `A` and built `List A`
    from it all along, and whatever the sugar emits the kernel still checks. -/

/-- `LenE b` — a bucket's length. `Std.lenFn` is monomorphic at `List Nat`. -/
def LenE : Term := prog{
  λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

/-- `FindL q b` — look `q` up in one bucket. The association-list model, and the leaf
    of everything this file specifies. -/
def FindL : Term := prog{
  λ (Q : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Opt Nat) {
      Nil => None Nat,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Opt Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bz : Bool). Opt Nat) {
              True => Some Nat V2,
              False => Rec } } } }

/-- `InsL k v b` — the bucket model of `insert_in_list`: overwrite in place if the key
    is present, otherwise append a fresh entry at the END. The key test is written
    `Eqb K2 K` (entry key first) because that is the order the PROGRAM's `if e : Eqb
    *kk k` produces, and a spec whose test is the other way round would need a
    symmetry lemma at every site to say the same thing. -/
def InsL : Term := prog{
  λ (K : Nat). λ (V : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Cons(Pair(K, V), Nil),
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb K2 K) return (λ (Bz : Bool). List (Σ (k : Nat). Nat)) {
              True => Cons(Pair(K2, V), T),
              False => Cons(Pair(K2, V2), Rec) } } } }

/-- `RemL k b` — drop the first entry whose key is `k`. -/
def RemL : Term := prog{
  λ (K : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Nil,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb K2 K) return (λ (Bz : Bool). List (Σ (k : Nat). Nat)) {
              True => T,
              False => Cons(Pair(K2, V2), Rec) } } } }

/-! ### They compute -/

def b0 : Term := prog{ Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)) }

example : chkL b0 Bucket = true := by native_decide
example : (pv prog{ LenE %b0 }).natOf? == Option.some 2 := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %b0) (Some Nat 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 9 %b0) (None Nat) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindL 3 %b0) (Some Nat 10) } = false := by
  native_decide

-- `InsL` overwrites in place (the key is present) …
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (InsL 3 99 %b0)
           Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide
-- … and appends at the tail (the key is absent), which is `insert_in_list`'s own shape.
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (InsL 5 50 %b0)
           Cons(Pair(1, 10), Cons(Pair(3, 30), Cons(Pair(5, 50), Nil))) } = true := by
  native_decide
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (RemL 1 %b0) Cons(Pair(3, 30), Nil) } = true := by
  native_decide

/-! ## 3. The invariant library

    Three array-level predicates, all `arrRec` folds in `SortedA`'s shape with the
    element type changed from `Nat` to a bucket. `arrRec` takes its element type as an
    argument, so nothing about the fold cares that an element is a list.

    `SlotsOk` is the one with a wrinkle. "Every entry in slot `i` hashes to `i`" needs
    the slot's INDEX, and an `arrRec` fold knows only the remaining length. So the
    motive returns `Π (Iz : Nat) → Type` and the index is threaded down the spine —
    `SplitAL`'s own device for its skip count, reused for exactly the reason it was
    invented. -/

/-- `BucketAt c i b` — every entry in `b` has `Mod key c = i`. -/
def BucketAt : Term := prog{
  λ (C : Nat). λ (I : Nat). λ (B : List (Σ (k : Nat). Nat)).
    elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Σ (Hh : Id Nat (Mod K2 C) I). Rec } } }

/-- `SlotsOk c i0 n a` — the slots of `a`, numbered from `i0`, are each well-hashed. -/
def SlotsOk : Term := prog{
  λ (C : Nat). λ (I0 : Nat). λ (N : Nat). λ (A : Array N (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (M : Nat). λ (Bz : Array M (List (Σ (k : Nat). Nat))). Π (Iz : Nat) → Type)
      (λ (Iz : Nat). Unit)
      (λ (M : Nat). λ (H : List (Σ (k : Nat). Nat)).
       λ (T : Array M (List (Σ (k : Nat). Nat))). λ (Ih : Π (Iz : Nat) → Type).
        λ (Iz : Nat). Σ (Hh : BucketAt C Iz H). Ih (S Iz))
      N A I0 }

/-- `SizeA n a` — the total number of entries across every bucket. This is the clause
    that lets a CALLER name a fuel bound without reaching into a bucket: `n` is the
    entry count, so `n` bounds every individual bucket's length. -/
def SizeA : Term := prog{
  λ (N : Nat). λ (A : Array N (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (M : Nat). λ (Bz : Array M (List (Σ (k : Nat). Nat))). Nat) Z
      (λ (M : Nat). λ (H : List (Σ (k : Nat). Nat)).
       λ (T : Array M (List (Σ (k : Nat). Nat))). λ (Ih : Nat). Add (LenE H) Ih)
      N A }

/-! ### The invariant, and the container that packs it

    `HMInv`'s four clauses are the problem statement's, in order: the capacity is
    positive, every slot is well-hashed, `n` is the entry count, and `load` is the 4/5
    threshold ledger for `cap`.

    The container puts the slots array and the invariant in a `Σ0`, so the PROOF is
    the erased half and the array is the runtime half. A `HMap` value therefore cannot
    exist broken: every operation's invariant-preservation obligation is discharged by
    returning a well-typed pack, and there is no separate "the invariant still holds"
    conjunct anywhere in this file. -/

def HMInv : Term := prog{
  λ (C : Nat). λ (L : Nat). λ (N : Nat). λ (Sl : Array C (List (Σ (k : Nat). Nat))).
    Σ (Hc : Le (S Z) C).
    Σ (Hs : SlotsOk C Z C Sl).
    Σ (Hn : Id Nat N (SizeA C Sl)).
      Id Nat L (Div (Mul C 4) 5) }

/-- The container. Named `HMapT` rather than `HashMap` because this namespace is
    already called `HashMap` and Lean would resolve the bare name to it. -/
def HMapT : Term := prog{
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInv cap load n slots }

/-- The pack's eliminator, written once so nothing else has to spell the four nested
    motives. `T` is a comptime type parameter — a `Π (T : Type)` telescope, which is
    how `IdCongr` already takes its type arguments. -/
def HmRec : Term := prog{
  λ (T : Type).
  λ (F : Π (C : Nat) → Π (L : Nat) → Π (N : Nat) →
         Π (Sl : Array C (List (Σ (k : Nat). Nat))) → HMInv C L N Sl → T).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInv cap load n slots).
    elim Hm return (λ (Hz : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInv cap load n slots). T) {
      Pair (C) (R1) =>
        elim R1 return (λ (R1z : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array C (List (Σ (k : Nat). Nat))). HMInv C load n slots). T) {
          Pair (L) (R2) =>
            elim R2 return (λ (R2z : Σ (n : Nat).
                Σ0 (slots : Array C (List (Σ (k : Nat). Nat))). HMInv C L n slots). T) {
              Pair (N) (R3) =>
                elim R3 return (λ (R3z : Σ0 (slots : Array C (List (Σ (k : Nat). Nat))).
                    HMInv C L N slots). T) {
                  Pair (Sl) (Hi) => F C L N Sl Hi } } } } }

/-! ## 4. The spec functions

    `FindHM` is the map's mathematical VIEW: look the key up in the bucket its hash
    selects. `FindIns`/`FindRem` are the model UPDATES the operations are specified
    against — pure functions of the entry state, so that an operation's whole
    functional claim is one pointwise equation between the exit view and the model
    update of the entry view. -/

/-! ### Selecting a slot: `AgetB`, and why the kernel's `aget` cannot be the spec

    The obvious spelling of "the bucket at index `i`" is the kernel's `aget`, and it
    is the wrong one — not for taste but because it does not COMPUTE where a proof
    needs it to. `Pure.whnfN`'s `aget` rule fires only when the index is a concrete
    numeral AND the array is a literal `Arr`; there is no rule taking
    `aget (S m) (S i) (acons m x t)` to `aget m i t`. So `aget` at a symbolic index
    into an `acons`/`arrCat` spine — which is exactly what a carve leaves behind — is
    inert, and every lemma one would want about it is not merely unproven but
    unstatable-as-provable: there is no eliminator for a stuck `aget`.

    `AgetB` is the same function written as an `arrRec` fold with the index threaded
    down the spine, `SlotsOk`'s device again. `arrRec` DOES fire on an `acons` head, so
    `AgetB (S m) (acons m x t) (S i)` reduces to `AgetB m t i` definitionally, and the
    lemmas below are ordinary inductions. Out of range it answers `Nil`, which makes it
    total and saves every caller a bound. -/

def AgetB : Term := prog{
  λ (N : Nat). λ (A : Array N (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (M : Nat). λ (Bz : Array M (List (Σ (k : Nat). Nat))).
        Π (Iz : Nat) → List (Σ (k : Nat). Nat))
      (λ (Iz : Nat). Nil)
      (λ (M : Nat). λ (H : List (Σ (k : Nat). Nat)).
       λ (T : Array M (List (Σ (k : Nat). Nat))).
       λ (Ih : Π (Iz : Nat) → List (Σ (k : Nat). Nat)). λ (Iz : Nat).
        elim Iz return (λ (Izz : Nat). List (Σ (k : Nat). Nat)) {
          Z => H,
          S (I') Rec => Ih I' })
      N A }

def FindHM : Term := prog{
  λ (Q : Nat). λ (Hm : HMapT).
    HmRec (Opt Nat)
      (λ (C : Nat). λ (L : Nat). λ (N : Nat).
       λ (Sl : Array C (List (Σ (k : Nat). Nat))). λ (Hi : HMInv C L N Sl).
         FindL Q (AgetB C Sl (Mod Q C))) Hm }

def SizeHM : Term := prog{
  λ (Hm : HMapT).
    HmRec Nat
      (λ (C : Nat). λ (L : Nat). λ (N : Nat).
       λ (Sl : Array C (List (Σ (k : Nat). Nat))). λ (Hi : HMInv C L N Sl). N) Hm }

/-- `Some`-ness as a Boolean, so the size accounting can be a spec FUNCTION rather
    than a conditional Π (the problem statement's requirement). -/
def IsNoneO : Term := prog{
  λ (T : Type). λ (O : Σ (b : Bool). OptP b T).
    elim O return (λ (Oz : Σ (b : Bool). OptP b T). Bool) {
      Pair (Bb) (Pp) =>
        elim Bb return (λ (Bz : Bool). Bool) { True => False, False => True } } }

def PredN : Term := prog{
  λ (N : Nat). elim N return (λ (Nz : Nat). Nat) { Z => Z, S (M) Rec => M } }

/-- The model update for insert: `Some v` at the inserted key, the old answer
    everywhere else. This one equation subsumes Aeneas' separate "found" and "frame"
    conjuncts, because it is TOTAL in the query. -/
def FindIns : Term := prog{
  λ (Q : Nat). λ (K : Nat). λ (V : Nat). λ (Hm : HMapT).
    elim (Eqb Q K) return (λ (Bz : Bool). Opt Nat) {
      True => Some Nat V,
      False => FindHM Q Hm } }

def FindRem : Term := prog{
  λ (Q : Nat). λ (K : Nat). λ (Hm : HMapT).
    elim (Eqb Q K) return (λ (Bz : Bool). Opt Nat) {
      True => None Nat,
      False => FindHM Q Hm } }

/-- The size after an insert: bumped exactly when the key was absent. -/
def SizeIns : Term := prog{
  λ (K : Nat). λ (Hm : HMapT).
    elim (IsNoneO Nat (FindHM K Hm)) return (λ (Bz : Bool). Nat) {
      True => S(SizeHM Hm),
      False => SizeHM Hm } }

/-- The size after a remove: decremented exactly when the key was present. -/
def SizeRem : Term := prog{
  λ (K : Nat). λ (Hm : HMapT).
    elim (IsNoneO Nat (FindHM K Hm)) return (λ (Bz : Bool). Nat) {
      True => SizeHM Hm,
      False => PredN (SizeHM Hm) } }

/-! ### The vocabulary is inhabited, computes, and is not vacuous

    A two-slot map holding `4 ↦ 40` in slot 0 and `3 ↦ 30` in slot 1. Its load ledger
    is `Div (Mul 2 4) 5 = 1`, its entry count is 2, and each of the four invariant
    clauses is discharged by a value written out here — which is worth doing once at a
    concrete map, because it is the shape every operation's exit pack has. -/

def sl2 : Term := prog{ Arr(Cons(Pair(4, 40), Nil), Cons(Pair(3, 30), Nil)) }

/-- `SlotsOk`'s inhabitant is one `Refl` per entry, nested down the spine. -/
def sok2 : Term := prog{ Pair(Pair(Refl, unit), Pair(Pair(Refl, unit), unit)) }
def inv2 : Term := prog{ Pair(unit, Pair(%sok2, Pair(Refl, Refl))) }
def map2 : Term := prog{ Pair(2, Pair(1, Pair(2, Pair(%sl2, %inv2)))) }

example : chkL sl2 prog{ Array 2 (List (Σ (k : Nat). Nat)) } = true := by native_decide
example : chkL sok2 prog{ SlotsOk 2 Z 2 %sl2 } = true := by native_decide
example : chkL inv2 prog{ HMInv 2 1 2 %sl2 } = true := by native_decide

/-- **The packed container is inhabited by that pack**, which is the whole claim of
    the representation: a `HMap` value carries its own well-formedness. -/
example : chkL map2 HMapT = true := by native_decide

-- …and it is NOT vacuous. Each clause is separately load-bearing: put key 3 (odd) in
-- slot 0 and `SlotsOk` has no inhabitant; miscount the entries and `Hn` has none;
-- get the load ledger wrong and the tail has none.
example : chkL sok2 prog{ SlotsOk 2 Z 2 Arr(Cons(Pair(3, 30), Nil), Nil) } = false := by
  native_decide
example : chkL prog{ Pair(unit, Pair(%sok2, Pair(Refl, Refl))) } prog{ HMInv 2 1 3 %sl2 }
    = false := by native_decide
example : chkL prog{ Pair(unit, Pair(%sok2, Pair(Refl, Refl))) } prog{ HMInv 2 2 2 %sl2 }
    = false := by native_decide
-- A capacity of zero is refused by the first clause, so no `HMap` is ever divided by 0.
example : chkL prog{ Pair(unit, Pair(unit, Pair(Refl, Refl))) } prog{ HMInv Z 0 0 Arr() }
    = false := by native_decide

/-! ### The view, the size, and the model updates all compute on it -/

example : (pv prog{ SizeA 2 %sl2 }).natOf? == Option.some 2 := by native_decide
example : (pv prog{ Mul 2 4 }).natOf? == Option.some 8 := by native_decide
example : (pv prog{ Div (Mul 2 4) 5 }).natOf? == Option.some 1 := by native_decide
-- The load threshold for the flagship's own test capacity, 32 ↦ 25.
example : (pv prog{ Div (Mul 32 4) 5 }).natOf? == Option.some 25 := by native_decide

-- The lookup goes through the hash: key 4 is in slot 0, key 3 in slot 1, and a key
-- that hashes to an occupied slot but is not there answers `None`.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 4 %map2) (Some Nat 40) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 3 %map2) (Some Nat 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 6 %map2) (None Nat) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 4 %map2) (Some Nat 30) } = false := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeHM %map2) 2 } = true := by native_decide

-- The model updates: `FindIns` answers the new value AT the key and defers elsewhere,
-- and the size accounting bumps only for an absent key.
example : chkL prog{ Refl }
  prog{ Id (Opt Nat) (FindIns 4 4 99 %map2) (Some Nat 99) } = true := by native_decide
example : chkL prog{ Refl }
  prog{ Id (Opt Nat) (FindIns 3 4 99 %map2) (Some Nat 30) } = true := by native_decide
example : chkL prog{ Refl }
  prog{ Id (Opt Nat) (FindRem 4 4 %map2) (None Nat) } = true := by native_decide
-- Key 4 is present, so an insert at it does NOT bump the size; key 6 is absent, so it does.
example : chkL prog{ Refl } prog{ Id Nat (SizeIns 4 %map2) 2 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeIns 6 %map2) 3 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeRem 4 %map2) 1 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeRem 6 %map2) 2 } = true := by native_decide

/-! ## 5. The empty table, and the three lemmas `New` needs

    `MkB n` builds `n` empty buckets at a SYMBOLIC length, which an `Arr` literal
    cannot do — `ctorSig "Arr"` has a field telescope only at a concrete length. The
    `acons` recursion can, and it converts against the rigid `Array (S m) T` at each
    step.

    Each of the three lemmas is the same two-line induction, and each is the exact
    obligation one component of `New`'s exit pack owes. -/

def MkB : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List (Σ (k : Nat). Nat))) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }
def MkBTy : Term := prog{ Π (N : Nat) → Array N (List (Σ (k : Nat). Nat)) }

/-- Every slot of a fresh table is empty — at EVERY index, including out of range,
    which is what `AgetB`'s totality buys. This is `New`'s functional conjunct. -/
def MkBAget : Term := prog{
  λ (N : Nat).
    elim N return (λ (Nz : Nat).
        Π (I : Nat) → Id (List (Σ (k : Nat). Nat)) (AgetB Nz (MkB Nz) I) Nil) {
      Z => λ (I : Nat). Refl,
      S (M) Ih => λ (I : Nat).
        elim I return (λ (Iz : Nat).
            Id (List (Σ (k : Nat). Nat)) (AgetB (S M) (MkB (S M)) Iz) Nil) {
          Z => Refl,
          S (I') Rec => Ih I' } } }
def MkBAgetTy : Term := prog{
  Π (N : Nat) → Π (I : Nat) → Id (List (Σ (k : Nat). Nat)) (AgetB N (MkB N) I) Nil }

/-- A fresh table is well-hashed vacuously, from any starting index. -/
def MkBSlotsOk : Term := prog{
  λ (C : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Π (I0 : Nat) → SlotsOk C I0 Nz (MkB Nz)) {
      Z => λ (I0 : Nat). unit,
      S (M) Ih => λ (I0 : Nat). Pair(unit, Ih (S I0)) } }
def MkBSlotsOkTy : Term := prog{
  Π (C : Nat) → Π (N : Nat) → Π (I0 : Nat) → SlotsOk C I0 N (MkB N) }

/-- A fresh table holds no entries. The step is EXACTLY the induction hypothesis:
    `SizeA` of an `acons` is `Add (LenE Nil) …`, and `Add Z x` computes to `x`. -/
def MkBSize : Term := prog{
  λ (N : Nat).
    elim N return (λ (Nz : Nat). Id Nat (SizeA Nz (MkB Nz)) Z) {
      Z => Refl,
      S (M) Ih => Ih } }
def MkBSizeTy : Term := prog{ Π (N : Nat) → Id Nat (SizeA N (MkB N)) Z }

example : chkL MkB MkBTy = true := by native_decide
example : chkL MkBAget MkBAgetTy = true := by native_decide
example : chkL MkBSlotsOk MkBSlotsOkTy = true := by native_decide
example : chkL MkBSize MkBSizeTy = true := by native_decide

-- `AgetB` agrees with the kernel's `aget` where the kernel's computes at all.
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (AgetB 2 %sl2 1) Cons(Pair(3, 30), Nil) } = true := by
  native_decide
example : chkL prog{ Refl }
  prog{ Id (List (Σ (k : Nat). Nat)) (AgetB 2 %sl2 7) Nil } = true := by native_decide

/-! ## 6. `New` — the first complete operation

    The return type carries both of the problem statement's conjuncts and the pack
    carries the invariant, so the whole of `New`'s correctness is one term.

    Note what is NOT in the signature: any claim that the invariant holds. It cannot
    be stated, because a `HMap` that did not satisfy it would not be a `HMap`. -/

def newRet : Term := prog{
  Σ0 (hm : HMapT).
    Σ (Hf : Π (Q : Nat) → Id (Opt Nat) (FindHM Q hm) (None Nat)).
      Id Nat (SizeHM hm) Z }

def newP (rest : Term) : Term := prog{
  fn New (cap : Nat, Hc : Le (S Z) cap) -> %newRet {
    Pair(Pair(cap, Pair(Div (Mul cap 4) 5, Pair(Z,
           Pair(MkB cap,
                Pair(Hc,
                Pair(MkBSlotsOk cap cap Z,
                Pair(IdSym Nat (SizeA cap (MkB cap)) Z (MkBSize cap),
                     Refl))))))),
         Pair(λ (Q : Nat).
                IdCongr (List (Σ (k : Nat). Nat)) (Opt Nat)
                  (λ (B : List (Σ (k : Nat). Nat)). FindL Q B)
                  (AgetB cap (MkB cap) (Mod Q cap)) Nil
                  (MkBAget cap (Mod Q cap)),
              Refl)) };
  %rest }

example : progOk (newP prog{ () }) = true := by native_decide

-- It RUNS, and the machine really builds the array at a symbolic capacity.
example : progOk (newP prog{ let h = New(4, unit); () }) = true := by native_decide

/-! ### `New`'s twins — one per conjunct

    The empty map's `find` is `None` at every key and its size is zero, so a lie about
    either is refused. Note the SECOND twin is the interesting one: `Some Nat Z` is a
    perfectly well-typed `Opt Nat`, so what is refused is the mathematics and not the
    encoding. -/

example : progOk (newP prog{ () }) = true := by native_decide

-- Conjunct 1 lied: the fresh map claims to hold `Z` at every key.
example : progOk (prog{
  fn New (cap : Nat, Hc : Le (S Z) cap) -> (Σ0 (hm : HMapT).
      Σ (Hf : Π (Q : Nat) → Id (Opt Nat) (FindHM Q hm) (Some Nat Z)).
        Id Nat (SizeHM hm) Z) {
    Pair(Pair(cap, Pair(Div (Mul cap 4) 5, Pair(Z,
           Pair(MkB cap,
                Pair(Hc, Pair(MkBSlotsOk cap cap Z,
                Pair(IdSym Nat (SizeA cap (MkB cap)) Z (MkBSize cap), Refl))))))),
         Pair(λ (Q : Nat).
                IdCongr (List (Σ (k : Nat). Nat)) (Opt Nat)
                  (λ (B : List (Σ (k : Nat). Nat)). FindL Q B)
                  (AgetB cap (MkB cap) (Mod Q cap)) Nil (MkBAget cap (Mod Q cap)),
              Refl)) };
  () }) = false := by native_decide

-- Conjunct 2 lied: the fresh map claims size one.
example : progOk (prog{
  fn New (cap : Nat, Hc : Le (S Z) cap) -> (Σ0 (hm : HMapT).
      Σ (Hf : Π (Q : Nat) → Id (Opt Nat) (FindHM Q hm) (None Nat)).
        Id Nat (SizeHM hm) (S Z)) {
    Pair(Pair(cap, Pair(Div (Mul cap 4) 5, Pair(Z,
           Pair(MkB cap,
                Pair(Hc, Pair(MkBSlotsOk cap cap Z,
                Pair(IdSym Nat (SizeA cap (MkB cap)) Z (MkBSize cap), Refl))))))),
         Pair(λ (Q : Nat).
                IdCongr (List (Σ (k : Nat). Nat)) (Opt Nat)
                  (λ (B : List (Σ (k : Nat). Nat)). FindL Q B)
                  (AgetB cap (MkB cap) (Mod Q cap)) Nil (MkBAget cap (Mod Q cap)),
              Refl)) };
  () }) = false := by native_decide

-- The PACK twin: the load ledger is off by one, so the invariant's fourth clause has
-- no inhabitant and the pack cannot be built at all. This is the packing earning its
-- keep — a broken map is refused at construction, not at some later use.
example : progOk (prog{
  fn New (cap : Nat, Hc : Le (S Z) cap) -> %newRet {
    Pair(Pair(cap, Pair(S(Div (Mul cap 4) 5), Pair(Z,
           Pair(MkB cap,
                Pair(Hc, Pair(MkBSlotsOk cap cap Z,
                Pair(IdSym Nat (SizeA cap (MkB cap)) Z (MkBSize cap), Refl))))))),
         Pair(λ (Q : Nat).
                IdCongr (List (Σ (k : Nat). Nat)) (Opt Nat)
                  (λ (B : List (Σ (k : Nat). Nat)). FindL Q B)
                  (AgetB cap (MkB cap) (Mod Q cap)) Nil (MkBAget cap (Mod Q cap)),
              Refl)) };
  () }) = false := by native_decide

/-! ## 7. Crossing a carve

    This is the invariant library proper, and it is `SortedArrCat`/`SplitACat*`'s
    shape throughout: every lemma is an induction on the LEFT array and nothing else.

    The shape they are all stated at is the one the PROGRAM produces. A hashmap
    operation carves its slots three ways at the hashed index —

        let lo   = &m (*slots)[Z ; s ; S j | LeAdd s (S j) | Hdec];
        let cell = &m (*slots)[s ; 1 ; j];
        let hi   = &m (*slots)[S s ; j];

    — so the array it then reasons about is `arrCat K (S M) L (acons M X R)` with
    total length `Add K (S M)`, and stating anything more general would be less usable
    (R7's lesson: `S k` and `Add k 1` do not convert at a symbolic `k`, and the program
    has the former).

    `Bucket` is the Lean-level `Term` for `List (Σ (k : Nat). Nat)`, spliced by name. -/

/-! ### Boolean discrimination, and `Eqb` reflected into `Id`

    `Znots`' shape at `Bool`: transport `unit` along the equation into a `boolRec`
    motive that answers `Unit` on one side and `Bot` on the other. -/

def TnotF : Term := prog{
  λ (H : Id Bool True False).
    j Bool True (λ (Y : Bool). λ (Hy : Id Bool True Y).
        elim Y return (λ (Yy : Bool). Type) { True => Unit, False => Bot })
      unit False H }
def TnotFTy : Term := prog{ Id Bool True False → Bot }

def FnotT : Term := prog{
  λ (H : Id Bool False True).
    j Bool False (λ (Y : Bool). λ (Hy : Id Bool False Y).
        elim Y return (λ (Yy : Bool). Type) { True => Bot, False => Unit })
      unit True H }
def FnotTTy : Term := prog{ Id Bool False True → Bot }

/-- `Eqb`'s completeness — the direction `Std` does not have. `EqbRefl` is the other
    one. This is what turns "the query and the inserted key test equal" into an
    equation the rest of a proof can rewrite along, and it is why the frame case of
    every operation below can rule out `q = key` from a slot mismatch alone. -/
def EqbTrueEq : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) True → Id Nat Az B) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) True → Id Nat Z Bz) {
          Z => λ (H : Id Bool True True). Refl,
          S (B') Rb => λ (H : Id Bool False True). botElim (Id Nat Z (S B')) (FnotT H) },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb (S A') Bz) True → Id Nat (S A') Bz) {
          Z => λ (H : Id Bool False True). botElim (Id Nat (S A') Z) (FnotT H),
          S (B') Rb => λ (H : Id Bool (Eqb A' B') True).
            IdCongr Nat Nat (λ (Nn : Nat). S Nn) A' B' (Ih B' H) } } }
def EqbTrueEqTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) True → Id Nat A B }

example : chkL TnotF TnotFTy = true := by native_decide
example : chkL FnotT FnotTTy = true := by native_decide
example : chkL EqbTrueEq EqbTrueEqTy = true := by native_decide

/-! ### Reading the carved slot back

    `AgetBMid` is the hit case and `AgetBNe` the frame, and between them they are the
    whole of what an operation's pointwise find equation needs from the array layer.

    `AgetBMid`'s step is LITERALLY the induction hypothesis, which is the payoff for
    writing `AgetB` as a fold: `arrCat` on an `acons`-headed left argument rebuilds as
    an `acons`, `AgetB` of an `acons` at `S i` steps to `AgetB` of the tail at `i`, and
    the two reductions meet with nothing left to say. -/

def AgetBMid : Term := prog{
  λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket). λ (K : Nat). λ (L : Array K Bucket).
    arrRec Bucket
      (λ (Kz : Nat). λ (Lz : Array Kz Bucket).
        Id Bucket (AgetB (Add Kz (S M)) (arrCat Kz (S M) Lz (acons M X R)) Kz) X)
      Refl
      (λ (K2 : Nat). λ (Hh : Bucket). λ (Tl : Array K2 Bucket).
       λ (Ih : Id Bucket (AgetB (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R)) K2) X).
         Ih)
      K L }
def AgetBMidTy : Term := prog{
  Π (M : Nat) → Π (X : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) →
    Id Bucket (AgetB (Add K (S M)) (arrCat K (S M) L (acons M X R)) K) X }

/-- **The frame.** Replacing the bucket at index `K` changes no other index. The
    hypothesis is the Boolean `Eqb T K = False` rather than a `Le`, because that is
    the form the PROOF SITE has: an operation's pointwise conjunct is a λ over the
    query, and the only way to split on "is the query's slot the one we wrote" inside
    a pure term is a `boolRec` carrying its own branch equation. -/
def AgetBNe : Term := prog{
  λ (M : Nat). λ (X : Bucket). λ (Y : Bucket). λ (R : Array M Bucket).
  λ (K : Nat). λ (L : Array K Bucket).
    arrRec Bucket
      (λ (Kz : Nat). λ (Lz : Array Kz Bucket).
        Π (T : Nat) → Id Bool (Eqb T Kz) False →
          Id Bucket (AgetB (Add Kz (S M)) (arrCat Kz (S M) Lz (acons M X R)) T)
                    (AgetB (Add Kz (S M)) (arrCat Kz (S M) Lz (acons M Y R)) T))
      (λ (T : Nat).
        elim T return (λ (Tz : Nat). Id Bool (Eqb Tz Z) False →
            Id Bucket (AgetB (S M) (acons M X R) Tz) (AgetB (S M) (acons M Y R) Tz)) {
          Z => λ (H : Id Bool True False).
                 botElim (Id Bucket (AgetB (S M) (acons M X R) Z)
                                    (AgetB (S M) (acons M Y R) Z)) (TnotF H),
          -- `Eqb (S t') Z` REDUCES to `False`; writing the hypothesis as the stuck
          -- `Eqb T' Z` is a different type and the arm silently fails to convert.
          S (T') Rt => λ (H : Id Bool False False). Refl })
      (λ (K2 : Nat). λ (Hh : Bucket). λ (Tl : Array K2 Bucket).
       λ (Ih : Π (T : Nat) → Id Bool (Eqb T K2) False →
            Id Bucket (AgetB (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R)) T)
                      (AgetB (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M Y R)) T)).
        λ (T : Nat).
          elim T return (λ (Tz : Nat). Id Bool (Eqb Tz (S K2)) False →
              Id Bucket
                (AgetB (S (Add K2 (S M)))
                   (acons (Add K2 (S M)) Hh (arrCat K2 (S M) Tl (acons M X R))) Tz)
                (AgetB (S (Add K2 (S M)))
                   (acons (Add K2 (S M)) Hh (arrCat K2 (S M) Tl (acons M Y R))) Tz)) {
            Z => λ (H : Id Bool False False). Refl,
            S (T') Rt => λ (H : Id Bool (Eqb T' K2) False). Ih T' H })
      K L }
def AgetBNeTy : Term := prog{
  Π (M : Nat) → Π (X : Bucket) → Π (Y : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) → Π (T : Nat) → Id Bool (Eqb T K) False →
    Id Bucket (AgetB (Add K (S M)) (arrCat K (S M) L (acons M X R)) T)
              (AgetB (Add K (S M)) (arrCat K (S M) L (acons M Y R)) T) }

example : chkL AgetBMid AgetBMidTy = true := by native_decide
example : chkL AgetBNe AgetBNeTy = true := by native_decide

/-! ### The invariant crossing the carve, both ways

    `SlotsOkSplit` takes the whole table's well-hashedness apart into the left part,
    the carved bucket, and the right part; `SlotsOkJoin` puts it back with a NEW
    bucket in the middle. An operation calls the first before it writes and the second
    to build its exit pack, and between them they are the entire invariant-preservation
    argument for a bucket-local update.

    **The one piece of arithmetic in the whole library** lives in these two, and it is
    worth naming because it is not obvious from the statement. `SlotsOk` threads the
    slot index DOWN the spine, so the induction hypothesis for a left part of length
    `K2` starting at `S I0` reports the middle bucket's index as `Add K2 (S I0)`, while
    the goal at length `S K2` starting at `I0` wants `Add (S K2) I0`, which computes to
    `S (Add K2 I0)`. Those two are `AddSucc` apart and nothing more, so each step
    carries exactly one `NatRw` over the motive
    `λ Z0. Σ (Hm : BucketAt C Z0 X). SlotsOk C (S Z0) M R` — the middle and the right
    part transported together, since they are the two things whose index moved. -/

def SlotsOkSplit : Term := prog{
  λ (C : Nat). λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket).
  λ (K : Nat). λ (L : Array K Bucket).
    arrRec Bucket
      (λ (Kz : Nat). λ (Lz : Array Kz Bucket).
        Π (I0 : Nat) →
          SlotsOk C I0 (Add Kz (S M)) (arrCat Kz (S M) Lz (acons M X R)) →
            Σ (Hl : SlotsOk C I0 Kz Lz).
            Σ (Hm : BucketAt C (Add Kz I0) X). SlotsOk C (S (Add Kz I0)) M R)
      (λ (I0 : Nat).
        λ (H : Σ (Hm : BucketAt C I0 X). SlotsOk C (S I0) M R). Pair(unit, H))
      (λ (K2 : Nat). λ (Hh : Bucket). λ (Tl : Array K2 Bucket).
       λ (Ih : Π (I0 : Nat) →
            SlotsOk C I0 (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R)) →
              Σ (Hl : SlotsOk C I0 K2 Tl).
              Σ (Hm : BucketAt C (Add K2 I0) X). SlotsOk C (S (Add K2 I0)) M R).
        λ (I0 : Nat).
        λ (H : Σ (Hb : BucketAt C I0 Hh).
                 SlotsOk C (S I0) (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R))).
          elim H return (λ (Hz : Σ (Hb : BucketAt C I0 Hh).
                 SlotsOk C (S I0) (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R))).
              Σ (Hl : Σ (Hb : BucketAt C I0 Hh). SlotsOk C (S I0) K2 Tl).
              Σ (Hm : BucketAt C (S (Add K2 I0)) X).
                SlotsOk C (S (S (Add K2 I0))) M R) {
            Pair (Hb) (Hrest) =>
              elim (Ih (S I0) Hrest) return (λ (Qz :
                  Σ (Hl : SlotsOk C (S I0) K2 Tl).
                  Σ (Hm : BucketAt C (Add K2 (S I0)) X).
                    SlotsOk C (S (Add K2 (S I0))) M R).
                  Σ (Hl : Σ (Hb2 : BucketAt C I0 Hh). SlotsOk C (S I0) K2 Tl).
                  Σ (Hm : BucketAt C (S (Add K2 I0)) X).
                    SlotsOk C (S (S (Add K2 I0))) M R) {
                Pair (Hl) (Htail) =>
                  Pair(Pair(Hb, Hl),
                       NatRw (λ (Z0 : Nat).
                                Σ (Hm : BucketAt C Z0 X). SlotsOk C (S Z0) M R)
                             (Add K2 (S I0)) (S (Add K2 I0))
                             (AddSucc K2 I0) Htail) } })
      K L }
def SlotsOkSplitTy : Term := prog{
  Π (C : Nat) → Π (M : Nat) → Π (X : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) → Π (I0 : Nat) →
    SlotsOk C I0 (Add K (S M)) (arrCat K (S M) L (acons M X R)) →
      Σ (Hl : SlotsOk C I0 K L).
      Σ (Hm : BucketAt C (Add K I0) X). SlotsOk C (S (Add K I0)) M R }

def SlotsOkJoin : Term := prog{
  λ (C : Nat). λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket).
  λ (K : Nat). λ (L : Array K Bucket).
    arrRec Bucket
      (λ (Kz : Nat). λ (Lz : Array Kz Bucket).
        Π (I0 : Nat) → SlotsOk C I0 Kz Lz →
          BucketAt C (Add Kz I0) X → SlotsOk C (S (Add Kz I0)) M R →
            SlotsOk C I0 (Add Kz (S M)) (arrCat Kz (S M) Lz (acons M X R)))
      (λ (I0 : Nat). λ (Hl : Unit). λ (Hm : BucketAt C I0 X).
       λ (Hr : SlotsOk C (S I0) M R). Pair(Hm, Hr))
      (λ (K2 : Nat). λ (Hh : Bucket). λ (Tl : Array K2 Bucket).
       λ (Ih : Π (I0 : Nat) → SlotsOk C I0 K2 Tl →
            BucketAt C (Add K2 I0) X → SlotsOk C (S (Add K2 I0)) M R →
              SlotsOk C I0 (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R))).
        λ (I0 : Nat).
        λ (Hl : Σ (Hb : BucketAt C I0 Hh). SlotsOk C (S I0) K2 Tl).
        λ (Hm : BucketAt C (S (Add K2 I0)) X).
        λ (Hr : SlotsOk C (S (S (Add K2 I0))) M R).
          elim Hl return (λ (Hlz : Σ (Hb : BucketAt C I0 Hh). SlotsOk C (S I0) K2 Tl).
              Σ (Hb2 : BucketAt C I0 Hh).
                SlotsOk C (S I0) (Add K2 (S M)) (arrCat K2 (S M) Tl (acons M X R))) {
            Pair (Hb) (Hl2) =>
              elim (NatRw (λ (Z0 : Nat).
                             Σ (Hm2 : BucketAt C Z0 X). SlotsOk C (S Z0) M R)
                          (S (Add K2 I0)) (Add K2 (S I0))
                          (IdSym Nat (Add K2 (S I0)) (S (Add K2 I0)) (AddSucc K2 I0))
                          Pair(Hm, Hr))
                return (λ (Qz : Σ (Hm2 : BucketAt C (Add K2 (S I0)) X).
                                  SlotsOk C (S (Add K2 (S I0))) M R).
                    Σ (Hb2 : BucketAt C I0 Hh).
                      SlotsOk C (S I0) (Add K2 (S M))
                        (arrCat K2 (S M) Tl (acons M X R))) {
                Pair (Hm2) (Hr2) => Pair(Hb, Ih (S I0) Hl2 Hm2 Hr2) } })
      K L }
def SlotsOkJoinTy : Term := prog{
  Π (C : Nat) → Π (M : Nat) → Π (X : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) → Π (I0 : Nat) → SlotsOk C I0 K L →
    BucketAt C (Add K I0) X → SlotsOk C (S (Add K I0)) M R →
      SlotsOk C I0 (Add K (S M)) (arrCat K (S M) L (acons M X R)) }

/-- The entry count splits across a concatenation. `CountArrCat`'s transfer, and the
    same induction; the step is one `IdCongr` under `Add (LenE Hh) …` plus the one
    `AddAssoc` that reassociates the head's contribution. -/
def SizeACat : Term := prog{
  λ (M : Nat). λ (R : Array M Bucket). λ (K : Nat). λ (L : Array K Bucket).
    arrRec Bucket
      (λ (Kz : Nat). λ (Lz : Array Kz Bucket).
        Id Nat (SizeA (Add Kz M) (arrCat Kz M Lz R)) (Add (SizeA Kz Lz) (SizeA M R)))
      Refl
      (λ (K2 : Nat). λ (Hh : Bucket). λ (Tl : Array K2 Bucket).
       λ (Ih : Id Nat (SizeA (Add K2 M) (arrCat K2 M Tl R))
                      (Add (SizeA K2 Tl) (SizeA M R))).
         IdTrans Nat
           (Add (LenE Hh) (SizeA (Add K2 M) (arrCat K2 M Tl R)))
           (Add (LenE Hh) (Add (SizeA K2 Tl) (SizeA M R)))
           (Add (Add (LenE Hh) (SizeA K2 Tl)) (SizeA M R))
           (IdCongr Nat Nat (λ (Cz : Nat). Add (LenE Hh) Cz)
              (SizeA (Add K2 M) (arrCat K2 M Tl R))
              (Add (SizeA K2 Tl) (SizeA M R)) Ih)
           (IdSym Nat (Add (Add (LenE Hh) (SizeA K2 Tl)) (SizeA M R))
                      (Add (LenE Hh) (Add (SizeA K2 Tl) (SizeA M R)))
              (AddAssoc (LenE Hh) (SizeA K2 Tl) (SizeA M R))))
      K L }
def SizeACatTy : Term := prog{
  Π (M : Nat) → Π (R : Array M Bucket) → Π (K : Nat) → Π (L : Array K Bucket) →
    Id Nat (SizeA (Add K M) (arrCat K M L R)) (Add (SizeA K L) (SizeA M R)) }

example : chkL SlotsOkSplit SlotsOkSplitTy = true := by native_decide
example : chkL SlotsOkJoin SlotsOkJoinTy = true := by native_decide
example : chkL SizeACat SizeACatTy = true := by native_decide

/-! ## 8. The bucket layer's find equation

    `FindL q (InsL k v b) = if q = k then Some v else FindL q b`, universally in the
    bucket. This is the mathematical core of the whole flagship: `insert_in_list` is
    the only place an entry is ever created or overwritten, and every operation's
    pointwise conjunct bottoms out here.

    It needs three pieces of Boolean bookkeeping, stated separately because each is
    about `boolRec` and nothing about hashmaps. -/

def BoolRw : Term := prog{
  λ (P : Bool → Type). λ (X : Bool). λ (Y : Bool). λ (H : Id Bool X Y). λ (Px : P X).
    j Bool X (λ (Y2 : Bool). λ (Hh : Id Bool X Y2). P Y2) Px Y H }
def BoolRwTy : Term := prog{
  Π (P : Bool → Type) → Π (X : Bool) → Π (Y : Bool) → Id Bool X Y → P X → P Y }

/-- A second test of the SAME scrutinee in the else-branch is dead. -/
def OptIf2 : Term := prog{
  λ (Bv : Bool). λ (Xa : Opt Nat). λ (Ya : Opt Nat). λ (Za : Opt Nat).
    elim Bv return (λ (Bz : Bool).
        Id (Opt Nat)
           (boolRec (λ (W : Bool). Opt Nat) Xa
              (boolRec (λ (W : Bool). Opt Nat) Ya Za Bz) Bz)
           (boolRec (λ (W : Bool). Opt Nat) Xa Za Bz)) {
      True => Refl,
      False => Refl } }
def OptIf2Ty : Term := prog{
  Π (Bv : Bool) → Π (Xa : Opt Nat) → Π (Ya : Opt Nat) → Π (Za : Opt Nat) →
    Id (Opt Nat)
       (boolRec (λ (W : Bool). Opt Nat) Xa
          (boolRec (λ (W : Bool). Opt Nat) Ya Za Bv) Bv)
       (boolRec (λ (W : Bool). Opt Nat) Xa Za Bv) }

/-- Two nested tests COMMUTE when they cannot both fire. The impossible corner is the
    only content; the other three are `Refl`. -/
def IfComm : Term := prog{
  λ (B1 : Bool). λ (B2 : Bool). λ (Xa : Opt Nat). λ (Ya : Opt Nat). λ (Za : Opt Nat).
  λ (Hno : Id Bool B1 True → Id Bool B2 True → Bot).
    elim B1 return (λ (Z1 : Bool).
        (Id Bool Z1 True → Id Bool B2 True → Bot) →
        Id (Opt Nat)
          (boolRec (λ (W : Bool). Opt Nat) Xa
             (boolRec (λ (W : Bool). Opt Nat) Ya Za B2) Z1)
          (boolRec (λ (W : Bool). Opt Nat) Ya
             (boolRec (λ (W : Bool). Opt Nat) Xa Za Z1) B2)) {
      True => λ (Hn : Id Bool True True → Id Bool B2 True → Bot).
        elim B2 return (λ (Z2 : Bool).
            (Id Bool True True → Id Bool Z2 True → Bot) →
            Id (Opt Nat)
              (boolRec (λ (W : Bool). Opt Nat) Xa
                 (boolRec (λ (W : Bool). Opt Nat) Ya Za Z2) True)
              (boolRec (λ (W : Bool). Opt Nat) Ya
                 (boolRec (λ (W : Bool). Opt Nat) Xa Za True) Z2)) {
          True => λ (Hn2 : Id Bool True True → Id Bool True True → Bot).
                    botElim (Id (Opt Nat) Xa Ya) (Hn2 Refl Refl),
          False => λ (Hn2 : Id Bool True True → Id Bool False True → Bot). Refl } Hn,
      False => λ (Hn : Id Bool False True → Id Bool B2 True → Bot).
        elim B2 return (λ (Z2 : Bool).
            Id (Opt Nat)
              (boolRec (λ (W : Bool). Opt Nat) Xa
                 (boolRec (λ (W : Bool). Opt Nat) Ya Za Z2) False)
              (boolRec (λ (W : Bool). Opt Nat) Ya
                 (boolRec (λ (W : Bool). Opt Nat) Xa Za False) Z2)) {
          True => Refl,
          False => Refl } } Hno }
def IfCommTy : Term := prog{
  Π (B1 : Bool) → Π (B2 : Bool) → Π (Xa : Opt Nat) → Π (Ya : Opt Nat) →
  Π (Za : Opt Nat) → (Id Bool B1 True → Id Bool B2 True → Bot) →
    Id (Opt Nat)
      (boolRec (λ (W : Bool). Opt Nat) Xa
         (boolRec (λ (W : Bool). Opt Nat) Ya Za B2) B1)
      (boolRec (λ (W : Bool). Opt Nat) Ya
         (boolRec (λ (W : Bool). Opt Nat) Xa Za B1) B2) }

example : chkL BoolRw BoolRwTy = true := by native_decide
example : chkL OptIf2 OptIf2Ty = true := by native_decide
example : chkL IfComm IfCommTy = true := by native_decide

/-- The bucket-level model update, as a function, so the equation below can be stated
    against a name rather than an inlined `boolRec`. -/
def FindInsL : Term := prog{
  λ (Q : Nat). λ (K : Nat). λ (V : Nat). λ (B : Bucket).
    elim (Eqb Q K) return (λ (Bz : Bool). Opt Nat) {
      True => Some Nat V,
      False => FindL Q B } }

/-- Two keys that both match `q` are equal, so `Eqb k2 k = False` rules the pair out.
    Extracted from `FindLIns`' inductive step, where it is the impossible corner. -/
def NoBoth : Term := prog{
  λ (Q : Nat). λ (K2 : Nat). λ (K : Nat). λ (He : Id Bool (Eqb K2 K) False).
  λ (H1 : Id Bool (Eqb Q K2) True). λ (H2 : Id Bool (Eqb Q K) True).
    TnotF (IdTrans Bool True (Eqb K2 K) False
      (IdSym Bool (Eqb K2 K) True
        (IdTrans Bool (Eqb K2 K) (Eqb K2 K2) True
          (IdSym Bool (Eqb K2 K2) (Eqb K2 K)
            (IdCongr Nat Bool (λ (Zz : Nat). Eqb K2 Zz) K2 K
              (IdTrans Nat K2 Q K
                (IdSym Nat Q K2 (EqbTrueEq Q K2 H1)) (EqbTrueEq Q K H2))))
          (EqbRefl K2)))
      He) }
def NoBothTy : Term := prog{
  Π (Q : Nat) → Π (K2 : Nat) → Π (K : Nat) → Id Bool (Eqb K2 K) False →
    Id Bool (Eqb Q K2) True → Id Bool (Eqb Q K) True → Bot }

example : chkL NoBoth NoBothTy = true := by native_decide

/-- **`FindL q (InsL k v b) = if q = k then Some v else FindL q b`.**

    The induction is on the bucket, and the step splits on `Eqb k2 k` — the SAME test
    `InsL` itself makes, which is why the split is written with the abstract-the-goal
    idiom: the motive replaces `Eqb K2 K` by the bound `Bv` everywhere it occurs in
    the goal AND carries the branch equation, so the arm sees both a reduced left-hand
    side and a hypothesis about why it reduced. Applied to `Refl` at the end.

    The overwrite arm rewrites `k` to `k2` (from `EqbTrueEq`) and then the outer test
    subsumes the inner one — `OptIf2`. The append arm rewrites by the induction
    hypothesis and then commutes the two tests — `IfComm`, whose impossible corner is
    `NoBoth`: two keys that both match `q` are equal, and `Eqb k2 k = False` says they
    are not. -/
def FindLIns : Term := prog{
  λ (Q : Nat). λ (K : Nat). λ (V : Nat). λ (B : Bucket).
    -- The motive's binder type is spelled `List (Σ (k : Nat). Nat)` and NOT the
    -- spliced `Bucket`, and that is load-bearing: the elim sugar reads its element
    -- type SYNTACTICALLY out of a `List A`, so a motive written as a bare name it
    -- cannot see through falls back to the old `Nat` default and builds a `listRec`
    -- at the wrong element type. It fails as a bare `false` with no message.
    elim B return (λ (Bz : List (Σ (k : Nat). Nat)).
        Id (Opt Nat) (FindL Q (InsL K V Bz)) (FindInsL Q K V Bz)) {
      Nil => Refl,
      Cons (E) (T) Rec =>
        elim E return (λ (Ez : Σ (k : Nat). Nat).
            Id (Opt Nat) (FindL Q (InsL K V Cons(Ez, T))) (FindInsL Q K V Cons(Ez, T))) {
          Pair (K2) (V2) =>
            elim (Eqb K2 K) return (λ (Bv : Bool).
                Id Bool (Eqb K2 K) Bv →
                Id (Opt Nat)
                  (FindL Q (boolRec (λ (W : Bool). Bucket)
                              Cons(Pair(K2, V), T)
                              Cons(Pair(K2, V2), InsL K V T) Bv))
                  (FindInsL Q K V Cons(Pair(K2, V2), T))) {
              -- The key was there: the entry's value is replaced, and the outer test
              -- (`q = k`, now `q = k2`) makes the inner one dead.
              True => λ (He : Id Bool (Eqb K2 K) True).
                BoolRw
                  (λ (Bw : Bool). Id (Opt Nat)
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V) (FindL Q T) (Eqb Q K2))
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V)
                        (boolRec (λ (W : Bool). Opt Nat) (Some Nat V2)
                           (FindL Q T) (Eqb Q K2)) Bw))
                  (Eqb Q K2) (Eqb Q K)
                  (IdCongr Nat Bool (λ (Zz : Nat). Eqb Q Zz) K2 K (EqbTrueEq K2 K He))
                  (IdSym (Opt Nat)
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V)
                        (boolRec (λ (W : Bool). Opt Nat) (Some Nat V2)
                           (FindL Q T) (Eqb Q K2)) (Eqb Q K2))
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V) (FindL Q T) (Eqb Q K2))
                     (OptIf2 (Eqb Q K2) (Some Nat V) (Some Nat V2) (FindL Q T))),
              -- The key was elsewhere: recurse, then commute the two tests.
              False => λ (He : Id Bool (Eqb K2 K) False).
                IdTrans (Opt Nat)
                  (boolRec (λ (W : Bool). Opt Nat) (Some Nat V2)
                     (FindL Q (InsL K V T)) (Eqb Q K2))
                  (boolRec (λ (W : Bool). Opt Nat) (Some Nat V2)
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V)
                        (FindL Q T) (Eqb Q K)) (Eqb Q K2))
                  (boolRec (λ (W : Bool). Opt Nat) (Some Nat V)
                     (boolRec (λ (W : Bool). Opt Nat) (Some Nat V2)
                        (FindL Q T) (Eqb Q K2)) (Eqb Q K))
                  (IdCongr (Opt Nat) (Opt Nat)
                     (λ (Zz : Opt Nat).
                        boolRec (λ (W : Bool). Opt Nat) (Some Nat V2) Zz (Eqb Q K2))
                     (FindL Q (InsL K V T)) (FindInsL Q K V T) Rec)
                  (IfComm (Eqb Q K2) (Eqb Q K) (Some Nat V2) (Some Nat V) (FindL Q T)
                     (NoBoth Q K2 K He)) } Refl } } }
def FindLInsTy : Term := prog{
  Π (Q : Nat) → Π (K : Nat) → Π (V : Nat) → Π (B : Bucket) →
    Id (Opt Nat) (FindL Q (InsL K V B)) (FindInsL Q K V B) }

example : chkL FindLIns FindLInsTy = true := by native_decide

/-! ## 9. `InsertInList` — the imperative bucket walk

    The Aeneas case study's own leaf, and the ONLY place in the flagship where an
    entry is created or overwritten. Its whole specification is that it implements
    `InsL`: `Id Bucket (*b) (InsL k v (old *b))`. Everything above it then reasons
    purely, against `FindLIns`.

    Three things about the body are forced rather than chosen.

    **The snapshots come first.** `K0`/`V0`/`T0` name the entry's key, value and tail
    as they are on entry, because the return type's far endpoint is `old *b` and a
    body cannot write that; `Kq`/`Vq` snapshot the function's own runtime `k`/`v`
    because the transport λ below mentions them and a λ body may cite only capital
    bindings (§2's λ law).

    **The branch equation is named** (`if e : Eqb *kk k`), and it is then run
    BACKWARDS through `BoolRw`: the goal's right-hand side is a `boolRec` on
    `Eqb K0 Kq` that does not compute at a symbolic key, so each branch proves the
    statement at its own literal tag and transports along `e` to reach the goal.

    **The fuel bound needs no arithmetic.** `Le (LenE (*b)) fuel` at a `Cons` with
    `fuel = S f2` IS `Le (LenE (*tl)) f2` by computation — `LenE` of a `Cons` steps to
    `S (LenE tl)` and `Le (S a) (S b)` steps to `Le a b` — so `Hf` is passed to the
    recursive call unchanged. -/

def iilRet : Term := prog{
  Id (List (Σ (k : Nat). Nat)) (*%(Term.var ⟨3, "b"⟩))
     (InsL %(Term.var ⟨1, "k"⟩) %(Term.var ⟨2, "v"⟩) (old *%(Term.var ⟨3, "b"⟩))) }

def iilP (rest : Term) : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel) -> %iilRet {
    match b {
      Nil => { *b := Cons(Pair(k, v), Nil); Refl },
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd {
          Pair(kk, vv) => {
            let K0 = *kk;
            let V0 = *vv;
            let T0 = *tl;
            let Kq = k;
            let Vq = v;
            if e : Eqb *kk k {
              *vv := v;
              BoolRw
                (λ (Bw : Bool). Id (List (Σ (k : Nat). Nat)) Cons(Pair(K0, Vq), T0)
                   (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                      Cons(Pair(K0, Vq), T0)
                      Cons(Pair(K0, V0), InsL Kq Vq T0) Bw))
                True (Eqb K0 Kq)
                (IdSym Bool (Eqb K0 Kq) True e) Refl
            } else {
              let h = InsertInList(f2, k, v, &m *tl, Hf);
              -- Two legs: lift the recursive call's equation through the head cell,
              -- then transport the `Eqb` test off its `False` branch onto the goal.
              IdTrans (List (Σ (k : Nat). Nat))
                Cons(Pair(K0, V0), *tl)
                Cons(Pair(K0, V0), InsL Kq Vq T0)
                (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                   Cons(Pair(K0, Vq), T0)
                   Cons(Pair(K0, V0), InsL Kq Vq T0) (Eqb K0 Kq))
                (IdCongr (List (Σ (k : Nat). Nat)) (List (Σ (k : Nat). Nat))
                   (λ (Z0 : List (Σ (k : Nat). Nat)). Cons(Pair(K0, V0), Z0))
                   (*tl) (InsL Kq Vq T0) h)
                (BoolRw
                   (λ (Bw : Bool). Id (List (Σ (k : Nat). Nat))
                      Cons(Pair(K0, V0), InsL Kq Vq T0)
                      (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                         Cons(Pair(K0, Vq), T0)
                         Cons(Pair(K0, V0), InsL Kq Vq T0) Bw))
                   False (Eqb K0 Kq)
                   (IdSym Bool (Eqb K0 Kq) False e) Refl)
            } } } } } };
  %rest }

/-- **The imperative bucket walk implements the model.** This is the flagship's one
    genuinely effectful leaf, and it is fully verified. -/
example : progOk (iilP prog{ () }) = true := by native_decide

/-! ### `InsertInList`'s twins -/

-- The spec lied onto the ENTRY payload: `*b` claimed to be what it USED to be.
example : progOk (prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel)
      -> (Id (List (Σ (k : Nat). Nat)) (old *b)
             (InsL k v (old *b))) { botElim Unit Hf };
  () }) = false := by native_decide

-- The BODY twin: the overwrite branch does not write. It still returns the same
-- claim, and only the found-key path is wrong.
example : progOk (prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel) -> %iilRet {
    match b {
      Nil => { *b := Cons(Pair(k, v), Nil); Refl },
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => match hd {
          Pair(kk, vv) => {
            let K0 = *kk;
            let V0 = *vv;
            let T0 = *tl;
            let Kq = k;
            let Vq = v;
            if e : Eqb *kk k {
              BoolRw
                (λ (Bw : Bool). Id (List (Σ (k : Nat). Nat)) Cons(Pair(K0, Vq), T0)
                   (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                      Cons(Pair(K0, Vq), T0)
                      Cons(Pair(K0, V0), InsL Kq Vq T0) Bw))
                True (Eqb K0 Kq)
                (IdSym Bool (Eqb K0 Kq) True e) Refl
            } else {
              let h = InsertInList(f2, k, v, &m *tl, Hf);
              IdTrans (List (Σ (k : Nat). Nat))
                Cons(Pair(K0, V0), *tl)
                Cons(Pair(K0, V0), InsL Kq Vq T0)
                (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                   Cons(Pair(K0, Vq), T0)
                   Cons(Pair(K0, V0), InsL Kq Vq T0) (Eqb K0 Kq))
                (IdCongr (List (Σ (k : Nat). Nat)) (List (Σ (k : Nat). Nat))
                   (λ (Z0 : List (Σ (k : Nat). Nat)). Cons(Pair(K0, V0), Z0))
                   (*tl) (InsL Kq Vq T0) h)
                (BoolRw
                   (λ (Bw : Bool). Id (List (Σ (k : Nat). Nat))
                      Cons(Pair(K0, V0), InsL Kq Vq T0)
                      (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                         Cons(Pair(K0, Vq), T0)
                         Cons(Pair(K0, V0), InsL Kq Vq T0) Bw))
                   False (Eqb K0 Kq)
                   (IdSym Bool (Eqb K0 Kq) False e) Refl)
            } } } } } };
  () }) = false := by native_decide

-- The `Nil` branch's write is load-bearing too: refill with `Nil` and the append
-- case is wrong while every other path still goes through.
example : progOk (prog{
  fn InsertInList [fuel] (fuel : Nat, k : Nat, v : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel) -> %iilRet {
    match b { Nil => { *b := Nil; Refl }, Cons(hd, tl) => botElim Unit Hf } };
  () }) = false := by native_decide

/-! ## 10. Opening a `HMap` — the shape, and the four rejections that fixed it

    A hashmap operation has to get from `self : &mut HMap` to a `&mut Bucket` at the
    hashed slot. Destructuring the pack through the borrow works and hands back
    borrows of all five components (§7's "borrow mode goes all the way down"), but
    four things about the route were measured rather than guessed, and each was a
    rejection with a message that named its own fix:

      * **Reading the capacity MOVES it.** `let c = *cap` leaves a hole:
        `audit: argument borrow self (ℓ0) holds a hole (⊥) at return, in a leaf it
        still owns — take without refill`. A `Nat` behind a `&mut` is still a payload
        take, so the read is followed by `*cap := c` and the value survives the refill.
      * **The invariant reads as knowledge.** `let Hi = *Hinv` is accepted with no
        refill, because the `Σ0` tail is comptime and a comptime read consumes nothing.
      * **The slot must be minted across a CALL** (the `hm-probe-mod` finding), and
        inside that call the slot must be a LOWERCASE `let`: a capital binder cannot
        be ⇒-moved into the returned pair (`fence: 'S0' is a COMPTIME binder … and
        cannot be ⇒-moved`). A runtime `let` is still value-transparent, so
        `Refl : Id Nat s0 (Mod key n)` closes and the caller keeps the connection back
        to `Mod key n` in the `Σ0`.
      * **A bare lemma spine cannot be match-scrutinized.** `let Pair(rr, hq) =
        ModDec …` is refused with `match: non-exhaustive — no branch for constructor
        'True'` — the checker cannot synthesize a type for an unascribed λ-spine and
        the match sees garbage. Ascribing it (`(ModDec … : Σ (r : Nat). …)`) fixes it,
        and the message is worth knowing because it names a constructor from a type
        that is nowhere in the program.

    `ModDec`'s residue moved from a capital `Σ (R : Nat)` to a lowercase `Σ (r : Nat)`
    in `StdLemmas` for the third of those reasons: a carve extent is runtime data, and
    the comptime binder fenced it out of the returned pair. -/

/-! ### Projecting the packed invariant

    `HMInv` is a Σ chain, so reading a clause out of it is a `sigmaRec`. The motive's
    binder type has to be written as the chain ITSELF rather than as `HMInv C L N Sl`,
    because the `Pair` branch of the elim sugar reads `A` and `B` syntactically out of
    `Σ (x : A). B` and a spliced application is opaque to it — the same syntactic-read
    trap the bucket motives hit. -/

def InvCap : Term := prog{
  λ (C : Nat). λ (L : Nat). λ (N : Nat). λ (Sl : Array C Bucket).
  λ (Hi : HMInv C L N Sl).
    elim Hi return (λ (Q : Σ (Hc : Le (S Z) C).
        Σ (Hs : SlotsOk C Z C Sl).
        Σ (Hn : Id Nat N (SizeA C Sl)).
          Id Nat L (Div (Mul C 4) 5)). Le (S Z) C) {
      Pair (Hc) (Rest) => Hc } }
def InvCapTy : Term := prog{
  Π (C : Nat) → Π (L : Nat) → Π (N : Nat) → Π (Sl : Array C Bucket) →
    HMInv C L N Sl → Le (S Z) C }

def InvSlots : Term := prog{
  λ (C : Nat). λ (L : Nat). λ (N : Nat). λ (Sl : Array C Bucket).
  λ (Hi : HMInv C L N Sl).
    elim Hi return (λ (Q : Σ (Hc : Le (S Z) C).
        Σ (Hs : SlotsOk C Z C Sl).
        Σ (Hn : Id Nat N (SizeA C Sl)).
          Id Nat L (Div (Mul C 4) 5)). SlotsOk C Z C Sl) {
      Pair (Hc) (Rest) =>
        elim Rest return (λ (Q2 : Σ (Hs : SlotsOk C Z C Sl).
            Σ (Hn : Id Nat N (SizeA C Sl)).
              Id Nat L (Div (Mul C 4) 5)). SlotsOk C Z C Sl) {
          Pair (Hs) (Rest2) => Hs } } }
def InvSlotsTy : Term := prog{
  Π (C : Nat) → Π (L : Nat) → Π (N : Nat) → Π (Sl : Array C Bucket) →
    HMInv C L N Sl → SlotsOk C Z C Sl }

def InvN : Term := prog{
  λ (C : Nat). λ (L : Nat). λ (N : Nat). λ (Sl : Array C Bucket).
  λ (Hi : HMInv C L N Sl).
    elim Hi return (λ (Q : Σ (Hc : Le (S Z) C).
        Σ (Hs : SlotsOk C Z C Sl).
        Σ (Hn : Id Nat N (SizeA C Sl)).
          Id Nat L (Div (Mul C 4) 5)). Id Nat N (SizeA C Sl)) {
      Pair (Hc) (Rest) =>
        elim Rest return (λ (Q2 : Σ (Hs : SlotsOk C Z C Sl).
            Σ (Hn : Id Nat N (SizeA C Sl)).
              Id Nat L (Div (Mul C 4) 5)). Id Nat N (SizeA C Sl)) {
          Pair (Hs) (Rest2) =>
            elim Rest2 return (λ (Q3 : Σ (Hn : Id Nat N (SizeA C Sl)).
                Id Nat L (Div (Mul C 4) 5)). Id Nat N (SizeA C Sl)) {
              Pair (Hn) (Rest3) => Hn } } } }
def InvNTy : Term := prog{
  Π (C : Nat) → Π (L : Nat) → Π (N : Nat) → Π (Sl : Array C Bucket) →
    HMInv C L N Sl → Id Nat N (SizeA C Sl) }

example : chkL InvCap InvCapTy = true := by native_decide
example : chkL InvSlots InvSlotsTy = true := by native_decide
example : chkL InvN InvNTy = true := by native_decide

def slotOfP (rest : Term) : Term := prog{
  fn SlotOf (key : Nat, n : Nat, Hc : Le (S Z) n)
      -> (Σ (i : Nat). Σ (r : Nat). Σ0 (Hi : Id Nat i (Mod key n)).
            Id Nat n (Add i (S r))) {
    let s0 = Mod key n;
    let Pair(rr, hq) = (ModDec s0 n (ModLtN key n Hc)
                          : Σ (r : Nat). Id Nat n (Add s0 (S r)));
    Pair(s0, Pair(rr, Pair(Refl, hq))) };
  %rest }

example : progOk (slotOfP prog{ () }) = true := by native_decide

/-- **The opening, entire**: destructure the pack, refill the capacity, read the
    packed invariant as knowledge, project `Le 1 cap` out of it, mint the slot across
    the call, and carve the slots array three ways at the returned index. -/
def openP (rest : Term) : Term := slotOfP prog{
  fn OpenAt (self : &mut HMapT, key : Nat) -> Unit {
    let Pair(cap, Pair(load, Pair(n, Pair(slots, Hinv)))) = self;
    let c = *cap;
    *cap := c;
    let Lv = *load;
    let Nv = *n;
    let Sv = *slots;
    let Hi = *Hinv;
    let Pair(i, Pair(r, Pair(Hix, Heq))) = SlotOf(key, c, InvCap c Lv Nv Sv Hi);
    let lo = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | Heq];
    let cell = &m (*slots)[i ; 1 ; r];
    let hi = &m (*slots)[S i ; r];
    let bk = &m (*cell)[0];
    () };
  %rest }

#eval chkProg (openP prog{ () })

-- Which borrow blocks the merge? Carve only, no element borrow:
#eval chkProg (slotOfP prog{
  fn OpenA (self : &mut HMapT, key : Nat) -> Unit {
    let Pair(cap, Pair(load, Pair(n, Pair(slots, Hinv)))) = self;
    let c = *cap;
    *cap := c;
    let Lv = *load;
    let Nv = *n;
    let Sv = *slots;
    let Hi = *Hinv;
    let Pair(i, Pair(r, Pair(Hix, Heq))) = SlotOf(key, c, InvCap c Lv Nv Sv Hi);
    let lo = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | Heq];
    let cell = &m (*slots)[i ; 1 ; r];
    let hi = &m (*slots)[S i ; r];
    () };
  () })

-- The control: the same carve on a slots array that is a PARAMETER rather than a
-- component of a destructured pack.
#eval chkProg prog{
  fn OpenB (nn : Nat, i : Nat, r : Nat, Heq : Id Nat nn (Add i (S r)),
            slots : &mut (Array nn (List (Σ (k : Nat). Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | Heq];
    let cell = &m (*slots)[i ; 1 ; r];
    let hi = &m (*slots)[S i ; r];
    let bk = &m (*cell)[0];
    () };
  () }

-- (D) Take the slots array OUT of the pack, carve a local, refill.
#eval chkProg (slotOfP prog{
  fn OpenD (self : &mut HMapT, key : Nat) -> Unit {
    let Pair(cap, Pair(load, Pair(n, Pair(slots, Hinv)))) = self;
    let c = *cap;
    *cap := c;
    let Lv = *load;
    let Nv = *n;
    let Sv = *slots;
    let Hi = *Hinv;
    let Pair(i, Pair(r, Pair(Hix, Heq))) = SlotOf(key, c, InvCap c Lv Nv Sv Hi);
    let sa = *slots;
    let sb = &m sa;
    let lo = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | Heq];
    let cell = &m (*sb)[i ; 1 ; r];
    let hi = &m (*sb)[S i ; r];
    *slots := sa;
    () };
  () })

-- (F) Push the carve behind a CALL, so §6.2's opacity re-mints the caller's array
--     uncarved at the declared type — `partitionA`'s device.
#eval chkProg (slotOfP prog{
  fn CarveIt (nn : Nat, i : Nat, r : Nat, Heq : Id Nat nn (Add i (S r)),
              slots : &mut (Array nn (List (Σ (k : Nat). Nat)))) -> Unit {
    let lo = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | Heq];
    let cell = &m (*slots)[i ; 1 ; r];
    let hi = &m (*slots)[S i ; r];
    let bk = &m (*cell)[0];
    () };
  fn OpenF (self : &mut HMapT, key : Nat) -> Unit {
    let Pair(cap, Pair(load, Pair(n, Pair(slots, Hinv)))) = self;
    let c = *cap;
    *cap := c;
    let Lv = *load;
    let Nv = *n;
    let Sv = *slots;
    let Hi = *Hinv;
    let Pair(i, Pair(r, Pair(Hix, Heq))) = SlotOf(key, c, InvCap c Lv Nv Sv Hi);
    CarveIt(c, i, r, Heq, &m *slots);
    () };
  () })

-- Is it the comptime read of the array (`let Sv = *slots`) that pins it?
#eval chkProg (slotOfP prog{
  fn OpenC (self : &mut HMapT, key : Nat) -> Unit {
    let Pair(cap, Pair(load, Pair(n, Pair(slots, Hinv)))) = self;
    let c = *cap;
    *cap := c;
    let lo = &m (*slots)[Z ; Z ; Z];
    () };
  () })

/-! ### What route F establishes, and what it leaves

    `OpenF` — the carve pushed behind a call — is refused, but by a DIFFERENT and much
    better message than the others:

        audit: self's payload (Pair σ124 (Pair σ126 (Pair σ128 (Pair σ138 σ131))))
        does not have its owed type …

    The slots component is now a clean fresh σ (`σ138`) rather than a segmented
    `Arr⟨…⟩`: §6.2's opacity re-minted it at the declared type when the call's group
    ended, so the carve DID rejoin. `partitionA`'s device — "the boundary is what
    makes the program possible at all" — transfers to a pack component.

    What is left is the genuine proof obligation and not plumbing: `σ131` is the OLD
    invariant, whose type mentions the old slots, and the pack owes an invariant about
    the new ones. So the operation must write a fresh proof through `Hinv` — and,
    because opacity has erased everything about `σ138`, that proof can only come from
    the callee's OWN return type. The shape the flagship wants is therefore

        fn InsertSlots (…, slots : &mut (Array cap Bucket), Hs : SlotsOk …, Hn : …)
          -> Σ (n1 : Nat). Σ0 (Hs2 : SlotsOk cap Z cap (*slots)).
               Σ (Hn2 : Id Nat n1 (SizeA cap (*slots))). Π (q : Nat) → …

    with `Insert` writing `*n := n1` and `*Hinv := Pair(Hc, Pair(Hs2, Pair(Hn2, Hl)))`.
    That is the decomposition-shaped ensures §11 prescribes, arrived at by being told
    what the caller cannot otherwise know. -/

/-! ## 11. Towards `InsertSlots` — the bucket invariant -/

/-- `Eqb` is symmetric. Needed because `FindL q` tests `Eqb q k2` while `InsL k` tests
    `Eqb k2 k`, and the size accounting has to compare the two. -/
def EqbSym : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) (Eqb B Az)) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) (Eqb Bz Z)) {
          Z => Refl, S (B') Rb => Refl },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Eqb (S A') Bz) (Eqb Bz (S A'))) {
          Z => Refl, S (B') Rb => Ih B' } } }
def EqbSymTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Id Bool (Eqb A B) (Eqb B A) }

/-- **Inserting a well-hashed key keeps the bucket well-hashed.** This is the whole of
    the slot invariant's local obligation, and it needs no branch equation at all: in
    the overwrite arm the goal is literally the hypothesis (the key does not change),
    and in the append arm the head's clause passes through and the tail is the
    induction hypothesis. -/
def BucketAtIns : Term := prog{
  λ (C : Nat). λ (I : Nat). λ (K : Nat). λ (V : Nat). λ (B : Bucket).
    elim B return (λ (Bz : List (Σ (k : Nat). Nat)).
        BucketAt C I Bz → Id Nat (Mod K C) I → BucketAt C I (InsL K V Bz)) {
      Nil => λ (Hb : Unit). λ (Hm : Id Nat (Mod K C) I). Pair(Hm, unit),
      Cons (E) (T) Rec =>
        elim E return (λ (Ez : Σ (k : Nat). Nat).
            BucketAt C I Cons(Ez, T) → Id Nat (Mod K C) I →
              BucketAt C I (InsL K V Cons(Ez, T))) {
          Pair (K2) (V2) =>
            λ (Hb : Σ (Hh : Id Nat (Mod K2 C) I). BucketAt C I T).
            λ (Hm : Id Nat (Mod K C) I).
              elim (Eqb K2 K) return (λ (Bv : Bool).
                  BucketAt C I (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                                  Cons(Pair(K2, V), T)
                                  Cons(Pair(K2, V2), InsL K V T) Bv)) {
                True => Hb,
                False =>
                  elim Hb return (λ (Hz : Σ (Hh : Id Nat (Mod K2 C) I). BucketAt C I T).
                      Σ (Hh : Id Nat (Mod K2 C) I). BucketAt C I (InsL K V T)) {
                    Pair (H1) (H2) => Pair(H1, Rec H2 Hm) } } } } }
def BucketAtInsTy : Term := prog{
  Π (C : Nat) → Π (I : Nat) → Π (K : Nat) → Π (V : Nat) → Π (B : Bucket) →
    BucketAt C I B → Id Nat (Mod K C) I → BucketAt C I (InsL K V B) }

/-- The entry count bounds every individual bucket's length — the fact that lets a
    caller name a fuel bound from `n` alone, without reaching into a bucket. -/
def LenLeSize : Term := prog{
  λ (I : Nat). λ (L : Array I Bucket). λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket).
    LeRwR (LenE X)
      (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
      (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
      (IdSym Nat (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
                 (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
         (SizeACat (S M) (acons M X R) I L))
      (LeTrans (LenE X) (Add (LenE X) (SizeA M R))
               (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
         (LeAdd (LenE X) (SizeA M R))
         (LeAddL (Add (LenE X) (SizeA M R)) (SizeA I L))) }
def LenLeSizeTy : Term := prog{
  Π (I : Nat) → Π (L : Array I Bucket) → Π (M : Nat) → Π (X : Bucket) →
  Π (R : Array M Bucket) →
    Le (LenE X) (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R))) }

example : chkL EqbSym EqbSymTy = true := by native_decide
example : chkL BucketAtIns BucketAtInsTy = true := by native_decide
example : chkL LenLeSize LenLeSizeTy = true := by native_decide

/-! ### The bucket's size accounting

    How long a bucket is after an insert: one longer exactly when the key was absent.
    This is the last piece the counting clause needs, and it is the one place where
    `FindL`'s test order (`Eqb q k2`) and `InsL`'s (`Eqb k2 k`) have to be reconciled —
    hence `EqbSym`, applied once through `BoolRw` to bring the two scrutinees together
    before the split. -/

def LenInsM : Term := prog{
  λ (K : Nat). λ (B : Bucket).
    boolRec (λ (W : Bool). Nat) (S (LenE B)) (LenE B) (IsNoneO Nat (FindL K B)) }

/-- `S` pushes through a test. Both arms `Refl`; it exists so the step below can move
    a successor from outside a `boolRec` to inside it. -/
def SPushIf : Term := prog{
  λ (Bv : Bool). λ (A : Nat). λ (B : Nat).
    elim Bv return (λ (Bz : Bool).
        Id Nat (S (boolRec (λ (W : Bool). Nat) A B Bz))
               (boolRec (λ (W : Bool). Nat) (S A) (S B) Bz)) {
      True => Refl, False => Refl } }
def SPushIfTy : Term := prog{
  Π (Bv : Bool) → Π (A : Nat) → Π (B : Nat) →
    Id Nat (S (boolRec (λ (W : Bool). Nat) A B Bv))
           (boolRec (λ (W : Bool). Nat) (S A) (S B) Bv) }

def LenInsL : Term := prog{
  λ (K : Nat). λ (V : Nat). λ (B : Bucket).
    elim B return (λ (Bz : List (Σ (k : Nat). Nat)).
        Id Nat (LenE (InsL K V Bz)) (LenInsM K Bz)) {
      Nil => Refl,
      Cons (E) (T) Rec =>
        elim E return (λ (Ez : Σ (k : Nat). Nat).
            Id Nat (LenE (InsL K V Cons(Ez, T))) (LenInsM K Cons(Ez, T))) {
          Pair (K2) (V2) =>
            IdTrans Nat
              (LenE (InsL K V Cons(Pair(K2, V2), T)))
              (boolRec (λ (W : Bool). Nat) (S (S (LenE T))) (S (LenE T))
                 (IsNoneO Nat (boolRec (λ (W : Bool). Opt Nat)
                                 (Some Nat V2) (FindL K T) (Eqb K2 K))))
              (LenInsM K Cons(Pair(K2, V2), T))
              -- Split on `InsL`'s own test, with BOTH sides abstracted over it.
              (elim (Eqb K2 K) return (λ (Bv : Bool). Id Nat
                   (LenE (boolRec (λ (W : Bool). List (Σ (k : Nat). Nat))
                            Cons(Pair(K2, V), T)
                            Cons(Pair(K2, V2), InsL K V T) Bv))
                   (boolRec (λ (W : Bool). Nat) (S (S (LenE T))) (S (LenE T))
                      (IsNoneO Nat (boolRec (λ (W : Bool). Opt Nat)
                                      (Some Nat V2) (FindL K T) Bv)))) {
                 True => Refl,
                 False =>
                   IdTrans Nat
                     (S (LenE (InsL K V T)))
                     (S (boolRec (λ (W : Bool). Nat) (S (LenE T)) (LenE T)
                           (IsNoneO Nat (FindL K T))))
                     (boolRec (λ (W : Bool). Nat) (S (S (LenE T))) (S (LenE T))
                        (IsNoneO Nat (FindL K T)))
                     (IdCongr Nat Nat (λ (Zz : Nat). S Zz)
                        (LenE (InsL K V T)) (LenInsM K T) Rec)
                     (SPushIf (IsNoneO Nat (FindL K T)) (S (LenE T)) (LenE T)) })
              -- …then bring `FindL`'s test order into line with `InsL`'s.
              (BoolRw
                 (λ (Bw : Bool). Id Nat
                    (boolRec (λ (W : Bool). Nat) (S (S (LenE T))) (S (LenE T))
                       (IsNoneO Nat (boolRec (λ (W : Bool). Opt Nat)
                                       (Some Nat V2) (FindL K T) (Eqb K2 K))))
                    (boolRec (λ (W : Bool). Nat) (S (S (LenE T))) (S (LenE T))
                       (IsNoneO Nat (boolRec (λ (W : Bool). Opt Nat)
                                       (Some Nat V2) (FindL K T) Bw))))
                 (Eqb K2 K) (Eqb K K2) (EqbSym K2 K) Refl) } } }
def LenInsLTy : Term := prog{
  Π (K : Nat) → Π (V : Nat) → Π (B : Bucket) →
    Id Nat (LenE (InsL K V B)) (LenInsM K B) }

example : chkL SPushIf SPushIfTy = true := by native_decide
example : chkL LenInsL LenInsLTy = true := by native_decide

-- It computes: inserting a fresh key lengthens the bucket, overwriting does not.
example : chkL prog{ Refl } prog{ Id Nat (LenE (InsL 5 50 %b0)) 3 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (LenE (InsL 3 99 %b0)) 2 } = true := by native_decide

/-! ### …and the same accounting at the table

    `SizeAIns` lifts `LenInsL` through the carve: the table's entry count after
    inserting into the slot at `I` is the old count bumped exactly when the key was
    absent. This is `HMInv`'s counting clause, and with it the array-level insert's
    invariant obligations are all discharged by lemmas that are green here. -/

/-- The bump commutes with the surrounding sums. The `True` arm is one `AddSucc`; the
    `False` arm is `Refl`. -/
def AddIfBump : Term := prog{
  λ (Bv : Bool). λ (SL : Nat). λ (A : Nat). λ (SR : Nat).
    elim Bv return (λ (Bz : Bool).
        Id Nat (Add SL (Add (boolRec (λ (W : Bool). Nat) (S A) A Bz) SR))
               (boolRec (λ (W : Bool). Nat) (S (Add SL (Add A SR)))
                                            (Add SL (Add A SR)) Bz)) {
      True => AddSucc SL (Add A SR),
      False => Refl } }
def AddIfBumpTy : Term := prog{
  Π (Bv : Bool) → Π (SL : Nat) → Π (A : Nat) → Π (SR : Nat) →
    Id Nat (Add SL (Add (boolRec (λ (W : Bool). Nat) (S A) A Bv) SR))
           (boolRec (λ (W : Bool). Nat) (S (Add SL (Add A SR)))
                                        (Add SL (Add A SR)) Bv) }

def SizeAIns : Term := prog{
  λ (I : Nat). λ (L : Array I Bucket). λ (M : Nat). λ (X : Bucket).
  λ (R : Array M Bucket). λ (K : Nat). λ (V : Nat).
    IdTrans Nat
      (SizeA (Add I (S M)) (arrCat I (S M) L (acons M (InsL K V X) R)))
      (Add (SizeA I L) (Add (LenE (InsL K V X)) (SizeA M R)))
      (boolRec (λ (W : Bool). Nat)
         (S (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R))))
         (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
         (IsNoneO Nat (FindL K X)))
      -- (1) split the NEW table at the carve
      (SizeACat (S M) (acons M (InsL K V X) R) I L)
      (IdTrans Nat
         (Add (SizeA I L) (Add (LenE (InsL K V X)) (SizeA M R)))
         (Add (SizeA I L) (Add (LenInsM K X) (SizeA M R)))
         (boolRec (λ (W : Bool). Nat)
            (S (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R))))
            (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
            (IsNoneO Nat (FindL K X)))
         -- (2) rewrite the touched bucket's length by `LenInsL`
         (IdCongr Nat Nat
            (λ (Zz : Nat). Add (SizeA I L) (Add Zz (SizeA M R)))
            (LenE (InsL K V X)) (LenInsM K X) (LenInsL K V X))
         (IdTrans Nat
            (Add (SizeA I L) (Add (LenInsM K X) (SizeA M R)))
            (boolRec (λ (W : Bool). Nat)
               (S (Add (SizeA I L) (Add (LenE X) (SizeA M R))))
               (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
               (IsNoneO Nat (FindL K X)))
            (boolRec (λ (W : Bool). Nat)
               (S (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R))))
               (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
               (IsNoneO Nat (FindL K X)))
            -- (3) pull the bump out through the surrounding sums
            (AddIfBump (IsNoneO Nat (FindL K X)) (SizeA I L) (LenE X) (SizeA M R))
            -- (4) put the OLD table back together, under both arms at once
            (IdCongr Nat Nat
               (λ (Zz : Nat). boolRec (λ (W : Bool). Nat) (S Zz) Zz
                                (IsNoneO Nat (FindL K X)))
               (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
               (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
               (IdSym Nat
                  (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
                  (Add (SizeA I L) (Add (LenE X) (SizeA M R)))
                  (SizeACat (S M) (acons M X R) I L))))) }
def SizeAInsTy : Term := prog{
  Π (I : Nat) → Π (L : Array I Bucket) → Π (M : Nat) → Π (X : Bucket) →
  Π (R : Array M Bucket) → Π (K : Nat) → Π (V : Nat) →
    Id Nat (SizeA (Add I (S M)) (arrCat I (S M) L (acons M (InsL K V X) R)))
           (boolRec (λ (W : Bool). Nat)
              (S (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R))))
              (SizeA (Add I (S M)) (arrCat I (S M) L (acons M X R)))
              (IsNoneO Nat (FindL K X))) }

example : chkL AddIfBump AddIfBumpTy = true := by native_decide
example : chkL SizeAIns SizeAInsTy = true := by native_decide

/-! ### The corollaries a program actually calls

    A table is numbered from `Z`, so every use of `SlotsOkSplit`/`SlotsOkJoin` is at
    `I0 = Z` — where the middle bucket's index comes out as `Add K Z`, which does NOT
    reduce to `K` because `Add` recurses on its first argument. One `AddZero` transport
    each, done once here rather than at every call site.

    (Stating the lemmas with `Add I0 K` instead would make this use site free and cost
    a transport in both the base and the step; the split as it stands puts the whole
    cost in one place.) -/

def SlotsOkSplit0 : Term := prog{
  λ (C : Nat). λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket).
  λ (K : Nat). λ (L : Array K Bucket).
  λ (H : SlotsOk C Z (Add K (S M)) (arrCat K (S M) L (acons M X R))).
    elim (SlotsOkSplit C M X R K L Z H) return (λ (Q :
        Σ (Hl : SlotsOk C Z K L).
        Σ (Hm : BucketAt C (Add K Z) X). SlotsOk C (S (Add K Z)) M R).
        Σ (Hl : SlotsOk C Z K L).
        Σ (Hm : BucketAt C K X). SlotsOk C (S K) M R) {
      Pair (Hl) (Ht) =>
        Pair(Hl, NatRw (λ (Z0 : Nat). Σ (Hm : BucketAt C Z0 X). SlotsOk C (S Z0) M R)
                       (Add K Z) K (AddZero K) Ht) } }
def SlotsOkSplit0Ty : Term := prog{
  Π (C : Nat) → Π (M : Nat) → Π (X : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) →
    SlotsOk C Z (Add K (S M)) (arrCat K (S M) L (acons M X R)) →
      Σ (Hl : SlotsOk C Z K L). Σ (Hm : BucketAt C K X). SlotsOk C (S K) M R }

def SlotsOkJoin0 : Term := prog{
  λ (C : Nat). λ (M : Nat). λ (X : Bucket). λ (R : Array M Bucket).
  λ (K : Nat). λ (L : Array K Bucket).
  λ (Hl : SlotsOk C Z K L). λ (Hm : BucketAt C K X). λ (Hr : SlotsOk C (S K) M R).
    elim (NatRw (λ (Z0 : Nat). Σ (Hm2 : BucketAt C Z0 X). SlotsOk C (S Z0) M R)
                K (Add K Z) (IdSym Nat (Add K Z) K (AddZero K)) Pair(Hm, Hr))
      return (λ (Q : Σ (Hm2 : BucketAt C (Add K Z) X). SlotsOk C (S (Add K Z)) M R).
          SlotsOk C Z (Add K (S M)) (arrCat K (S M) L (acons M X R))) {
        Pair (Hm2) (Hr2) => SlotsOkJoin C M X R K L Z Hl Hm2 Hr2 } }
def SlotsOkJoin0Ty : Term := prog{
  Π (C : Nat) → Π (M : Nat) → Π (X : Bucket) → Π (R : Array M Bucket) →
  Π (K : Nat) → Π (L : Array K Bucket) →
    SlotsOk C Z K L → BucketAt C K X → SlotsOk C (S K) M R →
      SlotsOk C Z (Add K (S M)) (arrCat K (S M) L (acons M X R)) }

example : chkL SlotsOkSplit0 SlotsOkSplit0Ty = true := by native_decide
example : chkL SlotsOkJoin0 SlotsOkJoin0Ty = true := by native_decide


/-! ## 12. The executing differential

    Checking is half the claim; the other half is that the concrete machine agrees.
    ArraySort's §(vi) is the precedent and the reason this is not a formality — its
    executing side found three `Drop`-empty bugs the symbolic side could never reach.

    **The port is Aeneas' own `test1`, and it is faithful rather than adapted.** That
    test uses capacity 32 and the keys 0, 128, 1024 and 1056, which are chosen so that
    all four hash to slot 0 — `Mod k 32 = 0` for every one of them, asserted below. So
    `test1` IS a single-bucket exercise: it is written to make the association list do
    the work, and running it against `InsertInList` on one bucket reproduces exactly
    the collision behaviour it was designed to exercise. The overwrite step (Aeneas
    reaches it through `get_mut`) is an insert at a key already present, which is the
    same bucket operation.

    E2E rule: every assertion below is runs-to-X or accepted/rejected. -/

-- The four keys really do collide, at the capacity the Rust uses.
example : (pv prog{ Mod 0 32 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod %(Term.nat 128) 32 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod %(Term.nat 1024) 32 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod %(Term.nat 1056) 32 }).natOf? == Option.some 0 := by native_decide
-- …and the hash is not constant: 1057 lands one slot along.
example : (pv prog{ Mod %(Term.nat 1057) 32 }).natOf? == Option.some 1 := by native_decide

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
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

/-- The trusted Lean-side reference: `insert_in_list`'s specification, written again
    in a different language so that agreeing with it means something. -/
def insRef : List (Nat × Nat) → Nat → Nat → List (Nat × Nat)
  | [], k, v => [(k, v)]
  | (k2, v2) :: t, k, v => if k2 == k then (k2, v) :: t else (k2, v2) :: insRef t k v

def refRun (ops : List (Nat × Nat)) : List (Nat × Nat) :=
  ops.foldl (fun b kv => insRef b kv.1 kv.2) []

/-- Build the caller: start from an empty bucket, run each insert through a fresh
    reborrow, then read the owner back. The fuel bound is `Le (LenE …) 40` at a
    concrete bucket, which computes to `Unit`, so `unit` discharges it and the caller
    CHECKS as well as runs. -/
def iilOps : List (Nat × Nat) → Nat → Term
  | [], _ => .letIn ⟨99, "y"⟩ (.var ⟨0, "z"⟩) .unit
  | (k, v) :: rest, i =>
      .letIn ⟨i, "b"⟩ (.borrow (.var ⟨0, "z"⟩))
        (.seq (.call "InsertInList"
                 [Term.nat 40, Term.nat k, Term.nat v, .var ⟨i, "b"⟩, .unit])
              (iilOps rest (i + 1)))

def iilCaller (ops : List (Nat × Nat)) : Term :=
  iilP (.letIn ⟨0, "z"⟩ prog{ Nil } (iilOps ops 1))

def iilRun (ops : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  match Dllbc.Tests.S9Diff.runExec (iilCaller ops) with
  | .ok env => (env.lookup "y").bind (entriesOfV 2000)
  | .error _ => none

/-! **The keys are scaled, and here is exactly why.** Running the literal Aeneas keys
    (0, 128, 1024, 1056) exhausts the interpreter's `defaultFuel`: `Nat` is unary, so
    `Term.nat 1056` is a 1056-deep tower of `S` and one `Eqb` between two such keys is
    a thousand reduction steps. That is the already-disclosed Nat divergence showing up
    as a cost rather than as a soundness gap — the SYMBOLIC side is unaffected (the
    `Mod k 32 = 0` assertions above are at the real keys and pass), and it is only the
    concrete run that cannot afford them.

    `test1Small` is the same test at capacity 8 with keys 0, 8, 16 and 24: four keys
    that all hash to slot 0, inserted in order, then the third overwritten. Every
    structural feature `test1` was written to exercise — the empty-bucket refill, the
    append chain, and an in-place overwrite in the middle of a collision list — is
    present. -/

example : (pv prog{ Mod 0 8 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod 8 8 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod 16 8 }).natOf? == Option.some 0 := by native_decide
example : (pv prog{ Mod 24 8 }).natOf? == Option.some 0 := by native_decide

def test1Small : List (Nat × Nat) := [(0, 42), (8, 18), (16, 138), (24, 256), (16, 56)]

-- **The differential.** The checked program and the trusted reference agree.
example : iilRun test1Small == Option.some (refRun test1Small) := by native_decide
-- …and pinned literally, so a change to either side is visible rather than merely
-- consistent: the overwrite landed IN PLACE at 16 and appended nothing.
example : iilRun test1Small
    == Option.some [(0, 42), (8, 18), (16, 56), (24, 256)] := by native_decide

/-! ### The program that runs is the program that was checked — with ONE call

    A single-insert caller CHECKS as well as runs: the bucket is the literal `Nil`, so
    `Le (LenE (*b)) 40` computes to `Unit` and `unit` discharges it.

    **A caller with two or more inserts does not check, and the reason is worth having
    in the record**: `call: comptime argument (unit) does not have its parameter type
    (natRec …)`. After the first call, §6.2's opacity has re-minted `z` as a fresh σ,
    so at the second call `LenE (*b)` is a stuck `listRec` under `Le` rather than a
    numeral, and no `unit` inhabits it. The caller has LOST the bucket's length at the
    call boundary.

    This is the same admission `HmProbeArrays` §A5' made about its `λ B. unit`, arrived
    at from the other side, and it is not a defect of the proof — it is the missing
    capability that `12-design-borrow-refounding.md` is about. The repair is for
    `InsertInList` to return a length bound (`Le (LenE (*b)) (S (LenE (old *b)))`) so a
    caller can chain it, which is one more bucket induction and one more conjunct; it
    is not attempted here.

    The E2E rule admits accepted/rejected OR runs-to-X, so the sequences below are
    asserted as runs-to-X and the checkable single call is asserted as accepted. -/

example : progOk (iilCaller [(7, 1)]) = true := by native_decide
example : progRejects (iilCaller test1Small) "does not have its parameter type" = true := by
  native_decide

-- Smaller shapes, each exercising one path: the `Nil` refill, a pure append chain,
-- an overwrite at the head, and an overwrite at the tail.
example : iilRun [(7, 1)] == Option.some [(7, 1)] := by native_decide
example : iilRun [(1, 1), (2, 2), (3, 3)] == Option.some [(1, 1), (2, 2), (3, 3)] := by
  native_decide
example : iilRun [(1, 1), (2, 2), (1, 9)] == Option.some [(1, 9), (2, 2)] := by native_decide
example : iilRun [(1, 1), (2, 2), (2, 9)] == Option.some [(1, 1), (2, 9)] := by native_decide

-- The checking and executing sides agree about the program that checks (M9's
-- simulation property, the assertion ArraySort's §(vi.c) makes for `quicksortA`).
example : Dllbc.Tests.S9Diff.diffV2 (iilCaller [(7, 1)]) = true := by native_decide

/-- `New` runs too, at a symbolic capacity, and the table it builds is the right
    length and empty. -/
def newRun (cap : Nat) : Term :=
  newP (.letIn ⟨0, "h"⟩ (.call "New" [Term.nat cap, .unit])
         (.letIn ⟨1, "y"⟩ (.var ⟨0, "h"⟩) .unit))
example : progOk (newRun 4) = true := by native_decide
example : (Dllbc.Tests.S9Diff.runExec (newRun 4)).isOk = true := by native_decide

end Dllbc.Tests.HashMap
end
