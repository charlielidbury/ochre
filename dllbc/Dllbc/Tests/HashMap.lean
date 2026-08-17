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

end Dllbc.Tests.HashMap
end
