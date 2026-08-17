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

end Dllbc.Tests.HashMap
end
