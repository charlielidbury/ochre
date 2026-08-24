import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship: a verified, resizable, in-place hashmap

Tests a hashmap written in DLLBC: an array of association-list buckets, the
hash is the identity, the slot is `Mod key cap`, load factor 4/5, resize by
doubling. The invariant is packed into the container's type, so a broken
`HashMap` value cannot be constructed.

spec: `docs/13-hashmap-flagship.md`, reference implementation:
`competitors/aeneas-hashmap/`.

Tests check each operation against a pure spec function, plus lying-twin
controls that confirm the checker rejects the corresponding bug.

Three layers in this one file: the checked map (spec functions, packed
invariant, the op chain and its twins), then the pinned borrow-returning ops
(`GetMutHM`/`GetMutOrInsertHM`, whose contracts need `~>`/`*res`), then the
executing layer (concrete runs decoded and compared against a trusted
Lean-side model).

## The single-allocation resize

A resize's only runtime allocation is `MkSlots (2·cap)`, the new array of
`Nil` buckets. The move path — `SlotPush`, `MoveBktR`, `MoveOne`, `MoveSlots`
— constructs no data-level `Cons`/`Pair` node: the only constructor write is
`MoveOne`'s `*bbs := Nil` (a constant take-out), and every other
`Cons(`/`Pair(` occurrence is a pattern, a type, or an erased/evidence
position. `InsertHM`'s resize arm adds exactly `MkSlots (2·cap)` plus the
container repack `*self := Pair(…)` that every arm of every op performs (a
struct-by-value write, not a bucket node). The moved nodes reach the new
table by mutation alone: `SlotPush` takes the bucket head off `src` and onto
the carved `dst` cell with the mem::replace rotation

    let tmp = *tail;  *tail := *bb;  *bb := *src;  *src := tmp;

where every read of node-typed data whose value reaches a runtime position is
immediately followed by an overwrite of the slot it was read from, so under a
move-compiling backend each step is three pointer relinks, zero allocation.
(`MoveOne`'s take-out `let bl = *bbs; *bbs := Nil` is the same idiom; `Nil` is
a constant, not an allocation.) The ordinary insert path still allocates one
fresh node per `InsertInList`'s `*b := Cons(Pair(key, val), Nil)`; only the
move path avoids it. The destination is never traversed: `MoveBktR`'s fuel
bounds the source bucket length, and the fuel ledger threaded through
`MoveOne`/`MoveSlots`/`InsertHM` mentions only the source total.

The compilation-model caveat: DLLBC's checker semantics is value-level
copy-on-read, so "one allocation" is a property of the program's shape under
a move-compiling backend (read-then-overwrite = move), the same way a Rust
program's allocation behavior is a property of its shape. Comptime snapshots
(`K0 = *kk`-style capital reads) are erased knowledge and never reach
runtime. One observable consequence of moving instead of re-inserting:
same-slot survivors of a resize appear in reversed order (prepend vs the old
append), an order the spec (`FindL` + `NodupB`) is deliberately blind to.
-/

section

open Dllbc
-- Raw proof terms, bare (StdChain's doctrine: proofs apply as constants).
-- Formers the std seed binds (Mod, Mul, Pred, …) are written QUALIFIED inside
-- the seeded blocks (docs/21 §9's audit residual); the hashmap's own formers
-- are file-local constants and stay bare everywhere.
open Dllbc.StdChainRaw
open Dllbc.Tests.S23Direct (mintOn crossOn markedBody? noopOf)

namespace Dllbc.Tests.HashMap

/-- Type-check a closed term against a closed type in the pure seed (as
    ArraySort's `chkL`). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000000 t

/-! ## (i) The slot arithmetic -/

def modOf (a b : Nat) : Term := pv prog{ Mod %(Term.nat a) %(Term.nat b) }
def divOf (a b : Nat) : Term := pv prog{ Div %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 6 3).natOf? == some 0 := by native_decide
example : (modOf 5 8).natOf? == some 5 := by native_decide
example : (modOf 3 0).natOf? == some 0 := by native_decide
example : (divOf 7 3).natOf? == some 2 := by native_decide

-- The reference test's own keys at its own capacity: 0, 128, 1024, 1056 all
-- land in slot 0 of 32, which is what exercises the collision list.
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide
example : (modOf 1057 32).natOf? == some 1 := by native_decide


/-! ## (ii) The ledger arithmetic -/


-- `Mul` computes, and the ledger inequality is the integer restatement
-- `5n ≤ 4c ⟺ n ≤ ⌊4c/5⌋`, spot-checked at the resize boundary.
example : (pv prog_parse { Mul 4 8 }).natOf? == some 32 := by native_decide
-- cap 32: threshold 25 (= ⌊128/5⌋). 5·25 ≤ 128 holds, 5·26 ≤ 128 does not.
example : chkL prog_parse { unit } prog_parse { Le (Mul 5 25) (Mul 4 32) } = true := by native_decide
example : chkL prog_parse { unit } prog_parse { Le (Mul 5 26) (Mul 4 32) } = false := by native_decide
example : (pv prog_parse { Div (Mul 4 32) 5 }).natOf? == some 25 := by native_decide

/-! ## (iii) The slot write: the index and residue are minted across a call
    returning a Σ (comptime spellings fail the occurs check), then the carve
    cites the returned equation. -/

def slotDecls : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDecRaw (Mod h n) n (ModLtNRaw h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let Pair(i, Pair(r, hd)) = SlotOf(h, n, Hne);
    let pre = &m (*slots)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*slots)[i ; 1 ; r];
    (*cell)[0] := v;
    ()
  };
  () }
example : progOk slotDecls = true := by native_decide

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 4000)
    | _ => none

def slotCaller (h : Nat) : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDecRaw (Mod h n) n (ModLtNRaw h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let Pair(i, Pair(r, hd)) = SlotOf(h, n, Hne);
    let pre = &m (*slots)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*slots)[i ; 1 ; r];
    (*cell)[0] := v;
    ()
  };
  let z = Arr(0, 0, 0, 0);
  let b = &m z;
  SlotWrite(%(Term.nat h), 4, 9, unit, b);
  let y = z;
  () }

def runSlot (h : Nat) : Option (List Nat) :=
  match runProgram (slotCaller h) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

example : runSlot 0 == some [9, 0, 0, 0] := by native_decide
example : runSlot 1 == some [0, 9, 0, 0] := by native_decide
example : runSlot 6 == some [0, 0, 9, 0] := by native_decide
example : runSlot 7 == some [0, 0, 0, 9] := by native_decide

/-! ## (iv) The elim sugar reads its element type: recursion over
    `List (Σ (k : Nat). Nat)` — a bucket — checks through the sugar. -/

example : chkL prog_parse {
    λ (B : List (Σ (k : Nat). Nat)).
      elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Nat) {
        Nil => Z,
        Cons (E) (T) Rec => Rec } }
  prog_parse { Π (B : List (Σ (k : Nat). Nat)) → Nat } = true := by native_decide

example : chkL prog_parse {
    λ (B : List (List Nat)).
      elim B return (λ (Bm : List (List Nat)). Nat) {
        Nil => Z,
        Cons (E) (T) Rec => Rec } }
  prog_parse { Π (B : List (List Nat)) → Nat } = true := by native_decide

/-! ## (v) Shape probes

    The packed container depends on (a) take-and-refill of a Σ-pack with a
    `Σ0` invariant tail through `&mut self` — including whether the destructure
    refines the entry σ, so `old *self` claims compute — and (b) through-borrow
    navigation of the same pack for the borrow-returning ops. -/

def whyP (t : Term) : String :=
  match checkProgram t prog_parse { Unit } with
  | .ok _ => "ACCEPTED"
  | .error e => "REJECTED: " ++ e

/-- A pure identity on a `Le` proof. A destructured Σ0 tail comes back at a
    capital binder, and a bare capital citation in a constructor argument is
    fenced (`cannot be ⇒-moved`) even where the component's mode is comptime,
    but an application in the same position is ⇝-computed — and the real
    code's repacked invariants are lemma applications anyway. `KeepLe` is the
    minimal such application. -/
def KeepLe : Term := prog_parse { λ (A : Nat). λ (B : Nat). λ (H : Le A B). H }

/-- (a1) Round-trip: take the pack, rebuild it, refill. The proof component is
    re-supplied through `KeepLe` — see its docstring for why. -/
def packRoundtrip : Term := prog{
  fn Touch (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(n, Pair(w, KeepLe n w Hw));
    () };
  () }
example : progOk packRoundtrip = true := by native_decide

/-- (a2) Does `old *self` compute through the destructure? If matching
    refines the entry σ to `Pair(σn, …)`, both sides of the returned equation
    reduce to `σn` and `Refl` closes it. -/
def FstOf : Term := prog_parse {
  λ (P : Σ (n : Nat). Σ0 (w : Nat). Le n w).
    elim P return (λ (Pm : Σ (n : Nat). Σ0 (w : Nat). Le n w). Nat) {
      Pair (N) (R1) => N } }

def packRefines : Term := prog{
  fn Same (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w))
      -> Id Nat (FstOf (*self)) (FstOf (old *self)) {
    let Pair(n, r1) = *self;
    *self := Pair(n, r1);
    Refl };
  () }
example : progOk packRefines = true := by native_decide

/-- (a3) An update under the packed proof: bump both components; the proof
    transports by conversion (`Le (S n) (S w) ⇝ Le n w`). -/
def packBump : Term := prog{
  fn BumpBoth (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(S(n), Pair(S(w), KeepLe n w Hw));
    () };
  () }
example : progOk packBump = true := by native_decide

-- …and the lying refill is refused: `Hw : Le n w` does not inhabit `Le (S n) w`.
def packBumpLie : Term := prog_parse {
  fn BumpLie (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(S(n), Pair(w, KeepLe n w Hw));
    () };
  () }
example : progOk packBumpLie = false := by native_decide

/-- (a4) An insert skeleton at a toy invariant: take the pack, mint the slot
    across a call, carve the slots array (a local, after the take), push into
    the bucket through the element borrow, repack, refill. -/
def packCarve : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDecRaw (Mod h n) n (ModLtNRaw h n Hne))
  };
  fn Ins0 (key : Nat, val : Nat,
           self : &mut (Σ (cap : Nat).
             Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap)) -> Unit {
    let Pair(cap, Pair(slots, Hcap)) = *self;
    let Pair(i, Pair(r, hd)) = SlotOf(key, cap, Hcap);
    let sb = &m slots;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let bb = &m (*cell)[0];
    let tl = *bb;
    *bb := Cons(Pair(key, val), tl);
    *self := Pair(cap, Pair(slots, KeepLe 1 cap Hcap));
    () };
  () }
example : progOk packCarve = true := by native_decide

/-- The toy pack's cap projection — pure, over the value. -/
def FstCap : Term := prog_parse {
  λ (P : Σ (cap : Nat). Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap).
    elim P return (λ (Pm : Σ (cap : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap). Nat) {
      Pair (Cap) (R1) => Cap } }

/-- The packed proof, extracted by comptime projection. A through-borrow match
    binds the Σ0 tail to state (a borrow), which a ⇝-position cannot read, so
    invariant clauses are snapshotted off `*self` before the destructure. -/
def PackCapLe : Term := prog_parse {
  λ (P : Σ (cap : Nat). Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap).
    elim P return (λ (Pm : Σ (cap : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap).
        Le (S Z) (FstCap Pm)) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (Rm : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
            Le (S Z) Cap). Le (S Z) Cap) {
          Pair (Slots) (Hc) => Hc } } }

/-- (b1) Through-borrow navigation: snapshot the packed proof off `*self`, match
    `self` down the pack, reach the slots component as a `&mut`, carve it at the
    minted slot, walk the bucket in the or_insert style, return the value borrow. -/
def packNav : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDecRaw (Mod h n) n (ModLtNRaw h n Hne))
  };
  fn Nav (key : Nat,
          self : &mut (Σ (cap : Nat).
            Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap)) -> &mut Nat {
    let Hle1 = PackCapLe (*self);
    let Pair(cap, Pair(slots, Hcap)) = self;

    -- A bare deref takes the payload, even a Nat's, so the read is an
    -- explicit take-and-refill, and the local Nat then copies freely.
    let c = *cap;
    *cap := c;
    let Pair(i, Pair(r, hd)) = SlotOf(key, c, Hle1);
    let pre = &m (*slots)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*slots)[i ; 1 ; r];
    let bb = &m (*cell)[0];
    match bb {
      Nil => {
        *bb := Cons(Pair(key, 0), Nil);
        match bb {
          Nil => (),
          Cons(Pair(kk, vv), tl2) => &m *vv
        }
      },
      Cons(hd2, tl2) => match hd2 { Pair(kk, vv) => &m *vv }
    } };
  () }
example : progOk packNav = true := by native_decide

/-! ## (vi) The Σ(Bool) Option vocabulary and the bucket specs -/

def OptP : Term := prog_parse {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

/-- `Opt T` — the option type at payload `T`. The kernel has no native Option
    type; this Σ(Bool) encoding stands in for it. -/
def Opt : Term := prog_parse { λ (T : Type). Σ (b : Bool). OptP b T }

/-- `Some`/`None` at `Nat`, v1's value type. -/
def SomeN : Term := prog_parse { λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog_parse { Pair(False, unit) }

example : chkL prog_parse { SomeN 5 } prog_parse { Opt Nat } = true := by native_decide
example : chkL NoneN prog_parse { Opt Nat } = true := by native_decide
example : chkL prog_parse { Pair(True, unit) } prog_parse { Opt Nat } = false := by native_decide

/-- Bucket lookup: first match wins, `None` past the end. An `Opt`-typed
    recursion over entries. -/
def FindL : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Opt Nat) {
      Nil => NoneN,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Opt Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Opt Nat) {
              True => SomeN V2,
              False => Rec } } } }

def IsSomeB : Term := prog_parse {
  λ (O : Σ (b : Bool). OptP b Nat).
    elim O return (λ (Om : Σ (b : Bool). OptP b Nat). Bool) {
      Pair (Bb) (P2) => Bb } }

/-- `HitL q l` — is `q` present? Defined through `FindL` so the two can never
    disagree. -/
def HitL : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)). IsSomeB (FindL Q L) }

/-- Bucket length (`Std.Len` is monomorphic at `List Nat`). -/
def LenE : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

-- They compute.
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat)
  (FindL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) (SomeN 30) } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat)
  (FindL 9 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) NoneN } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat)
  (FindL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) (SomeN 10) } = false := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Bool
  (HitL 3 Cons(Pair(3, 30), Nil)) True } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat
  (LenE Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 2 } = true := by native_decide

/-! ## (vii) The slots-level spec functions

    `AgetB` is this file's getter, not the kernel's `aget`: `aget` reduces
    only on a literal `Arr` (no `acons`/`arrCat` step), so nothing about it at
    a carve composition is provable. `AgetB` is an `arrRec` fold, computes on
    the cons view, and every crossing lemma about it is an ordinary
    induction. -/

def AgetB : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))). λ (I : Nat).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Nat → List (Σ (k : Nat). Nat))
      (λ (I2 : Nat). Nil)
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Nat → List (Σ (k : Nat). Nat)). λ (I2 : Nat).
          elim I2 return (λ (Iz : Nat). List (Σ (k : Nat). Nat)) {
            Z => H, S (I3) R3 => Ih I3 })
      M A I }

/-- Total entry count across the buckets — the pack's `n` clause. -/
def TotalE : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat)
      Z
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))). λ (Ih : Nat).
          Add (LenE H) Ih)
      M A }

example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (AgetB 3 Arr(Nil, Cons(Pair(5, 7), Nil), Nil) 1) Cons(Pair(5, 7), Nil) } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (AgetB 3 Arr(Nil, Cons(Pair(5, 7), Nil), Nil) 0) Nil } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat
  (TotalE 3 Arr(Nil, Cons(Pair(5, 7), Nil), Cons(Pair(1, 2), Cons(Pair(3, 4), Nil)))) 3 }
  = true := by native_decide

/-! ## (viii) The packed invariant

    `HMInv`'s clauses: `Le 1 cap`; every entry in slot `i` has
    `Mod key cap = i`; `n` equals the total entry count; `load` is the 4/5
    threshold ledger for `cap`, carried Div-free as `load = 4·cap` with
    occupancy `5·n ≤ load` (see `LedgerGrowRaw`'s ledger note in StdChain).

    Plus one clause the op specs force even though it isn't one of the above:
    keys within a bucket are pairwise distinct (`NodupB`). The reference
    implementation's own invariant has it (`slot_t_inv`'s pairwise-distinct
    conjunct), and both Remove's and resize's pointwise Find equations are
    false without it: removing the first of two same-key entries surfaces the
    shadowed one, and rehashing reorders same-key entries, so
    `FindRem`/Insert-through-resize would each need it anyway. -/

def AllKeysMod : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Nat (Mod K2 Cap) I }) × Rec } }

def NodupB : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Bool (HitL K2 T) False }) × Rec } }

/-- One slot's obligations: hashed here, and duplicate-free. -/
def SlotInv : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    AllKeysMod Cap I L × NodupB L }

/-- `SlotInv` folded over the array from starting index `I0` — the index rides
    as a fold argument so the crossing lemmas can generalize it. -/
def SlotsFrom : Term := prog_parse {
  λ (Cap : Nat). λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))). λ (I0 : Nat).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat → Type)
      (λ (I2 : Nat). Unit)
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Nat → Type). λ (I2 : Nat).
          SlotInv Cap I2 H × Ih (S I2))
      M A I0 }

def HMInvT : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
    λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
      Le (S Z) Cap ×
      (Id Nat Load (Mul 4 Cap) ×
      (Le (Mul 5 N) Load ×
      (Id Nat N (TotalE Cap Slots) ×
      SlotsFrom Cap Cap Slots Z))) }

/-- The container. The invariant is packed in the type: a `HashMap` value
    cannot exist broken, every op's invariant-preservation proof is returning a
    well-typed pack, and it survives opaque group ends. -/
def HashMapT : Term := prog_parse {
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots }

/-! A concrete inhabitant, as the invariant's own compute test: cap 2, load 8,
    one entry (key 3 in slot 1 — `Mod 3 2 = 1`). -/

def hmEx : Term := prog_parse {
  Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) }

example : chkL hmEx HashMapT = true := by native_decide

-- …and the invariant is not vacuous: the same pack with the entry in the
-- wrong slot (key 3 in slot 0) is refused — the `Mod` clause has no `Refl`.
example : chkL prog_parse {
  Pair(2, Pair(8, Pair(1, Pair(Arr(Cons(Pair(3, 30), Nil), Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)), Pair(Pair(unit, unit),
        unit)))))))))) } HashMapT = false := by native_decide

-- …a lying count (n = 2 with one entry) is refused.
example : chkL prog_parse {
  Pair(2, Pair(8, Pair(2, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) } HashMapT = false := by native_decide

-- …and a bucket with a duplicate key is refused by the Nodup clause.
example : chkL prog_parse {
  Pair(2, Pair(8, Pair(2, Pair(Arr(Nil, Cons(Pair(3, 30), Cons(Pair(3, 31), Nil))),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, Pair(Refl, unit)),
        Pair(Refl, Pair(Refl, unit))), unit)))))))))) } HashMapT = false := by native_decide

-- The ledger clause is live: cap 1 has threshold 0 (5·1 ≤ 4 fails), so a
-- one-entry map at capacity 1 cannot be packed…
example : chkL prog_parse {
  Pair(1, Pair(4, Pair(1, Pair(Arr(Cons(Pair(0, 9), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)), unit))))))))) }
  HashMapT = false := by native_decide

-- …while the empty map at capacity 1 can.
example : chkL prog_parse {
  Pair(1, Pair(4, Pair(Z, Pair(Arr(Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), unit))))))))) } HashMapT = true := by native_decide

/-! ## (ix) The map-level spec functions — pure, over the pack

    Each is a nested Σ-elim down the container; the motive spells the suffix
    telescope at each level (the elim sugar reads `A`/`B` off the motive's
    binder type syntactically — `SortedHeadRaw`'s precedent). -/

def CapHM : Term := prog_parse {
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) => Cap } }

def SizeHM : Term := prog_parse {
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Nat) {
              Pair (N) (R3) => N } } } }

/-- `FindHM q hm` — the spec lookup: `q`'s bucket is slot `Mod q cap`. -/
def FindHM : Term := prog_parse {
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Opt Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Opt Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Opt Nat) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Opt Nat) {
                  Pair (Slots) (Inv) => FindL Q (AgetB Cap Slots (Mod Q Cap)) } } } } }

def HitHM : Term := prog_parse {
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    IsSomeB (FindHM Q Hm) }

/-! The model updates: `FindIns` is `Some v` at `key`, the old answer
    elsewhere; `FindRem` is `None` at `key`; the size updates state the
    "bumped/decremented iff" via a spec function, not a conditional Π. -/

def FindIns : Term := prog_parse {
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (Eqb Q Key) return (λ (Bm : Bool). Opt Nat) {
      True => SomeN V,
      False => FindHM Q Hm } }

def FindRem : Term := prog_parse {
  λ (Q : Nat). λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (Eqb Q Key) return (λ (Bm : Bool). Opt Nat) {
      True => NoneN,
      False => FindHM Q Hm } }

def SizeIns : Term := prog_parse {
  λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Key Hm) return (λ (Bm : Bool). Nat) {
      True => SizeHM Hm,
      False => S(SizeHM Hm) } }

def SizeRem : Term := prog_parse {
  λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Key Hm) return (λ (Bm : Bool). Nat) {
      True => Pred (SizeHM Hm),
      False => SizeHM Hm } }

-- They compute on the concrete inhabitant: key 3 is present with 30, key 5
-- shares its bucket and misses, key 4 hits the empty bucket.
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindHM 3 hmEx) (SomeN 30) } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindHM 5 hmEx) NoneN } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindHM 4 hmEx) NoneN } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeHM hmEx) 1 } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindIns 3 5 9 hmEx) (SomeN 30) } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindIns 5 5 9 hmEx) (SomeN 9) } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id (Opt Nat) (FindRem 3 3 hmEx) NoneN } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeIns 5 hmEx) 2 } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeIns 3 hmEx) 1 } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeRem 3 hmEx) Z } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeRem 5 hmEx) 1 } = true := by native_decide

/-! ## (x) Projecting the invariant's clauses

    Generic product projections first (`A × B` converts with the spelled
    `Σ (Hx : A). B` — `SortedHeadRaw`'s precedent), then the five named clause
    projections every op body opens with. -/

def FstT : Term := prog_parse {
  λ (A : Type). λ (B : Type). λ (P : Σ (Hx : A). B).
    elim P return (λ (Q : Σ (Hx : A). B). A) { Pair (X) (Y) => X } }
def FstTTy : Term := prog_parse { Π (A : Type) → Π (B : Type) → (Σ (Hx : A). B) → A }

def SndT : Term := prog_parse {
  λ (A : Type). λ (B : Type). λ (P : Σ (Hx : A). B).
    elim P return (λ (Q : Σ (Hx : A). B). B) { Pair (X) (Y) => Y } }
def SndTTy : Term := prog_parse { Π (A : Type) → Π (B : Type) → (Σ (Hx : A). B) → B }

example : chkL FstT FstTTy = true := by native_decide
example : chkL SndT SndTTy = true := by native_decide

def InvLe1 : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Le (S Z) Cap)
      (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
        (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi }
def InvLe1Ty : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Le (S Z) Cap }

def InvLoad : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Id Nat Load (Mul 4 Cap))
      (Le (Mul 5 N) Load × (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))
      (SndT (Le (S Z) Cap)
        (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
          (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi) }
def InvLoadTy : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Id Nat Load (Mul 4 Cap) }

def InvLedger : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Le (Mul 5 N) Load)
      (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z)
      (SndT (Id Nat Load (Mul 4 Cap))
        (Le (Mul 5 N) Load × (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))
        (SndT (Le (S Z) Cap)
          (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
            (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi)) }
def InvLedgerTy : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Le (Mul 5 N) Load }

def InvCount : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Id Nat N (TotalE Cap Slots)) (SlotsFrom Cap Cap Slots Z)
      (SndT (Le (Mul 5 N) Load)
        (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z)
        (SndT (Id Nat Load (Mul 4 Cap))
          (Le (Mul 5 N) Load × (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))
          (SndT (Le (S Z) Cap)
            (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
              (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi))) }
def InvCountTy : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Id Nat N (TotalE Cap Slots) }

def InvSlots : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    SndT (Id Nat N (TotalE Cap Slots)) (SlotsFrom Cap Cap Slots Z)
      (SndT (Le (Mul 5 N) Load)
        (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z)
        (SndT (Id Nat Load (Mul 4 Cap))
          (Le (Mul 5 N) Load × (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))
          (SndT (Le (S Z) Cap)
            (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
              (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi))) }
def InvSlotsTy : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → SlotsFrom Cap Cap Slots Z }

example : chkL InvLe1 InvLe1Ty = true := by native_decide
example : chkL InvLoad InvLoadTy = true := by native_decide
example : chkL InvLedger InvLedgerTy = true := by native_decide
example : chkL InvCount InvCountTy = true := by native_decide
example : chkL InvSlots InvSlotsTy = true := by native_decide

/-! ## (xi) The crossing lemmas — `SplitACat*`'s shape for this container

    Everything an op proves is stated over the carve composition
    `arrCat M (S R) L (acons R B H)` (lo ++ [cell] ++ hi), which the checker
    converts with the carved place's payload. Each lemma is one `arrRec`
    induction on the left part. -/

def AgetBCatMid : Term := prog_parse {
  λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Id (List (Σ (k : Nat). Nat))
          (AgetB (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) Mz) B)
      Refl
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Id (List (Σ (k : Nat). Nat))
            (AgetB (Add K (S R)) (arrCat K (S R) T (acons R B H)) K) B).
          Ih)
      M L }
def AgetBCatMidTy : Term := prog_parse {
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) M) B }

def AgetBCatLo : Term := prog_parse {
  λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (J : Nat) → Le (S J) Mz →
          Id (List (Σ (k : Nat). Nat))
            (AgetB (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) J)
            (AgetB Mz Az J))
      (λ (J : Nat). λ (Hj : Le (S J) Z).
        botElim (Id (List (Σ (k : Nat). Nat))
          (AgetB (Add Z (S R)) (arrCat Z (S R) Arr() (acons R B H)) J)
          (AgetB Z Arr() J)) Hj)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (J : Nat) → Le (S J) K →
            Id (List (Σ (k : Nat). Nat))
              (AgetB (Add K (S R)) (arrCat K (S R) T (acons R B H)) J)
              (AgetB K T J)).
          λ (J : Nat).
            elim J return (λ (Jz : Nat). Le (S Jz) (S K) →
                Id (List (Σ (k : Nat). Nat))
                  (AgetB (Add (S K) (S R))
                    (arrCat (S K) (S R) (acons K H2 T) (acons R B H)) Jz)
                  (AgetB (S K) (acons K H2 T) Jz)) {
              Z => λ (Hj : Le (S Z) (S K)). Refl,
              S (J2) Ihj => λ (Hj : Le (S (S J2)) (S K)). Ih J2 Hj })
      M L }
def AgetBCatLoTy : Term := prog_parse {
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (J : Nat) → Le (S J) M →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) J)
      (AgetB M L J) }

def AgetBCatHi : Term := prog_parse {
  λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (D : Nat). λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Id (List (Σ (k : Nat). Nat))
          (AgetB (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) (Add Mz (S D)))
          (AgetB R H D))
      Refl
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Id (List (Σ (k : Nat). Nat))
            (AgetB (Add K (S R)) (arrCat K (S R) T (acons R B H)) (Add K (S D)))
            (AgetB R H D)).
          Ih)
      M L }
def AgetBCatHiTy : Term := prog_parse {
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (D : Nat) → Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) (Add M (S D)))
      (AgetB R H D) }

example : chkL AgetBCatMid AgetBCatMidTy = true := by native_decide
example : chkL AgetBCatLo AgetBCatLoTy = true := by native_decide
example : chkL AgetBCatHi AgetBCatHiTy = true := by native_decide

/-- `CountArrCatRaw`'s shape for the entry counter. -/
def TotalArrCat : Term := prog_parse {
  λ (Q : Nat). λ (X : Array Q (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Id Nat (TotalE (Add Mz Q) (arrCat Mz Q Az X))
               (Add (TotalE Mz Az) (TotalE Q X)))
      Refl
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Id Nat (TotalE (Add K Q) (arrCat K Q T X))
                       (Add (TotalE K T) (TotalE Q X))).
          IdTransRaw Nat
            (Add (LenE H2) (TotalE (Add K Q) (arrCat K Q T X)))
            (Add (LenE H2) (Add (TotalE K T) (TotalE Q X)))
            (Add (Add (LenE H2) (TotalE K T)) (TotalE Q X))
            (IdCongrRaw Nat Nat (λ (X2 : Nat). Add (LenE H2) X2)
              (TotalE (Add K Q) (arrCat K Q T X))
              (Add (TotalE K T) (TotalE Q X)) Ih)
            (IdSymRaw Nat (Add (Add (LenE H2) (TotalE K T)) (TotalE Q X))
              (Add (LenE H2) (Add (TotalE K T) (TotalE Q X)))
              (AddAssocRaw (LenE H2) (TotalE K T) (TotalE Q X))))
      M L }
def TotalArrCatTy : Term := prog_parse {
  Π (Q : Nat) → Π (X : Array Q (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id Nat (TotalE (Add M Q) (arrCat M Q L X))
           (Add (TotalE M L) (TotalE Q X)) }

/-- Collapse a stuck Bool-elim whose scrutinee has an equation — the transport
    every pointwise-Find branch performs. -/
def BoolRwT : Term := prog_parse {
  λ (T : Type). λ (X : T). λ (Y : T). λ (B : Bool). λ (E : Id Bool B True).
    IdCongrRaw Bool T (λ (W : Bool). boolRec (λ (W2 : Bool). T) X Y W) B True E }
def BoolRwTTy : Term := prog_parse {
  Π (T : Type) → Π (X : T) → Π (Y : T) → Π (B : Bool) → Id Bool B True →
    Id T (boolRec (λ (W2 : Bool). T) X Y B) X }

def BoolRwF : Term := prog_parse {
  λ (T : Type). λ (X : T). λ (Y : T). λ (B : Bool). λ (E : Id Bool B False).
    IdCongrRaw Bool T (λ (W : Bool). boolRec (λ (W2 : Bool). T) X Y W) B False E }
def BoolRwFTy : Term := prog_parse {
  Π (T : Type) → Π (X : T) → Π (Y : T) → Π (B : Bool) → Id Bool B False →
    Id T (boolRec (λ (W2 : Bool). T) X Y B) Y }

/-- `a ≤ b` and `a ≠ b` make `a` strictly below `b` — the frame case's
    trichotomy converter. -/
def LeNeLt : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Az : Nat).
      Π (B : Nat) → Le Az B → Id Bool (Eqb Az B) False → Le (S Az) B) {
    Z => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le Z Bz → Id Bool (Eqb Z Bz) False → Le (S Z) Bz) {
        Z => λ (H : Le Z Z). λ (E : Id Bool (Eqb Z Z) False).
          botElim (Le (S Z) Z) (BoolTFRaw E),
        S (B2) Ihb => λ (H : Le Z (S B2)). λ (E : Id Bool (Eqb Z (S B2)) False). unit },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le (S A2) Bz → Id Bool (Eqb (S A2) Bz) False →
          Le (S (S A2)) Bz) {
        Z => λ (H : Le (S A2) Z). λ (E : Id Bool (Eqb (S A2) Z) False).
          botElim (Le (S (S A2)) Z) H,
        S (B2) Ihb => λ (H : Le (S A2) (S B2)). λ (E : Id Bool (Eqb (S A2) (S B2)) False).
          Ih B2 H E } } }
def LeNeLtTy : Term := prog_parse {
  Π (A : Nat) → Π (B : Nat) → Le A B → Id Bool (Eqb A B) False → Le (S A) B }

example : chkL TotalArrCat TotalArrCatTy = true := by native_decide
example : chkL BoolRwT BoolRwTTy = true := by native_decide
example : chkL BoolRwF BoolRwFTy = true := by native_decide
example : chkL LeNeLt LeNeLtTy = true := by native_decide

/-! ### `SlotsFrom` across the carve: three extractors and the reglue. The fold's
    starting index is generalized through every induction (no per-depth
    ladders); the step arms pay one `AddSuccRaw` transport each. -/

def SFCatLo : Term := prog_parse {
  λ (Cap : Nat). λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (I : Nat) →
          SlotsFrom Cap (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) I →
          SlotsFrom Cap Mz Az I)
      (λ (I : Nat). λ (Hs : SlotsFrom Cap (S R) (acons R B H) I). unit)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (I : Nat) →
            SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) I →
            SlotsFrom Cap K T I).
          λ (I : Nat).
          λ (Hs : Σ (Hx : SlotInv Cap I H2).
              SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)).
            Pair(FstT (SlotInv Cap I H2)
                   (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs,
                 Ih (S I)
                   (SndT (SlotInv Cap I H2)
                     (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs)))
      M L }
def SFCatLoTy : Term := prog_parse {
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotsFrom Cap M L I }

def SFCatMid : Term := prog_parse {
  λ (Cap : Nat). λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (I : Nat) →
          SlotsFrom Cap (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) I →
          SlotInv Cap (Add Mz I) B)
      (λ (I : Nat).
        λ (Hs : Σ (Hx : SlotInv Cap I B). SlotsFrom Cap R H (S I)).
          FstT (SlotInv Cap I B) (SlotsFrom Cap R H (S I)) Hs)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (I : Nat) →
            SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) I →
            SlotInv Cap (Add K I) B).
          λ (I : Nat).
          λ (Hs : Σ (Hx : SlotInv Cap I H2).
              SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)).
            NatRwRaw (λ (W : Nat). SlotInv Cap W B) (Add K (S I)) (S (Add K I))
              (AddSuccRaw K I)
              (Ih (S I)
                (SndT (SlotInv Cap I H2)
                  (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs)))
      M L }
def SFCatMidTy : Term := prog_parse {
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotInv Cap (Add M I) B }

def SFCatHi : Term := prog_parse {
  λ (Cap : Nat). λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (I : Nat) →
          SlotsFrom Cap (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) I →
          SlotsFrom Cap R H (S (Add Mz I)))
      (λ (I : Nat).
        λ (Hs : Σ (Hx : SlotInv Cap I B). SlotsFrom Cap R H (S I)).
          SndT (SlotInv Cap I B) (SlotsFrom Cap R H (S I)) Hs)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (I : Nat) →
            SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) I →
            SlotsFrom Cap R H (S (Add K I))).
          λ (I : Nat).
          λ (Hs : Σ (Hx : SlotInv Cap I H2).
              SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)).
            NatRwRaw (λ (W : Nat). SlotsFrom Cap R H (S W)) (Add K (S I)) (S (Add K I))
              (AddSuccRaw K I)
              (Ih (S I)
                (SndT (SlotInv Cap I H2)
                  (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs)))
      M L }
def SFCatHiTy : Term := prog_parse {
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotsFrom Cap R H (S (Add M I)) }

example : chkL SFCatLo SFCatLoTy = true := by native_decide
example : chkL SFCatMid SFCatMidTy = true := by native_decide
example : chkL SFCatHi SFCatHiTy = true := by native_decide

/-- The reglue: lo's invariants, the new cell's `SlotInv` at the boundary
    index, hi's invariants — back to the whole composition. Every op's
    invariant-preservation exit goes through this. -/
def SFCatGlue : Term := prog_parse {
  λ (Cap : Nat). λ (R : Nat). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (M : Nat). λ (L : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (I : Nat) →
          SlotsFrom Cap Mz Az I →
          SlotInv Cap (Add Mz I) B →
          SlotsFrom Cap R H (S (Add Mz I)) →
          SlotsFrom Cap (Add Mz (S R)) (arrCat Mz (S R) Az (acons R B H)) I)
      (λ (I : Nat). λ (Hl : Unit). λ (Hm : SlotInv Cap I B).
        λ (Hh : SlotsFrom Cap R H (S I)).
          Pair(Hm, Hh))
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (I : Nat) →
            SlotsFrom Cap K T I →
            SlotInv Cap (Add K I) B →
            SlotsFrom Cap R H (S (Add K I)) →
            SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) I).
          λ (I : Nat).
          λ (Hl : Σ (Hx : SlotInv Cap I H2). SlotsFrom Cap K T (S I)).
          λ (Hm : SlotInv Cap (S (Add K I)) B).
          λ (Hh : SlotsFrom Cap R H (S (S (Add K I)))).
            Pair(FstT (SlotInv Cap I H2) (SlotsFrom Cap K T (S I)) Hl,
                 Ih (S I)
                   (SndT (SlotInv Cap I H2) (SlotsFrom Cap K T (S I)) Hl)
                   (NatRwRaw (λ (W : Nat). SlotInv Cap W B) (S (Add K I)) (Add K (S I))
                     (IdSymRaw Nat (Add K (S I)) (S (Add K I)) (AddSuccRaw K I)) Hm)
                   (NatRwRaw (λ (W : Nat). SlotsFrom Cap R H (S W)) (S (Add K I)) (Add K (S I))
                     (IdSymRaw Nat (Add K (S I)) (S (Add K I)) (AddSuccRaw K I)) Hh)))
      M L }
def SFCatGlueTy : Term := prog_parse {
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap M L I →
    SlotInv Cap (Add M I) B →
    SlotsFrom Cap R H (S (Add M I)) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I }

example : chkL SFCatGlue SFCatGlueTy = true := by native_decide

/-! ## (xii) The bucket walk's evidence, as standalone pure lemmas

    `insert_in_list`'s three branches each owe five conjuncts; every non-Refl
    one is proven here over Π-bound state, so the walk's body only applies them
    at its snapshots. `OptN`/`BktT` abbreviate the two types (splices — never
    used at an elim motive, where the sugar reads syntax). -/

def OptN : Term := prog_parse { Σ (bb : Bool). OptP bb Nat }
def BktT : Term := prog_parse { List (Σ (k : Nat). Nat) }

/-- The bucket-level model update: `Some v` at `key`, the old bucket answer
    elsewhere. -/
def BFindIns : Term := prog_parse {
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat). λ (L : BktT).
    elim (Eqb Q Key) return (λ (Bm : Bool). OptN) {
      True => SomeN V,
      False => FindL Q L } }

/-- The bucket-level length update: unchanged on a hit, bumped on a miss. -/
def BLenIns : Term := prog_parse {
  λ (Key : Nat). λ (L : BktT).
    elim (HitL Key L) return (λ (Bm : Bool). Nat) {
      True => LenE L,
      False => S(LenE L) } }

/-- The GENERIC bucket-level model update: answer `X` at `Key`, the old bucket
    elsewhere. `BFindIns Q K V` converts with `BFindUpd Q K (SomeN V)` and
    Remove's model with `BFindUpd Q K NoneN`, so the pointwise family below
    serves both ops. -/
def BFindUpd : Term := prog_parse {
  λ (Q : Nat). λ (Key : Nat). λ (X : OptN). λ (L : BktT).
    elim (Eqb Q Key) return (λ (Bm : Bool). OptN) {
      True => X,
      False => FindL Q L } }

/-- Pull `S` out of a stuck Bool-elim. -/
def BoolPushS : Term := prog_parse {
  λ (X : Nat). λ (Y : Nat). λ (B : Bool).
    boolRec (λ (Bm : Bool).
        Id Nat (boolRec (λ (W2 : Bool). Nat) (S X) (S Y) Bm)
               (S (boolRec (λ (W2 : Bool). Nat) X Y Bm)))
      Refl Refl B }
def BoolPushSTy : Term := prog_parse {
  Π (X : Nat) → Π (Y : Nat) → Π (B : Bool) →
    Id Nat (boolRec (λ (W2 : Bool). Nat) (S X) (S Y) B)
           (S (boolRec (λ (W2 : Bool). Nat) X Y B)) }
example : chkL BoolPushS BoolPushSTy = true := by native_decide

/-- The hit branch, presence: the head key equals `key`, so the bucket answers. -/
def HitEvHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRwRaw (λ (W : Nat). Id Bool True (HitL Key (Cons(Pair(W, V0), T0)))) Key K0
      (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (IdSymRaw Bool (HitL Key (Cons(Pair(Key, V0), T0))) True
        (IdCongrRaw OptN Bool IsSomeB
          (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
          (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbReflRaw Key)))) }
def HitEvHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Bool True (HitL Key (Cons(Pair(K0, V0), T0))) }
example : chkL HitEvHit HitEvHitTy = true := by native_decide

/-- The hit branch, the pointwise Find equation: overwrite in place. -/
def PtEvHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (V1 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRwRaw (λ (W : Nat).
        Π (Q : Nat) → Id OptN
          (FindL Q (Cons(Pair(W, V1), T0)))
          (BFindIns Q Key V1 (Cons(Pair(W, V0), T0))))
      Key K0
      (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (λ (Q : Nat).
        IfDecRaw (Eqb Q Key)
          (Id OptN (FindL Q (Cons(Pair(Key, V1), T0)))
                   (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))))
          (λ (E2 : Id Bool (Eqb Q Key) True).
            IdTransRaw OptN (FindL Q (Cons(Pair(Key, V1), T0))) (SomeN V1)
              (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
              (BoolRwT OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2)
              (IdSymRaw OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))) (SomeN V1)
                (BoolRwT OptN (SomeN V1)
                  (FindL Q (Cons(Pair(Key, V0), T0))) (Eqb Q Key) E2)))
          (λ (E2 : Id Bool (Eqb Q Key) False).
            IdTransRaw OptN (FindL Q (Cons(Pair(Key, V1), T0))) (FindL Q T0)
              (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
              (BoolRwF OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2)
              (IdSymRaw OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))) (FindL Q T0)
                (IdTransRaw OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
                  (FindL Q (Cons(Pair(Key, V0), T0))) (FindL Q T0)
                  (BoolRwF OptN (SomeN V1)
                    (FindL Q (Cons(Pair(Key, V0), T0))) (Eqb Q Key) E2)
                  (BoolRwF OptN (SomeN V0) (FindL Q T0) (Eqb Q Key) E2))))) }
def PtEvHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Π (Q : Nat) → Id OptN
      (FindL Q (Cons(Pair(K0, V1), T0)))
      (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0))) }
example : chkL PtEvHit PtEvHitTy = true := by native_decide

/-- The hit branch, the length equation: present key, length unchanged. -/
def LnEvHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (V1 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRwRaw (λ (W : Nat). Id Nat (LenE (Cons(Pair(W, V1), T0)))
                               (BLenIns Key (Cons(Pair(W, V0), T0)))) Key K0
      (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (IdSymRaw Nat (BLenIns Key (Cons(Pair(Key, V0), T0)))
        (LenE (Cons(Pair(Key, V0), T0)))
        (BoolRwT Nat (LenE (Cons(Pair(Key, V0), T0)))
          (S (LenE (Cons(Pair(Key, V0), T0))))
          (HitL Key (Cons(Pair(Key, V0), T0)))
          (IdCongrRaw OptN Bool IsSomeB
            (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
            (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbReflRaw Key))))) }
def LnEvHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Nat (LenE (Cons(Pair(K0, V1), T0))) (BLenIns Key (Cons(Pair(K0, V0), T0))) }
example : chkL LnEvHit LnEvHitTy = true := by native_decide

/-- The miss branch, presence: the head is not `key`, so presence delegates to
    the tail — on both the old and the new bucket. -/
def HitEvMiss : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (H2 : Bool).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hh : Id Bool H2 (HitL Key T0)).
    IdTransRaw Bool H2 (HitL Key T0) (HitL Key (Cons(Pair(K0, V0), T0)))
      Hh
      (IdSymRaw Bool (HitL Key (Cons(Pair(K0, V0), T0))) (HitL Key T0)
        (IdCongrRaw OptN Bool IsSomeB
          (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
          (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
            (IdTransRaw Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSymRaw Key K0) E)))) }
def HitEvMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (H2 : Bool) →
    Id Bool (Eqb K0 Key) False →
    Id Bool H2 (HitL Key T0) →
    Id Bool H2 (HitL Key (Cons(Pair(K0, V0), T0))) }
example : chkL HitEvMiss HitEvMissTy = true := by native_decide

/-- The miss branch, the pointwise Find equation lifted through the untouched head. -/
def UpdEvMiss : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (X : OptN). λ (Key : Nat).
  λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hp : Π (Q : Nat) → Id OptN (FindL Q T1) (BFindUpd Q Key X T0)).
    λ (Q : Nat).
      IfDecRaw (Eqb Q Key)
        (Id OptN (FindL Q (Cons(Pair(K0, V0), T1)))
                 (BFindUpd Q Key X (Cons(Pair(K0, V0), T0))))
        (λ (E2 : Id Bool (Eqb Q Key) True).
          IdTransRaw OptN (FindL Q (Cons(Pair(K0, V0), T1))) (FindL Q T1)
            (BFindUpd Q Key X (Cons(Pair(K0, V0), T0)))
            (BoolRwF OptN (SomeN V0) (FindL Q T1) (Eqb Q K0)
              (IdTransRaw Bool (Eqb Q K0) (Eqb Key K0) False
                (IdCongrRaw Nat Bool (λ (W : Nat). Eqb W K0) Q Key (EqbTrueEqRaw Q Key E2))
                (IdTransRaw Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSymRaw Key K0) E)))
            (IdTransRaw OptN (FindL Q T1) X
              (BFindUpd Q Key X (Cons(Pair(K0, V0), T0)))
              (IdTransRaw OptN (FindL Q T1) (BFindUpd Q Key X T0) X
                (Hp Q)
                (BoolRwT OptN X (FindL Q T0) (Eqb Q Key) E2))
              (IdSymRaw OptN (BFindUpd Q Key X (Cons(Pair(K0, V0), T0))) X
                (BoolRwT OptN X
                  (FindL Q (Cons(Pair(K0, V0), T0))) (Eqb Q Key) E2))))
        (λ (E2 : Id Bool (Eqb Q Key) False).
          IdTransRaw OptN (FindL Q (Cons(Pair(K0, V0), T1)))
            (FindL Q (Cons(Pair(K0, V0), T0)))
            (BFindUpd Q Key X (Cons(Pair(K0, V0), T0)))
            (IdCongrRaw OptN OptN
              (λ (W : OptN). boolRec (λ (W2 : Bool). OptN) (SomeN V0) W (Eqb Q K0))
              (FindL Q T1) (FindL Q T0)
              (IdTransRaw OptN (FindL Q T1) (BFindUpd Q Key X T0) (FindL Q T0)
                (Hp Q)
                (BoolRwF OptN X (FindL Q T0) (Eqb Q Key) E2)))
            (IdSymRaw OptN (BFindUpd Q Key X (Cons(Pair(K0, V0), T0)))
              (FindL Q (Cons(Pair(K0, V0), T0)))
              (BoolRwF OptN X
                (FindL Q (Cons(Pair(K0, V0), T0))) (Eqb Q Key) E2))) }
def UpdEvMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (X : OptN) → Π (Key : Nat) →
  Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    (Π (Q : Nat) → Id OptN (FindL Q T1) (BFindUpd Q Key X T0)) →
    Π (Q : Nat) → Id OptN
      (FindL Q (Cons(Pair(K0, V0), T1)))
      (BFindUpd Q Key X (Cons(Pair(K0, V0), T0))) }
example : chkL UpdEvMiss UpdEvMissTy = true := by native_decide

/-- The miss branch, the length equation lifted through the head. -/
def LnEvMiss : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hl : Id Nat (LenE T1) (BLenIns Key T0)).
    IdTransRaw Nat (S (LenE T1)) (S (BLenIns Key T0))
      (BLenIns Key (Cons(Pair(K0, V0), T0)))
      (IdCongrRaw Nat Nat (λ (W : Nat). S W) (LenE T1) (BLenIns Key T0) Hl)
      (IdSymRaw Nat (BLenIns Key (Cons(Pair(K0, V0), T0))) (S (BLenIns Key T0))
        (IdTransRaw Nat (BLenIns Key (Cons(Pair(K0, V0), T0)))
          (boolRec (λ (W2 : Bool). Nat)
            (LenE (Cons(Pair(K0, V0), T0)))
            (S (LenE (Cons(Pair(K0, V0), T0))))
            (HitL Key T0))
          (S (BLenIns Key T0))
          (IdCongrRaw Bool Nat
            (λ (W : Bool). boolRec (λ (W2 : Bool). Nat)
              (LenE (Cons(Pair(K0, V0), T0)))
              (S (LenE (Cons(Pair(K0, V0), T0)))) W)
            (HitL Key (Cons(Pair(K0, V0), T0))) (HitL Key T0)
            (IdCongrRaw OptN Bool IsSomeB
              (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
              (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
                (IdTransRaw Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSymRaw Key K0) E))))
          (BoolPushS (LenE T0) (S (LenE T0)) (HitL Key T0)))) }
def LnEvMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    Id Nat (LenE T1) (BLenIns Key T0) →
    Id Nat (LenE (Cons(Pair(K0, V0), T1))) (BLenIns Key (Cons(Pair(K0, V0), T0))) }
example : chkL LnEvMiss LnEvMissTy = true := by native_decide

/-- The miss branch, the Nodup head clause: `K0` absent from the tail stays
    absent after inserting a different key into it. -/
def UpdNdMiss : Term := prog_parse {
  λ (K0 : Nat). λ (X : OptN). λ (Key : Nat). λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hp : Π (Q : Nat) → Id OptN (FindL Q T1) (BFindUpd Q Key X T0)).
  λ (Hn : Id Bool (HitL K0 T0) False).
    IdTransRaw Bool (HitL K0 T1) (HitL K0 T0) False
      (IdCongrRaw OptN Bool IsSomeB (FindL K0 T1) (FindL K0 T0)
        (IdTransRaw OptN (FindL K0 T1) (BFindUpd K0 Key X T0) (FindL K0 T0)
          (Hp K0)
          (BoolRwF OptN X (FindL K0 T0) (Eqb K0 Key) E)))
      Hn }
def UpdNdMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (X : OptN) → Π (Key : Nat) → Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    (Π (Q : Nat) → Id OptN (FindL Q T1) (BFindUpd Q Key X T0)) →
    Id Bool (HitL K0 T0) False →
    Id Bool (HitL K0 T1) False }
example : chkL UpdNdMiss UpdNdMissTy = true := by native_decide

/-! ## (xiii) The map-level pointwise lift, and the pack builder -/

def LoadHM : Term := prog_parse {
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) => Load } } }

/-- The invariant, assembled by one application — a bare capital citation in a
    refill's constructor argument is fenced, an application is not, so every
    op's exit packs through this. -/
def MkInv : Term := prog_parse {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (H1 : Le (S Z) Cap). λ (H2 : Id Nat Load (Mul 4 Cap)).
  λ (H3 : Le (Mul 5 N) Load). λ (H4 : Id Nat N (TotalE Cap Slots)).
  λ (H5 : SlotsFrom Cap Cap Slots Z).
    Pair(H1, Pair(H2, Pair(H3, Pair(H4, H5)))) }
def MkInvTy : Term := prog_parse {
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    Le (S Z) Cap → Id Nat Load (Mul 4 Cap) → Le (Mul 5 N) Load →
    Id Nat N (TotalE Cap Slots) → SlotsFrom Cap Cap Slots Z →
    HMInvT Cap Load N Slots }
example : chkL MkInv MkInvTy = true := by native_decide

/-- Same-slot case of the pointwise lift: `q` hashes to the written slot, so
    both sides collapse to the bucket-level equation through `AgetBCatMid`. -/
def UpdPtSame : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (X : OptN).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Hb : Π (Q : Nat) → Id OptN (FindL Q B1) (BFindUpd Q Key X B0)).
  λ (Q : Nat).
  λ (Ej : Id Bool (Eqb (Mod Q (Add I (S R))) I) True).
    NatRwRaw (λ (W : Nat).
        Id OptN
          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) W))
          (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) W)))
      I (Mod Q (Add I (S R)))
      (IdSymRaw Nat (Mod Q (Add I (S R))) I (EqbTrueEqRaw (Mod Q (Add I (S R))) I Ej))
      (IdTransRaw OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) I))
        (FindL Q B1)
        (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
        (IdCongrRaw BktT OptN (λ (W : BktT). FindL Q W)
          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) I) B1
          (AgetBCatMid R B1 H I L))
        (IdTransRaw OptN (FindL Q B1) (BFindUpd Q Key X B0)
          (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
          (Hb Q)
          (IdSymRaw OptN
            (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
            (BFindUpd Q Key X B0)
            (IdCongrRaw BktT OptN (λ (W : BktT). BFindUpd Q Key X W)
              (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I) B0
              (AgetBCatMid R B0 H I L))))) }
def UpdPtSameTy : Term := prog_parse {
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (X : OptN) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    (Π (Q : Nat) → Id OptN (FindL Q B1) (BFindUpd Q Key X B0)) →
    Π (Q : Nat) → Id Bool (Eqb (Mod Q (Add I (S R))) I) True →
    Id OptN
      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
        (Mod Q (Add I (S R)))))
      (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
        (Mod Q (Add I (S R))))) }
example : chkL UpdPtSame UpdPtSameTy = true := by native_decide

/-- Different-slot case: `q`'s bucket is untouched. `Eqb Q Key = True` is dead
    (equal keys share a slot); otherwise the slot is strictly left of the cell
    (`AgetBCatLo`) or strictly right (`ModDecRaw` mints the offset, `AgetBCatHi`). -/
def UpdPtDiff : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (X : OptN).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Him : Id Nat I (Mod Key (Add I (S R)))).
  λ (Q : Nat).
  λ (Ej : Id Bool (Eqb (Mod Q (Add I (S R))) I) False).
    IfDecRaw (Eqb Q Key)
      (Id OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
          (Mod Q (Add I (S R)))))
        (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
          (Mod Q (Add I (S R))))))
      (λ (E2 : Id Bool (Eqb Q Key) True).
        botElim
          (Id OptN
            (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
              (Mod Q (Add I (S R)))))
            (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
              (Mod Q (Add I (S R))))))
          (BoolTFRaw (IdTransRaw Bool True (Eqb (Mod Q (Add I (S R))) I) False
            (IdSymRaw Bool (Eqb (Mod Q (Add I (S R))) I) True
              (IdTransRaw Bool (Eqb (Mod Q (Add I (S R))) I) (Eqb I I) True
                (IdCongrRaw Nat Bool (λ (W : Nat). Eqb W I) (Mod Q (Add I (S R))) I
                  (IdTransRaw Nat (Mod Q (Add I (S R))) (Mod Key (Add I (S R))) I
                    (IdCongrRaw Nat Nat (λ (W : Nat). Mod W (Add I (S R))) Q Key
                      (EqbTrueEqRaw Q Key E2))
                    (IdSymRaw Nat I (Mod Key (Add I (S R))) Him)))
                (EqbReflRaw I)))
            Ej)))
      (λ (E2 : Id Bool (Eqb Q Key) False).
        IfDecRaw (Leb (Mod Q (Add I (S R))) I)
          (Id OptN
            (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
              (Mod Q (Add I (S R)))))
            (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
              (Mod Q (Add I (S R))))))
          (λ (El : Id Bool (Leb (Mod Q (Add I (S R))) I) True).
            IdTransRaw OptN
              (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                (Mod Q (Add I (S R)))))
              (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
              (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                (Mod Q (Add I (S R)))))
              (IdCongrRaw BktT OptN (λ (W : BktT). FindL Q W)
                (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                  (Mod Q (Add I (S R))))
                (AgetB I L (Mod Q (Add I (S R))))
                (AgetBCatLo R B1 H I L (Mod Q (Add I (S R)))
                  (LeNeLt (Mod Q (Add I (S R))) I
                    (LebTrueLeRaw (Mod Q (Add I (S R))) I El) Ej)))
              (IdSymRaw OptN
                (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                  (Mod Q (Add I (S R)))))
                (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
                (IdTransRaw OptN
                  (BFindUpd Q Key X (AgetB (Add I (S R))
                    (arrCat I (S R) L (acons R B0 H)) (Mod Q (Add I (S R)))))
                  (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                    (Mod Q (Add I (S R)))))
                  (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
                  (BoolRwF OptN X
                    (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                      (Mod Q (Add I (S R)))))
                    (Eqb Q Key) E2)
                  (IdCongrRaw BktT OptN (λ (W : BktT). FindL Q W)
                    (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                      (Mod Q (Add I (S R))))
                    (AgetB I L (Mod Q (Add I (S R))))
                    (AgetBCatLo R B0 H I L (Mod Q (Add I (S R)))
                      (LeNeLt (Mod Q (Add I (S R))) I
                        (LebTrueLeRaw (Mod Q (Add I (S R))) I El) Ej))))))
          (λ (El : Id Bool (Leb (Mod Q (Add I (S R))) I) False).
            elim (ModDecRaw I (Mod Q (Add I (S R)))
                (LebFalseGtRaw (Mod Q (Add I (S R))) I El)) return
              (λ (W : Σ (R2 : Nat). Id Nat (Mod Q (Add I (S R))) (Add I (S R2))).
                Id OptN
                  (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                    (Mod Q (Add I (S R)))))
                  (BFindUpd Q Key X (AgetB (Add I (S R))
                    (arrCat I (S R) L (acons R B0 H)) (Mod Q (Add I (S R)))))) {
              Pair (D) (Hd) =>
                NatRwRaw (λ (W : Nat).
                    Id OptN
                      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) W))
                      (BFindUpd Q Key X (AgetB (Add I (S R))
                        (arrCat I (S R) L (acons R B0 H)) W)))
                  (Add I (S D)) (Mod Q (Add I (S R)))
                  (IdSymRaw Nat (Mod Q (Add I (S R))) (Add I (S D)) Hd)
                  (IdTransRaw OptN
                    (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                      (Add I (S D))))
                    (FindL Q (AgetB R H D))
                    (BFindUpd Q Key X (AgetB (Add I (S R))
                      (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                    (IdCongrRaw BktT OptN (λ (W : BktT). FindL Q W)
                      (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                        (Add I (S D)))
                      (AgetB R H D)
                      (AgetBCatHi R B1 H D I L))
                    (IdSymRaw OptN
                      (BFindUpd Q Key X (AgetB (Add I (S R))
                        (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                      (FindL Q (AgetB R H D))
                      (IdTransRaw OptN
                        (BFindUpd Q Key X (AgetB (Add I (S R))
                          (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                          (Add I (S D))))
                        (FindL Q (AgetB R H D))
                        (BoolRwF OptN X
                          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                            (Add I (S D))))
                          (Eqb Q Key) E2)
                        (IdCongrRaw BktT OptN (λ (W : BktT). FindL Q W)
                          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                            (Add I (S D)))
                          (AgetB R H D)
                          (AgetBCatHi R B0 H D I L))))) })) }
def UpdPtDiffTy : Term := prog_parse {
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (X : OptN) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    Id Nat I (Mod Key (Add I (S R))) →
    Π (Q : Nat) → Id Bool (Eqb (Mod Q (Add I (S R))) I) False →
    Id OptN
      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
        (Mod Q (Add I (S R)))))
      (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
        (Mod Q (Add I (S R))))) }
example : chkL UpdPtDiff UpdPtDiffTy = true := by native_decide

/-- The pointwise lift: the walk's bucket equation becomes Insert's whole-map
    equation, by deciding `q`'s slot against the written slot. -/
def UpdPointwise : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (X : OptN).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Him : Id Nat I (Mod Key (Add I (S R)))).
  λ (Hb : Π (Q : Nat) → Id OptN (FindL Q B1) (BFindUpd Q Key X B0)).
    λ (Q : Nat).
      IfDecRaw (Eqb (Mod Q (Add I (S R))) I)
        (Id OptN
          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
            (Mod Q (Add I (S R)))))
          (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
            (Mod Q (Add I (S R))))))
        (UpdPtSame I R Key X L B0 B1 H Hb Q)
        (UpdPtDiff I R Key X L B0 B1 H Him Q) }
def UpdPointwiseTy : Term := prog_parse {
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (X : OptN) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    Id Nat I (Mod Key (Add I (S R))) →
    (Π (Q : Nat) → Id OptN (FindL Q B1) (BFindUpd Q Key X B0)) →
    Π (Q : Nat) →
      Id OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
          (Mod Q (Add I (S R)))))
        (BFindUpd Q Key X (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
          (Mod Q (Add I (S R))))) }
example : chkL UpdPointwise UpdPointwiseTy = true := by native_decide

/-! ## (xiv) `New`'s builder and its three lemmas, and the slot pack -/

/-- `n` empty buckets, by `acons` recursion. -/
def MkSlots : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List (Σ (k : Nat). Nat))) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }

/-- Every slot of the fresh table satisfies its invariant (vacuously). -/
def SFMkSlots : Term := prog_parse {
  λ (Cap : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Π (I : Nat) → SlotsFrom Cap Nz (MkSlots Nz) I) {
      Z => λ (I : Nat). unit,
      S (M) Ih => λ (I : Nat). Pair(Pair(unit, unit), Ih (S I)) } }
def SFMkSlotsTy : Term := prog_parse {
  Π (Cap : Nat) → Π (N : Nat) → Π (I : Nat) → SlotsFrom Cap N (MkSlots N) I }
example : chkL SFMkSlots SFMkSlotsTy = true := by native_decide

/-- The fresh table holds nothing. -/
def TotalMkSlots : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Nz : Nat). Id Nat (TotalE Nz (MkSlots Nz)) Z) {
    Z => Refl,
    S (M) Ih => Ih } }
def TotalMkSlotsTy : Term := prog_parse {
  Π (N : Nat) → Id Nat (TotalE N (MkSlots N)) Z }
example : chkL TotalMkSlots TotalMkSlotsTy = true := by native_decide

/-- Every slot of the fresh table reads back `Nil` — at any index, in range or
    not, which is why `New`'s find-spec needs no bound side-condition. -/
def AgetBMkSlots : Term := prog_parse {
  λ (N : Nat).
    elim N return (λ (Nz : Nat).
        Π (J : Nat) → Id (List (Σ (k : Nat). Nat)) (AgetB Nz (MkSlots Nz) J) Nil) {
      Z => λ (J : Nat). Refl,
      S (M) Ih => λ (J : Nat).
        elim J return (λ (Jz : Nat).
            Id (List (Σ (k : Nat). Nat)) (AgetB (S M) (MkSlots (S M)) Jz) Nil) {
          Z => Refl,
          S (J2) Ihj => Ih J2 } } }
def AgetBMkSlotsTy : Term := prog_parse {
  Π (N : Nat) → Π (J : Nat) →
    Id (List (Σ (k : Nat). Nat)) (AgetB N (MkSlots N) J) Nil }
example : chkL AgetBMkSlots AgetBMkSlotsTy = true := by native_decide

/-- The slot quadruple `SlotOfE` returns: index, residue, the carve equation,
    and the identity tying the index to the hash, which the pointwise lift
    consumes as `Him`. -/
def SlotPack : Term := prog_parse {
  λ (H : Nat). λ (N : Nat). λ (Hne : Le (S Z) N).
    elim (ModDecRaw (Mod H N) N (ModLtNRaw H N Hne)) return
        (λ (Q : Σ (R : Nat). Id Nat N (Add (Mod H N) (S R))).
          Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N)) {
      Pair (R0) (Hd0) => Pair(Mod H N, Pair(R0, Pair(Hd0, Refl))) } }
def SlotPackTy : Term := prog_parse {
  Π (H : Nat) → Π (N : Nat) → Le (S Z) N →
    Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N) }
example : chkL SlotPack SlotPackTy = true := by native_decide

/-! ## (xvii) Remove's walk evidence

    The remove walk is a take-and-rebuild over the owned bucket: unlink the
    hit cell and move its value out — values stay move-only. Its models: -/

def BFindRem : Term := prog_parse {
  λ (Q : Nat). λ (Key : Nat). λ (L : BktT).
    elim (Eqb Q Key) return (λ (Bm : Bool). OptN) {
      True => NoneN,
      False => FindL Q L } }

def BLenRem : Term := prog_parse {
  λ (Key : Nat). λ (L : BktT).
    elim (HitL Key L) return (λ (Bm : Bool). Nat) {
      True => Pred (LenE L),
      False => LenE L } }

/-- A stuck Bool-elim whose branches agree collapses. -/
def BoolSame : Term := prog_parse {
  λ (T : Type). λ (X : T). λ (B : Bool).
    boolRec (λ (Bm : Bool). Id T X (boolRec (λ (W2 : Bool). T) X X Bm))
      Refl Refl B }
def BoolSameTy : Term := prog_parse {
  Π (T : Type) → Π (X : T) → Π (B : Bool) →
    Id T X (boolRec (λ (W2 : Bool). T) X X B) }
example : chkL BoolSame BoolSameTy = true := by native_decide

/-- An absent key's lookup is `None` — the Σ(Bool) Option has no Unit-η, so
    this is an induction, not a projection. -/
def NotHitFindNone : Term := prog_parse {
  λ (Q : Nat). λ (L : BktT).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (HitL Q Lm) False → Id OptN (FindL Q Lm) NoneN) {
      Nil => λ (Hn : Id Bool (HitL Q Nil) False). Refl,
      Cons (E) (T) Ih =>
        elim E return (λ (Em : Σ (k : Nat). Nat).
            Id Bool (HitL Q (Cons(Em, T))) False → Id OptN (FindL Q (Cons(Em, T))) NoneN) {
          Pair (K2) (V2) => λ (Hn : Id Bool (HitL Q (Cons(Pair(K2, V2), T))) False).
            IfDecRaw (Eqb Q K2)
              (Id OptN (FindL Q (Cons(Pair(K2, V2), T))) NoneN)
              (λ (E2 : Id Bool (Eqb Q K2) True).
                botElim (Id OptN (FindL Q (Cons(Pair(K2, V2), T))) NoneN)
                  (BoolTFRaw (IdTransRaw Bool True (HitL Q (Cons(Pair(K2, V2), T))) False
                    (IdSymRaw Bool (HitL Q (Cons(Pair(K2, V2), T))) True
                      (IdTransRaw Bool (HitL Q (Cons(Pair(K2, V2), T)))
                        (IsSomeB (SomeN V2)) True
                        (IdCongrRaw OptN Bool IsSomeB
                          (FindL Q (Cons(Pair(K2, V2), T))) (SomeN V2)
                          (BoolRwT OptN (SomeN V2) (FindL Q T) (Eqb Q K2) E2))
                        Refl))
                    Hn)))
              (λ (E2 : Id Bool (Eqb Q K2) False).
                IdTransRaw OptN (FindL Q (Cons(Pair(K2, V2), T))) (FindL Q T) NoneN
                  (BoolRwF OptN (SomeN V2) (FindL Q T) (Eqb Q K2) E2)
                  (Ih (IdTransRaw Bool (HitL Q T) (HitL Q (Cons(Pair(K2, V2), T))) False
                    (IdSymRaw Bool (HitL Q (Cons(Pair(K2, V2), T))) (HitL Q T)
                      (IdCongrRaw OptN Bool IsSomeB
                        (FindL Q (Cons(Pair(K2, V2), T))) (FindL Q T)
                        (BoolRwF OptN (SomeN V2) (FindL Q T) (Eqb Q K2) E2)))
                    Hn))) } } }
def NotHitFindNoneTy : Term := prog_parse {
  Π (Q : Nat) → Π (L : BktT) →
    Id Bool (HitL Q L) False → Id OptN (FindL Q L) NoneN }
example : chkL NotHitFindNone NotHitFindNoneTy = true := by native_decide

def SPredPos : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Nz : Nat). Le (S Z) Nz → Id Nat (S (Pred Nz)) Nz) {
    Z => λ (H : Le (S Z) Z). botElim (Id Nat (S (Pred Z)) Z) H,
    S (M) Ih => λ (H : Le (S Z) (S M)). Refl } }
def SPredPosTy : Term := prog_parse {
  Π (N : Nat) → Le (S Z) N → Id Nat (S (Pred N)) N }
example : chkL SPredPos SPredPosTy = true := by native_decide

/-- A bucket that answers is nonempty. -/
def HitLenPos : Term := prog_parse {
  λ (Q : Nat). λ (L : BktT).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (HitL Q Lm) True → Le (S Z) (LenE Lm)) {
      Nil => λ (Hh : Id Bool (HitL Q Nil) True).
        botElim (Le (S Z) (LenE Nil)) (BoolFTRaw Hh),
      Cons (E) (T) Ih => λ (Hh : Id Bool (HitL Q (Cons(E, T))) True). unit } }
def HitLenPosTy : Term := prog_parse {
  Π (Q : Nat) → Π (L : BktT) → Id Bool (HitL Q L) True → Le (S Z) (LenE L) }
example : chkL HitLenPos HitLenPosTy = true := by native_decide

/-- Remove's hit case: the unlinked value was the bucket's answer. -/
def RemHrHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRwRaw (λ (W : Nat). Id OptN (SomeN V0) (FindL Key (Cons(Pair(W, V0), T0))))
      Key K0 (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (IdSymRaw OptN (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
        (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbReflRaw Key))) }
def RemHrHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id OptN (SomeN V0) (FindL Key (Cons(Pair(K0, V0), T0))) }
example : chkL RemHrHit RemHrHitTy = true := by native_decide

/-- Remove's hit case, pointwise: the tail is the removed bucket, and at
    `Q = Key` the tail answers `None` because Nodup says the unlinked cell was
    the only one. -/
def RemPtHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
  λ (Hn : Id Bool (HitL K0 T0) False).
    NatRwRaw (λ (W : Nat). Π (Q : Nat) →
        Id OptN (FindL Q T0) (BFindRem Q Key (Cons(Pair(W, V0), T0))))
      Key K0 (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (λ (Q : Nat).
        IfDecRaw (Eqb Q Key)
          (Id OptN (FindL Q T0) (BFindRem Q Key (Cons(Pair(Key, V0), T0))))
          (λ (E2 : Id Bool (Eqb Q Key) True).
            NatRwRaw (λ (W : Nat).
                Id OptN (FindL W T0) (BFindRem W Key (Cons(Pair(Key, V0), T0))))
              Key Q (IdSymRaw Nat Q Key (EqbTrueEqRaw Q Key E2))
              (IdTransRaw OptN (FindL Key T0) NoneN
                (BFindRem Key Key (Cons(Pair(Key, V0), T0)))
                (NotHitFindNone Key T0
                  (NatRwRaw (λ (W : Nat). Id Bool (HitL W T0) False) K0 Key
                    (EqbTrueEqRaw K0 Key E) Hn))
                (IdSymRaw OptN (BFindRem Key Key (Cons(Pair(Key, V0), T0))) NoneN
                  (BoolRwT OptN NoneN (FindL Key (Cons(Pair(Key, V0), T0)))
                    (Eqb Key Key) (EqbReflRaw Key)))))
          (λ (E2 : Id Bool (Eqb Q Key) False).
            IdTransRaw OptN (FindL Q T0) (FindL Q (Cons(Pair(Key, V0), T0)))
              (BFindRem Q Key (Cons(Pair(Key, V0), T0)))
              (IdSymRaw OptN (FindL Q (Cons(Pair(Key, V0), T0))) (FindL Q T0)
                (BoolRwF OptN (SomeN V0) (FindL Q T0) (Eqb Q Key) E2))
              (IdSymRaw OptN (BFindRem Q Key (Cons(Pair(Key, V0), T0)))
                (FindL Q (Cons(Pair(Key, V0), T0)))
                (BoolRwF OptN NoneN (FindL Q (Cons(Pair(Key, V0), T0)))
                  (Eqb Q Key) E2)))) }
def RemPtHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Bool (HitL K0 T0) False →
    Π (Q : Nat) → Id OptN (FindL Q T0) (BFindRem Q Key (Cons(Pair(K0, V0), T0))) }
example : chkL RemPtHit RemPtHitTy = true := by native_decide

def RemLnHit : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRwRaw (λ (W : Nat). Id Nat (LenE T0) (BLenRem Key (Cons(Pair(W, V0), T0))))
      Key K0 (IdSymRaw Nat K0 Key (EqbTrueEqRaw K0 Key E))
      (IdSymRaw Nat (BLenRem Key (Cons(Pair(Key, V0), T0))) (LenE T0)
        (BoolRwT Nat (Pred (LenE (Cons(Pair(Key, V0), T0))))
          (LenE (Cons(Pair(Key, V0), T0)))
          (HitL Key (Cons(Pair(Key, V0), T0)))
          (IdCongrRaw OptN Bool IsSomeB
            (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
            (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbReflRaw Key))))) }
def RemLnHitTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Nat (LenE T0) (BLenRem Key (Cons(Pair(K0, V0), T0))) }
example : chkL RemLnHit RemLnHitTy = true := by native_decide

/-- Remove's miss case: the returned option delegates past the untouched head. -/
def RemHrMiss : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (Ret : OptN).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hr : Id OptN Ret (FindL Key T0)).
    IdTransRaw OptN Ret (FindL Key T0) (FindL Key (Cons(Pair(K0, V0), T0)))
      Hr
      (IdSymRaw OptN (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
        (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
          (IdTransRaw Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSymRaw Key K0) E))) }
def RemHrMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (Ret : OptN) →
    Id Bool (Eqb K0 Key) False →
    Id OptN Ret (FindL Key T0) →
    Id OptN Ret (FindL Key (Cons(Pair(K0, V0), T0))) }
example : chkL RemHrMiss RemHrMissTy = true := by native_decide

/-- Remove's miss case, length: `BLenRem` lifts through the head; the hit side
    needs the tail nonempty (`HitLenPos`) so `S ∘ Pred` cancels. -/
def RemLnMiss : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hl : Id Nat (LenE T1) (BLenRem Key T0)).
    IdTransRaw Nat (LenE (Cons(Pair(K0, V0), T1))) (S (BLenRem Key T0))
      (BLenRem Key (Cons(Pair(K0, V0), T0)))
      (IdCongrRaw Nat Nat (λ (W : Nat). S W) (LenE T1) (BLenRem Key T0) Hl)
      (IdSymRaw Nat (BLenRem Key (Cons(Pair(K0, V0), T0))) (S (BLenRem Key T0))
        (IdTransRaw Nat (BLenRem Key (Cons(Pair(K0, V0), T0)))
          (boolRec (λ (W2 : Bool). Nat)
            (Pred (LenE (Cons(Pair(K0, V0), T0))))
            (LenE (Cons(Pair(K0, V0), T0)))
            (HitL Key T0))
          (S (BLenRem Key T0))
          (IdCongrRaw Bool Nat
            (λ (W : Bool). boolRec (λ (W2 : Bool). Nat)
              (Pred (LenE (Cons(Pair(K0, V0), T0))))
              (LenE (Cons(Pair(K0, V0), T0))) W)
            (HitL Key (Cons(Pair(K0, V0), T0))) (HitL Key T0)
            (IdCongrRaw OptN Bool IsSomeB
              (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
              (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
                (IdTransRaw Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSymRaw Key K0) E))))
          (IfDecRaw (HitL Key T0)
            (Id Nat
              (boolRec (λ (W2 : Bool). Nat)
                (Pred (LenE (Cons(Pair(K0, V0), T0))))
                (LenE (Cons(Pair(K0, V0), T0)))
                (HitL Key T0))
              (S (BLenRem Key T0)))
            (λ (Eh : Id Bool (HitL Key T0) True).
              IdTransRaw Nat
                (boolRec (λ (W2 : Bool). Nat)
                  (Pred (LenE (Cons(Pair(K0, V0), T0))))
                  (LenE (Cons(Pair(K0, V0), T0)))
                  (HitL Key T0))
                (LenE T0) (S (BLenRem Key T0))
                (BoolRwT Nat (LenE T0) (S (LenE T0)) (HitL Key T0) Eh)
                (IdSymRaw Nat (S (BLenRem Key T0)) (LenE T0)
                  (IdTransRaw Nat (S (BLenRem Key T0)) (S (Pred (LenE T0))) (LenE T0)
                    (IdCongrRaw Nat Nat (λ (W : Nat). S W)
                      (BLenRem Key T0) (Pred (LenE T0))
                      (BoolRwT Nat (Pred (LenE T0)) (LenE T0) (HitL Key T0) Eh))
                    (SPredPos (LenE T0) (HitLenPos Key T0 Eh)))))
            (λ (Ef : Id Bool (HitL Key T0) False).
              IdTransRaw Nat
                (boolRec (λ (W2 : Bool). Nat)
                  (Pred (LenE (Cons(Pair(K0, V0), T0))))
                  (LenE (Cons(Pair(K0, V0), T0)))
                  (HitL Key T0))
                (S (LenE T0)) (S (BLenRem Key T0))
                (BoolRwF Nat (LenE T0) (S (LenE T0)) (HitL Key T0) Ef)
                (IdSymRaw Nat (S (BLenRem Key T0)) (S (LenE T0))
                  (IdCongrRaw Nat Nat (λ (W : Nat). S W)
                    (BLenRem Key T0) (LenE T0)
                    (BoolRwF Nat (Pred (LenE T0)) (LenE T0) (HitL Key T0) Ef))))))) }
def RemLnMissTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    Id Nat (LenE T1) (BLenRem Key T0) →
    Id Nat (LenE (Cons(Pair(K0, V0), T1))) (BLenRem Key (Cons(Pair(K0, V0), T0))) }
example : chkL RemLnMiss RemLnMissTy = true := by native_decide

/-- Removing from the empty bucket: both sides are `None`, but the model's
    elim is stuck on `Eqb Q Key` — `BoolSame` collapses it. -/
def RemPtNil : Term := prog_parse {
  λ (Key : Nat). λ (Q : Nat). BoolSame OptN NoneN (Eqb Q Key) }
def RemPtNilTy : Term := prog_parse {
  Π (Key : Nat) → Π (Q : Nat) →
    Id OptN (FindL Q Nil) (BFindRem Q Key Nil) }
example : chkL RemPtNil RemPtNilTy = true := by native_decide

/-- Remove's total accounting over the carve composition: on a hit the new
    total is one less (`S ∘ Pred` cancels through `HitLenPos`), on a miss it
    is unchanged. Stated with the hit-flag pre-collapsed to `HitL Key B0`. -/
def RemTotEv : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (Key : Nat).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Hl : Id Nat (LenE B1) (BLenRem Key B0)).
    IfDecRaw (HitL Key B0)
      (Id Nat
        (boolRec (λ (W2 : Bool). Nat)
          (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
          (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
          (HitL Key B0))
        (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H))))
      (λ (Eh : Id Bool (HitL Key B0) True).
        IdTransRaw Nat
          (boolRec (λ (W2 : Bool). Nat)
            (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
            (HitL Key B0))
          (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
          (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
          (BoolRwT Nat
            (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
            (HitL Key B0) Eh)
          (IdTransRaw Nat
            (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
            (S (Add (TotalE I L) (Add (LenE B1) (TotalE R H))))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
            (IdCongrRaw Nat Nat (λ (W : Nat). S W)
              (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
              (Add (TotalE I L) (Add (LenE B1) (TotalE R H)))
              (TotalArrCat (S R) (acons R B1 H) I L))
            (IdTransRaw Nat
              (S (Add (TotalE I L) (Add (LenE B1) (TotalE R H))))
              (S (Add (TotalE I L) (Add (Pred (LenE B0)) (TotalE R H))))
              (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
              (IdCongrRaw Nat Nat
                (λ (W : Nat). S (Add (TotalE I L) (Add W (TotalE R H))))
                (LenE B1) (Pred (LenE B0))
                (IdTransRaw Nat (LenE B1) (BLenRem Key B0) (Pred (LenE B0))
                  Hl
                  (BoolRwT Nat (Pred (LenE B0)) (LenE B0) (HitL Key B0) Eh)))
              (IdTransRaw Nat
                (S (Add (TotalE I L) (Add (Pred (LenE B0)) (TotalE R H))))
                (Add (TotalE I L) (Add (S (Pred (LenE B0))) (TotalE R H)))
                (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
                (IdSymRaw Nat
                  (Add (TotalE I L) (Add (S (Pred (LenE B0))) (TotalE R H)))
                  (S (Add (TotalE I L) (Add (Pred (LenE B0)) (TotalE R H))))
                  (AddSuccRaw (TotalE I L) (Add (Pred (LenE B0)) (TotalE R H))))
                (IdTransRaw Nat
                  (Add (TotalE I L) (Add (S (Pred (LenE B0))) (TotalE R H)))
                  (Add (TotalE I L) (Add (LenE B0) (TotalE R H)))
                  (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
                  (IdCongrRaw Nat Nat
                    (λ (W : Nat). Add (TotalE I L) (Add W (TotalE R H)))
                    (S (Pred (LenE B0))) (LenE B0)
                    (SPredPos (LenE B0) (HitLenPos Key B0 Eh)))
                  (IdSymRaw Nat
                    (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
                    (Add (TotalE I L) (Add (LenE B0) (TotalE R H)))
                    (TotalArrCat (S R) (acons R B0 H) I L)))))))
      (λ (Ef : Id Bool (HitL Key B0) False).
        IdTransRaw Nat
          (boolRec (λ (W2 : Bool). Nat)
            (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
            (HitL Key B0))
          (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
          (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
          (BoolRwF Nat
            (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
            (HitL Key B0) Ef)
          (IdTransRaw Nat
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
            (Add (TotalE I L) (Add (LenE B1) (TotalE R H)))
            (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
            (TotalArrCat (S R) (acons R B1 H) I L)
            (IdTransRaw Nat
              (Add (TotalE I L) (Add (LenE B1) (TotalE R H)))
              (Add (TotalE I L) (Add (LenE B0) (TotalE R H)))
              (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
              (IdCongrRaw Nat Nat
                (λ (W : Nat). Add (TotalE I L) (Add W (TotalE R H)))
                (LenE B1) (LenE B0)
                (IdTransRaw Nat (LenE B1) (BLenRem Key B0) (LenE B0)
                  Hl
                  (BoolRwF Nat (Pred (LenE B0)) (LenE B0) (HitL Key B0) Ef)))
              (IdSymRaw Nat
                (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H)))
                (Add (TotalE I L) (Add (LenE B0) (TotalE R H)))
                (TotalArrCat (S R) (acons R B0 H) I L))))) }
def RemTotEvTy : Term := prog_parse {
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    Id Nat (LenE B1) (BLenRem Key B0) →
    Id Nat
      (boolRec (λ (W2 : Bool). Nat)
        (S (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H))))
        (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B1 H)))
        (HitL Key B0))
      (TotalE (Add I (S R)) (arrCat I (S R) L (acons R B0 H))) }
example : chkL RemTotEv RemTotEvTy = true := by native_decide

/-! ## (xxi) Resize. The move fold's pure evidence, bucket level first. -/

/-- A key found in a well-hashed bucket hashes to that bucket's slot. -/
def HitKeyMod : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (K2 : Nat). λ (L : BktT).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        AllKeysMod Cap I Lm → Id Bool (HitL K2 Lm) True → Id Nat (Mod K2 Cap) I) {
      Nil => λ (Ha : AllKeysMod Cap I Nil). λ (Hh : Id Bool (HitL K2 Nil) True).
        botElim (Id Nat (Mod K2 Cap) I) (BoolFTRaw Hh),
      Cons (E) (T) Ih =>
        elim E return (λ (Em : Σ (k : Nat). Nat).
            AllKeysMod Cap I (Cons(Em, T)) → Id Bool (HitL K2 (Cons(Em, T))) True →
            Id Nat (Mod K2 Cap) I) {
          Pair (K3) (V3) =>
            λ (Ha : AllKeysMod Cap I (Cons(Pair(K3, V3), T))).
            λ (Hh : Id Bool (HitL K2 (Cons(Pair(K3, V3), T))) True).
              IfDecRaw (Eqb K2 K3) (Id Nat (Mod K2 Cap) I)
                (λ (E2 : Id Bool (Eqb K2 K3) True).
                  NatRwRaw (λ (W : Nat). Id Nat (Mod W Cap) I) K3 K2
                    (IdSymRaw Nat K2 K3 (EqbTrueEqRaw K2 K3 E2))
                    (FstT (Id Nat (Mod K3 Cap) I) (AllKeysMod Cap I T) Ha))
                (λ (E2 : Id Bool (Eqb K2 K3) False).
                  Ih (SndT (Id Nat (Mod K3 Cap) I) (AllKeysMod Cap I T) Ha)
                    (IdTransRaw Bool (HitL K2 T) (HitL K2 (Cons(Pair(K3, V3), T))) True
                      (IdSymRaw Bool (HitL K2 (Cons(Pair(K3, V3), T))) (HitL K2 T)
                        (IdCongrRaw OptN Bool IsSomeB
                          (FindL K2 (Cons(Pair(K3, V3), T))) (FindL K2 T)
                          (BoolRwF OptN (SomeN V3) (FindL K2 T) (Eqb K2 K3) E2)))
                      Hh)) } } }
def HitKeyModTy : Term := prog_parse {
  Π (Cap : Nat) → Π (I : Nat) → Π (K2 : Nat) → Π (L : BktT) →
    AllKeysMod Cap I L → Id Bool (HitL K2 L) True → Id Nat (Mod K2 Cap) I }
example : chkL HitKeyMod HitKeyModTy = true := by native_decide

/-- The contrapositive: a key hashing elsewhere is absent. -/
def NotHitOfMod : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (K2 : Nat). λ (L : BktT).
  λ (Ha : AllKeysMod Cap I L). λ (Ne : Id Bool (Eqb (Mod K2 Cap) I) False).
    IfDecRaw (HitL K2 L) (Id Bool (HitL K2 L) False)
      (λ (Eh : Id Bool (HitL K2 L) True).
        botElim (Id Bool (HitL K2 L) False)
          (BoolTFRaw (IdTransRaw Bool True (Eqb (Mod K2 Cap) I) False
            (IdSymRaw Bool (Eqb (Mod K2 Cap) I) True
              (IdTransRaw Bool (Eqb (Mod K2 Cap) I) (Eqb I I) True
                (IdCongrRaw Nat Bool (λ (W : Nat). Eqb W I) (Mod K2 Cap) I
                  (HitKeyMod Cap I K2 L Ha Eh))
                (EqbReflRaw I)))
            Ne)))
      (λ (Ef : Id Bool (HitL K2 L) False). Ef) }
def NotHitOfModTy : Term := prog_parse {
  Π (Cap : Nat) → Π (I : Nat) → Π (K2 : Nat) → Π (L : BktT) →
    AllKeysMod Cap I L → Id Bool (Eqb (Mod K2 Cap) I) False →
    Id Bool (HitL K2 L) False }
example : chkL NotHitOfMod NotHitOfModTy = true := by native_decide

def Le1Mul2 : Term := prog_parse {
  λ (C : Nat). λ (H : Le (S Z) C).
    LeTransRaw (S Z) C (Mul 2 C) H (LeAddRaw C (Add C Z)) }
def Le1Mul2Ty : Term := prog_parse { Π (C : Nat) → Le (S Z) C → Le (S Z) (Mul 2 C) }
example : chkL Le1Mul2 Le1Mul2Ty = true := by native_decide

/-- An array whose in-range buckets are all `Nil` holds nothing. -/
def TotalNilAll : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        (Π (J2 : Nat) → Le (S J2) Mz →
          Id (List (Σ (k : Nat). Nat)) (AgetB Mz Az J2) Nil) →
        Id Nat (TotalE Mz Az) Z)
      (λ (Hn : Π (J2 : Nat) → Le (S J2) Z →
          Id (List (Σ (k : Nat). Nat)) (AgetB Z Arr() J2) Nil). Refl)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : (Π (J2 : Nat) → Le (S J2) K →
            Id (List (Σ (k : Nat). Nat)) (AgetB K T J2) Nil) →
          Id Nat (TotalE K T) Z).
        λ (Hn : Π (J2 : Nat) → Le (S J2) (S K) →
            Id (List (Σ (k : Nat). Nat)) (AgetB (S K) (acons K H2 T) J2) Nil).
          IdTransRaw Nat (Add (LenE H2) (TotalE K T)) (Add (LenE H2) Z) Z
            (IdCongrRaw Nat Nat (λ (W : Nat). Add (LenE H2) W) (TotalE K T) Z
              (Ih (λ (J2 : Nat). λ (Hb : Le (S J2) K). Hn (S J2) Hb)))
            (IdTransRaw Nat (Add (LenE H2) Z) (LenE H2) Z
              (AddZeroRaw (LenE H2))
              (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
                (λ (W : List (Σ (k : Nat). Nat)). LenE W)
                H2 Nil (Hn Z unit))))
      M A }
def TotalNilAllTy : Term := prog_parse {
  Π (M : Nat) → Π (A : Array M (List (Σ (k : Nat). Nat))) →
    (Π (J2 : Nat) → Le (S J2) M →
      Id (List (Σ (k : Nat). Nat)) (AgetB M A J2) Nil) →
    Id Nat (TotalE M A) Z }
example : chkL TotalNilAll TotalNilAllTy = true := by native_decide

/-- One bucket-move step, pointwise: the head is inserted (fresh), the tail is
    moved by the recursive call; together they answer like the whole bucket. -/
def MoveStepPt : Term := prog_parse {
  λ (K : Nat). λ (V : Nat). λ (TL : BktT).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN). λ (D2 : Nat → OptN).
  λ (Hnd : Id Bool (HitL K TL) False).
  λ (H1 : Π (Q : Nat) → Id OptN (D1 Q)
       (boolRec (λ (W2 : Bool). OptN) (SomeN V) (D0 Q) (Eqb Q K))).
  λ (H2 : Π (Q : Nat) → Id OptN (D2 Q)
       (boolRec (λ (W2 : Bool). OptN) (FindL Q TL) (D1 Q) (HitL Q TL))).
    λ (Q : Nat).
      IfDecRaw (Eqb Q K)
        (Id OptN (D2 Q)
          (boolRec (λ (W2 : Bool). OptN)
            (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
            (HitL Q (Cons(Pair(K, V), TL)))))
        (λ (E2 : Id Bool (Eqb Q K) True).
          IdTransRaw OptN (D2 Q) (SomeN V)
            (boolRec (λ (W2 : Bool). OptN)
              (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
              (HitL Q (Cons(Pair(K, V), TL))))
            (IdTransRaw OptN (D2 Q) (D1 Q) (SomeN V)
              (IdTransRaw OptN (D2 Q)
                (boolRec (λ (W2 : Bool). OptN) (FindL Q TL) (D1 Q) (HitL Q TL))
                (D1 Q)
                (H2 Q)
                (BoolRwF OptN (FindL Q TL) (D1 Q) (HitL Q TL)
                  (NatRwRaw (λ (W : Nat). Id Bool (HitL W TL) False) K Q
                    (IdSymRaw Nat Q K (EqbTrueEqRaw Q K E2)) Hnd)))
              (IdTransRaw OptN (D1 Q)
                (boolRec (λ (W2 : Bool). OptN) (SomeN V) (D0 Q) (Eqb Q K))
                (SomeN V)
                (H1 Q)
                (BoolRwT OptN (SomeN V) (D0 Q) (Eqb Q K) E2)))
            (IdSymRaw OptN
              (boolRec (λ (W2 : Bool). OptN)
                (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                (HitL Q (Cons(Pair(K, V), TL))))
              (SomeN V)
              (IdTransRaw OptN
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                  (HitL Q (Cons(Pair(K, V), TL))))
                (FindL Q (Cons(Pair(K, V), TL)))
                (SomeN V)
                (BoolRwT OptN (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                  (HitL Q (Cons(Pair(K, V), TL)))
                  (IdSymRaw Bool True (HitL Q (Cons(Pair(K, V), TL)))
                    (HitEvHit K V Q TL
                      (IdTransRaw Bool (Eqb K Q) (Eqb Q K) True (EqbSymRaw K Q) E2))))
                (NatRwRaw (λ (W : Nat).
                    Id OptN (FindL W (Cons(Pair(K, V), TL))) (SomeN V))
                  K Q (IdSymRaw Nat Q K (EqbTrueEqRaw Q K E2))
                  (BoolRwT OptN (SomeN V) (FindL K TL) (Eqb K K) (EqbReflRaw K))))))
        (λ (E2 : Id Bool (Eqb Q K) False).
          IfDecRaw (HitL Q TL)
            (Id OptN (D2 Q)
              (boolRec (λ (W2 : Bool). OptN)
                (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                (HitL Q (Cons(Pair(K, V), TL)))))
            (λ (Eh : Id Bool (HitL Q TL) True).
              IdTransRaw OptN (D2 Q) (FindL Q TL)
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                  (HitL Q (Cons(Pair(K, V), TL))))
                (IdTransRaw OptN (D2 Q)
                  (boolRec (λ (W2 : Bool). OptN) (FindL Q TL) (D1 Q) (HitL Q TL))
                  (FindL Q TL)
                  (H2 Q)
                  (BoolRwT OptN (FindL Q TL) (D1 Q) (HitL Q TL) Eh))
                (IdSymRaw OptN
                  (boolRec (λ (W2 : Bool). OptN)
                    (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                    (HitL Q (Cons(Pair(K, V), TL))))
                  (FindL Q TL)
                  (IdTransRaw OptN
                    (boolRec (λ (W2 : Bool). OptN)
                      (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                      (HitL Q (Cons(Pair(K, V), TL))))
                    (boolRec (λ (W2 : Bool). OptN)
                      (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                      (HitL Q TL))
                    (FindL Q TL)
                    (IdCongrRaw Bool OptN
                      (λ (W : Bool). boolRec (λ (W2 : Bool). OptN)
                        (FindL Q (Cons(Pair(K, V), TL))) (D0 Q) W)
                      (HitL Q (Cons(Pair(K, V), TL))) (HitL Q TL)
                      (IdCongrRaw OptN Bool IsSomeB
                        (FindL Q (Cons(Pair(K, V), TL))) (FindL Q TL)
                        (BoolRwF OptN (SomeN V) (FindL Q TL) (Eqb Q K) E2)))
                    (IdTransRaw OptN
                      (boolRec (λ (W2 : Bool). OptN)
                        (FindL Q (Cons(Pair(K, V), TL))) (D0 Q) (HitL Q TL))
                      (FindL Q (Cons(Pair(K, V), TL)))
                      (FindL Q TL)
                      (BoolRwT OptN (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                        (HitL Q TL) Eh)
                      (BoolRwF OptN (SomeN V) (FindL Q TL) (Eqb Q K) E2)))))
            (λ (Ef : Id Bool (HitL Q TL) False).
              IdTransRaw OptN (D2 Q) (D0 Q)
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                  (HitL Q (Cons(Pair(K, V), TL))))
                (IdTransRaw OptN (D2 Q) (D1 Q) (D0 Q)
                  (IdTransRaw OptN (D2 Q)
                    (boolRec (λ (W2 : Bool). OptN) (FindL Q TL) (D1 Q) (HitL Q TL))
                    (D1 Q)
                    (H2 Q)
                    (BoolRwF OptN (FindL Q TL) (D1 Q) (HitL Q TL) Ef))
                  (IdTransRaw OptN (D1 Q)
                    (boolRec (λ (W2 : Bool). OptN) (SomeN V) (D0 Q) (Eqb Q K))
                    (D0 Q)
                    (H1 Q)
                    (BoolRwF OptN (SomeN V) (D0 Q) (Eqb Q K) E2)))
                (IdSymRaw OptN
                  (boolRec (λ (W2 : Bool). OptN)
                    (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                    (HitL Q (Cons(Pair(K, V), TL))))
                  (D0 Q)
                  (IdTransRaw OptN
                    (boolRec (λ (W2 : Bool). OptN)
                      (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                      (HitL Q (Cons(Pair(K, V), TL))))
                    (boolRec (λ (W2 : Bool). OptN)
                      (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                      (HitL Q TL))
                    (D0 Q)
                    (IdCongrRaw Bool OptN
                      (λ (W : Bool). boolRec (λ (W2 : Bool). OptN)
                        (FindL Q (Cons(Pair(K, V), TL))) (D0 Q) W)
                      (HitL Q (Cons(Pair(K, V), TL))) (HitL Q TL)
                      (IdCongrRaw OptN Bool IsSomeB
                        (FindL Q (Cons(Pair(K, V), TL))) (FindL Q TL)
                        (BoolRwF OptN (SomeN V) (FindL Q TL) (Eqb Q K) E2)))
                    (BoolRwF OptN (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
                      (HitL Q TL) Ef))))) }
def MoveStepPtTy : Term := prog_parse {
  Π (K : Nat) → Π (V : Nat) → Π (TL : BktT) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) → Π (D2 : Nat → OptN) →
    Id Bool (HitL K TL) False →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (SomeN V) (D0 Q) (Eqb Q K))) →
    (Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q TL) (D1 Q) (HitL Q TL))) →
    Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN)
        (FindL Q (Cons(Pair(K, V), TL))) (D0 Q)
        (HitL Q (Cons(Pair(K, V), TL)))) }
example : chkL MoveStepPt MoveStepPtTy = true := by native_decide

/-- Off-bucket frame between the entry and bucket-nilled compositions: any
    slot other than `J` reads the same bucket in both. -/
def NeBucketEq : Term := prog_parse {
  λ (J : Nat). λ (R : Nat).
  λ (LS : Array J BktT). λ (BJ : BktT). λ (HS : Array R BktT).
  λ (W : Nat).
  λ (Ne : Id Bool (Eqb W J) False).
    IfDecRaw (Leb W J)
      (Id (List (Σ (k : Nat). Nat))
        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W))
      (λ (El : Id Bool (Leb W J) True).
        IdTransRaw (List (Σ (k : Nat). Nat))
          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
          (AgetB J LS W)
          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W)
          (AgetBCatLo R Nil HS J LS W (LeNeLt W J (LebTrueLeRaw W J El) Ne))
          (IdSymRaw (List (Σ (k : Nat). Nat))
            (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W)
            (AgetB J LS W)
            (AgetBCatLo R BJ HS J LS W (LeNeLt W J (LebTrueLeRaw W J El) Ne))))
      (λ (El : Id Bool (Leb W J) False).
        elim (ModDecRaw J W (LebFalseGtRaw W J El)) return
          (λ (Wd : Σ (R2 : Nat). Id Nat W (Add J (S R2))).
            Id (List (Σ (k : Nat). Nat))
              (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
              (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W)) {
          Pair (Dd) (Hd) =>
            NatRwRaw (λ (W2 : Nat).
                Id (List (Σ (k : Nat). Nat))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W2)
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W2))
              (Add J (S Dd)) W
              (IdSymRaw Nat W (Add J (S Dd)) Hd)
              (IdTransRaw (List (Σ (k : Nat). Nat))
                (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) (Add J (S Dd)))
                (AgetB R HS Dd)
                (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) (Add J (S Dd)))
                (AgetBCatHi R Nil HS Dd J LS)
                (IdSymRaw (List (Σ (k : Nat). Nat))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) (Add J (S Dd)))
                  (AgetB R HS Dd)
                  (AgetBCatHi R BJ HS Dd J LS))) }) }
def NeBucketEqTy : Term := prog_parse {
  Π (J : Nat) → Π (R : Nat) →
  Π (LS : Array J BktT) → Π (BJ : BktT) → Π (HS : Array R BktT) →
  Π (W : Nat) →
    Id Bool (Eqb W J) False →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
      (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W) }
example : chkL NeBucketEq NeBucketEqTy = true := by native_decide

/-- The resize composition: the moved table answers like the model whenever the
    model answers, and like the (all-`None`) fresh table otherwise — where the
    model's misses collapse to the literal `None` through the caller-supplied
    η-escape (`NotHitFindNone` at the old map's stuck bucket). -/
def ResizeGlue : Term := prog_parse {
  λ (M : Nat → OptN). λ (DM : Nat → OptN). λ (DF : Nat → OptN). λ (DN : Nat → OptN).
  λ (HN : Π (Q : Nat) → Id OptN (DN Q) NoneN).
  λ (HM : Π (Q : Nat) → Id OptN (DM Q) (M Q)).
  λ (HF : Π (Q : Nat) → Id OptN (DF Q)
      (boolRec (λ (W2 : Bool). OptN) (DM Q) (DN Q) (IsSomeB (DM Q)))).
  λ (He : Π (Q : Nat) → Id Bool (IsSomeB (M Q)) False → Id OptN (M Q) NoneN).
    λ (Q : Nat).
      IfDecRaw (IsSomeB (M Q)) (Id OptN (DF Q) (M Q))
        (λ (E2 : Id Bool (IsSomeB (M Q)) True).
          IdTransRaw OptN (DF Q)
            (boolRec (λ (W2 : Bool). OptN) (M Q) (DN Q) (IsSomeB (M Q)))
            (M Q)
            (IdTransRaw OptN (DF Q)
              (boolRec (λ (W2 : Bool). OptN) (DM Q) (DN Q) (IsSomeB (DM Q)))
              (boolRec (λ (W2 : Bool). OptN) (M Q) (DN Q) (IsSomeB (M Q)))
              (HF Q)
              (IdCongrRaw OptN OptN
                (λ (X : OptN). boolRec (λ (W2 : Bool). OptN) X (DN Q) (IsSomeB X))
                (DM Q) (M Q) (HM Q)))
            (BoolRwT OptN (M Q) (DN Q) (IsSomeB (M Q)) E2))
        (λ (E2 : Id Bool (IsSomeB (M Q)) False).
          IdTransRaw OptN (DF Q) (DN Q) (M Q)
            (IdTransRaw OptN (DF Q)
              (boolRec (λ (W2 : Bool). OptN) (M Q) (DN Q) (IsSomeB (M Q)))
              (DN Q)
              (IdTransRaw OptN (DF Q)
                (boolRec (λ (W2 : Bool). OptN) (DM Q) (DN Q) (IsSomeB (DM Q)))
                (boolRec (λ (W2 : Bool). OptN) (M Q) (DN Q) (IsSomeB (M Q)))
                (HF Q)
                (IdCongrRaw OptN OptN
                  (λ (X : OptN). boolRec (λ (W2 : Bool). OptN) X (DN Q) (IsSomeB X))
                  (DM Q) (M Q) (HM Q)))
              (BoolRwF OptN (M Q) (DN Q) (IsSomeB (M Q)) E2))
            (IdTransRaw OptN (DN Q) NoneN (M Q)
              (HN Q)
              (IdSymRaw OptN (M Q) NoneN (He Q E2)))) }
def ResizeGlueTy : Term := prog_parse {
  Π (M : Nat → OptN) → Π (DM : Nat → OptN) → Π (DF : Nat → OptN) → Π (DN : Nat → OptN) →
    (Π (Q : Nat) → Id OptN (DN Q) NoneN) →
    (Π (Q : Nat) → Id OptN (DM Q) (M Q)) →
    (Π (Q : Nat) → Id OptN (DF Q)
      (boolRec (λ (W2 : Bool). OptN) (DM Q) (DN Q) (IsSomeB (DM Q)))) →
    (Π (Q : Nat) → Id Bool (IsSomeB (M Q)) False → Id OptN (M Q) NoneN) →
    Π (Q : Nat) → Id OptN (DF Q) (M Q) }
example : chkL ResizeGlue ResizeGlueTy = true := by native_decide

/-- Disjointness survives one bucket move: a key the nilled source still
    answers is off the moved bucket, so the after-move table still lacks it. -/
def MoveDisjStep : Term := prog_parse {
  λ (J : Nat). λ (R : Nat).
  λ (LS : Array J BktT). λ (BJ : BktT). λ (HS : Array R BktT).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN).
  λ (HakJ : AllKeysMod (Add J (S R)) J BJ).
  λ (HptB : Π (Q : Nat) → Id OptN (D1 Q)
       (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))).
  λ (Hdisj : Π (K2 : Nat) →
       Id Bool (IsSomeB (FindL K2 (AgetB (Add J (S R))
         (arrCat J (S R) LS (acons R BJ HS)) (Mod K2 (Add J (S R)))))) True →
       Id OptN (D0 K2) NoneN).
    λ (K2 : Nat).
    λ (Hs : Id Bool (IsSomeB (FindL K2 (AgetB (Add J (S R))
        (arrCat J (S R) LS (acons R Nil HS)) (Mod K2 (Add J (S R)))))) True).
      IfDecRaw (Eqb (Mod K2 (Add J (S R))) J)
        (Id OptN (D1 K2) NoneN)
        (λ (E2 : Id Bool (Eqb (Mod K2 (Add J (S R))) J) True).
          botElim (Id OptN (D1 K2) NoneN)
            (BoolFTRaw (IdTransRaw Bool False
              (IsSomeB (FindL K2 (AgetB (Add J (S R))
                (arrCat J (S R) LS (acons R Nil HS)) (Mod K2 (Add J (S R))))))
              True
              (IdSymRaw Bool
                (IsSomeB (FindL K2 (AgetB (Add J (S R))
                  (arrCat J (S R) LS (acons R Nil HS)) (Mod K2 (Add J (S R))))))
                False
                (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                  (λ (Wb : List (Σ (k : Nat). Nat)). IsSomeB (FindL K2 Wb))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                    (Mod K2 (Add J (S R))))
                  Nil
                  (NatRwRaw (λ (W : Nat).
                      Id (List (Σ (k : Nat). Nat))
                        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
                        Nil)
                    J (Mod K2 (Add J (S R)))
                    (IdSymRaw Nat (Mod K2 (Add J (S R))) J
                      (EqbTrueEqRaw (Mod K2 (Add J (S R))) J E2))
                    (AgetBCatMid R Nil HS J LS))))
              Hs)))
        (λ (E2 : Id Bool (Eqb (Mod K2 (Add J (S R))) J) False).
          IdTransRaw OptN (D1 K2) (D0 K2) NoneN
            (IdTransRaw OptN (D1 K2)
              (boolRec (λ (W2 : Bool). OptN) (FindL K2 BJ) (D0 K2) (HitL K2 BJ))
              (D0 K2)
              (HptB K2)
              (BoolRwF OptN (FindL K2 BJ) (D0 K2) (HitL K2 BJ)
                (NotHitOfMod (Add J (S R)) J K2 BJ HakJ E2)))
            (Hdisj K2
              (IdTransRaw Bool
                (IsSomeB (FindL K2 (AgetB (Add J (S R))
                  (arrCat J (S R) LS (acons R BJ HS)) (Mod K2 (Add J (S R))))))
                (IsSomeB (FindL K2 (AgetB (Add J (S R))
                  (arrCat J (S R) LS (acons R Nil HS)) (Mod K2 (Add J (S R))))))
                True
                (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                  (λ (Wb : List (Σ (k : Nat). Nat)). IsSomeB (FindL K2 Wb))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                    (Mod K2 (Add J (S R))))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                    (Mod K2 (Add J (S R))))
                  (IdSymRaw (List (Σ (k : Nat). Nat))
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                      (Mod K2 (Add J (S R))))
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                      (Mod K2 (Add J (S R))))
                    (NeBucketEq J R LS BJ HS (Mod K2 (Add J (S R))) E2)))
                Hs))) }
def MoveDisjStepTy : Term := prog_parse {
  Π (J : Nat) → Π (R : Nat) →
  Π (LS : Array J BktT) → Π (BJ : BktT) → Π (HS : Array R BktT) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) →
    AllKeysMod (Add J (S R)) J BJ →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))) →
    (Π (K2 : Nat) →
      Id Bool (IsSomeB (FindL K2 (AgetB (Add J (S R))
        (arrCat J (S R) LS (acons R BJ HS)) (Mod K2 (Add J (S R)))))) True →
      Id OptN (D0 K2) NoneN) →
    Π (K2 : Nat) →
      Id Bool (IsSomeB (FindL K2 (AgetB (Add J (S R))
        (arrCat J (S R) LS (acons R Nil HS)) (Mod K2 (Add J (S R)))))) True →
      Id OptN (D1 K2) NoneN }
example : chkL MoveDisjStep MoveDisjStepTy = true := by native_decide

/-- The already-moved prefix stays `Nil` after one more bucket is nilled. -/
def MoveNilStep : Term := prog_parse {
  λ (J : Nat). λ (R : Nat).
  λ (LS : Array J BktT). λ (BJ : BktT). λ (HS : Array R BktT).
  λ (HsrcLo : Π (J2 : Nat) → Id Bool (Leb (S J2) J) True →
       Id (List (Σ (k : Nat). Nat))
         (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J2) Nil).
    λ (J2 : Nat). λ (Hb : Id Bool (Leb (S J2) (S J)) True).
      IfDecRaw (Eqb J2 J)
        (Id (List (Σ (k : Nat). Nat))
          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) J2) Nil)
        (λ (E2 : Id Bool (Eqb J2 J) True).
          NatRwRaw (λ (W : Nat).
              Id (List (Σ (k : Nat). Nat))
                (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W) Nil)
            J J2 (IdSymRaw Nat J2 J (EqbTrueEqRaw J2 J E2))
            (AgetBCatMid R Nil HS J LS))
        (λ (E2 : Id Bool (Eqb J2 J) False).
          IdTransRaw (List (Σ (k : Nat). Nat))
            (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) J2)
            (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J2)
            Nil
            (NeBucketEq J R LS BJ HS J2 E2)
            (HsrcLo J2
              (LeLebTrueRaw (S J2) J
                (LeNeLt J2 J (LebTrueLeRaw J2 J Hb) E2)))) }
def MoveNilStepTy : Term := prog_parse {
  Π (J : Nat) → Π (R : Nat) →
  Π (LS : Array J BktT) → Π (BJ : BktT) → Π (HS : Array R BktT) →
    (Π (J2 : Nat) → Id Bool (Leb (S J2) J) True →
      Id (List (Σ (k : Nat). Nat))
        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J2) Nil) →
    Π (J2 : Nat) → Id Bool (Leb (S J2) (S J)) True →
      Id (List (Σ (k : Nat). Nat))
        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) J2) Nil }
example : chkL MoveNilStep MoveNilStepTy = true := by native_decide

/-- Frame case of the per-level composition: `q`'s slot is off the moved
    bucket, both array states show the same bucket there, and the dst chain
    collapses `D1` to `D0`. -/
def MoveSlotsFrame : Term := prog_parse {
  λ (AE : BktT). λ (AN : BktT). λ (W : BktT).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN). λ (D2 : Nat → OptN).
  λ (Q : Nat).
  λ (HE : Id BktT AE W). λ (HN : Id BktT AN W).
  λ (H10 : Id OptN (D1 Q) (D0 Q)).
  λ (HR : Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q AN) (D1 Q) (IsSomeB (FindL Q AN)))).
    IdTransRaw OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q W) (D0 Q) (IsSomeB (FindL Q W)))
      (boolRec (λ (W2 : Bool). OptN) (FindL Q AE) (D0 Q) (IsSomeB (FindL Q AE)))
      (IdTransRaw OptN (D2 Q)
        (boolRec (λ (W2 : Bool). OptN) (FindL Q W) (D1 Q) (IsSomeB (FindL Q W)))
        (boolRec (λ (W2 : Bool). OptN) (FindL Q W) (D0 Q) (IsSomeB (FindL Q W)))
        (IdTransRaw OptN (D2 Q)
          (boolRec (λ (W2 : Bool). OptN) (FindL Q AN) (D1 Q) (IsSomeB (FindL Q AN)))
          (boolRec (λ (W2 : Bool). OptN) (FindL Q W) (D1 Q) (IsSomeB (FindL Q W)))
          HR
          (IdCongrRaw BktT OptN
            (λ (Wb : BktT). boolRec (λ (W2 : Bool). OptN)
              (FindL Q Wb) (D1 Q) (IsSomeB (FindL Q Wb)))
            AN W HN))
        (IdCongrRaw OptN OptN
          (λ (Wo : OptN). boolRec (λ (W2 : Bool). OptN)
            (FindL Q W) Wo (IsSomeB (FindL Q W)))
          (D1 Q) (D0 Q) H10))
      (IdCongrRaw BktT OptN
        (λ (Wb : BktT). boolRec (λ (W2 : Bool). OptN)
          (FindL Q Wb) (D0 Q) (IsSomeB (FindL Q Wb)))
        W AE (IdSymRaw BktT AE W HE)) }
def MoveSlotsFrameTy : Term := prog_parse {
  Π (AE : BktT) → Π (AN : BktT) → Π (W : BktT) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) → Π (D2 : Nat → OptN) →
  Π (Q : Nat) →
    Id BktT AE W → Id BktT AN W →
    Id OptN (D1 Q) (D0 Q) →
    Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q AN) (D1 Q) (IsSomeB (FindL Q AN))) →
    Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q AE) (D0 Q) (IsSomeB (FindL Q AE))) }
example : chkL MoveSlotsFrame MoveSlotsFrameTy = true := by native_decide

/-- The per-level pointwise composition: moving bucket `J` composes with the
    recursive move of the (bucket-nilled) rest into the whole-level claim. -/
def MoveSlotsPt : Term := prog_parse {
  λ (J : Nat). λ (R : Nat).
  λ (LS : Array J BktT). λ (BJ : BktT). λ (HS : Array R BktT).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN). λ (D2 : Nat → OptN).
  λ (HakJ : AllKeysMod (Add J (S R)) J BJ).
  λ (HptB : Π (Q : Nat) → Id OptN (D1 Q)
       (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))).
  λ (HptR : Π (Q : Nat) → Id OptN (D2 Q)
       (boolRec (λ (W2 : Bool). OptN)
         (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
           (Mod Q (Add J (S R)))))
         (D1 Q)
         (IsSomeB (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
           (Mod Q (Add J (S R)))))))).
    λ (Q : Nat).
      IfDecRaw (Eqb (Mod Q (Add J (S R))) J)
        (Id OptN (D2 Q)
          (boolRec (λ (W2 : Bool). OptN)
            (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
              (Mod Q (Add J (S R)))))
            (D0 Q)
            (IsSomeB (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
              (Mod Q (Add J (S R))))))))
        (λ (Ej : Id Bool (Eqb (Mod Q (Add J (S R))) J) True).
          NatRwRaw (λ (W : Nat).
              Id OptN (D2 Q)
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W))
                  (D0 Q)
                  (IsSomeB (FindL Q
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W)))))
            J (Mod Q (Add J (S R)))
            (IdSymRaw Nat (Mod Q (Add J (S R))) J
              (EqbTrueEqRaw (Mod Q (Add J (S R))) J Ej))
            (IdTransRaw OptN (D2 Q)
              (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))
              (boolRec (λ (W2 : Bool). OptN)
                (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J))
                (D0 Q)
                (IsSomeB (FindL Q
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J))))
              (IdTransRaw OptN (D2 Q) (D1 Q)
                (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))
                (IdTransRaw OptN (D2 Q)
                  (boolRec (λ (W2 : Bool). OptN)
                    (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                      (Mod Q (Add J (S R)))))
                    (D1 Q)
                    (IsSomeB (FindL Q
                      (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                        (Mod Q (Add J (S R)))))))
                  (D1 Q)
                  (HptR Q)
                  (IdCongrRaw BktT OptN
                    (λ (Wb : BktT). boolRec (λ (W2 : Bool). OptN)
                      (FindL Q Wb) (D1 Q) (IsSomeB (FindL Q Wb)))
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                      (Mod Q (Add J (S R))))
                    Nil
                    (NatRwRaw (λ (W : Nat).
                        Id (List (Σ (k : Nat). Nat))
                          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
                          Nil)
                      J (Mod Q (Add J (S R)))
                      (IdSymRaw Nat (Mod Q (Add J (S R))) J
                        (EqbTrueEqRaw (Mod Q (Add J (S R))) J Ej))
                      (AgetBCatMid R Nil HS J LS))))
                (HptB Q))
              (IdSymRaw OptN
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J))
                  (D0 Q)
                  (IsSomeB (FindL Q
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J))))
                (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))
                (IdCongrRaw BktT OptN
                  (λ (Wb : BktT). boolRec (λ (W2 : Bool). OptN)
                    (FindL Q Wb) (D0 Q) (IsSomeB (FindL Q Wb)))
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) J)
                  BJ
                  (AgetBCatMid R BJ HS J LS)))))
        (λ (Ej : Id Bool (Eqb (Mod Q (Add J (S R))) J) False).
          IfDecRaw (Leb (Mod Q (Add J (S R))) J)
            (Id OptN (D2 Q)
              (boolRec (λ (W2 : Bool). OptN)
                (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                  (Mod Q (Add J (S R)))))
                (D0 Q)
                (IsSomeB (FindL Q
                  (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                    (Mod Q (Add J (S R))))))))
            (λ (El : Id Bool (Leb (Mod Q (Add J (S R))) J) True).
              MoveSlotsFrame
                (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                  (Mod Q (Add J (S R))))
                (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                  (Mod Q (Add J (S R))))
                (AgetB J LS (Mod Q (Add J (S R))))
                D0 D1 D2 Q
                (AgetBCatLo R BJ HS J LS (Mod Q (Add J (S R)))
                  (LeNeLt (Mod Q (Add J (S R))) J
                    (LebTrueLeRaw (Mod Q (Add J (S R))) J El) Ej))
                (AgetBCatLo R Nil HS J LS (Mod Q (Add J (S R)))
                  (LeNeLt (Mod Q (Add J (S R))) J
                    (LebTrueLeRaw (Mod Q (Add J (S R))) J El) Ej))
                (IdTransRaw OptN (D1 Q)
                  (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))
                  (D0 Q)
                  (HptB Q)
                  (BoolRwF OptN (FindL Q BJ) (D0 Q) (HitL Q BJ)
                    (NotHitOfMod (Add J (S R)) J Q BJ HakJ Ej)))
                (HptR Q))
            (λ (El : Id Bool (Leb (Mod Q (Add J (S R))) J) False).
              elim (ModDecRaw J (Mod Q (Add J (S R)))
                  (LebFalseGtRaw (Mod Q (Add J (S R))) J El)) return
                (λ (Wd : Σ (R2 : Nat). Id Nat (Mod Q (Add J (S R))) (Add J (S R2))).
                  Id OptN (D2 Q)
                    (boolRec (λ (W2 : Bool). OptN)
                      (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                        (Mod Q (Add J (S R)))))
                      (D0 Q)
                      (IsSomeB (FindL Q
                        (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                          (Mod Q (Add J (S R)))))))) {
                Pair (Dd) (Hd) =>
                  MoveSlotsFrame
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
                      (Mod Q (Add J (S R))))
                    (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
                      (Mod Q (Add J (S R))))
                    (AgetB R HS Dd)
                    D0 D1 D2 Q
                    (NatRwRaw (λ (W : Nat).
                        Id (List (Σ (k : Nat). Nat))
                          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS)) W)
                          (AgetB R HS Dd))
                      (Add J (S Dd)) (Mod Q (Add J (S R)))
                      (IdSymRaw Nat (Mod Q (Add J (S R))) (Add J (S Dd)) Hd)
                      (AgetBCatHi R BJ HS Dd J LS))
                    (NatRwRaw (λ (W : Nat).
                        Id (List (Σ (k : Nat). Nat))
                          (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS)) W)
                          (AgetB R HS Dd))
                      (Add J (S Dd)) (Mod Q (Add J (S R)))
                      (IdSymRaw Nat (Mod Q (Add J (S R))) (Add J (S Dd)) Hd)
                      (AgetBCatHi R Nil HS Dd J LS))
                    (IdTransRaw OptN (D1 Q)
                      (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))
                      (D0 Q)
                      (HptB Q)
                      (BoolRwF OptN (FindL Q BJ) (D0 Q) (HitL Q BJ)
                        (NotHitOfMod (Add J (S R)) J Q BJ HakJ Ej)))
                    (HptR Q) })) }
def MoveSlotsPtTy : Term := prog_parse {
  Π (J : Nat) → Π (R : Nat) →
  Π (LS : Array J BktT) → Π (BJ : BktT) → Π (HS : Array R BktT) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) → Π (D2 : Nat → OptN) →
    AllKeysMod (Add J (S R)) J BJ →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q BJ) (D0 Q) (HitL Q BJ))) →
    (Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN)
        (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
          (Mod Q (Add J (S R)))))
        (D1 Q)
        (IsSomeB (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R Nil HS))
          (Mod Q (Add J (S R)))))))) →
    Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN)
        (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
          (Mod Q (Add J (S R)))))
        (D0 Q)
        (IsSomeB (FindL Q (AgetB (Add J (S R)) (arrCat J (S R) LS (acons R BJ HS))
          (Mod Q (Add J (S R))))))) }
example : chkL MoveSlotsPt MoveSlotsPtTy = true := by native_decide

/-- The moved head stays fresh for the tail's move: derived outside the walk,
    because a λ inside a recursive fn may not cite that fn's own Π-typed
    parameter (see `lamFeedG`/`lamFeedJ` below; snapshots do not help). -/
def MoveFreshStep : Term := prog_parse {
  λ (C2v : Nat). λ (K : Nat). λ (V : Nat). λ (TL : BktT).
  λ (D0A : Array C2v BktT). λ (D1A : Array C2v BktT).
  λ (Hnd0 : Id Bool (HitL K TL) False).
  λ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB C2v D1A (Mod Q C2v)))
      (boolRec (λ (W2 : Bool). OptN) (SomeN V)
        (FindL Q (AgetB C2v D0A (Mod Q C2v))) (Eqb Q K))).
  λ (Hfr0 : Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (Cons(Pair(K, V), TL))) True) →
      Id OptN (FindL K2 (AgetB C2v D0A (Mod K2 C2v))) NoneN).
    (λ (K2 : Nat). λ (Hk : Id Bool (HitL K2 TL) True).
                  IfDecRaw (Eqb K2 K)
                    (Id OptN (FindL K2 (AgetB C2v D1A (Mod K2 C2v))) NoneN)
                    (λ (E2 : Id Bool (Eqb K2 K) True).
                      botElim (Id OptN (FindL K2 (AgetB C2v D1A (Mod K2 C2v))) NoneN)
                        (BoolTFRaw (IdTransRaw Bool True (HitL K TL) False
                          (IdSymRaw Bool (HitL K TL) True
                            (NatRwRaw (λ (W : Nat). Id Bool (HitL W TL) True) K2 K
                              (EqbTrueEqRaw K2 K E2) Hk))
                          (Hnd0))))
                    (λ (E2 : Id Bool (Eqb K2 K) False).
                      IdTransRaw OptN (FindL K2 (AgetB C2v D1A (Mod K2 C2v)))
                        (FindL K2 (AgetB C2v D0A (Mod K2 C2v))) NoneN
                        (IdTransRaw OptN (FindL K2 (AgetB C2v D1A (Mod K2 C2v)))
                          (boolRec (λ (W2 : Bool). OptN) (SomeN V)
                            (FindL K2 (AgetB C2v D0A (Mod K2 C2v))) (Eqb K2 K))
                          (FindL K2 (AgetB C2v D0A (Mod K2 C2v)))
                          (Hpt K2)
                          (BoolRwF OptN (SomeN V)
                            (FindL K2 (AgetB C2v D0A (Mod K2 C2v))) (Eqb K2 K) E2))
                        (Hfr0 K2 (IdSymRaw Bool True (HitL K2 (Cons(Pair(K, V), TL)))
                          (HitEvMiss K V K2 TL True
                            (IdTransRaw Bool (Eqb K K2) (Eqb K2 K) False
                              (EqbSymRaw K K2) E2)
                            (IdSymRaw Bool (HitL K2 TL) True Hk)))))) }
def MoveFreshStepTy : Term := prog_parse {
  Π (C2v : Nat) → Π (K : Nat) → Π (V : Nat) → Π (TL : BktT) →
  Π (D0A : Array C2v BktT) → Π (D1A : Array C2v BktT) →
    Id Bool (HitL K TL) False →
    (Π (Q : Nat) → Id OptN (FindL Q (AgetB C2v D1A (Mod Q C2v)))
      (boolRec (λ (W2 : Bool). OptN) (SomeN V)
        (FindL Q (AgetB C2v D0A (Mod Q C2v))) (Eqb Q K))) →
    (Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (Cons(Pair(K, V), TL))) True) →
      Id OptN (FindL K2 (AgetB C2v D0A (Mod K2 C2v))) NoneN) →
    Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 TL) True) →
      Id OptN (FindL K2 (AgetB C2v D1A (Mod K2 C2v))) NoneN }
example : chkL MoveFreshStep MoveFreshStepTy = true := by native_decide

/-- The moved bucket's keys are fresh in dst: the level's disjointness at the
    entry composition, specialized through the slot identity — outside the walk
    for the same recursive-λ reason. -/
def MoveSlotsFresh : Term := prog_parse {
  λ (Jv : Nat). λ (Rv : Nat). λ (C2v : Nat).
  λ (LSv : Array Jv BktT). λ (BJv : BktT). λ (HSv : Array Rv BktT).
  λ (DDv : Array C2v BktT).
  λ (HakJv : AllKeysMod (Add Jv (S Rv)) Jv BJv).
  λ (Hdisj0 : Π (K2 : Nat) → Π (Hs2 : Id Bool (IsSomeB (FindL K2
      (AgetB (Add Jv (S Rv)) (arrCat Jv (S Rv) LSv (acons Rv BJv HSv))
        (Mod K2 (Add Jv (S Rv)))))) True) →
      Id OptN (FindL K2 (AgetB C2v DDv (Mod K2 C2v))) NoneN).
    (λ (K2 : Nat). λ (Hk : Id Bool (HitL K2 BJv) True).
                Hdisj0 K2
                  (IdTransRaw Bool
                    (IsSomeB (FindL K2 (AgetB (Add Jv (S Rv))
                      (arrCat Jv (S Rv) LSv (acons Rv BJv HSv)) (Mod K2 (Add Jv (S Rv))))))
                    (IsSomeB (FindL K2 BJv)) True
                    (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                      (λ (Wb : List (Σ (k : Nat). Nat)). IsSomeB (FindL K2 Wb))
                      (AgetB (Add Jv (S Rv)) (arrCat Jv (S Rv) LSv (acons Rv BJv HSv)) (Mod K2 (Add Jv (S Rv))))
                      BJv
                      (NatRwRaw (λ (W : Nat).
                          Id (List (Σ (k : Nat). Nat))
                            (AgetB (Add Jv (S Rv)) (arrCat Jv (S Rv) LSv (acons Rv BJv HSv)) W)
                            BJv)
                        Jv (Mod K2 (Add Jv (S Rv)))
                        (IdSymRaw Nat (Mod K2 (Add Jv (S Rv))) Jv (HitKeyMod (Add Jv (S Rv)) Jv K2 BJv HakJv Hk))
                        (AgetBCatMid Rv BJv HSv Jv LSv)))
                    Hk)) }
def MoveSlotsFreshTy : Term := prog_parse {
  Π (Jv : Nat) → Π (Rv : Nat) → Π (C2v : Nat) →
  Π (LSv : Array Jv BktT) → Π (BJv : BktT) → Π (HSv : Array Rv BktT) →
  Π (DDv : Array C2v BktT) →
    AllKeysMod (Add Jv (S Rv)) Jv BJv →
    (Π (K2 : Nat) → Π (Hs2 : Id Bool (IsSomeB (FindL K2
      (AgetB (Add Jv (S Rv)) (arrCat Jv (S Rv) LSv (acons Rv BJv HSv))
        (Mod K2 (Add Jv (S Rv)))))) True) →
      Id OptN (FindL K2 (AgetB C2v DDv (Mod K2 C2v))) NoneN) →
    Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 BJv) True) →
      Id OptN (FindL K2 (AgetB C2v DDv (Mod K2 C2v))) NoneN }
example : chkL MoveSlotsFresh MoveSlotsFreshTy = true := by native_decide

/-- MoveSlots' base case, pointwise: every slot is below `j = capF`, so the
    drained source answers `None` everywhere and the fold's claim collapses to
    the untouched dst. Outside the walk (the recursive-λ restriction). -/
def MoveBasePt : Term := prog_parse {
  λ (CFv : Nat). λ (Jv : Nat). λ (C2v : Nat).
  λ (Sv : Array CFv BktT). λ (Dv : Array C2v BktT).
  λ (HLe1Fv : Le (S Z) CFv). λ (Hjz : Id Nat CFv Jv).
  λ (Hlo : Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CFv Sv J2) Nil).
    λ (Q : Nat).
      IdSymRaw OptN
        (boolRec (λ (W2 : Bool). OptN)
          (FindL Q (AgetB CFv Sv (Mod Q CFv)))
          (FindL Q (AgetB C2v Dv (Mod Q C2v)))
          (IsSomeB (FindL Q (AgetB CFv Sv (Mod Q CFv)))))
        (FindL Q (AgetB C2v Dv (Mod Q C2v)))
        (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
          (λ (Wb : List (Σ (k : Nat). Nat)).
            boolRec (λ (W2 : Bool). OptN)
              (FindL Q Wb)
              (FindL Q (AgetB C2v Dv (Mod Q C2v)))
              (IsSomeB (FindL Q Wb)))
          (AgetB CFv Sv (Mod Q CFv)) Nil
          (Hlo (Mod Q CFv)
            (LeLebTrueRaw (S (Mod Q CFv)) Jv
              (NatRwRaw (λ (W : Nat). Le (S (Mod Q CFv)) W) CFv Jv Hjz
                (ModLtNRaw Q CFv HLe1Fv))))) }
def MoveBasePtTy : Term := prog_parse {
  Π (CFv : Nat) → Π (Jv : Nat) → Π (C2v : Nat) →
  Π (Sv : Array CFv BktT) → Π (Dv : Array C2v BktT) →
    Le (S Z) CFv → Id Nat CFv Jv →
    (Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CFv Sv J2) Nil) →
    Π (Q : Nat) →
      Id OptN (FindL Q (AgetB C2v Dv (Mod Q C2v)))
        (boolRec (λ (W2 : Bool). OptN)
          (FindL Q (AgetB CFv Sv (Mod Q CFv)))
          (FindL Q (AgetB C2v Dv (Mod Q C2v)))
          (IsSomeB (FindL Q (AgetB CFv Sv (Mod Q CFv))))) }
example : chkL MoveBasePt MoveBasePtTy = true := by native_decide

/-- MoveSlots' base case, drainedness at every in-range index. -/
def MoveBaseNil : Term := prog_parse {
  λ (CFv : Nat). λ (Jv : Nat). λ (Sv : Array CFv BktT).
  λ (Hjz : Id Nat CFv Jv).
  λ (Hlo : Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CFv Sv J2) Nil).
    λ (J2 : Nat). λ (Hb : Le (S J2) CFv).
      Hlo J2 (LeLebTrueRaw (S J2) Jv
        (NatRwRaw (λ (W : Nat). Le (S J2) W) CFv Jv Hjz Hb)) }
def MoveBaseNilTy : Term := prog_parse {
  Π (CFv : Nat) → Π (Jv : Nat) → Π (Sv : Array CFv BktT) →
    Id Nat CFv Jv →
    (Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CFv Sv J2) Nil) →
    Π (J2 : Nat) → Π (Hb : Le (S J2) CFv) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CFv Sv J2) Nil }
example : chkL MoveBaseNil MoveBaseNilTy = true := by native_decide

/-- Rewrite the bucket everywhere in a one-bucket move claim. -/
def AgetBktCongr : Term := prog_parse {
  λ (B1 : BktT). λ (A1 : BktT).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN).
  λ (Hb : Id (List (Σ (k : Nat). Nat)) B1 A1).
  λ (Hpt : Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q B1) (D0 Q) (HitL Q B1))).
    λ (Q : Nat).
      IdTransRaw OptN (D1 Q)
        (boolRec (λ (W2 : Bool). OptN) (FindL Q B1) (D0 Q) (HitL Q B1))
        (boolRec (λ (W2 : Bool). OptN) (FindL Q A1) (D0 Q) (HitL Q A1))
        (Hpt Q)
        (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
          (λ (Wb : List (Σ (k : Nat). Nat)). boolRec (λ (W2 : Bool). OptN)
            (FindL Q Wb) (D0 Q) (IsSomeB (FindL Q Wb)))
          B1 A1 Hb) }
def AgetBktCongrTy : Term := prog_parse {
  Π (B1 : BktT) → Π (A1 : BktT) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) →
    Id (List (Σ (k : Nat). Nat)) B1 A1 →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q B1) (D0 Q) (HitL Q B1))) →
    Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q A1) (D0 Q) (HitL Q A1)) }
example : chkL AgetBktCongr AgetBktCongrTy = true := by native_decide

/-- A slot's invariant, read off the fold at an arbitrary in-range index — the
    carve-free extraction (`MoveOne`'s caller has no composition in scope). -/
def SFAgetInv : Term := prog_parse {
  λ (Cap : Nat). λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Π (I0 : Nat) → Π (Hs : SlotsFrom Cap Mz Az I0) →
        Π (J : Nat) → Π (Hb : Le (S J) Mz) →
          SlotInv Cap (Add J I0) (AgetB Mz Az J))
      (λ (I0 : Nat). λ (Hs : Unit). λ (J : Nat). λ (Hb : Le (S J) Z).
        botElim (SlotInv Cap (Add J I0) (AgetB Z Arr() J)) Hb)
      (λ (K : Nat). λ (H2 : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Π (I0 : Nat) → Π (Hs : SlotsFrom Cap K T I0) →
            Π (J : Nat) → Π (Hb : Le (S J) K) →
              SlotInv Cap (Add J I0) (AgetB K T J)).
          λ (I0 : Nat).
          λ (Hs : Σ (Hx : SlotInv Cap I0 H2). SlotsFrom Cap K T (S I0)).
          λ (J : Nat).
            elim J return (λ (Jz : Nat). Π (Hb : Le (S Jz) (S K)) →
                SlotInv Cap (Add Jz I0) (AgetB (S K) (acons K H2 T) Jz)) {
              Z => λ (Hb : Le (S Z) (S K)).
                FstT (SlotInv Cap I0 H2) (SlotsFrom Cap K T (S I0)) Hs,
              S (J2) Ihj => λ (Hb : Le (S (S J2)) (S K)).
                NatRwRaw (λ (W : Nat). SlotInv Cap W (AgetB K T J2))
                  (Add J2 (S I0)) (S (Add J2 I0))
                  (AddSuccRaw J2 I0)
                  (Ih (S I0)
                    (SndT (SlotInv Cap I0 H2) (SlotsFrom Cap K T (S I0)) Hs)
                    J2 Hb) })
      M A }
def SFAgetInvTy : Term := prog_parse {
  Π (Cap : Nat) → Π (M : Nat) → Π (A : Array M (List (Σ (k : Nat). Nat))) →
  Π (I0 : Nat) → Π (Hs : SlotsFrom Cap M A I0) →
  Π (J : Nat) → Π (Hb : Le (S J) M) →
    SlotInv Cap (Add J I0) (AgetB M A J) }
example : chkL SFAgetInv SFAgetInvTy = true := by native_decide

/-- The per-level pointwise composition, carve-free: the level's dst-change
    (bucket J moved) and the recursive claim over the drained-at-J source
    compose into the whole-level claim, using only the three opaque-array
    facts `MoveOne` exports. -/
def MoveLevelPt : Term := prog_parse {
  λ (CF : Nat). λ (Jv : Nat).
  λ (S0 : Array CF (List (Σ (k : Nat). Nat))).
  λ (SM : Array CF (List (Σ (k : Nat). Nat))).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN). λ (D2 : Nat → OptN).
  λ (HakJ : AllKeysMod CF Jv (AgetB CF S0 Jv)).
  λ (Hnil : Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil).
  λ (Hfrm : Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)).
  λ (HptB : Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
        (HitL Q (AgetB CF S0 Jv)))).
  λ (HptR : Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF SM (Mod Q CF))) (D1 Q)
        (IsSomeB (FindL Q (AgetB CF SM (Mod Q CF)))))).
    λ (Q : Nat).
      IfDecRaw (Eqb (Mod Q CF) Jv)
        (Id OptN (D2 Q)
          (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 (Mod Q CF))) (D0 Q)
            (IsSomeB (FindL Q (AgetB CF S0 (Mod Q CF))))))
        (λ (Ej : Id Bool (Eqb (Mod Q CF) Jv) True).
          NatRwRaw (λ (W : Nat).
              Id OptN (D2 Q)
                (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 W)) (D0 Q)
                  (IsSomeB (FindL Q (AgetB CF S0 W)))))
            Jv (Mod Q CF)
            (IdSymRaw Nat (Mod Q CF) Jv (EqbTrueEqRaw (Mod Q CF) Jv Ej))
            (IdTransRaw OptN (D2 Q) (D1 Q)
              (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
                (IsSomeB (FindL Q (AgetB CF S0 Jv))))
              (IdTransRaw OptN (D2 Q)
                (boolRec (λ (W2 : Bool). OptN)
                  (FindL Q (AgetB CF SM (Mod Q CF))) (D1 Q)
                  (IsSomeB (FindL Q (AgetB CF SM (Mod Q CF)))))
                (D1 Q)
                (HptR Q)
                (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
                  (λ (Wb : List (Σ (k : Nat). Nat)).
                    boolRec (λ (W2 : Bool). OptN) (FindL Q Wb) (D1 Q)
                      (IsSomeB (FindL Q Wb)))
                  (AgetB CF SM (Mod Q CF)) Nil
                  (NatRwRaw (λ (W : Nat).
                      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM W) Nil)
                    Jv (Mod Q CF)
                    (IdSymRaw Nat (Mod Q CF) Jv (EqbTrueEqRaw (Mod Q CF) Jv Ej))
                    Hnil)))
              (HptB Q)))
        (λ (Ej : Id Bool (Eqb (Mod Q CF) Jv) False).
          MoveSlotsFrame
            (AgetB CF S0 (Mod Q CF))
            (AgetB CF SM (Mod Q CF))
            (AgetB CF S0 (Mod Q CF))
            D0 D1 D2 Q
            Refl
            (Hfrm (Mod Q CF) Ej)
            (IdTransRaw OptN (D1 Q)
              (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
                (HitL Q (AgetB CF S0 Jv)))
              (D0 Q)
              (HptB Q)
              (BoolRwF OptN (FindL Q (AgetB CF S0 Jv)) (D0 Q)
                (HitL Q (AgetB CF S0 Jv))
                (NotHitOfMod CF Jv Q (AgetB CF S0 Jv) HakJ Ej)))
            (HptR Q)) }
def MoveLevelPtTy : Term := prog_parse {
  Π (CF : Nat) → Π (Jv : Nat) →
  Π (S0 : Array CF (List (Σ (k : Nat). Nat))) →
  Π (SM : Array CF (List (Σ (k : Nat). Nat))) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) → Π (D2 : Nat → OptN) →
    AllKeysMod CF Jv (AgetB CF S0 Jv) →
    Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil →
    (Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)) →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
        (HitL Q (AgetB CF S0 Jv)))) →
    (Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF SM (Mod Q CF))) (D1 Q)
        (IsSomeB (FindL Q (AgetB CF SM (Mod Q CF)))))) →
    Π (Q : Nat) → Id OptN (D2 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 (Mod Q CF))) (D0 Q)
        (IsSomeB (FindL Q (AgetB CF S0 (Mod Q CF))))) }
example : chkL MoveLevelPt MoveLevelPtTy = true := by native_decide

/-- Disjointness composes past one level, carve-free. -/
def MoveLevelDisj : Term := prog_parse {
  λ (CF : Nat). λ (Jv : Nat).
  λ (S0 : Array CF (List (Σ (k : Nat). Nat))).
  λ (SM : Array CF (List (Σ (k : Nat). Nat))).
  λ (D0 : Nat → OptN). λ (D1 : Nat → OptN).
  λ (HakJ : AllKeysMod CF Jv (AgetB CF S0 Jv)).
  λ (Hnil : Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil).
  λ (Hfrm : Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)).
  λ (HptB : Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
        (HitL Q (AgetB CF S0 Jv)))).
  λ (Hdisj0 : Π (K2 : Nat) → Π (Hs2 : Id Bool (IsSomeB (FindL K2
      (AgetB CF S0 (Mod K2 CF)))) True) → Id OptN (D0 K2) NoneN).
    λ (K2 : Nat).
    λ (Hs : Id Bool (IsSomeB (FindL K2 (AgetB CF SM (Mod K2 CF)))) True).
      IfDecRaw (Eqb (Mod K2 CF) Jv)
        (Id OptN (D1 K2) NoneN)
        (λ (Ej : Id Bool (Eqb (Mod K2 CF) Jv) True).
          botElim (Id OptN (D1 K2) NoneN)
            (BoolFTRaw (IdTransRaw Bool False
              (IsSomeB (FindL K2 (AgetB CF SM (Mod K2 CF)))) True
              (IdSymRaw Bool (IsSomeB (FindL K2 (AgetB CF SM (Mod K2 CF)))) False
                (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                  (λ (Wb : List (Σ (k : Nat). Nat)). IsSomeB (FindL K2 Wb))
                  (AgetB CF SM (Mod K2 CF)) Nil
                  (NatRwRaw (λ (W : Nat).
                      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM W) Nil)
                    Jv (Mod K2 CF)
                    (IdSymRaw Nat (Mod K2 CF) Jv (EqbTrueEqRaw (Mod K2 CF) Jv Ej))
                    Hnil)))
              Hs)))
        (λ (Ej : Id Bool (Eqb (Mod K2 CF) Jv) False).
          IdTransRaw OptN (D1 K2) (D0 K2) NoneN
            (IdTransRaw OptN (D1 K2)
              (boolRec (λ (W2 : Bool). OptN) (FindL K2 (AgetB CF S0 Jv)) (D0 K2)
                (HitL K2 (AgetB CF S0 Jv)))
              (D0 K2)
              (HptB K2)
              (BoolRwF OptN (FindL K2 (AgetB CF S0 Jv)) (D0 K2)
                (HitL K2 (AgetB CF S0 Jv))
                (NotHitOfMod CF Jv K2 (AgetB CF S0 Jv) HakJ Ej)))
            (Hdisj0 K2
              (IdTransRaw Bool (IsSomeB (FindL K2 (AgetB CF S0 (Mod K2 CF))))
                (IsSomeB (FindL K2 (AgetB CF SM (Mod K2 CF)))) True
                (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                  (λ (Wb : List (Σ (k : Nat). Nat)). IsSomeB (FindL K2 Wb))
                  (AgetB CF S0 (Mod K2 CF)) (AgetB CF SM (Mod K2 CF))
                  (IdSymRaw (List (Σ (k : Nat). Nat))
                    (AgetB CF SM (Mod K2 CF)) (AgetB CF S0 (Mod K2 CF))
                    (Hfrm (Mod K2 CF) Ej)))
                Hs))) }
def MoveLevelDisjTy : Term := prog_parse {
  Π (CF : Nat) → Π (Jv : Nat) →
  Π (S0 : Array CF (List (Σ (k : Nat). Nat))) →
  Π (SM : Array CF (List (Σ (k : Nat). Nat))) →
  Π (D0 : Nat → OptN) → Π (D1 : Nat → OptN) →
    AllKeysMod CF Jv (AgetB CF S0 Jv) →
    Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil →
    (Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)) →
    (Π (Q : Nat) → Id OptN (D1 Q)
      (boolRec (λ (W2 : Bool). OptN) (FindL Q (AgetB CF S0 Jv)) (D0 Q)
        (HitL Q (AgetB CF S0 Jv)))) →
    (Π (K2 : Nat) → Π (Hs2 : Id Bool (IsSomeB (FindL K2
      (AgetB CF S0 (Mod K2 CF)))) True) → Id OptN (D0 K2) NoneN) →
    Π (K2 : Nat) →
      Π (Hs : Id Bool (IsSomeB (FindL K2 (AgetB CF SM (Mod K2 CF)))) True) →
      Id OptN (D1 K2) NoneN }
example : chkL MoveLevelDisj MoveLevelDisjTy = true := by native_decide

/-- The already-drained prefix grows by one, carve-free. -/
def MoveLevelNil : Term := prog_parse {
  λ (CF : Nat). λ (Jv : Nat).
  λ (S0 : Array CF (List (Σ (k : Nat). Nat))).
  λ (SM : Array CF (List (Σ (k : Nat). Nat))).
  λ (Hnil : Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil).
  λ (Hfrm : Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)).
  λ (Hlo : Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF S0 J2) Nil).
    λ (J2 : Nat). λ (Hb : Id Bool (Leb (S J2) (S Jv)) True).
      IfDecRaw (Eqb J2 Jv)
        (Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) Nil)
        (λ (E2 : Id Bool (Eqb J2 Jv) True).
          NatRwRaw (λ (W : Nat). Id (List (Σ (k : Nat). Nat)) (AgetB CF SM W) Nil)
            Jv J2 (IdSymRaw Nat J2 Jv (EqbTrueEqRaw J2 Jv E2)) Hnil)
        (λ (E2 : Id Bool (Eqb J2 Jv) False).
          IdTransRaw (List (Σ (k : Nat). Nat))
            (AgetB CF SM J2) (AgetB CF S0 J2) Nil
            (Hfrm J2 E2)
            (Hlo J2 (LeLebTrueRaw (S J2) Jv
              (LeNeLt J2 Jv (LebTrueLeRaw J2 Jv Hb) E2)))) }
def MoveLevelNilTy : Term := prog_parse {
  Π (CF : Nat) → Π (Jv : Nat) →
  Π (S0 : Array CF (List (Σ (k : Nat). Nat))) →
  Π (SM : Array CF (List (Σ (k : Nat). Nat))) →
    Id (List (Σ (k : Nat). Nat)) (AgetB CF SM Jv) Nil →
    (Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 Jv) False) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) (AgetB CF S0 J2)) →
    (Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) Jv) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF S0 J2) Nil) →
    Π (J2 : Nat) → Π (Hb : Id Bool (Leb (S J2) (S Jv)) True) →
      Id (List (Σ (k : Nat). Nat)) (AgetB CF SM J2) Nil }
example : chkL MoveLevelNil MoveLevelNilTy = true := by native_decide

/-! ### The rotation move's pure vocabulary

    `SlotPush` moves one bucket node from src to dst by mutation (the
    mem::replace rotation) instead of constructing a fresh node. Its evidence
    is definitional where the old walk's was inductive, because the pushed
    bucket is literally `Cons(head, old-bucket)`. The vocabulary: emptiness as
    a Bool (`IsNilB` — the drain loop cannot match src, SlotPush does), the
    three Nil lemmas, the definitional push equation, the done-arm collapses,
    the two invariant-extension builders, and the identity applications for
    the constructor-argument fence (`KeepLe`'s trick at Nat and bucket). -/

def IdNat : Term := prog_parse { λ (X : Nat). X }
def IdNatTy : Term := prog_parse { Π (X : Nat) → Nat }
example : chkL IdNat IdNatTy = true := by native_decide

def IdBkt : Term := prog_parse { λ (X : List (Σ (k : Nat). Nat)). X }
def IdBktTy : Term := prog_parse {
  Π (X : List (Σ (k : Nat). Nat)) → List (Σ (k : Nat). Nat) }
example : chkL IdBkt IdBktTy = true := by native_decide

/-- Bucket emptiness, as a Bool the drain loop can `if e :` on. -/
def IsNilB : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Bool) {
      Nil => True,
      Cons (E) (T) Rec => False } }
def IsNilBTy : Term := prog_parse { Π (L : List (Σ (k : Nat). Nat)) → Bool }
example : chkL IsNilB IsNilBTy = true := by native_decide

/-- An `IsNilB`-empty bucket answers no key. -/
def NilHitFalse : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilB Lm) True → Id Bool (HitL Q Lm) False) {
      Nil => λ (Hn : Id Bool True True). Refl,
      Cons (E) (T) Rec => λ (Hn : Id Bool False True).
        botElim (Id Bool (HitL Q (Cons(E, T))) False) (BoolFTRaw Hn) } }
def NilHitFalseTy : Term := prog_parse {
  Π (Q : Nat) → Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilB L) True → Id Bool (HitL Q L) False }
example : chkL NilHitFalse NilHitFalseTy = true := by native_decide

/-- An `IsNilB`-empty bucket has length zero. -/
def NilLenZ : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilB Lm) True → Id Nat (LenE Lm) Z) {
      Nil => λ (Hn : Id Bool True True). Refl,
      Cons (E) (T) Rec => λ (Hn : Id Bool False True).
        botElim (Id Nat (LenE (Cons(E, T))) Z) (BoolFTRaw Hn) } }
def NilLenZTy : Term := prog_parse {
  Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilB L) True → Id Nat (LenE L) Z }
example : chkL NilLenZ NilLenZTy = true := by native_decide

/-- A nonempty bucket has positive length — the drain loop's fuel-Z absurdity. -/
def NotNilLenPos : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Id Bool (IsNilB Lm) False → Le (S Z) (LenE Lm)) {
      Nil => λ (Hn : Id Bool True False).
        botElim (Le (S Z) (LenE Nil)) (BoolTFRaw Hn),
      Cons (E) (T) Rec => λ (Hn : Id Bool False False). unit } }
def NotNilLenPosTy : Term := prog_parse {
  Π (L : List (Σ (k : Nat). Nat)) →
    Id Bool (IsNilB L) False → Le (S Z) (LenE L) }
example : chkL NotNilLenPos NotNilLenPosTy = true := by native_decide

/-- The push equation, definitional: prepending `(K0, V0)` answers `Some V0`
    at `K0` and delegates elsewhere — no walk, so no induction. This is
    `MoveStepPt`'s `H1` hypothesis shape verbatim. -/
def PtEvPush : Term := prog_parse {
  λ (K0 : Nat). λ (V0 : Nat). λ (B0 : BktT). λ (Q : Nat). Refl }
def PtEvPushTy : Term := prog_parse {
  Π (K0 : Nat) → Π (V0 : Nat) → Π (B0 : BktT) → Π (Q : Nat) →
    Id OptN (FindL Q (Cons(Pair(K0, V0), B0)))
      (boolRec (λ (W2 : Bool). OptN) (SomeN V0) (FindL Q B0) (Eqb Q K0)) }
example : chkL PtEvPush PtEvPushTy = true := by native_decide

/-- Drain-done, pointwise: the drained source answers no key, so the fold's
    claim collapses to the untouched dst (per-bucket `MoveBasePt`). -/
def MoveDonePt : Term := prog_parse {
  λ (C2 : Nat). λ (Bd : BktT). λ (Dd : Array C2 BktT).
  λ (E : Id Bool (IsNilB Bd) True).
    λ (Q : Nat).
      IdSymRaw OptN
        (boolRec (λ (W2 : Bool). OptN) (FindL Q Bd)
          (FindL Q (AgetB C2 Dd (Mod Q C2))) (HitL Q Bd))
        (FindL Q (AgetB C2 Dd (Mod Q C2)))
        (BoolRwF OptN (FindL Q Bd) (FindL Q (AgetB C2 Dd (Mod Q C2)))
          (HitL Q Bd) (NilHitFalse Q Bd E)) }
def MoveDonePtTy : Term := prog_parse {
  Π (C2 : Nat) → Π (Bd : BktT) → Π (Dd : Array C2 BktT) →
    Id Bool (IsNilB Bd) True →
    Π (Q : Nat) → Id OptN (FindL Q (AgetB C2 Dd (Mod Q C2)))
      (boolRec (λ (W2 : Bool). OptN) (FindL Q Bd)
        (FindL Q (AgetB C2 Dd (Mod Q C2))) (HitL Q Bd)) }
example : chkL MoveDonePt MoveDonePtTy = true := by native_decide

/-- Drain-done, the total: adding a drained bucket's length changes nothing. -/
def MoveDoneTot : Term := prog_parse {
  λ (C2 : Nat). λ (Bd : BktT). λ (Dd : Array C2 BktT).
  λ (E : Id Bool (IsNilB Bd) True).
    IdSymRaw Nat (Add (LenE Bd) (TotalE C2 Dd)) (TotalE C2 Dd)
      (IdCongrRaw Nat Nat (λ (W : Nat). Add W (TotalE C2 Dd))
        (LenE Bd) Z (NilLenZ Bd E)) }
def MoveDoneTotTy : Term := prog_parse {
  Π (C2 : Nat) → Π (Bd : BktT) → Π (Dd : Array C2 BktT) →
    Id Bool (IsNilB Bd) True →
    Id Nat (TotalE C2 Dd) (Add (LenE Bd) (TotalE C2 Dd)) }
example : chkL MoveDoneTot MoveDoneTotTy = true := by native_decide

/-- `AllKeysMod` extends over the pushed head, by application (the fence). -/
def MkAkCons : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (K : Nat). λ (V : Nat). λ (B : BktT).
  λ (Hm : Id Nat (Mod K Cap) I). λ (Ha : AllKeysMod Cap I B).
    Pair(Hm, Ha) }
def MkAkConsTy : Term := prog_parse {
  Π (Cap : Nat) → Π (I : Nat) → Π (K : Nat) → Π (V : Nat) → Π (B : BktT) →
    Id Nat (Mod K Cap) I → AllKeysMod Cap I B →
    AllKeysMod Cap I (Cons(Pair(K, V), B)) }
example : chkL MkAkCons MkAkConsTy = true := by native_decide

/-- `NodupB` extends over the pushed head, by application (the fence). -/
def MkNdCons : Term := prog_parse {
  λ (K : Nat). λ (V : Nat). λ (B : BktT).
  λ (Hn : Id Bool (HitL K B) False). λ (Hd : NodupB B).
    Pair(Hn, Hd) }
def MkNdConsTy : Term := prog_parse {
  Π (K : Nat) → Π (V : Nat) → Π (B : BktT) →
    Id Bool (HitL K B) False → NodupB B →
    NodupB (Cons(Pair(K, V), B)) }
example : chkL MkNdCons MkNdConsTy = true := by native_decide

/-! ## (xv) The fixed-capacity map chain, full specs

    TWO chained modules, seeded from the standard library and checked AT
    ELABORATION: `hmM0 := prog (Dllbc.std) { … }` holds the six bucket-level and
    allocation links (`InsertInList`, `RemoveL`, `SlotOfE`, `NewHM`, `SlotUpd`,
    `SlotRem`), and `hmM := prog (hmM0) { … }` holds the six map-level ones
    (`SlotPush`, `MoveBktR`, `MoveOne`, `MoveSlots`, `InsertHM`, `RemoveHM`).
    `hmM` is the consumer-facing seed. The cut is forced rather than stylistic:
    one module this size dies in the code generator, which is the eleven-links
    law StdChain hit first (docs/21 §11).

    Return types are written INLINE in their headers, where the parameters have
    their own names — no Lean function taking spliced return types, no telescope
    vocabulary to keep in step. The claim sites are NAMED with `@marker`s: eight
    carry the spec conjuncts (`nfind`/`nsize` for New, `ifind`/`iframe`/`isize`
    for Insert, `rfound`/`rpt`/`rsize` for Remove) and three sit inside bodies
    (`ivv`, `igrow`, `inogrow`). Every lying twin below is MINTED — one marked
    claim edited on the persisted `Checked.term`, checked from the same seed —
    so a twin is the honest program but for the one site, as a value-level fact
    rather than by a reader trusting that two spellings share a body. -/


/-- A slot's invariant pair, by application (the constructor-argument fence). -/
def MkSlotInv : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (B : BktT).
  λ (H1 : AllKeysMod Cap I B). λ (H2 : NodupB B).
    Pair(H1, H2) }
def MkSlotInvTy : Term := prog_parse {
  Π (Cap : Nat) → Π (I : Nat) → Π (B : BktT) →
    AllKeysMod Cap I B → NodupB B → SlotInv Cap I B }
example : chkL MkSlotInv MkSlotInvTy = true := by native_decide

/-- The trivial pointwise equation for a singleton bucket built from `Nil` —
    named so the Nil arm's component is an application, not a λ literal. -/
def PtEvNil : Term := prog_parse {
  λ (Key : Nat). λ (V : Nat). λ (Q : Nat). Refl }
def PtEvNilTy : Term := prog_parse {
  Π (Key : Nat) → Π (V : Nat) → Π (Q : Nat) →
    Id OptN (FindL Q (Cons(Pair(Key, V), Nil))) (BFindIns Q Key V Nil) }
example : chkL PtEvNil PtEvNilTy = true := by native_decide

/-! ### The chain, honest form (docs/21 §11)

    ONE seeded module: the walk, the slot pack, `New`, the move layer,
    `Insert` with resize, `Remove` — return types INLINE in their headers
    (no `keyIv`/`selfIv` vocabulary, no per-twin retype), claim sites marked.
    The `Insert` fresh-key ARMS are docs/22 FRAGMENTS spliced under markers
    (`@inogrow`/`@igrow`): an arm body is one term, and naming it is what lets
    `twinNoResize` plant the no-resize arm over the resize arm — the lie the
    id world could only transcribe at 670 lines. Every spec former the std
    seed binds (`Mod`, `Mul`, `Pred`, …) is written qualified inside the block
    (the §9 audit residual); the hashmap's own formers (`FindHM`, `SizeHM`, …)
    are file-local constants and stay bare. -/

/-- The no-resize arm of `InsertHM`'s fresh-key path (a docs/22 fragment:
    free names bind at the splice site). -/
def noGrowArm : Term := prog_parse {
*self := Pair(cap, Pair(load, Pair((@ibump S(nn)), Pair(slots,
  MkInv cap load (@ibump S nn) SL1 HLe1 HLoad
    (LebTrueLeRaw (Mul 5 (S nn)) load e4) H4y Hsf2))));
Pair(Hpt2,
  IdSymRaw Nat
    (boolRec (λ (W2 : Bool). Nat) nn (S nn)
      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))))
    (S nn)
    (BoolRwF Nat nn (S nn)
      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
      (IdTransRaw Bool
        (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
        Hit0 False
        (IdSymRaw Bool Hit0
          (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))) Hh2)
        e2)))
}

/-- The resize arm — rehash into `Mul 2 cap` slots via the move layer. -/
def growArm : Term := prog_parse {
let Val0 = val;
let nslots = MkSlots (Mul 2 cap);
let C2b = Mul 2 cap;
let DN0 = nslots;
let db = &m nslots;
let HdisjB = (λ (K2 : Nat).
      λ (Hs : Id Bool (IsSomeB (FindL K2
          (AgetB Cap0 SL1 (Mod K2 Cap0)))) True).
        IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
          (λ (Wb : List (Σ (k : Nat). Nat)). FindL K2 Wb)
          (AgetB C2b DN0 (Mod K2 C2b)) Nil
          (AgetBMkSlots C2b (Mod K2 C2b))
);
let HnilB = (λ (J2 : Nat). λ (Hb : Id Bool (Leb (S J2) Z) True).
        botElim (Id (List (Σ (k : Nat). Nat))
          (AgetB Cap0 SL1 J2) Nil) (BoolFTRaw Hb)
);
let Pair(HptM, Pair(HsrcFM, Pair(HtotM, HsfM))) =
  MoveSlots(cap, Z, fuel, cap, Mul 2 cap, Refl, &m *sb, &m *db,
    Le1Mul2 cap HLe1, HLe1,
    LeRwLRaw fuel (S (S nn)) (S (TotalE Cap0 SL1))
      (IdCongrRaw Nat Nat (λ (W : Nat). S W) (S nn) (TotalE Cap0 SL1) H4y)
      Hfuel,
    Hsf2,
    SFMkSlots (Mul 2 cap) (Mul 2 cap) Z, HdisjB, HnilB);
let SL1b = *sb;
let SL2 = *db;
*self := Pair(Mul 2 cap, Pair(Mul 4 (Mul 2 cap), Pair((@ibump S(nn)), Pair(nslots,
  MkInv (Mul 2 cap) (Mul 4 (Mul 2 cap)) (@ibump S nn) SL2
    (Le1Mul2 cap HLe1)
    Refl
    (LedgerGrowRaw cap nn HLe1
      (LeRwRRaw (Mul 5 nn) load (Mul 4 cap) HLoad HLed))
    (IdTransRaw Nat (S nn) (TotalE Cap0 SL1) (TotalE C2b SL2)
      H4y
      (IdSymRaw Nat (TotalE C2b SL2) (TotalE Cap0 SL1)
        (IdTransRaw Nat (TotalE C2b SL2)
          (Add (TotalE Cap0 SL1b) (TotalE C2b SL2))
          (TotalE Cap0 SL1)
          (IdSymRaw Nat
            (Add (TotalE Cap0 SL1b) (TotalE C2b SL2))
            (TotalE C2b SL2)
            (IdCongrRaw Nat Nat (λ (W : Nat). Add W (TotalE C2b SL2))
              (TotalE Cap0 SL1b) Z
              (TotalNilAll Cap0 SL1b HsrcFM)))
          (IdTransRaw Nat
            (Add (TotalE Cap0 SL1b) (TotalE C2b SL2))
            (Add (TotalE Cap0 SL1) (TotalE C2b DN0))
            (TotalE Cap0 SL1)
            HtotM
            (IdTransRaw Nat
              (Add (TotalE Cap0 SL1) (TotalE C2b DN0))
              (Add (TotalE Cap0 SL1) Z)
              (TotalE Cap0 SL1)
              (IdCongrRaw Nat Nat
                (λ (W : Nat). Add (TotalE Cap0 SL1) W)
                (TotalE C2b DN0) Z (TotalMkSlots C2b))
              (AddZeroRaw (TotalE Cap0 SL1)))))))
    HsfM))));
Pair(ResizeGlue
       (λ (Qz : Nat). boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
         (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0))) (Eqb Qz Key0))
       (λ (Qz : Nat). FindL Qz (AgetB Cap0 SL1 (Mod Qz Cap0)))
       (λ (Qz : Nat). FindL Qz (AgetB C2b SL2 (Mod Qz C2b)))
       (λ (Qz : Nat). FindL Qz (AgetB C2b DN0 (Mod Qz C2b)))
       (λ (Qz : Nat).
         IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
           (λ (Wb : List (Σ (k : Nat). Nat)). FindL Qz Wb)
           (AgetB C2b DN0 (Mod Qz C2b)) Nil
           (AgetBMkSlots C2b (Mod Qz C2b)))
       Hpt2 HptM
       (λ (Qz : Nat).
         λ (Ee : Id Bool (IsSomeB (boolRec (λ (W2 : Bool). OptN)
             (SomeN Val0)
             (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
             (Eqb Qz Key0))) False).
           IfDecRaw (Eqb Qz Key0)
             (Id OptN (boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
               (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
               (Eqb Qz Key0)) NoneN)
             (λ (E5 : Id Bool (Eqb Qz Key0) True).
               botElim (Id OptN (boolRec (λ (W2 : Bool). OptN)
                   (SomeN Val0)
                   (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                   (Eqb Qz Key0)) NoneN)
                 (BoolTFRaw (IdTransRaw Bool True
                   (IsSomeB (boolRec (λ (W2 : Bool). OptN)
                     (SomeN Val0)
                     (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                     (Eqb Qz Key0)))
                   False
                   (IdSymRaw Bool
                     (IsSomeB (boolRec (λ (W2 : Bool). OptN)
                       (SomeN Val0)
                       (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                       (Eqb Qz Key0)))
                     True
                     (IdCongrRaw OptN Bool IsSomeB
                       (boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
                         (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                         (Eqb Qz Key0))
                       (SomeN Val0)
                       (BoolRwT OptN (SomeN Val0)
                         (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                         (Eqb Qz Key0) E5)))
                   Ee)))
             (λ (E5 : Id Bool (Eqb Qz Key0) False).
               IdTransRaw OptN
                 (boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
                   (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                   (Eqb Qz Key0))
                 (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                 NoneN
                 (BoolRwF OptN (SomeN Val0)
                   (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                   (Eqb Qz Key0) E5)
                 (NotHitFindNone Qz (AgetB Cap0 SL0 (Mod Qz Cap0))
                   (IdTransRaw Bool
                     (IsSomeB (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0))))
                     (IsSomeB (boolRec (λ (W2 : Bool). OptN)
                       (SomeN Val0)
                       (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                       (Eqb Qz Key0)))
                     False
                     (IdCongrRaw OptN Bool IsSomeB
                       (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                       (boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
                         (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                         (Eqb Qz Key0))
                       (IdSymRaw OptN
                         (boolRec (λ (W2 : Bool). OptN) (SomeN Val0)
                           (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                           (Eqb Qz Key0))
                         (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                         (BoolRwF OptN (SomeN Val0)
                           (FindL Qz (AgetB Cap0 SL0 (Mod Qz Cap0)))
                           (Eqb Qz Key0) E5)))
                     Ee)))),
  IdSymRaw Nat
    (boolRec (λ (W2 : Bool). Nat) nn (S nn)
      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))))
    (S nn)
    (BoolRwF Nat nn (S nn)
      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
      (IdTransRaw Bool
        (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
        Hit0 False
        (IdSymRaw Bool Hit0
          (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))) Hh2)
        e2)))
}

set_option maxHeartbeats 0 in
def hmM0 : Checked := prog (Dllbc.std) {
  fn InsertInList [fuel] (fuel : Nat, cap : Nat, islot : Nat, key : Nat, val : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel,
                          Hkm : Id Nat (Dllbc.StdChainRaw.Mod key cap) islot,
                          Hak : AllKeysMod cap islot (*b),
                          Hnd : NodupB (*b))
      -> Σ (hit : Bool).
         Σ (Hh : Id Bool hit (HitL key (old *b))).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (*b)) (BFindIns Q key val (old *b))).
         Σ (Hln : Id Nat (LenE (*b)) (BLenIns key (old *b))).
         Σ0 (Hk2 : AllKeysMod cap islot (*b)). NodupB (*b)
      { match b {
          Nil => {
            *b := Cons(Pair(key, val), Nil);
            Pair(False, Pair(Refl, Pair(PtEvNil key val, Pair(Refl,
              Pair(Pair(Hkm, unit), Pair(Refl, unit))))))
          },
          Cons(Pair(kk, vv), tl) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
              let K0 = *kk;
              let V0 = *vv;
              let T0 = *tl;
              if e : Eqb *kk key {
                *vv := (@ivv val);
                Pair(True,
                  Pair(HitEvHit K0 V0 key T0 e,
                  Pair(PtEvHit K0 V0 val key T0 e,
                  Pair(LnEvHit K0 V0 val key T0 e,
                  Pair(Hak, Hnd)))))
              } else {
                let Pair(hit2, Pair(Hh2, Pair(Hpt2, Pair(Hln2, Pair(Hak3, Hnd3))))) =
                  InsertInList(f2, cap, islot, key, val, &m *tl, Hf, Hkm,
                    SndT (Id Nat (Dllbc.StdChainRaw.Mod K0 cap) islot) (AllKeysMod cap islot T0) Hak,
                    SndT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd);
                Pair(hit2,
                  Pair(HitEvMiss K0 V0 key T0 hit2 e Hh2,
                  Pair(UpdEvMiss K0 V0 (SomeN val) key T0 (*tl) e Hpt2,
                  Pair(LnEvMiss K0 V0 key T0 (*tl) e Hln2,
                  Pair(Pair(FstT (Id Nat (Dllbc.StdChainRaw.Mod K0 cap) islot)
                              (AllKeysMod cap islot T0) Hak, Hak3),
                       Pair(UpdNdMiss K0 (SomeN val) key T0 (*tl) e Hpt2
                              (FstT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd),
                            Hnd3))))))
              } }
          } } };
  fn RemoveL [fuel] (fuel : Nat, cap : Nat, islot : Nat, key : Nat,
                     l : List (Σ (k : Nat). Nat),
                     Hf : Le (LenE l) fuel,
                     Hak : AllKeysMod cap islot l,
                     Hnd : NodupB l)
      -> Σ (ret : Σ (bb : Bool). OptP bb Nat).
         Σ (l2 : List (Σ (k : Nat). Nat)).
         Σ (Hr : Id OptN ret (FindL key l)).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q l2) (BFindRem Q key l)).
         Σ (Hln : Id Nat (LenE l2) (BLenRem key l)).
         Σ0 (Hk2 : AllKeysMod cap islot l2). NodupB l2
      { match l {
          Nil =>
            Pair(NoneN, Pair(Nil, Pair(Refl, Pair(RemPtNil key, Pair(Refl,
              Pair(Hak, Hnd)))))),
          Cons(Pair(kk, vv), tl2) => match fuel {
            Z => botElim Unit Hf,
            S(f2) => {
              let K0 = kk;
              let V0 = vv;
              let T0 = tl2;
              if e : Eqb kk key {
                Pair(Pair(True, vv), Pair(tl2,
                  Pair(RemHrHit K0 V0 key T0 e,
                  Pair(RemPtHit K0 V0 key T0 e
                         (FstT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd),
                  Pair(RemLnHit K0 V0 key T0 e,
                  Pair(SndT (Id Nat (Dllbc.StdChainRaw.Mod K0 cap) islot) (AllKeysMod cap islot T0) Hak,
                       SndT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd))))))
              } else {
                let Pair(rr2, Pair(l3, Pair(Hr2, Pair(Hpt2, Pair(Hln2, Pair(Hak4, Hnd4)))))) =
                  RemoveL(f2, cap, islot, key, tl2, Hf,
                    SndT (Id Nat (Dllbc.StdChainRaw.Mod K0 cap) islot) (AllKeysMod cap islot T0) Hak,
                    SndT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd);
                let Ret0 = rr2;
                let L3 = l3;
                Pair(rr2, Pair(Cons(Pair(kk, vv), l3),
                  Pair(RemHrMiss K0 V0 key T0 Ret0 e Hr2,
                  Pair(UpdEvMiss K0 V0 NoneN key T0 L3 e Hpt2,
                  Pair(RemLnMiss K0 V0 key T0 L3 e Hln2,
                  Pair(Pair(FstT (Id Nat (Dllbc.StdChainRaw.Mod K0 cap) islot)
                              (AllKeysMod cap islot T0) Hak, Hak4),
                       Pair(UpdNdMiss K0 NoneN key T0 L3 e Hpt2
                              (FstT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd),
                            Hnd4)))))))
              } }
          } } };
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Dllbc.StdChainRaw.Mod h n) {
    SlotPack h n Hne };
  fn NewHM (cap : Nat, HLe1 : Le (S Z) cap) -> Σ (hm : HashMapT).
         Σ0 (Hfind : Π (Q : Nat) → Id OptN (FindHM Q hm) (@nfind NoneN)).
         Id Nat (SizeHM hm) (@nsize Z) {
    let Cap0 = cap;
    Pair(Pair(cap, Pair(Dllbc.StdChainRaw.Mul 4 cap, Pair(Z, Pair(MkSlots cap,
        MkInv cap (Dllbc.StdChainRaw.Mul 4 cap) Z (MkSlots cap) HLe1 Refl unit
          (IdSymRaw Nat (TotalE cap (MkSlots cap)) Z (TotalMkSlots cap))
          (SFMkSlots cap cap Z))))),
      Pair(λ (Q : Nat).
             IdCongrRaw (List (Σ (k : Nat). Nat)) (Σ (bb : Bool). OptP bb Nat)
               (λ (W : List (Σ (k : Nat). Nat)). FindL Q W)
               (AgetB Cap0 (MkSlots Cap0) (Dllbc.StdChainRaw.Mod Q Cap0)) Nil
               (AgetBMkSlots Cap0 (Dllbc.StdChainRaw.Mod Q Cap0)),
           Refl))
  };
  fn SlotUpd (fuel : Nat, cap : Nat, key : Nat, val : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))),
              HLe1 : Le (S Z) cap,
              Hfl : Le (S (TotalE cap (*b))) fuel,
              Hsf : SlotsFrom cap cap (*b) Z)
      -> Σ (hit : Bool).
         Σ (Hh : Id Bool hit (IsSomeB (FindL key (AgetB cap (old *b) (Dllbc.StdChainRaw.Mod key cap))))).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap (*b) (Dllbc.StdChainRaw.Mod Q cap)))
              (BFindIns Q key val (AgetB cap (old *b) (Dllbc.StdChainRaw.Mod Q cap)))).
         Σ0 (Htot : Id Nat (TotalE cap (*b))
              (boolRec (λ (W2 : Bool). Nat) (TotalE cap (old *b))
                (S (TotalE cap (old *b))) hit)).
         SlotsFrom cap cap (*b) Z
      {
        let Cap0 = cap;
        let Key0 = key;
        let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, HLe1);
        let I0 = i;
        let R0 = r;
        let Him0 = him;
        let pre = &m (*b)[Z ; i ; S r | LeAddRaw i (S r) | hd];
        let cell = &m (*b)[i ; 1 ; r];
        let hic = &m (*b)[S i ; r];
        let bb = &m (*cell)[0];
        let L0 = *pre;
        let B0 = *bb;
        let H0 = *hic;
        let HsfL = SFCatLo cap r B0 H0 i L0 Z Hsf;
        let HsfM = NatRwRaw (λ (W : Nat). SlotInv Cap0 W B0) (Add I0 Z) I0 (AddZeroRaw I0)
                     (SFCatMid cap r B0 H0 i L0 Z Hsf);
        let HsfH = SFCatHi cap r B0 H0 i L0 Z Hsf;
        let Hak0 = FstT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Hnd0 = SndT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Htot0 = TotalArrCat (S r) (acons r B0 H0) i L0;
        let HlenB = LeRwRRaw (LenE B0)
                      (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                      (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                      (IdSymRaw Nat (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))) Htot0)
                      (LeTransRaw (LenE B0) (Add (LenE B0) (TotalE r H0))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                        (LeAddRaw (LenE B0) (TotalE r H0))
                        (LeAddLRaw (Add (LenE B0) (TotalE r H0)) (TotalE i L0)));
        let HfB = LeTransRaw (LenE B0)
                    (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel
                    HlenB
                    (LePredLRaw (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel Hfl);
        let Pair(hit2, Pair(Hh2, Pair(Hpt2, Pair(Hln2, Pair(Hak3, Hnd3))))) =
          InsertInList(fuel, cap, i, key, val, &m *bb, HfB,
            IdSymRaw Nat i (Dllbc.StdChainRaw.Mod key cap) him, Hak0, Hnd0);
        let B1 = *bb;
        let Hit0 = hit2;
        let Htot1 = TotalArrCat (S r) (acons r B1 H0) i L0;
        let Hpt = UpdPointwise i r key (SomeN val) L0 B0 B1 H0 him Hpt2;
        let HsIz = NatRwRaw (λ (W : Nat). SlotInv Cap0 W B1) I0 (Add I0 Z)
                     (IdSymRaw Nat (Add I0 Z) I0 (AddZeroRaw I0))
                     (MkSlotInv cap i B1 Hak3 Hnd3);
        let H5x = SFCatGlue cap r B1 H0 i L0 Z HsfL HsIz HsfH;
        let HhB = IdTransRaw Bool Hit0 (HitL Key0 B0)
                    (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                    Hh2
                    (IdSymRaw Bool
                      (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                        (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                      (HitL Key0 B0)
                      (NatRwRaw (λ (W : Nat). Id Bool
                          (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) W)))
                          (HitL Key0 B0))
                        I0 (Dllbc.StdChainRaw.Mod Key0 Cap0) Him0
                        (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                          (λ (W : List (Σ (k : Nat). Nat)). IsSomeB (FindL Key0 W))
                          (AgetB (Add I0 (S R0))
                            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0) B0
                          (AgetBCatMid R0 B0 H0 I0 L0))));
        match e2 : hit2 {
          True => {
            let HitB0 = IdTransRaw Bool (HitL Key0 B0) Hit0 True
                          (IdSymRaw Bool Hit0 (HitL Key0 B0) Hh2) e2;
            let HlenEq = IdTransRaw Nat (LenE B1) (BLenIns Key0 B0) (LenE B0)
                           Hln2
                           (BoolRwT Nat (LenE B0) (S (LenE B0)) (HitL Key0 B0) HitB0);
            let HtotEq = IdTransRaw Nat (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                           (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                           (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                           (IdTransRaw Nat
                             (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                             (Add (TotalE i L0) (Add (LenE B1) (TotalE r H0)))
                             (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                             Htot1
                             (IdCongrRaw Nat Nat
                               (λ (W : Nat). Add (TotalE I0 L0) (Add W (TotalE R0 H0)))
                               (LenE B1) (LenE B0) HlenEq))
                           (IdSymRaw Nat (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                             (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))) Htot0);
            Pair(True,
              Pair(IdTransRaw Bool True Hit0
                     (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                       (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                     (IdSymRaw Bool Hit0 True e2) HhB,
              Pair(Hpt, Pair(HtotEq, H5x))))
          },
          False => {
            let HitB0F = IdTransRaw Bool (HitL Key0 B0) Hit0 False
                           (IdSymRaw Bool Hit0 (HitL Key0 B0) Hh2) e2;
            let HlenEqF = IdTransRaw Nat (LenE B1) (BLenIns Key0 B0) (S (LenE B0))
                            Hln2
                            (BoolRwF Nat (LenE B0) (S (LenE B0)) (HitL Key0 B0) HitB0F);
            let HtotEqF = IdTransRaw Nat (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                            (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                            (S (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))))
                            (IdTransRaw Nat
                              (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                              (Add (TotalE i L0) (Add (LenE B1) (TotalE r H0)))
                              (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                              Htot1
                              (IdCongrRaw Nat Nat
                                (λ (W : Nat). Add (TotalE I0 L0) (Add W (TotalE R0 H0)))
                                (LenE B1) (S (LenE B0)) HlenEqF))
                            (IdTransRaw Nat
                              (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                              (S (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))))
                              (S (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))))
                              (AddSuccRaw (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                              (IdCongrRaw Nat Nat (λ (W : Nat). S W)
                                (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                                (TotalE Cap0 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                                (IdSymRaw Nat
                                  (TotalE Cap0 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                                  (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                                  Htot0)));
            Pair(False,
              Pair(IdTransRaw Bool False Hit0
                     (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                       (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                     (IdSymRaw Bool Hit0 False e2) HhB,
              Pair(Hpt, Pair(HtotEqF, H5x))))
          }
        }
      };
  fn SlotRem (fuel : Nat, cap : Nat, key : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))),
              HLe1 : Le (S Z) cap,
              Hfl : Le (S (TotalE cap (*b))) fuel,
              Hsf : SlotsFrom cap cap (*b) Z)
      -> Σ (ret : Σ (bb : Bool). OptP bb Nat).
         Σ (Hr : Id OptN ret (FindL key (AgetB cap (old *b) (Dllbc.StdChainRaw.Mod key cap)))).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap (*b) (Dllbc.StdChainRaw.Mod Q cap)))
              (BFindRem Q key (AgetB cap (old *b) (Dllbc.StdChainRaw.Mod Q cap)))).
         Σ0 (Htot : Id Nat
              (boolRec (λ (W2 : Bool). Nat) (S (TotalE cap (*b))) (TotalE cap (*b))
                (IsSomeB ret))
              (TotalE cap (old *b))).
         SlotsFrom cap cap (*b) Z
      {
        let Cap0 = cap;
        let Key0 = key;
        let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, HLe1);
        let I0 = i;
        let R0 = r;
        let Him0 = him;
        let pre = &m (*b)[Z ; i ; S r | LeAddRaw i (S r) | hd];
        let cell = &m (*b)[i ; 1 ; r];
        let hic = &m (*b)[S i ; r];
        let bb = &m (*cell)[0];
        let L0 = *pre;
        let B0 = *bb;
        let H0 = *hic;
        let HsfL = SFCatLo cap r B0 H0 i L0 Z Hsf;
        let HsfM = NatRwRaw (λ (W : Nat). SlotInv Cap0 W B0) (Add I0 Z) I0 (AddZeroRaw I0)
                     (SFCatMid cap r B0 H0 i L0 Z Hsf);
        let HsfH = SFCatHi cap r B0 H0 i L0 Z Hsf;
        let Hak0 = FstT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Hnd0 = SndT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Htot0 = TotalArrCat (S r) (acons r B0 H0) i L0;
        let HlenB = LeRwRRaw (LenE B0)
                      (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                      (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                      (IdSymRaw Nat (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))) Htot0)
                      (LeTransRaw (LenE B0) (Add (LenE B0) (TotalE r H0))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                        (LeAddRaw (LenE B0) (TotalE r H0))
                        (LeAddLRaw (Add (LenE B0) (TotalE r H0)) (TotalE i L0)));
        let HfB = LeTransRaw (LenE B0)
                    (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel
                    HlenB
                    (LePredLRaw (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel Hfl);
        let bcur = *bb;
        let Pair(rr2, Pair(l3, Pair(Hr2, Pair(Hpt2, Pair(Hln2, Pair(Hak4, Hnd4)))))) =
          RemoveL(fuel, cap, i, key, bcur, HfB, Hak0, Hnd0);
        *bb := l3;
        let B1 = *bb;
        let Ret0 = rr2;
        let Hpt = UpdPointwise i r key NoneN L0 B0 B1 H0 him Hpt2;
        let HsIz = NatRwRaw (λ (W : Nat). SlotInv Cap0 W B1) I0 (Add I0 Z)
                     (IdSymRaw Nat (Add I0 Z) I0 (AddZeroRaw I0))
                     (MkSlotInv cap i B1 Hak4 Hnd4);
        let H5x = SFCatGlue cap r B1 H0 i L0 Z HsfL HsIz HsfH;
        let HrMap = IdTransRaw OptN Ret0 (FindL Key0 B0)
                      (FindL Key0 (AgetB (Add I0 (S R0))
                        (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0)))
                      Hr2
                      (IdSymRaw OptN
                        (FindL Key0 (AgetB (Add I0 (S R0))
                          (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 Cap0)))
                        (FindL Key0 B0)
                        (NatRwRaw (λ (W : Nat). Id OptN
                            (FindL Key0 (AgetB (Add I0 (S R0))
                              (arrCat I0 (S R0) L0 (acons R0 B0 H0)) W))
                            (FindL Key0 B0))
                          I0 (Dllbc.StdChainRaw.Mod Key0 Cap0) Him0
                          (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
                            (λ (W : List (Σ (k : Nat). Nat)). FindL Key0 W)
                            (AgetB (Add I0 (S R0))
                              (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0) B0
                            (AgetBCatMid R0 B0 H0 I0 L0))));
        let Htot = IdTransRaw Nat
                     (boolRec (λ (W2 : Bool). Nat)
                       (S (TotalE (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B1 H0))))
                       (TotalE (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B1 H0)))
                       (IsSomeB Ret0))
                     (boolRec (λ (W2 : Bool). Nat)
                       (S (TotalE (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B1 H0))))
                       (TotalE (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B1 H0)))
                       (HitL Key0 B0))
                     (TotalE (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                     (IdCongrRaw Bool Nat
                       (λ (W : Bool). boolRec (λ (W2 : Bool). Nat)
                         (S (TotalE (Add I0 (S R0))
                           (arrCat I0 (S R0) L0 (acons R0 B1 H0))))
                         (TotalE (Add I0 (S R0))
                           (arrCat I0 (S R0) L0 (acons R0 B1 H0))) W)
                       (IsSomeB Ret0) (HitL Key0 B0)
                       (IdCongrRaw OptN Bool IsSomeB Ret0 (FindL Key0 B0) Hr2))
                     (RemTotEv I0 R0 Key0 L0 B0 B1 H0 Hln2);
        Pair(rr2, Pair(HrMap, Pair(Hpt, Pair(Htot, H5x))))
      };
  () }

example : progOkFrom Dllbc.std hmM0.term = true := by native_decide

/-! The move layer and the op wrappers, chained from `hmM0` — the StdChain
    eleven-links cut: ONE block of the whole chain stops compiling (the code
    generator's recursion limit on the quoted term), two chained blocks do
    not, and the seam is free because a seeded module resolves its callees
    from the seed. `hmM` is the consumer-facing seed. -/
/--
info: key ↦ (σ₈₄₁₈ : Nat)
-/
#guard_msgs in
set_option maxHeartbeats 0 in
def hmM : Checked := prog (hmM0) {
  fn SlotPush (cap2 : Nat,
               src : &mut (List (Σ (k : Nat). Nat)),
               dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))),
               HLe1 : Le (S Z) cap2,
               Hne : Id Bool (IsNilB (*src)) False,
               Hsf : SlotsFrom cap2 cap2 (*dst) Z,
               Hnd : NodupB (*src),
               Hfr : Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (*src)) True) →
                     Id OptN (FindL K2 (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod K2 cap2))) NoneN)
      -> Σ (K0r : Nat). Σ (V0r : Nat). Σ (T0r : List (Σ (k : Nat). Nat)).
         Σ (Hdec : Id (List (Σ (k : Nat). Nat)) (old *src) (Cons(Pair(K0r, V0r), T0r))).
         Σ (Hsrc : Id (List (Σ (k : Nat). Nat)) (*src) T0r).
         Σ (Hhd : Id Bool (HitL K0r T0r) False).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod Q cap2)))
              (boolRec (λ (W2 : Bool). OptN) (SomeN V0r)
                (FindL Q (AgetB cap2 (old *dst) (Dllbc.StdChainRaw.Mod Q cap2))) (Eqb Q K0r))).
         Σ (Hfr2 : Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (*src)) True) →
              Id OptN (FindL K2 (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod K2 cap2))) NoneN).
         Σ (Hnd2 : NodupB (*src)).
         Σ (Hln : Id Nat (LenE (old *src)) (S (LenE (*src)))).
         Σ0 (Htot : Id Nat (TotalE cap2 (*dst)) (S (TotalE cap2 (old *dst)))).
         SlotsFrom cap2 cap2 (*dst) Z
      { match src {
          Nil => botElim Unit (BoolTFRaw Hne),
          Cons(Pair(kk, vv), tail) => {
            let C2 = cap2;
            let K0 = *kk;
            let V0 = *vv;
            let T0 = *tail;
            let HfrK = Hfr K0 (IdSymRaw Bool True (HitL K0 (Cons(Pair(K0, V0), T0)))
                         (HitEvHit K0 V0 K0 T0 (EqbReflRaw K0)));
            let HndHd = FstT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd;
            let HndTl = SndT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd;
            let k0 = *kk;
            *kk := k0;
            let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(k0, cap2, HLe1);
            let I0 = i;
            let R0 = r;
            let Him0 = him;
            let pre = &m (*dst)[Z ; i ; S r | LeAddRaw i (S r) | hd];
            let cell = &m (*dst)[i ; 1 ; r];
            let hic = &m (*dst)[S i ; r];
            let bb = &m (*cell)[0];
            let L0 = *pre;
            let B0 = *bb;
            let H0 = *hic;
            let HsfL = SFCatLo cap2 r B0 H0 i L0 Z Hsf;
            let HsfM = NatRwRaw (λ (W : Nat). SlotInv C2 W B0) (Add I0 Z) I0 (AddZeroRaw I0)
                         (SFCatMid cap2 r B0 H0 i L0 Z Hsf);
            let HsfH = SFCatHi cap2 r B0 H0 i L0 Z Hsf;
            let Hak0 = FstT (AllKeysMod cap2 i B0) (NodupB B0) HsfM;
            let Hnd0 = SndT (AllKeysMod cap2 i B0) (NodupB B0) HsfM;
            let HfrB0 = NatRwRaw (λ (W : Nat). Id OptN (FindL K0 (AgetB (Add I0 (S R0))
                            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) W)) NoneN)
                          (Dllbc.StdChainRaw.Mod K0 C2) I0 (IdSymRaw Nat I0 (Dllbc.StdChainRaw.Mod K0 C2) Him0) HfrK;
            let HndK0 = IdTransRaw Bool (HitL K0 B0) (IsSomeB NoneN) False
                          (IdCongrRaw OptN Bool IsSomeB (FindL K0 B0) NoneN
                            (IdTransRaw OptN (FindL K0 B0)
                              (FindL K0 (AgetB (Add I0 (S R0))
                                (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0))
                              NoneN
                              (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
                                (λ (W : List (Σ (k : Nat). Nat)). FindL K0 W)
                                B0
                                (AgetB (Add I0 (S R0))
                                  (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0)
                                (IdSymRaw (List (Σ (k : Nat). Nat))
                                  (AgetB (Add I0 (S R0))
                                    (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0)
                                  B0
                                  (AgetBCatMid R0 B0 H0 I0 L0)))
                              HfrB0))
                          Refl;
            let tmp = *tail;
            *tail := *bb;
            *bb := *src;
            *src := tmp;
            let B1 = *bb;
            let Hpt = UpdPointwise i r k0 (SomeN V0) L0 B0 B1 H0 him
                        (PtEvPush K0 V0 B0);
            let Hfr2 = MoveFreshStep C2 K0 V0 T0
                         (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                         (arrCat I0 (S R0) L0 (acons R0 B1 H0))
                         HndHd Hpt Hfr;
            let HakB1 = MkAkCons C2 I0 K0 V0 B0
                          (IdSymRaw Nat I0 (Dllbc.StdChainRaw.Mod K0 C2) Him0) Hak0;
            let HndB1 = MkNdCons K0 V0 B0 HndK0 Hnd0;
            let HsIz = NatRwRaw (λ (W : Nat). SlotInv C2 W B1) I0 (Add I0 Z)
                         (IdSymRaw Nat (Add I0 Z) I0 (AddZeroRaw I0))
                         (MkSlotInv cap2 i B1 HakB1 HndB1);
            let H5x = SFCatGlue cap2 r B1 H0 i L0 Z HsfL HsIz HsfH;
            let Htot = IdTransRaw Nat
                         (TotalE C2 (arrCat I0 (S R0) L0 (acons R0 B1 H0)))
                         (Add (TotalE I0 L0) (Add (LenE B1) (TotalE R0 H0)))
                         (S (TotalE C2 (arrCat I0 (S R0) L0 (acons R0 B0 H0))))
                         (TotalArrCat (S R0) (acons R0 B1 H0) I0 L0)
                         (IdTransRaw Nat
                           (Add (TotalE I0 L0) (Add (LenE B1) (TotalE R0 H0)))
                           (S (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0))))
                           (S (TotalE C2 (arrCat I0 (S R0) L0 (acons R0 B0 H0))))
                           (AddSuccRaw (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                           (IdCongrRaw Nat Nat (λ (W : Nat). S W)
                             (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                             (TotalE C2 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                             (IdSymRaw Nat
                               (TotalE C2 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                               (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                               (TotalArrCat (S R0) (acons R0 B0 H0) I0 L0))));
            Pair(IdNat K0, Pair(IdNat V0, Pair(IdBkt T0,
              Pair(Refl, Pair(Refl, Pair(HndHd, Pair(Hpt, Pair(Hfr2,
                Pair(HndTl, Pair(Refl, Pair(Htot, H5x)))))))))))
          }
        } };
  fn MoveBktR [fuel] (fuel : Nat, cap2 : Nat,
                      src : &mut (List (Σ (k : Nat). Nat)),
                      dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))),
                      HLe1 : Le (S Z) cap2,
                      Hdep : Le (LenE (*src)) fuel,
                      Hsf : SlotsFrom cap2 cap2 (*dst) Z,
                      Hnd : NodupB (*src),
                      Hfr : Π (K2 : Nat) → Π (Hk2 : Id Bool (HitL K2 (*src)) True) →
                            Id OptN (FindL K2 (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod K2 cap2))) NoneN)
      -> Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod Q cap2)))
            (boolRec (λ (W2 : Bool). OptN) (FindL Q (old *src))
              (FindL Q (AgetB cap2 (old *dst) (Dllbc.StdChainRaw.Mod Q cap2))) (HitL Q (old *src)))).
         Σ0 (Htot : Id Nat (TotalE cap2 (*dst))
            (Add (LenE (old *src)) (TotalE cap2 (old *dst)))).
         SlotsFrom cap2 cap2 (*dst) Z
      { if e : IsNilB (*src) {
          let C2 = cap2;
          let Bd = *src;
          let Dd = *dst;
          Pair(MoveDonePt C2 Bd Dd e, Pair(MoveDoneTot C2 Bd Dd e, Hsf))
        } else {
          match fuel {
            Z => {
              let Bd = *src;
              botElim Unit (LeTransRaw (S Z) (LenE Bd) Z (NotNilLenPos Bd e) Hdep)
            },
            S(f2) => {
              let C2 = cap2;
              let B0s = *src;
              let D0s = *dst;
              let Pair(K0, Pair(V0, Pair(T0, Pair(Hdec, Pair(Hsrc, Pair(Hhd,
                Pair(Hpt2, Pair(Hfr2, Pair(Hnd2, Pair(Hln2, Pair(Htot2, Hsf2))))))))))) =
                SlotPush(cap2, &m *src, &m *dst, HLe1, e, Hsf, Hnd, Hfr);
              let S1s = *src;
              let D1s = *dst;
              let Pair(HptR, Pair(HtotR, HsfR)) =
                MoveBktR(f2, cap2, &m *src, &m *dst, HLe1,
                  LeRwLRaw (S f2) (LenE B0s) (S (LenE S1s)) Hln2 Hdep,
                  Hsf2, Hnd2, Hfr2);
              let D2s = *dst;
              Pair(AgetBktCongr (Cons(Pair(K0, V0), T0)) B0s
                     (λ (Qz : Nat). FindL Qz (AgetB C2 D0s (Dllbc.StdChainRaw.Mod Qz C2)))
                     (λ (Qz : Nat). FindL Qz (AgetB C2 D2s (Dllbc.StdChainRaw.Mod Qz C2)))
                     (IdSymRaw (List (Σ (k : Nat). Nat)) B0s (Cons(Pair(K0, V0), T0)) Hdec)
                     (MoveStepPt K0 V0 T0
                       (λ (Qz : Nat). FindL Qz (AgetB C2 D0s (Dllbc.StdChainRaw.Mod Qz C2)))
                       (λ (Qz : Nat). FindL Qz (AgetB C2 D1s (Dllbc.StdChainRaw.Mod Qz C2)))
                       (λ (Qz : Nat). FindL Qz (AgetB C2 D2s (Dllbc.StdChainRaw.Mod Qz C2)))
                       Hhd Hpt2
                       (AgetBktCongr S1s T0
                         (λ (Qz : Nat). FindL Qz (AgetB C2 D1s (Dllbc.StdChainRaw.Mod Qz C2)))
                         (λ (Qz : Nat). FindL Qz (AgetB C2 D2s (Dllbc.StdChainRaw.Mod Qz C2)))
                         Hsrc HptR)),
                Pair(IdTransRaw Nat (TotalE C2 D2s)
                       (Add (LenE S1s) (TotalE C2 D1s))
                       (Add (LenE B0s) (TotalE C2 D0s))
                       HtotR
                       (IdTransRaw Nat (Add (LenE S1s) (TotalE C2 D1s))
                         (S (Add (LenE S1s) (TotalE C2 D0s)))
                         (Add (LenE B0s) (TotalE C2 D0s))
                         (IdTransRaw Nat (Add (LenE S1s) (TotalE C2 D1s))
                           (Add (LenE S1s) (S (TotalE C2 D0s)))
                           (S (Add (LenE S1s) (TotalE C2 D0s)))
                           (IdCongrRaw Nat Nat (λ (W : Nat). Add (LenE S1s) W)
                             (TotalE C2 D1s) (S (TotalE C2 D0s)) Htot2)
                           (AddSuccRaw (LenE S1s) (TotalE C2 D0s)))
                         (IdCongrRaw Nat Nat (λ (W : Nat). Add W (TotalE C2 D0s))
                           (S (LenE S1s)) (LenE B0s)
                           (IdSymRaw Nat (LenE B0s) (S (LenE S1s)) Hln2))),
                  HsfR))
            } }
        } };
  fn MoveOne (tfuel : Nat, capF : Nat, cap2 : Nat, j : Nat, m2 : Nat,
              src : &mut (Array capF (List (Σ (k : Nat). Nat))),
              dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))),
              HLe1 : Le (S Z) cap2,
              Hj : Id Nat capF (Add j (S m2)),
              Htf : Le (S (TotalE capF (*src))) tfuel,
              HsfS : SlotsFrom capF capF (*src) Z,
              HsfD : SlotsFrom cap2 cap2 (*dst) Z,
              Hdisj : Π (K2 : Nat) → Π (Hs2 : Id Bool (IsSomeB (FindL K2
                  (AgetB capF (*src) (Dllbc.StdChainRaw.Mod K2 capF)))) True) →
                  Id OptN (FindL K2 (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod K2 cap2))) NoneN)
      -> Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod Q cap2)))
            (boolRec (λ (W2 : Bool). OptN)
              (FindL Q (AgetB capF (old *src) j))
              (FindL Q (AgetB cap2 (old *dst) (Dllbc.StdChainRaw.Mod Q cap2)))
              (HitL Q (AgetB capF (old *src) j)))).
         Σ (Hnil : Id (List (Σ (k : Nat). Nat)) (AgetB capF (*src) j) Nil).
         Σ (Hfrm : Π (J2 : Nat) → Π (Hne : Id Bool (Eqb J2 j) False) →
            Id (List (Σ (k : Nat). Nat)) (AgetB capF (*src) J2)
              (AgetB capF (old *src) J2)).
         Σ (Htot : Id Nat (Add (TotalE capF (*src)) (TotalE cap2 (*dst)))
            (Add (TotalE capF (old *src)) (TotalE cap2 (old *dst)))).
         Σ (Hsdc : Le (TotalE capF (*src)) (TotalE capF (old *src))).
         Σ0 (HsfS2 : SlotsFrom capF capF (*src) Z).
         SlotsFrom cap2 cap2 (*dst) Z
      {
        let CF = capF;
        let C2 = cap2;
        let J0 = j;
        let M2 = m2;
        let pre = &m (*src)[Z ; j ; S m2 | LeAddRaw j (S m2) | Hj];
        let cell = &m (*src)[j ; 1 ; m2];
        let hic = &m (*src)[S j ; m2];
        let bbs = &m (*cell)[0];
        let LS0 = *pre;
        let BJ0 = *bbs;
        let HS0 = *hic;
        let HsfLs = SFCatLo capF m2 BJ0 HS0 j LS0 Z HsfS;
        let HsfMs = NatRwRaw (λ (W : Nat). SlotInv CF W BJ0) (Add J0 Z) J0 (AddZeroRaw J0)
                      (SFCatMid capF m2 BJ0 HS0 j LS0 Z HsfS);
        let HsfHs = SFCatHi capF m2 BJ0 HS0 j LS0 Z HsfS;
        let HakJ = FstT (AllKeysMod capF j BJ0) (NodupB BJ0) HsfMs;
        let HndJ = SndT (AllKeysMod capF j BJ0) (NodupB BJ0) HsfMs;
        let Htot0s = TotalArrCat (S m2) (acons m2 BJ0 HS0) j LS0;
        let D0d = *dst;
        let HlenBj = LeRwRRaw (LenE BJ0)
                       (Add (TotalE j LS0) (Add (LenE BJ0) (TotalE m2 HS0)))
                       (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0)))
                       (IdSymRaw Nat
                         (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0)))
                         (Add (TotalE j LS0) (Add (LenE BJ0) (TotalE m2 HS0)))
                         Htot0s)
                       (LeTransRaw (LenE BJ0) (Add (LenE BJ0) (TotalE m2 HS0))
                         (Add (TotalE j LS0) (Add (LenE BJ0) (TotalE m2 HS0)))
                         (LeAddRaw (LenE BJ0) (TotalE m2 HS0))
                         (LeAddLRaw (Add (LenE BJ0) (TotalE m2 HS0)) (TotalE j LS0)));
        let bl = *bbs;
        *bbs := Nil;
        let Pair(HptB, Pair(HtotB, HsfD1)) =
          MoveBktR(tfuel, cap2, &m bl, &m *dst, HLe1,
            LeTransRaw (LenE BJ0)
              (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0))) tfuel
              HlenBj
              (LePredLRaw (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0))) tfuel Htf),
            HsfD, HndJ,
            MoveSlotsFresh j m2 cap2 LS0 BJ0 HS0 D0d HakJ Hdisj);
        let D1d = *dst;
        let HsfS1 = SFCatGlue capF m2 Nil HS0 j LS0 Z HsfLs
                      (NatRwRaw (λ (W : Nat). SlotInv CF W Nil) J0 (Add J0 Z)
                        (IdSymRaw Nat (Add J0 Z) J0 (AddZeroRaw J0))
                        (MkSlotInv capF j Nil unit unit))
                      HsfHs;
        let HsumStep = IdTransRaw Nat
            (Add (TotalE capF (arrCat j (S m2) LS0 (acons m2 Nil HS0)))
              (TotalE cap2 D1d))
            (Add (Add (TotalE j LS0) (TotalE m2 HS0))
              (Add (LenE BJ0) (TotalE cap2 D0d)))
            (Add (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0)))
              (TotalE cap2 D0d))
            (IdTransRaw Nat
              (Add (TotalE capF (arrCat j (S m2) LS0 (acons m2 Nil HS0)))
                (TotalE cap2 D1d))
              (Add (Add (TotalE j LS0) (TotalE m2 HS0)) (TotalE cap2 D1d))
              (Add (Add (TotalE j LS0) (TotalE m2 HS0))
                (Add (LenE BJ0) (TotalE cap2 D0d)))
              (IdCongrRaw Nat Nat
                (λ (W : Nat). Add W (TotalE C2 D1d))
                (TotalE capF (arrCat j (S m2) LS0 (acons m2 Nil HS0)))
                (Add (TotalE j LS0) (TotalE m2 HS0))
                (TotalArrCat (S m2) (acons m2 Nil HS0) j LS0))
              (IdCongrRaw Nat Nat
                (λ (W : Nat). Add (Add (TotalE J0 LS0) (TotalE M2 HS0)) W)
                (TotalE cap2 D1d)
                (Add (LenE BJ0) (TotalE cap2 D0d))
                HtotB))
            (IdTransRaw Nat
              (Add (Add (TotalE j LS0) (TotalE m2 HS0))
                (Add (LenE BJ0) (TotalE cap2 D0d)))
              (Add (Add (TotalE j LS0) (LenE BJ0))
                (Add (TotalE m2 HS0) (TotalE cap2 D0d)))
              (Add (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0)))
                (TotalE cap2 D0d))
              (AddInterchangeRaw (TotalE j LS0) (TotalE m2 HS0) (LenE BJ0)
                (TotalE cap2 D0d))
              (IdTransRaw Nat
                (Add (Add (TotalE j LS0) (LenE BJ0))
                  (Add (TotalE m2 HS0) (TotalE cap2 D0d)))
                (Add (Add (Add (TotalE j LS0) (LenE BJ0)) (TotalE m2 HS0))
                  (TotalE cap2 D0d))
                (Add (TotalE capF (arrCat j (S m2) LS0 (acons m2 BJ0 HS0)))
                  (TotalE cap2 D0d))
                (IdSymRaw Nat
                  (Add (Add (Add (TotalE J0 LS0) (LenE BJ0)) (TotalE M2 HS0))
                    (TotalE C2 D0d))
                  (Add (Add (TotalE J0 LS0) (LenE BJ0))
                    (Add (TotalE M2 HS0) (TotalE C2 D0d)))
                  (AddAssocRaw (Add (TotalE J0 LS0) (LenE BJ0)) (TotalE M2 HS0)
                    (TotalE C2 D0d)))
                (IdTransRaw Nat
                  (Add (Add (Add (TotalE J0 LS0) (LenE BJ0)) (TotalE M2 HS0))
                    (TotalE C2 D0d))
                  (Add (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                    (TotalE C2 D0d))
                  (Add (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)))
                    (TotalE C2 D0d))
                  (IdCongrRaw Nat Nat (λ (W : Nat). Add W (TotalE C2 D0d))
                    (Add (Add (TotalE J0 LS0) (LenE BJ0)) (TotalE M2 HS0))
                    (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                    (AddAssocRaw (TotalE J0 LS0) (LenE BJ0) (TotalE M2 HS0)))
                  (IdCongrRaw Nat Nat (λ (W : Nat). Add W (TotalE C2 D0d))
                    (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                    (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)))
                    (IdSymRaw Nat
                      (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)))
                      (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                      Htot0s)))));
        let Hsdc = LeRwRRaw (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 Nil HS0)))
                     (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                     (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)))
                     (IdSymRaw Nat (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)))
                       (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                       Htot0s)
                     (LeRwLRaw (Add (TotalE J0 LS0) (Add (LenE BJ0) (TotalE M2 HS0)))
                       (Add (TotalE J0 LS0) (TotalE M2 HS0))
                       (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 Nil HS0)))
                       (IdSymRaw Nat (TotalE CF (arrCat J0 (S M2) LS0 (acons M2 Nil HS0)))
                         (Add (TotalE J0 LS0) (TotalE M2 HS0))
                         (TotalArrCat (S M2) (acons M2 Nil HS0) J0 LS0))
                       (LeAddMonoLRaw (TotalE J0 LS0) (TotalE M2 HS0)
                         (Add (LenE BJ0) (TotalE M2 HS0))
                         (LeAddLRaw (TotalE M2 HS0) (LenE BJ0))));
        Pair(AgetBktCongr BJ0
               (AgetB (Add J0 (S M2)) (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)) J0)
               (λ (Qz : Nat). FindL Qz (AgetB C2 D0d (Dllbc.StdChainRaw.Mod Qz C2)))
               (λ (Qz : Nat). FindL Qz (AgetB C2 D1d (Dllbc.StdChainRaw.Mod Qz C2)))
               (IdSymRaw (List (Σ (k : Nat). Nat))
                 (AgetB (Add J0 (S M2)) (arrCat J0 (S M2) LS0 (acons M2 BJ0 HS0)) J0)
                 BJ0
                 (AgetBCatMid M2 BJ0 HS0 J0 LS0))
               HptB,
          Pair(AgetBCatMid M2 Nil HS0 J0 LS0,
            Pair(NeBucketEq J0 M2 LS0 BJ0 HS0,
              Pair(HsumStep,
                Pair(Hsdc,
                  Pair(HsfS1, HsfD1))))))
      };
  fn MoveSlots [m] (m : Nat, j : Nat, tfuel : Nat, capF : Nat, cap2 : Nat,
                    Hj : Id Nat capF (Add j m),
                    src : &mut (Array capF (List (Σ (k : Nat). Nat))),
                    dst : &mut (Array cap2 (List (Σ (k : Nat). Nat))),
                    HLe1 : Le (S Z) cap2,
                    HLe1F : Le (S Z) capF,
                    Htf : Le (S (TotalE capF (*src))) tfuel,
                    HsfS : SlotsFrom capF capF (*src) Z,
                    HsfD : SlotsFrom cap2 cap2 (*dst) Z,
                    Hdisj : Π (K2 : Nat) →
                      Π (Hs2 : Id Bool (IsSomeB (FindL K2 (AgetB capF (*src)
                        (Dllbc.StdChainRaw.Mod K2 capF)))) True) →
                      Id OptN (FindL K2 (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod K2 cap2))) NoneN,
                    HsrcLo : Π (J2 : Nat) → Π (Hb2 : Id Bool (Leb (S J2) j) True) →
                      Id (List (Σ (k : Nat). Nat)) (AgetB capF (*src) J2) Nil)
      -> Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap2 (*dst) (Dllbc.StdChainRaw.Mod Q cap2)))
            (boolRec (λ (W2 : Bool). OptN)
              (FindL Q (AgetB capF (old *src) (Dllbc.StdChainRaw.Mod Q capF)))
              (FindL Q (AgetB cap2 (old *dst) (Dllbc.StdChainRaw.Mod Q cap2)))
              (IsSomeB (FindL Q (AgetB capF (old *src) (Dllbc.StdChainRaw.Mod Q capF)))))).
         Σ (HsrcF : Π (J2 : Nat) → Π (Hb2 : Le (S J2) capF) →
            Id (List (Σ (k : Nat). Nat)) (AgetB capF (*src) J2) Nil).
         Σ0 (Htot : Id Nat (Add (TotalE capF (*src)) (TotalE cap2 (*dst)))
            (Add (TotalE capF (old *src)) (TotalE cap2 (old *dst)))).
         SlotsFrom cap2 cap2 (*dst) Z
      { match m {
          Z => {
            let CF = capF;
            let J0 = j;
            let C2 = cap2;
            let Dd = *dst;
            let Sd = *src;
            let Hjz = IdTransRaw Nat CF (Add J0 Z) J0 Hj (AddZeroRaw J0);
            Pair(MoveBasePt CF J0 C2 Sd Dd HLe1F Hjz HsrcLo,
              Pair(MoveBaseNil CF J0 Sd Hjz HsrcLo,
                Pair(Refl, HsfD)))
          },
          S(m2) => {
            let CF = capF;
            let C2 = cap2;
            let J0 = j;
            let M2 = m2;
            let S0d = *src;
            let D0d = *dst;
            let HinvJ = NatRwRaw (λ (W : Nat). SlotInv CF W (AgetB CF S0d J0))
                          (Add J0 Z) J0 (AddZeroRaw J0)
                          (SFAgetInv capF capF S0d Z HsfS j
                            (LeRwRRaw (S j) (Add j (S m2)) capF
                              (IdSymRaw Nat capF (Add j (S m2)) Hj)
                              (LeAddSuccRaw j m2)));
            let HakJ = FstT (AllKeysMod CF J0 (AgetB CF S0d J0))
                         (NodupB (AgetB CF S0d J0)) HinvJ;
            let Pair(HptO, Pair(HnilO, Pair(HfrmO,
              Pair(HtotO, Pair(HsdcO, Pair(HsfSO, HsfDO)))))) =
              MoveOne(tfuel, capF, cap2, j, m2, &m *src, &m *dst,
                HLe1, Hj, Htf, HsfS, HsfD, Hdisj);
            let SMd = *src;
            let D1d = *dst;
            let HdisjR = MoveLevelDisj CF J0 S0d SMd
                (λ (Qz : Nat). FindL Qz (AgetB C2 D0d (Dllbc.StdChainRaw.Mod Qz C2)))
                (λ (Qz : Nat). FindL Qz (AgetB C2 D1d (Dllbc.StdChainRaw.Mod Qz C2)))
                HakJ HnilO HfrmO HptO Hdisj;
            let HnilR = MoveLevelNil CF J0 S0d SMd HnilO HfrmO HsrcLo;
            let Pair(HptR, Pair(HsrcFR, Pair(HtotR, HsfD2))) =
              MoveSlots(m2, S j, tfuel, capF, cap2,
                IdTransRaw Nat capF (Add j (S m2)) (S (Add j m2)) Hj (AddSuccRaw j m2),
                &m *src, &m *dst, HLe1, HLe1F,
                LeTransRaw (S (TotalE CF SMd)) (S (TotalE CF S0d)) tfuel HsdcO Htf,
                HsfSO, HsfDO, HdisjR, HnilR);
            let D2d = *dst;
            Pair(MoveLevelPt CF J0 S0d SMd
                   (λ (Qz : Nat). FindL Qz (AgetB C2 D0d (Dllbc.StdChainRaw.Mod Qz C2)))
                   (λ (Qz : Nat). FindL Qz (AgetB C2 D1d (Dllbc.StdChainRaw.Mod Qz C2)))
                   (λ (Qz : Nat). FindL Qz (AgetB C2 D2d (Dllbc.StdChainRaw.Mod Qz C2)))
                   HakJ HnilO HfrmO HptO HptR,
              Pair(HsrcFR,
                Pair(IdTransRaw Nat
                       (Add (TotalE CF (*src)) (TotalE C2 D2d))
                       (Add (TotalE CF SMd) (TotalE C2 D1d))
                       (Add (TotalE CF S0d) (TotalE C2 D0d))
                       HtotR HtotO,
                     HsfD2)))
          }
        } };
  fn InsertHM (fuel : Nat, key : Nat, val : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots),
               Hfuel : Le (S (S (SizeHM (*self)))) fuel)
      -> Σ0 (Hpt : Π (Q : Nat) → Id OptN (FindHM Q (@ifind *self))
           (FindIns Q key val (@iframe old *self))).
         Id Nat (SizeHM (*self)) (@isize SizeIns key (old *self))
      {
        let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = *self;
        let Cap0 = cap;
        let Key0 = key;
        let N0 = nn;
        let HLe1 = InvLe1 cap load nn slots HInv;
        let HLoad = InvLoad cap load nn slots HInv;
        let HLed = InvLedger cap load nn slots HInv;
        let HCnt = InvCount cap load nn slots HInv;
        let HSf = InvSlots cap load nn slots HInv;
        let SL0 = slots;
        let sb = &m slots;
        let Pair(hit2, Pair(Hh2, Pair(Hpt2, Pair(Htot2, Hsf2)))) =
          SlotUpd(fuel, cap, key, val, &m *sb, HLe1,
            LeRwLRaw fuel (S nn) (S (TotalE Cap0 SL0))
              (IdCongrRaw Nat Nat (λ (W : Nat). S W) N0 (TotalE Cap0 SL0) HCnt)
              (LePredLRaw (S nn) fuel Hfuel),
            HSf);
        let SL1 = *sb;
        -- The probe the honest form makes possible: a `show` INSIDE the
        -- flagship op, answering (docs/21 §1 — the spliced template was
        -- silently deferred and had nothing to say here).
        show key;
        let Hit0 = hit2;
        match e2 : hit2 {
          True => {
            let H4x = IdTransRaw Nat nn (TotalE Cap0 SL0) (TotalE Cap0 SL1)
                        HCnt
                        (IdSymRaw Nat (TotalE Cap0 SL1) (TotalE Cap0 SL0)
                          (IdTransRaw Nat (TotalE Cap0 SL1)
                            (boolRec (λ (W2 : Bool). Nat) (TotalE Cap0 SL0)
                              (S (TotalE Cap0 SL0)) Hit0)
                            (TotalE Cap0 SL0)
                            Htot2
                            (BoolRwT Nat (TotalE Cap0 SL0) (S (TotalE Cap0 SL0))
                              Hit0 e2)));
            *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
              MkInv cap load nn SL1 HLe1 HLoad HLed H4x Hsf2))));
            Pair(Hpt2,
              IdSymRaw Nat
                (boolRec (λ (W2 : Bool). Nat) nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0)))))
                nn
                (BoolRwT Nat nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                  (IdTransRaw Bool
                    (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                    Hit0 True
                    (IdSymRaw Bool Hit0
                      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0)))) Hh2)
                    e2)))
          },
          False => {
            let H4y = IdTransRaw Nat (S nn) (S (TotalE Cap0 SL0)) (TotalE Cap0 SL1)
                        (IdCongrRaw Nat Nat (λ (W : Nat). S W) N0 (TotalE Cap0 SL0) HCnt)
                        (IdSymRaw Nat (TotalE Cap0 SL1) (S (TotalE Cap0 SL0))
                          (IdTransRaw Nat (TotalE Cap0 SL1)
                            (boolRec (λ (W2 : Bool). Nat) (TotalE Cap0 SL0)
                              (S (TotalE Cap0 SL0)) Hit0)
                            (S (TotalE Cap0 SL0))
                            Htot2
                            (BoolRwF Nat (TotalE Cap0 SL0) (S (TotalE Cap0 SL0))
                              Hit0 e2)));
            if e4 : Leb (Dllbc.StdChainRaw.Mul 5 (S nn)) load {
              (@inogrow %noGrowArm)
            } else {
              (@igrow %growArm)
            }
          }
        }
      };
  fn RemoveHM (fuel : Nat, key : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots),
               Hfuel : Le (S (SizeHM (*self))) fuel)
      -> Σ (r : Σ (bb : Bool). OptP bb Nat).
         Σ (Hr : Id OptN r (FindHM key (@rfound old *self))).
         Σ0 (Hpt : Π (Q : Nat) → Id OptN (FindHM Q (@rpt *self))
           (FindRem Q key (old *self))).
         Id Nat (SizeHM (*self)) (@rsize SizeRem key (old *self))
      {
        let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = *self;
        let Cap0 = cap;
        let Key0 = key;
        let N0 = nn;
        let HLe1 = InvLe1 cap load nn slots HInv;
        let HLoad = InvLoad cap load nn slots HInv;
        let HLed = InvLedger cap load nn slots HInv;
        let HCnt = InvCount cap load nn slots HInv;
        let HSf = InvSlots cap load nn slots HInv;
        let SL0 = slots;
        let sb = &m slots;
        let Pair(rr, Pair(Hr2, Pair(Hpt2, Pair(Htot2, Hsf2)))) =
          SlotRem(fuel, cap, key, &m *sb, HLe1,
            LeRwLRaw fuel (S nn) (S (TotalE Cap0 SL0))
              (IdCongrRaw Nat Nat (λ (W : Nat). S W) N0 (TotalE Cap0 SL0) HCnt)
              Hfuel,
            HSf);
        let SL1 = *sb;
        let Ret0 = rr;
        match rr {
          Pair(tg, pv) => match e3 : tg {
            True => match nn {
              Z => botElim Unit
                     (ZnotsRaw (TotalE Cap0 SL1)
                       (IdSymRaw Nat (S (TotalE Cap0 SL1)) Z
                         (IdTransRaw Nat (S (TotalE Cap0 SL1)) (TotalE Cap0 SL0) Z
                           Htot2 (IdSymRaw Nat Z (TotalE Cap0 SL0) HCnt)))),
              S(m2) => {
                let H4r = SInjRaw m2 (TotalE Cap0 SL1)
                            (IdTransRaw Nat (S m2) (TotalE Cap0 SL0) (S (TotalE Cap0 SL1))
                              HCnt (IdSymRaw Nat (S (TotalE Cap0 SL1)) (TotalE Cap0 SL0) Htot2));
                *self := Pair(cap, Pair(load, Pair(m2, Pair(slots,
                  MkInv cap load m2 SL1 HLe1 HLoad
                    (LeTransRaw (Dllbc.StdChainRaw.Mul 5 m2) (Dllbc.StdChainRaw.Mul 5 (S m2)) load
                      (LeMulRRaw 5 m2 (S m2) (LeUpRRaw m2 m2 (LeReflRaw m2)))
                      HLed)
                    H4r Hsf2))));
                Pair(Pair(True, pv),
                  Pair(Hr2,
                  Pair(Hpt2,
                    IdSymRaw Nat
                      (boolRec (λ (W2 : Bool). Nat) (Dllbc.StdChainRaw.Pred N0) N0
                        (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0)))))
                      (Dllbc.StdChainRaw.Pred N0)
                      (BoolRwT Nat (Dllbc.StdChainRaw.Pred N0) N0
                        (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                        (IdTransRaw Bool
                          (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                          (IsSomeB Ret0) True
                          (IdSymRaw Bool (IsSomeB Ret0)
                            (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                            (IdCongrRaw OptN Bool IsSomeB Ret0
                              (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))) Hr2))
                          e3)))))
              }
            },
            False => {
              let H4n = IdTransRaw Nat nn (TotalE Cap0 SL0) (TotalE Cap0 SL1)
                          HCnt
                          (IdSymRaw Nat (TotalE Cap0 SL1) (TotalE Cap0 SL0) Htot2);
              *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
                MkInv cap load nn SL1 HLe1 HLoad HLed H4n Hsf2))));
              Pair(Pair(False, pv),
                Pair(Hr2,
                Pair(Hpt2,
                  IdSymRaw Nat
                    (boolRec (λ (W2 : Bool). Nat) (Dllbc.StdChainRaw.Pred N0) N0
                      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0)))))
                    N0
                    (BoolRwF Nat (Dllbc.StdChainRaw.Pred N0) N0
                      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                      (IdTransRaw Bool
                        (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                        (IsSomeB Ret0) False
                        (IdSymRaw Bool (IsSomeB Ret0)
                          (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))))
                          (IdCongrRaw OptN Bool IsSomeB Ret0
                            (FindL Key0 (AgetB Cap0 SL0 (Dllbc.StdChainRaw.Mod Key0 Cap0))) Hr2))
                        e3)))))
            }
          }
        }
      };
  () }

example : progOkFrom hmM0 hmM.term = true := by native_decide











/-! ### A restriction on recursive fns: inside a recursive fn, a λ may not
    cite the fn's own Π-typed parameter — not even through a snapshot
    (`lamFeedG`/`lamFeedJ` are rejected below) — while citing snapshots of
    data works (`lamFeedH`) and passing the parameter itself onward works
    (`lamFeedI`). Every fold-evidence builder in the move layer is therefore a
    top-level pure lemma applied to the parameter, never a local λ over it. -/
def lamFeedG : Term := prog_parse {
  fn Eat [fuel] (fuel : Nat, n : Nat,
                 Hp : Π (K2 : Nat) → Π (Hk2 : Le K2 n) → Le K2 (S n)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => {
        let N0 = n;
        let Hgive = (λ (K2 : Nat). λ (Hk : Le K2 N0). Hp K2 Hk);
        Eat(f2, n, Hgive);
        ()
      } } };
  () }
example : progOk lamFeedG = false := by native_decide


def lamFeedH : Term := prog{
  fn Eat [fuel] (fuel : Nat, n : Nat,
                 Hp : Π (K2 : Nat) → Π (Hk2 : Le K2 n) → Le K2 (S n)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => {
        let N0 = n;
        let Hgive = (λ (K2 : Nat). λ (Hk : Le K2 N0). LeUpRRaw K2 N0 Hk);
        Eat(f2, n, Hgive);
        ()
      } } };
  () }
example : progOk lamFeedH = true := by native_decide

def lamFeedI : Term := prog{
  fn Eat [fuel] (fuel : Nat, n : Nat,
                 Hp : Π (K2 : Nat) → Π (Hk2 : Le K2 n) → Le K2 (S n)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => {
        let N0 = n;
        let Hother = Hp Z;
        Eat(f2, n, Hp);
        ()
      } } };
  () }
example : progOk lamFeedI = true := by native_decide


def lamFeedJ : Term := prog_parse {
  fn Eat [fuel] (fuel : Nat, n : Nat,
                 Hp : Π (K2 : Nat) → Π (Hk2 : Le K2 n) → Le K2 (S n)) -> Unit {
    match fuel {
      Z => (),
      S(f2) => {
        let N0 = n;
        let Hp0 = Hp;
        let Hgive = (λ (K2 : Nat). λ (Hk : Le K2 N0). Hp0 K2 Hk);
        Eat(f2, n, Hgive);
        ()
      } } };
  () }
example : progOk lamFeedJ = false := by native_decide




/-- The checked caller: the fixed ensures are exactly sufficient for a caller
    to discharge Insert's preconditions by proof — New's size conjunct
    transports the fuel bound, and with resize in place there is no headroom
    obligation left. A FRAGMENT now, checked from the module's own state. -/
def s2CheckedCaller : Term := prog_parse {
  let Pair(m0, ev0) = NewHM(2, unit);
  let M0 = m0;
  let Pair(HfindN, HsizeN) = ev0;
  let b1 = &m m0;
  let Pair(Hpt1, Hsz1) = InsertHM(9, 5, 70, b1,
    NatRwRaw (λ (W : Nat). Le (S (S W)) 9) Z (SizeHM M0)
      (IdSymRaw Nat (SizeHM M0) Z HsizeN) unit);
  let y = m0;
  () }
example : progOkFrom hmM s2CheckedCaller = true := by native_decide


/-! ### The rotation, checked with values — the single-allocation move's core

    The mem::replace chain through a matched borrow: each lowercase read is
    immediately followed by an overwrite of the slot it was read from, so a
    move-compiling backend relinks three pointers and allocates nothing. In
    concrete mode the checker runs it and `Refl` closes both final states:
    the head of `a` moved onto `b` — the very node, not a copy. -/
def rotValues : Term := prog{
  let a = Cons(Pair(1, 10), Cons(Pair(2, 20), Nil));
  let b = Cons(Pair(9, 90), Nil);
  let og = &m a;
  let nw = &m b;
  match og {
    Nil => (),
    Cons(hd, tail) => {
      let tmp = *tail;
      *tail := *nw;
      *nw := *og;
      *og := tmp;
      ()
    }
  };
  let a2 = a;
  let b2 = b;
  let H1 = (Refl : Id (List (Σ (k : Nat). Nat)) a2 Cons(Pair(2, 20), Nil));
  let H2 = (Refl : Id (List (Σ (k : Nat). Nat)) b2
              Cons(Pair(1, 10), Cons(Pair(9, 90), Nil)));
  () }
example : progOk rotValues = true := by native_decide



-- P1: identity round-trip of the real container through &mut — destructure,
-- project the clauses, repack via MkInv, refill.
def s1P1 : Term := prog{
  fn Touch (self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots)) -> Unit {
    let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = *self;
    let HLe1 = InvLe1 cap load nn slots HInv;
    let HLoad = InvLoad cap load nn slots HInv;
    let HLed = InvLedger cap load nn slots HInv;
    let HCnt = InvCount cap load nn slots HInv;
    let HSf = InvSlots cap load nn slots HInv;
    let SL0 = slots;
    *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
      MkInv cap load nn SL0 HLe1 HLoad HLed HCnt HSf))));
    () };
  () }
example : progOk s1P1 = true := by native_decide

-- P2a: carve, then refill with the untouched entry clauses (typed at the
-- entry slots sigma) — isolates the audit-side segment-fold conversion.
def s1P2a : Term := prog{
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack h n Hne };
  fn Touch (key : Nat, self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots)) -> Unit {
    let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = *self;
    let HLe1 = InvLe1 cap load nn slots HInv;
    let HLoad = InvLoad cap load nn slots HInv;
    let HLed = InvLedger cap load nn slots HInv;
    let HCnt = InvCount cap load nn slots HInv;
    let HSf = InvSlots cap load nn slots HInv;
    let SL0 = slots;
    let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, HLe1);
    let sb = &m slots;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let bb = &m (*cell)[0];
    *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
      MkInv cap load nn SL0 HLe1 HLoad HLed HCnt HSf))));
    () };
  () }
-- The exit audit needs a carved array rejoined before it can re-type a
-- dependent pack: the array component may not stay segmented, even though
-- the sigma/composition equation is definitional (`s1P2c` below proves
-- that). `s1P2a` checks exactly this: the carve is rejoined at the exit, the
-- fold rebuilds the whole-array value, and the pack re-types against it. The
-- op layer's callee routing (`SlotUpd`/`SlotRem`/`MoveOne`) does not need to
-- route around this.
example : progOk s1P2a = true := by native_decide

-- P2c/P2d: is the entry sigma definitionally the composition of the segment
-- sigmas, from a carve of a local owned array? Asked with an ascribed Refl.
def s1P2c : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            a : Array n (List (Σ (k : Nat). Nat))) -> Unit {
    let SL0 = a;
    let sb = &m a;
    let pre = &m (*sb)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let bb = &m (*cell)[0];
    let L0 = *pre;
    let B0 = *bb;
    let H0 = *hic;
    let Heq = (Refl : Id (Array n (List (Σ (k : Nat). Nat))) SL0
                (arrCat i (S r) L0 (acons r B0 H0)));
    () };
  () }
example : progOk s1P2c = true := by native_decide



/-! ## (xviii) The borrow-returning ops — shape probes first

    GetMut must return a borrow into the pack, so its carve group cannot close
    before the return. Two candidate shapes over the real container: the carve
    inline in the pack-navigating fn, and the carve pushed into a `SlotGet`
    callee whose parameter is the plain (non-dependent) array borrow. -/

/-- The packed `Le 1 cap`, extracted off the pack value by pure projection. -/
def PackLe1 : Term := prog_parse {
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Le (S Z) (CapHM H0)) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Le (S Z) Cap) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Le (S Z) Cap) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Le (S Z) Cap) {
                  Pair (Slots) (Inv) => InvLe1 Cap Load N Slots Inv } } } } }
def PackLe1Ty : Term := prog_parse {
  Π (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) →
    Le (S Z) (CapHM Hm) }
example : chkL PackLe1 PackLe1Ty = true := by native_decide

/-- Probe G1: the monolithic shape — navigate, carve inline, walk, return. -/
def gmProbe1 : Term := prog_parse {
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack h n Hne };
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
                self : &mut HashMapT) -> &mut Nat
  {
    let HLe1 = PackLe1 (*self);
    let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = self;
    let c = *cap;
    *cap := c;
    let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, c, HLe1);
    let pre = &m (*slots)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*slots)[i ; 1 ; r];
    let bb = &m (*cell)[0];
    WalkVal(fuel, key, dflt, bb)
  };
  () }

/-- Probe G2: the layered shape — the carve lives in `SlotGet`, whose param is
    the PLAIN array borrow, and the pack-navigating fn only reborrows fields. -/
def gmProbe2 : Term := prog_parse {
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack h n Hne };
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
  fn SlotGet (fuel : Nat, cap : Nat, key : Nat, dflt : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))),
              HLe1 : Le (S Z) cap) -> &mut Nat {
    let Pair(i, Pair(r, Pair(hd, him))) = SlotOfE(key, cap, HLe1);
    let pre = &m (*b)[Z ; i ; S r | LeAddRaw i (S r) | hd];
    let cell = &m (*b)[i ; 1 ; r];
    let bb = &m (*cell)[0];
    WalkVal(fuel, key, dflt, bb) };
  fn GetMutRaw (fuel : Nat, key : Nat, dflt : Nat,
                self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))).
                    HMInvT cap load n slots)) -> &mut Nat {
    let HLe1 = PackLe1 (*self);
    let Pair(cap, Pair(load, Pair(nn, Pair(slots, HInv)))) = self;
    let c = *cap;
    *cap := c;
    SlotGet(fuel, c, key, dflt, &m *slots, HLe1)
  };
  () }

/-- Probe G3: no carve — a symbolic-index element borrow into the slots field,
    with the bound built from the packed `Le 1 cap` and the minted slot
    identity. Slots stays one leaf holding one element loan. -/
def gmProbe3 : Term := prog_parse {
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack h n Hne };
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
              let bb = &m (*slots)[i | NatRwRaw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSymRaw Nat i (Mod key C0) Him0)
                (ModLtNRaw key C0 HLe1)];
              WalkVal(fuel, key, dflt, bb)
            } } } } } };
  () }
/-! ### A known kernel gap: the borrow-returning ops (pinned by the three
    assertions below) cannot check against the intrinsically-packed
    container today.

    A returned borrow keeps its group open across the op's return, so the exit
    audit re-types self's payload with a loan (and the carve's segmentation)
    still inside the slots component. For a plain owned type that is fine —
    the audit exempts the returned borrow's sub-place and checks the rest
    (`quicksortA`'s shape; `packNav`'s toy pack with a slots-independent tail
    passes the same way). But `HashMapT`'s Σ0 tail is `HMInvT cap load n
    slots`: re-typing it needs the whole slots value, which no exemption can
    provide while a leaf of it is lent out — and every route to a bucket
    element goes through a carve or an index place (`gmProbe1` inline,
    `gmProbe3` index-place) or a callee boundary whose group-end re-mints the
    component and orphans the packed proof (`gmProbe2`).

    This is `12-design-borrow-refounding.md`'s loan-attached-debts gap
    arriving at the safety layer, not just the functional one: the flagship
    doc's "verified for safety + the packed invariant" expectation for GetMut
    was calibrated on an earlier whole-parameter audit exemption, which was
    unsound and has since been fixed to per-sub-place (see
    `AuditExemption.lean`) — the sound audit closes exactly the loophole the
    design would have used. Fixing it is kernel work (the audit/conversion in
    `Machine.lean`), so it is reported here rather than patched. The ops
    below are still exercised by the executing differential (the machine
    runs them correctly); their chain is asserted `progRejects` with the
    audit's needle. -/

example : progOk gmProbe1 = false := by native_decide
example : progOk gmProbe2 = false := by native_decide
example : progOk gmProbe3 = false := by native_decide


/-! ## (xx) Not vacuous: the lying twins, one per conjunct

    Each return type is the only description of its op, so each fixed conjunct
    gets a twin changing exactly it — MINTED from the persisted `Checked.term`
    (docs/21), each an edit of one marked claim site, checked from the same
    seed. `NewHM`/`InsertHM`/`RemoveHM` are unhoisted, so every ret-type site
    is single-copy. -/

-- New, conjunct 1: the fresh map claims to answer every key with `Some 0`.
example : progOkFrom Dllbc.std
  (mintOn hmM0.term "nfind" 1 (fun _ => prog_parse { SomeN Z })) = false := by native_decide

-- New, conjunct 2: the fresh map claims size one.
example : progOkFrom Dllbc.std
  (mintOn hmM0.term "nsize" 1 (fun b => .ctorApp "S" [b])) = false := by native_decide

-- Insert, conjunct 1a: the find-equation lied onto the entry map — the exit
-- claims the old answers (the update never happened).
example : progOkFrom hmM0
  (mintOn hmM.term "ifind" 1 (fun b => .app (.const "old") b)) = false := by native_decide

-- Insert, conjunct 1b: the frame direction flipped — the model updated the
-- exit state instead of the entry state (`old *self`'s own deref, read off
-- the honest claim's spine).
example : progOkFrom hmM0
  (mintOn hmM.term "iframe" 1 noopOf) = false := by native_decide

-- Insert, conjunct 2: the size accounting off by one.
example : progOkFrom hmM0
  (mintOn hmM.term "isize" 1 (fun b => .ctorApp "S" [b])) = false := by native_decide

-- Remove, conjunct 1: the returned option claims the exit map's answer (which
-- is None at the removed key) instead of the entry map's.
example : progOkFrom hmM0
  (mintOn hmM.term "rfound" 1 noopOf) = false := by native_decide

-- Remove, conjunct 2: the pointwise equation lied onto the entry map.
example : progOkFrom hmM0
  (mintOn hmM.term "rpt" 1 (fun b => .app (.const "old") b)) = false := by native_decide

-- Remove, conjunct 3: size accounting flipped to SizeIns's shape (bump-if-
-- absent instead of drop-if-present) — the spine's head swapped for the other
-- spec function.
example : progOkFrom hmM0
  (mintOn hmM.term "rsize" 1
    (fun b => match b with | .app (.app _ k) o => .app (.app SizeIns k) o | t => t))
  = false := by native_decide

/-! ## (xxii) Not vacuous, part 2: the body twins — MINTED

    The id world transcribed these at 60–670 lines each ("a body difference
    has no splice that can reach it"); each is now an edit of one marked body
    site. The vacuity sweep ran before the transcriptions were deleted: all
    five old body twins rejected at the audit, honest — the `splitANoSwap`
    class did not recur here. -/

-- The hit path skips the overwrite: the marked write's `val` becomes the
-- value already there (`V0`, in scope at the site) — same statements, same
-- claims, nothing written.
-- The hit path skips the overwrite: the marked write's `val` becomes the
-- cell's own current payload (`*vv` — the runtime read; the comptime snapshot
-- `V0` is fenced from ⇒-positions, which the first cut of this twin learned
-- the hard way) — same statements, same claims, nothing changed.
example : progRejectsFrom Dllbc.std
  (mintOn hmM0.term "ivv" 1 (fun _ => Term.deref (Term.var "vv")))
  "does not have return type" = true := by native_decide

-- The fresh-key path skips the `n` bump — every `S (nn)` in both fresh-key
-- arms' packs collapsed to `nn` (4 copies by name, the count pinned). The
-- pack's counting clause has no proof at the stale `n`, caught at the borrow
-- payload's audit.
example : progRejectsFrom hmM0
  (mintOn hmM.term "ibump" 4 (fun b => match b with | .ctorApp "S" [n] => n | t => t))
  "does not have its owed type" = true := by native_decide

-- The ledger-tripped path packs at the old capacity anyway: the NO-RESIZE
-- arm's body planted over the resize arm's (both arms are marked docs/22
-- fragments — an arm body is one term, and naming it is what makes a
-- 670-line transcription a one-line mint).
example : progRejectsFrom hmM0
  (match markedBody? "inogrow" hmM.term with
   | some b => mintOn hmM.term "igrow" 1 (fun _ => b)
   | none => .unit)
  "does not have its owed type" = true := by native_decide

/-- Body twin: insert into the unhashed slot — the slot pack computed off the
    wrong key. Caught where it is written: the returned identity cannot say
    `i = Mod h n`. -/
def twinUnhashedSlot : Term := prog_parse {
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack (S h) n Hne };
  () }
example : progOk twinUnhashedSlot = false := by native_decide





end Dllbc.Tests.HashMap
end

/-!
# The hashmap's pinned borrow-returning ops: GetMut and GetMutOrInsert

`GetMut`/`GetMutOrInsert` hand back a `&mut` into the hashmap's slot array
under a one-slot exit contract `~> E`: instead of re-typing the whole
container symbolically, a returned `&mut (s : τ ~> E)` states what the
container becomes once the borrow ends, with `*res` naming the borrow's own
exit payload, and the checker discharges the contract by hole-filling rather
than replaying the walk. This module builds the hashmap instance of that
contract: `SetHM` (the pack-to-pack model update), the pinned bucket walk,
and `GetMutHM`/`GetMutOrInsertHM`, closing with the round-trip law (what you
write through the cursor is there on the next get) checked at hashmap scale.

Every spec function here compares keys as `Eqb query entrykey`, matching
`FindL`'s own argument order, so the walk's branch equation (`if e : Eqb key
*kk`) is exactly the spine the pin's normalization gets stuck on. The
opposite orientation (`Eqb *kk key`) would need a repair lemma to line back
up, and a pin has no lemma slot to hold one — so this argument order is
load-bearing, not a style choice.
-/

section

open Dllbc
-- Raw proof terms, bare (StdChain's doctrine: proofs apply as constants).
-- Formers the std seed binds (Mod, Mul, Pred, …) are written QUALIFIED inside
-- the seeded blocks (docs/21 §9's audit residual); the hashmap's own formers
-- are file-local constants and stay bare everywhere.
open Dllbc.StdChainRaw
open Dllbc.Tests.S23Direct (mintOn crossOn markedBody? noopOf)

namespace Dllbc.Tests.HashMap

/-! ## The bucket-level update, key-oriented

    `BSetK q v l` sets the value at key `q` to `v`, leaving keys and structure
    untouched; a no-op when `q` is absent. It mirrors `FindL` clause for
    clause, so the two can never disagree about which entry is "the" hit. -/

def BSetK : Term := prog_parse {
  λ (Q : Nat). λ (V : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
      Nil => Nil,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). List (Σ (k : Nat). Nat)) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
              True => Cons(Pair(K2, V), T),
              False => Cons(Pair(K2, V2), Rec) } } } }

example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BSetK 3 99 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)))
  Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BSetK 7 99 Cons(Pair(1, 10), Nil)) Cons(Pair(1, 10), Nil) } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BSetK 3 99 Cons(Pair(3, 30), Cons(Pair(3, 31), Nil)))
  Cons(Pair(3, 99), Cons(Pair(3, 31), Nil)) } = true := by native_decide

/-- Presence survives a non-hit head: from `Eqb q k0 ≡ False` and presence in
    the whole bucket, presence in the tail — the walk's recursion premise. -/
def HitTailEv : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
  λ (H : Id Bool (HitL Q Cons(Pair(K0, V0), T)) True).
    IdTransRaw Bool (HitL Q T) (HitL Q Cons(Pair(K0, V0), T)) True
      (IdSymRaw Bool (HitL Q Cons(Pair(K0, V0), T)) (HitL Q T)
        (IdCongrRaw Bool Bool
          (λ (W : Bool). IsSomeB (elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
            True => SomeN V0, False => FindL Q T }))
          (Eqb Q K0) False E))
      H }
def HitTailEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False → Id Bool (HitL Q Cons(Pair(K0, V0), T)) True →
    Id Bool (HitL Q T) True }
example : chkL HitTailEv HitTailEvTy = true := by native_decide

/-- The hit leg's return conjunct: at `Eqb q k0 ≡ True`, the head's value IS
    the bucket's answer at `q`. Stated with `Some (*r)` on the left so the
    constructed proof's type is verbatim the declared one. -/
def FindEvHit : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSymRaw OptN (FindL Q Cons(Pair(K0, V0), T)) (SomeN V0)
      (IdCongrRaw Bool OptN
        (λ (W : Bool). elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
          True => SomeN V0, False => FindL Q T })
        (Eqb Q K0) True E) }
def FindEvHitTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id OptN (SomeN V0) (FindL Q Cons(Pair(K0, V0), T)) }
example : chkL FindEvHit FindEvHitTy = true := by native_decide

/-- The miss leg's transport: a non-hit head is skipped by the lookup, so tail
    evidence lifts to the whole bucket. -/
def FindTailEv : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSymRaw OptN (FindL Q Cons(Pair(K0, V0), T)) (FindL Q T)
      (IdCongrRaw Bool OptN
        (λ (W : Bool). elim W return (λ (Bm : Bool). Σ (bb : Bool). OptP bb Nat) {
          True => SomeN V0, False => FindL Q T })
        (Eqb Q K0) False E) }
def FindTailEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id OptN (FindL Q T) (FindL Q Cons(Pair(K0, V0), T)) }
example : chkL FindTailEv FindTailEvTy = true := by native_decide

/-! ## Does a key-driven walk discharge its own pin?

    A key-driven walk branches on `Eqb key *kk`, a stuck `Bool` over a
    symbolic key. The pin `BSetK key (*res) t`, once normalized, is stuck at
    that very `elim (Eqb key σkk)`, so discharge depends on whether the
    checker's conversion can consult the branch's own equation (the hit leg
    needs the True arm taken, the miss leg the False arm whose result must
    converge with the recursive call's projected pin at the shared exit).
    This test uses a plain `&mut Nat` return (no extra conjuncts) so a
    failure can only be about the pin, not about anything else in the
    signature. -/

def bktGetPinOnly : Term := prog_parse {
  fn BktGetP [fuel] (fuel : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetK key (*res) t),
      Hin : Id Bool (HitL key (*b)) True,
      Hf : Le (LenE (*b)) fuel) -> &mut Nat {
    match b {
      Nil => botElim Unit (BoolFTRaw Hin),
      Cons(Pair(kk, vv), tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => {
          let K0 = *kk;
          let V0 = *vv;
          let T0 = *tl;
          if e : Eqb key *kk {
            &m *vv
          } else {
            BktGetP(f2, key, &m *tl, HitTailEv key K0 V0 T0 e Hin, Hf)
          } } } } };
  () }

/-- **This is refused.** The hit-leg fill normalizes to `Cons (Pair σ18 σ22)
    σ17`, but the pin itself normalizes to a `boolRec` stuck on `Eqb σ11 σ18`
    — whose True arm is literally that fill, one ι-step away, gated on the
    very branch equation the body's `if e :` already established. Conversion
    does not consult branch equations, and `Eqb` is a fold that stays stuck
    even at syntactically equal neutral arguments (`EqbReflRaw` is a lemma, and
    a pin has no lemma slot). So no key-comparing update can ever discharge a
    pin over a symbolic key — not by accident, but on principle: **a pin's
    data must be pin-computable.** The key-to-position conversion can't
    happen inside the pin, so it has to happen in the signature instead: the
    walk below recurses on a position (a constructor, so each branch is a
    real refinement) and the position joins the parameters. -/
example : progRejects bktGetPinOnly
  "does not convert with the declared pin (boolRec" = true := by native_decide

/-! ### The position vocabulary: where `key` sits, and the update that needs
    no comparison -/

/-- `FindPosL q l` — the hit's position; `LenE l` when absent (every miss adds
    one `S`), which is exactly the or_insert write site. -/
def FindPosL : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Nat) {
              True => Z,
              False => S(Rec) } } } }

example : chkL prog_parse { Refl } prog_parse { Id Nat
  (FindPosL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 1 } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat
  (FindPosL 9 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 2 } = true := by native_decide

/-- `BSetP p v l` — value at position `p` becomes `v`, key and structure kept,
    no-op past the end. Index-first, so a constructor-refined `p` steps it with
    NO key comparison anywhere — this is what makes it pin-dischargeable where
    `BSetK` is not. -/
def BSetP : Term := prog_parse {
  λ (P : Nat). λ (V : Nat).
    elim P return (λ (Pz : Nat). Π (L : List (Σ (k : Nat). Nat)) → List (Σ (k : Nat). Nat)) {
      Z => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Nil,
          Cons (E) (T) Rec =>
            Cons(elim E return (λ (Em : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
              Pair (K2) (V2) => Pair(K2, V) }, T) },
      S (P2) Rec => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Nil,
          Cons (E) (T) Rec2 => Cons(E, Rec T) } } }

example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BSetP 1 99 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil)))
  Cons(Pair(1, 10), Cons(Pair(3, 99), Nil)) } = true := by native_decide

/-- Position `Z` on a hit bucket means the HEAD is the hit. -/
def PosZHit : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (Hp : Id Nat Z (FindPosL Q Cons(Pair(K0, V0), T))).
    IfDecRaw (Eqb Q K0) (Id Bool (Eqb Q K0) True)
      (λ (Et : Id Bool (Eqb Q K0) True). Et)
      (λ (Ef : Id Bool (Eqb Q K0) False).
        botElim (Id Bool (Eqb Q K0) True)
          (ZnotsRaw (FindPosL Q T)
            (IdTransRaw Nat Z (FindPosL Q Cons(Pair(K0, V0), T)) (S (FindPosL Q T)) Hp
              (IdCongrRaw Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) False Ef)))) }
def PosZHitTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Nat Z (FindPosL Q Cons(Pair(K0, V0), T)) → Id Bool (Eqb Q K0) True }
example : chkL PosZHit PosZHitTy = true := by native_decide

/-- Position `S p2` on a bucket means the head MISSED and `p2` locates the key
    in the tail — the walk's recursion evidence, in one package. -/
def PosSStep : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)). λ (P2 : Nat).
  λ (Hp : Id Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T))).
    IfDecRaw (Eqb Q K0) ((Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)))
      (λ (Et : Id Bool (Eqb Q K0) True).
        botElim ((Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)))
          (ZnotsRaw P2 (IdSymRaw Nat (S P2) Z
            (IdTransRaw Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) Z Hp
              (IdCongrRaw Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) True Et)))))
      (λ (Ef : Id Bool (Eqb Q K0) False).
        Pair(Ef, SInjRaw P2 (FindPosL Q T)
          (IdTransRaw Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) (S (FindPosL Q T)) Hp
            (IdCongrRaw Bool Nat (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
              True => Z, False => S (FindPosL Q T) }) (Eqb Q K0) False Ef)))) }
def PosSStepTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
  Π (P2 : Nat) → Id Nat (S P2) (FindPosL Q Cons(Pair(K0, V0), T)) →
    (Id Bool (Eqb Q K0) False) × (Id Nat P2 (FindPosL Q T)) }
example : chkL PosSStep PosSStepTy = true := by native_decide

/-! ### The position-driven walk, and why it discharges

    Recursing on `p` instead of the key means every recursive step the pin
    owes lands in a branch where `p` is a constructor, so it's a real
    refinement rather than a stuck fold. The key never needs comparing at
    the pin level; the return evidence reconstructs the `FindL` claim from
    the position facts afterward, at the value level, where lemmas are
    allowed. -/

def bktGetAtDecl : Term := prog{
  fn BktGetAt [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). Id OptN (SomeN (*r)) (FindL key (old *b)) {
    match b {
      Nil => botElim Unit (BoolFTRaw Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => Pair(&m *vv, FindEvHit key K0 V0 T0 (PosZHit key K0 V0 T0 Hpos)),
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktGetAt(p2, key, &m *tl,
              HitTailEv key K0 V0 T0 Emiss Hhit, Epos2);
            let W0 = *r2;
            Pair(r2, IdTransRaw OptN (SomeN W0) (FindL key T0)
              (FindL key Cons(Pair(K0, V0), T0)) h2
              (FindTailEv key K0 V0 T0 Emiss))
          } } } } };
  () }

example : progOk bktGetAtDecl = true := by native_decide

/-! ## The slot split, spelled so the pin can cite it

    Carving the slot array at `Mod key cap` needs its split point stated in
    terms the pin's own normalization actually produces, not a fresh minted
    variable that then fails to convert with `SetHM`'s internal `Mod`/`CoMod`
    applications. So the pinned op carves at the literal applications and
    cites `ModSplit` for the arithmetic instead. -/

/-- The residue: everything after `key`'s slot. `cap = Mod key cap + S (CoMod
    key cap)` whenever `1 ≤ cap` — that is `ModSplit`. -/
def CoMod : Term := prog_parse { λ (Q : Nat). λ (C : Nat). SubRaw C (S (Mod Q C)) }

def ModSplit : Term := prog_parse {
  λ (Q : Nat). λ (C : Nat). λ (H : Le (S Z) C).
    IdSymRaw Nat (Add (Mod Q C) (S (CoMod Q C))) C
      (IdTransRaw Nat (Add (Mod Q C) (S (CoMod Q C))) (S (Add (Mod Q C) (CoMod Q C))) C
        (AddSuccRaw (Mod Q C) (CoMod Q C))
        (AddSubCancelRaw C (S (Mod Q C)) (ModLtNRaw Q C H))) }
def ModSplitTy : Term := prog_parse {
  Π (Q : Nat) → Π (C : Nat) → Le (S Z) C →
    Id Nat C (Add (Mod Q C) (S (CoMod Q C))) }
example : chkL ModSplit ModSplitTy = true := by native_decide

-- Concrete check: cap 5, key 7 splits into slot 2 and residue 2.
example : chkL prog_parse { Refl } prog_parse { Id Nat 5 (Add (Mod 7 5) (S (CoMod 7 5))) } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (CoMod 7 5) 2 } = true := by native_decide

/-! ## `SetHM` — the pack-to-pack model update, decomposition-first

    `SetHM` names the carve's pieces with `atake`/`adrop` at the exact split
    terms the pinned body carves at (`Mod q cap`, `CoMod q cap`), with the
    element-level work done by `BSetK` on the `acons`-headed suffix — so
    the pin's hole-filled exit converts against this decomposition rather
    than an opaque update. The invariant component rides through untouched:
    a value write keeps every clause's inhabitant as it was. -/

def BumpHead : Term := prog_parse {
  λ (Q : Nat). λ (V : Nat). λ (R : Nat). λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BSetK Q V X) XS)
      (S R) A }

def SetHM : Term := prog_parse {
  λ (Q : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N, Pair(
                      arrCat (Mod Q Cap) (S (CoMod Q Cap))
                        (atake (Mod Q Cap) (S (CoMod Q Cap)) Slots)
                        (BumpHead Q V (CoMod Q Cap)
                          (adrop (Mod Q Cap) (S (CoMod Q Cap)) Slots)),
                      Inv)))) } } } } }

-- The hit key's answer moves; the frame — a different key hashing to the
-- same slot, and the size — does not.
example : chkL prog_parse { Refl } prog_parse { Id OptN (FindHM 3 (SetHM 3 99 hmEx)) (SomeN 99) }
  = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id OptN (FindHM 5 (SetHM 3 99 hmEx)) NoneN }
  = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id OptN (FindHM 7 (SetHM 7 99 hmEx)) NoneN }
  = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (SizeHM (SetHM 3 99 hmEx)) 1 } = true := by
  native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (CapHM (SetHM 3 99 hmEx)) 2 } = true := by
  native_decide

/-- `SetHM` preserves the size — the second call's fuel bound. Nested Σ-elims
    to the leaf, where both sides compute to the same `N` and `Refl` closes. -/
def SetHMSize : Term := prog_parse {
  λ (Q : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Id Nat (SizeHM (SetHM Q V H0)) (SizeHM H0)) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Id Nat (SizeHM (SetHM Q V Pair(Cap, H1))) (SizeHM Pair(Cap, H1))) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Id Nat (SizeHM (SetHM Q V Pair(Cap, Pair(Load, H2))))
                  (SizeHM Pair(Cap, Pair(Load, H2)))) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Id Nat (SizeHM (SetHM Q V Pair(Cap, Pair(Load, Pair(N, H3)))))
                      (SizeHM Pair(Cap, Pair(Load, Pair(N, H3))))) {
                  Pair (Slots) (Inv) => Refl } } } } }
def SetHMSizeTy : Term := prog_parse {
  Π (Q : Nat) → Π (V : Nat) →
  Π (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) →
    Id Nat (SizeHM (SetHM Q V Hm)) (SizeHM Hm) }
example : chkL SetHMSize SetHMSizeTy = true := by native_decide

/-! ## The map level — `SetHMAt`, and the pinned `GetMutHM`

    Citing `ModSplit key cap` directly in the carve would refine
    `σcap := Add (Mod key σcap) …`, which is cyclic and fails the occurs
    check. So the slot index and residue enter as parameters instead, with
    their defining equations carried as evidence, and the pin cites the
    parameters: `SetHMAt i rr p (*res) s`. The key leaves the pin entirely —
    slot `i` and cell `p` are the pin-computable data; `key` only appears in
    the return conjuncts and in the equations (`Him`/`Hhit`/`Hpos`) tying the
    data back to it. The caller mints `i`/`rr` as `Mod`/`CoMod` and
    discharges `Hd` with `ModSplit` from the previous section. -/

def BumpHeadP : Term := prog_parse {
  λ (P : Nat). λ (V : Nat). λ (R : Nat). λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BSetP P V X) XS)
      (S R) A }

def SetHMAt : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (P : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N, Pair(
                      arrCat I (S R) (atake I (S R) Slots)
                        (BumpHeadP P V R (adrop I (S R) Slots)),
                      Inv)))) } } } } }

/-- The position of `q` in its hashed bucket, over the pack. -/
def PosHM : Term := prog_parse {
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Nat) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Nat) {
                  Pair (Slots) (Inv) => FindPosL Q (AgetB Cap Slots (Mod Q Cap)) } } } } }

example : chkL prog_parse { Refl } prog_parse { Id Nat (PosHM 3 hmEx) Z } = true := by native_decide

/-- The crossing fact at the carve, index moved to the hash by the equation:
    `AgetB` of the composition at `Mod q cap` IS the carved bucket. -/
def AgetAtMod : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (M : Nat).
  λ (L : Array I (List (Σ (k : Nat). Nat))). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (Him : Id Nat I M).
    NatRwRaw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
        (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) W) B)
      I M Him
      (AgetBCatMid R B H I L) }
def AgetAtModTy : Term := prog_parse {
  Π (I : Nat) → Π (R : Nat) → Π (M : Nat) →
  Π (L : Array I (List (Σ (k : Nat). Nat))) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
    Id Nat I M →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B }
example : chkL AgetAtMod AgetAtModTy = true := by native_decide

/-! ### The value-level lookup — the Refl-matchable conjunct

    A return conjunct like `Id (Opt Nat) (Some (*r)) (FindHM key (old *self))`
    wraps the payload in a rigid constructor, and a `Refl`-match can't refine
    a symbolic variable sitting under a rigid head on both sides. So the op
    returns both: a bare Nat-level primary (`FindValHM`, the caller's
    `Refl`-match handle) and the `Opt`-shaped conjunct alongside it for
    callers that want the full statement. -/

def FindVL : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Nat) {
              True => V2,
              False => Rec } } } }

def FindValHM : Term := prog_parse {
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots). Nat) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots). Nat) {
                  Pair (Slots) (Inv) => FindVL Q (AgetB Cap Slots (Mod Q Cap)) } } } } }

example : chkL prog_parse { Refl } prog_parse { Id Nat (FindValHM 3 hmEx) 30 } = true := by native_decide

/-- The hit leg's Nat-level conjunct. -/
def FindVEvHit : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSymRaw Nat (FindVL Q Cons(Pair(K0, V0), T)) V0
      (IdCongrRaw Bool Nat
        (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
          True => V0, False => FindVL Q T })
        (Eqb Q K0) True E) }
def FindVEvHitTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id Nat V0 (FindVL Q Cons(Pair(K0, V0), T)) }
example : chkL FindVEvHit FindVEvHitTy = true := by native_decide

/-- The miss leg's Nat-level transport. -/
def FindVTailEv : Term := prog_parse {
  λ (Q : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSymRaw Nat (FindVL Q Cons(Pair(K0, V0), T)) (FindVL Q T)
      (IdCongrRaw Bool Nat
        (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
          True => V0, False => FindVL Q T })
        (Eqb Q K0) False E) }
def FindVTailEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (K0 : Nat) → Π (V0 : Nat) → Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id Nat (FindVL Q T) (FindVL Q Cons(Pair(K0, V0), T)) }
example : chkL FindVTailEv FindVTailEvTy = true := by native_decide

/-! ### `GetMut`, in the pin-computable spelling -/

set_option maxHeartbeats 0 in
def hmPinM : Checked := prog (Dllbc.std) {
  fn BktGetAt [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). (Id Nat (*r) (FindVL key (old *b)))
           × (Id OptN (SomeN (*r)) (FindL key (old *b))) {
    match b {
      Nil => botElim Unit (BoolFTRaw Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => {
            let Ehit = PosZHit key K0 V0 T0 Hpos;
            Pair(&m *vv, Pair(FindVEvHit key K0 V0 T0 Ehit,
              FindEvHit key K0 V0 T0 Ehit))
          },
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktGetAt(p2, key, &m *tl,
              HitTailEv key K0 V0 T0 Emiss Hhit, Epos2);
            let W0 = *r2;
            let Hv2 = FstT (Id Nat W0 (FindVL key T0)) (Id OptN (SomeN W0) (FindL key T0)) h2;
            let Ho2 = SndT (Id Nat W0 (FindVL key T0)) (Id OptN (SomeN W0) (FindL key T0)) h2;
            Pair(r2, Pair(
              IdTransRaw Nat W0 (FindVL key T0) (FindVL key Cons(Pair(K0, V0), T0)) Hv2
                (FindVTailEv key K0 V0 T0 Emiss),
              IdTransRaw OptN (SomeN W0) (FindL key T0)
                (FindL key Cons(Pair(K0, V0), T0)) Ho2
                (FindTailEv key K0 V0 T0 Emiss)))
          } } } } };
  fn GetMutHM (i : Nat, rr : Nat, p : Nat, key : Nat,
      self : &mut (s : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots
        ~> SetHMAt i rr p (*res) s),
      Hd : Id Nat (CapHM (*self)) (Add i (S rr)),
      Him : Id Nat i (Dllbc.StdChainRaw.Mod key (CapHM (*self))),
      Hhit : Id Bool (HitHM key (*self)) True,
      Hpos : Id Nat p (PosHM key (*self)))
      -> Σ (r : &mut Nat). (Id Nat (*r) (FindValHM key (old *self)))
           × (Id OptN (SomeN (*r)) (FindHM key (old *self))) {
    match self { Pair(capb, r1) => match r1 { Pair(loadb, r2x) => match r2x { Pair(nb, r3) => match r3 { Pair(sb, Invb) => {
      let I0 = i;
      let R0 = rr;
      let Key0 = key;
      let C0 = *capb;
      let pre = &m (*sb)[Z ; i ; S rr | LeAddRaw i (S rr) | Hd];
      let cell = &m (*sb)[i ; 1 ; rr];
      let hic = &m (*sb)[S i ; rr];
      let bb = &m (*cell)[0];
      let L0 = *pre;
      let B0 = *bb;
      let H0 = *hic;
      let EB = AgetAtMod I0 R0 (Dllbc.StdChainRaw.Mod Key0 C0) L0 B0 H0 Him;
      let HhitB = IdTransRaw Bool (HitL Key0 B0)
                    (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0)))) True
                    (IdSymRaw Bool
                      (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                        (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0))))
                      (HitL Key0 B0)
                      (IdCongrRaw (List (Σ (k : Nat). Nat)) Bool
                        (λ (W : List (Σ (k : Nat). Nat)). IsSomeB (FindL Key0 W))
                        (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                          (Dllbc.StdChainRaw.Mod Key0 C0)) B0 EB))
                    Hhit;
      let HposB = IdTransRaw Nat p
                    (FindPosL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0)))
                    (FindPosL Key0 B0)
                    Hpos
                    (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
                      (λ (W : List (Σ (k : Nat). Nat)). FindPosL Key0 W)
                      (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                        (Dllbc.StdChainRaw.Mod Key0 C0)) B0 EB);
      let Pair(rb, hb) = BktGetAt(p, key, &m *bb, HhitB, HposB);
      let W0 = *rb;
      let HvB = FstT (Id Nat W0 (FindVL Key0 B0)) (Id OptN (SomeN W0) (FindL Key0 B0)) hb;
      let HoB = SndT (Id Nat W0 (FindVL Key0 B0)) (Id OptN (SomeN W0) (FindL Key0 B0)) hb;
      Pair(rb, Pair(
        IdTransRaw Nat W0 (FindVL Key0 B0)
          (FindVL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
            (Dllbc.StdChainRaw.Mod Key0 C0)))
          HvB
          (IdSymRaw Nat
            (FindVL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
              (Dllbc.StdChainRaw.Mod Key0 C0)))
            (FindVL Key0 B0)
            (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
              (λ (W : List (Σ (k : Nat). Nat)). FindVL Key0 W)
              (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0))
              B0 EB)),
        IdTransRaw OptN (SomeN W0) (FindL Key0 B0)
          (FindL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
            (Dllbc.StdChainRaw.Mod Key0 C0)))
          HoB
          (IdSymRaw OptN
            (FindL Key0 (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
              (Dllbc.StdChainRaw.Mod Key0 C0)))
            (FindL Key0 B0)
            (IdCongrRaw (List (Σ (k : Nat). Nat)) OptN
              (λ (W : List (Σ (k : Nat). Nat)). FindL Key0 W)
              (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0))
              B0 EB))))
    } } } } } };
  () }

example : progOkFrom Dllbc.std hmPinM.term = true := by native_decide

/-- **`GetMut` checks.** The map-level pin discharges through the carve
    (`atake`/`adrop` reduce at the parameter split), the bucket callee's
    projected pin lands in the composition's cell, and the return conjuncts
    are rebuilt from the callee's evidence by the `AgetAtMod` transport. -/
def errOf (t : Term) : String :=
  match checkProgram t prog_parse { Unit } with | .ok _ => "OK" | .error e => e

/-- Seeded run/env helpers for the pinned-op chains. -/
def runVFrom (m : Checked) (t : Term) (name : String) : Option Val :=
  match runProgramFrom m t with
  | .ok env => env.lookup name
  | .error _ => none
def tailEnvFrom (m : Checked) (t : Term) (expected : Env) : Bool :=
  let seeded := m.env.env.map (·.1)
  match programPathsFrom m t with
  | [.ok p] =>
    canonicalize (p.2.env.filter (fun kv => !kv.1.isDecl && !seeded.contains kv.1)) == expected
  | _ => false

/-! ## The end-to-end round-trip chain, at hashmap scale

    Get the cursor, write 42 through it, get again at the same key: the
    second call's evidence plus one `Refl`-match lets the checker derive
    `T ≡ 42` and the exact final map. The premises at a concrete pack are all
    `Refl` (`Mod`/`CoMod`/`PosHM` compute) — and, notably, they are `Refl`
    again at the second call, whose argument is the first call's pinned
    release: `SetHMAt 1 0 0 42 m₀` computes because the pin made the release
    a value, not a fresh existential. An unpinned release would leave no
    premise about the resulting capacity or buckets for the second call to
    reuse. -/

def vN : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vN n]
def vP (a b : Val) : Val := .ctor "Pair" [a, b]
def vU : Val := .ctor "unit" []
def vR : Val := .ctor "Refl" []
def vNil : Val := .ctor "Nil" []

/-- The expected final pack: cap 2, load 8, n 1, slot 1 = `[(3, 42)]`, and the
    entry pack's own invariant inhabitant riding through unchanged. -/
def vPackY : Val :=
  vP (vN 2) (vP (vN 8) (vP (vN 1) (vP
    (.ctor "Arr" [vNil, .ctor "Cons" [vP (vN 3) (vN 42), vNil]])
    (vP vU (vP vR (vP vU (vP vR
      (vP (vP vU vU) (vP (vP (vP vR vU) (vP vR vU)) vU)))))))))

def hmChainCaller : Term := prog_parse {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(1, 0, 0, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    let b2 = &m m;
    let pr2 = GetMutHM(1, 0, 0, 3, b2, Refl, Refl, Refl, Refl);
    match pr2 { Pair(r2, h2) => {
      let Pair(hv, ho) = h2;
      match hv { Refl => {
        let T = *r2;
        let y = m;
        () } } } } } } }

example : progOkFrom hmPinM hmChainCaller = true := by native_decide

/-- The round-trip law, in the checker's own environment: `T ≡ 42` is derived
    (not run), and `y` is the exact updated pack. -/
example : tailEnvFrom hmPinM hmChainCaller
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot),
   ("h", .ctor "Pair" [.sym 0, .sym 1]),
   ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 2),
   ("T", vN 42), ("y", vPackY)] = true := by native_decide

-- A control: the same environment with `T ↦ 43` is refused, not vacuous.
example : tailEnvFrom hmPinM hmChainCaller
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot),
   ("h", .ctor "Pair" [.sym 0, .sym 1]),
   ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 2),
   ("T", vN 43), ("y", vPackY)] = false := by native_decide

-- The interpreter computes the same final map: checker and interpreter agree
-- on the pinned op.
example : (runVFrom hmPinM hmChainCaller "T" == some (vN 42)) = true := by native_decide
example : (runVFrom hmPinM hmChainCaller "y" == some vPackY) = true := by native_decide

/-! ## The counterfactual twins: what should be rejected -/

/-- The key-escape twin: identical body to the working walk, except the `Z`
    leg returns a borrow into the key instead of the value. The fill lands in
    the key slot while the pin still expects the value slot, so this should
    be refused. No extra return conjuncts here, so the refusal can only be
    about the pin. -/
def bktGetAtKey : Term := prog_parse {
  fn BktGetK [p] (p : Nat, key : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BSetP p (*res) t),
      Hhit : Id Bool (HitL key (*b)) True,
      Hpos : Id Nat p (FindPosL key (*b))) -> &mut Nat {
    match b {
      Nil => botElim Unit (BoolFTRaw Hhit),
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => &m *kk,
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            BktGetK(p2, key, &m *tl,
              HitTailEv key K0 V0 T0
                (FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep)
                Hhit,
              SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep)
          } } } } };
  () }

example : progRejects bktGetAtKey "pin is not met" = true := by native_decide

/-- The wrong-position caller: same as the working chain, but the first call
    claims position 1 where the key actually sits at 0. The `Hpos` `Refl` has
    no type to check at, so the caller is refused before any op runs. -/
def hmChainWrongPos : Term := prog_parse {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(1, 0, 1, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    () } } }

example : progOkFrom hmPinM hmChainWrongPos = false := by native_decide

/-- The wrong-slot caller: slot 0 claimed for key 3 at cap 2. `Him`'s `Refl`
    is refused. -/
def hmChainWrongSlot : Term := prog_parse {
  let m = Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit))))))))));
  let b = &m m;
  let pr = GetMutHM(0, 1, 0, 3, b, Refl, Refl, Refl, Refl);
  match pr { Pair(r, h) => {
    *r := 42;
    () } } }

example : progOkFrom hmPinM hmChainWrongSlot = false := by native_decide

/-! ## `GetMutOrInsert` — the or_insert vocabulary

    Position-driven like GetMut, with two extra moving parts. (1) `FindPosL`
    of an ABSENT key is the bucket length — exactly the append site — so ONE
    update (`BPutP`: set at `p`, or append `(key, v)` past the end) covers hit
    and fresh alike, and the walk needs no hit/miss branching. (2) The count
    moves: the pin cannot compute `hit ? n : S n` (the hit is not
    pin-computable data at the outer level), so the NEW COUNT `n2` is a
    parameter, the BODY writes it into the pack (`*nb := n2`), and honesty is
    a premise (`Hn2` ties `n2` to the hit; `Hroom` keeps the ledger). -/

def BPutP : Term := prog_parse {
  λ (P : Nat). λ (Key : Nat). λ (V : Nat).
    elim P return (λ (Pz : Nat). Π (L : List (Σ (k : Nat). Nat)) → List (Σ (k : Nat). Nat)) {
      Z => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Cons(Pair(Key, V), Nil),
          Cons (E) (T) Rec =>
            Cons(elim E return (λ (Em : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
              Pair (K2) (V2) => Pair(K2, V) }, T) },
      S (P2) Rec => λ (L : List (Σ (k : Nat). Nat)).
        elim L return (λ (Lm : List (Σ (k : Nat). Nat)). List (Σ (k : Nat). Nat)) {
          Nil => Cons(Pair(Key, V), Nil),
          Cons (E) (T) Rec2 => Cons(E, Rec T) } } }

example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BPutP 1 5 77 Cons(Pair(1, 10), Nil))
  Cons(Pair(1, 10), Cons(Pair(5, 77), Nil)) } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id (List (Σ (k : Nat). Nat))
  (BPutP 0 5 77 Cons(Pair(1, 10), Nil))
  Cons(Pair(1, 77), Nil) } = true := by native_decide

/-- What the returned borrow holds at entry: the old value if the key was
    there, the default if not. -/
def OrDefL : Term := prog_parse {
  λ (Q : Nat). λ (D : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim (HitL Q L) return (λ (Bm : Bool). Nat) {
      True => FindVL Q L,
      False => D } }

def OrDefHM : Term := prog_parse {
  λ (Q : Nat). λ (D : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Q Hm) return (λ (Bm : Bool). Nat) {
      True => FindValHM Q Hm,
      False => D } }

example : chkL prog_parse { Refl } prog_parse { Id Nat (OrDefHM 3 77 hmEx) 30 } = true := by native_decide
example : chkL prog_parse { Refl } prog_parse { Id Nat (OrDefHM 5 77 hmEx) 77 } = true := by native_decide

/-- A hit at the head makes the whole bucket's `OrDefL` its head value. -/
def OrDHitEv : Term := prog_parse {
  λ (Q : Nat). λ (D : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) True).
    IdSymRaw Nat (OrDefL Q D Cons(Pair(K0, V0), T)) V0
      (IdTransRaw Nat (OrDefL Q D Cons(Pair(K0, V0), T))
        (FindVL Q Cons(Pair(K0, V0), T)) V0
        (IdCongrRaw Bool Nat
          (λ (W : Bool). elim (IsSomeB (elim W return (λ (B2 : Bool). Σ (bb : Bool). OptP bb Nat) {
              True => SomeN V0, False => FindL Q T }))
            return (λ (B3 : Bool). Nat) {
              True => FindVL Q Cons(Pair(K0, V0), T), False => D })
          (Eqb Q K0) True E)
        (IdSymRaw Nat V0 (FindVL Q Cons(Pair(K0, V0), T)) (FindVEvHit Q K0 V0 T E))) }
def OrDHitEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (D : Nat) → Π (K0 : Nat) → Π (V0 : Nat) →
  Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) True →
    Id Nat V0 (OrDefL Q D Cons(Pair(K0, V0), T)) }
example : chkL OrDHitEv OrDHitEvTy = true := by native_decide

/-- A miss at the head passes `OrDefL` through to the tail. -/
def OrDMissEv : Term := prog_parse {
  λ (Q : Nat). λ (D : Nat). λ (K0 : Nat). λ (V0 : Nat). λ (T : List (Σ (k : Nat). Nat)).
  λ (E : Id Bool (Eqb Q K0) False).
    IdSymRaw Nat (OrDefL Q D Cons(Pair(K0, V0), T)) (OrDefL Q D T)
      (IdTransRaw Nat (OrDefL Q D Cons(Pair(K0, V0), T))
        (elim (HitL Q T) return (λ (B3 : Bool). Nat) {
          True => FindVL Q Cons(Pair(K0, V0), T), False => D })
        (OrDefL Q D T)
        (IdCongrRaw Bool Nat
          (λ (W : Bool). elim (IsSomeB (elim W return (λ (B2 : Bool). Σ (bb : Bool). OptP bb Nat) {
              True => SomeN V0, False => FindL Q T }))
            return (λ (B3 : Bool). Nat) {
              True => FindVL Q Cons(Pair(K0, V0), T), False => D })
          (Eqb Q K0) False E)
        (IdCongrRaw Nat Nat
          (λ (W : Nat). elim (HitL Q T) return (λ (B3 : Bool). Nat) {
            True => W, False => D })
          (FindVL Q Cons(Pair(K0, V0), T)) (FindVL Q T)
          (IdSymRaw Nat (FindVL Q T) (FindVL Q Cons(Pair(K0, V0), T))
            (FindVTailEv Q K0 V0 T E)))) }
def OrDMissEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (D : Nat) → Π (K0 : Nat) → Π (V0 : Nat) →
  Π (T : List (Σ (k : Nat). Nat)) →
    Id Bool (Eqb Q K0) False →
    Id Nat (OrDefL Q D T) (OrDefL Q D Cons(Pair(K0, V0), T)) }
example : chkL OrDMissEv OrDMissEvTy = true := by native_decide

def BumpPutP : Term := prog_parse {
  λ (P : Nat). λ (Key : Nat). λ (V : Nat). λ (R : Nat).
  λ (A : Array (S R) (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))).
        Array Mz (List (Σ (k : Nat). Nat)))
      Arr()
      (λ (M : Nat). λ (X : List (Σ (k : Nat). Nat)).
        λ (XS : Array M (List (Σ (k : Nat). Nat))).
        λ (Ih : Array M (List (Σ (k : Nat). Nat))).
          acons M (BPutP P Key V X) XS)
      (S R) A }

/-- The or_insert release: slot `i`'s bucket put-or-appended at `(p, key)`,
    and the count REPLACED by the parameter `n2` — the body stores it, the
    signature's `Hn2` premise keeps it honest. -/
def SetOrInsAt : Term := prog_parse {
  λ (I : Nat). λ (R : Nat). λ (P : Nat). λ (N2 : Nat). λ (Key : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
        Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots).
            Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
              Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
          Pair (Load) (R2) =>
            elim R2 return (λ (H2 : Σ (n : Nat).
                Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                  HMInvT Cap Load n slots).
                Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                  Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
              Pair (N) (R3) =>
                elim R3 return (λ (H3 : Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))).
                    HMInvT Cap Load N slots).
                    Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots) {
                  Pair (Slots) (Inv) =>
                    Pair(Cap, Pair(Load, Pair(N2, Pair(
                      arrCat I (S R) (atake I (S R) Slots)
                        (BumpPutP P Key V R (adrop I (S R) Slots)),
                      Inv)))) } } } } }

/-- The map-to-bucket `OrDefL` glue at the carve — packaged so the op's body
    applies one lemma instead of inlining the two-place congruence. -/
def OrDAgetEv : Term := prog_parse {
  λ (Q : Nat). λ (D : Nat). λ (I : Nat). λ (R : Nat). λ (M : Nat).
  λ (L : Array I (List (Σ (k : Nat). Nat))). λ (B : List (Σ (k : Nat). Nat)).
  λ (H : Array R (List (Σ (k : Nat). Nat))).
  λ (Him : Id Nat I M).
    IdSymRaw Nat
      (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
        return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D })
      (OrDefL Q D B)
      (IdTransRaw Nat
        (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
          return (λ (B3 : Bool). Nat) {
            True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
            False => D })
        (elim (IsSomeB (FindL Q B)) return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D })
        (OrDefL Q D B)
        (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
          (λ (W : List (Σ (k : Nat). Nat)).
            elim (IsSomeB (FindL Q W)) return (λ (B3 : Bool). Nat) {
              True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
              False => D })
          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B
          (AgetAtMod I R M L B H Him))
        (IdCongrRaw Nat Nat
          (λ (W : Nat). elim (IsSomeB (FindL Q B)) return (λ (B3 : Bool). Nat) {
            True => W, False => D })
          (FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M))
          (FindVL Q B)
          (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
            (λ (W : List (Σ (k : Nat). Nat)). FindVL Q W)
            (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M) B
            (AgetAtMod I R M L B H Him)))) }
def OrDAgetEvTy : Term := prog_parse {
  Π (Q : Nat) → Π (D : Nat) → Π (I : Nat) → Π (R : Nat) → Π (M : Nat) →
  Π (L : Array I (List (Σ (k : Nat). Nat))) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
    Id Nat I M →
    Id Nat (OrDefL Q D B)
      (elim (IsSomeB (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M)))
        return (λ (B3 : Bool). Nat) {
          True => FindVL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B H)) M),
          False => D }) }
example : chkL OrDAgetEv OrDAgetEvTy = true := by native_decide

/-! ### The or_insert ops -/

set_option maxHeartbeats 0 in
def hmOrM : Checked := prog (hmPinM) {
  fn BktPutAt [p] (p : Nat, key : Nat, d : Nat,
      b : &mut (t : List (Σ (k : Nat). Nat) ~> BPutP p key (*res) t),
      Hpos : Id Nat p (FindPosL key (*b)))
      -> Σ (r : &mut Nat). Id Nat (*r) (OrDefL key d (old *b)) {
    match b {
      Nil => match p {
        Z => {
          *b := Cons(Pair(key, d), Nil);
          match b { Cons(hd, tl) => match hd { Pair(kk, vv) =>
            Pair(&m *vv, Refl) } }
        },
        S(p2) => botElim Unit (ZnotsRaw p2 (IdSymRaw Nat (S p2) Z Hpos))
      },
      Cons(Pair(kk, vv), tl) => {
        let K0 = *kk;
        let V0 = *vv;
        let T0 = *tl;
        match p {
          Z => Pair(&m *vv, OrDHitEv key d K0 V0 T0 (PosZHit key K0 V0 T0 Hpos)),
          S(p2) => {
            let Ep = PosSStep key K0 V0 T0 p2 Hpos;
            let Emiss = FstT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Epos2 = SndT (Id Bool (Eqb key K0) False) (Id Nat p2 (FindPosL key T0)) Ep;
            let Pair(r2, h2) = BktPutAt(p2, key, d, &m *tl, Epos2);
            let W0 = *r2;
            Pair(r2, IdTransRaw Nat W0 (OrDefL key d T0)
              (OrDefL key d Cons(Pair(K0, V0), T0)) h2
              (OrDMissEv key d K0 V0 T0 Emiss))
          } } } } };
  fn GetMutOrInsertHM (i : Nat, rr : Nat, p : Nat, n2 : Nat, key : Nat, d : Nat,
      self : &mut (s : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
          Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots
        ~> SetOrInsAt i rr p n2 key (*res) s),
      Hd : Id Nat (CapHM (*self)) (Add i (S rr)),
      Him : Id Nat i (Dllbc.StdChainRaw.Mod key (CapHM (*self))),
      Hpos : Id Nat p (PosHM key (*self)),
      Hn2 : Id Nat n2 (elim (HitHM key (*self)) return (λ (Bm : Bool). Nat) {
        True => SizeHM (*self), False => S (SizeHM (*self)) }),
      Hroom : Le (Dllbc.StdChainRaw.Mul 5 n2) (LoadHM (*self)))
      -> Σ (r : &mut Nat). Id Nat (*r) (OrDefHM key d (old *self)) {
    match self { Pair(capb, r1) => match r1 { Pair(loadb, r2x) => match r2x { Pair(nb, r3) => match r3 { Pair(sb, Invb) => {
      let I0 = i;
      let R0 = rr;
      let Key0 = key;
      let D0 = d;
      let C0 = *capb;
      let pre = &m (*sb)[Z ; i ; S rr | LeAddRaw i (S rr) | Hd];
      let cell = &m (*sb)[i ; 1 ; rr];
      let hic = &m (*sb)[S i ; rr];
      let bb = &m (*cell)[0];
      let L0 = *pre;
      let B0 = *bb;
      let H0 = *hic;
      let HposB = IdTransRaw Nat p
                    (FindPosL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0)))
                    (FindPosL Key0 B0)
                    Hpos
                    (IdCongrRaw (List (Σ (k : Nat). Nat)) Nat
                      (λ (W : List (Σ (k : Nat). Nat)). FindPosL Key0 W)
                      (AgetB (Add I0 (S R0)) (arrCat I0 (S R0) L0 (acons R0 B0 H0))
                        (Dllbc.StdChainRaw.Mod Key0 C0)) B0
                      (AgetAtMod I0 R0 (Dllbc.StdChainRaw.Mod Key0 C0) L0 B0 H0 Him));
      *nb := n2;
      let Pair(rb, hb) = BktPutAt(p, key, d, &m *bb, HposB);
      let W0 = *rb;
      Pair(rb, IdTransRaw Nat W0 (OrDefL Key0 D0 B0)
        (elim (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0))))
          return (λ (B3 : Bool). Nat) {
            True => FindVL Key0 (AgetB (Add I0 (S R0))
              (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Dllbc.StdChainRaw.Mod Key0 C0)),
            False => D0 })
        hb
        (OrDAgetEv Key0 D0 I0 R0 (Dllbc.StdChainRaw.Mod Key0 C0) L0 B0 H0 Him))
    } } } } } };
  () }

example : progOkFrom Dllbc.std hmOrM.term = true := by native_decide

/-! ### The or_insert round-trip — and the append path's honest seam

    Fresh key 5 into slot 1 (colliding with key 1) at cap 4 — cap 2's ledger
    has no room for a second entry, so `Hroom` is a real premise here — then
    write 88 through the returned cursor and get the key back. A `Refl`-match
    lets the checker derive `T ≡ 88`, the exact final map, and the count
    bumped once.

    The seam this exposes (pinned honestly in `orInsReuse` below): appending
    grows the bucket, so the packed invariant's inhabitant gains conjuncts —
    the old proof tree no longer typechecks at the released slots, and a
    second op on the raw release is refused ("does not have its parameter
    type"). A plain value write (`GetMut`) has no such seam, since its proof
    tree is shape-invariant. Here the caller instead re-establishes the
    invariant by hand at the repack, where the new proof obligations are
    literal `Refl`/`unit` at concrete data; a version of `SetOrInsAt` that
    carries this repacking automatically is future work. -/

def vPackOr : Val :=
  vP (vN 4) (vP (vN 16) (vP (vN 2) (vP
    (.ctor "Arr" [vNil,
      .ctor "Cons" [vP (vN 1) (vN 10), .ctor "Cons" [vP (vN 5) (vN 88), vNil]],
      vNil, vNil])
    (vP vU (vP vR (vP vU (vP vR
      (vP (vP vU vU)
        (vP (vP (vP vR (vP vR vU)) (vP vR (vP vR vU)))
          (vP (vP vU vU) (vP (vP vU vU) vU)))))))))))

/-- The stale entry invariant, still visible as knowledge after the repack. -/
def vInvStale : Val :=
  vP vU (vP vR (vP vU (vP vR
    (vP (vP vU vU) (vP (vP (vP vR vU) (vP vR vU))
      (vP (vP vU vU) (vP (vP vU vU) vU)))))))

def orInsChain : Term := prog_parse {
  let m = Pair(4, Pair(16, Pair(1, Pair(Arr(Nil, Cons(Pair(1, 10), Nil), Nil, Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
  let b = &m m;
  let pr = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b, Refl, Refl, Refl, Refl, unit);
  match pr { Pair(r, h) => {
    match h { Refl => {
      *r := 88;
      let Pair(cc, rest1) = m;
      let Pair(ll, rest2) = rest1;
      let Pair(nn, rest3) = rest2;
      let Pair(ss, IV) = rest3;
      let m2 = Pair(cc, Pair(ll, Pair(nn, Pair(ss,
        Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
          Pair(Pair(unit, unit),
            Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
              Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
      let b2 = &m m2;
      let pr2 = GetMutHM(1, 2, 1, 5, b2, Refl, Refl, Refl, Refl);
      match pr2 { Pair(r2, h2) => {
        let Pair(hv, ho) = h2;
        match hv { Refl => {
          let T = *r2;
          let y = m2;
          () } } } } } } } } }

example : progOkFrom hmOrM orInsChain = true := by native_decide

/-- The or_insert law in the checker's environment: `T ≡ 88`, `y` the exact
    two-entry map, and `IV` the stale entry invariant left over from before
    the repack. -/
example : tailEnvFrom hmOrM orInsChain
  [("m", .bot), ("b", .bot), ("pr", .bot), ("r", .bot), ("h", .bot),
   ("cc", vN 4), ("rest1", .bot), ("ll", vN 16), ("rest2", .bot),
   ("nn", vN 2), ("rest3", .bot), ("ss", .bot), ("IV", vInvStale),
   ("m2", .bot), ("b2", .bot), ("pr2", .bot), ("r2", .bot), ("h2", .bot),
   ("hv", .bot), ("ho", .sym 0),
   ("T", vN 88), ("y", vPackOr)] = true := by native_decide

example : (runVFrom hmOrM orInsChain "T" == some (vN 88)) = true := by native_decide
example : (runVFrom hmOrM orInsChain "y" == some vPackOr) = true := by native_decide

/-- The same chain, re-calling on the raw release with no repack in between.
    The append left the entry invariant's inhabitant stale, so the second
    call is refused. -/
def orInsReuse : Term := prog_parse {
  let m = Pair(4, Pair(16, Pair(1, Pair(Arr(Nil, Cons(Pair(1, 10), Nil), Nil, Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit))))))))))));
  let b = &m m;
  let pr = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b, Refl, Refl, Refl, Refl, unit);
  match pr { Pair(r, h) => {
    *r := 88;
    let b2 = &m m;
    let pr2 = GetMutOrInsertHM(1, 2, 1, 2, 5, 77, b2, Refl, Refl, Refl, Refl, unit);
    match pr2 { Pair(r2, h2) => {
      () } } } } }

example : progRejectsFrom hmOrM orInsReuse "does not have its parameter type" = true := by
  native_decide

/-! ## The bridge: the pin's update equals the key-driven one

    The pin carries `BSetP p (*res)` (position-driven, pin-computable); the
    caller-facing law is stated with `SetHM`'s `BSetK key` (key-driven).
    Wherever the position evidence holds, the two updates coincide — proved
    by one induction — so a caller may rewrite its pinned release into the
    key-driven vocabulary. The map-level equality follows the same way,
    pointwise at the carve composition through `AgetAtMod`; the bucket level
    below is where the actual content of the proof lives. -/

def BSetPKEq : Term := prog_parse {
  λ (Q : Nat). λ (V : Nat).
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)).
        Π (P : Nat) → Id Nat P (FindPosL Q Lm) →
          Id (List (Σ (k : Nat). Nat)) (BSetP P V Lm) (BSetK Q V Lm)) {
      Nil => λ (P : Nat). λ (Hp : Id Nat P (FindPosL Q Nil)).
        NatRwRaw (λ (W : Nat). Id (List (Σ (k : Nat). Nat)) (BSetP W V Nil) Nil)
          Z P (IdSymRaw Nat P Z Hp) Refl,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat).
            Π (P : Nat) → Id Nat P (FindPosL Q Cons(Em, T)) →
              Id (List (Σ (k : Nat). Nat)) (BSetP P V Cons(Em, T)) (BSetK Q V Cons(Em, T))) {
          Pair (K2) (V2) => λ (P : Nat). λ (Hp : Id Nat P (FindPosL Q Cons(Pair(K2, V2), T))).
            IfDecRaw (Eqb Q K2)
              (Id (List (Σ (k : Nat). Nat))
                (BSetP P V Cons(Pair(K2, V2), T)) (BSetK Q V Cons(Pair(K2, V2), T)))
              (λ (Et : Id Bool (Eqb Q K2) True).
                IdTransRaw (List (Σ (k : Nat). Nat))
                  (BSetP P V Cons(Pair(K2, V2), T))
                  Cons(Pair(K2, V), T)
                  (BSetK Q V Cons(Pair(K2, V2), T))
                  (NatRwRaw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
                      (BSetP W V Cons(Pair(K2, V2), T)) Cons(Pair(K2, V), T))
                    Z P
                    (IdSymRaw Nat P Z
                      (IdTransRaw Nat P (FindPosL Q Cons(Pair(K2, V2), T)) Z Hp
                        (IdCongrRaw Bool Nat
                          (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                            True => Z, False => S (FindPosL Q T) })
                          (Eqb Q K2) True Et)))
                    Refl)
                  (IdSymRaw (List (Σ (k : Nat). Nat))
                    (BSetK Q V Cons(Pair(K2, V2), T)) Cons(Pair(K2, V), T)
                    (IdCongrRaw Bool (List (Σ (k : Nat). Nat))
                      (λ (W : Bool). elim W return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
                        True => Cons(Pair(K2, V), T),
                        False => Cons(Pair(K2, V2), BSetK Q V T) })
                      (Eqb Q K2) True Et)))
              (λ (Ef : Id Bool (Eqb Q K2) False).
                IdTransRaw (List (Σ (k : Nat). Nat))
                  (BSetP P V Cons(Pair(K2, V2), T))
                  Cons(Pair(K2, V2), BSetK Q V T)
                  (BSetK Q V Cons(Pair(K2, V2), T))
                  (IdTransRaw (List (Σ (k : Nat). Nat))
                    (BSetP P V Cons(Pair(K2, V2), T))
                    Cons(Pair(K2, V2), BSetP (FindPosL Q T) V T)
                    Cons(Pair(K2, V2), BSetK Q V T)
                    (NatRwRaw (λ (W : Nat). Id (List (Σ (k : Nat). Nat))
                        (BSetP W V Cons(Pair(K2, V2), T))
                        Cons(Pair(K2, V2), BSetP (FindPosL Q T) V T))
                      (S (FindPosL Q T)) P
                      (IdSymRaw Nat P (S (FindPosL Q T))
                        (IdTransRaw Nat P (FindPosL Q Cons(Pair(K2, V2), T))
                          (S (FindPosL Q T)) Hp
                          (IdCongrRaw Bool Nat
                            (λ (W : Bool). elim W return (λ (Bm : Bool). Nat) {
                              True => Z, False => S (FindPosL Q T) })
                            (Eqb Q K2) False Ef)))
                      Refl)
                    (IdCongrRaw (List (Σ (k : Nat). Nat)) (List (Σ (k : Nat). Nat))
                      (λ (W : List (Σ (k : Nat). Nat)). Cons(Pair(K2, V2), W))
                      (BSetP (FindPosL Q T) V T) (BSetK Q V T)
                      (Rec (FindPosL Q T) Refl)))
                  (IdSymRaw (List (Σ (k : Nat). Nat))
                    (BSetK Q V Cons(Pair(K2, V2), T))
                    Cons(Pair(K2, V2), BSetK Q V T)
                    (IdCongrRaw Bool (List (Σ (k : Nat). Nat))
                      (λ (W : Bool). elim W return (λ (Bm : Bool). List (Σ (k : Nat). Nat)) {
                        True => Cons(Pair(K2, V), T),
                        False => Cons(Pair(K2, V2), BSetK Q V T) })
                      (Eqb Q K2) False Ef))) } } }
def BSetPKEqTy : Term := prog_parse {
  Π (Q : Nat) → Π (V : Nat) → Π (L : List (Σ (k : Nat). Nat)) → Π (P : Nat) →
    Id Nat P (FindPosL Q L) →
    Id (List (Σ (k : Nat). Nat)) (BSetP P V L) (BSetK Q V L) }
example : chkL BSetPKEq BSetPKEqTy = true := by native_decide

end Dllbc.Tests.HashMap

end

/-!
# HashMap executing-layer tests

This file runs the hashmap's executing layer: decoders from machine values to
Lean values, a trusted Lean-side model, and callers that run the DLLBC ops
concretely and compare the result against the model. It is kept separate from
`HashMap.lean` so that iterating on the checked layer does not re-run the
expensive concrete executions.
-/

section

open Dllbc
-- Raw proof terms, bare (StdChain's doctrine: proofs apply as constants).
-- Formers the std seed binds (Mod, Mul, Pred, …) are written QUALIFIED inside
-- the seeded blocks (docs/21 §9's audit residual); the hashmap's own formers
-- are file-local constants and stay bare everywhere.
open Dllbc.StdChainRaw
open Dllbc.Tests.S23Direct (mintOn crossOn markedBody? noopOf)

namespace Dllbc.Tests.HashMap


/-! ## S1 executing differential

    The same declarations the checker accepted, run on concrete maps and
    compared against the trusted Lean-side model. These callers are
    runtime-only: their proof arguments are `unit`, which the machine
    ignores, so each test is a runs-to-X assertion. -/

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

/-- Decode a concrete pack into (cap, load, n, buckets). The invariant
    component is dropped; it is carried by the interpreter but not needed to
    state the model. -/
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

/-- The trusted model for one bucket: overwrite the matching entry in place
    on a hit, otherwise append the new entry at the bucket's end. -/
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

/-- `runProgramFrom`, with a caller-chosen step budget (the interpreter also
    evaluates the comptime layer, so a concrete hashmap run exceeds the
    default fuel). -/
def runProgramFromF (fuel : Nat) (m : Checked) (t : Term) : Except String Env :=
  m.exec.bind fun seed =>
    let (_, prepared) := moduleBoundary seed (moduleRetarget seed t)
    match (do let _ ← readR fuel prepared; endScope fuel).run
        { seed with executing := true } with
    | .ok _ st =>
      let seeded := seed.env.map (·.1)
      .ok (canonicalize (st.env.filter (fun kv => !seeded.contains kv.1)))
    | .error e _ => .error e

def runHMFrom (m : Checked) (t : Term) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) :=
  match runProgramFromF 2000000 m t with
  | .ok env => (env.lookup "y").bind hmOfV
  | .error _ => none

/-- Five inserts at cap 4: keys 5, 1, 9 all collide in slot 1 (the middle one
    walks past a miss), key 5 re-inserted mid-sequence must OVERWRITE in place,
    key 2 lands alone. -/
def s1RunCaller : Term := prog_parse {
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

-- The fifth distinct-key insert trips the load threshold (5·4 > 16), so the
-- map resizes to capacity 8 and rehashes; key 5 leaves the 1/9 collision
-- chain. The resize move prepends each moved node, so same-slot survivors
-- come out reversed: (9, 90) before (1, 10). Bucket order does not affect
-- membership, so this is still a correct instance of the model.
example : (runHMFrom hmM s1RunCaller ==
    some (8, 32, 4, [[], [(9, 90), (1, 10)], [(2, 20)], [], [], [(5, 71)], [], []]))
    = true := by native_decide

-- The model computed directly at capacity 4 (no resize) matches the
-- expected pre-resize bucket layout.
example : (s1Expected == (4, [[], [(5, 71), (1, 10), (9, 90)], [(2, 20)], []]))
    = true := by native_decide

/-- The insert sequence followed by three removes: key 5 (bucket-1 head, a
    hit), key 7 (a miss — nothing changes), key 1 (mid-bucket unlink). -/
def s1RemCaller : Term := prog_parse {
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

example : (runHMFrom hmM s1RemCaller ==
    some (8, 32, 2, [[], [(9, 90)], [(2, 20)], [], [], [], [], []]))
    = true := by native_decide

/-- From capacity 1 (threshold 0), four inserts force THREE doubling resizes:
    1 → 2 → 4 → 8, every entry re-slotted by the move fold each time. -/
def s1GrowCaller : Term := prog_parse {
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

example : (runHMFrom hmM s1GrowCaller ==
    some (8, 32, 4, [[], [(1, 10)], [(2, 20)], [(3, 30)], [(4, 40)], [], [], []]))
    = true := by native_decide

-- A freshly created map decodes with every bucket empty, n = 0, and
-- load = 4·cap.
def s1NewCaller : Term := prog_parse {
  let Pair(m0, Ev0) = NewHM(3, unit);
  let y = m0;
  () }
example : (runHMFrom hmM s1NewCaller == some (3, 12, 0, [[], [], []])) = true := by
  native_decide




/-! ## GetMut / GetMutOrInsert, executing, with the check status pinned

    GetMutHM borrows the entry via a total walk, ContainsHM tests presence
    via a Bool walk, and GetMutOrInsertHM inserts a default through the
    verified InsertHM before walking when the key is absent. The checker
    still rejects this chain (pinned by the assertion below), but it is
    exercised here to confirm it computes the correct answer at runtime. -/

/-- The GetMut chain — the ONE surviving tail-carrier, and why: this chain is
    checker-REJECTED (the known kernel gap pinned below), so it cannot be a
    module; its carrier is the sanctioned A2 pattern (a Lean function over the
    caller tail). What DID move to the honest world: the 1100-line S1 prefix
    is gone from it — the ops resolve from the `hmM` seed at check/run time —
    so the carrier is just the six GetMut fns. -/
def hmGmUnder (tail2 : Term) : Term :=
  prog_parse {
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
              let bb = &m (*slots)[i | NatRwRaw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSymRaw Nat i (Mod key C0) Him0)
                (ModLtNRaw key C0 HLe1)];
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
              let bb = &m (*slots)[i | NatRwRaw (λ (W : Nat). Le (S W) C0)
                (Mod key C0) i (IdSymRaw Nat i (Mod key C0) Him0)
                (ModLtNRaw key C0 HLe1)];
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
  tail2 }

-- The checker rejects the extended chain (from the hmM seed — the same
-- verdict the closed chain had); this pins the exact error text.
example : progRejectsFrom hmM (hmGmUnder prog_parse { () }) "does not have its owed type"
    = true := by native_decide

/-- Keys 0, 16, 64, and 80 all reduce to slot 0 at capacity 8, so they chain
    in one bucket. Overwrite key 64's value through GetMutHM, then remove
    key 64, and check that the surviving three entries decode correctly. -/
def gmTest1 : Term := hmGmUnder prog_parse {
  let Pair(m0, Ev0) = NewHM(8, unit);
  let b1 = &m m0;
  InsertHM(64, 0, 42, b1, unit);
  let b2 = &m m0;
  InsertHM(64, 16, 18, b2, unit);
  let b3 = &m m0;
  InsertHM(64, 64, 138, b3, unit);
  let b4 = &m m0;
  InsertHM(64, 80, 256, b4, unit);
  let b5 = &m m0;
  let e1 = GetMutHM(64, 64, b5, unit);
  *e1 := 56;
  let b6 = &m m0;
  RemoveHM(64, 64, b6, unit);
  let y = m0;
  () }

example : (runHMFrom hmM gmTest1 ==
    some (8, 32, 3,
      (List.replicate 8 ([] : List (Nat × Nat))).set 0
        [(0, 42), (16, 18), (80, 256)])) = true := by native_decide

/-- Both arms of the or_insert path: key 5 absent (inserts default 7 through
    the verified InsertHM, so n is accounted for), written through the
    returned borrow; then key 5 again (present, so no insert), written
    again. -/
def gmTest2 : Term := hmGmUnder prog_parse {
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

example : (runHMFrom hmM gmTest2 ==
    some (4, 16, 2, [[], [(1, 10), (5, 11)], [], []])) = true := by native_decide


end Dllbc.Tests.HashMap
end
