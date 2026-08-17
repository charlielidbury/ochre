import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff
import Dllbc.Tests.Direct

/-!
# The hashmap flagship — a verified, resizable, in-place hashmap

`docs/13-hashmap-flagship.md` is the problem statement; the reference is the
Aeneas ICFP'22 case study vendored at `competitors/aeneas-hashmap/`. Layout:
slots are an array of association-list buckets, the hash is the identity, the
slot is `Mod key cap`, load factor 4/5, resize by doubling. The invariant is
packed in the container's type, so a `HashMap` value cannot exist broken.

Ground ported here rather than rediscovered: slot arithmetic from branch
`hm-probe-mod` (now in `StdLemmas`), the Σ(Bool) Option vocabulary from
`hm-probe-opt`, the element-borrow bucket surgery from `hm-probe-arrays`, and
the total or_insert-style walk from `hm-probe-getmut`.
-/

section

open Dllbc
open Dllbc.StdLemmas (LeRefl LeAdd LeAddL LeAddSucc LeTrans LeUpR LePredL
  LebTrueLe LebFalseGt AddSucc AddZero AddComm AddAssoc IdTrans IdCongr IdSym
  NatRw NatRwTy LeZeroEq LeAntisym BoolFT BoolTF Znots SInj Pred
  LeRwL LeRwR LeAddMonoL EqbRefl
  NextR NextC NextQ ModC Mod DivC Div StepInv StepInvTy ModCLt ModCLtTy
  ModLtN ModLtNTy ModDec ModDecTy
  Mul AddSwapL AddSwapLTy AddInterchange AddInterchangeTy MulSucc MulSuccTy
  MulAddR MulAddRTy MulTwoDouble MulTwoDoubleTy LeAddMonoR LeAddMonoRTy
  LeAddMono LeAddMonoTy LeMulR LeMulRTy Le5M4 Le5M4Ty FiveN4Zero FiveN4ZeroTy
  LeLebTrue LeLebTrueTy EqbTrueEq EqbTrueEqTy EqbSym EqbSymTy IfDec IfDecTy
  LedgerGrow LedgerGrowTy)

namespace Dllbc.Tests.HashMap

/-- Type-check a closed term against a closed type in the pure seed (as
    ArraySort's `chkL`). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

def pv (t : Term) : Term := Pure.nf 4000000 t

/-! ## (i) The slot arithmetic, ported from `hm-probe-mod` — green in `StdLemmas` -/

def modOf (a b : Nat) : Term := pv prog{ Mod %(Term.nat a) %(Term.nat b) }
def divOf (a b : Nat) : Term := pv prog{ Div %(Term.nat a) %(Term.nat b) }

example : (modOf 7 3).natOf? == some 1 := by native_decide
example : (modOf 6 3).natOf? == some 0 := by native_decide
example : (modOf 5 8).natOf? == some 5 := by native_decide
example : (modOf 3 0).natOf? == some 0 := by native_decide
example : (divOf 7 3).natOf? == some 2 := by native_decide

-- The Aeneas test's own keys at its own capacity: 0, 128, 1024, 1056 all land in
-- slot 0 of 32, which is what makes that test exercise the collision list.
example : (modOf 128 32).natOf? == some 0 := by native_decide
example : (modOf 1024 32).natOf? == some 0 := by native_decide
example : (modOf 1056 32).natOf? == some 0 := by native_decide
example : (modOf 1057 32).natOf? == some 1 := by native_decide

example : chkL StepInv StepInvTy = true := by native_decide
example : chkL ModCLt ModCLtTy = true := by native_decide
example : chkL ModLtN ModLtNTy = true := by native_decide
example : chkL ModDec ModDecTy = true := by native_decide

/-! ## (ii) The ledger arithmetic -/

example : chkL AddSwapL AddSwapLTy = true := by native_decide
example : chkL AddInterchange AddInterchangeTy = true := by native_decide
example : chkL MulSucc MulSuccTy = true := by native_decide
example : chkL MulAddR MulAddRTy = true := by native_decide
example : chkL MulTwoDouble MulTwoDoubleTy = true := by native_decide
example : chkL LeAddMonoR LeAddMonoRTy = true := by native_decide
example : chkL LeAddMono LeAddMonoTy = true := by native_decide
example : chkL LeMulR LeMulRTy = true := by native_decide
example : chkL Le5M4 Le5M4Ty = true := by native_decide
example : chkL FiveN4Zero FiveN4ZeroTy = true := by native_decide
example : chkL LeLebTrue LeLebTrueTy = true := by native_decide
example : chkL EqbTrueEq EqbTrueEqTy = true := by native_decide
example : chkL EqbSym EqbSymTy = true := by native_decide
example : chkL IfDec IfDecTy = true := by native_decide
example : chkL LedgerGrow LedgerGrowTy = true := by native_decide

-- `Mul` computes, and the ledger inequality is the intended integer restatement:
-- `5n ≤ 4c ⟺ n ≤ ⌊4c/5⌋`, spot-checked at the resize boundary.
example : (pv prog{ Mul 4 8 }).natOf? == some 32 := by native_decide
-- cap 32: threshold 25 (= ⌊128/5⌋). 5·25 ≤ 128 holds, 5·26 ≤ 128 does not.
example : chkL prog{ unit } prog{ Le (Mul 5 25) (Mul 4 32) } = true := by native_decide
example : chkL prog{ unit } prog{ Le (Mul 5 26) (Mul 4 32) } = false := by native_decide
example : (pv prog{ Div (Mul 4 32) 5 }).natOf? == some 25 := by native_decide

/-! ## (iii) The slot write, ported from `hm-probe-mod`'s carve probe: the index
    and residue are minted across a CALL returning a Σ (comptime spellings fail
    the occurs check), then the carve cites the returned equation. -/

def slotDecls : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let Pair(i, Pair(r, hd)) = SlotOf(h, n, Hne);
    let pre = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | hd];
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
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn SlotWrite (h : Nat, n : Nat, v : Nat, Hne : Le (S Z) n,
                slots : &mut (Array n Nat)) -> Unit {
    let Pair(i, Pair(r, hd)) = SlotOf(h, n, Hne);
    let pre = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | hd];
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

/-! ## (iv) The elim sugar reads its element type (ported patch, `hm-probe-opt`
    commit 6b5a724e): recursion over `List (Σ (k : Nat). Nat)` — a bucket —
    checks through the sugar. These two were the probe's minimal failures. -/

example : chkL prog{
    λ (B : List (Σ (k : Nat). Nat)).
      elim B return (λ (Bm : List (Σ (k : Nat). Nat)). Nat) {
        Nil => Z,
        Cons (E) (T) Rec => Rec } }
  prog{ Π (B : List (Σ (k : Nat). Nat)) → Nat } = true := by native_decide

example : chkL prog{
    λ (B : List (List Nat)).
      elim B return (λ (Bm : List (List Nat)). Nat) {
        Nil => Z,
        Cons (E) (T) Rec => Rec } }
  prog{ Π (B : List (List Nat)) → Nat } = true := by native_decide

/-! ## (v) SHAPE PROBES — the two load-bearing unknowns, answered by assertion

    The packed container stands or falls on (a) take-and-refill of a Σ-pack with
    a `Σ0` invariant tail through `&mut self` — including whether the destructure
    REFINES the entry σ, so `old *self` claims compute — and (b) through-borrow
    navigation of the same pack for the borrow-returning ops. Nothing in the
    probe branches ever destructured a dependent pack. -/

def whyP (t : Term) : String :=
  match checkProgram t prog{ Unit } with
  | .ok _ => "ACCEPTED"
  | .error e => "REJECTED: " ++ e

/-- A pure identity on a `Le` proof. A destructured Σ0 tail comes back at a
    CAPITAL binder, and a bare capital citation in a constructor argument is
    fenced (`cannot be ⇒-moved`) even where the component's mode is comptime —
    but an APPLICATION in the same position is ⇝-computed, and the real code's
    repacked invariants are lemma applications anyway. `KeepLe` is the minimal
    such application, for the probes. -/
def KeepLe : Term := prog{ λ (A : Nat). λ (B : Nat). λ (H : Le A B). H }

/-- (a1) Round-trip: take the pack, rebuild it, refill. The proof component is
    re-supplied through `KeepLe` — see its docstring for why. -/
def packRoundtrip : Term := prog{
  fn Touch (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(n, Pair(w, KeepLe n w Hw));
    () };
  () }
example : progOk packRoundtrip = true := by native_decide

/-- (a2) THE REFINEMENT QUESTION: does `old *self` compute through the
    destructure? If matching refines the entry σ to `Pair(σn, …)`, both sides
    of the returned equation reduce to `σn` and `Refl` closes it. -/
def FstOf : Term := prog{
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

/-- (a3) A REAL update under the packed proof: bump both components; the proof
    transports by conversion (`Le (S n) (S w) ⇝ Le n w`). -/
def packBump : Term := prog{
  fn BumpBoth (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(S(n), Pair(S(w), KeepLe n w Hw));
    () };
  () }
example : progOk packBump = true := by native_decide

-- …and the lying refill is REFUSED: `Hw : Le n w` does not inhabit `Le (S n) w`.
def packBumpLie : Term := prog{
  fn BumpLie (self : &mut (Σ (n : Nat). Σ0 (w : Nat). Le n w)) -> Unit {
    let Pair(n, Pair(w, Hw)) = *self;
    *self := Pair(S(n), Pair(w, KeepLe n w Hw));
    () };
  () }
example : progOk packBumpLie = false := by native_decide

/-- (a4) The Insert SKELETON at a toy invariant: take the pack, mint the slot
    across a call, carve the slots ARRAY (a local, after the take), push into
    the bucket through the element borrow, repack, refill. -/
def packCarve : Term := prog{
  fn SlotOf (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Id Nat n (Add i (S r)) {
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn Ins0 (key : Nat, val : Nat,
           self : &mut (Σ (cap : Nat).
             Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap)) -> Unit {
    let Pair(cap, Pair(slots, Hcap)) = *self;
    let Pair(i, Pair(r, hd)) = SlotOf(key, cap, Hcap);
    let sb = &m slots;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let bb = &m (*cell)[0];
    let tl = *bb;
    *bb := Cons(Pair(key, val), tl);
    *self := Pair(cap, Pair(slots, KeepLe 1 cap Hcap));
    () };
  () }
example : progOk packCarve = true := by native_decide

/-- The toy pack's cap projection — pure, over the VALUE. -/
def FstCap : Term := prog{
  λ (P : Σ (cap : Nat). Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap).
    elim P return (λ (Pm : Σ (cap : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap). Nat) {
      Pair (Cap) (R1) => Cap } }

/-- The packed proof, extracted by comptime projection. A through-borrow match
    binds the Σ0 tail to STATE (a borrow), which a ⇝-position cannot read — so
    invariant clauses are snapshotted off `*self` BEFORE the destructure. -/
def PackCapLe : Term := prog{
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
    Pair(Mod h n, ModDec (Mod h n) n (ModLtN h n Hne))
  };
  fn Nav (key : Nat,
          self : &mut (Σ (cap : Nat).
            Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). Le (S Z) cap)) -> &mut Nat {
    let Hle1 = PackCapLe (*self);
    match self {
      Pair(cap, r1) => match r1 {
        Pair(slots, Hcap) => {
          -- A bare deref TAKES the payload, even a Nat's (the exit audit is
          -- per-leaf and found the hole) — so the read is an explicit
          -- take-and-refill, and the local Nat then copies freely.
          let c = *cap;
          *cap := c;
          let Pair(i, Pair(r, hd)) = SlotOf(key, c, Hle1);
          let pre = &m (*slots)[Z ; i ; S r | LeAdd i (S r) | hd];
          let cell = &m (*slots)[i ; 1 ; r];
          let bb = &m (*cell)[0];
          match bb {
            Nil => { *bb := Cons(Pair(key, 0), Nil);
                     match bb { Nil => (), Cons(hd2, tl2) =>
                       match hd2 { Pair(kk, vv) => &m *vv } } },
            Cons(hd2, tl2) => match hd2 { Pair(kk, vv) => &m *vv }
          } } } } };
  () }
example : progOk packNav = true := by native_decide

/-! ## (vi) The Σ(Bool) Option vocabulary (`hm-probe-opt`) and the bucket specs -/

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }

/-- `Opt T` — the option type at payload `T`. The kernel has no Option (that
    decision is closed; `hm-option-kernel` is the parked road-not-taken). -/
def Opt : Term := prog{ λ (T : Type). Σ (b : Bool). OptP b T }

/-- `Some`/`None` at `Nat`, v1's value type. -/
def SomeN : Term := prog{ λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog{ Pair(False, unit) }

example : chkL prog{ SomeN 5 } prog{ Opt Nat } = true := by native_decide
example : chkL NoneN prog{ Opt Nat } = true := by native_decide
example : chkL prog{ Pair(True, unit) } prog{ Opt Nat } = false := by native_decide

/-- Bucket lookup: first match wins, `None` past the end. The `Opt`-typed
    listRec over entries — the recursion the ported elim sugar exists for. -/
def FindL : Term := prog{
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Opt Nat) {
      Nil => NoneN,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Opt Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Opt Nat) {
              True => SomeN V2,
              False => Rec } } } }

def IsSomeB : Term := prog{
  λ (O : Σ (b : Bool). OptP b Nat).
    elim O return (λ (Om : Σ (b : Bool). OptP b Nat). Bool) {
      Pair (Bb) (P2) => Bb } }

/-- `HitL q l` — is `q` present? Defined THROUGH `FindL` so the two can never
    disagree. -/
def HitL : Term := prog{
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)). IsSomeB (FindL Q L) }

/-- Bucket length (`Std.lenFn` is monomorphic at `List Nat`). -/
def LenE : Term := prog{
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

-- They compute.
example : chkL prog{ Refl } prog{ Id (Opt Nat)
  (FindL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) (SomeN 30) } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat)
  (FindL 9 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) NoneN } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat)
  (FindL 3 Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) (SomeN 10) } = false := by native_decide
example : chkL prog{ Refl } prog{ Id Bool
  (HitL 3 Cons(Pair(3, 30), Nil)) True } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat
  (LenE Cons(Pair(1, 10), Cons(Pair(3, 30), Nil))) 2 } = true := by native_decide

/-! ## (vii) The slots-level spec functions

    `AgetB` is OUR getter, not the kernel's `aget`: `aget` reduces only on a
    literal `Arr` (no `acons`/`arrCat` step), so nothing about it at a carve
    composition is provable. `AgetB` is an `arrRec` fold, computes on the cons
    view, and every crossing lemma about it is an ordinary induction. -/

def AgetB : Term := prog{
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
def TotalE : Term := prog{
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat)
      Z
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))). λ (Ih : Nat).
          Add (LenE H) Ih)
      M A }

example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (AgetB 3 Arr(Nil, Cons(Pair(5, 7), Nil), Nil) 1) Cons(Pair(5, 7), Nil) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (List (Σ (k : Nat). Nat))
  (AgetB 3 Arr(Nil, Cons(Pair(5, 7), Nil), Nil) 0) Nil } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat
  (TotalE 3 Arr(Nil, Cons(Pair(5, 7), Nil), Cons(Pair(1, 2), Cons(Pair(3, 4), Nil)))) 3 }
  = true := by native_decide

/-! ## (viii) The packed invariant

    `HMInv`'s clauses (13-hashmap-flagship.md, content fixed): `Le 1 cap`; every
    entry in slot `i` has `Mod key cap = i`; `n` equals the total entry count;
    `load` is the 4/5 threshold ledger for `cap` — carried Div-free as
    `load = 4·cap` with occupancy `5·n ≤ load` (see the StdLemmas ledger note).

    PLUS one clause the listed four do not name but the fixed op specs force:
    keys within a bucket are pairwise DISTINCT (`NodupB`). Aeneas' own invariant
    has it (`slot_t_inv`'s pairwise-distinct conjunct), and both Remove's and
    resize's pointwise Find equations are FALSE without it: removing the first
    of two same-key entries surfaces the shadowed one, and rehashing reorders
    same-key entries, so `FindRem`/Insert-through-resize would each need it
    anyway. Recorded as a deviation-by-necessity, mirroring the reference. -/

def AllKeysMod : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Nat (Mod K2 Cap) I }) × Rec } }

def NodupB : Term := prog{
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Bool (HitL K2 T) False }) × Rec } }

/-- One slot's obligations: hashed here, and duplicate-free. -/
def SlotInv : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    AllKeysMod Cap I L × NodupB L }

/-- `SlotInv` folded over the array from starting index `I0` — the index rides
    as a fold argument so the crossing lemmas can generalize it. -/
def SlotsFrom : Term := prog{
  λ (Cap : Nat). λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))). λ (I0 : Nat).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat → Type)
      (λ (I2 : Nat). Unit)
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Nat → Type). λ (I2 : Nat).
          SlotInv Cap I2 H × Ih (S I2))
      M A I0 }

def HMInvT : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
    λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
      Le (S Z) Cap ×
      (Id Nat Load (Mul 4 Cap) ×
      (Le (Mul 5 N) Load ×
      (Id Nat N (TotalE Cap Slots) ×
      SlotsFrom Cap Cap Slots Z))) }

/-- THE CONTAINER. The invariant is packed in the type: a `HashMap` value
    cannot exist broken, every op's invariant-preservation proof is returning a
    well-typed pack, and it survives opaque group ends. -/
def HashMapT : Term := prog{
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots }

/-! A concrete inhabitant, as the invariant's own compute test: cap 2, load 8,
    one entry (key 3 in slot 1 — `Mod 3 2 = 1`). -/

def hmEx : Term := prog{
  Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) }

example : chkL hmEx HashMapT = true := by native_decide

-- …and the invariant is not vacuous: the same pack with the entry in the WRONG
-- slot (key 3 in slot 0) is refused — the `Mod` clause has no `Refl`.
example : chkL prog{
  Pair(2, Pair(8, Pair(1, Pair(Arr(Cons(Pair(3, 30), Nil), Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)), Pair(Pair(unit, unit),
        unit)))))))))) } HashMapT = false := by native_decide

-- …a lying count (n = 2 with one entry) is refused.
example : chkL prog{
  Pair(2, Pair(8, Pair(2, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) } HashMapT = false := by native_decide

-- …and a bucket with a DUPLICATE key is refused by the Nodup clause.
example : chkL prog{
  Pair(2, Pair(8, Pair(2, Pair(Arr(Nil, Cons(Pair(3, 30), Cons(Pair(3, 31), Nil))),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, Pair(Refl, unit)),
        Pair(Refl, Pair(Refl, unit))), unit)))))))))) } HashMapT = false := by native_decide

-- The ledger clause is live: cap 1 has threshold 0 (5·1 ≤ 4 fails), so a
-- one-entry map at capacity 1 cannot be packed…
example : chkL prog{
  Pair(1, Pair(4, Pair(1, Pair(Arr(Cons(Pair(0, 9), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)), unit))))))))) }
  HashMapT = false := by native_decide

-- …while the empty map at capacity 1 can.
example : chkL prog{
  Pair(1, Pair(4, Pair(Z, Pair(Arr(Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), unit))))))))) } HashMapT = true := by native_decide

/-! ## (ix) The map-level spec functions — pure, over the pack

    Each is a nested Σ-elim down the container; the motive spells the suffix
    telescope at each level (the elim sugar reads `A`/`B` off the motive's
    binder type syntactically — `SortedHead`'s precedent). -/

def CapHM : Term := prog{
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) => Cap } }

def SizeHM : Term := prog{
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
def FindHM : Term := prog{
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

def HitHM : Term := prog{
  λ (Q : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    IsSomeB (FindHM Q Hm) }

/-! The model updates (fixed content): `FindIns` is `Some v` at `key`, the old
    answer elsewhere; `FindRem` is `None` at `key`; the size updates state the
    "bumped/decremented iff" via a spec function, not a conditional Π. -/

def FindIns : Term := prog{
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (Eqb Q Key) return (λ (Bm : Bool). Opt Nat) {
      True => SomeN V,
      False => FindHM Q Hm } }

def FindRem : Term := prog{
  λ (Q : Nat). λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (Eqb Q Key) return (λ (Bm : Bool). Opt Nat) {
      True => NoneN,
      False => FindHM Q Hm } }

def SizeIns : Term := prog{
  λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Key Hm) return (λ (Bm : Bool). Nat) {
      True => SizeHM Hm,
      False => S(SizeHM Hm) } }

def SizeRem : Term := prog{
  λ (Key : Nat).
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim (HitHM Key Hm) return (λ (Bm : Bool). Nat) {
      True => Pred (SizeHM Hm),
      False => SizeHM Hm } }

-- They compute on the concrete inhabitant: key 3 is present with 30, key 5
-- shares its bucket and misses, key 4 hits the empty bucket.
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 3 %hmEx) (SomeN 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 5 %hmEx) NoneN } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindHM 4 %hmEx) NoneN } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeHM %hmEx) 1 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindIns 3 5 9 %hmEx) (SomeN 30) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindIns 5 5 9 %hmEx) (SomeN 9) } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id (Opt Nat) (FindRem 3 3 %hmEx) NoneN } = true := by
  native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeIns 5 %hmEx) 2 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeIns 3 %hmEx) 1 } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeRem 3 %hmEx) Z } = true := by native_decide
example : chkL prog{ Refl } prog{ Id Nat (SizeRem 5 %hmEx) 1 } = true := by native_decide

/-! ## (x) Projecting the invariant's clauses

    Generic product projections first (`A × B` converts with the spelled
    `Σ (Hx : A). B` — `SortedHead`'s precedent), then the five named clause
    projections every op body opens with. -/

def FstT : Term := prog{
  λ (A : Type). λ (B : Type). λ (P : Σ (Hx : A). B).
    elim P return (λ (Q : Σ (Hx : A). B). A) { Pair (X) (Y) => X } }
def FstTTy : Term := prog{ Π (A : Type) → Π (B : Type) → (Σ (Hx : A). B) → A }

def SndT : Term := prog{
  λ (A : Type). λ (B : Type). λ (P : Σ (Hx : A). B).
    elim P return (λ (Q : Σ (Hx : A). B). B) { Pair (X) (Y) => Y } }
def SndTTy : Term := prog{ Π (A : Type) → Π (B : Type) → (Σ (Hx : A). B) → B }

example : chkL FstT FstTTy = true := by native_decide
example : chkL SndT SndTTy = true := by native_decide

def InvLe1 : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Le (S Z) Cap)
      (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
        (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi }
def InvLe1Ty : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Le (S Z) Cap }

def InvLoad : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (Hi : HMInvT Cap Load N Slots).
    FstT (Id Nat Load (Mul 4 Cap))
      (Le (Mul 5 N) Load × (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))
      (SndT (Le (S Z) Cap)
        (Id Nat Load (Mul 4 Cap) × (Le (Mul 5 N) Load ×
          (Id Nat N (TotalE Cap Slots) × SlotsFrom Cap Cap Slots Z))) Hi) }
def InvLoadTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Id Nat Load (Mul 4 Cap) }

def InvLedger : Term := prog{
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
def InvLedgerTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Le (Mul 5 N) Load }

def InvCount : Term := prog{
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
def InvCountTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    HMInvT Cap Load N Slots → Id Nat N (TotalE Cap Slots) }

def InvSlots : Term := prog{
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
def InvSlotsTy : Term := prog{
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
    induction on the LEFT part. -/

def AgetBCatMid : Term := prog{
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
def AgetBCatMidTy : Term := prog{
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) M) B }

def AgetBCatLo : Term := prog{
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
def AgetBCatLoTy : Term := prog{
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (J : Nat) → Le (S J) M →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) J)
      (AgetB M L J) }

def AgetBCatHi : Term := prog{
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
def AgetBCatHiTy : Term := prog{
  Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (D : Nat) → Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id (List (Σ (k : Nat). Nat))
      (AgetB (Add M (S R)) (arrCat M (S R) L (acons R B H)) (Add M (S D)))
      (AgetB R H D) }

example : chkL AgetBCatMid AgetBCatMidTy = true := by native_decide
example : chkL AgetBCatLo AgetBCatLoTy = true := by native_decide
example : chkL AgetBCatHi AgetBCatHiTy = true := by native_decide

/-- `CountArrCat`'s shape for the entry counter. -/
def TotalArrCat : Term := prog{
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
          IdTrans Nat
            (Add (LenE H2) (TotalE (Add K Q) (arrCat K Q T X)))
            (Add (LenE H2) (Add (TotalE K T) (TotalE Q X)))
            (Add (Add (LenE H2) (TotalE K T)) (TotalE Q X))
            (IdCongr Nat Nat (λ (X2 : Nat). Add (LenE H2) X2)
              (TotalE (Add K Q) (arrCat K Q T X))
              (Add (TotalE K T) (TotalE Q X)) Ih)
            (IdSym Nat (Add (Add (LenE H2) (TotalE K T)) (TotalE Q X))
              (Add (LenE H2) (Add (TotalE K T) (TotalE Q X)))
              (AddAssoc (LenE H2) (TotalE K T) (TotalE Q X))))
      M L }
def TotalArrCatTy : Term := prog{
  Π (Q : Nat) → Π (X : Array Q (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
    Id Nat (TotalE (Add M Q) (arrCat M Q L X))
           (Add (TotalE M L) (TotalE Q X)) }

/-- Collapse a stuck Bool-elim whose scrutinee has an equation — the transport
    every pointwise-Find branch performs. -/
def BoolRwT : Term := prog{
  λ (T : Type). λ (X : T). λ (Y : T). λ (B : Bool). λ (E : Id Bool B True).
    IdCongr Bool T (λ (W : Bool). boolRec (λ (W2 : Bool). T) X Y W) B True E }
def BoolRwTTy : Term := prog{
  Π (T : Type) → Π (X : T) → Π (Y : T) → Π (B : Bool) → Id Bool B True →
    Id T (boolRec (λ (W2 : Bool). T) X Y B) X }

def BoolRwF : Term := prog{
  λ (T : Type). λ (X : T). λ (Y : T). λ (B : Bool). λ (E : Id Bool B False).
    IdCongr Bool T (λ (W : Bool). boolRec (λ (W2 : Bool). T) X Y W) B False E }
def BoolRwFTy : Term := prog{
  Π (T : Type) → Π (X : T) → Π (Y : T) → Π (B : Bool) → Id Bool B False →
    Id T (boolRec (λ (W2 : Bool). T) X Y B) Y }

/-- `a ≤ b` and `a ≠ b` make `a` STRICTLY below `b` — the frame case's
    trichotomy converter. -/
def LeNeLt : Term := prog{
  λ (A : Nat). elim A return (λ (Az : Nat).
      Π (B : Nat) → Le Az B → Id Bool (Eqb Az B) False → Le (S Az) B) {
    Z => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le Z Bz → Id Bool (Eqb Z Bz) False → Le (S Z) Bz) {
        Z => λ (H : Le Z Z). λ (E : Id Bool (Eqb Z Z) False).
          botElim (Le (S Z) Z) (BoolTF E),
        S (B2) Ihb => λ (H : Le Z (S B2)). λ (E : Id Bool (Eqb Z (S B2)) False). unit },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le (S A2) Bz → Id Bool (Eqb (S A2) Bz) False →
          Le (S (S A2)) Bz) {
        Z => λ (H : Le (S A2) Z). λ (E : Id Bool (Eqb (S A2) Z) False).
          botElim (Le (S (S A2)) Z) H,
        S (B2) Ihb => λ (H : Le (S A2) (S B2)). λ (E : Id Bool (Eqb (S A2) (S B2)) False).
          Ih B2 H E } } }
def LeNeLtTy : Term := prog{
  Π (A : Nat) → Π (B : Nat) → Le A B → Id Bool (Eqb A B) False → Le (S A) B }

example : chkL TotalArrCat TotalArrCatTy = true := by native_decide
example : chkL BoolRwT BoolRwTTy = true := by native_decide
example : chkL BoolRwF BoolRwFTy = true := by native_decide
example : chkL LeNeLt LeNeLtTy = true := by native_decide

/-! ### `SlotsFrom` across the carve: three extractors and the reglue. The fold's
    starting index is generalized through every induction (no per-depth
    ladders); the step arms pay one `AddSucc` transport each. -/

def SFCatLo : Term := prog{
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
def SFCatLoTy : Term := prog{
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotsFrom Cap M L I }

def SFCatMid : Term := prog{
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
            NatRw (λ (W : Nat). SlotInv Cap W B) (Add K (S I)) (S (Add K I))
              (AddSucc K I)
              (Ih (S I)
                (SndT (SlotInv Cap I H2)
                  (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs)))
      M L }
def SFCatMidTy : Term := prog{
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotInv Cap (Add M I) B }

def SFCatHi : Term := prog{
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
            NatRw (λ (W : Nat). SlotsFrom Cap R H (S W)) (Add K (S I)) (S (Add K I))
              (AddSucc K I)
              (Ih (S I)
                (SndT (SlotInv Cap I H2)
                  (SlotsFrom Cap (Add K (S R)) (arrCat K (S R) T (acons R B H)) (S I)) Hs)))
      M L }
def SFCatHiTy : Term := prog{
  Π (Cap : Nat) → Π (R : Nat) → Π (B : List (Σ (k : Nat). Nat)) →
  Π (H : Array R (List (Σ (k : Nat). Nat))) →
  Π (M : Nat) → Π (L : Array M (List (Σ (k : Nat). Nat))) →
  Π (I : Nat) →
    SlotsFrom Cap (Add M (S R)) (arrCat M (S R) L (acons R B H)) I →
    SlotsFrom Cap R H (S (Add M I)) }

example : chkL SFCatLo SFCatLoTy = true := by native_decide
example : chkL SFCatMid SFCatMidTy = true := by native_decide
example : chkL SFCatHi SFCatHiTy = true := by native_decide

/-- The reglue: lo's invariants, the NEW cell's `SlotInv` at the boundary
    index, hi's invariants — back to the whole composition. Every op's
    invariant-preservation exit goes through this. -/
def SFCatGlue : Term := prog{
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
                   (NatRw (λ (W : Nat). SlotInv Cap W B) (S (Add K I)) (Add K (S I))
                     (IdSym Nat (Add K (S I)) (S (Add K I)) (AddSucc K I)) Hm)
                   (NatRw (λ (W : Nat). SlotsFrom Cap R H (S W)) (S (Add K I)) (Add K (S I))
                     (IdSym Nat (Add K (S I)) (S (Add K I)) (AddSucc K I)) Hh)))
      M L }
def SFCatGlueTy : Term := prog{
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
    one is proven here over Π-bound state, so the walk's body only APPLIES them
    at its snapshots. `OptN`/`BktT` abbreviate the two types (splices — never
    used at an elim motive, where the sugar reads syntax). -/

def OptN : Term := prog{ Σ (bb : Bool). OptP bb Nat }
def BktT : Term := prog{ List (Σ (k : Nat). Nat) }

/-- The bucket-level model update: `Some v` at `key`, the old bucket answer
    elsewhere. -/
def BFindIns : Term := prog{
  λ (Q : Nat). λ (Key : Nat). λ (V : Nat). λ (L : BktT).
    elim (Eqb Q Key) return (λ (Bm : Bool). OptN) {
      True => SomeN V,
      False => FindL Q L } }

/-- The bucket-level length update: unchanged on a hit, bumped on a miss. -/
def BLenIns : Term := prog{
  λ (Key : Nat). λ (L : BktT).
    elim (HitL Key L) return (λ (Bm : Bool). Nat) {
      True => LenE L,
      False => S(LenE L) } }

/-- Pull `S` out of a stuck Bool-elim. -/
def BoolPushS : Term := prog{
  λ (X : Nat). λ (Y : Nat). λ (B : Bool).
    boolRec (λ (Bm : Bool).
        Id Nat (boolRec (λ (W2 : Bool). Nat) (S X) (S Y) Bm)
               (S (boolRec (λ (W2 : Bool). Nat) X Y Bm)))
      Refl Refl B }
def BoolPushSTy : Term := prog{
  Π (X : Nat) → Π (Y : Nat) → Π (B : Bool) →
    Id Nat (boolRec (λ (W2 : Bool). Nat) (S X) (S Y) B)
           (S (boolRec (λ (W2 : Bool). Nat) X Y B)) }
example : chkL BoolPushS BoolPushSTy = true := by native_decide

/-- HIT branch, presence: the head key equals `key`, so the bucket answers. -/
def HitEvHit : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRw (λ (W : Nat). Id Bool True (HitL Key (Cons(Pair(W, V0), T0)))) Key K0
      (IdSym Nat K0 Key (EqbTrueEq K0 Key E))
      (IdSym Bool (HitL Key (Cons(Pair(Key, V0), T0))) True
        (IdCongr OptN Bool IsSomeB
          (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
          (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbRefl Key)))) }
def HitEvHitTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Bool True (HitL Key (Cons(Pair(K0, V0), T0))) }
example : chkL HitEvHit HitEvHitTy = true := by native_decide

/-- HIT branch, the pointwise Find equation: overwrite in place. -/
def PtEvHit : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (V1 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRw (λ (W : Nat).
        Π (Q : Nat) → Id OptN
          (FindL Q (Cons(Pair(W, V1), T0)))
          (BFindIns Q Key V1 (Cons(Pair(W, V0), T0))))
      Key K0
      (IdSym Nat K0 Key (EqbTrueEq K0 Key E))
      (λ (Q : Nat).
        IfDec (Eqb Q Key)
          (Id OptN (FindL Q (Cons(Pair(Key, V1), T0)))
                   (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))))
          (λ (E2 : Id Bool (Eqb Q Key) True).
            IdTrans OptN (FindL Q (Cons(Pair(Key, V1), T0))) (SomeN V1)
              (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
              (BoolRwT OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2)
              (IdSym OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))) (SomeN V1)
                (BoolRwT OptN (SomeN V1)
                  (FindL Q (Cons(Pair(Key, V0), T0))) (Eqb Q Key) E2)))
          (λ (E2 : Id Bool (Eqb Q Key) False).
            IdTrans OptN (FindL Q (Cons(Pair(Key, V1), T0))) (FindL Q T0)
              (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
              (BoolRwF OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2)
              (IdSym OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0))) (FindL Q T0)
                (IdTrans OptN (BFindIns Q Key V1 (Cons(Pair(Key, V0), T0)))
                  (FindL Q (Cons(Pair(Key, V0), T0))) (FindL Q T0)
                  (BoolRwF OptN (SomeN V1)
                    (FindL Q (Cons(Pair(Key, V0), T0))) (Eqb Q Key) E2)
                  (BoolRwF OptN (SomeN V0) (FindL Q T0) (Eqb Q Key) E2))))) }
def PtEvHitTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Π (Q : Nat) → Id OptN
      (FindL Q (Cons(Pair(K0, V1), T0)))
      (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0))) }
example : chkL PtEvHit PtEvHitTy = true := by native_decide

/-- HIT branch, the length equation: present key, length unchanged. -/
def LnEvHit : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (V1 : Nat). λ (Key : Nat). λ (T0 : BktT).
  λ (E : Id Bool (Eqb K0 Key) True).
    NatRw (λ (W : Nat). Id Nat (LenE (Cons(Pair(W, V1), T0)))
                               (BLenIns Key (Cons(Pair(W, V0), T0)))) Key K0
      (IdSym Nat K0 Key (EqbTrueEq K0 Key E))
      (IdSym Nat (BLenIns Key (Cons(Pair(Key, V0), T0)))
        (LenE (Cons(Pair(Key, V0), T0)))
        (BoolRwT Nat (LenE (Cons(Pair(Key, V0), T0)))
          (S (LenE (Cons(Pair(Key, V0), T0))))
          (HitL Key (Cons(Pair(Key, V0), T0)))
          (IdCongr OptN Bool IsSomeB
            (FindL Key (Cons(Pair(Key, V0), T0))) (SomeN V0)
            (BoolRwT OptN (SomeN V0) (FindL Key T0) (Eqb Key Key) (EqbRefl Key))))) }
def LnEvHitTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) → Π (T0 : BktT) →
    Id Bool (Eqb K0 Key) True →
    Id Nat (LenE (Cons(Pair(K0, V1), T0))) (BLenIns Key (Cons(Pair(K0, V0), T0))) }
example : chkL LnEvHit LnEvHitTy = true := by native_decide

/-- MISS branch, presence: the head is not `key`, so presence delegates to the
    tail — on both the old and the new bucket. -/
def HitEvMiss : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (H2 : Bool).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hh : Id Bool H2 (HitL Key T0)).
    IdTrans Bool H2 (HitL Key T0) (HitL Key (Cons(Pair(K0, V0), T0)))
      Hh
      (IdSym Bool (HitL Key (Cons(Pair(K0, V0), T0))) (HitL Key T0)
        (IdCongr OptN Bool IsSomeB
          (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
          (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
            (IdTrans Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSym Key K0) E)))) }
def HitEvMissTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (H2 : Bool) →
    Id Bool (Eqb K0 Key) False →
    Id Bool H2 (HitL Key T0) →
    Id Bool H2 (HitL Key (Cons(Pair(K0, V0), T0))) }
example : chkL HitEvMiss HitEvMissTy = true := by native_decide

/-- MISS branch, the pointwise Find equation lifted through the untouched head. -/
def PtEvMiss : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (V1 : Nat). λ (Key : Nat).
  λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hp : Π (Q : Nat) → Id OptN (FindL Q T1) (BFindIns Q Key V1 T0)).
    λ (Q : Nat).
      IfDec (Eqb Q Key)
        (Id OptN (FindL Q (Cons(Pair(K0, V0), T1)))
                 (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0))))
        (λ (E2 : Id Bool (Eqb Q Key) True).
          IdTrans OptN (FindL Q (Cons(Pair(K0, V0), T1))) (FindL Q T1)
            (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0)))
            (BoolRwF OptN (SomeN V0) (FindL Q T1) (Eqb Q K0)
              (IdTrans Bool (Eqb Q K0) (Eqb Key K0) False
                (IdCongr Nat Bool (λ (W : Nat). Eqb W K0) Q Key (EqbTrueEq Q Key E2))
                (IdTrans Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSym Key K0) E)))
            (IdTrans OptN (FindL Q T1) (SomeN V1)
              (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0)))
              (IdTrans OptN (FindL Q T1) (BFindIns Q Key V1 T0) (SomeN V1)
                (Hp Q)
                (BoolRwT OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2))
              (IdSym OptN (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0))) (SomeN V1)
                (BoolRwT OptN (SomeN V1)
                  (FindL Q (Cons(Pair(K0, V0), T0))) (Eqb Q Key) E2))))
        (λ (E2 : Id Bool (Eqb Q Key) False).
          IdTrans OptN (FindL Q (Cons(Pair(K0, V0), T1)))
            (FindL Q (Cons(Pair(K0, V0), T0)))
            (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0)))
            (IdCongr OptN OptN
              (λ (W : OptN). boolRec (λ (W2 : Bool). OptN) (SomeN V0) W (Eqb Q K0))
              (FindL Q T1) (FindL Q T0)
              (IdTrans OptN (FindL Q T1) (BFindIns Q Key V1 T0) (FindL Q T0)
                (Hp Q)
                (BoolRwF OptN (SomeN V1) (FindL Q T0) (Eqb Q Key) E2)))
            (IdSym OptN (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0)))
              (FindL Q (Cons(Pair(K0, V0), T0)))
              (BoolRwF OptN (SomeN V1)
                (FindL Q (Cons(Pair(K0, V0), T0))) (Eqb Q Key) E2))) }
def PtEvMissTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) →
  Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    (Π (Q : Nat) → Id OptN (FindL Q T1) (BFindIns Q Key V1 T0)) →
    Π (Q : Nat) → Id OptN
      (FindL Q (Cons(Pair(K0, V0), T1)))
      (BFindIns Q Key V1 (Cons(Pair(K0, V0), T0))) }
example : chkL PtEvMiss PtEvMissTy = true := by native_decide

/-- MISS branch, the length equation lifted through the head. -/
def LnEvMiss : Term := prog{
  λ (K0 : Nat). λ (V0 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hl : Id Nat (LenE T1) (BLenIns Key T0)).
    IdTrans Nat (S (LenE T1)) (S (BLenIns Key T0))
      (BLenIns Key (Cons(Pair(K0, V0), T0)))
      (IdCongr Nat Nat (λ (W : Nat). S W) (LenE T1) (BLenIns Key T0) Hl)
      (IdSym Nat (BLenIns Key (Cons(Pair(K0, V0), T0))) (S (BLenIns Key T0))
        (IdTrans Nat (BLenIns Key (Cons(Pair(K0, V0), T0)))
          (boolRec (λ (W2 : Bool). Nat)
            (LenE (Cons(Pair(K0, V0), T0)))
            (S (LenE (Cons(Pair(K0, V0), T0))))
            (HitL Key T0))
          (S (BLenIns Key T0))
          (IdCongr Bool Nat
            (λ (W : Bool). boolRec (λ (W2 : Bool). Nat)
              (LenE (Cons(Pair(K0, V0), T0)))
              (S (LenE (Cons(Pair(K0, V0), T0)))) W)
            (HitL Key (Cons(Pair(K0, V0), T0))) (HitL Key T0)
            (IdCongr OptN Bool IsSomeB
              (FindL Key (Cons(Pair(K0, V0), T0))) (FindL Key T0)
              (BoolRwF OptN (SomeN V0) (FindL Key T0) (Eqb Key K0)
                (IdTrans Bool (Eqb Key K0) (Eqb K0 Key) False (EqbSym Key K0) E))))
          (BoolPushS (LenE T0) (S (LenE T0)) (HitL Key T0)))) }
def LnEvMissTy : Term := prog{
  Π (K0 : Nat) → Π (V0 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    Id Nat (LenE T1) (BLenIns Key T0) →
    Id Nat (LenE (Cons(Pair(K0, V0), T1))) (BLenIns Key (Cons(Pair(K0, V0), T0))) }
example : chkL LnEvMiss LnEvMissTy = true := by native_decide

/-- MISS branch, the Nodup head clause: `K0` absent from the tail stays absent
    after inserting a DIFFERENT key into it. -/
def NdEvMiss : Term := prog{
  λ (K0 : Nat). λ (V1 : Nat). λ (Key : Nat). λ (T0 : BktT). λ (T1 : BktT).
  λ (E : Id Bool (Eqb K0 Key) False).
  λ (Hp : Π (Q : Nat) → Id OptN (FindL Q T1) (BFindIns Q Key V1 T0)).
  λ (Hn : Id Bool (HitL K0 T0) False).
    IdTrans Bool (HitL K0 T1) (HitL K0 T0) False
      (IdCongr OptN Bool IsSomeB (FindL K0 T1) (FindL K0 T0)
        (IdTrans OptN (FindL K0 T1) (BFindIns K0 Key V1 T0) (FindL K0 T0)
          (Hp K0)
          (BoolRwF OptN (SomeN V1) (FindL K0 T0) (Eqb K0 Key) E)))
      Hn }
def NdEvMissTy : Term := prog{
  Π (K0 : Nat) → Π (V1 : Nat) → Π (Key : Nat) → Π (T0 : BktT) → Π (T1 : BktT) →
    Id Bool (Eqb K0 Key) False →
    (Π (Q : Nat) → Id OptN (FindL Q T1) (BFindIns Q Key V1 T0)) →
    Id Bool (HitL K0 T0) False →
    Id Bool (HitL K0 T1) False }
example : chkL NdEvMiss NdEvMissTy = true := by native_decide

/-! ## (xiii) The map-level pointwise lift, and the pack builder -/

def LoadHM : Term := prog{
  λ (Hm : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
      Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots).
    elim Hm return (λ (H0 : Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
        Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots). Nat) {
      Pair (Cap) (R1) =>
        elim R1 return (λ (H1 : Σ (load : Nat). Σ (n : Nat).
            Σ0 (slots : Array Cap (List (Σ (k : Nat). Nat))). HMInvT Cap load n slots). Nat) {
          Pair (Load) (R2) => Load } } }

/-- The invariant, assembled by ONE application — a bare capital citation in a
    refill's constructor argument is fenced, an application is not, so every
    op's exit packs through this. -/
def MkInv : Term := prog{
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
  λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
  λ (H1 : Le (S Z) Cap). λ (H2 : Id Nat Load (Mul 4 Cap)).
  λ (H3 : Le (Mul 5 N) Load). λ (H4 : Id Nat N (TotalE Cap Slots)).
  λ (H5 : SlotsFrom Cap Cap Slots Z).
    Pair(H1, Pair(H2, Pair(H3, Pair(H4, H5)))) }
def MkInvTy : Term := prog{
  Π (Cap : Nat) → Π (Load : Nat) → Π (N : Nat) →
  Π (Slots : Array Cap (List (Σ (k : Nat). Nat))) →
    Le (S Z) Cap → Id Nat Load (Mul 4 Cap) → Le (Mul 5 N) Load →
    Id Nat N (TotalE Cap Slots) → SlotsFrom Cap Cap Slots Z →
    HMInvT Cap Load N Slots }
example : chkL MkInv MkInvTy = true := by native_decide

/-- Same-slot case of the pointwise lift: `q` hashes to the written slot, so
    both sides collapse to the bucket-level equation through `AgetBCatMid`. -/
def InsPtSame : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (V : Nat).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Hb : Π (Q : Nat) → Id OptN (FindL Q B1) (BFindIns Q Key V B0)).
  λ (Q : Nat).
  λ (Ej : Id Bool (Eqb (Mod Q (Add I (S R))) I) True).
    NatRw (λ (W : Nat).
        Id OptN
          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) W))
          (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) W)))
      I (Mod Q (Add I (S R)))
      (IdSym Nat (Mod Q (Add I (S R))) I (EqbTrueEq (Mod Q (Add I (S R))) I Ej))
      (IdTrans OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) I))
        (FindL Q B1)
        (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
        (IdCongr BktT OptN (λ (W : BktT). FindL Q W)
          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) I) B1
          (AgetBCatMid R B1 H I L))
        (IdTrans OptN (FindL Q B1) (BFindIns Q Key V B0)
          (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
          (Hb Q)
          (IdSym OptN
            (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I))
            (BFindIns Q Key V B0)
            (IdCongr BktT OptN (λ (W : BktT). BFindIns Q Key V W)
              (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H)) I) B0
              (AgetBCatMid R B0 H I L))))) }
def InsPtSameTy : Term := prog{
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (V : Nat) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    (Π (Q : Nat) → Id OptN (FindL Q B1) (BFindIns Q Key V B0)) →
    Π (Q : Nat) → Id Bool (Eqb (Mod Q (Add I (S R))) I) True →
    Id OptN
      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
        (Mod Q (Add I (S R)))))
      (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
        (Mod Q (Add I (S R))))) }
example : chkL InsPtSame InsPtSameTy = true := by native_decide

/-- Different-slot case: `q`'s bucket is untouched. `Eqb Q Key = True` is dead
    (equal keys share a slot); otherwise the slot is strictly left of the cell
    (`AgetBCatLo`) or strictly right (`ModDec` mints the offset, `AgetBCatHi`). -/
def InsPtDiff : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (V : Nat).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Him : Id Nat I (Mod Key (Add I (S R)))).
  λ (Q : Nat).
  λ (Ej : Id Bool (Eqb (Mod Q (Add I (S R))) I) False).
    IfDec (Eqb Q Key)
      (Id OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
          (Mod Q (Add I (S R)))))
        (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
          (Mod Q (Add I (S R))))))
      (λ (E2 : Id Bool (Eqb Q Key) True).
        botElim
          (Id OptN
            (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
              (Mod Q (Add I (S R)))))
            (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
              (Mod Q (Add I (S R))))))
          (BoolTF (IdTrans Bool True (Eqb (Mod Q (Add I (S R))) I) False
            (IdSym Bool (Eqb (Mod Q (Add I (S R))) I) True
              (IdTrans Bool (Eqb (Mod Q (Add I (S R))) I) (Eqb I I) True
                (IdCongr Nat Bool (λ (W : Nat). Eqb W I) (Mod Q (Add I (S R))) I
                  (IdTrans Nat (Mod Q (Add I (S R))) (Mod Key (Add I (S R))) I
                    (IdCongr Nat Nat (λ (W : Nat). Mod W (Add I (S R))) Q Key
                      (EqbTrueEq Q Key E2))
                    (IdSym Nat I (Mod Key (Add I (S R))) Him)))
                (EqbRefl I)))
            Ej)))
      (λ (E2 : Id Bool (Eqb Q Key) False).
        IfDec (Leb (Mod Q (Add I (S R))) I)
          (Id OptN
            (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
              (Mod Q (Add I (S R)))))
            (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
              (Mod Q (Add I (S R))))))
          (λ (El : Id Bool (Leb (Mod Q (Add I (S R))) I) True).
            IdTrans OptN
              (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                (Mod Q (Add I (S R)))))
              (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
              (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                (Mod Q (Add I (S R)))))
              (IdCongr BktT OptN (λ (W : BktT). FindL Q W)
                (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                  (Mod Q (Add I (S R))))
                (AgetB I L (Mod Q (Add I (S R))))
                (AgetBCatLo R B1 H I L (Mod Q (Add I (S R)))
                  (LeNeLt (Mod Q (Add I (S R))) I
                    (LebTrueLe (Mod Q (Add I (S R))) I El) Ej)))
              (IdSym OptN
                (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                  (Mod Q (Add I (S R)))))
                (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
                (IdTrans OptN
                  (BFindIns Q Key V (AgetB (Add I (S R))
                    (arrCat I (S R) L (acons R B0 H)) (Mod Q (Add I (S R)))))
                  (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                    (Mod Q (Add I (S R)))))
                  (FindL Q (AgetB I L (Mod Q (Add I (S R)))))
                  (BoolRwF OptN (SomeN V)
                    (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                      (Mod Q (Add I (S R)))))
                    (Eqb Q Key) E2)
                  (IdCongr BktT OptN (λ (W : BktT). FindL Q W)
                    (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                      (Mod Q (Add I (S R))))
                    (AgetB I L (Mod Q (Add I (S R))))
                    (AgetBCatLo R B0 H I L (Mod Q (Add I (S R)))
                      (LeNeLt (Mod Q (Add I (S R))) I
                        (LebTrueLe (Mod Q (Add I (S R))) I El) Ej))))))
          (λ (El : Id Bool (Leb (Mod Q (Add I (S R))) I) False).
            elim (ModDec I (Mod Q (Add I (S R)))
                (LebFalseGt (Mod Q (Add I (S R))) I El)) return
              (λ (W : Σ (R2 : Nat). Id Nat (Mod Q (Add I (S R))) (Add I (S R2))).
                Id OptN
                  (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                    (Mod Q (Add I (S R)))))
                  (BFindIns Q Key V (AgetB (Add I (S R))
                    (arrCat I (S R) L (acons R B0 H)) (Mod Q (Add I (S R)))))) {
              Pair (D) (Hd) =>
                NatRw (λ (W : Nat).
                    Id OptN
                      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H)) W))
                      (BFindIns Q Key V (AgetB (Add I (S R))
                        (arrCat I (S R) L (acons R B0 H)) W)))
                  (Add I (S D)) (Mod Q (Add I (S R)))
                  (IdSym Nat (Mod Q (Add I (S R))) (Add I (S D)) Hd)
                  (IdTrans OptN
                    (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                      (Add I (S D))))
                    (FindL Q (AgetB R H D))
                    (BFindIns Q Key V (AgetB (Add I (S R))
                      (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                    (IdCongr BktT OptN (λ (W : BktT). FindL Q W)
                      (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
                        (Add I (S D)))
                      (AgetB R H D)
                      (AgetBCatHi R B1 H D I L))
                    (IdSym OptN
                      (BFindIns Q Key V (AgetB (Add I (S R))
                        (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                      (FindL Q (AgetB R H D))
                      (IdTrans OptN
                        (BFindIns Q Key V (AgetB (Add I (S R))
                          (arrCat I (S R) L (acons R B0 H)) (Add I (S D))))
                        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                          (Add I (S D))))
                        (FindL Q (AgetB R H D))
                        (BoolRwF OptN (SomeN V)
                          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                            (Add I (S D))))
                          (Eqb Q Key) E2)
                        (IdCongr BktT OptN (λ (W : BktT). FindL Q W)
                          (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
                            (Add I (S D)))
                          (AgetB R H D)
                          (AgetBCatHi R B0 H D I L))))) })) }
def InsPtDiffTy : Term := prog{
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (V : Nat) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    Id Nat I (Mod Key (Add I (S R))) →
    Π (Q : Nat) → Id Bool (Eqb (Mod Q (Add I (S R))) I) False →
    Id OptN
      (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
        (Mod Q (Add I (S R)))))
      (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
        (Mod Q (Add I (S R))))) }
example : chkL InsPtDiff InsPtDiffTy = true := by native_decide

/-- THE POINTWISE LIFT: the walk's bucket equation becomes Insert's whole-map
    equation, by deciding `q`'s slot against the written slot. -/
def InsPointwise : Term := prog{
  λ (I : Nat). λ (R : Nat). λ (Key : Nat). λ (V : Nat).
  λ (L : Array I BktT). λ (B0 : BktT). λ (B1 : BktT). λ (H : Array R BktT).
  λ (Him : Id Nat I (Mod Key (Add I (S R)))).
  λ (Hb : Π (Q : Nat) → Id OptN (FindL Q B1) (BFindIns Q Key V B0)).
    λ (Q : Nat).
      IfDec (Eqb (Mod Q (Add I (S R))) I)
        (Id OptN
          (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
            (Mod Q (Add I (S R)))))
          (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
            (Mod Q (Add I (S R))))))
        (InsPtSame I R Key V L B0 B1 H Hb Q)
        (InsPtDiff I R Key V L B0 B1 H Him Q) }
def InsPointwiseTy : Term := prog{
  Π (I : Nat) → Π (R : Nat) → Π (Key : Nat) → Π (V : Nat) →
  Π (L : Array I BktT) → Π (B0 : BktT) → Π (B1 : BktT) → Π (H : Array R BktT) →
    Id Nat I (Mod Key (Add I (S R))) →
    (Π (Q : Nat) → Id OptN (FindL Q B1) (BFindIns Q Key V B0)) →
    Π (Q : Nat) →
      Id OptN
        (FindL Q (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B1 H))
          (Mod Q (Add I (S R)))))
        (BFindIns Q Key V (AgetB (Add I (S R)) (arrCat I (S R) L (acons R B0 H))
          (Mod Q (Add I (S R))))) }
example : chkL InsPointwise InsPointwiseTy = true := by native_decide

/-! ## (xiv) `New`'s builder and its three lemmas, and the slot pack -/

/-- `n` empty buckets, by `acons` recursion (probe O2's shape). -/
def MkSlots : Term := prog{
  λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm (List (Σ (k : Nat). Nat))) {
    Z => Arr(),
    S (M) Rec => acons M Nil Rec } }

/-- Every slot of the fresh table satisfies its invariant (vacuously). -/
def SFMkSlots : Term := prog{
  λ (Cap : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Π (I : Nat) → SlotsFrom Cap Nz (MkSlots Nz) I) {
      Z => λ (I : Nat). unit,
      S (M) Ih => λ (I : Nat). Pair(Pair(unit, unit), Ih (S I)) } }
def SFMkSlotsTy : Term := prog{
  Π (Cap : Nat) → Π (N : Nat) → Π (I : Nat) → SlotsFrom Cap N (MkSlots N) I }
example : chkL SFMkSlots SFMkSlotsTy = true := by native_decide

/-- The fresh table holds nothing. -/
def TotalMkSlots : Term := prog{
  λ (N : Nat). elim N return (λ (Nz : Nat). Id Nat (TotalE Nz (MkSlots Nz)) Z) {
    Z => Refl,
    S (M) Ih => Ih } }
def TotalMkSlotsTy : Term := prog{
  Π (N : Nat) → Id Nat (TotalE N (MkSlots N)) Z }
example : chkL TotalMkSlots TotalMkSlotsTy = true := by native_decide

/-- Every slot of the fresh table reads back `Nil` — at ANY index, in range or
    not, which is why `New`'s find-spec needs no bound side-condition. -/
def AgetBMkSlots : Term := prog{
  λ (N : Nat).
    elim N return (λ (Nz : Nat).
        Π (J : Nat) → Id (List (Σ (k : Nat). Nat)) (AgetB Nz (MkSlots Nz) J) Nil) {
      Z => λ (J : Nat). Refl,
      S (M) Ih => λ (J : Nat).
        elim J return (λ (Jz : Nat).
            Id (List (Σ (k : Nat). Nat)) (AgetB (S M) (MkSlots (S M)) Jz) Nil) {
          Z => Refl,
          S (J2) Ihj => Ih J2 } } }
def AgetBMkSlotsTy : Term := prog{
  Π (N : Nat) → Π (J : Nat) →
    Id (List (Σ (k : Nat). Nat)) (AgetB N (MkSlots N) J) Nil }
example : chkL AgetBMkSlots AgetBMkSlotsTy = true := by native_decide

/-- The slot quadruple `SlotOfE` returns: index, residue, the carve equation,
    and — new over the probe's `SlotOf` — the identity tying the index to the
    hash, which the pointwise lift consumes as `Him`. -/
def SlotPack : Term := prog{
  λ (H : Nat). λ (N : Nat). λ (Hne : Le (S Z) N).
    elim (ModDec (Mod H N) N (ModLtN H N Hne)) return
        (λ (Q : Σ (R : Nat). Id Nat N (Add (Mod H N) (S R))).
          Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N)) {
      Pair (R0) (Hd0) => Pair(Mod H N, Pair(R0, Pair(Hd0, Refl))) } }
def SlotPackTy : Term := prog{
  Π (H : Nat) → Π (N : Nat) → Le (S Z) N →
    Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat N (Add i (S r))). Id Nat i (Mod H N) }
example : chkL SlotPack SlotPackTy = true := by native_decide

/-! ## (xv) THE S1 CHAIN — fixed-capacity map, full specs

    ArraySort's `arrUnder` shape: one Lean function building the declaration
    chain, the spec return types spliced so the lying twins share the bodies
    verbatim. `New`'s and `Insert`'s telescopes for the spliced types:
    NewHM: cap=0, HLe1=1.  InsertHM: fuel=0, key=1, val=2, self=3, Hfuel=4,
    Hroom=5. -/

def keyIv : Term := .var ⟨1, "key"⟩
def valIv : Term := .var ⟨2, "val"⟩
def selfIv : Term := .var ⟨3, "self"⟩

/-- A slot's invariant pair, by application (the constructor-argument fence). -/
def MkSlotInv : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (B : BktT).
  λ (H1 : AllKeysMod Cap I B). λ (H2 : NodupB B).
    Pair(H1, H2) }
def MkSlotInvTy : Term := prog{
  Π (Cap : Nat) → Π (I : Nat) → Π (B : BktT) →
    AllKeysMod Cap I B → NodupB B → SlotInv Cap I B }
example : chkL MkSlotInv MkSlotInvTy = true := by native_decide

/-- The trivial pointwise equation for a singleton bucket built from `Nil` —
    named so the Nil arm's component is an application, not a λ literal. -/
def PtEvNil : Term := prog{
  λ (Key : Nat). λ (V : Nat). λ (Q : Nat). Refl }
def PtEvNilTy : Term := prog{
  Π (Key : Nat) → Π (V : Nat) → Π (Q : Nat) →
    Id OptN (FindL Q (Cons(Pair(Key, V), Nil))) (BFindIns Q Key V Nil) }
example : chkL PtEvNil PtEvNilTy = true := by native_decide

def hmS1Under (nret iret tail : Term) : Term := prog{
  fn InsertInList [fuel] (fuel : Nat, cap : Nat, islot : Nat, key : Nat, val : Nat,
                          b : &mut (List (Σ (k : Nat). Nat)),
                          Hf : Le (LenE (*b)) fuel,
                          Hkm : Id Nat (Mod key cap) islot,
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
                *vv := val;
                Pair(True,
                  Pair(HitEvHit K0 V0 key T0 e,
                  Pair(PtEvHit K0 V0 val key T0 e,
                  Pair(LnEvHit K0 V0 val key T0 e,
                  Pair(Hak, Hnd)))))
              } else {
                let Pair(hit2, Pair(Hh2, Pair(Hpt2, Pair(Hln2, Pair(Hak3, Hnd3))))) =
                  InsertInList(f2, cap, islot, key, val, &m *tl, Hf, Hkm,
                    SndT (Id Nat (Mod K0 cap) islot) (AllKeysMod cap islot T0) Hak,
                    SndT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd);
                Pair(hit2,
                  Pair(HitEvMiss K0 V0 key T0 hit2 e Hh2,
                  Pair(PtEvMiss K0 V0 val key T0 (*tl) e Hpt2,
                  Pair(LnEvMiss K0 V0 key T0 (*tl) e Hln2,
                  Pair(Pair(FstT (Id Nat (Mod K0 cap) islot)
                              (AllKeysMod cap islot T0) Hak, Hak3),
                       Pair(NdEvMiss K0 val key T0 (*tl) e Hpt2
                              (FstT (Id Bool (HitL K0 T0) False) (NodupB T0) Hnd),
                            Hnd3))))))
              } }
          } } };
  fn SlotOfE (h : Nat, n : Nat, Hne : Le (S Z) n)
      -> Σ (i : Nat). Σ (r : Nat). Σ (hd : Id Nat n (Add i (S r))). Id Nat i (Mod h n) {
    SlotPack h n Hne };
  fn NewHM (cap : Nat, HLe1 : Le (S Z) cap) -> %nret {
    let Cap0 = cap;
    Pair(Pair(cap, Pair(Mul 4 cap, Pair(Z, Pair(MkSlots cap,
        MkInv cap (Mul 4 cap) Z (MkSlots cap) HLe1 Refl unit
          (IdSym Nat (TotalE cap (MkSlots cap)) Z (TotalMkSlots cap))
          (SFMkSlots cap cap Z))))),
      Pair(λ (Q : Nat).
             IdCongr (List (Σ (k : Nat). Nat)) (Σ (bb : Bool). OptP bb Nat)
               (λ (W : List (Σ (k : Nat). Nat)). FindL Q W)
               (AgetB Cap0 (MkSlots Cap0) (Mod Q Cap0)) Nil
               (AgetBMkSlots Cap0 (Mod Q Cap0)),
           Refl))
  };
  fn SlotUpd (fuel : Nat, cap : Nat, key : Nat, val : Nat,
              b : &mut (Array cap (List (Σ (k : Nat). Nat))),
              HLe1 : Le (S Z) cap,
              Hfl : Le (S (TotalE cap (*b))) fuel,
              Hsf : SlotsFrom cap cap (*b) Z)
      -> Σ (hit : Bool).
         Σ (Hh : Id Bool hit (IsSomeB (FindL key (AgetB cap (old *b) (Mod key cap))))).
         Σ (Hpt : Π (Q : Nat) → Id OptN (FindL Q (AgetB cap (*b) (Mod Q cap)))
              (BFindIns Q key val (AgetB cap (old *b) (Mod Q cap)))).
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
        let pre = &m (*b)[Z ; i ; S r | LeAdd i (S r) | hd];
        let cell = &m (*b)[i ; 1 ; r];
        let hic = &m (*b)[S i ; r];
        let bb = &m (*cell)[0];
        let L0 = *pre;
        let B0 = *bb;
        let H0 = *hic;
        let HsfL = SFCatLo cap r B0 H0 i L0 Z Hsf;
        let HsfM = NatRw (λ (W : Nat). SlotInv Cap0 W B0) (Add I0 Z) I0 (AddZero I0)
                     (SFCatMid cap r B0 H0 i L0 Z Hsf);
        let HsfH = SFCatHi cap r B0 H0 i L0 Z Hsf;
        let Hak0 = FstT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Hnd0 = SndT (AllKeysMod cap i B0) (NodupB B0) HsfM;
        let Htot0 = TotalArrCat (S r) (acons r B0 H0) i L0;
        let HlenB = LeRwR (LenE B0)
                      (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                      (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                      (IdSym Nat (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))) Htot0)
                      (LeTrans (LenE B0) (Add (LenE B0) (TotalE r H0))
                        (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                        (LeAdd (LenE B0) (TotalE r H0))
                        (LeAddL (Add (LenE B0) (TotalE r H0)) (TotalE i L0)));
        let HfB = LeTrans (LenE B0)
                    (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel
                    HlenB
                    (LePredL (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))) fuel Hfl);
        let Pair(hit2, Pair(Hh2, Pair(Hpt2, Pair(Hln2, Pair(Hak3, Hnd3))))) =
          InsertInList(fuel, cap, i, key, val, &m *bb, HfB,
            IdSym Nat i (Mod key cap) him, Hak0, Hnd0);
        let B1 = *bb;
        let Hit0 = hit2;
        let Htot1 = TotalArrCat (S r) (acons r B1 H0) i L0;
        let Hpt = InsPointwise i r key val L0 B0 B1 H0 him Hpt2;
        let HsIz = NatRw (λ (W : Nat). SlotInv Cap0 W B1) I0 (Add I0 Z)
                     (IdSym Nat (Add I0 Z) I0 (AddZero I0))
                     (MkSlotInv cap i B1 Hak3 Hnd3);
        let H5x = SFCatGlue cap r B1 H0 i L0 Z HsfL HsIz HsfH;
        let HhB = IdTrans Bool Hit0 (HitL Key0 B0)
                    (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                      (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 Cap0))))
                    Hh2
                    (IdSym Bool
                      (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                        (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 Cap0))))
                      (HitL Key0 B0)
                      (NatRw (λ (W : Nat). Id Bool
                          (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) W)))
                          (HitL Key0 B0))
                        I0 (Mod Key0 Cap0) Him0
                        (IdCongr (List (Σ (k : Nat). Nat)) Bool
                          (λ (W : List (Σ (k : Nat). Nat)). IsSomeB (FindL Key0 W))
                          (AgetB (Add I0 (S R0))
                            (arrCat I0 (S R0) L0 (acons R0 B0 H0)) I0) B0
                          (AgetBCatMid R0 B0 H0 I0 L0))));
        match e2 : hit2 {
          True => {
            let HitB0 = IdTrans Bool (HitL Key0 B0) Hit0 True
                          (IdSym Bool Hit0 (HitL Key0 B0) Hh2) e2;
            let HlenEq = IdTrans Nat (LenE B1) (BLenIns Key0 B0) (LenE B0)
                           Hln2
                           (BoolRwT Nat (LenE B0) (S (LenE B0)) (HitL Key0 B0) HitB0);
            let HtotEq = IdTrans Nat (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                           (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                           (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                           (IdTrans Nat
                             (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                             (Add (TotalE i L0) (Add (LenE B1) (TotalE r H0)))
                             (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                             Htot1
                             (IdCongr Nat Nat
                               (λ (W : Nat). Add (TotalE I0 L0) (Add W (TotalE R0 H0)))
                               (LenE B1) (LenE B0) HlenEq))
                           (IdSym Nat (TotalE cap (arrCat i (S r) L0 (acons r B0 H0)))
                             (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))) Htot0);
            Pair(True,
              Pair(IdTrans Bool True Hit0
                     (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                       (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 Cap0))))
                     (IdSym Bool Hit0 True e2) HhB,
              Pair(Hpt, Pair(HtotEq, H5x))))
          },
          False => {
            let HitB0F = IdTrans Bool (HitL Key0 B0) Hit0 False
                           (IdSym Bool Hit0 (HitL Key0 B0) Hh2) e2;
            let HlenEqF = IdTrans Nat (LenE B1) (BLenIns Key0 B0) (S (LenE B0))
                            Hln2
                            (BoolRwF Nat (LenE B0) (S (LenE B0)) (HitL Key0 B0) HitB0F);
            let HtotEqF = IdTrans Nat (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                            (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                            (S (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))))
                            (IdTrans Nat
                              (TotalE cap (arrCat i (S r) L0 (acons r B1 H0)))
                              (Add (TotalE i L0) (Add (LenE B1) (TotalE r H0)))
                              (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                              Htot1
                              (IdCongr Nat Nat
                                (λ (W : Nat). Add (TotalE I0 L0) (Add W (TotalE R0 H0)))
                                (LenE B1) (S (LenE B0)) HlenEqF))
                            (IdTrans Nat
                              (Add (TotalE i L0) (S (Add (LenE B0) (TotalE r H0))))
                              (S (Add (TotalE i L0) (Add (LenE B0) (TotalE r H0))))
                              (S (TotalE cap (arrCat i (S r) L0 (acons r B0 H0))))
                              (AddSucc (TotalE i L0) (Add (LenE B0) (TotalE r H0)))
                              (IdCongr Nat Nat (λ (W : Nat). S W)
                                (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                                (TotalE Cap0 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                                (IdSym Nat
                                  (TotalE Cap0 (arrCat I0 (S R0) L0 (acons R0 B0 H0)))
                                  (Add (TotalE I0 L0) (Add (LenE B0) (TotalE R0 H0)))
                                  Htot0)));
            Pair(False,
              Pair(IdTrans Bool False Hit0
                     (IsSomeB (FindL Key0 (AgetB (Add I0 (S R0))
                       (arrCat I0 (S R0) L0 (acons R0 B0 H0)) (Mod Key0 Cap0))))
                     (IdSym Bool Hit0 False e2) HhB,
              Pair(Hpt, Pair(HtotEqF, H5x))))
          }
        }
      };
  fn InsertHM (fuel : Nat, key : Nat, val : Nat,
               self : &mut (Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
                 Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots),
               Hfuel : Le (S (SizeHM (*self))) fuel,
               Hroom : Le (Mul 5 (S (SizeHM (*self)))) (LoadHM (*self)))
      -> %iret
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
            LeRwL fuel (S nn) (S (TotalE Cap0 SL0))
              (IdCongr Nat Nat (λ (W : Nat). S W) N0 (TotalE Cap0 SL0) HCnt)
              Hfuel,
            HSf);
        let SL1 = *sb;
        let Hit0 = hit2;
        match e2 : hit2 {
          True => {
            let H4x = IdTrans Nat nn (TotalE Cap0 SL0) (TotalE Cap0 SL1)
                        HCnt
                        (IdSym Nat (TotalE Cap0 SL1) (TotalE Cap0 SL0)
                          (IdTrans Nat (TotalE Cap0 SL1)
                            (boolRec (λ (W2 : Bool). Nat) (TotalE Cap0 SL0)
                              (S (TotalE Cap0 SL0)) Hit0)
                            (TotalE Cap0 SL0)
                            Htot2
                            (BoolRwT Nat (TotalE Cap0 SL0) (S (TotalE Cap0 SL0))
                              Hit0 e2)));
            *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
              MkInv cap load nn SL1 HLe1 HLoad HLed H4x Hsf2))));
            Pair(Hpt2,
              IdSym Nat
                (boolRec (λ (W2 : Bool). Nat) nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))))
                nn
                (BoolRwT Nat nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
                  (IdTrans Bool
                    (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
                    Hit0 True
                    (IdSym Bool Hit0
                      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))) Hh2)
                    e2)))
          },
          False => {
            let H4y = IdTrans Nat (S nn) (S (TotalE Cap0 SL0)) (TotalE Cap0 SL1)
                        (IdCongr Nat Nat (λ (W : Nat). S W) N0 (TotalE Cap0 SL0) HCnt)
                        (IdSym Nat (TotalE Cap0 SL1) (S (TotalE Cap0 SL0))
                          (IdTrans Nat (TotalE Cap0 SL1)
                            (boolRec (λ (W2 : Bool). Nat) (TotalE Cap0 SL0)
                              (S (TotalE Cap0 SL0)) Hit0)
                            (S (TotalE Cap0 SL0))
                            Htot2
                            (BoolRwF Nat (TotalE Cap0 SL0) (S (TotalE Cap0 SL0))
                              Hit0 e2)));
            *self := Pair(cap, Pair(load, Pair(S(nn), Pair(slots,
              MkInv cap load (S nn) SL1 HLe1 HLoad Hroom H4y Hsf2))));
            Pair(Hpt2,
              IdSym Nat
                (boolRec (λ (W2 : Bool). Nat) nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))))
                (S nn)
                (BoolRwF Nat nn (S nn)
                  (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
                  (IdTrans Bool
                    (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0))))
                    Hit0 False
                    (IdSym Bool Hit0
                      (IsSomeB (FindL Key0 (AgetB Cap0 SL0 (Mod Key0 Cap0)))) Hh2)
                    e2)))
          }
        }
      };
  %tail }

/-- `New`'s honest ensures: finds nothing, size zero. -/
def newRetHonest : Term := prog{
  Σ (hm : HashMapT). Σ0 (Hfind : Π (Q : Nat) → Id OptN (FindHM Q hm) NoneN).
  Id Nat (SizeHM hm) Z }

/-- `Insert`'s honest ensures — the two fixed conjuncts: the pointwise Find
    equation (subsuming Aeneas' found + frame in one total claim) and the size
    accounting via the `SizeIns` spec function. -/
def insRetHonest : Term := prog{
  Σ0 (Hpt : Π (Q : Nat) → Id OptN (FindHM Q (*%selfIv))
       (FindIns Q %keyIv %valIv (old *%selfIv))).
  Id Nat (SizeHM (*%selfIv)) (SizeIns %keyIv (old *%selfIv)) }

/-- THE S1 HEADLINE: the fixed-capacity chain checks as ONE program, against
    no table — walk, slot pack, New, Insert, full specs. -/
def s1Chain : Term := hmS1Under newRetHonest insRetHonest prog{ () }
example : progOk s1Chain = true := by native_decide


-- BISECTION P1: identity round-trip of the REAL container through &mut —
-- destructure, project the clauses, repack via MkInv, refill.
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

-- BISECTION P2a: carve, then refill with the UNTOUCHED entry clauses (typed at
-- the entry slots sigma) — isolates the audit-side segment-fold conversion.
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
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
    let cell = &m (*sb)[i ; 1 ; r];
    let hic = &m (*sb)[S i ; r];
    let bb = &m (*cell)[0];
    *self := Pair(cap, Pair(load, Pair(nn, Pair(slots,
      MkInv cap load nn SL0 HLe1 HLoad HLed HCnt HSf))));
    () };
  () }
-- PINNED LIMIT (the finding that shaped the op layer): the exit audit cannot
-- re-type a DEPENDENT pack whose array component is still SEGMENTED — the
-- entry clauses are typed at the whole-array sigma, the demanded tail
-- instantiates the raw segment-list value, and the two do not convert at the
-- audit even though the sigma/composition equation holds (s1P2c below). So
-- every op routes its carve through a CALLEE (SlotUpd) and packs the fresh
-- opaque sigma the group end mints — the function boundary is load-bearing,
-- exactly as ArraySort found for the flex-length carve.
example : progOk s1P2a = false := by native_decide

-- P2c/P2d: is the entry sigma definitionally the composition of the segment
-- sigmas, from a carve of a LOCAL owned array? Asked with an ascribed Refl.
def s1P2c : Term := prog{
  fn Touch (n : Nat, i : Nat, r : Nat, hd : Id Nat n (Add i (S r)),
            a : Array n (List (Σ (k : Nat). Nat))) -> Unit {
    let SL0 = a;
    let sb = &m a;
    let pre = &m (*sb)[Z ; i ; S r | LeAdd i (S r) | hd];
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

def runHM (t : Term) : Option (Nat × Nat × Nat × List (List (Nat × Nat))) :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok env => (env.lookup "y").bind hmOfV
  | .error _ => none

/-- Five inserts at cap 4: keys 5, 1, 9 all collide in slot 1 (the middle one
    walks past a miss), key 5 re-inserted mid-sequence must OVERWRITE in place,
    key 2 lands alone. -/
def s1RunCaller : Term := hmS1Under newRetHonest insRetHonest prog{
  let Pair(m0, Ev0) = NewHM(4, unit);
  let b1 = &m m0;
  InsertHM(9, 5, 70, b1, unit, unit);
  let b2 = &m m0;
  InsertHM(9, 1, 10, b2, unit, unit);
  let b3 = &m m0;
  InsertHM(9, 5, 71, b3, unit, unit);
  let b4 = &m m0;
  InsertHM(9, 9, 90, b4, unit, unit);
  let b5 = &m m0;
  InsertHM(9, 2, 20, b5, unit, unit);
  let y = m0;
  () }

def s1Expected : Nat × List (List (Nat × Nat)) :=
  modelRun 4 [(5, 70), (1, 10), (5, 71), (9, 90), (2, 20)]

example : (runHM s1RunCaller ==
    some (4, 16, s1Expected.1, s1Expected.2)) = true := by native_decide

-- …and the model itself is what we think it is (the differential is two-sided).
example : (s1Expected == (4, [[], [(5, 71), (1, 10), (9, 90)], [(2, 20)], []]))
    = true := by native_decide

-- The empty map runs and decodes: all buckets Nil, n = 0, load = 4·cap.
def s1NewCaller : Term := hmS1Under newRetHonest insRetHonest prog{
  let Pair(m0, Ev0) = NewHM(3, unit);
  let y = m0;
  () }
example : (runHM s1NewCaller == some (3, 12, 0, [[], [], []])) = true := by
  native_decide

end Dllbc.Tests.HashMap
end
