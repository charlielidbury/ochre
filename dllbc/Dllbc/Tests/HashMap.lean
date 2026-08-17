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

end Dllbc.Tests.HashMap
end
