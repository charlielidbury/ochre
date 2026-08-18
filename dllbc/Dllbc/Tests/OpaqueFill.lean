import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Opaque fill for escaping borrows — the acceptance suite

`docs/14-packed-borrows.md` is the problem statement. The rule that landed is one
sentence: **when the exit audit re-types a payload holding a borrow the callee
ISSUED into its result, the lent place is filled with a fresh σ at that borrow's
owed type, not with its current value.** A place under a borrow the callee KEEPS
still gets the actual payload. `spliceInFlight` in `Machine.lean` is the whole of
it; `auditObligation` carries the owed types in so it can.

## Why it had to change: four programs that checked and should not have

The two fills used to be one fill, and the audit could not tell a `&mut` handed
out onto a hashmap's VALUE cell from one handed out onto its KEY. Four escaping
borrows, four routes by which the caller's next write falsifies a claim the type
system had already accepted:

    escKey         onto a cell a packed invariant HASHES
    escExtent      onto an ARRAY'S EXTENT
    escPinned      onto a cell a Σ0 tail PINS to a literal
    escRuntimeDep  onto a cell a LATER RUNTIME BINDER'S TYPE needs

**The counterfactual, measured.** Revert `spliceInFlight`'s issued arm to
`| some p => pure p` and exactly these four go green again — `(escKey, escExtent,
escPinned, escRuntimeDep)` reads `(true, true, true, true)` before and
`(false, false, false, false)` after, and `escKeyExploit` reads `true` before and
`false` after. Nothing else in this file moves, and nothing else in the corpus
moves either: a full `lake build` across both rules differs by one σ number in one
needle (`AuditExemption`'s `siblingBadWrite`, ledgered at its site).

`escKeyExploit` is the end of that road and the acceptance form for the whole
fix — three parts, because two of them are about the MACHINE and only the third
is about the checker: the program RUNS, it runs to a pack whose stored `Refl` is
now a proof of `Id Nat 1 7`, and `chkL` of that exact value against its own
declared type is `false`. So the refusal is not a taste; the accepted program had
a value in it that does not inhabit its type.

## Why it is not over-eager

`escVal` is the same body one field over — the borrow escapes onto a VALUE cell —
and it still checks. That is the point of minting at the ISSUED BORROW's owed
type: an escaping `&mut Nat` owes back `Nat`, so the σ lands on the leaf and the
structure around it stays concrete enough for a packed invariant to compute over.
§6 is the same claim on the real `HMInvT`.

`wrVal1`/`wrKey1` fix the other side of the split: a NON-escaping value write is
accepted and a non-escaping key write is refused, and both were already right
before this change. The actual-payload fill was never the problem — escaping was
the whole of the gap. `g5Caller` is the caller-side control: an accepted callee,
a write through the borrow it returned, the group end, and the pack still good.

## What this does NOT fix — §7, pinned red

`GetMut` over an intrinsically packed container still cannot be written, and this
rule was never going to be what unblocked it. §7's bisection is the evidence and
it is kept here as the acceptance suite for whoever takes that on:

  * `bisB` — carve ONE element out of a packed container's array, with nothing
    escaping, nothing written, and no σ anywhere near a value leaf — is already
    red, while `bisF` and `bisI` (no opaque remainder left by the carve) are
    green. A partial carve leaves an opaque SLICE and an invariant that folds over
    the whole array cannot step past one. `HMInv` folds all `cap` slots, so every
    bucket borrow leaves `cap-1` of them opaque.
  * `layer1Val` — the same carve moved behind a callee boundary, with the inner
    group CLOSED and nothing escaping — is red because `endGroup`'s opaque release
    hands the array component back as a bare fresh σ at the COMPONENT's type,
    carrying no relation to what the packed proof names. That is the
    granularity mistake this fix exists to avoid, in the one place where the
    kernel has no better answer.

Neither moves under this rule, and neither is reachable by any refinement of it:
the exit audit is conversion, and no conversion crosses either gap.
-/

section

open Dllbc

namespace Dllbc.Tests.OpaqueFill

/-- Type-check a closed term against a closed type in the pure seed (ArraySort §i). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- What the EXECUTING machine leaves in one binding. The checker's verdict and
    the machine's value are different questions, and `escKeyExploit` is the
    program that needs both asked. -/
def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

/-! ## §1 The container

    `AllK7` is `AllKeysMod`'s value-insensitivity reduced to one clause: a fold
    over the array asserting every KEY is 7, reading nothing else. `PackDep1`/
    `PackDep2` pack it in the type at extent 1 and 2, so a value of either type
    cannot exist with a wrong key in it — which is exactly the property an
    escaping borrow onto a key cell destroys. -/

def AllK7 : Term := prog{
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

example : chkL prog{ Pair(Refl, Pair(Refl, unit)) }
  prog{ AllK7 2 Arr(Pair(7, 1), Pair(7, 2)) } = true := by native_decide
example : chkL prog{ Pair(Refl, Pair(Refl, unit)) }
  prog{ AllK7 2 Arr(Pair(7, 1), Pair(8, 2)) } = false := by native_decide

/-! ## §2 THE FOUR HOLES — escaping borrows that used to check

    Each is a `fn` handing the caller a `&mut Nat` aimed at a cell the pack's own
    type depends on. All four were GREEN before opaque fill. -/

/-- Onto a cell the packed invariant HASHES. -/
def escKey : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

example : progRejects escKey
  "audit: self's payload (Pair σ2 (Pair [Pair σ9 σ8] σ5)) does not have its owed type"
  = true := by native_decide

/-- Onto an ARRAY'S EXTENT. -/
def escExtent : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array n Nat). Le (S Z) n)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => &m *nn } } };
  () }

example : progRejects escExtent
  "(Pair σ6 (Pair σ4 σ5)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : (Array #§0 Nat)). ⇝(natRec"
  = true := by native_decide

/-- Onto a cell a Σ0 tail PINS to a literal. -/
def escPinned : Term := prog{
  fn G (self : &mut (Σ (x : Nat). Σ0 (d : Unit). Id Nat x 7)) -> &mut Nat {
    match self { Pair(xx, r1) => match r1 { Pair(dd, H) => &m *xx } } };
  () }

example : progRejects escPinned
  "(Pair σ6 (Pair σ4 σ5)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : Unit). ⇝(Id #§0 (S (S (S (S (S (S (S Z)))))))))"
  = true := by native_decide

/-- Onto a cell a LATER RUNTIME BINDER'S TYPE needs — the dependence is not in a
    Σ0 tail at all, which is the route the doc's rule had to be checked against
    rather than assumed to cover. -/
def escRuntimeDep : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ (a : Array n Nat). Nat)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, w) => &m *nn } } };
  () }

example : progRejects escRuntimeDep
  "(Pair σ6 (Pair σ4 σ5)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : (Array #§0 Nat)). Nat)"
  = true := by native_decide

/-- **NOT VACUOUS.** The same body one field over: the borrow escapes onto a
    VALUE cell, `AllK7` never reads a value, and it CHECKS. The rule refuses what
    a write could break and nothing else. -/
def escVal : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

example : progOk escVal = true := by native_decide

/-! ## §3 The end-to-end witness

    `escKey` is only a hole if a caller can reach through it, so this is the
    caller: take the borrow, write a 1 into the cell the invariant says is a 7,
    and let the group end. THREE parts, and only the last is about the checker. -/

def escKeyExploit : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  fn Break (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    let r = G(self);
    *r := 1;
    () };
  let p = Pair(Z, Pair(Arr(Pair(7, 5)), Pair(Refl, unit)));
  let q = &m p;
  Break(q);
  () }

-- (1) The MACHINE runs it, and this is what it leaves in `p`: the key is a 1 and
--     the pack's stored `Refl` now sits at `Id Nat 1 7`. Execution does not
--     consult the checker, so this is what the ACCEPTED program did.
example : runBinding escKeyExploit "p"
  = some "Pair Z (Pair [Pair (S Z) (S (S (S (S (S Z)))))] (Pair Refl unit))"
  := by native_decide

-- (2) The CHECKER refuses it, and the sentence names the opaque cell: the key
--     leaf reads `σ9`, filled at the escaping borrow's owed type. Compare §4's
--     `wrKey1`, whose key leaf reads `(S Z)` — the same write, kept instead of
--     returned, judged on its actual value.
example : progRejects escKeyExploit
  "audit: self's payload (Pair σ2 (Pair [Pair σ9 σ8] σ5)) does not have its owed type"
  = true := by native_decide

-- (3) …and that value does not inhabit the type the accepting checker left the
--     caller holding. `Refl` proves `Id Nat 7 7`; it does not prove `Id Nat 1 7`.
example : chkL prog{ Pair(Refl, unit) } prog{ AllK7 1 Arr(Pair(7, 5)) } = true := by
  native_decide
example : chkL prog{ Pair(Refl, unit) } prog{ AllK7 1 Arr(Pair(1, 5)) } = false := by
  native_decide
example : chkL prog{ Pair(Z, Pair(Arr(Pair(1, 5)), Pair(Refl, unit))) }
  prog{ Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = false := by
  native_decide

/-! ## §4 The fill-mode split, from the other side

    A NON-escaping write is judged on its actual value, and always was. These two
    are `escVal`/`escKey`'s bodies with the borrow kept instead of returned, and
    they are the reason the split is a split rather than a blanket σ: the audit is
    already right about places the caller cannot reach. -/

def wrVal1 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *vv := 99; () } } } } } };
  () }

def wrKey1 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *kk := 1; () } } } } } };
  () }

example : progOk wrVal1 = true := by native_decide

-- The key leaf reads `(S Z)` — the value actually written. `escKeyExploit`'s
-- reads `σ9`. One escapes and one does not, and that is the only difference
-- between the two programs.
example : progRejects wrKey1
  "audit: self's payload (Pair σ2 (Pair [Pair (S Z) σ8] σ5)) does not have its owed type"
  = true := by native_decide

/-! ## §5 The caller side

    `escVal` is accepted, so its caller can be walked: call it, write through the
    borrow it returned, end the group. §6.2's opacity re-mints the owner as a
    fresh σ at the declared pack type, which re-asserts the invariant — and here
    that is sound, which is the whole point of the callee-side rule earning it. -/

def g5Caller : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  fn Use (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    let r = G(self);
    *r := 1;
    () };
  let p = Pair(Z, Pair(Arr(Pair(7, 0)), Pair(Refl, unit)));
  let q = &m p;
  Use(q);
  () }

example : progOk g5Caller = true := by native_decide

-- The key survives the caller's write, so the pack the machine hands back really
-- does inhabit the type the group end re-minted it at. `escKeyExploit` is the
-- same three lines with the borrow one field over, and it does not.
example : runBinding g5Caller "p"
  = some "Pair Z (Pair [Pair (S (S (S (S (S (S (S Z))))))) (S Z)] (Pair Refl unit))"
  := by native_decide
example : chkL prog{ Pair(Z, Pair(Arr(Pair(7, 1)), Pair(Refl, unit))) }
  prog{ Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = true := by
  native_decide

/-! ## §6 The same claim on the REAL invariant

    `AllK7` is one clause; the flagship's `HMInvT` is five, and the useful half of
    this rule is the prediction that a borrow onto a hashmap's VALUE cell survives
    all five while one onto a KEY cell survives none. Ported here from
    `origin/hm-flagship-fable` — the Σ(Bool) `Opt` vocabulary, the bucket specs and
    the invariant, with `Mod`/`Mul` re-stated because they live in that branch's
    `StdLemmas` additions and not in this one's.

    A fresh σ at type τ is a universally quantified variable of type τ as far as
    `hasType` is concerned, so `Π (V : Nat). …` is the pure-layer stand-in for what
    the fill puts in the cell, and the proof term is the SAME one the concrete pack
    carries. That is the claim: the stored proof still inhabits the abstracted
    type. -/

def NextR : Term := prog{
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C2) Rc => S(R) } }
def NextC : Term := prog{
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C2) Rc => C2 } }
def ModC : Term := prog{
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def Mod : Term := prog{
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => ModC A B2 Z B2 } }
def Mul : Term := prog{
  λ (A : Nat). λ (B : Nat). elim A return (λ (Az : Nat). Nat) {
    Z => Z, S (A2) Rec => Add B Rec } }

def OptP : Term := prog{
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }
def Opt : Term := prog{ λ (T : Type). Σ (b : Bool). OptP b T }
def SomeN : Term := prog{ λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog{ Pair(False, unit) }

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

def HitL : Term := prog{
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)). IsSomeB (FindL Q L) }

def LenE : Term := prog{
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

def TotalE : Term := prog{
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat)
      Z
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))). λ (Ih : Nat).
          Add (LenE H) Ih)
      M A }

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

def SlotInv : Term := prog{
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    AllKeysMod Cap I L × NodupB L }

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

def HashMapT : Term := prog{
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots }

/-- The fable branch's concrete inhabitant, as the port's own compute test. -/
def hmEx : Term := prog{
  Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) }
def hmExInv : Term := prog{
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
      unit)))))) }

example : chkL hmEx HashMapT = true := by native_decide
example : chkL hmExInv prog{
  HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, 30), Nil)) } = true := by native_decide

-- The VALUE leaf abstracted: same proof, universally quantified. All five
-- clauses survive — `TotalE` counts entries, `AllKeysMod` and `NodupB` read keys.
example : chkL prog{ λ (V : Nat). hmExInv } prog{
  Π (V : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, V), Nil)) } = true := by native_decide
example : chkL prog{
  λ (V : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, V), Nil)), hmExInv)))) }
  prog{ Π (V : Nat) → HashMapT } = true := by native_decide

-- The KEY leaf abstracted: refused, and it should be — a key write really would
-- break hashing.
example : chkL prog{ λ (K : Nat). hmExInv } prog{
  Π (K : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(K, 30), Nil)) } = false := by native_decide
example : chkL prog{
  λ (K : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(K, 30), Nil)), hmExInv)))) }
  prog{ Π (K : Nat) → HashMapT } = false := by native_decide

/-! `NodupB`'s conjunct is `Id Bool (HitL K2 T) False`, and `HitL` runs `FindL`,
    which BUILDS `SomeN V2` out of a value before `IsSomeB` projects the tag off
    again. A one-entry bucket never exercises it — the tail is `Nil` — so the
    two-entry bucket is where the value-insensitivity claim is actually tested. -/

def hm2Inv : Term := prog{
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit),
    Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
    Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit)))))))) }

example : chkL prog{
  Pair(4, Pair(16, Pair(2, Pair(Arr(Nil, Cons(Pair(1, 10), Cons(Pair(5, 50), Nil)), Nil, Nil),
    hm2Inv)))) } HashMapT = true := by native_decide

example : chkL prog{ λ (V1 : Nat). λ (V2 : Nat). hm2Inv } prog{
  Π (V1 : Nat) → Π (V2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, V1), Cons(Pair(5, V2), Nil)), Nil, Nil) }
  = true := by native_decide

example : chkL prog{ λ (K2 : Nat). hm2Inv } prog{
  Π (K2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, 10), Cons(Pair(K2, 50), Nil)), Nil, Nil) }
  = false := by native_decide

/-- A whole BUCKET abstracted — what a `&mut (List …)` escaping onto a slot would
    fill. Refused: the folds have no `Cons`/`Nil` to step on. The rule is not
    "values are always fine", it is "ask the type". -/
example : chkL prog{ λ (B : List (Σ (k : Nat). Nat)). hmExInv } prog{
  Π (B : List (Σ (k : Nat). Nat)) → HMInvT 2 8 1 Arr(Nil, B) } = false := by native_decide

/-! ## §7 THE REMAINING WALL — pinned red, and NOT this rule's to move

    `GetMut` over an intrinsically packed container is still unwritable. These are
    the acceptance probes for whoever takes that on; every verdict below is
    identical with and without opaque fill, which is the measurement that says so.

    ### §7.1 The bisection — the wall is not about escaping borrows

    One pack, `AllK7` folded over its array, five bodies all returning `Unit`, so
    nothing escapes and the fill is the identity throughout. `bisB` is already red
    with no borrow escaping, no write, and no σ anywhere near a value leaf. -/

def bisA : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => () } } };
  () }

def bisB : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0]; () } } } };
  () }

def bisC : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => () } } } } };
  () }

example : progOk bisA = true := by native_decide
example : progOk bisC = false := by native_decide

/-- The needle is the finding: the array comes back as `Arr⟨1 ▷ [σ9], 1 ▷ σ8⟩` —
    the carved element beside an OPAQUE SLICE, and `arrRec` cannot step past σ8.
    Nothing here escapes, so no fill of any kind is involved. -/
example : progRejects bisB
  "audit: self's payload (Pair σ2 (Pair Arr⟨(S Z) ▷ [σ9], (S Z) ▷ σ8⟩ σ5)) does not have its owed type"
  = true := by native_decide

/-! ### §7.2 …it is about the opaque REMAINDER

    Remove the remainder and the same carve re-types. `bisF` carves an extent-1
    array (the carve consumes it whole); `bisI` carves BOTH elements of an
    extent-2 array (multi-segment, nothing opaque left). Both GREEN — so the carve
    does not lose the packed proof's identity, and the segmented form is not the
    problem either. `bisJ` puts a two-element remainder back and it is red again. -/

def bisF : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => () } } } } };
  () }

def bisI : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e0 = &m (*a)[0];
      let e1 = &m (*a)[1];
      () } } } };
  () }

def bisJ : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0]; () } } } };
  () }

example : progOk bisF = true := by native_decide
example : progOk bisI = true := by native_decide
example : progOk bisJ = false := by native_decide

/-! ### §7.3 The audit really is re-typing — two whole-array controls

    A whole-array borrow collapses home to the same σ the proof was minted over
    (`bisG`, green). Overwrite the array through it with keys that are not 7 and
    the audit catches it (`bisH`); overwrite with keys that ARE 7 and it is still
    refused (`bisK`), because the entry proof is not a proof of the new array's
    invariant and the audit will not invent one. -/

def bisG : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; () } } } };
  () }

def bisH : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(1, 1), Pair(2, 2)); () } } } };
  () }

def bisK : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(7, 1), Pair(7, 2)); () } } } };
  () }

example : progOk bisG = true := by native_decide
example : progOk bisH = false := by native_decide
example : progOk bisK = false := by native_decide

/-! ### §7.4 The SECOND wall: the group end re-mints the component

    Move the carve behind a callee boundary and the pack fails for a different
    reason. `layer1Val`'s inner fn returns a VALUE, so its group closes before `G`
    exits and nothing is escaping or in flight at the audit at all — and the array
    component still comes back as a bare fresh σ, because `endGroup`'s opaque
    release mints at the COMPONENT's owed type. The packed proof names the entry
    array; that σ names nothing. This is the granularity mistake `spliceInFlight`'s
    issued arm was written to avoid, in the one place where the kernel has no
    better answer than to make it.

    `layer1Ctl` is the control: the identical boundary over an array-INDEPENDENT
    tail is green, so the boundary is not what fails. -/

def layer1 : Term := prog{
  fn Get (a : &mut (Array 1 (Σ (k : Nat). Nat))) -> &mut Nat {
    let e = &m (*a)[0];
    match e { Pair(kk, vv) => &m *vv } };
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => Get(&m *a) } } };
  () }

def layer1Val : Term := prog{
  fn Get (a : &mut (Array 1 (Σ (k : Nat). Nat))) -> Unit {
    let e = &m (*a)[0];
    match e { Pair(kk, vv) => () } };
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => Get(&m *a) } } };
  () }

def layer1Ctl : Term := prog{
  fn Get (a : &mut (Array 1 (Σ (k : Nat). Nat))) -> &mut Nat {
    let e = &m (*a)[0];
    match e { Pair(kk, vv) => &m *vv } };
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). Le (S Z) n))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => Get(&m *a) } } };
  () }

example : progOk layer1Ctl = true := by native_decide
example : progOk layer1 = false := by native_decide

/-- `σ12` is the component-level mint. Nothing escapes here and the inner group is
    closed, so no fill of any kind ran — this is `endGroup`'s release, not the
    audit's. -/
example : progRejects layer1Val
  "audit: self's payload (Pair σ8 (Pair σ12 σ11)) does not have its owed type"
  = true := by native_decide

end Dllbc.Tests.OpaqueFill

end
