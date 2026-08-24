import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.Tests.Diff

/-!
# Opaque fill for escaping borrows

spec: docs/14-packed-borrows.md

Tests the exit audit's opaque fill for escaping borrows. When a callee returns a
borrow it issued into its result, the audit re-types the lent place as a fresh
symbol at the borrow's declared type rather than its current value; places under
borrows the callee keeps get their actual payloads. The caller can write anything
through an escaped borrow after the call, so accepting the callee based on the
current value would let that later write falsify an invariant the type system
already certified. The rejects here are four routes to exactly that unsoundness:
a hashed cell, an array extent, a pinned cell, and a cell a later runtime type
depends on.
-/


section

open Dllbc

namespace Dllbc.Tests.OpaqueFill

/-- Type-check a closed term against a closed type in the pure seed. -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- What executing the machine leaves in one binding, as distinct from what the
    checker accepts. -/
def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

/-! ## The container

    `AllK7` is a fold over the array asserting every key is 7, reading nothing
    else. Packing it in the type means a value of that type cannot exist with a
    wrong key in it — which is exactly the property an escaping borrow onto a
    key cell destroys. -/

def AllK7 : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

example : chkL prog_parse { Pair(Refl, Pair(Refl, unit)) }
  prog_parse { AllK7 2 Arr(Pair(7, 1), Pair(7, 2)) } = true := by native_decide
example : chkL prog_parse { Pair(Refl, Pair(Refl, unit)) }
  prog_parse { AllK7 2 Arr(Pair(7, 1), Pair(8, 2)) } = false := by native_decide

/-! ## Escaping borrows onto cells the pack's type depends on

    Each is a `fn` handing the caller a `&mut Nat` aimed at such a cell; each
    should be rejected. -/

/-- Escapes onto a cell the packed invariant hashes. -/
def escKey : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

example : progRejects escKey
  "audit: self's payload (Pair σ₂ (Pair [Pair σ₉ σ₈] σ₅)) does not have its owed type"
  = true := by native_decide

/-- Escapes onto an array's extent. -/
def escExtent : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array n Nat). Le (S Z) n)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => &m *nn } } };
  () }

example : progRejects escExtent
  "(Pair σ₆ (Pair σ₄ σ₅)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : (Array §0 Nat)). ⇝(natRec"
  = true := by native_decide

/-- Escapes onto a cell a Σ0 tail pins to a literal. -/
def escPinned : Term := prog_parse {
  fn G (self : &mut (Σ (x : Nat). Σ0 (d : Unit). Id Nat x 7)) -> &mut Nat {
    match self { Pair(xx, r1) => match r1 { Pair(dd, H) => &m *xx } } };
  () }

example : progRejects escPinned
  "(Pair σ₆ (Pair σ₄ σ₅)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : Unit). ⇝(Id §0 (S (S (S (S (S (S (S Z)))))))))"
  = true := by native_decide

/-- Escapes onto a cell a later runtime binder's type needs — the dependence is
    not in a Σ0 tail at all. -/
def escRuntimeDep : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ (a : Array n Nat). Nat)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, w) => &m *nn } } };
  () }

example : progRejects escRuntimeDep
  "(Pair σ₆ (Pair σ₄ σ₅)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : (Array §0 Nat)). Nat)"
  = true := by native_decide

/-- Control: the same body one field over. The borrow escapes onto a value cell,
    which `AllK7` never reads, and this is accepted. The rule refuses what a
    write could break and nothing else. -/
def escVal : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

example : progOk escVal = true := by native_decide

/-! ### The rule reads the invariant, not the field

    `AllV7` is `AllK7` reading the other component — every value is 7 — and over
    it the two verdicts swap: escaping onto the value is refused, escaping onto
    the key is accepted. -/

def AllV7 : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat V2 7 }) × Ih)
      M A }

/-- Escaping value borrow, invariant reads values — refused. -/
def escValV : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllV7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

/-- Escaping key borrow, invariant reads values — accepted. -/
def escKeyV : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllV7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

example : progRejects escValV
  "audit: self's payload (Pair σ₂ (Pair Arr⟨(S Z) ▷ [Pair σ₁₀ σ₁₂], (S Z) ▷ σ₈⟩ σ₅)) does not have its owed type"
  = true := by native_decide
example : progOk escKeyV = true := by native_decide


/-! ## The end-to-end witness

    `escKey` is only a hole if a caller can reach through it, so this is the
    caller: take the borrow, write a 1 into the cell the invariant says is a 7,
    and let the group end. Three parts; only the last is about the checker. -/

def escKeyExploit : Term := prog_parse {
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

-- (1) The machine runs it: the key ends up 1 and the pack's stored `Refl` now
--     sits at `Id Nat 1 7`. Execution does not consult the checker.
example : runBinding escKeyExploit "p"
  = some "Pair Z (Pair [Pair (S Z) (S (S (S (S (S Z)))))] (Pair Refl unit))"
  := by native_decide

-- (2) The checker refuses it: the key leaf reads `σ9`, filled at the escaping
--     borrow's owed type rather than its written value.
example : progRejects escKeyExploit
  "audit: self's payload (Pair σ₂ (Pair [Pair σ₉ σ₈] σ₅)) does not have its owed type"
  = true := by native_decide

-- (3) …and the written value does not inhabit the type the accepting checker
--     left the caller holding: `Refl` proves `Id Nat 7 7`, not `Id Nat 1 7`.
example : chkL prog_parse { Pair(Refl, unit) } prog_parse { AllK7 1 Arr(Pair(7, 5)) } = true := by
  native_decide
example : chkL prog_parse { Pair(Refl, unit) } prog_parse { AllK7 1 Arr(Pair(1, 5)) } = false := by
  native_decide
example : chkL prog_parse { Pair(Z, Pair(Arr(Pair(1, 5)), Pair(Refl, unit))) }
  prog_parse { Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = false := by
  native_decide

/-! ## The other side of the split: non-escaping writes

    A non-escaping write is judged on its actual value. These two are
    `escVal`/`escKey`'s bodies with the borrow kept instead of returned. -/

def wrVal1 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *vv := 99; () } } } } } };
  () }

def wrKey1 : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *kk := 1; () } } } } } };
  () }

example : progOk wrVal1 = true := by native_decide

-- The key leaf reads `(S Z)`, the value actually written, unlike the escaping
-- `escKeyExploit`'s `σ9` for the same write.
example : progRejects wrKey1
  "audit: self's payload (Pair σ₂ (Pair [Pair (S Z) σ₈] σ₅)) does not have its owed type"
  = true := by native_decide

/-! ## The caller side

    `escVal` is accepted, so its caller can be walked: call it, write through the
    borrow it returned, end the group. The group end re-mints the owner as a
    fresh σ at the declared pack type, re-asserting the invariant — sound here
    because the write only touched the value. -/

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
-- does inhabit the type the group end re-minted it at.
example : runBinding g5Caller "p"
  = some "Pair Z (Pair [Pair (S (S (S (S (S (S (S Z))))))) (S Z)] (Pair Refl unit))"
  := by native_decide
example : chkL prog_parse { Pair(Z, Pair(Arr(Pair(7, 1)), Pair(Refl, unit))) }
  prog_parse { Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = true := by
  native_decide

/-! ## The same claim on the real hashmap invariant

    `AllK7` is one clause; the hashmap's `HMInvT` is five. This section checks
    that a borrow onto a hashmap's value cell survives all five while one onto a
    key cell survives none.

    A fresh σ at type τ is a universally quantified variable of type τ as far as
    `hasType` is concerned, so `Π (V : Nat). …` stands in for what the fill puts
    in the cell, with the proof term the same one the concrete pack carries: the
    stored proof still inhabits the abstracted type. -/

def NextR : Term := prog_parse {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C2) Rc => S(R) } }
def NextC : Term := prog_parse {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C2) Rc => C2 } }
def ModC : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def Mod : Term := prog_parse {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => ModC A B2 Z B2 } }
def Mul : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). elim A return (λ (Az : Nat). Nat) {
    Z => Z, S (A2) Rec => Add B Rec } }

def OptP : Term := prog_parse {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }
def Opt : Term := prog_parse { λ (T : Type). Σ (b : Bool). OptP b T }
def SomeN : Term := prog_parse { λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog_parse { Pair(False, unit) }

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

def HitL : Term := prog_parse {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)). IsSomeB (FindL Q L) }

def LenE : Term := prog_parse {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

def TotalE : Term := prog_parse {
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat)
      Z
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))). λ (Ih : Nat).
          Add (LenE H) Ih)
      M A }

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

def SlotInv : Term := prog_parse {
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    AllKeysMod Cap I L × NodupB L }

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

def HashMapT : Term := prog_parse {
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots }

/-- A concrete inhabitant of `HashMapT`, as a compute test. -/
def hmEx : Term := prog_parse {
  Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) }
def hmExInv : Term := prog_parse {
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
      unit)))))) }

example : chkL hmEx HashMapT = true := by native_decide
example : chkL hmExInv prog_parse {
  HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, 30), Nil)) } = true := by native_decide

-- The value leaf abstracted: same proof, universally quantified. All five
-- clauses survive — `TotalE` counts entries, `AllKeysMod` and `NodupB` read keys.
example : chkL prog_parse { λ (V : Nat). hmExInv } prog_parse {
  Π (V : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, V), Nil)) } = true := by native_decide
example : chkL prog_parse {
  λ (V : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, V), Nil)), hmExInv)))) }
  prog_parse { Π (V : Nat) → HashMapT } = true := by native_decide

-- The key leaf abstracted: refused, and it should be — a key write really would
-- break hashing.
example : chkL prog_parse { λ (K : Nat). hmExInv } prog_parse {
  Π (K : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(K, 30), Nil)) } = false := by native_decide
example : chkL prog_parse {
  λ (K : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(K, 30), Nil)), hmExInv)))) }
  prog_parse { Π (K : Nat) → HashMapT } = false := by native_decide

/-! `NodupB`'s conjunct is `Id Bool (HitL K2 T) False`, and `HitL` runs `FindL`,
    which builds `SomeN V2` out of a value before `IsSomeB` projects the tag off
    again. A one-entry bucket never exercises this path — the tail is `Nil` — so
    a two-entry bucket is needed to test value-insensitivity here. -/

def hm2Inv : Term := prog_parse {
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit),
    Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
    Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit)))))))) }

example : chkL prog_parse {
  Pair(4, Pair(16, Pair(2, Pair(Arr(Nil, Cons(Pair(1, 10), Cons(Pair(5, 50), Nil)), Nil, Nil),
    hm2Inv)))) } HashMapT = true := by native_decide

example : chkL prog_parse { λ (V1 : Nat). λ (V2 : Nat). hm2Inv } prog_parse {
  Π (V1 : Nat) → Π (V2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, V1), Cons(Pair(5, V2), Nil)), Nil, Nil) }
  = true := by native_decide

example : chkL prog_parse { λ (K2 : Nat). hm2Inv } prog_parse {
  Π (K2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, 10), Cons(Pair(K2, 50), Nil)), Nil, Nil) }
  = false := by native_decide

/-- A whole bucket abstracted — what a `&mut (List …)` escaping onto a slot would
    fill. Refused: the folds have no `Cons`/`Nil` to step on. -/
example : chkL prog_parse { λ (B : List (Σ (k : Nat). Nat)). hmExInv } prog_parse {
  Π (B : List (Σ (k : Nat). Nat)) → HMInvT 2 8 1 Arr(Nil, B) } = false := by native_decide

/-! ## `GetMut` over an intrinsically packed container

    This remains only partly writable; these are acceptance probes for the
    remaining gap. Every verdict below is identical with and without opaque fill.

    ### The bisection — the wall is not about escaping borrows

    One pack, `AllK7` folded over its array, five bodies all returning `Unit`, so
    nothing escapes and the fill is the identity throughout: `bisB`'s carve has no
    borrow escaping, no write, and no σ anywhere near a value leaf, and it still
    needs `subsKnowledge` to know what a carve contributes to the fold. -/

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

/-- Both accepted: after a carve, `subsKnowledge` (what a component contributes
    to a dependent tail) folds the rejoined carve back to the `arrCat` spine the
    carve's own `refineSym` already made the entry σ equal to, so the tail types
    with no stepping required. -/
example : progOk bisB = true := by native_decide
example : progOk bisC = true := by native_decide

/-! ### The role of the opaque remainder

    `bisF` carves an extent-1 array (the carve consumes it whole); `bisI` carves
    both elements of an extent-2 array (multi-segment, nothing opaque left). Both
    accepted, via different routes: `bisF`'s single segment unwraps to its body
    (`segsNode`), `bisI`'s two adjacent one-element runs concatenate
    (`mergeSegList`). Neither leaves a `§segs` node behind, which is the shape
    `subsKnowledge` could not otherwise read — `bisJ` puts a two-element remainder
    back and needs `subsKnowledge`'s carve case for the same reason `bisB`/`bisC`
    do. -/

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
/-- Accepted for the same reason as `bisB`/`bisC`: a two-element remainder is a
    surviving `§segs`, and `subsKnowledge` has a case for it. -/
example : progOk bisJ = true := by native_decide

/-! ### The audit really is re-typing — two whole-array controls

    A whole-array borrow collapses home to the same σ the proof was minted over
    (`bisG`, accepted). Overwrite the array through it with keys that are not 7
    and the audit catches it (`bisH`); overwrite with keys that are 7 and it is
    still refused (`bisK`), because the entry proof is not a proof of the new
    array's invariant and the audit will not invent one. -/

def bisG : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; () } } } };
  () }

def bisH : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(1, 1), Pair(2, 2)); () } } } };
  () }

def bisK : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(7, 1), Pair(7, 2)); () } } } };
  () }

example : progOk bisG = true := by native_decide
example : progOk bisH = false := by native_decide
example : progOk bisK = false := by native_decide

/-! ### A second wall: the group end re-mints the component

    Move the carve behind a callee boundary and the pack fails for a different
    reason. `layer1Val`'s inner fn returns a value, so its group closes before `G`
    exits and nothing is escaping or in flight at the audit at all — yet the array
    component still comes back as a bare fresh σ, because `endGroup`'s opaque
    release mints at the component's owed type. The packed proof names the entry
    array; that σ names nothing.

    `layer1Ctl` is the control: the identical boundary over an array-independent
    tail is accepted, so the boundary alone is not what fails. -/

def layer1 : Term := prog_parse {
  fn Get (a : &mut (Array 1 (Σ (k : Nat). Nat))) -> &mut Nat {
    let e = &m (*a)[0];
    match e { Pair(kk, vv) => &m *vv } };
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => Get(&m *a) } } };
  () }

def layer1Val : Term := prog_parse {
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
    closed, so no fill ran — this is `endGroup`'s release, not the audit's. -/
example : progRejects layer1Val
  "audit: self's payload (Pair σ₈ (Pair σ₁₂ σ₁₁)) does not have its owed type"
  = true := by native_decide


/-! ### A third wall, this rule's own: the fill's σ must reduce away

    A partially-carved packed array re-types, so the `GetMut` shape can be asked.
    It works for a carve at index 0:

        gmVal2   extent 2, carve index 0, escaping value borrow    accepted
        gmVal3   extent 3, carve index 0, escaping value borrow    accepted
        gmKey2   the same at the key                                refused

    and is refused for a carve anywhere else (`gmValMid`, `gmValLast`).

    **The cause is not the carve position.** `midUnit3`, `lastUnit3` and
    `lastUnit2` carve at index 1 and 2 and are accepted, and `midSplit3` —
    `gmValMid` with the escape removed and nothing else changed, same extent,
    same carve, same field split — is accepted too. So the only difference
    between the accepted program and the refused one is the σ this rule's fill
    put in the value position.

    **The mechanism.** The fill deliberately makes the two sides of the audit's
    conversion differ at the lent leaf: the payload carries a fresh σ where the
    packed proof's type carries the entry σ. That difference is invisible exactly
    when the invariant reduces past the lent element, because `AllK7`'s cons step
    projects the key and drops the value, so the leaf's position vanishes from the
    normal form. `arrRec` reduces from the head, so the fill's σ is erased iff
    every element before the lent one is concrete — which is what "carve at index
    0" means and what a carve further in breaks, since the prefix is then an
    opaque slice and the fold cannot take a step at all. The stuck spine keeps the
    σ, the two sides differ, and the audit refuses.

    **The refusal is correct.** A stuck fold is the checker saying it does not
    know the invariant ignores that cell — and it does not, since nothing has
    told it. Accepting would mean asserting that a fold whose motive it cannot
    evaluate is insensitive to a position it never reached, which is a theorem
    about `arrRec`, not a conversion. Fixing this is a design question for the
    `GetMut` lane rather than a contained change: the shape of the answer is a
    fold that can begin at a symbolic prefix, which is why `SlotsFrom` already
    threads its start index as a fold argument.

    It matters because a hashmap's slot index is symbolic: the real `GetMut` is
    `gmValMid`-shaped, never `gmVal2`-shaped. -/

def gmVal2 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

def gmVal3 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

def gmKey2 : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

/-- The `GetMut` shape, working: a partially-carved packed array with an
    escaping value borrow out of the carved element. -/
example : progOk gmVal2 = true := by native_decide
example : progOk gmVal3 = true := by native_decide
example : progOk gmKey2 = false := by native_decide

/-- Carve at index 1 and index 2: the escaping borrow's σ is no longer reduced
    away. `gmValMid`'s payload prints `Arr⟨1 ▷ σ6, 1 ▷ [Pair σ10 σ12], 1 ▷ σ8⟩` —
    `σ6` is the opaque prefix that stops the fold and `σ12` is the fill the fold
    therefore never erases. -/
def gmValMid : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

def gmValLast : Term := prog_parse {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[2];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

example : progRejects gmValMid
  "audit: self's payload (Pair σ₂ (Pair Arr⟨(S Z) ▷ σ₆, (S Z) ▷ [Pair σ₁₀ σ₁₂], (S Z) ▷ σ₈⟩ σ₅)) does not have its owed type"
  = true := by native_decide
example : progOk gmValLast = false := by native_decide

/-- The minimal refused shape: the count component and the third element are
    both inessential. A bare `Σ0` pack over a two-element array, carved at index
    1 — one leading opaque slice is enough to keep the invariant's fold from
    reaching the filled leaf. Same mechanism as `gmValMid`, two components
    smaller. -/
def gmValMin : Term := prog_parse {
  fn G (self : &mut (Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-- Control: the identical body with the escape removed. Accepted — the
    escaping loan is the whole objection, at this size too. -/
def gmValMinCtl : Term := prog{
  fn G (self : &mut (Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a)) -> Unit {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => () } } } };
  () }

example : progRejects gmValMin
  "audit: self's payload (Pair Arr⟨(S Z) ▷ σ₄, (S Z) ▷ [Pair σ₈ σ₁₀]⟩ σ₃) does not have its owed type"
  = true := by native_decide
example : progOk gmValMinCtl = true := by native_decide

/-! Four carves at index ≥ 1 with no escaping borrow, all accepted — so neither
    the carve position nor the opaque prefix is what the audit objects to.
    `midSplit3` is `gmValMid` verbatim with `&m *vv` replaced by `()`; it produces
    the same three-segment payload with the same field split, and it passes. -/

def midUnit3 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1]; () } } } };
  () }

def lastUnit3 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[2]; () } } } };
  () }

def lastUnit2 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1]; () } } } };
  () }

def midSplit3 : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => () } } } } };
  () }

example : progOk midUnit3 = true := by native_decide
example : progOk lastUnit3 = true := by native_decide
example : progOk lastUnit2 = true := by native_decide
example : progOk midSplit3 = true := by native_decide

/-! A competing hypothesis, tested and excluded: that the middle-known/outer-opaque
    shape defeats adjacent-run merging (the mechanism behind `bisF`/`bisI` never
    leaving a `§segs` behind) and yields a spine association the entry σ's
    refinement does not match.

    It does not, and two independent measurements say so.

    `midSplit3` above already settles it on its own: typing that pack requires the
    Σ0 tail `AllK7 3 <spine>` to be inhabited by the entry proof, so a spine the
    entry refinement did not match could not have produced an accepted verdict.
    The three-segment shape matches.

    `midCarveEscN` says it again without relying on that inference: carve at index
    1, producing exactly the ⟨1 ▷ σ6, 1 ▷ [..], 1 ▷ σ8⟩ shape, and let the
    escaping borrow go onto the pack's `n` field instead of into the array. The
    spine is present and the array is filled with its actual payload; only `n`
    receives the fill's fresh σ, and the tail does not mention `n`. Accepted. The
    spine is not what fails — the fill's σ landing somewhere the invariant's
    normal form never reaches is.

    So the discriminator here is whether the invariant reduces past the
    abstracted position, which is a question about the fold's motive rather than
    the value's shape. -/


def midCarveEscN : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *nn } } } } };
  () }

/-- The index-0 twin, controlling for the escape target rather than the carve. -/
def frontCarveEscN : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *nn } } } } };
  () }

example : progOk midCarveEscN = true := by native_decide
example : progOk frontCarveEscN = true := by native_decide

/-! ### A pin routes around the third wall: a declared update over a carved
    pack, discharged by conversion

    The previous wall is about what a type-claim can promise: re-typing the
    filled payload against the pack's Σ0 means asking the invariant's fold to
    reduce past the fill's σ, and a fold that cannot is the checker honestly not
    knowing. A pin changes the question: the release is a declared value — "the
    pack with the array's cell-`i` value replaced by what comes back through the
    borrow I issued" — and the discharge is a conversion between the hole-filled
    exit payload and that declaration, with the invariant nowhere in it.
    `pinFill` folds the carve into its `arrCat` spine with the lent cell
    standing at the shared exit σ and every other place at its actual payload,
    so both sides normalize by the same ι's.

    `AVSet`/`PVSet2`/`PVSet3` are a toy index-first, cons-view update that keeps
    the key, defined here as the container's own theory (like `AllK7`). The
    measured boundary: the index-first update computes past a prefix exactly
    when the body's own flow exposed it (a match on the cell makes its segment a
    run, and `arrCat`'s ι steps on a run head). A blind carve at index ≥ 1
    leaves a σ-bodied prefix no conversion can step past (`gmPin2at1blind`) —
    the same boundary as the fill's, now with both sides printed. That matches
    the real hashmap's `GetMut`, which reaches its slot by walking, and a walk
    opens exactly the prefix the discharge needs. The pin-less `gmValMin`/
    `gmValMid` above are unaffected by this: the fill's conservatism is
    unchanged, and the pin routes around it rather than removing it. -/

def AVSetT : Term := prog_parse {
  λ (I : Nat). λ (V : Nat).
    elim I return (λ (Z0 : Nat). Π (N : Nat) → Π (A : Array N (Σ (k : Nat). Nat)) → Array N (Σ (k : Nat). Nat)) {
      Z => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          Arr()
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M (elim X return (λ (Xz : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
                Pair (Kx) (Vx) => Pair Kx V }) XS)
          N A,
      S (I2) Rec => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          Arr()
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M X (Rec M XS))
          N A } }

def PVSet2T : Term := prog_parse {
  λ (I : Nat). λ (V : Nat). λ (P : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a).
    elim P return (λ (Pz : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a).
                     Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a) {
      Pair (A) (H) => Pair ((%AVSetT) I V 2 A) H } }

def PVSet3T : Term := prog_parse {
  λ (I : Nat). λ (V : Nat). λ (P : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a).
    elim P return (λ (Pz : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a).
                     Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a) {
      Pair (A) (H) => Pair ((%AVSetT) I V 3 A) H } }

def gmPin2at0 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 0 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

def gmPin2at1 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *vv } } } } } };
  () }

def gmPin3at2 : Term := prog{
  fn G (self : &mut (s : Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a ~> (%PVSet3T) 2 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e1 = &m (*a)[1];
        match e1 { Pair(k1, v1) => {
          let e = &m (*a)[2];
          match e { Pair(kk, vv) => &m *vv } } } } } } } };
  () }

/-- The `GetMut` shape, pinned, at every carve index — where the fill alone
    only works at index 0. -/
example : progOk gmPin2at0 = true := by native_decide
example : progOk gmPin2at1 = true := by native_decide
example : progOk gmPin3at2 = true := by native_decide

/-- Negative control: the same pin with the key escaping. The fill puts the
    shared exit in the key slot, the pin puts it in the value slot, and the two
    sides are reported differing in exactly those positions. -/
def gmPinKey2at1 : Term := prog_parse {
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *kk } } } } } };
  () }

example : progRejects gmPinKey2at1 "pin is not met" = true := by native_decide

/-- The measured boundary: `gmValMin`'s body verbatim, pin added, prefix not
    opened. The reported sides are the finding — fill
    `arrCat 1 1 σ₄ [Pair σ₈ σ₁₀]` against the update stuck at the σ₄ prefix.
    Opening the prefix (one match) is what the walk does anyway. -/
def gmPin2at1blind : Term := prog_parse {
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

example : progRejects gmPin2at1blind "pin is not met" = true := by native_decide

end Dllbc.Tests.OpaqueFill

end
