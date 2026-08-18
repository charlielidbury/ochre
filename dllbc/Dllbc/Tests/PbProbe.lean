import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# Viability probe: opaque-fill for escaping borrows (`docs/14-packed-borrows.md`)

SCRATCH. Nothing here is a kernel edit; every assertion is a measurement.

The thesis under test: when the exit audit re-types a payload holding an
ESCAPING mutable borrow, fill the lent place with a FRESH σ instead of its
current value. A fresh σ at type τ is, for typing purposes, exactly a
universally quantified variable of type τ — so the PURE-layer analogue of the
audit's `hasType filled ob.owed` is

    chkL (λ (V : τ). <pack with V at the lent leaf>) (Π (V : τ). <pack type>)

which is what §V1 measures, on the real `HMInvT`.
-/

section

open Dllbc

namespace Dllbc.Tests.PbProbe

/-- Type-check a closed term against a closed type in the pure seed (ArraySort §i). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! `Mod`/`Mul` live in the FABLE branch's `StdLemmas` additions (295 lines main
    does not have), so they are re-stated here verbatim rather than the whole
    block ported. Nothing else the invariant needs is branch-local. -/

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

/-! ## The real invariant, ported verbatim from `origin/hm-flagship-fable`

    (`HashMap.lean` §vi–§viii: the Σ(Bool) Option vocabulary, the bucket specs,
    and the five-clause `HMInvT`.) -/

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

example : chkL hmEx HashMapT = true := by native_decide

/-! ## V1 — does the invariant CONVERT with a leaf abstracted?

    A fresh σ at type τ is a universally quantified variable of type τ as far as
    `hasType` is concerned, so `Π (V : Nat). …` is the faithful pure-layer stand-in
    for the audit's proposed fill. The proof term is the SAME one `hmEx` carries —
    that is the claim: the stored proof still inhabits the abstracted type. -/

/-- The five-clause tail of `hmEx`, verbatim. -/
def hmExInv : Term := prog{
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
      unit)))))) }

-- (a) CONTROL: the concrete leaf.
example : chkL hmExInv prog{
  HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, 30), Nil)) } = true := by native_decide

-- (b) THE THESIS: the VALUE leaf abstracted. Same proof, universally quantified.
example : chkL prog{ λ (V : Nat). hmExInv } prog{
  Π (V : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, V), Nil)) } = true := by native_decide

-- (c) …and the whole PACK with the value leaf abstracted still has `HashMapT`.
example : chkL prog{
  λ (V : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, V), Nil)), hmExInv)))) }
  prog{ Π (V : Nat) → HashMapT } = true := by native_decide

-- (d) THE NEGATIVE CONTROL: the KEY leaf abstracted. Must be refused.
example : chkL prog{ λ (K : Nat). hmExInv } prog{
  Π (K : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(K, 30), Nil)) } = false := by native_decide

example : chkL prog{
  λ (K : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(K, 30), Nil)), hmExInv)))) }
  prog{ Π (K : Nat) → HashMapT } = false := by native_decide

/-! ### The two-entry bucket — the clause that reads a SIBLING entry

    `NodupB`'s conjunct is `Id Bool (HitL K2 T) False`, and `HitL` runs `FindL`,
    which BUILDS `SomeN V2` out of a value before `IsSomeB` projects the tag off
    again. A one-entry bucket never exercises it (the tail is `Nil`); this does. -/

def hm2Ex : Term := prog{
  Pair(4, Pair(16, Pair(2, Pair(Arr(Nil, Cons(Pair(1, 10), Cons(Pair(5, 50), Nil)), Nil, Nil),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit),
      Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
      Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit)))))))))))) }

example : chkL hm2Ex HashMapT = true := by native_decide

def hm2Inv : Term := prog{
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit),
    Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
    Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit)))))))) }

-- (e) BOTH values abstracted, in a bucket whose `NodupB` reads the sibling entry.
example : chkL prog{ λ (V1 : Nat). λ (V2 : Nat). hm2Inv } prog{
  Π (V1 : Nat) → Π (V2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, V1), Cons(Pair(5, V2), Nil)), Nil, Nil) }
  = true := by native_decide

-- (f) the SECOND key abstracted — `AllKeysMod` and `NodupB` both go stuck.
example : chkL prog{ λ (K2 : Nat). hm2Inv } prog{
  Π (K2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, 10), Cons(Pair(K2, 50), Nil)), Nil, Nil) }
  = false := by native_decide

-- (g) a whole BUCKET abstracted (what a `&mut (List …)` into a slot would fill):
--     refused — the folds have no `Cons`/`Nil` to step on.
example : chkL prog{ λ (B : List (Σ (k : Nat). Nat)). hmExInv } prog{
  Π (B : List (Σ (k : Nat). Nat)) → HMInvT 2 8 1 Arr(Nil, B) } = false := by native_decide

/-! ## V3 — the three needles, on a MINIMAL pack

    `gmProbe1/2/3` need the fable branch's slot arithmetic (`Mod`, `ModLtN`,
    `SlotPack`, `PackLe1`) to even parse. The blocking VARIABLE is none of that: it
    is whether the pack's Σ0 tail mentions the borrowed component. So the repro is
    `packNav`'s shape at literal extent, run TWICE — once with a slots-independent
    tail (the control, expected green) and once with a tail that folds over the
    array (the real thing, expected red). Everything else is held verbatim. -/

/-- Every key in the array is 7 — a fold over the array that reads KEYS only,
    which is `AllKeysMod`'s value-insensitivity in one clause. -/
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

/-- CONTROL (`packNav`'s shape): the Σ0 tail does NOT mention the array. -/
def toyCtl : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). Le (S Z) n))
      -> &mut Nat {
    match self {
      Pair(nn, r1) => match r1 {
        Pair(a, H) => {
          let e = &m (*a)[0];
          match e { Pair(kk, vv) => &m *vv } } } } };
  () }

/-- THE REAL SHAPE: the same body, the Σ0 tail folded over the array. -/
def toyDep : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> &mut Nat {
    match self {
      Pair(nn, r1) => match r1 {
        Pair(a, H) => {
          let e = &m (*a)[0];
          match e { Pair(kk, vv) => &m *vv } } } } };
  () }

#eval (progOk toyCtl, progOk toyDep)
#eval (match checkProgram toyCtl prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram toyDep prog{ Unit } with | .ok _ => "OK" | .error e => e)

/-! ### The bisection: what does the dependent tail actually lose?

    Four bodies over the SAME dependent pack, adding one step at a time. Every
    one of these returns `Unit`, so no borrow escapes and the fill is the
    identity — they isolate the re-typing question from the escaping question. -/

def PackDepT : Term := prog{
  Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a }

/-- (A) navigate only. -/
def bisA : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => () } } };
  () }

/-- (B) navigate, take an element borrow, let its group close at exit. -/
def bisB : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0]; () } } } };
  () }

/-- (C) …and split the element into its key/value field borrows. -/
def bisC : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => () } } } } };
  () }

/-- (D) …and WRITE a new value through the value field borrow. This is the
    caller's write (moment 2) performed INSIDE the callee, where the audit sees
    it: if the invariant survives a value write at all, it survives here. -/
def bisD : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *vv := 99; () } } } } } };
  () }

/-- (E) …and write a new KEY. Must be REFUSED however the rest lands. -/
def bisE : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => { *kk := 99; () } } } } } };
  () }

#eval (progOk bisA, progOk bisB, progOk bisC, progOk bisD, progOk bisE)
#eval (match checkProgram bisB prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram bisD prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram bisE prog{ Unit } with | .ok _ => "OK" | .error e => e)

/-! ### Which half kills it: the opaque REMAINDER, or the lost IDENTITY?

    `bisB`'s payload is `Arr⟨1 ▷ [σ9], 1 ▷ σ8⟩` — a segmented array of fresh σs,
    while the packed proof `σ5` was minted at the WHOLE entry array. Two
    independent reasons that cannot re-type, and they need different repairs:

      (i) the fold is STUCK on the opaque tail `σ8`, so the type does not compute;
     (ii) even where it computes, `σ5 : AllK7 2 σ_entry` and the demanded type
          names a DIFFERENT array — no equation links them.

    `bisF` removes (i): extent 1, so the carve leaves NO remainder. `bisG` removes
    the carve entirely (a whole-array borrow collapses back to the same σ). -/

/-- (F) extent 1 — the carve consumes the whole array, no opaque tail survives. -/
def bisF : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => () } } } } };
  () }

/-- (G) a WHOLE-array borrow — no segmentation at all; the loan collapses home
    and the payload is the same σ the proof was minted over. -/
def bisG : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; () } } } };
  () }

/-- (H) the control for (G): a whole-array borrow that WRITES a whole new array
    through it. The invariant proof is the entry one, so this must be REFUSED —
    it is the "writes are only audited at boundaries" claim being audited. -/
def bisH : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(1, 1), Pair(2, 2)); () } } } };
  () }

#eval (progOk bisF, progOk bisG, progOk bisH)
#eval (match checkProgram bisF prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram bisG prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram bisH prog{ Unit } with | .ok _ => "OK" | .error e => e)

/-! ### `bisF` is GREEN — so the carve does NOT lose the proof's identity

    Extent 1: the element carve consumes the whole array, the payload comes back
    with concrete structure, and the ENTRY proof `σ5` still types the pack. So the
    machine DOES refine the entry σ through the carve; hypothesis (ii) is dead.

    That leaves the opaque remainder — and one confound: at extent 1 the payload
    is a plain array, at extent 2 it is a `§segs` node, and `hasType` may simply
    have no rule for the node (this is `s1P2a`, the doc's separately-dispatched
    prerequisite). `bisI` separates them: extent 2 with BOTH elements carved is
    multi-segment with NOTHING opaque left. -/

/-- (I) extent 2, both elements carved: `§segs` with no opaque remainder. -/
def bisI : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e0 = &m (*a)[0];
      let e1 = &m (*a)[1];
      () } } } };
  () }

/-- (J) extent 3, element 0 carved: a two-element opaque remainder. -/
def bisJ : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0]; () } } } };
  () }

/-- (K) `bisH` with a GOOD array written: keys are 7, so the DEMANDED type is
    inhabited — but by `Pair(Refl, Pair(Refl, unit))`, not by the entry proof
    `σ5`. Green here would mean the audit re-types by conversion; red would mean
    the packed proof's identity is load-bearing even where the claim is true. -/
def bisK : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(7, 1), Pair(7, 2)); () } } } };
  () }

#eval (progOk bisI, progOk bisJ, progOk bisK)
#eval (match checkProgram bisI prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram bisK prog{ Unit } with | .ok _ => "OK" | .error e => e)

/-! ## V2 — the thesis where it can actually be tested

    `bisF`/`bisI` are the configurations in which a packed, array-dependent
    invariant re-types across a carve TODAY. Put an ESCAPING borrow into one of
    them and the thesis becomes decidable: today's audit fills the lent place
    with its ACTUAL payload, so a `&mut` into a *value* cell and a `&mut` into a
    *key* cell are indistinguishable to the exit audit — and the second is a
    write that breaks the invariant. -/

/-- Escaping VALUE borrow, in the extent-1 configuration `bisF` proved green. -/
def escVal : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

/-- Escaping KEY borrow — the SAME body but for `&m *kk`. The packed invariant
    says every key is 7; this hands the caller a `&mut Nat` aimed at one. -/
def escKey : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

#eval (progOk escVal, progOk escKey)

/-- **THE EXPLOIT.** `escKey` checks, so a caller may hold a `&mut` into a key
    cell of a pack whose invariant says the key is 7 — and write 99 into it. The
    checker's optimism is §6.2's group-end opacity: the owner is re-minted as a
    fresh σ at the DECLARED pack type, which re-asserts `AllK7`, while the
    executing machine hands back an array whose key is 99. -/
def escKeyExploit : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  fn Break (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> Unit {
    let r = G(self);
    *r := 99;
    () };
  let p = Pair(Z, Pair(Arr(Pair(7, 5)), Pair(Refl, unit)));
  let q = &m p;
  Break(q);
  () }

#eval progOk escKeyExploit
#eval (match checkProgram escKeyExploit prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match runProgram escKeyExploit with
       | .ok env => env.map (fun (kv : String × Val) => (kv.1, kv.2.pretty))
       | .error e => [("ERR", e)])

/-- …and the value the machine actually produces does NOT inhabit the type the
    checker left the caller holding. -/
example : chkL prog{ Pair(Refl, unit) } prog{ AllK7 1 Arr(Pair(7, 5)) } = true := by
  native_decide
example : chkL prog{ Pair(Refl, unit) } prog{ AllK7 1 Arr(Pair(99, 5)) } = false := by
  native_decide
example : chkL prog{ Pair(Z, Pair(Arr(Pair(99, 5)), Pair(Refl, unit))) }
  prog{ Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = false := by
  native_decide

/-! ### …and the false claim, stated by the program's own type

    `Key0` reads the pack's only key; `Leak` projects the packed invariant's
    first conjunct, so `Leak pk : Id Nat (Key0 pk) 7` — sound for any pack that
    really is one. Applied to the post-write `p`, the checker accepts it while
    `Key0 p` is 99. -/

def Key0 : Term := prog{
  λ (P : Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a).
    elim P return (λ (Pm : Σ (n : Nat).
        Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a). Nat) {
      Pair (N) (R) =>
        elim R return (λ (Rm : Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a). Nat) {
          Pair (A) (H) =>
            arrRec (Σ (k : Nat). Nat)
              (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Nat)
              Z
              (λ (K : Nat). λ (Hd : Σ (k : Nat). Nat).
                λ (T : Array K (Σ (k : Nat). Nat)). λ (Ih : Nat).
                  elim Hd return (λ (Hm : Σ (k : Nat). Nat). Nat) {
                    Pair (K2) (V2) => K2 })
              1 A } } }

example : chkL prog{ Refl }
  prog{ Id Nat (Key0 Pair(Z, Pair(Arr(Pair(7, 5)), Pair(Refl, unit)))) 7 } = true := by
  native_decide
example : chkL prog{ Refl }
  prog{ Id Nat (Key0 Pair(Z, Pair(Arr(Pair(99, 5)), Pair(Refl, unit)))) 7 } = false := by
  native_decide

/-! ## V2 — does the abstraction catch every dependence route?

    The thesis must refuse a borrow into a cell that a RUNTIME component's type
    depends on, not only one an invariant tail mentions. Two routes, each with
    today's verdict measured: an ARRAY EXTENT, and a Σ0 identity on the cell. -/

/-- Route 1: the borrowed cell is the array's EXTENT. -/
def escExtent : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array n Nat). Le (S Z) n)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => &m *nn } } };
  () }

/-- Route 2: a Σ0 tail that pins the borrowed cell to a literal. -/
def escPinned : Term := prog{
  fn G (self : &mut (Σ (x : Nat). Σ0 (d : Unit). Id Nat x 7)) -> &mut Nat {
    match self { Pair(xx, r1) => match r1 { Pair(dd, H) => &m *xx } } };
  () }

/-- Route 3: a LATER runtime binder's type depends on the borrowed cell —
    the dependence is not in a Σ0 tail at all. -/
def escRuntimeDep : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ (a : Array n Nat). Nat)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, w) => &m *nn } } };
  () }

#eval (progOk escExtent, progOk escPinned, progOk escRuntimeDep)
#eval (match checkProgram escExtent prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram escPinned prog{ Unit } with | .ok _ => "OK" | .error e => e)
#eval (match checkProgram escRuntimeDep prog{ Unit } with | .ok _ => "OK" | .error e => e)

end Dllbc.Tests.PbProbe

end
