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

**The counterfactual, measured — the FLIP LEDGER.** Revert `spliceInFlight`'s
issued arm to `| some (p, _) => pure p`, leaving everything else in place, and
rebuild this module. NINE of its 50 assertions go red, and they do not all mean
the same thing, so they are split:

    SEVEN the rule BUYS — accepted without it, and each one unsound:
    §2    progRejects escKey
    §2    progRejects escExtent
    §2    progRejects escPinned
    §2    progRejects escRuntimeDep
    §2.1  progRejects escValV
    §3    progRejects escKeyExploit
    §7.5  progOk gmKey2 = false

    THREE the rule COSTS — accepted without it, and safely so:
    §7.5  progRejects gmValMid
    §7.5  progOk gmValLast = false
    §7.5  progRejects gmValMin   (the minimal shape, pinned for 14-'s trace)

Nothing else moves. `escVal`, `gmVal2` and `gmVal3` still check, §4's split still
splits, `g5Caller` still runs, and §6 and §7.1–7.4 are untouched.

**This ledger was FIVE before Gap A merged, and the three it gained say something
worth reading.** `gmKey2` is a new soundness buy: Gap A made partially-carved
packs re-typable, which is what the flagship needed — and it thereby made an
escaping KEY borrow into one of them TYPE. Landing that fold without this fill
would have opened a fresh instance of exactly the hole §2 closes. The two lanes
were independent in their diffs and not independent in their consequences.

`gmValMid` and `gmValLast` are the cost, stated honestly: both are escaping VALUE
borrows that a write could not break, and this rule refuses them anyway (with
`gmValMin` as the same shape at its minimum). That is
§7.5, and it is the whole of what §7.5 costs — three assertions, all value borrows
at a carve index ≥ 1.

Nothing else in the CORPUS moves either: a full `lake build` across both rules
differs by one σ number in one needle (`AuditExemption`'s `siblingBadWrite`,
ledgered at its site).

Note which parts of §3 do NOT flip: the `runBinding` assertion and the `chkL`
one. That is the point of stating the witness in three parts — what the machine
does and what inhabits a type are facts about the program, not about the audit
rule, and they are what make the fifth flip a soundness result rather than a
change of taste.

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

## What this does NOT fix — §7, and there turned out to be three of them

`GetMut` over an intrinsically packed container was blocked by three separate
things, and this section was written when only one of them was visible. It has
been wrong twice about what the wall was, so the history is kept: each reading was
the honest one from where it was standing, and each was corrected by a
measurement rather than by an argument.

  * **§7.1–7.2, FALLEN.** `bisB` — carve one element out of a packed container's
    array with nothing escaping and nothing written — was red, and this file first
    read that as "an invariant folding over the whole array cannot step past an
    opaque slice". Branch `audit-fold-segments` (Gap A) showed the reading was one
    level off: a `§segs` node never reached the fold at all, because
    `subsKnowledge` had no case for a carve and returned `@stateComponent`. It is
    green now, and so are `bisC` and `bisJ`. See their ledgered flips.
  * **§7.4, STANDS.** `layer1Val` — the same carve behind a callee boundary, inner
    group CLOSED, nothing escaping — is red because `endGroup`'s opaque release
    hands the array component back as a bare fresh σ at the COMPONENT's type,
    carrying no relation to what the packed proof names. That is the granularity
    mistake this rule exists to avoid, in the one place where the kernel has no
    better answer than to make it.
  * **§7.5, STANDS, and it is THIS RULE'S OWN.** With Gap A landed, the `GetMut`
    shape checks — for a carve at index 0 (`gmVal2`, `gmVal3` green, `gmKey2`
    red), and nowhere else (`gmValMid`, `gmValLast` red). The fill deliberately
    makes the two sides of the audit's conversion differ at the lent leaf, and
    that difference is invisible only while the invariant REDUCES past the lent
    element. `arrRec` reduces from the head, so the σ is erased iff every element
    before the lent one is concrete. `midSplit3` is the A/B that pins it:
    `gmValMid` with the escape removed and nothing else changed, and it is green.
    The competing reading — that the three-segment shape yields a spine the entry
    σ's refinement does not match — was tested and excluded; `midCarveEscN` builds
    that exact spine and types, because the fill's σ lands outside the array.

The claim this section used to end on — "no conversion crosses either gap" — was
wrong, and Gap A is the counterexample. What can be said instead is narrower and
survives the evidence: §7.5's refusal is CORRECT rather than incomplete tooling. A
stuck fold is the checker saying it does not know the invariant ignores that cell,
and it does not; accepting would be a theorem about `arrRec`, not a conversion.
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

def AllK7 : Term := prog defer_check {
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat K2 7 }) × Ih)
      M A }

example : chkL prog defer_check { Pair(Refl, Pair(Refl, unit)) }
  prog defer_check { AllK7 2 Arr(Pair(7, 1), Pair(7, 2)) } = true := by native_decide
example : chkL prog defer_check { Pair(Refl, Pair(Refl, unit)) }
  prog defer_check { AllK7 2 Arr(Pair(7, 1), Pair(8, 2)) } = false := by native_decide

/-! ## §2 THE FOUR HOLES — escaping borrows that used to check

    Each is a `fn` handing the caller a `&mut Nat` aimed at a cell the pack's own
    type depends on. All four were GREEN before opaque fill. -/

/-- Onto a cell the packed invariant HASHES. -/
def escKey : Term := prog defer_check {
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
def escExtent : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array n Nat). Le (S Z) n)) -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => &m *nn } } };
  () }

example : progRejects escExtent
  "(Pair σ6 (Pair σ4 σ5)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : (Array #§0 Nat)). ⇝(natRec"
  = true := by native_decide

/-- Onto a cell a Σ0 tail PINS to a literal. -/
def escPinned : Term := prog defer_check {
  fn G (self : &mut (Σ (x : Nat). Σ0 (d : Unit). Id Nat x 7)) -> &mut Nat {
    match self { Pair(xx, r1) => match r1 { Pair(dd, H) => &m *xx } } };
  () }

example : progRejects escPinned
  "(Pair σ6 (Pair σ4 σ5)) does not have its owed type (Σ(§0 : Nat). Σ(§1 : Unit). ⇝(Id #§0 (S (S (S (S (S (S (S Z)))))))))"
  = true := by native_decide

/-- Onto a cell a LATER RUNTIME BINDER'S TYPE needs — the dependence is not in a
    Σ0 tail at all, which is the route the doc's rule had to be checked against
    rather than assumed to cover. -/
def escRuntimeDep : Term := prog defer_check {
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

/-! ### §2.1 …and it is not about which field it is

    `escVal`/`escKey` on their own are consistent with a rule that had simply
    learned "keys matter, values do not". `AllV7` is `AllK7` reading the OTHER
    component — every VALUE is 7 — and over it the two verdicts swap. The rule
    reads the invariant, not the field. -/

def AllV7 : Term := prog defer_check {
  λ (M : Nat). λ (A : Array M (Σ (k : Nat). Nat)).
    arrRec (Σ (k : Nat). Nat)
      (λ (Mz : Nat). λ (Az : Array Mz (Σ (k : Nat). Nat)). Type)
      Unit
      (λ (K : Nat). λ (H : Σ (k : Nat). Nat). λ (T : Array K (Σ (k : Nat). Nat)).
        λ (Ih : Type).
          (elim H return (λ (Hm : Σ (k : Nat). Nat). Type) {
            Pair (K2) (V2) => Id Nat V2 7 }) × Ih)
      M A }

/-- Escaping VALUE borrow, invariant reads VALUES — REFUSED. -/
def escValV : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllV7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

/-- Escaping KEY borrow, invariant reads VALUES — ACCEPTED. -/
def escKeyV : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllV7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

example : progRejects escValV
  "audit: self's payload (Pair σ2 (Pair Arr⟨(S Z) ▷ [Pair σ10 σ12], (S Z) ▷ σ8⟩ σ5)) does not have its owed type"
  = true := by native_decide
example : progOk escKeyV = true := by native_decide


/-! ## §3 The end-to-end witness

    `escKey` is only a hole if a caller can reach through it, so this is the
    caller: take the borrow, write a 1 into the cell the invariant says is a 7,
    and let the group end. THREE parts, and only the last is about the checker. -/

def escKeyExploit : Term := prog defer_check {
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
example : chkL prog defer_check { Pair(Refl, unit) } prog defer_check { AllK7 1 Arr(Pair(7, 5)) } = true := by
  native_decide
example : chkL prog defer_check { Pair(Refl, unit) } prog defer_check { AllK7 1 Arr(Pair(1, 5)) } = false := by
  native_decide
example : chkL prog defer_check { Pair(Z, Pair(Arr(Pair(1, 5)), Pair(Refl, unit))) }
  prog defer_check { Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = false := by
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

def wrKey1 : Term := prog defer_check {
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
example : chkL prog defer_check { Pair(Z, Pair(Arr(Pair(7, 1)), Pair(Refl, unit))) }
  prog defer_check { Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a } = true := by
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

def NextR : Term := prog defer_check {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C2) Rc => S(R) } }
def NextC : Term := prog defer_check {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C2) Rc => C2 } }
def ModC : Term := prog defer_check {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def Mod : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => ModC A B2 Z B2 } }
def Mul : Term := prog defer_check {
  λ (A : Nat). λ (B : Nat). elim A return (λ (Az : Nat). Nat) {
    Z => Z, S (A2) Rec => Add B Rec } }

def OptP : Term := prog defer_check {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }
def Opt : Term := prog defer_check { λ (T : Type). Σ (b : Bool). OptP b T }
def SomeN : Term := prog defer_check { λ (V : Nat). Pair(True, V) }
def NoneN : Term := prog defer_check { Pair(False, unit) }

def FindL : Term := prog defer_check {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Opt Nat) {
      Nil => NoneN,
      Cons (E) (T) Rec =>
        elim E return (λ (Em : Σ (k : Nat). Nat). Opt Nat) {
          Pair (K2) (V2) =>
            elim (Eqb Q K2) return (λ (Bm : Bool). Opt Nat) {
              True => SomeN V2,
              False => Rec } } } }

def IsSomeB : Term := prog defer_check {
  λ (O : Σ (b : Bool). OptP b Nat).
    elim O return (λ (Om : Σ (b : Bool). OptP b Nat). Bool) {
      Pair (Bb) (P2) => Bb } }

def HitL : Term := prog defer_check {
  λ (Q : Nat). λ (L : List (Σ (k : Nat). Nat)). IsSomeB (FindL Q L) }

def LenE : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Nat) {
      Nil => Z,
      Cons (E) (T) Rec => S(Rec) } }

def TotalE : Term := prog defer_check {
  λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat)
      Z
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))). λ (Ih : Nat).
          Add (LenE H) Ih)
      M A }

def AllKeysMod : Term := prog defer_check {
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Nat (Mod K2 Cap) I }) × Rec } }

def NodupB : Term := prog defer_check {
  λ (L : List (Σ (k : Nat). Nat)).
    elim L return (λ (Lm : List (Σ (k : Nat). Nat)). Type) {
      Nil => Unit,
      Cons (E) (T) Rec =>
        (elim E return (λ (Em : Σ (k : Nat). Nat). Type) {
          Pair (K2) (V2) => Id Bool (HitL K2 T) False }) × Rec } }

def SlotInv : Term := prog defer_check {
  λ (Cap : Nat). λ (I : Nat). λ (L : List (Σ (k : Nat). Nat)).
    AllKeysMod Cap I L × NodupB L }

def SlotsFrom : Term := prog defer_check {
  λ (Cap : Nat). λ (M : Nat). λ (A : Array M (List (Σ (k : Nat). Nat))). λ (I0 : Nat).
    arrRec (List (Σ (k : Nat). Nat))
      (λ (Mz : Nat). λ (Az : Array Mz (List (Σ (k : Nat). Nat))). Nat → Type)
      (λ (I2 : Nat). Unit)
      (λ (K : Nat). λ (H : List (Σ (k : Nat). Nat)).
        λ (T : Array K (List (Σ (k : Nat). Nat))).
        λ (Ih : Nat → Type). λ (I2 : Nat).
          SlotInv Cap I2 H × Ih (S I2))
      M A I0 }

def HMInvT : Term := prog defer_check {
  λ (Cap : Nat). λ (Load : Nat). λ (N : Nat).
    λ (Slots : Array Cap (List (Σ (k : Nat). Nat))).
      Le (S Z) Cap ×
      (Id Nat Load (Mul 4 Cap) ×
      (Le (Mul 5 N) Load ×
      (Id Nat N (TotalE Cap Slots) ×
      SlotsFrom Cap Cap Slots Z))) }

def HashMapT : Term := prog defer_check {
  Σ (cap : Nat). Σ (load : Nat). Σ (n : Nat).
    Σ0 (slots : Array cap (List (Σ (k : Nat). Nat))). HMInvT cap load n slots }

/-- The fable branch's concrete inhabitant, as the port's own compute test. -/
def hmEx : Term := prog defer_check {
  Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, 30), Nil)),
    Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
      Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
        unit)))))))))) }
def hmExInv : Term := prog defer_check {
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit), Pair(Pair(Pair(Refl, unit), Pair(Refl, unit)),
      unit)))))) }

example : chkL hmEx HashMapT = true := by native_decide
example : chkL hmExInv prog defer_check {
  HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, 30), Nil)) } = true := by native_decide

-- The VALUE leaf abstracted: same proof, universally quantified. All five
-- clauses survive — `TotalE` counts entries, `AllKeysMod` and `NodupB` read keys.
example : chkL prog defer_check { λ (V : Nat). hmExInv } prog defer_check {
  Π (V : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(3, V), Nil)) } = true := by native_decide
example : chkL prog defer_check {
  λ (V : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(3, V), Nil)), hmExInv)))) }
  prog defer_check { Π (V : Nat) → HashMapT } = true := by native_decide

-- The KEY leaf abstracted: refused, and it should be — a key write really would
-- break hashing.
example : chkL prog defer_check { λ (K : Nat). hmExInv } prog defer_check {
  Π (K : Nat) → HMInvT 2 8 1 Arr(Nil, Cons(Pair(K, 30), Nil)) } = false := by native_decide
example : chkL prog defer_check {
  λ (K : Nat). Pair(2, Pair(8, Pair(1, Pair(Arr(Nil, Cons(Pair(K, 30), Nil)), hmExInv)))) }
  prog defer_check { Π (K : Nat) → HashMapT } = false := by native_decide

/-! `NodupB`'s conjunct is `Id Bool (HitL K2 T) False`, and `HitL` runs `FindL`,
    which BUILDS `SomeN V2` out of a value before `IsSomeB` projects the tag off
    again. A one-entry bucket never exercises it — the tail is `Nil` — so the
    two-entry bucket is where the value-insensitivity claim is actually tested. -/

def hm2Inv : Term := prog defer_check {
  Pair(unit, Pair(Refl, Pair(unit, Pair(Refl,
    Pair(Pair(unit, unit),
    Pair(Pair(Pair(Refl, Pair(Refl, unit)), Pair(Refl, Pair(Refl, unit))),
    Pair(Pair(unit, unit), Pair(Pair(unit, unit), unit)))))))) }

example : chkL prog defer_check {
  Pair(4, Pair(16, Pair(2, Pair(Arr(Nil, Cons(Pair(1, 10), Cons(Pair(5, 50), Nil)), Nil, Nil),
    hm2Inv)))) } HashMapT = true := by native_decide

example : chkL prog defer_check { λ (V1 : Nat). λ (V2 : Nat). hm2Inv } prog defer_check {
  Π (V1 : Nat) → Π (V2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, V1), Cons(Pair(5, V2), Nil)), Nil, Nil) }
  = true := by native_decide

example : chkL prog defer_check { λ (K2 : Nat). hm2Inv } prog defer_check {
  Π (K2 : Nat) →
    HMInvT 4 16 2 Arr(Nil, Cons(Pair(1, 10), Cons(Pair(K2, 50), Nil)), Nil, Nil) }
  = false := by native_decide

/-- A whole BUCKET abstracted — what a `&mut (List …)` escaping onto a slot would
    fill. Refused: the folds have no `Cons`/`Nil` to step on. The rule is not
    "values are always fine", it is "ask the type". -/
example : chkL prog defer_check { λ (B : List (Σ (k : Nat). Nat)). hmExInv } prog defer_check {
  Π (B : List (Σ (k : Nat). Nat)) → HMInvT 2 8 1 Arr(Nil, B) } = false := by native_decide

/-! ## §7 THE REMAINING WALL — two of them, and the first one has since fallen

    `GetMut` over an intrinsically packed container is still unwritable. These are
    the acceptance probes for whoever takes that on; every verdict below is
    identical with and without opaque fill, which is the measurement that says so.

    **§7.1 and §7.2 were the OTHER lane's**, and they are green now. This section
    was written pinned red and handed on; branch `audit-fold-segments` (Gap A of
    `docs/14-packed-borrows.md`) took it, and its diagnosis is §7.2's own sentence
    read one level down — see the ledger there. §7.3's soundness controls and
    §7.4's second wall are untouched by it, which is what says the two lanes were
    about different things.

    ### §7.1 The bisection — the wall is not about escaping borrows

    One pack, `AllK7` folded over its array, five bodies all returning `Unit`, so
    nothing escapes and the fill is the identity throughout. `bisB` was already red
    with no borrow escaping, no write, and no σ anywhere near a value leaf — so
    whatever it was, it was not this rule's. -/

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

/-- **LEDGERED FLIP** (branch `audit-fold-segments`, Gap A): red → GREEN. The
    rejection this used to carry named its own cause — "the array comes back as
    `Arr⟨1 ▷ [σ9], 1 ▷ σ8⟩`" — and the reading of it was one level off. The
    obstacle was not `arrRec` failing to step past σ8; it was that a `§segs` node
    never reached `arrRec` at all. `subsKnowledge`, which says what a component
    contributes to a dependent tail, had no reading for a carve and returned
    `@stateComponent`, so the tail was demanded at a name that converts with
    nothing. Folding the rejoined carve through ¶1.3's ⇝ bridge gives back the
    `arrCat` spine the carve's own `refineSym` already made the entry σ equal to,
    and the tail types with no stepping required. -/
example : progOk bisB = true := by native_decide
example : progOk bisC = true := by native_decide

/-! ### §7.2 …it is about the opaque REMAINDER — and that was the whole of it

    Remove the remainder and the same carve re-types. `bisF` carves an extent-1
    array (the carve consumes it whole); `bisI` carves BOTH elements of an
    extent-2 array (multi-segment, nothing opaque left). Both GREEN — so the carve
    does not lose the packed proof's identity, and the segmented form is not the
    problem either. `bisJ` puts a two-element remainder back and it was red again.

    **The bisection was right and its two green cases say why**, which is worth
    keeping now that all five are green. `bisF` carves an extent-1 array, so
    `segsNode` unwraps the single segment to its body; `bisI` carves both elements,
    so `mergeSegList` concatenates two adjacent one-element RUNS. Neither leaves a
    `§segs` node behind — and a surviving `§segs` node was exactly the case
    `subsKnowledge` could not read. So "the wall is the opaque remainder" was
    precisely "the wall is a carve that does not normalize itself away", and Gap A's
    fold is the general form of what `segsNode` and `mergeSegList` were doing for
    the two easy shapes. -/

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
/-- **LEDGERED FLIP** (branch `audit-fold-segments`, Gap A): red → GREEN, and the
    same flip as `bisB`/`bisC` — a two-element remainder is a surviving `§segs`. -/
example : progOk bisJ = true := by native_decide

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

def bisH : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> Unit {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let b = &m *a; *b := Arr(Pair(1, 1), Pair(2, 2)); () } } } };
  () }

def bisK : Term := prog defer_check {
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

def layer1 : Term := prog defer_check {
  fn Get (a : &mut (Array 1 (Σ (k : Nat). Nat))) -> &mut Nat {
    let e = &m (*a)[0];
    match e { Pair(kk, vv) => &m *vv } };
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 1 (Σ (k : Nat). Nat)). AllK7 1 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => Get(&m *a) } } };
  () }

def layer1Val : Term := prog defer_check {
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


/-! ### §7.5 The THIRD wall, and it is this rule's own: the fill's σ must be
    REDUCED AWAY, and reduction starts at the head

    With Gap A landed, a partially-carved packed array re-types, so the `GetMut`
    shape can finally be asked. It works — for a carve at index 0:

        gmVal2   extent 2, carve index 0, escaping VALUE borrow    GREEN
        gmVal3   extent 3, carve index 0, escaping VALUE borrow    GREEN
        gmKey2   the same at the KEY                               red

    and stops working for a carve anywhere else (`gmValMid`, `gmValLast`).

    **The cause is not the carve.** That was the obvious reading and it is wrong:
    `midUnit3`, `lastUnit3` and `lastUnit2` carve at index 1 and 2 and are GREEN,
    and `midSplit3` — `gmValMid` with the escape removed and NOTHING else changed,
    same extent, same carve, same field split — is GREEN too. The A/B is exact, so
    the only difference between the green program and the red one is the σ this
    rule's fill put in the value position.

    **The mechanism.** The fill deliberately makes the two sides of the audit's
    conversion differ at the lent leaf: the payload carries a fresh σ where the
    packed proof's type carries the entry σ. That difference is invisible exactly
    when the invariant REDUCES past the lent element, because `AllK7`'s cons step
    projects the key and drops the value, so the leaf's position vanishes from the
    normal form. `arrRec` reduces from the head. So the fill's σ is erased iff
    every element BEFORE the lent one is concrete — which is what "index 0" means
    and what a carve further in destroys, since the prefix is then an opaque slice
    and the fold cannot take a step at all. The stuck spine keeps the σ, the two
    sides differ, and the audit refuses.

    **The refusal is CORRECT, and that is why this is pinned rather than fixed.**
    A stuck fold is the checker saying it does not know the invariant ignores that
    cell. It does not; nothing has told it. Accepting would mean asserting that a
    fold whose motive it cannot evaluate is insensitive to a position it never
    reached — a theorem about `arrRec`, not a conversion. Gap A's fix worked
    because the equation it needed (`refineSym` had already made the entry σ equal
    to the `arrCat` spine) was definitional and merely unreachable. There is no
    corresponding equation here. So this is a DESIGN question for the GetMut lane,
    not a contained fix, and the shape of the answer is a fold that can begin at a
    symbolic prefix — `SlotsFrom` already threads its start index as a fold
    argument for exactly this reason.

    It matters for the flagship because a hashmap's slot index is symbolic: the
    real `GetMut` is `gmValMid`-shaped, never `gmVal2`-shaped. -/

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

def gmKey2 : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *kk } } } } };
  () }

/-- **THE GetMut SHAPE, WORKING** — a partially-carved packed array with an
    escaping value borrow out of the carved element. Red before Gap A. -/
example : progOk gmVal2 = true := by native_decide
example : progOk gmVal3 = true := by native_decide
example : progOk gmKey2 = false := by native_decide

/-- Carve at index 1 and index 2: the escaping borrow's σ is no longer reduced
    away, and these are the pinned probes of the gap. `gmValMid`'s payload prints
    `Arr⟨1 ▷ σ6, 1 ▷ [Pair σ10 σ12], 1 ▷ σ8⟩` — `σ6` is the opaque prefix that
    stops the fold and `σ12` is the fill the fold therefore never erases. -/
def gmValMid : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

def gmValLast : Term := prog defer_check {
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[2];
      match e { Pair(kk, vv) => &m *vv } } } } };
  () }

example : progRejects gmValMid
  "audit: self's payload (Pair σ2 (Pair Arr⟨(S Z) ▷ σ6, (S Z) ▷ [Pair σ10 σ12], (S Z) ▷ σ8⟩ σ5)) does not have its owed type"
  = true := by native_decide
example : progOk gmValLast = false := by native_decide

/-- **The MINIMAL red shape** (pinned for `14-packed-borrows.md`'s problem
    statement): the count component and the third element are both inessential.
    A bare `Σ0` pack over a TWO-element array, carved at index 1 — one leading
    opaque slice is enough to keep the invariant's fold from reaching the filled
    leaf. Same mechanism as `gmValMid`, two components smaller. -/
def gmValMin : Term := prog defer_check {
  fn G (self : &mut (Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

/-- …and its A/B: the identical body with the escape removed. Green — the
    escaping loan is the whole objection, at this size too. -/
def gmValMinCtl : Term := prog{
  fn G (self : &mut (Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a)) -> Unit {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => () } } } };
  () }

example : progRejects gmValMin
  "audit: self's payload (Pair Arr⟨(S Z) ▷ σ4, (S Z) ▷ [Pair σ8 σ10]⟩ σ3) does not have its owed type"
  = true := by native_decide
example : progOk gmValMinCtl = true := by native_decide

/-! **THE A/B THAT PINS IT.** Four carves at index ≥ 1 with no escaping borrow,
    all GREEN — so neither the carve position nor the opaque prefix is what the
    audit objects to. `midSplit3` is `gmValMid` verbatim with `&m *vv` replaced by
    `()`; it produces the same three-segment payload with the same field split, and
    it passes. -/

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

/-! **THE COMPETING HYPOTHESIS, TESTED AND EXCLUDED.** Gap A's author read this
    residual as its own question one position over: the wall was always carves
    that do not SELF-NORMALIZE (`segsNode` unwraps a single segment, `mergeSegList`
    concatenates adjacent RUNS, which is why `bisF` and `bisI` never left a `§segs`
    behind), so the middle-known/outer-opaque shape might defeat adjacent-run
    merging and yield a spine association the entry σ's refinement does not match.

    It does not, and two independent measurements say so.

    `midSplit3` above already settles it on its own: typing that pack REQUIRES the
    Σ0 tail `AllK7 3 <spine>` to be inhabited by the entry proof, so a spine the
    entry refinement did not match could not have produced a green verdict. The
    three-segment shape matches.

    `midCarveEscN` says it again without relying on that inference: carve at index
    1, producing exactly the ⟨1 ▷ σ6, 1 ▷ [..], 1 ▷ σ8⟩ shape, and let the ESCAPING
    borrow go onto the pack's `n` field instead of into the array. The spine is
    present and the array is filled with its actual payload; only `n` receives the
    fill's fresh σ, and the tail does not mention `n`. GREEN. The spine is not what
    fails — the fill's σ landing somewhere the invariant's normal form never
    reaches is.

    So "self-normalizing" is the right account of §7.1–7.2 and not of this: these
    four probes and `midSplit3` all leave a `§segs` behind and are all green. The
    discriminator here is whether the invariant REDUCES past the abstracted
    position, which is a question about the fold's motive rather than the value's
    shape. -/

-- (§7.6, the pin over these same shapes, is at the end of the file — after the
-- §7.5 evidence it routes around.)


def midCarveEscN : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *nn } } } } };
  () }

/-- The index-0 twin, controlling for the escape TARGET rather than the carve. -/
def frontCarveEscN : Term := prog{
  fn G (self : &mut (Σ (n : Nat). Σ0 (a : Array 3 (Σ (k : Nat). Nat)). AllK7 3 a))
      -> &mut Nat {
    match self { Pair(nn, r1) => match r1 { Pair(a, H) => {
      let e = &m (*a)[0];
      match e { Pair(kk, vv) => &m *nn } } } } };
  () }

example : progOk midCarveEscN = true := by native_decide
example : progOk frontCarveEscN = true := by native_decide

/-! ### §7.6 THE PIN ROUTES AROUND §7.5 (M35, residual (a)) — a DECLARED update
    over a carved pack, discharged by conversion

    §7.5's refusal is about what a TYPE-claim can promise: re-typing the filled
    payload against the pack's Σ0 means asking the invariant's fold to reduce
    past the fill's σ, and a fold that cannot is the checker honestly not
    knowing. A PIN changes the question: the release is a declared VALUE —
    "the pack with the array's cell-`i` value replaced by what comes back
    through the borrow I issued" — and the discharge is a CONVERSION between
    the hole-filled exit payload and that declaration, with the invariant
    nowhere in it. `pinFill` folds the carve into its `arrCat` spine with the
    lent cell standing at the SHARED exit σ and every other place at its actual
    payload, so both sides normalize by the same ι's.

    `AVSet`/`PVSet2`/`PVSet3` are the toy's update (index-first, cons-view,
    keeping the key — defined here, like `AllK7`, as the container's own
    theory). The measured boundary, pinned by `gmPin2at1blind`: the index-first
    update computes past a prefix exactly when the BODY'S OWN FLOW exposed it
    (a match on the cell makes its segment a run, and `arrCat`'s ι steps on a
    run head). A blind carve at index ≥ 1 leaves a σ-bodied prefix no
    conversion can step past — the same boundary §7.5 pinned for the fill, now
    with both sides PRINTED. That is the walk-shaped GetMut's own story: the
    real hashmap GetMut reaches its slot by walking, and a walk opens exactly
    the prefix the discharge needs. The pin-less `gmValMin`/`gmValMid` above
    stay red with their needles — the fill's conservatism is unchanged; the pin
    ROUTES AROUND it, per signature. -/

def AVSetT : Term := prog defer_check {
  λ (I : Nat). λ (V : Nat).
    elim I return (λ (Z0 : Nat). Π (N : Nat) → Π (A : Array N (Σ (k : Nat). Nat)) → Array N (Σ (k : Nat). Nat)) {
      Z => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M (elim X return (λ (Xz : Σ (k : Nat). Nat). Σ (k : Nat). Nat) {
                Pair (Kx) (Vx) => Pair Kx V }) XS)
          N A,
      S (I2) Rec => λ (N : Nat). λ (A : Array N (Σ (k : Nat). Nat)).
        arrRec (Σ (k : Nat). Nat)
          (λ (M : Nat). λ (Az : Array M (Σ (k : Nat). Nat)). Array M (Σ (k : Nat). Nat))
          %(Term.ctorApp "Arr" [])
          (λ (M : Nat). λ (X : Σ (k : Nat). Nat). λ (XS : Array M (Σ (k : Nat). Nat)).
            λ (Ih : Array M (Σ (k : Nat). Nat)).
              acons M X (Rec M XS))
          N A } }

def PVSet2T : Term := prog defer_check {
  λ (I : Nat). λ (V : Nat). λ (P : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a).
    elim P return (λ (Pz : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a).
                     Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a) {
      Pair (A) (H) => Pair ((%AVSetT) I V 2 A) H } }

def PVSet3T : Term := prog defer_check {
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

/-- The GetMut shape, pinned, at every carve index — where §7.5 stops at 0. -/
example : progOk gmPin2at0 = true := by native_decide
example : progOk gmPin2at1 = true := by native_decide
example : progOk gmPin3at2 = true := by native_decide

/-- The NEGATIVE control: the same pin with the KEY escaping. The fill puts the
    shared exit in the key slot, the pin puts it in the value slot, and the two
    sides are PRINTED differing in exactly those positions. -/
def gmPinKey2at1 : Term := prog defer_check {
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e0 = &m (*a)[0];
      match e0 { Pair(k0, v0) => {
        let e = &m (*a)[1];
        match e { Pair(kk, vv) => &m *kk } } } } } };
  () }

example : progRejects gmPinKey2at1 "pin is not met" = true := by native_decide

/-- The measured BOUNDARY: `gmValMin`'s body verbatim, pin added, prefix NOT
    opened. The printed sides are the finding — fill
    `arrCat 1 1 σ4 [Pair σ8 σ10]` against the update stuck at the σ4 prefix.
    Opening the prefix (one match) is what the walk does anyway. -/
def gmPin2at1blind : Term := prog defer_check {
  fn G (self : &mut (s : Σ0 (a : Array 2 (Σ (k : Nat). Nat)). AllK7 2 a ~> (%PVSet2T) 1 (*res) s)) -> &mut Nat {
    match self { Pair(a, H) => {
      let e = &m (*a)[1];
      match e { Pair(kk, vv) => &m *vv } } } };
  () }

example : progRejects gmPin2at1blind "pin is not met" = true := by native_decide

end Dllbc.Tests.OpaqueFill

end
