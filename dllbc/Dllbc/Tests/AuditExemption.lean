import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# The exit audit's exemption: per-parameter, and it should be per-place

`hm-probe-getmut`'s SECOND FINDING, lifted here as an acceptance suite.

§6.1 exempts an argument borrow from the exit audit when a borrow derived from it
is consumed into the result — "being issued is its exemption". The exemption is
granted at the granularity of the WHOLE PARAMETER, and the finding is that a
callee may then leave a hole (⊥) in a leaf of that parameter it does NOT return,
and be accepted.

Downstream, the caller checks green — §6.2's opacity re-mints the owner as a fresh
σ at the declared type, which REPAIRS the hole in checking — while the executing
machine hands back an array with a ⊥ in a leaf. The checker is the optimistic side.

The bisection that pins the granularity is in §4: the same hole with a `Unit`
return is caught, the same hole in a SECOND parameter while the borrow returns out
of the first is caught, and the no-hole two-parameter control passes.

M34 narrows the exemption to the returned SUB-PLACE (`residueAudit` in
`Machine.lean`). Two halves, and each has its own section here: §5 the hole check
(is anything missing from a leaf the callee is finished with) and §6 the type check
(is what is there still what it was lent). §7 pins the one ordering decision the
narrowing forced.
-/

open Dllbc

namespace Dllbc.Tests.AuditExemption

/-! ## Reading helpers (from `ArraySort` §vi, via the probe) -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

/-- Succeeds only on a FOLDED run of plain naturals — so a leftover segmentation or
    a ⊥ in a slot makes it `none`, which is how the hole is asserted. -/
def arrOfV : Val → Option (List Nat)
  | v => match Val.asCtor? v with
    | some ("Arr", vs) => vs.mapM (natOfV 2000)
    | _ => none

/-- What the executing machine left in `y`. -/
def runY (t : Term) : Option Val :=
  match Dllbc.Tests.S9Diff.runExec t with
  | .ok env => env.lookup "y"
  | .error _ => none

/-- The verbatim checker message, for the failure reports. -/
def why (t : Term) (retType : Term := prog{ Unit }) : String :=
  match checkProgram t retType with
  | .ok _ => "ACCEPTED"
  | .error e => e

/-! ## §1 — THE DIVERGENCE PAIR

    A three-way carve of a borrowed array. The callee returns a borrow into the
    MIDDLE cell, and leaves a hole in the LEFT one: `(*l)[0 ; 1]` is a RANGE read,
    which is §2.2's take-and-refill, and it never refills.

    It must be the range form. `(*l)[0]` is an INDEX read of a `Nat`, hence
    index-kind, so §2.1's copy-on-read leaves the array intact — no hole, and that
    variant is accepted correctly (§3 below). -/

def siblingHole : Term := prog{
  fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0 ; 1];
    let e = &m (*c)[0];
    e };
  () }

def holeCaller : Term := prog{
  fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0 ; 1];
    let e = &m (*c)[0];
    e };
  let z = Arr(3, 1, 2);
  let b = &m z;
  let e = SiblingHole(b);
  *e := 7;
  let y = z;
  () }

/-- **THE FLIP.** Before M34's narrowing this was `progOk … = true`, and the
    caller below checked green while the machine returned an array with a ⊥ in a
    leaf. The needle names the leaf the callee does NOT return. -/
example : progRejects siblingHole
  "left ⊥ in a leaf it does NOT return" = true := by native_decide

/-- The caller goes with it: with the callee refused, the divergence has no
    program to live in. -/
example : progRejects holeCaller
  "left ⊥ in a leaf it does NOT return" = true := by native_decide

/-! ## §2 — the machine's side of the divergence, which does not move

    Whatever the audit decides, the EXECUTING machine's answer is the same: it
    runs, and what it hands back is not a run of three naturals. These two hold
    before and after any fix — they are what the fix is measured against. -/

example : ((runY holeCaller).bind arrOfV).isNone = true := by native_decide
example : (runY holeCaller).isSome = true := by native_decide

/-! ## §3 — CONTROLS that must stay green -/

/-- Index-kind read of the sibling: copy-on-read, no hole, correctly accepted. -/
def siblingCopy : Term := prog{
  fn SiblingCopy (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0];
    let e = &m (*c)[0];
    e };
  () }
example : progOk siblingCopy = true := by native_decide

/-- The carve-and-return with NO hole anywhere: the shape `get_mut` needs. -/
def getSlot : Term := prog{
  fn GetSlot (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
example : progOk getSlot = true := by native_decide

def getSlotCaller : Term := prog{
  fn GetSlot (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  let z = Arr(3, 1, 2);
  let b = &m z;
  let e = GetSlot(b);
  *e := 7;
  let y = z;
  () }
example : progOk getSlotCaller = true := by native_decide
example : runY getSlotCaller == some (varr [3, 7, 2]) := by native_decide

/-! ## §4 — THE BISECTION: what granularity is the exemption?

    Each of these keeps the hole and varies exactly one thing. -/

/-- The same hole, nothing returned. CAUGHT — so the return is what buys it. -/
def holeNoRet : Term := prog{
  fn HoleNoRet (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let t = (*l)[0 ; 1];
    () };
  () }
example : progRejects holeNoRet "holds ⊥" = true := by native_decide

/-- Two parameters: the hole is in `a2`, the returned borrow comes out of `a1`.
    CAUGHT — so the exemption is granted per PARAMETER. -/
def holeOtherParam : Term := prog{
  fn HoleOther (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let t = (*l)[0 ; 1];
    let e = &m (*a1)[1];
    e };
  () }
example : progRejects holeOtherParam "holds ⊥" = true := by native_decide

/-- …and the control: the same two parameters, no hole anywhere. -/
def holeOtherOk : Term := prog{
  fn HoleOtherOk (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let e = &m (*a1)[1];
    e };
  () }
example : progOk holeOtherOk = true := by native_decide

/-- A hole in the RETURNED cell itself: caught by the issued-borrow payload check,
    which is a different check from the obligation audit. -/
def retHole : Term := prog{
  fn RetHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let c = &m (*a)[1 ; 1];
    let e = &m (*c)[0];
    let t = *e;
    e };
  () }
example : progRejects retHole "cannot type value ⊥" = true := by native_decide

/-! ## §5 — THE HOLE HALF, beyond the array repro

    The narrowing is stated on loans, not on arrays, so it reaches every shape a
    parameter can be carved into. Each case here was ACCEPTED before M34; each is
    paired with the refill control that must stay accepted. -/

/-- Nested: the hole is inside a LIST held in a carved cell, two layers down. -/
def nestedHole : Term := prog{
  fn NestedHole (s : &mut (Array 3 (List Nat))) -> &mut (List Nat) {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bkl = &m (*l)[0];
    let t = *bkl;
    let bk = &m (*c)[0];
    bk };
  () }
example : progRejects nestedHole
  "left ⊥ in a leaf it does NOT return" = true := by native_decide

def nestedRefill : Term := prog{
  fn NestedRefill (s : &mut (Array 3 (List Nat))) -> &mut (List Nat) {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bkl = &m (*l)[0];
    let t = *bkl;
    *bkl := t;
    let bk = &m (*c)[0];
    bk };
  () }
example : progOk nestedRefill = true := by native_decide

/-- No array anywhere: `hd` and `tl` are sibling FIELDS under the same parameter,
    `tl` goes out in the result, and `*hd` is moved out and never put back. -/
def fieldHole : Term := prog{
  fn FieldHole (v : &mut List Nat) -> &mut (List Nat) {
    match v {
      Nil => v,
      Cons(hd, tl) => { let t = *hd; &m *tl }
    } };
  () }
example : progRejects fieldHole
  "left ⊥ in a leaf it does NOT return" = true := by native_decide

def fieldRefill : Term := prog{
  fn FieldRefill (v : &mut List Nat) -> &mut (List Nat) {
    match v {
      Nil => v,
      Cons(hd, tl) => { let t = *hd; *hd := t; &m *tl }
    } };
  () }
example : progOk fieldRefill = true := by native_decide

/-- A carve the callee never rejoins, with the returned borrow elsewhere: the
    extents still sum, so this is legitimate and stays accepted. -/
def carveLeftOpen : Term := prog{
  fn CarveLeftOpen (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let l2 = &m (*l)[Z ; 1];
    let e = &m (*c)[0];
    e };
  () }
example : progOk carveLeftOpen = true := by native_decide

/-! ## §6 — THE TYPE HALF

    "Nothing is missing" is not "everything is what it was lent". A write of the
    wrong type into a residue leaf leaves no hole, and the hole check passes it.
    The ordinary (non-exempt) audit catches such a write — the write rule itself
    does not type-check, so the audit is the only thing that does — and the
    narrowed exemption now catches it too, by splicing the in-flight places back in
    and asking `hasType` the same question the ordinary path asks. -/

/-- `True` written into a `Nat` cell of a sibling segment. -/
def siblingBadWrite : Term := prog{
  fn SiblingBadWrite (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e0 = &m (*l)[0];
    *e0 := True;
    let e = &m (*c)[0];
    e };
  () }
example : progRejects siblingBadWrite
  "residue (Arr⟨(S Z) ▷ [True], (S Z) ▷ [σ9], (S Z) ▷ σ7⟩) does not have its owed type (Array (S (S (S Z))) Nat)"
  = true := by native_decide

/-- The CONTROL that says the ordinary path already caught this: the same write,
    nothing returned, so no exemption applies. -/
def siblingBadWriteUnit : Term := prog{
  fn SiblingBadWriteU (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let e0 = &m (*l)[0];
    *e0 := True;
    () };
  () }
example : progRejects siblingBadWriteUnit
  "a's payload (Arr⟨(S Z) ▷ [True], (S (S Z)) ▷ σ4⟩) does not have its owed type"
  = true := by native_decide

/-! ### The CALL-GROUP shape: the returned borrow came out of an inner call

    `getMutOr`'s structure — lend the bucket borrow to a callee, return what that
    callee issued. Here the residue's in-flight marker is a loan CAPTURED by a
    group that is still open, so its borrow is not in Ω to splice; the group table
    is what supplies the stand-in, at the owed type the loan was lent at. -/

def withWalk (rest : Term) : Term := prog{
  fn Walk [f] (f : Nat, v : &mut List Nat) -> &mut Nat {
    match f {
      Z => { *v := Cons(0, Nil);
             match v { Nil => (), Cons(hd, tl) => &m *hd } },
      S(f2) => match v {
        Nil => { *v := Cons(0, Nil);
                 match v { Nil => (), Cons(hd, tl) => &m *hd } },
        Cons(hd, tl) => Walk(f2, &m *tl)
      }
    } };
  %rest }

def callGroupOk : Term := withWalk prog{
  fn GetMutC (s : &mut (Array 3 (List Nat)), f : Nat) -> &mut Nat {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bk = &m (*c)[0];
    Walk(f, bk) };
  () }
example : progOk callGroupOk = true := by native_decide

def callGroupHole : Term := withWalk prog{
  fn GetMutCH (s : &mut (Array 3 (List Nat)), f : Nat) -> &mut Nat {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bl = &m (*l)[0];
    let t = *bl;
    let bk = &m (*c)[0];
    Walk(f, bk) };
  () }
example : progRejects callGroupHole
  "left ⊥ in a leaf it does NOT return" = true := by native_decide

def callGroupBadWrite : Term := withWalk prog{
  fn GetMutCB (s : &mut (Array 3 (List Nat)), f : Nat) -> &mut Nat {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bl = &m (*l)[0];
    *bl := True;
    let bk = &m (*c)[0];
    Walk(f, bk) };
  () }
example : progRejects callGroupBadWrite
  "residue (Arr⟨(S Z) ▷ [True], (S Z) ▷ [σ24], (S Z) ▷ σ19⟩) does not have its owed type"
  = true := by native_decide

/-! ## §7 — THE ORDERING the narrowing forced

    The residue's type check stands a value in for the returned sub-place, at that
    borrow's own owed type. If the RETURN TYPE is wrong for the place the borrow
    points into, the residue check would fail — truthfully, but blaming the
    parameter for a mistake in the return type. So `auditAction` now checks the
    issued borrows FIRST and the obligations second, and these two negative
    controls (from the probe corpus) are what pin it: each keeps its own sentence.

    Nothing depends on the old order — the residue collapse ends only loans that do
    not reach a result loan, so it cannot disturb an issued borrow's payload. -/

def badTyElem : Term := prog{
  fn BadTyElem (a : &mut (Array 3 Nat)) -> &mut Bool {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
example : progRejects badTyElem
  "returned borrow's payload (σ8) does not have its owed type (Bool)" = true := by
  native_decide

def badWidth : Term := prog{
  fn BadWidth (a : &mut (Array 3 Nat)) -> &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    c };
  () }
example : progRejects badWidth
  "returned borrow's payload (σ6) does not have its owed type (Array (S (S Z)) Nat)"
  = true := by native_decide

end Dllbc.Tests.AuditExemption
