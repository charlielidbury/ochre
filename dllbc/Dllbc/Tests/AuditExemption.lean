import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.Tests.Diff

/-!
# Exit audit exemption: per sub-place, not per parameter

This file tests the exit audit's exemption for an argument borrow that gets
consumed into the function's result. The exemption applies only to the
returned sub-place, not to the whole parameter it lives in: under a
whole-parameter exemption, a callee could return a borrow into one leaf of a
parameter while leaving a hole (⊥) in another leaf of that same parameter, and
still be accepted — even though the executing machine hands the caller back a
value with a hole in it. The audit instead collapses what the callee is
finished with, rejects a hole in whatever it still owns, and types the result
with the in-flight places filled in.
-/

open Dllbc

namespace Dllbc.Tests.AuditExemption

/-! ## Reading helpers for array values -/

def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def varr (l : List Nat) : Val := .ctor "Arr" (l.map vnat)

def natOfV : Nat → Val → Option Nat
  | f, v =>
    match Val.asCtor? v, f with
    | some ("Z", []), _ => some 0
    | some ("S", [w]), f' + 1 => (natOfV f' w).map (· + 1)
    | _, _ => none

/-- Succeeds only on a folded run of plain naturals — a leftover segmentation or
    a ⊥ in a slot makes it `none`, which is how a hole gets asserted. -/
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
def why (t : Term) (retType : Term := prog_parse { Unit }) : String :=
  match checkProgram t retType with
  | .ok _ => "ACCEPTED"
  | .error e => e

/-! ## §1 — the hole repro: checker and machine disagree

    A three-way carve of a borrowed array. The callee returns a borrow into the
    middle cell, and leaves a hole in the left one: `(*l)[0 ; 1]` is a range read
    that takes a value out and never puts it back.

    It must be the range form. `(*l)[0]` is an index read of a `Nat`, so
    copy-on-read leaves the array intact — no hole, and that variant is
    correctly accepted (§3 below). -/

def siblingHole : Term := prog_parse {
  fn SiblingHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let t = (*l)[0 ; 1];
    let e = &m (*c)[0];
    e };
  () }

def holeCaller : Term := prog_parse {
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

/-- Before this exemption was narrowed to the sub-place, this program checked
    (`progOk … = true`) while the machine returned an array with a ⊥ in a
    leaf. The needle names the leaf the callee does not return. -/
example : progRejects siblingHole
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide
-- …and the message explains the rule, not just the symptom.
example : progRejects siblingHole
  "not the whole parameter: every other leaf is a place the caller recovers verbatim"
  = true := by native_decide

/-- The caller goes with it: with the callee refused, the divergence has no
    program to live in. -/
example : progRejects holeCaller
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

/-! ## §2 — the machine's side of the divergence, which does not move

    Whatever the audit decides, the executing machine's answer is the same: it
    runs, and what it hands back is not a run of three naturals. These two hold
    before and after any fix — they are what a fix is measured against. -/

example : ((runY holeCaller).bind arrOfV).isNone = true := by native_decide
example : (runY holeCaller).isSome = true := by native_decide

/-! ## §3 — controls that must stay green -/

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

/-- The carve-and-return with no hole anywhere: the shape `get_mut` needs. -/
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

/-! ## §4 — the bisection that pins the granularity

    Each of these keeps the hole and varies exactly one thing. -/

/-- The same hole, nothing returned. Caught — so the return is what buys it. -/
def holeNoRet : Term := prog_parse {
  fn HoleNoRet (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let t = (*l)[0 ; 1];
    () };
  () }
example : progRejects holeNoRet "holds a hole (⊥) at return" = true := by native_decide

/-- Two parameters: the hole is in `a2`, the returned borrow comes out of `a1`.
    Caught — the exemption on one parameter's return doesn't excuse a hole in
    another parameter. -/
def holeOtherParam : Term := prog_parse {
  fn HoleOther (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let t = (*l)[0 ; 1];
    let e = &m (*a1)[1];
    e };
  () }
example : progRejects holeOtherParam "holds a hole (⊥) at return" = true := by native_decide

/-- …and the control: the same two parameters, no hole anywhere. -/
def holeOtherOk : Term := prog{
  fn HoleOtherOk (a1 : &mut (Array 3 Nat), a2 : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a2)[Z ; 1];
    let e = &m (*a1)[1];
    e };
  () }
example : progOk holeOtherOk = true := by native_decide

/-- A hole in the returned cell itself: caught by the issued-borrow payload check,
    which is separate from the obligation audit. -/
def retHole : Term := prog_parse {
  fn RetHole (a : &mut (Array 3 Nat)) -> &mut Nat {
    let c = &m (*a)[1 ; 1];
    let e = &m (*c)[0];
    let t = *e;
    e };
  () }
example : progRejects retHole "cannot type value ⊥" = true := by native_decide

/-! ## §5 — the hole half, beyond the array repro

    The narrowing is stated on loans, not on arrays, so it reaches every shape a
    parameter can be carved into. Each case here was accepted before the
    narrowing; each is paired with a refill control that must stay accepted. -/

/-- Nested: the hole is inside a list held in a carved cell, two layers down. -/
def nestedHole : Term := prog_parse {
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
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

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

/-- No array anywhere: `hd` and `tl` are sibling fields under the same parameter,
    `tl` goes out in the result, and `*hd` is moved out and never put back. -/
def fieldHole : Term := prog_parse {
  fn FieldHole (v : &mut List Nat) -> &mut (List Nat) {
    match v {
      Nil => v,
      Cons(hd, tl) => { let t = *hd; &m *tl }
    } };
  () }
example : progRejects fieldHole
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

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

/-! ## §6 — the type half

    "Nothing is missing" is not "everything is what it was lent". A write of the
    wrong type into a leaf leaves no hole, so the hole hunt alone passes it. The
    write rule itself does not type-check — the exit audit is the only place that
    ever judges a write into a borrowed place — which is what makes this half
    load-bearing rather than belt-and-braces. Filling the in-flight places is what
    lets the same `hasType` check run on a parameter that has a borrow out in the
    result. -/

/-- `True` written into a `Nat` cell of a sibling segment. -/
def siblingBadWrite : Term := prog_parse {
  fn SiblingBadWrite (a : &mut (Array 3 Nat)) -> &mut Nat {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e0 = &m (*l)[0];
    *e0 := True;
    let e = &m (*c)[0];
    e };
  () }
-- The returned (middle) segment is filled with a fresh, opaquely minted σ
-- rather than its original payload, so the audit reports σ10 here instead of
-- σ9. The verdict, the rule, and every other segment are unchanged — this test
-- is still about the wrong-typed write (`[True]`) in the first segment.
example : progRejects siblingBadWrite
  "a's payload (Arr⟨(S Z) ▷ [True], (S Z) ▷ [σ₁₀], (S Z) ▷ σ₇⟩) does not have its owed type (Array (S (S (S Z))) Nat)"
  = true := by native_decide

/-- The control showing the audit is the only thing checking writes at all: the
    same write, nothing returned, so nothing is in flight and the fill is the
    identity — same rejection, from the same rule. -/
def siblingBadWriteUnit : Term := prog_parse {
  fn SiblingBadWriteU (a : &mut (Array 3 Nat)) -> Unit {
    let l = &m (*a)[Z ; 1];
    let e0 = &m (*l)[0];
    *e0 := True;
    () };
  () }
example : progRejects siblingBadWriteUnit
  "a's payload (Arr⟨(S Z) ▷ [True], (S (S Z)) ▷ σ₄⟩) does not have its owed type"
  = true := by native_decide

/-! ### The call-group shape: the returned borrow came out of an inner call

    A get-mut-like call chain: lend a borrow into a callee (`Walk`), and return
    what that callee issued. Here the residue's in-flight marker is a loan
    captured by a group that is still open, so its borrow isn't available to
    splice in directly — the group table supplies the stand-in, at the type the
    loan was lent at. -/

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

def callGroupOk : Term := withWalk prog_parse {
  fn GetMutC (s : &mut (Array 3 (List Nat)), f : Nat) -> &mut Nat {
    let l = &m (*s)[Z ; 1];
    let c = &m (*s)[1 ; 1];
    let r = &m (*s)[2 ; ..];
    let bk = &m (*c)[0];
    Walk(f, bk) };
  () }
example : progOk callGroupOk = true := by native_decide

def callGroupHole : Term := withWalk prog_parse {
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
  "holds a hole (⊥) at return, in a leaf it still owns" = true := by native_decide

def callGroupBadWrite : Term := withWalk prog_parse {
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
  "s's payload (Arr⟨(S Z) ▷ [True], (S Z) ▷ [σ₂₄], (S Z) ▷ σ₁₉⟩) does not have its owed type"
  = true := by native_decide

/-! ## §7 — the ordering the fill forced

    The fill splices the issued borrows' own payloads into the parameter, so a
    defect in what the result points at lands inside the parameter and surfaces as
    a complaint about the parameter. `auditAction` therefore checks the issued
    borrows first and the obligations second.

    `retHole` in §4 is the control that pins this: a body that empties the cell
    it returns must be told its result holds ⊥, not its argument. With the order
    swapped, `retHole` is the one assertion here that would flip.

    The next two are ordinary return-type negative controls on either side of
    this decision — the return type is wrong for the place the borrow points
    into, and each keeps the issued check's own sentence. The residue collapse
    only ends loans that don't reach a result loan, so it can't disturb an
    issued borrow's payload either way. -/

def badTyElem : Term := prog_parse {
  fn BadTyElem (a : &mut (Array 3 Nat)) -> &mut Bool {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    let e = &m (*c)[0];
    e };
  () }
example : progRejects badTyElem
  "returned borrow's payload (σ₈) does not have its owed type (Bool)" = true := by
  native_decide

def badWidth : Term := prog_parse {
  fn BadWidth (a : &mut (Array 3 Nat)) -> &mut (Array 2 Nat) {
    let l = &m (*a)[Z ; 1];
    let c = &m (*a)[1 ; 1];
    let r = &m (*a)[2 ; ..];
    c };
  () }
example : progRejects badWidth
  "returned borrow's payload (σ₆) does not have its owed type (Array (S (S Z)) Nat)"
  = true := by native_decide

end Dllbc.Tests.AuditExemption
