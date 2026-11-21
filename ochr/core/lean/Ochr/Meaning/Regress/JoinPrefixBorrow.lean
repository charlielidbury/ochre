import Ochr.Examples.Nat
import Ochr.Test

/-!
# A match's result borrowing a prefix of a place the join drops: every variant rejected (asserted)

Main's question (2026-11-20, from the slice's report 13): `dropAtJoin` rejects a drop whose own value
holds a loan of a borrow the arm's result (in flight, a temporary) holds (D65), but a borrow the
result holds that is lent at a PREFIX of the dropped place is ended by `movedPlace`'s fill branch
(`accessPath` of the parent) with no such check. If an accepted program reached that, the match
would return a borrow whose loan the join ended.

Tried in earnest: one arm moves a non-copy field, the other returns a borrow of the whole (made
before the match, or in the arm), of a prefix one level down, through a borrow parameter's content,
through a local borrow, or a pair holding it; the result used after the match (read through,
written through) or returned; known and unknown scrutinee; tail and non-tail. Every one is
rejected, by one of four rules:
- [Entry] (static ends, rule 2, D90): a non-tail match, on a known or an unknown scrutinee, first
  accesses the captures its stuck block would take; a moved field's capture ends every borrow lent
  at a prefix of it, so the arm cannot return that borrow (`NK1`, `NU1`, `NKW`, `ND`, `NP`, `NLB`,
  `TPair`: "[Read] r0 was moved out or its borrow ended");
- [Join]'s D65 check with K1(g): a borrow taken in the arm uses its place whole, so the join moves
  the place whole, and dropping it while the result borrows it is rejected (`NK2`, `NU2`, `ND2`,
  `NDR`);
- in tail position the lender must outlive the function, so the dropped place is inside a borrow
  parameter's content: the join's access does end the result's borrow (the run returns `⊥ : &P`),
  and the definition is rejected by D53 when that parameter's borrow ends over a partly moved
  content (`TK`, `TU`). So D53 is what catches the tail case; were it relaxed, [Return] would have to
  reject a `⊥` result of a borrow type.

Since main's D106 (no access ends a borrow a value in flight holds, checked at the one place every
access ends a borrow, `endTopLoan`), the tail case on a known scrutinee (`TK`) is rejected at the
join's access itself, with [Access]'s message, before the borrow can end; on an unknown scrutinee
(`TU`) the match is split, not joined, and D53 still rejects the moving arm. No verdict changed.

Since main's D119 (each world of a split in tail position ends with the match's join, as a known
constructor's arm does) `TU` is rejected for `TK`'s reason, at the join's access in its world `Z`
(before, by D53 in its world `S`). Still rejected; only the message moved.
-/

open Ochr.Test

ochr JoinPrefixBorrow uses Nats {
  inductive L := LNil | LCons(h : Nat, t : L)
  inductive P := MkP(a : L, b : L)
  inductive Q := MkQ(p : P, c : L)
  reject def NK1 (x : P) (y : P) : L := (
    let r0 = &x; let ry = &y; let k = Z;
    let r = match k { Z => r0, S m => (let a = x.1; ry) };
    clone((*r).1))
  reject def NK2 (x : P) (y : P) : L := (
    let k = Z;
    let r = match k { Z => &x, S m => (let a = x.1; &y) };
    clone((*r).1))
  reject def NU1 (n : Nat) (x : P) (y : P) : L := (
    let r0 = &x; let ry = &y;
    let r = match n { Z => r0, S m => (let a = x.1; ry) };
    clone((*r).1))
  reject def NU2 (n : Nat) (x : P) (y : P) : L := (
    let r = match n { Z => &x, S m => (let a = x.1; &y) };
    clone((*r).1))
  reject def NKW (x : P) (y : P) : P := (
    let r0 = &x; let ry = &y; let k = Z;
    let r = match k { Z => r0, S m => (let a = x.1; ry) };
    (*r).1 := LNil;
    x)
  reject def TK (x : &P) (y : &P) : &P := (
    let r0 = &*x; let k = Z;
    match k { Z => r0, S m => (let a = (*x).1; y) })
  reject def TU (n : Nat) (x : &P) (y : &P) : &P := (
    let r0 = &*x;
    match n { Z => r0, S m => (let a = (*x).1; y) })
  reject def ND (x : Q) (y : P) : L := (
    let r0 = &x.0; let ry = &y; let k = Z;
    let r = match k { Z => r0, S m => (let a = (x.0).1; ry) };
    clone((*r).1))
  reject def NP (x : P) (y : P) : L := (
    let r0 = &x; let ry = &y; let k = Z;
    let pr = match k { Z => (r0, Z), S m => (let a = x.1; (ry, Z)) };
    let r = pr.0;
    clone((*r).1))
  reject def ND2 (x : Q) (y : P) : L := (
    let k = Z;
    let r = match k { Z => &x.0, S m => (let a = (x.0).1; &y) };
    clone((*r).1))
  reject def NDR (x : &P) (y : &P) : L := (
    let k = Z;
    let r = match k { Z => &*x, S m => (let a = (*x).1; &*y) };
    clone((*r).1))
  reject def NLB (x : P) (y : P) : L := (
    let rx = &x; let k = Z;
    let r = match k { Z => &*rx, S m => (let a = x.1; &y) };
    clone((*r).1))
  reject def TPair (n : Nat) (x : &P) (y : &P) : &P := (
    let r0 = &*x;
    let pr = match n { Z => (r0, Z), S m => (let a = (*x).1; (y, Z)) };
    pr.0)
}

#guard (run "JoinPrefixBorrow" JoinPrefixBorrow).rejectedWith [
  ("NK1", "[Read] r0 was moved out or its borrow ended"),
  ("NU1", "[Read] r0 was moved out or its borrow ended"),
  ("NKW", "[Read] r0 was moved out or its borrow ended"),
  ("ND", "[Read] r0 was moved out or its borrow ended"),
  ("NP", "[Read] r0 was moved out or its borrow ended"),
  ("TPair", "[Read] r0 was moved out or its borrow ended"),
  ("NLB", "no such place *rx"),
  ("NK2", "[Join] x is moved by another arm of the match"),
  ("NU2", "[Join] x is moved by another arm of the match"),
  ("ND2", "[Join] x.0 is moved by another arm of the match"),
  ("NDR", "[Join] *x is moved by another arm of the match"),
  -- main's D106 (no access ends a borrow a value in flight holds): `TK` is now rejected at the
  -- join's access itself, which used to end the result's borrow and leave D53 to catch it later.
  ("TK", "[Access] reading or writing *x ends a borrow that a value in flight holds"),
  -- main's D119 (the split in tail position joins in each world): `TU` as `TK`
  ("TU", "[Access] reading or writing *x ends a borrow that a value in flight holds")]
