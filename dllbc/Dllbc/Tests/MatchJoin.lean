import Dllbc.ElabCheck
import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program
import Dllbc.Std
import Dllbc.StdChain

/-!
# MatchJoin — the unconditional join (docs/19 v2), accepted/rejected

Every statement-position symbolic match is JOINED: arms checked terminally
under their refinements exactly as ever, the continuation ONCE from the
pre-split state, each slot and the result by the conservative ladder. No
annotation anywhere in this file — the syntax is exactly main's. Each case
names the ladder rule it exercises.
-/

namespace Dllbc.Tests.MatchJoin
open Dllbc

/-! ## (1) THE HEADLINE — sequential matches stop multiplying (ladder rule 5:
    disagreeing results re-mint as fresh σ : Bool, continuation walked once). -/

def seqJoins : Term := prog{
  fn P (n : Nat, m : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    let c = match m { Z => True, S(k2) => False };
    let d = b;
    () };
  () }
example : progOk seqJoins = true := by native_decide

/-! ## (2) AGREEING ARMS PASS THROUGH LOSSLESSLY (rule 4). Both arms return
    `True`; the continuation cites `Refl : Id Bool b True` and it CHECKS —
    the join costs nothing in knowledge when the arms agree. (v1's motive
    design minted always and rejected this; v2 corrects it.) -/

def agreeArms : Term := prog{
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True, S(k) => True };
    let h = (Refl : Id Bool b True);
    () };
  () }
example : progOk agreeArms = true := by native_decide

/-! ## (3) THE CORRELATION CLASS FLIPS TO REJECTED (docs/19 v2 §3, pinned).
    `N0` snapshots the scrutinee, the flag is re-split, and the True arm cites
    `n ≡ Z` — under the fork the flag was concrete per path, selection kept the
    correlation, and this CHECKED. Under the join the flag is an opaque σ, the
    re-split learns nothing about `n`, and the citation fails. The remedy is
    (5) below: return the evidence as data. -/

def correlClass : Term := prog_parse {
  fn P (n : Nat) -> Unit {
    let N0 = n;
    let b = match n { Z => True, S(k) => False };
    match b { True => { let h = (Refl : Id Nat N0 Z); () }, False => () }
  };
  () }
example : progRejects correlClass "does not have its ascribed type" = true := by
  native_decide

/-! ## (4) BRANCH-DIVERGENT BORROWS STAY REJECTED (rule 7; loan-sets out of
    scope) — with the seam's own message naming the slot and the remedy. -/

def divergentBorrows : Term := prog_parse {
  fn F (c : Bool, x : &mut Nat, y : &mut Nat) -> Unit {
    let r = match c { True => x, False => y };
    *r := 5;
    () };
  () }
example : progRejects divergentBorrows "the arms disagree at the result" = true := by
  native_decide

/-! ## (5) THE DEPENDENT-PACK HEURISTIC, END TO END (rule 6). The arms return
    `Pair(True, e)` / `Pair(False, e)` — the M23 branch equation as DATA. The
    seam anti-unifies the second component's types across the arms
    (`Id Bool (Leb a b) True` / `… False` join at `Id Bool (Leb a b) σf`), so
    the pack needs no annotation. The continuation destructures, re-splits the
    flag, and the True arm's refinement σf := True turns the evidence back
    into `Id Bool (Leb a b) True` — `LebTrueLeRaw` closes it. The heuristic's
    refinement propagation is sensitive to the citation staying a PURE
    APPLICATION in this arm (a call-and-bind through the chain's sealed
    `LebTrueLe`, or any further statement after it that calls another sealed
    `fn`, drops the refinement and the argument no longer converts — probed
    2026-08-24, the raw splice behaves identically regardless of which
    library copy supplies it, so this is not a value difference):
    `Dllbc.StdChainRaw.LebTrueLeRaw` is value-identical to the pre-migration
    copy this file used to cite (`native_decide`-checked), so it stays a
    file-local pure-term ingredient (docs/20 §6 playbook: a
    conversion-sensitive citation can't move to a chain call), spliced from
    the chain's own raw copy. This is the
    correlation class (3), repaired by the language's own idiom. -/

def packEvidence : Term := prog{
  fn NeedLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn P (a : Nat, b : Nat) -> Unit {
    let c = Leb a b;
    let p = match e : c { True => Pair(True, e), False => Pair(False, e) };
    let Pair(flag, ev) = p;
    match flag { True => { NeedLe(a, b, (%(Dllbc.StdChainRaw.LebTrueLeRaw)) a b ev); () }, False => () }
  };
  () }
example : progOk packEvidence = true := by native_decide

/-! ## (6) BORROW-MODE JOIN WITH AN ARM WRITE (rules 3 then 5 on the payload):
    the arm writes through a field borrow, the seam collapses the arm's loans
    and re-mints the disagreeing payload at its own type, the continuation
    round-trips `*v`, and the fn's exit audit passes on the joined path. -/

def borrowWrite : Term := prog{
  fn F (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } };
    let w = *v;
    *v := w;
    () };
  () }
example : progOk borrowWrite = true := by native_decide

/-! ## (7) CONCRETE SCRUTINEE — selection, checked AND run: fork ≡ join at one
    taken arm, and the executing walk (the lazily rebuilt seam shape) leaves
    exactly the envs the pre-pass regime left. -/

def concreteJoin : Term := prog{
  let l = Cons(1, Nil);
  let b = match l { Nil => True, Cons(h, t) => False };
  let y = b;
  () }
example : progOk concreteJoin = true := by native_decide
example : progRunsTo concreteJoin
  [("l", .bot), ("b", .ctor "False" []), ("y", .ctor "False" [])] = true := by
  native_decide

/-! ## (8) The join is exhaustiveness-checked like any symbolic split. -/

def joinNonExh : Term := prog_parse {
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True };
    () };
  () }
example : progRejects joinNonExh "non-exhaustive" = true := by native_decide

/-! ## (9) THE ONE-BRANCH MATCH IS LOSSLESS (fork ≡ join at N=1): a Σ
    destructure keeps its field σs and their knowledge across the statement —
    the pervasive `let Pair(a, b) = p` idiom is untouched by the join. -/

def singleArm : Term := prog{
  fn P (q : Σ (a : Nat). Id Nat a a) -> Unit {
    let Pair(a, h) = q;
    let h2 = (h : Id Nat a a);
    () };
  () }
example : progOk singleArm = true := by native_decide

end Dllbc.Tests.MatchJoin
