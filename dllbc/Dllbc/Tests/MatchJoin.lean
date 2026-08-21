import Dllbc.ElabCheck
import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program

/-!
# MatchJoin — the joining match (docs/19), accepted/rejected

`let x : τ = match s { … }; rest` — the ascription is the join marker and the
motive. Arms are checked against τ under their own refinements; `rest` is
checked ONCE, from the pre-split environment, with `x` a fresh σ : τ. The pairs
below pin both halves of the claim: what the join buys (one walk, sequential
matches stop multiplying) and what it deliberately costs (the seam forgets
per-arm knowledge — the join is a WEAKENING, and programs that need the arm
facts must carry them in the motive or keep the fork).
-/

namespace Dllbc.Tests.MatchJoin
open Dllbc

/-! ## (1) The headline: sequential joined matches, one continuation walk -/

def seqJoins : Term := prog{
  fn P (n : Nat, m : Nat) -> Unit {
    let b : Bool = match n { Z => True, S(k) => False };
    let c : Bool = match m { Z => True, S(k2) => False };
    let d = b;
    () };
  () }
example : progOk seqJoins = true := by native_decide

/-! ## (2) THE WEAKENING PAIR — the sharpest fork/join distinction there is.

    Both arms return `True`, and the continuation cites `Refl : Id Bool b True`.
    Under the FORK `b` is comptime-known `True` on every path and the citation
    checks. Under the JOIN `b` is an opaque σ : Bool — the seam forgot what the
    arms agreed on, exactly as declared — and the same citation is rejected.
    A program relying on post-match knowledge NOT carried by the motive is the
    docs/19 §5 reliance class, pinned here as a live pair. -/

def agreeFork : Term := prog{
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True, S(k) => True };
    let h = (Refl : Id Bool b True);
    () };
  () }
example : progOk agreeFork = true := by native_decide

def agreeJoin : Term := prog defer_check {
  fn P (n : Nat) -> Unit {
    let b : Bool = match n { Z => True, S(k) => True };
    let h = (Refl : Id Bool b True);
    () };
  () }
example : progRejects agreeJoin "Refl" = true := by native_decide

/-! ## (3) The blind re-split: post-join σb is genuinely symbolic Bool.

    A continuation match on the joined binder must be EXHAUSTIVE — under the
    fork, `b` is concrete per path, no split happens, and the same program
    walks into the missing-branch error instead. Two shapes, two messages,
    both rejections — the join's message is the type-driven one. -/

def blindJoin : Term := prog defer_check {
  fn P (n : Nat) -> Unit {
    let b : Bool = match n { Z => True, S(k) => False };
    match b { True => () } };
  () }
example : progRejects blindJoin "non-exhaustive" = true := by native_decide

def blindFork : Term := prog defer_check {
  fn P (n : Nat) -> Unit {
    let b = match n { Z => True, S(k) => False };
    match b { True => () } };
  () }
example : progRejects blindFork "no branch for constructor" = true := by native_decide

/-! ## (4) A DEPENDENT motive: the type cites the scrutinee, each arm proves it
    at its own constructor (`Id Nat n n` refines to `Id Nat Z Z` and
    `Id Nat (S k) (S k)`), and the joined binder stands at the un-refined σ. -/

def depMotive : Term := prog{
  fn P (n : Nat) -> Unit {
    let e : Id Nat n n = match n { Z => Refl, S(k) => Refl };
    () };
  () }
example : progOk depMotive = true := by native_decide

/-! ## (5) The arm-vs-motive check: a wrong arm is named, not smuggled. -/

def armWrong : Term := prog defer_check {
  fn P (n : Nat) -> Unit {
    let b : Bool = match n { Z => True, S(k) => Z };
    () };
  () }
example : progRejects armWrong "declared motive" = true := by native_decide

/-! ## (6) Borrow-mode join with an arm WRITE (the docs/19 §3.4 risk, as a
    program): the arm writes through a field borrow, the join re-mints the
    payload, the continuation reads and writes back through the parent, and
    the exit audit passes on the joined path. -/

def borrowWrite : Term := prog{
  fn F (v : &mut List Nat) -> Unit {
    let u : Unit = match v { Nil => (), Cons(hd, tl) => { *hd := 0; () } };
    let w = *v;
    *v := w;
    () };
  () }
example : progOk borrowWrite = true := by native_decide

/-! ## (7) Concrete scrutinee: fork ≡ join at one arm — checked AND run.
    The executing side is the differential's guard that `pushJoinArms`
    rebuilds exactly the fork's seam. -/

def concreteJoin : Term := prog{
  let l = Cons(1, Nil);
  let b : Bool = match l { Nil => True, Cons(h, t) => False };
  let y = b;
  () }
example : progOk concreteJoin = true := by native_decide
example : progRunsTo concreteJoin
  [("l", .bot), ("b", .ctor "False" []), ("y", .ctor "False" [])] = true := by native_decide

/-! ## (8) The branch-equation form composes with the motive: `match e2 : n`
    binds the M23 equation per-arm (arm-local — it dies at the seam). -/

def eqnForm : Term := prog{
  fn P (n : Nat) -> Unit {
    let b : Bool = match e2 : n { Z => True, S(k) => False };
    () };
  () }
example : progOk eqnForm = true := by native_decide

/-! ## (9) The join is exhaustiveness-checked like any symbolic split. -/

def joinNonExh : Term := prog defer_check {
  fn P (n : Nat) -> Unit {
    let b : Bool = match n { Z => True };
    () };
  () }
example : progRejects joinNonExh "non-exhaustive" = true := by native_decide

end Dllbc.Tests.MatchJoin
