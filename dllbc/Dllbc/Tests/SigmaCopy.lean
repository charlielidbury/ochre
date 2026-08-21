import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.SigmaCopy` — when a Σ pack is Copy

This file tests when a Σ pack is Copy: a pack copies iff every component is
copyable or erased, where erased means the Σ marked the position comptime (a
capital binder marks the domain, `Σ0` marks the tail) AND the position is
erasure-bound — index-kind, or a type whose constructors the machine does not
know.

Scalars-with-proofs (refinement packs like machine integers) are morally
scalars and should not cost a move-staging at every reuse, while packs holding
real data must keep the move discipline that makes aggregate duplication
visible.

Four groups of programs are checked below: the positive cases (packs that
copy), the negative cases (packs that still move, and why), the differential
(the checking and executing machines agree on the same packs), and a
composite example (`try_resize`, a hashmap growth guard) showing the feature
removing real staging from a realistic body.
-/

namespace Dllbc.Tests.SigmaCopy

open Dllbc
open Dllbc.StdLemmas (LeTransRaw LeAddRaw LebTrueLeRaw IdCongrRaw IdSymRaw LeRwLRaw)

/-! ## (i) Positive and negative cases, one binding used twice

    Every probe here is the same program with one thing changed: the type of the
    pack. `Snk` takes it by value, so a call MOVES it unless the pack is Copy, and
    calling `Snk` twice from one binding therefore reads "this type is Copy" as an
    acceptance and "this type moves" as a use-after-move rejection. -/

/-- A pair of `Nat`s copies: both components are index-kind, so the pack is,
    and calling `Snk` twice from the same binding is accepted. -/
def pairNatTwice : Term := prog{
  fn Snk (p : (Σ (a : Nat). Nat)) -> Unit { () };
  fn Chain (p : (Σ (a : Nat). Nat)) -> Unit { let x = Snk(p); let y = Snk(p); () };
  () }
example : progOk pairNatTwice = true := by native_decide

/-- A pack with a `List` in it moves: one component is real data, so the
    aggregate is, and duplicating it would be exactly the silent copy the move
    discipline exists to prevent. The negative control for the probe above —
    the two programs differ only in that one type. -/
def pairListTwice : Term := prog defer_check {
  fn Snk (p : (Σ (a : Nat). List Nat)) -> Unit { () };
  fn Chain (p : (Σ (a : Nat). List Nat)) -> Unit { let x = Snk(p); let y = Snk(p); () };
  () }
example : progRejects pairListTwice "p#0 holds ⊥ (use-after-move" = true := by native_decide

/-- The slice pack `Σ (c : Nat). &mut (Array c Nat)` still moves: a borrow
    component is neither copyable nor erased, and copying the pack would hand
    out two owners of one payload — exactly what the move discipline exists to
    prevent.

    A slice-pack parameter is seeded as `ctor "Pair" [know σ_c, borrowM ℓ …]`,
    and `Val.ctor` collapses a node to a knowledge leaf only when every child is
    knowledge, so this value never reaches the `Pair` rule at all — it takes
    `indexKindV`'s `node` answer, which is MOVE. -/
def sliceTwice : Term := prog defer_check {
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  fn Twice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit {
    let x = SliceTouch(s); let y = SliceTouch(s); () };
  () }
example : progRejects sliceTwice "s#0 holds ⊥ (use-after-move" = true := by native_decide

/-! ## (ii) The refinement pack the feature is for

    `U MAX := Σ0 (n : Nat). Le n MAX` is a bounded machine integer: a runtime
    `Nat` and a comptime proof that it is in range. It is Copy: the value half
    is index-kind, and the proof half is marked by the `0` and erasure-bound,
    because `Le n MAX` under an opaque `n` is a stuck spine whose constructor
    set the machine does not know.

    `Val`, the first projection, is all the library this file needs. `U MAX`
    itself is not written at an `elim` motive, because the elim sugar reads a
    Σ's domain and family off the binder's type syntactically, so the pack
    would have to be respelled at every elimination. -/

def Val : Term := prog defer_check {
  λ (MAX : Nat). λ (A : Σ0 (n : Nat). Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat). Le n MAX). Nat) { Pair (x) (h) => x } }

/-- A `U 15` local is used from two consuming calls with no staging in between,
    and is accepted: the refinement pack is Copy, so a machine integer behaves
    like a scalar rather than an ordinary owned pair. -/
def packTwice : Term := prog{
  fn Snk (p : (Σ0 (n : Nat). Le n 15)) -> Nat { Val 15 p };
  fn Chain (p : (Σ0 (n : Nat). Le n 15)) -> Nat { let a = Snk(p); let b = Snk(p); b };
  () }
example : progOk packTwice = true := by native_decide

/-- A nested qualifying pack, with the marker at the other end: the inner Σ's
    binder is capital, which marks its domain as erased, exactly as `Σ0` marks a
    tail. Both spellings of "this position is erased" are exercised here, and
    the recursion through the nesting costs the rule no case of its own. -/
def nestedPackTwice : Term := prog{
  fn Snk (p : (Σ (n : Nat). Σ (H : Le n 15). Unit)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Σ (H : Le n 15). Unit)) -> Unit {
    let a = Snk(p); let b = Snk(p); () };
  () }
example : progOk nestedPackTwice = true := by native_decide

/-! ### Two spellings that look close but still move

    Both packs below are one character away from a pack that copies, and both
    move because the rule asks for the marker and never tries to infer from a
    type alone whether a component is a proof: a stuck recursor spine like
    `Le n MAX` under an opaque `n` has no head to recognize, and a σ typed by a
    stuck `VecF Nat n` is the same shape, so "stuck spine to `Type` ⇒ copy"
    would also copy a vector. -/

/-- An unmarked proposition component moves. `Σ (n : Nat). Le n 15` — the same
    pack as `U 15` with the `0` deleted — is a `Nat` and a runtime proof, and a
    runtime proof of a stuck-typed proposition is not index-kind. There has to
    be a way to say "erased"; there is no way to guess it. -/
def unmarkedPropTwice : Term := prog defer_check {
  fn Snk (p : (Σ (n : Nat). Le n 15)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Le n 15)) -> Unit { let a = Snk(p); let b = Snk(p); () };
  () }
example : progRejects unmarkedPropTwice "p#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-- The proof-in-the-domain spelling with a lowercase binder also moves.
    `Σ (n : Nat). Σ0 (h : Le n 15). Unit` looks like a refinement pack and is
    not one: `Σ0` marks the tail, so what is erased here is the `Unit`, while
    the proof sits at a lowercase binder — a runtime component of stuck type.
    Capitalise that binder and the pack copies (`nestedPackTwice` above is that
    program): the two read alike, and the marker is the whole difference. -/
def tailMarkedWrongEndTwice : Term := prog defer_check {
  fn Snk (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit {
    let a = Snk(p); let b = Snk(p); () };
  () }
example : progRejects tailMarkedWrongEndTwice "p#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-! ## (iii) The differential — the two machines classify the same pack

    A copy rule is the kind of rule the two machines can disagree about, because
    they meet the pack in two representations: the checking machine holds a
    parameter as a σ and asks `indexKindTy` of its type, while the executing
    machine holds a concrete `Pair(3, unit)` and asks `indexKindT`'s Pair rule
    of the value. So the programs below are checked and run, and both
    representations are exercised in each: the top-level `let` builds a
    concrete pack and consumes it twice, and the callee it hands it to consumes
    its parameter twice again. -/

/-- Two consuming calls on a concrete pack at the top level, and two more on the
    same pack as a callee's parameter — so the σ rule and the value rule are
    both load-bearing in one program. `3 + 3 = 6` twice over. -/
def packConcreteTwice : Term := prog{
  fn Snk (p : (Σ0 (n : Nat). Le n 15)) -> Nat { Val 15 p };
  fn Chain (p : (Σ0 (n : Nat). Le n 15)) -> Nat { let a = Snk(p); let b = Snk(p); Add a b };
  let q = Pair(3, unit);
  let out = Chain(q);
  let out2 = Chain(q);
  () }
example : progOk packConcreteTwice = true := by native_decide
example : (match runProgram packConcreteTwice with
           | .ok env => (env.lookup "out") == some (Val.nat 6)
                        && (env.lookup "out2") == some (Val.nat 6)
           | .error _ => false) = true := by native_decide

/-- The same shape at a bare pair of `Nat`s, so the copy is asserted executing
    as well as checking. -/
def pairNatConcreteTwice : Term := prog{
  fn Fst (p : (Σ (a : Nat). Nat)) -> Nat { elim p return (λ (Q : Σ (a : Nat). Nat). Nat) {
    Pair (x) (y) => x } };
  let q = Pair(4, 7);
  let out = Fst(q);
  let out2 = Fst(q);
  () }
example : progOk pairNatConcreteTwice = true := by native_decide
example : (match runProgram pairNatConcreteTwice with
           | .ok env => (env.lookup "out") == some (Val.nat 4)
                        && (env.lookup "out2") == some (Val.nat 4)
           | .error _ => false) = true := by native_decide

/-- The negative control, executing: a pack with a `List` in it is refused on
    the second consuming call, at a concrete value rather than at a σ. The two
    machines agree about the move as well as about the copy. -/
def pairListConcreteTwice : Term := prog defer_check {
  fn Snk (p : (Σ (a : Nat). List Nat)) -> Unit { () };
  let q = Pair(4, Cons(1, Nil));
  let out = Snk(q);
  let out2 = Snk(q);
  () }
example : progRejects pairListConcreteTwice "q#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-! ### Why the marker alone is not enough: a marked component of aggregate type

    If a marked position were exempt unconditionally, the program below would
    be accepted by the checker and then fail at runtime, because the checker
    holds the callee's parameter as a σ and asks of its type — where the `Σ0`
    marker is visible — while the executing machine holds a concrete
    `Pair(3, Cons(1, Nil))` and asks of the value, where a component carries no
    marker at all. A marked position is therefore only exempt when it is also
    erasure-bound: index-kind, or a type whose constructor set the machine does
    not know (a stuck proposition spine like `Le n MAX`, whose concrete
    inhabitants are `unit`/`Refl` and so index-kind on the value side too).
    `List Nat` has a known constructor set and is not index-kind, so it is not
    exempt and both machines move the pack. -/

/-- Used twice: refused, and refused for the same reason in both machines. -/
def packListTail : Term := prog defer_check {
  fn Snk (p : (Σ0 (n : Nat). List Nat)) -> Unit { () };
  fn Chain (p : (Σ0 (n : Nat). List Nat)) -> Unit { let a = Snk(p); let b = Snk(p); () };
  let q = Pair(3, Cons(1, Nil));
  let o = Chain(q);
  () }
example : progRejects packListTail "p#0 holds ⊥ (use-after-move" = true := by native_decide

/-- Used once: accepted and runs, so the rejection above is about the second
    use and not about the type being unusable. -/
def packListTailOnce : Term := prog{
  fn Snk (p : (Σ0 (n : Nat). List Nat)) -> Nat { 7 };
  let q = Pair(3, Cons(1, Nil));
  let out = Snk(q);
  () }
example : progOk packListTailOnce = true := by native_decide
example : (match runProgram packListTailOnce with
           | .ok env => (env.lookup "out") == some (Val.nat 7)
           | .error _ => false) = true := by native_decide

/-! ## (iv) The composite — `try_resize` without the staging

    This is the Aeneas hashmap's growth guard: an `if` whose condition licenses
    the arithmetic, a certified op whose return type says what its result is
    (so the next operation's precondition can cite it), and a result that pairs
    the new capacity with the recomputed load.

    Without the Copy rule, a value that is both consumed by a call and used
    again afterward has to be staged first as a copyable `Nat` and a comptime
    bound, since a pack cannot otherwise be used twice, and the returned pack
    has to be re-minted from the staged halves. The version below needs none
    of that staging, because every pack involved is Copy. Every ownership
    event of the original guard survives here: two consuming calls on pack
    parameters, a proof built after the call that consumed the values it
    cites, and a returned pack the body uses again after handing it away.

    The arithmetic is `Add`, standing in for the original's `Mul`/`Div` — those
    lemmas are not in `StdLemmas`, and porting them would add nothing to the
    staging point this file is making. -/

/-- The certified addition: `H` is the caller's obligation that the sum is in
    range, and the `Id` in the tail is what lets the next operation's
    precondition mention this result (a call is opaque, so `-> U MAX` alone
    would say only "some number in range"). `Refl` proves it — the ι-rule
    fires on the pack the body just built. -/
def uAddC (tail : Term) : Term := prog{
  fn AddUC (MAX : Nat, a : (Σ0 (n : Nat). Le n MAX), b : (Σ0 (n : Nat). Le n MAX),
            H : Le (Add (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (r : (Σ0 (n : Nat). Le n MAX))
            . Id Nat (Val MAX r) (Add (Val MAX a) (Val MAX b)))
      { Pair(Pair(Add (Val MAX a) (Val MAX b), H), Refl) };
  %tail }

example : progOk (uAddC prog defer_check { () }) = true := by native_decide

/-- The growth guard, staging-free. `capacity` and `growth` are both consumed
    by the first call and both cited after it; `nc` is consumed by the second
    call and returned after it — with no capture-before-consume bindings
    needed. -/
def grow (tail : Term) : Term := uAddC prog{
  fn Grow (MAX : Nat,
           capacity : (Σ0 (n : Nat). Le n MAX),
           growth : (Σ0 (n : Nat). Le n MAX),
           mload : (Σ0 (n : Nat). Le n MAX))
      -> (Σ (c2 : (Σ0 (n : Nat). Le n MAX)). (Σ0 (n : Nat). Le n MAX))
      { if hg : Leb (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth)) MAX {
          let HBig = LebTrueLeRaw
                       (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                       MAX hg;
          let HA = LeTransRaw (Add (Val MAX capacity) (Val MAX growth))
                     (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth)) MAX
                     (LeAddRaw (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                     HBig;
          let Pair(nc, Enc) = AddUC(MAX, capacity, growth, HA);
          -- `capacity` and `growth` were both moved by the call above, and both
          -- are named here directly, with no staging beforehand.
          let HB = LeRwLRaw MAX
                     (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                     (Add (Val MAX nc) (Val MAX growth))
                     (IdCongrRaw Nat Nat (λ (X : Nat). Add X (Val MAX growth))
                       (Add (Val MAX capacity) (Val MAX growth)) (Val MAX nc)
                       (IdSymRaw Nat (Val MAX nc)
                         (Add (Val MAX capacity) (Val MAX growth)) Enc))
                     HBig;
          -- The result is the pack itself, after the call that consumed it —
          -- not a re-mint from staged halves.
          let Pair(nd, End) = AddUC(MAX, nc, growth, HB);
          Pair(nc, nd)
        } else {
          Pair(capacity, mload)
        } };
  %tail }

example : progOk (grow prog defer_check { () }) = true := by native_decide

/-! ### It runs, on both branches

    `MAX = 15`, growth 2. At capacity 3 the guard `3 + 2 + 2 ≤ 15` holds, so the
    new capacity is 5 and the recomputed load is 7. At capacity 13 it does not
    (`13 + 2 + 2 = 17`), so capacity and load come back untouched. -/

def growCall (m cap g ml : Nat) : Term := grow prog{
  let cP = Pair(%(Term.nat cap), unit);
  let gP = Pair(%(Term.nat g), unit);
  let mP = Pair(%(Term.nat ml), unit);
  let Pair(a, b) = Grow(%(Term.nat m), cP, gP, mP);
  let out = Val %(Term.nat m) a;
  let out2 = Val %(Term.nat m) b;
  () }

def growOut (t : Term) (a b : Nat) : Bool :=
  match runProgram t with
  | .ok env => (env.lookup "out") == some (Val.nat a) && (env.lookup "out2") == some (Val.nat b)
  | .error _ => false

-- The guard holds: capacity 3 grows to 5, load recomputes to 7.
example : progOk (growCall 15 3 2 0) = true := by native_decide
example : growOut (growCall 15 3 2 0) 5 7 = true := by native_decide
-- The guard fails: capacity 13 and load 9 come back unchanged.
example : progOk (growCall 15 13 2 9) = true := by native_decide
example : growOut (growCall 15 13 2 9) 13 9 = true := by native_decide

end Dllbc.Tests.SigmaCopy
