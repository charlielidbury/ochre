import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.SigmaCopy` — the Σ pack that is Copy (M34)

§2.1's copy-on-read used to stop at the constructor: a `Nat`, a `Bool`, a proof, a
type and a λ read by COPY, and everything a constructor built read by MOVE. That
line is Rust's, and the reason for it — silent aggregate duplication is exactly the
cost the move discipline makes visible — is unchanged for lists, arrays and user
data.

It was drawn one shape too wide. Rust ALSO copies a struct of scalars
(`#[derive(Copy)]`), and DLLBC's version of that struct is the Σ pack: a machine
integer written as a refinement over `Nat` (`Σ0 (n : Nat). Le n MAX`, the shape the
finite-ints library is built on) is a runtime number and an erased proof, which is
morally a scalar and was costing a capture-before-consume staging at every reuse.

**The amended rule, in one sentence: a Σ pack copies iff every component is
copyable or erased.** Erased means two things, and the second was learned here
rather than designed: the producing Σ marked that position comptime — a capital
binder marks the domain, `Σ0` marks the tail — AND the position is *erasure-bound*,
which is index-kind or a type whose constructor set the machine does not know. The
marker alone is the honest semantics and is not a fact both machines can read;
§(iii)'s differential caught that as a program the checker accepted and the run got
stuck on.

Four things are pinned below, in order:

  * the POSITIVE cases — a pair of `Nat`s, a `U MAX`-shaped refinement pack, and a
    nested one — used twice from one binding, with no staging;
  * the NEGATIVE cases — a pack with a `List` in it, the M24 slice pack
    `Σ (c : Nat). &mut (Array c Nat)`, and the two spellings whose components are
    unmarked propositions — which still move, each for its own reason;
  * the DIFFERENTIAL — the same packs in the executing machine, run to a value, so
    that the two machines' copy rules are asserted to agree rather than assumed to;
  * the COMPOSITE — `try_resize`, the Aeneas hashmap's growth guard, ported from
    the finite-ints lane WITHOUT that lane's four capture-before-consume bindings,
    which is the ergonomic claim as a program that checks.
-/

namespace Dllbc.Tests.SigmaCopy

open Dllbc
open Dllbc.StdLemmas (LeTrans LeAdd LebTrueLe IdCongr IdSym LeRwL)

/-! ## (i) The micro-battery — one binding, two consuming calls

    Every probe here is the same program with one thing changed: the type of the
    pack. `Snk` takes it by value, so a call MOVES it unless the pack is Copy, and
    calling `Snk` twice from one binding therefore reads "this type is Copy" as an
    acceptance and "this type moves" as a use-after-move rejection. -/

/-- **A pair of `Nat`s copies.** This is the deferral that M34 closes: the note at
    `indexKindT` used to read "DEFERRED (until measured pain): tuple-of-copyables
    (a `Pair Nat Nat` as Copy, Rust-style) — a data ctor all of whose fields are
    index-kind stays a MOVE for now." **THE NEEDLE MOVED**: both components are
    index-kind, so the pack is, and this is accepted where it was a
    use-after-move. -/
def pairNatTwice : Term := prog{
  fn Snk (p : (Σ (a : Nat). Nat)) -> Unit { () };
  fn Chain (p : (Σ (a : Nat). Nat)) -> Unit { let x = Snk(p); let y = Snk(p); () };
  () }
example : progOk pairNatTwice = true := by native_decide

/-- **A pack with a `List` in it MOVES** — Rust's line, exactly where Rust draws
    it. One component is data proper, so the aggregate is, and duplicating it
    would be the silent copy §2.1 exists to prevent. The negative control for the
    probe above: the two programs differ in one type. -/
def pairListTwice : Term := prog defer_check {
  fn Snk (p : (Σ (a : Nat). List Nat)) -> Unit { () };
  fn Chain (p : (Σ (a : Nat). List Nat)) -> Unit { let x = Snk(p); let y = Snk(p); () };
  () }
example : progRejects pairListTwice "p#0 holds ⊥ (use-after-move" = true := by native_decide

/-- **THE SOUNDNESS EDGE**: the M24 slice pack `Σ (c : Nat). &mut (Array c Nat)`
    still moves. A borrow component is neither copyable nor erased, and copying
    the pack would hand out two owners of one payload — the E0382 class the whole
    index-kind rule exists to prevent, at the one shape the M34 relaxation comes
    nearest to.

    The representation is what states it rather than a guard: a slice-pack
    parameter is seeded as `ctor "Pair" [know σ_c, borrowM ℓ …]`, and `Val.ctor`
    collapses a node to a knowledge leaf only when EVERY child is knowledge, so
    this value never reaches the `Pair` rule at all — it takes `indexKindV`'s
    `node` answer, which is and was MOVE. -/
def sliceTwice : Term := prog defer_check {
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  fn Twice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit {
    let x = SliceTouch(s); let y = SliceTouch(s); () };
  () }
example : progRejects sliceTwice "s#0 holds ⊥ (use-after-move" = true := by native_decide

/-! ## (ii) The refinement pack — the shape the feature is FOR

    `U MAX := Σ0 (n : Nat). Le n MAX` is the finite-ints lane's bounded machine
    integer: a runtime `Nat` and a comptime proof that it is in range. Under the
    amended rule it is Copy — the value half is index-kind, and the proof half is
    marked by the `0` and erasure-bound, because `Le n MAX` under an opaque `n` is
    a stuck spine whose constructor set the machine does not know. That is the
    sentence "a `usize` is `Copy`" arriving in DLLBC by way of the type rather than
    by way of a trait.

    `Val`, the first projection, is ported from the lane and is all the library
    this file needs. The lane's `U` and `Bnd` are not here: `U MAX` cannot be
    written at an `elim` motive (the sugar reads the Σ's domain and family off the
    binder's type syntactically, so the pack is respelled at every elimination),
    and `Bnd` exists in the lane to STAGE a pack's bound before the call that
    consumes it — which is the binding this feature removes. -/

def Val : Term := prog defer_check {
  λ (MAX : Nat). λ (A : Σ0 (n : Nat). Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat). Le n MAX). Nat) { Pair (x) (h) => x } }

/-- **THE NEEDLE MOVED, and this is the headline.** Ported VERBATIM from the
    finite-ints lane's `packTwice`, where the assertion reads
    `progRejects packTwice "use-after-move"` and the surrounding note reads "a
    `U MAX` local may not [be passed to two calls] — the pack is an ordinary owned
    pair, so a call that takes it by value MOVES it, and the second use finds ⊥".
    That was the lane's sharpest finding — "a machine integer wants to be `Copy`
    and a Σ pack is affine" — and it is what M34 answers. -/
def packTwice : Term := prog{
  fn Snk (p : (Σ0 (n : Nat). Le n 15)) -> Nat { Val 15 p };
  fn Chain (p : (Σ0 (n : Nat). Le n 15)) -> Nat { let a = Snk(p); let b = Snk(p); b };
  () }
example : progOk packTwice = true := by native_decide

/-- A NESTED qualifying pack, with the marker at the other end: the inner Σ's
    binder is CAPITAL, which puts `⇝` on its domain (M32 R3b) exactly as `Σ0`
    puts it on a tail. Both spellings of "this position is erased" are therefore
    exercised, and the recursion through the nesting costs the rule no case of its
    own. -/
def nestedPackTwice : Term := prog{
  fn Snk (p : (Σ (n : Nat). Σ (H : Le n 15). Unit)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Σ (H : Le n 15). Unit)) -> Unit {
    let a = Snk(p); let b = Snk(p); () };
  () }
example : progOk nestedPackTwice = true := by native_decide

/-! ### The two spellings that still MOVE, and why each is right

    Both are one character from a pack that copies, and both move because the rule
    asks for the MARKER and never tries to work out from a type alone whether a
    component is a proof. That second thing is what makes these decidable at all:
    `Le n MAX` under an opaque `n` is a stuck recursor spine with no head to
    recognize, and `Direct.lean`'s pain diary already ruled on it — a naive
    "stuck-recursor-to-`Type` ⇒ copy" is DEAD, because a σ typed by a stuck
    `VecF Nat n` is that same shape and copying it copies a vector. -/

/-- **An UNMARKED proposition component moves.** `Σ (n : Nat). Le n 15` — the same
    pack as `U 15` with the `0` deleted — is a `Nat` and a RUNTIME proof, and a
    runtime proof of a stuck-typed proposition is not index-kind. This is §2.1's
    long-standing "proofs move because `indexKindTy` does not recognize stuck
    proposition spines" reaching the Σ rule unchanged: M34 adds a way to say
    "erased", it does not add a way to guess it. -/
def unmarkedPropTwice : Term := prog defer_check {
  fn Snk (p : (Σ (n : Nat). Le n 15)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Le n 15)) -> Unit { let a = Snk(p); let b = Snk(p); () };
  () }
example : progRejects unmarkedPropTwice "p#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-- **And so does the proof-in-the-DOMAIN spelling with a lowercase binder.**
    `Σ (n : Nat). Σ0 (h : Le n 15). Unit` looks like a refinement pack and is not
    one: `Σ0` marks the TAIL, so what is erased here is the `Unit`, while the
    proof sits at a lowercase binder — a runtime component of stuck type. Capitalise
    that binder and the pack copies (`nestedPackTwice` above is that program).
    Pinned because the two read alike and the mode is the whole difference. -/
def tailMarkedWrongEndTwice : Term := prog defer_check {
  fn Snk (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit {
    let a = Snk(p); let b = Snk(p); () };
  () }
example : progRejects tailMarkedWrongEndTwice "p#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-! ## (iii) The differential — the two machines classify the same pack

    A copy rule is exactly the kind of rule the two machines can disagree about,
    because they meet the pack in two representations: the CHECKING machine holds
    a parameter as a σ and asks `indexKindTy` of its TYPE, while the EXECUTING
    machine holds a concrete `Pair(3, unit)` and asks `indexKindT`'s Pair rule of
    the VALUE. The repo's copy-on-read history says this seam is where a wrong
    copy rule shows up, so the programs below are checked AND run, and both
    representations are exercised in each: the top-level `let` builds a concrete
    pack and consumes it twice, and the callee it hands it to consumes its
    parameter twice again. -/

/-- Two consuming calls on a CONCRETE pack at the top level, and two more on the
    same pack as a callee's parameter — so the σ rule and the value rule are both
    load-bearing in one program. `3 + 3 = 6` twice over. -/
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

/-- The same shape at a bare pair of `Nat`s, so the closed deferral is asserted
    executing as well as checking. -/
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

/-- …and the negative control, executing: a pack with a `List` in it is refused
    on the SECOND consuming call, at a concrete value rather than at a σ. The two
    machines agree about the move as well as about the copy. -/
def pairListConcreteTwice : Term := prog defer_check {
  fn Snk (p : (Σ (a : Nat). List Nat)) -> Unit { () };
  let q = Pair(4, Cons(1, Nil));
  let out = Snk(q);
  let out2 = Snk(q);
  () }
example : progRejects pairListConcreteTwice "q#0 holds ⊥ (use-after-move" = true := by
  native_decide

/-! ### The differential's one real finding: a marked component of AGGREGATE type

    Written with the marker alone doing the exempting, the rule ACCEPTED the
    program below and the run then died at `readR: p#0 holds ⊥`. The break is
    structural rather than incidental: the checker holds the callee's parameter as
    a σ and asks of its TYPE, where the `Σ0` marker is visible; the executing
    machine holds `Pair(3, Cons(1, Nil))` and asks of the VALUE, where a concrete
    component carries no mode anywhere. Marker-alone is therefore not a fact both
    machines can read.

    `erasureBound` is the closure: a marked position is exempt only when it is
    erasure-bound as §2.1 already means it — index-kind, or a type whose
    constructor set the machine does not know (a stuck proposition spine like
    `Le n MAX`, whose concrete inhabitants are `unit`/`Refl` and so index-kind on
    the value side too). `List Nat` has a known constructor set and is not
    index-kind, so it is not exempt and BOTH machines move the pack. -/

/-- Used TWICE: refused, and refused for the same reason in both machines. -/
def packListTail : Term := prog defer_check {
  fn Snk (p : (Σ0 (n : Nat). List Nat)) -> Unit { () };
  fn Chain (p : (Σ0 (n : Nat). List Nat)) -> Unit { let a = Snk(p); let b = Snk(p); () };
  let q = Pair(3, Cons(1, Nil));
  let o = Chain(q);
  () }
example : progRejects packListTail "p#0 holds ⊥ (use-after-move" = true := by native_decide

/-- Used ONCE: accepted and runs, so the rejection above is about the second use
    and not about the type being unusable. -/
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

    The finite-ints lane's port of the Aeneas hashmap's growth guard carries this
    note, and it is the ergonomic claim M34 is answering:

        THE OWNERSHIP STAGING, which is the ergonomic cost: `nc` is returned AND
        fed to the second multiplication, and a pack cannot be used twice. So its
        two halves are staged as a copyable `Nat` and a comptime bound before the
        call that consumes it, and the returned pack is re-minted from them. Rust
        needs none of this because `usize` is `Copy`.

    Four bindings pay that tax in the lane's body — `let cv = Val MAX capacity`,
    `let gv = Val MAX growth`, `let ncv = Val MAX nc`, `let Hncb = Bnd MAX nc`
    (the lane's `Bnd` is the pack's second projection) — and the version below has
    NONE of them. The guard's shape is ported whole:
    an `if` whose condition is what licenses the arithmetic, a certified op whose
    return type says what its result IS (so the next operation's precondition can
    cite it), and a result that pairs the new capacity with the recomputed load.

    The arithmetic is `Add` where the lane's is `Mul`/`Div`, because `Mul`, `Div`
    and their lemmas live in the lane and not in `StdLemmas` — porting them would
    duplicate that lane's library on this branch for no gain, and the STAGING is
    what this file is about. Every ownership event of the original survives the
    substitution: two consuming calls on pack parameters, a proof built after the
    call that consumed the values it cites, and a returned pack the body used
    again after handing it away.

    **The four eliminated bindings, by name and site.**

      * `cv`/`gv` — the lane stages `Val MAX capacity` and `Val MAX growth` before
        the first op because that op MOVES both. Here `HB` cites them afterwards,
        directly.
      * `ncv`/`Hncb` — the lane stages the new capacity's value and its bound
        before the second op, then re-mints `Pair(ncv, Hncb)` for the result.
        Here the result is `Pair(nc, nd)`: the pack itself, used again after the
        call that consumed it. -/

/-- The certified addition: `H` is the caller's obligation that the sum is in
    range, and the `Id` in the tail is what lets the NEXT operation's precondition
    mention this result (a call is opaque, so `-> U MAX` alone would say only
    "some number in range"). `Refl` proves it — the ι-rule fires on the pack the
    body just built. -/
def uAddC (tail : Term) : Term := prog{
  fn AddUC (MAX : Nat, a : (Σ0 (n : Nat). Le n MAX), b : (Σ0 (n : Nat). Le n MAX),
            H : Le (Add (Val MAX a) (Val MAX b)) MAX)
      -> (Σ0 (r : (Σ0 (n : Nat). Le n MAX))
            . Id Nat (Val MAX r) (Add (Val MAX a) (Val MAX b)))
      { Pair(Pair(Add (Val MAX a) (Val MAX b), H), Refl) };
  %tail }

example : progOk (uAddC prog defer_check { () }) = true := by native_decide

/-- **THE COMPOSITE, staging-free.** `capacity` and `growth` are both consumed by
    the first call and both cited after it; `nc` is consumed by the second call
    and returned after it. On the lane this body needs four capture-before-consume
    bindings and here it needs none — which is the whole of the feature, written
    as a program that checks. -/
def grow (tail : Term) : Term := uAddC prog{
  fn Grow (MAX : Nat,
           capacity : (Σ0 (n : Nat). Le n MAX),
           growth : (Σ0 (n : Nat). Le n MAX),
           mload : (Σ0 (n : Nat). Le n MAX))
      -> (Σ (c2 : (Σ0 (n : Nat). Le n MAX)). (Σ0 (n : Nat). Le n MAX))
      { if hg : Leb (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth)) MAX {
          let HBig = LebTrueLe
                       (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                       MAX hg;
          let HA = LeTrans (Add (Val MAX capacity) (Val MAX growth))
                     (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth)) MAX
                     (LeAdd (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                     HBig;
          let Pair(nc, Enc) = AddUC(MAX, capacity, growth, HA);
          -- **`cv`/`gv` ELIMINATED.** `capacity` and `growth` were both MOVED by
          -- the call above, and both are named here — this is the line the lane
          -- has to stage two bindings for.
          let HB = LeRwL MAX
                     (Add (Add (Val MAX capacity) (Val MAX growth)) (Val MAX growth))
                     (Add (Val MAX nc) (Val MAX growth))
                     (IdCongr Nat Nat (λ (X : Nat). Add X (Val MAX growth))
                       (Add (Val MAX capacity) (Val MAX growth)) (Val MAX nc)
                       (IdSym Nat (Val MAX nc)
                         (Add (Val MAX capacity) (Val MAX growth)) Enc))
                     HBig;
          -- **`ncv`/`Hncb` ELIMINATED.** The result is the pack itself, after the
          -- call that consumed it — not a re-mint from staged halves.
          let Pair(nd, End) = AddUC(MAX, nc, growth, HB);
          Pair(nc, nd)
        } else {
          Pair(capacity, mload)
        } };
  %tail }

example : progOk (grow prog defer_check { () }) = true := by native_decide

/-! ### It RUNS, on both branches

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
