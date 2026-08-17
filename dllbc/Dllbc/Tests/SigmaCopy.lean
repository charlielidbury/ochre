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
copyable or erased.** Erased means the producing Σ marked that position comptime —
a capital binder marks the domain, `Σ0` marks the tail — and a marked position is
free because it is erased, so duplicating it duplicates nothing at runtime.

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
open Dllbc.StdLemmas (LeRefl LeTrans LeAdd LebTrueLe IdCongr IdSym LeRwL)

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
def pairListTwice : Term := prog{
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
def sliceTwice : Term := prog{
  fn SliceTouch (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit { () };
  fn Twice (s : Σ (c : Nat). &mut (Array c Nat)) -> Unit {
    let x = SliceTouch(s); let y = SliceTouch(s); () };
  () }
example : progRejects sliceTwice "s#0 holds ⊥ (use-after-move" = true := by native_decide

/-! ## (ii) The refinement pack — the shape the feature is FOR

    `U MAX := Σ0 (n : Nat). Le n MAX` is the finite-ints lane's bounded machine
    integer: a runtime `Nat` and a comptime proof that it is in range. Under the
    amended rule it is Copy — the value half is index-kind, the proof half is
    marked by the `0` — which is the sentence "a `usize` is `Copy`" arriving in
    DLLBC by way of the marker rather than by way of a trait. -/

/-- `U : Nat → Type`, ported from the finite-ints lane. -/
def U : Term := prog{ λ (MAX : Nat). Σ0 (n : Nat). Le n MAX }

/-- The underlying `Nat`. The motive cannot be written `U MAX` — the `elim` sugar
    reads the Σ's domain and family off the binder's type syntactically — so the
    pack is respelled at every elimination, as it is in the lane. -/
def Val : Term := prog{
  λ (MAX : Nat). λ (A : Σ0 (n : Nat). Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat). Le n MAX). Nat) { Pair (x) (h) => x } }
def ValTy : Term := prog{ Π (MAX : Nat) → (Σ0 (n : Nat). Le n MAX) → Nat }

/-- The bound, recovered from a pack — the dependent second projection. -/
def Bnd : Term := prog{
  λ (MAX : Nat). λ (A : Σ0 (n : Nat). Le n MAX).
    elim A return (λ (Q : Σ0 (n : Nat). Le n MAX). Le (Val MAX Q) MAX) {
      Pair (x) (h) => h } }
def BndTy : Term := prog{
  Π (MAX : Nat) → Π (A : Σ0 (n : Nat). Le n MAX) → Le (Val MAX A) MAX }

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

    Both are one character from a pack that copies, and the rule reads the MARKER
    rather than the type's inhabitants — which is what makes these decidable at
    all, since `Le n MAX` under an opaque `n` is a stuck recursor spine with no
    head to recognize (the ruling recorded in `Direct.lean`'s pain diary: a naive
    "stuck-recursor-to-`Type` ⇒ copy" is DEAD, because a σ typed by a stuck
    `VecF Nat n` is that same shape and copying it copies a vector). -/

/-- **An UNMARKED proposition component moves.** `Σ (n : Nat). Le n 15` — the same
    pack as `U 15` with the `0` deleted — is a `Nat` and a RUNTIME proof, and a
    runtime proof of a stuck-typed proposition is not index-kind. This is §2.1's
    long-standing "proofs move because `indexKindTy` does not recognize stuck
    proposition spines" reaching the Σ rule unchanged: M34 adds a way to say
    "erased", it does not add a way to guess it. -/
def unmarkedPropTwice : Term := prog{
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
def tailMarkedWrongEndTwice : Term := prog{
  fn Snk (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit { () };
  fn Chain (p : (Σ (n : Nat). Σ0 (h : Le n 15). Unit)) -> Unit {
    let a = Snk(p); let b = Snk(p); () };
  () }
example : progRejects tailMarkedWrongEndTwice "p#0 holds ⊥ (use-after-move" = true := by
  native_decide

end Dllbc.Tests.SigmaCopy
