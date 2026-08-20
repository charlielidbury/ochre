import Dllbc.ElabCheck

/-!
# `show x` — a value made visible, where you put it (docs/18)

**This file asserts itself.** `Tests/HoverSpans` and `Tests/PointSpans` both carry
the same limitation — there is no `#guard_msgs` analogue for hover, so their
pinned positions are checkable only through a language server, one call per case.
A `show` is a DIAGNOSTIC, and diagnostics are exactly what `#guard_msgs` pins. So
the same answer becomes assertable by `lake build` purely by changing where it is
delivered, and everything below is checked by the build rather than by a comment.

`show x` prints, at its own position, exactly what hovering `x` there would say.
Not a second renderer and not a second query — the same call, forced eagerly.
-/

open Dllbc

namespace Dllbc.Tests.ShowSpans

set_option trace.Dllbc.check false

/-! ## (S1) THE EVOLUTION TRACE — the user's own use case

    One variable, shown at three points, evolving. This is docs/17's
    four-points-four-answers borrow with `show`s where the hovers were.

    The middle one is the one worth pausing on: between `let a = *b` and the
    write, the payload has been MOVED OUT, so the borrow is holding ⊥. A demo
    that skipped it would be hiding the borrow discipline; showing it is the
    point of being able to put a probe anywhere. -/

/--
info: **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
---
info: **b ≡ `borrowₘ ℓ0 ⊥`** — comptime-known value
---
info: **b ≡ `borrowₘ ℓ0 (Cons (S (S Z)) Nil)`** — comptime-known value
-/
#guard_msgs in
example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  show b;
  let a = *b;
  show b;
  *b := Cons(2, Nil);
  show b;
  let d = *b;
  () }

/-! ## (S2) ERASURE — the kernel never learns the word

    A program with `show`s is the SAME `Term` as one without. `Term` gains no
    node, nothing is read, moved or borrowed, and Ω is untouched — so no program
    checks differently for having been probed. -/

example :
    ((prog{ let x = Cons(1, Nil); let b = &m x; show b; *b := Cons(2, Nil);
            let d = *b; () })
     == (prog{ let x = Cons(1, Nil); let b = &m x; *b := Cons(2, Nil);
               let d = *b; () })) = true := by
  native_decide

/-! ## (S3) A PARAMETER shows both of its answers

    The type from the source and the contents here — the same two-question form
    a point hover gives, because it is the same call.

    **σ0 prints BARE here, and that is the immutability rule being obeyed rather
    than a gap.** A delta carries the σ-context as it stood AT that change, and
    the binding of a borrow parameter is filed by `bindSlot` during
    `seedTelescopeV` before the σ's type is registered — so at this point the
    checker genuinely did not yet know it. One statement later the annotation
    appears. Printing `(σ0 : List Nat)` here would be reporting a fact from the
    future, which is exactly what docs/17 §1 forbids; the alternative would be to
    order the seed so the type lands first, which is a change to the checker for
    a cosmetic gain and is not taken. -/

/--
info: **v : `&mut List Nat`** — here `borrowₘ ℓ0 σ0`
-/
#guard_msgs in
example : Term := prog{
  fn M (v : &mut List Nat) -> Unit {
    show v;
    let a = *v;
    *v := a;
    () };
  () }

/-! ## (S4) A TRAILING `show` anchors to the final expression

    A `show` takes its point from the NEXT statement, because the state entering
    that statement is the state where the `show` is written. Every block ends in a
    final expression, so a trailing `show` always has one to anchor to — which is
    what makes the rule total rather than nearly so. -/

/--
info: **n ≡ `S Z`** — comptime-known value
-/
#guard_msgs in
example : Term := prog{
  let n = S(Z);
  show n;
  () }

end Dllbc.Tests.ShowSpans
