import Dllbc.ElabCheck

/-!
# `show x` (docs/18)

`show x` prints, at its own position, exactly what hovering `x` there would say —
the same computation, delivered as a diagnostic instead of a hover — which makes
the answer assertable by `lake build` via `#guard_msgs`. Each case pins the
printed text for one binder/position shape.
-/

open Dllbc

namespace Dllbc.Tests.ShowSpans

set_option trace.Dllbc.check false

/-! ## (S1) One binder, shown at three points as it evolves

    Between the move-out (`let a = *b`) and the write, the borrow holds ⊥;
    the middle `show` pins that. -/

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

/-! ## (S2) Erasure — `show` adds no node to `Term`

    A program with `show`s is the same `Term` as one without, so no program
    checks differently for having been probed. -/

example :
    ((prog{ let x = Cons(1, Nil); let b = &m x; show b; *b := Cons(2, Nil);
            let d = *b; () })
     == (prog{ let x = Cons(1, Nil); let b = &m x; *b := Cons(2, Nil);
               let d = *b; () })) = true := by
  native_decide

/-! ## (S3) A parameter shows both of its answers

    The type from the source and the contents here — the same two-question form
    a point hover gives, because it is the same call.

    σ0 prints bare here: `bindSlot` files a borrow parameter's binding during
    `seedTelescopeV`, before the σ's type is registered, so at this point the
    checker does not yet know it. One statement later the annotation appears. -/

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

/-! ## (S4) A trailing `show` anchors to the final expression

    A `show` takes its point from the next statement, so the state it reports is
    the state entering that statement. Every block ends in a final expression,
    so a trailing `show` always has one to anchor to. -/

/--
info: **n ≡ `S Z`** — comptime-known value
-/
#guard_msgs in
example : Term := prog{
  let n = S(Z);
  show n;
  () }

end Dllbc.Tests.ShowSpans
