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
info: b ↦ borrowₘ ℓ₀ (Cons (S Z) Nil)
---
info: b ↦ borrowₘ ℓ₀ ⊥
---
info: b ↦ borrowₘ ℓ₀ (Cons (S (S Z)) Nil)
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

/-! ## (S3) A PARAMETER shows its entry state, σ typed inline

    One answer, one form — the static "type from the source" half is gone
    (2026-08-21 ruling: under strong updates nothing about a slot is timeless),
    and the parameter answers from the checker's own seed like every other
    binder.

    **σ₀ carries its type inline, and the earlier "bare σ₀" pin was retired
    WITH its reasoning.** The old text argued printing `(σ₀ : List Nat)` at the
    first statement would report a fact from the future, because `bindSlot`
    filed the binding before the type was registered. `seedTelescopeV` now
    registers the type FIRST — binding and registration are one seeding
    instant, so the delta carrying its own σ's type is ordering within a point,
    not clairvoyance. -/

/--
info: v ↦ borrowₘ ℓ₀ (σ₀ : List Nat)
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
info: n ↦ S Z
-/
#guard_msgs in
example : Term := prog{
  let n = S(Z);
  show n;
  () }

/-! ## (S5) PATTERN BINDERS are binders like any other

    A match arm's binders are seeded at arm entry, under the match statement's
    key, per path — so they hover (and `show`) from their own arm's seed
    through `replayEntry`, exactly as a parameter answers from the telescope's.
    Ownership match binds the payload's components; borrow-mode match binds
    reborrow loans INTO the payload, and the tooltip says which.

    KNOWN LIMIT, stated: a `show` whose anchor is an arm's FINAL EXPRESSION
    declines ("no value here") — continuation-grafting rewrites an arm's tail,
    so the machine files no key for it and the surface's anchor points at a
    statement that never happens. A `show` above any real arm statement works;
    the shows below anchor to the `let`s after them. Pattern-binder HOVERS are
    unaffected — they are entry occurrences of the match key, not anchored
    forward. -/

/--
info: hd ↦ S Z
---
info: tl ↦ Nil
---
info: hd ↦ borrowₘ ℓ₁ (σ₂ : Nat)
-/
#guard_msgs in
example : Term := prog{
  let x = Cons(1, Nil);
  let r = match x {
    Nil => Z,
    Cons(hd, tl) => {
      show hd;
      show tl;
      let k = hd;
      k }
  };
  fn F (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => {
        show hd;
        let u = Z;
        () }
    };
    let a = *v;
    *v := a;
    () };
  () }

/-! ## (S6) A `show` ABOVE a match keys AT the match — the depth regression, pinned

    The drain of pending `show`s was depth-blind: the first statement row to
    tag after a `show` claimed it, and for a `show` above a statement-position
    match that was `let u = Z` INSIDE the Cons arm — so the outer probe
    reported the arm's suspension, a fact from the future, with no path label
    to flag it (the Nil path declined). `takePendings`/`restorePendings` is
    the fix; this case is the reporter's own program, and the first line is
    the assertion that a probe above a match sees the UNNARROWED borrow. -/

/--
info: v ↦ borrowₘ ℓ₀ (σ₀ : List Nat)
---
info: v ↦ borrowₘ ℓ₀ (Cons loanₘ ℓ₁ loanₘ ℓ₂)
-/
#guard_msgs in
example : Term := prog{
  fn F (v : &mut List Nat) -> Unit {
    show v;
    match v {
      Nil => (),
      Cons(hd, tl) => {
        show v;
        let u = Z;
        () }
    };
    let a = *v;
    *v := a;
    () };
  () }

end Dllbc.Tests.ShowSpans
