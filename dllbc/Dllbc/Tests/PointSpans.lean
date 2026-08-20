import Dllbc.ElabCheck

/-!
# Point hovers — what the checker knew *here* (docs/17)

Same discipline as `Tests/HoverSpans`: every case elaborates, and the assertion
is what `textDocument/hover` returns at a pinned position, recorded beside it.
There is no `#guard_msgs` analogue for hover, so `lake build` asserts only that
these blocks elaborate.

**Point granularity is the DEFAULT since docs/17**, so these cases need no
option. `set_option dllbc.pointHover false` reverts every position here to
`docs/16`'s binder-granularity answer, which is what `Tests/HoverSpans` pins by
setting exactly that. The two files disagreeing at the same source shape is the
feature, and flipping one switch is how a reader sees both.
-/

open Dllbc

namespace Dllbc.Tests.PointSpans

set_option trace.Dllbc.check false

/-! ## (P1) THE ACCEPTANCE CASE — docs/16 case (12), inverted

    Under binder granularity `b` reported its BINDING-time payload everywhere,
    including below a write that changed it, and docs/16 pinned that as correct.
    Here the same three occurrences give three different answers, each true at
    its own point:

      (P1a) L44 C7   `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
      (P1b) L45 C12  `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S Z) Nil)`** — comptime-known value
      (P1c) L46 C4   `b`  ⇒  **b ≡ `borrowₘ ℓ0 ⊥`** — comptime-known value
      (P1d) L47 C12  `b`  ⇒  **b ≡ `borrowₘ ℓ0 (Cons (S (S Z)) Nil)`** — comptime-known value

    (P1d) is the acceptance test: below the write, `b` shows what the write put
    there. (P1c) is the same mechanism telling a harder truth — entering the
    assignment the payload has been MOVED OUT by the read above it, so the borrow
    is holding ⊥, and a tooltip that hid that would be hiding the borrow
    discipline itself. -/

example : Term := prog{
  let x = Cons(1, Nil);
  let b = &m x;
  let a = *b;
  *b := Cons(2, Nil);
  let d = *b;
  () }

/-! ## (P2) A PARAMETER answers TWO questions

    docs/16 let S1 win outright for a parameter: the annotation is exact, and the
    binding-time fact had nothing better to offer. At point granularity that
    precedence hides the interesting half — `v : &mut List Nat` is true and says
    nothing about what is in it here — so the tooltip answers both, the type from
    the source and the contents from the checker.

      (P2a) L66 C9   `v`  ⇒  **v : `&mut List Nat`**                       (at the binder: no point yet)
      (P2b) L69 C27  `v`  ⇒  **v : `&mut List Nat`** — here `borrowₘ ℓ0 ⊥`

    (P2b) is `match *v` having taken the payload out to bind the arm's fields;
    the arm writes it back on the next token. The type is unchanged and the
    contents are ⊥, and both are worth saying. -/

example : Term := prog{
  fn M (v : &mut List Nat) -> Unit {
    match *v {
      Nil => { *v := Nil; () },
      Cons(x, rest) => { *v := Cons(x, rest); () }
    } };
  () }

/-! ## (P3) MULTI-PATH — labelled, not first-past-the-post

    This is the case that was silently first-path until the seal carry was made
    per-path. A borrow-mode match refines the parent's payload per branch (M14),
    so below the match `v` genuinely holds two different things, and the tooltip
    says both with the arm trail that produced each. Past three the list stops
    and COUNTS the remainder; it never truncates silently.

    It is also the user's original narrowing question, answered: the NARROWED
    SHAPE is visible on the parent through the suspension. What does not exist is
    value-narrowing on an owned scrutinee — `match n` moves it.

      (P3a) L95 C14  `v`   ⇒  **v : `&mut List Nat`** — here `borrowₘ ℓ0 (Cons loanₘ ℓ1 loanₘ ℓ2)` *(on v ⇒ Cons)*; `borrowₘ ℓ0 Nil` *(on v ⇒ Nil)*
      (P3b) L93 C34  `hd`  ⇒  **hd ≡ `borrowₘ ℓ1 (σ2 : Nat)`** — binding-time shape
-/

example : Term := prog{
  fn M (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => { let a = *hd; *hd := a; () }
    };
    let w = *v;
    *v := w;
    () };
  () }

end Dllbc.Tests.PointSpans
