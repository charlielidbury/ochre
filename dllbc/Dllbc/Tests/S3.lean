import Dllbc.Machine
import Dllbc.Macro

/-!
# §3 test suite — "Match" (concrete machine)

The runtime content of §3: owned destructuring (§3.1) and borrow-mode match —
field reborrows, suspension, variant change through the parent (§3.3–3.4). The
symbolic layer (§3.2 σ, ⇜ refinement) is out of scope (milestone 3).

Same golden-Ω style as S2: run the `dllbc{…}` program, compare the final
canonicalized environment (loan ids in first-appearance order) against the
expected Ω, or assert a distinctive error substring. Since there are no
functions yet, §3's traces are adapted — branch bodies rebuild a constructor
or return a component instead of computing `a + b`, and the parent is read
back after the match to observe the lazy End-Mut collapse.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S3

/-- A `Pair` value, for expected environments. -/
def pair (a b : Val) : Val := .ctor "Pair" [a, b]

/-! ## §3.1 Owned mode: destructuring -/

-- The scrutinee is ⇒-consumed, its fields move into the binders; the branch
-- rebuilds the pair. p ↦ ⊥, a ↦ ⊥, b ↦ ⊥, q ↦ Pair 3 7.
example : expectEnv dllbc{
  let p = Pair(3, 7);
  let q = match p { Pair(a, b) => Pair(a, b) };
  ()
} [("p", .bot), ("a", .bot), ("b", .bot), ("q", pair (nat 3) (nat 7))] = true := by
  native_decide

-- A nested owned match: destructure the pair, then destructure its second
-- field. The unused tail binder `t` keeps its (unconsumed) value.
example : expectEnv dllbc{
  let p = Pair(1, Cons(2, Nil));
  let r = match p {
    Pair(a, rest) => match rest { Cons(h, t) => Pair(a, h), Nil => Pair(a, a) }
  };
  ()
} [("p", .bot), ("a", .bot), ("rest", .bot), ("h", .bot), ("t", nil),
   ("r", pair (nat 1) (nat 2))] = true := by native_decide

/-! ## §3.3 Borrow mode: matching through -/

-- The suspended state, observed by ending the program right after the match:
-- each field binder is a whole-value reborrow, the parent's payload is a Cons
-- of loan markers (unreadable), and `*hd := 0` was a strong update.
example : expectEnv dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  ()
} [("x", .loanM 0),
   ("b", .borrowM 0 (cons (.loanM 1) (.loanM 2))),
   ("hd", .borrowM 1 (nat 0)),
   ("tl", .borrowM 2 nil)] = true := by native_decide

-- Reading the owner back collapses the chain lazily: End-Mut ℓ0 (parent),
-- then the owned-position field loans ℓ1, ℓ2 are ended in turn as the value is
-- moved, so `x`'s value arrives fully updated. y ↦ Cons 0 Nil.
example : expectEnv dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot),
   ("y", cons (nat 0) nil)] = true := by native_decide

-- The nullary branch binds nothing and issues no loans (degenerate case).
example : expectEnv dllbc{
  let x = Nil;
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("y", nil)] = true := by native_decide

/-! ## §3.4 Variant change through the parent -/

-- The Cons branch replaces the parent's payload with a different variant:
-- `*b := Nil` forces a drop of the old payload (a Cons of field-loan markers
-- whose borrows are the Ω entries hd, tl) — End-Mut each, hd/tl die to ⊥ —
-- then Nil fills. Reading the owner back yields y ↦ Nil.
example : expectEnv dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  match b {
    Cons(hd, tl) => { *b := Nil; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", nil)] = true := by
  native_decide

/-! ## Nested borrow-mode match (through a field binder) -/

-- Match `b` through, then match the field binder `tl` (itself a reborrow)
-- through — a two-level suspension. Writing `*h2 := 0` updates the inner
-- element; reading the owner collapses the whole nested chain.
-- y ↦ Cons 1 (Cons 0 Nil).
example : expectEnv dllbc{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  match b {
    Cons(hd, tl) => match tl {
      Cons(h2, t2) => { *h2 := 0; () },
      Nil => ()
    },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot),
   ("h2", .bot), ("t2", .bot), ("y", cons (nat 1) (cons (nat 0) nil))] = true := by
  native_decide

/-! ## Rejections -/

-- Match on a moved variable: the scrutinee slot is ⊥.
example : expectErr dllbc{
  let p = Nil;
  let q = p;
  match p { Nil => () }
} "use-after-move" = true := by native_decide

-- No branch matches the head constructor (no exhaustiveness checking — there
-- are no inductive declarations yet — so an unmatched head is a runtime stuck).
example : expectErr dllbc{
  let p = Nil;
  match p { Cons(h, t) => () }
} "no branch" = true := by native_decide

-- Matching through a hole: `*b` is taken first, leaving the borrow payload ⊥,
-- and no rule reads through ⊥.
example : expectErr dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  match b { Cons(hd, tl) => (), Nil => () }
} "hole" = true := by native_decide

end Dllbc.Tests.S3
