import Dllbc.Machine
import Dllbc.Macro

/-!
# §2 test suite — "First Programs"

Every annotated trace in doc §2 is encoded as a `native_decide` test: the
program (written in the `dllbc{…}` surface syntax) is run to its final
environment, canonicalized (loan ids renumbered to first-appearance order),
and compared against the expected Ω built from `Val` constructors. Rejection
programs assert `.error` carrying a distinctive substring.

Helpers `expectEnv` / `expectErr` live in `Dllbc.Machine`; `Val.nat`,
`Val.nil`, `Val.cons` build expected values.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S2

/-! ## §2.1 Moves, and the vacant slot -/

-- A move consumes: `x` moves out, ⊥ is left behind; a vacant slot refills.
-- let x = 3; let y = x; x := 7  ⟹  x ↦ 7, y ↦ 3
example : expectEnv dllbc{
  let x = 3;
  let y = x;
  x := 7;
  ()
} [("x", nat 7), ("y", nat 3)] = true := by native_decide

-- §2.1 copy-on-read: reading a marker-free value copies it, the owner stays.
-- let x = 3; let y = x  ⟹  x ↦ 3 (copied), y ↦ 3
example : expectEnv dllbc{
  let x = 3;
  let y = x;
  ()
} [("x", nat 3), ("y", nat 3)] = true := by native_decide

/-! ## §2.2 Borrowing, writing through, and ending -/

-- &mut mints a loan: the marker parks at x, ownership moves into b.
-- let x = 3; let b = &mut x  ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 3
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 3))] = true := by native_decide

-- Writing through the borrow replaces the payload in place, b not consumed.
-- … *b := 7  ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 7
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  *b := 7;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 7))] = true := by native_decide

-- Reading x forces a lazy End-Mut on ℓ0 first: 7 returns to x, b dies to ⊥; the
-- retry read then COPIES x (§2.1 — now marker-free), so x stays.
-- … let y = x  ⟹  x ↦ 7 (copied), b ↦ ⊥, y ↦ 7
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  *b := 7;
  let y = x;
  ()
} [("x", nat 7), ("b", .bot), ("y", nat 7)] = true := by native_decide

/-! ## §2.3 Drop -/

-- Assigning onto a live borrow forces a drop of its contents first: End-Mut
-- returns 3 to x, the dead borrow is discarded, then 9 fills.
-- let x = 3; let b = &mut x; b := 9  ⟹  x ↦ 3, b ↦ 9
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  b := 9;
  ()
} [("x", nat 3), ("b", nat 9)] = true := by native_decide

/-! ## §2.4 Take and refill: reading through a borrow -/

-- `*b` under ⇒ moves the payload out through the borrow, leaving a hole ⊥.
-- let x = Cons(3, Nil); let b = &mut x; let tail = *b
--   ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 ⊥, tail ↦ Cons 3 Nil
example : expectEnv dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 .bot), ("tail", cons (nat 3) nil)] = true := by
  native_decide

-- The refill closes the hole; no list node was copied. `tail` is DATA (a
-- Cons-tree), so reading it into the new node MOVES it (§2.1 keeps Rust's line
-- for aggregates) — tail ↦ ⊥.
-- … *b := Cons(7, tail)
--   ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 (Cons 7 (Cons 3 Nil)), tail ↦ ⊥
example : expectEnv dllbc{
  let x = Cons(3, Nil);
  let b = &mut x;
  let tail = *b;
  *b := Cons(7, tail);
  ()
} [("x", .loanM 0),
   ("b", .borrowM 0 (cons (nat 7) (cons (nat 3) nil))),
   ("tail", .bot)] = true := by native_decide

/-! ## §2.5 Reborrow -/

-- `&mut *b` reborrows the payload: b is suspended (holds a loan marker where
-- its payload was), the chain reads x → ℓ0 → ℓ1 → the value.
-- let x = 3; let b = &mut x; let c = &mut *b
--   ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 (loanₘ ℓ1), c ↦ borrowₘ ℓ1 3
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (.loanM 1)), ("c", .borrowM 1 (nat 3))] = true := by
  native_decide

-- Reading x through the suspended reborrow collapses the whole chain: End-Mut
-- ℓ0 then End-Mut ℓ1 fire in turn (the fuel-bounded reorganize-retry loop), and
-- x's value arrives; the retry read then COPIES it (§2.1).
--   ⟹  x ↦ 3 (copied), b ↦ ⊥, c ↦ ⊥, z ↦ 3
example : expectEnv dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  let z = x;
  ()
} [("x", nat 3), ("b", .bot), ("c", .bot), ("z", nat 3)] = true := by native_decide

/-! ## Rejections (stuckness = no applicable rule) -/

-- §2.1 copy-on-read makes a marker-free value re-readable: the second read of x
-- copies again — no use-after-move. (Use-after-move rejections now live on
-- marker-carrying values — a moved borrow, a taken payload.)
example : expectEnv dllbc{
  let x = 3;
  let y = x;
  let z = x;
  ()
} [("x", nat 3), ("y", nat 3), ("z", nat 3)] = true := by native_decide

-- Fill through a non-place term: ⇐ is only defined on places.
example : expectErr dllbc{
  Pair(1) := 7;
  ()
} "not a place" = true := by native_decide

-- The flagship §2.5 self-reborrow: `b := c` after `let c = &mut *b`. The RHS
-- ⇒-consumes c, so borrowₘ ℓ1 3 is in flight; drop must vacate b, which
-- requires ending ℓ1, whose borrow is exactly that in-flight value — no entry,
-- no rule, rejected.
example : expectErr dllbc{
  let x = 3;
  let b = &mut x;
  let c = &mut *b;
  b := c;
  ()
} "in flight" = true := by native_decide

end Dllbc.Tests.S2
