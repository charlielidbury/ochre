import Dllbc.ElabCheck
import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program

/-!
# Traces

Tests for the executing borrow machine's basic walks: moves and the vacant
slot, borrowing and writing through, ending a borrow, drop, take-and-refill,
reborrow, match in owned and borrow mode (concrete and symbolic scrutinees),
variant change through a parent, and frame/scope cleanup — plus the
rejections, where no rule applies and stuckness is the error.
-/

section
/-!
# First programs

Each program (written in the `prog{…}` surface syntax) is run to its final
environment, canonicalized (loan ids renumbered to first-appearance order),
and compared against the expected Ω built from `Val` constructors. Rejection
programs assert `.error` carrying a distinctive substring.

Helpers `expectEnv` / `expectErr` live in `Dllbc.Machine`; `Val.nat`,
`Val.nil`, `Val.cons` build expected values.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S2

/-! ## Moves, and the vacant slot -/

-- A move consumes: `x` moves out, ⊥ is left behind; a vacant slot refills.
example : expectEnv prog{
  let x = 3;
  let y = x;
  x := 7;
  ()
} [("x", nat 7), ("y", nat 3)] = true := by native_decide

-- Copy-on-read: reading a marker-free value copies it, the owner stays.
example : expectEnv prog_parse {
  let x = 3;
  let y = x;
  ()
} [("x", nat 3), ("y", nat 3)] = true := by native_decide

/-! ## Borrowing, writing through, and ending -/

-- &mut mints a loan: the marker parks at x, ownership moves into b.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 3))] = true := by native_decide

-- Writing through the borrow replaces the payload in place, b not consumed.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  *b := 7;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 7))] = true := by native_decide

-- Reading x forces a lazy End-Mut on ℓ₀ first: 7 returns to x, b dies to ⊥; the
-- retry read then copies x (now marker-free), so x stays.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  *b := 7;
  let y = x;
  ()
} [("x", nat 7), ("b", .bot), ("y", nat 7)] = true := by native_decide

/-! ## Drop -/

-- Assigning onto a live borrow forces a drop of its contents first: End-Mut
-- returns 3 to x, the dead borrow is discarded, then 9 fills.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  b := 9;
  ()
} [("x", nat 3), ("b", nat 9)] = true := by native_decide

/-! ## Take and refill: reading through a borrow -/

-- `*b` under ⇒ moves the payload out through the borrow, leaving a hole ⊥.
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  let tail = *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 .bot), ("tail", cons (nat 3) nil)] = true := by
  native_decide

-- The refill closes the hole; no list node was copied. `tail` is data (a
-- Cons-tree), so reading it into the new node moves it — tail ↦ ⊥.
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  let tail = *b;
  *b := Cons(7, tail);
  ()
} [("x", .loanM 0),
   ("b", .borrowM 0 (cons (nat 7) (cons (nat 3) nil))),
   ("tail", .bot)] = true := by native_decide

/-! ## Reborrow -/

-- `&mut *b` reborrows the payload: b is suspended (holds a loan marker where
-- its payload was), the chain reads x → ℓ0 → ℓ1 → the value.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  let c = &m *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (.loanM 1)), ("c", .borrowM 1 (nat 3))] = true := by
  native_decide

-- Reading x through the suspended reborrow collapses the whole chain: End-Mut
-- ℓ₀ then End-Mut ℓ₁ fire in turn (the fuel-bounded reorganize-retry loop), and
-- x's value arrives; the retry read then copies it.
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  let c = &m *b;
  let z = x;
  ()
} [("x", nat 3), ("b", .bot), ("c", .bot), ("z", nat 3)] = true := by native_decide

/-! ## Rejections (stuckness = no applicable rule) -/

-- Copy-on-read makes a marker-free value re-readable: the second read of x
-- copies again — no use-after-move. Use-after-move rejections live on
-- marker-carrying values instead — a moved borrow, a taken payload.
example : expectEnv prog_parse {
  let x = 3;
  let y = x;
  let z = x;
  ()
} [("x", nat 3), ("y", nat 3), ("z", nat 3)] = true := by native_decide

-- Fill through a non-place term: ⇐ is only defined on places.
example : expectErr prog_parse {
  Pair(1) := 7;
  ()
} "not a place" = true := by native_decide

-- The self-reborrow: `b := c` after `let c = &mut *b`. The RHS ⇒-consumes c,
-- so borrowₘ ℓ1 3 is in flight; drop must vacate b, which requires ending ℓ1,
-- whose borrow is exactly that in-flight value — no entry, no rule, rejected.
example : expectErr prog_parse {
  let x = 3;
  let b = &m x;
  let c = &m *b;
  b := c;
  ()
} "in flight" = true := by native_decide

end Dllbc.Tests.S2
end

section
/-!
# Match (concrete machine)

Owned destructuring and borrow-mode match: field reborrows, suspension, and
variant change through the parent. The symbolic layer (σ, ⇜ refinement) is
covered separately below.

Same golden-Ω style as above: run the `prog{…}` program, compare the final
canonicalized environment (loan ids in first-appearance order) against the
expected Ω, or assert a distinctive error substring. Since there are no
functions yet, these traces are adapted — branch bodies rebuild a constructor
or return a component instead of computing `a + b`, and the parent is read
back after the match to observe the lazy End-Mut collapse.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S3

/-- A `Pair` value, for expected environments. -/
def pair (a b : Val) : Val := .ctor "Pair" [a, b]

/-! ## Owned mode: destructuring -/

-- The scrutinee is ⇒-consumed, its fields move into the binders; the branch
-- rebuilds the pair, reading `a`/`b` by copy (marker-free). The binders are the
-- arm's, so they leave with it when the arm closes.
example : expectEnv prog{
  let p = Pair(3, 7);
  let q = match p { Pair(a, b) => Pair(a, b) };
  ()
} [("p", .bot), ("q", pair (nat 3) (nat 7))] = true := by
  native_decide

-- A nested owned match: destructure the pair, then destructure its second
-- field. The inner match is in tail position within the outer arm, so it has
-- no seam of its own and its binders die with the arm that contains them: one
-- pop takes `a`, `rest`, `h` and `t` together, and only the outer `let`'s `r`
-- survives.
example : expectEnv prog{
  let p = Pair(1, Cons(2, Nil));
  let r = match p {
    Pair(a, rest) => match rest { Cons(h, t) => Pair(a, h), Nil => Pair(a, a) }
  };
  ()
} [("p", .bot), ("r", pair (nat 1) (nat 2))] = true := by native_decide

/-! ## Borrow mode: matching through -/

-- The field binders are whole-value reborrows and the parent's payload is a
-- Cons of loan markers — but the binders are the arm's, so the arm's close
-- ends their reborrows (in reverse binding order: ℓ2, then ℓ1) and each
-- payload plugs back into the parent. What is observable one statement later
-- is therefore the parent holding the strong-updated payload, not the marker
-- chain.
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  ()
} [("x", .loanM 0),
   ("b", .borrowM 0 (cons (nat 0) nil))] = true := by native_decide

-- Reading the owner back collapses the rest of the chain: End-Mut ℓ0 (parent)
-- — the field loans ℓ1, ℓ2 having already ended at the arm's close — so `x`'s
-- value arrives fully updated. `x` is a Cons-tree (data), so the read moves it.
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("y", cons (nat 0) nil)] = true := by native_decide

-- The nullary branch binds nothing and issues no loans (degenerate case).
example : expectEnv prog{
  let x = Nil;
  let b = &m x;
  match b {
    Cons(hd, tl) => { *hd := 0; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("y", nil)] = true := by native_decide

/-! ## Variant change through the parent -/

-- The Cons branch replaces the parent's payload with a different variant:
-- `*b := Nil` forces a drop of the old payload (a Cons of field-loan markers
-- whose borrows are the Ω entries hd, tl) — End-Mut each, hd/tl die to ⊥ —
-- then Nil fills. Reading the owner back yields y ↦ Nil.
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  match b {
    Cons(hd, tl) => { *b := Nil; () },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("y", nil)] = true := by
  native_decide

/-! ## Nested borrow-mode match (through a field binder) -/

-- Match `b` through, then match the field binder `tl` (itself a reborrow)
-- through — a two-level suspension. Writing `*h2 := 0` updates the inner
-- element; reading the owner collapses the whole nested chain.
example : expectEnv prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &m x;
  match b {
    Cons(hd, tl) => match tl {
      Cons(h2, t2) => { *h2 := 0; () },
      Nil => ()
    },
    Nil => ()
  };
  let y = x;
  ()
} [("x", .bot), ("b", .bot), ("y", cons (nat 1) (cons (nat 0) nil))] = true := by
  native_decide

/-! ## Rejections -/

-- Match on a moved variable: `p = Nil` is data (a List), so `let q = p` moves
-- it, and the later match finds the slot ⊥.
example : expectErr prog_parse {
  let p = Nil;
  let q = p;
  match p { Nil => () }
} "use-after-move" = true := by native_decide

-- No branch matches the head constructor (no exhaustiveness checking — there
-- are no inductive declarations yet — so an unmatched head is a runtime stuck).
example : expectErr prog_parse {
  let p = Nil;
  match p { Cons(h, t) => () }
} "no branch" = true := by native_decide

-- Matching through a hole: `*b` is taken first, leaving the borrow payload ⊥,
-- and no rule reads through ⊥.
example : expectErr prog_parse {
  let x = Cons(3, Nil);
  let b = &m x;
  let tail = *b;
  match b { Cons(hd, tl) => (), Nil => () }
} "hole" = true := by native_decide

end Dllbc.Tests.S3
end

section
/-!
# Match, symbolic scrutinee

Matching a *symbolic* scrutinee splits the run: the `explore` driver forks one
path per branch, each entered by a ⇜ refinement (`writeC`) that substitutes
`C (sym σ₁) … (sym σₙ)` for σ everywhere in Ω. Owned mode then destructures;
borrow mode reborrows the fields. Concrete programs are unaffected.

Every test below is a program the surface can write: the call rule hands a
caller a fresh existential at the callee's return type, so `let n = anyNat()`
*is* a symbolic `n`, minted by the checker. The ones that observe a mid-borrow
state (`x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ σ`) reach it the way a program does — own
the value, then borrow it.

Golden-Ω style, unchanged: `tailPaths` compares the per-path canonicalized
environments (ℓ- and σ-ids renumbered to first-appearance order) in
branch-declaration order, and the path count with them.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S3Sym

/-- Two declarations that exist to be called. Checking mode never runs a
    callee's body — it applies the signature rule — so what a caller learns
    from `anyNat()` is exactly "a Nat, and nothing else", which is what a σ
    is. The bodies are irrelevant to every test in this file and are the
    simplest that typecheck.

    Written as a prefix: every test below is `withAny prog{ … }` and gets
    them in scope. -/
def withAny (rest : Term) : Term := prog{
  fn AnyNat () -> Nat { 0 };
  fn AnyList () -> List Nat { Nil };
  %rest }

/-! `tailPaths` (in `Dllbc/Program.lean`) runs a program and compares the
    per-path environments and the path count. The count is half the
    assertion, not a formality: the whole claim here is that matching a
    symbolic scrutinee splits the run, so an assertion that checked only the
    environments would still pass if the fork stopped happening. -/

/-! ## Symbolic scrutinee: refinement as ⇜ (owned mode) -/

-- is_zero's shape: n ↦ (σ : Nat); a two-branch owned match splits into two
-- paths. Z branch: ⇜ σ := Z, then n consumed to ⊥. S branch: ⇜ σ := S σ′,
-- then n ↦ ⊥ and the field binder m ↦ (σ′ : Nat).
def isZero : Term := withAny prog_parse {
  let n = AnyNat();
  match n { Z => (), S(m) => () }
}

example : tailPaths isZero
  [ [("n", .bot)],
    [("n", .bot), ("m", .sym 0)] ] = true := by native_decide

/-! ## Borrow mode on a symbolic payload -/

-- zero_head, symbolic: b ↦ borrowₘ ℓ (σ : List). The Cons branch reborrows the
-- fields, `*hd := 0` strong-updates the head, and demanding the owner collapses
-- the chain to `Cons 0 σ₂`. The Nil branch refines the payload to Nil. Two
-- paths.
def zeroHead : Term := withAny prog_parse {
  let x = AnyList();
  let b = &m x;
  match b {
    Cons(hd, tl) => {
      *hd := 0;
      ()
    },
    Nil => ()
  };
  let y = x;
  ()
}

-- JOINED (docs/19 v2): one continuation path. The arms disagreed about the
-- payload (`Cons 0 σtl` vs `Nil`), so the seam re-minted it as a fresh σ at the
-- payload's own type — `y` is that σ, and the per-arm values are gone. The
-- count is still half the assertion, now in the other direction: a fork
-- reappearing here would make it two again.
example : tailPaths zeroHead
  [ [("x", .bot), ("b", .bot), ("y", .sym 0)] ] = true := by native_decide

/-! ## Symbolic variant change -/

-- `*b := Nil` in the Cons branch drops the reborrowed fields (their loans are Ω
-- entries) and installs Nil; both paths leave the owner holding Nil.
def variantChange : Term := withAny prog_parse {
  let x = AnyList();
  let b = &m x;
  match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
  let y = x;
  ()
}

-- Both paths now leave the same Ω — the Cons path's `hd`/`tl` left with the
-- arm and were the only thing distinguishing it. The path count is what this
-- assertion still discriminates on.
example : tailPaths variantChange
  [ [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Two-level symbolic match (composed refinements) -/

-- Match `b` through, then match the field binder `tl` through — the refinements
-- compose. Three paths (outer Cons × {inner Cons, inner Nil}, plus outer Nil):
--   Cons σ₀ (Cons 0 σ₁),  Cons σ₀ Nil,  Nil.
def twoLevel : Term := withAny prog_parse {
  let x = AnyList();
  let b = &m x;
  match b {
    Cons(hd, tl) => match tl {
      Cons(h2, t2) => { *h2 := 0; let y = x; () },
      Nil => { let y = x; () }
    },
    Nil => { let y = x; () }
  }
}

example : tailPaths twoLevel
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("h2", .bot), ("t2", .bot),
     ("y", cons (.sym 0) (cons (nat 0) (.sym 1)))],
    [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", cons (.sym 0) nil)],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Rejections -/

-- ⇜ (writeC) refines only a symbolic place; aimed at a concrete value it errors.
-- This one keeps its hand-seeded Ω on purpose: it drives the arrow DIRECTLY,
-- with no program around it, so there is nothing for a program to be written in.
example : expectMErr [(Var.slot "x", cons (nat 3) nil)]
  (writeC (.var "x") (nat 9)) "expected a symbolic" = true := by native_decide

-- A symbolic match in expression position (a constructor argument) cannot split
-- and is rejected clearly by the pre-pass / readR.
def exprPosition : Term := withAny prog_parse {
  let z = AnyList();
  let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
  ()
}

example : progRejects exprPosition "expression position"
  = true := by native_decide

end Dllbc.Tests.S3Sym
end

section
/-!
# Scopes pop, and dropping ends what they held

Ω entries leave with the scope that bound them: a match arm's binders at the
arm's close, a call frame's slots at return. Each popped entry surrenders the
borrows it holds first, in reverse binding order — Rust's — so the ends that used
to wait for the next demand happen at the scope boundary instead.

The match traces above already carry the arm half in their expected
environments (the binders are simply not there any more). What is asserted
here is the part those traces cannot show: that the pop is not a leak — the
drop really runs — and that the one case where an entry must not go still
works.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S31Pop

/-! ## The drop runs: an arm's reborrows are surrendered at its close -/

-- The arm reborrows the fields and writes through one of them. At the arm's
-- close both reborrows end — last-bound first — so the parent is whole again
-- without anything having demanded it, and the owner reads back its updated
-- value. Compare the borrow-mode match trace above, which observes the same
-- program one statement earlier.
def armDrop : Term := prog{
  let x = Cons(3, Cons(4, Nil));
  let b = &m x;
  match b { Cons(hd, tl) => { *hd := 0; () }, Nil => () };
  let y = x;
  ()
}

example : progOk armDrop = true := by native_decide
example : progRunsTo armDrop
  [("x", .bot), ("b", .bot), ("y", cons (nat 0) (cons (nat 4) nil))] = true := by
  native_decide

/-! ## The one entry a pop must keep: a borrow of an arm-local that escapes it -/

-- `a` is bound inside the arm and `r` borrows it, so `r` outlives its owner's
-- scope. The pop keeps `a`'s storage — that storage is where the escaping
-- borrow's payload returns to — and the write through `r` lands there, so the
-- program's end still finds a loan to End-Mut. Popping `a` would leave the
-- marker unfindable and the borrow dangling, which is a silent loss rather than
-- an error: nothing would be left in Ω for `endScope` to end.
def armEscape : Term := prog{
  let l = Cons(1, Nil);
  let r = match l { Cons(hd, tl) => { let a = 5; &m a }, Nil => { let a = 6; &m a } };
  *r := 7;
  let w = r;
  ()
}

example : progOk armEscape = true := by native_decide
example : progRunsTo armEscape
  [("l", .bot), ("a", nat 7), ("r", .bot), ("w", .bot)] = true := by native_decide

/-! ## A frame's slots leave with the frame -/

-- The callee binds `v` and, in its arm, `hd` and `tl`. None of them is an
-- entry of Ω once the call has returned. Asserted as absence-from-Ω rather
-- than as a whole expected environment because the declaration entry itself
-- is a runtime λ, which has no writable literal.
def frameDrop : Term := prog{
  fn SetHead (v : &mut (List Nat ~> List Nat)) -> Unit {
    match v { Cons(hd, tl) => { *hd := 0; () }, Nil => () }
  };
  let x = Cons(9, Nil);
  SetHead(&m x);
  let y = x;
  ()
}

example : progOk frameDrop = true := by native_decide
example : (match runProgram frameDrop with
    | .ok env => (env.lookup "v").isNone && (env.lookup "hd").isNone
                 && (env.lookup "tl").isNone
                 && (env.lookup "y") == some (cons (nat 0) nil)
    | .error _ => false) = true := by native_decide

end Dllbc.Tests.S31Pop
end
