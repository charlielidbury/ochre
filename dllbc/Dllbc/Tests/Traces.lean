import Dllbc.Machine
import Dllbc.ProgMacro
import Dllbc.Program

/-!
# Traces — the §2/§3 walks, verbatim from the document, and the symbolic split

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S2.lean`
  * `S3.lean`
  * `S3Sym.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S2.lean` ──────────────────────────────────────────────
section
/-!
# §2 test suite — "First Programs"

Every annotated trace in doc §2 is encoded as a `native_decide` test: the
program (written in the `prog{…}` surface syntax) is run to its final
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
example : expectEnv prog{
  let x = 3;
  let y = x;
  x := 7;
  ()
} [("x", nat 7), ("y", nat 3)] = true := by native_decide

-- §2.1 copy-on-read: reading a marker-free value copies it, the owner stays.
-- let x = 3; let y = x  ⟹  x ↦ 3 (copied), y ↦ 3
example : expectEnv prog{
  let x = 3;
  let y = x;
  ()
} [("x", nat 3), ("y", nat 3)] = true := by native_decide

/-! ## §2.2 Borrowing, writing through, and ending -/

-- &mut mints a loan: the marker parks at x, ownership moves into b.
-- let x = 3; let b = &mut x  ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 3
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 3))] = true := by native_decide

-- Writing through the borrow replaces the payload in place, b not consumed.
-- … *b := 7  ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 7
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  *b := 7;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (nat 7))] = true := by native_decide

-- Reading x forces a lazy End-Mut on ℓ0 first: 7 returns to x, b dies to ⊥; the
-- retry read then COPIES x (§2.1 — now marker-free), so x stays.
-- … let y = x  ⟹  x ↦ 7 (copied), b ↦ ⊥, y ↦ 7
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  *b := 7;
  let y = x;
  ()
} [("x", nat 7), ("b", .bot), ("y", nat 7)] = true := by native_decide

/-! ## §2.3 Drop -/

-- Assigning onto a live borrow forces a drop of its contents first: End-Mut
-- returns 3 to x, the dead borrow is discarded, then 9 fills.
-- let x = 3; let b = &mut x; b := 9  ⟹  x ↦ 3, b ↦ 9
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  b := 9;
  ()
} [("x", nat 3), ("b", nat 9)] = true := by native_decide

/-! ## §2.4 Take and refill: reading through a borrow -/

-- `*b` under ⇒ moves the payload out through the borrow, leaving a hole ⊥.
-- let x = Cons(3, Nil); let b = &mut x; let tail = *b
--   ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 ⊥, tail ↦ Cons 3 Nil
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
  let tail = *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 .bot), ("tail", cons (nat 3) nil)] = true := by
  native_decide

-- The refill closes the hole; no list node was copied. `tail` is DATA (a
-- Cons-tree), so reading it into the new node MOVES it (§2.1 keeps Rust's line
-- for aggregates) — tail ↦ ⊥.
-- … *b := Cons(7, tail)
--   ⟹  x ↦ loanₘ ℓ0, b ↦ borrowₘ ℓ0 (Cons 7 (Cons 3 Nil)), tail ↦ ⊥
example : expectEnv prog{
  let x = Cons(3, Nil);
  let b = &m x;
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
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  let c = &m *b;
  ()
} [("x", .loanM 0), ("b", .borrowM 0 (.loanM 1)), ("c", .borrowM 1 (nat 3))] = true := by
  native_decide

-- Reading x through the suspended reborrow collapses the whole chain: End-Mut
-- ℓ0 then End-Mut ℓ1 fire in turn (the fuel-bounded reorganize-retry loop), and
-- x's value arrives; the retry read then COPIES it (§2.1).
--   ⟹  x ↦ 3 (copied), b ↦ ⊥, c ↦ ⊥, z ↦ 3
example : expectEnv prog{
  let x = 3;
  let b = &m x;
  let c = &m *b;
  let z = x;
  ()
} [("x", nat 3), ("b", .bot), ("c", .bot), ("z", nat 3)] = true := by native_decide

/-! ## Rejections (stuckness = no applicable rule) -/

-- §2.1 copy-on-read makes a marker-free value re-readable: the second read of x
-- copies again — no use-after-move. (Use-after-move rejections now live on
-- marker-carrying values — a moved borrow, a taken payload.)
example : expectEnv prog{
  let x = 3;
  let y = x;
  let z = x;
  ()
} [("x", nat 3), ("y", nat 3), ("z", nat 3)] = true := by native_decide

-- Fill through a non-place term: ⇐ is only defined on places.
example : expectErr prog{
  Pair(1) := 7;
  ()
} "not a place" = true := by native_decide

-- The flagship §2.5 self-reborrow: `b := c` after `let c = &mut *b`. The RHS
-- ⇒-consumes c, so borrowₘ ℓ1 3 is in flight; drop must vacate b, which
-- requires ending ℓ1, whose borrow is exactly that in-flight value — no entry,
-- no rule, rejected.
example : expectErr prog{
  let x = 3;
  let b = &m x;
  let c = &m *b;
  b := c;
  ()
} "in flight" = true := by native_decide

end Dllbc.Tests.S2
end
-- └── end of what was `S2.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S3.lean` ──────────────────────────────────────────────
section
/-!
# §3 test suite — "Match" (concrete machine)

The runtime content of §3: owned destructuring (§3.1) and borrow-mode match —
field reborrows, suspension, variant change through the parent (§3.3–3.4). The
symbolic layer (§3.2 σ, ⇜ refinement) is out of scope (milestone 3).

Same golden-Ω style as S2: run the `prog{…}` program, compare the final
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
-- rebuilds the pair, reading `a`/`b` by copy (§2.1, marker-free). The binders are
-- the ARM's, so they leave with it (M31 Stage 0 pop-with-drop) — before that they
-- outlived it, and the environment read `a ↦ 3, b ↦ 7` after the match.
-- p ↦ ⊥, q ↦ Pair 3 7.
example : expectEnv prog{
  let p = Pair(3, 7);
  let q = match p { Pair(a, b) => Pair(a, b) };
  ()
} [("p", .bot), ("q", pair (nat 3) (nat 7))] = true := by
  native_decide

-- A nested owned match: destructure the pair, then destructure its second
-- field. The inner match is in TAIL position within the outer arm, so it has no
-- seam of its own and its binders die with the arm that contains them: one pop
-- takes `a`, `rest`, `h` and `t` together (M31 Stage 0), and only the outer
-- `let`'s `r` survives.
example : expectEnv prog{
  let p = Pair(1, Cons(2, Nil));
  let r = match p {
    Pair(a, rest) => match rest { Cons(h, t) => Pair(a, h), Nil => Pair(a, a) }
  };
  ()
} [("p", .bot), ("r", pair (nat 1) (nat 2))] = true := by native_decide

/-! ## §3.3 Borrow mode: matching through -/

-- **What the suspension survives, and what ends it.** The field binders are
-- whole-value reborrows and the parent's payload is a Cons of loan markers — but
-- the binders are the arm's, so the arm's close ENDS their reborrows (M31 Stage 0
-- drops in reverse binding order: ℓ2, then ℓ1) and each payload plugs back into
-- the parent. What is observable one statement later is therefore the parent
-- holding the strong-updated payload, not the marker chain. Before pop-with-drop
-- the chain survived here and collapsed lazily at the next demand; this is the
-- timing shift, and the value it collapses to is the same one.
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

-- Reading the owner back collapses the rest of the chain: End-Mut ℓ0 (parent) —
-- the field loans ℓ1, ℓ2 having already ended at the arm's close — so `x`'s value
-- arrives fully updated. `x` is a Cons-tree (DATA), so the read MOVES it (§2.1).
-- y ↦ Cons 0 Nil.
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

/-! ## §3.4 Variant change through the parent -/

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
-- y ↦ Cons 1 (Cons 0 Nil).
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

-- Match on a moved variable: `p = Nil` is DATA (a List), so `let q = p` MOVES it
-- (§2.1 keeps Rust's line for aggregates), and the later match finds the slot ⊥.
example : expectErr prog{
  let p = Nil;
  let q = p;
  match p { Nil => () }
} "use-after-move" = true := by native_decide

-- No branch matches the head constructor (no exhaustiveness checking — there
-- are no inductive declarations yet — so an unmatched head is a runtime stuck).
example : expectErr prog{
  let p = Nil;
  match p { Cons(h, t) => () }
} "no branch" = true := by native_decide

-- Matching through a hole: `*b` is taken first, leaving the borrow payload ⊥,
-- and no rule reads through ⊥.
example : expectErr prog{
  let x = Cons(3, Nil);
  let b = &m x;
  let tail = *b;
  match b { Cons(hd, tl) => (), Nil => () }
} "hole" = true := by native_decide

end Dllbc.Tests.S3
end
-- └── end of what was `S3.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S3Sym.lean` ──────────────────────────────────────────────
section
/-!
# §3.2 test suite — the symbolic layer (σ and ⇜)

Matching a *symbolic* scrutinee splits the run: the `explore` driver forks one
path per branch, each entered by a ⇜ refinement (`writeC`) that substitutes
`C (sym σ₁) … (sym σₙ)` for σ everywhere in Ω. Owned mode then destructures;
borrow mode reborrows the fields. Concrete programs are unaffected (the S2/S3
suites still pass).

**Where the σ comes from.** These tests used to inject one, seeding Ω by hand
(`expectPaths [(⟨0,"n"⟩, .sym 0)] …`) on the grounds that symbolic entries have
no surface syntax. They do not need one: §6.1's call rule hands a caller a fresh
existential at the callee's return type, so `let n = anyNat()` *is* a symbolic
`n`, minted by the checker rather than by the harness. Every test below is now a
program the surface can write, and the ones that observed a mid-borrow state
(`x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ σ`) reach it the way a program does — own the value,
then borrow it.

Golden-Ω style, unchanged: `progPathsOfT` compares the per-path
canonicalized environments (ℓ- and σ-ids renumbered to first-appearance order) in
branch-declaration order, and the path COUNT with them. It drops the cohort's own
function bindings, so what is compared is exactly what the hand-seeded harness
used to compare — the expected environments below are the originals, unedited.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S3Sym

/-- Two declarations that exist to be CALLED. Checking mode never runs a callee's
    body — it applies the §5.3/§6.1 signature rule — so what a caller learns from
    `anyNat()` is exactly "a Nat, and nothing else", which is what a σ is. The
    bodies are irrelevant to every test in this file and are the simplest that
    typecheck.

    Both are written as a PREFIX: every test below is `withAny prog{ … }` and gets
    them in scope. Legal as a prefix helper — and the only shape that is — because
    the tails are plain statements: a `%`-spliced tail may not itself declare
    functions, since both chains number their slots from `progBase` and the inner
    would shadow the outer. -/
def withAny (rest : Term) : Term := prog{
  fn AnyNat () -> Nat { 0 };
  fn AnyList () -> List Nat { Nil };
  %rest }

/-! The file-local `progPathsOfT` retired with the `FnDef` subjects it took (M28
    ν): `tailPaths` in `Dllbc/Program.lean` is the same three lines over a
    program, and carries the same reason for existing. The COUNT is half the
    assertion and not a formality — §3.2's whole claim is that matching a symbolic
    scrutinee splits the run, so a rewrite that checked only the environments would
    still pass if the fork stopped happening. That is also why these assertions
    exist at all: deleting them was weighed when the file moved off its hand-seeded
    Ω, and they were kept for the path-count canary and for the doc traces they
    carry verbatim. -/

/-! ## §3.2 Symbolic scrutinee: refinement as ⇜ (owned mode) -/

-- is_zero's shape: n ↦ (σ : Nat); a two-branch owned match splits into two
-- paths. Z branch: ⇜ σ := Z, then n consumed to ⊥. S branch: ⇜ σ := S σ′,
-- then n ↦ ⊥ and the field binder m ↦ (σ′ : Nat).
def isZero : Term := withAny prog{
  let n = AnyNat();
  match n { Z => (), S(m) => () }
}

example : tailPaths isZero
  [ [("n", .bot)],
    [("n", .bot), ("m", .sym 0)] ] = true := by native_decide

/-! ## §3.3 Borrow mode on a symbolic payload -/

-- zero_head, symbolic: b ↦ borrowₘ ℓ (σ : List). The Cons branch reborrows the
-- fields, `*hd := 0` strong-updates the head, and demanding the owner collapses
-- the chain to `Cons 0 σ₂` (the doc's trace verbatim). The Nil branch refines
-- the payload to Nil. Two paths.
def zeroHead : Term := withAny prog{
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

example : tailPaths zeroHead
  [ [("x", .bot), ("b", .bot), ("y", cons (nat 0) (.sym 0))],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## §3.4 Symbolic variant change -/

-- `*b := Nil` in the Cons branch drops the reborrowed fields (their loans are Ω
-- entries) and installs Nil; both paths leave the owner holding Nil.
def variantChange : Term := withAny prog{
  let x = AnyList();
  let b = &m x;
  match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
  let y = x;
  ()
}

-- Both paths now leave the SAME Ω — the Cons path's `hd`/`tl` left with the arm
-- (M31 Stage 0) and were the only thing distinguishing it. The path COUNT is
-- what this assertion still discriminates on, which is the half it was kept for.
example : tailPaths variantChange
  [ [("x", .bot), ("b", .bot), ("y", nil)],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Two-level symbolic match (composed refinements) -/

-- Match `b` through, then match the field binder `tl` through — the refinements
-- compose. Three paths (outer Cons × {inner Cons, inner Nil}, plus outer Nil):
--   Cons σ₀ (Cons 0 σ₁),  Cons σ₀ Nil,  Nil.
def twoLevel : Term := withAny prog{
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
example : expectMErr [(⟨0,"x"⟩, cons (nat 3) nil)]
  (writeC (.var ⟨0,"x"⟩) (nat 9)) "expected a symbolic" = true := by native_decide

-- A symbolic match in expression position (a constructor argument) cannot split
-- and is rejected clearly by the pre-pass / readR.
def exprPosition : Term := withAny prog{
  let z = AnyList();
  let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
  ()
}

example : progRejects exprPosition "expression position"
  = true := by native_decide

end Dllbc.Tests.S3Sym
end
-- └── end of what was `S3Sym.lean` ───────────────────────────────────────────────


-- ┌── M31 Stage 0: pop-with-drop ─────────────────────────────────────────────
section
/-!
# Scopes pop, and dropping ends what they held

Ω entries leave with the scope that bound them: a match arm's binders at the
arm's close, a call frame's slots at return. Each popped entry surrenders the
borrows it holds first, in reverse binding order — Rust's — so the ends that used
to wait for the next demand happen at the scope boundary instead.

The §3 traces above already carry the arm half in their expected environments
(the binders are simply not there any more). What is asserted here is the part
those traces cannot show: that the pop is not a leak — the drop really runs — and
that the one case where an entry must NOT go still works.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S31Pop

/-! ## The drop runs: an arm's reborrows are surrendered at its close -/

-- The arm reborrows the fields and writes through one of them. At the arm's
-- close both reborrows end — last-bound first — so the parent is whole again
-- without anything having demanded it, and the owner reads back its updated
-- value. Compare the §3.3 trace above, which observes the same program one
-- statement earlier.
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

-- The callee binds `v` and, in its arm, `hd` and `tl`. None of them is an entry
-- of Ω once the call has returned — which is what retired the `id < 10000`
-- filter every Ω-reading harness used to carry (`Program.runProgram`). Asserted
-- as absence-from-Ω rather than as a whole expected environment because the
-- declaration entry itself is a runtime λ, which has no writable literal.
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
-- └── end of M31 Stage 0 ────────────────────────────────────────────────────
