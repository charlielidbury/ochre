import Dllbc.Program
import Dllbc.ProgMacro

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
  fn anyNat () -> Nat { 0 };
  fn anyList () -> List Nat { Nil };
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
  let n = anyNat();
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
  let x = anyList();
  let b = &mut x;
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
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", cons (nat 0) (.sym 0))],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## §3.4 Symbolic variant change -/

-- `*b := Nil` in the Cons branch drops the reborrowed fields (their loans are Ω
-- entries) and installs Nil; both paths leave the owner holding Nil.
def variantChange : Term := withAny prog{
  let x = anyList();
  let b = &mut x;
  match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
  let y = x;
  ()
}

example : tailPaths variantChange
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", nil)],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Two-level symbolic match (composed refinements) -/

-- Match `b` through, then match the field binder `tl` through — the refinements
-- compose. Three paths (outer Cons × {inner Cons, inner Nil}, plus outer Nil):
--   Cons σ₀ (Cons 0 σ₁),  Cons σ₀ Nil,  Nil.
def twoLevel : Term := withAny prog{
  let x = anyList();
  let b = &mut x;
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
  let z = anyList();
  let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
  ()
}

example : progRejects exprPosition "expression position"
  = true := by native_decide

end Dllbc.Tests.S3Sym
