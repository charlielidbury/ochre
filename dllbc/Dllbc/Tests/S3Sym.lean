import Dllbc.Machine
import Dllbc.Macro

/-!
# §3.2 test suite — the symbolic layer (σ and ⇜)

Matching a *symbolic* scrutinee splits the run: the `explore` driver forks one
path per branch, each entered by a ⇜ refinement (`writeC`) that substitutes
`C (sym σ₁) … (sym σₙ)` for σ everywhere in Ω. Owned mode then destructures;
borrow mode reborrows the fields. Concrete programs are unaffected (the S2/S3
suites still pass).

Symbolic entries have no surface syntax, so each test seeds Ω directly (a
stand-in for a telescope entry until §5) and writes the program with
`dllbcWith [names]{…}`, which pre-binds the seeded variables to ids `0,1,…`.
Golden-Ω style: `expectPaths` compares the per-path canonicalized environments
(ℓ- and σ-ids renumbered to first-appearance order) in branch-declaration
order.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S3Sym

/-! ## §3.2 Symbolic scrutinee: refinement as ⇜ (owned mode) -/

-- is_zero's shape: n ↦ (σ : Nat); a two-branch owned match splits into two
-- paths. Z branch: ⇜ σ := Z, then n consumed to ⊥. S branch: ⇜ σ := S σ′,
-- then n ↦ ⊥ and the field binder m ↦ (σ′ : Nat).
example : expectPaths [(⟨0,"n"⟩, .sym 0)]
  dllbcWith [n] { match n { Z => (), S(m) => () } }
  [ [("n", .bot)],
    [("n", .bot), ("m", .sym 0)] ] = true := by native_decide

/-! ## §3.3 Borrow mode on a symbolic payload -/

-- zero_head, symbolic: b ↦ borrowₘ ℓ (σ : List). The Cons branch reborrows the
-- fields, `*hd := 0` strong-updates the head, and demanding the owner collapses
-- the chain to `Cons 0 σ₂` (the doc's trace verbatim). The Nil branch refines
-- the payload to Nil. Two paths.
example : expectPaths [(⟨0,"x"⟩, .loanM 0), (⟨1,"b"⟩, .borrowM 0 (.sym 0))]
  dllbcWith [x, b] {
    match b { Cons(hd, tl) => { *hd := 0; () }, Nil => () };
    let y = x;
    ()
  }
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", cons (nat 0) (.sym 0))],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## §3.4 Symbolic variant change -/

-- `*b := Nil` in the Cons branch drops the reborrowed fields (their loans are Ω
-- entries) and installs Nil; both paths leave the owner holding Nil.
example : expectPaths [(⟨0,"x"⟩, .loanM 0), (⟨1,"b"⟩, .borrowM 0 (.sym 0))]
  dllbcWith [x, b] {
    match b { Cons(hd, tl) => { *b := Nil; () }, Nil => () };
    let y = x;
    ()
  }
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", nil)],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Two-level symbolic match (composed refinements) -/

-- Match `b` through, then match the field binder `tl` through — the refinements
-- compose. Three paths (outer Cons × {inner Cons, inner Nil}, plus outer Nil):
--   Cons σ₀ (Cons 0 σ₁),  Cons σ₀ Nil,  Nil.
example : expectPaths [(⟨0,"x"⟩, .loanM 0), (⟨1,"b"⟩, .borrowM 0 (.sym 0))]
  dllbcWith [x, b] {
    match b {
      Cons(hd, tl) => match tl {
        Cons(h2, t2) => { *h2 := 0; let y = x; () },
        Nil => { let y = x; () }
      },
      Nil => { let y = x; () }
    }
  }
  [ [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("h2", .bot), ("t2", .bot),
     ("y", cons (.sym 0) (cons (nat 0) (.sym 1)))],
    [("x", .bot), ("b", .bot), ("hd", .bot), ("tl", .bot), ("y", cons (.sym 0) nil)],
    [("x", .bot), ("b", .bot), ("y", nil)] ] = true := by native_decide

/-! ## Rejections -/

-- ⇜ (writeC) refines only a symbolic place; aimed at a concrete value it errors.
example : expectMErr [(⟨0,"x"⟩, cons (nat 3) nil)]
  (writeC (.var ⟨0,"x"⟩) (nat 9)) "expected a symbolic" = true := by native_decide

-- A symbolic match in expression position (a constructor argument) cannot split
-- and is rejected clearly by the pre-pass / readR.
example : expectSomePathErr [(⟨0,"z"⟩, .sym 0)]
  dllbcWith [z] {
    let y = Cons(match z { Nil => Nil, Cons(a, r) => Nil }, Nil);
    ()
  } "expression position" = true := by native_decide

end Dllbc.Tests.S3Sym
