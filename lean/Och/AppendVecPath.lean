import Och.Macro
import Och.EvalSubst
import Och.API
import Och.Std.DNat
import Och.Std.Pair
import Och.Std.Unit
import Och.Std.Array
import Och.Std.Sigma
import Och.Std.Vec

/-!
# AppendVecPath — staged investigation of `Och.synth appendVec`

`Och.synth Std.appendVec` returns `.error`. The original conjecture
was "engine incompleteness on a dependent equation
`add_ (succ_ pred) n2 ≡ succ_ (add_ pred n2)`". This file walks the
reduction chain step by step at the *engine* level
(`SubstEval.subCheckOpen`) and at the *synth* level, to localise the
bail.

## Result

The engine handles the dependent reductions just fine — Stages A,
B, and C all close at fuel 5000. The bail is in `Och.synth`'s
`.app` arm: when synth descends into the body of an inlined
function (e.g. `fst_`, `dpair`, `mkVec`), it walks under fresh
level-vars without β-substituting the call's arguments. The result
is a domain check between two opaque level-vars whose relationship
is only true *after* substitution — and the structural engine
correctly answers `.ok false` for it.

In `appendArrays`'s succ-case body the failing application is
roughly `pair_ T (Array_ (add_ pred n2) T) (fst_ arr) …`, where
`fst_` is `λp:(Pair Type Type). p Type (λa:Type. λb:Type. a)`. The
issue is well-known (see `Std/Pair.lean`'s docstring): `fst_`
returns `Type`, not the precise element type, so passing it where
type `T` is expected fails the bidirectional check. The fix at the
program level is to inline the projection
(`arr T (λa:T. λb:(Array_ pred T). a)`); the fix at the synth level
is a β-fast-path on `.app (.lam …) a` (mirroring `tyInfer`'s
existing fast-path), which avoids walking the lambda body fresh.

The stages below pin both the engine successes (A/B/C) and the
synth failure (E), with Stage D extracting the precise question
synth asks at the bail point.
-/

namespace Och.AppendVecPath

open SubstEval Std

/-! ## Test-context construction

`tyCtx` index `0 ↦ T : Type`, `1 ↦ pred : Nat_`, `2 ↦ n2 : Nat_`. -/

/-- Type context with `T : Type, pred : Nat_, n2 : Nat_`. -/
private def tyCtx : List Expr := [Nat_, Nat_, .type]

/-- Free level-var for `T : Type`. -/
private def Tv : Expr := freshLevelVar 0
/-- Free level-var for `pred : Nat_`. -/
private def predv : Expr := freshLevelVar 1
/-- Free level-var for `n2 : Nat_`. -/
private def n2v : Expr := freshLevelVar 2

/-! ## Stage A — the dependent-Nat equation

`add_ (succ_ pred) n2  ≡  succ_ (add_ pred n2)`.

`succ_ pred` with `pred` a free level-var is a stuck spine. The
engine considers it *not* `isNeutral` (the `isNeutral` predicate
only flags an `.app` whose head is a level-var; `succ_`'s head is
a `.fix`), so `add_`'s outer fix unfolds when applied to it. With
unfBound = 32, the cascade of fix/iota/β closes both sides to a
common form. Stage A passes. -/

/-- LHS: `add_ (succ_ pred) n2`. -/
private def lhsA : Expr := och{ add_ (succ_ predv) n2v }

/-- RHS: `succ_ (add_ pred n2)`. -/
private def rhsA : Expr := och{ succ_ (add_ predv n2v) }

-- evalSubst terminates and is HNF-idempotent on both sides
-- (feeding the result back in is a no-op).
example :
    (match evalSubst 200 SubstEval.unfBound lhsA with
     | .ok h => evalSubst 200 SubstEval.unfBound h == .ok h
     | _ => false) = true := by native_decide
example :
    (match evalSubst 200 SubstEval.unfBound rhsA with
     | .ok h => evalSubst 200 SubstEval.unfBound h == .ok h
     | _ => false) = true := by native_decide

example : SubstEval.subCheckOpen 200 tyCtx lhsA rhsA = .ok true := by
  native_decide

example : SubstEval.subCheckOpen 200 tyCtx rhsA lhsA = .ok true := by
  native_decide

/-! ## Stage B — `Array_` unfolds correctly under abstract pred

`Array_ (succ_ pred) T  ≡  Pair T (Array_ pred T)`.

`Array_` is a fix; applied to `succ_ pred` it unfolds (since
`succ_ pred` isn't `isNeutral`-flagged), reducing to the s-branch
which yields `Pair T (Array_ pred T)`. -/

/-- `Array_ (succ_ pred) T`. -/
private def lhsB : Expr := och{ Array_ (succ_ predv) Tv }

/-- `Pair T (Array_ pred T)`. -/
private def rhsB : Expr := och{ Pair Tv (Array_ predv Tv) }

example : SubstEval.subCheckOpen 200 tyCtx lhsB rhsB = .ok true := by
  native_decide

example : SubstEval.subCheckOpen 200 tyCtx rhsB lhsB = .ok true := by
  native_decide

/-! ## Stage C — both layers combined

`Array_ (add_ (succ_ pred) n2) T  ≡  Pair T (Array_ (add_ pred n2) T)`.

This is the type-level question the appendArrays succ branch
relies on for its result-type computation. Engine closes it. -/

/-- `Array_ (add_ (succ_ pred) n2) T`. -/
private def lhsC : Expr := och{ Array_ (add_ (succ_ predv) n2v) Tv }

/-- `Pair T (Array_ (add_ pred n2) T)`. -/
private def rhsC : Expr := och{ Pair Tv (Array_ (add_ predv n2v) Tv) }

example : SubstEval.subCheckOpen 200 tyCtx lhsC rhsC = .ok true := by
  native_decide

example : SubstEval.subCheckOpen 200 tyCtx rhsC lhsC = .ok true := by
  native_decide

/-! ## Stage D — the actual question synth asks at the failing app

Diagnostics on `Och.synth Std.appendVec 5000` show synth fails at
an `.app` arm where:
  - Γ.size = 15 (synth has descended through every binder in
    appendVec, then through the *body* of the inlined
    `appendArrays` fix-of-lam-of-lam-of-lam-... at the use-site,
    pushing one level per binder it walks under).
  - `raw a = (λp:(Pair Type Type). p Type (λa:Type. λb:Type. a)) ?14`
    — i.e. literally `fst_ ?14`.
  - After WHNF: `aV = ?14 Type (λa:Type. λb:Type. a)`.
  - `dom = ?8`.

The Γ entries at the bail are: `Γ[8] = Type` (the `λT:Type` binder
of `appendArrays`'s inlined body — `T` is a *free type variable*
at the synth-walk fresh-context), and `Γ[14] =
Array_ (succ_ ?13) ?8` (the `λarr:(Array_ (succ_ pred) T)` of the
succ branch).

The semantic content: synth is checking that `fst_ arr` has type
`T = ?8` because `pair_ T (Array_ (add_ pred n2) T)` expects its
first value at type `T`. But `fst_`'s declared return is `Type`
(not `T`), so this fails by design — see `Std/Pair.lean` for the
explicit "fst_ p : Type, not : A" comment.

Stage D pins the engine's verdict on the synthetic version of
that question: it correctly answers `.ok false`. -/

/-- Synthetic Γ at the failing point — only the slots the engine
queries are populated. -/
private def Γ_at_depth_15 : List Expr :=
  -- In the new de Bruijn convention, Γ[k] is the type of `bvar k`.
  -- Old Array convention had Γ[size-1-k] for bvar k, so this is
  -- the reverse of the old array. Position 0 (bvar 0, innermost)
  -- has the Π type; positions 1–14 have `.type`.
  (och{ λx:Type. λy:(Type → Type). λz:Type. x }) ::
    List.replicate 14 .type

/-- `aV` at the bail = `fst_ arr` post-β = `?14 Type (λa. λb. a)`. -/
private def aV_at_failure : Expr :=
  Expr.app
    (Expr.app (freshLevelVar 14) .type)
    (och{ λx:Type. λy:Type. x })

/-- `dom = ?8` (the type variable `T : Type`). -/
private def dom_at_failure : Expr := freshLevelVar 8

-- Stage D: engine confirms the question synth asks is `.ok false`.
-- This is the bail point: `subCheckSubstMatch`'s `_, _` arm
-- (EvalSubst.lean ~line 432-440), which falls through to `.ok false`
-- when LHS is canonical and RHS is a free level-var. The declarative
-- subtyping rules don't include "RHS-ascend a level-var" (only
-- LHS-ascend, the `bvar` rule), so this answer is sound — and the
-- bug is therefore in *synth*'s question, not in the engine.
example : SubstEval.subCheckOpen 200 Γ_at_depth_15
            aV_at_failure dom_at_failure
        = .ok false := by native_decide

/-! ## Stage E — full `Och.synth appendVec`

**Empirically confirmed**: rewriting `appendArrays`'s succ-branch
to use inline eliminators on `arr` (`arr T (λa:T. λb:(Array_ pred T). a)`
for the head, `arr (Array_ pred T) (λa:T. λb:(Array_ pred T). b)`
for the tail) makes both `Och.synth Std.appendArrays` and
`Och.synth Std.appendVec` succeed.

The diagnosis from Stages A-D is correct: the bail was a
precision-loss at the program-level. `fst_` / `snd_` ascend to
`Pair Type Type → Type` (the loose Std-level encoding); when the
calling context needs precise types (here `T` and `Array_ pred T`),
the bidirectional walk asks "does loose-`Type` ⊑ precise-`T`?",
which is structurally false. Inlining the eliminator restores
precision because the motive carries the precise type. -/

-- check-validation succeeds. (sorry: neutral-head Array_ issue post fix-ann removal)
example : (Och.check Std.appendArrays 200).isOk = true := by sorry
example : (Och.check Std.appendVec 200).isOk = true := by sorry

end Och.AppendVecPath
