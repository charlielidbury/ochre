import Och.SubCheckVal
import Och.TyCheck
import Och.NbE
import Och.Std.Nat
import Och.Std.Unit
import Och.Std.Bool
import Och.Std.DBool
import Och.Std.DNat
import Och.Std.Pair

/-!
# Property tests for the NbE checker

Three families targeting gaps the per-module tests don't cover:

  1. **Open-context** — `subCheckVal` under non-empty `tyCtx`/`ρ`,
     so neutral-ascent, `.lam,.lam` body recursion, and `.app`-
     neutral arguments are exercised at depth. The soundness
     proof's open-Γ generalisation (`tyCheck_sound_open`) needs
     exactly these paths.
  2. **Negative subtyping** — `NbE.subCheck a b = .ok false` for
     pairs that *should* fail. Per-module tests are mostly
     positive; this pins down rejection.
  3. **Quote round-trip** — `nf e ≡ e` (both directions of
     `subCheck`) for a corpus of closed terms. Empirically
     witnesses `eval_quote_equiv_closed`.

All NbE-only (`NbE.subCheck`/`subCheckVal`/`typeCheck`); the
legacy Expr-domain `subCheckNF` is being retired.
-/

namespace Och.PropertyTests
open Std NbE

/-! ## 1. Open-context `subCheckVal` -/

section OpenContext

-- A two-entry type context: var 0 : Nat_, var 1 : (Nat_ → Nat_).
private def vNat   : Val := (eval 200 unfBound [] Nat_).get!
private def vUnit  : Val := (eval 200 unfBound [] Unit_).get!
private def vNatNat : Val := (eval 200 unfBound [] (och{Nat_ → Nat_})).get!
private def Γ₂ : NbE.TyCtx := #[vNat, vNatNat]
-- Matching value-environment (de Bruijn index ↦ level): bvar 0
-- in a 2-context is the *innermost* binder = level 1, bvar 1 =
-- level 0. So ρ is reversed.
private def ρ₂ : Env := [.neutral (.var 1), .neutral (.var 0)]

-- (1a) Bare neutral ascent: `var 0 : Nat_`, so `var 0 ⊑ Nat_`.
example : subCheckVal 200 Γ₂ [] (.neutral (.var 0)) vNat
  = .ok true := by native_decide

-- (1b) The other binder: `var 1 : (Nat_ → Nat_)`, so
-- `var 1 ⊑ (Nat_ → Nat_)`.
example : subCheckVal 200 Γ₂ [] (.neutral (.var 1)) vNatNat
  = .ok true := by native_decide

-- (1c) Neutral-app ascent: `var 1 : (Nat_ → Nat_)`, applying it
-- to `var 0 : Nat_` gives a neutral whose ascent type is
-- `Nat_` (the codomain). So `(var 1) (var 0) ⊑ Nat_`.
example : subCheckVal 200 Γ₂ []
    (.neutral (.app (.var 1) (.neutral (.var 0)))) vNat
  = .ok true := by native_decide

-- (1d) Cross-ascent failure: `var 0 : Nat_`, NOT `Unit_`.
example : subCheckVal 200 Γ₂ [] (.neutral (.var 0)) vUnit
  = .ok false := by native_decide

-- (1e) `.lam,.lam` body recursion under non-empty Γ. Both sides
-- are `λx:Nat_. (bvar 1) x` evaluated in ρ₂ (bvar 1 is the
-- outer level-1 neutral, type `Nat_ → Nat_`); the body
-- comparison happens at Γ₂.push vNat (depth 2). Built as a raw
-- Expr since the `och{}` macro has no syntax for free bvars.
private def vLamApp : Val :=
  (eval 200 unfBound ρ₂
    (.lam Nat_ (.app (.bvar 1) (.bvar 0)))).get!
example : subCheckVal 200 Γ₂ [] vLamApp vLamApp
  = .ok true := by native_decide
-- And against the type `(Nat_ → Nat_)`: the body `(var 1) x`
-- ascends to `Nat_` via `tyCtx[1] = (Nat_ → Nat_)` applied to
-- `x : Nat_`.
example : subCheckVal 200 Γ₂ [] vLamApp vNatNat
  = .ok true := by native_decide

-- (1f) Pinning a known incompleteness: the algorithm has only
-- LHS-neutral ascent, so a concrete type can never be checked
-- *below* a fresh neutral. With `var 0 : Nat_`, neither
-- direction of `(λy:(var 0). y) ?⊑? (Nat_ → Nat_)` passes —
-- the `.lam,.lam` body check ends up at `vNat ⊑ var2` (RHS
-- neutral, no ascent) or the contravariant domain at
-- `vNat ⊑ var0` (same). This is the same shape as the A6
-- `domA`-vs-`domB` incompleteness; pinned so a future
-- RHS-ascent / `domB` re-enabling flips it visibly.
private def vLamVar0 : Val :=
  (eval 200 unfBound ρ₂ (.lam (.bvar 1) (.bvar 0))).get!
example : subCheckVal 200 Γ₂ [] vNatNat vLamVar0
  = .ok false := by native_decide
example : subCheckVal 200 Γ₂ [] vLamVar0 vNatNat
  = .ok false := by native_decide
-- But two open lambdas with the *same* neutral domain DO match
-- (refl on the neutral):
example : subCheckVal 200 Γ₂ [] vLamVar0 vLamVar0
  = .ok true := by native_decide

-- (1g) `tyCheck` at non-empty context: `tyCheck Γ₂ ρ₂ (?0) Nat_`.
-- bvar 0 evals in ρ₂ to `var 1`, whose tyCtx entry is
-- `(Nat_ → Nat_)`, so checking against `Nat_` should *fail*;
-- against `(Nat_ → Nat_)` should pass.
example : tyCheck 200 Γ₂ ρ₂ (.bvar 0) vNat = .ok false := by
  native_decide
example : tyCheck 200 Γ₂ ρ₂ (.bvar 0) vNatNat = .ok true := by
  native_decide

end OpenContext

/-! ## 2. Negative subtyping -/

section Negative

-- Numerals are not their predecessors.
example : NbE.subCheck 800 dtwo done_ = .ok false := by native_decide
example : NbE.subCheck 400 done_ dzero = .ok false := by native_decide
example : NbE.subCheck 400 dzero done_ = .ok false := by native_decide

-- Distinct base types.
example : NbE.subCheck 200 Nat_ Unit_ = .ok false := by native_decide
example : NbE.subCheck 200 Unit_ Nat_ = .ok false := by native_decide
example : NbE.subCheck 200 Std.Bool Nat_ = .ok false := by native_decide

-- Distinct lambdas (different domain ⇒ different function).
example : NbE.subCheck 200 (och{ λx:Nat_. x }) (och{ λx:Unit_. x })
  = .ok false := by native_decide
example : NbE.subCheck 200 (och{ λx:Unit_. x }) (och{ λx:Nat_. x })
  = .ok false := by native_decide

-- DBool: the type is not one of its constructors, and the
-- constructors are mutually unrelated. (Already in DBool.lean,
-- duplicated here so this file alone covers the negative shape.)
example : NbE.subCheck 200 dBool dtrue = .ok false := by native_decide
example : NbE.subCheck 200 dfalse dtrue = .ok false := by native_decide
example : NbE.subCheck 200 dtrue dfalse = .ok false := by native_decide

-- Parametric: `Pair A B` is invariant in both arguments
-- (post-A1, neutral-app args are bidirectional).
example : NbE.subCheck 200 (och{ Pair Nat_ Unit_ })
  (och{ Pair Unit_ Nat_ }) = .ok false := by native_decide
-- And the value-vs-type direction:
example : NbE.subCheck 200 (och{ Pair Nat_ Unit_ }) Nat_
  = .ok false := by native_decide

-- A constructor is not the type, in either DNat direction.
example : NbE.subCheck 400 dNat dzero = .ok false := by native_decide
example : NbE.subCheck 400 dNat done_ = .ok false := by native_decide

-- Top is one-directional.
example : NbE.subCheck 200 (.type) Nat_ = .ok false := by native_decide

end Negative

/-! ## 3. Quote round-trip

`nf e = quote (eval e)`. For closed `e`, `nf e` should be
`Subtype'`-equivalent to `e` (both directions of `subCheck`).
This is `eval_quote_equiv_closed` empirically. -/

section RoundTrip

private def rtCorpus : List Expr := [
  .type, zero_, one_, Nat_, Std.Bool, true_, Unit_, unit_,
  dtrue, dfalse, dBool, dzero, done_, dNat,
  och{ Nat_ → Nat_ }, och{ λx:Nat_. x }, och{ succ_ zero_ },
  och{ Pair Nat_ Unit_ }, och{ pair_ Nat_ Unit_ zero_ unit_ },
  .iota .type Nat_, .fix .type Nat_,
  .asc zero_ Nat_, .letE zero_ (.bvar 0)
]

/-- Each corpus term normalises within fuel 400. -/
theorem rt_nf_total :
    rtCorpus.all (fun e => (nf 400 e).isOk) = true := by
  native_decide

/-- Forward: `nf e ⊑ e` for every corpus term. -/
theorem rt_forward :
    rtCorpus.all (fun e =>
      match nf 400 e with
      | .ok e' => NbE.subCheck 400 e' e == .ok true
      | _ => false) = true := by
  native_decide

/-- Backward: `e ⊑ nf e` for every corpus term. -/
theorem rt_backward :
    rtCorpus.all (fun e =>
      match nf 400 e with
      | .ok e' => NbE.subCheck 400 e e' == .ok true
      | _ => false) = true := by
  native_decide

/-- **Finding**: syntactic idempotence (`nf (nf e) = nf e`) does
NOT hold — `done_` fails: `nf done_` is 44863 chars,
`nf (nf done_)` is 88671. The cause is the `unf=1↔unfBound`
mismatch (`quoteClosure` re-evaluates closure bodies at
`unf=1`, but `nf`'s outer `eval` uses `unf=unfBound`); this is
the documented `eval_unf_equiv` gap (SoundnessProof.lean). The
two are *semantically* equivalent (subCheck both directions
✓), so we test that instead. -/
theorem rt_nf_idempotent_equiv :
    rtCorpus.all (fun e =>
      match nf 400 e with
      | .ok e' =>
        match nf 400 e' with
        | .ok e'' =>
          NbE.subCheck 400 e' e'' == .ok true &&
          NbE.subCheck 400 e'' e' == .ok true
        | _ => false
      | _ => false) = true := by
  native_decide

/-- The non-idempotent witness, pinned so it doesn't silently
flip if `quoteClosure`'s `unf` changes. -/
example : (nf 400 done_) >>= (nf 400 ·) ≠ nf 400 done_ := by
  native_decide

end RoundTrip

/-! ## 4. Reflexivity / top sweep

Cheap structural sanity over the same corpus — every term
subtypes itself, and everything subtypes `Type`. -/

theorem refl_sweep :
    rtCorpus.all (fun e =>
      NbE.subCheck 400 e e == .ok true) = true := by
  native_decide

theorem top_sweep :
    rtCorpus.all (fun e =>
      NbE.subCheck 400 e .type == .ok true) = true := by
  native_decide

end Och.PropertyTests
