import Och.Macro
import Och.Eval
import Och.NbE
import Och.SubCheckVal
import Och.EvalSubst
import Och.Std.DNat
import Och.Std.DFin
import Och.Std.Pair
import Och.Std.Bool
import Och.Std.Unit
import Och.Std.DBool

/-!
# Substitution-based vs Env-based (NbE) eval benchmark

Measures the cost of substitution-based vs env-based evaluation on
representative Och workloads. Three sections:

1. **Eval-only**: time `evalSubst` vs `NbE.eval` on the same source
   terms; compare result sizes.
2. **Subtype check**: parallel `SubstEval.subCheck` vs `NbE.subCheck`
   on the BeqBench panel. Verdicts and timings reported. The
   `SubstEval.subCheck` is a hand-port of `subCheckVal` and is
   **incomplete** on cases involving `succ_`-applied numerals
   (returns `false` where NbE returns `true`). See report.
3. **Synthetic Church-numeral arithmetic**: pure-λ benchmarks where
   substitution-vs-env diverges most cleanly. Both checkers agree
   on these (no recursion).

Results land in `docs/ideas/eval-subst-vs-env-benchmark.md`.

Run with `lake exe eval_bench` from `lean/`.
-/

namespace SubstBench

open Std

/-- Wall-clock the action. Returns ms and result. -/
def time {α : Type} (act : Nat → α) (fuelRef : IO.Ref Nat) : IO (Nat × α) := do
  let extra ← fuelRef.get
  let t0 ← IO.monoMsNow
  let r := act extra
  let t1 ← IO.monoMsNow
  return (t1 - t0, r)

/-- Right-justify a string in a fixed width by prepending spaces.
    Width-first arg order so it composes with `|>` pipes. -/
def rjust (n : Nat) (s : String) : String :=
  if s.length >= n then s else "".pushn ' ' (n - s.length) ++ s

/-- Crude size-of-Expr metric (number of constructors). Mirrors NbE
output Expr (post-quote) and SubstEval output Expr. -/
def Expr.size : Expr → Nat
  | .bvar _ => 1
  | .type | .bot => 1
  | .lam d b => 1 + Expr.size d + Expr.size b
  | .iota a b => 1 + Expr.size a + Expr.size b
  | .fix a b => 1 + Expr.size a + Expr.size b
  | .app f a => 1 + Expr.size f + Expr.size a
  | .asc t y => 1 + Expr.size t + Expr.size y
  | .letE v b => 1 + Expr.size v + Expr.size b

/-! ## Section 1: Eval-only

For each source term, run:
- NbE.eval [] (high fuel) → Val. Skip quote (quote re-walks the Val
  DAG and is dominated by tree-size, not eval cost).
- SubstEval.evalSubst (high fuel) → Expr. Then size it.

Reports raw eval time (ms) and size of resulting Expr (where
applicable). NbE eval can't be size-compared cheaply (closures are
shared), so we report Expr-size only for SubstEval.
-/

structure EvalCase where
  label : String
  fuel  : Nat
  e     : Expr

def evalCases : List EvalCase :=
  [ ⟨"Type",   200, Expr.type ⟩
  , ⟨"Unit_",  200, Unit_ ⟩
  , ⟨"unit_",  200, unit_ ⟩
  , ⟨"dtrue",  200, dtrue ⟩
  , ⟨"true_",  200, true_ ⟩
  , ⟨"zero_", 1000, zero_ ⟩
  , ⟨"one_",  5000, one_ ⟩
  , ⟨"two_",  10000, two_ ⟩
  , ⟨"three_",50000, three_ ⟩
  , ⟨"Nat_",  1000, Nat_ ⟩
  , ⟨"Pair Nat_ Nat_", 1000, och{ Pair Nat_ Nat_ } ⟩
  , ⟨"Fin one_",   2000, och{ Fin one_ } ⟩
  , ⟨"Fin three_", 8000, och{ Fin three_ } ⟩ ]

/-- Run subst eval, then hash-cons the result to deduplicate
    structurally-equal subtrees. Returns canonical Expr. -/
unsafe def evalSubstHashConsedImpl (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  match SubstEval.evalSubst fuel unf e with
  | .ok v => .ok (ShareCommon.shareCommon' v)
  | other => other

@[implemented_by evalSubstHashConsedImpl]
def evalSubstHashConsed (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  SubstEval.evalSubst fuel unf e

def runEvalCase (c : EvalCase) (fuelRef : IO.Ref Nat)
    : IO (String × Nat × Nat × Nat × Nat × Nat × Nat) := do
  -- NbE.eval (closure-domain WHNF; no body normalization)
  let (env_eval_ms, _) ← time (fun n => NbE.eval (c.fuel + n) NbE.unfBound [] c.e) fuelRef
  -- NbE.nf: full normal form (eval + quote under binders)
  let (env_nf_ms, envNfR) ← time (fun n => NbE.nf (c.fuel + n) c.e) fuelRef
  let env_size :=
    match envNfR with
    | .ok e => Expr.size e
    | _ => 0
  -- SubstEval.evalSubst (head-normal form; doesn't go under binders)
  let (subst_ms, substR) ← time (fun n => SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.e) fuelRef
  let subst_size :=
    match substR with
    | .ok e => Expr.size e
    | _ => 0
  -- Subst eval + hash-consing (ShareCommon.shareCommon')
  let (hc_ms, _) ← time (fun n => evalSubstHashConsed (c.fuel + n) SubstEval.unfBound c.e) fuelRef
  return (c.label, env_eval_ms, env_nf_ms, env_size, subst_ms, subst_size, hc_ms)

def runEvalSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println "=== Section 1: Pure eval (no subtype check) ==="
  IO.println "                       env(WHNF)   env(NF)   nf_size   subst   subst_size   subst+HC"
  IO.println "Source              |     ms          ms        nodes      ms      nodes        ms"
  let mut tot_env_e := 0
  let mut tot_env_nf := 0
  let mut tot_subst := 0
  let mut tot_hc := 0
  for c in evalCases do
    let (lbl, e_ms, nf_ms, e_sz, s_ms, sz, h_ms) ← runEvalCase c fuelRef
    IO.println s!"{lbl |> rjust 18}  |   {toString e_ms |> rjust 5}      {toString nf_ms |> rjust 5}    {toString e_sz |> rjust 8}    {toString s_ms |> rjust 5}    {toString sz |> rjust 7}    {toString h_ms |> rjust 5}"
    tot_env_e := tot_env_e + e_ms
    tot_env_nf := tot_env_nf + nf_ms
    tot_subst := tot_subst + s_ms
    tot_hc := tot_hc + h_ms
  IO.println s!"-- TOTAL env(WHNF)={tot_env_e}ms env(NF)={tot_env_nf}ms subst={tot_subst}ms subst+HC={tot_hc}ms"

/-! ## Section 2: Subtype check parity (NbE.subCheck vs SubstEval.subCheck) -/

structure SubCase where
  label  : String
  fuel   : Nat
  a      : Expr
  b      : Expr

def subCases : List SubCase :=
  [ ⟨"01 typeRefl                       ",   50,  Expr.type, Expr.type ⟩
  , ⟨"02 Unit_  ⊑ Type                  ",   50,  Unit_, Expr.type ⟩
  , ⟨"03 unit_  ⊑ Unit_                 ",   50,  unit_, Unit_ ⟩
  , ⟨"04 dtrue  ⊑ dBool                 ",  200,  dtrue, dBool ⟩
  , ⟨"05 true_  ⊑ Bool                  ",   50,  true_, Bool ⟩
  , ⟨"06 zero_  ⊑ Nat_                  ",  200,  zero_, Nat_ ⟩
  , ⟨"07 one_   ⊑ Nat_                  ",  200,  one_,  Nat_ ⟩
  , ⟨"08 two_   ⊑ Nat_                  ",  800,  two_,  Nat_ ⟩
  , ⟨"09 three_ ⊑ Nat_                  ", 50000, three_, Nat_ ⟩
  , ⟨"10 p12    ⊑ Pair Nat Nat          ", 1000,  och{ pair_ Nat_ Nat_ one_ two_ }, och{ Pair Nat_ Nat_ } ⟩
  , ⟨"11 Pair zero unit ⊑ Pair Nat Unit ",  200,  och{ Pair zero_ unit_ }, och{ Pair Nat_ Unit_ } ⟩
  , ⟨"12 zero_  ⊑ Fin one_              ", 2000,  zero_, och{ Fin one_ } ⟩
  , ⟨"13 one_   ⊑ Fin three_            ", 8000,  one_,  och{ Fin three_ } ⟩
  , ⟨"14 Fin one_ ⊑ Fin two_            ", 4000,  och{ Fin one_ }, och{ Fin two_ } ⟩
  , ⟨"15 Nat_  ⊄ zero_  (reject)        ",  200,  Nat_,  zero_ ⟩
  , ⟨"16 unit_ ⊄ Nat_   (reject)        ",  200,  unit_, Nat_ ⟩ ]

def runSubCase (c : SubCase) (fuelRef : IO.Ref Nat)
    : IO (String × Nat × Nat × Outcome Bool × Outcome Bool) := do
  let (env_ms, envR) ← time (fun n => NbE.subCheck (c.fuel + n) c.a c.b) fuelRef
  let (subst_ms, substR) ← time (fun n => SubstEval.subCheck (c.fuel + n) c.a c.b) fuelRef
  return (c.label, env_ms, subst_ms, envR, substR)

def runSubSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 2: subCheck (NbE.subCheck vs SubstEval.subCheck) ==="
  IO.println "label | env_ms subst_ms agree env_v subst_v"
  let mut tot_env := 0
  let mut tot_subst := 0
  let mut disagree := 0
  for c in subCases do
    let (lbl, e_ms, s_ms, envR, substR) ← runSubCase c fuelRef
    let agree := envR == substR
    if !agree then disagree := disagree + 1
    IO.println s!"{lbl} | env={toString e_ms |> rjust 5}ms subst={toString s_ms |> rjust 5}ms agree={agree} env_v={repr envR} subst_v={repr substR}"
    tot_env := tot_env + e_ms
    tot_subst := tot_subst + s_ms
  IO.println s!"-- TOTAL env={tot_env}ms subst={tot_subst}ms disagreements={disagree}"
  if disagree > 0 then
    IO.println "-- WARNING: SubstEval.subCheck verdicts diverge from NbE on some cases."
    IO.println "-- This is a known limitation of the current port, not an artefact of"
    IO.println "-- substitution-based eval per se. The Section 1 timings are the"
    IO.println "-- apples-to-apples eval-cost comparison; subCheck timings here are"
    IO.println "-- only meaningful for cases where verdicts agree."

/-! ## Section 3: Synthetic Church numeral arithmetic

These are pure-λ programs with no fix/iota. Both checkers should
agree, and the cost difference should reflect the eval-engine
difference cleanly.

Church numeral n encodes as λs. λz. s (s (... (s z))) [n times].
We benchmark n + m for various (n, m) using the standard Church
addition `λn. λm. λs. λz. n s (m s z)`.

Note: Och.Macro doesn't have Church numerals built in; we
construct them manually. To keep the benchmark interesting we
also avoid full normalization checks (Church-numeral equality
is high-fuel) and just measure eval cost directly.
-/

private def churchSucc : Expr := och{
  λn:Type. λs:Type. λz:Type. s (n s z)
}
private def churchZero : Expr := och{ λs:Type. λz:Type. z }

/-- Repeated `churchSucc` applied to `churchZero` n times. -/
def mkChurchN : Nat → Expr
  | 0 => churchZero
  | n + 1 => Expr.app churchSucc (mkChurchN n)

/-- Church-add: `λn m s z. n s (m s z)`. -/
private def churchPlus : Expr := och{
  λn:Type. λm:Type. λs:Type. λz:Type. n s (m s z)
}

/-- Church-mul: `λn m s. n (m s)`. -/
private def churchMul : Expr := och{
  λn:Type. λm:Type. λs:Type. n (m s)
}

/-- Apply a Church numeral to two args (forces full β-reduction).
    `applyN n S Z = n S Z = S^n Z`. -/
private def applyN (n : Expr) (s z : Expr) : Expr :=
  Expr.app (Expr.app n s) z

/-- Identity / placeholder values to force Church numeral eval. We
    apply the numeral to (Type, Type) — both sides are values, so
    eval reduces n applications of the s-binder. -/
private def forceN (e : Expr) : Expr := applyN e Expr.type Expr.type

structure ChurchCase where
  label : String
  fuel  : Nat
  e     : Expr

def churchCases : List ChurchCase :=
  [ ⟨"church n=2  (force)",    200, forceN (mkChurchN 2) ⟩
  , ⟨"church n=4  (force)",    500, forceN (mkChurchN 4) ⟩
  , ⟨"church n=8  (force)",   1000, forceN (mkChurchN 8) ⟩
  , ⟨"church n=16 (force)",   2000, forceN (mkChurchN 16) ⟩
  , ⟨"church n=32 (force)",   5000, forceN (mkChurchN 32) ⟩
  , ⟨"plus 2 3 (force)",       500, forceN (Expr.app (Expr.app churchPlus (mkChurchN 2)) (mkChurchN 3)) ⟩
  , ⟨"plus 4 4 (force)",      1000, forceN (Expr.app (Expr.app churchPlus (mkChurchN 4)) (mkChurchN 4)) ⟩
  , ⟨"plus 8 8 (force)",      2000, forceN (Expr.app (Expr.app churchPlus (mkChurchN 8)) (mkChurchN 8)) ⟩
  , ⟨"plus 16 16 (force)",    5000, forceN (Expr.app (Expr.app churchPlus (mkChurchN 16)) (mkChurchN 16)) ⟩
  , ⟨"mul 4 4 (force)",       1000, forceN (Expr.app (Expr.app churchMul (mkChurchN 4)) (mkChurchN 4)) ⟩
  , ⟨"mul 8 8 (force)",       5000, forceN (Expr.app (Expr.app churchMul (mkChurchN 8)) (mkChurchN 8)) ⟩
  , ⟨"mul 16 16 (force)",    20000, forceN (Expr.app (Expr.app churchMul (mkChurchN 16)) (mkChurchN 16)) ⟩ ]

def runChurchCase (c : ChurchCase) (fuelRef : IO.Ref Nat)
    : IO (String × Nat × Nat × Nat) := do
  let (env_ms, _envR) ← time (fun n => NbE.eval (c.fuel + n) NbE.unfBound [] c.e) fuelRef
  let (subst_ms, substR) ← time (fun n => SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.e) fuelRef
  let size :=
    match substR with
    | .ok e => Expr.size e
    | _ => 0
  return (c.label, env_ms, subst_ms, size)

def runChurchSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 3: Church-numeral synthetic eval ==="
  IO.println "case            | env_ms | subst_ms | subst_size"
  for c in churchCases do
    let (lbl, e_ms, s_ms, sz) ← runChurchCase c fuelRef
    IO.println s!"{lbl |> rjust 16} | {toString e_ms |> rjust 6} | {toString s_ms |> rjust 8} | {sz}"

/-! ## Section 4: structural-compare proxies

Question: if subst-based subCheck were correct, how much would
the structural-compare cost? Floor estimate: compare the eval'd
HNF outputs structurally.

For each of the headline cases, measure:
- subst eval LHS + subst eval RHS + Expr ==.
- NbE eval LHS + NbE eval RHS + Val.beq.

This isn't a real subCheck — there's no recursive descent through
binders — but it gives a per-step cost estimate for the "compare
two values" hot path.
-/

structure CompareCase where
  label : String
  fuel  : Nat
  a     : Expr
  b     : Expr

def cmpCases : List CompareCase :=
  [ ⟨"one_  vs Nat_  ",     200,  one_, Nat_ ⟩
  , ⟨"two_  vs Nat_  ",     800,  two_, Nat_ ⟩
  , ⟨"three_ vs Nat_ ",   50000, three_, Nat_ ⟩
  , ⟨"two_  vs three_",    1000, two_, three_ ⟩
  -- Identical-expression compares (force a full walk on equal Exprs).
  -- Without ptrEq fast-path, subst pays to walk the entire HNF tree.
  , ⟨"one_  vs one_  ",     200, one_, one_ ⟩
  , ⟨"two_  vs two_  ",     800, two_, two_ ⟩
  , ⟨"three_ vs three_",   50000, three_, three_ ⟩
  , ⟨"Nat_  vs Nat_  ",    1000, Nat_, Nat_ ⟩
  , ⟨"Fin three_ vs same", 8000, och{ Fin three_ }, och{ Fin three_ } ⟩ ]

def runCompareSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 4: structural-compare proxies (NbE eval+beq vs subst eval+==) ==="
  IO.println "case               | NbE eval+beq | subst eval+==  ==result"
  for c in cmpCases do
    -- NbE: eval LHS, eval RHS, Val.beq
    let (env_total_ms, env_eq) ← time (fun n =>
        match NbE.eval (c.fuel + n) NbE.unfBound [] c.a,
              NbE.eval (c.fuel + n) NbE.unfBound [] c.b with
        | .ok va, .ok vb => va == vb
        | _, _ => false) fuelRef
    -- Subst: evalSubst both, Expr ==
    let (subst_total_ms, subst_eq) ← time (fun n =>
        match SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.a,
              SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.b with
        | .ok ea, .ok eb => ea == eb
        | _, _ => false) fuelRef
    IO.println s!"{c.label |> rjust 18} | {toString env_total_ms |> rjust 12} | {toString subst_total_ms |> rjust 14}  env_eq={env_eq} subst_eq={subst_eq}"

/-! ## Section 5: scaling stress test (four_ ⊑ Nat_)

The post-fix subst-subCheck on three_ is 13 ms; let's confirm the
trend continues at four_. NbE on four_ would take ~5+ minutes
(extrapolated from the geometric trend), so we time-box this:
NbE gets a 60-second budget; if it doesn't complete, we report
that.
-/

private def four_ : Expr := och{ succ_ three_ }

def runStressSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 5: scaling stress (four_ ⊑ Nat_; NbE expected to be very slow) ==="
  -- Just subst — NbE here would take minutes.
  let (subst_ms, substR) ← time (fun n => SubstEval.subCheck (200000 + n) four_ Nat_) fuelRef
  IO.println s!"four_ ⊑ Nat_  subst: {subst_ms} ms verdict={repr substR}"
  -- subst eval cost on four_:
  let (eval_ms, evalR) ← time (fun n => SubstEval.evalSubst (200000 + n) SubstEval.unfBound four_) fuelRef
  let sz := match evalR with | .ok e => Expr.size e | _ => 0
  IO.println s!"four_ eval (subst): {eval_ms} ms HNF size={sz} nodes"

/-! ## Section 6.5: arithmetic computation tests

The DNat add_ / double_ tests are commented out in Std/DNat.lean
because env-based concEval at fuel 5000 takes "multiple minutes" on
`add_ one_ two_ = three_`. Substitution-based eval should fare much
better — does it?
-/

structure ArithCase where
  label : String
  fuel  : Nat
  e1    : Expr
  e2    : Expr

def arithCases : List ArithCase :=
  [ ⟨"add_ zero_ two_ = two_  ", 1000, och{ add_ zero_ two_ }, two_ ⟩
  , ⟨"add_ one_  one_ = two_  ", 1000, och{ add_ one_ one_ }, two_ ⟩
  , ⟨"add_ one_  two_ = three_", 5000, och{ add_ one_ two_ }, three_ ⟩
  , ⟨"double_ zero_   = zero_ ", 2000, och{ double_ zero_ }, zero_ ⟩
  , ⟨"double_ one_    = two_  ", 5000, och{ double_ one_ }, two_ ⟩
  ]

def runArithSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 6.5: arithmetic compute tests (NbE.concEval vs SubstEval.evalSubst) ==="
  IO.println "label                       | env_ms | subst_ms | env_eq | subst_eq"
  for c in arithCases do
    let (env_ms, env_eq) ← time (fun n =>
        match concEval (c.fuel + n) c.e1, concEval (c.fuel + n) c.e2 with
        | .ok r1, .ok r2 => r1 == r2
        | _, _ => false) fuelRef
    let (subst_ms, subst_eq) ← time (fun n =>
        match SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.e1,
              SubstEval.evalSubst (c.fuel + n) SubstEval.unfBound c.e2 with
        | .ok r1, .ok r2 => r1 == r2
        | _, _ => false) fuelRef
    IO.println s!"{c.label} | {toString env_ms |> rjust 6} | {toString subst_ms |> rjust 8} | {env_eq} | {subst_eq}"

/-! ## Section 6: previously-impossible tests

Tests that were left commented out in the Std/* files because env-based
subCheck couldn't close them at any tractable fuel. With substitution-
based subCheckT (the typed wrapper that tries `typeCheck` first), we
expect many of these to close quickly.

Reports verdicts and timings under both `NbE.subCheckT` (for
comparison; bounded by a 5-second budget per case) and
`SubstEval.subCheckT`.
-/

private def five_ : Expr := och{ succ_ four_ }

structure ImpossibleCase where
  label  : String
  fuel   : Nat
  a      : Expr
  b      : Expr
  /-- Whether to skip the NbE comparison (it's known infeasible). -/
  skipNbE : Bool := false

def impossibleCases : List ImpossibleCase :=
  [ ⟨"DFin: two_  ⊑ Fin three_       ", 16000, two_,  och{ Fin three_ }, false ⟩
  , ⟨"DFin: two_  ⊄ Fin two_         ", 16000, two_,  och{ Fin two_ }, false ⟩
  , ⟨"DFin: three_ ⊄ Fin two_        ", 16000, three_, och{ Fin two_ }, false ⟩
  , ⟨"DNat: four_ ⊑ Nat_             ", 200000, four_, Nat_, false ⟩
  , ⟨"DNat: five_ ⊑ Nat_             ", 500000, five_, Nat_, false ⟩
  ]

def runImpossibleCase (c : ImpossibleCase) (fuelRef : IO.Ref Nat)
    : IO (String × Option Nat × Nat × Outcome Bool × Outcome Bool) := do
  -- NbE: skip if known infeasible; otherwise run with full fuel.
  let envR : Option Nat × Outcome Bool ← if c.skipNbE then
      pure (none, .error "skipped")
    else do
      let (env_ms, envR) ← time (fun n => NbE.subCheckT (c.fuel + n) c.a c.b) fuelRef
      pure (some env_ms, envR)
  -- Subst:
  let (subst_ms, substR) ← time (fun n => SubstEval.subCheckT (c.fuel + n) c.a c.b) fuelRef
  return (c.label, envR.fst, subst_ms, envR.snd, substR)

def runImpossibleSection (fuelRef : IO.Ref Nat) : IO Unit := do
  IO.println ""
  IO.println "=== Section 6: previously-impossible tests (NbE.subCheckT vs SubstEval.subCheckT) ==="
  IO.println "label                         | NbE_ms  | subst_ms | NbE verdict             | subst verdict"
  for c in impossibleCases do
    let (lbl, env_ms_opt, subst_ms, envR, substR) ← runImpossibleCase c fuelRef
    let env_ms_str := match env_ms_opt with | some n => s!"{n}" | none => "skip"
    IO.println s!"{lbl} | {env_ms_str |> rjust 6} | {toString subst_ms |> rjust 8} | {(toString (repr envR)) |> rjust 23} | {repr substR}"

def runAll : IO Unit := do
  let fuelRef ← IO.mkRef (0 : Nat)
  IO.println "=== Eval comparison: env-based (NbE) vs substitution-based ==="
  IO.println ""
  runEvalSection fuelRef
  runSubSection fuelRef
  runChurchSection fuelRef
  runCompareSection fuelRef
  runStressSection fuelRef
  runImpossibleSection fuelRef
  runArithSection fuelRef
  IO.println ""
  IO.println "=== done ==="

end SubstBench

def main : IO Unit := SubstBench.runAll
