import Dllbc.Boundary
import Dllbc.Macro

/-!
# Differential v2 — whole-program simulation (§9)

Closes M8's finding B: the differential now runs CALLER+CALLEE with the real
simulation relation, so it catches wrong-value refinements — the class the M7
`constrained` bug belonged to — not merely stuckness.

The property, upgraded: for every checkFn-accepted caller, its CONCRETE final
environment (run in *executing* mode — calls run the callee's actual body) is a
σ-**instance** of some accepted SYMBOLIC path's final environment (run in
*checking* mode — calls use the §5.3/§6.1 signature rule). `instanceOf` is
first-order matching: a symbolic `sym σ` matches any concrete value
*consistently* (same σ ⟹ same value), constructors match structurally,
loans/borrows up to the canonical renumbering. This is the simulation relation
proper.

**Harness validation** (the essential part — a counterexample-finder that has
never found its counterexample is unvalidated): with the (removed, unsound)
`constrained` wire forced on, the `advance`-caller differential goes RED; with
it off, GREEN. The `advance` cursor shares `through`'s signature but writes only
the tail, so the constrained refinement (owner ← surrendered tail) is a
provably-wrong fact — exactly what the relation catches.

Result (this run): 4 callers (through / advance / choose / push shaped), all
accepted, all a σ-instance of an accepted symbolic path (GREEN). The
`advance`-caller goes RED under forced-constrained and GREEN without —
validated.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S9Diff

def natT : Term := .const "Nat"
def boolT : Term := .const "Bool"
def listNatT : Term := .app (.const "List") natT

/-! ## The fixed callee pool -/

def through : Decl :=
  { name := "through", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { b } }

/-- `advance`: returns the tail's field reborrow on `Cons`, the argument on
    `Nil`. Same signature as `through`, different body. -/
def advance : Decl :=
  { name := "advance", retType := .borrowT listNatT listNatT,
    telescope := [("b", .borrowT listNatT listNatT)],
    body := dllbcWith [b] { match b { Nil => b, Cons(hd, tl) => tl } } }

def choose : Decl :=
  { name := "choose", retType := .borrowT natT natT,
    telescope := [("c", boolT), ("x", .borrowT natT natT), ("y", .borrowT natT natT)],
    body := dllbcWith [c, x, y] { match c { True => x, False => y } } }

def push : Decl :=
  { name := "push", retType := .const "Unit",
    telescope := [("e", natT), ("v", .borrowT listNatT listNatT)],
    body := dllbcWith [e, v] { let tail = *v; *v := Cons(e, tail); () } }

def pool : List Decl := [through, advance, choose, push]

/-! ## The simulation relation: `instanceOf` -/

/-- Match a symbolic value against a concrete one, threading a σ→value
    substitution (consistency: the same σ must map to the same value). -/
def matchVal : Val → Val → List (Nat × Val) → Option (List (Nat × Val))
  | .sym σ, cv, subst =>
    match subst.find? (·.1 == σ) with
    | some (_, v) => if v == cv then some subst else none
    | none => some ((σ, cv) :: subst)
  | .ctor n1 a1, .ctor n2 a2, subst => if n1 == n2 then matchList a1 a2 subst else none
  | .borrowM x p, .borrowM y q, subst => if x == y then matchVal p q subst else none
  | a, b, subst => if a == b then some subst else none   -- ⊥, loanM, pure: exact (canonicalized)
where matchList : List Val → List Val → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | v1 :: vs1, v2 :: vs2, s => match matchVal v1 v2 s with | some s' => matchList vs1 vs2 s' | none => none
  | _, _, _ => none

/-- Match two environments entry-by-entry (same names, same order). -/
def matchEnv : Env → Env → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | (n1, v1) :: r1, (n2, v2) :: r2, s =>
    if n1 == n2 then (match matchVal v1 v2 s with | some s' => matchEnv r1 r2 s' | none => none) else none
  | _, _, _ => none

/-- The concrete env is a σ-instance of the symbolic env. -/
def instanceOf (symEnv concEnv : Env) : Bool := (matchEnv symEnv concEnv []).isSome

/-! ## The two runs and the differential check -/

/-- Executing mode: run a body concretely (calls run callee bodies), returning
    the caller's own final Ω (frame vars id ≥ 10000 filtered out). -/
def runExec (table : List Decl) (body : Term) : Except String Env :=
  match (readR defaultFuel body).run { initSt with decls := table, executing := true } with
  | .ok _ st => .ok (canonicalize (st.env.filter (·.1.id < 10000)))
  | .error e _ => .error e

/-- Checking mode: the accepted symbolic paths' final environments. `fc`
    forces the (removed) constrained wire on — used only by the harness
    validation, `false` for the real property. -/
def symEnvs (fc : Bool) (table : List Decl) (body : Term) : List (Except String Env) :=
  (explore defaultFuel (pushContinuations body) { initSt with decls := table, forceConstrained := fc }).map
    (fun r => r.map (fun p => canonicalize (p.2.env.filter (·.1.id < 10000))))

/-- The differential: the concrete final env is an instance of some symbolic
    path's final env. -/
def diffV2 (fc : Bool) (table : List Decl) (body : Term) : Bool :=
  match runExec table body with
  | .error _ => false
  | .ok concEnv => (symEnvs fc table body).any (fun r => match r with
      | .ok se => instanceOf se concEnv
      | .error _ => false)

/-- checkFn on a caller (empty telescope). -/
def callerDecl (body : Term) : Decl :=
  { name := "caller", retType := .const "Unit", telescope := [], body := body }

/-! ## Callers (each demands ALL its owners, so both runs fully collapse) -/

/-- The choose caller from §6.1, demanding BOTH owners. -/
def chooseCaller : Term := dllbcWith [] {
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  *r := 7;
  let za = a; let zb = b;
  () }

/-- A push caller. -/
def pushCaller : Term := dllbcWith [] {
  let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () }

/-! ## The property, over the caller set -/

def callers : List Term :=
  [ dllbcWith [] { let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = through(b); *r := Cons(9, Nil); let y = x; () },
    dllbcWith [] { let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () },
    chooseCaller,
    pushCaller ]

def accepted : List Term := callers.filter (fun b => checkFnOk (callerDecl b) pool)

-- Every accepted caller's concrete run is a σ-instance of an accepted symbolic
-- path — the whole-program simulation theorem, over the caller set.
example : accepted.all (fun b => diffV2 false pool b) = true := by native_decide

/-! ## Harness validation: the bug goes RED, the fix GREEN -/

def advCallerBody : Term :=
  dllbcWith [] { let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () }

-- With the (removed, unsound) constrained wire FORCED on, the advance-caller's
-- symbolic run refines the owner to the surrendered tail (Cons 9 Nil), while it
-- concretely holds Cons 1 (Cons 9 Nil) — NOT an instance. The harness catches
-- it: RED.
example : diffV2 true pool advCallerBody = false := by native_decide

-- With it OFF (the real behavior), the opaque σ matches the concrete value: GREEN.
example : diffV2 false pool advCallerBody = true := by native_decide

end Dllbc.Tests.S9Diff
