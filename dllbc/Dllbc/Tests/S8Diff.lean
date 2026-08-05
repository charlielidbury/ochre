import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.DeclMacro
import Dllbc.Migrate

/-!
# Differential suite — the simulation theorem in testable form (§8)

**The property**: if `checkFn` accepts a declaration, then every small concrete
run of its body completes (is not stuck) and passes the concrete audit. This is
the simulation theorem — the symbolic checker over-approximates concrete
execution — as an exhaustively-checked `native_decide` proposition over a
bounded enumeration of bodies. It is the automated counterexample-finder that a
soundness bug (like M7's signature-driven `constrained`, once calls enter the
generator) trips mechanically, and the promised precursor to any metatheory.

v1 scope: NO calls (so this exercises the *callee-side* simulation — body
checking vs concrete body runs; caller-side group soundness needs calls, v2).
Matches are generated **exhaustive** over the scrutinee type's full constructor
set, deliberately: a non-exhaustive match is accepted (exhaustiveness checking
is deferred with inductive declarations) but concretely stuck on the missing
case — a known, separate gap, not the ownership soundness this suite targets.

If any accepted body has a concretely-stuck or audit-failing instantiation, the
`native_decide` below fails: that is a soundness counterexample, to be
minimized and reported, never hidden.

Counts (this run — and ASSERTED at the foot of this file, so a drift goes red
rather than quietly falsifying this comment): 136 bodies generated across three
telescopes, 75 accepted by `checkFn`, 238 concrete runs — all complete and audit.
No counterexample. "This run" is the honest reading: these describe the generator
and the acceptance behaviour as they stand, and a legitimate change to either
should update the numbers here, the assertions below, and the paper's §6.1
together.
  * `(v : &mut List Nat) → Unit`   : 91 gen / 47 accepted / 141 runs
  * `(n : Nat) → Nat`               : 32 gen / 15 accepted / 45 runs
  * `(b : &mut Nat, c : Bool) → Unit`: 13 gen / 13 accepted / 52 runs
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S8Diff

-- CONV-SUBJECT: generator builds raw Terms by design
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-! ## Body generator for `(v : &mut List Nat) → Unit`

    v is runtime var 0; match binders use fixed ids 2 (hd/x/tail), 3 (tl). A
    two-level, capped enumeration over the grammar constructs: `*`-take, `:=`
    through 0/1/2 peels, `&mut`, `let`, `seq`, and match-through (exhaustive
    over `Nil`/`Cons`). checkFn filters the ill-formed. -/

-- CONV-SUBJECT: generator builds raw Terms by design
def v0 : Term := .var ⟨0, "v"⟩

-- CONV-SUBJECT: generator builds raw Terms by design
/-- Small expression pool over v (RHS / place fillers). -/
def exprs : List Term :=
  [ .unit, nilT, tnat 0, tnat 1, .deref v0,
    .ctorApp "Cons" [tnat 0, nilT],
    .ctorApp "Cons" [tnat 0, .deref v0],
    .var ⟨2, "x"⟩ ]
where nilT : Term := .ctorApp "Nil" []

-- CONV-SUBJECT: generator builds raw Terms by design
/-- Leaf statement bodies (each returns `()`), depth ≈ 1. -/
def leafBodies : List Term :=
  [ .unit ]
  ++ exprs.map (fun e => .seq e .unit)                          -- e ; ()
  -- p := e ; ()  for p a place through 0/1/2 peels
  ++ ([v0, .deref v0].flatMap fun p => exprs.map fun e => .assign p e .unit)
  -- the take-and-refill idiom
  ++ [ .letIn ⟨2, "tail"⟩ (.deref v0)
        (.assign (.deref v0) (.ctorApp "Cons" [tnat 0, .var ⟨2, "tail"⟩]) .unit) ]
  -- a stray let
  ++ [ .letIn ⟨2, "x"⟩ (.deref v0) .unit ]

/-- Bodies with one exhaustive match-through on v, branches drawn from
    `leafBodies` (capped). In the `Cons` branch, hd = id 2, tl = id 3. -/
def matchBodies : List Term :=
  (leafBodies.take 8).flatMap fun bNil =>
    (leafBodies.take 8).map fun bCons =>
      .matchE ⟨0, "v"⟩ none [.mk "Nil" [] bNil, .mk "Cons" [⟨2, "hd"⟩, ⟨3, "tl"⟩] bCons]

/-- All generated bodies for the list-borrow telescope. -/
def vBodies : List Term := leafBodies ++ matchBodies

/-! ## The declaration and the concrete pool -/

def vDecl (body : Term) : FnDef :=
  decl{ fn f (v : &mut List Nat) -> Unit = %body }

/-- Concrete payloads for v: the small list pool. -/
def vPool : List Val := [ nil, cons (nat 1) nil, cons (nat 1) (cons (nat 2) nil) ]

/-! ## The concrete run and the differential check -/

/-- Seed a telescope with CONCRETE argument values (σ-free): a pure argument
    binds its value; a borrow argument binds `borrowM ℓ cval` and yields an
    obligation. -/
def seedConcrete (fuel : Nat) : Nat → List (String × Term) → List Val → M (List Obligation)
  | _, [], _ => pure []
  | i, (name, tyTerm) :: tRest, cval :: cRest => do
    let x : Var := ⟨i, name⟩
    match tyTerm with
    | .borrowT _ S => do
      let ℓ ← freshLoan
      bindSlot x (.borrowM ℓ cval)
      let owed := Val.nfV fuel (Val.substPure 0 cval (← readC fuel S))
      pure (⟨x, ℓ, owed, trivialOwedT tyTerm⟩ :: (← seedConcrete fuel (i + 1) tRest cRest))
    | _ => do
      bindSlot x cval
      seedConcrete fuel (i + 1) tRest cRest
  | _, _ :: _, [] => throwErr "seedConcrete: not enough concrete arguments"

/-- Run a declaration's body CONCRETELY from the given argument values, then run
    the concrete audit. `true` iff every path completes (not stuck) and audits. -/
def diffCheck (decl : FnDef) (concreteArgs : List Val) : Bool :=
  match (seedConcrete defaultFuel 0 decl.telescope concreteArgs).run initSt with
  | .error _ _ => false
  | .ok obs st =>
    let paths := explore defaultFuel (pushContinuations decl.body) st
    0 < paths.length && paths.all (fun r =>
      match r with
      | .ok (v, st') =>
        match (auditAction defaultFuel decl.retType v).run { st' with obligations := obs } with
        | .ok _ _ => true
        | .error _ _ => false
      | .error _ => false)

/-! ## The property, for the list-borrow telescope

    Every body the checker ACCEPTS runs to completion and audits on every
    concrete instantiation. -/

def vAccepted : List Term := vBodies.filter (fun b => Migrate.progOkOf (vDecl b))

def vDiffOk : Bool := vAccepted.all (fun b => vPool.all (fun cv => diffCheck (vDecl b) [cv]))

example : vDiffOk = true := by native_decide

/-! ## Non-exhaustive bodies are now all rejected (§9)

    With exhaustiveness checking, "accepted ⟹ concrete-safe" is unconditional
    over the generator's grammar: a symbolic match missing a constructor is
    rejected, so no accepted body can be concretely stuck on a missing branch. -/

-- CONV-SUBJECT: generator builds raw Terms by design
def vNonExhaustive : List Term :=
  (leafBodies.take 8).map (fun b => .matchE ⟨0, "v"⟩ none [.mk "Cons" [⟨2, "hd"⟩, ⟨3, "tl"⟩] b])   -- missing Nil
  ++ (leafBodies.take 8).map (fun b => .matchE ⟨0, "v"⟩ none [.mk "Nil" [] b])                       -- missing Cons

def vAllRejected : Bool := vNonExhaustive.all (fun b => !Migrate.progOkOf (vDecl b))

example : vAllRejected = true := by native_decide

/-! ## Telescope `(n : Nat) → Nat` (owned symbolic argument, value return) -/

-- CONV-SUBJECT: generator builds raw Terms by design
def n0 : Term := .var ⟨0, "n"⟩
def nLeaf : List Term := [tnat 0, tnat 1, n0, .var ⟨1, "m"⟩, .ctorApp "S" [.var ⟨1, "m"⟩]]

def nBodies : List Term :=
  [ n0, tnat 0, tnat 1, .ctorApp "S" [n0], .ctorApp "S" [tnat 0],
    .letIn ⟨1, "x"⟩ n0 (.ctorApp "S" [.var ⟨1, "x"⟩]),
    .letIn ⟨1, "x"⟩ (tnat 0) n0 ]
  -- exhaustive match on n
  ++ (nLeaf.take 5).flatMap fun b1 =>
       (nLeaf.take 5).map fun b2 =>
         .matchE ⟨0, "n"⟩ none [.mk "Z" [] b1, .mk "S" [⟨1, "m"⟩] b2]

def nDecl (body : Term) : FnDef :=
  decl{ fn f (n : Nat) -> Nat = %body }
def nPool : List Val := [ nat 0, nat 1, nat 2 ]

def nAccepted : List Term := nBodies.filter (fun b => Migrate.progOkOf (nDecl b))
def nDiffOk : Bool := nAccepted.all (fun b => nPool.all (fun cv => diffCheck (nDecl b) [cv]))

example : nDiffOk = true := by native_decide

/-! ## Telescope `(b : &mut Nat, c : Bool) → Unit` (a borrow and a bool) -/

-- CONV-SUBJECT: generator builds raw Terms by design
def bb : Term := .var ⟨0, "b"⟩
def bcLeaf : List Term :=
  [ .unit, .assign (.deref bb) (tnat 0) .unit, .assign (.deref bb) (tnat 1) .unit ]

def bcBodies : List Term :=
  bcLeaf
  ++ [ .letIn ⟨2, "tk"⟩ (.deref bb) (.assign (.deref bb) (tnat 0) .unit) ]   -- take + refill
  -- exhaustive match on c
  ++ (bcLeaf.take 5).flatMap fun b1 =>
       (bcLeaf.take 5).map fun b2 =>
         .matchE ⟨1, "c"⟩ none [.mk "True" [] b1, .mk "False" [] b2]

def bcDecl (body : Term) : FnDef :=
  decl{ fn f (b : &mut Nat, c : Bool) -> Unit = %body }
def bcPool : List (List Val) :=
  [ [nat 0, .ctor "True" []], [nat 0, .ctor "False" []],
    [nat 1, .ctor "True" []], [nat 1, .ctor "False" []] ]

def bcAccepted : List Term := bcBodies.filter (fun b => Migrate.progOkOf (bcDecl b))
def bcDiffOk : Bool := bcAccepted.all (fun b => bcPool.all (fun cv => diffCheck (bcDecl b) cv))

example : bcDiffOk = true := by native_decide

/-! ## The counts, asserted

    The header comment above quotes this harness's size — bodies generated,
    bodies accepted, concrete runs — and the paper's §6.1 quotes it in turn. A
    number in a comment is a claim nothing checks, and it duly went unchecked
    across two milestones that touched both the `match` form the generator emits
    and the take rule its bodies exercise. (It survived: the M23 currency pass
    re-measured all three telescopes by hand and found them exact.) Asserting
    them costs one `native_decide` each and turns the next drift into a red
    build instead of a stale sentence in a paper.

    These are DESCRIPTIVE, not normative: a legitimate change to the generator
    or to what the checker accepts should update these numbers and the header
    comment together. What they forbid is changing either silently. -/

example : (vBodies.length, vAccepted.length) = (91, 47) := by native_decide
example : (nBodies.length, nAccepted.length) = (32, 15) := by native_decide
example : (bcBodies.length, bcAccepted.length) = (13, 13) := by native_decide

-- …and the totals the header and the paper actually quote: 136 generated, 75
-- accepted, 238 concrete runs (each accepted body run against its telescope's pool).
example : vBodies.length + nBodies.length + bcBodies.length = 136 := by native_decide
example : vAccepted.length + nAccepted.length + bcAccepted.length = 75 := by native_decide
example : vAccepted.length * vPool.length + nAccepted.length * nPool.length
            + bcAccepted.length * bcPool.length = 238 := by native_decide

end Dllbc.Tests.S8Diff
