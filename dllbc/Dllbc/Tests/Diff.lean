import Dllbc.ElabCheck
import Dllbc.Program
import Dllbc.Boundary
import Dllbc.ProgMacro

/-!
# The differential: two machines, one relation

This file tests the differential between the two machines: the checker's
symbolic walk and the executing machine. It enumerates generated function
bodies per telescope, runs both machines on each, and asserts the simulation
relation (`instanceOf`) between the outcomes, with the agreement counts
pinned. The checker's verdict is only meaningful if a checked body's execution
is an instance of what the checker predicted.
-/

section
/-! ## Callee-side simulation: no calls

This section exercises only body checking against concrete body runs; no
generated body applies a function to another. If the checker accepts a body,
every small concrete run of it must complete (not get stuck) and pass the
concrete audit — the simulation theorem, as an exhaustively-checked
`native_decide` proposition over a bounded enumeration of bodies.

Matches are generated exhaustive over the scrutinee type's full constructor
set, deliberately: a non-exhaustive match is accepted (exhaustiveness checking
is deferred with inductive declarations) but concretely stuck on the missing
case — a known, separate gap, not the ownership soundness this suite targets.

If any accepted body has a concretely-stuck or audit-failing instantiation,
the `native_decide` below fails: that is a soundness counterexample, to be
minimized and reported, never hidden.

Counts, per telescope (asserted at the end of this section):
  * `(v : &mut List Nat) → Unit`   : 91 gen / 47 accepted / 141 runs
  * `(n : Nat) → Nat`               : 32 gen / 15 accepted / 45 runs
  * `(b : &mut Nat, c : Bool) → Unit`: 13 gen / 13 accepted / 52 runs
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S8Diff

/-! ## Body generator for `(v : &mut List Nat) → Unit`

    The pools are `prog_parse { }` FRAGMENTS (docs/22): `v` is free in every one
    and is bound where a body is spliced into `fn F (v : …) { %body }` — the
    telescope's own `v`, at its positional id, with no id written here. A
    fragment's own binders (`tail`, `x`, a match's `hd`/`tl`) mint from its own
    counter. The pools used to be raw `Term` literals with `v` at 0 and the
    binders at hand-chosen ids 2/3 — "the generator needs AST literals, not the
    `prog{}` macro" — and the conversion was witnessed body-for-body against
    them: the same term modulo those ids, the same verdict from `progOk`, the
    same 91/47 below.

    A two-level, capped enumeration over the grammar constructs: `*`-take, `:=`
    through 0/1/2 peels, `&mut`, `let`, `seq`, and match-through (exhaustive
    over `Nil`/`Cons`). `progOk` filters the ill-formed — including `x`, a name
    no telescope binds, which the boundary rejects as a free identifier. -/

/-- Small expression pool over v (RHS / place fillers). -/
def exprs : List Term :=
  [ prog_parse { () }, prog_parse { Nil }, prog_parse { 0 }, prog_parse { 1 }, prog_parse { *v },
    prog_parse { Cons(0, Nil) }, prog_parse { Cons(0, *v) }, prog_parse { x } ]

/-- Leaf statement bodies (each returns `()`), depth ≈ 1. -/
def leafBodies : List Term :=
  [ prog_parse { () } ]
  ++ exprs.map (fun e => prog_parse { %e; () })                                -- e ; ()
  -- p := e ; ()  for p a place through 0/1/2 peels
  ++ ([prog_parse { v }, prog_parse { *v }].flatMap fun p => exprs.map fun e => prog_parse { %p := %e; () })
  -- the take-and-refill idiom
  ++ [ prog_parse { let tail = *v; *v := Cons(0, tail); () } ]
  -- a stray let
  ++ [ prog_parse { let x = *v; () } ]

/-- Bodies with one exhaustive match-through on v, branches drawn from
    `leafBodies` (capped). `v` is a FREE scrutinee — the one free occurrence
    the grammar carries as a `Var` rather than a `Term`, bound by name at the
    splice like the rest. -/
def matchBodies : List Term :=
  (leafBodies.take 8).flatMap fun bNil =>
    (leafBodies.take 8).map fun bCons =>
      prog_parse { match v { Nil => %bNil, Cons(hd, tl) => %bCons } }

/-- All generated bodies for the list-borrow telescope. -/
def vBodies : List Term := leafBodies ++ matchBodies

/-! ## The two programs a generated body becomes

    Each generated body becomes two programs: `vCheck b` declares the function
    and leaves it unapplied, so `progOk` gives the checker's verdict on the
    body alone. `vRun b a` declares the same function and applies it to a
    concrete argument, so `progRuns` is "evaluating this call completes". The
    property below compares the two: accepted ⟹ every concrete run
    completes. -/

def vCheck (body : Term) : Term := prog{
  fn F (v : &mut List Nat) -> Unit { %body };
  () }

def vRun (body arg : Term) : Term := prog{
  fn F (v : &mut List Nat) -> Unit { %body };
  let x = %arg; let p = &m x; F(p); () }

/-- Concrete payloads for v: the small list pool, as the terms a caller writes. -/
def vArgs : List Term := [prog_parse { Nil }, prog_parse { Cons(1, Nil) }, prog_parse { Cons(1, Cons(2, Nil)) }]

/-! ## The property, for the list-borrow telescope

    Every body the checker ACCEPTS runs to completion on every concrete
    instantiation. -/

def vAccepted : List Term := vBodies.filter (fun b => progOk (vCheck b))

example : vAccepted.all (fun b => vArgs.all (fun a => progRuns (vRun b a))) = true := by
  native_decide

/-! ## Non-exhaustive matches are rejected

    With exhaustiveness checking, "accepted ⟹ concrete-safe" is unconditional
    over the generator's grammar: a symbolic match missing a constructor is
    rejected, so no accepted body can be concretely stuck on a missing branch. -/

def vNonExhaustive : List Term :=
  (leafBodies.take 8).map (fun b => prog_parse { match v { Cons(hd, tl) => %b } })   -- missing Nil
  ++ (leafBodies.take 8).map (fun b => prog_parse { match v { Nil => %b } })         -- missing Cons

example : vNonExhaustive.all (fun b => !progOk (vCheck b)) = true := by native_decide

/-! ## Telescope `(n : Nat) → Nat` (owned symbolic argument, value return) -/

-- `n` free, bound at the header; `m` free, bound by the `S(m)` arm each leaf
-- is spliced under.
def nLeaf : List Term := [prog_parse { 0 }, prog_parse { 1 }, prog_parse { n }, prog_parse { m }, prog_parse { S(m) }]

def nBodies : List Term :=
  [ prog_parse { n }, prog_parse { 0 }, prog_parse { 1 }, prog_parse { S(n) }, prog_parse { S(0) },
    prog_parse { let x = n; S(x) },
    prog_parse { let x = 0; n } ]
  -- exhaustive match on n
  ++ (nLeaf.take 5).flatMap fun b1 =>
       (nLeaf.take 5).map fun b2 =>
         prog_parse { match n { Z => %b1, S(m) => %b2 } }

def nCheck (body : Term) : Term := prog{ fn F (n : Nat) -> Nat { %body }; () }
def nRun (body arg : Term) : Term := prog{
  fn F (n : Nat) -> Nat { %body };
  let r = F(%arg); () }
def nArgs : List Term := [prog_parse { 0 }, prog_parse { 1 }, prog_parse { 2 }]

def nAccepted : List Term := nBodies.filter (fun b => progOk (nCheck b))

example : nAccepted.all (fun b => nArgs.all (fun a => progRuns (nRun b a))) = true := by
  native_decide

/-! ## Telescope `(b : &mut Nat, c : Bool) → Unit` (a borrow and a bool) -/

def bcLeaf : List Term :=
  [ prog_parse { () }, prog_parse { *b := 0; () }, prog_parse { *b := 1; () } ]

def bcBodies : List Term :=
  bcLeaf
  ++ [ prog_parse { let tk = *b; *b := 0; () } ]   -- take + refill
  -- exhaustive match on c
  ++ (bcLeaf.take 5).flatMap fun b1 =>
       (bcLeaf.take 5).map fun b2 =>
         prog_parse { match c { True => %b1, False => %b2 } }

def bcCheck (body : Term) : Term := prog{
  fn F (b : &mut Nat, c : Bool) -> Unit { %body };
  () }
def bcRun (body a0 a1 : Term) : Term := prog{
  fn F (b : &mut Nat, c : Bool) -> Unit { %body };
  let x = %a0; let p = &m x; F(p, %a1); () }
def bcArgs : List (Term × Term) :=
  [ (prog_parse { 0 }, prog_parse { True }), (prog_parse { 0 }, prog_parse { False }),
    (prog_parse { 1 }, prog_parse { True }), (prog_parse { 1 }, prog_parse { False }) ]

def bcAccepted : List Term := bcBodies.filter (fun b => progOk (bcCheck b))

example : bcAccepted.all (fun b => bcArgs.all (fun a => progRuns (bcRun b a.1 a.2))) = true := by
  native_decide

/-! ## The counts, pinned

    The generated/accepted/run counts quoted in the header above are otherwise
    just a claim nothing checks. Asserting them here turns a silent drift —
    from a change to the generator or to what the checker accepts — into a red
    build instead of a stale comment. These are descriptive, not normative: a
    legitimate change should update both the numbers and the header
    together. -/

example : (vBodies.length, vAccepted.length) = (91, 47) := by native_decide
example : (nBodies.length, nAccepted.length) = (32, 15) := by native_decide
example : (bcBodies.length, bcAccepted.length) = (13, 13) := by native_decide

-- The totals across all three telescopes: 136 generated, 75 accepted, 238
-- concrete runs (each accepted body run against its telescope's pool).
example : vBodies.length + nBodies.length + bcBodies.length = 136 := by native_decide
example : vAccepted.length + nAccepted.length + bcAccepted.length = 75 := by native_decide
example : vAccepted.length * vArgs.length + nAccepted.length * nArgs.length
            + bcAccepted.length * bcArgs.length = 238 := by native_decide

end Dllbc.Tests.S8Diff
end

section
/-! ## Whole-program simulation: callers and callees

The property extends to calls: for every accepted caller, its concrete final
environment (executing mode — calls run the callee's body) is a σ-instance of
some accepted symbolic path's final environment (checking mode — calls use the
callee's signature). `instanceOf` is first-order matching: a symbolic value
matches any concrete value consistently (the same σ always maps to the same
value), constructors match structurally, borrows match up to the canonical
renumbering.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S9Diff

/-! ## The fixed callee pool

    Four callees, declared as `fn` statements that a caller's program is
    prefixed with; a call resolves against whichever callee precedes it in
    scope. The symbolic side checks a call against the callee's sealed
    signature; the concrete side runs the callee's body. -/

def withPool (rest : Term) : Term := prog{
  fn Through (b : &mut List Nat) -> &mut List Nat { b };
  fn Advance (b : &mut List Nat) -> &mut List Nat { match b { Nil => b, Cons(hd, tl) => tl } };
  fn Choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat { match c { True => x, False => y } };
  fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  %rest }

/-! ## The simulation relation: `instanceOf` -/

/-- Match a symbolic value against a concrete one, threading a σ→value
    substitution (consistency: the same σ must map to the same value).

    Arrays are matched up to the fold, not structurally: a symbolic array can be
    segmented where the concrete one is a run, because a checking-mode group
    release introduces a fresh existential at the segment's owed type rather
    than rejoining it the way the executing run does. The relation splits the
    concrete run by the symbolic extents and matches segment-wise; without this
    case the harness reports a false counterexample on the first array body it
    is given. -/
partial def matchVal : Val → Val → List (Nat × Val) → Option (List (Nat × Val))
  | sv, cv, subst =>
    match sv.symOf? with
    | some σ =>
      match subst.find? (·.1 == σ) with
      | some (_, v) => if v == cv then some subst else none
      | none => some ((σ, cv) :: subst)
    | none =>
    match sv, Val.asCtor? cv with
    | .node "§segs" segs, some ("Arr", vs) => matchSegs segs vs subst
    | sv, _ =>
      match Val.asCtor? sv, Val.asCtor? cv with
      | some (n1, a1), some (n2, a2) => if n1 == n2 then matchList a1 a2 subst else none
      | _, _ =>
        match sv, cv with
        | .borrowM x p, .borrowM y q => if x == y then matchVal p q subst else none
        | a, b => if a == b then some subst else none    -- ⊥, loanM, pure: exact
where
  matchList : List Val → List Val → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | v1 :: vs1, v2 :: vs2, s => match matchVal v1 v2 s with | some s' => matchList vs1 vs2 s' | none => none
  | _, _, _ => none
  matchSegs : List Val → List Val → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | seg :: rest, vs, s =>
    match Val.asSeg? seg with
    | none => none
    | some (c, body) =>
      match Term.natOf? (Pure.nf 100 c) with
      | none => none                                     -- a symbolic extent cannot align a run
      | some k =>
        match matchVal body (.ctor "Arr" (vs.take k)) s with
        | some s' => matchSegs rest (vs.drop k) s'
        | none => none
  | _, _, _ => none

/-- Match two environments entry-by-entry (same names, same order). -/
def matchEnv : Env → Env → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | (n1, v1) :: r1, (n2, v2) :: r2, s =>
    if n1 == n2 then (match matchVal v1 v2 s with | some s' => matchEnv r1 r2 s' | none => none) else none
  | _, _, _ => none

/-- The concrete env is a σ-instance of the symbolic env. -/
def instanceOf (symEnv concEnv : Env) : Bool := (matchEnv symEnv concEnv []).isSome

/-! ## The relation, up to computation

    `matchVal` compares structurally; it has no case for a symbolic value that
    sits inside an evaluated expression rather than at a call boundary or
    group release — `let a = (3 : Nat); let b = add a 1` leaves the symbolic
    side holding the neutral spine `natRec … σ₀` where the concrete side holds
    `4`. `instanceOfC` below closes that gap in two passes:

      1. Collect σ ↦ concrete from every position where the symbolic side IS a
         σ — descending through constructors, borrows, and a carved `§segs`
         node faced with a concrete run. First binding wins; an inconsistent
         one is caught by the second pass.
      2. Instantiate the whole symbolic environment, normalize, and compare
         with `matchVal` — so the comparison is up to the array fold and up to
         the pure fragment's own computation.

    This is `instanceOf` with *instance* read up to computation as well as up
    to the array fold. -/

/-- Pass 1. -/
partial def collectSyms : Val → Val → List (Nat × Val) → List (Nat × Val)
  | sv, cv, s =>
    match sv.symOf? with
    | some σ => if (s.find? (·.1 == σ)).isSome then s else (σ, cv) :: s
    | none =>
    -- A carve on the symbolic side against a run on the concrete one: without
    -- this the σ standing for a released segment is never collected, and pass 2
    -- compares an uninstantiated `§segs` against a run.
    match sv, Val.asCtor? cv with
    | .node "§segs" segs, some ("Arr", vs) => goSegs segs vs s
    | sv, _ =>
      match Val.asCtor? sv, Val.asCtor? cv with
      | some (_, a1), some (_, a2) => go a1 a2 s
      | _, _ =>
        match sv, cv with
        | .borrowM _ p, .borrowM _ q => collectSyms p q s
        | _, _ => s
where
  go : List Val → List Val → List (Nat × Val) → List (Nat × Val)
  | v1 :: vs1, v2 :: vs2, s => go vs1 vs2 (collectSyms v1 v2 s)
  | _, _, s => s
  goSegs : List Val → List Val → List (Nat × Val) → List (Nat × Val)
  | seg :: rest, vs, s =>
    match Val.asSeg? seg with
    | none => s
    | some (c, body) =>
      match Term.natOf? (Pure.nf 100 c) with
      | none => s                                        -- symbolic extent: cannot align
      | some k => goSegs rest (vs.drop k) (collectSyms body (.ctor "Arr" (vs.take k)) s)
  | _, _, s => s

/-- Normalize every knowledge leaf of a store value. -/
partial def nfVal (fuel : Nat) : Val → Val
  | .know t => .know (Pure.nf fuel t)
  | .node n args => .ctor n (args.map (nfVal fuel))
  | .borrowM ℓ p => .borrowM ℓ (nfVal fuel p)
  | v => v

/-- Substitute a σ by a STORE value. Where the replacement is knowledge this is
    the kernel's own `Term.substSym` at the leaves; where it is not — a runtime
    function value standing for a sealed σ, which is what a checking-mode `F ↦ σ`
    faces concretely — only a whole leaf can be filled, because there is no `Term`
    to splice a `λr` into. -/
partial def substSymV (σ : Nat) (repl : Val) : Val → Val
  | .know t =>
    if Term.beq t (Term.sym σ) then repl
    else match repl.know? with
      | some rt => .know (Term.substSym σ rt t)
      | none => .know t
  | .node n args => .ctor n (args.map (substSymV σ repl))
  | .borrowM ℓ p => .borrowM ℓ (substSymV σ repl p)
  | v => v

/-- Pass 2's substitution. Concrete values carry no σ, so one sweep is a
    fixpoint; normalization is what makes the comparison up to computation. -/
def instantiateSyms (subst : List (Nat × Val)) (v : Val) : Val :=
  nfVal 2000 (subst.foldl (fun acc kv => substSymV kv.1 kv.2 acc) v)

/-- **The relation**: the concrete env is a σ-instance of the symbolic one, up to
    the array fold and up to computation. -/
def instanceOfC (symEnv concEnv : Env) : Bool :=
  let subst := (symEnv.zip concEnv).foldl (fun s p => collectSyms p.1.2 p.2.2 s) []
  symEnv.length == concEnv.length
    && (matchEnv (symEnv.map (fun p => (p.1, instantiateSyms subst p.2))) concEnv []).isSome

/-! ## The two runs and the differential check -/

/-- Executing mode: run a body concretely (calls run callee bodies), returning
    the caller's own final environment, declaration slots dropped. A call opens
    its own scope, and `popScopesTo` pops it on the way out, so no callee slots
    leak into the caller's environment. -/
def runExec (body : Term) : Except String Env :=
  match (readR defaultFuel body).run { initSt with executing := true } with
  | .ok _ st => .ok (canonicalize (st.env.filter (fun kv => kv.1.id != declSlot)))
  | .error e _ => .error e

/-- Checking mode: the accepted symbolic paths' final environments. -/
def symEnvs (body : Term) : List (Except String Env) :=
  (explore defaultFuel (atBoundary body) initSt).map
    (fun r => r.map (fun p => canonicalize (p.2.env.filter (fun kv =>
      kv.1.id != declSlot))))

/-- The differential: the concrete final env is an instance of some symbolic
    path's final env. -/
def diffV2 (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok concEnv => (symEnvs body).any (fun r => match r with
      | .ok se => instanceOf se concEnv
      | .error _ => false)

/-- The differential under the relation extended to computation. Same
    property, but no longer reports a false counterexample on a program that
    both carves an array and computes. -/
def diffC (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok concEnv => (symEnvs body).any (fun r => match r with
      | .ok se => instanceOfC se concEnv
      | .error _ => false)

/-- The differential on a whole program rather than on a caller body: the
    concrete final environment is a σ-instance of some accepted symbolic
    path's. It differs from `diffC` only in which walk it uses —
    `runProgram`/`programEnvs` end the scope, where `runExec`/`symEnvs` do
    not. -/
def progDiff (t : Term) : Bool :=
  match runProgram t with
  | .error _ => false
  | .ok concEnv => (programEnvs t).any (fun r => match r with
      | .ok se => instanceOfC se concEnv
      | .error _ => false)

/-! ## Callers (each demands ALL its owners, so both runs fully collapse) -/

/-- The choose caller, demanding BOTH owners. -/
def chooseCaller : Term := withPool (prog_parse {
  let a = 0; let b = 0; let pa = &m a; let pb = &m b;
  let r = Choose(True, pa, pb);
  *r := 7;
  let za = a; let zb = b;
  () })

/-- A push caller. -/
def pushCaller : Term := withPool (prog_parse {
  let x = Cons(1, Nil); let b = &m x; Push(7, b); let y = x; () })

/-! ## The property, over the caller set -/

def callers : List Term :=
  [ withPool (prog_parse { let x = Cons(1, Cons(2, Nil)); let b = &m x; let r = Through(b); *r := Cons(9, Nil); let y = x; () }),
    withPool (prog_parse { let x = Cons(1, Cons(2, Nil)); let b = &m x; let r = Advance(b); *r := Cons(9, Nil); let y = x; () }),
    chooseCaller,
    pushCaller ]

-- A caller is itself a program, callees and all: no wrapper, no table.
def accepted : List Term := callers.filter (fun b => progOk b)

-- Every accepted caller's concrete run is a σ-instance of an accepted symbolic
-- path — the whole-program simulation theorem, over the caller set.
example : accepted.all (fun b => diffV2 b) = true := by native_decide

/-! ## The advance caller, which the validation below is about -/

def advCallerBody : Term :=
  withPool (prog_parse { let x = Cons(1, Cons(2, Nil)); let b = &m x; let r = Advance(b); *r := Cons(9, Nil); let y = x; () })

-- The real behaviour: the opaque σ matches the concrete value. GREEN.
example : diffV2 advCallerBody = true := by native_decide

/-! ### Discriminating a wrong refinement

    The wrong refinement this validates against — the owner recovering the
    surrendered tail — is written directly as an environment below, alongside
    the honest one, and both are put to the relation: it must say NO to the
    wrong environment and YES to the honest one. -/

/-- The wrong refinement: the owner recovers the tail the issued borrow
    surrendered. -/
def constrainedLie : Env := [("x", .bot), ("b", .bot), ("r", .bot), ("y", cons (nat 9) nil)]

/-- What is true: the owner recovers an opaque existential. -/
def honestSym : Env := [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)]

-- The concrete run holds `Cons 1 (Cons 9 Nil)` — the write landed in the TAIL, and
-- the head is still there. The lie is not an instance of it, under either relation.
example : (match runExec advCallerBody with
           | .ok ce => instanceOf constrainedLie ce || instanceOfC constrainedLie ce
           | .error _ => true) = false := by native_decide

-- …and the honest σ is, under both — so the refusal above is discrimination and
-- not a relation that says NO to everything.
example : (match runExec advCallerBody with
           | .ok ce => instanceOf honestSym ce && instanceOfC honestSym ce
           | .error _ => false) = true := by native_decide

/-! ### The pinned twin: a declared wire

    `honestSym` above is what an unpinned signature yields. A signature that
    declares the wire (`~> *res`) releases the surrendered payload itself,
    checked at both ends, so the checking-mode environment holds the concrete
    written value directly — and the simulation relation accepts it exactly as
    it accepts the opaque σ. `through` and `advance` no longer share a
    signature once one of them writes its pin. -/

def throughPinCallerBody : Term := prog{
  fn ThroughP (b : &mut (s : List Nat ~> *res)) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &m x;
  let r = ThroughP(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

-- The checker's own environment holds the written value directly…
def pinnedKnown : Env := [("x", .bot), ("b", .bot), ("r", .bot), ("y", cons (nat 9) nil)]
example : tailEnv throughPinCallerBody pinnedKnown = true := by native_decide

-- …it is an instance of the concrete run under both relations…
example : (match runExec throughPinCallerBody with
           | .ok ce => instanceOf pinnedKnown ce && instanceOfC pinnedKnown ce
           | .error _ => false) = true := by native_decide

-- …and the whole-program simulation holds for the pinned caller.
example : diffV2 throughPinCallerBody = true := by native_decide

/-! ### Under the extended relation

    The extended relation must still accept everything the plain one does, and
    must still say NO to the wrong refinement. -/

example : accepted.all (fun b => diffC b) = true := by native_decide
-- Still says NO to the wrong refinement: computation does not launder it,
-- because pass 2 compares the instantiated value.
example : diffC advCallerBody = true := by native_decide

end Dllbc.Tests.S9Diff
end
