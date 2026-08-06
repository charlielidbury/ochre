import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S23Direct
import Dllbc.Tests.S25ArrSort

/-!
# §26 (M26-E) — programs are terms

`combining-fns.md` §8: **a program is an arbitrary term, and running it is
⇒-evaluating it.** A module is a let-chain — transparent lets, sealed lets, a
tail — and checking it is the symbolic ⇒-walk of the same term. `FnDef` is what
this deletes.

Three claims are tested here, and the third is the one that needed a kernel rule:

  1. **The walk is the check.** `checkProgram` is `explore` plus the audit of each
     path's result; each sealed `let` fires its audit once, at its own node, in
     program order. Nothing new — §5 put the audit at the node in M26-C, and a
     let-chain is what puts the nodes in order.
  2. **Scope is the call table.** A callee is a binding lexically above the call,
     and the surface has resolved `f(…)` that way since M26-A. So a program is
     checked against NO table, and a forward reference is unwritable rather than
     rejected: a let-chain cannot reference downward.
  3. **§7 cost 2's "and globals" acquires a referent.** Until now a runtime λ's
     body had to be closed, because its callees lived in the table and were
     reached by name. With the table gone they are variables, so a body's free
     variables are its callees — admitted when they name a FUNCTION bound above,
     refused otherwise (capture stays deferred, constraint 5). Both machines
     needed it: the checking side seeds them through frame isolation, the
     executing side keeps their ids out of the frame shift.

**Both machines, every program.** Per §12 decision 7 and constraint 6, each
program below is CHECKED and RUN, and the differential — the merged relation of
M26-C — is asserted on it. A checking-side claim about a program that was never
run is exactly what the polarity doctrine forbids.
-/

open Dllbc
open Dllbc.StdLemmas (le_trans le_refl id_congr append len Le)

namespace Dllbc.Tests.S26Prog

/-! ## Helpers

    `progOk`/`progRejects`/`runProgram` are `Program.lean`'s. The differential is
    S9Diff's merged relation, applied to a program instead of to a `FnDef` body —
    which is the same thing now, and the reason `diffC` needed no new definition:
    it already took a TERM. -/

/-- The concrete final Ω is a σ-instance of some accepted symbolic path's. -/
def progDiff (t : Term) (table : List FnDef := []) : Bool :=
  match runProgram t table with
  | .error _ => false
  | .ok concEnv => (programEnvs t table).any (fun r => match r with
      | .ok se => Tests.S9Diff.instanceOfC se concEnv
      | .error _ => false)

/-- The walk WITHOUT the end-of-scope demand — for showing that `endScope` is not
    vacuous (it is the difference between a parked loan and a released value). -/
def rawEnvs (t : Term) : List (Except String Env) :=
  (explore defaultFuel (pushContinuations t) initSt).map
    (fun r => r.map (fun p => canonicalize (p.2.env.filter (·.1.id < 10000))))

/-! ## §A. A program is a term

    The smallest complete statement of §8: no `FnDef`, no telescope, no return
    type to declare — a let-chain and a tail, checked by one walk and run by the
    other. -/

-- A1. Transparent lets and a tail. The tail is checked in the ACCUMULATED Ω,
-- which is what makes `retType` a real demand site rather than decoration.
def a1 : Term := prog{ let x = 3; let y = S(x); y }
example : progOk a1 (.const "Nat") = true := by native_decide
example : progRejects a1 "does not have return type" (.const "Bool") = true := by native_decide
-- `x` survives its own use: a `Nat` is index-kind, so §2.1's copy-on-read leaves
-- the owner intact where data proper would be moved out.
example : progRunsTo a1 [("x", Val.nat 3), ("y", Val.nat 4)] = true := by native_decide
example : progDiff a1 = true := by native_decide

-- A2. A sealed `let` is a definition, and the next binding calls it. Two things
-- at once: the seal's audit fires at its own node, and the call resolves to a
-- BINDING rather than to a table entry.
def a2 : Term := prog{
  let f = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let g = (λ(y : Nat){ f(y) } : Π (y : Nat) → Nat);
  let r = g(3);
  r }
example : progOk a2 (.const "Nat") = true := by native_decide
example : progDiff a2 = true := by native_decide
-- The claim that it was really the seal that made `f` callable: the same program
-- with `f` bound to a NON-function is refused, and the refusal names the capture.
def a2cap : Term := prog{
  let f = 3;
  let g = (λ(y : Nat){ let z = f; y } : Π (y : Nat) → Nat);
  () }
example : progRejects a2cap "not a function" = true := by native_decide

-- A3. A sealed function that MUTATES through a borrow, applied to a local. The
-- program owns the list, lends it, and gets it back — the whole borrow story with
-- no declaration anywhere in it.
def push : Term := prog{
  let push = (λ(e : Nat, v : &mut (s : List Nat ~> List Nat)){
                    let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit);
  let l = Cons(1, Nil);
  let r = push(7, &mut l);
  () }
example : progOk push = true := by native_decide
-- The list really was mutated through the borrow, and the borrow really did come
-- back: `l` holds the pushed list, not a hole and not a parked loan.
example : (match runProgram push with
           | .ok env => (env.lookup "l" == some (Val.cons (Val.nat 7) (Val.cons (Val.nat 1) Val.nil)))
           | .error _ => false) = true := by native_decide
example : progDiff push = true := by native_decide

/-! ## §B. Each sealed `let` fires its audit ONCE, at its own node, in program order

    §8's sentence about checking, taken apart into the three things it claims. The
    audit is at the BINDING (not at a use), it happens whether or not there is a
    use, and the order the lets are written is the order the audits run. -/

-- B1. A sealed function that does not inhabit its ascription is refused AT ITS
-- OWN `let`, with nothing downstream of it — the binding is the demand site,
-- which is what "the audit is the checking of the seal" means (§5).
def b1 : Term := prog{ let f = (λ(x : Nat){ x } : Π (x : Nat) → Bool); () }
example : progRejects b1 "does not have return type (Bool)" = true := by native_decide

/-- ### B2. The vacuous twin, kept beside it

    An UNSEALED λ with the same nonsense body is ACCEPTED, because nothing demands
    it: `readR` forms the value and never looks inside. This is phase A's
    per-DEMAND-SITE finding, and it is the trap a reader of B1 would otherwise
    fall into — "binding a bad function is caught" is true only of a SEALED
    binding. The live twin below is what makes it a real difference: call it, and
    the demand arrives. -/
def b2vac : Term := prog{ let g = λ(x : Nat){ True }; () }
def b2live : Term := prog{ let g = λ(x : Nat){ True }; let r = g(1); r }
example : progOk b2vac = true := by native_decide
example : progRejects b2live "does not have return type (Nat)" (.const "Nat") = true := by native_decide

-- B3. **Program order**, pinned the only way it can be: two lies, and the one
-- that is reported is the FIRST. (Both messages have the same shape, so the
-- needles are the types, which differ.)
def b3 : Term := prog{
  let f = (λ(x : Nat){ x } : Π (x : Nat) → Bool);
  let g = (λ(x : Nat){ True } : Π (x : Nat) → Unit);
  () }
example : progRejects b3 "does not have return type (Bool)" = true := by native_decide
example : progRejects b3 "does not have return type (Unit)" = false := by native_decide

/-! ## §C. Scope is the call table

    "A caller sees exactly the bindings lexically above it, so the checker's
    callee-resolution table and its assembly disappear." Every program in this
    file is checked against an EMPTY table (`checkProgram`'s default), which is
    the positive half of that claim. Here is the rest. -/

/-- ### C1. No forward references — unwritable, not rejected

    A let-chain cannot reference downward, so `h` in `g`'s body does not resolve
    to the `h` bound below: it resolves to nothing, and falls through to the
    (empty) table. Nothing implements this rule — it is what scope IS, which is
    why §8 can say mutual recursion "becomes unwritable" rather than "stays
    rejected". Note WHERE it is caught: at `g`'s own seal, because the audit is at
    the binding, so the diagnosis does not wait for a call. -/
def c1 : Term := prog{
  let g = (λ(y : Nat){ h(y) } : Π (y : Nat) → Nat);
  let h = (λ (x : Nat). x : Π (x : Nat) → Nat);
  () }
example : progRejects c1 "unknown function 'h'" = true := by native_decide
-- …and the same program with the two bindings SWAPPED is accepted, so the
-- rejection is about the order and not about the pair.
def c1ok : Term := prog{
  let h = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let g = (λ(y : Nat){ h(y) } : Π (y : Nat) → Nat);
  let r = g(3);
  r }
example : progOk c1ok (.const "Nat") = true := by native_decide
example : progDiff c1ok = true := by native_decide

/-! ### C2. The deliberately-wrong table becomes a different let-prefix

    The old suite guarded caller-side reasoning by checking a caller against a
    table entry whose signature was a lie. There is no table to lie in now, so the
    same test becomes **one program under two signatures**: the callee's body and
    the caller that uses it are identical and honest in both, and what differs is
    the type the body is SEALED at. That is §5 point 4 with nothing left to
    interpret — what the caller keeps is what the programmer wrote — and it is a
    sharper test than the old one, because the lying version is a program that
    itself checks. -/

/-- The whole program, parameterised by the ONE thing the pair differs in. Body
    and caller are shared by construction rather than by two copies agreeing, so
    the difference the test measures is the only difference there is. -/
def c2under (sig : Term) : Term := prog{
  let f = (λ(n : Nat){ Pair(n, Refl) } : %sig);
  let r = f(3);
  r }
/-- The retType the program is demanded at: the equation the caller wants. -/
def c2demand : Term := pure{ Σ (m : Nat) → Id Nat m 3 }

/-- A — the signature CARRIES the equation. -/
def c2keeps : Term := c2under (pure{ Π (n : Nat) → Σ (m : Nat) → Id Nat m n })
/-- B — the same body, sealed at a type that FORGETS it (true, and useless). It
    checks: the lie is not in the callee, it is in what the callee promises. -/
def c2forgets : Term := c2under (pure{ Π (n : Nat) → Σ (m : Nat) → Id Nat m m })

example : progOk c2keeps c2demand = true := by native_decide
example : progRejects c2forgets "does not have return type" c2demand = true := by native_decide
-- Not vacuous: the forgetting prefix is a program that checks on ITS OWN terms —
-- at the weaker demand its callee's signature does support. So the rejection
-- above is about what was kept across the seal, and not about the program being
-- broken.
example : progOk c2forgets (pure{ Σ (m : Nat) → Id Nat m m }) = true := by native_decide
-- The keeping prefix does NOT also satisfy the weaker demand, which is worth a
-- line because it is the honest reading of "what you keep is what you write":
-- there is no subsumption here, only conversion — a σ has the type it was minted
-- at, and `Id Nat m 3` and `Id Nat m m` are different types even though the first
-- is the more informative claim about this particular callee.
example : progOk c2keeps (pure{ Σ (m : Nat) → Id Nat m m }) = false := by native_decide

/-! ## §D. Globals: the one kernel rule this phase needed

    §7 cost 2 admits "closed" function values — "arms reference only their own
    binders **and globals**" — and until now the second half was empty, because
    the callees lived in the table. §8 puts them in scope, so a body's free
    variables ARE its callees, and the closedness premise had to learn the
    difference between naming a function above you and capturing your
    environment. `admitGlobals` is that line, and it is drawn at what the body can
    DO with the binding: a function is CALLED (a place read — the callee is
    located, never moved), while data is moved, borrowed or written.

    Both machines needed something, and neither needed the other's: the checking
    side seeds the admitted bindings through frame isolation (a sealed body's Ω is
    otherwise fresh), the executing side keeps their ids out of the frame shift
    (`shiftVarsK`) so a reference to `#901` still finds `#901` inside a frame. -/

-- D1. Two frames deep: `h` calls `g` calls `f`, each a binding above it. This is
-- what says the keep set survives NESTING — the innermost body is entered through
-- two frame shifts, and both globals are still where the program put them.
def d1 : Term := prog{
  let f = (λ (x : Nat). S(x) : Π (x : Nat) → Nat);
  let g = (λ(y : Nat){ f(f(y)) } : Π (y : Nat) → Nat);
  let h = (λ(z : Nat){ g(g(z)) } : Π (z : Nat) → Nat);
  let r = h(0);
  r }
example : progOk d1 (.const "Nat") = true := by native_decide
-- The executing machine agrees, and on the VALUE: four applications of successor.
example : (match runProgram d1 with
           | .ok env => env.lookup "r" == some (Val.nat 4)
           | .error _ => false) = true := by native_decide
example : progDiff d1 = true := by native_decide

/-- ### D2. What is still refused, per capture kind

    Constraint 5 defers environment capture wholesale, and it stays deferred:
    admitting functions is not admitting environments. Each refusal is paired with
    the same program passing the thing IN, so the rejection is about the capture
    and not about the program. -/

-- D2a. DATA. (M26-C's a3bad, now with the message that says which of the two
-- things went wrong — it names a binding in scope, and that binding is not a
-- function.)
def d2data : Term := prog{
  let n = 3;
  let g = (λ(a : Nat){ let z = n; a } : Π (a : Nat) → Nat);
  () }
def d2dataOk : Term := prog{
  let n = 3;
  let g = (λ(a : Nat, m : Nat){ let z = m; a } : Π (a : Nat) → Π (m : Nat) → Nat);
  let r = g(1, n);
  r }
example : progRejects d2data "not a function" = true := by native_decide
example : progOk d2dataOk (.const "Nat") = true := by native_decide

-- D2b. A BORROW — the case constraint 5 is really about, since a captured borrow
-- is a suspended loan with no scope to end it in.
def d2borrow : Term := prog{
  let l = Cons(1, Nil);
  let b = &mut l;
  let g = (λ(a : Nat){ *b := Nil; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d2borrow "not a function" = true := by native_decide

-- D2c. A free variable that names NOTHING is a different rejection with a
-- different message, and it is the one §8 explains: a let-chain cannot reference
-- downward. (Reached here through a `.callV`-free body, so it is the variable
-- rule and not the call rule doing the work — c1 covers the call side.)
def d2free : Term :=
  .letIn ⟨0, "g"⟩ (.seal (.lamR [(⟨1, "a"⟩, .const "Nat")] (.letIn ⟨2, "z"⟩ (.var ⟨9, "nope"⟩) (.var ⟨1, "a"⟩)))
    (pure{ Π (a : Nat) → Nat })) .unit
example : progRejects d2free "not bound anywhere above it" = true := by native_decide

-- D3. A sealed PROOF is not a global either, and that is deliberate rather than
-- an oversight: §5's `Qed` binding is a value, and a body that wants it should
-- take it as a capital parameter (which is exactly what §6 built). Recorded as a
-- limitation with its route beside it, not as a defect.
def d3 : Term := prog{
  let cert = (le_refl 3 : Le 3 3);
  let g = (λ(a : Nat){ let z = cert; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d3 "not a function" = true := by native_decide

-- D3b. And the capital form of the same binding is refused EARLIER and for a
-- different reason, which is §6's own parenthesis becoming a rejection: `let X =
-- e` reads `e` under ⇝, and the seal is a ⇒-form because minting needs an event.
-- So "sealed" and "comptime-bound" are mutually exclusive, and a reader who
-- expects `let Cert = (… : …)` to be the `Qed` form is told which half to drop.
def d3cap : Term := prog{ let C = (le_refl 3 : Le 3 3); () }
example : progRejects d3cap "not in the comptime fragment" = true := by native_decide

/-! ## §E. The end of a program is a demand on everything it still holds

    A program that lends a local and never looks at it again leaves the loan
    parked: the checking machine releases a group when something demands it, and
    nothing does. The executing machine releases a frame's loans on the way out.
    Without `endScope` the two would end in visibly different Ωs on an ordinary
    program — so this is not tidiness, it is the differential's precondition, and
    it is shown as a difference rather than asserted. -/

-- E1. The raw walk leaves the loan parked…
example : (rawEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide
-- …and the ended one has released it into a σ, which the concrete list then
-- instantiates (that is why §A's `progDiff push` is green).
example : (programEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .sym _ => true | _ => false)
    | .error _ => false) = true := by native_decide

/-! ## §F. The flagship — RETIRED HERE (M28 D3), because the source is fuel-threaded

    M23's in-place quicksort — `Sorted` and the permutation count equation over the
    exit snapshot, no declared `back` anywhere in the call tree — assembled as three
    sealed lets and a tail, checked against no table and run to a sorted list. That
    was this milestone's acceptance test, and it needed a MIGRATION to exist:
    `partition` and `append_back` were written with `[v]`, which has no recursor
    form, so this section fuel-threaded `append_back` by hand, retargeted
    quicksort's two call sites with a term-rewriting pass (`toP`/`migrate`), and
    assembled `[partitionF, appendBackF, quicksortP]` with `progOf`.

    **The migration has been adopted at the source** (M28 D3). `S23Direct` stage
    (vi) is that cohort, written once as one `fn` chain in the surface — the
    fuel-threaded `partition` that lived in `S26Fn`, the `append_backF` that lived
    here, and the quicksort the rewriter used to produce — so there is no rewrite
    left to run and no second definition to keep in step.

    Everything this section asserted is asserted there, on the same program:

      * the headline (`progOk`), the RUN (`runQs` on seven inputs, against Lean's
        own sort), and the twin battery, which grew from three to six on the way.
      * `toP`'s own regression — that the rewrite really did change both call sites
        — was a `calleeNames` probe of a term-rewriter's output, and it retires with
        the rewriter rather than with a claim. The call sites are now written, not
        computed: `partition(f2, &mut *v, x, hfuel)` and `append_back(lv, &mut *v,
        w, le_refl lv)` are lines of the source.

    What does NOT move is the DIFFERENTIAL, which is this file's own business and
    the one thing §F asserted that is about programs rather than about quicksort:
    the two machines agree on the whole final Ω of the largest program in the
    corpus. Kept below, on `S23Direct`'s chain. -/

/-- The two machines agree on the whole final Ω of the flagship — the differential
    of M26-C, run on a program rather than on a `FnDef` body, at the largest scale
    the corpus has. -/
example : progDiff (Tests.S23Direct.qsRun [3, 1, 2]) = true := by native_decide

/-! ## §G. The ARRAY flagship, as a program term — and it needed no source change

    `quicksortA` is the array era's in-place scan: it carves, swaps through element
    borrows, and returns an index. It shares no code with §F's list quicksort —
    not the program, not the predicates, not the partition, not the container.

    It goes through unchanged, and that is the finding: the array cohort was
    ALREADY fuel-threaded (`splitA [fuel]`, `quicksortA [fuel]`, `partitionA` not
    recursive at all), so §12 decision 8 costs this lane nothing. R12's carve
    machinery — the one part of the corpus that leans hardest on the call
    boundary's re-mint — transfers to the seal without a single adjustment, which
    is the strongest available evidence that §5's opacity and §6.1's call rule
    really are the same mechanism reached two ways. -/

def arrCohort : List FnDef :=
  [Tests.S25ArrSort.splitA, Tests.S25ArrSort.partitionA, Tests.S25ArrSort.quicksortA]

def arrProg (tail : Term) : Except String Term := FnMacro.progOf arrCohort tail

/-- The array flagship checks as a program, against no table. -/
example : (match arrProg .unit with
           | .ok t => progOk t
           | .error _ => false) = true := by native_decide

/-- …and runs, in place, on a real array. `qsCallerA` is S25's own caller term,
    handed over unchanged — `progOf` retargets its `.call`s, because the tail is in
    the accumulated scope like everything else. -/
def runQsAP (l : List Nat) : Option (List Nat) :=
  match arrProg (Tests.S25ArrSort.qsCallerA l) with
  | .error _ => none
  | .ok t => match runProgram t with
             | .ok env => (env.lookup "y").bind Tests.S25ArrSort.arrOfV
             | .error _ => none

example : runQsAP [3, 1, 2] == some [1, 2, 3] := by native_decide
example : runQsAP [9, 8, 7, 6, 5, 4, 3, 2, 1] == some [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  native_decide

/-! ### G2. Coverage preserved on the array side too

    S25 guards its three functions with seven twins — two length lies, two
    invariant lies, a count lie, and the two quicksort conjuncts. Each is dropped
    into the cohort in place of the function it lies about (the twins keep their
    subjects' names, so this is a substitution and not a rewrite) and the program
    is refused. -/

/-- Replace the cohort member with the twin's name. -/
def sub (twin : FnDef) : List FnDef :=
  arrCohort.map (fun d => if d.name == twin.name then twin else d)

def arrTwins : List FnDef :=
  [Tests.S25ArrSort.splitALieLen, Tests.S25ArrSort.splitALieSp,
   Tests.S25ArrSort.splitALieCount, Tests.S25ArrSort.partALieLen,
   Tests.S25ArrSort.partALiePart, Tests.S25ArrSort.qsALieSorted,
   Tests.S25ArrSort.qsALieCount]

example : arrTwins.all (fun tw =>
    match FnMacro.progOf (sub tw) .unit with
    | .ok t => !progOk t
    | .error _ => false) = true := by native_decide
-- Not vacuous: the substitution mechanism itself accepts the honest cohort.
example : (match FnMacro.progOf (sub Tests.S25ArrSort.splitA) .unit with
           | .ok t => progOk t
           | .error _ => false) = true := by native_decide

/-! ### G3. THE CROSS-DIFFERENTIAL, re-run in program-term form

    S25's (vi.c): two implementations written against the same postcondition,
    sharing no code, compared elementwise against a trusted sort — the control that
    catches a wrong SHARED reading of the spec, which neither type checker would
    see. Both sides are now programs rather than declaration tables, and the
    conjunction is one expression, so a two-way agreement on a wrong answer still
    goes red. -/

def runQsLP (l : List Nat) : Option (List Nat) :=
  match runProgram (Tests.S23Direct.qsRun l) with
  | .ok env => (env.lookup "y").bind (Tests.S25ArrSort.listOfV 2000)
  | .error _ => none

def crossP (l : List Nat) : Bool :=
  match runQsLP l, runQsAP l with
  | some a, some b => a == b && a == l.mergeSort (fun a b => a <= b)
  | _, _ => false

example : (([[], [1], [2,1], [3,1,2], [1,2,3], [3,2,1], [5,5,5], [4,1,3,2,5],
             [3,1,4,1,5,9,2], [2,2,1,1], [7,3,7,3,7]] : List (List Nat)).all crossP)
    = true := by native_decide

/-! ## §H. Both dispatch surfaces, for the rules this phase added

    The standing warning (M26-C §K, earned when phase B's fence was DEAD until
    duplicated at the driver): `explore` is a second dispatch surface, and a
    statement-position `match` or `let` never reaches `readR`'s own cases. Every
    rule here has to be exercised where `pushContinuations` sends a real body —
    INSIDE a branch of a symbolic match — and not only at the top level.

    The rules this phase added are `admitGlobals` (at `.lamR` and at the seal) and
    `endScope`. They are reached by construction rather than by duplication, and
    the reason is worth stating because "no duplication needed" is exactly what a
    phantom rule looks like from the inside: a runtime λ and a seal are always
    EXPRESSIONS — a let's right-hand side, an argument, a tail — and the driver
    reaches every expression through `.letIn`'s right-hand side, `.seq`'s
    expression, and the final-expression fall-through. `endScope` runs per path
    after the walk, so a forked path gets its own.

    Each is placed inside a branch with a NEGATIVE TWIN at the same position, so
    the branch is not merely skipped. -/

/-- A symbolic scrutinee at the top level of a program: an abstract call's result
    is a σ, and matching on one is what forks the driver's paths. -/
def hSplit (inZ inS : Term) : Term :=
  .letIn ⟨0, "f"⟩ (prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) })
    (.letIn ⟨1, "n"⟩ (.callV ⟨0, "f"⟩ [pure{ 3 }])
      (.matchE ⟨1, "n"⟩ none [Branch.mk "Z" [] inZ, Branch.mk "S" [⟨2, "k"⟩] inS]))

-- H0. The split is real: two paths, not one.
example : (programEnvs (hSplit .unit .unit)).length == 2 := by native_decide

-- H1. A GLOBAL-REFERENCING runtime λ, formed and called inside a branch. `f` is
-- the program-level binding two `let`s above; the branch is a body, so this is
-- `admitGlobals` reached through the driver.
def hGlobal (bad : Bool) : Term :=
  hSplit .unit
    (.letIn ⟨3, "g"⟩ (.lamR [(⟨4, "y"⟩, .const "Nat")] (.callV ⟨0, "f"⟩ [.var ⟨4, "y"⟩]))
      (.letIn ⟨5, "r"⟩ (.callV ⟨3, "g"⟩ [.var ⟨2, "k"⟩])
        (if bad then pure{ True } else .unit)))
example : progOk (hGlobal false) = true := by native_decide
-- The negative twin at the SAME position: the branch is entered and its result
-- audited, so the accept above is not the branch being skipped.
example : progRejects (hGlobal true) "does not have return type" = true := by native_decide

-- H2. A CAPTURE inside a branch is refused there too — the fence is not weaker on
-- a path than at the top level. (`k` is the branch's own binder, a `Nat`, so this
-- is data capture: the same rejection §D2a pins, reached the other way.)
def hCapture : Term :=
  hSplit .unit
    (.letIn ⟨3, "g"⟩ (.lamR [(⟨4, "y"⟩, .const "Nat")] (.letIn ⟨6, "z"⟩ (.var ⟨2, "k"⟩) (.var ⟨4, "y"⟩)))
      .unit)
example : progRejects hCapture "not a function" = true := by native_decide

-- H3. A SEAL inside a branch fires its audit there, in that branch's Ω.
def hSeal (bad : Bool) : Term :=
  hSplit .unit
    (.letIn ⟨3, "s"⟩
      (.seal (.lamR [(⟨4, "y"⟩, .const "Nat")] (.var ⟨4, "y"⟩))
        (if bad then pure{ Π (y : Nat) → Bool } else pure{ Π (y : Nat) → Nat }))
      .unit)
example : progOk (hSeal false) = true := by native_decide
example : progRejects (hSeal true) "does not have return type (Bool)" = true := by native_decide

-- H4. `endScope` runs PER PATH. The borrow is lent inside ONE branch only, so the
-- path that lends must demand it back at its own end while the path that does not
-- has nothing to demand — and the differential is what says both are right, since
-- the concrete run takes exactly one of them.
def hLend : Term :=
  .letIn ⟨0, "push"⟩
    (prog{ (λ(e : Nat, v : &mut (s : List Nat ~> List Nat)){
                  let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit) })
    (.letIn ⟨1, "l"⟩ (pure{ Cons(1, Nil) })
      (.letIn ⟨2, "id"⟩ (prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) })
        (.letIn ⟨3, "n"⟩ (.callV ⟨2, "id"⟩ [pure{ 3 }])
          (.matchE ⟨3, "n"⟩ none
            [Branch.mk "Z" [] .unit,
             Branch.mk "S" [⟨4, "k"⟩]
               (.letIn ⟨5, "r"⟩ (.callV ⟨0, "push"⟩ [.var ⟨4, "k"⟩, .borrow (.var ⟨1, "l"⟩)])
                 .unit)]))))
example : progOk hLend = true := by native_decide
example : progDiff hLend = true := by native_decide
-- It really is two paths, and the lending one really does end its loan: no path
-- leaves `l` holding a parked loan.
example : ((programEnvs hLend).length == 2
        && (programEnvs hLend).all (fun r => match r with
             | .ok env => !((env.lookup "l").any (fun v => match v with
                 | .loanM _ => true | _ => false))
             | .error _ => false)) = true := by native_decide
-- …and the raw walk (no end-of-scope demand) leaves one, so the assertion above is
-- about `endScope` and not about the program never lending.
example : (rawEnvs hLend).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide

end Dllbc.Tests.S26Prog
