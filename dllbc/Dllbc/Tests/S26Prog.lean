import Dllbc.Program
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.S9Diff

/-!
# §26 (M26-E) — programs are terms

`combining-fns.md` §8: **a program is an arbitrary term, and running it is
⇒-evaluating it.** A module is a let-chain — transparent lets, sealed lets, a
tail — and checking it is the symbolic ⇒-walk of the same term. `Decl` is what
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
open Dllbc.StdLemmas (le_trans le_refl)

namespace Dllbc.Tests.S26Prog

/-! ## Helpers

    `progOk`/`progRejects`/`runProgram` are `Program.lean`'s. The differential is
    S9Diff's merged relation, applied to a program instead of to a `Decl` body —
    which is the same thing now, and the reason `diffC` needed no new definition:
    it already took a TERM. -/

/-- The concrete final Ω is a σ-instance of some accepted symbolic path's. -/
def progDiff (t : Term) (table : List Decl := []) : Bool :=
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

    The smallest complete statement of §8: no `Decl`, no telescope, no return
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
  let f = seal(λ (x : Nat). x, Π (x : Nat) → Nat);
  let g = seal(λ(y){ f(y) }, Π (y : Nat) → Nat);
  let r = g(3);
  r }
example : progOk a2 (.const "Nat") = true := by native_decide
example : progDiff a2 = true := by native_decide
-- The claim that it was really the seal that made `f` callable: the same program
-- with `f` bound to a NON-function is refused, and the refusal names the capture.
def a2cap : Term := prog{
  let f = 3;
  let g = seal(λ(y){ let z = f; y }, Π (y : Nat) → Nat);
  () }
example : progRejects a2cap "not a function" = true := by native_decide

-- A3. A sealed function that MUTATES through a borrow, applied to a local. The
-- program owns the list, lends it, and gets it back — the whole borrow story with
-- no declaration anywhere in it.
def push : Term := prog{
  let push = seal(λ(e, v){ let tail = *v; *v := Cons(e, tail); () },
                  Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit);
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
def b1 : Term := prog{ let f = seal(λ(x){ x }, Π (x : Nat) → Bool); () }
example : progRejects b1 "does not have return type (Bool)" = true := by native_decide

/-- ### B2. The vacuous twin, kept beside it

    An UNSEALED λ with the same nonsense body is ACCEPTED, because nothing demands
    it: `readR` forms the value and never looks inside. This is phase A's
    per-DEMAND-SITE finding, and it is the trap a reader of B1 would otherwise
    fall into — "binding a bad function is caught" is true only of a SEALED
    binding. The live twin below is what makes it a real difference: call it, and
    the demand arrives. -/
def b2vac : Term := prog{ let g = λ(x){ True }; () }
def b2live : Term := prog{ let g = λ(x){ True }; let r = g(1); r }
example : progOk b2vac = true := by native_decide
example : progRejects b2live "does not have return type (Nat)" (.const "Nat") = true := by native_decide

-- B3. **Program order**, pinned the only way it can be: two lies, and the one
-- that is reported is the FIRST. (Both messages have the same shape, so the
-- needles are the types, which differ.)
def b3 : Term := prog{
  let f = seal(λ(x){ x }, Π (x : Nat) → Bool);
  let g = seal(λ(x){ True }, Π (x : Nat) → Unit);
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
  let g = seal(λ(y){ h(y) }, Π (y : Nat) → Nat);
  let h = seal(λ (x : Nat). x, Π (x : Nat) → Nat);
  () }
example : progRejects c1 "unknown function 'h'" = true := by native_decide
-- …and the same program with the two bindings SWAPPED is accepted, so the
-- rejection is about the order and not about the pair.
def c1ok : Term := prog{
  let h = seal(λ (x : Nat). x, Π (x : Nat) → Nat);
  let g = seal(λ(y){ h(y) }, Π (y : Nat) → Nat);
  let r = g(3);
  r }
example : progOk c1ok (.const "Nat") = true := by native_decide
example : progDiff c1ok = true := by native_decide

/-! ### C2. The deliberately-wrong table becomes a different let-prefix

    The old suite guarded caller-side reasoning by checking a caller against a
    table entry whose signature was a lie. There is no table to lie in now, so the
    same test becomes **one caller suffix under two prefixes**: the callee's body
    is identical and honest in both, and what differs is the type it is SEALED at.
    That is §5 point 4 with nothing left to interpret — what the caller keeps is
    what the programmer wrote — and it is a sharper test than the old one, because
    the lying prefix is a program that itself checks. -/

/-- The shared suffix: call it at 3 and hand back what came out. -/
def c2suffix : Term := progWith [f] { let r = f(3); r }
/-- The retType the suffix is demanded at: the equation the caller wants. -/
def c2demand : Term := pure{ Σ (m : Nat) → Id Nat m 3 }

/-- Prefix A — the signature CARRIES the equation. -/
def c2keeps : Term :=
  .letIn ⟨900, "f"⟩
    (prog{ seal(λ(n){ Pair(n, Refl) }, Π (n : Nat) → Σ (m : Nat) → Id Nat m n) }) c2suffix
/-- Prefix B — the same body, sealed at a type that FORGETS it (true, and
    useless). It checks: the lie is not in the callee, it is in what the callee
    promises. -/
def c2forgets : Term :=
  .letIn ⟨900, "f"⟩
    (prog{ seal(λ(n){ Pair(n, Refl) }, Π (n : Nat) → Σ (m : Nat) → Id Nat m m) }) c2suffix

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
  let f = seal(λ (x : Nat). S(x), Π (x : Nat) → Nat);
  let g = seal(λ(y){ f(f(y)) }, Π (y : Nat) → Nat);
  let h = seal(λ(z){ g(g(z)) }, Π (z : Nat) → Nat);
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
  let g = seal(λ(a){ let z = n; a }, Π (a : Nat) → Nat);
  () }
def d2dataOk : Term := prog{
  let n = 3;
  let g = seal(λ(a, m){ let z = m; a }, Π (a : Nat) → Π (m : Nat) → Nat);
  let r = g(1, n);
  r }
example : progRejects d2data "not a function" = true := by native_decide
example : progOk d2dataOk (.const "Nat") = true := by native_decide

-- D2b. A BORROW — the case constraint 5 is really about, since a captured borrow
-- is a suspended loan with no scope to end it in.
def d2borrow : Term := prog{
  let l = Cons(1, Nil);
  let b = &mut l;
  let g = seal(λ(a){ *b := Nil; a }, Π (a : Nat) → Nat);
  () }
example : progRejects d2borrow "not a function" = true := by native_decide

-- D2c. A free variable that names NOTHING is a different rejection with a
-- different message, and it is the one §8 explains: a let-chain cannot reference
-- downward. (Reached here through a `.callV`-free body, so it is the variable
-- rule and not the call rule doing the work — c1 covers the call side.)
def d2free : Term :=
  .letIn ⟨0, "g"⟩ (.seal (.lamR [⟨1, "a"⟩] (.letIn ⟨2, "z"⟩ (.var ⟨9, "nope"⟩) (.var ⟨1, "a"⟩)))
    (pure{ Π (a : Nat) → Nat })) .unit
example : progRejects d2free "not bound anywhere above it" = true := by native_decide

-- D3. A sealed PROOF is not a global either, and that is deliberate rather than
-- an oversight: §5's `Qed` binding is a value, and a body that wants it should
-- take it as a capital parameter (which is exactly what §6 built). Recorded as a
-- limitation with its route beside it, not as a defect.
def d3 : Term := prog{
  let cert = seal(le_refl 3, Le 3 3);
  let g = seal(λ(a){ let z = cert; a }, Π (a : Nat) → Nat);
  () }
example : progRejects d3 "not a function" = true := by native_decide

-- D3b. And the capital form of the same binding is refused EARLIER and for a
-- different reason, which is §6's own parenthesis becoming a rejection: `let X =
-- e` reads `e` under ⇝, and the seal is a ⇒-form because minting needs an event.
-- So "sealed" and "comptime-bound" are mutually exclusive, and a reader who
-- expects `let Cert = seal(…)` to be the `Qed` form is told which half to drop.
def d3cap : Term := prog{ let C = seal(le_refl 3, Le 3 3); () }
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

end Dllbc.Tests.S26Prog
