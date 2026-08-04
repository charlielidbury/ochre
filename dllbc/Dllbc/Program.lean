import Dllbc.Boundary

/-!
# Programs are terms (`docs/combining-fns.md` §8)

> "There is no declaration former and no module story, because there is nothing
> left for one to do: **a program is an arbitrary term, and running it is
> ⇒-evaluating it.**"

A module is a let-chain: transparent `let`s, sealed `let`s, and a tail
expression. Every piece of structure a declaration form ever carried already
lives on the binding — mode by case (§6), opacity by `.seal` on the right-hand
side (§5), recursion inside the term as a recursor (§7) — so this file adds no
kernel rule at all. It is two entry points and their test helpers.

**Checking a program is the symbolic ⇒-walk of it.** `explore` already is that
walk: each `let` binds, each sealed `let` fires its audit once at its own `.seal`
node (in program order, since ⇒ evaluates a let-chain in order), a symbolic match
forks paths, and the tail is checked in the accumulated Ω. What `checkFn` adds on
top of the walk — seeding a telescope, pinning a dependent return type, exit
snapshots — a program has no need of: it takes no arguments. So `checkProgram` is
`explore` plus the audit of each path's result, and nothing else.

**Scope is the call table.** A callee is a binding lexically above the call
(`.callV` on a slot, resolved by the surface from scope alone), so the `table`
parameter below defaults to EMPTY — the flagship programs are checked against no
table at all. It survives only as J1's bridge for half-migrated programs, whose
un-migrated callees are still `Decl`s.

**No forward references, by construction.** A let-chain cannot reference
downward: a name used before its binding is not in scope, so it does not resolve
to a later definition — it fails to resolve at all. Nothing rejects a forward
reference, because none can be written (`S26Prog` pins it).
-/

namespace Dllbc

/-- **The end of a program is a demand on everything it still holds.** A program
    that lends a local to a call and never looks at it again leaves the loan
    parked: the checking machine releases a group when something demands it (§5.2,
    "every demand collapses first"), and nothing ever does. The executing machine
    is not lazy in the same way — a frame's loans are released on the way out of
    it — so without this the two machines would end in visibly different Ωs on an
    ordinary program, and the differential would report a counterexample that is
    only a difference in *when*.

    Ending the scope is what a `Decl`'s audit did for its arguments
    (`collapseArg`) and what `releaseFrameLoans` does for a frame; at the top
    level there is no caller to hand anything back to, so every parked loan is
    simply demanded. It can legitimately FAIL — a group whose release is not
    justified is rejected here rather than passed over — which is why it belongs
    to checking and not to the harness. -/
partial def endScope (fuel : Nat) : M Unit := do
  match (← getEnv).findSome? (fun kv => firstLoanMarker kv.2) with
  | some ℓ => do endLoan fuel ℓ; endScope fuel
  | none => pure ()

/-- **Check a program** (§8): one symbolic ⇒-walk, auditing each path's result at
    `retType`. `table` is J1's bridge and defaults to empty — scope is the call
    table. -/
def checkProgram (t : Term) (retType : Term := .const "Unit")
    (table : List Decl := []) : Except String Unit :=
  auditPaths retType
    ((explore defaultFuel (pushContinuations t) { initSt with decls := table }).map
      (fun r => r.bind (fun p =>
        match (endScope defaultFuel).run p.2 with
        | .ok _ st => .ok (p.1, st)
        | .error e _ => .error e)))

/-- **Run a program** (§8): ⇒-evaluate it, concretely (executing mode — a call
    runs the callee's actual body), and return the final canonicalized Ω. -/
def runProgram (t : Term) (table : List Decl := []) : Except String Env :=
  match (do let _ ← readR defaultFuel (pushContinuations t); endScope defaultFuel).run
      { initSt with decls := table, executing := true } with
  | .ok _ st => .ok (canonicalize (st.env.filter (·.1.id < 10000)))
  | .error e _ => .error e

/-- The symbolic paths' final environments — for inspecting *what* a program
    leaves in Ω, and for the differential's checking side. -/
def programEnvs (t : Term) (table : List Decl := []) : List (Except String Env) :=
  (explore defaultFuel (pushContinuations t) { initSt with decls := table }).map
    (fun r => r.bind (fun p =>
      match (endScope defaultFuel).run p.2 with
      | .ok _ st => .ok (canonicalize (st.env.filter (·.1.id < 10000)))
      | .error e _ => .error e))

/-! ## Test helpers -/

/-- The program checks. -/
def progOk (t : Term) (retType : Term := .const "Unit") (table : List Decl := []) : Bool :=
  match checkProgram t retType table with | .ok _ => true | .error _ => false

/-- The program is rejected, with `needle` in the message.

    Asserted on the message rather than on a Bool for the reason phase A gave:
    `hasType` returns `false` for "does not have this type" and the audit turns
    that into an error, so a helper that collapsed error and false would let a
    *stuckness* pass for a *typing* rejection. -/
def progRejects (t : Term) (needle : String) (retType : Term := .const "Unit")
    (table : List Decl := []) : Bool :=
  match checkProgram t retType table with
  | .ok _ => false
  | .error e => strContains e needle

/-- The program runs to the given final Ω. -/
def progRunsTo (t : Term) (expected : Env) (table : List Decl := []) : Bool :=
  match runProgram t table with | .ok env => env == expected | .error _ => false

/-- The program's execution is rejected, with `needle` in the message. -/
def progRunErr (t : Term) (needle : String) (table : List Decl := []) : Bool :=
  match runProgram t table with
  | .ok _ => false
  | .error e => strContains e needle

end Dllbc
