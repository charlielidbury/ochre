import Ochr.Check

/-!
# The runtime: running a closed call of accepted code (D85)

The checker only checks. This module is the one place that runs a program: `runCall` runs a
closed call `g(v̄)` of an accepted global, untyped, in runtime mode (`MState.runtime`), where
`J(A, a, b, P, h, t)` is `t`, unconditionally ([J-run], RULES §3 "Runtime"). A proof parameter's
argument is `⋆`, as the erased program passes it. Otherwise the run is the machine's untyped run
(RULES §3): its statements still run on private copies that are discarded (D68), which leaves the
state as skipping them would, and it closes off where it is stuck ([Close]), so a result holding a
sealed program is a closed run that got stuck.

The checker cannot reach the runtime rule. `checkProgram` (`Ochr/Run.lean`) and every module it
imports do not import this one, so nothing they run can call `runCall`; this is the only code that
sets `runtime`, and every state the checker starts from has it off (`checkDefs`,
`globalsAfterFrom`). So the checker's untyped runs (callee bodies, [Seal]'s re-runs, private
copies) keep [J] and [J-stuck], and what it accepts is unchanged.
-/

namespace Ochr

/-- The closed call `g(vs)`, run by the machine untyped from a state holding only the globals and
inductive types `Σ`. With `runtime`, it is the runtime's run ([J-run]); without it, the checker's
own untyped run of the same call ([J], [J-stuck]), to compare the two. The arguments are values,
so a borrow parameter cannot be passed one (a borrow needs a cell: run `let c = v; g(&c)`). -/
def closedCall (globals : List GDef) (inds : List IndDecl) (g : String) (vs : List Value)
    (runtime : Bool) (fuel : Nat := 2000000) : Outcome Value :=
  let st : MState := { globals := globals, inds := inds, runtime := runtime }
  (runMachine (do pure (← eval (← fuelLeft) false (.call (.const g) (vs.map .val) false)).1) st fuel).1

/-- The runtime's entry point (D85): the closed call `g(vs)` of an accepted global, with `J` its
transported term. -/
def runCall (globals : List GDef) (inds : List IndDecl) (g : String) (vs : List Value)
    (fuel : Nat := 2000000) : Outcome Value :=
  closedCall globals inds g vs true fuel

end Ochr
