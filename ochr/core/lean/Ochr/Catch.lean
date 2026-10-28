import Ochr.Pretty
import Ochr.Loc

/-!
# How a run fails, and the only ways the checker may catch a failure

A run of the machine ends with a value, or fails: it is `stuck` on a neutral, or it hits an
`error` (a type error, a borrow error, a name that is not declared). Separately, it may be
`Exhausted`: out of fuel, or past a depth limit. Exhaustion is not a failure of the program but
"the checker does not know" (as in Och's `outOfFuel`, `lean/Och/Outcome.lean`), so it lives in
its own exception layer *below* `Fail` (`Ochr.M`): a `tryCatch` on `Fail` cannot see it, and
it reaches the top as the verdict `undecided`. The fuel counter lives below both, beside the
log, so no catch can roll it back.

**The rule** (`notes/catch-census.md`; the user, 2026-10-28, after the consistency statement
found 54 handlers, 38 of them one-line defaults that also caught running out of fuel and
refunded the fuel spent, so that a low-fuel run could decide differently from a high-fuel
one): an error, running out of fuel and a depth limit are never turned into a decision. Below
the top-level verdict boundary (`checkDefs`, where an error is a `rejected` verdict) a failure
is handled only by:
* `catchStuck`: the one outcome rules of the paper name, a run stuck on a neutral, which
  [App-close], [App-head], [Seal-stuck], [Obs] and `split`'s search handle. An error is
  rethrown (exhaustion never reaches a handler on `Fail`).
* `onFail`: restore bookkeeping (a flag, a frame, a private copy) and rethrow unchanged.
* `locateErrors`: give an unlocated error a source range and rethrow it.

A question whose answer may legitimately be "undefined" (does this place exist, is this value's
type readable, is this name declared) is asked of a total function returning `Option`, never by
trying and catching. The checker's other modules call none of `tryCatch`, `try … catch` or
`toOption` on a run; they use the three helpers here (the rule is stated for authors in
`ochr/core/CLAUDE.md`).
-/

namespace Ochr

inductive Fail where
  -- `on`: the neutral a match was stuck on, if any. A diagnostic only (D61): no handler but
  -- `split`'s search (`stuckScrutinee`) reads it, so it changes no result
  | stuck (on : Option Value)
  -- `at?`: where in the source (the editor, `located`); `none` everywhere else
  | error (msg : String) (at? : Option Loc := none)

instance : Inhabited Fail := ⟨.error "?"⟩

/-- Out of fuel, or past a depth limit: the checker does not know. Thrown below `Fail`, so no
handler on `Fail` sees it; the top level reports it as `undecided`. -/
structure Exhausted where
  msg : String

/-- The fuel left, in the state layer below every exception (`Ochr.M`), so that a caught failure
never refunds what it spent. -/
structure Fuel where
  left : Nat

/-- Run `x`; if it is stuck, continue with `h` (a rule of the paper handles a stuck run:
[App-close], [Seal-stuck], …). An error is rethrown unchanged. -/
@[inline] def catchStuck {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf Fail m]
    (x : m α) (h : Option Value → m α) : m α :=
  tryCatchThe Fail x fun e => match e with
    | .stuck on => h on
    | e => throwThe Fail e

/-- Run `x`; if it fails in any way, run `cleanup` (from the state at the `try`) and rethrow the
same failure. A `finally` for bookkeeping, never a recovery. -/
@[inline] def onFail {m : Type → Type} {ε α : Type} [Monad m] [MonadExcept ε m]
    (x : m α) (cleanup : m Unit) : m α :=
  tryCatch x fun e => do cleanup; throw e

/-- Run `x`; an error escaping it that no inner term located is located at `l`, and rethrown.
Every other failure is rethrown unchanged. -/
@[inline] def locateErrors {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf Fail m]
    (l : Loc) (x : m α) : m α :=
  tryCatchThe Fail x fun e => match e with
    | .error msg none => throwThe Fail (.error msg (some l))
    | e => throwThe Fail e

end Ochr
