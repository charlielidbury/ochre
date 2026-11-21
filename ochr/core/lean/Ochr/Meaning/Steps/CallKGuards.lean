import Ochr.Meaning.Steps.BorrowParGuards
import Ochr.Meaning.Steps.CallJ2

/-!
# The first caller of a borrow-returning function, `L` (lead20, 2026-11-22; docs/31 D146)

`def L : Nat := let x = S(Z); let y = K(&x); *y := Z; x` with `K (r : &Nat) : &Nat := r` in Σ: the smallest accepted
program that calls a function returning a borrow and uses the result (writes through it, then reads the lender, which
ends it). Its value is `0`: the write through `y` reaches `x`.

What the checker does at the call `K(&x)`, from the state after `let x = S(Z)` (`stLX`: `x ↦ S(Z) : Nat`, counter 0),
pinned below (every `#guard` runs the checker):
* `&x` lends `x` (`x ↦ loan₀`) and the argument `borrow₀ S(Z)` is bound to `K`'s parameter;
* the call RUNS `K`'s body (the recorded entry has two frames; the body's exit value is `borrow₀ S(Z)`, the parameter's
  borrow), it is not closed off;
* [Lend] then gives the result a FRESH label `1` and re-marks the lender: the value `borrow₁ S(Z) : &Nat` in flight,
  `x ↦ lent₁ loan₁` (`.gloan 1 (.loan 1)`), the counter at `2`; label `0` (the argument's) occurs nowhere after.

The reference (`callOfL`'s `.ref` row) matches it: the argument's label is consumed (`takeLabel`), a fresh label `k` is
the result's, parked in a temporary with the forward value, the lender `x` (lent to the argument's label) reads the
backward function at `k`'s final content, and `x` is lent to `k` as a FILL. The relation after the call maps the
checker's `1` to `k`; `x` means `ψ k` on both sides exactly at the futures that give `k` a member of `Nat` (the
backward function decodes `ψ k` there), which are the futures `Rel` compares at (`TypedLive`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW.Guards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open Ochr.Meaning.Steps.Form.CallJ2 (xB)

/-- `L`'s body: `let x = S(Z); let y = K(&x); *y := Z; x`. -/
def bodyL : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.call (.const "K") [.borrow (.var 0)] false)
  (.seq (.assign (.deref (.var 0)) .zero) (.place (.var 1))))
def defL : Def := { name := "L", hs := [], doms := [], cod := .nat, body := bodyL }
/-- The checker's state before `L`'s body: `K` in Σ. -/
def stL : MState := { env := #[{}], globals := [gK] }

/-- The call `K(&x)`. -/
def callK : Term := .call (.const "K") [.borrow (.var 0)] false
/-- The state before the call: `x ↦ S(Z) : Nat`. -/
def stLX : MState := { env := #[{ binds := #[xB (.succ .zero)] }], globals := [gK] }
/-- The kernel after the call: `x ↦ lent₁ loan₁`, the counter at `2`. -/
def stLY : MState := { env := #[{ binds := #[xB (.gloan 1 (.loan 1))] }], globals := [gK], nextLoan := 2 }

#guard isOk (checkDef defL) stL 100000
#guard (match runMachine (checkDef defL) { stL with cfg := { derivation := true, trace := true } } 100000 with
  | (_, _, log) => log.toList.filterMap fun | LogEntry.line s => some s | _ => none) ==
  ["[Call-type] K(borrow_0 1) : &Nat", "[Lend] the result is lent every place its 1 borrow argument(s) lend",
   "[Read] its declared type is not a copy type: moved out",
   "[Return] L is defined as it: 0 : Nat, with 0 place(s) held by borrow"]
-- `L`'s value: `0` (the write through `y` reaches `x`)
#guard outVal (Ochr.eval 100 true bodyL (some .tNat)) stL 100000 == (.zero, some .tNat)

-- the call: `borrow₁ S(Z) : &Nat`, `x ↦ lent₁ loan₁`, counter 2; at every hint, and untyped
#guard [some (.tRef .tNat), none].all fun h =>
  outVal (Ochr.eval 100 true callK h) stLX 100000 == (.borrow 1 (.succ .zero), some (.tRef .tNat)) &&
    kernEq (outSt (Ochr.eval 100 true callK h) stLX 100000) stLY
#guard (outVal (Ochr.eval 100 false callK none) stLX 100000).1 == .borrow 1 (.succ .zero)

/-- The recorded entries and exits of the bodies run at the call. -/
def deepK : List (Bool × Option (Value × Option Value) × MState) :=
  match runMachine (Ochr.eval 100 true callK (some (.tRef .tNat))) { stLX with cfg := { recordDeep := true } } 100000 with
  | (_, _, log) => log.toList.filterMap fun
      | LogEntry.deep ex fl st => some (ex, fl, st) | _ => none

-- the call runs `K`'s body (entry, two frames; exit, the parameter's borrow `borrow₀ S(Z)`): not closed off
#guard deepK.map (fun x => (x.1, x.2.2.env.size, x.2.1.map (·.1))) ==
  [(false, 2, none), (true, 2, some (.borrow 0 (.succ .zero)))]

end Ochr.Meaning.Steps.Form.ColumnW.Guards

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **`K`'s call in `L`** (a fact about the checker alone, for the machine lane; docs/31 D146): every successful typed
`eval` of `K(&x)` from a state with `stLX`'s kernel, in the plain mode, with no handed-down reading, returns a borrow of
fresh label `1` at `&Nat` and ends with `stLY`'s kernel (`x ↦ lent₁ loan₁`, counter `2`); the borrow's content is the
body's value's, `S(Z)`, or a sealed call (a call's inversion names the body's value or the sealed call; the guards see
only the first). Guarded in `Steps/CallKGuards.lean`. -/
def CallKInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Kern Guards.stLX st → Mode st → st.tailDecl = none →
    Runs (Ochr.eval n true Guards.callK hint) st bh (v, T?) st' →
    T? = some (.tRef .tNat) ∧ Kern Guards.stLY st' ∧
      (v = .borrow 1 (.succ .zero) ∨ ∃ w, v = .borrow 1 w ∧ w.isSealed = true)

end Ochr.Meaning.Steps.Form.ColumnW
