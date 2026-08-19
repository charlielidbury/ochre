import Dllbc.ElabCheck

/-!
# The squiggle lands on the offending *syntax*

`prog check { … }` checks as it elaborates, so a rejection is a Lean diagnostic at
the syntax that caused it rather than a string inside a `native_decide` three
declarations away. One case per granularity the span table provides.

Each case is a program the checker rejects, so the test is the error's text AND
its position; `#guard_msgs` pins the text, and `#check` is used throughout because
a rejected `def` would still be added with a `sorryAx` body, which panics on
import under `precompileModules`.
-/

open Dllbc

namespace Dllbc.Tests.ElabSpans

-- These `#guard_msgs` pin error text exactly, so the file must not also emit the
-- per-program timing traces if the suite is built with `trace.Dllbc.check` on.
set_option trace.Dllbc.check false

/-! ## (1) A call argument

    `F` takes a `Bool`; the call passes `3`. The squiggle belongs on `3` alone —
    not on the call, not on the statement — and the message states the parameter
    type the argument was checked against. -/

/--
error: dllbc: the program is rejected:
call: argument (S (S (S Z))) does not have its parameter type (Bool)
-/
#guard_msgs in
#check (prog check{
  fn F (b : Bool) -> Unit { () };
  let r = F(3);
  () } : Term)

/-! ## (2) A statement mid-program

    The move is three statements in; the read that follows it is the error. -/

/--
error: dllbc: the program is rejected:
readR: x#0 holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6).
-/
#guard_msgs in
#check (prog check{
  let x = Cons(1, Nil);
  let y = x;
  let z = x;
  () } : Term)

/-! ## (3) Inside one arm of a match

    The double take is only on the `S` path, and the message says so: under
    path-sensitive checking a statement is checked once per path, so which path
    failed is half the diagnosis. -/

/--
error: dllbc: the program is rejected, on the path where n ⇒ S:
readR(*): borrow payload is already a hole (⊥) — nothing to take
-/
#guard_msgs in
#check (prog check{
  let n = S(Z);
  let l = Cons(1, Nil);
  let v = &m l;
  match n {
    Z => (),
    S(k) => { let a = *v; let b = *v; *v := a; () }
  } } : Term)

/-! ## (4) The return type

    `-> τ` is what asks for the audit, so an audit rejection squiggles the type
    that was asked for rather than whichever statement happened to run last. -/

/--
error: dllbc: the program is rejected:
audit: result (S Z) does not have return type (Bool)
-/
#guard_msgs in
#check (prog check -> Bool {
  let x = S(Z);
  x } : Term)

/-! ## (5) A program that CHECKS elaborates to exactly the term it always did

    The check is a side effect of elaboration and changes nothing about the value.
    `prog check { … }` and `prog{ … }` on the same source are the same `Term`. -/

example :
    ((prog check{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })
     == (prog{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })) = true := by
  native_decide

/-! ## (6) SPLICE AUTO-DEFERRAL

    A body template whose return type is spliced from a Lean-level parameter has
    no closed value at elaboration time, so it is declined silently — no marker
    written, no error raised. This is the twin-template pattern: `under` is
    instantiated below at a type it satisfies and at one it does not, and it is
    those INSTANTIATIONS that carry the assertions. -/

def under (ret : Term) : Term := prog check -> %ret {
  let x = S(Z);
  x }

-- The `-> τ` is elaboration metadata and not part of the value, so both
-- instantiations are the SAME `Term` and the return type is supplied to the
-- assertion. That is the twin pattern exactly: one body, two claims about it.
example : progOk (under prog{ Nat }) prog{ Nat } = true := by native_decide
example :
    progRejects (under prog{ Bool }) "does not have return type" prog{ Bool } = true := by
  native_decide

end Dllbc.Tests.ElabSpans
