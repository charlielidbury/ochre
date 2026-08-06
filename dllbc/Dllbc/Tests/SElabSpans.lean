import Dllbc.ProgMacro

/-!
# The squiggle lands on the offending *syntax*

`dllbc{ … }` checks as it elaborates, so a rejection is a Lean diagnostic at the
syntax that caused it rather than a string inside an `#eval` three declarations
away. Three granularities, one per shape the span table provides.

Each case is a program the checker rejects, so the test is the error's text AND
position; `#guard_msgs` pins the text, and `#check` is used throughout because a
rejected `def` would still be added with a `sorryAx` body, which panics on import
under `precompileModules`.
-/

open Dllbc

namespace Dllbc.Tests.SElabSpans

-- These `#guard_msgs` pin error text exactly, so the file must not also emit the
-- per-program timing traces if the suite is built with `trace.Dllbc.check` on.
set_option trace.Dllbc.check false

/-! ## (1) A call argument

    `f` takes a `Bool`; the call passes `3`. The squiggle belongs on `3` alone —
    not on the call, not on the statement — and the message states the parameter
    type the argument was checked against. -/

/--
error: dllbc: the program is rejected:
call: argument (S (S (S Z))) does not have its parameter type (Bool)
-/
#guard_msgs in
#check (dllbc{
  let f = seal(λ(b : Bool){ () }, Π (b : Bool) → Unit);
  let r = f(3);
  () } : Term)

/-! ## (2) A statement mid-program

    The move is three statements in; the read that follows it is the error. -/

/--
error: dllbc: the program is rejected:
readR: x#0 holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6).
-/
#guard_msgs in
#check (dllbc{
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
#check (dllbc{
  let n = S(Z);
  let l = Cons(1, Nil);
  let v = &mut l;
  match n {
    Z => (),
    S(k) => { let a = *v; let b = *v; *v := a; () }
  } } : Term)

end Dllbc.Tests.SElabSpans
