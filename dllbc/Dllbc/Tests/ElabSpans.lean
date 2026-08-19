import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
# The squiggle lands on the offending *syntax*

`prog{ … }` checks as it elaborates, so a rejection is a Lean diagnostic at
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
#check (prog{
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
#check (prog{
  fn F (l : List Nat) -> Unit { () };
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
#check (prog{
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
#check (prog -> Bool {
  fn F (n : Nat) -> Unit { () };
  let x = S(Z);
  x } : Term)

/-! ## (4a) INSIDE a `fn` body — the argument

    A function body is checked inside a seal, on its own machine state, and the
    audit throws into the ENCLOSING one. Carrying the breadcrumb back out is what
    makes this land on the argument rather than on the declaration — and this is
    where it matters most, because a `fn` body is where the corpus lives. -/

/--
error: dllbc: the program is rejected:
call: argument (S (S (S Z))) does not have its parameter type (Bool)
-/
#guard_msgs in
#check (prog{
  fn F (b : Bool) -> Unit { () };
  fn G (x : Nat) -> Unit { F(3); () };
  () } : Term)

/-! ## (4b) INSIDE a `fn` body — the statement -/

/--
error: dllbc: the program is rejected:
readR: a#1 holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6).
-/
#guard_msgs in
#check (prog{
  fn H (x : Nat) -> Unit { let a = Cons(1, Nil); let b = a; let c = a; () };
  () } : Term)

/-! ## (5) A program that CHECKS elaborates to exactly the term it always did

    The check is a side effect of elaboration and changes nothing about the value.
    `prog{ … }` (which checks) and `ty{ … }` (which does not) on the same source
    are the same `Term`.

    This comparison is what keeps the claim falsifiable. Before the surface move
    the two braces were `prog check{ }` and `prog{ }`; both spellings now route to
    the checking elaborator, so writing it that way would compare a term with
    itself and assert nothing. `ty{ }` is the brace that survives BELOW the
    checker, and it is the honest right-hand side. -/

example :
    ((prog{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })
     == (ty{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })) = true := by
  native_decide

/-! ## (6) SPLICE AUTO-DEFERRAL

    A body template whose return type is spliced from a Lean-level parameter has
    no closed value at elaboration time, so it is declined silently — no marker
    written, no error raised. This is the twin-template pattern: `under` is
    instantiated below at a type it satisfies and at one it does not, and it is
    those INSTANTIATIONS that carry the assertions. -/

def under (ret : Term) : Term := prog -> %ret {
  let x = S(Z);
  x }

-- The `-> τ` is elaboration metadata and not part of the value, so both
-- instantiations are the SAME `Term` and the return type is supplied to the
-- assertion. That is the twin pattern exactly: one body, two claims about it.
example : progOk (under prog{ Nat }) prog{ Nat } = true := by native_decide
example :
    progRejects (under prog{ Bool }) "does not have return type" prog{ Bool } = true := by
  native_decide

/-! ## (7) THE OTHER HALF OF THE INFORMATION RULE — an ascribed PURE block

    A block with no `fn` in it carries no specification, so nothing can be asked
    of it — unless a `-> τ` supplies one, and then the check that type asks for is
    `hasTypeT`, not the ⇒-walk. This extends elaboration-time checking to PROOFS:
    a lemma with a type error fails at its own definition instead of at a `chk`
    probe in another file.

    `LeRefl` is `StdLemmas`' own, verbatim, with its type moved from the separate
    `LeReflTy` definition into the ascription. -/

example :
    ((prog -> Π (N : Nat) → Le N N {
        λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
          Z => unit,
          S (K) Ih => Ih } })
     == StdLemmas.LeRefl) = true := by native_decide

/-! And the lie fails at the definition. The message is thinner than the program
    path's — `hasTypeT` answers `false` without saying where inside the term the
    mismatch was, so there is no statement to point at and the error lands on the
    ascription (the plan's S3 is what would sharpen it). Thinner, but local: this
    is the lemma's own line. -/

/--
error: dllbc: the program is rejected:
the term does not have its stated type (Π(N : ⇝Nat). Id #N #N)
-/
#guard_msgs in
#check (prog -> Π (N : Nat) → Id Nat N N {
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (K) Ih => Ih } } : Term)

/-! ## (8) A bare pure block is checked by nothing, and that is information
    absence rather than a policy

    No `fn`, no ascription: there is no specification anywhere, and a λ is
    checkable but not synthesizable. Nothing is deferred here — there is simply
    no question to ask. It elaborates to exactly what `ty{ }` gives. -/

example :
    ((prog{ λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
                    Z => unit, S (K) Ih => Ih } })
     == StdLemmas.LeRefl) = true := by native_decide

end Dllbc.Tests.ElabSpans
