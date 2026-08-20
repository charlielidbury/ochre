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
error: dllbc:
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
error: dllbc:
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
error: dllbc, on the path where n ⇒ S:
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

/-! ## (4) A RESULT SEAL — what the retired `-> τ` used to express

    `-> τ` is what asks for the audit, so an audit rejection squiggles the type
    that was asked for rather than whichever statement happened to run last. -/

/--
error: dllbc:
seal: the sealed term (S Z) does not have its ascribed type (Bool)
-/
#guard_msgs in
#check (prog{
  fn F (n : Nat) -> Unit { () };
  let x = S(Z);
  (x : Bool) } : Term)

/-! ## (4a) INSIDE a `fn` body — the argument

    A function body is checked inside a seal, on its own machine state, and the
    audit throws into the ENCLOSING one. Carrying the breadcrumb back out is what
    makes this land on the argument rather than on the declaration — and this is
    where it matters most, because a `fn` body is where the corpus lives. -/

/--
error: dllbc:
call: argument (S (S (S Z))) does not have its parameter type (Bool)
-/
#guard_msgs in
#check (prog{
  fn F (b : Bool) -> Unit { () };
  fn G (x : Nat) -> Unit { F(3); () };
  () } : Term)

/-! ## (4b) INSIDE a `fn` body — the statement -/

/--
error: dllbc:
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

def under (ret : Term) : Term := prog{
  let x = S(Z);
  (x : %ret) }

-- The `-> τ` is elaboration metadata and not part of the value, so both
-- instantiations are the SAME `Term` and the return type is supplied to the
-- assertion. That is the twin pattern exactly: one body, two claims about it.
example : progOk (under prog defer_check { Nat }) prog defer_check { Nat } = true := by native_decide
example :
    progRejects (under prog defer_check { Bool }) "does not have its ascribed type" prog defer_check { Bool } = true := by
  native_decide

/-! ## (7) AN ASCRIBED PURE BLOCK — a proof checked at its own definition

    A block with no `fn` in it carries no specification, so nothing can be asked
    of it — unless a SEAL supplies one. `(e : τ)` is the ascription, in the
    grammar, and its symbolic-⇒ rule verifies the term at the node. This extends
    elaboration-time checking to PROOFS: a lemma with a type error fails at its
    own definition instead of at a `chk` probe in another file.

    `LeRefl` is `StdLemmas`' own, verbatim, sealed at the type its separate
    `LeReflTy` definition states.

    **The `!=` is the point, not a workaround.** `prog -> τ { M }` treated the
    type as elaboration METADATA and produced `M`; a seal is a TERM FORMER and
    produces `.seal s M τ`. So retiring `-> τ` in favour of the seal changes what
    the block evaluates to, and this assertion pins that difference rather than
    hiding it. Anything comparing a sealed block against an unsealed constant has
    to account for the seal. -/

example :
    (prog{ (λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
             Z => unit,
             S (K) Ih => Ih } : Π (N : Nat) → Le N N) } != StdLemmas.LeRefl) = true := by
  native_decide

/-! And the lie fails at the definition, at the seal node.

    **A COST OF THE MIGRATION, RECORDED RATHER THAN HIDDEN.** The retired
    `checkPureDiag` path printed one line — "the term does not have its stated
    type (Π(N : ⇝Nat). Id #N #N)" — naming only the TYPE. The seal prints the
    whole NORMALIZED TERM before naming the type, so the same lie on a real
    `StdLemmas` proof produces roughly fifteen lines of `natRec` spine. That is
    worse to read, and it is also unpinnable: any change to normalization would
    break a `#guard_msgs` on it.

    So the specimen here is deliberately TINY — `(unit : Nat)` — which keeps the
    property under test (a pure ascription mismatch reports at the seal) and drops
    only the incidental bulk. The verbosity is a real regression against the
    retired path and belongs in the report, not in this file's expectations. -/

/--
error: dllbc:
seal: the sealed term (unit) does not have its ascribed type (Nat)
-/
#guard_msgs in
#check (prog{ (unit : Nat) } : Term)

/-! ## (8) `defer_check` elaborates and checks nothing

    The one explicit opt-out. It parses and binds; no walk, no verdict. What it
    marks is a block whose checking lives at its PROBE — a proof checked by a
    `chk`, a spec term, a rejection twin whose rejection is its assertion. -/

example :
    ((prog defer_check { λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
                    Z => unit, S (K) Ih => Ih } })
     == StdLemmas.LeRefl) = true := by native_decide

/-! ## (9) THE SEAL IS THE ASCRIPTION — the specimen that retired `prog -> τ`

    **This case is the user's own probe**, written during review to ask whether
    the built-in ascription already did what the `-> τ` arm was hand-rolling. It
    does. `(M : τ)` is surface syntax for `.seal s M τ`, and `Syntax.lean`'s
    description of that node is verbatim the arm's job: "CHECKING (⇒, symbolic):
    verify `t : u` ONCE, at the node — this check *is* the audit".

    So the ascription is in the GRAMMAR, the check happens at a term node the
    span machinery already localizes, and there is no macro side-channel and no
    special-cased error attribution. `(5 : Unit)` is the lie and `(5 : Nat)`
    beside it is the control — the block would elaborate but for the first seal.

    That this passes today is the retirement's whole evidence. -/

/--
error: dllbc:
seal: the sealed term (S (S (S (S (S Z))))) does not have its ascribed type (Unit)
-/
#guard_msgs in
#check (prog{
  (5 : Unit);
  (5 : Nat);
  ()
} : Term)

end Dllbc.Tests.ElabSpans
