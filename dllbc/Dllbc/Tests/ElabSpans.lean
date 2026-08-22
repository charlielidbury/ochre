import Dllbc.ElabCheck
import Dllbc.StdLemmas

/-!
`prog{ }` checks as it elaborates, so a rejection surfaces as a Lean
diagnostic at the offending syntax rather than as a string checked three
declarations later. Each case here pins both the error text and its position,
one per span granularity the checker can localize to.

`#check` is used throughout rather than `def`: a rejected `def` would still be
added with a `sorryAx` body, which breaks importing under `precompileModules`.
-/

open Dllbc

namespace Dllbc.Tests.ElabSpans

-- `#guard_msgs` below pins error text exactly, so trace output from
-- `trace.Dllbc.check` must stay off regardless of the ambient setting.
set_option trace.Dllbc.check false

/-! ## (1) A call argument

    `F` takes a `Bool`; the call passes `3`. The error must land on the
    argument `3` alone, not the call or the statement, since that is the
    syntax the parameter-type check applies to. -/

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

    `x` moves into `y`; the error must land on the read of `x` in the next
    statement, not on the move that emptied it. -/

/--
error: dllbc:
readR: x holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6).
-/
#guard_msgs in
#check (prog{
  fn F (l : List Nat) -> Unit { () };
  let x = Cons(1, Nil);
  let y = x;
  let z = x;
  () } : Term)

/-! ## (3) Inside one arm of a match

    The double read is only on the `S(k)` arm. Checking is path-sensitive, so
    the message must name which arm failed as well as the statement inside it. -/

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

/-! ## (4) A result seal

    `(x : Bool)` asks for the audit; a failing audit must squiggle the
    ascribed type, not whichever statement happens to run last. -/

/--
error: dllbc:
seal: the sealed term (S Z) does not have its ascribed type (Bool)
-/
#guard_msgs in
#check (prog{
  fn F (n : Nat) -> Unit { () };
  let x = S(Z);
  (x : Bool) } : Term)

/-! ## (4a) Inside a `fn` body — the argument

    Same case as (1), but the failing call is inside `G`'s body: the error
    must still land on the argument `3`, not on the enclosing declaration. -/

/--
error: dllbc:
call: argument (S (S (S Z))) does not have its parameter type (Bool)
-/
#guard_msgs in
#check (prog{
  fn F (b : Bool) -> Unit { () };
  fn G (x : Nat) -> Unit { F(3); () };
  () } : Term)

/-! ## (4b) Inside a `fn` body — the statement

    Same case as (2), but inside `H`'s body: the error must land on the read
    of `a`, not on the enclosing declaration. -/

/--
error: dllbc:
readR: a holds ⊥ (use-after-move or uninitialized). If a CALL moved it and that callee only needs it in types or proofs, capitalizing the callee's parameter makes the argument a ⇝-read, which consumes nothing (§6).
-/
#guard_msgs in
#check (prog{
  fn H (x : Nat) -> Unit { let a = Cons(1, Nil); let b = a; let c = a; () };
  () } : Term)

/-! ## (4c) A pure-reader refusal on a statement that calls a sibling `fn`

    `Add 1 (A(n))` is ⇝-read as `B`'s tail, and the reader refuses the `A(n)`
    inside it: a sealed callee must be ENTERED, which is ⇒'s. The error must
    land on that tail expression, not on the program.

    This is the case that used to reach the "span-table gap" fallback, and the
    reason was not a missing key: a statement keyed by its OWN TERM (a tail
    expression, an expression statement, a call argument) is filed from the
    surface syntax, while the walker sees the term AFTER `bindFn` retargeted
    `A(n)` into an app spine on `A`'s slot. `let`/`fn` keys are binders and never
    noticed. `rekeySpansFrom` (Uni.lean) re-keys through the same `bindFn`.

    The span is the STATEMENT — the whole tail expression, not the `A(n)`
    inside it — because a statement is the narrowest thing the table keys
    short of a call argument. -/

/--
error: dllbc:
readC (⇝): a call is not in the comptime fragment — its result is a fresh existential, minted at an EVENT, and ⇝ has none. (Comptime application of an ABSTRACT function is the structured neutral `f a` and does reflect; a sealed or imperative callee must be entered, which is ⇒'s.)
-/
#guard_msgs in
#check (prog{
  fn A (n : Nat) -> Nat { n };
  fn B (n : Nat) -> Nat { Add 1 (A(n)) };
  () } : Term)

/-! The same refusal at a call ARGUMENT that mentions a sibling `fn` under a
    pure spine: the argument key is re-keyed too, so it lands on the argument
    `Add 1 (A(2))` rather than the `let`. -/

/--
error: dllbc:
readC (⇝): a call is not in the comptime fragment — its result is a fresh existential, minted at an EVENT, and ⇝ has none. (Comptime application of an ABSTRACT function is the structured neutral `f a` and does reflect; a sealed or imperative callee must be entered, which is ⇒'s.)
-/
#guard_msgs in
#check (prog{
  fn A (n : Nat) -> Nat { n };
  fn F (n : Nat) -> Nat { n };
  let r = F(Add 1 (A(2)));
  () } : Term)

/-! And a `[k]`-hoisted callee whose decreasing parameter is not first: the
    retarget PERMUTES the call's arguments, so a key rewritten by hand (`.call`
    to app spine, arguments in declaration order) would still miss. The key
    goes through `bindFn` itself, so it cannot. -/

/--
error: dllbc:
readC (⇝): a call is not in the comptime fragment — its result is a fresh existential, minted at an EVENT, and ⇝ has none. (Comptime application of an ABSTRACT function is the structured neutral `f a` and does reflect; a sealed or imperative callee must be entered, which is ⇒'s.)
-/
#guard_msgs in
#check (prog{
  fn A [l] (n : Nat, l : List Nat) -> Nat { match l { Nil => n, Cons(h, t) => A(n, t) } };
  fn B (n : Nat) -> Nat { Add 1 (A(n, Nil)) };
  () } : Term)

/-! ## (5) Checking doesn't change the term

    Checking is a side effect of elaboration; it does not change the value.
    `prog{ }` (which checks) and `ty{ }` (which does not) applied to the same
    source must elaborate to the same `Term`. -/

example :
    ((prog{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })
     == (ty{ fn F (b : Bool) -> Unit { () }; let r = F(True); () })) = true := by
  native_decide

/-! ## (6) Splice auto-deferral

    A body template whose return type is spliced from a Lean-level parameter
    has no closed value at elaboration time, so checking is silently skipped
    there — no error, no marker. `under` is instantiated below at a type it
    satisfies and at one it does not; those instantiations carry the
    assertions. -/

def under (ret : Term) : Term := prog{
  let x = S(Z);
  (x : %ret) }

-- The ascribed return type is elaboration metadata, not part of the value,
-- so both instantiations below produce the same `Term`; the check against
-- each return type happens only via `progOk`/`progRejects`'s own argument.
example : progOk (under prog_parse { Nat }) prog_parse { Nat } = true := by native_decide
example :
    progRejects (under prog_parse { Bool }) "does not have its ascribed type" prog_parse { Bool } = true := by
  native_decide

/-! ## (7) An ascribed pure block — checked at its own definition

    A block with no `fn` in it has no specification to check against unless
    an ascription supplies one. `(e : τ)` verifies the term at that node,
    which extends elaboration-time checking to proofs: a lemma with a type
    error fails at its own definition rather than at a separate `chk` probe.

    This copies `StdLemmas.LeReflRaw` verbatim and seals it at the type
    `LeReflTy` states. The comparison uses `!=`, not `==`: sealing is a term
    former, so `(e : τ)` produces `.seal s e τ`, a different term from the
    unsealed `e`, and the two sides are never expected to be equal. -/

example :
    (prog{ (λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
             Z => unit,
             S (K) Ih => Ih } : Π (N : Nat) → Le N N) } != StdLemmas.LeReflRaw) = true := by
  native_decide

/-! And a failing ascription reports at the seal node.

    The specimen is deliberately tiny — `(unit : Nat)` — because the seal's
    error message prints the whole normalized term before naming the type. A
    realistic proof term would produce many lines of recursor spine, which
    would make the `#guard_msgs` block fragile against normalization changes
    without testing anything more about where the error is reported. -/

/--
error: dllbc:
seal: the sealed term (unit) does not have its ascribed type (Nat)
-/
#guard_msgs in
#check (prog{ (unit : Nat) } : Term)

/-! ## (8) `prog_parse` elaborates and checks nothing

    The explicit opt-out: the block parses and binds but the checker never
    walks it. Whatever verifies it does so elsewhere, at a separate probe. -/

example :
    ((prog_parse { λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
                    Z => unit, S (K) Ih => Ih } })
     == StdLemmas.LeReflRaw) = true := by native_decide

/-! ## (9) The ascription is the check

    `(M : τ)` is surface syntax for `.seal s M τ`: an ordinary term node that
    the span machinery already localizes, checked once where it appears. No
    macro side-channel and no special-cased error attribution is needed.

    `(5 : Unit)` is the lie; `(5 : Nat)` beside it is the control, showing the
    rest of the block would elaborate but for the first seal. -/

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
