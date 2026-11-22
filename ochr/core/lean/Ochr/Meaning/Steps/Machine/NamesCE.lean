import Ochr.Examples.Nat

/-!
# `NamesFact`'s parameter part is false (machine11, 2026-11-22)

READ FALSE: `Assembly.NamesFact`'s inductive parameter part ("its parameter types name only the stage's"). The checker
ACCEPTS `inductive Q6 (A : Type) (x : (let z = Z; match z { Z => A, S(k) => Q6 })) := MkQ6`: the parameter type of
`x` names `Q6` itself, which is not in the stage (`stageNames` holds the earlier items' names only).

Why: D118's `undeclaredCheck (some n) (params ++ field types)` (`Check.lean`, `checkInd`) admits the type's own name in
its PARAMETER types as in its field types; a mention of the type in its own parameter list is otherwise refused only
by evaluating it (`Q1`, `Q2` below: the application is one parameter short), and the arm of a match on a known number
that is not taken is never evaluated (nor is its arity checked by `declOf`). Field types cannot do this: D36 rejects a
field type that is not first-order data (a match in a field type is refused).

Fix candidates (the lead's call): in the checker, `undeclaredCheck none` on the parameter types (a parameter type may
not mention the type being declared), one line; or in the fact, the parameter part read with `fieldNames` (the stage's
names and the declaration itself), if its consumer allows. Side note: `inductive Q3 (A : Type) (n : Nat) (x : Q3(A, n,
n)) := MkQ3` (each application of `Q3` in its parameter list asks for another) did not finish in 120 s at fuel 200000
and the first attempt, at the default fuel, was killed by SIGTERM (memory): not accepted, but a hazard for the box.
-/

open Ochr.Test

ochr NamesCE uses Nats {
  -- ACCEPTED: the parameter type of `x` names `Q6` in the arm the match on `Z` does not take
  inductive Q6 (A : Type) (x : (let z = Z; match z { Z => A, S(k) => Q6 })) := MkQ6
  -- controls: a mention the checker evaluates is one parameter short
  reject inductive Q1 (A : Type) (x : Q1(A)) := MkQ1
  reject inductive Q2 (x : Q2) := MkQ2
}

#guard (Ochr.Test.runWith (some Prelude) "NamesCE" NamesCE {} (fuel := 200000) (located := false)).allAsExpected
