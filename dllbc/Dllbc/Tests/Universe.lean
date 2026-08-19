import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.Universe` — the universe rule (M35)

`hasTypeT` had arms for the binder formers — `Type`, `Π`, `Σ`, `Id` all answered
`Type` — and **nothing at all for the rest of the type language**. `Nat`, `Bool`,
`Unit`, `Bot`, `List T` and `Array n T` fell through to the M5 deferral
("cannot type value …"), so the judgment `Nat : Type` was not false, it was an
ERROR.

That one hole cost value-level genericity outright, and it was measured twice
before it was closed:

  * the hm probe (O3) found that DECLARING `fn Poly (T : Type, x : T) -> T { x }`
    works — `T` is capital, so it is a comptime binder, and a declaration never
    has to type its own telescope's arguments — while CALLING it, `Poly(Nat, 5)`,
    dies checking the actual `Nat` against the parameter type `Type`. The same
    judgment is what a `Σ` packing a type needs, so `Pair(Nat, 5)` at
    `Σ (T : Type). T` failed for the identical reason;
  * the pin lane hit the classification half of it and worked around it with a
    SYNTACTIC head-recogniser, because there was no semantic "is this a type" to
    ask.

§1 pins the formation rules, §2 the two refusals, §3 the payoff — the probe's
failing battery, green.

## The one design flag: `Type : Type`

This checker is type-in-type, and in a full theory that is Girard's paradox: the
logic is inconsistent, and a closed term of `Bot` can be built. It is accepted
here because the repo's standing policy is **consistency deferred for soundness**
— the property being built is that a checked program does at RUN time what its
types say, and a universe hierarchy buys nothing for that while costing every
former a level argument.

What M35 changes is the arm's STANDING, not its verdict. `| .type => …` was
already in `hasTypeT` before this lane, as an unreachable-in-practice leaf. The
formation rules below now *depend* on it — `Σ (T : Type). T` is a type only
because `Type` is one, and that Σ is precisely the shape the hashmap flagship
wants — so it is load-bearing from here on. Refusing it is not cheap: it would
take the payoff in §3 with it. Recorded rather than discovered.
-/

namespace Dllbc.Tests.Universe

open Dllbc

/-- Type-check a closed term against a closed type in the pure seed (as §23/§24
    of `ArraySort`, `Arrays`, `OpaqueFill`). -/
def chkL (tm ty : Term) : Bool :=
  match (do let v ← readC 8000 tm; let t ← readC 8000 ty; hasTypeT 8000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-- `hasTypeT` on a RAW term, message kept. The two mode markers cannot travel
    through `readC` at all (it refuses `borrowT` outright), so handing the
    judgment the term is the only way to ask it about one — and the refusal is
    asserted on its TEXT, since `chkL` would collapse "not a type" into the same
    `false` a mistyped value gets. -/
def chkRawMsg (tm ty : Term) : String :=
  match (hasTypeT 8000 tm ty).run (seedPure [] []) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

def U : Term := prog{ Type }

/-- What the executing machine leaves in ONE binding (as `OpaqueFill`'s
    `runBinding`). The whole final Ω is not the assertion here: it also holds the
    declaration's own closure, whose printed body is not what these programs
    claim. -/
def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

/-! ## §1 The formation rules

    Each type former, at `Type`. The four ground constants first — these are the
    ones `Poly(Nat, 5)` died on. -/

example : chkL prog{ Nat } U = true := by native_decide
example : chkL prog{ Bool } U = true := by native_decide
example : chkL prog{ Unit } U = true := by native_decide
example : chkL prog{ Bot } U = true := by native_decide

/-- `Type : Type` — the flagged arm, asserted so the decision has a test and not
    just a comment. See the module header. -/
example : chkL U U = true := by native_decide

/-- The two parameterised formers, including nested, which is what makes the
    recursion in the arm visible rather than incidental. -/
example : chkL prog{ List Nat } U = true := by native_decide
example : chkL prog{ List (List Nat) } U = true := by native_decide
example : chkL prog{ Array 3 Nat } U = true := by native_decide
example : chkL prog{ Array 3 (List Nat) } U = true := by native_decide

/-- The binder formers, which had arms already and keep them. -/
example : chkL prog{ Π (x : Nat) → Nat } U = true := by native_decide
example : chkL prog{ Σ (x : Nat). Nat } U = true := by native_decide
example : chkL prog{ Id Nat 1 1 } U = true := by native_decide

/-! ### …and the same formers at a type that is NOT `Type`

    A `false`, not an error: the expected type is checked before any parameter is
    visited, so asking `List Nat : Nat` never recurses into `Nat`. -/

example : chkL prog{ Nat } prog{ Nat } = false := by native_decide
example : chkL prog{ Bot } prog{ Nat } = false := by native_decide
example : chkL prog{ List Nat } prog{ Nat } = false := by native_decide
example : chkL prog{ Array 3 Nat } prog{ Nat } = false := by native_decide

/-- Arity is exact. `List` alone is `Type → Type` and does not inhabit `Type`;
    it falls past the formation arm to the deferral, which is the honest answer —
    a partially applied former is a neutral this judgment has no rule for, not a
    type that fails to be one. -/
example : chkL prog{ List } U = false := by native_decide
example : chkL prog{ Array 3 } U = false := by native_decide

/-! ## §2 The two binder-mode markers, refused

    `⇝τ` and `&mut (s : τ ↝ τ′)` are written where a type goes and are not types:
    they say how a BINDER takes its argument — comptime snapshot, runtime borrow
    — which is the doctrine stated at both of their definitions in `Syntax.lean`.
    The refusal is an ARM rather than a fall-through, because two things lean on
    it and a fall-through would give today's verdict while losing tomorrow's
    reason:

      * a `Π` whose domain is `&mut …` is a function SIGNATURE, and `hasType`
        already refuses to admit any value at one (`hasBorrowT ty` guards the
        closure arm) — the two refusals are the same rule, read from the two
        ends;
      * `docs/12-design-borrow-refounding.md`'s proof-fragment exclusion IS "no
        `borrowT` inhabits the universe". If the marker ever became a type, a
        proof term could quantify over a borrow. -/

example : strContains (chkRawMsg (.cmpT (.const "Nat")) .type) "binder MODE" = true := by
  native_decide
example : strContains (chkRawMsg (.cmpT (.const "Nat")) .type) "comptime binder" = true := by
  native_decide
example :
  strContains (chkRawMsg (.borrowT "s" (.const "Nat") (.const "Nat")) .type) "binder MODE"
    = true := by native_decide
example :
  strContains (chkRawMsg (.borrowT "s" (.const "Nat") (.const "Nat")) .type) "runtime borrow"
    = true := by native_decide

/-- Neither is reachable through `readC` either — the marker is refused before
    the judgment is ever asked — so the arm above is a second lock on a door that
    is already shut, deliberately. -/
example : chkL prog{ &mut Nat } U = false := by native_decide

/-! ## §3 The payoff — the hm probe's O3 battery, green

    Every assertion here was a recorded FAILURE in the probe. -/

/-- (a) A `Σ` packing a type: the existential the hashmap's slot vocabulary wants.
    The first component is checked at `Type` — the judgment that did not exist —
    and the second at whatever the first turned out to be, which is what makes
    the pack dependent rather than a pair of unrelated things. -/
def sigTy : Term := prog{ Σ (T : Type). T }
example : chkL prog{ Pair(Nat, 5) } sigTy = true := by native_decide
example : chkL prog{ Pair(List Nat, Cons(1, Nil)) } sigTy = true := by native_decide

/-- …and it DISCRIMINATES: the payload must inhabit the type that was packed. -/
example : chkL prog{ Pair(Bool, 5) } sigTy = false := by native_decide

/-- (b) A generic `fn`, DECLARED — which already worked, kept as the control that
    isolates the call as the thing that changed. -/
def polyDecl : Term := prog{
  fn Poly (T : Type, x : T) -> T { x };
  () }
example : progOk polyDecl = true := by native_decide

/-- (c) …and CALLED, which is the headline. `Poly(Nat, 5)` checks the actual
    `Nat` against the parameter type `Type`, and that judgment is M35's. -/
def polyCall : Term := prog{
  fn Poly (T : Type, x : T) -> T { x };
  let y = Poly(Nat, 5);
  () }
example : progOk polyCall = true := by native_decide
example : progRuns polyCall = true := by native_decide
example : runBinding polyCall "y" = some "S (S (S (S (S Z))))" := by native_decide

/-- The call still discriminates on the payload: instantiating at `Nat` and
    passing a `Bool` is rejected, so the type parameter is doing work rather than
    being waved through. -/
def polyBad : Term := prog{
  fn Poly (T : Type, x : T) -> T { x };
  let y = Poly(Nat, True);
  () }
example : progRejects polyBad "does not have its parameter type" = true := by native_decide

/-- (d) ONE generic `fn`, used at TWO different types in one program. -/
def polyTwice : Term := prog{
  fn Poly (T : Type, x : T) -> T { x };
  let y = Poly(Nat, 5);
  let b = Poly(Bool, True);
  () }
example : progOk polyTwice = true := by native_decide
example : progRuns polyTwice = true := by native_decide
example : runBinding polyTwice "y" = some "S (S (S (S (S Z))))" := by native_decide
example : runBinding polyTwice "b" = some "True" := by native_decide

/-- (e) A type parameter UNDER a formation — `List T` for a comptime `T` — which
    is the `List` arm and the call rule composing. -/
def polyList : Term := prog{
  fn PolyCons (T : Type, x : T, xs : List T) -> List T { Cons(x, xs) };
  let l = PolyCons(Nat, 5, Nil);
  () }
example : progOk polyList = true := by native_decide
example : progRuns polyList = true := by native_decide
example : runBinding polyList "l" = some "Cons (S (S (S (S (S Z))))) Nil" := by native_decide

/-- (f) The composite `new_with_capacity` wanted: a generic fill whose return
    type is `Array n T` at a SYMBOLIC length and a comptime element type. Both
    of the `Array` arm's premises are live here — `n : Nat` against a telescope
    σ, and `T : Type` against the comptime parameter. -/
def MkFillFn : Term := prog{
  λ (T : Type). λ (X : T). λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm T) {
    Z => Arr(),
    S (M) Rec => acons M X Rec } }
def MkFillTy : Term := prog{ Π (T : Type) → Π (X : T) → Π (N : Nat) → Array N T }
example : chkL MkFillFn MkFillTy = true := by native_decide
example : chkL MkFillTy U = true := by native_decide

def polyArr : Term := prog{
  fn Fill (T : Type, x : T, n : Nat) -> Array n T { %MkFillFn T x n };
  () }
example : progOk polyArr = true := by native_decide

end Dllbc.Tests.Universe
