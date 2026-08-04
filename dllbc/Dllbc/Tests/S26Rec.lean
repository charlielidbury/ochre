import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S26Seal

/-!
# §26 (M26-C) — effectful recursors: the executing machine first

Phase C of the `fn`/λ unification (`docs/combining-fns.md` §7). §12 decision 7 is
explicit about the order — "the executing machine is built first or in lockstep,
never after" — and this file is that half: **ι-reduction of a recursor whose arms
are BODIES**, with the differential running from the first commit.

## The two forms

  * `Term.lamR` / `Val.rfn` — **the runtime λ**, `λ(x, y){ … }`: named binders and
    a *body*. Phase A could not build it ("a λ whose body is a runtime body has no
    `Val` representation"), and the reason it needs a second former rather than a
    second rule is that a body reaches its binders through Ω — a match scrutinizes
    a `Var`, `&mut x` roots a place at a `Var` — and a de Bruijn index names no
    slot. So the pure λ substitutes and this one binds.
  * `applyR` — ⇒-application of a function value, which is where the three rules
    meet: β for a pure λ, bind-and-run for a runtime λ, and **ι with the arm
    applied as a body** for a recursor at a constructor scrutinee.

## What `ih` is, mechanically

`natRec P z s (S m) v … ↦ s m ⟨natRec P z s m⟩ v …`, and the second argument is
`ih`: literally the recursor at the predecessor. It is a `Val` spine — closed,
marker-free, index-kind — which is §7 cost 2's "boring kind" of first-class
function value, with no environment capture anywhere in it. Calling it is
`.callV`, and the modes of its arguments come off the base arm's binder NAMES
(§6), because a borrow-moded Π has no value to read them off.

## Saturation is what keeps the borrows honest (§12 decision 4)

ι hands the arm the predecessor, the recursor at it, and everything the caller
still owed **in one application**, so no partial application ever exists holding a
borrow while it waits. That is not an accident of the encoding — it is the reason
§7 cost 3 demands spine application, arriving as the shape of the ι rule.
-/

open Dllbc
open Dllbc.Tests.S26Seal (ok rejects caller envOf)
open Dllbc.Tests.S9Diff (runExec symEnvs instanceOfC diffC)

namespace Dllbc.Tests.S26Rec

/-! ## §A. The runtime λ — the form, and the four things it is not -/

-- A1. Bind and run. The body is a body (a `let`, a constructor), and both
-- machines take the same rule: transparent application is β in the pure fragment
-- and inlining here, and neither machine verifies anything the other does not.
def a1 : Decl := decl{ fn caller () -> Unit
  { let g = λ(a) { let b = S(a); S(b) }; let r = g(1); () } }
example : ok a1 = true := by native_decide
example : diffC [] a1.body = true := by native_decide

-- A2. A runtime function value is INDEX-KIND, so calling it is a place read and
-- the slot survives. `ih` depends on this: `quicksort` recurses twice from one
-- arm, and a callee that moved out of its slot could be called once.
def a2 : Decl := decl{ fn caller () -> Unit
  { let g = λ(a) { S(a) }; let r = g(1); let s = g(4); () } }
example : ok a2 = true := by native_decide
example : diffC [] a2.body = true := by native_decide

/-! ### A3. CLOSED — checked, not assumed

    §7 cost 2 admits only closed function values, and constraint 5 defers
    environment capture wholesale. That is a premise this file has to enforce
    rather than describe: a body is entered under a fresh id window, so a free
    variable would not dangle — it would be silently rebound to whatever the shift
    lands on, which is capture arriving by accident. The rejection names the
    variable, and its twin (the same program with the value passed in) is
    accepted, so the refusal is about the CAPTURE and not about the program. -/

def a3bad : Decl := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a) { let z = n; () }; () } }
def a3ok : Decl := decl{ fn caller () -> Unit
  { let n = 3; let g = λ(a, m) { let z = m; () }; g(1, n); () } }
example : rejects a3bad "is none of its 1 binder(s)" = true := by native_decide
example : ok a3ok = true := by native_decide

-- A4. A NULLARY runtime λ is refused, and for a real ambiguity rather than
-- tidiness: `λ(){ e }` is a thunk, and at ι there is no way to tell "the arm
-- applied to no arguments" from "the arm with nothing owed" — `applyRest` has to
-- answer one way. Nothing in §7 wants a thunk.
def a4 : Decl := decl{ fn caller () -> Unit { let g = λ() { () }; () } }
example : rejects a4 "must bind at least one argument" = true := by native_decide

-- A5/A6. Saturation, both directions (§12 decision 4).
def a5 : Decl := decl{ fn caller () -> Unit { let g = λ(a, b) { () }; g(1); () } }
def a6 : Decl := decl{ fn caller () -> Unit { let g = λ(a) { () }; g(1, 2); () } }
example : rejects a5 "partial application" = true := by native_decide
example : rejects a6 "too many arguments" = true := by native_decide

/-! ### A7. ⇝ never meets the runtime λ

    The same grammar fact as the seal's (phase A, §A5), and it has to be asked of
    `readC` directly, because a rule that is merely never *reached* is not a rule
    that excludes anything. `.lamR` joins `&mut`, `:=`, `;`, `f(…)` and `seal` on
    `reflectC`'s list — this calculus's standing definition of the pure
    sub-grammar (§1.3). -/

def readCOn (t : Term) : String :=
  match (readC 1000 t).run (seedPure [] []) with
  | .ok v _ => "ACCEPTED " ++ v.pretty
  | .error e _ => e

example : strContains (readCOn (.lamR [⟨0, "x"⟩] (.var ⟨0, "x"⟩)))
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is where a mode flag consulted
-- at the top would have let it through.
example : strContains (readCOn (.app (.const "S") (.lamR [⟨0, "x"⟩] (.var ⟨0, "x"⟩))))
  "not in the comptime fragment" = true := by native_decide

/-! ## §B. ι with the arms as bodies — the executing machine (§7 cost 5)

    The rule §12 decision 7 puts first. A recursor whose arms are bodies is not a
    comptime object at all — `readC` refuses `.lamR`, and the motive is a
    borrow-moded Π which `readC` refuses too — so ⇒ evaluates the spine itself and
    ι-reduces it as **control flow**: the scrutinee's constructor selects an arm,
    and the arm runs, writing through borrows and calling.

    The programs below are fuel-threaded, which is §12 decision 8 rather than a
    convenience: `[v]`-style payload decrease has no recursor form, that regression
    is accepted, and fuel is the blessed interim. -/

/-- The motive, and the one place a runtime recursor's type is written by hand
    until phase D's macro derives it: `λ f. Π (v : &mut List Nat) → Unit`. It must
    be built in a ⇝ position (`pure{}`) — in a body, `&mut` is the borrow
    *operation*, not the borrow type. -/
def zeroMot : Term := pure{ λ (f : Nat). Π (v : &mut List Nat) → Unit }

/-- `zeroAll`, as a recursor term: walk the list through a mutable borrow and
    write `0` into every element, recursing on fuel.

    Everything §7 promises is in these four lines. The arms are bodies (`*hd := 0`
    is a write through a field reborrow). `ih` is a bound runtime variable holding
    a closed function value. The recursive call `ih(tl)` passes a BORROW as an
    argument — cost 2's "taking its borrows as arguments" — and is saturated, so
    no partial application ever holds `tl` while waiting. And there is no `[k]`
    guard anywhere: termination is by construction. -/

def b1 : Decl := decl{ fn caller () -> Unit {
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v) { () })
            (λ(f2, ih, v) { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(3, b);
  let y = x;
  () } }
example : ok b1 = true := by native_decide

/-- Read a slot back as the trace line it prints. -/
def slotOf (table : List Decl) (d : Decl) (name : String) : Option String :=
  (envOf table d).bind (fun e => (e.lookup name).map Val.pretty)

-- The list really is zeroed, in place, through the borrow — and the recursion
-- really did happen, since a body that never recursed would leave the tail alone.
example : slotOf [] b1 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- …and the recursor itself sits in an ordinary runtime slot as a VALUE: a closed
-- function value, which is what §7 cost 2 says the whole closure story has to be
-- for this phase. `@motive` is the erased motive slot (a borrow-moded Π has no ⇝
-- reading, and ι has no use for one — the checking side derives it from the
-- ascription instead, §7).
example : slotOf [] b1 "f" = some "natRec @motive λr(v){…} λr(f2, ih, v){…}" := by
  native_decide

-- B2. Surplus fuel is harmless: the list runs out first and the `Nil` arm returns.
def b2 : Decl := decl{ fn caller () -> Unit {
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v) { () })
            (λ(f2, ih, v) { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(9, b);
  let y = x;
  () } }
example : slotOf [] b2 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- B3. `listRec`, and a motive that is a function type — which is the shape §7
-- always has, since the trailing binders are what carry the borrows. The
-- structural recursion needs no fuel: the scrutinee is the list itself.
def bumpMot : Term := pure{ λ (l : List Nat). Π (v : &mut Nat) → Unit }
def b3 : Decl := decl{ fn caller () -> Unit {
  let l = Cons(7, Cons(8, Nil));
  let acc = 0;
  let a = &mut acc;
  let f = listRec Nat %bumpMot
            (λ(w) { () })
            (λ(h, t, ih, v) { *v := S(*v); ih(v); () });
  f(l, a);
  let r = acc;
  () } }
example : ok b3 = true := by native_decide
-- One increment per element: the arm ran twice, through the same borrow, handed
-- down the recursion and handed back.
example : slotOf [] b3 "r" = some "S (S Z)" := by native_decide

/-! ### B4. A recursor stuck on a symbolic scrutinee is a VALUE — and applying one
    is not this phase's rule

    Both halves matter and they are the same fact from two sides. Unapplied, the
    stuck spine is exactly what §7's convergence argument says a recursive
    occurrence must be — "`ih` is a bound Π-typed variable, literally the sealed
    view at the predecessor" — so it has to be a legal value, and B1 above shows
    it standing in a slot. APPLIED, it is arms-as-bodies checking, which is
    reachable through a seal and not through a call; refused here by name rather
    than by getting stuck somewhere downstream. -/

def b4 : Decl := decl{ fn b4 (fuel : Nat) -> Unit {
  let x = Cons(1, Nil);
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v) { () })
            (λ(f2, ih, v) { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(fuel, b);
  let y = x;
  () } }
example : rejects b4 "stuck on a symbolic scrutinee" = true := by native_decide

-- …and the same program without the application checks, because forming the
-- recursor is forming a value. This is the pair that says the rejection above is
-- about APPLYING a stuck recursor, not about writing one.
def b4v : Decl := decl{ fn b4v (fuel : Nat) -> Unit {
  let f = natRec %zeroMot
            (λ(v) { () })
            (λ(f2, ih, v) { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  () } }
example : ok b4v = true := by native_decide

/-! ## §C. The differential, under ONE relation (constraint 6, and inherited fact 4)

    Constraint 6 asks for both machines on every new value form, and §12 decision
    7 asks for the differential "running from the first commit". Both are here.

    **The relation was two relations and is now one.** M26-A extended `matchVal`
    for the seal (a σ inside arithmetic must be compared up to computation) but
    deliberately left its extension beside S9Diff's rather than folding them
    together, recording that neither was a superset: S9Diff's had the array-carve
    case and no computation, M26-A's computed and had no carve case. A program
    that carved AND computed would have been a false counterexample under either.
    `S9Diff.instanceOfC` is the merge — collect σ ↦ concrete through constructors,
    borrows AND carved segments, then instantiate, normalize, and compare with the
    segment-aware matcher — and the three groups below are what say the merge kept
    both halves and can still say NO. -/

-- C1. The recursor programs: every one of them, both machines, same Ω.
def recShapes : List Term := [a1.body, a2.body, b1.body, b2.body, b3.body, b4v.body]
example : recShapes.all (fun t => diffC [] t) = true := by native_decide

-- C2. THE CARVE HALF, kept. `S24Arrays`' callers are the programs that forced the
-- segment case into the relation in the first place ("the first array body handed
-- to `diffV2` reported a counterexample, and it was a FALSE one"): a checking-mode
-- release leaves `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where the concrete run is
-- `[3, 9, 2]`. They stay green under the merged relation, so computation was added
-- without costing the fold.
example : Tests.S24Arrays.arrCallers.all
    (fun b => diffC Tests.S24Arrays.arrPool b) = true := by native_decide

-- C3. THE COMPUTATION HALF, kept: phase A's counterexample, where a seal puts a σ
-- inside ordinary arithmetic and the structural matcher reports a counterexample
-- that is not one.
example : diffC [] Tests.S26Seal.d1.body = true := by native_decide
example : Tests.S26Seal.diffOld [] Tests.S26Seal.d1.body = false := by native_decide

/-! ### C4. Harness liveness — the relation must be able to say NO about a RECURSOR

    A counterexample-finder that has never found its counterexample is unvalidated
    (S9Diff's standing rule), and validating it on the seal's programs would say
    nothing about the ι rule. So: the symbolic side of `b1` (fuel 3, both elements
    zeroed) against the concrete side of the same program with fuel 1 — which
    zeroes the head and leaves the tail at 2. Same slots, same shapes, one
    genuinely different value. -/

def b1short : Decl := decl{ fn caller () -> Unit {
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v) { () })
            (λ(f2, ih, v) { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(1, b);
  let y = x;
  () } }
-- The mutant is a real program and a different one: it stops after the head.
example : slotOf [] b1short "y" = some "Cons Z (Cons (S (S Z)) Nil)" := by native_decide

example :
  (match symEnvs false [] b1.body, runExec [] b1short.body with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => true) = false := by native_decide
-- …and YES to the honest pairing, so the NO above is discrimination rather than a
-- relation that cannot see recursor programs at all.
example :
  (match symEnvs false [] b1.body, runExec [] b1.body with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => false) = true := by native_decide

/-! ## §D. A limitation, pinned rather than left to be met

    A runtime recursor needs a **function motive** — which is §7's shape anyway,
    since the trailing binders are what carry the borrows. At a DATA motive
    (`λ l. Nat`) the arms have no trailing binders, so `ih` is not a function but
    the recursor-at-the-predecessor itself, handed to the arm as a value; the arm
    stores it, and the pure fragment cannot reduce it afterwards, because its own
    arm is a body and `whnfV` has no rule for applying one.

    The result is a stuck spine rather than a wrong answer — both machines produce
    the same thing, so this is not a differential failure — and the audit rejects
    it when it tries to type the result. Pinned so the phase-D agent meets a test
    rather than a surprise, with the honest reading beside it: a recursor whose
    motive is not a function type has ordinary terms for arms, and the PURE
    recursor already computes those. -/

def lenMot : Term := pure{ λ (l : List Nat). Nat }
def d1 : Decl := decl{ fn caller () -> Nat {
  let l = Cons(7, Cons(8, Nil));
  let f = listRec Nat %lenMot Z (λ(h, t, ih) { S(ih) });
  f(l) } }
example : rejects d1 "cannot type neutral" = true := by native_decide

end Dllbc.Tests.S26Rec
