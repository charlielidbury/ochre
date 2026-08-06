import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S24Arrays
import Dllbc.Tests.S26Seal
import Dllbc.Tests.S23Direct

/-!
# §26 (M26-C) — effectful recursors: the executing machine first

Phase C of the `fn`/λ unification (`docs/combining-fns.md` §7). §12 decision 7 is
explicit about the order — "the executing machine is built first or in lockstep,
never after" — and this file is that half: **ι-reduction of a recursor whose arms
are BODIES**, with the differential running from the first commit.

## The two forms

  * `Term.lamR` / `Val.rfn` — **the runtime λ**, `λ(x : τ, y : υ){ … }`: named binders and
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
open Dllbc.Tests.S9Diff (runExec symEnvs instanceOfC diffC)
open Dllbc.StdLemmas (id_congr)

namespace Dllbc.Tests.S26Rec

/-! ## The declared side's two verdicts

    §E compares a DECLARED function against its sealed twin, so it needs the
    verdict of a `FnDef` — the one thing in this file that is not a program, and
    deliberately so (a declaration is what the pair is comparing against). These
    used to be borrowed from `S26Seal`, which had them because everything there
    was a declaration; that file is programs now (M28 ν) and has none, so the file
    that still needs them owns them. -/

def ok (d : FnDef) (table : List FnDef := [d]) : Bool := Migrate.progOkOf d table
def rejects (d : FnDef) (needle : String) (table : List FnDef := [d]) : Bool :=
  Migrate.progRejectsOf d needle table

/-! ## §A. The runtime λ — the form, and the four things it is not -/

-- A1. Bind and run. The body is a body (a `let`, a constructor), and both
-- machines take the same rule: transparent application is β in the pure fragment
-- and inlining here, and neither machine verifies anything the other does not.
def a1 : Term := prog{ let g = λ(a : Nat) { let b = S(a); S(b) }; let r = g(1); () }
example : progOk a1 = true := by native_decide
example : diffC [] a1 = true := by native_decide

-- A2. A runtime function value is INDEX-KIND, so calling it is a place read and
-- the slot survives. `ih` depends on this: `quicksort` recurses twice from one
-- arm, and a callee that moved out of its slot could be called once.
def a2 : Term := prog{ let g = λ(a : Nat) { S(a) }; let r = g(1); let s = g(4); () }
example : progOk a2 = true := by native_decide
example : diffC [] a2 = true := by native_decide

/-! ### A3. CLOSED — checked, not assumed

    §7 cost 2 admits only closed function values, and constraint 5 defers
    environment capture wholesale. That is a premise this file has to enforce
    rather than describe: a body is entered under a fresh id window, so a free
    variable would not dangle — it would be silently rebound to whatever the shift
    lands on, which is capture arriving by accident. The rejection names the
    variable, and its twin (the same program with the value passed in) is
    accepted, so the refusal is about the CAPTURE and not about the program. -/

def a3bad : Term := prog{ let n = 3; let g = λ(a : Nat) { let z = n; () }; () }
def a3ok : Term := prog{ let n = 3; let g = λ(a : Nat, m : Nat) { let z = m; () }; g(1, n); () }
example : progRejects a3bad "is none of its 1 binder(s)" = true := by native_decide
example : progOk a3ok = true := by native_decide

-- A4. A NULLARY runtime λ is refused, and for a real ambiguity rather than
-- tidiness: `λ(){ e }` is a thunk, and at ι there is no way to tell "the arm
-- applied to no arguments" from "the arm with nothing owed" — `applyRest` has to
-- answer one way. Nothing in §7 wants a thunk.
def a4 : Term := prog{ let g = λ() { () }; () }
example : progRejects a4 "must bind at least one argument" = true := by native_decide

-- A5/A6. Saturation, both directions (§12 decision 4).
def a5 : Term := prog{ let g = λ(a : Nat, b : Nat) { () }; g(1); () }
def a6 : Term := prog{ let g = λ(a : Nat) { () }; g(1, 2); () }
example : progRejects a5 "partial application" = true := by native_decide
example : progRejects a6 "too many arguments" = true := by native_decide

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

example : strContains (readCOn (.lamR [(⟨0, "x"⟩, .const "Nat")] (.var ⟨0, "x"⟩)))
  "not in the comptime fragment" = true := by native_decide
-- …including buried inside a pure former, which is where a mode flag consulted
-- at the top would have let it through.
example : strContains (readCOn (.app (.const "S") (.lamR [(⟨0, "x"⟩, .const "Nat")] (.var ⟨0, "x"⟩))))
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

def b1 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(3, b);
  let y = x;
  () }
example : progOk b1 = true := by native_decide

/-- Read a slot back as the trace line it prints. -/
def slotOf (t : Term) (name : String) : Option String :=
  match tailEnvs t with
  | [.ok e] => (e.lookup name).map Val.pretty
  | _ => none

-- The list really is zeroed, in place, through the borrow — and the recursion
-- really did happen, since a body that never recursed would leave the tail alone.
example : slotOf b1 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- …and the recursor itself sits in an ordinary runtime slot as a VALUE: a closed
-- function value, which is what §7 cost 2 says the whole closure story has to be
-- for this phase. `@motive` is the erased motive slot (a borrow-moded Π has no ⇝
-- reading, and ι has no use for one — the checking side derives it from the
-- ascription instead, §7).
example : slotOf b1 "f" = some "natRec @motive λr(v){…} λr(f2, ih, v){…}" := by
  native_decide

-- B2. Surplus fuel is harmless: the list runs out first and the `Nil` arm returns.
def b2 : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(9, b);
  let y = x;
  () }
example : slotOf b2 "y" = some "Cons Z (Cons Z Nil)" := by native_decide

-- B3. `listRec`, and a motive that is a function type — which is the shape §7
-- always has, since the trailing binders are what carry the borrows. The
-- structural recursion needs no fuel: the scrutinee is the list itself.
def bumpMot : Term := pure{ λ (l : List Nat). Π (v : &mut Nat) → Unit }
def b3 : Term := prog{
  let l = Cons(7, Cons(8, Nil));
  let acc = 0;
  let a = &mut acc;
  let f = listRec Nat %bumpMot
            (λ(w : &mut Nat) { () })
            (λ(h : Nat, t : List Nat, ih : Π (v : &mut Nat) → Unit, v : &mut Nat)
               { *v := S(*v); ih(v); () });
  f(l, a);
  let r = acc;
  () }
example : progOk b3 = true := by native_decide
-- One increment per element: the arm ran twice, through the same borrow, handed
-- down the recursion and handed back.
example : slotOf b3 "r" = some "S (S Z)" := by native_decide

/-! ### B4. A recursor stuck on a symbolic scrutinee is a VALUE — and applying one
    is not this phase's rule

    Both halves matter and they are the same fact from two sides. Unapplied, the
    stuck spine is exactly what §7's convergence argument says a recursive
    occurrence must be — "`ih` is a bound Π-typed variable, literally the sealed
    view at the predecessor" — so it has to be a legal value, and B1 above shows
    it standing in a slot. APPLIED, it is arms-as-bodies checking, which is
    reachable through a seal and not through a call; refused here by name rather
    than by getting stuck somewhere downstream. -/

def b4 : Term := prog{ fn b4 (fuel : Nat) -> Unit {
  let x = Cons(1, Nil);
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(fuel, b);
  let y = x;
  () }; () }
example : progRejects b4 "stuck on a symbolic scrutinee" = true := by native_decide

-- …and the same program without the application checks, because forming the
-- recursor is forming a value. This is the pair that says the rejection above is
-- about APPLYING a stuck recursor, not about writing one.
def b4v : Term := prog{
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  () }
example : progOk b4v = true := by native_decide

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
def recShapes : List Term := [a1, a2, b1, b2, b3, b4v]
example : recShapes.all (fun t => diffC [] t) = true := by native_decide

-- C2. THE CARVE HALF, kept. `S24Arrays`' callers are the programs that forced the
-- segment case into the relation in the first place ("the first array body handed
-- to `diffV2` reported a counterexample, and it was a FALSE one"): a checking-mode
-- release leaves `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where the concrete run is
-- `[3, 9, 2]`. They stay green under the merged relation, so computation was added
-- without costing the fold.
-- (the pool went with M28 ν: each caller declares its own callee, so the table is
-- empty and the shape is one self-contained program.)
example : Tests.S24Arrays.arrCallers.all
    (fun b => diffC [] b) = true := by native_decide

-- C3. THE COMPUTATION HALF, kept: phase A's counterexample, where a seal puts a σ
-- inside ordinary arithmetic and the structural matcher reports a counterexample
-- that is not one.
-- (`d1` is a PROGRAM since M28 ν, so the body is the thing itself — the `.body`
-- projection went with the declaration that used to wrap it.)
example : diffC [] Tests.S26Seal.d1 = true := by native_decide
example : Tests.S26Seal.diffOld [] Tests.S26Seal.d1 = false := by native_decide

/-! ### C4. Harness liveness — the relation must be able to say NO about a RECURSOR

    A counterexample-finder that has never found its counterexample is unvalidated
    (S9Diff's standing rule), and validating it on the seal's programs would say
    nothing about the ι rule. So: the symbolic side of `b1` (fuel 3, both elements
    zeroed) against the concrete side of the same program with fuel 1 — which
    zeroes the head and leaves the tail at 2. Same slots, same shapes, one
    genuinely different value. -/

def b1short : Term := prog{
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  let f = natRec %zeroMot
            (λ(v : &mut List Nat) { () })
            (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
               { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } });
  f(1, b);
  let y = x;
  () }
-- The mutant is a real program and a different one: it stops after the head.
example : slotOf b1short "y" = some "Cons Z (Cons (S (S Z)) Nil)" := by native_decide

example :
  (match symEnvs [] b1, runExec [] b1short with
   | [.ok se], .ok ce => instanceOfC se ce
   | _, _ => true) = false := by native_decide
-- …and YES to the honest pairing, so the NO above is discrimination rather than a
-- relation that cannot see recursor programs at all.
example :
  (match symEnvs [] b1, runExec [] b1 with
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
def d1 : Term := prog{ fn caller () -> Nat {
  let l = Cons(7, Cons(8, Nil));
  let f = listRec Nat %lenMot Z (λ(h : Nat, t : List Nat, ih : Nat) { S(ih) });
  f(l) }; () }
example : progRejects d1 "cannot type neutral" = true := by native_decide

/-! ## §E. The audit relocation — checking a seal IS `checkFn`'s content (§5.4)

    Phase A's third pinned limitation, and the one the whole ensures discipline
    rests on. `.seal t u` with a borrow-moded Π `u` cannot be checked by
    `hasType`: a Π with `&mut` binders is a *function signature*, `readC` refuses
    `borrowT` outright, and there is no value for `hasType` to be asked about. The
    check is §5.4's audit — seed `u`'s telescope, explore the body one path per
    symbolic branch, audit each path at return with exit snapshots and
    obligations — which is exactly `checkFn`'s content, reached from the node
    instead of from a declaration.

    **What decides which rule fires is the sealed TERM, not the type.** A runtime
    λ takes the audit; everything else takes phase A's `readC`-then-`hasType`
    unchanged, which is what keeps §12-open-4's identity intact (§B of `S26Seal`
    still passes, pair for pair). `checkFn` is untouched and still checks every
    `FnDef` in the corpus: content moved, nothing was deleted (J1). -/

def unitSeal : Term := pure{ Π (v : &mut List Nat) → Unit }
def pinSeal : Term := pure{ Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 Nil) }

-- E1. The rule, end to end: a sealed function taking a borrow is checked at the
-- node, called through its σ by the table's own call rule, and executes.
def e1 : Term := prog{
  let f = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
  let x = Cons(1, Nil);
  let b = &mut x;
  f(b);
  let y = x;
  () }
example : progOk e1 = true := by native_decide
example : diffC [] e1 = true := by native_decide

/-! ### E2. The ensures, threaded through the seal (§5 point 4)

    The M23 shape, with the callee sealed instead of declared: the caller holds a
    borrow, hands a reborrow to the sealed function, and RETURNS the equation it
    got back as its own postcondition. That only type-checks if the σ the call
    re-minted for the payload is the same σ the caller's exit `*v` reads — §5.4's
    caller-side σ-sharing — so this pins the whole ensures pipeline through a
    sealed callee, not merely that the seal was accepted.

    The sealed body has to PRODUCE the proof, which is the thing a `Unit`-sealed
    body does not have to do. That is what makes the pair below the real test of
    "what you keep is what you write". -/

def e2 : Term := prog{ fn caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let f = (λ(w : &mut List Nat) { *w := Cons(9, Nil); Refl } : %pinSeal);
  f(&mut *v) }; () }
example : progOk e2 = true := by native_decide

-- The same program, the same body, sealed at `Unit`: the caller gets nothing back
-- and cannot state its own postcondition. Sound, honest, useless — one ascription
-- apart, which is §5 point 4 with nothing left to interpret.
def e2none : Term := prog{ fn caller (v : &mut List Nat) -> Id (List Nat) (*v) (Cons 9 Nil) {
  let f = (λ(w : &mut List Nat) { *w := Cons(9, Nil); () } : %unitSeal);
  f(&mut *v) }; () }
example : progRejects e2none "does not have return type" = true := by native_decide

/-! ### E3. The negative controls, one per branch of the new rule -/

-- The body does not establish the ensures: rejected AT THE SEAL by the audit, and
-- the message is the audit's own — `Refl` does not inhabit the equation the
-- ascription promised.
def e3a : Term := prog{
  let f = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal); () }
example : progRejects e3a "does not have return type" = true := by native_decide

-- The body leaves a hole in its argument borrow: the OBLIGATION audit, which is
-- the half of §5.4 the ensures check does not cover, and which only exists
-- because the seal now seeds a telescope.
def e3b : Term := prog{
  let f = (λ(v : &mut List Nat) { let l = *v; () } : %unitSeal); () }
example : progRejects e3b "holds a hole (⊥) at return" = true := by native_decide

-- Mode disagreement: the λ's binder is lowercase where the ascription binds
-- comptime. §6 could be stated twice here and disagree, so it is checked — and
-- this is the callee-side half of phase B's "the ascription is the contract"
-- (F3 settled the caller side).
def cmpSeal : Term := pure{ Π (N : Nat) → Nat }
def e3c : Term := prog{
  let f = (λ(n : Nat) { S(n) } : %cmpSeal); () }
example : progRejects e3c "the ascribed type binds it as comptime" = true := by native_decide
-- …and its twin, one character apart, is accepted.
def e3cok : Term := prog{
  let f = (λ(N : Nat) { Z } : %cmpSeal); () }
example : progOk e3cok = true := by native_decide

-- Arity disagreement (§12 decision 4, at the ascription rather than at a call).
def e3d : Term := prog{
  let f = (λ(v : &mut List Nat, w : Nat) { () } : %unitSeal); () }
example : progRejects e3d "no Π binder left for it" = true := by native_decide

-- Sealing something that is NOT a runtime λ at a function signature — phase A's
-- A4, now refused for the reason instead of for the phase.
def e3e : Term := prog{
  let f = (λ (x : Nat). x : %unitSeal); () }
example : progRejects e3e "the sealed term must be a runtime λ" = true := by native_decide

/-! ### E4. FRAME ISOLATION — the sealed body's effects stay inside the check

    Phase A evaluated a seal's body IN PLACE and recorded that "a sealed FUNCTION
    body will want frame isolation, and that arrives with phase C's audit
    relocation". This is that debt paid, and it is directly testable: the sealed
    body below borrows and writes, and the caller's `x` is untouched by any of it
    — still owned, still `Cons 1 Nil`, movable afterwards. A body checked in place
    would have consumed something of the caller's. -/

def e4 : Term := prog{
  let x = Cons(1, Nil);
  let f = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
  let y = x;
  () }
example : progOk e4 = true := by native_decide
example : slotOf e4 "y" = some "Cons (S Z) Nil" := by native_decide

/-! ### E5. THE SMELL TEST, extended to borrow-moded seals

    §12-open-4 asked whether the audit of a borrow-FREE sealed λ degenerates to
    exactly `hasType`; phase A discharged that as an identity over a 16-pair
    battery. The borrow-moded question is its sibling and the one this phase owes:
    does the audit of a sealed λ agree with **`checkFn`'s verdict on the same
    function declared**? If §7 is right that `fn` is a macro, it must — the two
    are supposed to be the same check reached by two routes.

    Discharged as an identity over hand-written twins rather than a spot check,
    with both polarities so it cannot hold vacuously. Each pair is the same
    telescope, the same return type and the same body, written once as a `FnDef`
    and once as `(λ(… : …){ … } : Π …)`. -/

def pushD : Term := prog{ fn pushD (e : Nat, v : &mut List Nat) -> Unit
  { let tail = *v; *v := Cons(e, tail); () }; () }
def pushS : Term := prog{ let f = (λ(e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut List Nat) → Unit); () }

/-- The `old *v` shape: an ensures relating the EXIT payload to the ENTRY one,
    which is the convention M23's whole corpus is written in and the reason the
    seal has to seed `entrySyms` as well as `exitSyms`. -/
def consD : Term := prog{ fn consD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(9, t); Refl }; () }
def consS : Term := prog{ let f = (λ(v : &mut List Nat) { let t = *v; *v := Cons(9, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The spec lie: the body conses `8` where the ensures says `9`. -/
def lieD : Term := prog{ fn lieD (v : &mut List Nat)
  -> Id (List Nat) (*v) (Cons 9 (old *v))
  { let t = *v; *v := Cons(8, t); Refl }; () }
def lieS : Term := prog{ let f = (λ(v : &mut List Nat) { let t = *v; *v := Cons(8, t); Refl } : Π (v : &mut List Nat) → Id (List Nat) (*v) (Cons 9 (old *v))); () }

/-- The obligation lie: the payload is taken and never refilled. -/
def holeD : Term := prog{ fn holeD (v : &mut List Nat) -> Unit { let l = *v; () }; () }
def holeS : Term := prog{ let f = (λ(v : &mut List Nat) { let l = *v; () } : Π (v : &mut List Nat) → Unit); () }

/-- Each pair: the `fn` STATEMENT and the hand-written sealed λ of the same
    function. Both sides are programs (M28 ι for the seal, M28 D5 for the `fn`),
    which is what the pair was always comparing — §7 says `fn` is a macro over the
    seal, and this is that sentence as two verdicts. -/
def twins : List (Term × Term) :=
  [ (pushD, pushS), (consD, consS), (lieD, lieS), (holeD, holeS) ]

-- THE SMELL TEST: the `fn` lowering's audit and the hand-written seal's agree,
-- pair for pair. (It used to compare against `checkFn`; that path died in M27-δ
-- and the surviving comparison is the one §7 is actually about.)
example : twins.all (fun p => progOk p.1 == progOk p.2) = true := by native_decide
-- …and it is not vacuous: both verdicts occur, so the identity above is pinning
-- agreement rather than a constant function.
example : (twins.any (fun p => progOk p.1) && twins.any (fun p => !progOk p.1)) = true := by
  native_decide
-- …and the rejections agree on WHY, not merely that. A sealed body that lies
-- about its ensures and a `fn` that lies about the same ensures are refused by the
-- same audit with the same message — which is what says the check was relocated
-- rather than reimplemented.
example : (progRejects lieD "does not have return type" && progRejects lieS "does not have return type")
  = true := by native_decide
example : (progRejects holeD "holds a hole (⊥) at return" && progRejects holeS "holds a hole (⊥) at return")
  = true := by native_decide

/-! ## §F. Arms as bodies — the CHECKING side (§7 cost 1)

    "Runtime-moded recursor motives are the one real kernel addition: arms contain
    writes, calls and borrows — *bodies* — so the checker must symbolically execute
    an arm as a body with an abstract `ih : Π` in scope. The content of that
    judgment is exactly today's guard-checking; the plumbing is new."

    Three things make it work and each is worth naming, because each turned out to
    be something the earlier phases already had:

      * **The motive is derived from the signature.** Peel one Π off the
        ascription and the codomain IS the motive's body. §7 promised the macro
        would need no inference; the checker needs none either.
      * **Each arm is checked once, at its own constructor** — `Z` and `S k` ARE
        the split, and the motive instantiated at each is the goal. No driver
        change: `exploreMatch` forks paths because a runtime match does not know
        its scrutinee, while a recursor's arms come labelled.
      * **`ih` is a σ with a signature and no body**, which is the sealed self-view
        at the predecessor. It is seeded by the same rule that seeds any Π-typed
        parameter and called by the same rule that calls any sealed function —
        §7's "self-ensures FORCED rather than stipulated", as plumbing. -/

def zeroSeal : Term := pure{ Π (fuel : Nat) → Π (v : &mut List Nat) → Unit }


def f1 : Term := prog{
  let f = (natRec %zeroMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  f(3, b);
  let y = x;
  () }
example : progOk f1 = true := by native_decide

-- The seal is what makes it opaque: the caller learns only `Unit`, so the list it
-- gets back is an EXISTENTIAL — §2.2's forgetting, now reached through a recursor
-- rather than through a declaration. (Asserted as "a σ" rather than as a σ id: the
-- id is a counter, and pinning it would make this test fail for reasons that have
-- nothing to do with what it is about.)
example : (slotOf f1 "y").map (fun s => s.take 1) = some "σ" := by native_decide

-- …and the SAME program executes, with the recursion really running: both
-- machines, one differential.
example : diffC [] f1 = true := by native_decide
example :
  (match Dllbc.Tests.S9Diff.runExec [] f1 with
   | .ok e => (e.lookup "y").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

/-! ### F2. The motive is derived, and a written one that disagrees is refused

    §7 makes the motive redundant — it is the sealed Π with the scrutinee peeled
    off — so the checker derives it and compares. Syntactically, and that is
    forced rather than lazy: a motive over a borrow-moded Π has no `Val`, hence no
    conversion to be compared up to. Phase D's macro will derive it, so the
    comparison is free there; a hand-written mismatch is told what was expected. -/

def wrongMot : Term := pure{ λ (f : Nat). Π (v : &mut List Nat) → Nat }
def f2 : Term := prog{
  let f = (natRec %wrongMot
                 (λ(v : &mut List Nat) { () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Nat, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f2 "not the one its ascription derives" = true := by native_decide

/-! ### F3. An arm that does not establish the motive is rejected AT ITS OWN ARM

    The base arm below returns without restoring what it took, so its obligation
    audit fails — and the step arm is untouched and would pass. That is what says
    the arms are checked *separately*, each at its own instantiation, rather than
    the whole recursor being checked as one lump. -/

def f3 : Term := prog{
  let f = (natRec %zeroMot
                 (λ(v : &mut List Nat) { let l = *v; () })
                 (λ(f2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat)
                    { match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %zeroSeal);
  () }
example : progRejects f3 "holds a hole (⊥) at return" = true := by native_decide

/-! ## §G. THE CONVERGENCE TEST — `split_off`, declared and as a sealed recursor

    §7's claim is not that recursors are expressive enough in principle; it is that
    `fn` **is a macro** over a sealed recursor binding, so a real M23 function must
    check the same way both ways. `split_off` is the subject because it is real:
    it recurses, it mutates through a borrow, it hands a reborrow to its own
    recursive call, its return type is a Σ-chain of two equations relating the exit
    and entry snapshots, and it has a dead branch discharged by ex falso.

    It also needs no fuel, and that is worth noticing rather than glossing:
    §12 decision 8 accepts a naturalness regression for `[v]`-style *payload*
    decrease, but `split_off` recurses on its INDEX, which is a `Nat` — so the
    recursor form is `natRec` on the very argument `[i]` already named, and the
    elaboration is the mechanical one §7 describes with nothing threaded through.

    The two forms below are the same function. `S23Direct.splitOff` is the
    declared one, checked by `checkFn` with the `[i]` guard policing its self-call;
    this one is `.seal ⟨natRec …⟩ ⟨Π …⟩`, checked at the node with `ih` as an
    abstract signature and no guard anywhere. Both are accepted, and the second is
    what §7 says the first should elaborate to. -/

def splitTy : Term := pure{
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
         → Id (List Nat) ret (drop i (old *v)) }

def splitMot : Term := pure{
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
         → Id (List Nat) ret (drop i (old *v)) }

/-- `split_off` as §7 says a `fn` elaborates. The body is `S23Direct.splitOff`'s,
    transcribed with one change and one deletion: the self-call
    `split_off(&mut *tl, i2, hi)` becomes `ih(&mut *tl, hi)` — the scrutinee
    argument is gone, because ι supplies it — and the `match i` disappears into the
    two arms. -/
def splitSealed : Term := prog{
  let f = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i2 (old *v)))
                     → Id (List Nat) ret (drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = take i2 (*tl);
             let p = ih(&mut *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTy);
  () }

-- THE CONVERGENCE. ~~The declared function and the sealed recursor both check.~~
-- Half of that claim retired with `checkFn` (M27-δ): there is no declared path to
-- converge WITH, and §7's "fn is a macro" is no longer a comparison between two
-- checkers but the only elaboration there is. What survives is the half that was
-- always the interesting one — this hand-written sealed recursor and
-- `S23Direct.splitOff` are the same function, and `S26Fn` §"the macro's output is
-- α-equal to the hand-written recursor" is where that identity is now asserted.
example : progOk splitSealed = true := by native_decide

/-! ### G2. Not vacuous — the sealed form rejects the same lies the declared one does

    `S23Direct` guards `splitOff` with four twins (three spec lies and a body lie)
    so that its acceptance is not a coincidence. The sealed form has to be guarded
    the same way, or "both check" would be a much weaker statement than it looks.
    The body lie is the sharper of the two here: it breaks the congruence in the
    `Cons` arm, which is the arm `ih` lives in. -/

def splitMotLie : Term := pure{
  λ (i : Nat). Π (v : &mut List Nat) → Π (hi : Le i (len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (drop i (old *v)))
         → Id (List Nat) ret (drop i (old *v)) }
def splitTyLie : Term := pure{
  Π (i : Nat) → Π (v : &mut List Nat) → Π (hi : Le i (len *v))
    → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (drop i (old *v)))
         → Id (List Nat) ret (drop i (old *v)) }

-- A SPEC lie: the prefix conjunct claims `drop` where the body leaves `take`.
def splitSpecLie : Term := prog{
  let f = (natRec %splitMotLie
      (λ(v : &mut List Nat, hi : Le Z (len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (drop i2 (old *v)))
                     → Id (List Nat) ret (drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = take i2 (*tl);
             let p = ih(&mut *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTyLie);
  () }
-- Caught on the BASE arm (`Pair σ (Pair Refl Refl)` against `Id Nil σ`), exactly
-- where `S23Direct` says its spec lies are caught.
example : progRejects splitSpecLie "does not have return type" = true := by native_decide

-- A BODY lie: the `Cons` arm forgets to restore the head, so the prefix conjunct
-- is false on the recursive path — the arm `ih` lives in.
def splitBodyLie : Term := prog{
  let f = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i2 (old *v)))
                     → Id (List Nat) ret (drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = take i2 (*tl);
             let p = ih(&mut *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(h1, h2)) } } } } } }) : %splitTy);
  () }
-- Caught on the STEP arm — the one `ih` lives in, and the one the spec lies leave
-- untested. Same division of labour as the declared function's four twins, which
-- is what makes "both check" a claim about the same coverage and not just the same
-- verdict.
example : progRejects splitBodyLie "does not have return type" = true := by native_decide

/-! ## §H. `bad()`, twice — the incoherence, probed rather than assumed

    §8's guard exists because a self-call admitted at its own declared return type
    with nothing decreasing proves anything: `fn bad () -> Id Nat Z (S Z) { bad() }`.
    §7 claims the guard EVAPORATES for recursor-expressed functions, so the two
    ways `bad()` could come back have to be checked directly rather than argued
    away. Constraint 3 is the standard: "the `bad()` self-proof stays unwritable by
    construction". -/

/-! ### H1. An unsealed recursive λ is UNWRITABLE, which is the honest form of
    "it has no checking story"

    §7 derives that an unsealed recursive λ is incoherent at checking (unfolding
    self never terminates) and constraint 3 requires it to stay unwritable. It
    does, and the mechanism is not a rule about recursion at all: **the binding is
    not in scope in its own right-hand side.** `let g = λ(n : Nat){ g(n) }` binds `g` for
    what FOLLOWS, so the `g` inside the λ names nothing lexical and falls through
    to the declaration table, where it is not. §8 predicts exactly this — "a
    let-chain cannot reference downward, so no forward references falls out,
    consistent by construction with mutual recursion being rejected" — and
    self-reference is the degenerate downward reference.

    **This control had to be made to bite.** Written as a `let` that is never used,
    the program is ACCEPTED, and looks like a working negative test: the λ's body
    is never demanded, so nothing ever resolves the name. That is phase A's finding
    (a negative test must be per DEMAND SITE) arriving a third time, and it is why
    both forms below make something ask. -/

-- Demanded by APPLYING it: the body runs and the name resolves against nothing.
def h1 : Term := prog{
  let g = λ(n : Nat) { g(n) };
  g(1);
  () }
example : progRejects h1 "unknown function 'g'" = true := by native_decide

-- Demanded by SEALING it, which is the form §7 contrasts with: sealing is what
-- makes a body get checked, and it is also what a recursive function needs — but
-- the seal does not put the binding in its own scope either. Recursion has to come
-- from the recursor, which is the point of §7.
def h1s : Term := prog{
  let g = (λ(n : Nat) { g(n) } : Π (n : Nat) → Nat);
  () }
example : progRejects h1s "unknown function 'g'" = true := by native_decide

-- The vacuous version, pinned as the trap it is rather than deleted: the same
-- program with nothing demanding the λ's body is accepted, and tests nothing.
def h1vacuous : Term := prog{ let g = λ(n : Nat) { g(n) }; () }
example : progOk h1vacuous = true := by native_decide

/-! ### H2. A sealed recursor whose motive promises a falsehood is rejected at its
    own audit — AND the rejection comes from the base arm

    The `bad()` shape as a recursor: a motive claiming `Id Nat Z (S Z)` at every
    level. The step arm goes through, and that is not a bug — `ih` really does hand
    it the claim at the predecessor, which is exactly the self-ensures §7 says is
    forced. What stops it is the BASE arm, which has no `ih` and must inhabit the
    claim outright. That is structural induction doing the job §8's guard was doing
    by hand, and it is why the guard can evaporate: the side condition is not
    checked, it is unnecessary.

    The pair below is what says so. `h2` is the whole recursor and is rejected;
    `h2step` is the same step arm sealed on its own at the type `ih` gave it —
    `Π (u : Unit) → Id Nat Z (S Z)` assumed, the same returned — and is ACCEPTED,
    which is the assumption discharged honestly rather than a hole. -/

def badMot : Term := pure{ λ (n : Nat). Π (u : Unit) → Id Nat Z (S Z) }
def badTy : Term := pure{ Π (n : Nat) → Π (u : Unit) → Id Nat Z (S Z) }

def h2 : Term := prog{
  let f = (natRec %badMot
                 (λ(u : Unit) { Refl })
                 (λ(n2 : Nat, ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { ih(u) }) : %badTy);
  () }
example : progRejects h2 "does not have return type" = true := by native_decide

-- The step arm alone, with the predecessor's claim as a HYPOTHESIS: accepted. So
-- the rejection above is located at the base case and nowhere else — `bad()` dies
-- because `Id Nat Z (S Z)` has no proof at zero, not because a guard forbade the
-- recursion.
def h2step : Term := prog{
  let f = (λ(ih : Π (u : Unit) → Id Nat Z (S Z), u : Unit) { ih(u) } : Π (ih : Π (u : Unit) → Id Nat Z (S Z)) → Π (u : Unit) → Id Nat Z (S Z));
  () }
example : progOk h2step = true := by native_decide

/-! ## §I. `ih` at the wrong level — the guard's content surviving as TYPING

    §8's guard policed "the recursive call's argument is a strict structural
    predecessor". §7 says that becomes unnecessary, and this is the mechanism: `ih`
    is typed `P k` while the arm proves `P (S k)`, so an arm that tries to use the
    recursion at its OWN level has nothing to pass it. The check is not a
    comparison the checker performs; it is the type `ih` was given.

    The motive below carries a fuel bound, which is what makes the levels visible:
    `Hn : Le (len *v) n`. In the step arm `Hn : Le (len *v) (S n2)` and `ih` wants
    `Le (len *v) n2` — one successor apart, and no term bridges them. The accepted
    twin derives the predecessor's bound properly and passes THAT, so the rejection
    is about the level and not about the program being unwritable. -/

def bndMot : Term := pure{
  λ (n : Nat). Π (v : &mut List Nat) → Π (Hn : Le (len *v) n) → Unit }
def bndTy : Term := pure{
  Π (n : Nat) → Π (v : &mut List Nat) → Π (Hn : Le (len *v) n) → Unit }

-- The arm hands `ih` its OWN bound, `Le (len *v) (S n2)`, where `ih` binds
-- `Le (len *v) n2`. Refused, by the argument check at the abstract call.
def i1 : Term := prog{
  let f = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (len *v) Z) { () })
                 (λ(n2 : Nat,
                    ih : Π (v : &mut List Nat) → Π (Hn : Le (len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (len *v) (S n2)) { ih(&mut *v, Hn); () }) : %bndTy);
  () }
example : progRejects i1 "does not have its parameter type" = true := by native_decide

-- …and the twin that recurses at the predecessor's level is ACCEPTED — which is
-- what says the discipline is usable and not merely restrictive. Matching `v`
-- makes `*v` a `Cons`, so `len *v` is `S (len *tl)` and the arm's own
-- `Le (S (len *tl)) (S n2)` IS `Le (len *tl) n2` definitionally: the bound the
-- predecessor wants, obtained by the list getting shorter rather than by a lemma.
-- That is M14's bounds-cursor property, doing here exactly what §8's guard used to
-- do by comparing snapshots — except it is the TYPE, so nothing checks it.
def i2 : Term := prog{
  let f = (natRec %bndMot
                 (λ(v : &mut List Nat, Hn : Le (len *v) Z) { () })
                 (λ(n2 : Nat,
                    ih : Π (v : &mut List Nat) → Π (Hn : Le (len *v) n2) → Unit,
                    v : &mut List Nat, Hn : Le (len *v) (S n2))
                    { match v { Nil => (), Cons(hd, tl) => { ih(&mut *tl, Hn); () } } }) : %bndTy);
  () }
example : progOk i2 = true := by native_decide

/-! ## §J. The sealed `split_off`, RUN — the convergence closed at both arrows

    §G says the two forms check the same. This says the sealed one is a program:
    the same recursor, called concretely, splitting a real list, with the two
    machines agreeing. Without it the convergence would be a statement about the
    checker only, and §12 decision 7's whole point is that the executing machine is
    where this project's surprises live.

    `hi : Le 1 (len *v)` is supplied as `()`: `Le` computes, the payload is
    concrete, and `Le 1 2` reduces to `Unit`. That is the ordinary route — the
    bound holds by computation, not by citation. -/

def j1 : Term := prog{
  let f = (natRec %splitMot
      (λ(v : &mut List Nat, hi : Le Z (len *v))
         { let tail = *v; *v := Nil; Pair(tail, Pair(Refl, Refl)) })
      (λ(i2 : Nat,
         ih : Π (v : &mut List Nat) → Π (hi : Le i2 (len *v))
                → Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i2 (old *v)))
                     → Id (List Nat) ret (drop i2 (old *v)),
         v : &mut List Nat,
         hi : Le (S i2) (len *v)) {
         match v {
           Nil => botElim Unit hi,
           Cons(hd, tl) => {
             let y1 = take i2 (*tl);
             let p = ih(&mut *tl, hi);
             match p { Pair(rr, q) => match q { Pair(h1, h2) => {
               let c1 = id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a)
                          (*tl) y1 h1;
               Pair(rr, Pair(c1, h2)) } } } } } }) : %splitTy);
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &mut x;
  let r = f(1, b, ());
  let y = x;
  () }
example : progOk j1 = true := by native_decide

-- It really splits: after `split_off` at index 1 the borrow's payload keeps the
-- first element and the rest came back by value inside the returned Σ.
example :
  (match Dllbc.Tests.S9Diff.runExec [] j1 with
   | .ok e => (e.lookup "y").map Val.pretty
   | .error _ => none) = some "Cons (S Z) Nil" := by native_decide

-- …and the two machines agree on the whole final Ω.
example : diffC [] j1 = true := by native_decide

/-! ## §K. Both dispatch surfaces (the phase-B lesson, audited rather than assumed)

    Phase B's fence was DEAD until it was duplicated at the explore driver: a
    statement-position `match` or `let` never reaches `readR`'s own cases. So every
    rule this phase adds has to be checked at both surfaces rather than assumed to
    be reached.

    It is, and by construction rather than by duplication — which is worth stating
    as the reason and not just the outcome. Phase B's fence lived INSIDE `readR`'s
    `.matchE` and `.letIn` cases, which are exactly the two the driver bypasses.
    Every rule here is a different `readR` case (`.seal`, `.lamR`, `.callV`, the
    recursor spine), and the driver reaches all of them: through `.letIn`'s
    right-hand side, through `.seq`'s expression, and through the final-expression
    fall-through. The tests below put a seal and a recursor call at each of those
    three positions, INSIDE a branch of a symbolic match — which is where
    `pushContinuations` sends a real body and where phase B's rule went dark. -/

def k1 : Term := prog{ fn k1 (n : Nat) -> Unit {
  match n {
    Z => (),
    S(m) => {
      -- a seal as a `let` right-hand side, inside a branch
      let f = (λ(v : &mut List Nat) { *v := Cons(9, Nil); () } : %unitSeal);
      let x = Cons(1, Nil);
      let b = &mut x;
      -- a sealed call in statement position, inside a branch
      f(b);
      let y = x;
      () } } }; () }
example : progOk k1 = true := by native_decide

-- The negative twin at the same two positions: a body that lies about its ensures
-- is caught inside the branch, not skipped along with it.
def k2 : Term := prog{ fn k2 (n : Nat) -> Unit {
  match n {
    Z => (),
    S(m) => {
      let f = (λ(v : &mut List Nat) { *v := Cons(8, Nil); Refl } : %pinSeal);
      () } } }; () }
example : progRejects k2 "does not have return type" = true := by native_decide

-- …and a seal in FINAL-EXPRESSION position inside a branch, which is the third
-- route (`explore`'s fall-through to `readR`). The ascription here is borrow-free
-- because a DECLARED fn cannot yet return a borrow-moded Π — `checkFn` has no
-- reading for such a return type, which is a pre-existing limitation of the
-- declaration form and one §8 dissolves rather than fixes (a program is a term, so
-- there is no return type to read, only a `let`).
def natFn : Term := pure{ Π (n : Nat) → Nat }
def k3 : Term := prog{ fn k3 (n : Nat) -> %natFn {
  match n {
    Z => (λ(m : Nat) { Z } : %natFn),
    S(m) => (λ(k : Nat) { S(k) } : %natFn) } }; () }
example : progOk k3 = true := by native_decide

/-! ## §M (M27-P3). `ih` READ AS A VALUE — and the two machines disagree

    `indexKindV` classifies a runtime function value (`Val.rfn`) as index-kind, so
    reading one COPIES and leaves the owner intact. Its comment justified that with
    "copy-on-read is what makes a body able to recurse twice (`quicksort`'s two
    halves)". M27-P3 measured the claim by flipping the case to `false` and running
    the whole suite: **it stayed green**, so nothing exercised it. Writing the test
    that would exercise it found something better than an unexercised case.

    **The two machines answer differently, and the checking side is the one that
    cannot reach `.rfn` at all.** Binding `ih` to a local is REJECTED when checking
    and RUNS when executing:

      * Checking: `ih` is a **σ** whose signature lives in `St.fsig` — a borrow-moded
        Π has no `Val`, which is M26-C's founding fact — and `indexKindV`'s `.sym`
        case consults `sctx`, not `fsig`. No entry, so it takes the conservative
        default and MOVES. **This is now REFUSED at the read** (M27's third
        containment), rather than left to be noticed by whatever demanded the
        emptied slot afterwards.
      * Executing: `ih` really is a `Val.rfn` in a slot, the `.rfn` case fires, and
        the read copies.

    So the comment was wrong twice over: copy-on-read is not what serves quicksort's
    two recursive calls (`.callV` LOCATES its callee and never moves it — M26-E),
    and the case it justifies is unreachable from the machine the comment is written
    beside. It is a correct conservative default on a value form only the executing
    machine ever holds.

    **The safe-direction reading was wrong, and c1's curry probe corrected it.**
    This file priced the divergence as reject-vs-run — the checker refusing a
    program the machine would run, which costs expressiveness and nothing else.
    §G3b of the curry probe exhibits a program BOTH machines ACCEPT whose final Ωs
    do not correspond (`f = ⊥` checking, the λ-spine executing), which is a
    simulation break on an accepted program: the class S9Diff's whole-program
    assertions exist to catch, arriving where they cannot see it. It also needs no
    recursor — any sealed borrow-taking function bound to a slot has it, because
    the trigger is the borrow-moded Π's lack of a `Val` and not anything about
    `ih`.

    So the position is now UNWRITABLE rather than merely awkward, and the
    assertions below are the containment's controls. The real fix — teaching
    `indexKindV` about `fsig` — changes the read rule for every σ and is filed for
    the function-model round, where the comptime-functions proposal may delete the
    whole class. Nothing in §7 wants `ih` in a slot anyway (cost 2 is explicit that
    it is "never partially applied"). -/

def mSeal : Term := pure{ Π (n : Nat) → Π (v : &mut List Nat) → Unit }
def mMot : Term := pure{ λ (n : Nat). Π (v : &mut List Nat) → Unit }

/-- The arm binds `ih` to a local and then still calls it. -/
def m1 : Term := prog{
  let f = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    let g = ih;
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  f(3, b);
  () }

-- CHECKING: refused. M27's third containment moved WHERE it is refused — the
-- refusal now fires at the BINDING rather than at the later call that found ⊥ —
-- because c1's curry probe showed the divergence is not confined to the safe
-- direction: a program that binds `ih` and never calls it is ACCEPTED by both
-- machines with final Ωs that do not correspond. The read is the event; the call
-- was only where the old rule happened to notice.
--
-- **And the REASON has since moved too** (M27 α.2): the refusal is no longer a
-- containment keyed on a borrow-moded Π's missing `Val`, it is the model —
-- functions are reached by NAME, and `let g = ih` reads one into a second slot.
-- Nothing about this program's verdict changed; what changed is what the message
-- says, and §7 wanted none of this anyway (cost 2 is explicit that `ih` is "never
-- partially applied").
example : progRejects m1 "reached by NAME" = true := by native_decide

-- EXECUTING: the same program runs to completion and really zeroes the list,
-- because there `ih` is a `Val.rfn` and the `.rfn` case copies it.
example : (match Dllbc.Tests.S9Diff.runExec [] m1 with
   | .ok e => (e.lookup "x").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

-- Not vacuous: the SAME body without the `let g = ih` line checks, so the
-- rejection above is about reading `ih` as a value and not about the shape.
def m0 : Term := prog{
  let f = (natRec %mMot
                 (λ(v : &mut List Nat) { () })
                 (λ(n2 : Nat, ih : Π (v : &mut List Nat) → Unit, v : &mut List Nat) {
                    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ih(tl); () } } }) : %mSeal);
  let x = Cons(1, Cons(2, Nil));
  let b = &mut x;
  f(3, b);
  () }
example : progOk m0 = true := by native_decide
example : (match Dllbc.Tests.S9Diff.runExec [] m0 with
   | .ok e => (e.lookup "x").map Val.pretty
   | .error _ => none) = some "Cons Z (Cons Z Nil)" := by native_decide

end Dllbc.Tests.S26Rec