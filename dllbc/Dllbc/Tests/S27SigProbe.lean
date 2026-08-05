import Dllbc.Program
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.DeclMacro
import Dllbc.ProgMacro
import Dllbc.FnMacro
import Dllbc.Tests.S9Diff
import Dllbc.Tests.S23Direct

/-!
# §27 — the Σ-PACKAGE application form, PROBED

`combining-fns.md` §7 cost 3 offers two disciplines for saturated runtime
application: **n-ary spine** (the incumbent — `processArgs` consumes a telescope
whole, `piPeel` is the seam between curried Π types and whole-argument-list
calls) or **one unary λ taking a dependent Σ-package of its arguments, matched
immediately** — no arity, no partials by construction, no peel.

§12 open 5 names the unexercised unknown: Σ-of-borrows was probed in the
**passed** direction only (M24's G2 slice). This file probes all three
directions with negative controls, answers the moded-components question, and
tries the form on a real M23 function.

## The verdict, up front

| direction | status |
|---|---|
| PASSED | works for **exactly one shape** — `Σ (value) → &mut τ`. Everything else is refused by `readC` (§A.7). One real defect found and fixed here (§A.4). |
| STORED | **clean.** The suspended loan inside a stored package stays reachable by the demand-end rule, both machines, with a live negative control (§B). |
| RETURNED | **clean, and already fully general** — borrow-first and depth-2 packages work today, because `buildResult`/`collectResultBorrows` recurse the Σ-tree while the seeding side pattern-matches one shape (§C). |
| moded components | **option (c) is NOT free.** A proof inside the package is moved with it and the caller loses it — R16 verbatim (§E). |
| the call rule | **BLOCKED, and not by the seeding gap.** The ensures convention names a *telescope-level* borrow parameter; a packaged borrow has no name a return type can deref, so `*v`/`old *v` — the whole M23 interface — become unstatable (§D). |

## The finding that dominates

§D is the one that argues against the form, and it is not a machinery gap that
more code closes. `*v` and `old *v` resolve a **parameter**; `borrowVarIds` and
`borrowParamIds` both key exit/entry snapshots by the telescope index of a
`.borrowT` entry. In the package form there are no parameters — only projections
of one value — so every M23 signature in the corpus stops being writable.

The repair that suggests itself (let the *Σ binder* be the name a return type
derefs) is worth stating because of what it implies: a Σ telescope whose binders
name parameters IS a telescope. The form would not delete `piPeel`; it renames it
`sigmaPeel`, and the snapshot machinery gets *harder* — one var id per borrow
becomes one PATH per borrow.
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_trans id_congr len Le)

namespace Dllbc.Tests.S27SigProbe

/-! ## Helpers

    Rejections are asserted on the message, never on a Bool: `hasType` returns
    `false` for "does not have this type" and the audit turns that into an error,
    so a helper collapsing error and false would let a *stuckness* pass for a
    *typing* rejection (S26Seal's rule, kept). -/

def ok (d : Decl) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => true | .error _ => false

def rejects (d : Decl) (needle : String) (table : List Decl := [d]) : Bool :=
  match checkFn table d with | .ok _ => false | .error e => strContains e needle

/-- The concrete final Ω is a σ-instance of some accepted symbolic path's. -/
def progDiff (t : Term) (table : List Decl := []) : Bool :=
  match runProgram t table with
  | .error _ => false
  | .ok concEnv => (programEnvs t table).any (fun r => match r with
      | .ok se => Tests.S9Diff.instanceOfC se concEnv
      | .error _ => false)

/-! ## §A. PASSED — a Σ-package as THE argument

    M24's G2 built exactly one shape: `Σ (c : Nat) → &mut (Array c T)` — a value
    component first, ONE borrow second. §A asks how far that generalizes, because
    a package holding a function's whole argument list is not that shape: a
    borrow is usually the FIRST thing a function takes, and there are usually
    more than two components. -/

-- A1. The G2 shape away from arrays, so the case is about the SHAPE and not
-- about `Array`: a value component and a borrow component.
def a1 : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut List Nat) -> Unit { () } }
example : ok a1 = true := by native_decide

-- A2. …destructured by the immediate match the discipline calls for. Both
-- components are nameable in the arm, and the borrow is writable through.
def a2 : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut List Nat) -> Unit {
    match s { Pair(n, v) => { *v := Nil; () } } } }
example : ok a2 = true := by native_decide

/-! ### A3. The callee's audit DOES see through the package

    The obligation seeded for a packaged borrow is a real one: `auditObligation`
    locates the borrow by loan (`findBorrowPayload` descends into constructors),
    so the owed type is enforced at the boundary exactly as for a bare parameter.
    Three-way: discharge it, violate it, ignore it. -/

def a3ok : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut (Bool ~> Nat)) -> Unit {
  match s { Pair(n, v) => { *v := 0; () } } } }
example : ok a3ok = true := by native_decide

def a3wrong : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut (Bool ~> Nat)) -> Unit {
  match s { Pair(n, v) => { *v := True; () } } } }
example : rejects a3wrong "does not have its owed type" = true := by native_decide

-- Dropping the package unexamined does NOT drop its obligation.
def a3drop : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut (Bool ~> Nat)) -> Unit { () } }
example : rejects a3drop "does not have its owed type" = true := by native_decide

/-! ### A4. THE DEFECT THIS PROBE FOUND — field-loan collapse did not see through
    a package, and the machines disagreed because of it

    `auditObligation` collapses an argument borrow's suspended field loans before
    typing its payload, and it did so **by slot shape**: `lookupSlot ob.arg` had
    to BE a `borrowM`. A Σ-packaged borrow's slot holds a `Pair`, and after the
    immediate match it holds nothing at all — so the collapse silently did not
    run, and a `loanₘ` marker rode into `hasType`, which has no rule for one.

    Why M24's G2 never hit it: an array payload is never matched into fields, so
    no field loan was ever suspended under a package. It takes a `Cons`-match
    through the packaged borrow — which is what every list-shaped callee does.

    The twin is what makes it a defect rather than a limitation: the SAME body
    with the borrow as a bare parameter checks. And the executing machine ran the
    program happily throughout, so this was a checking-vs-executing divergence of
    exactly the kind constraint 6 exists to catch.

    **Fixed here** (`Machine.lean`, `collapseLoanIn`): collapse by LOAN, locating
    the borrow anywhere in Ω, when the slot is not itself the borrow. Twelve
    lines; the whole corpus stays green. -/

def a4pkg : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut List Nat) -> Unit {
  match s { Pair(n, v) => match v { Nil => (), Cons(h, t) => () } } } }
def a4bare : Decl := decl{ fn takes (v : &mut List Nat) -> Unit {
  match v { Nil => (), Cons(h, t) => () } } }
example : ok a4pkg = true := by native_decide
example : ok a4bare = true := by native_decide

-- …and with a write under the suspended field loan, which is the shape that
-- actually forces the collapse.
def a4write : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut List Nat) -> Unit {
  match s { Pair(n, v) => match v { Nil => (), Cons(h, t) => { *t := Nil; () } } } } }
example : ok a4write = true := by native_decide

/-! ### A5. Both machines, concrete and symbolic (constraint 6)

    A program builds a package, hands it to a sealed unary callee, and is CHECKED
    and RUN with the differential asserted. The second one matches the packaged
    borrow — the shape A4's defect lived in — so it is the differential, not the
    reasoning, that says the fix is real. -/

def a5conc : Term := prog{
  let f = seal(λ(s){ match s { Pair(n, v) => { *v := Cons(n, Nil); () } } },
               Π (s : Σ (n : Nat) → &mut List Nat) → Unit);
  let x = Nil;
  let r = f(Pair(S(Z), &mut x));
  let y = x;
  () }
example : progOk a5conc = true := by native_decide
example : progDiff a5conc = true := by native_decide

def a5match : Term := prog{
  let f = seal(λ(s){ match s { Pair(n, v) => match v { Nil => (), Cons(h, t) => () } } },
               Π (s : Σ (n : Nat) → &mut List Nat) → Unit);
  let x = Cons(Z, Nil);
  let r = f(Pair(S(Z), &mut x));
  let y = x;
  () }
example : progOk a5match = true := by native_decide
example : progDiff a5match = true := by native_decide

-- A6. The package is passed ON to another call: the obligation transfers, so a
-- package is an ordinary owned value as far as the group discipline is concerned.
def a6inner : Decl := decl{ fn inner (s : Σ (n : Nat) → &mut (Bool ~> Nat)) -> Unit {
  match s { Pair(n, v) => { *v := 0; () } } } }
def a6outer : Decl := decl{ fn outer (s : Σ (n : Nat) → &mut (Bool ~> Nat)) -> Unit {
  inner(s) } }
example : ok a6outer [a6outer, a6inner] = true := by native_decide

/-! ### A7. THE SHAPE WALL — exactly one package shape is seedable

    `seedTelescopeV` has ONE Σ case, written as a literal pattern:

        | .sigmaT aTy (.borrowT τ S) => …

    so anything else reaches `readC`, which refuses a borrow type outside a
    telescope position. All four refusals below carry that one message, and
    together they are the whole space a real argument list needs: a borrow FIRST
    (what almost every function takes), TWO borrows, a value-value-borrow nest,
    and a borrow in the middle.

    This is a machinery gap rather than a design wall — the returned direction
    (§C) shows the general Σ-tree walk is already written, in `buildResult` — but
    it is the reason nothing bigger than a two-tuple could be probed here. -/

def a7first : Decl := decl{ fn takes (s : Σ (v : &mut List Nat) → Nat) -> Unit { () } }
def a7two   : Decl := decl{ fn takes (s : Σ (a : &mut List Nat) → &mut List Nat) -> Unit { () } }
def a7nest  : Decl := decl{ fn takes (s : Σ (n : Nat) → Σ (m : Nat) → &mut List Nat) -> Unit { () } }
def a7mid   : Decl := decl{ fn takes (s : Σ (n : Nat) → Σ (v : &mut List Nat) → Le n n) -> Unit { () } }
example : rejects a7first "only valid at a telescope position" = true := by native_decide
example : rejects a7two   "only valid at a telescope position" = true := by native_decide
example : rejects a7nest  "only valid at a telescope position" = true := by native_decide
example : rejects a7mid   "only valid at a telescope position" = true := by native_decide

/-! ## §B. STORED — a Σ-of-borrows in a runtime slot, across statements

    §12 open 5's second unexercised direction, and the standing doctrine it has
    to meet: **every demand collapses first**. A package sitting in a slot holds
    a suspended loan, and the owner must stay reachable through it. -/

-- B1. The package outlives the statement that built it; the write through its
-- borrow lands in the owner; both machines agree.
def b1 : Term := prog{ let x = Nil; let p = Pair(Z, &mut x);
                       match p { Pair(n, b) => { *b := Cons(Z, Nil); () } };
                       let y = x; () }
example : progOk b1 = true := by native_decide
example : progRunsTo b1
  [("x", .bot), ("p", .bot), ("n", .ctor "Z" []), ("b", .bot),
   ("y", .ctor "Cons" [.ctor "Z" [], .ctor "Nil" []])] = true := by native_decide
example : progDiff b1 = true := by native_decide

/-! ### B2. The negative control — the demand-end rule really reaches inside

    Read the owner BEFORE the package's borrow is used and the loan is demanded
    out from under the package: the later write finds a hole. Both machines say
    so, with the same message, which is what makes B1 a statement about the
    demand-end rule rather than about nothing happening. -/

def b2 : Term := prog{ let x = Nil; let p = Pair(Z, &mut x); let y = x;
                       match p { Pair(n, b) => { *b := Cons(Z, Nil); () } }; () }
example : progRejects b2 "cannot peel a vacant slot" = true := by native_decide
example : progRunErr b2 "cannot peel a vacant slot" = true := by native_decide

/-! ### B3. The NON-immediate match is coherent, not rejected

    §7 cost 3 says "matched immediately". Nothing enforces it, and nothing needs
    to: a body that binds the package to another slot first, or never matches it
    at all, is checked by the same demand-end and obligation rules. Pinned
    because the discipline's enforceability was the open question — the answer is
    that the discipline is a *style*, and the kernel does not lean on it. -/

def b3store : Decl := decl{ fn caller () -> Unit {
  let f = seal(λ(s){ let q = s; match q { Pair(n, v) => { *v := Nil; () } } },
               Π (s : Σ (n : Nat) → &mut List Nat) → Unit);
  () } }
example : ok b3store = true := by native_decide

-- Never matched at all — accepted, and A3's `a3drop` is why that is safe: the
-- obligation is audited whether or not the body ever looks inside.
def b3drop : Decl := decl{ fn caller () -> Unit {
  let f = seal(λ(s){ () }, Π (s : Σ (n : Nat) → &mut List Nat) → Unit);
  () } }
example : ok b3drop = true := by native_decide

/-! ## §C. RETURNED — and the direction that is already general

    `buildResult` and `collectResultBorrows` both RECURSE the Σ-tree, minting one
    issued loan per borrow leaf at any depth and in any position. So the returned
    direction needs nothing built: the three shapes §A.7 cannot seed are all
    returnable today. The asymmetry is the migration's map — the general walk
    exists, on the wrong side. -/

def c1val : Decl := decl{ fn giveBack (v : &mut List Nat) -> Σ (n : Nat) → &mut List Nat
  { Pair(Z, &mut *v) } }
def c1first : Decl := decl{ fn giveBackF (v : &mut List Nat) -> Σ (b : &mut List Nat) → Nat
  { Pair(&mut *v, Z) } }
def c1nest : Decl := decl{ fn giveBackN (v : &mut List Nat) -> Σ (n : Nat) → Σ (m : Nat) → &mut List Nat
  { Pair(Z, Pair(Z, &mut *v)) } }
example : ok c1val = true := by native_decide
example : ok c1first = true := by native_decide
example : ok c1nest = true := by native_decide

/-! ### C2. The caller's group discipline, and the ending order

    The caller captures its own borrow into the call's group and receives the
    package holding the issued reborrow. Using the returned borrow is fine;
    touching the OWNER first releases the group and the returned borrow is gone —
    which is the ending order, asserted rather than assumed. -/

def c2use : Decl := decl{ fn caller (x : &mut List Nat) -> Unit {
  let p = giveBack(&mut *x);
  match p { Pair(n, b) => { *b := Nil; () } } } }
example : ok c2use [c2use, c1val] = true := by native_decide

def c2early : Decl := decl{ fn caller (x : &mut List Nat) -> Unit {
  let p = giveBack(&mut *x);
  let y = *x;
  match p { Pair(n, b) => { *b := Nil; () } } } }
example : rejects c2early "cannot peel a vacant slot" [c2early, c1val] = true := by native_decide

-- The borrow-FIRST package at a caller, so C1's acceptance is not just a type
-- being well-formed: the group really finds the loan wherever it sits.
def c2first : Decl := decl{ fn caller (x : &mut List Nat) -> Unit {
  let p = giveBackF(&mut *x);
  match p { Pair(b, n) => { *b := Nil; () } } } }
example : ok c2first [c2first, c1first] = true := by native_decide

/-! ### C3. The returned package's owed type is enforced, at both ends

    A callee that promises a `Nat`-owing borrow inside a package and leaves the
    entry `Bool` in it is refused by `collectResultBorrows`' payload check — the
    same rule a bare returned borrow gets, reached through the Σ. -/

def c3lie : Decl :=
  decl{ fn lieBack (v : &mut (Bool ~> Bool)) -> Σ (n : Nat) → &mut (Bool ~> Nat)
    { Pair(Z, &mut *v) } }
example : rejects c3lie "does not have its owed type" = true := by native_decide

-- The honest twin: the promise and the entry agree, so nothing is owed on the
-- way out and the same shape is accepted.
def c3ok : Decl :=
  decl{ fn okBack (v : &mut (Nat ~> Nat)) -> Σ (n : Nat) → &mut (Nat ~> Nat)
    { Pair(Z, &mut *v) } }
example : ok c3ok = true := by native_decide

-- …and the CALLER of the honest one owes the same type through the package.
def c3useOk : Decl := decl{ fn caller (x : &mut (Nat ~> Nat)) -> Unit {
  let p = okBack(&mut *x); match p { Pair(n, b) => { *b := 0; () } } } }
def c3useBad : Decl := decl{ fn caller (x : &mut (Nat ~> Nat)) -> Unit {
  let p = okBack(&mut *x); match p { Pair(n, b) => { *b := True; () } } } }
example : ok c3useOk [c3useOk, c3ok] = true := by native_decide
example : rejects c3useBad "does not have its owed type" [c3useBad, c3ok] = true := by native_decide

/-! ## §D. THE ENSURES WALL — the finding that argues against the form

    M23's thesis is that the declared return type IS the caller's whole knowledge,
    and the convention it is written in is `*v` (the exit snapshot of borrow
    parameter `v`) and `old *v` (its entry snapshot). Both are keyed to a
    TELESCOPE-LEVEL borrow parameter, by var id:

        borrowVarIds   (tel : List (Var × Term))            -- filters `.borrowT` only
        borrowParamIds (telescope : List (String × Term))   -- likewise

    A packaged borrow is neither. `seedTelescopeV`'s Σ case records no
    `entrySyms` entry, `borrowVarIds` does not list it, and a return type that
    derefs the package gets `readC`'s honest refusal: the slot holds a `Pair`.

    So under the package form **no M23 signature in the corpus is writable**.
    That is not a gap more seeding code closes — it is what "there are no
    parameters, only projections" costs. -/

def d1 : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut List Nat)
  -> Id (List Nat) (*s) Nil { match s { Pair(n, v) => { *v := Nil; Refl } } } }
example : rejects d1 "dereferenced value is not a borrow" = true := by native_decide

def d2 : Decl := decl{ fn takes (s : Σ (n : Nat) → &mut List Nat)
  -> Id (List Nat) Nil (old *s) { match s { Pair(n, v) => { *v := Nil; Refl } } } }
example : rejects d2 "dereferenced value is not a borrow" = true := by native_decide

-- The bare-parameter twin, which is the convention the whole corpus is written
-- in: the same claim, statable and proved.
def d3 : Decl := decl{ fn takes (v : &mut List Nat)
  -> Id (List Nat) (*v) Nil { *v := Nil; Refl } }
example : ok d3 = true := by native_decide

/-! ### D4. On a REAL telescope: shape yes, contract no

    `partition (v : &mut List Nat, p : Nat)` is one of the few M23 functions whose
    argument list fits the single supported package shape at all — reorder to put
    the borrow last and it seeds. Its ensures still cannot be stated, so what
    survives the packaging is the function minus its interface. -/

def d4shape : Decl := decl{ fn part (s : Σ (p : Nat) → &mut List Nat) -> Unit {
  match s { Pair(p, v) => { *v := Nil; () } } } }
example : ok d4shape = true := by native_decide

def d4spec : Decl := decl{ fn part (s : Σ (p : Nat) → &mut List Nat)
  -> Σ (hi : List Nat) → Id (List Nat) (*s) Nil {
  match s { Pair(p, v) => { *v := Nil; Pair(Nil, Refl) } } } }
example : rejects d4spec "dereferenced value is not a borrow" = true := by native_decide

/-! ### D5. THE ONE ESCAPE HATCH, measured — the `~>` owed type still works

    The return type is not the only place an exit spec can live: `&mut (t : τ ~>
    S)` states one ENTRY-RELATIVELY, and `seedTelescopeV`'s Σ case threads the
    entry snapshot into it correctly. So a relational contract IS statable through
    a package — in M16's `swapS01` style, where the payload literally becomes a
    pair carrying its own proof.

    Measured rather than asserted, because it is the only route §D leaves open,
    and its price is exactly the one M23 paid to get away from it: the OWED TYPE
    is a property of the payload's own type, so the data representation changes to
    carry the evidence, and every reader of the borrow destructures a pair. M23's
    return-type ensures exists because that was worse. -/

def d5 : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut (t : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len t)))
  -> Unit { match s { Pair(n, v) => { let l = *v; *v := Pair(l, Refl); () } } } }
example : ok d5 = true := by native_decide

-- Not vacuous: the same package with a body that files the WRONG evidence — a
-- list of a different length beside a `Refl` that cannot bridge it.
def d5lie : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut (t : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len t)))
  -> Unit { match s { Pair(n, v) => { let l = *v; *v := Pair(Cons(Z, l), Refl); () } } } }
example : rejects d5lie "does not have its owed type" = true := by native_decide

/-! ## §E. THE MODED-COMPONENTS QUESTION

    §6 gives modes to "λ, Π and `let` alike" — the binders of PARAMETERS — and
    `Uni.lean` records the deliberate omission: "a Σ's binder names a projection,
    not a parameter … a capital Σ binder is therefore legal and inert". Under the
    package form every capital parameter becomes a Σ component, so the omission
    stops being harmless.

    Option (c) — "proofs are already unrestricted values; is a mode marker even
    needed inside a package the callee immediately matches?" — was to be tested
    first because it might be free. **It is not free, and the twin says so.** -/

-- E1. The proof rides inside the package. The caller loses it: building the
-- `Pair` is a ⇒-read of `hnm`, and `indexKindV` classifies a σ typed at a stuck
-- `Le` spine as data, so it MOVES. R16, verbatim, back at full strength.
def e1callee : Decl := decl{ fn takesP (n : Nat, m : Nat, s : Σ (H : Le n m) → Nat) -> Unit { () } }
def e1caller : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  takesP(n, m, Pair(hnm, Z)); hnm } }
example : rejects e1caller "holds ⊥" [e1caller, e1callee] = true := by native_decide

-- E2. The capital-PARAMETER twin — today's spine convention — keeps it, which is
-- what says E1 is about the package and not about the proof.
def e2callee : Decl := decl{ fn takesCap (n : Nat, m : Nat, H : Le n m) -> Unit { () } }
def e2caller : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  takesCap(n, m, hnm); hnm } }
example : ok e2caller [e2caller, e2callee] = true := by native_decide

-- E3. The rejection the checker itself writes names the missing mechanism: it
-- tells the programmer to capitalize the callee's PARAMETER, which is precisely
-- what the package form takes away.
example : rejects e1caller "capitalizing the callee's parameter" [e1caller, e1callee]
  = true := by native_decide

/-! ### E4. A capital Σ binder is legal and inert — pinned from both sides

    So option (a) ("Σ components gain modes") cannot be had by writing a capital
    name: the elaborator accepts it and nothing reads it. The mode a caller must
    obey is a fact about the TYPE it sees (§5 point 4, S26Modes F3), and a Σ type
    carries none — so (a) is a change to the Σ former, not a convention. -/

def e4 : Decl := decl{ fn takes (s : Σ (N : Nat) → &mut List Nat) -> Unit {
  match s { Pair(n, v) => { *v := Nil; () } } } }
example : ok e4 = true := by native_decide

/-! ## §F. THE CALL-RULE SKETCH — and why `split_off` could not be written

    §7 cost 3's form for `split_off` is `Π (p : Σ (v : &mut List Nat) → Σ (i :
    Nat) → Le i (len *v)) → ⟨ensures⟩`, matched immediately. It fails twice
    before the body is reached:

      1. the package puts a borrow FIRST and has THREE components (§A.7);
      2. the ensures needs `*v` and `old *v` (§D).

    Failure 1 is machinery. Failure 2 is the design. Both are pinned below, and
    the reordering that would dodge failure 1 does not exist either: `Hi`'s type
    mentions `*v`, so the borrow cannot be moved after it, and a value-value-borrow
    nest is refused anyway. -/

def f1 : Decl := decl{
  fn so (s : Σ (v : &mut List Nat) → Σ (i : Nat) → Le i (len *v)) -> Unit { () } }
example : rejects f1 "only valid at a telescope position" = true := by native_decide

def f2 : Decl := decl{
  fn so (s : Σ (i : Nat) → Σ (Hi : Le i i) → &mut List Nat) -> Unit { () } }
example : rejects f2 "only valid at a telescope position" = true := by native_decide

/-! ### F3. What DOES work, at the seal, so the wall is bounded

    A unary sealed λ over the one supported package shape checks and is callable
    — the call rule needs nothing new, because `processArgs` reads a one-entry
    telescope like any other. The form is viable exactly as far as its types are
    seedable, which is §A.7's line; and the spine twin beside it is the
    comparison the probe was for. -/

def f3 : Decl := decl{ fn caller (x : &mut List Nat) -> Unit {
  let f = seal(λ(s){ match s { Pair(n, v) => { *v := Nil; () } } },
               Π (s : Σ (n : Nat) → &mut List Nat) → Unit);
  let r = f(Pair(Z, &mut *x));
  () } }
example : ok f3 = true := by native_decide

def f3spine : Decl := decl{ fn caller (x : &mut List Nat) -> Unit {
  let f = seal(λ(n, v){ *v := Nil; () },
               Π (n : Nat) → Π (v : &mut List Nat) → Unit);
  let r = f(Z, &mut *x);
  () } }
example : ok f3spine = true := by native_decide

end Dllbc.Tests.S27SigProbe
