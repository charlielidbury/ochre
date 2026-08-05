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
# §27 — the GATE PROBE for the comptime-functions model: dependent MIXED packages

The model under design: every function is a ⇝-resolved name taking **one** runtime
argument — a dependent Σ-package whose components interleave runtime data, borrows
and comptime proofs by dependency. `S27SigProbe` measured the three *directions*
(passed / stored / returned) for packages of DATA and BORROWS. This file measures
what that one did not reach: a component whose TYPE reads through a **borrow**
component of the same package (the reverse of M24's G2 data→borrow seeding), what
constructing a mixed package costs, and what a return type can say about one.

## Verdict, up front

| Q | question | verdict |
|---|---|---|
| Q1 | borrow→proof dependency inside one package | **CLOSED — and not by the shape wall.** §B |
| Q2 | mixed construction moves the proof | **confirmed for packages holding a borrow, and ALREADY SOLVED for those that do not** (§C.5). The capital-`let` workaround does not exist. §C |
| Q3 | return types over packages | **match-in-Π works over a VALUE package (§D.3); `*(proj p)` is unreachable in principle; and `eb510a0f` has closed the returned direction outright.** §D |
| Q4 | mixed packages execute | **yes** — proof+borrow packages construct, call, destructure, mutate and return, both machines. §A |

**GATE CLOSED for "one runtime argument". GATE OPEN for everything the model
wanted that argument to buy** — because §B.4 measures the hybrid working today:
borrows stay named telescope parameters, *everything else* packages into one
dependent Σ that may read through them, and the full M23 interface (`*v`,
`old *v`, pinned Σ results) survives, with lie twins refused.

## The one sentence

`*` is a **reflection-time projection on Ω, not a value former**. `Val` has no
deref constructor, so `reflectC` must discharge every `*` bottom-up *before* a
single ι-step runs; a deref therefore only succeeds when its operand reflects
DIRECTLY to a `borrowM`. A `.var` naming a borrow slot does. A projection, a
β-redex or a `sigmaRec` arm-binder never can — they need normalization to become
a `borrowM`, and normalization happens after reflection is over.

That ordering fact is the probe. It is not `borrowVarIds`, it is not
`seedTelescopeV`'s single Σ pattern, and generalizing either one does not touch
it. Its corollary is the design output: a packaged borrow becomes dereferenceable
exactly when it is given an **Ω slot and a var name** at seeding — at which point
the package *is* a telescope, and `*v` works again for the only reason it ever
worked (§E).
-/

open Dllbc
open Dllbc.StdLemmas (le_refl le_trans id_congr len Le)

namespace Dllbc.Tests.S27PkgProbe

/-! ## Helpers — S26Seal's rule, kept

    Rejections assert on the MESSAGE, never on a `Bool`: `hasType` returns
    `false` for "does not have this type" and the audit turns that into an error,
    so a helper collapsing error and false would let *stuckness* pass for a
    *typing* rejection. -/

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

/-- One slot of the concrete final Ω, by name — used where the whole Ω contains a
    `lamR` closure that no literal can spell. -/
def slotIs (t : Term) (name : String) (v : Val) (table : List Decl := []) : Bool :=
  match runProgram t table with
  | .error _ => false
  | .ok e => match e.lookup name with | some v' => v' == v | none => false

/-! ## §A. Q4 — EXECUTING FIRST: a MIXED package runs

    The polarity doctrine: the machine before the argument. A package mixing a
    *comptime* component (a proof) with a *runtime* one (a borrow) is the model's
    atom, and the first question is not whether it type-checks but whether it
    constructs, calls, destructures, mutates and returns.

    It does — and it needed nothing new, because `Σ (H : Le a b) → &mut τ` is an
    instance of the ONE seedable package shape (`seedTelescopeV`'s
    `.sigmaT aTy (.borrowT τ S)`). A proof is a value, and "value component then
    borrow component" is what that case matches. So the mixed package is not a new
    shape: §A measures how much of the model already runs, and the answer is all
    of it, minus every dependency (§B) and every contract (§D). -/

-- A1. Construct, call, destructure, mutate through, and see the write land in the
-- owner. Both machines, plus the owner's final value.
def a1 : Term := prog{
  let f = seal(λ(s){ match s { Pair(h, v) => { *v := Cons(Z, Nil); () } } },
               Π (s : Σ (H : Le (S Z) (S Z)) → &mut List Nat) → Unit);
  let x = Nil;
  let r = f(Pair(le_refl (S Z), &mut x));
  let y = x;
  () }
example : progOk a1 = true := by native_decide
example : progDiff a1 = true := by native_decide
example : slotIs a1 "y" (.ctor "Cons" [.ctor "Z" [], .ctor "Nil" []]) = true := by native_decide
-- the owner is left moved-out where it was lent, not silently duplicated
example : slotIs a1 "x" .bot = true := by native_decide

/-! ### A2. The proof component is LOAD-BEARING, not carried dead

    A package with a slot nothing reads would make A1 a statement about pairs. The
    callee's arm binder is a live `Le a b` and the body returns it; the twin
    beside it cites the same binder for the reversed claim and is refused.

    Written symbolically (`a`, `b` telescope parameters) on purpose: `Le` COMPUTES
    — `Le (S Z) (S Z)` and `Le Z Z` are both `Unit` — so a concrete "wrong proof"
    control would be a definitional identity and would pass for the wrong reason.
    A stuck `Le` spine on two σ's is the only honest negative here. -/

def a2 : Decl := decl{ fn usesProof (a : Nat, b : Nat, s : Σ (H : Le a b) → &mut List Nat)
  -> Le a b { match s { Pair(h, v) => { *v := Nil; h } } } }
example : ok a2 = true := by native_decide

def a2lie : Decl := decl{ fn usesProof (a : Nat, b : Nat, s : Σ (H : Le a b) → &mut List Nat)
  -> Le b a { match s { Pair(h, v) => { *v := Nil; h } } } }
example : rejects a2lie "does not have return type" = true := by native_decide

-- A3. A second running program: the packaged borrow is MATCHED through (the shape
-- S27SigProbe's §A.4 found a checking-vs-executing divergence in) and written
-- under a suspended field loan, with a proof riding alongside.
def a3 : Term := prog{
  let f = seal(λ(s){ match s { Pair(h, v) =>
            match v { Nil => (), Cons(hd, tl) => { *tl := Nil; () } } } },
               Π (s : Σ (H : Le (S Z) (S Z)) → &mut List Nat) → Unit);
  let x = Cons(Z, Cons(S(Z), Nil));
  let r = f(Pair(le_refl (S Z), &mut x));
  let y = x;
  () }
example : progOk a3 = true := by native_decide
example : progDiff a3 = true := by native_decide
example : slotIs a3 "y" (.ctor "Cons" [.ctor "Z" [], .ctor "Nil" []]) = true := by native_decide

/-! ## §B. Q1 — THE GATE: a component whose type reads through a packaged borrow

    M24's G2 seeded `Σ (c : Nat) → &mut (Array c T)` — the borrow's payload type
    reading the VALUE component (data→borrow). The gate is the reverse: a proof
    component reading `len *v` off the BORROW component. `split_off`'s argument
    list, `Σ (v : &mut List Nat) → Σ (i : Nat) → Le i (len *v)`, is the model's
    motivating instance. -/

-- B1. The target shape, refused — S27SigProbe's `f1`, re-pinned because
-- everything below is about WHY.
def b1 : Decl := decl{
  fn so (s : Σ (v : &mut List Nat) → Σ (i : Nat) → Le i (len *v)) -> Unit { () } }
example : rejects b1 "only valid at a telescope position" = true := by native_decide

/-! ### B2. The refusal is NOT the shape wall — isolated

    It would be easy to read B1 as `seedTelescopeV`'s single Σ pattern, and to
    conclude that generalizing the pattern opens the gate. It does not, and the
    control that shows it uses the ONE shape that already seeds: put the borrow
    where it is legal (last, after a value) and then ask a *separate* telescope
    entry to deref the package. No shape is violated. The deref still fails, and
    the message is a different one — `readC (⇝ *)`, not the telescope-position
    refusal.

    So there are two independent walls, and the shape wall is the shallower. -/

def b2 : Decl := decl{ fn f (s : Σ (n : Nat) → &mut List Nat, h : Le Z (len *s)) -> Unit { () } }
example : rejects b2 "dereferenced value is not a borrow" = true := by native_decide

-- The seedable shape ALONE, so B2's rejection is attributable to the deref and to
-- nothing about the package's type.
def b2shape : Decl := decl{ fn f (s : Σ (n : Nat) → &mut List Nat) -> Unit { () } }
example : ok b2shape = true := by native_decide

/-! ### B3. The THIRD wall: `&mut τ` is not a type the pure fragment can name

    The obvious repair for B2 is a projection: write `snd s` and deref *that*.
    It cannot be written. A Σ-elimination needs a motive, the motive's binder type
    is the Σ itself, and `readC` refuses a `borrowT` anywhere a pure type is read
    — so a projection whose RESULT is a borrow has no typeable motive. B3 pins it
    at the codomain position where §D wants it most: the same match-in-Π that
    works over a value package (§D.3) is refused the moment the package holds a
    borrow.

    This is why the two walls cannot be attacked separately. Any computation that
    would produce a borrow needs a borrow *type* in the pure fragment; there is
    none; so `*`'s operand can only ever be a variable. -/

def b3 : Decl := decl{ fn f (s : Σ (n : Nat) → &mut List Nat)
  -> elim s return (λ (q : Σ (n : Nat) → &mut List Nat). Type) { Pair (x) (y) => Id Nat Z Z }
  { match s { Pair(a, b) => { *b := Nil; Refl } } } }
example : rejects b3 "only valid at a telescope position" = true := by native_decide

-- …and a borrow of a borrow, for the same reason: the inner `&mut` is at a pure
-- position. The rule is uniform, which is what makes it a fragment boundary
-- rather than a missing case.
def b3chain : Decl := decl{ fn f (v : &mut (&mut List Nat)) -> Unit { () } }
example : rejects b3chain "only valid at a telescope position" = true := by native_decide

/-! ### B4. THE FINDING THAT DECIDES THE MODEL — the dependency works when the
    borrow keeps a NAME

    The gate question was whether borrow→proof dependency is expressible. It is,
    today, fully — and with the whole M23 interface intact. What it costs is
    exactly one thing: the borrow stays a telescope parameter, and only the
    *rest* of the argument list packages.

    `f (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))` seeds: `v` is a
    borrow parameter so `*v` reflects to its entry σ, and `s`'s type — an ordinary
    pure Σ — is `readC`'d against an Ω where that σ already exists. The proof
    component reads the borrow. That is the gate, open, one argument short of the
    model's shape. -/

def b4 : Decl := decl{ fn f (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v)) -> Unit {
  match s { Pair(i, h) => { *v := Nil; () } } } }
example : ok b4 = true := by native_decide

-- Not vacuous: the packaged proof is CITED at a demand site that needs exactly
-- its statement…
def useLe : Decl := decl{ fn useLe (a : Nat, b : Nat, h : Le a b) -> Unit { () } }
def b4use : Decl := decl{ fn needs (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))
  -> Unit { match s { Pair(i, h) => { useLe(i, len *v, h); () } } } }
example : ok b4use [b4use, useLe] = true := by native_decide

-- …and citing it for the reversed claim is refused, at the call that demands it.
-- So `len *v` inside the package's type really is the borrow's payload length and
-- not an opaque token that would unify with anything.
def b4lie : Decl := decl{ fn needs (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))
  -> Unit { match s { Pair(i, h) => { useLe(len *v, i, h); () } } } }
example : rejects b4lie "does not have its parameter type" [b4lie, useLe] = true := by native_decide

/-! ### B5. …and the M23 interface survives on top of it

    B4 would be a curiosity if the hybrid could not also state a contract. It can:
    the same function carries an exit ensures over `*v`, a `old *v` entry
    reference, and a pinned Σ result — the three things §D of `S27SigProbe`
    reported lost — because the borrow it talks about is still a parameter.

    This is the measurement the gate verdict rests on. Everything the package form
    was for (one dependent argument, comptime and runtime interleaved by
    dependency) is available for every component except the borrows. -/

def b5ens : Decl := decl{ fn f (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))
  -> Id (List Nat) (*v) Nil { match s { Pair(i, h) => { *v := Nil; Refl } } } }
example : ok b5ens = true := by native_decide

def b5lie : Decl := decl{ fn f (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))
  -> Id (List Nat) (*v) (Cons(Z, Nil)) { match s { Pair(i, h) => { *v := Nil; Refl } } } }
example : rejects b5lie "does not have return type" = true := by native_decide

-- `old *v` and a pinned Σ result, over the same packaged argument.
def b5old : Decl := decl{ fn f (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v))
  -> Σ (r : List Nat) → Id (List Nat) r (old *v) {
  match s { Pair(i, h) => { let l = *v; *v := Nil; Pair(l, Refl) } } } }
example : ok b5old = true := by native_decide

/-! ## §C. Q2 — MIXED CONSTRUCTION, characterized

    Building a package is a `.ctorApp "Pair"`, and `readR`'s rule for one is
    `readArgs` — the ⇒-read, which CONSUMES. So a proof placed into a package is
    moved out of the caller. R16 verbatim, and S27SigProbe's §E measured it. §C's
    job is to pin what the repair must be, by measuring every workaround that
    already exists and failing each one precisely. -/

def c0callee : Decl := decl{ fn takesP (n : Nat, m : Nat, s : Σ (H : Le n m) → Nat) -> Unit { () } }

-- C1. The consumption, pinned. The caller cannot cite `hnm` after packing it.
def c1 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  takesP(n, m, Pair(hnm, Z)); hnm } }
example : rejects c1 "holds ⊥" [c1, c0callee] = true := by native_decide

-- …and the checker's own advice names the mechanism the package form removes:
-- capitalize the callee's PARAMETER. There is no parameter to capitalize.
example : rejects c1 "capitalizing the callee's" [c1, c0callee] = true := by native_decide

/-! ### C2. The capital-`let` workaround DOES NOT EXIST — it fails harder

    The natural dodge is to bind the proof comptime first and pack the copy:
    `let H = hnm; … Pair(H, Z)`. A capital `let` is a ⇝-binding and the §6 fence
    forbids ⇒-moving it — and building a `Pair` IS a ⇒-move. So the workaround
    converts a use-after-move into a fence violation. Both are refusals; there is
    no third thing to try at the construction site. -/

def c2 : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  let H = hnm; takesP(n, m, Pair(H, Z)); hnm } }
example : rejects c2 "cannot be ⇒-moved" [c2, c0callee] = true := by native_decide

/-! ### C3. Whole-package mode WORKS — and is available exactly when it is useless

    The one granularity §6 does offer is the parameter, and it applies to a
    package like any other type: capitalize the callee's package parameter and the
    entire argument is ⇝-read, so the caller keeps its proof. C3a is that, working.

    C3b is why it does not rescue the model: `seedTelescopeV` refuses a capitalized
    binder whose type is `Σ … → &mut τ`, in as many words — "a ⇝-read of `&mut` is
    meaningless". A comptime package cannot contain a borrow. So whole-package
    mode is available precisely for the packages that have no runtime component,
    which are the packages the model did not need help with.

    This is the exact spec of the missing feature, by subtraction: the mode must
    cut BELOW the package. -/

def c3calleeC : Decl := decl{ fn takesPC (n : Nat, m : Nat, S : Σ (H : Le n m) → Nat) -> Unit { () } }
def c3a : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  takesPC(n, m, Pair(hnm, Z)); hnm } }
example : ok c3a [c3a, c3calleeC] = true := by native_decide

def c3b : Decl := decl{ fn f (S : Σ (n : Nat) → &mut List Nat) -> Unit { () } }
example : rejects c3b "is capitalized (comptime, §6) but its type is a borrow" = true := by native_decide

/-! ### C4. What the 0-mark must do differently — stated against the code

    The reading mechanism already exists: `readArgsModed` takes a per-position
    `List Bool` and `readComptimeArg`s the `true` ones. A call gets its mode list
    from the callee's telescope (`processArgs` reads `declVar.isComptime`). A
    `Pair` gets nothing, and cannot: `readR`'s `.ctorApp` case is pure SYNTHESIS —
    it has the constructor's name and its argument terms, and no expected type.

    So the 0-mark is not a new read; it is a new *direction*. Two consequences the
    feature has to answer, both visible above:

      1. `Pair` must be CHECKED against its Σ type at construction, or carry the
         marks itself; otherwise there is no mode list to hand `readArgsModed`.
      2. A Σ's binder currently "names a projection, not a parameter" (`Uni.lean`),
         and a capital Σ binder is legal and inert (S27SigProbe §E.4). A 0-mark is
         therefore a change to the Σ FORMER — the mark must reach `beq`/`convert`
         decisions about Σ types, since a caller's obligation is a fact about the
         type it sees (§5 point 4) — and not a naming convention. -/

-- C4a. The inertness that makes (2) necessary, re-pinned at construction: the
-- capital Σ binder changes nothing about how the `Pair` is read.
def c4callee : Decl := decl{ fn takesQ (n : Nat, m : Nat, s : Σ (H : Le n m) → Nat) -> Unit { () } }
def c4a : Decl := decl{ fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m {
  takesQ(n, m, Pair(hnm, Z)); hnm } }
example : rejects c4a "holds ⊥" [c4a, c4callee] = true := by native_decide

/-! ### C5. THE TAX IS ALREADY AVOIDABLE — for the shape §B.4 says is the reachable one

    C1–C4 measured mixed construction for a package that CONTAINS a borrow, and
    every route failed. §B.4's hybrid does not contain one, and that changes the
    answer completely: the callee's package parameter can be capitalized, the whole
    package is ⇝-read at the call, and the caller keeps its proof — while the
    package's type still reads `len *v` off the borrow beside it.

    A one-character twin, and the two rejections are different in kind, which is
    what makes the pair evidence: the lowercase caller's proof is a hole; the
    capital caller's is intact. So whole-package mode COMPOSES with the hybrid —
    §C3b's refusal ("a ⇝-read of `&mut` is meaningless") is not triggered, because
    the borrow was never in the package.

    The scheduling conclusion is direct, and it is the probe's practical output:
    **per-component Σ marks buy nothing until packaged borrows have names.** The
    only configuration a 0-mark serves is a package mixing a borrow with a
    comptime component, and §B says that package cannot be written at all. -/

def c5callee  : Decl := decl{ fn g  (v : &mut List Nat, S : Σ (i : Nat) → Le i (len *v)) -> Unit { () } }
def c5calleeL : Decl := decl{ fn gl (v : &mut List Nat, s : Σ (i : Nat) → Le i (len *v)) -> Unit { () } }

def c5keep : Decl := decl{ fn caller (x : &mut List Nat, i : Nat, h : Le i (len *x))
  -> Le i (len (old *x)) { g(&mut *x, Pair(i, h)); h } }
example : ok c5keep [c5keep, c5callee] = true := by native_decide

def c5move : Decl := decl{ fn caller (x : &mut List Nat, i : Nat, h : Le i (len *x))
  -> Le i (len (old *x)) { gl(&mut *x, Pair(i, h)); h } }
example : rejects c5move "holds ⊥" [c5move, c5calleeL] = true := by native_decide

/-! ## §D. Q3 — RETURN TYPES OVER PACKAGES

    Three separate questions, three different answers. -/

/-! ### D1. `*(proj p)` — unreachable in principle, and the containment is moot

    A codomain of the `Id Nat (len *(fst p)) …` class cannot be written, for §B.3's
    reason: no projection can have borrow type. The reachable approximation is
    dereferencing the package variable itself, and it is refused by the deref rule,
    not by a return-type rule — which is the point. `old` fares identically:
    `reflectC`'s `old` case matches the SYNTACTIC pattern `.app (.const "old")
    (.deref (.var v))`, so `old *s` on a package falls through to the generic
    application rule and its inner deref throws first. Nothing ever reaches an
    `entrySyms` lookup. -/

def d1exit : Decl := decl{ fn f (s : Σ (n : Nat) → &mut List Nat) -> Id Nat (len *s) Z {
  match s { Pair(n, v) => { *v := Nil; Refl } } } }
example : rejects d1exit "dereferenced value is not a borrow" = true := by native_decide

def d1old : Decl := decl{ fn f (s : Σ (n : Nat) → &mut List Nat) -> Id Nat Z (len (old *s)) {
  match s { Pair(n, v) => { *v := Nil; Refl } } } }
example : rejects d1old "dereferenced value is not a borrow" = true := by native_decide

-- The bare-parameter twins, so both refusals are about the PACKAGE and not about
-- `old` or about `len`.
def d1bare : Decl := decl{ fn f (v : &mut List Nat) -> Id Nat (len (old *v)) (len (old *v)) {
  *v := Nil; Refl } }
example : ok d1bare = true := by native_decide

/-! ### D2. THE CONTAINMENT COLLISION — `eb510a0f` has closed the returned direction

    `S27SigProbe` §C reported the returned direction "clean, and already fully
    general", on the strength of `fn giveBack (v : &mut List Nat) -> Σ (n : Nat) →
    &mut List Nat`. That function is **refused on main**. `eb510a0f` ("refuse
    return types that mix borrow and non-borrow components") lands after that
    probe's branch point, and a package is a mix by construction.

    This is reported as a collision rather than a defect, because the containment's
    reasoning is exactly right: a borrow-carrying return type is audited
    structurally, per issued borrow against its owed type, and the value check is
    skipped for the whole type — so a value component would be judged by nothing
    while the caller still received it as a proof. Returning `Σ (cursor) → (proof
    about it)` is not merely unimplemented; under today's audit it would be a
    soundness hole.

    The consequence for the model is sharp. Of the three directions, RETURNED is
    now the most closed, not the most open, and it is closed by a rule the model
    must displace rather than extend. -/

def d2mixed : Decl := decl{ fn giveBack (v : &mut List Nat) -> Σ (n : Nat) → &mut List Nat
  { Pair(Z, &mut *v) } }
example : rejects d2mixed "may not also carry VALUE components" = true := by native_decide

-- The proof-carrying version the model actually wants — a cursor plus its
-- certificate — refused by the same rule.
def d2cert : Decl := decl{ fn f (v : &mut List Nat) -> Σ (b : &mut List Nat) → Id Nat Z Z
  { Pair(&mut *v, Refl) } }
example : rejects d2cert "may not also carry VALUE components" = true := by native_decide

-- An all-VALUE package return is unaffected, which is what says D2 is the
-- borrow/value mix and not Σ-returns in general.
def d2val : Decl := decl{ fn f (n : Nat) -> Σ (m : Nat) → Id Nat m n { Pair(n, Refl) } }
example : ok d2val = true := by native_decide

/-! ### D3. match-in-Π as a codomain former — WORKS, over a value package

    The one positive result in §D. `elim s return (λ q. …) { Pair (x) (y) => … }`
    in a return-type position elaborates to `sigmaRec` (`Uni.lean` §9), and the
    ι-rule fires against the seeded package's slot, which holds a real
    `ctor "Pair"`. So a codomain that destructures its argument is a working
    codomain former today.

    Its limit is B3's: the motive's binder type is the Σ, so the moment a
    component is a borrow the motive is unwritable. match-in-Π is available for
    exactly the packages `*` was never needed for. -/

def d3 : Decl := decl{ fn f (s : Σ (n : Nat) → Nat)
  -> elim s return (λ (q : Σ (n : Nat) → Nat). Type) { Pair (x) (y) => Id Nat x x }
  { match s { Pair(a, b) => Refl } } }
example : ok d3 = true := by native_decide

/-! ### D4. The surviving contract route, confirmed on main

    `S27SigProbe` §D.5's escape hatch — state the contract ENTRY-RELATIVELY as the
    borrow's owed type, `&mut (t : τ ~> S)` — still checks after all three
    containment commits, with its lie twin still refused. It is the only way a
    packaged borrow can carry a contract today, and its price is unchanged: the
    payload's own type changes to carry the evidence, so every reader of the
    borrow destructures a pair. -/

def d4 : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut (t : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len t)))
  -> Unit { match s { Pair(n, v) => { let l = *v; *v := Pair(l, Refl); () } } } }
example : ok d4 = true := by native_decide

def d4lie : Decl := decl{
  fn takes (s : Σ (n : Nat) → &mut (t : List Nat ~> Σ (l : List Nat) → Id Nat (len l) (len t)))
  -> Unit { match s { Pair(n, v) => { let l = *v; *v := Pair(Cons(Z, l), Refl); () } } } }
example : rejects d4lie "does not have its owed type" = true := by native_decide

/-! ## §E. THE TWO FEATURE SPECS

    ### E.1 — Σ per-component quantity marks (the 0-mark)

    NOT the feature that opens the gate. §B is a deref-order wall and §C is a
    construction-direction wall; they are independent, and the 0-mark addresses
    only §C. Spec, from the measurements:

      * **What it must change.** `readR`'s `.ctorApp` is synthesis-only, so a
        marked component has no mode list to consult. Either `Pair` acquires a
        checking rule against an expected Σ type, or the mark rides on the
        constructor application. The read itself needs nothing: `readArgsModed`
        and `readComptimeArg` already exist and already do the ⇝-read (C4).
      * **Where it must be visible.** On the Σ FORMER, reaching `beq`/`convert`,
        because a caller's obligation is a fact about the type it sees. A capital
        binder will not do: capital Σ binders are legal and inert (C4a), and the
        one mode that IS read — the parameter's — is whole-package and refuses to
        contain a borrow (C3b).
      * **What it buys, and when.** Exactly C1/C2: packing a proof stops consuming
        it. It makes no type in §B or §D writable — and C5 shows the tax is
        ALREADY avoidable, by capitalizing the package parameter, for every
        package that does not contain a borrow. The 0-mark's sole beneficiary is a
        package mixing a borrow with a comptime component, which §B says cannot be
        written. **It should therefore be built after the E.2 prerequisite, not
        before it**; built first, it has no use site.

    ### E.2 — `*old M` over packages (loan-keyed entry snapshots)

    The premise this probe was dispatched with was that loan-keyed `*old M`
    dissolves S27SigProbe's §D wall. **It does not, and the reason is an ordering
    the var-keying was hiding.** `entrySyms` is keyed by var id, so the repair
    looks like re-keying it by loan — but no lookup is ever reached. D1's
    rejections come from `reflectC`'s `.deref` case, which fails while *reflecting
    the operand*, before `old`'s snapshot rule, before normalization, before any
    key of any kind is consulted.

    So the spec has a prerequisite, and it is the larger half:

      1. **Prerequisite — a packaged borrow must be reachable by a place.** `*`
         succeeds only on an operand that reflects DIRECTLY to a `borrowM`. `Val`
         has no deref former and the pure fragment has no borrow type (B3), so no
         projection, β-redex or `sigmaRec` arm can ever produce one. The only
         constructions that work are `.var`s naming borrow slots. Therefore
         seeding must give each packaged borrow **its own Ω slot and var name**,
         and `M` must be spelled out of those names.
      2. **Then, and only then, loan-keying.** With the borrow reachable, keying
         entry snapshots by loan rather than by telescope index is what lets
         `old *M` resolve for a borrow that has no telescope index — and
         `markExit`'s `.deref (.var v)` pattern needs the same generalization for
         the exit side.

    The prerequisite has a name. A seeding that binds every component to a named Ω
    slot, in dependency order, with the later components' types reading the
    earlier ones, is a **telescope**. S27SigProbe's §D guessed this ("a Σ telescope
    whose binders name parameters IS a telescope"); the measurements here say it is
    forced, and say why: not because `borrowVarIds` filters `.borrowT`, but because
    a borrow can only be spoken about through a name.

    ### E.3 — the verdict

    GATE CLOSED for "one runtime argument holding the borrows". The model's
    one-argument form requires (1), (2), a checking-mode `Pair`, a Σ former
    carrying marks, and the displacement of `eb510a0f` — and after all of it the
    package's internals are telescope entries wearing a Σ.

    GATE OPEN, today, for the substance: §B.4 and §B.5 run the hybrid — borrows
    named, everything else in one dependent package that reads through them, full
    M23 ensures, lie twins refused. That is the model's dependency structure minus
    its calling convention, and it needs nothing built. -/

end Dllbc.Tests.S27PkgProbe
