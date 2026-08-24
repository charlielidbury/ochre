import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.Tests.Diff

/-!
# `Dllbc.Tests.Universe` — the universe rule

Tests the universe rule: which terms inhabit `Type`. The ground formers
(`Nat`, `Bool`, `Unit`, `Bot`), the parameterised formers (`List`, `Array`),
and the binder formers (`Π`, `Σ`, `Id`) are all types. A binder's mode marker
(comptime `⇝τ`, borrow `&mut`) is not a type — a borrow-moded `Π` is a
function signature, well-formed but not a type, so checking it against
`Type` answers `false`, not an error. The payoff is value-level genericity:
a function like `fn Poly (T : Type, x : T)` can be called at any type. The
closing battery checks the type vocabulary's internal agreement — the surface's
reserved constructor names, the kernel's constructor signatures, and the
exhaustiveness table must name the same basis.

## The one design flag: `Type : Type`

This checker is type-in-type, which is inconsistent in a full theory
(Girard's paradox — a closed term of `Bot` can be built). It is accepted
here because the standing policy is consistency deferred for soundness: the
property being built is that a checked program does at run time what its
types say, and a universe hierarchy buys nothing for that while costing
every former a level argument. `Type : Type` is load-bearing rather than an
unreachable leaf: `Σ (T : Type). T` is a type only because `Type` is one,
and that shape is what the generic-function tests below depend on.
-/

namespace Dllbc.Tests.Universe

open Dllbc

/-- Type-check a closed term against a closed type in the pure seed. -/
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

def U : Term := prog_parse { Type }

/-- What the executing machine leaves in ONE binding. The whole final Ω is not
    the assertion here: it also holds the declaration's own closure, whose
    printed body is not what these programs claim. -/
def runBinding (t : Term) (name : String) : Option String :=
  match runProgram t with
  | .ok env => (env.lookup name).map Val.pretty
  | .error _ => none

/-! ## §1 The formation rules

    Each type former, checked against `Type`. The four ground constants
    first. -/

example : chkL prog_parse { Nat } U = true := by native_decide
example : chkL prog_parse { Bool } U = true := by native_decide
example : chkL prog_parse { Unit } U = true := by native_decide
example : chkL prog_parse { Bot } U = true := by native_decide

/-- `Type : Type` — the design flag from the module header, asserted
    directly. -/
example : chkL U U = true := by native_decide

/-- The two parameterised formers, including nested, which is what makes the
    recursion in the arm visible rather than incidental. -/
example : chkL prog_parse { List Nat } U = true := by native_decide
example : chkL prog_parse { List (List Nat) } U = true := by native_decide
example : chkL prog_parse { Array 3 Nat } U = true := by native_decide
example : chkL prog_parse { Array 3 (List Nat) } U = true := by native_decide

/-- The binder formers, which had arms already and keep them. -/
example : chkL prog_parse { Π (x : Nat) → Nat } U = true := by native_decide
example : chkL prog_parse { Σ (x : Nat). Nat } U = true := by native_decide
example : chkL prog_parse { Id Nat 1 1 } U = true := by native_decide

/-! ### …and the same formers at a type that is NOT `Type`

    A `false`, not an error: the expected type is checked before any parameter is
    visited, so asking `List Nat : Nat` never recurses into `Nat`. -/

example : chkL prog_parse { Nat } prog_parse { Nat } = false := by native_decide
example : chkL prog_parse { Bot } prog_parse { Nat } = false := by native_decide
example : chkL prog_parse { List Nat } prog_parse { Nat } = false := by native_decide
example : chkL prog_parse { Array 3 Nat } prog_parse { Nat } = false := by native_decide

/-- Arity is exact. `List` alone is `Type → Type` and does not inhabit `Type`;
    it falls past the formation arm to the deferral, which is the honest answer —
    a partially applied former is a neutral this judgment has no rule for, not a
    type that fails to be one. -/
example : chkL prog_parse { List } U = false := by native_decide
example : chkL prog_parse { Array 3 } U = false := by native_decide

/-! ## §2 The two binder-mode markers, refused

    `⇝τ` and `&mut (s : τ ↝ τ′)` are written where a type goes and are not
    types: they say how a binder takes its argument — comptime snapshot,
    runtime borrow — as defined in `Syntax.lean`. The refusal is an explicit
    arm rather than a fall-through, for two reasons:

      * a `Π` whose domain is `&mut …` is a function signature, and `hasType`
        already refuses to admit any value at one (`hasBorrowT ty` guards the
        closure arm) — the two refusals are the same rule, read from the two
        ends;
      * borrow types are excluded from the proof fragment: no `borrowT` may
        inhabit the universe, or a proof term could quantify over a
        borrow. -/

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
example : chkL prog_parse { &mut Nat } U = false := by native_decide

/-! ## §3 The payoff — value-level genericity

    A generic function callable at any type, and a `Σ` that packs a type
    together with a value of it. -/

/-- (a) A `Σ` packing a type: the first component is checked at `Type`, and
    the second at whatever the first turned out to be, which is what makes
    the pack dependent rather than a pair of unrelated things. -/
def sigTy : Term := prog_parse { Σ (T : Type). T }
example : chkL prog_parse { Pair(Nat, 5) } sigTy = true := by native_decide
example : chkL prog_parse { Pair(List Nat, Cons(1, Nil)) } sigTy = true := by native_decide

/-- …and it DISCRIMINATES: the payload must inhabit the type that was packed. -/
example : chkL prog_parse { Pair(Bool, 5) } sigTy = false := by native_decide

/-- (b) A generic `fn` declaration, kept as a control: declaring a generic
    function does not itself exercise the universe rule, only calling one
    does. -/
def polyDecl : Term := prog{
  fn Poly (T : Type, x : T) -> T { x };
  () }
example : progOk polyDecl = true := by native_decide

/-- (c) …and called: `Poly(Nat, 5)` checks the actual argument `Nat` against
    the parameter type `Type`. -/
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
def polyBad : Term := prog_parse {
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

/-- (f) A generic fill function whose return type is `Array n T` at a
    symbolic length and a comptime element type. Both of the `Array` arm's
    premises are live here — `n : Nat` against a telescope σ, and `T : Type`
    against the comptime parameter. -/
def MkFillFn : Term := prog_parse {
  λ (T : Type). λ (X : T). λ (N : Nat). elim N return (λ (Nm : Nat). Array Nm T) {
    Z => Arr(),
    S (M) Rec => acons M X Rec } }
def MkFillTy : Term := prog_parse { Π (T : Type) → Π (X : T) → Π (N : Nat) → Array N T }
example : chkL MkFillFn MkFillTy = true := by native_decide
example : chkL MkFillTy U = true := by native_decide

def polyArr : Term := prog{
  fn Fill (T : Type, x : T, n : Nat) -> Array n T { %MkFillFn T x n };
  () }
example : progOk polyArr = true := by native_decide

/-! ## §4 The binder formers, checked recursively

    `Π`, `Σ` and `Id` are types only if their components are: a domain, a
    codomain, or an `Id`'s carrier and endpoints that fail to be types (or
    fail to inhabit them) make the whole former `false`. -/

/-- A codomain that is not a type. -/
example : chkL prog_parse { Π (x : Nat) → 5 } U = false := by native_decide
example : chkL prog_parse { Σ (x : Nat). 5 } U = false := by native_decide

/-- A domain that is not a type. -/
example : chkL prog_parse { Π (x : 5) → Nat } U = false := by native_decide

/-- `Id` demands its endpoints inhabit its carrier — the premise `Refl`'s
    `ctorSig` entry already assumes when it converts them. -/
example : chkL prog_parse { Id Nat True True } U = false := by native_decide

/-- …and the positives the recursion has to keep. The binder is opened at a fresh
    σ carrying the domain, which is what lets a later domain MENTION an earlier
    binder (`Π (X : T)`, where `T` is the type parameter) and a codomain mention
    the length index. -/
example : chkL prog_parse { Π (T : Type) → Π (X : T) → T } U = true := by native_decide
example : chkL prog_parse { Π (n : Nat) → Array n (List Nat) } U = true := by native_decide
example : chkL prog_parse { Σ (c : Nat). Array c Nat } U = true := by native_decide

/-- A borrow-moded binder is a `false`, not §2's error. `Π (v : &mut τ) → …`
    is a well-formed thing — a function signature, which is where `fsig`
    keeps one — that does not inhabit `Type`. Asking directly whether `&mut
    τ` is a type is the category error §2 answers; the telescope-position
    question must not be routed into that one by recursion.

    The check is `atUniverse`'s second conjunct: `hasBorrowT` enforces that
    borrow types are excluded from the proof fragment — a `borrowT` may not
    occur inside an `Id`, inside a `Σ` a proof inhabits, or anywhere `Pure.nf`
    output is consumed as a proof term. -/
example :
  chkRawMsg ty{ Π (v : &mut (s : Nat ~> Nat)) → Nat } .type
    = "ok false" := by native_decide

/-- The codomain is in the exclusion too: `Π (x : Nat) → &mut Nat` is a
    signature as much as the domain case is (a `fn` returning a borrow), and
    if only the domain were tested the recursion would reach the codomain,
    hit §2's arm, and throw where it owes a verdict. `atUniverse` tests the
    whole former, which is why this is one check and not five. -/
example :
  chkRawMsg ty{ Π (x : Nat) → &mut (s : Nat ~> Nat) } .type
    = "ok false" := by native_decide

/-- Same premise, same answer, at a `List` — `List (&mut T)` is a runtime
    value only. -/
example :
  chkRawMsg ty{ List (&mut (s : Nat ~> Nat)) } .type
    = "ok false" := by native_decide
example :
  chkRawMsg ty{ Σ (c : Nat). &mut (s : Nat ~> Nat) } .type
    = "ok false" := by native_decide

/-- The comptime marker is the opposite case, and the asymmetry is the point:
    `⇝` is a legal binder mode on a domain, so a `Π` carrying one is an
    ordinary type — the arm strips before it checks. A `Σ` strips its tail
    too, since `Σ0 (x : A). P` is the comptime-second-component spelling. -/
example : chkRawMsg ty{ Π (X : Nat) → Nat } .type = "ok true" := by
  native_decide
example :
  chkRawMsg ty{ Σ0 (x : Nat). Nat } .type = "ok true" := by
  native_decide

/-! ## §5 Neutral types

    A type need not be closed: a σ (a telescope variable) or a stuck spine
    can also inhabit `Type`, once the formation rules above give them a
    `Type`-typed position to be reached in. -/

/-- Against a seeded `sctx`: `σ₀ : Type` is what a telescope's comptime type
    parameter leaves behind, and the `symOf?` case at the top of the judgment
    types it by lookup and conversion. -/
def chkS (sctx : List (Nat × Term)) (tm ty : Term) : String :=
  match (hasTypeT 8000 tm ty).run (seedPure [] sctx) with
  | .ok r _ => s!"ok {r}"
  | .error e _ => s!"error {e}"

example : chkS [(0, .type)] (Term.sym 0) .type = "ok true" := by native_decide
example : chkS [(0, .const "Nat")] (Term.sym 0) .type = "ok false" := by native_decide

/-- …and a formation OVER a type parameter, which is `List T` inside a generic
    function's own signature. -/
example : chkS [(0, .type)] prog_parse { List %(Term.sym 0) } .type = "ok true" := by native_decide
example : chkS [(0, .type)] prog_parse { Array 3 %(Term.sym 0) } .type = "ok true" := by
  native_decide
example : chkS [(0, .type)] prog_parse { Π (x : %(Term.sym 0)) → %(Term.sym 0) } .type = "ok true" := by
  native_decide

/-- A σ-headed SPINE whose signature lands in `Type` — a type-level function
    passed as a parameter, typed by the ordinary Π-instantiation the `.app` case
    already does. -/
example :
  chkS [(0, prog_parse { Π (x : Nat) → Type })] prog_parse { %(Term.sym 0) 3 } .type = "ok true" := by
  native_decide

/-- A stuck spine that lands in `Type`: `OptP` is a type-valued comptime
    function — a `boolRec` whose motive is `λ _. Type` — encoding `Option`
    via `Σ (Bool)`. At a symbolic tag it does not reduce, and the spine case
    synthesizes `Type` from the motive, which is what makes a type-level
    `match` a type. -/
def OptP : Term := prog_parse {
  λ (B : Bool). λ (T : Type). elim B return (λ (Bm : Bool). Type) {
    True => T,
    False => Unit } }
example : chkS [(0, .const "Bool")] prog_parse { %OptP %(Term.sym 0) Nat } .type = "ok true" := by
  native_decide

/-- …and the same spine under a binder, which is the type the `Σ (Bool)`
    Option encoding actually is. -/
example : chkL prog_parse { Σ (b : Bool). %OptP b Nat } U = true := by native_decide

/-! ## §6 Types have no ⇒ reading

    Types have a value-level standing only through ⇝ (§3: `Poly(Nat, 5)`
    passes `Nat` at a capital parameter, `Pair(Nat, 5)` packs it under a
    capital Σ binder). A type written or computed at a lowercase binder is
    ⇒-read instead, and has no meaningful runtime representation, so that
    reading is refused rather than allowed to hand back a type as a runtime
    datum: `readR`'s former arms are refusals (as the `.borrowT` and `.cmpT`
    arms already were), and `pureLift` refuses a type-former head on arrival
    (`Pure.typeFormerHead`) — catching both an applied former like `List Nat`
    (an `.app` spine) and a spine that merely computes to a type. -/

/-- WRITTEN bare formers at a lowercase `let`: each dies on its own removed
    arm, by name. -/
def sigWritten : Term := prog_parse { let t = Σ (l : Nat). Nat; () }
example : progRejects sigWritten "no ⇒ reading" = true := by native_decide

def piWritten : Term := prog_parse { let t = Π (x : Nat) → Nat; () }
example : progRejects piWritten "no ⇒ reading" = true := by native_decide

def typeWritten : Term := prog_parse { let t = Type; () }
example : progRejects typeWritten "no ⇒ reading" = true := by native_decide

def idWritten : Term := prog_parse { let t = Id Nat 1 1; () }
example : progRejects idWritten "no ⇒ reading" = true := by native_decide

/-- WRITTEN applied formers: `List Nat` is `.app (.const "List") (.const
    "Nat")`, so it reaches the pure lift through `readR`'s `.app` arm and is
    refused there, by its head. -/
def listApplied : Term := prog_parse { let t = List Nat; () }
example : progRejects listApplied "⇒ produced a type" = true := by native_decide

def arrApplied : Term := prog_parse { let t = Array 2 Nat; () }
example : progRejects arrApplied "⇒ produced a type" = true := by native_decide

/-- COMPUTED: a pure spine that whnf's to a type — `OptP True Nat` reduces to
    `Nat` — arriving at a lowercase `let`. Nothing about the WRITTEN form says
    "type"; only the lift's head test can catch it. -/
def computedType : Term := prog_parse { let t = %OptP True Nat; () }
example : progRejects computedType "⇒ produced a type" = true := by native_decide

/-- The program's TAIL is ⇒-read too, and a type there refuses through the same
    arm — there is no separate tail admission to forget. -/
def tailType : Term := prog_parse { let x = 1; Σ (l : Nat). Nat }
example : progRejects tailType "no ⇒ reading" = true := by native_decide

/-- A constructor FIELD is ⇒-read (`readArgs` reads a `ctorApp`'s arguments
    with no type in hand), so a type written inside one hits the same arms.
    The TYPED route stays open: `Pair(Nat, 5)` at `Σ (T : Type). T` reads its
    first component by the capital binder's ⇝ — §3(a) above. -/
def ctorFieldType : Term := prog_parse { let l = Cons(Nat, Nil); () }
example : progRejects ctorFieldType "no ⇒ reading" = true := by native_decide

/-- A `fn` whose RUNTIME body returns a type: the body's tail is read against
    the declared return type (`readResult`), `Type` pins no Σ/⇝ route, so the
    tail falls to `readR` and dies on the removed `Σ` arm — inside the seal's
    audit, before the binding. -/
def fnRetType : Term := prog_parse {
  fn Bad (x : Nat) -> Type { Σ (l : Nat). Nat };
  () }
example : progRejects fnRetType "no ⇒ reading" = true := by native_decide

/-- The ⇝ channel is untouched: the same Σ at a capital `let` checks and
    runs; §3's Poly/Pair battery above is the value-level half of the same
    story. -/
def sigCapital : Term := prog{ let NatPair = Σ (l : Nat). Nat; () }
example : progOk sigCapital = true := by native_decide
example : progRuns sigCapital = true := by native_decide

/-! ### The head vocabulary agrees with the exhaustiveness table

    `Pure.typeFormerHead`'s const-name row and `Pure.typeCtors`'s rows must
    agree — a former added to one and not the other lets a type ⇒ silently
    move again. Checked both directions, over the basis: every type
    `typeCtors` answers for has a type-former head, and every const name the
    head test refuses is a former `typeCtors` knows (applied, where
    application is what makes it a type). -/

def formerBasis : List Term :=
  [prog_parse { Nat }, prog_parse { Bool }, prog_parse { Unit }, prog_parse { Bot }, prog_parse { List Nat },
   prog_parse { Σ (X : Nat). Nat }, prog_parse { Id Nat unit unit }, prog_parse { Array 2 Nat }]
example : formerBasis.all Pure.typeFormerHead = true := by native_decide
example : (["Nat", "Bool", "Unit", "Bot"].all
      (fun c => (Pure.typeCtors (.const c)).isSome)
    && (Pure.typeCtors prog_parse { List Nat }).isSome
    && (Pure.typeCtors prog_parse { Array 2 Nat }).isSome) = true := by native_decide

/-- …and the heads the lift must KEEP lifting are not in the vocabulary: a
    stuck recursor spine (a runtime list value in checking mode), a
    constructor, a σ. -/
example : Pure.typeFormerHead
    (.app (.app (.const "natRec") (.const "@motive")) (.ctorApp "Z" [])) = false := by
  native_decide
example : Pure.typeFormerHead (.ctorApp "Cons" [.ctorApp "Z" [], .ctorApp "Nil" []]) = false := by
  native_decide
example : Pure.typeFormerHead (Term.sym 0) = false := by native_decide

end Dllbc.Tests.Universe

section
namespace Dllbc.Tests.S33Macro
open Dllbc Dllbc.Tests

/-! ## The same function, written twice — the surface and the kernel

    The kernel's `Add` is a hand-written `Term` (`Pure.kAddFn`), because the
    carve rule's premises are stated against it and a kernel rule cannot cite
    a library it does not import. The surface can say the same thing
    (`surfAdd`), and this battery checks that the two spellings are actually
    one term rather than merely two terms that compute the same answer.

    Conversion is mode-blind (`Term.convEq`), and both are `natRec` over the
    same arms, so they always denoted the same function. What is checked here
    is stronger: `Term.alphaEq` — the key `abstractInto` generalizes with — is
    mode-sensitive, so agreeing under it also means every comptime/runtime
    marker matches between the two spellings, right down to the recursor's
    arm binders and its unwritable motive binder `§_`. -/

def surfAdd : Term :=
  prog_parse { λ (A : Nat). λ (B : Nat). elim A return (λ (N : Nat). Nat) { Z => B, S (A') R => S(R) } }

-- `surfAdd` names its motive binder `N` where the kernel names it `Am`, so
-- this line says two independently-written surface spellings of `Add` are one
-- term up to α — and since `Term.alphaEq` is mode-sensitive, it is also
-- saying every marker agrees.
example : Term.alphaEq surfAdd Pure.kAddFn = true := by native_decide
example : (Pure.nf 1000 surfAdd == Pure.nf 1000 Pure.kAddFn) = true := by native_decide
example : Term.convEq (Pure.nf 1000 surfAdd) (Pure.nf 1000 Pure.kAddFn) = true := by native_decide

-- The behaviour, so that a later respell that agrees structurally and computes
-- something else cannot pass on the two lines above.
example : (Pure.nf 200 ty{ %surfAdd 2 3 } == Term.nat 5) = true := by
  native_decide

/-! ## The constructor basis, checked instead of kept adjacent

    `Val.ctorNames` is the list the surface reserves as binder keywords, and
    `Pure.ctorSig` is the kernel's field-type table. They must agree, and a
    build failure enforces that now rather than a comment noting they sit next
    to each other.

    Both directions. Every reserved name has a signature; and every
    constructor the exhaustiveness table can name, at each type former there
    is, is reserved. The second is what catches a constructor added to
    `ctorSig` and `typeCtors` and forgotten at the surface. -/

def basisTypes : List Term :=
  [prog_parse { Nat }, prog_parse { Bool }, prog_parse { Unit }, prog_parse { Bot }, prog_parse { List Nat },
   prog_parse { Σ (X : Nat). Nat }, prog_parse { Id Nat unit unit }, prog_parse { Array 2 Nat }]

example : Val.ctorNames.all (fun n => (Pure.ctorSig n).isSome) = true := by native_decide
example : basisTypes.all (fun ty => ((Pure.typeCtors ty).getD []).all
    (fun c => Val.ctorNames.contains c)) = true := by native_decide

-- …and the control the two lines above need: a name outside the basis has no
-- signature, so the first is a claim about this list rather than about `ctorSig`
-- answering for everything.
example : (Pure.ctorSig "Cons2").isNone = true := by native_decide

end Dllbc.Tests.S33Macro
end
