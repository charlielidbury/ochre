import Dllbc.Machine
import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.StdLemmas

/-!
# The kernel floor — the pure fragment, the fording layer, and the surface's own report card

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S4Pure.lean`
  * `S10Ford.lean`
  * `S11Lib.lean`
  * `S15Elab.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S4Pure.lean` ──────────────────────────────────────────────
section
/-!
# §4 test suite — the pure fragment (⇝, conversion, value typing)

β/ι reduction via `readC` (the ⇝ arrow), stuck neutrals and conversion, the
large-elimination flagship (`VecF` — a `Vec`-shaped type family computed by
`natRec`, converting under a stuck index), and value typing (`hasType`) against
the fixed constructor basis. Prior suites are untouched and green.

**This file is deliberately EXEMPT from the end-to-end test rule** (every
assertion a program accepted, rejected, or run to a value). It is the one place
that asserts about the kernel directly, and the exemption is load-bearing:

* **It is the kernel floor.** Reduction, conversion and value typing are probed
  through the checker's own API — `readC`, `convert`, `hasType` — with no macro
  anywhere in the loop. A macro regression therefore cannot move a single subject
  in this file, which is what makes a red line here mean the kernel changed.
* **It is the control group.** When a kernel change turns the corpus red, this
  file says whether the rules moved or only their surface did; a test suite whose
  every subject is elaborated cannot answer that question about itself.
* **It is the hand-built anchor.** The surface layers are pinned by round-trips
  against terms built by hand (S15Elab checks `StdLemmas.LeRefl`, authored in
  `prog{ }`, convertible with the hand-built `Std.le_reflT`). Those anchors are
  only worth something if the hand-built side is independently exercised, which is
  this file's `Add`/`VecF`/recursor library.

**The OLD reason is superseded, and is recorded here so a future simplification
pass does not refute it and delete an exempted file.** The header used to say
"pure terms have no surface syntax, so the library is built directly from the
pure `Term`/`Val` formers". That was true at §4 and false since §15: `prog{ … }`
authors pure terms, and `StdLemmas` is written in it. The rawness here is a
CHOICE about what is under test, not a gap in the grammar.

σ's are seeded via a variable slot (`readC` reads the snapshot).
-/

open Dllbc
open Dllbc.Term (nat)

namespace Dllbc.Tests.S4Pure

-- SUBJECT FILE: the whole library here is built directly from raw Term/Val formers,
-- and the rawness is the POINT rather than a missing grammar (`prog{ }` would author
-- every one of these since §15) — these raw constructions ARE the subject under test
-- (reduction, hasType, convert), reached with no macro in the loop. Every raw
-- constructor below is intentional test machinery. See the exemption in the header.

/-! ## Pure library (built from the raw formers) — SUBJECT: raw pure Terms under test -/

def natT : Term := .const "Nat"
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-- `Add m n = natRec (λ_.Nat) n (λ_. λr. S r) m`. -/
def addT : Term :=
  .lam "m" natT (.lam "n" natT
    (.app (.app (.app (.app (.const "natRec") (.lam "_" natT natT)) (.pvar "n"))
      (.lam "_" natT (.lam "r" natT (.ctorApp "S" [.pvar "r"])))) (.pvar "m")))

/-- `VecF T n = natRec (λ_.Type) Unit (λn'. λrec. Σ(_:T). rec) n` — a `Vec`-shaped
    family by large elimination (§4.2's `VecF Nat Z = Unit`, `VecF Nat (S n) =
    Σ (_:Nat). VecF Nat n`). -/
def vecFT : Term :=
  .lam "T" .type (.lam "n" natT
    (.app (.app (.app (.app (.const "natRec") (.lam "_" natT .type)) (.const "Unit"))
      (.lam "n'" natT (.lam "rec" .type (.sigmaT "_" (.pvar "T") (.pvar "rec"))))) (.pvar "n")))

/-- `boolRec (λ_.Nat) t f b`. -/
def boolRecNat (t f b : Term) : Term :=
  .app (.app (.app (.app (.const "boolRec") (.lam "_" (.const "Bool") natT)) t) f) b

/-- A slot holding `σ0`, and the term reading it. -/
def sVar : Term := .var ⟨0, "s"⟩
def seedS : Omega := [(⟨0, "s"⟩, .sym 0)]

/-! ## β / ι reduction (⇝) — SUBJECT: raw pure Terms under reduction test -/

-- add 2 3 ⇝ 5.
example : expectReadC [] [] (.app (.app addT (tnat 2)) (tnat 3)) (nat 5) = true := by native_decide

-- boolRec both ways.
example : expectReadC [] [] (boolRecNat (tnat 7) (tnat 9) (.ctorApp "True" [])) (nat 7) = true := by
  native_decide
example : expectReadC [] [] (boolRecNat (tnat 7) (tnat 9) (.ctorApp "False" [])) (nat 9) = true := by
  native_decide

-- botElim never fires (⊥ has no constructors): `botElim Nat σ` is a stuck value.
example : expectReadC seedS [] (.app (.app (.const "botElim") natT) sVar)
  (.app (.app (.const "botElim") (.const "Nat")) (.sym 0)) = true := by native_decide

/-! ## Stuck neutrals and conversion -/

-- add σ 1 evaluates to the canonical stuck spine `natRec (λ_.Nat) 1 step σ`.
-- The expected value is READBACK OUTPUT, so its binders are the reserved
-- level-named ones readback mints (`§0`, `§1`) rather than the source's — which is
-- the canonicality property this file is the control group for, written down.
example : expectReadC seedS [] (.app (.app addT sVar) (tnat 1))
  (.app (.app (.app (.app (.const "natRec") (.lam "§0" (.const "Nat") (.const "Nat"))) (nat 1))
    (.lam "§0" (.const "Nat") (.lam "§1" (.const "Nat") (.ctorApp "S" [.pvar "§1"])))) (.sym 0)) = true := by
  native_decide

-- Conversion of stuck neutrals: reflexive, and sensitive to the argument.
example : expectConv seedS [] (.app (.app addT sVar) (tnat 1)) (.app (.app addT sVar) (tnat 1))
  = true := by native_decide
example : expectConv seedS [] (.app (.app addT sVar) (tnat 1)) (.app (.app addT sVar) (tnat 2))
  = false := by native_decide

/-! ## Large elimination (the flagship): computation under a stuck index
    SUBJECT: raw pure Terms (VecF etc.) under the conversion test. -/

-- `VecF Nat (S σ)` CONVERTS to `Σ (_:Nat). VecF Nat σ` — natRec proceeding past a
-- stuck index, the property §4.2's dependent push stands on.
example : expectConv seedS []
  (.app (.app vecFT natT) (.ctorApp "S" [sVar]))
  (.sigmaT "_" natT (.app (.app vecFT natT) sVar)) = true := by native_decide

/-! ## Value typing -/

-- Val-level library (hasType works on values).
def natV : Term := .const "Nat"
def listNat : Term := .app (.const "List") natV
def vecFV : Term :=
  .lam "T" .type (.lam "n" natV
    (.app (.app (.app (.app (.const "natRec") (.lam "_" natV .type)) (.const "Unit"))
      (.lam "n'" natV (.lam "rec" .type (.sigmaT "_" (.pvar "T") (.pvar "rec"))))) (.pvar "n")))
/-- `Σ (l : Nat). VecF Nat l` (the l is a genuine dependency). -/
def sigVecF : Term := .sigmaT "l" natV (.app (.app vecFV natV) (.pvar "l"))

-- Positives: `Cons σₑ σ : List Nat` under sctx = {σₑ : Nat, σ : List Nat};
-- `Pair 1 p : Σ (l:Nat). VecF Nat l` with `p = Pair 5 unit : VecF Nat 1` — the
-- second field's type is instantiated at the first field's value.
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctorApp "Cons" [.sym 0, .sym 1]) listNat = true := by native_decide

example : expectHasType [] []
  (.ctorApp "Pair" [nat 1, .ctorApp "Pair" [nat 5, .ctorApp "unit" []]]) sigVecF = true := by native_decide

-- Negatives: wrong constructor for the type; a `Pair` whose second field fails
-- the instantiated type (`True` does not inhabit `VecF Nat 1`).
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctorApp "Cons" [.sym 0, .sym 1]) (.const "Bool") = false := by native_decide

example : expectHasType [] []
  (.ctorApp "Pair" [nat 1, .ctorApp "True" []]) sigVecF = false := by native_decide

/-! ## Conversion negative under a binder -/

-- Two λ's that differ only in their bodies are not convertible (no eta; bodies
-- compared structurally after normalization, which renames both binders to the
-- same level name and so cannot be what tells them apart).
example : Pure.convert 1000 (.lam "u" natV (.pvar "u")) (.lam "u" natV (.ctorApp "Z" [])) = false := by
  native_decide

/-! ## Readback is CANONICAL (M30 step 2)

    Binders are source names now, and `convert` is still `nfV a == nfV b` — a
    *literal* comparison of normal forms. That is only sound because `readback`
    renames every binder it opens to `readbackName ⟨its level⟩`, so a normal form
    does not remember what its binders were called. Six assertions, because the
    property is load-bearing for every conversion in the calculus and is the thing
    a future change to `readback` would break silently:

      1. the renaming happens, and to the reserved namespace;
      2. it is by LEVEL, so nesting is what distinguishes binders;
      3. two α-variant functions therefore normalize to the same tree;
      4. …and are convertible, which is (3) read through the rule that uses it;
      5. shadowing means the INNER binder, without a gensym anywhere;
      6. and the renaming does not make everything equal — the no-η negative
         above and this one are what say it is a renaming and not an erasure.

    A source program cannot write a reserved name (`Surface.reservedBinder`
    refuses one, and the tokenizer would need an escaped identifier to offer it),
    so nothing a program writes can collide with what readback mints. -/

-- (1) and (2): the binder a normal form carries is its level, in the reserved
-- namespace. Written as the whole tree rather than as a predicate, so a change to
-- the naming scheme fails HERE and says what it changed to.
example : (Pure.nf 1000 (.lam "x" natV (.pvar "x")) == .lam "§0" natV (.pvar "§0")) = true := by
  native_decide
example : (Pure.nf 1000 (.lam "a" natV (.lam "b" natV (.app (.pvar "a") (.pvar "b"))))
            == .lam "§0" natV (.lam "§1" natV (.app (.pvar "§0") (.pvar "§1")))) = true := by
  native_decide

-- (3): two α-variants of one function read back to the SAME tree — not merely to
-- convertible ones, which is the weaker fact `convert` would still give if
-- readback minted from a counter.
example : (Pure.nf 1000 (.lam "a" natV (.lam "b" natV (.app (.pvar "a") (.pvar "b"))))
            == Pure.nf 1000 (.lam "p" natV (.lam "q" natV (.app (.pvar "p") (.pvar "q"))))) = true := by
  native_decide

-- (4): and so they convert. (Under the de Bruijn representation this was true for
-- a reason that no longer exists — the binders had no names to differ in.)
example : Pure.convert 1000 (.lam "x" natV (.pvar "x")) (.lam "y" natV (.pvar "y")) = true := by
  native_decide

-- (5): SHADOWING IS THE SCOPE RULE. `λ (x : Nat). λ (x : Nat). x` is the second
-- projection, and both halves are asserted — it converts with `λ a. λ b. b` and
-- does NOT convert with `λ a. λ b. a`. Nothing was renamed to make this work;
-- the evaluator's environment is prepended to and the lookup finds the first hit.
example : Pure.convert 1000 (.lam "x" natV (.lam "x" natV (.pvar "x")))
                           (.lam "a" natV (.lam "b" natV (.pvar "b"))) = true := by native_decide
example : Pure.convert 1000 (.lam "x" natV (.lam "x" natV (.pvar "x")))
                           (.lam "a" natV (.lam "b" natV (.pvar "a"))) = false := by native_decide

-- (6): the renaming is not an erasure — two functions that differ in WHICH binder
-- they return stay distinct after it.
example : Pure.convert 1000 (.lam "a" natV (.lam "b" natV (.pvar "a")))
                           (.lam "a" natV (.lam "b" natV (.pvar "b"))) = false := by native_decide

-- The namespace itself: what readback mints is reserved, and a source binder may
-- not be. The second is the surface check rather than the tokenizer, because an
-- escaped Lean identifier (`«§0»`) would otherwise slip one through.
example : Dllbc.isReservedName (Dllbc.readbackName 0) = true := by native_decide
example : Dllbc.Surface.reservedBinder "§0" = true := by native_decide
example : Dllbc.Surface.reservedBinder "x" = false := by native_decide

end Dllbc.Tests.S4Pure
end
-- └── end of what was `S4Pure.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S10Ford.lean` ──────────────────────────────────────────────
section
/-!
# §10 test suite — the fording kit: `Id`, `J`, `K`, and the minimal indexed match

The milestone that closes the `Id`/`J`/`K` gap. The **kernel** gains exactly
three things: the type former `Id A a b`, its sole constructor `Refl`, and the
two eliminator constants `j` (Paulin-Mohring J) and `k` (Streicher K) — whose
ι-rules fire on `Refl`. Plus one machine rule: matching a symbolic `p : Id A a b`
against `Refl` is the **solution transition** — whnf both endpoints; if one is a
substitutable σ (occurs-checked against the other), `⇜`-refine it to the other
endpoint everywhere; if both are rigid, STUCK (naming `j`/`k` as the route). No
unification beyond solution: injectivity, conflict, cycle are the *library's* job.

The point of the milestone is the last clause: everything past the solution
transition is **terms, not rules**. The second half of this file derives the
whole no-confusion toolkit *inside* the calculus — `NatCode` by double `natRec`,
`natNoConf` and injectivity by `J`, `UIP` by `K`, and the conflict discharge
(`⊥` from `Id Nat Z (S n)`, eliminated to any type) — each a checked term.

The eliminator neutrals are typed by `hasType`'s §10 synthesis (`j A a P d b p :
P b p`, `k A a P d p : P p`, `botElim T x : T`); that is what lets the library
derivations type-check as ordinary terms.

**The declaration half is written as programs** (M28 ν): `fn` is a statement, so
each fording test is a program that declares one function and returns `()`. The
library half below is untouched — it is `hasType` derivations over `Val`s, which
never went through a declaration form at all.
-/

open Dllbc
open Dllbc.Term

namespace Dllbc.Tests.S10Ford

/-! ## Pure library, as `Val`s (types and proofs are terms) -/

def natV : Term := .const "Nat"
def sZ : Term := .ctorApp "Z" []
def sS (v : Term) : Term := .ctorApp "S" [v]
def vnat : Nat → Term | 0 => sZ | n + 1 => sS (vnat n)
def refl : Term := .ctorApp "Refl" []
def unitV : Term := .ctorApp "unit" []

def natRecV (P z s n : Term) : Term := .app (.app (.app (.app (.const "natRec") P) z) s) n
def jV (a aa P d b p : Term) : Term := .app (.app (.app (.app (.app (.app (.const "j") a) aa) P) d) b) p
def kV (a aa P d p : Term) : Term := .app (.app (.app (.app (.app (.const "k") a) aa) P) d) p
def botElimV (t x : Term) : Term := .app (.app (.const "botElim") t) x

/-- `NatCode : Nat → Nat → Type` by double `natRec`: `(Z,Z) ↦ ⊤`, `(S,S) ↦`
    code of predecessors, mixed `↦ ⊥`. The diagonal `NatCode a a` is `⊤`. -/
def zCase : Term :=
  .lam "b" natV (natRecV (.lam "_" natV .type) (.const "Unit")
    (.lam "_" natV (.lam "_" .type (.const "Bot"))) (.pvar "b"))
def sCase : Term :=
  .lam "a'" natV (.lam "recA" (.pi "_" natV .type) (.lam "b" natV
    (natRecV (.lam "_" natV .type) (.const "Bot")
      (.lam "b'" natV (.lam "_" .type (.app (.pvar "recA") (.pvar "b'")))) (.pvar "b"))))
def natCodeV : Term := .lam "a" natV (natRecV (.lam "_" natV (.pi "_" natV .type)) zCase sCase (.pvar "a"))
def natCode (a b : Term) : Term := .app (.app natCodeV a) b

/-- `Pred : Nat → Nat` (`Pred Z = Z`, `Pred (S n) = n`). -/
def predV : Term :=
  .lam "n" natV (natRecV (.lam "_" natV natV) sZ (.lam "m" natV (.lam "_" natV (.pvar "m"))) (.pvar "n"))

/-! ## §10 kernel: the ι-rules (`j` and `k` fire on `Refl`)

    `j A a P d b p` and `k A a P d p` reduce to `d` when the proof is `Refl`;
    on a symbolic proof they are stuck neutral values. (The motive is irrelevant
    to reduction — ι fires on the proof.) -/

-- j Nat Z P 42 Z Refl ↦ 42
example : (Pure.nf 1000 (jV natV sZ (.lam "b" natV (.lam "q" natV natV)) (vnat 42) sZ refl) == vnat 42) = true := by
  native_decide

-- k Nat Z P 7 Refl ↦ 7
example : (Pure.nf 1000 (kV natV sZ (.lam "q" natV natV) (vnat 7) refl) == vnat 7) = true := by native_decide

-- On a *symbolic* proof (sym 0), `j` does not fire — it is a stuck value, not 42.
example : (Pure.nf 1000 (jV natV sZ (.lam "b" natV (.lam "q" natV natV)) (vnat 42) sZ (.sym 0)) == vnat 42) = false := by
  native_decide

/-! ## The Refl-match: the solution transition (owned and through a borrow)

    The workhorse. Matching a symbolic `p : Id A a b` against `Refl` refines the
    substitutable endpoint everywhere — Ω, `sctx`, *and* the owed obligations. -/

-- `learn (n : Nat, p : Id Nat n 2) → Nat = match p { Refl => n }`. The match
-- refines `n := 2`; the body returns `n`, now a concrete `2` typed against Nat.
-- (An inter-parameter dependency is written with the earlier param's RUNTIME
-- var — `Id Nat n 2` — resolved by the `readC` snapshot read, not a pure de
-- Bruijn index.)
def learn : Term := prog{
  fn Learn (n : Nat, p : Id Nat n 2) -> Nat { match p { Refl => n } };
  () }

example : progOk learn = true := by native_decide

-- The refinement is OBSERVABLE in the final Ω: after the match, `let m = n`
-- copies the *refined* value, so `m ↦ 2` (not a symbolic `n`). Had refinement
-- not fired, `m` would be a `sym`.
def learnObs : Term := prog{
  fn LearnObs (n : Nat, p : Id Nat n 2) -> Unit { match p { Refl => { let m = n; () } } };
  () }

-- Its Ω assertion died with `checkFn` (below), and until this file migrated the
-- only thing still reading it was `S26Migrate.p10` — a pool, i.e. inventory. So
-- it gets the assertion the pool's `progVerdict` was computing for it anyway:
-- the declaration checks. That is weaker than what it was written for and
-- stronger than nothing, and `learnDemand` below is where the claim actually
-- went.
example : progOk learnObs = true := by native_decide

/-! ### The refinement, CONVERTED from an Ω observation to a DEMAND (M27-δ)

    `learnObs` asserted the refinement by looking at the final Ω: after the match,
    `let m = n` copies the REFINED value, so `m ↦ 2` and not a σ. That assertion
    could not survive `checkFn` — a body with a telescope is entered only inside
    the seal's isolated frame, whose Ω is discarded by design.

    So it is restated as what a body can PROVE under the refinement rather than
    what the machine happens to hold: `(Refl : Id Nat m 2)` is a certificate
    that typechecks **only if** `m`'s snapshot is concretely `2`. Unrefined, `m` is
    a σ and `Refl` does not inhabit `Id Nat σ 2`.

    That is the per-demand-site doctrine applied to the kernel's own tests, and it
    is a strictly better assertion than the one it replaces: it says the
    refinement is USABLE, where the Ω observation only said it was recorded. -/

def learnDemand : Term := prog{
  fn LearnDemand (n : Nat, p : Id Nat n 2) -> Unit {
    match p { Refl => { let m = n; let c = (Refl : Id Nat m 2); () } } };
  () }
example : progOk learnDemand = true := by native_decide

-- THE TWIN, and it is what makes the certificate a demand rather than a
-- decoration: the same `let m = n` and the same seal with the match REMOVED. `m`
-- is unrefined, so `Refl` has nothing to inhabit.
def learnDemandNo : Term := prog defer_check {
  fn LearnDemandNo (n : Nat, p : Id Nat n 2) -> Unit {
    let m = n; let c = (Refl : Id Nat m 2); () };
  () }
example : progRejects learnDemandNo "does not have its ascribed type"
  = true := by native_decide

-- Through a borrow: `pb : &mut (Id Nat n 2)`. The refl-match reads through the
-- borrow, refines `n := 2`, and — because refinement now reaches the owed
-- obligations — the audit sees `pb` owing `Id Nat 2 2`, which its `Refl` payload
-- inhabits. This is the case that forced obligations into machine state.
def learnBorrow : Term := prog{
  fn LearnBorrow (n : Nat, pb : &mut (Id Nat n 2)) -> Unit {
    match pb { Refl => { let m = n; () } } };
  () }

example : progOk learnBorrow = true := by native_decide

-- …and the same conversion through the borrow, so the demand form covers both
-- routes the refinement takes rather than only the owned one.
def learnBorrowDemand : Term := prog{
  fn LearnBorrowDemand (n : Nat, pb : &mut (Id Nat n 2)) -> Unit {
    match pb { Refl => { let m = n; let c = (Refl : Id Nat m 2); () } } };
  () }
example : progOk learnBorrowDemand = true := by native_decide

-- Rigid-rigid: `p : Id Nat Z (S Z)`. Neither endpoint is a σ, so there is no
-- solution by refinement — STUCK, naming `j`/`k` as the elimination route. The
-- kernel does NOT auto-discharge the conflict; that is the library's job (below).
def rigidStuck : Term := prog defer_check {
  fn RigidStuck (p : Id Nat 0 1) -> Nat { match p { Refl => 0 } };
  () }

example : progRejects rigidStuck "rigid" = true := by native_decide
example : progRejects rigidStuck "j/k" = true := by native_decide

-- Occurs check: `p : Id Nat n (S n)`. Refining `n := S n` would be cyclic —
-- rejected before it can loop.
def occursFn : Term := prog defer_check {
  fn Occ (n : Nat, p : Id Nat n (S n)) -> Unit { match p { Refl => () } };
  () }

example : progRejects occursFn "occurs check" = true := by native_decide

/-! ## Exhaustiveness and scope (Id's constructor set is `{Refl}`) -/

-- An empty match on `p : Id Nat n 2` is non-exhaustive: `Refl` is uncovered.
example : progRejects (prog defer_check {
  fn F (n : Nat, p : Id Nat n 2) -> Unit { match p { } }; () }) "non-exhaustive" = true := by native_decide

-- A stray non-`Refl` constructor is likewise not enough to be exhaustive.
example : progRejects (prog defer_check {
  fn F (n : Nat, p : Id Nat n 2) -> Unit { match p { Z => () } }; () }) "non-exhaustive" = true := by native_decide

-- Scope guard: `Id` over a *borrow* type is rejected — reflecting the borrow-type
-- index throws (borrow types live only at telescope positions), no special
-- machinery needed. (Id over ordinary indexed types is unrestricted.)
example : progRejects (prog defer_check {
  fn F (q : Id (&mut Nat) 0 0) -> Unit { () }; () }) "borrow type" = true := by native_decide

/-! ## The fording library — no confusion, injectivity, K, all as checked terms

    Beyond the solution transition, everything is a term. These are `hasType`
    derivations: a proof term is checked against its goal type under a σ-context
    seeding the free variables. The eliminator neutrals are typed by §10
    synthesis. -/

/-! ### `natNoConf` (specialized at `Z`) and the conflict discharge

    `natNoConf` via `J`: from `p : Id Nat Z b`, a proof of `NatCode Z b`, with
    base `unit : NatCode Z Z = ⊤`. At `b = S n` the code whnf's to `⊥` — so
    `natNoConf` gives `⊥` from a `Z = S n` identity, and `botElim` sends it to
    any type. This is the impossible branch, discharged with ordinary terms. -/

-- P = λb'. λ_ : Id Nat Z b'. NatCode Z b'
def nncMotive : Term :=
  .lam "b" natV (.lam "q" (.idT natV sZ (.pvar "b")) (.app (.app natCodeV sZ) (.pvar "b")))
def nncProof (n p : Term) : Term := jV natV sZ nncMotive unitV (sS n) p
-- σ0 = n : Nat, σ1 = p : Id Nat Z (S n)
def nncSctx : List (Nat × Term) := [(0, natV), (1, .idT natV sZ (sS (.sym 0)))]

-- `natNoConf p : NatCode Z (S n)`, and — since that code reduces — `: ⊥`.
example : expectHasType [] nncSctx (nncProof (.sym 0) (.sym 1)) (natCode sZ (sS (.sym 0))) = true := by
  native_decide
example : expectHasType [] nncSctx (nncProof (.sym 0) (.sym 1)) (.const "Bot") = true := by native_decide

-- Conflict discharge: `botElim T (natNoConf p) : T` for any `T` — the impossible
-- branch eliminated to an arbitrary return type.
example : expectHasType [] nncSctx (botElimV natV (nncProof (.sym 0) (.sym 1))) natV = true := by
  native_decide
example : expectHasType [] nncSctx (botElimV (.const "Bool") (nncProof (.sym 0) (.sym 1))) (.const "Bool") = true := by
  native_decide

/-! ### Injectivity of `S`: `Id Nat (S a) (S b) → Id Nat a b`, via `J`

    Motive `P y (_ : Id Nat (S a) y) = Id Nat a (Pred y)`; base `Refl : Id Nat a
    (pred (S a)) = Id Nat a a`; transported to `Id Nat a (pred (S b)) = Id Nat a
    b`. (`pred (S σ)` reduces because the `S` is concrete around the symbol.) -/

def injMotive (a : Term) : Term :=
  .lam "y" natV (.lam "q" (.idT natV (sS a) (.pvar "y")) (.idT natV a (.app predV (.pvar "y"))))
def injProof (a b p : Term) : Term := jV natV (sS a) (injMotive a) refl (sS b) p
def injSctx : List (Nat × Term) := [(0, natV), (1, natV), (2, .idT natV (sS (.sym 0)) (sS (.sym 1)))]

example : expectHasType [] injSctx (injProof (.sym 0) (.sym 1) (.sym 2)) (.idT natV (.sym 0) (.sym 1)) = true := by
  native_decide

-- The proof genuinely proves `Id Nat a b`, not a wrong goal like `Id Nat a (S b)`.
example : expectHasType [] injSctx (injProof (.sym 0) (.sym 1) (.sym 2)) (.idT natV (.sym 0) (sS (.sym 1))) = false := by
  native_decide

/-! ### UIP / K: `(p : Id Nat a a) → Id (Id Nat a a) p Refl`, via `K`

    Streicher K: motive `P q = Id (Id Nat a a) q Refl`, base `Refl : Id … Refl
    Refl`, so `k … p : Id (Id Nat a a) p Refl` — uniqueness of identity proofs,
    a decided commitment of this kernel. -/

def idAA (a : Term) : Term := .idT natV a a
def uipMotive (a : Term) : Term := .lam "q" (idAA a) (.idT (idAA a) (.pvar "q") refl)
def uipProof (a p : Term) : Term := kV natV a (uipMotive a) refl p
def uipSctx : List (Nat × Term) := [(0, natV), (1, idAA (.sym 0))]

example : expectHasType [] uipSctx (uipProof (.sym 0) (.sym 1)) (.idT (idAA (.sym 0)) (.sym 1) refl) = true := by
  native_decide

/-! ### `NatCode` computes (the double-`natRec` corners) -/

example : (Pure.convert 1000 (natCode sZ sZ) (.const "Unit")) = true := by native_decide       -- (Z,Z) ↦ ⊤
example : (Pure.convert 1000 (natCode sZ (sS sZ)) (.const "Bot")) = true := by native_decide    -- (Z,S) ↦ ⊥
example : (Pure.convert 1000 (natCode (sS sZ) sZ) (.const "Bot")) = true := by native_decide    -- (S,Z) ↦ ⊥
example : (Pure.convert 1000 (natCode (vnat 2) (vnat 2)) (.const "Unit")) = true := by native_decide  -- diagonal ↦ ⊤

end Dllbc.Tests.S10Ford
end
-- └── end of what was `S10Ford.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S11Lib.lean` ──────────────────────────────────────────────
section
/-!
# §11 test suite — the pure lift

The kernel move this milestone is the **pure lift (§1.3)**: on the borrow-free
fragment ⇒ coincides with ⇝ up to consumption, so a body may ⇒-produce a
comptime-only term (a proof — an eliminator application, `Refl`, a Π-typed λ) and
store, pass, or return it as an ordinary datum. That is the M10 conflict discharge
in the shape the fording spec wanted: a dead branch whose body is
`botElim T (natNoConf p)`.

Three programs say it: a proof RETURNED, a proof STORED in a Σ's dependent second
field, and a proof CONSUMED to close a dead branch.

**The rest of §11 dissolved (M28).** The milestone also landed `listRec`,
`natRec`/`boolRec` neutral synthesis, λ-vs-Π typing, pure `let` in `readC`, and
`Dllbc.Std` (`Le`, `Eqb`/`Leb`, `Count`, `Bound`/`Sorted`, `LeRefl`). Those were
tested here by `Pure.convert`/`Pure.nf` computation probes and `expectHasType`
inhabitation probes — granular meta-assertions that the corpus has long since
subsumed. Every bound in a checked program forces `Le` to compute (an ex-falso
branch is precisely `Le (S n) Z` computing to `Bot`); every count postcondition
forces `Count`, and `Count` is `listRec` threading a `boolRec` on `Eqb`; every
`Sorted`/`Bound` spec forces the predicates by inhabitation, and the
out-of-bounds rejections are the no-inhabitant fact. `LeRefl` is checked at its
stated type in S15Elab and round-tripped there against `Std.le_reflT`.

**§11.4's naturalness probe is gone too.** It was the M12+ work-list — the
quicksort program we wanted, annotated line by line with what the calculus could
not yet express — and every gap it named has since closed: dependent call-site
instantiation (§12), Term-level `Std` at telescope positions (§12), the
two-cursor access-at-depth idiom (M14's bounds cursor), `Take`/`Drop` (Std, and
the array slices of ¶2.1), `if`-sugar over the Bool match (§12), and bounded
recursion, which turned out not to need a bound at all once `fn` became a sealed
recursor (M26). The program it described is `S23Direct.quicksort`.
-/

open Dllbc

namespace Dllbc.Tests.S11Lib

/-! ## The fording vocabulary, authored in `prog{ }`

    `NatCode : Nat → Nat → Type` by double `natRec` — `(Z,Z) ↦ ⊤`, `(S,S) ↦` the
    code of the predecessors, mixed `↦ ⊥` — and the motive that turns a
    `p : Id Nat Z b` into an inhabitant of `NatCode Z b`, which for `b = S n`
    computes to `⊥`. §10 derives the same kit as `Val`s; this is the `Term` side,
    because a `fn` body is made of `Term`s.

    **These were raw `Term`s until M28, on a rationale that expired.** The file
    used to say "the surface macro has no syntax for `j`/`app`/`const`, and the
    j-spine's `.pvar` motives cannot be reproduced by a named binder". Both halves
    are false since §15's `prog{ }` and M27's juxtaposition application:
    `natRec`/`j`/`botElim` are resolvable kernel constants (`constSet`), a spine
    is juxtaposition, and a named λ binder elaborates to exactly the de Bruijn
    index the hand-built motive spelled out.

    Authoring them by name found a **latent off-by-one** the raw form had carried
    since M11 and no test could see: the `jReflProof` motive's inner λ DOMAIN was
    written `Id Nat a (pvar 1)` where a domain sits OUTSIDE its own binder
    (`shiftPure` passes `c`, not `c + 1`, into a `.lam`'s domain), so the index was
    dangling. It never bit because `j … Refl` ι-reduces without consulting its
    motive. Written with names there is no index to get wrong — see `storeProof`
    below, whose motive is `λ (x : Nat). λ (q : Id Nat a x). Id Nat a x`. -/

/-- `NatCode`'s `Z` row: `Z ↦ ⊤`, `S _ ↦ ⊥`. -/
def zCase : Term := prog defer_check {
  λ (M : Nat). natRec (λ (X : Nat). Type) Unit (λ (X : Nat). λ (R : Type). Bot) M }

/-- `NatCode`'s `S` row: `Z ↦ ⊥`, `S m2 ↦ code of the predecessors` (the
    outer recursor's `ih`, applied). -/
def sCase : Term := prog defer_check {
  λ (N : Nat). λ (F : Π (X : Nat) → Type). λ (M : Nat).
    natRec (λ (X : Nat). Type) Bot (λ (M2 : Nat). λ (R : Type). F M2) M }

/-- `NatCode : Nat → Nat → Type`, by `natRec` at a Π-valued motive. -/
def natCode : Term := prog defer_check {
  λ (A : Nat). natRec (λ (X : Nat). Π (Y : Nat) → Type) zCase sCase A }

/-- The no-confusion motive at `Z`: `λ m. λ (q : Id Nat Z m). NatCode Z m`. With
    `j`'s `d := unit : NatCode Z Z`, `j Nat Z nncMotive unit (S n) p` has type
    `NatCode Z (S n)`, which computes to `Bot`. -/
def nncMotive : Term := prog defer_check { λ (M : Nat). λ (Q : Id Nat Z M). natCode Z M }

/-! ## §11.1 The pure lift — ⇒ produces proof terms -/

-- Returning a proof: `Refl` at an `Id`-typed return. A `ctorApp`, so it lifts
-- trivially — the degenerate case, which is why it goes first.
example : progOk (prog{
  fn RetRefl (a : Nat) -> Id Nat a a { Refl };
  () }) = true := by native_decide

-- Storing a proof: a J-application (which ⇝-reduces to `Refl`) is ⇒-lifted into a
-- `Pair`'s dependent second field and audited against `Id Nat a a`.
example : progOk (prog{
  fn StoreProof (a : Nat) -> Σ (x : Nat). Id Nat x x
    { Pair(a, j Nat a (λ (X : Nat). λ (Q : Id Nat a X). Id Nat a X) Refl a Refl) };
  () }) = true := by native_decide

-- The M10 conflict discharge, as a dead branch in a checked `fn` (the shape the
-- fording spec originally wanted). The `False` arm holds `p : Id Nat Z (S n)`,
-- derives ⊥ through the no-confusion spine, and ⇒-lifts `botElim Nat (…)` to
-- close the branch.
example : progOk (prog{
  fn Discharge (n : Nat, p : Id Nat Z (S n), b : Bool) -> Nat {
    match b {
      True => Z,
      False => botElim Nat (j Nat Z nncMotive unit (S n) p)
    } };
  () }) = true := by native_decide

-- Not vacuous: the discharge is what closes the branch, and without it the arm
-- has nothing of the return type to give. The same function with the `False` arm
-- returning the PROOF rather than eliminating it is rejected.
example : progRejects (prog defer_check {
  fn DischargeLie (n : Nat, p : Id Nat Z (S n), b : Bool) -> Nat {
    match b {
      True => Z,
      False => p
    } };
  () }) "does not have return type" = true := by native_decide

end Dllbc.Tests.S11Lib
end
-- └── end of what was `S11Lib.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S15Elab.lean` ──────────────────────────────────────────────
section
/-!
# §15 test suite — the pure surface authoring layer, and `LeTrans`

The M11 wall was mis-indexed de Bruijn failing silently. This milestone's claim:
names + explicit motives collapse it without a unifier. The evidence is here —
`LeTrans`, the lemma I abandoned as a raw term, authored in `prog{ }` and
checked; plus the J warm-ups and the round-trip that a hand-built term and its
surface elaboration are convertible.

Two `hasType` additions served it (both ordinary type theory, not a unifier):
application-spine synthesis for a bound function variable (`ih b c hab hbc`), and
over-application of an eliminator (`natRec … n` returning a function, then given
its argument).
-/

open Dllbc

namespace Dllbc.Tests.S15Elab

/-- Check a pure `Term` against a pure type `Term` (deep fuel — lemmas nest). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 2000 tm; let t ← readC 2000 ty; hasTypeT 2000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## Elaboration round-trip: surface `LeRefl` = the hand-built kernel term -/

-- The surface `LeRefl` (StdLemmas) elaborates to a `Term` convertible with the
-- M11 hand-built `Std.le_reflT`.
example : expectConv [] [] Dllbc.StdLemmas.LeRefl Std.le_reflT = true := by native_decide

/-! ## `let` is ONE form, and the two ways it can capture (M29 α)

    `let` used to elaborate two ways — a `letIn` under ⇒, a de Bruijn β-redex
    under ⇝ — and merging them onto `letIn` moved a `let` into positions its
    de Bruijn spelling had made impossible. These four pin the merge: the first
    two that it means the same thing, the last two that neither capture the
    spelling would have permitted actually happens. Each of the last two was a
    MEASURED wrong answer before the fix (M29 step-0 probe 2 and its
    counterfactual), not a hypothesis. -/

-- (1) The merged `let` means what the β-redex it replaced meant.
example : expectConv [] [] prog defer_check { let a = 2 ; Add a a } prog defer_check { (λ (A : Nat). Add A A) 2 } = true := by
  native_decide
-- (2) …and a `let` chain still means its nesting.
example : expectConv [] [] prog defer_check { let a = 2 ; let b = S a ; Add a b } prog defer_check { 5 } = true := by
  native_decide

-- (3) A `let` may SHADOW a pure binder, and the innermost one wins. A pure λ's
-- body is a `uterm`, so a `let` cannot sit directly under one; an `elim` arm's
-- body is a `ublk` and its binders push the de Bruijn context, so that is the
-- reachable route. `resolveName` consults that context FIRST, so without the
-- surface's mask this reads the ARM's `k` — measured as `Z`, not `7`.
example : expectConv [] []
    prog defer_check { elim 1 return (λ (X : Nat). Nat) { Z => 0, S(K) Ih => let k = 7 ; k } }
    prog defer_check { 7 } = true := by native_decide

-- (4) A let-bound value MENTIONING a pure binder, read two binders deeper. ⇝
-- reads `let` by β and lifts the value from the depth it was bound at to the
-- depth it is used at; the Ω-binding reading this replaced did not, and returned
-- a value pointing at the inner arm's binders instead. `s = S k = 1`.
example : expectConv [] []
    prog defer_check { elim 1 return (λ (X : Nat). Nat) {
            Z => 0,
            S(K) Ih =>
              let s = S K ;
              elim 1 return (λ (Y : Nat). Nat) { Z => 0, S(J) Ih2 => s } } }
    prog defer_check { 1 } = true := by native_decide

/-! ## The lemmas check at their stated types -/

example : chk Dllbc.StdLemmas.LeRefl Dllbc.StdLemmas.LeReflTy = true := by native_decide
-- THE ACCEPTANCE TEST — `LeTrans` authored in the surface, checked.
example : chk Dllbc.StdLemmas.LeTrans Dllbc.StdLemmas.LeTransTy = true := by native_decide
example : chk Dllbc.StdLemmas.IdTrans Dllbc.StdLemmas.IdTransTy = true := by native_decide
example : chk Dllbc.StdLemmas.IdCongr Dllbc.StdLemmas.IdCongrTy = true := by native_decide

/-! ## `LeTrans` APPLIED in a checked function — closing the loop with §12

    A body that ⇒-lifts `LeTrans Nat a b c p q` (the pure lift, §11) and returns
    it at the dependent type `Le a c` (instantiated at the actuals, §12). -/

-- `LeTrans a b c p q` (Le is monomorphic at Nat — no type argument), cited by
-- name through the surface's identifier fallback.
def useTrans : Term := prog{
  fn UseTrans (a : Nat, b : Nat, c : Nat, p : Le a b, q : Le b c) -> Le a c
        { StdLemmas.LeTrans a b c p q };
  () }
example : progOk useTrans = true := by native_decide

/-! ## Negative tests -/

-- Wrong motive: `elim n return (λ m. Le Z m) { … }` gives a proof of `Le Z n`,
-- but the function claims `Le n n`. Elaboration SUCCEEDS (the term is
-- well-formed); the audit rejects it — the motive is written on the `return`
-- clause and thus visible, so the failure is comprehensible. The surfaced error
-- is: "audit: result (…) does not have return type (…)".
def LeFn : Term := Std.LeFnT
def badReflClosed : Term := prog defer_check {
  λ (N : Nat). elim N return (λ (M : Nat). LeFn Z M) { Z => unit, S (K) Ih => Ih } }
-- SUBJECT: a deliberately-lying function — the return type claims `Le n n` while
-- the body proves `Le Z n`. It was a hand-built `FnDef` record on the argument that
-- a surface form would obscure the lie; written as a `fn` the lie is the two lines
-- side by side, which is more explicit rather than less. The body is the pure term
-- above, spliced and applied — the mis-motive is what is under test, so it stays
-- exactly as written.
def badRefl : Term := prog defer_check {
  fn BadRefl (n : Nat) -> Le n n { %badReflClosed n };
  () }
example : progRejects badRefl "does not have return type" = true := by native_decide

-- Unresolved name: `prog{ Le nope nope }` where `nope` is unbound is a Lean
-- elaboration error at macro time (the resolve-or-error discipline), not a
-- silent `pvar`. Demonstrated by `#guard_msgs` would require the exact message;
-- here we simply note it cannot be written — an unbound lowercase name in a
-- `prog{ }` block fails to compile, exactly as in `prog{ }`.

/-! ## The measure (§15's report card)

    `LeTrans` in the surface: 14 lines (`StdLemmas.LeTrans`), every binder named,
    every motive written once and visible on its `return` clause. The M11 raw-term
    attempt was ABANDONED at the wall: a three-level nested dependent induction
    over ~15 distinct de Bruijn binder contexts, each mis-index failing silently
    with only a `false` from `native_decide` and no locus. The surface term
    type-checked on the SECOND attempt (the first surfaced two real bugs in
    `hasType` — sym-application and eliminator over-application — not de Bruijn
    slips, because there are no indices to slip). Names + explicit motives
    collapsed the wall; no unifier, no motive inference, no case trees. -/

/-! ## Σ binds with a DOT, and the dot is the only spelling

    A Π *is* a function and keeps its arrow; a Σ builds a PAIR, and an arrow on a
    pair former reads like a function it is not. The dot is the surface's own
    convention — λ has bound with one since the grammar was written — so these
    pin the spelling rather than introduce a style.

    These pin SHAPES, not convertibility: what a spelling elaborates to is the
    whole claim, and `rfl` decides it because both sides are closed `Term`
    literals built by the macro at elaboration time.

    **What is deliberately NOT tested here, and cannot be.** `Σ (x : A) → B` was
    the spelling before the migration, and it survived briefly as a parsing alias
    so in-flight branches could land. The alias is now DELETED — an arrow after a
    Σ binder is a parse error. Five goldens asserting `dot = arrow` (at Σ, at Σ0,
    and across a tower written all-arrow and two ways MIXED) went with it, and
    nothing replaces them: a parse failure is a Lean elaboration error at macro
    time, so it cannot be asserted from inside the file that would fail to
    compile. The absence is the assertion.

    **Consequence for branches written before this**, re-measured against
    `origin/main` at the time this landed rather than carried over. Five unmerged
    branches add a file that spells Σ with an arrow, and those files will fail to
    PARSE at merge — not fail a check, which is a friendlier failure than it
    sounds, since a parse error names its line and its token:

      hm-probe-opt/…/Tests/HmProbeOpt.lean           107
      hm-finite-ints/…/Tests/Finite.lean              64
      hm-probe-arrays/…/Tests/HmProbeArrays.lean      30
      hm-probe-getmut/…/Tests/HmProbeGetmut.lean       8
      borrow-refound-design/…/BorrowRefoundGoals.lean   6

    215 sites, and the fix for each is one run of `dllbc/scripts/sigmadot.py`
    over the new file. Do not hand-edit and do not reach for the obvious regex: a
    Σ domain's own parentheses defeat a non-nesting pattern, which is how the
    original migration nearly missed a third of its sites.

    These counts MOVE, and that is the point of re-measuring rather than trusting
    the list: `hm-finite-ints` grew from 38 to 64 between the removal being
    written and it landing, and `audit-exemption-fix` merged in the interval —
    arrow-free, so it landed needing nothing. Count the old spelling again after
    every rebase; a rebase can also carry OLD prose back across a migration, which
    is how one resurrected arrow reached `Machine.lean` and had to be re-fixed.

    `hm-option-kernel`'s `Tests/OptionT.lean` needs no scanner run — it is already
    arrow-free — but that branch modifies six files this lane or the migration
    rewrote (`Uni.lean`, `Machine.lean`, `Pure.lean`, `Value.lean`,
    `FnMacro.lean`, and this file), and `hm-probe-opt` modifies `Uni.lean`, whose
    Σ grammar rows are exactly what got deleted. Those merges want reading rather
    than accepting: an auto-merge taking their side would resurrect the alias
    rows, or arrow-form Σs that then fail to parse. -/

-- The dot form elaborates to the pair former it names. Σ0's `0` is the `.cmpT` on
-- the CODOMAIN and nothing else — same `sigmaT`, same binder.
example : prog defer_check { Σ (x : Nat). Nat } = Term.sigmaT "x" (.const "Nat") (.const "Nat") := by rfl
example : prog defer_check { Σ0 (h : Nat). Nat }
    = Term.sigmaT "h" (.const "Nat") (.cmpT (.const "Nat")) := by rfl

-- A Σ TOWER associates to the right, so a chain of dots nests rather than
-- flattening. (`Id A a b` is its own grammar row and builds `Term.idT`, not an
-- application spine over a `.const "Id"` — worth spelling out once, since the
-- surface gives no hint of it.)
example : prog defer_check { Σ (n : Nat). Σ (r : Nat). Id Nat n r }
    = Term.sigmaT "n" (.const "Nat")
        (Term.sigmaT "r" (.const "Nat")
          (Term.idT (.const "Nat") (.pvar "n") (.pvar "r"))) := by rfl

-- A Σ whose codomain is a Π keeps the Π's arrow: the two formers are told apart
-- by their punctuation, which is the whole point. The dot is the pair and the
-- arrow is the function, in one type. (The Π's binder is CAPITAL, so §2.1 puts a
-- `.cmpT` on its domain — the elaborated Π is not the one you would write by
-- hand, and the golden says so rather than hiding it behind a round-trip.)
example : prog defer_check { Σ (n : Nat). Π (Q : Nat) → Id Nat n Q }
    = Term.sigmaT "n" (.const "Nat")
        (Term.pi "Q" (.cmpT (.const "Nat"))
          (Term.idT (.const "Nat") (.pvar "n") (.pvar "Q"))) := by rfl

-- The printer spells the dot (`Term.prettyPrec`'s `.sigmaT` case), which is the
-- round-trip the surface owes a user reading a rejection message: a Σ goes in as
-- a dot and comes back out as one, and there is no longer any other way in.
example : Term.pretty (Term.sigmaT "n" (.const "Nat") (.const "Bool")) = "Σ(n : Nat). Bool" := by
  native_decide
example : Term.pretty prog defer_check { Σ (n : Nat). Nat } = "Σ(n : Nat). Nat" := by native_decide

end Dllbc.Tests.S15Elab
end
-- └── end of what was `S15Elab.lean` ───────────────────────────────────────────────

-- ┌── M32 R1: the σ namespace ────────────────────────────────────────────────
section
/-!
# The `§σ` namespace — unwritable, and unshadowed

M32 R1 makes a σ a reserved pure NAME (`Term.sym σ` = `pvar "§σ<id>"`), which
puts two claims on the critical path. Both are asserted as behaviour here rather
than argued in a comment, because both are the silent kind: a violation would
present as a refinement that quietly stops reaching an occurrence.

  1. **`Term.substP`'s rebinding guard is vacuous for a σ-name.** The guard stops
     at a binder that rebinds the name, so a binder called `§σ0` would fence a
     refinement out of its body. The kernel's complete minted-binder inventory is
     `§<digits>` (readback), `§gen`, `§let<digits>`, `§p<digits>`, `§_` and the
     hand-written recursor premise binders — none of which is `§σ<digits>`.
  2. **No program can write one.** An ordinary Lean `ident` cannot contain `§`.
     An ESCAPED one can (`«§σ0»`) — and the reason that route is closed is
     stronger than the guard `Surface.reservedBinder` puts in front of it:
     `Name.toString` re-escapes, so the binder such a program writes is literally
     named `«§σ0»`, guillemets and all, which is a DIFFERENT name from `§σ0` and
     is not in the reserved namespace at all. (Measured, not assumed — the guard
     never fires on this input, so a reader who checked only the guard would
     conclude the opposite.)
-/

open Dllbc

namespace Dllbc.Tests.S32Sigma

/-- Substituting a σ reaches an occurrence under a binder of each shape the
    kernel mints. -/
def underBinder (nm : String) : Term :=
  .lam nm (.const "Nat") (.ctorApp "S" [Term.sym 0])

def refined (nm : String) : Term :=
  Term.substSym 0 (Term.nat 4) (underBinder nm)

def reaches (nm : String) : Bool :=
  Term.beq (refined nm) (.lam nm (.const "Nat") (.ctorApp "S" [Term.nat 4]))

example : reaches (readbackName 0) = true := by native_decide
example : reaches genName = true := by native_decide
example : reaches (Pure.letName 7) = true := by native_decide
example : reaches "§p3" = true := by native_decide
example : reaches "§_" = true := by native_decide
example : reaches "§k" = true := by native_decide
example : reaches "§ih" = true := by native_decide
example : reaches "§xs" = true := by native_decide
-- The one name that WOULD fence it out is the σ's own, which is exactly what
-- makes the guard's vacuity a claim about the inventory above and not about
-- `substP`.
example : reaches (symName 0) = false := by native_decide

-- An escaped identifier does not land in the namespace: the escape is part of
-- the name.
def escapedSigma : Term := prog defer_check { λ («§σ0» : Nat). «§σ0» }
example : (match escapedSigma with
           | .lam nm _ _ => isReservedName nm.name
           | _ => true) = false := by native_decide
-- …so a refinement of σ0 passes straight through it, unfenced.
example : (Term.beq (Term.substSym 0 (Term.nat 4)
             (.lam "«§σ0»" (.const "Nat") (.ctorApp "S" [Term.sym 0])))
           (.lam "«§σ0»" (.const "Nat") (.ctorApp "S" [Term.nat 4]))) = true := by native_decide

end Dllbc.Tests.S32Sigma
end
-- └── end of the M32 R1 σ-namespace battery ────────────────────────────────────

-- ┌── the M32 R2 cook-at-generalization canary ─────────────────────────────────
section
namespace Dllbc.Tests.S32Cook
open Dllbc

/-! # Cook-at-generalization, with the control that makes it mean something

    suspensions.md §3 derives ONE persistent cooking event from one criterion: a
    store-wide sweep is safe iff it commutes with evaluation. Refinement is
    atom-keyed and commutes; X-Gen's generalization is compound-keyed and does
    not. Stage V sharpened the failing case to MATERIALIZED-vs-LATENT — a spine
    materialized in ρ survives the sweep untouched, and only a spine the body
    RE-MINTS from ρ's ingredients speaks pre-generalization vocabulary
    afterwards.

    This is Stage V bet (c)(iii), built and run **in both directions**, because a
    green result here is worth exactly the negative control that accompanies it:
    the failure mode is silent by construction (M30's measured count-equation
    break).

    The suspension: ρ binds `V ↦ σ5` and `W ↦ σ6`, and the body is the stuck
    spine `leb V W`. The generalized spine `leb σ5 σ6` is therefore **LATENT** —
    it is nowhere in ρ and nowhere in the raw body, and it comes into existence
    only when the body is evaluated. (`leb` stands here for §19's own scrutinee,
    an unknown head that `whnfN` leaves neutral; the shape is what matters.) -/

def vSlot : Var := ⟨700, "V"⟩
def wSlot : Var := ⟨701, "W"⟩
def latentRho : List (Var × Val) :=
  [(vSlot, .know (Term.sym 5)), (wSlot, .know (Term.sym 6))]
def latentBody : Term := .app (.app (.const "leb") (.var vSlot)) (.var wSlot)
def latentNode : Term := .lam "§x" (.const "Nat") latentBody
def latent : Val := .closure latentRho latentNode none

/-- The spine the split generalizes, normalized as `generalizeStuck` normalizes
    it, and the fresh σ it is abstracted into. -/
def sp : Term := Pure.nf 1000 (.app (.app (.const "leb") (Term.sym 5)) (Term.sym 6))
def σb : Nat := 99

/-- Cook a value that is a closure; anything else is not this test's subject. -/
def cooked : Val → Term
  | .closure ρ n _ => cookClosure 1000 ρ n
  | v => .const s!"NOT-A-CLOSURE:{v.pretty}"

/-- **The eager answer**: cook, THEN sweep. What a cook-at-formation system would
    have produced, and the vocabulary the branch equation speaks. -/
def eager : Term := Term.abstractInto sp σb (cooked latent)

/-- **R2's rule**: `cookForGen` at the spine's support, then the sweep, then
    apply (= cook) afterwards. -/
def withCooking : Term := cooked (abstractInto sp σb (cookForGen 1000 sp.symIds latent))

/-- **The control**: the same with cook-at-generalization DISABLED — the sweep
    alone, then apply. -/
def withoutCooking : Term := cooked (abstractInto sp σb latent)

-- The instrument first, so a pass cannot be vacuous: the support is what the
-- spine is over, and the closure IS in scope of the support-scoped rule.
example : sp.symIds = [5, 6] := by native_decide
example : (Val.symIdsRho latentRho).any (fun s => sp.symIds.contains s) = true := by native_decide

-- POSITIVE: with cooking, the raw suspension agrees with the eager answer.
example : Term.beq withCooking eager = true := by native_decide

-- NEGATIVE, and this is the half that makes the positive mean something: with
-- cooking disabled the same suspension DIVERGES — it re-mints `leb σ5 σ6` from
-- ingredients the sweep never touched, and speaks the pre-generalization
-- vocabulary the branch has stopped using.
example : Term.beq withoutCooking eager = false := by native_decide

-- Named, so a reader sees WHICH two answers those are rather than taking the
-- disagreement on trust.
example : eager.pretty = "λ(§0 : Nat). σ99" := by native_decide
example : withoutCooking.pretty = "λ(§0 : Nat). leb σ5 σ6" := by native_decide

/-! ## The rule is SUPPORT-SCOPED, and that is asserted rather than described

    A closure whose ρ mentions no σ of the spine's support cannot re-mint the
    spine, so it is left RAW — the difference between §3's rule and
    "normalize at every split", which §3 rejects because it pays at the commuting
    sweeps that need nothing. -/
def unrelated : Val := .closure [(vSlot, .know (Term.sym 7))] latentNode none
example : (match cookForGen 1000 sp.symIds unrelated with
           | .closure ρ n _ => ρ.length == 1 && Term.beq n latentNode
           | _ => false) = true := by native_decide

/-! ## An IMPERATIVE body is never cooked, ever (§3)

    It never participates in conversion — audited once at formation, then only
    entered — and cooking one is not merely pointless but undefined, since ⇝ has
    no rule for a write. Its ρ is still descended, because a comptime closure can
    sit inside one. -/
def impNode : Term := Term.lamTel [(⟨702, "w"⟩, .const "Nat")] (.seq (.var vSlot) .unit)
def impClosure : Val := .closure latentRho impNode none
example : (match cookForGen 1000 sp.symIds impClosure with
           | .closure ρ n _ => ρ.length == 2 && Term.beq n impNode
           | _ => false) = true := by native_decide

/-! ## A limit of the sweep, found by building this canary — CLOSED at M33

    R2 found it here and recorded it as a demand. `Term.abstractInto` matched by
    `Term.beq`, which compares binder NAMES, and `readback` names a binder by its
    LEVEL. So a generalized spine that itself CONTAINS a binder did not match its
    own occurrence under a λ: normalized at depth 0 the spine says `§0`, and the
    same spine normalized one binder deeper says `§1`. `len σ5` is such a spine —
    it unfolds to a `listRec` over λ arms — and abstracting it reached every
    knowledge leaf in Ω and none of the occurrences inside a cooked closure body.

    This was not new at R2 (a λ at rest was normalized knowledge before it was a
    closure, with the same level shift), and it was never what
    cook-at-generalization is about — cooking fixes LATENCY, and this was a
    matching question underneath it.

    **M33 made the key `Term.alphaEq`**, which is what R2 named as the fix. The
    assertion below is kept, flipped: it is the same probe, and its verdict is now
    the opposite one. That is deliberately more informative than deleting it —
    the line that used to say "the sweep finds nothing here" now says "the sweep
    finds it", and the two are the same measurement. -/
def lenBody : Term := prog defer_check { %(Std.lenFnT) %(Term.var vSlot) }
def lenLatent : Val := .closure [(vSlot, .know (Term.sym 5))] (.lam "§x" (.const "Nat") lenBody) none
def lenSp : Term := Pure.nf 1000 (prog defer_check { %(Std.lenFnT) %(Term.sym 5) })
-- The spine BINDS: it unfolds to a `listRec` over λ arms, so its normal form
-- carries binders and their names are levels.
example : strContains lenSp.pretty "λ(§0" = true := by native_decide
-- …and the sweep now FIRES inside the cooked body, where under the name key it
-- walked past. (FLIPPED at M33: this read `= true` while the key was `beq`.)
example : Term.beq (Term.abstractInto lenSp 98 (cooked lenLatent)) (cooked lenLatent)
          = false := by native_decide
-- Named, so the flip is a rewrite and not merely a difference: the cooked body's
-- occurrence reads `σ98`, which is what the branch's refinement can then reach.
example : (Term.abstractInto lenSp 98 (cooked lenLatent)).pretty
          = "λ(§0 : Nat). σ98" := by native_decide

/-! ### The same limit as a PROGRAM (M33), and the pair that isolates it

    The assertion above is the limit at unit level, where it was found. This is
    the limit as something a programmer meets: two programs differing in ONE
    thing — whether the occurrence of the split spine sits under a binder — with
    opposite verdicts.

    Both split on `Leb (Len L) 2`, so both generalize the SAME spine, and that
    spine binds (`Leb` unfolds to a `natRec` over λ arms and `Len` to a `listRec`
    over λ arms, so it binds twice over). Both then ask the True branch to show
    that a value which recomputes the spine is `True`, which is exactly what the
    ⇜ refinement of `σb` delivers — provided the sweep reached the occurrence.

      * `alphaControlDepth0` holds the spine in a comptime `let`. Its knowledge
        leaf sits at binder depth ZERO, which is the depth `generalizeStuck`
        normalized the needle at, so the names agree and `Term.beq` matches.
      * `alphaRepro` holds it in a comptime λ. `cookForGen` cooks the closure
        (its ρ mentions L's σ, so it is in the support), and the cooked body puts
        the spine one binder deeper — where readback numbered the spine's own
        binders from 1 instead of from 0. Under the NAME key the sweep walked
        straight past it, the body kept speaking pre-generalization vocabulary,
        and the `Refl` died at the call.

    **FLIPPED at M33**: with the key α-insensitive, `alphaRepro` is accepted, and
    the pair now asserts that the two programs agree — which is the property that
    was wanted all along, since binder depth is not something a programmer should
    be able to observe. The rejected version is not deleted but recorded in the
    commit that pinned it (`M33 α.1`), where the needle it died with is quoted. -/

def alphaControlDepth0 : Term := prog{
  fn NeedTrue (B : Bool, h : Id Bool B True) -> Unit { () };
  fn AlphaControlDepth0 (L : List Nat) -> Unit
        { let C = Leb (Len L) (S (S Z));
          let c = Leb (Len L) (S (S Z));
          match e : c {
            True => { NeedTrue(C, Refl); () },
            False => ()
          } };
  () }
example : progOk alphaControlDepth0 = true := by native_decide

def alphaRepro : Term := prog{
  fn NeedTrue (B : Bool, h : Id Bool B True) -> Unit { () };
  fn AlphaRepro (L : List Nat) -> Unit
        { let F = λ (X : Nat). Leb (Len L) (S (S Z));
          let c = Leb (Len L) (S (S Z));
          match e : c {
            True => { NeedTrue(F Z, Refl); () },
            False => ()
          } };
  () }
example : progOk alphaRepro = true := by native_decide

-- The accept DISCRIMINATES: the same program asking the True branch to show the
-- spine is `False` is still rejected. Without this, "α-insensitive" could have
-- been read as "matches more things than it should", and an accept that a
-- rubber-stamping sweep would also produce says nothing about the key.
def alphaReproLie : Term := prog defer_check {
  fn NeedFalse (B : Bool, h : Id Bool B False) -> Unit { () };
  fn AlphaReproLie (L : List Nat) -> Unit
        { let F = λ (X : Nat). Leb (Len L) (S (S Z));
          let c = Leb (Len L) (S (S Z));
          match e : c {
            True => { NeedFalse(F Z, Refl); () },
            False => ()
          } };
  () }
example : progRejects alphaReproLie "does not have its parameter type" = true := by native_decide

/-! ### The diagnosis, stated as the two keys disagreeing

    Why the pair used to split is not left to the prose: the needle and the
    occurrence one binder deeper are the same term up to α and different terms up
    to names, and these two lines say so. Nothing about the gap was ever hard to
    DECIDE — `Term.alphaEq` already returned the right answer at R2 — which is why
    the residual was a change to the sweep's KEY rather than to its traversal. -/
def lenSpDeeper : Term :=
  match Pure.nf 1000 prog defer_check { Π (X : Nat) → Len %(Term.sym 5) } with
  | .pi _ _ c => c
  | t => t
example : Term.beq lenSp lenSpDeeper = false := by native_decide
example : Term.alphaEq lenSp lenSpDeeper = true := by native_decide

end Dllbc.Tests.S32Cook
end
-- └── end of the M32 R2 cook-at-generalization canary ─────────────────────────

-- ┌── the M32 R2 capture-generality battery ────────────────────────────────────
section
namespace Dllbc.Tests.S32Capture
open Dllbc

/-! # What a body may name, and what a closure carries out (suspensions.md §2.6)

    Two things landed together and only look like one rule. The SURFACE stopped
    elaborating a `fn` body in a params-only context, so a body can now cite the
    bindings lexically above it. The KERNEL started keeping what such a citation
    resolves to, in ρ, so the citation survives the λ escaping the scope it was
    written in. Stage C measured that program-scope citation already worked; the
    closure is what makes the escaping case safe. -/

-- ACCEPTED, and this is the flip: a `fn` body citing a comptime binding above
-- it. Before R2 this was a Lean elaboration error — `H0` resolved against the
-- parameters and there were none by that name.
def fnCitesEnclosing : Term := prog{
  let H0 = 3;
  fn Uses (n : Nat) -> Nat { let Snap = H0; n };
  () }
example : progOk fnCitesEnclosing = true := by native_decide

-- The same for a λ bound as a value: the citation is admitted, and what it
-- resolves to is CAPTURED — the closure carries `H0`, so applying it later reads
-- what the λ saw.
def lamCitesEnclosing : Term := prog{
  let H0 = 3;
  let G = λ(a : Nat) { let Snap = H0; a };
  let r = G(1);
  () }
example : progOk lamCitesEnclosing = true := by native_decide

-- REFUSED, by the capture rule and not by scoping: a RUNTIME (lowercase)
-- binding is not capturable, because a λ is formed now and used later and a
-- runtime citation would be an implicit snapshot taken in that gap (§2.4). The
-- surface can see `h0` now; the kernel is what says no.
def lamCitesRuntime : Term := prog defer_check {
  let h0 = 3;
  let G = λ(a : Nat) { let Snap = h0; a };
  () }
example : progRejects lamCitesRuntime "a runtime (lowercase) binding" = true := by native_decide

-- And the capture really is in the VALUE rather than resolved dynamically: the
-- closure sitting in `G`'s slot carries a one-entry ρ naming `H0`.
def capturedProg : Term := prog{ let H0 = 3; let G = λ(a : Nat) { let Snap = H0; a }; () }
def capturedRho : List String :=
  match (Dllbc.tailEnvs capturedProg).head! with
  | Except.ok env => match env.lookup "G" with
    | some (Val.closure ρ _ _) => ρ.map (·.1.name)
    | _ => ["NOT-A-CLOSURE"]
  | Except.error e => [e]
example : capturedRho = ["H0"] := by native_decide

end Dllbc.Tests.S32Capture
end
-- └── end of the M32 R2 capture-generality battery ────────────────────────────

-- ┌── the M32 R3 ⇝-sealing battery ─────────────────────────────────────────────
section
namespace Dllbc.Tests.S32Seal
open Dllbc

/-! # The seal, ⇝-evaluated (suspensions.md §2.4, M32 R3)

    ⇝ refused the seal because minting a fresh σ needs an event and ⇝ has none —
    so a seal reduced twice under ⇝ would disagree with itself. R3's answer is
    that the σ is not fresh: it is the one this seal's SITE has at these INPUTS,
    and the two halves of that sentence are what this battery asserts.

    Sites come from `Term.numberSeals`, a pass at the program boundary. Inputs
    are what the seal's free runtime variables hold when it is read — the values
    its check consults, which is why agreeing on them means agreeing on the
    check's answer.

    §6's sharp edge ("seal-site identity: stable across macro expansion and
    α-canonicalization") is asked here rather than assumed. -/

/-- The first seal in a term, with its site as the boundary pass assigned it. -/
partial def firstSeal : Term → Option (Nat × Term × Term)
  | .seal s t u => some (s, t, u)
  | .letIn _ a b => (firstSeal a).orElse (fun _ => firstSeal b)
  | .seq a b | .app a b => (firstSeal a).orElse (fun _ => firstSeal b)
  | .lam _ d b | .pi _ d b | .sigmaT _ d b => (firstSeal d).orElse (fun _ => firstSeal b)
  | _ => none

def sealOf (t : Term) : Option (Nat × Term × Term) := firstSeal (Term.numberSeals t).2

/-! ## A. THE GOLDEN IS UNCHANGED — the flip is behaviour-identical

    `let F = (…)` was ⇒'s (`Var.comptimeRhs`'s seal carve-out) and is ⇝'s. What
    a caller sees is the σ it always saw, at the number it always had: the site
    table is filled from `nextSym` on a miss, so a program whose seals are read
    in program order allocates them exactly where `sealMint`'s `freshSym` did. -/

def c2 : Term := prog{
  let F = (λ (X : Nat). S X : Π (X : Nat) → Nat); let y = F(2); () }

example : tailEnv c2 [("F", .sym 0), ("y", .sym 1)] = true := by native_decide
-- …and the instrument before the conclusion: there IS one seal here, so the
-- assertion above is about a ⇝-read seal and not about a program without one.
example : (Term.numberSeals c2).1 = 1 := by native_decide

/-! ## B. DETERMINISTIC — the same site at the same inputs is one value

    Asserted at the rule rather than through a program, because a program cannot
    reach one seal site twice in one state thread: `explore` forks a match into
    paths that carry their own states, and a `fn` body is audited once. So the
    rule is applied twice directly, in the state the first application left. -/

def capSeal : Term := prog{
  let N = 1; let F = (λ (X : Nat). N : Π (X : Nat) → Nat); () }

def stAt (n : Nat) : St := { initSt with env := [(⟨0, "N"⟩, .know (Term.nat n))] }

/-- Read a seal node in a given state: the value, and the state it leaves. -/
def readSeal (node : Nat × Term × Term) (st : St) : Except String (Val × St) :=
  match (sealNode defaultFuel node.1 node.2.1 node.2.2).run st with
  | .ok v st' => .ok (v, st')
  | .error e _ => .error e

/-- Twice in one state: the values, whether they agree, and how many σs the
    SECOND reading minted. -/
def twiceSame : Option (Val × Val × Nat) :=
  match sealOf capSeal with
  | none => none
  | some nd =>
    match readSeal nd (stAt 1) with
    | .error _ => none
    | .ok (v1, st1) =>
      match readSeal nd st1 with
      | .error _ => none
      | .ok (v2, st2) => some (v1, v2, st2.nextSym - st1.nextSym)

-- ==-equal, and the second reading mints NOTHING — which is the stronger claim:
-- the rule is a lookup the second time, so nothing downstream can tell the two
-- readings apart even by counting.
example : (twiceSame.map (fun p => p.1 == p.2.1)) = some true := by native_decide
example : (twiceSame.map (fun p => p.2.2)) = some 0 := by native_decide

/-! ## C. DISTINGUISHING — the same site at different inputs is not

    The negative control the determinism assertion needs: if the table were keyed
    on the site alone, B would pass for the wrong reason and a `fn` that returns
    a sealed function would give every caller the same σ. Same state thread, same
    node, one citation changed underneath it. -/

def twiceDiff : Option (Val × Val) :=
  match sealOf capSeal with
  | none => none
  | some nd =>
    match readSeal nd (stAt 1) with
    | .error _ => none
    | .ok (v1, st1) =>
      match readSeal nd { st1 with env := [(⟨0, "N"⟩, .know (Term.nat 2))] } with
      | .error _ => none
      | .ok (v2, _) => some (v1, v2)

example : (twiceDiff.map (fun p => p.1 == p.2)) = some false := by native_decide

/-! ## D. SITE STABILITY (§6's sharp edge, asked not assumed)

    A site must survive the two things that rewrite a program without changing
    it. **Macro expansion**: the numbering pass runs at the boundary, after every
    macro, so `fn`'s elaboration cannot move one — asserted by numbering the
    elaborated term. **α-canonicalization**: the pass reads structure and never a
    name, so renaming every binder leaves every site where it was. -/

def twoSeals : Term := prog{
  let F = (λ (X : Nat). S X : Π (X : Nat) → Nat);
  let G = (λ (Y : Nat). S Y : Π (Y : Nat) → Nat);
  () }
def twoSealsRenamed : Term := prog{
  let F = (λ (Aa : Nat). S Aa : Π (Aa : Nat) → Nat);
  let G = (λ (Bb : Nat). S Bb : Π (Bb : Nat) → Nat);
  () }

/-- Every site in a term, in traversal order. -/
partial def sites : Term → List Nat
  | .seal s t u => s :: sites t ++ sites u
  | .letIn _ a b => sites a ++ sites b
  | .seq a b | .app a b => sites a ++ sites b
  | .lam _ d b | .pi _ d b | .sigmaT _ d b => sites d ++ sites b
  | _ => []

example : sites (Term.numberSeals twoSeals).2 = [0, 1] := by native_decide
-- α-INSENSITIVE: rename every binder and the sites do not move.
example : sites (Term.numberSeals twoSeals).2
        = sites (Term.numberSeals twoSealsRenamed).2 := by native_decide
-- And they are DISTINCT, so two textually identical seals at two program points
-- stay two functions — which is what makes the site a site and not a hash.
example : (Term.numberSeals twoSeals).1 = 2 := by native_decide

/-! ## E. THE EXECUTING MACHINE GAINS NOTHING

    The acceptance contract's own words: no comparison, no ⇝ detour. Concrete
    evaluation reads a seal transparently, so it never asks which σ a site has —
    and the table it would have to compare against is empty when the program
    ends. (The `fn` here is REACHED, so the assertion is not vacuous: `y` holds
    what the callee computed.) -/

def execProg : Term := prog{
  fn Inc (n : Nat) -> Nat { S n };
  let y = Inc(2);
  () }

def execSealSites : Option Nat :=
  match (do let _ ← readR defaultFuel (atBoundary execProg); endScope defaultFuel).run
      { initSt with executing := true } with
  | .ok _ st => some st.sealSites.length
  | .error _ _ => none

example : execSealSites = some 0 := by native_decide
-- **The closure CARRIES ITS ASCRIPTION** (M33 Σ0's prerequisite): the `Π(…). Nat`
-- is the third field, and this golden is where it is spelled. It is `some` here
-- and `none` for every un-sealed λ in this file, which is the whole distinction —
-- a λ that was never ascribed promises nothing about its result. The binder is
-- `§p0` because the return type does not depend on the argument, so the surface
-- mints its unused name for it.
example : progRunsTo execProg [("Inc", .closure []
            (Term.lamTel [(⟨0, "n"⟩, .const "Nat")] (.ctorApp "S" [.var ⟨0, "n"⟩]))
            (some (.pi "§p0" (.const "Nat") (.const "Nat")))),
          ("y", Val.nat 3)] = true := by native_decide

end Dllbc.Tests.S32Seal
end
-- └── end of the M32 R3 ⇝-sealing battery ─────────────────────────────────────

-- ┌── the M32 R3 backstop-demolition battery ───────────────────────────────────
section
namespace Dllbc.Tests.S32Backstop
open Dllbc

/-! # What is left of the mode backstop (suspensions.md §2.5, M32 R3)

    Stage A enforced "a function may not land in a runtime binding" at THREE
    sites. R3 left ONE — `refuseFnBinding`, at the `let` — and **M33b deletes
    that one too**, measured: with the recursor's self-view spelled `Ih`, its
    survivor assertion (`S26Rec.m1`'s `let g = ih`) is a ⇒-move of a capital
    binding and `fenceComptime` refuses it a layer earlier, so the corpus is
    green with the rule neutralised. This battery is now the evidence for all
    three sites that went. -/

-- **`bindFields`' site went because it is UNREACHABLE**, not because it is
-- redundant, and this is the argument as a program: to put a function in a
-- constructor field you must ⇒-read one, and the bindings that hold one are
-- capital, which the erasure fence refuses. The field never receives a function,
-- so the check there had nothing left to catch.
def fieldFn : Term := prog defer_check {
  fn Inc (n : Nat) -> Nat { S n };
  let p = Pair(Inc, 1);
  () }
example : progRejects fieldFn "cannot be ⇒-moved" = true := by native_decide

/-! ## THE PIN: §2.5's rule — REFUTED TWICE, and LAW at M33

    The history, kept because it is the reason to believe the rule rather than a
    record of failures. §2.5 asked that a runtime binding never hold a function,
    `let f = Add 1` included. R3 built the refusal and measured the corpus saying
    no; R3b ran §2.1's binder migration first and measured it saying no again. The
    diagnosis both times was the same and was correct: **a proof of a ∀-statement
    is a λ**, the corpus binds those at lowercase names (`let cnt = MkL lo hi
    hcnt`), and nothing in this calculus distinguishes the two shapes — both bind
    a partial application at a Π type, and there is no Prop/Type split to say one
    is a proof and the other a computation.

    **M33 did not find the distinction. It made the distinction unnecessary.**
    §2.7's Σ0 gives the one position that had no way to say "comptime" a way to say
    it, and with that every position holding a function in this corpus SAYS SO: a
    capital `let`, a ⇝ parameter, a Σ0 component or tail, an ascription, a recursor
    arm. The rule is then not "tell a proof from a computation" — it is "a function
    value must arrive somewhere that reads by ⇝", and both arrows can check that.
    Two refusals enforce it: `readR`'s λ arm for a λ that is WRITTEN, and the pure
    lift for one that is COMPUTED.

    So both programs below FLIP, and they are two of the three tripwires §2.7 named
    (the third is `sigmaTailProof`, above, whose needle moved when the tail got its
    message). Each is kept with a one-character accepting twin, so the rejection is
    discriminating against its own accept and not against nothing. -/

-- §2.5's own example — **FLIPPED at M33, deliberately, and it is the LAST of the
-- three tripwires.** It read "ACCEPTED: `Add 1` is a function and `f` is a runtime
-- binding". `Add 1` is still a function and `f` is still a runtime binding; what
-- changed is that a runtime binding may no longer hold one. This is the refusal at
-- the PURE LIFT — the shape `readR`'s λ arm cannot see, because `Add 1` is a spine
-- until it is evaluated and a `λ (B : Nat). natRec …` after.
def computePartial : Term := prog defer_check { let f = Add 1; () }
example : progRejects computePartial "⇒ produced a function value" = true := by native_decide

-- …and the accepting twin, one character away.
def computePartialCap : Term := prog defer_check { let F = Add 1; () }
example : progOk computePartialCap = true := by native_decide

-- Its twin — a λ-valued runtime binding — **FLIPPED at M33 too.** It read
-- "indistinguishable … Accepted by the same rule, and it is the one that MUST be,
-- because the flagship returns values built this way": the flagship's values reach
-- their destinations now (a Σ0 tail, a capital `let`), so nothing depends on this
-- being legal. This is the refusal at `readR`'s λ ARM — the destination rule,
-- which sees the λ before anything is evaluated and names every destination there
-- is. `computePartial` above is the same rule one step later.
def lamValued : Term := prog defer_check { let f = λ (N : Nat). Add N 1; () }
example : progRejects lamValued "needs a comptime destination" = true := by native_decide

-- …and the accepting twin, one character away: the same λ at a capital binder.
-- Without it the rejection above would also pass for a rule that refused λs.
def lamValuedCap : Term := prog defer_check { let F = λ (N : Nat). Add N 1; () }
example : progOk lamValuedCap = true := by native_decide

/-! ## R3b: THE Σ COMPONENT'S BINDER MODE, and exactly how far it reaches

    R3's wall was `fence: 'Cnt' … cannot be ⇒-moved` — a capital binding handed
    out as a Σ component, where `readArgs` reads a `ctorApp`'s arguments with no
    type in hand and therefore ⇒-reads all of them. R3b gives the tail of a body
    a type-directed read (`readResult`): a `Pair` checked against a `Σ` reads each
    component by that component's BINDER, so a capital Σ binder makes its
    component comptime and its value ⇝-read.

    These two programs are that rule and its negative control, and they differ in
    ONE CHARACTER — the case of the Σ's binder. -/

open Dllbc.StdLemmas in
/-- A proof returned as a Σ component at a **capital** binder: ⇝-read, accepted. -/
def sigmaProofCapital : Term := prog{
  fn F (n : Nat) -> Σ (H : Le n n). Nat { let H0 = LeRefl n; Pair(H0, n) };
  () }
example : progOk sigmaProofCapital = true := by native_decide

open Dllbc.StdLemmas in
/-- The same program with the Σ binder LOWERCASE: the component is ⇒-read, and
    the fence refuses the capital binding — which is the wall R3 measured, still
    standing where §2.1 says it should. Without this control the acceptance above
    would also pass for a rule that simply stopped fencing. -/
def sigmaProofLower : Term := prog defer_check {
  fn F (n : Nat) -> Σ (h : Le n n). Nat { let H0 = LeRefl n; Pair(H0, n) };
  () }
example : progRejects sigmaProofLower "cannot be ⇒-moved" = true := by native_decide

open Dllbc.StdLemmas in
/-- **WAS THE RESIDUAL, is now the negative control** (M33's Σ0). What stood here
    said: a Σ chain's LAST component has no binder, so §2.1 gives it no mode and
    there is nothing for `readResult` to read; the same proof at the same capital
    binding, in the tail position instead of a bindered one, is REJECTED and the
    rejection IS the wall. It named what it would take — "a mode for the tail;
    `⇝τ` already exists and already survives readback, what does not exist is a
    surface way to write it there" — and that is exactly what `Σ0` now is.

    So the program is unchanged and still REJECTED, and what moved is the NEEDLE.
    It used to die at `fence: 'H0' … cannot be ⇒-moved`, which names the
    consequence and advises lower-casing a proof; it dies at the tail now, which
    names the position and gives the spelling (`tailFence`). Its accepting twin,
    one character away, is `sigmaTailProof0` in the Σ0 battery below.

    This is where quicksort's `cnt` sits. Its ensures is
    `Σ (hi : List Nat). … → Π n. Id …`, and the trailing `Π n. Id …` is the
    ∀-proof: five components have binders and the sixth is the tail. -/
def sigmaTailProof : Term := prog defer_check {
  fn F (n : Nat) -> Σ (H : Le n n). Le n n { let H0 = LeRefl n; Pair(H0, H0) };
  () }
example : progRejects sigmaTailProof "the TAIL of a Σ chain is runtime-moded" = true := by
  native_decide

end Dllbc.Tests.S32Backstop
end
-- └── end of the M32 R3 backstop-demolition battery ───────────────────────────

-- ┌── M33: Σ0, the comptime tail ───────────────────────────────────────────────
section
namespace Dllbc.Tests.S33Sigma0

open Dllbc Dllbc.Tests

/-! # Σ0 — the comptime tail (M33, suspensions.md §2.7)

    `Σ0 (x : A). P` is the pair whose SECOND projection is comptime — DLLBC's
    subset type, with comptime where Lean's `Subtype`/Coq's `sig` use
    Prop/irrelevance. It is not a new former: it is `sigmaT` with the existing
    `Term.cmpT` on the CODOMAIN, the same marker a capital binder puts on a
    domain, seen from the other end of the pair. Same `Pair`, same `sigmaRec`.

    Three things are pinned here — construction, destruction, erasure — and each
    against a spelling ONE CHARACTER away, so every accept is discriminating. -/

/-! ## Construction: a proof in the tail

    `S32Backstop.sigmaTailProof` is this program with `Σ` where this one has
    `Σ0`, and it is REJECTED. The two differ in one character, and that character
    is the whole feature. -/

open Dllbc.StdLemmas in
def sigmaTailProof0 : Term := prog{
  fn F (n : Nat) -> Σ0 (H : Le n n). Le n n { let H0 = LeRefl n; Pair(H0, H0) };
  () }
example : progOk sigmaTailProof0 = true := by native_decide

/-! **A λ literal in a Σ0 tail is LEGAL**, and this is the promise §2.7 makes
    about the position rather than an accident: the tail is read by ⇝, so a λ
    there lands in a comptime channel and needs no other destination. The proof
    of a ∀-statement — the shape that refuted §2.5 twice — is exactly this. -/
open Dllbc.StdLemmas in
def tailLam0 : Term := prog{
  fn F (n : Nat) -> Σ0 (H : Le n n). (Π (N : Nat) → Le N N)
    { let H0 = LeRefl n; Pair(H0, λ (N : Nat). LeRefl N) };
  () }
example : progOk tailLam0 = true := by native_decide

/-! ## Destruction: the arm binder that receives a Σ0 tail must be CAPITAL

    M33a's arm check, reaching the one binder position it could not answer for.
    `componentMode` needs no case of its own — it already asks `sctx` per field,
    and `reattachSigmaMode` now writes the tail's entry the way it has written the
    first component's since M33a. Four programs: two type spellings (`Σ`/`Σ0`)
    times two arm spellings, and the diagonal is what is accepted. -/

def s0V : Term := .var ⟨0, "v"⟩

/-- Σ0 producer, CAPITAL tail binder at the consumer: accepted. -/
def tail0Upper : Term := prog{
  fn Zap0 (v : &mut List Nat) -> Σ0 (k : Nat). Id (List Nat) (*%s0V) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use0 (w : &mut List Nat) -> Unit
    { let Pair(k2, H2) = Zap0(&m *w); () };
  () }
example : progOk tail0Upper = true := by native_decide

/-- …and lowercase at the same consumer: refused, because the tail is comptime. -/
def tail0Lower : Term := prog defer_check {
  fn Zap0 (v : &mut List Nat) -> Σ0 (k : Nat). Id (List Nat) (*%s0V) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use0 (w : &mut List Nat) -> Unit
    { let Pair(k2, h2) = Zap0(&m *w); () };
  () }
example : progRejects tail0Lower "Capitalise the arm binder" = true := by native_decide

/-- The SAME consumer over a plain `Σ`: now lowercase is the legal spelling… -/
def tailRunLower : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (k : Nat). Id (List Nat) (*%s0V) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(k2, h2) = Zap(&m *w); () };
  () }
example : progOk tailRunLower = true := by native_decide

/-- …and capital is refused. One character in the CALLEE's return type decides
    which spelling of the CALLER's arm is legal, in both directions — which is
    what says the rule reads the type and not the shape. -/
def tailRunUpper : Term := prog defer_check {
  fn Zap (v : &mut List Nat) -> Σ (k : Nat). Id (List Nat) (*%s0V) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(k2, H2) = Zap(&m *w); () };
  () }
example : progRejects tailRunUpper "lower-case the arm binder" = true := by native_decide

/-! ## Erasure: the executing machine is untouched

    A Σ0 component is comptime knowledge — evaluated today, dropped by
    compilation, exactly as a capital Σ component already is. So the program runs,
    and the DATA component is what the run leaves behind. -/

open Dllbc.StdLemmas in
def erase0 : Term := prog{
  fn F0 (n : Nat) -> Σ0 (k : Nat). Le n n { let H0 = LeRefl n; Pair(n, H0) };
  let Pair(a, H) = F0(S(S(Z)));
  let y = a; () }
example : progOk erase0 = true := by native_decide
example : (match runProgram erase0 with
           | .ok env => (env.lookup "y") == some (Val.nat 2)
           | .error _ => false) = true := by native_decide

/-! ## Elimination: `sigmaRec`, unchanged

    §2.7 promises no new eliminator, and this is that promise as two programs: the
    SAME `elim` over the same pair, with the motive's binder type written `Σ` in
    one and `Σ0` in the other. `sigmaRec`'s second parameter is the type FAMILY
    `λ x. B`, and `⇝` is a mode marker rather than part of `B`, so a Σ0's family
    is its Σ twin's and the elimination is literally the same term. -/

open Dllbc.StdLemmas in
def elimSig : Term := prog defer_check {
  let P0 = Pair(Z, LeRefl Z);
  let K = elim P0 return (λ (p : Σ (k : Nat). Le Z Z). Nat) { Pair (k) (h) => k };
  () }
example : progOk elimSig = true := by native_decide

open Dllbc.StdLemmas in
def elimSig0 : Term := prog defer_check {
  let P0 = Pair(Z, LeRefl Z);
  let K = elim P0 return (λ (p : Σ0 (k : Nat). Le Z Z). Nat) { Pair (k) (H) => k };
  () }
example : progOk elimSig0 = true := by native_decide

end Dllbc.Tests.S33Sigma0
end
-- └── end of the M33 Σ0 battery ───────────────────────────────────────────────

-- ┌── M32 R4: `callV` retires, and the split it looked like it carried ─────────
section
namespace Dllbc.Tests.S32Spine

open Dllbc Dllbc.Tests
open Dllbc.StdLemmas (LeRefl)

/-! # The application spine, and what retiring a node must not take with it

    `Term.callV` is gone: `f(a, b)` is surface sugar for `.app (.app f a) b`, so
    the surface's n-ary shape and the document's binary grammar are one thing.

    The hazard the plan named is that `callV` LOOKED like it carried the
    mint-vs-remember split, when §12 decision 5 says that split is ARROW-keyed —
    ⇒ mints a fresh existential at the instantiated codomain, ⇝ remembers the
    structured neutral. With two nodes you cannot tell which key is load-bearing;
    with one you can, and these are the assertions that say so. -/

/-! ## §A. The two spellings are ONE TERM

    Not "behave the same" — the same `Term`, which is the strongest form the
    claim has and the one that makes every other assertion about calls apply to
    juxtaposition automatically. -/

def spelledCall : Term := prog defer_check { let F = λ (x : Nat). x; let z = F(2); () }
def spelledJux  : Term := prog defer_check { let F = λ (x : Nat). x; let z = F 2; () }
example : Term.beq spelledCall spelledJux = true := by native_decide

/-! ## §B. ⇒ MINTS at the instantiated codomain

    An abstract `σ : Π` applied under ⇒ forgets the application and keeps what
    the type promised — a FRESH σ per call, which is why the two calls below get
    distinct ones. This is `callV`'s old rule, and it now runs off the value. -/

def mintTwice : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let y = F(2); let z = F(2); () }
example : tailEnv mintTwice [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by
  native_decide

-- …and the juxtaposed spelling mints too, which is §A's consequence made
-- explicit: if this ever diverges from the line above, the split has gone
-- node-keyed again.
def mintTwiceJux : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat); let y = F 2; let z = F 2; () }
example : tailEnv mintTwiceJux [("F", .sym 0), ("y", .sym 1), ("z", .sym 2)] = true := by
  native_decide

/-! ## §C. ⇝ REMEMBERS the structured neutral — and refuses to ENTER

    The other half, and it needs both directions. ⇝ has a reading of an
    application of an ABSTRACT function (the neutral `f a`), and no reading at
    all of an application that must be ENTERED — a sealed function's result is a
    fresh existential minted at an event, and ⇝ has no events. `reflectC` keyed
    that on the `.callV` node until R4; it keys it on the callee's VALUE now. -/

-- REMEMBERED: a Π-typed comptime parameter applied inside a spec position. The
-- program checks, which is the assertion — the neutral has a reading.
def rememberNeutral : Term := prog{
  fn Use (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk rememberNeutral = true := by native_decide

-- REFUSED: a SEALED function's call, ⇝-read at a capital `let`. Entering is an
-- event; this is the refusal that retired with `.callV` and came back on the
-- value.
def enterRefused : Term := prog defer_check {
  fn GiveLe (a : Nat) -> Le a a { %LeRefl a };
  fn Caller (n : Nat) -> Unit { let P = GiveLe(n); () };
  () }
example : progRejects enterRefused "not in the comptime fragment" = true := by native_decide

/-! ## §D. A `.var`-headed spine is IMPERATIVE

    `Term.imperative` named `.callV` explicitly, and the classification is what
    `Term.lamImperative` reads to decide whether applying a λ is ⇒-entry. Read
    off the arguments alone, a nullary `fn` whose body is only a call would
    classify PURE — its one binder is the Unit-desugar's comptime `U§`, so the
    binder half cannot save it, and `.app (.var g) .unit` has no imperative
    leaf. A `.const`/`.pvar` head stays comptime, which is the pure spine. -/

example : Term.imperative (.app (.var ⟨0, "g"⟩) .unit) = true := by native_decide
example : Term.imperative (.app (.const "Len") (.var ⟨0, "l"⟩)) = false := by native_decide
example : Term.imperative (.app (.pvar "Le") (.pvar "a")) = false := by native_decide
-- A bare `.var` is a snapshot read, not a call, and both arrows have a rule.
example : Term.imperative (.var ⟨0, "g"⟩) = false := by native_decide

/-! ## §E. The `[k]` PERMUTATION survives (E8's standing decision)

    `retarget` reorders a call's arguments to match a `[k]`-hoisted callee's
    telescope — the hoist puts the scrutinee first, so a call written in
    declaration order has to be reordered the same way, and omitting it silently
    passes a borrow where a `Nat` is expected. E8 keeps that at the surface.
    Retiring `callV` changed what `retarget` BUILDS and not what it decides, and
    these assert the decision against the new shape rather than against a
    program that could pass for other reasons. -/

-- `[k]` at parameter 1: the built spine puts argument 1 FIRST.
example : Term.beq
    (FnMacro.retarget [("f", ⟨7, "f"⟩, some 1)] (.call "f" [.unit, .type]))
    (Term.appSpine (.var ⟨7, "f"⟩) [.type, .unit]) = true := by native_decide

-- …and with no hint, declaration order is kept — without which the line above
-- would pass on a `retarget` that reordered unconditionally.
example : Term.beq
    (FnMacro.retarget [("f", ⟨7, "f"⟩, none)] (.call "f" [.unit, .type]))
    (Term.appSpine (.var ⟨7, "f"⟩) [.unit, .type]) = true := by native_decide

-- The nullary desugar's `()` still arrives at the call site (M32 R2), which is
-- what makes a no-argument `fn` a spine at all rather than a bare variable.
example : Term.beq
    (FnMacro.retarget [("f", ⟨7, "f"⟩, none)] (.call "f" []))
    (.app (.var ⟨7, "f"⟩) .unit) = true := by native_decide

-- And the spine reader inverts the builder, head and all.
example : (Term.appSpineVar? (Term.appSpine (.var ⟨9, "f"⟩) [.unit, .type]))
    == some (⟨9, "f"⟩, [.unit, .type]) := by native_decide
example : (Term.appSpineVar? (Term.appSpine (.const "Len") [.unit])).isSome = false := by
  native_decide

end Dllbc.Tests.S32Spine
end
-- └── end of the M32 R4 spine battery ─────────────────────────────────────────

-- ┌── the M33a ⇝-transparency battery ──────────────────────────────────────────
section
namespace Dllbc.Tests.S33Cmp
open Dllbc

/-! # A `⇝` domain is TRANSPARENT to the kernel's type walks (M33a)

    R3b put §2.1's mode on the Σ DOMAIN — `Σ (H : τ)` elaborates to
    `.sigmaT "H" (⇝τ) …` — and that made the Σ half of the convention operative.
    What it did not do is tell the walks that traverse a return type about the
    new former, and three of them had no case for it: they end in a
    `| t => t`-shaped fallthrough, so a `⇝τ` was treated as a LEAF and its
    subterm was skipped in silence.

    `markExit` is the one with teeth. §5.4's exit-snapshot transform stamps a
    borrow parameter's `*v` as `@exit(*v)` throughout the return type, and a
    comptime component's type was not reached — so that component alone read the
    ENTRY payload while every other component read the exit. The symptom is a
    type error at a branch whose proof is correct: `splitOff`'s `Z` arm returns
    `Refl` at `Id Nil Nil` and the audit demanded `Id σ0 Nil` of it.

    **This is what actually blocked R3b's residual 2, and it is not what R3b
    said blocked it.** R3b recorded the four red assertions as a CONSUMER
    problem — "a match-arm binder's case is unchecked against the Σ's" — and
    with these three cases added, the same four go green with their arm binders
    untouched and still lowercase. The consumer check is worth having on its own
    terms (S33Arms, below) but it is not the unblocker; a producer-side silent
    skip was.

    Pinned as one program in two spellings one character apart, plus the lie that
    makes the accept discriminating. -/

def zapUnder (dom : Term) : Term := prog{
  fn Zap (v : &mut List Nat) -> %dom { *v := Nil; Pair(Refl, unit) };
  () }

def zapV : Term := .var ⟨0, "v"⟩

-- The COMPTIME component: its `Id` mentions `*v`, so it is exactly the type
-- `markExit` has to reach through the `⇝` to stamp.
def zapCmp : Term := prog defer_check { Σ (H : Id (List Nat) (*%zapV) Nil). Unit }
-- …and its one-character twin, which was green before M33a and is the control
-- that says the `⇝` is the whole difference.
def zapRun : Term := prog defer_check { Σ (h : Id (List Nat) (*%zapV) Nil). Unit }
-- …and the lie, so neither accept is vacuous: the exit is `Nil`, not `[Z]`.
def zapLie : Term := prog defer_check { Σ (H : Id (List Nat) (*%zapV) (Cons Z Nil)). Unit }

example : progOk (zapUnder zapCmp) = true := by native_decide
example : progOk (zapUnder zapRun) = true := by native_decide
example : progRejects (zapUnder zapLie) "does not have return type" = true := by native_decide

end Dllbc.Tests.S33Cmp
end
-- └── end of the M33a ⇝-transparency battery ──────────────────────────────────

-- ┌── the M33a arm-binder mode battery ─────────────────────────────────────────
section
namespace Dllbc.Tests.S33Arms
open Dllbc

/-! # §2.1's convention reaches the MATCH ARM (M33a)

    A match arm's binders are binders, and they were the last position whose
    spelling nothing read. Both directions are checked, because they are two
    different mistakes — a capital binder over data claims erasure of something
    the match moves; a lowercase binder over a comptime component is the
    runtime-binding-holds-knowledge state the `let` already refuses
    (`fenceComptime`), reached by a rule that was not looking.

    Each direction is one program in two spellings one character apart, so each
    reject is discriminating against its own accept rather than against nothing. -/

/-! ## Direction 1 — a CAPITAL arm binder over a runtime DATA component

    `Cons`' head and tail are data at every type there is, which is why this
    direction needs no type in hand at all: the fixed constructor basis decides
    it, and `Pair` is the only member it does not decide. -/

def armDataLower : Term := prog{
  match Cons(Z, Nil) { Nil => (), Cons(h, t) => () } }

def armDataUpper : Term := prog defer_check {
  match Cons(Z, Nil) { Nil => (), Cons(H, t) => () } }

example : progOk armDataLower = true := by native_decide
example : progRejects armDataUpper "lower-case the arm binder" = true := by native_decide

/-! ## Direction 2 — a LOWERCASE arm binder over a COMPTIME component

    The producer is `S33Cmp.zapCmp`'s shape: a Σ whose component binder is
    capital, so `readResult` ⇝-reads that component and the CALLER's
    `buildResult` mints its σ at a `⇝` type. That `sctx` entry is the whole of
    the mode source — no type is re-derived at the match. -/

def armV : Term := .var ⟨0, "v"⟩

def armCmpUpper : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (H : Id (List Nat) (*%armV) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(H2, u) = Zap(&m *w); () };
  () }

def armCmpLower : Term := prog defer_check {
  fn Zap (v : &mut List Nat) -> Σ (H : Id (List Nat) (*%armV) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(h2, u) = Zap(&m *w); () };
  () }

example : progOk armCmpUpper = true := by native_decide
example : progRejects armCmpLower "Capitalise the arm binder" = true := by native_decide

/-! ## …and the SAME consumer over a runtime component is unchanged

    The control that says direction 2 keys on the producing Σ binder's case and
    not on the component sitting in a `Pair`: one character in the CALLEE's
    return type flips which spelling of the CALLER's arm is legal. -/

def armRunLower : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (h : Id (List Nat) (*%armV) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(h2, u) = Zap(&m *w); () };
  () }

example : progOk armRunLower = true := by native_decide

end Dllbc.Tests.S33Arms
end
-- └── end of the M33a arm-binder mode battery ─────────────────────────────────


-- ┌── M33 macro-top: the twin probe ─────────────────────────────────────────────
section
namespace Dllbc.Tests.S33Macro
open Dllbc Dllbc.Tests

/-! # The same function, written twice — the surface and the kernel

    The kernel's `Add` is a hand-written `Term` (`Pure.kAddFn`), because the CARVE
    rule's premises are stated against it and a kernel rule cannot cite a library
    it does not import. The surface can say the same thing, and this is the two
    spellings side by side.

    **They were not the same term, and the two ways they differed are this
    milestone's whole subject.** Pinned at commit 0 as they were then, so that
    the commits removing each difference are measurements rather than claims:

      * ~~the surface's recursor ARM binders are unmarked where the kernel's
        `clam` marks them~~ — **CLOSED at commit 1**: `elabUElim` puts every arm
        binder through `binderDom` now, so `λ A' : ⇝Nat` on both sides;
      * the kernel's MOTIVE binder is the reserved unmarked `§_` where a surface
        motive has to name its binder, and a named capital binder is marked —
        `λ §_ : Nat. Nat` against `λ N : ⇝Nat. Nat`. This one cannot be closed
        from the surface, because `§_` is unwritable: the only way the two terms
        become one is for the KERNEL term to be the surface term, which is
        commit 3.

    Conversion is mode-blind (`Term.convEq`) and both were `natRec` over the same
    arms, so the third line was TRUE from the start: the two spellings always
    denoted the same function. What was not true is that they were the same TERM,
    and `Term.alphaEq` — the key `abstractInto` generalizes with — is
    mode-sensitive by design, so the difference was one the generalization sweep
    could see and the type-checker could not. -/

def surfAdd : Term :=
  prog defer_check { λ (A : Nat). λ (B : Nat). elim A return (λ (N : Nat). Nat) { Z => B, S (A') R => S(R) } }

-- **ALL THREE TRUE at commit 3.** Pinned `false`/`false`/`true` at commit 0;
-- commit 1 closed the arm-binder drift and commit 3 the motive one, by making
-- `Pure.kAddFn` itself a `prog{ }`. The first line is still doing work rather
-- than comparing a term with itself: `surfAdd` names its motive binder `N` where
-- the kernel names it `Am`, so what it says is that two INDEPENDENT surface
-- spellings of `Add` are one term up to α — and `Term.alphaEq` is mode-sensitive,
-- so it is also saying every marker agrees.
example : Term.alphaEq surfAdd Pure.kAddFn = true := by native_decide
example : (Pure.nf 1000 surfAdd == Pure.nf 1000 Pure.kAddFn) = true := by native_decide
example : Term.convEq (Pure.nf 1000 surfAdd) (Pure.nf 1000 Pure.kAddFn) = true := by native_decide

-- The behaviour, so that a later respell that agrees structurally and computes
-- something else cannot pass on the two lines above.
example : (Pure.nf 200 (.app (.app surfAdd (Term.nat 2)) (Term.nat 3)) == Term.nat 5) = true := by
  native_decide

/-! ## The constructor basis, checked instead of kept adjacent

    `Val.ctorNames` is the list the SURFACE reserves as binder keywords, and
    `Pure.ctorSig` is the kernel's field-type table. They must agree, and until
    M33 macro-top the only thing making that true was that they sat next to each
    other in one file with a comment saying so. With the macro layer below the
    kernel the list had to move down to `Value.lean`, so the adjacency is gone —
    and what replaces it is stronger than what it replaced, because a convention
    a reader has to notice becomes a build that goes red.

    Both directions. Every reserved name has a signature; and every constructor
    the exhaustiveness table can NAME, at each type former there is, is reserved.
    The second is what catches a constructor added to `ctorSig` and `typeCtors`
    and forgotten at the surface — which is the omission the adjacency comment
    was worried about, and the direction it could not have caught either. -/

def basisTypes : List Term :=
  [prog defer_check { Nat }, prog defer_check { Bool }, prog defer_check { Unit }, prog defer_check { Bot }, prog defer_check { List Nat },
   prog defer_check { Σ (X : Nat). Nat }, prog defer_check { Id Nat unit unit }, prog defer_check { Array 2 Nat }]

example : Val.ctorNames.all (fun n => (Pure.ctorSig n).isSome) = true := by native_decide
example : basisTypes.all (fun ty => ((Pure.typeCtors ty).getD []).all
    (fun c => Val.ctorNames.contains c)) = true := by native_decide

-- …and the control the two lines above need: a name outside the basis has no
-- signature, so the first is a claim about THIS list rather than about `ctorSig`
-- answering for everything.
example : (Pure.ctorSig "Cons2").isNone = true := by native_decide

end Dllbc.Tests.S33Macro
end
-- └── end of the M33 macro-top twin probe ──────────────────────────────────────
