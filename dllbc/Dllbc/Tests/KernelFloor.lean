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
  against terms built by hand (S15Elab checks `StdLemmas.le_refl`, authored in
  `prog{ }`, convertible with the hand-built `Std.le_reflT`). Those anchors are
  only worth something if the hand-built side is independently exercised, which is
  this file's `add`/`VecF`/recursor library.

**The OLD reason is superseded, and is recorded here so a future simplification
pass does not refute it and delete an exempted file.** The header used to say
"pure terms have no surface syntax, so the library is built directly from the
pure `Term`/`Val` formers". That was true at §4 and false since §15: `prog{ … }`
authors pure terms, and `StdLemmas` is written in it. The rawness here is a
CHOICE about what is under test, not a gap in the grammar.

σ's are seeded via a variable slot (`readC` reads the snapshot).
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S4Pure

-- SUBJECT FILE: the whole library here is built directly from raw Term/Val formers,
-- and the rawness is the POINT rather than a missing grammar (`prog{ }` would author
-- every one of these since §15) — these raw constructions ARE the subject under test
-- (reduction, hasType, convert), reached with no macro in the loop. Every raw
-- constructor below is intentional test machinery. See the exemption in the header.

/-! ## Pure library (built from the raw formers) — SUBJECT: raw pure Terms under test -/

def natT : Term := .const "Nat"
def tnat : Nat → Term | 0 => .ctorApp "Z" [] | n + 1 => .ctorApp "S" [tnat n]

/-- `add m n = natRec (λ_.Nat) n (λ_. λr. S r) m`. -/
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
    (.lam "§0" (.const "Nat") (.lam "§1" (.const "Nat") (.ctor "S" [.pvar "§1"])))) (.sym 0)) = true := by
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
def natV : Val := .const "Nat"
def listNat : Val := .app (.const "List") natV
def vecFV : Val :=
  .lam "T" .type (.lam "n" natV
    (.app (.app (.app (.app (.const "natRec") (.lam "_" natV .type)) (.const "Unit"))
      (.lam "n'" natV (.lam "rec" .type (.sigmaT "_" (.pvar "T") (.pvar "rec"))))) (.pvar "n")))
/-- `Σ (l : Nat). VecF Nat l` (the l is a genuine dependency). -/
def sigVecF : Val := .sigmaT "l" natV (.app (.app vecFV natV) (.pvar "l"))

-- Positives: `Cons σₑ σ : List Nat` under sctx = {σₑ : Nat, σ : List Nat};
-- `Pair 1 p : Σ (l:Nat). VecF Nat l` with `p = Pair 5 unit : VecF Nat 1` — the
-- second field's type is instantiated at the first field's value.
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctor "Cons" [.sym 0, .sym 1]) listNat = true := by native_decide

example : expectHasType [] []
  (.ctor "Pair" [nat 1, .ctor "Pair" [nat 5, .ctor "unit" []]]) sigVecF = true := by native_decide

-- Negatives: wrong constructor for the type; a `Pair` whose second field fails
-- the instantiated type (`True` does not inhabit `VecF Nat 1`).
example : expectHasType [] [(0, natV), (1, listNat)]
  (.ctor "Cons" [.sym 0, .sym 1]) (.const "Bool") = false := by native_decide

example : expectHasType [] []
  (.ctor "Pair" [nat 1, .ctor "True" []]) sigVecF = false := by native_decide

/-! ## Conversion negative under a binder -/

-- Two λ's that differ only in their bodies are not convertible (no eta; bodies
-- compared structurally after normalization, which renames both binders to the
-- same level name and so cannot be what tells them apart).
example : Val.convert 1000 (.lam "u" natV (.pvar "u")) (.lam "u" natV (.ctor "Z" [])) = false := by
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
example : (Val.nfV 1000 (.lam "x" natV (.pvar "x")) == .lam "§0" natV (.pvar "§0")) = true := by
  native_decide
example : (Val.nfV 1000 (.lam "a" natV (.lam "b" natV (.app (.pvar "a") (.pvar "b"))))
            == .lam "§0" natV (.lam "§1" natV (.app (.pvar "§0") (.pvar "§1")))) = true := by
  native_decide

-- (3): two α-variants of one function read back to the SAME tree — not merely to
-- convertible ones, which is the weaker fact `convert` would still give if
-- readback minted from a counter.
example : (Val.nfV 1000 (.lam "a" natV (.lam "b" natV (.app (.pvar "a") (.pvar "b"))))
            == Val.nfV 1000 (.lam "p" natV (.lam "q" natV (.app (.pvar "p") (.pvar "q"))))) = true := by
  native_decide

-- (4): and so they convert. (Under the de Bruijn representation this was true for
-- a reason that no longer exists — the binders had no names to differ in.)
example : Val.convert 1000 (.lam "x" natV (.pvar "x")) (.lam "y" natV (.pvar "y")) = true := by
  native_decide

-- (5): SHADOWING IS THE SCOPE RULE. `λ (x : Nat). λ (x : Nat). x` is the second
-- projection, and both halves are asserted — it converts with `λ a. λ b. b` and
-- does NOT convert with `λ a. λ b. a`. Nothing was renamed to make this work;
-- the evaluator's environment is prepended to and the lookup finds the first hit.
example : Val.convert 1000 (.lam "x" natV (.lam "x" natV (.pvar "x")))
                           (.lam "a" natV (.lam "b" natV (.pvar "b"))) = true := by native_decide
example : Val.convert 1000 (.lam "x" natV (.lam "x" natV (.pvar "x")))
                           (.lam "a" natV (.lam "b" natV (.pvar "a"))) = false := by native_decide

-- (6): the renaming is not an erasure — two functions that differ in WHICH binder
-- they return stay distinct after it.
example : Val.convert 1000 (.lam "a" natV (.lam "b" natV (.pvar "a")))
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
open Dllbc.Val

namespace Dllbc.Tests.S10Ford

/-! ## Pure library, as `Val`s (types and proofs are terms) -/

def natV : Val := .const "Nat"
def sZ : Val := .ctor "Z" []
def sS (v : Val) : Val := .ctor "S" [v]
def vnat : Nat → Val | 0 => sZ | n + 1 => sS (vnat n)
def refl : Val := .ctor "Refl" []
def unitV : Val := .ctor "unit" []

def natRecV (P z s n : Val) : Val := .app (.app (.app (.app (.const "natRec") P) z) s) n
def jV (a aa P d b p : Val) : Val := .app (.app (.app (.app (.app (.app (.const "j") a) aa) P) d) b) p
def kV (a aa P d p : Val) : Val := .app (.app (.app (.app (.app (.const "k") a) aa) P) d) p
def botElimV (t x : Val) : Val := .app (.app (.const "botElim") t) x

/-- `NatCode : Nat → Nat → Type` by double `natRec`: `(Z,Z) ↦ ⊤`, `(S,S) ↦`
    code of predecessors, mixed `↦ ⊥`. The diagonal `NatCode a a` is `⊤`. -/
def zCase : Val :=
  .lam "b" natV (natRecV (.lam "_" natV .type) (.const "Unit")
    (.lam "_" natV (.lam "_" .type (.const "Bot"))) (.pvar "b"))
def sCase : Val :=
  .lam "a'" natV (.lam "recA" (.pi "_" natV .type) (.lam "b" natV
    (natRecV (.lam "_" natV .type) (.const "Bot")
      (.lam "b'" natV (.lam "_" .type (.app (.pvar "recA") (.pvar "b'")))) (.pvar "b"))))
def natCodeV : Val := .lam "a" natV (natRecV (.lam "_" natV (.pi "_" natV .type)) zCase sCase (.pvar "a"))
def natCode (a b : Val) : Val := .app (.app natCodeV a) b

/-- `pred : Nat → Nat` (`pred Z = Z`, `pred (S n) = n`). -/
def predV : Val :=
  .lam "n" natV (natRecV (.lam "_" natV natV) sZ (.lam "m" natV (.lam "_" natV (.pvar "m"))) (.pvar "n"))

/-! ## §10 kernel: the ι-rules (`j` and `k` fire on `Refl`)

    `j A a P d b p` and `k A a P d p` reduce to `d` when the proof is `Refl`;
    on a symbolic proof they are stuck neutral values. (The motive is irrelevant
    to reduction — ι fires on the proof.) -/

-- j Nat Z P 42 Z Refl ↦ 42
example : (Val.nfV 1000 (jV natV sZ (.lam "b" natV (.lam "q" natV natV)) (vnat 42) sZ refl) == vnat 42) = true := by
  native_decide

-- k Nat Z P 7 Refl ↦ 7
example : (Val.nfV 1000 (kV natV sZ (.lam "q" natV natV) (vnat 7) refl) == vnat 7) = true := by native_decide

-- On a *symbolic* proof (sym 0), `j` does not fire — it is a stuck value, not 42.
example : (Val.nfV 1000 (jV natV sZ (.lam "b" natV (.lam "q" natV natV)) (vnat 42) sZ (.sym 0)) == vnat 42) = false := by
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
  fn learn (n : Nat, p : Id Nat n 2) -> Nat { match p { Refl => n } };
  () }

example : progOk learn = true := by native_decide

-- The refinement is OBSERVABLE in the final Ω: after the match, `let m = n`
-- copies the *refined* value, so `m ↦ 2` (not a symbolic `n`). Had refinement
-- not fired, `m` would be a `sym`.
def learnObs : Term := prog{
  fn learnObs (n : Nat, p : Id Nat n 2) -> Unit { match p { Refl => { let m = n; () } } };
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
  fn learnDemand (n : Nat, p : Id Nat n 2) -> Unit {
    match p { Refl => { let m = n; let c = (Refl : Id Nat m 2); () } } };
  () }
example : progOk learnDemand = true := by native_decide

-- THE TWIN, and it is what makes the certificate a demand rather than a
-- decoration: the same `let m = n` and the same seal with the match REMOVED. `m`
-- is unrefined, so `Refl` has nothing to inhabit.
def learnDemandNo : Term := prog{
  fn learnDemandNo (n : Nat, p : Id Nat n 2) -> Unit {
    let m = n; let c = (Refl : Id Nat m 2); () };
  () }
example : progRejects learnDemandNo "does not have its ascribed type"
  = true := by native_decide

-- Through a borrow: `pb : &mut (Id Nat n 2)`. The refl-match reads through the
-- borrow, refines `n := 2`, and — because refinement now reaches the owed
-- obligations — the audit sees `pb` owing `Id Nat 2 2`, which its `Refl` payload
-- inhabits. This is the case that forced obligations into machine state.
def learnBorrow : Term := prog{
  fn learnBorrow (n : Nat, pb : &mut (Id Nat n 2)) -> Unit {
    match pb { Refl => { let m = n; () } } };
  () }

example : progOk learnBorrow = true := by native_decide

-- …and the same conversion through the borrow, so the demand form covers both
-- routes the refinement takes rather than only the owned one.
def learnBorrowDemand : Term := prog{
  fn learnBorrowDemand (n : Nat, pb : &mut (Id Nat n 2)) -> Unit {
    match pb { Refl => { let m = n; let c = (Refl : Id Nat m 2); () } } };
  () }
example : progOk learnBorrowDemand = true := by native_decide

-- Rigid-rigid: `p : Id Nat Z (S Z)`. Neither endpoint is a σ, so there is no
-- solution by refinement — STUCK, naming `j`/`k` as the elimination route. The
-- kernel does NOT auto-discharge the conflict; that is the library's job (below).
def rigidStuck : Term := prog{
  fn rigidStuck (p : Id Nat 0 1) -> Nat { match p { Refl => 0 } };
  () }

example : progRejects rigidStuck "rigid" = true := by native_decide
example : progRejects rigidStuck "j/k" = true := by native_decide

-- Occurs check: `p : Id Nat n (S n)`. Refining `n := S n` would be cyclic —
-- rejected before it can loop.
def occursFn : Term := prog{
  fn occ (n : Nat, p : Id Nat n (S n)) -> Unit { match p { Refl => () } };
  () }

example : progRejects occursFn "occurs check" = true := by native_decide

/-! ## Exhaustiveness and scope (Id's constructor set is `{Refl}`) -/

-- An empty match on `p : Id Nat n 2` is non-exhaustive: `Refl` is uncovered.
example : progRejects (prog{
  fn f (n : Nat, p : Id Nat n 2) -> Unit { match p { } }; () }) "non-exhaustive" = true := by native_decide

-- A stray non-`Refl` constructor is likewise not enough to be exhaustive.
example : progRejects (prog{
  fn f (n : Nat, p : Id Nat n 2) -> Unit { match p { Z => () } }; () }) "non-exhaustive" = true := by native_decide

-- Scope guard: `Id` over a *borrow* type is rejected — reflecting the borrow-type
-- index throws (borrow types live only at telescope positions), no special
-- machinery needed. (Id over ordinary indexed types is unrestricted.)
example : progRejects (prog{
  fn f (q : Id (&mut Nat) 0 0) -> Unit { () }; () }) "borrow type" = true := by native_decide

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
def nncMotive : Val :=
  .lam "b" natV (.lam "q" (.idT natV sZ (.pvar "b")) (.app (.app natCodeV sZ) (.pvar "b")))
def nncProof (n p : Val) : Val := jV natV sZ nncMotive unitV (sS n) p
-- σ0 = n : Nat, σ1 = p : Id Nat Z (S n)
def nncSctx : List (Nat × Val) := [(0, natV), (1, .idT natV sZ (sS (.sym 0)))]

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

    Motive `P y (_ : Id Nat (S a) y) = Id Nat a (pred y)`; base `Refl : Id Nat a
    (pred (S a)) = Id Nat a a`; transported to `Id Nat a (pred (S b)) = Id Nat a
    b`. (`pred (S σ)` reduces because the `S` is concrete around the symbol.) -/

def injMotive (a : Val) : Val :=
  .lam "y" natV (.lam "q" (.idT natV (sS a) (.pvar "y")) (.idT natV a (.app predV (.pvar "y"))))
def injProof (a b p : Val) : Val := jV natV (sS a) (injMotive a) refl (sS b) p
def injSctx : List (Nat × Val) := [(0, natV), (1, natV), (2, .idT natV (sS (.sym 0)) (sS (.sym 1)))]

example : expectHasType [] injSctx (injProof (.sym 0) (.sym 1) (.sym 2)) (.idT natV (.sym 0) (.sym 1)) = true := by
  native_decide

-- The proof genuinely proves `Id Nat a b`, not a wrong goal like `Id Nat a (S b)`.
example : expectHasType [] injSctx (injProof (.sym 0) (.sym 1) (.sym 2)) (.idT natV (.sym 0) (sS (.sym 1))) = false := by
  native_decide

/-! ### UIP / K: `(p : Id Nat a a) → Id (Id Nat a a) p Refl`, via `K`

    Streicher K: motive `P q = Id (Id Nat a a) q Refl`, base `Refl : Id … Refl
    Refl`, so `k … p : Id (Id Nat a a) p Refl` — uniqueness of identity proofs,
    a decided commitment of this kernel. -/

def idAA (a : Val) : Val := .idT natV a a
def uipMotive (a : Val) : Val := .lam "q" (idAA a) (.idT (idAA a) (.pvar "q") refl)
def uipProof (a p : Val) : Val := kV natV a (uipMotive a) refl p
def uipSctx : List (Nat × Val) := [(0, natV), (1, idAA (.sym 0))]

example : expectHasType [] uipSctx (uipProof (.sym 0) (.sym 1)) (.idT (idAA (.sym 0)) (.sym 1) refl) = true := by
  native_decide

/-! ### `NatCode` computes (the double-`natRec` corners) -/

example : (Val.convert 1000 (natCode sZ sZ) (.const "Unit")) = true := by native_decide       -- (Z,Z) ↦ ⊤
example : (Val.convert 1000 (natCode sZ (sS sZ)) (.const "Bot")) = true := by native_decide    -- (Z,S) ↦ ⊥
example : (Val.convert 1000 (natCode (sS sZ) sZ) (.const "Bot")) = true := by native_decide    -- (S,Z) ↦ ⊥
example : (Val.convert 1000 (natCode (vnat 2) (vnat 2)) (.const "Unit")) = true := by native_decide  -- diagonal ↦ ⊤

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
`Dllbc.Std` (`Le`, `eqb`/`leb`, `count`, `Bound`/`Sorted`, `le_refl`). Those were
tested here by `Val.convert`/`Val.nfV` computation probes and `expectHasType`
inhabitation probes — granular meta-assertions that the corpus has long since
subsumed. Every bound in a checked program forces `Le` to compute (an ex-falso
branch is precisely `Le (S n) Z` computing to `Bot`); every count postcondition
forces `count`, and `count` is `listRec` threading a `boolRec` on `eqb`; every
`Sorted`/`Bound` spec forces the predicates by inhabitation, and the
out-of-bounds rejections are the no-inhabitant fact. `le_refl` is checked at its
stated type in S15Elab and round-tripped there against `Std.le_reflT`.

**§11.4's naturalness probe is gone too.** It was the M12+ work-list — the
quicksort program we wanted, annotated line by line with what the calculus could
not yet express — and every gap it named has since closed: dependent call-site
instantiation (§12), Term-level `Std` at telescope positions (§12), the
two-cursor access-at-depth idiom (M14's bounds cursor), `take`/`drop` (Std, and
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
def zCase : Term := prog{
  λ (m : Nat). natRec (λ (x : Nat). Type) Unit (λ (x : Nat). λ (r : Type). Bot) m }

/-- `NatCode`'s `S` row: `Z ↦ ⊥`, `S m2 ↦ code of the predecessors` (the
    outer recursor's `ih`, applied). -/
def sCase : Term := prog{
  λ (n : Nat). λ (f : Π (x : Nat) → Type). λ (m : Nat).
    natRec (λ (x : Nat). Type) Bot (λ (m2 : Nat). λ (r : Type). f m2) m }

/-- `NatCode : Nat → Nat → Type`, by `natRec` at a Π-valued motive. -/
def natCode : Term := prog{
  λ (a : Nat). natRec (λ (x : Nat). Π (y : Nat) → Type) zCase sCase a }

/-- The no-confusion motive at `Z`: `λ m. λ (q : Id Nat Z m). NatCode Z m`. With
    `j`'s `d := unit : NatCode Z Z`, `j Nat Z nncMotive unit (S n) p` has type
    `NatCode Z (S n)`, which computes to `Bot`. -/
def nncMotive : Term := prog{ λ (m : Nat). λ (q : Id Nat Z m). natCode Z m }

/-! ## §11.1 The pure lift — ⇒ produces proof terms -/

-- Returning a proof: `Refl` at an `Id`-typed return. A `ctorApp`, so it lifts
-- trivially — the degenerate case, which is why it goes first.
example : progOk (prog{
  fn retRefl (a : Nat) -> Id Nat a a { Refl };
  () }) = true := by native_decide

-- Storing a proof: a J-application (which ⇝-reduces to `Refl`) is ⇒-lifted into a
-- `Pair`'s dependent second field and audited against `Id Nat a a`.
example : progOk (prog{
  fn storeProof (a : Nat) -> Σ (x : Nat) → Id Nat x x
    { Pair(a, j Nat a (λ (x : Nat). λ (q : Id Nat a x). Id Nat a x) Refl a Refl) };
  () }) = true := by native_decide

-- The M10 conflict discharge, as a dead branch in a checked `fn` (the shape the
-- fording spec originally wanted). The `False` arm holds `p : Id Nat Z (S n)`,
-- derives ⊥ through the no-confusion spine, and ⇒-lifts `botElim Nat (…)` to
-- close the branch.
example : progOk (prog{
  fn discharge (n : Nat, p : Id Nat Z (S n), b : Bool) -> Nat {
    match b {
      True => Z,
      False => botElim Nat (j Nat Z nncMotive unit (S n) p)
    } };
  () }) = true := by native_decide

-- Not vacuous: the discharge is what closes the branch, and without it the arm
-- has nothing of the return type to give. The same function with the `False` arm
-- returning the PROOF rather than eliminating it is rejected.
example : progRejects (prog{
  fn dischargeLie (n : Nat, p : Id Nat Z (S n), b : Bool) -> Nat {
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
# §15 test suite — the pure surface authoring layer, and `le_trans`

The M11 wall was mis-indexed de Bruijn failing silently. This milestone's claim:
names + explicit motives collapse it without a unifier. The evidence is here —
`le_trans`, the lemma I abandoned as a raw term, authored in `prog{ }` and
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
  match (do let v ← readC 2000 tm; let t ← readC 2000 ty; hasType 2000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## Elaboration round-trip: surface `le_refl` = the hand-built kernel term -/

-- The surface `le_refl` (StdLemmas) elaborates to a `Term` convertible with the
-- M11 hand-built `Std.le_reflT`.
example : expectConv [] [] Dllbc.StdLemmas.le_refl Std.le_reflT = true := by native_decide

/-! ## `let` is ONE form, and the two ways it can capture (M29 α)

    `let` used to elaborate two ways — a `letIn` under ⇒, a de Bruijn β-redex
    under ⇝ — and merging them onto `letIn` moved a `let` into positions its
    de Bruijn spelling had made impossible. These four pin the merge: the first
    two that it means the same thing, the last two that neither capture the
    spelling would have permitted actually happens. Each of the last two was a
    MEASURED wrong answer before the fix (M29 step-0 probe 2 and its
    counterfactual), not a hypothesis. -/

-- (1) The merged `let` means what the β-redex it replaced meant.
example : expectConv [] [] prog{ let a = 2 ; add a a } prog{ (λ (a : Nat). add a a) 2 } = true := by
  native_decide
-- (2) …and a `let` chain still means its nesting.
example : expectConv [] [] prog{ let a = 2 ; let b = S a ; add a b } prog{ 5 } = true := by
  native_decide

-- (3) A `let` may SHADOW a pure binder, and the innermost one wins. A pure λ's
-- body is a `uterm`, so a `let` cannot sit directly under one; an `elim` arm's
-- body is a `ublk` and its binders push the de Bruijn context, so that is the
-- reachable route. `resolveName` consults that context FIRST, so without the
-- surface's mask this reads the ARM's `k` — measured as `Z`, not `7`.
example : expectConv [] []
    prog{ elim 1 return (λ (x : Nat). Nat) { Z => 0, S(k) ih => let k = 7 ; k } }
    prog{ 7 } = true := by native_decide

-- (4) A let-bound value MENTIONING a pure binder, read two binders deeper. ⇝
-- reads `let` by β and lifts the value from the depth it was bound at to the
-- depth it is used at; the Ω-binding reading this replaced did not, and returned
-- a value pointing at the inner arm's binders instead. `s = S k = 1`.
example : expectConv [] []
    prog{ elim 1 return (λ (x : Nat). Nat) {
            Z => 0,
            S(k) ih =>
              let s = S k ;
              elim 1 return (λ (y : Nat). Nat) { Z => 0, S(j) ih2 => s } } }
    prog{ 1 } = true := by native_decide

/-! ## The lemmas check at their stated types -/

example : chk Dllbc.StdLemmas.le_refl Dllbc.StdLemmas.le_refl_ty = true := by native_decide
-- THE ACCEPTANCE TEST — `le_trans` authored in the surface, checked.
example : chk Dllbc.StdLemmas.le_trans Dllbc.StdLemmas.le_trans_ty = true := by native_decide
example : chk Dllbc.StdLemmas.id_trans Dllbc.StdLemmas.id_trans_ty = true := by native_decide
example : chk Dllbc.StdLemmas.id_congr Dllbc.StdLemmas.id_congr_ty = true := by native_decide

/-! ## `le_trans` APPLIED in a checked function — closing the loop with §12

    A body that ⇒-lifts `le_trans Nat a b c p q` (the pure lift, §11) and returns
    it at the dependent type `Le a c` (instantiated at the actuals, §12). -/

-- `le_trans a b c p q` (Le is monomorphic at Nat — no type argument), cited by
-- name through the surface's identifier fallback.
def useTrans : Term := prog{
  fn useTrans (a : Nat, b : Nat, c : Nat, p : Le a b, q : Le b c) -> Le a c
        { StdLemmas.le_trans a b c p q };
  () }
example : progOk useTrans = true := by native_decide

/-! ## Negative tests -/

-- Wrong motive: `elim n return (λ m. Le Z m) { … }` gives a proof of `Le Z n`,
-- but the function claims `Le n n`. Elaboration SUCCEEDS (the term is
-- well-formed); the audit rejects it — the motive is written on the `return`
-- clause and thus visible, so the failure is comprehensible. The surfaced error
-- is: "audit: result (…) does not have return type (…)".
def LeFn : Term := Std.LeFnT
def badReflClosed : Term := prog{
  λ (n : Nat). elim n return (λ (m : Nat). LeFn Z m) { Z => unit, S (k) ih => ih } }
-- SUBJECT: a deliberately-lying function — the return type claims `Le n n` while
-- the body proves `Le Z n`. It was a hand-built `FnDef` record on the argument that
-- a surface form would obscure the lie; written as a `fn` the lie is the two lines
-- side by side, which is more explicit rather than less. The body is the pure term
-- above, spliced and applied — the mis-motive is what is under test, so it stays
-- exactly as written.
def badRefl : Term := prog{
  fn badRefl (n : Nat) -> Le n n { %badReflClosed n };
  () }
example : progRejects badRefl "does not have return type" = true := by native_decide

-- Unresolved name: `prog{ Le nope nope }` where `nope` is unbound is a Lean
-- elaboration error at macro time (the resolve-or-error discipline), not a
-- silent `pvar`. Demonstrated by `#guard_msgs` would require the exact message;
-- here we simply note it cannot be written — an unbound lowercase name in a
-- `prog{ }` block fails to compile, exactly as in `prog{ }`.

/-! ## The measure (§15's report card)

    `le_trans` in the surface: 14 lines (`StdLemmas.le_trans`), every binder named,
    every motive written once and visible on its `return` clause. The M11 raw-term
    attempt was ABANDONED at the wall: a three-level nested dependent induction
    over ~15 distinct de Bruijn binder contexts, each mis-index failing silently
    with only a `false` from `native_decide` and no locus. The surface term
    type-checked on the SECOND attempt (the first surfaced two real bugs in
    `hasType` — sym-application and eliminator over-application — not de Bruijn
    slips, because there are no indices to slip). Names + explicit motives
    collapsed the wall; no unifier, no motive inference, no case trees. -/

end Dllbc.Tests.S15Elab
end
-- └── end of what was `S15Elab.lean` ───────────────────────────────────────────────
