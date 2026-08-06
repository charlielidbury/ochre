import Dllbc.Program
import Dllbc.ProgMacro

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
  .lam natV (natRecV (.lam natV .type) (.const "Unit") (.lam natV (.lam .type (.const "Bot"))) (.pvar 0))
def sCase : Val :=
  .lam natV (.lam (.pi natV .type) (.lam natV
    (natRecV (.lam natV .type) (.const "Bot") (.lam natV (.lam .type (.app (.pvar 3) (.pvar 1)))) (.pvar 0))))
def natCodeV : Val := .lam natV (natRecV (.lam natV (.pi natV .type)) zCase sCase (.pvar 0))
def natCode (a b : Val) : Val := .app (.app natCodeV a) b

/-- `pred : Nat → Nat` (`pred Z = Z`, `pred (S n) = n`). -/
def predV : Val := .lam natV (natRecV (.lam natV natV) sZ (.lam natV (.lam natV (.pvar 1))) (.pvar 0))

/-! ## §10 kernel: the ι-rules (`j` and `k` fire on `Refl`)

    `j A a P d b p` and `k A a P d p` reduce to `d` when the proof is `Refl`;
    on a symbolic proof they are stuck neutral values. (The motive is irrelevant
    to reduction — ι fires on the proof.) -/

-- j Nat Z P 42 Z Refl ↦ 42
example : (Val.nfV 1000 (jV natV sZ (.lam natV (.lam natV natV)) (vnat 42) sZ refl) == vnat 42) = true := by
  native_decide

-- k Nat Z P 7 Refl ↦ 7
example : (Val.nfV 1000 (kV natV sZ (.lam natV natV) (vnat 7) refl) == vnat 7) = true := by native_decide

-- On a *symbolic* proof (sym 0), `j` does not fire — it is a stuck value, not 42.
example : (Val.nfV 1000 (jV natV sZ (.lam natV (.lam natV natV)) (vnat 42) sZ (.sym 0)) == vnat 42) = false := by
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
    what the machine happens to hold: `seal(Refl, Id Nat m 2)` is a certificate
    that typechecks **only if** `m`'s snapshot is concretely `2`. Unrefined, `m` is
    a σ and `Refl` does not inhabit `Id Nat σ 2`.

    That is the per-demand-site doctrine applied to the kernel's own tests, and it
    is a strictly better assertion than the one it replaces: it says the
    refinement is USABLE, where the Ω observation only said it was recorded. -/

def learnDemand : Term := prog{
  fn learnDemand (n : Nat, p : Id Nat n 2) -> Unit {
    match p { Refl => { let m = n; let c = seal(Refl, Id Nat m 2); () } } };
  () }
example : progOk learnDemand = true := by native_decide

-- THE TWIN, and it is what makes the certificate a demand rather than a
-- decoration: the same `let m = n` and the same seal with the match REMOVED. `m`
-- is unrefined, so `Refl` has nothing to inhabit.
def learnDemandNo : Term := prog{
  fn learnDemandNo (n : Nat, p : Id Nat n 2) -> Unit {
    let m = n; let c = seal(Refl, Id Nat m 2); () };
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
    match pb { Refl => { let m = n; let c = seal(Refl, Id Nat m 2); () } } };
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
def nncMotive : Val := .lam natV (.lam (.idT natV sZ (.pvar 0)) (.app (.app natCodeV sZ) (.pvar 1)))
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
  .lam natV (.lam (.idT natV (sS a) (.pvar 0)) (.idT natV a (.app predV (.pvar 1))))
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
def uipMotive (a : Val) : Val := .lam (idAA a) (.idT (idAA a) (.pvar 0) refl)
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
