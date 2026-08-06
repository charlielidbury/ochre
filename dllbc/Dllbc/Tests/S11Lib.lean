import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.PureMacro

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

/-! ## The fording vocabulary, authored in `pure{ }`

    `NatCode : Nat → Nat → Type` by double `natRec` — `(Z,Z) ↦ ⊤`, `(S,S) ↦` the
    code of the predecessors, mixed `↦ ⊥` — and the motive that turns a
    `p : Id Nat Z b` into an inhabitant of `NatCode Z b`, which for `b = S n`
    computes to `⊥`. §10 derives the same kit as `Val`s; this is the `Term` side,
    because a `fn` body is made of `Term`s.

    **These were raw `Term`s until M28, on a rationale that expired.** The file
    used to say "the surface macro has no syntax for `j`/`app`/`const`, and the
    j-spine's `.pvar` motives cannot be reproduced by a named binder". Both halves
    are false since §15's `pure{ }` and M27's juxtaposition application:
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
def zCase : Term := pure{
  λ (m : Nat). natRec (λ (x : Nat). Type) Unit (λ (x : Nat). λ (r : Type). Bot) m }

/-- `NatCode`'s `S` row: `Z ↦ ⊥`, `S m2 ↦ code of the predecessors` (the
    outer recursor's `ih`, applied). -/
def sCase : Term := pure{
  λ (n : Nat). λ (f : Π (x : Nat) → Type). λ (m : Nat).
    natRec (λ (x : Nat). Type) Bot (λ (m2 : Nat). λ (r : Type). f m2) m }

/-- `NatCode : Nat → Nat → Type`, by `natRec` at a Π-valued motive. -/
def natCode : Term := pure{
  λ (a : Nat). natRec (λ (x : Nat). Π (y : Nat) → Type) zCase sCase a }

/-- The no-confusion motive at `Z`: `λ m. λ (q : Id Nat Z m). NatCode Z m`. With
    `j`'s `d := unit : NatCode Z Z`, `j Nat Z nncMotive unit (S n) p` has type
    `NatCode Z (S n)`, which computes to `Bot`. -/
def nncMotive : Term := pure{ λ (m : Nat). λ (q : Id Nat Z m). natCode Z m }

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
