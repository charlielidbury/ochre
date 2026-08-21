import Dllbc.ElabCheck
import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Tests.Direct
import Dllbc.Tests.ArraySort
import Dllbc.Tests.Programs

/-!
# Regression checks for retired-mechanism claims and binder-mode conventions

Two batteries. The first checks that programs and lemmas whose declarations used
to carry a `back` field (a declared backward specification) still hold their
claims after that field was removed — either as an equivalent `ensures`-style
postcondition, as a program that now typechecks outright, or as a lie twin that is
still correctly rejected. The second measures capitalisation of comptime binders
(the convention that a capital binder name is comptime, lowercase is runtime)
across the flagship program and the standard library.
-/

section

open Dllbc

namespace Dllbc.Tests.S27Dispose

open Dllbc.Tests
open Dllbc.StdLemmas (Ub Lb Len)

/-! ## Declarations whose claim survives the `back` field's removal

    Each check below confirms one declaration's claim survives without the field:
    either the function still typechecks as a program, or an equivalent
    `ensures`-style postcondition holds, or a lie twin is still correctly rejected. -/

/-! ### Rewritten as fuel-threaded programs -/

-- A cursor with no decreasing argument but the payload.
example : progOk S26Fuel.zeroAllF = true := by native_decide
-- Negative control: `walk` is accepted, `walkArr` is refused for taking `[a]` on
-- a borrow — the two differ only in that hint.
example : progOk S24Arrays.walk = true := by native_decide
-- The flagship quicksort cohort, one fuel-threaded chain.
example : progOk S23Direct.flagship = true := by native_decide
-- Already fuel-threaded, so needed no rewrite.
example : progOk S25ArrSort.arrChain = true := by native_decide

/-! ### Lie twins

    The honest programs above must be paired with lie twins that are still
    correctly rejected, or acceptance is only half a differential. `partitionLoses`,
    `qsStaleBound` and the other four spec lies live beside `partition` and
    `quicksort` in `S23Direct` and are checked there with `progRejects`. -/

/-! ### `recSame`, `recWrongIdx`, `recGrow` — negative controls for a deleted guard

    A self-call at the same argument, at a different one, and at a larger one.
    Their subject was a snapshot-subterm check that no longer exists, but each is
    still rejected for an independent reason: the recursor's `ih` is bound at the
    predecessor, so a self-call anywhere else has nothing to become, and the
    let-chain cannot reference downward, so the un-elaborated form resolves to no
    function at all. -/

def guardTwins : List Term := [S23Direct.recSame, S23Direct.recWrongIdx, S23Direct.recGrow]

example : guardTwins.all (fun t => progRejects t "not the predecessor") = true := by native_decide
-- Not vacuous: the honest sibling elaborates, so the three refusals are about the
-- argument and not about the shape.
example : progOk S23Direct.recGood = true := by native_decide

/-! ### `recDeep` — a macro limit, not a calculus limit

    `recDeep` recurses two constructors down: an arm's `ih` is bound at the
    *immediate* predecessor of the motive it is given, so reaching two steps back
    needs a motive that already carries both values. The macro derives only the
    motive that matches the function signature, so it cannot produce this one and
    declines the declaration — but a hand-written recursor with a stronger motive
    typechecks, which is what the rest of this section checks:

    1. **`recDeep`'s own motive is CONSTANT** (`Π (n : Nat) → Id Nat Z Z` — nothing
       depends on `n`), so `ih : P a` already IS `P b` for every `b`. The direct
       recursor expresses it verbatim, and that is what the program below checks.
    2. **The general two-down shape** — where `P` really does depend on `n` — has
       a described route and NOT a mechanized one, and the distinction is left
       standing rather than blurred: a course-of-values motive `Q m := P m × P (S m)`,
       whose base arm inhabits `P 0` and `P 1` directly and whose step arm at `a`
       with `ih : Q a` returns `Pair(snd ih, fst ih)` — `P (S a)` is `ih`'s second
       component and the two-down call `f a` is its first — then one projection at
       the end. One `natRec`, one stronger motive. Nothing below checks this; it is
       filed as the route, and only construction 1 is a build fact.

    So the limit is real but it is a **macro** limit, not a calculus one: `fnElab`
    derives the motive mechanically from the signature (§7: "the motive is derived
    from the signature — so the macro needs no inference"), and neither of these
    motives is that one. That is the same shape as §9's own survey warning — "the
    eliminator must accept a motive stronger than the signature, plus a weakening
    step" — arriving a second time, from the other end of the language, before §9
    is built. Filed as a macro capability rather than as an expressiveness wall. -/

def deepSealT : Term := prog defer_check { Π (n : Nat) → Id Nat Z Z }
def deepMotT : Term := prog defer_check { λ (n : Nat). Id Nat Z Z }

/-- `recDeep`, hand-written as a sealed recursor. The step arm keeps the corpus's
    own inner `match a`, reaching `ih` from inside it — the move the macro refuses
    to make on the author's behalf.

    The base arm must bind a unit binder rather than an empty telescope: an arm
    that is not a λ is not a suspension, so it would run when the spine is formed
    rather than when ι selects it. `deepBaseArmBare` below is the rejected twin
    that omits the binder. -/
def deepBaseArm : Term :=
  Term.lamTel [(unitBinder, .cmpT (.const "Unit"))] (.ctorApp "Refl" [])
def deepBaseArmBare : Term := Term.lamTel [] (.ctorApp "Refl" [])
def deepStepArm : Term :=
  -- `ih`'s domain is the motive at the predecessor; `deepMotT` is constant, so
  -- `ih : P a` already is `P b` for every `b`.
  Term.lamTel [(⟨0, "a"⟩, .const "Nat"), (⟨1, "ih"⟩, prog defer_check { Id Nat Z Z })]
    (.matchE ⟨0, "a"⟩ none
      [ .mk "Z" [] (.ctorApp "Refl" [])
      , .mk "S" [⟨2, "b"⟩] (.var ⟨1, "ih"⟩) ])
def deepRec : Term :=
  .app (.app (.app (.const "natRec") deepMotT) deepBaseArm) deepStepArm
def recDeepProg : Term := .letIn ⟨900, "F"⟩ (.seal 0 deepRec deepSealT) .unit

example : progOk recDeepProg = true := by native_decide

/-- The same program with the base arm left bare is refused: the two differ in
    one binder, which is what makes the accept above about the arm's shape
    rather than about the program. -/
def recDeepBare : Term :=
  .letIn ⟨900, "F"⟩ (.seal 0
    (.app (.app (.app (.const "natRec") deepMotT) deepBaseArmBare) deepStepArm) deepSealT) .unit
example : progRejects recDeepBare "is a bare term, not a λ" = true := by native_decide

/-- The seal really audits the recursor: ascribed at a Π claiming
    `Id Nat Z (S Z)` instead, the arms cannot inhabit it and this is rejected. -/
def deepSealLie : Term := prog defer_check { Π (n : Nat) → Id Nat Z (S Z) }
def recDeepLie : Term :=
  .letIn ⟨900, "F"⟩ (.seal 0 (.app (.app (.app (.const "natRec")
    (prog defer_check { λ (n : Nat). Id Nat Z (S Z) })) deepBaseArm) deepStepArm) deepSealLie) .unit
example : progOk recDeepLie = false := by native_decide

/-- The macro itself still declines the declaration: the form is expressible, but
    `fnElab` does not derive this motive. -/
example : progRejects S23Direct.recDeep "not the predecessor" = true := by native_decide

/-! ## Declarations that actually declared a `back` field

    What happened to each one's claim once the field was removed. -/

/-! ### Round-trip parser tests, retired

    Several tests asserted only that a written `back = …` parsed into the expected
    `FnDef` field. With the field gone there is no claim left to re-express. -/

/-! ### `setAt`/`swapAt` — the composition claim, restated as `ensures`

    Backward specs used to compose along a call chain, so a caller of `swapS`
    recovered the exact swapped list. `S23Direct.setAt`/`swapAt` restate the same
    two model functions (`Set`, `SwapL`) as postconditions instead
    (`Id (List Nat) (*v) (Set i x (old *v))`, similarly for `SwapL`): the caller
    now learns a propositional equation it can rewrite along, which is strictly
    more than the value the backward spec used to hand it. -/

-- One program declaring both facts, since the point is that a caller learns the
-- equation from either.
example : progOk S23Direct.setSwap = true := by native_decide

-- The lie twins for these two facts (index moved; update was a no-op) are checked
-- in `S23Direct`'s `setSwapUnder` skeleton, not restated here.

/-! ### The Architecture A model-conformance stratum

    `pivotPlace`, `partScan`, `partition`, `quicksort` and their siblings were an
    imperative program checked as an implementation of a pure model, with
    `back = PartitionL …`/`SortRangeL …` naming the model. Stripping the field
    does not delete these functions: the ensures-era stratum in the same file
    (`swapSE`, `partitionRangeE`, `quicksortE`, `quicksortSorted`, …) reaches them
    through its call graph, so what retires is each one's back-specific assertion,
    not the function.

    `twoRec`'s `back = *v` is the identity and incidental to what it tests —
    sequential reborrow, the quicksort recursion shape, checking only because
    `&mut` on a place holding a parked loan demand-ends the prior call's group
    before reborrowing. Dropping the field leaves that subject intact: -/

example : progOk S19Partition.twoRec = true := by native_decide

/-! ### Outside the test pool

    `Dllbc/Bench.lean` and `Dllbc/BenchQS.lean` hold verbatim copies of
    back-declaring test definitions, compiled as timing harnesses (`lean_exe
    bench`/`benchqs`) rather than run under `native_decide`. They retire with
    `checkFn` for the same reason as everything above; nothing here asserts
    anything about them. -/

end Dllbc.Tests.S27Dispose
end

section
namespace Dllbc.Tests.S32Binders
open Dllbc

/-! # Comptime-binder capitalisation, measured across the corpus

    Convention: a capital binder name is comptime, a lowercase one is runtime.
    Today the same fact is also readable from `Var.bindsSlot` — whether the
    binder has an Ω store slot id at all (`noSlot` is the sentinel) — which is
    the check the ids exist for. The functions below count, for a given term,
    how many binders follow or violate the naming convention, how many disagree
    with the slot-based reading, and several related conventions (whether a Σ
    component or match-arm binder is marked comptime). Each is run against the
    flagship program and a few hand-written library terms to confirm the corpus
    is fully migrated. -/

/-- Comptime binders (no slot) whose name is neither capitalised nor reserved —
    binders that violate the naming convention. -/
partial def lowerComptime : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !isUpperInit x.name && !isReservedName x.name then 1 else 0)
      + lowerComptime d + lowerComptime b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerComptime d + lowerComptime b
  | .app f a | .seq f a | .seal _ f a => lowerComptime f + lowerComptime a
  | .letIn _ r t => lowerComptime r + lowerComptime t
  | .assign p e r => lowerComptime p + lowerComptime e + lowerComptime r
  | .idT a b c => lowerComptime a + lowerComptime b + lowerComptime c
  | .ctorApp _ as | .call _ as => (as.map lowerComptime).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => lowerComptime br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerComptime t
  | _ => 0

/-- Binders that DO bind a slot — these already carry their mode in their case,
    for comparison against `lowerComptime`'s count. -/
partial def slotBinders : Term → Nat
  | .lam x d b => (if x.bindsSlot then 1 else 0) + slotBinders d + slotBinders b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => slotBinders d + slotBinders b
  | .app f a | .seq f a | .seal _ f a => slotBinders f + slotBinders a
  | .letIn _ r t => slotBinders r + slotBinders t
  | .assign p e r => slotBinders p + slotBinders e + slotBinders r
  | .idT a b c => slotBinders a + slotBinders b + slotBinders c
  | .ctorApp _ as | .call _ as => (as.map slotBinders).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => slotBinders br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => slotBinders t
  | _ => 0

/-- `lowerComptime`'s twin: a comptime binder is two halves written together —
    the capital name and the `⇝` marking its domain — and `Term.clam`/`Term.cpi`
    exist so a hand-written term cannot spell one without the other.
    `lowerComptime` counts binders with the domain half but not the name half;
    this counts the reverse. The two are not symmetric in the tree: the
    hand-written kernel library is 0 because `clam` always writes both halves,
    while every surface `elim` arm binder shows up here because `elabUElim`
    builds arm binders with a bare `Term.lam` and never calls `binderDom`. Same
    scope restriction as `lowerComptime` (`!bindsSlot`). -/
partial def unmarkedCaps : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && isUpperInit x.name && !d.domComptime then 1 else 0)
      + unmarkedCaps d + unmarkedCaps b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => unmarkedCaps d + unmarkedCaps b
  | .app f a | .seq f a | .seal _ f a => unmarkedCaps f + unmarkedCaps a
  | .letIn _ r t => unmarkedCaps r + unmarkedCaps t
  | .assign p e r => unmarkedCaps p + unmarkedCaps e + unmarkedCaps r
  | .idT a b c => unmarkedCaps a + unmarkedCaps b + unmarkedCaps c
  | .ctorApp _ as | .call _ as => (as.map unmarkedCaps).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => unmarkedCaps br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => unmarkedCaps t
  | _ => 0

/-- The direction that must be zero: a runtime binder with nowhere to put its
    argument. Lowercase says the argument arrives by ⇒ — moved or loan-seeded
    into the store — so a lowercase binder that binds no Ω slot is a binder whose
    argument has no destination. -/
partial def keyDisagree : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !(isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + keyDisagree d + keyDisagree b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => keyDisagree d + keyDisagree b
  | .app f a | .seq f a | .seal _ f a => keyDisagree f + keyDisagree a
  | .letIn _ r t => keyDisagree r + keyDisagree t
  | .assign p e r => keyDisagree p + keyDisagree e + keyDisagree r
  | .idT a b c => keyDisagree a + keyDisagree b + keyDisagree c
  | .ctorApp _ as | .call _ as => (as.map keyDisagree).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => keyDisagree br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => keyDisagree t
  | _ => 0

/-- The other direction, which is not zero: a capital binder that binds an Ω
    slot. Legitimate, because `seedTelescopeV` slots every parameter regardless
    of case, and capital says how the argument is read, not where it lands. -/
partial def comptimeSlotParams : Term → Nat
  | .lam x d b =>
    (if x.bindsSlot && (isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + comptimeSlotParams d + comptimeSlotParams b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => comptimeSlotParams d + comptimeSlotParams b
  | .app f a | .seq f a | .seal _ f a => comptimeSlotParams f + comptimeSlotParams a
  | .letIn _ r t => comptimeSlotParams r + comptimeSlotParams t
  | .assign p e r => comptimeSlotParams p + comptimeSlotParams e + comptimeSlotParams r
  | .idT a b c => comptimeSlotParams a + comptimeSlotParams b + comptimeSlotParams c
  | .ctorApp _ as | .call _ as => (as.map comptimeSlotParams).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => comptimeSlotParams br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => comptimeSlotParams t
  | _ => 0

/-- λ nodes this term classifies as imperative. The number the telescope rule
    protects: if the slot test were swapped for a case test, every `fn` whose
    parameters are all capital would leave this count and lose its audit. -/
partial def impLams : Term → Nat
  | .lam x d b =>
    (if Term.lamImperative (.lam x d b) then 1 else 0) + impLams d + impLams b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => impLams d + impLams b
  | .app f a | .seq f a | .seal _ f a => impLams f + impLams a
  | .letIn _ r t => impLams r + impLams t
  | .assign p e r => impLams p + impLams e + impLams r
  | .idT a b c => impLams a + impLams b + impLams c
  | .ctorApp _ as | .call _ as => (as.map impLams).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => impLams br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => impLams t
  | _ => 0

-- The in-place quicksort, the largest program in the corpus, with its specs and
-- library lemmas elaborated in: every comptime binder spells its mode, and the
-- 22 runtime binders are untouched by the naming convention.
example : lowerComptime Dllbc.Tests.S23Direct.flagship = 0 := by native_decide
example : slotBinders Dllbc.Tests.S23Direct.flagship = 22 := by native_decide

-- Two kernel library terms, hand-written rather than elaborated: `len` and the
-- `Le` predicate the carve rule's premises are stated against.
example : lowerComptime Std.lenFnT = 0 := by native_decide
example : lowerComptime Pure.kLeFn = 0 := by native_decide

/-! **`unmarkedCaps` on the flagship and the hand-written library, both 0.**

    A recursor arm built by `elabUElim` used a bare `Term.lam` for its binders
    and never called `binderDom`, so `elim n return … { Z => …, S (A') R => … }`
    produced `λ A'. λ R. …` with plain domains where `Term.clam "A'"`/`"R"` would
    write `⇝Nat`. Every capital binder the surface elaborator wrote was affected;
    every capital binder a human wrote using `clam` was already correct. Routing
    `elabUElim`'s arm binders (and the Σ-elimination type family) through
    `binderDom` fixes it, with zero verdict changes anywhere in the corpus —
    conversion is mode-blind by construction (`Term.convEq`), so the marker
    was inert to every judgment that runs. It is not inert to `Term.alphaEq`,
    the key binder abstraction generalizes with, which is why the asymmetry
    was worth removing rather than documenting. -/
example : unmarkedCaps Dllbc.Tests.S23Direct.flagship = 0 := by native_decide
example : unmarkedCaps Dllbc.Tests.S24Arrays.sort2 = 0 := by native_decide
example : unmarkedCaps Std.lenFnT = 0 := by native_decide
example : unmarkedCaps Pure.kLeFn = 0 := by native_decide
example : unmarkedCaps Pure.kAddFn = 0 := by native_decide

/-! ### Why `bindsSlot`, not the case test, decides slotting

    Swapping `Var.bindsSlot` for a capitalisation-based case test would cost
    exactly 4 binders in the flagship — all a capital telescope parameter
    binding an Ω slot, because `seedTelescopeV` slots every parameter, comptime
    or not. The swap should not happen: case and `bindsSlot` answer different
    questions. **Case** is the read mode — ⇝ or ⇒, erased or moved. **`bindsSlot`**
    is the location — whether the argument lands in Ω; the telescope rule says a
    telescope binder binds a slot regardless of case.

    So the two checks below are not the same claim measured twice: `keyDisagree`
    (lowercase, no slot) is a real invariant that must be zero — a runtime
    binder whose argument has nowhere to land — while `comptimeSlotParams`
    (capital, slotted) is the telescope rule's own population, which is content,
    not debt. -/
example : keyDisagree Dllbc.Tests.S23Direct.flagship = 0 := by native_decide
example : keyDisagree Std.lenFnT = 0 := by native_decide
example : keyDisagree Pure.kLeFn = 0 := by native_decide

-- The telescope rule's population: each `Hf`/`Hfuel` is a proof parameter of a
-- recursive `fn` (`Partition`, `AppendBack`, `Quicksort`) carried capital because
-- the length/fuel facts it relates are themselves capital; each `Ih` is the
-- recursor's self-view of the function at the predecessor, which is a Π and so
-- must be comptime under §2.5 (no runtime binding may hold a function).
example : comptimeSlotParams Dllbc.Tests.S23Direct.flagship = 9 := by native_decide

/-! **The count the rule protects.** A case test at `Term.lamImperative` would
    take every all-capital-parameter `fn` out of this number. It lands on
    `slotBinders`' own 22, and that is arithmetic rather than
    coincidence: a telescope is nested λs, so a λ node is imperative exactly when
    a slot binder sits at or below it in its own chain, and each slot binder is
    the innermost such node for exactly one prefix. -/
example : impLams Dllbc.Tests.S23Direct.flagship = 22 := by native_decide


/-! ## The Σ half: comptime components and the arm binders that consume them

    `lowerComptime` above counts λ binders and is blind to Σ's — `.sigmaT` is on
    the line that recurses without inspecting the binder. These functions cover
    that position, on both sides of it: which Σ components are marked comptime,
    and which match-arm binders consuming them are correspondingly capitalised. -/

/-- Σ binders that declare their component comptime (`⇝` on the domain) — the
    producer side. -/
partial def cmpSigmas : Term → Nat
  | .sigmaT _ d b => (if Term.domComptime d then 1 else 0) + cmpSigmas d + cmpSigmas b
  | .lam _ d b | .pi _ d b | .borrowT _ d b => cmpSigmas d + cmpSigmas b
  | .app f a | .seq f a | .seal _ f a => cmpSigmas f + cmpSigmas a
  | .letIn _ r t => cmpSigmas r + cmpSigmas t
  | .assign p e r => cmpSigmas p + cmpSigmas e + cmpSigmas r
  | .idT a b c => cmpSigmas a + cmpSigmas b + cmpSigmas c
  | .ctorApp _ as | .call _ as => (as.map cmpSigmas).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => cmpSigmas br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => cmpSigmas t
  | _ => 0

/-- Match-arm binders spelled capital — the consumer side, and the population
    `checkArmModes` refuses to leave lowercase. -/
partial def capArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => isUpperInit x.name)).length + capArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => capArms d + capArms b
  | .app f a | .seq f a | .seal _ f a => capArms f + capArms a
  | .letIn _ r t => capArms r + capArms t
  | .assign p e r => capArms p + capArms e + capArms r
  | .idT a b c => capArms a + capArms b + capArms c
  | .ctorApp _ as | .call _ as => (as.map capArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => capArms t
  | _ => 0

/-- The ones that stay lowercase, the other half of the claim: the check is
    bidirectional, so this number is asserted by the same run. -/
partial def lowerArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => !isUpperInit x.name)).length + lowerArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerArms d + lowerArms b
  | .app f a | .seq f a | .seal _ f a => lowerArms f + lowerArms a
  | .letIn _ r t => lowerArms r + lowerArms t
  | .assign p e r => lowerArms p + lowerArms e + lowerArms r
  | .idT a b c => lowerArms a + lowerArms b + lowerArms c
  | .ctorApp _ as | .call _ as => (as.map lowerArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerArms t
  | _ => 0

example : cmpSigmas Dllbc.Tests.S23Direct.flagship = 91 := by native_decide
example : capArms Dllbc.Tests.S23Direct.flagship = 14 := by native_decide
example : lowerArms Dllbc.Tests.S23Direct.flagship = 22 := by native_decide

/-! **The three numbers, read together.**

      * **91 comptime Σ components.** Most are the library's — `Ub`, `Lb` and
        `Sorted` unfold to Σ chains with capital binders — plus five written by
        hand in the spec (`Hub`, `Hlb`, `Hl1`, `Hl2`, `Hs`).
      * **14 capital arm binders**, consuming those five spec components:
        `Partition`'s four in each of its two consumer chains, plus
        `Quicksort`'s `Hs1`/`Hs2`, plus the tails (`Hcnt` twice, `Hpc`,
        `Hc1`/`Hc2`) whose `sctx` entry carries `⇝` and so cannot stay lowercase.
      * **22 lowercase arm binders** — the data components (`hi`, `x`, `rest`,
        `lo`) that the same rule positively requires to stay lowercase. The
        check runs in both directions: without it, all 36 binders could be
        capital. -/

end Dllbc.Tests.S32Binders
end
