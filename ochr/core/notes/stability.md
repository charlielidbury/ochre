# Stability (Conjecture 2): statement, decomposition, and what is left

Branch `stability`, off main `4cc0beda`. The theory lane toward full consistency. Every model lane (`depfields-model`, `split-model`, `id-model`) ends on the paper's stability conjecture: refinement commutes with checking. This note states it against the checker, breaks it into one lemma per decision site, reports what happened to the two weakest sites, and reduces what is left to as few lemmas as I could.

## 1. The statement (`Ochr/Stability.lean`)

`Conjecture2 := DecisionsCommute ∧ RunsCorrespond`, proof `sorry`.

- **Refinement.** `α : List (Nat × Value)`, values for abstract values, applied as the checker applies [Split]'s refinement: `refine` substitutes into Ω's values, stored types, unknowns' types and the goal and re-normalises every sealed program it reaches; `substV`/`substT` do the same for values and terms. Abstract functions and holes are abstract values, so this covers all three kinds the paper names. `Respects α Ω` asks each value to check at a type convertible with its unknown's.
- **"The same decisions".** The big-step machine builds no derivation tree, and the two runs do not visit the same subterms (the generic run closes off what the instance runs, and checks every arm the instance takes one of). So the paper's "at every subterm both runs reach" is split into two precise halves:
  - `DecisionsCommute`: each decision function, on refined inputs, gives the refinement of its answer on the originals: the erasure pre-pass (item 1), `byTypeMatch` (1), `fnClass` and `declKind` (4), `closeOffMatch`'s block (2), `placeType` for an observed place up to conversion (5), and footprint containment (6).
  - `RunsCorrespond`: the instance run (`tα` at `Ωα`) does not fail where the generic run (`t` at `Ω`) succeeded, and when it finishes it agrees up to resolution with the generic result and final state refined by `α`. This is what puts related inputs in front of the decision functions at the subterms both runs reach; it gives item 3 (arms well typed on both or neither) and item 6's "the extra equations compute to ⊤".
- **Up to resolution (`AgreeUpToρ`).** End every borrow (`endAll`), which leaves no loan to rename; then rename the unknowns either run created (at or above `Ω.nextAbs`) injectively, itself a refinement by unknowns; then compare the values and every position's content.
- **Proved:** `byTypeMatch_arms` (site 11). `#print axioms stability`: propext, sorryAx, Classical.choice, Quot.sound.

## 2. Per-site decomposition (the 25 census sites)

Each site needs: *if the two runs present α-related inputs, the decision agrees*. Classification:
- **(a) by construction:** decided in `Decide.lean` from syntax, declarations and declared readings, none of which a refinement changes (it changes values and stored types, never a term's syntax or a binding's `decl`);
- **(p) follows from a principle:** a short argument from a named principle or one of the elementary lemmas in §3;
- **(o) open:** needs `RunsCorrespond` (N) or typing/machine agreement (M), §4.

| # | Decision | Class | Lemma it needs |
|---|---|---|---|
| 1 | Erasure pre-pass | a | Binding readings are now syntactic (D77), so `declOf` in live scope reads only syntax and `decl`s. Embedded values (`.val v` in sealed programs) are read by their head: L-sort, L-class. |
| 2 | After-the-fact classification | a | A check, not a decision: any disagreement with 1 is a rejection, never a different result. |
| 3 | A function type's class | a | Read off the codomain term (D54). A stuck block's function reads its codomain value's sort: L-sort. |
| 4 | Proof parameters | a | Parameter type terms. |
| 5 | Is a call a statement | p | The callee value's Π-type class: L-class (D54: Π-types of different class do not convert, so a refined value's type keeps its class). |
| 6 | Statement argument in place | a | **Was (b).** Now the argument's declared type (D77, `stmtArgInPlace`). |
| 7 | A binding's class | a | **Was (b), the weakest.** Now its declared type's syntax, type functions read through their bodies (D77). |
| 8 | [Close]'s row | a | The declared codomain term; for a stuck block, `& ` is never produced by computation (D48(2)), so the codomain value is `&T` exactly when written so. |
| 9 | η at `Unit` | p | D59: every value at `Unit` is `()`, so normalising one path's value and not the other's changes no `Eq`. Refinement only makes a type more concrete. |
| 10 | Proof irrelevance (`isPropV`) | p | L-sort (D55: sorts are syntactic, evaluation and refinement preserve them). |
| 11 | Match on a proof | a | Proved: `byTypeMatch_arms`. |
| 12 | Arm a match on a proof takes | p | L-head on the scrutinee's stored type: refinement refines its parameters, never its head (note 25). |
| 13 | Stuck-block captures and modes | p | Syntax (occurrences); copy-ness (as 16); ⊥ per arm (type-directed); borrow-ness of a binding (now a declared-type fact, as 6); a split capture's constructor (L-ctor); (X)/(S) of `split-model`. |
| 14 | Footprint and owners | o | Containment: roots are syntax, extra owners come from a hole's fill, which refinement can only lose (`id-model` (A)/(F)). That the extra equations compute to ⊤ is N. |
| 15 | [Rec] decrease | p | L-ctor: refinement only adds constructors, so a strict subterm stays one. |
| 16 | Copy or move on a read | p | Copy-ness is monotone: an abstract or neutral type is never a copy type and refinement only makes types more concrete, so the generic run moves at least what the instance moves; the difference is a ⊥ the generic run then rejects on (fail-safe). |
| 17 | `Eq` computes | o | Injective/disjoint: L-ctor. Reflexive: conversion is closed under refinement, which for [Conv-fun] (observation of the generic call) is N. Stuck stays stuck or computes later. |
| 18 | `J` computes | o | As 17. |
| 19 | Conversion checks | o | As 17: structural conversion commutes with refinement by determinism of `substV`; [Conv-fun] needs N. |
| 20 | [Split], [Split-gen], records | o | (X)/(S)/(G)/(B) of `split-model` for the worlds; the re-normalisation of generalised sealed programs is N. |
| 21 | Re-observing a stuck side by typing | o | M: a typed run and an untyped run of the same term agree when neither is stuck. |
| 22 | Is a hole a proof | p | L-sort. Holes are outside the consistency statement anyway. |
| 23 | K2/K3 model-code checks | p | Flags are syntax; a content's type head: L-head. |
| 24 | [Open], [Repack], whole-again points | p | (W)/(P) and [Return] of D76 (`depfields-model`, unmerged): every producer of a dependent neutral checks it whole through `closeBlock`/`bodyReturns`, and the generic run is the stricter path. |
| 25 | `&A` well formed | p | L-sort (D55, D66). |

**Counts:** by construction 8 (1, 2, 3, 4, 6, 7, 8, 11); from a principle 11 (5, 9, 10, 12, 13, 15, 16, 22, 23, 24, 25); open 6 (14, 17, 18, 19, 20, 21). Before D77, 6 and 7 were the two (b) sites and site 1 was not by construction either, because binding readings came from `refineDecl`'s value reading.

## 3. The elementary lemmas

All four are about `substV` and the readers of value heads; each follows by unfolding `substV` case by case, and none needs the evaluator.
- **L-ctor.** Substitution keeps a constructor value's constructor: `substV σ r (C(ā; v̄)) = C(ā'; v̄')`. (Only `.sealed` re-normalises; constructor values are rebuilt componentwise.)
- **L-head.** Substitution keeps a type value's head (`tInd n`, `tRef`, `tPi`, `tNat`, `tUnit`, `sort`). **Not** `tEq`: `mkEqM` may compute an equation to `True`, `False` or a conjunction. Its sort is kept, which is L-sort.
- **L-sort.** Substitution keeps a type value's sort (`sortOf`): heads are kept (L-head), an equation stays a proposition, and an unknown's sort is its type's, which `Respects` makes convertible with the refined value's.
- **L-class.** Substitution keeps a Π-type value's class: the codomain term is unchanged and its captured values keep their declared readings (`valueDecl` reads heads: L-head), so `fnClass` reads the same term in the same scope (D54).

## 4. The two weak sites (D77)

- **`refineDecl` (site 7).** The census's weakest argument. Probing it found a real path disagreement: at an instance where a parameter of type `RefPred(0)` holds a *sealed* function value (`PickP(n)` stuck on `n`), `refineDecl` read `other` (there is no case for sealed values, and the call's declared codomain `RefPred(0)` is not syntactically a Π-type), so the instance ran `p(&c)` where the generic call, reading the evaluated type, erased it. The pre-pass assertion caught the disagreement, so the definition was rejected with an INTERNAL error: fail-safe, but true statements (`InstPow`, `DirectPow`) were rejected. A second probe (`MixT`: a family whose arms are Π-types of different classes) showed the generic call reading `other` and the instance reading the arm's class, again caught by the assertion.
  - **Fix (D77):** read a type function's call off its body (a Π-term through `let`s and match arms; a self-call neutral), a constant type off its value, and make `refineDecl` read nothing else. Arms that disagree with a Π-type among them are a `conflict` and the binding is rejected. Every earlier verdict unchanged; the true statements are accepted; the open lemma for site 7 is gone.
  - **Edge cases found by probing the new reading, fixed before landing:** a recursive type function's self-call through its `by` binder read as a proposition (made `RecP` a conflict); a body naming its Π-type with a `let` read as data (made `RunLet` an INTERNAL rejection). Both now read correctly and are regressions.
- **`stmtArgIf` (site 6).** Leaned on A.5 condition 5 (Assumption 11, T1, unproved). No disagreement found; made syntactic anyway (`stmtArgInPlace`, declared type a borrow type), every verdict unchanged, and the lemma it needed is gone.

**Findings:** no closed proof of `False`. One path disagreement (site 7), fail-safe through the pre-pass assertion, now removed by construction; it had made true statements unprovable.

## 5. What is left: the minimal remaining lemma

Everything open reduces to two lemmas.

- **N, symbolic naturality (`RunsCorrespond`).** Evaluation commutes with refinement up to resolution. It splits by what the generic run does at an unknown it meets:
  - **(P) Parametricity in uninspected unknowns.** A run that completes without inspecting `σ` (it would have been stuck, or split, or closed off) computes, with `α(σ)` in `σ`'s place, the same steps on the substituted values. Its value-dependent decisions read only heads and declared readings, which §3's lemmas keep. This is the paper's "hole parametricity" (A.8, Assumption 10 (N3)) generalised from holes to every unknown, and it is the one genuinely global lemma: an induction over the evaluator's 116-function cycle, uniform in each case.
  - **(C) Closing off is correct.** Where the generic run closes a call off, the sealed programs it leaves, re-normalised under `α`, compute what the instance's direct run of the call computes: its result and the final contents of its borrowed places. This is property 3 of the paper's Figure 9; it was mechanised as `close_res/fin/cur/back` for the earlier rule set in the deleted `meta-lean`.
  - **(Sp) Splits commute.** Where the generic run splits `σ`, `α(σ)`'s constructor picks the arm the instance takes, and the arm's state refined by the fields' values is the instance's. Given (X)/(S) of `split-model` this is bookkeeping.
- **M, typing refines the machine.** A typed and an untyped run of the same term agree when neither is stuck (needed for site 21, and implicitly wherever typing re-runs a callee body with the machine). This is the paper's design claim that typing is the machine run with types.

So Conjecture 2 is not a separate problem from naturality: with the decisions made syntactic (8 sites by construction) or local (11 sites from short principles), **stability reduces to symbolic naturality (N, which is P plus C plus Sp) and typed/untyped agreement (M)**. Of these, (P) is the heart; (C) has been mechanised before for an older rule set; (Sp) is bookkeeping given `split-model`; (M) is a design claim with no known counterexample.

## 6. Open questions

- **(P) in Lean.** The checker is total (D74-era), so (P) is stateable and provable in principle against `Machine.lean`: a mutual induction over the fuel-indexed cycle, with a "does not inspect σ" predicate on runs. It is large but uniform, and it is the step that would turn this decomposition into a proof.
- **The incompleteness D77 keeps.** A type function returning a parameter used as a type (`F(A : Type₁) : Type₁ := A`) reads `other`. Making it exact needs the type arguments read through the body, i.e. a syntactic substitution of the call's argument terms; no program in the suite needs it.
- **Footprint ⊤.** Site 14's second half (extra equations compute to ⊤) is N for the observation's runs; `id-model` P4 is one instance where it holds.
