# 26. The two-paths census re-audited under the meaning criterion

Written on 2026-11-06 by a fork of the coordinating session, as the census audit that `docs/23` (the route to consistency by meaning preservation) calls for. It is read-only with respect to code and audits `ochr/core/notes/two-paths-census.md` as it stands on main at `da8b260b` (with D80 and D81; D82, every binding typed by declaration, is on branch `typed-bodies` and not merged). The census file itself is not edited here.

## The criterion

`docs/18` asked of each decision: is it identical on the generic run and on every instance run? `docs/23`'s route has only one run, the symbolic one, and asks a different question of each step that makes a decision. For every assignment ρ of set-theoretic values to the unknowns (consistent with the path conditions), does each outcome the step could take keep the meaning ⟦Ω⟧_ρ of the state and the remaining program?

- **same**: every outcome keeps the meaning, possibly given *membership* (a value's meaning lies in its type's meaning, the lemma (b) that `docs/23` proves together with meaning preservation).
- **aligned**: the outcomes differ in meaning (running a term in place or on a private copy that is thrown away), so the model must make the same choice. It can, because the decision reads only syntax and declared types (census class (a)); the model's denotation is defined by the same reading.
- **⊑**: one outcome is less informative than the other in the information order, and every later step that *computes* on the state must then be ⊑-monotone.
- **check**: the step only accepts or rejects. Only its accepting direction must be sound, so a rejection is free. Checks fall into three groups:
  - **membership**: needed by lemma (b);
  - **invariant**: needed for ⟦Ω⟧ to be defined at all;
  - **runtime**: needed only for the affine and runtime-safety reading, and not for consistency in a non-affine model.
- **neither**: an outcome can change the meaning in a way that is neither aligned nor ⊑-related. These are the real work items.

## Assumptions

- **The model is non-affine** (`docs/23`). Values are sets; a move makes a place inaccessible to the program but does not change what it means.
- **⊥**, which `docs/23` leaves open:
  - **(O) old value**: ⊥ means the value the place held before it was moved;
  - **(N) no information**: ⊥ ⊑ v for every v.

  Where the two readings differ, both are given. Under (O), ⊥ needs no ⊑. Under (N), every computing step must be monotone over ⊥. This audit finds that (O) fails at block captures (row 13b), so ⊥ must mean (N). This resolves the choice `docs/23` left to its test 2.
- **The well-formedness invariant** of `docs/23` holds at every step: no aliasing live borrows, loans only where closing off allows, and every closure and global has passed [Rec].

## The table

Census sites are numbered as in the census; rows marked "abl." are the items found by `ochr/core/notes/machine-ablation.md` that no census site covers; "vT" rows are the remaining `valType?` call sites.

| # | Decision (where) | Its outcomes | Verdict | Rests on |
|---|---|---|---|---|
| 1 | Erasure pre-pass: is a term erased, is it a proof (`preFlags`) | run in place, or on a discarded private copy with value `⋆` | **aligned**; `⋆` is **same** | the model reads erasure from the same syntax (D28, D35, D55); membership for `⋆` (⟦v⟧ ∈ ⟦P⟧ ⊆ {•}) |
| 2 | The after-the-fact classification (an internal assertion) | agree, or internal error | **check** (free) | nothing |
| 3 | A function type's class (`fnClass`, from the codomain *term*) | the calls are statements (arguments on private copies) or not | **aligned** | D54: a value has the class of its declared Π-type |
| 4 | Which parameters are proofs (`paramFlags`) | bound to `⋆` or to an unknown | **same** | membership |
| 5 | Is a call a statement (`stmtCallee`) | as 3 | **aligned** when the head's reading is written (`cls?`); otherwise read off the value's Π-type (`funType?`, a sealed value's typing run): see "neither", item 3 | D54, and convPi's class check (ablation #23, untested) |
| 6 | A statement argument runs in place (`stmtArgInPlace`, D77) | in place, or on a discarded copy | **aligned** (class a since D77; the census row still says b→c) | the model reads the same declared borrow type |
| 7 | A binding's class (`refineDecl`, D77) | as 3 | **aligned** (class a since D77; the census row is stale) | the known non-free decision; D77 makes it syntactic |
| 8 | [Close]'s row: borrow, `Unit` or data | a borrow with a hole, `()`, or a sealed program | **aligned** for borrow vs data; **same** for `()` | D48 (`&` is never computed, so a block's `B` is `&T` exactly when written so); membership for `()` |
| 9 | η at `Unit` for a call's result (D80) | `()` or the sealed program | **same** | membership (⟦f⟧(args) ∈ ⟦Unit⟧ = {•}); a computed-type rule would be equally fine here |
| 10 | A value of a proposition is `⋆` (`isPropV`, by the type's head) | `⋆` or the value | **same** | membership (the head's declared sort is `Prop`) |
| 11 | A match is on a proof (`byTypeMatch`) | match by type, fields bound to fresh unknowns | **same** (proofs mean •; fresh unknowns are universally quantified, which only strengthens what is checked) | subsingleton elimination as in Carneiro |
| 12 | Which arm a match on a proof takes (`scrutType`, `largeElim`) | the arm the stored type's head names | **same**; a neutral type is a type error (**check**) | membership |
| 13a | Stuck block: copy-ness of a capture (D80) | copy or move | (O) **same**; (N) **⊑** | non-affine model |
| 13b | Stuck block: a capture some arm moves is taken by move (K1(d), K1(e)) | the place left ⊥, or kept | (O) **neither**: when another arm *writes* the place, ⊥ read as the old value contradicts the arm that writes; (N) **⊑** | ⊥ must mean (N); every computing step must be monotone over ⊥ |
| 13c | Stuck block: does a binding hold a borrow (`b.val.isBorrow`) | capture as a borrow or as data | **same** | the invariant (a value is a borrow exactly when its type is a borrow type) |
| 13d | Stuck block: split a partly moved capture by its content's constructor (K1(g)) | split into fields, or take it whole by move | **⊑** (taking it whole loses the siblings) | (N); the constructor head is ρ-invariant |
| 14 | Observation footprint and owners (`Obs.footprint`, `owners`) | which places `Id` compares | **same** if the footprint covers every place either side may write under every ρ (extra owners give equations that are true) | a coverage lemma: `Pick`, inert loans, the extra owners at a call site (injectivity, T4) |
| 15 | [Rec]: is the recursive argument a strict subterm (`recCheck`) | accept or reject | **check** (invariant) | the check must hold under every ρ (refinement only adds constructors); the model needs it to define `fix` by well-founded recursion |
| 16 | Copy or move on a read, closure capture, the Fn rule (D80) | copy or move | (O) **same**; (N) **⊑** | non-affine model |
| 17 | `Eq` computes (`mkEqM`) | `True`, a conjunction, `False`, or stuck | **same** (computing) | conversion soundness; injectivity and disjointness of constructors in sets; monotone over ⊥ because `Eq` with ⊥ stays stuck (ablation #17) |
| 18 | `J` computes | as 17 | **same** | conversion soundness |
| 19 | Conversion (`conv`, `convPi`, `convFn`) | convertible or not | **check** (free; one-sided) | convertible implies equal meaning: [Conv-fun] by meaning preservation of the generic call under every extension of ρ; comparing sealed programs by text is sound |
| 20 | [Split], [Split-gen], generalisation records, `canonNeutral`, `renormAll` | run an arm, split, generalise, re-run | **same** | path conditions on ρ: arms cover every ρ; a record means ρ(σ) = ⟦t⟧_ρ; same text gives same meaning; leaving an arm drops ρ-dependent facts (D37, D79) |
| 21 | Re-observing a stuck `Id` side with typing (`observeTyping`) | machine value, or typing's split-and-close | **same** (both runs keep meaning) | none beyond 20; D82 deletes the step |
| 22 | Is a hole a proof | — | not applicable: a program with holes is not a closed proof | — |
| 23 | K2/K3 model-code checks | accept or reject | **check** (free) | — |
| 24 | [Open], [Repack], whole-again points (D64, D72, D73) | accept or reject | **check** (membership) | [Repack] restores membership of raw field tuples; see vT `lentUnknown` |
| 25 | `&A` only for `A : Type₀` (`isBorrowable`) | accept or reject | **check** (invariant: `&` means forward and backward functions on data only) | — |
| 26 | [Close]'s fill of a lent place (D80) | `()` or a sealed fill | **same** | membership (⟦c⟧ ∈ ⟦Unit⟧) |
| abl.7 | Record η: an unknown of a one-constructor type is refined when a field is moved out (`movedPlace`) | refine, or not | **same** | every element of a one-constructor type's meaning is that constructor applied; the refinement belongs to its world (D79) |
| abl.8 | K1(a): a closure in an arm takes the places it mentions by move | ⊥ or kept | (O) **neither**, as 13b; (N) **⊑** | as 13b |
| abl.9 | K1(b): a borrow variable used whole is taken by move | as abl.8 | (N) **⊑** | as 13b |
| abl.14, 15, 32 | A returned borrow must be whole; borrows passed to a closing-off or erased call must be whole; M2b | accept or reject | **check** (runtime) | under (N) a hole is "no information" (⊑) and a read of it is an error; not needed for consistency in a non-affine model |
| abl.17 | `Eq` with ⊥ stays stuck | stuck or computed | **needed** under (N), as monotonicity (two sides each ⊥ on different arms can mean different values); under (O) it guards only the affine reading (`MovedBothSides` is true in a non-affine model) | (N) |
| abl.18 | Injectivity blocked while index fields differ | stuck or a conjunction | **same** (the conjunction means the same as sets) | needed for membership: the conjunction's second equation would be ill-typed |
| abl.19 | A `Z`/`S` match needs a `Nat` scrutinee | accept or reject | **check** (membership) | — |
| abl.20 | A neutral head closes off at once, except as [Seal]'s head | — | free (termination of the checker; a run that does not finish gives no derivation) | — |
| abl.21 | D66 for terms: `&p` needs `Type₀` | accept or reject | **check** (invariant) | — |
| abl.25–28, 33 | Lent proof fields, repack on a whole read, D73, D64 [Open], each arm's end checked as a return (D76) | accept or reject | **check** (membership) | see vT `lentUnknown` |
| abl.29, 30 | `symm` of `False`, `trans` with `True` | — | **same** (proofs mean •; only typing changes) | membership |
| abl.31 | D63 in blocks: a closure may not capture what the block borrows | accept or reject | **check** (invariant: closures capture no borrows, so a closure means a set function) | needs its copy-type witness test (ablation) |
| abl.34 | [Rec] L1: a function occurs in its body only as a call's head | accept or reject | **check** (invariant: `fix` means a function only through well-founded recursion) | **untested**: no example exercises it |
| vT | `placeType?` fallback, `valType`, `indValType?`, `depFieldType`, `convVal`, `idType`'s owner type, an embedded loan in `evalCore`, `funType?` of a sealed value | some type of a value | typing only (lemma b) | one lemma, *`valType?` is sound*: ⟦v⟧_ρ ∈ ⟦valType? v⟧_ρ for every ρ. D82 removes the binding uses |
| vT | `packedErr` | an error message | free | — |
| vT | `lentUnknown` (D73), `lentProofAssign` | the lent part checked as an unknown of the *content's own type*; when that type cannot be read, the loan stays in the value and [Repack] rejects it | **check** (membership); first marked **neither**, corrected after a probe (item 2) | `valType?` soundness; reading the borrow's *declared* type, as the rule says, would change no verdict and remove that dependence |

## Neither: the real work items

1. **⊥ must mean "no information".** Block captures by move (13b, K1(a), K1(b), K1(d), K1(e)) leave ⊥ in a place that another arm may *write*. Read as the old value, ⊥ contradicts that arm. Read as "no information", these steps are ⊑ and need only that every computing step is monotone over ⊥. The checker already has that: `Eq` with ⊥ stays stuck (ablation #17), a read of ⊥ is an error, and an owner holding ⊥ gives a stuck equation (`idType`). This settles the choice `docs/23` left to its test 2.
2. **The D73 lent-part check reads the content's type, not the borrow's: a proof simplification, not a gap** (corrected on 2026-11-06 after a probe (`a2e90a29`, local branch `probe-lent`)). `lentUnknown` replaces a live loan's content by a fresh unknown of `valType?`'s type for the current content. This audit first read its fallback, for when that type cannot be read, as checking only the current content, and so as a candidate soundness gap. The probe found the opposite: in that case the loan stays in the value, and [Repack]'s leaf check reads the same unreadable type and reports "is not of type", so the fallback rejects. It is also effectively unreachable: an index field is first-order data, whose content's type is always readable (constructor values record their parameters, unknowns have stored types, sealed programs their head's codomain). Four attacks and a closed `: False` attempt were all rejected by [Repack]. Reading the borrow's declared type, as the rule says, would change no verdict; it would only remove the check's dependence on `valType?` being sound.
3. **The class of a call head that is an embedded value** (census 5, when no reading is written). It is read off the value's Π-type (`funType?`; a sealed function value's type comes from its typing run). This is the one non-free kind of decision, a binding's class (a private copy discards writes). It agrees with the declared position only through D54's rule that Π-types of different class are not convertible, enforced in `convPi`, and no test exercises that half (ablation #23). Write the witness test (`Π(x : Nat). Type₀` against `Π(x : Nat). T(x)` with `T(x) := Type₀`), or carry the reading with the value as D80 does for captures.

## What the "same" rows rest on: five lemmas, not one per site

- **Membership (b)**, proved together with meaning preservation. Rows 1, 4, 8–12, 26 and abl.29–30 need it.
- ***`valType?` is sound*** (vT rows): one lemma about one function.
- **Footprint coverage** (14): the owners include every place either side may write, under every ρ.
- **Conversion soundness** (17–19), with [Conv-fun] by meaning preservation of the generic call.
- **The well-formedness invariant**, with its checks (15, 25, abl.21, abl.31, abl.34). Two of them (abl.31's copy-type case, abl.34) have no test.

## Guards that leave the consistency argument

In a non-affine model with ⊥ read as (N), these are needed for runtime safety, `docs/18`'s clause (i), but not for consistency:
- the whole-borrow guards (abl.14, 15, 32);
- K1(d) and K1(e)'s "the generic path moves at least what an arm moves", as far as moves go: keeping a value an arm moved agrees with a non-affine model.

They stay in the checker for the runtime claim; the consistency proof does not need lemmas about them.

## Summary

Of 26 census sites and the 34 ablated items plus the remaining `valType?` sites:
- **Free:** every pure check, plus termination; the consistency proof needs only their accepting direction, or nothing.
- **Same:** the η family, erasure's `⋆`, `Eq`/`J`, [Split] and records, and copy-or-move under (O).
- **Aligned:** erasure, class, a statement argument's place, [Close]'s row. These are class (a) since D77 and D80, so the model reads them the same way.
- **⊑ under (N):** the block captures and moves.
- **Neither:** ⊥ read as the old value (resolved by choosing (N)); the D73 lent-part check's content-type reading (first flagged as a candidate gap; a probe found its fallback rejects and is effectively unreachable, so reading the borrow's declared type is a proof simplification, not a fix); and the class of an embedded call head (needs D54's class check witnessed).
