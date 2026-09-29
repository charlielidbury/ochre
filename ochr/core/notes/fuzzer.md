# fuzzer: a differential naturality tester for the Ochr checker

## v2 (rules v2.1 with D52, branch ochr-fuzz-v2, 2026-09-29)

**Verdict.** The fuzzer found one closed proof of `False` on the v2.1 checker: F-v2-1, a checker bug. It is fixed on ochr-core by 3ff0e1e2.

On the fixed checker, 10⁶ cases on the default rules (ochr-core 658cc108) produced no refinement that disagreed with the direct path on a value. There were no `nat`, `false`, `truth`, `frame` or `adequacy` value disagreements, and one `conv` finding, which is an error on one side and falls in R1. Every other finding is one of three kinds:
- **fail-safe**: one path gets a type error where the other succeeds, so the checker rejects rather than accepts. Five classes, R1 to R5, 21,642 cases in total.
- **scoping imprecision**: E, 142 cases, which cannot change a value.
- **vacuous**: some hypothesis is `False` at that refinement.

**Most important finding.** F-v2-1. On 0127f58b and 96d788a1, typing a sealed program (`sealedType`) emptied the [Rec] accumulators, after which recursive calls were no longer checked. `def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }` was accepted, and so was `Boom : False := Lie(0, ⟨refl, refl⟩)`. It was common: 351 cases in 10⁵ on 96d788a1.

**What must change.** Nothing further for soundness. The fail-safe classes are incompleteness in the checker's untyped machine and in how stuck blocks capture and are typed; §v2.5 gives one change for each.

**Validation.** With one rule switched off at a time, the fuzzer produced findings absent under the default rules for 17 of the ledger's 22 soundness rows (§v2.3). Three of the five it misses need constructs it never generates: inductive declarations (D36), `&` of a non-data type (D48(2)), and a scrutinee whose type is a computed family (scrutTyped). The other two are D40 and P3-without-D41.

**Also found by validation:**
- **P2 is a soundness row, not a completeness row.** With the private copy off and D41 on, an erased call that writes through a borrow argument gives a closed proof of `False` (`Scratch/P2Alone.lean`).
- **The D53 prototype (off by default) breaks naturality in two ways**, one of them in the unsound direction.

**Confidence.**
- F-v2-1 is certain: the unmodified checker accepted it, and the fix flips it (`Scratch/RecWipe.lean`).
- "No value disagreement in 10⁶ cases" holds only within the generator's coverage (§v2.6).

### v2.1 How to run

```
cd ochr/core/lean
lake build fuzz
lake exe fuzz --seed 1 --count 100000 --jobs 16                    # 10⁵ cases, ~50 s on 16 cores
lake exe fuzz --seed 1 --count 20000 --jobs 12 --diff --switch D32   # attribute to one rule
lake exe fuzz --seed 1 --show 1424                                  # one case, verbosely
```
- Case `i` of seed `S` is a pure function of `(S, i)`.
- `--switch X` takes the name of a `Config` switch or the ledger row name of a rule (`D17`…`D52`, `P1`, `P2`, `P3`, `L1`–`L3`, `C5`, `C8`, `G1`), or `D53on`, which turns on the D53 prototype (moving reads). A switch named `+X` would apply to both sides of a `--diff`. There is none now: `+F1`, which applied the F-v2-1 fix before it landed, was dropped at the merge of 3ff0e1e2.
- `--diff` reports only the findings a case shows with the switches on and not without them.
- `--shrink K` shrinks and prints K findings per kind and worker.
- `--jobs J` runs crash-isolated worker processes.
- A printed counterexample is an `ochr` block. Pasted into a Lean file after `import Ochr.Fuzz.Replay`, `#eval IO.println (replay Cex)` re-runs the oracles on it.

**Checker hooks.** None: the fuzzer uses the checker as it is, and `lake exe tests` reports 467/467 on this branch. The v1.x emulations `+D37`, `+D35` and `+N12` are gone, because D37, D35/D40 and D41/D42 are now rules. `+F1` (`Config.keepRecCands`, off by default) existed until the fix landed.

### v2.2 What changed from v1

**Harness.**
- The generic environment is built as `checkFix` builds it: declared proof flags (`paramFlags`) and proof parameters bound to `⋆`.
- A case's program is `Prelude` (`Pair`, `False`, `True`, `And`) followed by its own declarations.
- An observation is packed as one value for refinement and comparison. `observe` returns a tuple of the machine, not a `Pair`.
- Values are compared modulo `And`'s unit laws. D50 makes those laws conversion, so a refined `False ∧ ⊤` and a direct `False` agree.

**Oracles.** The truth oracle counts an instance as false only when:
- its `Id` computes to `False` (not merely something other than `⊤`), and
- every proof parameter's type is `⊤` there.

A finding at a refinement where some proof parameter's type is `False` is marked `vacuous`. The truth oracle also tries two new proof shapes:
- Knot's L1 shape: the function passed to an inline λ that calls it.
- KnotL's L3 shape: the recursive call inside a λ, on the λ's own argument.

**Generator (v2.x constructs).**
- Proof parameters: `⊤`, `⊤ ∧ ⊤`, `False`, `Or(⊤, ⊤)`, `ExN`, and hypotheses about earlier data parameters (`Eq Nat n k`, `Le(n, m)`, `PropIf(*x)`, and conjunctions of these with `⊤`).
- Matches on proofs, which go by the proof's type (D45): one arm for `True`/`And`, arms into proofs only for `Or` and for `ExN` (whose data field is a fresh abstract value, D49), and no arms for `False`.
- Zero-arm matches at any type, annotated.
- Proof constructors (`⟨h, k⟩`, `Inl[⊤, ⊤](refl)`, `Wit(n, refl)`).
- λs that take `⊤ ∧ ⊤` or return proofs.
- Closures capturing reads of borrowed places.
- Pairs at `Nat × Nat` (D52): `(a, b)`, `Mk(a, b)`, `match q { Mk(a, b) => … }`, the places `q.1`/`q.2` of local pairs, `&(Nat × Nat)` parameters, and `Id` at `Nat × Nat`, which exercises injectivity.
- New templates: `AndSwap`, `Absurd`, `WriteIf`, `OrProof`, `ExProof`, `EffL`, `Clo`, `CapN`, `PropIf`, and `Le` via `False`.

### v2.3 Validation: each ledger row switched off

**Method.**
- `--diff --switch X` against the default rules, on ochr-core 658cc108 merged (branch commit 0ce60481).
- Pass 1 ran every row: seed 1, 20,000 cases, about 17–40 s per row on 12 workers.
- Pass 2 re-ran the rows pass 1 did not reach: seed 2, 100,000 cases.
- A row is *reached* when the fuzzer reports a non-vacuous finding the default rules do not.
- "First" is the index of the first case showing it.
- The row kind (soundness, completeness, …) is the one the counterfactual ledger (`lake exe tests`) gives the row.

**Soundness, model, false-lemma and policy rows:**

| switch off (ledger kind) | reached? | first | what it finds (shrunk shape) |
|---|---|---|---|
| D17 [Rec] entry values (soundness) | yes | 1 | `truth` 3,418: `Lie(…) by x := Lie(…)` with no decrease is accepted for a false statement |
| D31 no `f` without `by` (soundness) | yes | 1 | `truth` 3,418: the same without `by` |
| L1 self only as a call head (soundness) | yes | 10 | `truth` 2,099 in 10⁵: Knot's shape, `(λ(f : Π(yy : Nat). T[yy]) (z : Nat) : T[z] => f(z))(Lie, x)` |
| L3 [Rec] in nested functions (soundness) | yes | 10 | `truth` 6,069 in 10⁵: KnotL's shape, `let g = (λ(yy : Nat) : T[yy] => Lie(yy)); g(x)` |
| D18 owners are sets (soundness) | yes, rarely | 25,251 (pass 2) | `nat` 1 in 10⁵: `let a4 = match n0 { Z => &n0, S p6 => let a7 = &*x1; &n0 }; Id Unit (*a4 := 0) ()`, the hole in two owners |
| D19 [Access] ends loans inside (soundness) | yes | 115 | [Drop]-while-borrowed verdicts; `nat` 3 |
| L2 no ⊥ argument (soundness) | yes | 152 | verdicts: `G1(&n0, n0)`, where the second argument ends the first one's borrow and the callee reads `⊥` |
| C5 blocks move moved borrows (soundness) | yes | 3,927 | `Id Unit () (*x0 := match *x0 { Z => let a1 = x0; 0, S p2 => 0 })`: use after move on the direct path |
| D29 matching ends loans in a neutral (soundness) | yes | 964 | `nat` 28, `escape` 31: a returned borrow's hole left in the observation (`loan_2`) |
| D30 closures by observation (soundness) | yes | 18 | `conv` 856, `false` 41: `Id Unit (match *x0 { Mk(p0, _) => *x0 := Mk(0, 0) }) (match *x0 { Mk(p1, p2) => *x0 := *x0 })` is ⊤ generically and `False` at `(0, 1)` |
| D32 pattern writes (soundness) | yes | 20 | `nat` 530, `false` 44: `Id Unit (match *x0 { Mk(p4, p5) => WriteIf(&p5, refl) }) ()` |
| D35 class of a local function (soundness) | yes, rarely | 10,524 (pass 2) | `nat` 1 in 10⁵: `let a4 = MkF(n0); a4(&n0); (n0, n0)` (BoomL/X1) |
| D35/D40 block erased iff each arm (soundness) | yes | 108 | `nat` 142, `truth` 4: `Id Prop (match n2 { Z => n0 := 0; ⊤, S p5 => ⊤ }) ⊤` (BoomB) |
| D40 not by the computed type (soundness) | no | – | only vacuous findings in 2·10⁴ (needs `V(Z)`-typed arms of a data-class call, which the generator rarely forms) |
| D37 global generalisation records (soundness) | yes | 116 | `escape` 540 (2,850 in 10⁵ in pass 2): a generalised σ of a returned borrow's content escapes the private copy (X3's root). Example: `let a0 = match *x0 { Z => x0, S p1 => &p1 }; match *a0 { … }` |
| D38 borrow results observed by a write (soundness) | yes | 253 | `conv` 61: `PickX`/`PickY`-style closures found convertible (X4) |
| D45 + D42 (soundness) | yes | 313 | `nat` 6: a proof is `I` on one path and `⋆` on the other (`Id ⊤ (match q1 { Mk(p1, p2) => let a4 : ⊤ = refl; a4 }) refl`); D41 verdicts; `adequacy` 2 |
| P2 without D41 (soundness) | yes | 232 | `false` 150, `nat` 388, `truth` 3 (N1's shape) |
| P3 without D41 (soundness) | fail-safe only | 934 | R1/R2 errors only; BoomH's value-classified variable is not generated |
| D28 erasure by declaration (false lemma) | yes, caught | 642 | D41 verdicts only: the misclassified term writes, and D41 rejects it on the path that erases it (the fail-safe working) |
| D35r [Close]'s row by declaration (policy) | no | – | needs a `U(n)`-typed call whose row differs by path |
| P1 without D41 (policy) | yes | 313 | `nat` 8 |
| D41 confinement (policy) | fail-safe only | 934 | R1/R2 errors only: with the other classification rules on, the generator produces no misclassified inline term for D41 to catch |
| D44 borrow result needs a borrow parameter (model) | no | – | abstract `Π(n : Nat). &Nat` is never generated |
| D45 subsingleton elimination (model) | yes | 11,407 | `adequacy` 3: `match h1 { Wit(p2, p3) => p2 := 0; refl }`, the untyped machine reads the field of `⋆` |
| D48(1) only data borrowed (model) | no | – | `&` of a sort or proposition is never generated |
| D48(2) `&` only at the top (soundness) | no | – | same |
| D36 positivity (soundness) | no | – | inductive declarations are not generated |
| scrutTyped (soundness) | no | – | a scrutinee whose type is a computed family is not generated |

**Completeness rows.** A switched-off completeness rule rejects more, so the fuzzer can see it only as a disagreement between the two paths.
- **Reached:**
  - P2 alone: `nat` 3. Also a closed proof of `False`; see below.
  - D27 (proof parameters `⋆`): `nat` 21, where a proof parameter is `σ` on one path and `⋆` on the other.
  - G1: `escape` 539 (2,850 in 10⁵).
  - D35s: D41 verdicts.
  - P1 alone: D41 verdicts.
  - D39: `normalisation depth exceeded`, 1 case (X5's loop).
  - D42: D41 verdicts, `nat` 5.
  - D47: R1/R2 only.
  - D45 (match on a proof by its type) and D49(3) (a proof's data field is a fresh σ): `nat` 1 in 10⁵ each (pass 2), the same case, which matches a pair after calling an abstract function.
  - D52 (injectivity): R1/R2 only (pass 2).
- **Not reached:** C8, P3 alone, capTypes, D48(3), D50 on, confineBodies.

**P2 is a soundness row, not a completeness row.** The ledger lists P2 (erased terms run on a private copy) as completeness under D41. But D41 lets an erased term pass an outer place to an erased call, and without the private copy that call's writes persist on the direct path, while the closed-off erased block skips them. With P2 alone off, the checker accepts a closed proof of `False` (`Scratch/P2Alone.lean`, 4/4 as expected on the default rules):
```
def F5 (x : &Nat) : Prop := *x := 5; ⊤
def Lie (x : &Nat) : Id Nat (let a = match *x { Z => refl, S p => F5(&*x); refl }; *x) *x := refl
def Boom : False ∧ False := let c = 1; Lie(&c)          -- accepted with eraseOnCopy := false
def Boom2 : False := let b = Boom; match b { Intro(l, r) => l }   -- accepted with eraseOnCopy := false
```

**D53on** (the D53 prototype, `Config.movingReads`, switched on). `nat` 1,361 and about 490 verdicts in 2·10⁴ cases, first at case 10. In 10⁵ cases (pass 2): `nat` 7,041, verdicts about 2,300, and `conv` 6. There are three shapes:
- **(a) A closed-off block moves the places it only reads.** `Id L n0 (match n0 { Z => Nil, S _ => Nil })` at `n0 := 0`: the owner is `⊥` on the block path and `0` on the direct path.
- **(b) [Close] turns a move out through a borrow into a copy.** `Id Nat 0 (match *x0 { Z => *x0, S p3 => … })` at `x0 := 0`: the direct path errors (a borrow ends with `⊥` inside), while the result's and the owner's sealed programs each re-run the call and both see `0`.

- **(c) Conversion misses a move through a borrow.** The checker accepts `ConvEq : Eq (Π(z0 : &Nat) (z1 : &Nat). &Nat) ConvF ConvG := refl` for `ConvF := λ(y9 : &Nat) (y10 : &Nat) : &Nat => *y10; y10` and `ConvG := λ(y9 : &Nat) (y10 : &Nat) : &Nat => y10`. On ground inputs `ConvF` returns a borrow of `⊥` (the read moved `*y10` out) and `ConvG` a borrow of `0` (seed 2, case 6313).

(b) and (c) are the unsound direction: the generic path accepts what an instance rejects, or identifies two functions that an instance tells apart. Reported to the lead for D53.

### v2.4 At-scale runs (the default rules, 2026-09-29)

| run | checker | seeds | cases | time (16 workers) | real findings |
|---|---|---|---|---|---|
| main | ochr-core 658cc108 (recCands fixed; branch commit 0ce60481), default rules | 1–10 | 1,000,000 | 491 s | none |
| same, before the fix | 96d788a1 with `+F1` (the fix as an opt-in hook) | 1–10 | 1,000,000 | 536 s | none; every count equal to the main run's |
| unpatched | 96d788a1, default rules | 11–12 | 100,000 | 56 s | 351 `truth`, all F-v2-1 (each disappears with `+F1`) |

"None" means no `nat`, `false`, `truth`, `frame` or `adequacy` value disagreement: only the fail-safe, imprecision and vacuous classes below.

In the main run:
- **Statuses.** 971,562 cases were checked. In 23,699 the generic statement errs on all three components (lhs, rhs, `Id`); in 4,739 the generator made a surface error (a borrow with nothing to borrow).
- **No crashes.** No worker process died on any case.
- **Counting.** Findings are counted per case and kind. A case can show several kinds, and `--shrink 1` prints one shrunk example per kind and worker.

| class | kind: reason (cases in 10⁶) | vacuous too |
|---|---|---|
| R1 untyped `Id` owner holding a loan | `renorm: cannot infer the type of the value` 16,551; `verdict: …` 21; `adequacy: …` 20; `conv: error` 1 | 2,885 |
| R2 block captures a nested λ's write | `renorm: a closure or Π-type captures the borrow` 4,662; `verdict: …` 33 | 816 |
| R3 conversion runs a block's function at a generic call | `verdict: no such place … its path does not exist` 330 | 64 |
| R4 call of a sealed function in untyped code | `renorm/verdict: the type of the sealed function … is not known here` 23 | 3 |
| R5 arm types formed under different refinements | `verdict: the arms of a non-tail match have different types` 1 | 0 |
| E arm-local abstract value in a block's inferred type | `escape` 142 | 8 |
| V hypothesis `False` at the refinement | `nat: vacuous` 681; `verdict: vacuous [D41] …` 255; `verdict: vacuous [Match] …` 35; `renorm: vacuous [D41] …` 3 | all |

### v2.5 Findings on the default rules

Every program below is in `lean/Scratch/` and checks as annotated (`lake env lean Scratch/X.lean`).

**F-v2-1: closed proof of `False`.** This is a checker bug, fixed by 3ff0e1e2. The program is `Scratch/RecWipe.lean`: accepted on 0127f58b and 96d788a1, rejected since the fix.
```
def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S a' => match b { Z => False, S b' => Le(a', b') } }
def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }
def Boom : False := Lie(0, ⟨refl, refl⟩)                            -- accepted before 3ff0e1e2
reject def Lie2 (n : Nat) (h : ⊤ ∧ ⊤) : False by n := match h { Intro(a, b) => Lie2(n, h) }    -- rejected by [Rec]
reject def Lie3 (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := Lie3(n, h)                        -- rejected by [Rec]
```
How [Rec] stopped checking, on those commits:
1. `sealedType` (Machine.lean) typed a sealed program on a copy with `recStack := [], recCands := []`.
2. When the copy was discarded, `restoreKeep` kept `cur.recCands.drop (cur.recCands.length - saved.recCands.length)`. With the copy emptied, that is `[].drop 0 = []`, while `recStack` was restored.
3. `recCheck` zipped the two lists, so from then on no recursive call of the function being checked was checked.

`sealedType` runs whenever `valType` meets a sealed program. The fuzzer reached it two ways:
- `fieldTypes` of `And` at the parameter `⌈Le(σ, 1)⌉`, when a match takes the hypothesis apart (seed 1, case 1424).
- A λ capturing a place that holds a backward function, whose type D51 records (seed 1, case 1369): `let a3 = TailM(&n0); let a4 = (λ(y5 : &Nat) : U(n0) => V(n0)); …` with `Lie(n0) by n0 := Lie(n0)`.

The fix (3ff0e1e2): [Rec] frames carry their own candidates, and restores merge them by identity. Before it landed, the fuzzer carried the same fix as an opt-in hook, `+F1`. With the hook, all 351 `truth` findings of seeds 11–12 disappear, and 10⁶ cases give exactly the counts of the fixed checker.

**R1: untyped `Id` owner holding a loan.** Fail-safe. `idType` types each footprint owner from its stored type, or else from its current value. In the untyped machine (a sealed program's re-normalisation, a callee body, `callObs`), the owner is a `let c = …` cell of [Close]'s `L`, which has no stored type, and it is lent out at that moment, so `valType(loan_ℓ)` fails. Example: `Id Prop (match *x0 { Z => Id Unit () (*x0 := 0), S _ => ⊤ }) ⊤` is accepted, but its proof by `match *x0 { Z => refl, S _ => refl }` is rejected (`Scratch/V2Classes.lean`, `R1s`). Rules-level fix: [Close]'s `L` binds `cᵢ : Tᵢ` (the parameter's content type), or an owner's type is read through the loan to its borrow's content.

**R2: a stuck block captures a nested λ's write.** Fail-safe. A block's capture analysis (`closeOffMatch`, RULES §3 "Stuck blocks") counts `n0 := 0` inside a λ in one arm as a write by the block, so the block takes `n0` by `&`. That write is the λ's write to its own captured copy (closures capture by value), so it should count as a read. Re-normalising at `n0 := S σ` then makes the λ capture a borrow, which is an error. Example: `Id Nat (match n0 { Z => n0, S p2 => let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0 }) n0`, whose split proof is rejected (`R2s`). RULES should say that occurrences inside a nested function are captures (reads) of the block.

**R3: conversion observes a closed-off block's function at a generic call.** Fail-safe. A block formed inside an arm reads sub-places that exist only under that arm's refinement: a pattern variable of an enclosing match, such as `(*q0).fst` or `x0.1`. D30's conversion compares two such blocks' functions by running them at a fresh generic argument, where the sub-place does not exist. `convFn` lets that error escape instead of answering "not convertible", as `convPi` does. Examples:
- `Id B2 (match *x0 { Z => T, S p1 => match p1 { … } }) (match *x0 { Z => T, S p12 => match p12 { … } })` at `x0 := S σ`.
- The pair version, `R3`/`R3s` in `Scratch/V2Classes.lean`.

**R4: call of a sealed function in untyped code.** Fail-safe. A block whose arms return λs closes off to a sealed function `⌈f(σ)⌉`. Calling it where only the untyped machine runs (re-normalisation) needs its Π-type for [Close]'s row, which is not recorded, so the call errors with "the type of the sealed function … is not known here". Example: `Id Unit (let a2 = match *x0 { Z => λ(y4 : &Nat) : Unit => (), S p5 => λ(y6 : &Nat) : Unit => () }; a2(x1)) ()` at `x1 := 0` (`R4s`).

**R5: arm types formed under different refinements.** Fail-safe, 1 case in 10⁶. Two arms return λs whose codomain `U(κ)` captures a place holding a sealed program. The arms' refinements (`σ := 0` versus `S σ'`) made that program differ, so D48(3)'s comparison under binders finds `U(⌈…0…⌉) ≠ U(⌈…S σ9…⌉)`, although both are `Prop`. The "annotate it" error then fires on the direct path only.

**E: an arm-local abstract value in a block's inferred type.** Imprecision, not unsound. A block's result type is the first arm's type, formed under that arm's refinement. When it is a Π-type that captured the scrutinee, it records the arm's values: `Π(y7 : Nat) (y8 : ⊤ ∧ ⊤). Unit where κ1 = (σ3, σ4)`, where σ3 and σ4 are the fields of that arm's `Mk`. Example: `Id Prop (let a0 = match q2 { Mk(p5, p6) => λ(y7 : Nat) (y8 : ⊤ ∧ ⊤) : Unit => q2 := q2 }; ⊤) ⊤`. The value never escapes into a result, because untyped runs do not read a block function's codomain. It can make two equal sealed programs non-convertible, which is fail-safe. The arms' types are checked convertible after refinement, so the recorded type agrees with the true one at every instance.

**V: vacuous.** A zero-arm match yields `⋆` at any type (D49), so under `h : False` a `Unit`-typed term is `⋆` on the direct path and `()` from a closed-off block's row. Its tail being a proof also makes an enclosing `;`/`let` erased, which trips D41. No instance satisfies the hypothesis, so none of this is observable.

**v1.6's N1 and N2** are rejected on v2.1 by D41 (an erased term may not write a place that outlives it). `Scratch/OldN12.lean` has every program of the v1.x log §3, each rejected.

### v2.6 What the fuzzer does not cover

**Language features never generated:**
- Inductive declarations, so D36 (positivity) is out of reach, and parameterised inductives other than `Pair` at `Nat × Nat` and `Or` at `⊤, ⊤`.
- Universes other than `Prop`/`Type`, or type-valued λs, except the `U`/`V` family.
- `J`, `cong`, `trans`, `symm`; conversion (D48(3)) meets Π-types only through closures.
- Borrows of non-data types, so D48(1)/(2) are out of reach.
- Abstract functions returning borrows without borrow parameters, so D44 is out of reach.
- Recursive local functions (`fix … by`).
- D53 exists only as a prototype, off by default. It is tested only as a switch (`D53on`, §v2.3), and `clone` is never generated.

**Limits of the oracles and generator:**
- Refinements are one constructor level deep, plus six ground instances drawn from the values 0–3 and lists or pairs of them.
- The truth oracle tries about ten proof shapes. A false statement whose only accepted proof has another shape goes unnoticed.
- The conversion oracle only runs on function pairs of simple signatures.
- The frame oracle only runs where a borrow parameter can sit inside a `S`, `Mk`, `MkB` or `Cons` hole.
- Programs are small: 1–3 statement parameters, 0–2 random functions, and a term budget of 3–10.
- The generator is type-directed but tracks liveness conservatively. About 2.4% of cases are rejected at the generic call, and those test nothing.

**Relation to the paper.** Naturality is tested as syntactic equality of normal forms after resolution. The comparison is modulo renaming of fresh abstract values and loans, the unit laws of `And`, and ground completion of any leftover abstract values. It is not modulo full conversion.

## v1.6–v1.8 (branch ochr-core-fuzz): the original log

Kept as it was left. §4 (`proofByValue`) and §5 (not checked yet) were never written. N1 and N2 are rejected on v2.1 by D41 (§v2.5, `Scratch/OldN12.lean`). The emulation switches `+D37`, `+D35` and `+N12` below no longer exist.


**Verdict (running log, newest findings first in §3).** The fuzzer rediscovers the known two-path bugs when their rule is switched off, and on the v1.6 snapshot it found two new closed proofs of false (N1, N2 below) that no v1.7/v1.8 rule addresses.
**Most important finding:** the checker decides "this term is a proof, so it is erased" (P2) from a syntactic list of proof formers, plus an ascription's type in typed mode only. A proof tail that is not `refl`/`⟨⟩`/`J`/… (a proof λ, a proof variable, a let-bound proof), or an ascribed proof run by the untyped machine ([Seal] re-normalisation, callee bodies), is erased on one path and run on the other.
**What must change:** P2's "declared type has sort Prop" needs a definition that the untyped machine can apply (e.g. "its value is ⋆", which C7 makes equivalent and which is determined by declared types), and the checker must use it for every non-call term in both modes.
**Confidence:** high for N1 and N2 (both accepted by the unmodified v1.6 checker, programs below).
**Not checked yet:** see §5.

### 1. How it works

`lake exe fuzz` (files `ochr/core/lean/Ochr/Fuzz/*.lean`, `Fuzz.lean`). Case `i` of seed `S` is a pure function of `(S, i)`.

- **Generator** (`Gen.lean`, `GenTerm.lean`, `Case.lean`, `Lib.lean`): type-directed over `Nat`, user inductives `B2 := F | T`, `L := Nil | Cons(h, t)`, `Box := Mk(v)`, borrows `&p`, reborrows `&*x`, moves of borrow variables, sub-place borrows `&(p).1`, assignments, tail and non-tail matches with pattern variables, `let` with and without annotations, local λs (including codomain `U(n)`), `Id`/`Eq`/`∧` statements and nested `Id` inside terms, proofs with effects, abstract function parameters instantiated by library functions. A template library (AddM, Add, TailM, Pick, PickX, PickY, Keep, Double, IsZ, G1, Clr, Inc, U, V, W, MkF, Le, Lemma, F5, LastM, AppendM, Len) is drawn at random per case, plus 0–2 random (sometimes recursive) functions, checked first. The statement is `def Stmt (params) : Prop := Id A lhs rhs`.
- **Oracles** (`Harness.lean`, `Refine.lean`, `Oracle.lean`, `Run.lean`): the generic environment is built exactly as [Def] does. G = the checker's own `observe` of each side (result and final content of every binding: the full resolution) and the `Id` type. For each refinement α (`σ := Z`, `S σ'`, `S (S σ')`, each constructor with fresh fields, each library function of an abstract function's type) and 6 ground instances, D = the same observations from `refine`d Ω, and R = G refined by `substV` (which re-normalises sealed programs). Generalisation records are undone (`σ_g := ⌈n⌉`) on both sides first. R and D are compared up to renaming of fresh σs and loans; if they differ syntactically but are not ground, both are ground-completed (4 completions) and compared again. Findings: `nat` (R ≠ D), `false` (generic `Id` is ⊤, a ground instance is not), `verdict` (generic succeeds, direct errors), `renorm` (re-normalising R errors, direct succeeds), `escape` (a σ that is neither a parameter nor a recorded generalisation, or a surviving loan), `adequacy` (typed direct run vs the untyped machine at a ground instance).
- **Shrinker** (`Shrink.lean`): greedy deletion/replacement on the surface program, keeping the same finding kind and error class. **Printer** (`Print.lean`): the paper's surface syntax, re-parseable by `ochr { }`. **Replay** (`Replay.lean`): `replay Cex` runs the oracles on a pasted counterexample.
- **Attribution**: `--diff --switch X` reports only findings present with rule X off and absent with it on (same case). `--jobs J` runs crash-isolated worker processes (a crashing case, e.g. a stack overflow, is reported and skipped).
- **Emulations** (two opt-in `Config` hooks, default off, so the checker's behaviour and the ledger are unchanged): `+D37` (`genGlobal`: restores keep generalisation records and fresh-name counters) and `+D35` (`syntacticClass`: a closure's class from its codomain term, a stuck block erased only when its match is a proof, and sequencing forms erased only when they evaluate to a proof). They let the fuzzer look past bugs already fixed in v1.7/v1.8.

Usage: `lake exe fuzz --seed 1 --count 100000 --jobs 16 [--switch +D37 --switch +D35] [--diff --switch D32] [--shrink 2] [--quiet]`; `--show I` re-runs case I verbosely.

### 2. Validation: known bugs rediscovered with their rule switched off

`--diff`, seed 1, with `+D37` (so X3-style escapes do not mask them). "Case" is the index of the first case exhibiting it (cases are ~3 ms each).

| switch off | rediscovered | first case | shrunk shape |
|---|---|---|---|
| D32 (pattern writes) | F5 `Clear` | 118 | `Id Prop (match *x0 { Z => () \| S p => p := 0 }; ⊤) ⊤` at `x0 := S σ` |
| D28 (erasure by declaration) | F1 | 405 | `W(&n0, *x1); ()` at `x1 := 0` |
| D29 (match ends loans in neutral head) | F2 | 116 / 359 | returned borrow's hole orphaned; direct path reads ⊥ |
| P2/D26 (erased terms on a private copy) | N1 | 203 | `let a = match n1 { Z => refl \| S p => n0 := n1; refl }` |
| D19 (access ends loans inside) | BadA1-type | 1888 | verdict: the direct path errors where the generic path accepted |
| C5 (blocks move moved borrows) | `MovedByBlock` | 815 | `match *x0 { Z => let a = x0; () \| S _ => () }; … *x0 …` at `x0 := 0`: use after move |
| D18 (owners are sets) | meta-model C2 | 19587 | `let a = match *x0 { Z => &n1 \| S p => x0 }; Id Unit () (*a := 0)` |
| D30 (closures by observation) | F3 | 8 (conv oracle); 191 (`false`) | closures equal on results only; block closures inside sealed programs too |
| D17 ([Rec] entry values) | Loop/Bot' shape | 0 (truth oracle) | `def Lie (n0 : Nat) (x1 : &Nat) : Id Nat *x1 0 by n0 := Lie(n0, x1)` accepted |
| D31 (no `f` without `by`) | F4 | 0 (truth oracle) | the same without `by` |
| L1 (f only as a call head) | not reached | | the proof candidates never pass `Lie` as a value |
| none (default v1.6 rules) | X2/BoomB (D35) | 56 | `Id Prop (match *x2 { Z => ⊤ \| S p => *x1 := 0; ⊤ }) ⊤` |
| none (default v1.6 rules) | X3's root (D37) | 28 | a generalised σ escapes the private copy of `observe` |
| none (default v1.6 rules) | X4 (D38) | 4525 | `PickX ≡ PickY` accepted; they observe `(0,(7,0))` vs `(0,(0,7))` |
| none | X5 (D39) | not reached | no crash in 900k cases: an abstract `Π(x y : &Nat). &Nat` called with two borrows and an owner read back never came up |

The truth oracle (§1): when a statement is false at a ground instance, it tries `refl`, a one-level split of each parameter, structural recursion on each `Nat`/`&Nat`/list parameter, and non-decreasing recursion with and without `by`; an accepted one is a closed proof of false by instantiation.

### 3. Findings on the current rules (v1.6 snapshot; labels say what already fixes them)

Soundness first. Every program below was checked with the unmodified v1.6 checker (`Scratch/R2.lean`, `R3.lean` in the worktree; the `reject def` lines are the ones it rejects).

**N1 (new, closed proof of false; rule at fault: the checker's reading of P2 clause "declared type has sort Prop", not fixed by D35/D37–D39).** A `Prop`-typed match whose arm writes and then ends in a proof that is not a syntactic proof former. At the generic call the match is stuck, closes off as a block whose codomain is a proposition, and the block is erased as a proof (class 2): the write is discarded. At `n = 0` the same match runs inline; `eval` marks a term erased only if it is `refl`, `⟨⟩`, `cong`, `trans`, `symm`, a `J` with a `Prop` motive or an ascription at a `Prop` type, and a `seq`/`let`/`match` inherits its tail's mark, so `(c := 1; λ…)` is not erased and the write persists.
```
def LieL (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; λ(y : &Nat) : ⊤ => refl) | S _ => λ(y : &Nat) : ⊤ => refl }; c) 0 := refl
def BoomL : Eq Nat 1 0 := LieL(0)                                     -- accepted
def LieV (n : Nat) (h : ⊤) : Id Nat (let c = 0; let f = match n { Z => (c := 1; h) | S _ => h }; c) 0 := refl
def BoomV : Eq Nat 1 0 := LieV(0, refl)                               -- accepted
def LieR (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; let e = refl; e) | S _ => refl }; c) 0 := refl
def BoomR : Eq Nat 1 0 := LieR(0)                                     -- accepted
def LieF (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; refl) | S _ => refl }; c) 0 := refl
reject def BoomF : Eq Nat 1 0 := LieF(0)                              -- rejected: refl is a proof former
```
Found at case 354 of seed 1 (with `+D37 +D35`), shrunk to `Id Prop ⊤ (let a = match *x0 { Z => *x0 := 1; λ(y : &Nat) : ⊤ => refl | S _ => λ(y : &Nat) : ⊤ => refl }; ⊤)`.

**N2 (new, closed proof of false; same root, in the untyped machine).** The untyped machine (callee bodies and every [Seal] re-normalisation) has no types, and `eval` decides an ascription's erasure from its declared type only in typed mode, so it runs an ascribed proof's write that the typed path erases. [Split] re-normalises the sealed block with the untyped machine; the instance evaluates the same match typed.
```
def LieA (n : Nat) : Id Nat (match n { Z => let c = 5; let a : ⊤ = (c := 0; let e = refl; e); c | S _ => 0 }) 0 :=
  match n { Z => refl | S _ => refl }
def BoomA : Eq Nat 5 0 := LieA(0)                                     -- accepted
```
Found as an `adequacy` disagreement (typed run vs machine) at case 6232 of seed 1: `Id Unit (n0 := (let a0 : ⊤ = (n0 := 0; let a6 = refl; a6); n0)) 0` at `n0 := 1` gives `n0 = 1` typed and `0` on the machine; the checker itself rejects `Main(1) = 1` for `Main(n) := let c = n; let a : ⊤ = (c := 0; let e = refl; e); c` because [Call-type] runs `Main`'s body untyped.

*Fix for N1 and N2.* P2 is right as written ("any other term is erased iff … its declared type has sort Prop"), but the machine cannot see declared types. Every value of a proposition is ⋆ and only proofs evaluate to ⋆ (C7), and that is fixed by declared types, so "a non-call term is erased iff its value is ⋆" is the same condition, readable in both modes and stable under refinement. RULES should say so (one clause in P2); the checker's hook `proofByValue` implements it (below, §4, runs with it on).
