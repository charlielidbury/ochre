# fuzzer: a differential naturality tester for the Ochr checker

## v2 (rules v2.1 with D52–D58, branch ochr-fuzz-v2, 2026-09-29)

**Verdict.** On the checker with the soundness batch (ochr-core 84470253: recCands fix, D54, D55, D56, D58, the ⋆/loan typing fix), and again on ochr-core-lean ff6b634a (which fixes R2, R3 and R7), 10⁶ cases each on the default rules produced no refinement that disagreed with the direct path on a value. There were no `false`, `truth`, `irrel`, `frame` or `adequacy` value disagreements. The only `nat` findings are 14 where both sides are the same conjunction of equations in a different order (R6). Every remaining finding is one of:
- **fail-safe**: one path gets a type error where the other succeeds, so the checker rejects rather than accepts. Classes R1–R8 in §v2.6. On 84470253: 3,614 cases in 10⁶, of which R2 is 3,405. On ff6b634a, which fixes R2, R3 and R7: 2,250, of which 2,235 are R8, a new regression in the erasure pre-pass.
- **scoping imprecision**: E, which cannot change a value.
- **vacuous**: some hypothesis is `False` at that refinement.

**Real findings, in order.**
1. **F-v2-1, a closed proof of `False`.** [Rec] stopped checking after a sealed program was typed. It was common: 351 cases in 10⁵ on 96d788a1. Fixed by 3ff0e1e2.
2. **P2 is soundness-relevant, not just completeness.** With P2 alone switched off (D41 on), there is a closed proof of `False`. The ledger lists P2 as completeness.
3. **The D53 prototype breaks naturality in three ways**, two of them in the unsound direction. It is off by default, and these results became D53's acceptance criterion.
4. **R1 (untyped `Id` owners holding a loan), an incompleteness.** Fixed by ef1195ff, apart from one residual shape (1 case in 10⁶): an owner reached through a returned borrow.
5. **R8, a regression in the erasure pre-pass (ff6b634a).** Its own INTERNAL assertion fires when a closed-off block calls a captured proof-function parameter. Fail-safe; reported with a two-line reproduction (`Scratch/R8PrePass.lean`).

The extended generator also re-finds the cold reviewers' attacks when their switch is off: reviewer-5's D54 `Boom` (as a `false` and a `truth` finding), and reviewer-4's `TT` (as `irrel`). §v2.3 counts which attack shapes it reaches.

6. **The absTy arm-leak (found by arrays-library, checked by the fuzzer; a false rejection).** Refinements leak across match arms through `absTy` (the types of abstract values), which `restoreKeep` keeps under D37 while restoring the environment. With a parameter `r : Slice(Sub(n, k))`, the `n := Z` arm rewrites `absTy[σ_r]` to the `Z`-form, and because that replaces `σ_n` by `Z`, the `n := S m` arm cannot undo it: a use-site that types `r` through `valType` sees `Slice(Sub(0, k))` (`Scratch/LeakSweep.lean`). This is a false rejection. It is not exploitable as a false acceptance within the current rules: the over-refinement only makes a consuming check stricter, and eliminating `r` as the leaked type needs it to compute to a concrete inductive, which the leak's precondition (a second parameter left abstract) denies — `Sub(0, k)` with `k` abstract stays stuck (`Scratch/LeakBoom.lean`). Under D55 these families are all `Type`-valued, so the leak cannot flip a sort. The binding type of a parameter is restored correctly, so most type reads are unaffected.

**Validation.** Every ledger rule was switched off in turn (§v2.4). The fuzzer rediscovers 17 of the ledger's 22 soundness rows and 2 of its 4 model rows. Three of the soundness misses need constructs it never generates: inductive declarations, `&` of a non-data type, and a scrutinee of computed type. The other two, D18 and D35, are rare shapes: each was found once in 10⁵ cases by an earlier generator version.

**Confidence.**
- F-v2-1 and the P2 finding are certain: each is a program the checker accepts. F-v2-1 on 96d788a1 (`Scratch/RecWipe.lean`); the P2 one with `eraseOnCopy := false` (`Scratch/P2Alone.lean`).
- "No value disagreement" holds only within the generator's coverage (§v2.7).

### v2.1 How to run

```
cd ochr/core/lean
lake build fuzz
lake exe fuzz --seed 1 --count 100000 --jobs 8                    # 10⁵ cases, about 70 s on 8 cores
lake exe fuzz --seed 1 --count 20000 --jobs 8 --diff --switch D54   # attribute findings to one rule
lake exe fuzz --seed 1 --show 1424                                 # one case, verbosely
lake exe fuzz … --list                                             # also print `@FIND case key` per finding
```
- Case `i` of seed `S` is a pure function of `(S, i)`.
- `--switch X` names a ledger row: `D17`…`D58`, `P1`/`P2`/`P3`, `L1`–`L3`, `C5`, `C8`, `G1`, `capTypes`, `scrutTyped`, `confineBodies`, `D50on`. It can also name `D53on`, which turns the D53 prototype on.
- `--diff` keeps only the findings a case shows with the switches on and not with the default rules.
- `--jobs J` runs crash-isolated worker processes.
- `--shrink K` shrinks and prints K findings per kind and worker. A printed counterexample is an `ochr` block. After `import Ochr.Fuzz.Replay`, `#eval IO.println (replay Cex)` re-runs the oracles on it.

**Where the code lives.** The fuzzer is on branch `ochr-fuzz-core`, which is ochr-core plus the fuzzer only (`Fuzz.lean`, `Ochr/Fuzz/`, the `fuzz` exe, `Scratch/`, these notes). It builds against ochr-core's checker as is. The ff6b634a runs in §v2.5 used branch `ochr-fuzz-v2`, which also carries the checker lane's ochr-core-lean head. The `Scratch/` files' expectations are for ochr-core; each says how it changes on ff6b634a.

**Checker hooks.** None. The fuzzer uses the checker unmodified, and `lake exe tests` reports 519/519 on this branch.

### v2.2 What it checks

**Harness.**
- The generic environment is built as `checkFix` builds it: declared proof flags, proof parameters bound to `⋆`.
- The statement's declared types first pass `checkDef`'s static checks: its own name not in its type, D48(2), and D55 in every type position.
- A case's program is `Prelude` followed by its own declarations.
- An observation (result and final contents of every binding) is packed as one value.
- Values are compared modulo renaming of fresh abstract values and loans, and modulo the unit laws of `And` (D50).
- A `nat` finding is reported only when both sides, ground-completed, are ground and still differ.

**Oracles.**
- **`nat`**: the refined generic observation differs from the direct one.
- **`false`**: the generic `Id` is `⊤`, while a ground instance's is `False` and its hypotheses are `⊤`.
- **`truth`**: a proof of a statement that is `False` at some instance is accepted. About ten proof shapes are tried, among them non-decreasing recursion, Knot's L1 shape and KnotL's L3 shape.
- **`irrel`** (new, reviewer-4 W2): two instances of a parameter whose type is a proposition by computation give different data.
- **`verdict` / `renorm`**: one path errs where the other succeeds.
- **`escape`**: an abstract value that is neither a parameter nor a generalisation record appears, or a loan survives.
- **`adequacy`**: the typed run and the untyped machine differ at a ground instance.
- **`frame`**: plugging a borrowed cell into a larger owner changes the observation other than as the frame lemma says.
- **`conv`**: two functions the checker finds convertible observe differently on ground inputs.

A finding at a refinement where some proof parameter's type is `False` is marked `vacuous`.

**Generator.** Type-directed. It covers:
- `Nat`, user inductives (`B2`, `L`, `Box`), `Nat × Nat` pairs (D52), borrows, reborrows, sub-place borrows and returned borrows;
- matches (tail and non-tail) with pattern variables, `let`s with and without annotations, and λs capturing values;
- `Id`, `Eq`, `∧`;
- proof parameters (`⊤`, `⊤ ∧ ⊤`, `False`, `Or`, `ExN`, and hypotheses about data parameters);
- matches on proofs by their type (D45), zero-arm matches, and proof constructors;
- about 45 templates, plus 0–2 random, sometimes recursive, functions.

The cold reviewers' attack shapes are included:
- **D54, reviewer-5.** Function parameters on one borrow whose codomain is `Prop`, `⊤`, `Unit`, `&Nat`, or a term that evaluates to one of them (`P0`, `UU(Z)`, `V(Z)`). Library writers at those codomains (`H`, `HP`, `HU`, `HW`, `HTop`, `HTopW`) and identity wrappers (`IdFP`/`IdFT`/`IdFU`, `RunG`, `RunK`). Calls through a parameter, a `let` alias, a wrapper, or an annotated `let` whose codomain is written differently (Boom4's shape).
- **D55, reviewer-4.** The `V(Z)` family and `TT := Π(x : &Nat). V(Z)`, as codomains, parameter types and annotations. The default rules reject these, so they are offered as an attack family, live only with a switch off.
- **D56.** Data-level `J` casts along a hypothesis `Eq Nat a b`.

### v2.3 History of real findings

1. **F-v2-1: closed proof of `False` (checker bug).** On 0127f58b and 96d788a1, `sealedType` emptied the [Rec] accumulators inside `onCopy`, and `restoreKeep` kept `[].drop 0 = []` while restoring `recStack`. `recCheck` zips the two, so later recursive calls went unchecked. Found by the truth oracle at seed 1, case 1424, in the first 2,000 cases. Also reached through a λ capturing a place that holds a backward function (case 1369). Common: 351 cases in 10⁵ on 96d788a1. Fixed by 3ff0e1e2/3d429334, where [Rec] state is one uid-keyed stack.
   ```
   def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S a' => match b { Z => False, S b' => Le(a', b') } }
   def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }
   def Boom : False := Lie(0, ⟨refl, refl⟩)          -- accepted before the fix (Scratch/RecWipe.lean)
   ```
2. **P2 is soundness-relevant (found by validation).** The ledger lists P2 (erased terms run on a private copy) as completeness under D41. D41 lets an erased term pass an outer place to an erased call, and without the private copy that call's writes persist on the direct path but not on the closed-off one. With `eraseOnCopy := false` alone, the fuzzer finds `false` findings (3 in 2·10⁴), and the checker accepts `Boom2 : False` (`Scratch/P2Alone.lean`):
   ```
   def F5 (x : &Nat) : Prop := *x := 5; ⊤
   def Lie (x : &Nat) : Id Nat (let a = match *x { Z => refl, S p => F5(&*x); refl }; *x) *x := refl
   def Boom : False ∧ False := let c = 1; Lie(&c)
   def Boom2 : False := let b = Boom; match b { Intro(l, r) => l }
   ```
3. **The D53 prototype breaks naturality** (`D53on`, off by default; reported to the lead, now D53's acceptance criterion). There are three shapes; (b) and (c) are in the unsound direction:
   - **(a) A closed-off block moves the places it only reads.** `Id L n0 (match n0 { Z => Nil, S _ => Nil })` at `n0 := 0`: `⊥` on the block path, `0` on the direct path.
   - **(b) [Close] turns a move out through a borrow into a copy.** `Id Nat 0 (match *x0 { Z => *x0, S p3 => … })` at `x0 := 0`: the direct path errors, the closed-off path sees `0` twice.
   - **(c) Conversion misses a move through a borrow.** `λ(y9 : &Nat) (y10 : &Nat) : &Nat => *y10; y10` is found convertible to `λ(y9 : &Nat) (y10 : &Nat) : &Nat => y10`, yet on ground inputs one returns a borrow of `⊥` and the other a borrow of `0`.
4. **R1: untyped `Id` owners holding a loan (incompleteness).** Fixed by ef1195ff: a live loan is typed by its borrow's content. 16,551 cases in 10⁶ on 658cc108, none since.
5. **The cold reviewers' attacks**, re-found by the extended generator with their switch off (seeds 1 and 3, 2·10⁴ cases each):

| attack | switch | found? | as | first shrunk example |
|---|---|---|---|---|
| reviewer-5 `Boom`, `RunGGen(H)` | D54 | yes | `false` 2, `truth` 1 | `Stmt (h1 : Π(z0 : &Nat). Prop) := Id Nat (RunG(h1)) 0`, false at `h1 := H` |
| reviewer-5 `BoomI`, through an identity function | D54 + D55 | yes | `false` | `Id Nat (RunG(match *x0 { Mk(p0, p1) => IdFP(H) })) 0`, also through a stuck match choosing the function |
| let alias (`let g = f; g(&c)`) | D54 | yes | `nat` | `let c1 = 0; let g0 : Π(x : &Nat). P0 = h1; g0(&c1); c1` at `h1 := F5`: refined 0, direct 5 |
| reviewer-4 `Boom4`, an annotated `let` in a stuck match | D54 | yes | `truth` 1, `nat` | `match n0 { …, S p3 => let g5 : Π(x : &Nat). P0 = HP; g5(&n0); () }` |
| reviewer-4 W2 `TT`, a proposition with relevant inhabitants | D55 | yes | `irrel` 27 | `Stmt (h0 : TT) := Id (Nat × Nat) (1, 0) (let a9 = 0; let g11 = h0; g11(&a9); (a9, 1))` at `h0 := FV` against `GV` |
| reviewer-4 W1 `Boom`/`Boom2`, `RunK(f, x)` with `f : Π(x : &Nat). T(Z)` | D54 + D55 | not as a `false` finding | – | `RunK` and `FV` co-occur in 11 finding cases, but no closed false of this exact shape appeared in 2·10⁴ |
| reviewer-5's proof variant (`V(Z)` codomain at `Π(x : &Nat). ⊤`) | D54 + D55 | not as a `false` finding | – | – |
| reviewer-4 W4, `J` casts under absurd hypotheses | D56 | vacuous only | – | the casts live only under a `False` hypothesis, which the naturality oracles call vacuous |

With the default rules (D54, D55, D56 on), none of these shapes produces a finding in the 10⁶-case run below.

### v2.4 Validation: each ledger row switched off

**Method.**
- `--diff --switch X` on the batch head (branch commit 42a08017, ochr-core 84470253).
- Pass 1 ran every row: seed 1, 20,000 cases, `--jobs 8`, 20–90 s per row.
- Pass 2 re-ran the rows pass 1 missed: seed 2, 100,000 cases.
- A row is *rediscovered* when a non-vacuous finding absent under the default rules is one of that rule's own failures. Findings of the fail-safe classes R2–R7 alone do not count.
- Row kinds are the ledger's (`lake exe tests`).

**Soundness rows: 17 of 22 rediscovered.**

| switch off | first case | what it finds |
|---|---|---|
| P2 without D41 | 64 | `false` 106, `nat` 291, `truth` 5 (N1's shape) |
| D17 [Rec] entry values | 0 | `truth` 2,558: non-decreasing recursion proves a false statement |
| D31 no `f` without `by` | 0 | `truth` 2,558 |
| L1 self only as a call head | 72 | `truth` 321, Knot's shape |
| L3 [Rec] in nested functions | 34 | `truth` 1,011, KnotL's shape |
| D19 [Access] ends loans inside | 1,923 | [Drop]-while-borrowed verdicts, `escape` |
| L2 no ⊥ argument | 101 | verdicts, `G1(&n0, n0)` |
| C5 blocks move moved borrows | 3,882 | use after move on the direct path |
| D29 matching ends loans in a neutral | 175 | `escape` 16: a returned borrow's hole left in the observation |
| D30 closures by observation | 68 | `conv` 914, `false` 28, `nat` 49 |
| D32 pattern writes | 3 | `nat` 523, `false` 42, `truth` 5 |
| D35/D40 block erased iff each arm | 93 | `nat` 168, `truth` 12, `false` 1 |
| P1 with the computed-type block rule | 683 | `nat` 15, `false` 4 |
| D37 global generalisation records | 3 | `escape` 407 (X3's root) |
| D38 borrow results observed by a write | 59 | `conv` 55 (X4) |
| D45 + D42 | 88 | `nat` 2, `adequacy`, D41 verdicts |
| D54 class and borrow row in Π-types | 17 | `adequacy` 203, `nat` 89, `false` 2, `truth` 1 (reviewer-5) |

**Tally: 18 of 23 soundness rows reached** (the 17 above, plus P2-alone below, which is a soundness finding the ledger mislabels as completeness).

**Soundness rows not rediscovered (5):**
- **D18** (owners are sets) and **D35** (a function's class from its codomain term) are rare shapes, not out of reach: each was found once in 10⁵ cases by an earlier generator version (658cc108). On the batch head with the current generator they did not recur.
- **D36** (positivity), **D48(2)** (`&` only at the top) and **scrutTyped** (a scrutinee's constructors from its type) are declaration- and elaboration-level rules, not the two-path property the naturality oracles test. D36 rejects a malformed `inductive`; D48(2) rejects a codomain computing to `&T`; scrutTyped rejects a match whose scrutinee's type is a computed family. Reaching them differentially would need the generator to synthesise inductive declarations and dependent parameter types, which it does not. Their soundness is validated by the ledger's curated counterfactual witnesses (`Positivity.Boom`, `BorrowTypes.G`, `ScrutineeTypes.g`) rather than by the fuzzer.

**Model rows: 2 of 4.**
- D55 (syntactic sorts): `irrel` 27, first case 23 (reviewer-4 W2).
- D45 (subsingleton elimination): `adequacy` 1.
- Not reached: D44 (an abstract `Π(n : Nat). &Nat` is never generated) and D48(1).

**False-lemma row.** P3 without D41: R2 only.

**Policy rows:**
- D28 is reached as D41 verdicts (27): D41 rejects the misclassified term on the path that erases it. This is the fail-safe working.
- P1 without D41: `nat` 4.
- D41: R2 only.
- D35r: not reached.

**Completeness rows:**
- **P2 alone:** `false` 3. This is the soundness finding above.
- **D27:** `irrel` 8 and `symm` verdicts, since proof parameters become `σ`.
- **G1:** `escape` 407.
- **D35 (sequencing), P1, D42:** D41 verdicts.
- **capTypes:** renorm errors.
- **D47:** `nat` 1, conjunction order (R6: without disjointness, ground equations between distinct constructors stay uncomputed), and R2.
- **D52:** `nat` 2. Without injectivity, the two paths' `Id` differ in conjunct order (R6) or in granularity: a whole pair owner `Eq (Nat × Nat) (1, 3) (1, 1)` against its field `Eq Nat 3 1`. The truth values are equal, so this is an incompleteness. Injectivity is what reconciles the two paths, for open terms too.
- **D39:** `renorm: normalisation depth exceeded` 3 in 10⁵ (X5's loop).
- **D56, D58:** vacuous only.
- **Not reached:** C8, P3 alone, D45 (match by type), D48(3), D49(3), D50 on, confineBodies.

**D53on (prototype).** `nat` 1,019 and about 400 verdicts in 2·10⁴ cases; see §v2.3.

### v2.5 At-scale runs

| checker | seeds | cases | time | value disagreements | notes |
|---|---|---|---|---|---|
| ff6b634a (R2, R3, R7 fixed; erasure pre-pass), default rules | 1–10 | 1,000,000 | 788 s, 12 workers | **0** (plus 14 conjunct-order differences, R6) | R2/R3/R7 gone; a new fail-safe class R8 from the pre-pass |
| 84470253 (the batch), default rules | 1–10 | 1,000,000 | 661 s, 8 workers | **0** (plus 14 conjunct-order differences, R6) | fail-safe classes only, table below |
| 658cc108 (recCands fixed) | 1–10 | 1,000,000 | 491 s, 16 workers | 0 | before the reviewer shapes were added to the generator |
| 96d788a1 with the fix as an opt-in hook | 1–10 | 1,000,000 | 536 s, 16 workers | 0 | the same counts as the row above |
| 96d788a1, unpatched | 11–12 | 100,000 | 56 s, 16 workers | – | 351 `truth` findings, all F-v2-1 |

**Main run statuses (84470253).** 936,320 cases were checked. In 49,375, the default rules reject the generic statement; in a sample of 400 cases, 12 of the 16 rejected or unresolved ones were the reviewers' attack shapes, which only a switch-off makes live. In 14,305, the case does not resolve, mostly an attack template that the default rules left out. No crashes.

| class | findings in 10⁶ on 84470253, non-vacuous (vacuous) | on ff6b634a |
|---|---|
| R2 a λ in a block's arm captures a borrow | 3,405 (500) | 0 (fixed) |
| R3 conversion runs a block's function generically | 160 (8) | 0 (fixed) |
| R7 `symm` in an unreachable branch | 34 (1,850) | 0 (fixed) |
| R6 conjunction order | 14 (1) | 14 (1) |
| E arm-local value in a block's inferred type | 92 (2) | 65 (1) |
| R1 residual (an owner reached through a returned borrow) | 1 (0) | 1 (0) |
| R4, R5 | 0 | 0 |
| R8 the erasure pre-pass's INTERNAL assertion (new) | – | 2,235 (339) |
| vacuous: `adequacy: stuck (escaped to the top)` (a `J` cast or zero-arm match stuck under a `False` hypothesis, run by the untyped machine) | 0 (27,938) | 0 (28,039) |

### v2.6 The fail-safe classes, one sentence each

Each class has a true statement the checker rejects today, in `lean/Scratch/` (`lake env lean Scratch/X.lean`, all "as expected").

- **R1: an untyped `Id` owner holding a loan (mostly fixed by ef1195ff).** Re-normalising a sealed program that forms an `Id` about a cell it has lent out failed to type the cell (16,551 cases in 10⁶ on 658cc108; `V2Classes.R1s` is accepted now). One residual case in 10⁶ on 84470253 remains, where the owner is reached through a returned borrow: `R1Residual.Split` is a true statement, proved by splitting, that is rejected with "cannot infer the type of the value loan_ℓ".
- **R2 (fixed by ff6b634a): a λ in a stuck block's arm captures a borrow on re-normalisation.** A block takes a place by `&` when an arm writes it. Two things go wrong:
  - (i) The capture analysis counts a nested λ's write to its own copy as a write by the block (`V2Classes.R2s`: `Id Nat (match n0 { Z => n0, S p2 => let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0 }) n0`).
  - (ii) A λ that only reads the place captures the block's borrow parameter rather than the value it reads (`EV.ClassE4`: `match q2 { Mk(p5, p6) => let f = (λ(y7 : Nat) : Nat => p5); q2 := (1, 1); f }`).

  Fix: occurrences inside a nested function count as reads of the block, and `capture` captures the place a λ reads (`(*q2).fst`, by value), not the root variable.
- **R3 (fixed by ff6b634a): conversion runs a block's function at a generic call.** A block formed inside an arm reads pattern sub-places (`x0.1`, `(*q0).fst`) that exist only under that arm's refinement. D30's conversion observes such a function at a fresh generic argument, where the sub-place does not exist, and `convFn` lets the error escape instead of answering "not convertible" as `convPi` does (`V2Classes.R3s`).
- **R4 (fixed by 84470253/ff6b634a): a call of a sealed function in untyped code.** A block whose arms return λs closes off to a sealed function. Calling it during re-normalisation needs its Π-type for [Close]'s row, which is not recorded It was 23 cases in 10⁶ on 658cc108 and 0 since.
- **R5: arm types formed under different refinements** (1 case in 10⁶, 658cc108). Two arms' Π-types capture a place holding a sealed program that the arms' refinements made different, so D48(3)'s comparison finds `U(⌈…0…⌉) ≠ U(⌈…S σ⌉)` although both are `Prop`.
- **R6: `Id`'s conjunction order is not stable under closing off.** `Id` lists the observed owners in the order of Ω, and a closed-off block orders them by its captures. `And` is not commutative by conversion, so a true statement proved by splitting is rejected (`R6Order.Direct`). With pairs, `Eq` at `Nat × Nat` splits by injectivity, so this shows even at ground instances (`False ∧ (False ∧ False)` against `(False ∧ False) ∧ False`). Fix: order the footprint canonically (by first occurrence in the statement, or by parameter position), not by Ω.
- **R7 (fixed by ff6b634a): `symm` in an unreachable branch.** `symm h` (and `trans`) needs `h`'s type to be an equation or `True`. In a branch whose refinement makes the hypothesis `False`, the branch is unreachable, but `symm h` is a type error (`R7Symm.Split`), while the plain `J` along `h` is accepted there.
- **E: an arm-local abstract value in a block's inferred type (not unsound).** A block's result type is read off the first arm, under that arm's refinement. When it is a Π-type that captured the scrutinee, arm-local values (`Mk(σ3, σ4)`) sit in its `where κ` captures (`EV.ClassE`, `ClassE4`). Untyped runs never read a block function's codomain. A stale type mentions only fresh σs that nothing else shares, so it can make a conversion fail, never succeed wrongly. It needs the block to take the place by `&` (some arm writes it) for its sealed program to reach an observation. On 84470253 it arrived with R2 (ii); since R2 is fixed it stands alone (65 cases in 10⁶ on ff6b634a, `EV.ClassE4`).
- **R8 (new on ff6b634a, the erasure pre-pass): the pre-pass misreads a closed-off block's proof parameter.** When a stuck block captures a proof-function parameter, the block function declares that parameter in the captured form `(Π(z0 : &Nat). ⊤ : Prop)`. The pre-pass does not read that ascription as a proof, so it classifies a call through it as data while the machine (correctly) erases it, and the pre-pass's own assertion fires: "INTERNAL [pre-pass] …: erased/proof = (false, false) by its declared type, (true, true) after running". `R8PrePass.OnNat` is a true statement rejected by it: `(n : Nat) (h2 : Π(z0 : &Nat). ⊤) : Id Nat (match n { Z => 0, S p => h2(&p); 0 }) 0`, proved by splitting `n`. Variants: a captured λ returning a proof; and a proof `h : ExN` whose data field an arm writes, which makes the block capture the proof by borrow (`h3 : &ExN`, a borrow of a proposition) and the two readings disagree the other way. Fail-safe; 2,235 cases in 10⁶.
- **V (gone with D58): `⋆` against `()` under `h : False`.** A zero-arm match yielded `⋆` at any type, so a `Unit`-typed term was `⋆` on the direct path and `()` from a block's row. With D58 the match is stuck outside proof positions. `--switch D58` brings the vacuous findings back.

### v2.7 What the fuzzer does not cover

**Language features never generated:**
- Inductive declarations (D36).
- Parameterised inductives other than `Pair` at `Nat × Nat` and `Or` at `⊤, ⊤`.
- Universes beyond `Prop`/`Type`, or type-valued λs beyond the `U`/`V`/`P0`/`UU` families.
- `cong` and `trans`. `J` appears only as data casts whose motive computes to `Nat`.
- Borrows of non-data types (D48(1)/(2)).
- Abstract functions returning borrows without borrow parameters (D44).
- Recursive local functions.
- Arrays (D57).
- D53 (tested only as the prototype switch `D53on`).

**Limits of the oracles:**
- Refinements go one constructor deep, plus six ground instances from 0–3 and small lists or pairs.
- A function parameter's instances are the library functions of a convertible type. With none, its completions stay symbolic and are not compared.
- The truth oracle tries about ten proof shapes.
- The frame oracle only covers holes in `S`, `Mk`, `MkB`, `Cons`.

**Relation to the paper.** Naturality is tested as equality of normal forms after resolution. The comparison is modulo renaming of fresh abstract values and loans, the unit laws of `And`, and ground completion; R6 is reported separately.

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
