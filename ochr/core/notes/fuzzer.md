# fuzzer: a differential naturality tester for the Ochr checker

## v2 (rules v2.1 with D52–D61, branches ochr-fuzz-v2 and ochr-fuzz-core, 2026-09-30)

**Headline (ochr-core c469da44, the paper's numbers; D53 off by default there).**
- **Validation: 17 of the ledger's 20 soundness rows are rediscovered by switching the rule off** (§v2.4). All three misses are declaration-level rules that the generator never exercises: D36 (positivity of inductive declarations), D48(2) (`&` only at the top of a declared type) and scrutTyped (a scrutinee's constructors are read from its type). D19 counts as found through its new call-free witness `V` (§v2.4).
- **10⁶ cases on the default rules: 0 value disagreements, 0 `exec` findings (accepted functions that go wrong when run), and 0 fail-safe findings.** Classes R1–R8 are all at zero: R2, R3 and R7 fixed by ff6b634a, R1's residual by 06da7a2c, R6 by 1678d2a2, and R8 by the pre-pass fixes. What remains is 65 cases of E, a scoping imprecision that cannot change a value (plus 1 vacuous), and 28,039 vacuous `adequacy` findings under a `False` hypothesis. There were 936,787 cases checked, 47,419 rejected and 15,794 unresolved, with no crashes, in 1,165 s on 12 workers.

**D53 acceptance passes on ochr-core-lean b2ce75b5** (`--switch +D53`, execution oracle, 10⁶ cases): 0 `exec` findings, 0 value disagreements, 0 fail-safe findings; E 59 (1 vacuous) and 26,919 vacuous. Statuses: 924,079 checked, 60,127 rejected and 15,794 unresolved, with no crashes. The rounds went 15,567 `exec` cases (55977f8e) → 950 (10a7861a) → 10 (0b8a68f0) → 0. Each round's residue was shrunk and fixed by the checker lane (`Scratch/D53Blocks.lean`, `D53Residual.lean`, `D53Residual2.lean`, which now assert the fixed verdicts). The flip branch `ochr-d53-on` 9bb6b1c7, with D53 on by default, gives 0 `exec` and 0 value disagreements in 2·10⁵ cases (seeds 1 and 11). It also shows one fail-safe renorm, which revealed two problems:
- On the flip, `Config.prePassAssert` is false for every configuration. It normalises `d53 := false`, but the default is now `true`.
- R9 (`Scratch/R9PrePassArms.lean`): a match on a known scrutinee whose arms are a proof and data. The pre-pass reads the arms' mixed declared classes as data; the run takes the proof arm; the assertion fires INTERNAL. This happens on b2ce75b5 with and without D53. It is fail-safe, and while the assertion is on it hides as a rejected statement.

**Earlier D53 acceptance runs (ochr-core-lean 55977f8e, and again on 95da7c12 with D59; D53 on by default there; tour suite only): failed.** Each run was 10⁶ cases on the default rules, and the two runs gave the same counts. The existing oracles observe statements as types, which are erased, and D53's erased reads copy. On those oracles there is no value disagreement besides R6 (15 cases), and R8 is still there (2,344 non-vacuous cases). The new execution oracle (§v2.2) runs every accepted data function at ground inputs at runtime depth. It finds 15,567 cases (1.6%) in which the checker accepts a function that goes wrong when it runs. In almost all of them a stuck block hides its arms' moves from the rest of the function (§v2.3 item 5, `Scratch/D53Blocks.lean`). Switching `moves` off exposes nothing, which fits its "cost" class. Switching `ghosts` or `fnRule` off only changes which programs are accepted (§v2.4).

**Verdict on earlier heads.** On the checker with the soundness batch (ochr-core 84470253: recCands fix, D54, D55, D56, D58, the ⋆/loan typing fix), and again on ochr-core-lean ff6b634a (which fixes R2, R3 and R7), 10⁶ cases each on the default rules produced no refinement that disagreed with the direct path on a value. There were no `false`, `truth`, `irrel`, `frame` or `adequacy` value disagreements. The only `nat` findings are 14 where both sides are the same conjunction of equations in a different order (R6). Every remaining finding is one of:
- **fail-safe**: one path gets a type error where the other succeeds, so the checker rejects rather than accepts. Classes R1–R8 in §v2.6. On 84470253: 3,614 cases in 10⁶, of which R2 is 3,405. On ff6b634a, which fixes R2, R3 and R7: 2,250, of which 2,235 are R8, a new regression in the erasure pre-pass.
- **scoping imprecision**: E, which cannot change a value.
- **vacuous**: some hypothesis is `False` at that refinement.

**Real findings, in order.**
1. **F-v2-1, a closed proof of `False`.** [Rec] stopped checking after a sealed program was typed. It was common: 351 cases in 10⁵ on 96d788a1. Fixed by 3ff0e1e2.
2. **P2 is soundness-relevant, not just completeness.** With P2 alone switched off (D41 on), there is a closed proof of `False`. The ledger lists P2 as completeness.
3. **The D53 prototype breaks naturality in three ways**, two of them in the unsound direction. It is off by default, and these results became D53's acceptance criterion.
4. **R1 (untyped `Id` owners holding a loan), an incompleteness.** Fixed by ef1195ff, apart from one residual shape (1 case in 10⁶): an owner reached through a returned borrow.
5. **R8, a regression in the erasure pre-pass (ff6b634a).** Its own INTERNAL assertion fires when a closed-off block calls a captured proof-function parameter. Fail-safe; reported with a two-line reproduction (`Scratch/R8PrePass.lean`). Still present on 55977f8e.

The extended generator also re-finds the cold reviewers' attacks when their switch is off: reviewer-5's D54 `Boom` (as a `false` and a `truth` finding), and reviewer-4's `TT` (as `irrel`). §v2.3 counts which attack shapes it reaches.

6. **The absTy arm-leak (found by arrays-library, checked by the fuzzer; a false rejection).** Refinements leak across match arms through `absTy` (the types of abstract values), which `restoreKeep` keeps under D37 while restoring the environment. With a parameter `r : Slice(Sub(n, k))`, the `n := Z` arm rewrites `absTy[σ_r]` to the `Z`-form, and because that replaces `σ_n` by `Z`, the `n := S m` arm cannot undo it: a use-site that types `r` through `valType` sees `Slice(Sub(0, k))` (`Scratch/LeakSweep.lean`). This is a false rejection. It is not exploitable as a false acceptance within the current rules: the over-refinement only makes a consuming check stricter, and eliminating `r` as the leaked type needs it to compute to a concrete inductive, which the leak's precondition (a second parameter left abstract) denies — `Sub(0, k)` with `k` abstract stays stuck (`Scratch/LeakBoom.lean`). Under D55 these families are all `Type`-valued, so the leak cannot flip a sort. The binding type of a parameter is restored correctly, so most type reads are unaffected.
7. **D53: a stuck block hides its arms' moves (55977f8e).** The checker accepts functions that read moved data when run: 15,567 cases in 10⁶, all found by the execution oracle. See §v2.3 item 5.

**Validation.** Every ledger rule was switched off in turn (§v2.4). On c469da44 the fuzzer rediscovers 17 of the ledger's 20 soundness rows and 2 of its 4 model rows. The three soundness misses are declaration-level: inductive declarations, `&` inside a declared type, and a scrutinee of computed type. D18 is a rare shape (1 case in 6·10⁵). On D53's three rows the fuzzer agrees with the ledger's classes: `moves` is a cost row, and `ghosts` and `fnRule` are completeness rows. On 84470253 the tally was 18 of 23, before the D35 rows were deleted.

**Confidence.**
- F-v2-1 and the P2 finding are certain: each is a program the checker accepts. F-v2-1 on 96d788a1 (`Scratch/RecWipe.lean`); the P2 one with `eraseOnCopy := false` (`Scratch/P2Alone.lean`).
- The D53 findings are certain. Each is a function the checker accepts, and the checker itself rejects a call of it on a ground input (`Scratch/D53Blocks.lean`).
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
- `--switch X` names a ledger row: `D17`…`D59`, `P1`/`P2`/`P3`, `L1`–`L3`, `C5`, `C8`, `G1`, `capTypes`, `scrutTyped`, `confineBodies`, `D50on`, and D53's three: `moves`, `ghosts`, `fnRule`. On ochr-core D53 is off by default. `--switch +D53` turns it on, for the default and the `--diff` base alike, so D53's rows are `--switch +D53 --switch moves` and so on. The D35 rows were deleted with the erasure pre-pass.
- `--diff` keeps only the findings a case shows with the switches on and not with the default rules. With `--list` it also prints `@FLIP i base>switched` when the switch changes the statement's verdict, and `@XFLIP i m>n` when it changes how many of the statement's two sides the checker accepts as data functions (the execution oracle's `ExecL`/`ExecR`). A row such as `moves` changes acceptance without changing any value, and this is how it is measured.
- `--runtime-refine` refines the generic observation at runtime depth instead of erased. It is a diagnostic for the RN class (§v2.6). The checker refines statements erased, so most of what it reports are artefacts.
- `--jobs J` runs crash-isolated worker processes.
- `--shrink K` shrinks and prints K findings per kind and worker. A printed counterexample is an `ochr` block. After `import Ochr.Fuzz.Replay`, `#eval IO.println (replay Cex)` re-runs the oracles on it.

**Checker hooks.** None. The fuzzer uses the checker unmodified, and `lake exe tests` reports 548/548 on this branch (merged with ochr-core-lean 55977f8e).

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
- **`exec`** (new, D53; always on, in every campaign): a data function the checker accepts is run at every ground input at runtime depth, where reads move. It must not err, and it must observe what its erased run observes. This covers the random library functions, and the statement's two sides declared as data functions `ExecL`/`ExecR` over its parameters, when the checker accepts them. A `⊤` hypothesis gets `⋆`. A function with any other hypothesis or a function parameter is not run, and neither is one that returns a proof or a type. The other oracles observe statements as types, which are erased, so without this oracle D53's runtime moves were reached only through `conv` (2 cases in 10⁶).

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
5. **D53 acceptance: a stuck block hides its arms' moves (55977f8e; `Scratch/D53Blocks.lean`).** The fuzzer found D53 unsound before D53 was turned on in ochr-core. D53 stays off there by default until the execution oracle shows zero findings over at least 10⁵ cases. Each function below is accepted, and running it on the ground input shown is rejected. The same moves outside a block are rejected at the definition (`C1`, `C2`). All four are generic-accepts, instance-errors findings. In a compiled program they would be reads of moved data.
   - **M1: an arm moves a field that its pattern exposed.** `def A1 (q0 : Nat × Nat) : Nat × Nat := let a = match q0 { Mk(p, _) => p }; q0`. At `(0, 0)` the result is "q0 was partly moved out". `def A2 (n0 : Nat) : Nat := let a = match n0 { Z => 0, S p => p }; n0` fails the same way at 1. Cause: `splitArmsThenClose` takes each free variable's `before` value once, before the arms' refinements. `newHoles(σ, S ⊥)` has no case for an abstract `before`, so the move of `n0.1` never reaches `moved`.
   - **M2: an arm moves a whole captured place that is not a variable.** `def B1 (x0 : &Nat) (n1 : Nat) : Nat := let a = match n1 { Z => 0, S _ => *x0 }; a`. At `(&0, 1)` the borrow ends partly moved out. Here `moved` does contain `*x0`. But `closeOffMatch` makes a capture a move only when it is a whole variable (`whole && moved.any (· == .var o)`) or a strict sub-part of a copy capture. A moved place that is itself a maximal capture (`*x0`, `n1.1`, a pattern variable) stays an in-place copy. `B2` and `B3` are the same shape with a pair scrutinee and with a returned borrow.
   - **M2b: the block takes the borrow itself.** `def B4 (x0 : &Nat) : Nat := S (match *x0 { Z => x0; 0, S _ => *x0 })`. One arm reads `x0` whole, so the block moves the borrow in. Another arm moves out through it. The block now owns the borrow, and nothing checks the borrow's content when it ends.
   - **M3: erased code in a run.** A definition is checked on the typed path, but a call runs its body in the untyped machine, and there two erased terms are not treated as erased:
     - (i) The untyped `J` evaluates its endpoints under `onCopy` at runtime depth rather than under `confinedCopy`. So `def J1 (n : Nat) (h : Eq Nat n 1) : Nat := let m = n; J(Nat, n, 1, λ (z : Nat) : Type => Nat, h, m)` fails at `J1(1, refl)` with "n was moved out".
     - (ii) An `Id` whose side writes a moved place cannot type that place's owner: `def I1 (n1 : Nat) : Nat := let m = n1; let a0 = Id Unit () (n1 := 0); 0` fails at `I1(0)` with "cannot infer the type of the value ⊥".

   **After the fixes (ochr-core 10a7861a, `--switch +D53`): 950 cases in 10⁶.** M1, M2, M2b and M3 are fixed in `Scratch/D53Blocks.lean`: the functions are rejected at the definition, and M3's run. RN is fixed too. Five shapes remain, reproduced in `Scratch/D53Residual.lean`:
   - N1 and N2: a stuck block nested in an arm of another stuck block moves out of a place that the outer refinement did not expose. N2 is M2b one level down.
   - N3: a block returns a borrow into an owner while an arm moves another part of that owner. [Close]'s sealed owner hides the partial move.
   - N4: an arm moves a sibling field into the scrutinee's own sub-place.
   - N5: a block's returned borrow, whose content an arm moved out. The same body returned from a function is rejected.

   Rates in 10⁶ cases on 55977f8e: 15,567 cases. To check that M1 and M2 account for them, a diagnostic patch was applied locally and never committed. It computes `before` per arm, after the refinement, and makes a capture a move whenever the capture itself is in `moved`. On seed 1 (10⁵ cases) it takes the exec findings from 1,608 to 111. All 111 are M2b. The statuses are unchanged (93,656 checked against 93,659). M3 is rare: 4 cases of (ii) in 10⁶. (i) is out of the generator's reach, because the execution oracle skips functions with an `Eq` hypothesis.
6. **The cold reviewers' attacks**, re-found by the extended generator with their switch off (seeds 1 and 3, 2·10⁴ cases each):

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

**Method (ochr-core c469da44, the ledger's 49 rows).**
- Pass 1 ran every row with `--diff --switch X --list`: seed 1, 20,000 cases, 8 workers, with the execution oracle on.
- Pass 2 re-ran the soundness rows that pass 1 missed: seed 2, 100,000 cases. D18 got four more seeds (3–7, 100,000 each).
- A row is *rediscovered* when a non-vacuous finding that the default rules do not show is one of that rule's own failures. Verdicts from D41's confinement check (`[D] erased term borrows/assigns/moves a place`) are the fail-safe working and do not count.
- Row kinds are the ledger's (`lake exe tests`, 996/996 on this head). D19 is listed as "subsumed" there until its new witnesses land; it is counted here as a soundness row.

**Soundness rows: 17 of 20 rediscovered.**

| row switched off | what the fuzzer finds (pass 1 unless noted) |
|---|---|
| P2 (erased terms on a private copy) | `false` 3, `nat` 8: `BoomP2`'s shape |
| P2 without D41 | `false` 106, `nat` 292, `truth` 5 (N1's shape) |
| D18 owners are sets | `nat` 1 in 6·10⁵ (pass 2, seed 6, case 61772): `let a0 = match n0 { Z => x1, S p2 => &n0 }; Id Unit () (*a0 := 0)`, a returned borrow into one of two owners (meta-model C2's shape) |
| D17 [Rec] entry values | `truth` 2,600: non-decreasing recursion proves a false statement |
| D19 [Access] ends loans inside | verdicts 10, `escape` 2. The call-free witness `V` (case 17830, `Scratch/D19Witness.lean`): `let a0 = match n0 { Z => &n0, S _ => &n0 }; *a0 := n0` is accepted without D19, and `V(0)` has no place to write |
| L1 self only as a call head | `truth` 331, Knot's shape |
| L2 no ⊥ argument | verdicts 56 ("no such place"), `conv` 4 |
| C5 blocks move moved borrows | verdicts 6: use after move on the direct path |
| L3 [Rec] in nested functions | `truth` 1,041, KnotL's shape |
| D29 matching ends loans in a neutral | `escape` 16: a returned borrow's hole left in the observation |
| D30 closures by observation | `conv` 914, `nat` 2 |
| D31 no `f` without `by` | `truth` 2,600 |
| D32 pattern writes | `nat` 523, `false` 42, `truth` 5 |
| D37 global generalisation records | `escape` 407 (X3's root) |
| D38 borrow results observed by a write | `conv` 55 (X4) |
| D45 + D42 | `adequacy` 7 (a proof's data field read by the typed run, `⋆` in the machine), `nat` 1 (`⋆` against `I`), besides D41 verdicts |
| D54 class and borrow row in Π-types | `nat` 8: `h0 : Π(z0 : &Nat). P0` at `h0 := HP` observes `0` generically (the call is erased by its codomain) and `1` at the instance (`HP` writes). This is D54's own failure: a writing function passes where one returning types is expected |

**Soundness rows not rediscovered (3), all declaration-level:** D36 (positivity: rejects a malformed `inductive`), D48(2) (`&` only at the top of a declared type: rejects a codomain computing to `&T`) and scrutTyped (rejects a match whose scrutinee's type is a computed family). These check declarations and elaboration, not the two-path property that the naturality oracles test. Reaching them would need the generator to synthesise inductive declarations and dependent parameter types, which it does not. Their soundness rests on the ledger's curated witnesses (`Positivity.Boom`, `BorrowTypes.G`, `ScrutineeTypes.g`). None of the three appeared in 1.2·10⁵ cases (passes 1 and 2).

**Model rows: 2 of 4.** D55 (syntactic sorts): `irrel` 15 (reviewer-4 W2). D45 (subsingleton elimination): `adequacy` 1, a proof's data field borrowed, which the machine cannot reach. Not reached: D44 (an abstract `Π(n : Nat). &Nat` is never generated) and D48(1).

**Cost row, D53 (`--switch +D53 --switch moves`): confirmed as cost.** There are no new findings. 235 statements and 5,853 sides-as-data-functions are accepted only without moves. These are programs that duplicate non-copy data, which compiled code would have to clone.

**False-lemma and policy rows** (P3 without D41; P1 without D41; D41): no findings. Each only changes verdicts (about 320 statements each way), because D41's confinement is what they remove.

**Completeness rows:**
- **D27:** `irrel` 8, since proof parameters become `σ`.
- **G1:** `escape` 407.
- **capTypes:** 3 renorm errors.
- **D42:** D41 verdicts, and `nat` 1 (`⋆` against `I`).
- **D47:** `adequacy` 1.
- **D52:** `nat` 1 (granularity: a whole pair owner against its fields).
- **D53 (c), `ghosts`:** 7 `exec` findings, which are M1/M2 relabelled ("reading ⊥").
- **D53 (e), `fnRule`:** 18 `exec` findings. These are M1/M2, reached through closures that only the switch-off admits (a library `Clo` whose closure moves its capture).
- **Verdicts only, no findings:** C8, D28, P1, P3, D39, D45 (match by type), D48(3), D49(3), D50 on, confineBodies, D56, D58, D59.

**Earlier tallies.** On 84470253 (before the pre-pass, with the D35 rows) it was 18 of 23. The five misses were D18 and D35, which are rare shapes, and the same three declaration-level rules. The D35 rows were deleted with the erasure pre-pass. P2 alone, which was then mislabelled as completeness, is now a soundness row with its own witness (`BoomP2`).

**D53 rows on 55977f8e** (D53 on by default there; seed 1, 20,000 cases, `--diff --list`, execution oracle on):

| switch off | new findings | statement verdicts changed | sides accepted as data functions (`@XFLIP`) | reading |
|---|---|---|---|---|
| `moves` (runtime reads copy) | none | 0 | 4,743 cases gain sides, 5,991 sides in all; none lose one | **cost**, as classed. Without moves the checker accepts code that duplicates non-copy data, which compiled code would have to clone. Every oracle still agrees, and the M1/M2 findings disappear with the moves themselves. |
| `ghosts` (a move leaves ⊥) | the M1/M2 cases again, relabelled ("reading ⊥" for "moved out (D53)"), 10 | 0 | 10 cases lose a side; none gain one | **completeness**. An erased read of a moved place (a `J` endpoint, an `Id` side) is rejected. Nothing new is accepted. |
| `fnRule` (a call consumes its function; closures may move captures out) | none | 0 | 26 cases gain a side, 24 lose one | **completeness**, both ways. Without the rule, functions are used once each (Rust's `FnOnce` reading). A function parameter called twice is rejected (`h(&n1); h(&n1)`). A closure whose body moves a capture out is accepted, but the call consumes it, so it cannot run twice. Both readings are consistent, and no oracle separates them. |

Probe for the `fnRule` row: `def F (n : Nat) : Nat := let f = (λ (u : Unit) : Nat => n); let a = f(()); f(())`. With the default rules, the closure's body is rejected ("moves a captured value out … clone it"). With `fnRule` off, the second call is rejected ("f was moved out"). Either way the double move is refused, at a different point. This is a hand probe, not a fuzzer finding.

### v2.5 At-scale runs

| checker | seeds | cases | time | value disagreements | notes |
|---|---|---|---|---|---|
| ochr-core 10a7861a (M1–M3/RN fixed), `--switch +D53`, execution oracle | 1–10 | 1,000,000 | 656 s, 12 workers | **0**; **950 `exec`** | D53 acceptance still fails, on five residual shapes N1–N5 (§v2.3 item 5); no fail-safe classes; E 59 |
| ochr-core 10a7861a, default rules (D53 off), execution oracle | 1–10 | 1,000,000 | 820 s, 12 workers | **0**; **0 `exec`** | identical to c469da44 in every count |
| **ochr-core c469da44 (D53 off by default), default rules, execution oracle** | 1–10 | 1,000,000 | 1,165 s, 12 workers | **0**; **0 `exec`** | no fail-safe findings: R1–R8 all fixed; E 65 (1 vacuous) |
| 95da7c12 (D53 on, D59), default rules, execution oracle | 1–10 | 1,000,000 | 815 s, 12 workers | **0** (plus 15, R6); **15,567 `exec`** | the same counts as 55977f8e: D59 changes nothing the fuzzer observes |
| 95da7c12 with `moves` off (the sanity baseline), execution oracle | 1–10 | 1,000,000 | 728 s, 12 workers | **0** (plus 15, R6); **0 `exec`** | no R8: the pre-pass assertion runs only under the default configuration (`prePassAssert`). What R8 hides with the assertion off is 12 `renorm: no such place` (2 vacuous) and 1 `[Read]` renorm |
| 55977f8e (D53 on), default rules, execution oracle | 1–10 | 1,000,000 | 1,002 s, 12 workers (machine load ≈ 18) | **0** (plus 15 conjunct-order differences, R6); **15,567 `exec`** | D53 acceptance fails: M1/M2/M2b/M3, §v2.3 item 5; R8 still present |
| ff6b634a (R2, R3, R7 fixed; erasure pre-pass), default rules | 1–10 | 1,000,000 | 788 s, 12 workers | **0** (plus 14 conjunct-order differences, R6) | R2/R3/R7 gone; a new fail-safe class R8 from the pre-pass |
| 84470253 (the batch), default rules | 1–10 | 1,000,000 | 661 s, 8 workers | **0** (plus 14 conjunct-order differences, R6) | fail-safe classes only, table below |
| 658cc108 (recCands fixed) | 1–10 | 1,000,000 | 491 s, 16 workers | 0 | before the reviewer shapes were added to the generator |
| 96d788a1 with the fix as an opt-in hook | 1–10 | 1,000,000 | 536 s, 16 workers | 0 | the same counts as the row above |
| 96d788a1, unpatched | 11–12 | 100,000 | 56 s, 16 workers | – | 351 `truth` findings, all F-v2-1 |

**Main run statuses (84470253).** 936,320 cases were checked. In 49,375, the default rules reject the generic statement; in a sample of 400 cases, 12 of the 16 rejected or unresolved ones were the reviewers' attack shapes, which only a switch-off makes live. In 14,305, the case does not resolve, mostly an attack template that the default rules left out. No crashes.

| class | findings in 10⁶ on 84470253, non-vacuous (vacuous) | on ff6b634a | on 55977f8e (D53) | on c469da44 (D53 off) |
|---|---|---|---|---|
| R2 a λ in a block's arm captures a borrow | 3,405 (500) | 0 (fixed) | 0 | 0 |
| R3 conversion runs a block's function generically | 160 (8) | 0 (fixed) | 0 | 0 |
| R7 `symm` in an unreachable branch | 34 (1,850) | 0 (fixed) | 0 | 0 |
| R6 conjunction order | 14 (1) | 14 (1) | 15 (1) | 0 (fixed, 1678d2a2) |
| E arm-local value in a block's inferred type | 92 (2) | 65 (1) | 68 (3) | 65 (1) |
| R1 residual (an owner reached through a returned borrow) | 1 (0) | 1 (0) | 0 | 0 (fixed, 06da7a2c) |
| R4, R5 | 0 | 0 | 0 | 0 |
| R8 the erasure pre-pass's INTERNAL assertion (new) | – | 2,235 (339) | 2,344 (362) | 0 (fixed) |
| vacuous: `adequacy: stuck (escaped to the top)` (a `J` cast or zero-arm match stuck under a `False` hypothesis, run by the untyped machine) | 0 (27,938) | 0 (28,039) | 0 (28,083) | 0 (28,039) |
| D53 `exec`: an accepted function goes wrong when run (M1, M2, M2b, M3; §v2.3 item 5) | – | – | 15,567 cases (the two `conv: error` cases are among them) | 0 (D53 off) |

On 55977f8e the statuses were 936,239 checked, 47,833 rejected and 15,928 unresolved, with no crashes.

### v2.6 The fail-safe classes, one sentence each

Each class has a true statement that the checker rejected, in `lean/Scratch/` (`lake env lean Scratch/X.lean`, all "as expected"). On c469da44 the fixed classes' statements are accepted.

- **R1 (fixed: ef1195ff, and the residual by 06da7a2c): an untyped `Id` owner holding a loan.** Re-normalising a sealed program that forms an `Id` about a cell it has lent out failed to type the cell (16,551 cases in 10⁶ on 658cc108; `V2Classes.R1s` is accepted now). One residual case in 10⁶ on 84470253 remains, where the owner is reached through a returned borrow: `R1Residual.Split` is a true statement, proved by splitting, that was rejected with "cannot infer the type of the value loan_ℓ", and is accepted since 06da7a2c.
- **R2 (fixed by ff6b634a): a λ in a stuck block's arm captures a borrow on re-normalisation.** A block takes a place by `&` when an arm writes it. Two things go wrong:
  - (i) The capture analysis counts a nested λ's write to its own copy as a write by the block (`V2Classes.R2s`: `Id Nat (match n0 { Z => n0, S p2 => let a5 = (λ(y6 : &Nat) : Unit => n0 := 0); n0 }) n0`).
  - (ii) A λ that only reads the place captures the block's borrow parameter rather than the value it reads (`EV.ClassE4`: `match q2 { Mk(p5, p6) => let f = (λ(y7 : Nat) : Nat => p5); q2 := (1, 1); f }`).

  Fix: occurrences inside a nested function count as reads of the block, and `capture` captures the place a λ reads (`(*q2).fst`, by value), not the root variable.
- **R3 (fixed by ff6b634a): conversion runs a block's function at a generic call.** A block formed inside an arm reads pattern sub-places (`x0.1`, `(*q0).fst`) that exist only under that arm's refinement. D30's conversion observes such a function at a fresh generic argument, where the sub-place does not exist, and `convFn` lets the error escape instead of answering "not convertible" as `convPi` does (`V2Classes.R3s`).
- **R4 (fixed by 84470253/ff6b634a): a call of a sealed function in untyped code.** A block whose arms return λs closes off to a sealed function. Calling it during re-normalisation needs its Π-type for [Close]'s row, which is not recorded It was 23 cases in 10⁶ on 658cc108 and 0 since.
- **R5: arm types formed under different refinements** (1 case in 10⁶, 658cc108). Two arms' Π-types capture a place holding a sealed program that the arms' refinements made different, so D48(3)'s comparison finds `U(⌈…0…⌉) ≠ U(⌈…S σ⌉)` although both are `Prop`.
- **R6 (fixed by 1678d2a2: owners in a canonical order, writes first, by first occurrence): `Id`'s conjunction order is not stable under closing off.** `Id` lists the observed owners in the order of Ω, and a closed-off block orders them by its captures. `And` is not commutative by conversion, so a true statement proved by splitting is rejected (`R6Order.Direct`). With pairs, `Eq` at `Nat × Nat` splits by injectivity, so this shows even at ground instances (`False ∧ (False ∧ False)` against `(False ∧ False) ∧ False`). Fix: order the footprint canonically (by first occurrence in the statement, or by parameter position), not by Ω.
- **R7 (fixed by ff6b634a): `symm` in an unreachable branch.** `symm h` (and `trans`) needs `h`'s type to be an equation or `True`. In a branch whose refinement makes the hypothesis `False`, the branch is unreachable, but `symm h` is a type error (`R7Symm.Split`), while the plain `J` along `h` is accepted there.
- **E: an arm-local abstract value in a block's inferred type (not unsound).** A block's result type is read off the first arm, under that arm's refinement. When it is a Π-type that captured the scrutinee, arm-local values (`Mk(σ3, σ4)`) sit in its `where κ` captures (`EV.ClassE`, `ClassE4`). Untyped runs never read a block function's codomain. A stale type mentions only fresh σs that nothing else shares, so it can make a conversion fail, never succeed wrongly. It needs the block to take the place by `&` (some arm writes it) for its sealed program to reach an observation. On 84470253 it arrived with R2 (ii); since R2 is fixed it stands alone (65 cases in 10⁶ on ff6b634a, `EV.ClassE4`).
- **R8 (new on ff6b634a, fixed by the pre-pass fixes merged in 9fb58523): the pre-pass misreads a closed-off block's proof parameter.** When a stuck block captures a proof-function parameter, the block function declares that parameter in the captured form `(Π(z0 : &Nat). ⊤ : Prop)`. The pre-pass does not read that ascription as a proof, so it classifies a call through it as data while the machine (correctly) erases it, and the pre-pass's own assertion fires: "INTERNAL [pre-pass] …: erased/proof = (false, false) by its declared type, (true, true) after running". `R8PrePass.OnNat` is a true statement rejected by it: `(n : Nat) (h2 : Π(z0 : &Nat). ⊤) : Id Nat (match n { Z => 0, S p => h2(&p); 0 }) 0`, proved by splitting `n`. Variants: a captured λ returning a proof; and a proof `h : ExN` whose data field an arm writes, which makes the block capture the proof by borrow (`h3 : &ExN`, a borrow of a proposition) and the two readings disagree the other way. Fail-safe; 2,235 cases in 10⁶.
- **RN (D53): a data function's split re-runs a type's sealed program as code.** A proof's split refines its goal erased. A data function's split refines the stored types of its parameters at runtime depth, so a sealed program inside a hypothesis's type is re-run with reads that move. `D53Renorm3.DataSplit` is rejected with "n was moved out": `(n : Nat) (h : Id (Nat × Nat) (match n { Z => (n, n), S p => (p, p) }) (match n { Z => (0, 0), S p => (p, p) })) : Nat := match n { Z => 0, S _ => 1 }`. The same statement as a proof (`PrfSplit`) is accepted. Fail-safe. The fuzzer cannot measure its rate. Its statements are types, and `--runtime-refine` (refining them at runtime depth) reports about 15% of cases, which is mostly the artefact of re-running observations that the checker would refine erased.
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
- Runtime code, for D53, only through the execution oracle. That oracle never runs a function with a hypothesis other than `⊤` or with a function parameter, so the `J` casts, which all sit under an `Eq` hypothesis, are never run at runtime depth (M3 (i) was found by hand).

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
