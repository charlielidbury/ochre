# Reviewer 7: cold review, from the Rust-verification side

Paper: "Proving the Program You Run" (ochr/core/paper, as of ochr-core c49e4f36). Artifact: `ochr/core/lean` (checker, fuzzer), `ochr/core/meta-lean`, `competitors/`. Everything below was re-run on c49e4f36 in a private detached worktree; no file of the artifact was changed.

## 1. Summary

Ochr is a core calculus that puts Aeneas's symbolic borrow semantics (LLBC values with borrows and loans) inside a Lean-style dependent type theory, so that definitional equality runs in-place code on symbolic inputs.
A call that gets stuck on an unknown value is "closed off": its result and the final contents of the places it borrowed become sealed source programs, which play the role of Aeneas's backward functions, with a loan standing for the final value of a returned borrow.
`Id A t u` compares two computations by their result and by the final contents of the places they may write (read off the syntax and traced to their owners), and computes to ordinary equations; induction hypotheses are typed in the caller's environment, so the frame argument is done by evaluation.
The evidence is a Lean reference checker (1,013 verdicts, a counterfactual ledger, a differential fuzzer), a mechanisation of an earlier first-order fragment, and two case studies: a hash map against Aeneas's F\* development (37% fewer lines, 11% fewer tokens, longer proofs) and an in-place quicksort against Verus (8 times the lines).
Consistency, the agreement of the two evaluation paths, and adequacy are conjectures, and the checked semantics copies where the compiled program is meant to move.

## 2. Strengths

- **A genuinely new idea for Rust verification.** Doing Aeneas's functional translation lazily, inside conversion, in the source language, and only as far as an equation needs, is new to me. `AddMZero` by bare structural recursion, and `AddSub`, where a lemma about the pure `Add` discharges a precondition about in-place mutated state with no bridging lemma, are striking demonstrations.
- **Loans as variables bound by their borrow** make returned borrows cheap. The hole of a borrow-returning stuck call is just a loan, and the ordinary [End] rule fills it. This is a clean way to present the neutral form of Aeneas's region abstraction for one call.
- **Owners and the IH at the call site** (§2.4, §5) turn the frame argument into evaluation. The requirement that every owner of a hole be observed (Fig. 8, property 6) is correctly motivated.
- **The model constraint on returned borrows is identified correctly.** Rust's `'static` borrows break injectivity of backward functions, and the paper rules them out explicitly (D44, the definition of the relation R, §10). Most papers in this area miss this.
- **Unusually honest scope statements.** Fig. 1 (what of Rust is covered), Fig. 9 (status of each property) and §10 state limitations plainly.
- **A strong artifact discipline.**
  - Every printed program is a test. I spot-checked 20 of them, and all 20 are in `Ochr/Examples`.
  - Every verdict is asserted, with counts per file.
  - `lake exe tests` gives 1013/1013 as expected. The ledger has exactly the 49 rows by class that Fig. 10 claims.
  - The fuzzer is a real differential tester. A 5,000-case default-configuration run (seed 11) gave no value or execution disagreement.
  - The mechanisation builds, with exactly one `sorry`, the termination statement at `GuardTerm.lean:416`, as claimed.
- **The size table reproduces.** An independent recount with my own tokenizer lands within about 1% of every cell in Fig. 11 (details in §4.5).

## 3. Weaknesses, ranked by severity

### W1. The program that is verified is not the program that would run (title, abstract, §1.5 Fig. 1 "Moves", §10 "The checked machine is not yet the compiled program")

The title promises "the program you run". The checker's default semantics copies every borrow-free read, which Rust (and the intended compilation) does not. The paper says a move semantics exists "behind a switch", is "validated by the fuzzer's execution oracle" and "will become the default" (§10). On the submitted artifact:

- **The case studies do not check under moves.** With `{ d53 := true }`, the verdicts that come out as expected are:

  | Block | As expected with moves on |
  |---|---|
  | Arrays | 20/26 |
  | ArrayLemmas | 7/14 |
  | Quicksort | 29/77 |
  | HashMap | 13/41 |
  | HashMapLookup | 9/46 |
  | HashMapLength | 9/20 |
  | HashMapResize | 10/79 |

  The roots are in the programs themselves, not the proofs:
  - `Read`'s model `Nth(E, n, *s, i, h)` moves out of `*s` ("a borrow ends while its content is partly moved out").
  - `WithSplit`, `ModGo` and `BInsert` use a `Nat` twice ("[Read] n was moved out").
  - Everything else cascades from these. The verified quicksort and hash map are therefore programs whose meaning under the intended runtime semantics is "rejected".
- **The move semantics itself is not yet sound.** See §4.1: an accepted program goes wrong at every instance. The fuzzer shipped in the artifact finds 6 execution-oracle failures in the first 3,000 cases with `--switch +D53 --seed 7`, such as case 1126: "symbolic path: runtime run errors: [D53] a borrow ends while its content is partly moved out".
- **Two other constructs mean something different from what the same Rust code means** (§4.2):
  - Closures reset their captured state on every call, where Rust's `FnMut` accumulates. `CloMutEq` proves that calling a closure that increments its capture twice gives `(1, 1)`. This holds with D53 too, so "closures follow Rust's `Fn`" (§10) is not accurate.
  - Pattern variables are places, not bindings. `PVNew` reads the new predecessor after the scrutinee is overwritten, a program rustc rejects.

Fix:
1. Make D53 the default, and fix the [Close] gap of §4.1.
2. Re-check both case studies with moves on, inserting `clone` exactly where Rust would, and report how many clones that takes and the new sizes.
3. Say in §2 that pattern variables are places and that closures are snapshots.
4. Until then, weaken the title and abstract: what is verified is a copy-semantics program with Rust-style mutable borrows, not the program that runs.

### W2. The evaluation does not carry the thesis, and the prose disagrees with the table (§8.2, §8.3, Fig. 11)

The thesis (§1.1: one development beats spec + implementation + agreement) rests on one case study, the hash map. There, Ochr's property proofs are longer and the token margin is small and sensitive to counting choices.

- **The prose contradicts Fig. 11.**

  | Claim in the text | Place | What Fig. 11 gives |
  |---|---|---|
  | Property proofs are "1.25 times" Aeneas's in tokens | §8.2 "What is written" and "What is still costly" | 14.7/12.5 = 1.18 |
  | The first version's proofs were "1.8 times as long" | §8.2 | 20.8/12.5 = 1.66 |
  | Model plus agreement are "a quarter" of Aeneas's tokens | §8.2 | (3.0+2.7)/19.7 = 29% |

  1.25 and 1.77 both match an Aeneas property column without the `.fsti` statements (11.7k tokens), so this looks like prose left over from an older table.
- **Other factual slips:**
  - "`Insert` doubles the table once the entries outnumber the buckets" is off by one. With n+1 buckets, `Insert` resizes when `Lt(n, len)` (`17HashMap.lean:303`), that is, when the entries equal the buckets. The artifact's `RunLayout` resizes a 2-bucket map on its second insert.
  - Verus's quicksort is not "loop-based". Its partition is a `while` loop, but the sort recurses (`decreases arr.len()`, `competitors/verus/src/main.rs:120`).
  - Quicksort "checks … in about 0.2 s". `lake exe tests` reports 372 ms for the `Quicksort` block alone.
- **Counting choices that favour Ochr:**
  - 172 lines / 1.4k tokens of Aeneas's `Properties.fst` are dead code: never referenced, no SMT pattern, some marked "TODO: remove?" (e.g. `:919`, `:1039`) or "I finally didn't use" (`:1433`).
  - Removing them, Ochr is 32% smaller in lines but only about 5% smaller in tokens, and its proofs are 1.29 times Aeneas's.
  - For quicksort, the permutation machinery (`Count`, `CountJoin`, `CountSet`, `CountSwapHead`, `CountSwap`, `SwapS`: 126 lines / 1.3k tokens, `16Arrays.lean:536–675`) sits in the uncounted "array library". Verus's own `perm` and `lemma_swap_preserves_multiset` are counted.
- **Choices that favour Aeneas** also exist: 127 pragma lines are excluded, and 9 termination measures are counted as 9 lines rather than 35. I mention them for balance.
- **The programs differ in ways that matter to a Rust reader:**
  - Ochr's values are `Nat`, not a type parameter.
  - The table is a list of buckets, with a linear index that saturates at the last bucket, so there is no bounds proof.
  - The bucket index `k mod (n+1)` is unary recursion on `k`, so O(k) per operation. The paper does not say this.
  - The load factor is fixed at 1, there is no overflow, and `GetMut` needs a proof that the key is present.
- **The baseline is the 2022 F\* development**, verified with Z3. Aeneas has since moved to Lean, with a `progress` tactic and a Lean hash map. Ochr is closest to that, and it would be the fair comparison for a 2026 paper.

Fix:
1. Correct the three ratios and the three slips above.
2. Report the sensitivity of the token margin: without the dead code, and with the `Count` machinery counted in the quicksort row.
3. Compare against the current Aeneas Lean hash map, or justify the F\* baseline.
4. Add a second thesis case study that exercises returned borrows through data structures Aeneas also verifies (e.g. `list_nth_mut`, or a linked-list `get_mut`/`push_back`).
5. Drop "first version" rows from Fig. 11: they are history, not evidence.

### W3. None of the properties of the calculus as presented is proved (§7, Fig. 9)

- **What is mechanised is a different system.** The mechanisation covers version 1.3 of the rules, a first-order fragment without types, erasure, closures or stuck blocks (§7.3). But nearly all the soundness rows of Figs. 8 and 10 concern exactly those features. So the mechanised theorems (frame, `close_*`, `exec_wf`) do not apply to the machine the checker implements:
  - [Close] as in Fig. 14 now has no Unit row;
  - stuck blocks close off with Rust-style captures;
  - closures capture.
- **The rest is conjecture:**
  - consistency (Conjecture, §7.1);
  - stability (Conjecture 3), which the paper admits is "an enumeration of the decisions we know of, and each earlier version of it missed one";
  - naturality and adequacy (property 9);
  - termination of checking, which is open.
- **The design history shows where the risk lies.** Fig. 8 lists about twenty side conditions, each found by a counterexample, several of them only by external reviews. For a calculus paper at POPL/ICFP, this reads as a design that has converged empirically, not a result.

Fix:
1. Extend the mechanised frame and close properties to the current machine's first-order borrow fragment, with stuck blocks and returned borrows, still without types. That is where the Rust-facing claims live.
2. Mechanise adequacy of `Id` for that fragment: an `Id` computed on abstract inputs holds on every concrete input.
3. Otherwise, state in the abstract that no property of the presented calculus is proved.

### W4. The borrow model is a narrow fragment of `&mut`, and checking it is not modular (§1.5, §4, §10)

- **Coverage is narrow.** Ochr has:
  - no shared borrows, the most common Rust borrow;
  - no loops;
  - no borrows in data (no `Option<&mut T>`, `iter_mut`, `split_at_mut` as a pair);
  - no generic `&A`;
  - one region per call.

  Sealed programs "play the role of Aeneas's backward functions" only for this fragment. Aeneas itself has since been extended to loops (work the paper cites in §9). The abstract should say "for a first-order fragment without shared borrows, loops or borrows in data" next to the claim.
- **Borrow checking by running is not modular.** Whether a caller checks depends on the callee's body and on which inputs are concrete (§1.5 admits this).
  - Callee-dependence: a function that returns a borrow into its first argument keeps its second borrowed only if its body is stuck.
  - Naturality is lost: `PickEarly` (§7.2) is valid at every concrete `n` but rejected symbolically.
  - For a Rust reader, this unpredictability is a bigger cost than the paper acknowledges. Changing a callee's body can break its callers' borrow checking, not only their proofs.
- **Verification is not modular either.** Conversion unfolds callees, and the only way to hide a body is an axiom (§10 "Opaque definitions"). As far as I can see, the checker has no top-level bodiless definitions; the only opaque functions are function parameters (`09Functions.lean`).
- **Moves out of a borrow.** In the default configuration, `let v = *x` copies out of a borrow. Rust forbids moving out of `*x` (E0507), except by `mem::replace`-like patterns.

Fix:
1. State the fragment precisely in the abstract and in Fig. 1.
2. Add a paragraph relating Ochr's regions to Rust lifetimes. Which elided signatures does Ochr accept with the same borrow behaviour, and which does it approximate?
3. Give a concrete plan for check-then-hide definitions, and discuss how [Call-type] would then use only the signature.

### W5. The array and quicksort claims rest on an unenforced abstraction (§8.3)

- **The abstraction the paper describes is not enforced.** The paper says "runtime code reaches arrays only through these" eight native functions, and that "a part of an array is borrowed only while a continuation runs" (also Fig. 1). But the representation is ordinary user-matchable data ([K3] in `16Arrays.lean`), and user code can bypass the interface (§4.4):
  - `Suffix` returns a borrow of a sub-slice that outlives any continuation;
  - `TwoParts` holds two disjoint borrows without `WithSplit`;
  - `Rebuild` replaces the representation wholesale.

  A flat-buffer compilation would have to reject or natively implement these.
- **The "fully verified in-place array sort" is a sort of a different kind of program:**
  - it runs on a model made of linked cells of unary `Nat`s;
  - it recurses on fuel;
  - its `WithSplit` model copies `*s` and the two pieces;
  - under moves, its `Read` model would need to clone the whole slice.

Fix:
1. Make the representation abstract outside the library (phase B), or restate the claim: "a sort on a cons-cell model through an interface designed to be implemented by flat arrays".
2. List what compiled code must trust: the natives implement their models, and nothing else touches the representation.

### W6. Presentation

- **A Rust-verification reader is lost from §6.3 to §6.7.** These sections are about erasure decisions agreeing on two paths: the class of Π-types, syntactic sorts, subsingleton elimination. They are needed for soundness, but they read as a changelog, and Fig. 8 is a list of patches. The borrow story (Close, owners, the IH at the call site) is the contribution for this audience, and it is spread across §2.2, §4.4, §5 and §6.1.
- **The Aeneas correspondence is never shown concretely.** Show `add_m` in Rust, Aeneas's `add_m_fwd`/`add_m_back`, and the Ochr sealed programs, side by side, once. Do the same for `tail_m` with its region abstraction.
- **Terminology collides with existing uses.** `Id` (HoTT), "refinement" (refinement types), "observation" (OTT) and "sealed" (sealing in security) all carry other meanings in adjacent communities. Define them early, or rename.
- **The Fig. 11 caption defines four columns for three systems in one paragraph.** Split it into a small legend per system.
- **The abstract is long** and mixes contributions with status. Put the scope sentence first.

### W7. Related work gaps (§9)

- **Prusti's pledges** (Astrauskas et al., OOPSLA 2019) specify what holds when a returned borrow expires. They are the closest specification-level analogue of Ochr's holes.
- **Linear Dafny** ("Linear Types for Large-Scale Systems Verification", Li et al., OOPSLA 2022) verifies in-place code with a functional meaning in one language. It is directly relevant to the "one development" thesis.
- **The current Aeneas Lean backend** (the `progress`-based proofs), and Aeneas's own loop and nested-borrow extensions, as the natural baseline.
- **Lean 4's own imperative verification** (`do`-notation with `Std.Do` and verification condition generation) is a one-language approach inside the same kernel family.
- **Verus's `ghost`/`tracked` modes** are the practical counterpart of Ochr's erasure and ghosts.

## 4. Attempted attacks and their outcomes

All programs were run as `ochr` blocks under `Std` (and `Fixtures`/`ArrayLemmas` where stated) with `lake env lean`, on c49e4f36. "Default" means `Config {}`, and "D53" means `{ d53 := true }`.

### 4.1 Accepted, then wrong at runtime: moving a partly or fully moved borrow into a stuck call (D53 only)

```
def H (x : &Nat) (n : Nat) : Unit := (match n { Z => (), S _ => match *x { Z => (), S q => *x := q } })
def FullMove (x : &Nat) (n : Nat) : Nat := (let v = *x; H(x, n); v)
def PartMove (x : &Nat) (n : Nat) : Unit := (match *x { Z => (), S p => (let v = p; H(x, n)) })
def PartMoveOpaque (g : Π(y : &Nat). Unit) (x : &Nat) : Unit := (match *x { Z => (), S p => (let v = p; g(x)) })
def Thm1 : Id Nat (let c = 3; FullMove(&c, 0)) 3 := refl
```

With D53, all five are **accepted**. At runtime they go wrong:
- `(let c = 3; FullMove(&c, 0))` fails with "[D53] a borrow ends while its content is partly moved out (⊥)".
- `(let c = 3; PartMove(&c, 1); c)` fails with "[Read] (*x).1 was moved out".
- `PartMoveOpaque` applied to `λ(y : &Nat) : Unit => AddM(y, 1)` fails with "[Borrow] (*x).1 was moved out".

So `Thm1` is a false equation about an accepted program: it says `FullMove(&3, 0)` returns 3, but running it errors. Statements read without moving (ghosts), so the statement itself checks.

The same happens through a returned borrow: `let t = TailM(x); let v = *t; H(t, n); v` is accepted.

The direct versions are correctly rejected:
- `let v = p; let y = x; ()` fails with "a borrow ends while … partly moved";
- reborrowing, `let v = p; H(&*x, n); …`, fails with "[Borrow] *x was partly moved out".

Cause: moving a whole borrow whose content holds ⊥ into a call that then closes off skips the partial-move check, and [Close] seals the ⊥ into the fill (`let c1 = S(⊥); H(&c1, σn); c1`). Rust rejects all of these at `let v = *x` (E0507).

Suggested fix: [Call]/[Close] should reject a borrow argument whose content contains ⊥, as [Borrow] does. The fuzzer independently finds the same class: 6 execution-oracle failures in 3,000 cases with `lake exe fuzz --seed 7 --count 3000 --switch +D53` (e.g. `--show 1126`). The paper's "validated by the fuzzer's execution oracle" therefore does not hold of the submitted artifact.

### 4.2 Accepted, and consistent with Ochr's semantics, but not with Rust's (default)

```
def AliasRun (x : Nat) : Nat := (let p = (x, x); AddM(&p.1, 1); p.2)
def AliasRunEq (x : Nat) : Id Nat (AliasRun(x)) x := refl
```
Accepted in the default configuration and rejected with D53 ("[Read] x was moved out"). The default checker proves equations about programs that are use-after-move under the intended compilation.

```
def PVNew (m : Nat) : Id Nat (let c = S m; match c { Z => 0, S y => (c := S (S Z); y) }) 1 := refl
```
Accepted: the pattern variable reads the new predecessor. In Rust, `y` is either a copy (giving `m`) or a `ref` binding, in which case the assignment is rejected.

```
def CloMut (n : Word) : Word × Word := (let c = n; let f = (λ(u : Unit) : Word => (c := Succ(c); c)); (f(()), f(())))
def CloMutEq : Id (Word × Word) (CloMut(Zero)) (Succ(Zero), Succ(Zero)) := refl
```
Accepted with and without D53. A Rust `FnMut` closure returns `(1, 2)`; a Rust `Fn` closure could not assign `c`.

Under D53, 29/77 quicksort verdicts and 41/186 hash map verdicts are as expected (W1).

### 4.3 Borrowing through a branch, then reading a sibling (default)

```
def Sib  (n : Nat) (q : Nat × Nat) : Nat := (let r = match n { Z => &q.1, S _ => &q.1 }; let z = q.2; *r := 5; z)
def Sib2 (n : Nat) (q : Nat × Nat) : Nat := (match q { Mk(a, b) => (let r = match n { Z => &a, S _ => &a }; let z = b; *r := 5; z) })
def Sib3 (n : Nat) (q : Nat × Nat) : Nat := (match q { Mk(a, b) => (let r = match n { Z => &a, S _ => &b }; let z = b; *r := 5; z) })
```
- `Sib` is rejected ("no such place q.1: its path does not exist in σ1"), but only because an abstract pair has no fields until it is split (no η), which is a usability cost.
- `Sib2`, which splits first, is accepted, as in Rust.
- `Sib3` is rejected, as rustc rejects it.

The one-region-per-call incompleteness proper is the paper's own `PickEarly` (§7.2).

### 4.4 Array abstraction (with `ArrayLemmas`, default)

```
def Suffix (m : Nat) (s : &Slice(Nat, S m)) : &Slice(Nat, m) := (match *s { MkSlice(c) => match c { MkC(x, t) => &t } })
def TwoParts (m : Nat) (s : &Slice(Nat, S m)) : Unit := (
  match *s { MkSlice(c) => match c { MkC(x, t) => (let a = &x; let b = &t; *a := 0; Fill(Nat, m, b, 1)) } })
def Rebuild (s : &Slice(Nat, 1)) : Unit := (*s := MkSlice(MkC(7, MkSlice(End))))
```
All accepted. They are sound in the model, but they bypass the eight natives and `WithSplit` (W5).

### 4.5 Recount of Fig. 11

This was an independent recount, with my own comment stripper and a simple tokenizer.

| Row | Paper (lines / tokens) | Mine |
|---|---|---|
| Ochr hash map: spec / implementation / proofs | 144/1.1k, 242/1.6k, 1,308/14.7k | 144/1,125, 242/1,593, 1,311/14,723 |
| Aeneas hash map: model / implementation / agreement / property | 321/3.0k, 210/1.5k, 459/2.7k, 1,680/12.5k | ≈319/2.94k; 201 Rust lines/1,478 + 9 measures; 460/2.67k (the split is judgemental); ≈1,690/12.6k |
| Aeneas trusted model | 82/0.9k | 80/0.88k |
| Aeneas generated F\* | 550 | 555 |
| Verus quicksort: spec / implementation / proofs | 6/0.1k, 36/0.2k, 66/0.7k | 6/79, 33–36/216–226, 66/745 |
| Ochr quicksort: spec / implementation / proofs | 30/0.2k, 52/0.7k, 780/13.1k | 30/229, 52/739, 780/13,082 |
| Array library | 521 | 521/5,161 |

The headline ratios reproduce: 37% fewer lines and 11% fewer tokens (I get 36.6% and 11.7%), 1/8 and 1/13 for quicksort against Verus, 47% statements, and "a fifth shorter with `rewrite`". The prose ratios listed in W2 do not.

`17HashMap.lean` does not use the array library. It uses about 17 uncounted lines of `Std` (`AddM`, `Add`, `AddMZero`).

Coverage of Aeneas's `.fsti` holds, with small differences in form:
- length 0 after `new`/`clear` is not stated; `NewCount` and `ClearCount` state `len = Count(...)` instead;
- `RemoveLen` gives `len' = Pred(len)`, weaker than Aeneas's `len = len' + 1` without the invariant;
- the load factor is a separate `NotOver` rather than part of `Inv`.

The paper's remark that Aeneas's `remove` lemma asserts the invariant of its input (`fsti:255`) is correct.

### 4.6 Attacks that failed (the checker defended)

Each ran in the default configuration unless marked.

| Attack | Program | Outcome |
|---|---|---|
| Project a data field out of a proof | `inductive Ex : Prop := MkEx(w : Nat)`, `def GetW (h : Ex) : Nat := h.1` | Rejected: "no sub-place at type Ex". |
| `split` on a borrow-returning function | `def TailIsZ (x : &Nat) : Id Nat (let t = TailM(x); *t) 0 := split TailM in refl` | Rejected: not stuck on a result of `TailM`. So no σ of type `&Nat` is ever made. |
| `split` on a `Prop`-returning function | `split LeZ in refl` on `Eq Prop (LeZ(a)) ⊤` | Rejected. |
| A borrow type as a type argument | `Wrap((&Nat), …)`, `Id2((&Nat), x)` | Rejected by the parser (`&` is only a type annotation). |
| Write through a borrow after its owner was read | `let r = &x; let y = x; *r := 5; y` | Rejected. |
| Write through a returned borrow after the owner was reassigned | `let t = TailM(&*x); *x := 7; *t := 5; *x` | Rejected. |
| A proposition read through a place, used as a type | `(x : &Box(Prop)) (h : match *x { MkBox(P) => P })`; the same on an owned `Box(Prop)` | Rejected by [D55]. Through a function (`UnboxP(*x)`) it is accepted, consistently, as a proof. |
| Launder a partly moved borrow through a returned borrow (D53) | `let v = p; let y = K(x); H(&*y, n); *y := S v` | Rejected: "a returned borrow's content is partly moved out". |
| Move a partly moved owned value into a stuck call or block (D53) | `CallPart`, `BlockPartBorrow` | Rejected. |

Accepted, and correct:
- `ReadInType`, `let t = TailM(&*x); let h : Id Nat (*x) (*x) = refl; *t := 5`: a type reads on a private copy and does not end `t`.
- `SiblingWrite`: disjoint fields of a matched pair, as in Rust.
- `ViaClo`: an IH through a λ-wrapped callee.
- `ProofKeeps`: a proof call does not consume its borrow.

I also looked for these, without finding a problem:
- injectivity violations for `Π(x : &Nat). &Nat` (every Ochr-definable inhabitant returns a borrow derived from `x`, and a local cannot be lent out past the frame);
- order-dependence of borrow endings with a hole in two fills;
- [Rec] escapes through generalised values, local copies and closures;
- `rewrite` with a non-variable endpoint.

Default-configuration fuzzing (`--seed 11 --count 5000`) found no disagreement, only 133 "adequacy: vacuous stuck" findings of the kind the paper calls harmless.

## 5. Questions for the authors

1. With moves as the default, what do the quicksort and hash map programs look like? How many `clone`s do they need? Under a cost model where a `Nat` clone is O(n), is the quicksort still in place?
2. Why is the 2022 F\* Aeneas development the baseline rather than the current Lean one? What is the Lean hash map's size under your counting rules?
3. Can the mechanised frame and close theorems be restated for the current machine's first-order fragment (stuck blocks with Rust-style captures, the Unit-less [Close])? What is the obstacle?
4. Shared borrows: would `&T` of non-copy data need sealed programs, or would the frame property suffice? How would two-phase borrows interact with [Access] ending borrows on read?
5. Modularity: with check-then-hide definitions, [Call-type] could no longer unfold the callee. Which of the case studies' proofs would survive, and what would the IH at the call site become?
6. Is borrow checking (checking by running) guaranteed to terminate for accepted programs, separately from type checking? Is there an example where adding a lemma call changes whether a data function borrow-checks?
7. The checker has no top-level bodiless definitions; §10 speaks of opaque definitions. Which is it?
8. How large do owner sets and sealed programs get in the hash map proofs? Is checking time polynomial in program size in practice?
9. What does a user see when a proof fails? Are sealed programs printed as the user's own wrappers, as §10 promises, in the checker today?

## 6. What to cut or compress

- **Fig. 8 and §6.7:** keep three representative counterexamples in the body and move the rest to the appendix. The long list reads as a changelog.
- **§6.3–6.6:** compress to one page stating the principle and the four decisions. The detail is in Appendix A.4.
- **The "first version" rows of Fig. 11 and the prose about them:** cut.
- **§7.2's fuzzer paragraph:** keep the numbers, and cut the list of what the fuzzer found about itself.
- **Appendix notes 12–27:** cut or move to the artifact.
- **Use the space for:**
  - a side-by-side Rust / Aeneas / Ochr example;
  - a precise statement of the covered fragment;
  - the move-semantics results for the case studies;
  - a paragraph on non-modularity with a concrete example (a callee edit that breaks a caller's borrow check).

## 7. Score and confidence

**Score: C (weak reject).** The idea is novel and could matter for Rust verification. But at present:
- the metatheory of the presented calculus is conjectural;
- the verified programs do not check under the semantics they are meant to run with, and that semantics has an accepted-then-wrong program;
- the thesis rests on one comparison, which has prose errors and a small, counting-sensitive margin.

**Confidence: high** on the borrow and Rust-verification side, and on the evaluation; medium on the type-theoretic side (erasure, sorts), which I probed but did not try to break systematically.

**What would move my score up one notch (to B):**
1. Make moves the default, fix the [Close] partial-move gap (§4.1), and show both case studies checking under moves, with the clone count reported.
2. Correct the §8.2 ratios and slips, add the sensitivity analysis (Aeneas dead code; `Count` counted for quicksort), and either compare with the current Aeneas Lean development or justify the choice.
3. Mechanise the frame property and the `close_*` equations for the current machine's first-order borrow fragment, including stuck blocks and returned borrows, so that the borrow-side claims rest on a proof about the rules the paper presents.
