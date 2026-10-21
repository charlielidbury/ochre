# 11. Hashmap ergonomics: surface sugar and a central Word library

Lane: `hm-ergo` (fresh agent, worktree `ochre-hm-ergo`, branch `hm-ergo`). Written by team-lead on 2026-10-21 from the user's review of `17HashMap.lean`. Phase 1 is §1–2. Phase 2 (§3, the hashmap rewrite) waits for the user's decision on §3.2.

## 1. Surface sugar (user item 4): no rule changes

Each sugar is a desugaring in the surface elaborator (`Surface.lean` / `Notation.lean`). RULES gets no new rule. If any sugar turns out to need a rule change, stop and report.

1. **Destructuring `let` for any single-constructor inductive.** `let C(x̄) = e; u` means `match e { C(x̄) => u }`.
   - It is allowed only when `C`'s inductive has exactly one constructor. Otherwise the error names the type and says to use `match`.
   - Patterns follow match arms: `_` ignores a field, and fields are bound by position.
   - The existing `let ⟨…⟩ = p` (And) and `let (a, b) = p` (Pair) become instances of this; keep both spellings.
   - Example: `let HM(n, len, slots) = *hm; …`.
2. **`if`.** `if c { a } else { b }` means `match c { true => a, false => b }` on Std's `Bool`.
   - `else if` chains are allowed.
   - `else` may be omitted only when the then-branch has type `Unit`, and then means `else { () }`.
   - Choose the concrete syntax to fit the existing grammar (braces, as in `match`), and record the choice in the book.
3. **`match` on any expression.** `match E { … }` where `E` is not a place means `(let x = E; match x { … })`, with a fresh `x`.
   - When `E` *is* a place (`x`, `*p`, `p.f`, …), nothing changes: a place is matched in place, and its arms bind sub-places. Rewriting it to a `let` would move it.
   - Check that proofs keep their power: matching a variable whose content is a stuck call generalises that call and splits on it, as matching the place did.

Tests for each:
- accepted programs;
- the error cases (multi-constructor `let`, and `if` on a non-`Bool`);
- a proof that splits through `match F(x) { … }`;
- a run (`Id … := refl`) showing the desugaring computes as the hand-written form.

Then update:
- OCHR_BOOK §3 (syntax table) and §8 (proofs);
- the paper's surface-syntax description, if it lists the forms (keep the body to 25 pages, with the Conclusion ending on page 25);
- the bench GUIDE.

## 2. One central Word library (user item 3)

Arithmetic and comparison on `Word` are defined several times:
- `17HashMap.lean`: `EqB`, `Lt` (Bool), `ModGo`, `Idx`, `Pred`, `WAdd`, `W`;
- `16Arrays.lean`'s `Index` block: `Le`/`Lt` (Prop), `LeRefl`/`LeStep`/`LeTrans`/…, `Sub`, `WAdd`, `W`;
- possibly `18DependentFields.lean` and the bench packages too. Grep for them.

Put one copy of each in `00Std.lean`, as a `Word` section, or as a new library block that every example `uses`:
- Bool comparisons;
- Prop orders and their lemmas;
- arithmetic;
- `W(n)` numerals.

Then delete the duplicates and migrate their users. Names must not clash. Where two files define the same name differently (for example `Lt` as a Bool in one and a Prop in another), pick distinct names, such as `LtB` for the Bool and `Lt` for the Prop, and migrate.

Bench packages:
- check whether their provided headers duplicate these definitions;
- if they `use` Std, they should use the central copy too;
- the sandboxes must still build, with each skeleton failing only on its named holes.

## 3. Phase 2, after the user decides §3.2: rewrite `17HashMap.lean` (user items 1, 2, 5)

Do not start this phase until team-lead says go.

1. **Generic and built on the libraries.**
   - Values generic in `V`, with keys `Word`.
   - Buckets are Std's `List` of a key–value pair; the table is `Array(…, cap)` from `16Arrays`; `GetMut` comes from the library.
   - Delete the hand-rolled `Opt`/`Bucket`/`Slots`/`Slot`/`BGetMut`/`EmptySlots` and use the generic ones.
   - The new sugar should be used throughout.
   - **The representation, pending the user's decision (user item 6: "could hashmap be defined in terms of `Array`, so HashMap<V> = Array<List<V>>").**
     - Buckets must keep their keys: `List(Pair(Word, V))`.
     - A fixed-capacity map could be just the type function `HashMap(V, cap) := Array(List(Pair(Word, V)), cap)`.
     - A *resizing* map changes its capacity, and a borrow fixes its type, so it needs the Σ shape: `HM(n : Word, slots : Array(List(Pair(Word, V)), Succ(n)))`.
     - Dropping the `len` field removes the `len = Count(slots)` invariant entirely. But it makes `Len` O(cap), and it makes **`Insert` O(cap)** too, because the resize check reads `len` on every insert. Keep `len` (team-lead, 2026-10-21), unless the resize trigger changes, for example to the length of the bucket just inserted into. That would be a different structure from Rust's and Aeneas's, and it would weaken the load-factor theorem.
2. **The invariant in the type, pending the user's decision.** The option: `HashMap(V) := HM(n, len, slots : Array(…), inv : Inv(…))`, a dependent proof field (D64). This is possible since D64-amended (8e036130) lets a proof field be re-established while a borrow (`get_mut`'s `&V`) is live. See the `CellGet` test in `18DependentFields`.
3. **Shared by the other hashmaps.** Consolidate the smaller hashmaps in `16Arrays` and `18DependentFields` onto this one, or delete them, if they only duplicate it.
4. **The paper.** Re-measure the paper's case-study numbers (lines, check time, the Aeneas comparison table) and update §8 and `notes/hashmap-case-study.md`.

## Landing (each phase, FF-CAS, by you)

- **Rebase onto `origin/ochr-core`. Never create a merge commit.** Then, in `/home/charlielidbury/repos/ochre-ochr-core`, run `git pull --ff-only origin ochr-core && git merge --ff-only hm-ergo && git push origin ochr-core`. Retry from the rebase if that fails. Don't touch the user's uncommitted files there.
- Acceptance:
  - `lake build`, `lake build tests fuzz` and `lake exe tests` are green;
  - fuzz statuses are unchanged (default family, seed 1, 2·10⁴ cases, at most 6 workers);
  - every program printed in the paper checks (the paper sweep);
  - the Conclusion still ends on page 25 (check that page, not the total);
  - all four bench sandboxes build, with their holes named.
- Land §1 and §2 as separate landings if that is easier; §1 is independent.
- Pin heavy commands with `taskset -c 0-14`, and run one `lake build` at a time.
- Commit and push the branch at checkpoints, with detailed messages. Never `git stash`.
- Plain language, and no bare internal ids.

## Addendum (2026-10-21): §1 and §2 run in parallel, and §2 widens to de-duplicating Examples

The user asked: "across the whole Examples folder, are there other examples of duplication (like we saw with word) which can be removed?" and "surely 1. and 2. can be done in parallel?".

- **Lanes.** §1 stays with lane `hm-ergo`. §2 goes to lane `hm-lib` (worktree `ochre-hm-lib`, branch `hm-lib`).
  - `hm-ergo` adds its sugar tests in their own block, doesn't sweep existing examples to use the sugar, and edits only book §3/§8.
  - `hm-lib` owns every other edit to existing example files.

### The duplication survey (team-lead, a script over `Examples/*.lean`)

877 declared names, 61 of them declared in more than one file. Most of the 61 are throwaway test names (`F`, `G`, `P`, `T`, `Q`, …) in self-contained feature tests, and are not duplication. The library-like duplicates are:

- **Word/Nat arithmetic and orders:**
  - `Le` (04ClosingOff, 07Recursion, 08CaseSplits, 12CurrentState, 16Arrays);
  - `Lt` (04, 10Inductives, 16, 17HashMap);
  - `Sub` (08, 16), `WAdd` (16, 17), `W` numerals (13Erasure, 16, 17), `Pred` (01Numbers, 17), `Count` (16, 17, Editor);
  - `Dec`/`LeDec` (04, 16);
  - `EqB` and `ModGo`/`Idx` (17).
- **Option-like and empty types:**
  - `Opt` (08, 17, 18DependentFields; Std has none);
  - `IsSome`/`IsNone` (17, 18);
  - `Void`/`absurd`/`absurdV` (10, 11Propositions, 18);
  - `Box`/`List`/`Pick` redeclared in 08 and 10 beside Std's.
- **Three hashmaps:** `16Arrays` (`HashMap`, `Insert`, `GetMut`, `Count`, …), `17HashMap`, and `18DependentFields` (`Table`, `Resize`, `Clear`, …). Consolidating them is phase 2 (§3.3). `hm-lib` leaves the hashmap code itself alone, apart from swapping its arithmetic and `Opt` for the central ones.
- **An older copy of the arrays model in 08CaseSplits:** `Slice`, `SliceOf`, `Cells`, `CellsEnd`, `Cell`, `JoinS`, `AllGe`.
- **Others:** `Swap` (11, 15BorrowTypes, 16, Units), `Insert`/`AppendM` (08, 10), `Nth` (16, 17), `GetMutRead` (16, 17).

### The rule for `hm-lib`

- **Centralise and migrate** a definition that is used as a helper (arithmetic, orders, decision types, `Opt`, `Void`/`absurd`, numerals, generic containers): `Std` (or a library block every example uses) holds one copy, and the duplicates are deleted.
- **Keep** a definition that is the *subject* of its test, such as a test about how a user-declared `List` or `Opt` behaves, or a minimal regression witness whose meaning depends on its own definitions. Examples are 08CaseSplits' `BoomLeak` with its own `Slice`, and the feature tests in 01–15 that deliberately don't `use Std`. Each kept duplicate gets a one-line comment saying why.
- **Report** the list of what you centralised, what you kept and why, and the line counts before and after for each file.
- **Bench packages** use the central copies where they `use` Std. Their sandboxes must still build, with each skeleton failing only on its named holes.

## The final Examples layout (user-approved, 2026-10-21)

This supersedes "Std" in §2 and the Addendum. The user's words:
- "we should instead just delete 00Std.lean and move words into 00Word.lean etc."
- "is it perhaps worth getting rid of the number prefixes? … 00Array.lean -> Array.lean"
- on per-block declaration counts: "truncation isn't really worth catching".

**No number prefixes.** Imports become `import Ochr.Examples.Word`. Reading order lives in a new `Examples/README.md`: the library, then the tour in its old order, then the case studies.

**The library.** One block per file, named for its topic. Each block `uses` only what it needs. The graph is a DAG with no root.

| File | Block | Contents | Uses |
|---|---|---|---|
| `Bool.lean` | `Bool` | `Bool` | — |
| `Logic.lean` | `Logic` | `Dec(P, Q)`, `Void`/`absurd` (`False`/`True`/`And` stay in the built-in Prelude) | — |
| `Nat.lean` | `Nat` | `AddM`, `Add`, `AddMZero`, `TailM` | — |
| `Word.lean` | `Word` | `Word`, `W(n)`, `WAdd`, `Sub`, `Pred`, `Le`/`Lt` (Prop) and their lemmas, `Leb`/`Eqb` (Bool), `LeDec`/`LtDec`, `ModS`/`ModLt` | Bool, Logic |
| `List.lean` | `List` | `List(A)`, `LenL` | Word |
| `Option.lean` | `Option` | `Opt(A)`, `IsSome`, `IsNone` | — |
| `Box.lean` | `Box` | `Box(A)` | — |
| `Array.lean` | `Array`, `ArrayLemmas` | from `16Arrays`: the representation, the natives, `Swap`/`Replicate`/`Fill`, and the lemma library | Word, List, Logic |
| `Fixtures.lean` | `Fixtures` | test-only definitions (`Pick`, `Empty`, `U`/`V`) | — |

Block names that are also Lean namespaces (`Bool`, `Nat`, `List`, `Option`, `Array`) put `<Block>.decls` into those namespaces. Check that this is harmless. If it isn't, fall back to plural block names (`Bools`, …) and keep the file names.

**The tour.** Renamed without prefixes, content unchanged except for its `uses`/`import`s and de-duplication by the Addendum's rule: `Numbers`, `Borrows`, `ReturnedBorrows`, `ClosingOff`, `Equality`, `Snapshots`, `Recursion`, `CaseSplits`, `Functions`, `Inductives`, `Propositions`, `CurrentState`, `Erasure`, `Universes`, `BorrowTypes`.

**The case studies:**
- `ArrayBench.lean`: what is left of `16Arrays`, the arrays chapter and its benchmarks, renamed so it isn't confused with `Array.lean`.
- `HashMap.lean`: was `17HashMap`; lane `hm-gen` is rewriting it.
- `DependentFields.lean`: was `18DependentFields`.
- `Quicksort.lean`: new, the `Quicksort` block moved out of `16Arrays`.

**Infrastructure** (unchanged names): `Registry`, `Ledger`, `CaseStudyLedger`, `Units`, `Editor`, `Playground` (the user's, untracked: leave it alone).

**Delete every per-block `#guard <Block>.decls.length == N`.** Keep the registry's single expected total.

**References.** Update every living reference to the old names and to `Std`:
- `Ochr/Examples.lean` and the lakefile;
- the Registry and the ledgers;
- the test runner;
- the paper and its sweep;
- `OCHR_BOOK.md` §2 (the import header) and its file list;
- `ochr/core/lean/README.md`;
- RULES, if it names files;
- the bench packages, `sandbox.py`, GUIDE and SPEC;
- `CLAUDE.md`-style pointers.

Historical notes (`ochr/core/notes/`, DECISIONS) keep the old names. A mapping table in `Examples/README.md` resolves them.

## Reusable blocks and test blocks (user ruling, 2026-10-21)

The user's words: "it does not hurt for the concrete runs to have a name, but I only want them being run once every time lake build happens … these files should be split into `ochr Numbers uses Std` and `ochr NumbersTests uses Numbers`, then other files import Numbers but not NumbersTests. This will reduce the total amount being checked and make visual separation between whats supposed to be re-used and what is a result".

Why it matters: a used block's accepted declarations are re-checked inside every block that uses it, transitively (`Block.closure`, `libWith`: nothing is cached). So a concrete run or a headline theorem in a used block is re-checked once per user.

The rule:
- **A block that another block `uses` contains only what is meant to be reused:** types, operations, model functions, and lemmas that later blocks call.
- **Everything else moves into a companion block, `<Block>Tests uses <Block>`, in the same file, which no block uses.** That covers concrete runs (`Run…`, `…Run`), headline theorems, feature-test examples and `reject def`s.
- **A block that nothing uses stays as it is:** everything in it is already a result.
- **Today's used blocks:** `Std`, `Fixtures`, `Index`/`Arrays`/`ArrayLemmas`/`ArrayBench`, `HashMap`/`HashMapLookup`/`HashMapLength`/`HashMapResize`, and `AttrLib`. After the layout change, the new topic library files get companions where they have tests.
- **Ledger, Registry, paper sweep and tests that name `Block.Decl`** follow the moved declarations.
- **`DepVec uses ArrayBench`** should use `Array`/`ArrayLemmas` instead, if all it needs is the library.
- **Report** the total check time and declaration-check count of `lake build` before and after.

Lane `hm-gen` applies the rule inside the hashmap case study. Lane `hm-lib` applies it everywhere else.

**Agents may fork themselves** (the Agent tool with subagent_type "fork") for parallelisable subtasks:
- partition the files, so no two forks edit the same file;
- give each fork its own branch or worktree, or a disjoint set of files with commits by explicit path;
- the lane owner reviews and lands.
