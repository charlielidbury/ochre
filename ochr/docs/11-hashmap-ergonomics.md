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
     - Dropping the `len` field removes the `len = Count(slots)` invariant entirely, at the cost of an O(cap) `Len`.
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
