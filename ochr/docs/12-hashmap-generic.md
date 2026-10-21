# 12. The hashmap case study, generic: the plan and the `hm-gen` brief

Written by team-lead on 2026-10-21. This replaces docs/11 §3 ("phase 2"). User decisions:
- values generic in `V`, keys `Word`;
- built on the generic `List` and `Array` libraries, with no hand-rolled `Opt`/`Bucket`/`Slots`/`BGetMut` copies;
- keep the `len` field, because dropping it makes `Insert` O(capacity) through the resize check;
- keep the invariant outside the type for now. Moving it into the type is a later, separate, measured step (user: "agree to do 2. move invariant into type after the fact");
- break the work down to run in parallel (user: "the goal here is to break work down so its nice and parallelisable").

## The plan (dependency graph)

| Lane | Work | Depends on |
|---|---|---|
| `hm-ergo` | docs/11 §1: surface sugar (destructuring `let`, `if`, `match` on any expression) | none (running) |
| `hm-lib` | docs/11 §2 and Addendum: split `00Std` into topic-named library blocks in a DAG, centralise helpers, de-duplicate Examples | none (running) |
| **`hm-gen`** | **this brief, §1–§3: rewrite `17HashMap.lean`** | none |
| `hm-gen`, step 2 | this brief, §4: fold the hashmaps in `16Arrays` and `18DependentFields` into the new one, or delete them; re-measure the paper's case study | `hm-lib`, `hm-gen` landed |
| `hm-ergo`, step 2 | adopt the sugar across the examples where it reads better | `hm-ergo`, `hm-lib`, `hm-gen` landed |
| `hm-inv` | move the invariant into the type as a proof field, measured, and revert if the code gets too noisy | `hm-gen` landed |

## `hm-gen` brief

1. **Representation.** `HashMap(V) := HM(n : Word, len : Word, slots : Array(List(Pair(Word, V)), Succ(n)))`. That is the Σ shape (docs/09, `Vec`). It is needed because resizing changes the capacity, and a borrow fixes a value's type. Use `16Arrays`'s `Array`, `GetMut`, `WithSplit`, `ArrFromFn` and literals, Std's `List`, and the Prelude's `Pair`. Use the library's option type if there is one; otherwise a generic `Opt(V)`. `hm-lib` is centralising one; take its name when you rebase.
2. **Same program, same theorems.** Keep the operations (new, len, get, contains, insert with resize, remove, get_mut, clear, resize) and the whole theorem list the paper compares with Aeneas, theorem for theorem:
   - lookups, lengths, the invariant and its preservation, resize, the load factor;
   - the `Id` statements over borrowed parameters, and the propositions over value parameters.
   - The API follows the generic bench packages (`ochr/bench/hashmap/SPEC.md` §3): `get(&m, k, h : Contains(…)) : &V`, used read-only, and `get_mut : &V`. Insert and remove return the value moved out, as `Opt(V)`.
   - A theorem that no longer makes sense generically (for example one that copies a `Nat` value) is restated with `clone`, or dropped with a one-line reason in the notes.
3. **Plain syntax.** Don't wait for `hm-ergo`'s sugar: write `match`, not `if`, and bind call results before matching them. `hm-ergo` adopts the sugar later.
   - **Helpers.** Keep the Word helpers you need (key comparison, mod/index, numerals) in one clearly marked section at the top, so that whoever lands second can swap them for `hm-lib`'s central ones mechanically.
   - **The concrete runs** (`RunGet`, `RunCollide`, …) stay, at `V := Word`, using array literals.
4. **Step 2, after both `hm-lib` and `hm-gen` have landed (wait for team-lead's go).**
   - Fold the smaller hashmaps in `16Arrays` and `18DependentFields` into this one, or delete them if they only duplicate it. Keep anything that is the subject of its own test.
   - Re-measure the case study: declarations, lines and check time per block, and the Aeneas comparison table in `notes/hashmap-case-study.md`. Then update the paper's case-study section (§8) and its numbers. The paper body must stay within 25 pages, with the Conclusion ending on page 25.

### Resources

- `ochr/bench/hashmap/{ochr,ochr-2p}/HashMap.lean`: the generic statements, with a provided generic model in `ochr-2p`.
- `ochr/bench/hashmap/SPEC.md`.
- `18DependentFields`' `Vec`: the Σ shape with `Array`.
- `notes/hashmap-case-study.md`: what each theorem is for.

### Landing (FF-CAS, by you)

Rebase onto `origin/ochr-core`, never merge-commit. Then, in `/home/charlielidbury/repos/ochre-ochr-core`, run `git pull --ff-only origin ochr-core && git merge --ff-only hm-gen && git push origin ochr-core`, retrying from the rebase if that fails.

Acceptance:
- `lake build`, `lake build tests fuzz` and `lake exe tests` are green;
- fuzz statuses are unchanged;
- every program printed in the paper checks (the paper sweep);
- the Conclusion ends on page 25;
- all four bench sandboxes build, with their holes named.

The paper's case-study numbers may lag until step 2. Say so in the landing commit.
