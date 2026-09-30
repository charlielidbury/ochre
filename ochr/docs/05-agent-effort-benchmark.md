# 05. Agent-effort benchmark: design

Written 2026-09-30 by team-lead, at the user's request. The user's ruling on the metric: "tokens" means "how many tokens does an agent need to get a {hashmap, quicksort} implementation working. This includes thinking tokens etc. The idea here is to get a metric which captures the difficulty of what's going on, not just the output artifact". Source-token counts were removed from the paper (20a764c3).

The user asked for coursework-style assignments ("create a hashmap datastructure with <these> properties which passes <these> tests, with a skeleton file with holes"). The Aeneas condition uses the most modern toolchain available. There are controls for unverified Rust, pure Lean and Verus, and the same again for verified quicksort. Only the problem statements go in the repo; the assessed agents are not run.

The lead added three things:
- the `ochr-2p` ablation (same language, forced two-program structure), which isolates the thesis variable from language familiarity;
- a calibration task per system;
- the sandboxing rules.

The text below is the brief given verbatim to the five agents building `ochr/bench/`: bench-spec, bench-ochr, bench-aeneas, bench-verus and bench-controls. Two decisions for the user to review: fixed capacity with no resize, and `get_mut` requiring the key to be present. The protocol as built is `ochr/bench/README.md`.

## Shared design (identical in every bench agent's brief)

**Why this exists.** Ochr is a core calculus combining Rust-style `&mut` borrows with a Lean-style dependent type theory. The in-place program itself appears in types and proofs, so there is no separate pure spec and no refinement proof. The thesis under test: one system in which the in-place algorithm can appear in types and proofs needs *less total effort* than the two-program setup (a pure spec, an efficient implementation, and a proof that they agree: Aeneas, Low*, VeriFast). The user defines effort as **the number of tokens an AI agent consumes, thinking included, to get from a coursework-style assignment to a passing, verified solution**. It is not the size of the final source. There are two problems, a hashmap and in-place quicksort, each posed in several systems. THIS PASS BUILDS THE ASSIGNMENTS ONLY: nobody runs the assessed agents, and nobody writes verified solutions (they would be contamination and are the experiment itself).

**Layout** (in the git worktree `/home/charlielidbury/repos/ochre-ochr-core`, branch `ochr-core`), under `ochr/bench/`:
- `README.md`: the protocol (owner: bench-spec).
- `common/`: shared grader helpers, e.g. `check_fixed.py` (owner: bench-spec).
- `hashmap/SPEC.md`, `hashmap/tests.json`: the system-neutral assignment and test vectors (owner: bench-spec).
- `hashmap/_reference/`: an unverified Rust reference used only to validate `tests.json`. It is never copied into a sandbox (owner: bench-spec).
- `hashmap/<condition>/`: one self-contained package per condition (owner: that condition's agent).
- `quicksort/...`: the same.

**Conditions** (package directory names):
- `ochr`: Ochr, one program. The properties are stated directly about the in-place code.
- `ochr-2p`: an Ochr ablation, two programs. The skeleton also requires a pure functional model (written by the agent), an agreement theorem between the in-place code and the model (statement FIXED), and the properties stated about the model. The language is the same as `ochr`, so the only difference is one program versus two. This is the cleanest test of the thesis: it removes the confounds of language familiarity, automation and ecosystem.
- `aeneas`: Rust → Charon → Aeneas → Lean 4, with the latest Aeneas.
- `verus`: Verus.
- `rust`: unverified Rust, implementation and tests only. This is the floor: verification overhead is a condition's cost minus this.
- `lean`: pure Lean 4. A functional implementation (`Array`-based, updated in place when unshared) with the same properties. It measures the cost of the proofs with no memory model at all.

**Each package contains:**
- `ASSIGNMENT.md`: written like a university coursework brief. It covers:
  - what to build;
  - the required properties, transcribed from SPEC.md into the system's own notation;
  - the tests;
  - what is provided and what is forbidden;
  - how to check your work (`./grade.sh`);
  - what counts as done.
  It is self-contained: assume the reader has only this directory, its toolchain, and the docs the sandbox includes.
- **The skeleton.** The FIXED parts go between marker comments `FIXED-BEGIN <id>` / `FIXED-END <id>`, in the system's comment syntax. These are the types, the representation, the public signatures, the property statements, the tests and definitions such as `sorted` and `perm`. The holes are what the agent fills in. Write holes in the system's own idiom (`sorry`, `todo!()`, `admit()`). For Ochr, use whatever the checker supports; an unbound name `TODO` that the checker rejects is acceptable.
- `grade.sh`: exits 0 iff all of the following hold.
  1. Everything builds and checks.
  2. No holes and no escape hatches remain (`sorry`, `admit`, `axiom`, `assume`, `#[verifier::external_body]`, `unsafe`, new `implemented by`/`abstract` beyond those provided, library shortcuts such as `std::collections::HashMap` or `sort`). The exact list for each system goes in README and ASSIGNMENT.
  3. Every FIXED region is byte-identical to the original (via `common/check_fixed.py`).
  4. All tests pass.
  It prints a one-line verdict plus the solution's line counts (a secondary metric).
- `flake.nix` (+ `flake.lock`) providing the pinned toolchain. Follow the pattern of `competitors/aeneas/` and `competitors/verus/` at the repo root. Never modify the root `flake.nix`.
- `make-sandbox.sh DEST`: copies the package plus exactly the allowed libraries and docs into a fresh directory for an assessed agent, and nothing else from this repo.

**Hashmap: shared decisions.** It has a fixed capacity and uses separate chaining. There is no resize, because Ochr has no dependent fields today.
- Keys and values are unsigned machine words (u64; Ochr's `Word`).
- Representation (FIXED): an array of `cap` buckets, each a singly linked list of (key, value) entries, plus a `len` field. The bucket for key `k` is `k mod cap`. Operations are in place: no copy of the table or of a bucket.
- API:
  - `new(cap)`, which requires `cap > 0`;
  - `len(m)`;
  - `get(m, k) -> Option<u64>`;
  - `insert(m, k, v) -> Option<u64>`, returning the previous value;
  - `remove(m, k) -> Option<u64>`, returning the removed value;
  - `get_mut(m, k) -> &mut u64`, requiring `k` to be present. This is a precondition because Ochr cannot return a borrow inside an `Option`.
- Properties are observational: stated through `get` and `len`, not through a model. A solution may define any model or invariant it likes internally. The agent defines an invariant `Inv` (a hole) and proves:
  - `Inv(new(c))`, and every mutating operation preserves `Inv`.
  - Under `Inv`, for `get`:
    - `get` on `new` is None;
    - `get` after `insert`: Some v at the same key, unchanged at any other key;
    - `insert` returns the old `get`;
    - `get` after `remove`: None at the same key, unchanged at any other key;
    - `remove` returns the old `get`.
  - Under `Inv`, for `len`:
    - `len(new) = 0`;
    - `insert` increments `len` iff the key was absent;
    - `remove` decrements `len` iff the key was present.
  - Writing `w` through `get_mut(m, k)` has the same effect on every `get`, on `len` and on `Inv` as `insert(m, k, w)`.
  - `get` and `len` leave the map unchanged. Omit this where the type system guarantees it (Rust `&self`) and say so in the correspondence table.
  Systems with bounded integers may assume `len(m) < 2^64 − 1` as a precondition of `insert`.
- Tests: a scripted sequence (collisions, overwrite, remove, `get_mut`) and a larger randomized sequence with expected results, both in `tests.json`.

**Quicksort: shared decisions.**
- In-place quicksort of an array/slice of u64 (in Ochr, whatever the arrays library provides). Partition with Lomuto or Hoare, and say which. Then make two recursive calls on the two disjoint sub-ranges, borrowed `split_at_mut`-style, with no copy-out/copy-back. Auxiliary space is O(1) beyond the recursion.
- Properties: `sorted(final) ∧ perm(final, initial)`. Both `sorted` and `perm` are FIXED definitions; `perm` is count-based (every value occurs equally often). Where a system's library offers an equivalent (e.g. Verus multisets), the correspondence table must justify the equivalence.
- Tests: empty, singleton, duplicates, sorted, reverse-sorted, all-equal, and random arrays.
- Where a system cannot express recursion on a measure (Ochr today), the FIXED signature may take fuel, with the property stated at fuel = length. Document this as a language limitation.

**Sandboxing rules the packages must support** (README states them):
- The assessed agent has no network.
- It has no access to known solutions: this repo's Ochr case studies (`ochr/core/lean/Ochr/Examples/17HashMap.lean`, the `Quicksort` block and case-study lemmas in `16Arrays.lean`), the Ochr paper (it prints solution excerpts), `competitors/`, Aeneas's own hashmap tests and proofs, and Verus's examples of hashmaps or sorting.
- Every condition gets comparable documentation in its sandbox: the tool's own docs or tutorial, and for Ochr a language reference plus the examples tour minus the case studies.

**Validation required before you report (no verified solutions!):**
- the skeleton builds or checks, with its holes reported as holes;
- `grade.sh` fails on the untouched skeleton and names the holes;
- `grade.sh` rejects three planted cheats, each in a scratch copy: (a) an escape hatch (`sorry` or equivalent) in a proof, (b) an edited FIXED region, (c) a forbidden construct;
- `make-sandbox.sh` produces a directory that builds on its own and contains none of the excluded files (grep it);
- the tests are the ones in `tests.json`, transcribed mechanically (a script, not by hand, where practical).

**Git discipline.** This checkout is shared with other agents.
- Touch only files you own.
- Commit with `git commit -m "<msg>" -- <your paths>`. Never use a bare `git commit`, `git add -A`, or `git stash`.
- Then `git push origin ochr-core`. If the push is rejected, run `git pull --rebase origin ochr-core` and push again.
- Add a `.gitignore` in your package dirs for build outputs (`target/`, `.lake/`, `result`, generated Lean).
- End each commit message with `Agent: <your name> (teammate of team-lead), <date>.` and a blank line, then `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
- Plain language, no hard line wrapping in prose. Report to team-lead when done: what you built, the pins, the validation results, and anything that made a condition unfair or impossible.

## Amendments

Approved by team-lead on 2026-09-30, after the brief was issued. `ochr/bench/README.md` is the authoritative protocol.

- **Only a pristine copy's grade counts.** Each package lists the files the agent edits in `SOLUTION_FILES`. The authoritative grade copies only those files into a fresh sandbox made by `make-sandbox.sh` and runs that sandbox's `grade.sh`. Reason: inside its own sandbox the agent can edit `grade.sh`, `check_fixed.py`, the tests or a vendored checker, so the in-sandbox grade is only advisory.
- **`grade.sh` ends with a machine-readable verdict.** Its last line starts with `GRADE: PASS` or `GRADE: FAIL`. Reason: a runner finds the first passing run in the transcript by that prefix, which is where the primary metric stops counting.
- **The randomized hashmap tests are four 50-op sequences, at capacities 1, 3, 4 and 7, instead of one sequence of about 200 ops.** Reason: at capacity 1 every key collides, the other capacities give different bucket shapes, and each sequence is a separate, smaller concrete run for Ochr's checker.
- **Every `grade.sh` confirms that the FIXED statements were really checked.** It uses the checker's per-declaration verdicts, a grader-owned file that names each FIXED theorem (with `#print axioms` in Lean), or the verifier's count of verified items. Reason: `check_fixed.py` only compares bytes, and a region can be disabled from outside it, by a block comment opened before it, `#[cfg]`, `#exit`, a redefined notation or instance, or in Ochr a `reject def`, which the checker counts as correct when it is rejected.
- **Every property is total** (both SPECs, §5): the operations terminate, do not panic and do not overflow under their preconditions. This is automatic in Ochr and pure Lean. In Aeneas it is part of the FIXED statement (`= ok …`), and in Verus it is the `decreases`, panic and overflow checks. Reason: otherwise Aeneas and Verus would get partial correctness for free, while Ochr's quicksort at fuel = |a| pays for termination.
- **`sorted` is pairwise** (`i < j ⟹ a[i] ≤ a[j]`) in every condition. Reason: one definition for all conditions, in the form that Lean's `List.Pairwise` and the usual Verus idiom already use.
- **H17 and H18 (`get` and `len` leave the map unchanged) are unconditional equalities of the representation.** Reason: they hold for every map, not only those satisfying `Inv`, and equality of the representation is what Ochr's `Id` states directly.
- **The bounded-`len` allowance also covers H14–H16.** Reason: those properties run `insert`, which a bounded system may guard with `len(m) < 2⁶⁴ − 1`.
- **The tests check `get` after a write through `get_mut`, not the value read through the borrow.** Reason: the brief specifies only the write's effect (H14–H16), and the tests stay within the properties.
- **The token budget `B` is one number of output tokens for every cell, fixed from unscored pilot runs before the first scored trial.** A trial that fails has its count censored at `B`. Reason: no one can guess the right size before a pilot, and one budget for every cell keeps the success rates comparable.
- **The calibration tasks C1 (`add_m`) and C2 (`append_length`) are specified in the README (§4) and not yet packaged.** Both are textbook exercises whose near-solutions appear in every system's documentation, and Ochr's examples tour keeps `AddM` and the in-place `AppendM`. Reason: calibration measures the cost of learning a tool from its documentation, not of inventing a proof. `AppendM` is ordinary documentation, like the list examples the other systems' tutorials include.
- **Quicksort test arrays have at most 24 elements, not 64, in every condition.** Reason: Ochr's checker runs the tests by evaluating unary numbers, and bench-ochr measured about 100 s for the 29 vectors at the original cap of 64, far above the roughly 10 s a grading run can take. The cap is set by Ochr's speed, not by the task. Ochr does not get a separate, smaller set. With the cap, bench-ochr measured Ochr's run of the 29 quicksort tests at 6–7 s end to end in the compiled checker (5–6 s for the tests, about 1.4 s re-checking the library), and the hashmap set at 1.5 s, both on a loaded machine. That is under the 10 s bar. (An earlier relayed figure of "about 1 min" was wrong.) Most of the time at the old cap went to worst-case partitions, which are quadratic in the length, each comparison walking a unary `Word`.
- **Integrity is checked by review, not by grader hardening** (user, 2026-09-30): "automating the 'did the agent cheat' check is fairly unimportant because we can review the solution manually very easy (just spin up another agent)". The graders keep the basic checks already built (FIXED regions, holes, forbidden constructs, restatement and kernel replay where they exist), but no further anti-cheat work is done. Every passing trial's solution is read by a separate reviewer agent before it counts, and that review is the authoritative integrity check.
- **The hashmap is generic in its value type `V`, in every condition; keys stay words.** The user: "yes definitely make it generic, it is not a useful comparison otherwise". `get` returns the value in each system's natural read-only form: a shared reference `Option<&V>` in Rust, Verus and Aeneas, and a copy by value in Ochr (the built-in `clone`, a real copy that runs no user code) and in pure Lean. Reason for the reference: with `V: Clone`, Rust's `clone` is an arbitrary user implementation, so neither Aeneas nor Verus could prove that it returns an equal value, and `get`'s properties would become unprovable. `get_mut` returns `&mut V` (Ochr: `&V`, which needs D66); H1–H18 keep their meaning, stated over the observed value; the tests instantiate `V := u64`/`Word`.
- **Threat to validity: the generic hashmap raises the contamination risk.** It looks more like Aeneas's published case study (`HashMap<T>`) than a word-valued map would. That case study's proofs are excluded from the sandbox, but pretraining may know them, which would lower the `aeneas` condition's token counts.
