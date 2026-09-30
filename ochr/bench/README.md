# Agent-effort benchmark: protocol

This directory holds coursework-style assignments for measuring how much effort it takes to produce a verified in-place hash map and a verified in-place quicksort in several verification systems, Ochr among them. Effort is measured as the tokens an AI agent spends to get from the assignment to a passing, verified solution. This file is the protocol: what is measured, how a trial runs, what counts as success, and what could make the numbers misleading.

Only the assignments are here. No assessed agent has been run, and no verified solution is in the repository. A solution would contaminate the experiment, and producing one is the experiment itself.

The shared design the packages were built from is `ochr/docs/05-agent-effort-benchmark.md`. Its Amendments section records the changes to that design approved since, all of which this protocol includes.

## 1. What is being tested, and why tokens

**The thesis.** Ochr is a core calculus that combines Rust-style `&mut` borrows with a Lean-style dependent type theory. The in-place program itself can appear in types and proofs, so a verified in-place program needs no separate pure specification and no proof that the two agree. The claim under test is that this one-program setup takes *less total effort* than the usual two-program setup, where you write a pure model, an efficient implementation, and a refinement proof that they agree (Aeneas, Low*, VeriFast, and in a different way Verus).

**Why tokens rather than lines.** Counting the lines or tokens of a finished development measures the artifact, not the work. Two developments of the same size can take very different amounts of work: one may come out right first time, the other after many failed attempts, dead ends and re-reads of the documentation. A proof that a tool's automation discharges costs no lines, but finding the phrasing that makes the automation succeed can cost a lot. The user's definition of effort is therefore the number of tokens an AI agent consumes, thinking included, to get from the assignment to a passing, verified solution. That number includes reading the documentation, understanding error messages, false starts and retries, which is the difficulty the thesis is about. Final line counts are still recorded, as a secondary number.

## 2. Layout

```
README.md                 this protocol
common/check_fixed.py     checks that FIXED regions are unchanged (shared by every grade.sh)
hashmap/SPEC.md           the system-neutral hashmap assignment, properties H1–H18
hashmap/tests.json        its test vectors
hashmap/_reference/       unverified Rust reference and the test generator (never in a sandbox)
hashmap/<condition>/      one self-contained package per condition
quicksort/…               the same for quicksort, properties Q1–Q2
```

Each package (`<problem>/<condition>/`) contains:
- `ASSIGNMENT.md`, the brief the assessed agent reads, written like a university coursework assignment;
- the skeleton: source files in which the FIXED parts (types, representation, signatures, property statements, tests, definitions such as `sorted` and `perm`) sit between `FIXED-BEGIN <id>` and `FIXED-END <id>` markers, and the holes are what the agent fills in;
- `SOLUTION_FILES`: the paths, one per line, of the files the agent is expected to edit;
- `grade.sh`, the grader (§8);
- `flake.nix` and `flake.lock`, pinning the toolchain;
- `make-sandbox.sh DEST`, which builds a trial's sandbox (§7).

## 3. Conditions

| Condition | What the agent writes | What it controls for |
|---|---|---|
| `ochr` | One in-place Ochr program, with the properties stated and proved directly about it. | The thesis condition. |
| `ochr-2p` | The same in-place Ochr program, plus a pure functional model of it, a proof that the program agrees with the model (the statement is FIXED), and the properties proved about the model. | The ablation: the language, checker, documentation and lack of automation are the same as `ochr`, and only the one-program versus two-program structure differs. It is the cleanest test of the thesis, because it removes the confounds of pretraining familiarity, proof automation and ecosystem that every cross-system comparison has. |
| `aeneas` | Rust, translated by Charon and the latest Aeneas into Lean 4, with the proofs in Lean about the generated functions. | The state of the art of the two-program setup for Rust: the translation plays the role of the model. |
| `verus` | Rust with Verus specifications and proofs, checked by an SMT solver. | A mature Rust verifier with strong automation. Its specifications are written in a pure ghost language next to the code, a lighter form of two programs. |
| `lean` | A pure functional Lean 4 implementation (an `Array` updated in place when unshared), with the same properties. | The cost of the proofs with no memory model at all: a lower bound for what the properties themselves cost. |
| `rust` | Unverified Rust: the implementation and the tests only. | The floor. A condition's verification overhead is its cost minus this. |

## 4. Tasks

### Main tasks

- **Hashmap** (`hashmap/SPEC.md`): a fixed-capacity hash map with separate chaining, in place, with `new`, `len`, `get`, `insert`, `remove` and `get_mut`, and eighteen properties (H1–H18) stated through `get` and `len` under an invariant the solver chooses.
- **Quicksort** (`quicksort/SPEC.md`): in-place quicksort with a Lomuto or Hoare partition and two recursive calls on disjoint borrowed sub-ranges, proved sorted (Q1) and a permutation of its input (Q2).

Each package's `ASSIGNMENT.md` transcribes its SPEC into the system's notation and cites the property numbers. The correspondence table at the end of each SPEC records, per condition, which declaration states which property and where a statement differs.

### Calibration tasks

Ochr has no presence in any model's pretraining, while Rust, Lean and to a lesser degree Verus and Aeneas do. Part of what an assessed agent spends on an Ochr task is learning the language from its documentation. The calibration tasks estimate that fixed cost of learning each tool. They are posed in every condition exactly the way the main tasks are: a package with an `ASSIGNMENT.md`, a skeleton whose FIXED regions hold the types, signatures, statements and tests, holes for the implementation and the proofs, and a `grade.sh`. They are specified here and will be built as small packages later (`calibration/add_m/<condition>/`, `calibration/append_length/<condition>/`).

- **C1, `add_m`.** An in-place addition.
  - FIXED signature: `add_m(x : &mut 𝕎, y : 𝕎)`, returning nothing.
  - FIXED property K1: if `x₀` is `*x` before the call and `x₁` is `*x` after it, then `x₁ = x₀ + y`. A system with bounded words may require `x₀ + y ≤ 2⁶⁴ − 1`, and the call must then not overflow.
  - Hole: the body and the proof. Any implementation that changes `*x` in place is accepted, including one that uses the system's own addition.
  - FIXED tests: `(x, y) ∈ {(0, 0), (0, 5), (7, 0), (3, 4), (20, 22)}`, each checking `*x` afterwards.
- **C2, `append_length`.** A recursive function and a proof by induction.
  - FIXED type: `L ::= Nil | Cons(head : 𝕎, tail : L)`, a list type declared in the skeleton, not the library's list.
  - FIXED specification function: `length(Nil) = 0`, `length(Cons(h, t)) = 1 + length(t)`, with results in ℕ.
  - FIXED signature: `append(xs : L, ys : L) → L`, taking both lists by value.
  - FIXED property K2: `length(append(xs, ys)) = length(xs) + length(ys)` for all `xs`, `ys`.
  - Hole: the body of `append` and the proof.
  - FIXED tests: `append([], []) = []`, `append([1, 2], []) = [1, 2]`, `append([], [3]) = [3]`, `append([1, 2], [3, 4, 5]) = [1, 2, 3, 4, 5]`.

Both are deliberately textbook exercises, and every system's documentation contains near-identical examples: Ochr's examples tour has `AddM` on `Nat` and an in-place `AppendM`, and the Lean and Verus tutorials prove facts about list append. What the calibration measures is the cost of finding, reading and applying the documentation and of getting through the toolchain and the grader, not the cost of inventing a proof.

`ochr` and `ochr-2p` share the calibration, since the language is the same. The calibration figures are reported alongside the main ones, per condition. Subtracting them from the main-task figures gives a rough learning-adjusted cost, reported as a secondary view only, since learning a tool and using it are not additive.

## 5. Metric

**Primary: output tokens to the first pass.** The output tokens of the assessed model, thinking included, summed over every model call in the trial from its start up to and including the call whose tool use ran the first `grade.sh` that reported a pass. For the Claude API, `output_tokens` already includes thinking tokens.

**Secondary:**
- total tokens processed: input, cache-creation input, cache-read input and output tokens, summed over the same calls (this is where verbose tools and long documentation show up);
- wall-clock time from the start of the trial to the first pass (this is where slow builds and slow solvers show up);
- the number of turns (model calls);
- the number of `grade.sh` runs;
- the success rate within the budget (§6);
- the final solution's size: non-blank lines outside the FIXED regions of the solution files, as `check_fixed.py` prints them, for the solution and for the skeleton.

## 6. Trials

- A *cell* is one task in one condition. Each cell gets at least 5 trials.
- Every trial of every cell uses the same model and the same effort level, recorded with the results.
- Every trial has the same fixed budget `B` of output tokens, and a wall-clock limit. `B` is fixed once, before the first scored trial, from unscored pilot runs, and recorded. A trial that reaches `B` or the time limit without an authoritative pass (below) is a failure, and its token count is recorded as censored at `B`.
- Each trial runs in a fresh sandbox made by the package's `make-sandbox.sh`. Nothing carries over between trials: no files, no agent memory, no session history.
- The agent runs with a clean configuration: no user or project `CLAUDE.md`, no memory files, no MCP servers, no plugins or skills, no web tools and no sub-agents. Its tools are shell, read, edit, write and search, inside the sandbox only. (With Claude Code: `--bare`, `--strict-mcp-config`, and `--disallowedTools` for the web and sub-agent tools.)
- Every trial gets the same prompt, with only the directory differing:

  > You are working in `<sandbox>`. Read `ASSIGNMENT.md` and complete the assignment it describes. Check your work with `./grade.sh`. You are done when `./grade.sh` passes.

- The session ends at the first `grade.sh` run that reports a pass (the runner may stop it there), at the budget, at the time limit, or when the agent stops.
- **The authoritative grade.** The in-sandbox `grade.sh` is only advisory, since the agent could have edited it, `check_fixed.py`, the tests or a vendored library. After the session, the runner makes a fresh sandbox, copies in only the files listed in `SOLUTION_FILES` from the agent's sandbox, and runs that pristine `grade.sh`. The trial passes only if the pristine grade passes. If the agent's grade said pass and the pristine one says fail, the trial is a failure and is flagged for review. Files that the agent created but `SOLUTION_FILES` does not list are not copied, so a solution must live in the listed files.

**Reporting.** For each cell: the success rate; the median of output tokens to the first pass, with failed trials counted as larger than any success (so the median exists when more than half succeed); the minimum and maximum; and the same for each secondary number. Conditions are compared by the ratio of medians, and by a rank test (Mann–Whitney U) that treats failures as tied at the top. With 5 trials per cell only large differences are detectable, and the report says so.

## 7. Sandboxing

- **No network.** The assessed agent has no network access for the whole trial. Every toolchain and library must already be in the sandbox or in the nix store.
- **No known solutions.** `make-sandbox.sh` copies the package and exactly the libraries and documentation it allows, and nothing else from this repository. These are excluded from every sandbox:
  - this repository's Ochr case studies: `ochr/core/lean/Ochr/Examples/17HashMap.lean`, and the `Quicksort` block and the case-study lemmas in `ochr/core/lean/Ochr/Examples/16Arrays.lean`;
  - the Ochr paper (`ochr/core/paper/`), which prints excerpts of the solutions, and the case-study notes (`ochr/core/notes/`);
  - `competitors/`, and this repository's other verification developments of hash maps or sorting;
  - Aeneas's own hashmap tests and proofs;
  - Verus's examples of hash maps and of sorting;
  - this benchmark's `_reference/` directories and every other condition's package.

  Each package's validation greps its sandbox for the excluded files and for distinctive names from the case studies.
- **Comparable documentation.** Every condition gets its tool's own documentation or tutorial in the sandbox, as files the agent can read offline:
  - Ochr: a language reference and the examples tour, minus the case studies;
  - Aeneas: the Aeneas and Charon documentation and the Aeneas Lean library's sources;
  - Verus: the Verus guide and the `vstd` sources;
  - Lean: the Lean 4 documentation and the standard library's sources;
  - Rust: the standard library documentation.

  Each `ASSIGNMENT.md` says where the documentation is.

## 8. What every grade.sh does

`grade.sh` exits 0 if and only if all of these hold:
1. everything builds and checks;
2. no holes and no forbidden constructs remain (§9);
3. every FIXED region is byte-identical to the original, by `common/check_fixed.py`;
4. every test passes.

Its last line of output is a one-line verdict that starts with `GRADE: PASS` or `GRADE: FAIL`. A runner finds the first pass by that prefix. On a failure the line names the reasons (the remaining holes, for example); on a pass, and where possible on a failure, the output also includes `check_fixed.py`'s line counts.

`check_fixed.py` only compares bytes. A FIXED statement could still be neutralised from outside its region: commented out by a block comment opened before it, compiled out (`#[cfg(...)]`), cut off (`#exit`), or given a different meaning by a redefined notation, instance or name. Each `grade.sh` therefore also checks that the FIXED statements were really checked: by the checker's own list of checked declarations, by a grader-owned file that refers to each FIXED theorem by name (with `#print axioms` in Lean), or by the verifier's count of verified items. The constructs that do this are also forbidden (§9), and the human check reads the solution's diff against the skeleton.

`check_fixed.py ORIGINAL SOLUTION [ORIGINAL SOLUTION …]` takes pairs of files. A region runs from the line with `FIXED-BEGIN <id>` to the line with `FIXED-END <id>`, markers included, in any comment syntax. It fails if a region was changed, added, removed or reordered, or if its markers were broken. `check_fixed.py --self-test` runs its own tests.

## 9. Forbidden constructs

Each package's `grade.sh` rejects at least the following in the solution files, and its `ASSIGNMENT.md` lists them. A package may forbid more, and says why in its `ASSIGNMENT.md`. Constructs inside FIXED regions, provided by the skeleton, are allowed.

**Every condition:**
- the package's hole marker (`sorry`, `todo!()`, `admit()`, `TODO`, …);
- library data structures and algorithms that do the task: hash maps, tree maps, sets and association lists for the hashmap; sorting, selection and partitioning routines for quicksort;
- anything that stops a FIXED region from being checked (§8);
- changes to the toolchain, the provided libraries, the build configuration or the grader. These are outside `SOLUTION_FILES`, so the authoritative grade ignores them anyway.

**`ochr` and `ochr-2p`** (Ochr is embedded in Lean, as `ochr Name uses … { … }` blocks):
- `reject`: a `reject def` is counted as correct when the checker rejects it, so it would turn a failed proof into a pass;
- any Lean outside the `ochr` blocks other than in FIXED regions: no `axiom`, `sorry`, `set_option`, `macro`, `syntax`, `elab`, `notation`, `import`, `open`, `#eval` or attributes;
- changing the checker's switches (such as `d53` or `unitEta`), or the checker or library sources;
- `ochr-2p` only: in-place code (borrows, assignment) in the pure model.

**`aeneas`:**
- Rust: `unsafe`; `std::collections`; library sorting and selection (`sort*`, `select_nth_unstable*`); Charon or Aeneas attributes beyond those provided (such as `#[charon::opaque]`); external crates;
- Lean: `sorry`, `admit`, `axiom`, `native_decide` and `decide +native`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque` beyond those provided, `set_option debug.skipKernelTC`, `#exit`; editing the generated Lean files (the grader regenerates them from the Rust); every property theorem's `#print axioms` may show only `propext`, `Classical.choice` and `Quot.sound`.

**`verus`:**
- `assume(…)`, `admit()`, `#[verifier::external_body]`, `#[verifier::external]`, `#[verifier::external_fn_specification]`, `assume_specification`, `#[verifier::exec_allows_no_decreases_clause]`, `unsafe`, and `#[cfg(…)]`;
- code outside the `verus!` macro, other than what the skeleton provides;
- in executable code, `vstd` or `std` hash maps, sets and sorts. `vstd`'s mathematical types (`Seq`, `Map`, `Multiset`) may be used in specifications and proofs.

**`lean`:**
- `sorry`, `admit`, `axiom`, `native_decide` and `decide +native`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque` beyond those provided, `set_option debug.skipKernelTC`, `#exit`;
- `Std.HashMap`, `Std.DHashMap`, `Std.TreeMap`, `Lean.HashMap`, `Lean.AssocList` and the Batteries and Mathlib equivalents; `Array.qsort`, `Array.insertionSort`, `List.mergeSort`, `List.insertionSort` and other library sorts;
- every property theorem's `#print axioms` may show only `propext`, `Classical.choice` and `Quot.sound`.

**`rust`:**
- `unsafe`; `std::collections`; library sorting and selection (`sort*`, `select_nth_unstable*`); external crates; `#[cfg(…)]` outside the FIXED tests.

## 10. What counts as success

A trial succeeds when both hold:
1. the authoritative grade passes (§6): the pristine `grade.sh` exits 0 on the agent's solution files;
2. a human reader confirms that the solution is the required algorithm and does not game the grader:
   - hashmap: SPEC requirements A1–A3 (only `k`'s bucket is touched; in place, with no copied or rebuilt bucket; no auxiliary structure or resizing);
   - quicksort: SPEC requirements A1–A4 (Lomuto or Hoare, as the solver's comment says, and it really is that scheme; two recursive calls on disjoint borrowed sub-ranges; no copy; no library or fallback sort);
   - both: the diff against the skeleton outside the holes adds only helper definitions and lemmas, and nothing that changes the meaning of a FIXED statement (§8);
   - `ochr`, `ochr-2p`: no proof relies on a soundness bug in the checker. A suspected one fails the trial and is reported as a finding about Ochr.

The human check is done blind to the token counts, and its verdict is recorded with a one-line reason.

## 11. Recording tokens (for a future runner)

The runner is not written yet. With the Claude Code CLI, one trial would look like:

```
cd "$SANDBOX" && claude -p "$PROMPT" --output-format stream-json --verbose \
  --model "$MODEL" --effort "$EFFORT" --bare --strict-mcp-config \
  --disallowedTools "WebFetch WebSearch Agent" > trial.jsonl
```

run inside a network-less container that holds only the sandbox and the nix store. From `trial.jsonl`:
- Every `{"type": "assistant", …}` event carries `message.usage` with `input_tokens`, `output_tokens`, `cache_creation_input_tokens` and `cache_read_input_tokens`. One model call can be split across several events that share `message.id`, so count each `message.id` once.
- The first pass is the first `tool_result` whose output contains a line starting with `GRADE: PASS`. Match it to its `tool_use` by id, and sum the usage of every model call up to and including the one that issued that tool use. The runner can stop the session at that point.
- The final `{"type": "result", …}` event gives `num_turns`, `duration_ms`, and per-model totals under `modelUsage`. Count only the assessed model: the CLI can make small side calls with another model, and those are not the agent's effort.
- Count `grade.sh` runs from the `Bash` tool uses whose command invokes it.
- Record the model id, effort level, CLI version, the package's git commit and the sandbox's hash with each trial.

## 12. Threats to validity

- **Pretraining familiarity.** Ochr has no presence in any model's pretraining. Rust and Lean have a great deal, Verus some and Aeneas little. This biases every cross-system comparison against Ochr. The calibration tasks estimate the size of the bias, and `ochr` against `ochr-2p` is immune to it.
- **Automation.** Verus discharges many obligations with an SMT solver. Aeneas and Lean have `simp`, `omega`, `progress` and similar tactics. Ochr has none: every case split and rewrite is written out. A cross-system difference therefore mixes the thesis variable (one program or two) with automation. `ochr-2p` isolates the thesis variable. The cross-system comparisons show where Ochr stands against today's tools, automation included.
- **Contamination.** Aeneas's hashmap is a published case study, and verified quicksorts in Lean and Verus are common in public code. A model may recall parts of a solution, lowering those conditions' token counts. The sandbox removes local copies, but it cannot remove what the model memorised. Ochr cannot be contaminated through pretraining. It can be contaminated through this repository, which is why the case studies and the paper are excluded.
- **Harness effects.** The numbers are for one agent harness (Claude Code), one model and one effort level. Its system prompt, tools, context compaction and caching all affect token use. Tool latency does not cost output tokens, so slow builds (Charon with Lean and Mathlib) are cheap in the primary metric and show up only in wall-clock time. Tool verbosity costs input tokens, not output tokens, and shows up in total tokens. The quality of a tool's error messages does affect the primary metric, and legitimately so, since that is part of what a tool costs its user.
- **An agent, not a human.** The benchmark measures an AI agent's effort. It correlates only imperfectly with a human expert's: an agent reads documentation fast and does not tire of long explicit proofs, and it is weaker at some kinds of insight a human finds easy. The results do not say how long a human would take.
- **Differences between the conditions' tasks.** Each package's FIXED statements are the SPEC in its system's idiom, and idioms differ. Ochr's `Word` is unbounded, so Ochr has no overflow obligations; bounded systems get an allowance for `len` but still have index arithmetic to check in quicksort. Ochr's quicksort takes fuel, so its proofs include showing that the fuel suffices, where the others prove termination. Some statements in Ochr are about copies of the map. The correspondence tables record every such difference so that a reader can judge it.
- **Size and variance.** Two small problems, and at least 5 trials per cell of a high-variance process. Results may not generalise to larger developments, and only large differences are detectable.
- **Checker soundness.** Ochr's checker is a research prototype, and earlier cold reviews found closed proofs of `False`. An agent could find and exploit such a bug, deliberately or not. The human check looks for this, and a solution that relies on one is a failure and a finding.

## 13. Test vectors and the references

`tests.json` in each problem directory is generated by `_reference/gen_tests.py`: a hand-written script of ops and splitmix64 pseudo-random ops from a fixed seed, with the expected results computed by an oracle independent of any implementation under test (Python's `dict` and `sorted`). `_reference/run.sh` checks that `tests.json` is exactly the generator's output and that an unverified Rust reference, written against the SPEC's representation and API, passes every expected result. The references validate the test vectors, not the other way round, and they are never copied into a sandbox.

Keys are at most 23 and values at most 99, so that Ochr, whose numbers are unary, can run every test.
