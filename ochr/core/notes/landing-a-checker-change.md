# Landing a change to the checker: the checklist and its traps

Written 2026-11-21 from the final report of the agent that landed D90 to D103, at the orchestrator's request, for whoever lands the next change. The standards are in `ochr/core/CLAUDE.md`; this is the procedure that meets them, as actually done.

## The checklist

1. `git fetch`, then `git worktree add ../ochre-<lane> -b <branch> origin/main`, and seed the build cache with `cp --reflink=always -r ochr/core/lean/.lake` from an up-to-date sibling worktree.
2. Make the change and run `taskset -c 0-14 lake build` in `ochr/core/lean`. It is the definition of correct: every asserted verdict, and the total in `Registry.expectedTotal`, which you raise for new rows.
3. Probe programs with `lake env lean <file>`: an `ochr` block in which every row is a plain `def`, so each rejection prints its reason. Run them on the branch and on a baseline worktree at `origin/main` (`git worktree add --detach`). That gives the before-and-after table.
4. Add the probes as an asserted block, register it, and pin rejection messages with `#guard (run "B" B).rejectedWith [...]` (a prefix match).
5. Run the full dump on both sides, with the new tests copied into the baseline. Soften the baseline first, so that main builds with tests it fails: `sed -i '560,564s/logErrorAt/logWarningAt/' Ochr/Notation.lean` and `sed -i 's/^#guard /#eval  /' Ochr/Examples/*.lean`. Then run `DUMP_OUT=… DUMP_LOCATED=0|1 lake env lean <scratch>/dump2/Dump.lean` on each side and `diff`. Every changed row is a finding.
6. Run `lake exe sweep` and `lake exe sweep --probes` on both sides and compare from the first `states checked` line on (`sed -n '/^states checked/,$p'`); `lake exe sweep --pushes` must report no value in flight without a type in a typed run. Then run the probe files under `ochr/core/probes` on both sides, normalising "warning:" to "error:" on the softened side.
7. Update `DECISIONS.md`, `RULES.md` (the rule's text and the history line), and the paper if the rule's text is there. Then `typst compile main.typ main.pdf`, and check that `pdftotext -f 25 -l 25` contains "Conclusion" and that page 26 starts with "Bibliography".
8. Two commits (code and tests; documents), each with the full reason and the evidence, ending with the single `Co-Authored-By:` line.
9. Rebase onto `origin/main`, rebuild green, `git merge --ff-only` in the main checkout and push. If main moved meanwhile, rebase and retry. Then remove the worktrees (`--force` for the softened baseline) and delete the branch, locally and on the remote.

## Traps

- **Conflicts on every landing.** `DECISIONS.md` is append-only, so two lanes always conflict at its end. Resolve by deleting the markers only, never with a regular expression over the file (one attempt collapsed a blank line 700 lines up). `git checkout -m <file>` restores the conflict if the resolution goes wrong. The history in `RULES.md` is one long line 3 that every lane prepends to: take HEAD's line and prepend your sentence. `main.pdf` conflicts as a binary: recompile it, do not choose a side.
- **Page 25.** Check that the Conclusion is on page 25, not the page count, and check again after every rebase that touched `paper/`.
- **The dump.** One line per row: `Block.row: verdict / message @ location [log N]`. The located mode carries byte offsets and counts of editor notes, so an edit above a row shifts locations: compare against a baseline with the same example files. A green softened build proves nothing about rows expected to be rejected: read the dump, not the build, when probing. A guard on a rejected row must read the message.
- **The sweep.** It prints "FAILED" on main by design (known clause faults), so compare outputs and do not read the exit status. `--probes` is a separate small set. As of 2026-11-21 it records states at the outermost call depth only; a mode for every depth is being added.
- **Shell and tooling.** On NixOS `#!/bin/bash` does not exist (run `bash script.sh`). In zsh an unmatched glob aborts the whole line (`rm -f dir/*` on an empty directory), and `echo ===` is an error. The main checkout's `.lake` is usually stale and can crash `lake env lean`: use a built worktree.
- **The machine is shared.** Long jobs need `taskset -c 0-14`, and timings are comparable only when interleaved at equal load. Never `git stash` (the stash is shared by every worktree): commit work in progress and amend.
- **Proofs about the checker.** A probe that edits a function `StabilitySig.lean` reasons about breaks the build. Stub the proof with `sorry` only in the probe run, and restore from a saved copy.
- **One verification job at a time in a checkout.** A second job's `git checkout` switches the tree under the first.

## More from later landings (D107 to D109)

- **Build the exact commit you push.** Merging a sibling's examples or `Registry` changes is a rebase too. Never push and then build: `main` must not hold a commit nobody has built, even for a minute, because other lanes fetch it.
- **`RULES.md` line 3.** Split your own clause off at the `v2.1 also has D` that follows it, then prepend it to HEAD's line. Splitting on a fixed prefix such as "D10" once swallowed a following "D110" clause and duplicated it.
- **A dump from before a rebase does not carry over.** Run the baseline at the new `origin/main` in a second detached worktree, its `.lake` reflink-copied from your own build, in parallel with your branch's run. A whole cycle (build, dump, sweep, probe files) takes about 15 minutes on both sides.
- **A change that adds rows to an existing block.** `sweep` over main's blocks will not match. Sweep that block alone on both sides and show the two differences are equal.
- **Showing that a change of equality or of a decision moves nothing.** Build a throwaway variant that computes both answers and rejects with a marker string wherever they differ, then grep the dump and the probe outputs for the marker. Proofs in `StabilityDecide` / `StabilityFootprint` break on such variants: stub them with `sorry` in the probe build only, from saved copies, and restore before the real build.
- **The session scratch directory is shared by every agent.** Write logs under a subdirectory of your own.
- **What is reachable from `checkProgram`.** `Scratch/Reach.lean` walks every constant reachable from it and lists those the kernel cannot see into, with the chain that reaches each. Grepping does not do this job: an earlier census by grep missed a `while` loop.
- **Before starting a fix, look for a worktree that already has it.** Two agents once built the same fix at the same time; `git worktree list` and a glance at uncommitted changes in the sibling worktrees costs a minute.
- **Differential rows.** When a fix makes two forms behave alike (a plain borrow and a borrow a call returns; a generic function and its closed calls), generate the table: every operation by every variant, the two columns side by side, verdict and value. Count the rows that differ before and after.

## Before fixing a fault: hunt its class

Added by the orchestrator from the night of 2026-11-20. Each of the two soundness faults found that night turned into several once the fixing agent, before changing anything, tried every other route to the same root: the positivity hole had a second, independent hole of the same kind; the unchecked write to a dependent field had three routes to `False`. So: reproduce with a control in the same file; shrink and re-check; state the root as "the checker trusts X without checking it"; list every other place it does that; write one program per place and run it; send each accepted wrong program as it is found; only then fix, and assert every program of the hunt.

## From the lane that landed D104 to D111 and the sweep at every call depth

Its final report, 2026-11-21, kept for whoever lands the next change.

- **Cost is instructions retired, not time.** `perf stat -e instructions:u -x, -o f taskset -c 6 <exe>`, reading the `cpu_core` line. Paired wall-clock runs of one binary varied by up to 70% with the load on the sibling hyperthread (cores 2k and 2k+1 share a P-core; 12 to 19 are E-cores); instruction counts agree to 0.05%.
- **Background jobs go through the tool's own background mode.** A shell `&` job is killed when the call returns; one verification chain was lost that way.
- **The dump tool** is a scratch `VerdictDump.lean` plus an uncommitted `lean_exe vdump` entry in the lakefile, kept as a patch file. Revert the lakefile before every commit and rebase (a rebase refuses with it dirty, and `git stash` is forbidden). Building both sides at once with the cores split 0 to 7 and 8 to 14 halves a cycle. A rebase that touched only `docs/` needs no rebuild; check with `git diff --stat <old> <new> -- ochr/core`.
- **Main moves under a landing.** It moved six times during D111's. Budget for repeated rebase, build and dump cycles.
- **Rules about borrows ending belong in `endTopLoan`,** the one place every [Access] ends a borrow (D106). D65's earlier checks in the drops stay for their messages and test the same condition.
- **A temporary's stored type (D104) is never read by the checker:** `tyAt` of a temporary is `none`, so [Repack] at a borrow's end runs only when a binding holds the borrow. Harmless so far, because a temporary is never a place's root.
- **Typing belongs to an evaluation, not to a state.** The sweep's `MState.typing` is the innermost evaluation's flag, while frames are shared by nested runs of different typing. A clause of the form "in a typed run, every …" is therefore unsound at depth or inside private copies; test facts about pushes with `--pushes`, which logs at the push.
- **`evalCall` has a `given` parameter** (the head's and the arguments' types from the caller), used only by `closeBlock`. Use it rather than computing types for untyped calls.
- **A new function in `Decide` reached from one proved in `StabilitySig`** needs a `SigPres` lemma and an `sp_ext` registration (see D105's `sigPres_inferFrom`).
- **A wrong decision can hide as cost.** The index bug in `ctorNeedsCtx` cost 13% of checking time, in codomains computed for hints nobody needed.
- **Showing a fact about a state.** A hole `?` with `located := true` prints Ω at that point. For a fact at depth, `lake exe sweep --deep-private <Block>` with a block filter takes seconds.
- **Dependent-field code:** a field's parameters are `var 0 … var (np-1)` whichever field it is; the fields come after the parameters (`IndDecl.fieldRefs`).
- **Known and unfixed on main:** `Fuzz.Lib` has not built since D84 (`AddMZeroL` fails [Id-typestate]); it is not a default target.
