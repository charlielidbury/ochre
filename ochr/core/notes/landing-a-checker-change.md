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

## Before fixing a fault: hunt its class

Added by the orchestrator from the night of 2026-11-20. Each of the two soundness faults found that night turned into several once the fixing agent, before changing anything, tried every other route to the same root: the positivity hole had a second, independent hole of the same kind; the unchecked write to a dependent field had three routes to `False`. So: reproduce with a control in the same file; shrink and re-check; state the root as "the checker trusts X without checking it"; list every other place it does that; write one program per place and run it; send each accepted wrong program as it is found; only then fix, and assert every program of the hunt.
