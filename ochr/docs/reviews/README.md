# Paper reviews

## 2026-10-25: three independent referee reviews

- **Reviewed:** `ochr/core/paper/main.pdf` at commit `db541739668427f84f6dd83a9dc566139654467d` (branch `ochr-core`). The PDF there is byte-identical to the one last built at `eec447e3` (sha256 `c7f4c735…e168741`), 65 pages. The reviewers could also read the repository, as it stood at that commit, to check the paper's claims against it.
- **Reviewers:** three Opus agents (`paper-review-a`, `-b`, `-c`), given the identical prompt below, read-only, run in parallel. The point was to see what each noticed on its own and where they disagreed, so none saw the others' output.
- **Verdicts:** A weak reject (medium confidence), B weak reject (medium-high), C weak reject (high).
- **Files:** `2026-10-25-review-{a,b,c}.md`, verbatim.

The reviewers were later asked to save their full text to a scratch file outside the repo, because the final messages were cut off in transit. That instruction changed only how the review was delivered, not its content.

### The prompt (identical for all three)

```
You are an expert referee for a top programming-languages venue (POPL/ICFP/PLDI). Review the paper at /home/charlielidbury/repos/ochre-ochr-core/ochr/core/paper/main.pdf.

STRICTLY READ-ONLY. Do not create, edit, move or delete any file anywhere; do not run builds (no lake/cargo/typst/nix build), git commits, git stash, or anything that writes to disk. You may read any file in the repository (e.g. the paper source, the Lean checker, notes) to check claims against the artefact, but the paper itself is the object under review.

Read the WHOLE paper, every page, including appendices. It is 65 pages; use the Read tool with the pages parameter in chunks of at most 20 pages (e.g. "1-20", "21-40", "41-60", "61-65"). Do not skim or skip sections.

Write the review you would submit as a referee. Form your own judgement; there is no particular aspect you are expected to focus on. Use this structure so reviews can be compared:

1. Summary — what the paper claims and contributes, in your own words (one paragraph).
2. Overall assessment — accept / weak accept / borderline / weak reject / reject, with your confidence (low/medium/high) and a short justification.
3. Strengths — what is genuinely good.
4. Major concerns — issues that would need addressing before acceptance (correctness, soundness of claims, missing evidence, framing, positioning against related work, etc.). For each: what the problem is, where (page / section / rule / theorem), why it matters, and what would fix it.
5. Minor concerns — smaller technical or presentation issues, with page references.
6. Presentation and readability — structure, clarity, notation, figures, length, whether a reader can follow it.
7. Questions for the authors.
8. Typos / small errors (page-referenced).

Be specific and cite page numbers for everything. Be honest; do not soften criticism and do not invent problems. Your final message should be the full review text.
```
