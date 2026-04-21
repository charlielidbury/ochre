# Claude-in-CI for Doc/Lean Cross-Reference Sync

## Goal

Markdown in `docs/` frequently cites Lean files and vice versa. As the codebase
moves, these citations rot. We want: on every PR, a mandatory workflow that
invokes the `claude` CLI on the self-hosted runner to (a) verify
cross-references, (b) auto-fix anything fixable and push the fix to the PR
branch, (c) leave a PR comment listing anything it couldn't fix, and (d) block
merge until a clean run exists on the PR's head SHA.

This doc is the design. The workflow YAML, setup commands, and branch
protection rules should all be visible and scriptable via `gh` so agents can
read this file and reproduce/modify the setup without web-UI clicks.

## Design decisions

### Auth: fine-grained PAT, not GitHub App

We need Claude's pushes to *re-trigger* the workflow on the new HEAD SHA —
otherwise branch protection sees a stale green on the pre-fix SHA. Pushes made
with the default `GITHUB_TOKEN` deliberately don't re-trigger (GitHub's loop
guard). Three ways around this:

1. **GitHub App token** — canonical for org/team setups. Bot identity, no seat,
   scoped install. Downside: App creation is a web-UI step, adds moving parts
   (App ID, private key, installation ID).
2. **Fine-grained PAT** — single secret, tied to one user. Simpler, equally
   effective for a solo repo. PAT creation is web-UI but a one-time step.
3. **`GITHUB_TOKEN` + self-posted commit status** — no re-trigger; Claude
   explicitly marks the new SHA via `gh api -X POST /repos/:o/:r/statuses/:sha`.
   Clever but relies on Claude self-reporting its own pass — acceptable because
   Claude *is* the oracle for doc-sync (there's no external validator to
   disagree with it), but not a pattern to generalize.

**Pick:** fine-grained PAT. Cleanest path to "workflow re-runs on the fixed
SHA", minimal setup, conventional. Rotation cadence ≈ yearly.

PAT scopes (for `charlielidbury/ochre` only):
- `contents: read/write` (push fixes)
- `pull-requests: read/write` (comment)
- `metadata: read` (required)

### Runner

`runs-on: self-hosted` — the server already has `claude` installed and
authenticated. No token or API key needs to be wired into the workflow for
Claude itself; it runs under the user that owns the runner.

### Invocation

`claude -p "<prompt>"` in non-interactive print mode. The prompt tells Claude
to diff `origin/main...HEAD`, audit citations in the touched files, apply
fixes, and emit a JSON report for the workflow to read and turn into a PR
comment if non-empty.

Scope the audit to the diff, not the whole repo — keeps runtime bounded and
avoids Claude fixing unrelated rot outside the PR's intent.

## Workflow sketch

`.github/workflows/doc-sync.yml`:

```yaml
name: doc-sync
on:
  pull_request:
    types: [opened, synchronize, reopened]
    paths:
      - 'docs/**'
      - 'lean/**'
      - '**/*.md'

concurrency:
  group: doc-sync-${{ github.event.pull_request.number }}
  cancel-in-progress: true

jobs:
  audit:
    runs-on: self-hosted
    permissions:
      contents: write
      pull-requests: write
    steps:
      - uses: actions/checkout@v4
        with:
          token: ${{ secrets.OCHRE_BOT_PAT }}
          ref: ${{ github.event.pull_request.head.ref }}
          fetch-depth: 0

      - name: Run Claude audit
        id: audit
        env:
          GH_TOKEN: ${{ secrets.OCHRE_BOT_PAT }}
          PR_NUMBER: ${{ github.event.pull_request.number }}
          BASE_REF: ${{ github.event.pull_request.base.ref }}
        run: |
          set -euo pipefail
          git config user.name  "ochre-doc-sync"
          git config user.email "ochre-doc-sync@users.noreply.github.com"

          claude -p "$(cat .github/prompts/doc-sync.md)" \
            --output-format json \
            > claude-report.json

          # Claude writes unfixable items to report.unfixable[]
          # and applies fixes directly to the working tree.

          if ! git diff --quiet; then
            git add -A
            git commit -m "doc-sync: auto-fix cross-references

            Co-Authored-By: Claude <noreply@anthropic.com>"
            git push
          fi

          UNFIXABLE=$(jq '.unfixable | length' claude-report.json)
          if [ "$UNFIXABLE" -gt 0 ]; then
            jq -r '.unfixable[] | "- " + .'  claude-report.json \
              | gh pr comment "$PR_NUMBER" --body-file -
            exit 1
          fi
```

The prompt lives at `.github/prompts/doc-sync.md` so it's versioned, reviewable,
and agents editing the behavior know where to look.

## Setup (all via `gh`)

One-time, after creating the PAT in the web UI:

```bash
# 1. Store the PAT
gh secret set OCHRE_BOT_PAT --body "<paste-pat>"

# 2. Confirm the self-hosted runner is registered and idle
gh api /repos/:owner/:repo/actions/runners

# 3. Add branch protection requiring the doc-sync check on main
gh api -X PUT /repos/:owner/:repo/branches/main/protection \
  -F required_status_checks.strict=true \
  -F 'required_status_checks.contexts[]=doc-sync / audit' \
  -F enforce_admins=false \
  -F required_pull_request_reviews.required_approving_review_count=0 \
  -F restrictions=
```

Agents inspecting the setup later:

```bash
gh secret list                                    # names only, not values
gh api /repos/:owner/:repo/branches/main/protection
gh workflow view doc-sync.yml
gh run list --workflow=doc-sync.yml
gh pr checks <pr-number>
```

## Open questions / gotchas

- **Infinite fix loop.** If Claude's fix introduces a new inconsistency,
  re-trigger re-fires Claude. The prompt should explicitly say "if you
  already applied a fix and the same issue persists, escalate to unfixable
  rather than loop." A belt-and-braces guard: inspect the last N commits for
  `ochre-doc-sync` authorship and bail if the chain is >2 deep.

- **Concurrency with human pushes.** If a developer pushes while Claude is
  running, the push-to-PR-branch will be rejected (non-fast-forward). The
  `concurrency` block cancels the in-flight run, but Claude may have already
  half-committed. Safe outcome: the cancelled run leaves no commit (we commit
  only after `claude -p` returns, which won't happen if cancelled); on re-run
  Claude starts fresh against the new HEAD.

- **Cost.** Every PR action burns Claude tokens. For a research repo with
  low PR volume this is fine; revisit if volume grows.

- **Non-determinism.** Claude may flag slightly different things run-to-run.
  Branch protection will see the final run's result; occasional "re-run to
  pass" is acceptable but if flakiness is frequent, tighten the prompt to
  reduce ambiguity in what counts as a broken citation.

- **Prompt drift.** The prompt is the spec for what "in sync" means. Keep it
  in `.github/prompts/doc-sync.md` and treat changes to it as policy changes
  — review them like code.
