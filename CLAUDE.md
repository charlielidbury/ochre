This repo contains a (very) work in progress programming language called Ochre.

The current focus is on proving out the metatheory via the construction and analysis of a core calculus called Och.

# Important Context
- docs/what-is-ochre.md - Explanation of what Ochre is/the broader vision
- docs/what-is-och.md - Explanation of what Och is (prone to getting outdated)
- docs/why-och-matters-for-ochre.md - The link between the two
- SUGGESTIONS.md - The central roadmap (what to try next). Named suggestions so agents/you don't feel like they are obligated to execute on this directly; oftentimes the most productive thing for them to do is an idea they came up with themselves.
- PROGRESS.md, DECISION-LOG.md - Internal logs of what happened for agents/you to co-ordinate across sessions.
- AGENT_PROMPT.md - The prompt given to the agents/you working on this project (agents/you are often made by the ./loop.sh script)

# Building / Tooling
Everything is built via the Nix flake at the repo root. The `.envrc` at the repo root runs `use flake`, so tooling (Lean, Rust nightly, Agda, OCaml) should be on PATH transparently via direnv — just run `lake build` / `cargo build` as normal. If tools are missing, surface this to the user and offer to fix the direnv/nix setup. Use `nix build .#och-lean` or `nix build .#compiler` for reproducible CI-style builds. Do not install elan/rustup manually.

Worktrees build WITHOUT `direnv allow` in this harness, and it is worth knowing why rather than being surprised by it: agent shells start in the primary checkout (where direnv is allowed), direnv exports the flake env as ordinary environment variables, and its swap hook only fires at interactive prompts — so `cd ../some-worktree && lake build` inherits the primary checkout's env regardless of cwd (verified: `DIRENV_FILE` still points at the primary `.envrc` from inside worktrees; a clean `env -i` shell in a worktree finds no lake at all). What PATH provides is the nix-store *elan shim*; the actual Lean toolchain is dispatched per-directory from the nearest `lean-toolchain` file (git provides it in every worktree), so branches that bump `lean-toolchain` get their own compiler. The residual caveat: NON-Lean flake tooling (and elan itself) stays pinned at the primary checkout's env — a branch changing the flake needs an explicit `nix develop` in its worktree for those changes to take effect.

# Git Context
Agents/you are prompted into putting what they did and their rational into commit messages in great detail. This is often the most efficient way to figure out **why** something was done or to get more details about something unclear.

A helper CLI called `claude-ask` is provided which can be used to ask agents/you questions based on the agent ID in the commit message which is very useful for getting more information about why things were done or more detail about what they tried. Usage: `claude-ask <agent-id-from-commit> "Your prompt goes here"`. The answer comes back over stdout.

# Worktree gotcha
`Agent({ isolation: "worktree" })` and `EnterWorktree` branch from the repo's default branch (`main`), **not** the session's current HEAD — despite docs claiming "based on HEAD". Always include an explicit `git reset --hard origin/<branch>` step at the start of any worktree-isolated agent prompt, or the agent will work on a stale codebase and produce commits that don't apply cleanly.