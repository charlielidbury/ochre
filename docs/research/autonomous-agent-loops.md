# Autonomous AI Coding Loops: What Works, What Doesn't, and Why They Fall Off the Rails

**Motivation:** Ochre uses a `loop.sh` script that spawns sequential Claude Code
agents, each picking up where the last left off via git history and
`PROGRESS.md`. After 4–5 iterations the agents reliably drift — losing
coherence, repeating failed approaches, or wandering off-task. This document
surveys public examples of autonomous agent loops at scale and distills the
techniques that made them work.

---

## 1. Case Studies

### 1.1 Anthropic: 16 Agents Build a C Compiler

**Source:** [Building a C compiler with a team of parallel Claudes](https://www.anthropic.com/engineering/building-c-compiler) (Nicholas Carlini, Anthropic Safeguards team)

**What they built:** A 100,000-line Rust-based C compiler ("CCC") that compiles
Linux 6.9 on x86, ARM, and RISC-V, passes 99% of GCC's torture tests, and
runs FFmpeg, SQLite, Postgres, and Redis.

**Scale:** ~2,000 Claude Code sessions, $20K (2B input tokens, 140M output
tokens), two weeks.

**The loop:**

```bash
while true; do
    COMMIT=$(git rev-parse --short=6 HEAD)
    LOGFILE="agent_logs/agent_${COMMIT}.log"
    claude --dangerously-skip-permissions \
           -p "$(cat AGENT_PROMPT.md)" \
           --model claude-opus-X-Y &> "$LOGFILE"
done
```

Each agent starts fresh with only the repo (including `AGENT_PROMPT.md` and
progress files). No explicit orchestrator — agents independently pick "the
next most obvious problem."

**Coordination (parallel agents):** Git-based task locking. Agents claim work by
creating a file in `current_tasks/` (e.g., `current_tasks/parse_if_statement.txt`)
and committing + pushing. Git's linear history means only one agent can
successfully push a given filename; the loser picks a different task. On
completion, the agent deletes the lock file.

**What made it work:**

1. **Test quality was everything.** Carlini: "Claude solves whatever problem the
   verifier defines." If the tests are wrong or incomplete, the agent solves
   the wrong problem. He used GCC's torture test suite as the primary oracle.

2. **Minimal, structured test output.** Verbose logs flood the context window.
   Tests were designed to output minimal text with a consistent error format
   (`ERROR: [reason]`) so agents could grep for failures. Detailed logs went
   to separate files.

3. **`--fast` flags for time-blind agents.** Agents have no sense of time and
   will happily run thousands of tests for hours. He added `--fast` modes that
   ran 1–10% of tests (deterministic per-agent, varied across VMs) so agents
   could detect regressions quickly without burning their context on test
   output.

4. **Oracle-based debugging.** When agents couldn't figure out why a program
   broke, they compiled random subsets of files with GCC (the known-good
   compiler) to binary-search for the broken file.

5. **Naturally decomposable tasks.** Each failing test was an independent unit
   of work. In later phases, agents specialized — one consolidated duplicate
   code, another optimized performance, another improved Rust idioms.

6. **Extensive in-repo documentation.** `AGENT_PROMPT.md`, READMEs, and
   progress files let fresh agents self-orient without handoff.

7. **The GCC oracle trick (key for parallelization).** When 16 agents all
   tried to compile the Linux kernel, they all hit the same bug and
   overwrote each other's fixes. Carlini's solution: a harness that
   randomly compiled most kernel files with GCC and only a subset with
   CCC. Each agent (different random seed) hit different bugs in different
   files, enabling true parallelism.

8. **CI pipeline for regression prevention.** When agents started breaking
   each other's work, they added CI ensuring new commits couldn't regress
   existing passing tests. This was crucial for maintaining forward progress.

9. **Model generation mattered.** Opus 4 was "barely capable," Opus 4.5
   could pass test suites but not compile real projects, Opus 4.6 crossed
   the threshold for production-scale compilation.

**What hit limits:**

- The compiler reached "the limits of Opus's abilities" — it couldn't
  independently implement 16-bit x86 code generation and had to shell out to
  GCC for that phase.
- New features frequently regressed existing functionality, suggesting the
  approach struggles with architectural coherence.
- Generated code was less efficient than `gcc -O0`.
- Critics noted this was an "in-distribution" problem — compilers are
  exhaustively documented in training data.

---

### 1.2 Cursor: Thousands of Agents Build a Web Browser

**Source:** [Scaling long-running autonomous coding](https://cursor.com/blog/scaling-agents) (Cursor / Anysphere)

**What they built:** "FastRender" — a web browser from scratch including an HTML
parser, CSS cascade/layout engine, text shaper, painter, and a custom
JavaScript VM. ~3M lines of code, ~30,000 commits over one week.

**Scale:** ~2,000 concurrent agents at peak, 10 million tool calls, 1,000
commits/hour at peak.

**What failed first: flat hierarchies.**

Their initial design gave all agents equal status with shared file locks for
coordination. This failed catastrophically:

- **Lock bottlenecks:** "Twenty agents would slow down to the effective
  throughput of two or three, with most time spent waiting."
- **Lock mismanagement:** Agents held locks indefinitely, acquired locks they
  already owned, or modified shared files without acquiring locks.
- **Risk aversion:** Without hierarchy, agents avoided difficult tasks and made
  only "small, safe changes," leading to "work churning for long periods
  without progress."

**What worked: the Planner–Worker–Judge pipeline.**

They introduced role-based specialization:

| Role | Responsibility |
|------|----------------|
| **Planner** | Continuously explores the codebase, creates tasks. Can spawn sub-planners for specific areas (planning is itself parallel and recursive). |
| **Worker** | Accepts a task, grinds until done, pushes changes. No inter-worker coordination. |
| **Judge** | Evaluates progress at each cycle's end. Decides whether to continue or restart fresh. |

This solved most coordination problems and let them scale to very large
projects.

**Key findings:**

1. **"The prompts matter more."** "A surprising amount of the system's behavior
   comes down to how we prompt the agents. Getting them to coordinate well,
   avoid pathological behaviors, and maintain focus over long periods required
   extensive experimentation. The harness and models matter, but the prompts
   matter more."

2. **Model choice matters a lot.** They found GPT-5.2 was "much better" than
   alternatives for long-running autonomous work — "maintaining focus, avoiding
   drift, and implementing things precisely and completely." Opus 4.5 "tends to
   stop earlier and take shortcuts when convenient." They use different models
   for different roles.

3. **Removing complexity helped more than adding it.** An "integrator role" for
   quality control created more bottlenecks than it solved. Workers were
   already capable of handling merge conflicts themselves.

4. **Feedback loops via specifications.** Web standards (HTML/CSS/JS specs) as
   git submodules + screenshot comparisons with vision models to validate
   rendering progress.

5. **Tolerance for intermittent breakage.** Allowing temporary compilation
   errors enabled higher throughput than requiring every commit to be clean.

6. **Periodic fresh starts remain necessary.** Even with the pipeline, "periodic
   fresh starts" are needed to combat drift and tunnel vision.

**Guardrails from [Cursor's best practices](https://cursor.com/blog/agent-best-practices):**

- Start new conversations when "the agent seems confused or keeps making the
  same mistakes" or when "you've finished one logical unit of work."
- Let the agent find its own context via search rather than pre-loading files.
- Test-driven: write tests first, confirm they fail, then implement.
- If the agent builds something wrong, revert and refine the plan rather than
  trying to fix through follow-up prompts.

---

### 1.3 The "Ralph Loop" Pattern

**Sources:**
[ralph-claude-code](https://github.com/frankbria/ralph-claude-code),
[Addy Osmani — Self-Improving Agents](https://addyosmani.com/blog/self-improving-agents/),
[claudefast — Autonomous Agent Loops](https://claudefa.st/blog/guide/mechanics/autonomous-agent-loops)

The "Ralph Wiggum Loop" (named by Geoffrey Huntley) is the community's
standard pattern for serial autonomous agent loops — essentially what Ochre's
`loop.sh` implements. The core insight: **each iteration starts with a clear
slate and explicit instructions** rather than one massive prompt.

**The canonical loop:**

1. Pick the next incomplete task from a task list
2. Implement code for that specific feature
3. Validate via tests and type checks
4. Commit if checks pass
5. Update task status and log learnings
6. Reset context and repeat

**Memory across iterations (the AGENTS.md / PROGRESS.md pattern):**

| Mechanism | Purpose |
|-----------|---------|
| `AGENTS.md` / `PROGRESS.md` | Living handbook of patterns, gotchas, what was tried |
| Git commit messages | What changed and why — agents read `git log` to orient |
| `progress.txt` / task JSON | Ground truth about which tasks are done/pending/failed |
| `AGENT_PROMPT.md` | Persistent instructions that every agent reads first |

**Failure modes the community has identified:**

| Problem | Root Cause | Fix |
|---------|-----------|-----|
| Agent ends too early | Weak verification / no clear completion signal | Add tests; explicit completion criteria |
| Agent spins forever | Impossible task or missing exit condition | Max iterations; clarify completion signals |
| Agent loses coherence | Context noise accumulation over long runs | Fresh starts after major chunks |
| Agent repeats failed approaches | No record of what was tried | Document failures in progress files |
| Agent drifts off-task | Vague or overly broad prompt | Scope tightly; tell agent what's in-bounds AND what's off-limits |
| Agent makes only tiny safe changes | No clear ownership or priority | Explicit task assignment; hierarchy |

---

### 1.4 Anthropic's Harness Design Guide

**Source:** [Effective harnesses for long-running agents](https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents)

Anthropic's own guide for building outer loops. Key insights:

- **Separate initializer from worker.** The first agent sets up the
  environment (init scripts, progress files, initial commit). Subsequent
  agents get different instructions focused on incremental work.

- **Feature tracking JSON.** A file listing 200+ features, each marked
  "passing" or "failing." Agents work through the list. The constraint:
  "It is unacceptable to remove or edit tests because this could lead to
  missing or buggy functionality."

- **Agents lie about completion.** "Claude's tendency to mark a feature as
  complete without proper testing" is a real problem. Solution: give agents
  browser automation tools (Puppeteer) and instruct them to test as users
  would, not just verify syntax.

- **Context resets beat compaction.** Fresh context each iteration reduces
  confusion better than trying to compress/summarize prior context.

- **The analogy:** "Imagine a software project staffed by engineers working in
  shifts, where each new engineer arrives with no memory of what happened on
  the previous shift." The entire harness design is about making that handoff
  work.

---

### 1.5 Anthropic's Three-Agent Harness (Newest Pattern)

**Source:** [Harness design for long-running application development](https://www.anthropic.com/engineering/harness-design-long-running-apps)

Anthropic's most recent guidance introduces a three-agent architecture that
addresses the self-evaluation problem head-on:

| Agent | Role |
|-------|------|
| **Planner** | Transforms a brief prompt into a detailed spec with feature lists, user stories, and requirements |
| **Generator** | Works incrementally through features with explicit decomposition |
| **Evaluator** | Provides external feedback via active testing (separate agent with fresh context) |

**Why separation matters:** "When asked to grade their own work, agents
confidently praise the work — even when quality is obviously mediocre."
Separating generation from evaluation was one of the most impactful changes.

**Key meta-insight:** "Every component in a harness encodes an assumption about
what the model can't do on its own, and those assumptions are worth stress
testing." As models improve, scaffolding requirements shrink. With Opus 4.5,
the "sprint" construct became unnecessary.

### 1.6 OpenAI Codex: Long-Horizon Tasks

**Source:** [Run Long Horizon Tasks with Codex](https://developers.openai.com/cookbook/examples/codex/long_horizon_tasks/)

OpenAI documented a four-file durable memory pattern:

| File | Purpose |
|------|---------|
| `Prompt.md` | Spec — "Freeze the target so the agent doesn't build something impressive but wrong" |
| `Plan.md` | Milestones with acceptance criteria and validation commands |
| `Implement.md` | Runbook telling agent to follow the plan, keep diffs scoped, run validations |
| `Documentation.md` | Real-time status log of decisions, current milestone, known issues |

A demo ran Codex for ~25 hours uninterrupted, ~13M tokens, ~30K lines.
Performance was strong on following specs, staying on task, and repairing
failures — but only because the spec was frozen and each milestone had a
concrete validation command.

### 1.7 The AGENTS.md Research Paper

**Source:** [Codified Context Infrastructure (arXiv 2602.20478)](https://arxiv.org/html/2602.20478v1)

A 2026 research paper documented a three-tier context architecture used to
build a 108,000-line C# system over 283 sessions:

- **Tier 1 (Hot):** ~660-line project constitution, always loaded. Coding
  standards, build commands, architectural patterns, task routing.
- **Tier 2 (Domain):** 19 specialized agent specs (115–1,233 lines each)
  with domain-specific knowledge, created when repeated debugging indicates
  knowledge gaps.
- **Tier 3 (Cold):** 34 subsystem spec documents (~16,250 lines) retrieved
  on-demand via MCP.

Context infrastructure comprised 24.2% of total project lines. The presence
of AGENTS.md was associated with 29% reduction in median runtime and 17%
reduction in output tokens. The primary failure mode was **specification
staleness** — agents generating code conflicting with recent refactors.
Maintenance overhead averaged 1–2 hours weekly.

---

## 2. Why Loops Fall Off the Rails After N Iterations

Synthesizing across all sources, the failure modes cluster into a few
categories:

### 2.1 Context Degradation and Attention Drift

Each agent reads the repo state, but doesn't truly understand the *trajectory*
of the project. After several iterations, the accumulated state (progress
files, partial changes, failed experiments) becomes noise rather than signal.
Agents start misinterpreting the current situation.

Research on [agent drift](https://www.chanl.ai/blog/agent-drift-silent-degradation)
quantifies this: system prompt instructions lose weight as context grows
(transformer attention mechanism). Drift becomes measurable around 20–100
turns, with ~2% accuracy degradation per reasoning step. A 20-step workflow
compounds to roughly 40% failure rates. Context drift has been identified as
causing 65% of enterprise AI failures.

**Ochre-specific risk:** The Lean proof state is highly interdependent. An agent
that doesn't deeply understand *why* the previous agent made a choice will
undo it or build on wrong assumptions.

### 2.2 No Verifiable Completion Signal

Carlini's compiler had GCC's torture tests. Cursor had web specs + screenshot
diffs. When the only signal is "does `lake build` pass?" and it already
passes (with `sorry`s), agents lack a tight feedback loop to know if they're
making progress or spinning.

The [SWE-EVO benchmark (arXiv 2512.18470)](https://arxiv.org/html/2512.18470v2)
found a stark gap between short-task and long-horizon performance: GPT-5 with
OpenHands achieved 65% on SWE-Bench (single issues) but only 21% on long-
horizon software evolution tasks. The primary failure mode was instruction
following — misinterpreting or incompletely addressing long, nuanced specs.

### 2.3 Task Granularity Mismatch

The compiler worked because each failing test was an atomic, independent unit.
Ochre's problem — proving soundness of a type system — is deeply
interconnected. Changing one definition can invalidate work across multiple
files. This is fundamentally harder to parallelize or serialize into
independent iterations.

### 2.4 Insufficient Failure Documentation

When agents don't know what was already tried and *why it failed*, they repeat
the same approaches. Ochre's `PROGRESS.md` and commit messages help, but the
failure modes of proof attempts are subtle and hard to communicate in text.

### 2.5 Premature Commitment / Tunnel Vision

Agents tend to commit to the first approach and grind on it rather than
stepping back to reconsider. After 4–5 iterations of agents all trying
variations of the same broken approach, the project is stuck.

### 2.6 Self-Evaluation Bias

Agents grade their own work too generously. Anthropic found agents
"confidently praise the work — even when quality is obviously mediocre."
Without external evaluation, agents declare problems solved prematurely.

### 2.7 Specification Staleness

The AGENTS.md paper found that as codebases evolve, the persistent context
documents lag behind. Agents then generate code that conflicts with recent
refactors. This is especially relevant for Ochre, where definitions change
frequently and SUGGESTIONS.md can become outdated within a few iterations.

---

## 3. Recommendations for Ochre's Loop

Based on the patterns above, here's what might help:

### 3.1 Tighten the Feedback Loop

The compiler had per-test pass/fail. Ochre needs something analogous.
Possibilities:

- **Sorry count as a metric.** Track the number of `sorry`s in each commit.
  Agents should be instructed that their job is to reduce this number (or
  produce documented evidence that a theorem statement is wrong).
- **Per-sorry acceptance tests.** For each sorry, write a `#check` or
  `example` that would succeed if the sorry were filled. This gives agents a
  concrete target.
- **`lake build` exit code is necessary but not sufficient.** The real signal
  is sorry count + test pass count.

### 3.2 Document Failures Aggressively

Carlini's agents had test output. Ochre's agents need something like a
`DEAD_ENDS.md`:

```markdown
## Attempted: bind self to annotation type (Option D)
- Agent: ochre-20260405-091658
- What: absEval binds self to opaque type variable in context
- Why it failed: Church-encoded types have inner mus with symbolic bvar
  annotations; domain checks fail on symbolic applications
- Specifically: [file:line] — this case returns none because ...
- Don't retry unless: you have a way to handle symbolic bvar annotations
```

The current SUGGESTIONS.md does some of this but it's mixed in with the
roadmap. A dedicated "what was tried and why it failed" file prevents the
#1 failure mode (repeating dead ends).

### 3.3 Scope Each Iteration More Tightly

Instead of "work on the highest priority sorry," consider:

- **One sorry per session, named explicitly.** "Your task: fill the sorry at
  Soundness.lean:XXX. If you cannot fill it, document exactly why and what
  you tried."
- **Time-box and exit.** "If you haven't made progress in 20 minutes, stop.
  Document what you tried and why it didn't work. This documentation IS
  your contribution."

### 3.4 Add a Judge / Review Step

Cursor's Planner–Worker–Judge pipeline worked because the judge could decide
"this isn't working, restart fresh." Ochre's loop could add a lightweight
review step between iterations:

```bash
# After agent finishes, before starting next:
claude -p "Read PROGRESS.md and the last 3 commits. Is the project making
progress or stuck in a loop? If stuck, update SUGGESTIONS.md with what
to try differently."
```

### 3.5 Rotate Strategy Explicitly

After N iterations on the same approach, force a strategy change:

```markdown
# In AGENT_PROMPT.md:
If the last 2 agents worked on the same sorry and didn't resolve it,
you MUST try a fundamentally different approach or work on a different
sorry. Read their commit messages to understand what they tried.
```

### 3.6 Consider the Task's Suitability

The honest takeaway from the case studies: autonomous loops work best on
**decomposable, independently testable** problems. Compilers are ideal —
each language feature is semi-independent and has a clear test. Theorem
proving is at the other extreme — proofs are deeply interdependent, progress
is hard to verify automatically, and the "right" approach requires deep
understanding of the mathematical structure.

Ochre's problem may simply be harder for autonomous loops than a compiler or
browser. The most impactful intervention might not be improving the loop
mechanics, but restructuring the *work* to be more loop-friendly:

- Break the soundness proof into lemmas that can be proved independently
- Create concrete test cases for each lemma (not just "does it compile")
- Make each lemma's proof self-contained enough that an agent can work on it
  without understanding the full proof structure

---

## 4. Summary Table

| Project | Duration | Agents | Output | Key Technique | Why It Worked |
|---------|----------|--------|--------|---------------|---------------|
| Anthropic C compiler | 2 weeks | 16 parallel | 100K LOC | Test-driven + git task locks | Independently testable units |
| Cursor FastRender | 1 week | ~2,000 peak | 3M LOC | Planner–Worker–Judge pipeline | Role specialization + specs as oracle |
| Ralph loops (community) | Hours–days | 1 serial | Varies | Task JSON + fresh context each iteration | Atomic tasks + clear completion signals |
| Anthropic harness guide | N/A | 1 serial | N/A | Initializer + worker separation | Feature checklist + browser testing |

---

## 5. The Consensus Playbook

Across all sources, these techniques consistently appear in successful
autonomous loops:

1. **Git as memory, not context window.** Fresh context per iteration. Let
   files and commit history carry state.
2. **Durable markdown files as project memory.** Spec, plan, progress log,
   decision log, guardrails — all persisted to disk, read each iteration.
3. **Tests as the primary guardrail.** Machine-verifiable pass/fail signals
   that agents can act on without human judgment. TDD loop is the most
   reliable autonomous pattern.
4. **Hooks over prompts for critical rules.** Deterministic enforcement
   (linters, formatters, test runners, pre-push hooks) beats advisory
   instructions.
5. **Separate generation from evaluation.** Never let an agent grade its own
   work. Use a different session, agent, or human reviewer.
6. **Small atomic tasks.** Decompose work into checkpoint-sized pieces with
   explicit "done when" criteria.
7. **Stop conditions.** Max iterations, time limits, idle detection, spend
   limits. The Ralph loop defaults to 20 iterations max.
8. **Keep persistent context concise.** Anthropic recommends CLAUDE.md under
   200 lines / 2,000 tokens. If it's too long, rules get lost.
9. **Periodic fresh starts.** Even within a project, reset context to combat
   tunnel vision and accumulated confusion.
10. **Document failures, not just successes.** A guardrails.md or dead-ends
    file that records what was tried, why it failed, and when to retry
    prevents the #1 failure mode.

---

## Sources

**Primary case studies:**
- [Building a C compiler with a team of parallel Claudes](https://www.anthropic.com/engineering/building-c-compiler) — Anthropic Engineering (Carlini)
- [Scaling long-running autonomous coding](https://cursor.com/blog/scaling-agents) — Cursor
- [FastRender: a browser built by thousands of parallel agents](https://simonwillison.net/2026/Jan/23/fastrender/) — Simon Willison

**Anthropic engineering guides:**
- [Harness design for long-running application development](https://www.anthropic.com/engineering/harness-design-long-running-apps) — three-agent architecture
- [Effective harnesses for long-running agents](https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents) — initializer/worker pattern
- [Long-running Claude for scientific computing](https://www.anthropic.com/research/long-running-Claude) — tmux + HPC clusters

**Best practices and community patterns:**
- [Best practices for coding with agents](https://cursor.com/blog/agent-best-practices) — Cursor
- [Self-Improving Coding Agents](https://addyosmani.com/blog/self-improving-agents/) — Addy Osmani
- [Autonomous Agent Loops](https://claudefa.st/blog/guide/mechanics/autonomous-agent-loops) — claudefast
- [Everything is a Ralph Loop](https://ghuntley.com/loop/) — Geoffrey Huntley (originator)
- [ralph-claude-code](https://github.com/frankbria/ralph-claude-code) — GitHub
- [Run Long Horizon Tasks with Codex](https://developers.openai.com/cookbook/examples/codex/long_horizon_tasks/) — OpenAI

**Research on drift and failure modes:**
- [Agent drift: the silent degradation](https://www.chanl.ai/blog/agent-drift-silent-degradation) — Chanl
- [Asymmetric Goal Drift in Coding Agents](https://arxiv.org/html/2603.03456v1) — arXiv
- [Codified Context Infrastructure](https://arxiv.org/html/2602.20478v1) — arXiv (AGENTS.md paper)
- [SWE-EVO: long-horizon software evolution benchmark](https://arxiv.org/html/2512.18470v2) — arXiv
- [The Three Developer Loops](https://itrevolution.com/articles/the-three-developer-loops-a-new-framework-for-ai-assisted-coding/) — Gene Kim & Steve Yegge
- [8 Tactics to Reduce Context Drift](https://lumenalta.com/insights/8-tactics-to-reduce-context-drift-with-parallel-ai-agents/) — Lumenalta
