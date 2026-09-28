# Brief for everyone working on the Ochr core

Read this whole file, then `RULES.md`, then `DECISIONS.md`. Background (optional, read if your task touches it): `ochr/docs/00-idea.md` (the original problem), `ochr/docs/01-closing-off.md` and `ochr/docs/04-worked-example.typ` (earlier drafts of the close-off idea; superseded where they disagree with RULES.md), `ochr/docs/02-lit-review.md` (how other systems equate effectful programs). Papers are in `docs/papers/` (`aeneas.pdf`, `theory-of-lean.pdf`, `fire-triangle.pdf`, `qtt.pdf`, ...). If you read a paper, read all of it, not one section.

## The goal

A programming language that is both an efficient systems language (Rust-style `&mut` borrows, in-place mutation, no GC) and a theorem prover (Lean-style dependent types), with **no divide between specification and implementation and no divide between pure and impure code**. You write the in-place program once, and you prove things about *that program* directly, by the same definitional unfolding Lean uses for pure functions.

The motivating example:

```
AddM : Π(x : &Nat) (y : Nat). Unit          -- adds y onto *x in place: walk to the final Z, move y there
AddM x y := match *x { Z => *x := y | S p => AddM &p y }

AddMZero : Π(x : &Nat). Id Unit (AddM x 0) ()   -- "adding 0 in place has no effect"
AddMZero x := match *x { Z => refl | S p => AddMZero &p }
```

`Id Unit (AddM x 0) ()` compares two *computations*: their results and their effects on the places they write. That effect-sensitive equality is the novelty; without it this is existing work. The proof is plain structural recursion with no congruence lemma: the borrow structure of the environment performs the congruence.

The deliverable is a paper-quality **minimal core calculus** (a "diamond": every rule earns its place), with worked examples, a mechanised executable checker, and a metatheory story.

## Non-negotiable end goals (never overturn these)

1. No spec/implementation divide: proofs are about the efficient in-place program itself, not a pure model of it.
2. No pure/impure divide in the language: the programmer never marks code pure or effectful, any program may appear in a type, and the programmer never writes or sees backward functions or a second language.
3. `Id Unit (AddM x 0) ()` (effect-sensitive equality between computations) must be expressible and provable.

Everything else in `RULES.md` is a technical decision and may be overturned with a reason recorded in `DECISIONS.md`.

## How to treat complexity

**Complexity and edge cases are evidence that an earlier decision was wrong.** If a rule exists only to patch one example, or a derivation needs a special case, say so loudly and propose which earlier decision to revisit, rather than adding a patch. A shorter rule set that covers the same examples is always better.

## Conventions

- Plain language first, jargon second. Define any non-obvious term the first time you use it.
- No hard line wrapping in prose (the user uses soft wrap).
- `&T` means a mutable borrow (there are no shared borrows). `σ` is an abstract value (a free variable of the symbolic machine, exactly Lean's fvar). `Ω` is the environment.
- Derivations: conclusion first, premises indented below, comments after `//`, one machine step per line with the rule name.
- Every claim of the form "this derives" must show the derivation. Every claim "this is unsound" must show the concrete bad derivation (e.g. a proof of `Id Nat Z (S Z)` or of `⊥`).

## Where things live (branch `ochr-core`, worktree `/home/charlielidbury/repos/ochre-ochr-core`)

- `ochr/core/BRIEF.md` (this), `RULES.md` (the current rule set; owned by the lead, do not edit unless told), `DECISIONS.md` (decision log; lead-owned).
- `ochr/core/notes/<your-agent-name>.md`: your report. Write it incrementally (≤150 lines per write) so nothing is lost if you are interrupted.
- `ochr/core/paper/`: the typst paper (lead-owned).
- `ochr/core/lean/`: the Lean formalisation (owned by the formalisation agent).

Do not `git stash` (the stash stack is shared across worktrees). Commit only files you own; the lead commits notes unless told otherwise. If you build Lean, do it in your own git worktree unless told otherwise.

## Report format

Start your report with a 5-line summary: verdict, the most important finding, what (if anything) in RULES.md must change, confidence, and what you did not check.
