# Pasquale & García-Pérez PSS checker — Lean port feasibility

Status: read-only investigation, no code touched.
Artifact: `pss/checker-artifact/` (PPDP 2025).
Existing Lean: `pss/Pss/Mpss/*.lean` (~4.8k LOC mechanizing the 2024 MPSS paper).

## 1. What the artifact actually is

**Total ~1936 LOC of Emacs Lisp** across 24 files. Breakdown:

| Module | LOC | Role | Port category |
|---|---:|---|---|
| `src/path-management.el` | 129 | path/sexp helpers; half is Emacs cursor/buffer plumbing, half is pure `get/replace-subexpression-at-path` | (a)+(b) split |
| `src/reduction.el` | 148 | β-substitution, `(y f)→(f (y f))`, `(top body)→top`, capture-respecting subst | (a) pure |
| `src/subtype.el` | 94 | `find-binding-type-in-sexp`, `promote-at-path` (variable→type, otherwise→top) | (a) pure |
| `src/refl.el` | 62 | α-equivalence on `(FUN v t b)` | (a) pure |
| `src/macroexpand.el` | 84 | global `*term-definitions*` alist; expand/collapse | (a) pure (with one `defvar` registry) |
| `src/or-split.el` | 40 | `(OR a b ...)` splitter (returns N goals) | (a) pure |
| `src/utilities.el` | 51 | `has-at-least-one-or-expression`, shadowing-aware variable-count | (a) pure |
| `src/compile.el` | 97 | term-traversal that emits proof obligations as `(env . arg . type)` | (a) pure |
| `src/replay.el` | 132 | interpreter for proof-script s-exprs (`start-term`, `rewrite`, `qed`, `focus`, `commit`) | (a) pure |
| `src/algorithms/base.el` | 1 | empty placeholder | n/a |
| `src/interactive/proof-mode-command.el` | 367 | spawn `*Term*`/`*Goal*`/`*Proof*` buffers, multi-window layout, `proof-mode-replay-proof` | (b) Emacs-only |
| `src/interactive/action-command.el` | 83 | wraps each pure op as a `(interactive)` command that mutates the buffer at point | (b) Emacs-only |
| `src/interactive/{logging,helper,all-binds}.el` | 82 | log writer, `C-c …` keymap, copy-sexp-at-point | (b) Emacs-only |
| `terms/{int,bool,list}.el` | 490 | Scott-encoded `*int*`/`*bool*`/`*list*`, plus `*plus*`, `*mult*`, `*fact*`, `*leq*`, `*syracuse-factory*` | (c) test fixtures |
| `examples/subtyping/{int,or,list}.el` + 4 `proofs/*.txt` | 65 + ~15k chars | proof obligations and machine-replayable scripts | (c) test fixtures |

**~720 LOC of pure logic + ~530 LOC of Emacs-UI + ~700 LOC of fixtures and proofs.** No Common Lisp; everything depends on `cl-lib` (only `cl-block`/`cl-loop`/`cl-reduce`/`cl-subseq`, all trivially available). The only Emacs API surface is `point`/`save-excursion`/`with-current-buffer`/`get-buffer-create`/`split-window-*`/`thing-at-point`/`syntax-ppss`/`global-set-key` — all confined to the `interactive/` directory and `path-management.el`'s `sexp-path-at-point`.

## 2. Hard-to-port Lisp features

- **S-expression-based AST.** Trivial. We already have `Pss.Syntax.Term` (5 ctors). The artifact's runtime grammar is `'x | top | (FUN x t u) | (u v) | (Y u) | (Or a b)` — exactly our `Term` plus two new ctors (`Y`, `Or`). One inductive datatype with two extra constructors and we are done.
- **Dynamic typing / `quote`-based metaprogramming.** Used pervasively as a *tagging* discipline — variables are `'x` (`(quote x)`), references to other defined terms are unquoted symbols `*int*`, list-headed tags are atoms `'top`, `'FUN`, `'OR`, `'y`. None of this is metaprogramming in the Lean sense; it is just a tagged-union encoding that Lean's `inductive` types model directly.
- **Mutable global state.** Two locations only: `*term-definitions*` (alist for macros) in `macroexpand.el`, and the four Emacs buffers (`*Proof*`, `*Temp-Proof*`, `*Term*`, `*Objective*`, plus `*Term-N*`/`*Objective-N*` for split goals) in `proof-mode-command.el`. The macro registry maps cleanly to a `HashMap String Term` threaded as `ReaderM` or held in an `IO.Ref`. The buffer state can be made purely functional: a `ProofState := { goals : Array (Term × Term), focus : Nat, log : Array Action }` and a step function `Action → ProofState → Except String ProofState`.
- **Emacs buffers / cursors.** Genuinely not portable. The `sexp-path-at-point` function reads `syntax-ppss` and walks the cursor — it is the *only* place where the user's editing position becomes a `path : List Nat`. Without Emacs, the user has to type the path explicitly (or pick a goal/subgoal in a CLI). The buffer-driven UI is replaceable by either (a) a `#eval`-able script interpreter, or (b) a Lean tactic frontend; neither needs to mimic the four-window layout.
- **Macros (defmacro).** Not used. The codebase uses `defun` exclusively. `define-term` is a regular function that mutates `*term-definitions*`.
- **`eval` / runtime code generation.** None. The closest the implementation comes is `(read sexp-str)` which only *parses* user input. No `eval`, no dynamic compilation.

Verdict: nothing in the pure logic is hard. Only the cursor-driven UI and four-window layout are Emacs-bound, and neither is essential to the algorithm.

## 3. What translates cleanly

- **Reduction.** `beta-substitute-at-path`, `beta-substitute-all-in-term` and `substitute-in-term` map directly onto our existing `Term.opening`/`Term.subst` machinery in `Pss.Syntax.LocallyNameless`. The artifact's β rule `((FUN var type body) arg) → body[arg/var]` is exactly `Term.opening arg body` after the named-binder is converted to locally-nameless. **Estimated new code: ~40 LOC** for `(y f) → (f (y f))`, `(top body) → top`, and a path-indexed congruence wrapper.
- **Subtyping primitives.** `promote-at-path` is just lookup-in-context plus "anything else becomes top". Pure, ~30 LOC of Lean. `alpha-equivalent-p` is unnecessary in locally-nameless representation — `decEq` on `Term` already gives us this for free.
- **Compile / proof-obligation generation.** `pss-compile-term` is an 80-line traversal returning `List (Ctx × Term × Term)`. ~60 LOC of Lean.
- **Replay interpreter.** ~130 LOC mapping each action symbol to a path-indexed transformer. Lean port: `def stepAction : Action → ProofState → Except String ProofState`, ~150 LOC.
- **Scott encodings** (`int.el`, `bool.el`, `list.el`): become a `Pss/TestSuite/Encodings.lean` of `def` constants. The `*plus-factory*`/`*plus*` pair (factored over the recursive type annotation `t`) ports verbatim.

**Reuse from existing 4.8k LOC of MPSS metatheory.** The `Pss.Syntax.Term` inductive, `LocallyNameless` opening/closing, `Term.subst`, `Term.LC`, `Ctx`, `Stack`, and the `MEqRed`/`MSubRed` reduction relations themselves are all reusable as the *ground truth* against which the checker's executable rewriter can be validated. The checker builds witness derivations; our `MEqRed`/`MSubRed` are the relations those witnesses inhabit. This is a strong argument for option (B) below — the existing metatheory and a Lean checker would compose into "executable witness ↔ relational specification" pairs.

## 4. Test suite viability

The PPDP §4 examples and the four `proofs/*.txt` scripts:

| Example | Uses `Y` | Uses `Or` | MPSS-only port viable? |
|---|---|---|---|
| §4.1 `*1* ≤ *int*` | yes (in `*int*`) | yes (in `*int*`) | **No** — `*int*` itself needs both |
| §4.2 `plus (succ int) int ≤ succ int` | yes | yes | No |
| §4.3 factorial ≤ succ int | yes | yes | No |
| §4.4 safediv compilation | yes | yes | No |
| §4.5 Syracuse ≤ 1 | yes | yes | No |
| `subtyping/or.el` `(<=p *1* (OR *1* *2*))` | no | yes | needs `Or` only |

**Every interesting example needs both `Y` and `Or`.** Our MPSS formalization has neither. A pure-MPSS test suite would be limited to toy cases like `(<=p *1* *1*)` (reflexivity) and `(<=p *1* top)` (top), which test the relational machinery but exercise nothing the paper claims is interesting. The Scott `*int*` encoding (`Y(λself≤top. λz≤top. λs≤(λn≤self.top). Or(z, s self))`) is irreducibly Y+Or.

**Implication:** to get a meaningful test suite, the Lean checker must extend the term language with `Y` and `Or` ctors and add the corresponding reduction/subtype rules from §2 of the PPDP paper. This is one inductive ctor and one reduction rule per feature — small in Lean code, but it formally **diverges from the metatheory** we are mechanizing.

## 5. Recommendation

**Pick (B): port the pure logic + Scott encodings + replay interpreter; skip the buffer/cursor UI entirely.** Concretely:

1. Add `.fix` (Y) and `.or` constructors to a fresh `Pss.Checker.Term` (do *not* touch `Pss.Syntax.Term` — keep MPSS pristine). ~50 LOC.
2. Port `reduction.el` + `subtype.el` + `or-split.el` + `macroexpand.el` + `compile.el` + `replay.el` as pure functions over `Pss.Checker.Term` and `List Nat` paths. ~500 LOC.
3. Port `terms/int.el`, `terms/bool.el` as `def` constants in `Pss.Checker.Encodings`. ~200 LOC.
4. Port the four `proofs/*.txt` scripts as Lean string literals; write `#eval replay <proof>` and a `theorem replay_succeeds : … = .ok ()` for each. This gives a regression test suite with no Emacs, no cursor, no buffers — the user provides paths explicitly.

This is ~1k LOC of Lean and zero new metatheoretical commitment (the Lean code is purely executable, with no `Prop`-level claims). It also leaves a clean follow-up — connect the executable rewriter to `MEqRed`/`MSubRed` via a soundness lemma `replay_step_sound : stepAction a σ = .ok σ' → ∃ derivation : MEqRedStar Γ s σ.term σ'.term, …`. That is option (C) territory and worth deferring.

Avoid **(A)** — without `Y`/`Or` the test suite has no real examples. Avoid **(D)** — writing MPSS-only "examples that mirror the paper's" is not actually possible; there are no MPSS-only versions of factorial or Syracuse. Avoid **(C)** as a first deliverable — the Lean tactic frontend is large and the user has not asked for an interactive Lean proof environment, only a regression suite.
