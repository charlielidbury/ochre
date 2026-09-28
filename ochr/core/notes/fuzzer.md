# fuzzer: a differential naturality tester for the Ochr checker (branch ochr-core-fuzz)

**Verdict (running log, newest findings first in §3).** The fuzzer rediscovers the known two-path bugs when their rule is switched off, and on the v1.6 snapshot it found two new closed proofs of false (N1, N2 below) that no v1.7/v1.8 rule addresses.
**Most important finding:** the checker decides "this term is a proof, so it is erased" (P2) from a syntactic list of proof formers, plus an ascription's type in typed mode only. A proof tail that is not `refl`/`⟨⟩`/`J`/… (a proof λ, a proof variable, a let-bound proof), or an ascribed proof run by the untyped machine ([Seal] re-normalisation, callee bodies), is erased on one path and run on the other.
**What must change:** P2's "declared type has sort Prop" needs a definition that the untyped machine can apply (e.g. "its value is ⋆", which C7 makes equivalent and which is determined by declared types), and the checker must use it for every non-call term in both modes.
**Confidence:** high for N1 and N2 (both accepted by the unmodified v1.6 checker, programs below).
**Not checked yet:** see §5.

## 1. How it works

`lake exe fuzz` (files `ochr/core/lean/Ochr/Fuzz/*.lean`, `Fuzz.lean`). Case `i` of seed `S` is a pure function of `(S, i)`.

- **Generator** (`Gen.lean`, `GenTerm.lean`, `Case.lean`, `Lib.lean`): type-directed over `Nat`, user inductives `B2 := F | T`, `L := Nil | Cons(h, t)`, `Box := Mk(v)`, borrows `&p`, reborrows `&*x`, moves of borrow variables, sub-place borrows `&(p).1`, assignments, tail and non-tail matches with pattern variables, `let` with and without annotations, local λs (including codomain `U(n)`), `Id`/`Eq`/`∧` statements and nested `Id` inside terms, proofs with effects, abstract function parameters instantiated by library functions. A template library (AddM, Add, TailM, Pick, PickX, PickY, Keep, Double, IsZ, G1, Clr, Inc, U, V, W, MkF, Le, Lemma, F5, LastM, AppendM, Len) is drawn at random per case, plus 0–2 random (sometimes recursive) functions, checked first. The statement is `def Stmt (params) : Prop := Id A lhs rhs`.
- **Oracles** (`Harness.lean`, `Refine.lean`, `Oracle.lean`, `Run.lean`): the generic environment is built exactly as [Def] does. G = the checker's own `observe` of each side (result and final content of every binding: the full resolution) and the `Id` type. For each refinement α (`σ := Z`, `S σ'`, `S (S σ')`, each constructor with fresh fields, each library function of an abstract function's type) and 6 ground instances, D = the same observations from `refine`d Ω, and R = G refined by `substV` (which re-normalises sealed programs). Generalisation records are undone (`σ_g := ⌈n⌉`) on both sides first. R and D are compared up to renaming of fresh σs and loans; if they differ syntactically but are not ground, both are ground-completed (4 completions) and compared again. Findings: `nat` (R ≠ D), `false` (generic `Id` is ⊤, a ground instance is not), `verdict` (generic succeeds, direct errors), `renorm` (re-normalising R errors, direct succeeds), `escape` (a σ that is neither a parameter nor a recorded generalisation, or a surviving loan), `adequacy` (typed direct run vs the untyped machine at a ground instance).
- **Shrinker** (`Shrink.lean`): greedy deletion/replacement on the surface program, keeping the same finding kind and error class. **Printer** (`Print.lean`): the paper's surface syntax, re-parseable by `ochr { }`. **Replay** (`Replay.lean`): `replay Cex` runs the oracles on a pasted counterexample.
- **Attribution**: `--diff --switch X` reports only findings present with rule X off and absent with it on (same case). `--jobs J` runs crash-isolated worker processes (a crashing case, e.g. a stack overflow, is reported and skipped).
- **Emulations** (two opt-in `Config` hooks, default off, so the checker's behaviour and the ledger are unchanged): `+D37` (`genGlobal`: restores keep generalisation records and fresh-name counters) and `+D35` (`syntacticClass`: a closure's class from its codomain term, a stuck block erased only when its match is a proof, and sequencing forms erased only when they evaluate to a proof). They let the fuzzer look past bugs already fixed in v1.7/v1.8.

Usage: `lake exe fuzz --seed 1 --count 100000 --jobs 16 [--switch +D37 --switch +D35] [--diff --switch D32] [--shrink 2] [--quiet]`; `--show I` re-runs case I verbosely.

## 2. Validation: known bugs rediscovered with their rule switched off

`--diff`, seed 1, with `+D37` (so X3-style escapes do not mask them). "Case" is the index of the first case exhibiting it (cases are ~3 ms each).

| switch off | rediscovered | first case | shrunk shape |
|---|---|---|---|
| D32 (pattern writes) | F5 `Clear` | 118 | `Id Prop (match *x0 { Z => () \| S p => p := 0 }; ⊤) ⊤` at `x0 := S σ` |
| D28 (erasure by declaration) | F1 | 405 | `W(&n0, *x1); ()` at `x1 := 0` |
| D29 (match ends loans in neutral head) | F2 | 116 / 359 | returned borrow's hole orphaned; direct path reads ⊥ |
| P2/D26 (erased terms on a private copy) | N1 | 203 | `let a = match n1 { Z => refl \| S p => n0 := n1; refl }` |
| D19 (access ends loans inside) | BadA1-type | 1888 | verdict: the direct path errors where the generic path accepted |
| none (default v1.6 rules) | X2/BoomB (D35) | 56 | `Id Prop (match *x2 { Z => ⊤ \| S p => *x1 := 0; ⊤ }) ⊤` |
| none (default v1.6 rules) | X3's root (D37) | 28 | a generalised σ escapes the private copy of `observe` |
| C5, D18 | not yet (see §5) | | |
