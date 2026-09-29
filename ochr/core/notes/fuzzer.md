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
| C5 (blocks move moved borrows) | `MovedByBlock` | 815 | `match *x0 { Z => let a = x0; () \| S _ => () }; … *x0 …` at `x0 := 0`: use after move |
| D18 (owners are sets) | meta-model C2 | 19587 | `let a = match *x0 { Z => &n1 \| S p => x0 }; Id Unit () (*a := 0)` |
| D30 (closures by observation) | F3 | 8 (conv oracle); 191 (`false`) | closures equal on results only; block closures inside sealed programs too |
| D17 ([Rec] entry values) | Loop/Bot' shape | 0 (truth oracle) | `def Lie (n0 : Nat) (x1 : &Nat) : Id Nat *x1 0 by n0 := Lie(n0, x1)` accepted |
| D31 (no `f` without `by`) | F4 | 0 (truth oracle) | the same without `by` |
| L1 (f only as a call head) | not reached | | the proof candidates never pass `Lie` as a value |
| none (default v1.6 rules) | X2/BoomB (D35) | 56 | `Id Prop (match *x2 { Z => ⊤ \| S p => *x1 := 0; ⊤ }) ⊤` |
| none (default v1.6 rules) | X3's root (D37) | 28 | a generalised σ escapes the private copy of `observe` |
| none (default v1.6 rules) | X4 (D38) | 4525 | `PickX ≡ PickY` accepted; they observe `(0,(7,0))` vs `(0,(0,7))` |
| none | X5 (D39) | not reached | no crash in 900k cases: an abstract `Π(x y : &Nat). &Nat` called with two borrows and an owner read back never came up |

The truth oracle (§1): when a statement is false at a ground instance, it tries `refl`, a one-level split of each parameter, structural recursion on each `Nat`/`&Nat`/list parameter, and non-decreasing recursion with and without `by`; an accepted one is a closed proof of false by instantiation.

## 3. Findings on the current rules (v1.6 snapshot; labels say what already fixes them)

Soundness first. Every program below was checked with the unmodified v1.6 checker (`Scratch/R2.lean`, `R3.lean` in the worktree; the `reject def` lines are the ones it rejects).

**N1 (new, closed proof of false; rule at fault: the checker's reading of P2 clause "declared type has sort Prop", not fixed by D35/D37–D39).** A `Prop`-typed match whose arm writes and then ends in a proof that is not a syntactic proof former. At the generic call the match is stuck, closes off as a block whose codomain is a proposition, and the block is erased as a proof (class 2): the write is discarded. At `n = 0` the same match runs inline; `eval` marks a term erased only if it is `refl`, `⟨⟩`, `cong`, `trans`, `symm`, a `J` with a `Prop` motive or an ascription at a `Prop` type, and a `seq`/`let`/`match` inherits its tail's mark, so `(c := 1; λ…)` is not erased and the write persists.
```
def LieL (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; λ(y : &Nat) : ⊤ => refl) | S _ => λ(y : &Nat) : ⊤ => refl }; c) 0 := refl
def BoomL : Eq Nat 1 0 := LieL(0)                                     -- accepted
def LieV (n : Nat) (h : ⊤) : Id Nat (let c = 0; let f = match n { Z => (c := 1; h) | S _ => h }; c) 0 := refl
def BoomV : Eq Nat 1 0 := LieV(0, refl)                               -- accepted
def LieR (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; let e = refl; e) | S _ => refl }; c) 0 := refl
def BoomR : Eq Nat 1 0 := LieR(0)                                     -- accepted
def LieF (n : Nat) : Id Nat (let c = 0; let f = match n { Z => (c := 1; refl) | S _ => refl }; c) 0 := refl
reject def BoomF : Eq Nat 1 0 := LieF(0)                              -- rejected: refl is a proof former
```
Found at case 354 of seed 1 (with `+D37 +D35`), shrunk to `Id Prop ⊤ (let a = match *x0 { Z => *x0 := 1; λ(y : &Nat) : ⊤ => refl | S _ => λ(y : &Nat) : ⊤ => refl }; ⊤)`.

**N2 (new, closed proof of false; same root, in the untyped machine).** The untyped machine (callee bodies and every [Seal] re-normalisation) has no types, and `eval` decides an ascription's erasure from its declared type only in typed mode, so it runs an ascribed proof's write that the typed path erases. [Split] re-normalises the sealed block with the untyped machine; the instance evaluates the same match typed.
```
def LieA (n : Nat) : Id Nat (match n { Z => let c = 5; let a : ⊤ = (c := 0; let e = refl; e); c | S _ => 0 }) 0 :=
  match n { Z => refl | S _ => refl }
def BoomA : Eq Nat 5 0 := LieA(0)                                     -- accepted
```
Found as an `adequacy` disagreement (typed run vs machine) at case 6232 of seed 1: `Id Unit (n0 := (let a0 : ⊤ = (n0 := 0; let a6 = refl; a6); n0)) 0` at `n0 := 1` gives `n0 = 1` typed and `0` on the machine; the checker itself rejects `Main(1) = 1` for `Main(n) := let c = n; let a : ⊤ = (c := 0; let e = refl; e); c` because [Call-type] runs `Main`'s body untyped.

*Fix for N1 and N2.* P2 is right as written ("any other term is erased iff … its declared type has sort Prop"), but the machine cannot see declared types. Every value of a proposition is ⋆ and only proofs evaluate to ⋆ (C7), and that is fixed by declared types, so "a non-call term is erased iff its value is ⋆" is the same condition, readable in both modes and stable under refinement. RULES should say so (one clause in P2); the checker's hook `proofByValue` implements it (below, §4, runs with it on).
