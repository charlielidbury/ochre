# Ochr core: an executable reference checker for RULES v1.9

A Lean 4 implementation of the calculus in `ochr/core/RULES.md` (rule set v1.9), extended to user-declared inductive types: the machine of §3, observation and `Id` of §4, and the typing of §5, with the examples of §7 and the round-1 attacks as tests. It exists to run the examples, and to find every place where the rules are ambiguous or wrong. Findings are in `ochr/core/notes/lean-checker.md`.

## Build and run

```
cd ochr/core/lean
lake build          # checks every example; a failing verdict or a wrong assertion count fails the build
lake exe tests      # prints every verdict table and the counterfactual ledger; exit 1 on any unexpected verdict
```

Toolchain `leanprover/lean4:v4.33.0` (see `lean-toolchain`), no dependencies. A clean build takes about 42 seconds (most of it the counterfactual ledger) and prints every verdict table; `lake exe tests` compiles the runner first and prints per-declaration check times (all 247 declarations check in about 12.4 ms).

## Writing programs

```lean
import Ochr.Test
open Ochr.Test

ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit by x :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () by x :=
    match *x { Z => refl | S p => AddMZero(&p) }

  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}

#eval IO.println (run "E1" E1).show                       -- the verdict table
#eval IO.println ((run "E1" E1 { trace := true }).showTrace "AddMZero")   -- goals, splits, call types
#guard (run "E1" E1).allAsExpected
```

`def` expects acceptance and `reject def` expects rejection. `inductive List := Nil | Cons(h : Nat, t : List)` declares an inductive type; its constructors are applied like calls (`Cons(1, Nil)`), and `match xs { Nil => … | Cons(h, t) => … }` binds `h`, `t` as the field places `xs.h`, `xs.t`. `by x` names the decreasing parameter; a definition without `by` may not call itself. Calls are saturated and written `f(a, …)` with no space before the parenthesis. `S t`, `Id A t u` and `Eq A t u` are written by juxtaposition, and transport by `J(A, a, b, P, h, t)`. Other syntax: `&p`, `*p`, `p.1`, `p := t`, `let x = t; u`, `let x : T = t; u` (for a match, `T` is the block's type), `t; u`, `match p { Z => t | S y => u }` (and `S _`), `Π(x : A) (y : B). C`, `A → B`, `λ(x : A) : B => t`, `fix f (x : A) : B by x := t`, `(t : A)`, `()`, `(t, u)`, `⟨h, k⟩`, `refl`, `⊤`, `P ∧ Q`, `A × B`, `Nat`, `Unit`, `Prop`, `Type`, and numerals. `cong f h`, `trans h k` and `symm h` exist as derivable conveniences outside the core. A `λ` or `Π` in the bound position of a `let`, or a `Π` as a result type, needs parentheses.

`Config` switches each turn off one rule, for counterfactual runs: `eraseOnCopy` (P2, v1.3), `multiOwner` (D18), `recGuard` (D17), `accessInside` (D19), `selfHeadOnly` (v1.1 head-only), `argNotBot` (v1.2 temporaries), `generalize` (v1.2 generalise-then-split), `blockMoves` (v1.3 captures), `proofParamsStar` (v1.4 D27), `recNested` ([Rec] inside nested functions), `erasureByDecl` (D28), `matchEndsInside` (D29), `closureConv` (D30), `unboundWithoutBy` (D31), `patternWritesVisible` (D32), `genConsistent` (finding G1), `classBySyntax`, `blockRule`, `seqByProof`, `rowByDecl` (D35), `leafRule` (findings P1, P3), `positivity` (D36), `globalRecords` (D37), `obsBorrow` (D38), `headGuardNeutral` (D39), `genPlaceType` ([Split-gen]'s type), `confine` (D41), `confineBodies` (an extension of D41, off by default), `p5` (v1's call skipping), `inferRecPos` (v1's inferred decreasing parameter), and `trace`.

## Layout

| File | Contents |
|---|---|
| `Ochr/Syntax.lean` | terms, places, values (§1, §2); de Bruijn indices, binder names as `Hint`s that `==` ignores |
| `Ochr/Basic.lean` | `mkEq`/`mkAnd` (the `Eq` computation rules), traversals |
| `Ochr/Pretty.lean` | printing in the paper's notation |
| `Ochr/Env.lean` | Ω (frames of typed bindings plus temporaries), the machine state and monad |
| `Ochr/Obs.lean` | paths, `owners`, the footprint `W`, observation tuples (the pure half of §4) |
| `Ochr/Machine.lean` | one `mutual` block: the machine, [Seal], [Close], [Split], stuck blocks, observation, `Id`, [Call-type], [Rec], [Def] |
| `Ochr/Check.lean` | programs as sequences of top-level definitions |
| `Ochr/Surface.lean`, `Ochr/Notation.lean` | named surface terms, their resolution, the `ochr` command |
| `Ochr/Test.lean` | running programs, verdict tables, traces |
| `Ochr/Examples/*.lean` | E1–E6, the attacks (rounds 1–3), v1.5, v1.7, v1.8 and v1.9 regressions (breaker-fresh-v16 X1–X5, positivity, confinement), inductive types (lists, BSTs), unit tests (incl. D18), the registry, total count and counterfactual ledger |
| `Tests.lean` | `lake exe tests` |

## Rule → function

| Rule (RULES v1) | Function (`Ochr/Machine.lean` unless noted) |
|---|---|
| §3 [End ℓ] | `endBorrow` (substitution of every `loan_ℓ` by `substEnv`) |
| §3 [Access] | `accessPath` (loans on the path, including the place itself), `accessInside` (loans inside the content) |
| §3 [Read] | `readPlace` |
| §3 [Borrow] | `borrowPlace` |
| §3 [Assign] | `eval` (`.assign`), `assignPlace` |
| §3 [Let] | `eval` (`.letIn`) |
| §3 [Drop] | `dropTopBind`, `dropValue`, `popFrame` |
| §3 [Call] | `evalCall`, `callFn`, `runBody`, `endBorrowArgs` |
| §3 [Match] | `evalMatch` |
| §3 [Close] | `closeCall` (asserts the precondition), `declKind` (the table's row, from the declared codomain, v1.7) |
| §3 [Seal] | `nfSealed` (the head call is `Term.call _ _ true` and is not eligible for [Close], a neutral-headed one included, D39); `substV` re-normalises after refinement or [End] |
| §3 stuck blocks | `splitArmsThenClose` (arms, annotation, whether every arm is a proof), `closeOffMatch` (Rust-style captures on maximal place prefixes; erased iff every arm is a proof, v1.7) |
| §4 owners, footprint | `owners`, `footprint` (`Ochr/Obs.lean`) |
| §4 observation, `Id` | `observe`, `idType`; a borrow result in `convFn` is observed through a fresh value (D38) |
| §4 `Eq` computes | `mkEq`, `mkAnd` (`Ochr/Basic.lean`), re-applied by `substV` |
| §5 [Call-type] | `callType` |
| §5 [Def] | `checkFix`; top-level definitions in `checkDef`, inductive declarations in `checkInd`/`firstOrder` (D36) (`Ochr/Check.lean`) |
| §5 [Split] | `checkTail` (tail position), `splitThenClose` (otherwise), `refine`, `generalizeNeutral` (sealed heads; σ gets the place's type; records are global and fresh names never reused, `restoreKeep` in `Env.lean`, D37) |
| §5 [Rec] | `recCheck` (a stack of contexts, one per enclosing function), `headOnly` (f only as a call head) |
| §5 errors | the `err` calls in the functions above |
| P1 conversion | `==` on normal forms (`Value.beq`, which ignores binder names) |
| P2 erased terms | `eval` (flags *erased* and *proof*: a call by its callee's class; `let`/`;`/`match` iff their tail is a proof; proof formers; a variable declared of sort Prop (a flag on its binding: `paramFlags`, `leafProof`), a proof constant, a `λ` returning proofs; an ascription at a declared proposition), `fnClass`/`propDecl`/`declOfDom`/`declOfVal` (a function's class from its codomain term, v1.7), `logEffect`/`settleErased`/`flushPending`/`confinedCopy` (D41: erased runs are confined, judged by the outermost erased term; arguments of erased calls exempt), `evalType` (types on a private copy), `capture` (Π-types and closures close over values, never borrows) |

## Where the rules left a choice

`notes/lean-checker.md` §3 lists every point where RULES was ambiguous, the reading implemented, and whether later rule sets adopted or changed it (C1–C19). The remaining open points are:
- static vs dynamic "moves out of in any arm" (C19);
- the sort of a sealed type (C16);
- Unit η (C14);
- universes (C15);
- J's motive sort (C12);
- calls of sealed function values in untyped code (C18).

Rule bugs found by running the rules (L1–L4, including the uncurried D18 attack; P1, P2 in round 3) are in §1, §4 and §10 there. One reading remains this checker's own: a function's class is "data" when `propDecl` cannot read a codomain's declared sort (e.g. `q.1`), which is consistent on both paths because blocks follow their arms (§10). §11 there lists where the checker, RULES v1.8 and the formal appendix still differ: mainly *declared* (RULES, checker) versus *computed* (appendix) sort Prop for non-call terms, and the missing types of captured proofs and neutrals.
