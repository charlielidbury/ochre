# Ochr core: an executable reference checker for RULES v1.4

A Lean 4 implementation of the calculus in `ochr/core/RULES.md` (rule set v1.4): the machine of §3, observation and `Id` of §4, and the typing of §5, with the examples of §7 and the round-1 attacks as tests. It exists to run the examples, and to find every place where the rules are ambiguous or wrong. Findings are in `ochr/core/notes/lean-checker.md`.

## Build and run

```
cd ochr/core/lean
lake build          # checks every example; a failing verdict or a wrong assertion count fails the build
lake exe tests      # prints every verdict table and the counterfactual ledger; exit 1 on any unexpected verdict
```

Toolchain `leanprover/lean4:v4.33.0` (see `lean-toolchain`), no dependencies. A clean build takes about ten seconds and prints every verdict table; `lake exe tests` compiles the runner first (about 20 s) and prints per-declaration check times (all 139 declarations check in about 5 ms).

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

`def` expects acceptance and `reject def` expects rejection. `by x` names the decreasing parameter; a definition without `by` may not call itself. Calls are saturated and written `f(a, …)` with no space before the parenthesis. `S t`, `Id A t u` and `Eq A t u` are written by juxtaposition, and transport by `J(A, a, b, P, h, t)`. Other syntax: `&p`, `*p`, `p.1`, `p := t`, `let x = t; u`, `let x : T = t; u` (for a match, `T` is the block's type), `t; u`, `match p { Z => t | S y => u }` (and `S _`), `Π(x : A) (y : B). C`, `A → B`, `λ(x : A) : B => t`, `fix f (x : A) : B by x := t`, `(t : A)`, `()`, `(t, u)`, `⟨h, k⟩`, `refl`, `⊤`, `P ∧ Q`, `A × B`, `Nat`, `Unit`, `Prop`, `Type`, and numerals. `cong f h`, `trans h k` and `symm h` exist as derivable conveniences outside the core. A `λ` or `Π` in the bound position of a `let`, or a `Π` as a result type, needs parentheses.

`Config` switches each turn off one rule, for counterfactual runs: `eraseOnCopy` (P2, v1.3), `multiOwner` (D18), `recGuard` (D17), `accessInside` (D19), `selfHeadOnly` (v1.1 head-only), `argNotBot` (v1.2 temporaries), `generalize` (v1.2 generalise-then-split), `blockMoves` (v1.3 captures), `proofParamsStar` (v1.4 D27), `recNested` ([Rec] inside nested functions), `p5` (v1's call skipping), `inferRecPos` (v1's inferred decreasing parameter), and `trace`.

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
| `Ochr/Examples/*.lean` | E1–E6, the attacks, further probes, unit tests (incl. D18), the registry, total count and counterfactual ledger |
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
| §3 [Close] | `closeCall` (asserts the precondition), `resultKind`/`kindOf` (the table's row) |
| §3 [Seal] | `nfSealed` (the head call is `Term.call _ _ true` and is not eligible for [Close]); `substV` re-normalises after refinement or [End] |
| §3 stuck blocks | `splitThenClose` (arms, annotation), `closeOffMatch` (Rust-style captures on maximal place prefixes) |
| §4 owners, footprint | `owners`, `footprint` (`Ochr/Obs.lean`) |
| §4 observation, `Id` | `observe`, `idType` |
| §4 `Eq` computes | `mkEq`, `mkAnd` (`Ochr/Basic.lean`), re-applied by `substV` |
| §5 [Call-type] | `callType` |
| §5 [Def] | `checkFix`; top-level definitions in `checkDef` (`Ochr/Check.lean`) |
| §5 [Split] | `checkTail` (tail position), `splitThenClose` (otherwise), `refine`, `generalizeNeutral` (sealed heads) |
| §5 [Rec] | `recCheck` (a stack of contexts, one per enclosing function), `headOnly` (f only as a call head) |
| §5 errors | the `err` calls in the functions above |
| P1 conversion | `==` on normal forms (`Value.beq`, which ignores binder names) |
| P2 erased terms | `eval`/`erasedValue` (a term whose value is a proof `⋆` or a type leaves Ω unchanged), `evalType` (types on a private copy), `capture` (Π-types and closures close over values, never borrows) |

## Where the rules left a choice

`notes/lean-checker.md` §3 lists every point where RULES was ambiguous, the reading implemented, and whether later rule sets adopted or changed it (C1–C19). The remaining open points are:
- static vs dynamic "moves out of in any arm" (C19);
- the sort of a sealed type (C16);
- Unit η (C14);
- universes (C15);
- J's motive sort (C12);
- calls of sealed function values in untyped code (C18).

Rule bugs found by running the rules (L1–L4, including the uncurried D18 attack) are in §1 and §4 there.
