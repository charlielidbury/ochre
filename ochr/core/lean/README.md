# Ochr core: an executable reference checker for RULES v1

A Lean 4 implementation of the calculus in `ochr/core/RULES.md` (rule set v1): the machine of §3, observation and `Id` of §4, and the typing of §5, with the examples of §7 and the round-1 attacks as tests. It exists to run the examples, and to find every place where the rules are ambiguous or wrong. Findings are in `ochr/core/notes/lean-checker.md`.

## Build and run

```
cd ochr/core/lean
lake build          # checks every example; a failing verdict or a wrong assertion count fails the build
lake exe tests      # prints every verdict table and the counterfactual ledger; exit 1 on any unexpected verdict
```

Toolchain `leanprover/lean4:v4.33.0` (see `lean-toolchain`), no dependencies. A clean build takes about ten seconds and prints every verdict table; `lake exe tests` compiles the runner first (about 20 s).

## Writing programs

```lean
import Ochr.Test
open Ochr.Test

ochr E1 {
  def AddM (x : &Nat) (y : Nat) : Unit :=
    match *x { Z => *x := y | S p => AddM(&p, y) }

  def AddMZero (x : &Nat) : Id Unit (AddM(x, 0)) () :=
    match *x { Z => refl | S p => AddMZero(&p) }

  reject def WriteThenRefl (x : &Nat) : Id Nat (*x) 5 := *x := 5; refl
}

#eval IO.println (run "E1" E1).show                       -- the verdict table
#eval IO.println ((run "E1" E1 { trace := true }).showTrace "AddMZero")   -- goals, splits, call types
#guard (run "E1" E1).allAsExpected
```

`def` expects acceptance and `reject def` expects rejection. Calls are saturated and written `f(a, …)` with no space before the parenthesis. `S t`, `Id A t u`, `Eq A t u`, `cong f h`, `J A P h t`, `trans h k` and `symm h` are written by juxtaposition. Other syntax: `&p`, `*p`, `p.1`, `p := t`, `let x = t; u`, `let x : A = t; u`, `t; u`, `match p { Z => t | S y => u }` (and `S _`), `Π(x : A) (y : B). C`, `A → B`, `λ(x : A) : B => t`, `fix f (x : A) : B := t`, `(t : A)`, `()`, `(t, u)`, `⟨h, k⟩`, `refl`, `⊤`, `P ∧ Q`, `A × B`, `Nat`, `Unit`, `Prop`, `Type`, and numerals. A `λ` or `Π` in the bound position of a `let`, or a `Π` as a result type, needs parentheses. `Config` switches (`p5`, `multiOwner`, `recGuard`, `accessInside`, `selfHeadOnly`, `argNotBot`, `generalize`, `blockMoves`) each turn off one rule, for counterfactual runs.

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
| `Ochr/Examples/*.lean` | E1–E4, E6, the attacks, further probes, unit tests, the registry and counterfactual ledger |
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
| §3 [Call], P5 | `evalCall`, `callFn`, `runBody`, `endBorrowArgs` |
| §3 [Match] | `evalMatch` |
| §3 [Close] | `closeCall`, `resultKind`/`kindOf` (the table's row) |
| §3 [Seal] | `nfSealed` (the head call is `Term.call _ _ true` and is not eligible for [Close]); `substV` re-normalises after refinement or [End] |
| §3 stuck blocks | `closeOffMatch` |
| §4 owners, footprint | `owners`, `footprint` (`Ochr/Obs.lean`) |
| §4 observation, `Id` | `observe`, `idType` |
| §4 `Eq` computes | `mkEq`, `mkAnd` (`Ochr/Basic.lean`), re-applied by `substV` |
| §5 [Call-type] | `callType` |
| §5 [Def] | `checkFix`; top-level definitions in `checkDef` (`Ochr/Check.lean`) |
| §5 [Split] | `checkTail` (tail position), `splitThenClose` (otherwise), `refine` |
| §5 [Rec] | `recCheck`, and `headOnly` for fix L1 |
| §5 errors | the `err` calls in the functions above |
| P1 conversion | `==` on normal forms (`Value.beq`, which ignores binder names) |
| P2 formation | `evalType` (on a private copy), `capture` (Π-types and closures close over values) |

## Deviations from and clarifications of RULES v1

Details, with the runs that motivated them, are in `notes/lean-checker.md` §3. In brief:

- **L1 (fix of a v1 soundness bug):** in the body of `fix f`, `f` occurs only as the head of a call.
- **L2 (fix):** an argument that is `⊥` at the call point is an error.
- **L3 (clarification):** [Rec] applies to recursive calls inside nested closures, against the outer function's entry values.
- **C1** recursive position: inferred, any position that decreases in every recursive call; [Rec] fails at the first call that leaves no candidate.
- **C2** every type former is evaluated on a private copy of Ω (v1 says so only for `Id`).
- **C3** closures and Π-types capture variables by value; capturing a borrow variable is an error.
- **C4** a non-tail match's arms must have the same type, which is the closed-off match's type.
- **C5** a stuck block takes a borrow variable by move if some arm moves it, else by reborrow `&*x`; a written owned variable by `&x`; a read-only one by value.
- **C6** type-level stuck matches get their result type by checking the arms, as in C4.
- **C7** proof irrelevance: every value of a proposition is the single proof value `⋆`, including Prop-typed functions; calling `⋆` is always P5.
- **C8** [Split] on a sealed program (not in v1) generalises it to a fresh `σ` first.
- **C9** pattern variables are sub-places and are re-read after writes; a path that does not exist is an error.
- **C10** P5 erases the call, not its arguments: argument evaluation still happens.
- **C11** values in flight are temporaries in Ω, visible to [End].
- **C12** `J`'s endpoints come from the equation's type; if it has computed to `⊤`, the transported term keeps its type. `trans`, `symm` are primitives (derivable from `J`).
- **C13** `λ` needs its result type: `λ(x : A) : B => t` (a non-recursive `fix`, which carries `B`).
- **C14** no Unit η for abstract values; [Close]'s Unit row makes stuck Unit results `()`.
- **C15** universes: `Prop : Type_0 : Type_1 …`, Π at the `imax` level; nothing further is checked.
- **C16** the [Def] generic value of a parameter of a proposition is `⋆`; the cell of a borrow parameter `x` is named `x°` in frame 0.
- **C17** `Id` inside a callee's body (run by the untyped machine) does not re-check its sides' types; an owner with no stored type takes its value's type.
