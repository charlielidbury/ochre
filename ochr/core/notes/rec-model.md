# A model of recursion and the [Rec] guard

Written by the `rec-model` lane on 2026-10-29, toward full consistency. Earlier lanes modelled dependent fields (D75/D76), case splitting and `Id` (`notes/split-model.md`, `notes/id-model.md`). This one models what makes a recursive definition well-founded, derives what [Rec] must check, and compares that with the checker. It found one closed proof of `False`, fixed as D78.

## Why it matters

A proof that recurses without a well-founded measure proves anything: `Loop`, `Knot`, `Spin`, `Lie`, `OuterBad` and their `Boom`s in `Examples/Recursion.lean`. The checker's fuel only makes a non-terminating *check* undecided; it does not make an accepted recursive *proof* well-founded. A proof is never run ([T-Call-proof]), so nothing at runtime would notice. [Rec] is the only thing standing between a recursive proof and `False`.

## The model

A definition `fix f (x̄ : Ā) : B by xⱼ := b` denotes the function defined by well-founded recursion on the size of the **entry value** of `xⱼ`: the value of `xⱼ` (its content, through the borrow, for `&D`) when the call starts. Each call of `f` inside `b` is an appeal to the induction hypothesis, valid exactly when its argument in position `j` (its content, through a borrow) is smaller than the caller's entry value. Ochr uses the simplest well-founded order: being a **strict subterm**, through any field.

Principles:

- **(E) The measure is the entry value.** What the body does to `xⱼ`'s place afterwards does not matter: writes, moves, `*x := S(*x)`. Each recursive call's argument content is compared with the caller's *entry* value, and each callee's entry value is that argument content. Strict subterm implies smaller size, so every chain of recursive calls is finite. The comparison is made against the entry value *as refined so far*: a [Split] in the body learns its shape, and refinement only adds constructors, so a strict subterm found at the generic call is one at every instance (two-paths census, site 15).
- **(N) Recursive calls are named.** The only way a definition under check can be invoked is through the name it binds for itself: `f` occurs in `b` only as the head of a call (fix L1), not at all without `by` (D31), and no earlier definition can see it. Inside a nested function, `f` is reached through that function's capture of the name. So *which calls recurse* is a fact about syntax, and [Rec] must check exactly those calls. It must not identify them by comparing function values: a local function's value is a closure over its captures, and refinement, [End] and re-normalisation change captured values without changing which function it is.
- **(B) Check before running.** The check is made at the call point, before the call runs, since running a non-decreasing call may not terminate.
- **(O) One order on definitions.** A definition sees only the earlier, accepted definitions and itself, so there is no mutual recursion between definitions. Program-wide, every chain of calls is ordered lexicographically by (definition, entry size), which is Theorem 19's measure. Higher-order calls do not break it: a call through a function *value* (a parameter, a closure) is not a recursive call unless its head is the name (N). A closure formed in `f`'s body that calls `f` is checked, where it is formed, against `f`'s entry value, so its calls decrease the measure of the `f` that formed it.
- **(T) Types recurse like terms.** A type function is a definition like any other, with the same check. A statement never mentions the definition being checked ([Def]), so [Call-type] at a recursive call evaluates the callee's statement without recursing into it.
- **(R) Runs only unfold.** Untyped runs (a callee's body, re-normalising a sealed program, a conversion's generic call) unfold definitions without [Rec]. That is only the fixpoint equation computing; it decides nothing about well-foundedness. Every self-call in the code was checked on every path of the case tree, so such runs terminate (given stability); a run that does not is fuel exhaustion, `undecided`, never a decision.
- **(H) Holes are axioms.** A hole stands for a value of any type, so a hole of a recursive type is an unchecked axiom. The consistency statement excludes holes.

## Derived obligations against the checker

| Obligation | Checker | Verdict |
|---|---|---|
| (E) compare argument content with the entry value as refined (`expandRefs`), by strict subterms through every field | `recCheck`, `strictSubterms` | matches |
| (E) the decreasing parameter has an inductive type, or is a borrow of one | `checkFix`'s `by` check, note 21 | matches |
| (N) `f` only as a call head, nowhere without `by` | `headOnly`, D31 | matches |
| (N) a call is recursive by its head's name, including captures in nested functions | `ctx.fn == fv` (value equality) | **missing: finding, D78** |
| (B) check at the call point, before the body runs | `recCheck` before `runBody` in `callFn`; also before [T-Call-proof]'s erasure | matches |
| (B) entries persist across private copies and branches | `RecCtx.uid`, `restoreKeep`'s `keepCands` | matches |
| (O) item-by-item checking against earlier items | `checkDefs` | matches |
| (T) a definition does not mention itself in its type | `checkDef` | matches |
| (R) no decision from an unfolding run | untyped `callFn` has no [Rec], and exhaustion is uncatchable | matches |

## The finding (D78)

`recCheck` found the entry for a call by `ctx.fn == fv`. With a local recursive function that captures a value its body splits on, the [Split] substituted inside the function's binding of itself but not inside the entry, so the calls in the arms matched no entry and went unchecked:

```
CapSplit (n x : Nat) : False := (fix go (y : Nat) : False by y := match n { Z => go(y), S q => go(y) })(x)
BoomCapSplit : False := CapSplit(0, 0)
```

Both were accepted on main `4cc0beda`. Two further shapes went the same way:
- `BoomCapLam`: the recursion goes only through closures formed in the arms. Capturing `go` moves it (a closure over non-copy data is not a copy), so its value is gone from the binding as well.
- `Nest2`: a capture of a capture, with a split at each level.

The control `(fix go (y : Nat) : False by y := go(y))(x)` was always rejected.

**Fix.** The function's binding of itself carries its entry's uid (`Binding.recUid`). A nested function's capture of a marked binding is marked too, read from the bindings themselves before `capture` moves them (`capMarks`). `recFrameOf` is the one place that decides whether a call belongs to an entry, by the head's mark. Value equality stays as a fail-safe that can only add a check.

## Audit of the bug class

The bug class is identifying something by `==` on values that a refinement can change. Only the [Rec] entry's identification skipped a check on a mismatch. The rest fail safe or are semantic:

- **`neutrals`** (generalisation records, looked up by value): a miss only loses a fact, so less is known. Two programs that become equal after a refinement denote the same value in that world, so a hit is right.
- **`convStack`** (pairs under observational comparison): a repeated pair answers "not convertible", the least relation; a missed cycle runs out of fuel.
- **`classCache`** (a Π-type's class): the class is a function of the value, and a miss recomputes it.
- **The remaining `==` tests** are reflexivity in conversion and the strict-subterm test (E). Both are semantic: values that are equal after a refinement are equal in that world.

(The `stability` lane's §8 lists the same value-keyed tables for a different reason: they break the heap port's parametricity, not soundness.)

## Probes

Every probe printed its verdicts explicitly, next to a control that must be rejected.

| Probe | main `4cc0beda` | `rec-model` |
|---|---|---|
| `CapSplit` / `BoomCapSplit` | accepted | rejected by [Rec] |
| `BoomCapLam`: closures in both arms | accepted | rejected by [Rec] |
| `Nest2`: a capture of a capture, a split at each level | accepted | rejected by [Rec] |
| `CapLamOnly`: a `Unit` function recursing only through a closure | undecided (loops) | rejected by [Rec] |
| `InType`: a recursive call in a type annotation inside the body | rejected | rejected |
| `LamNoSplit`, `TopLam`: closure recursion without a split | rejected | rejected |

## Proposals (not implemented)

- **The candidates list is vestigial.** Since D23 (`by` is mandatory) and D70 (`inferRecPos` gone), `RecCtx.cands` is always `[j]` or `[]`. It could be the declared index, and the "positions that survive every call" accumulator and its `keepCands` restore could go.
- **Drop the value-equality fail-safe** in `recFrameOf` once the name-based identification has been reviewed, so the decision is purely syntactic as §6.3 states.
- **Move "which calls recurse" into `Decide.lean`.** It is now a syntactic decision; `recFrameOf` reads only the binding mark and could live with the other deciders.

## Open

- Well-foundedness of a run rests on stability: the check's case tree must cover the path a concrete run takes, which is (Sp) in `notes/stability.md`.
- Structural recursion only. Recursion on a measure, or on a proof (docs/13), would each need a new obligation in this model.
