# Extend Och gradually until it's ready

## URGENT: Stop normalizing under binders in concEval

The concrete evaluator currently normalizes inside lambda bodies:
`γ ⊢ λ(x: τ). e ⟶ λ(x: τ). e'` where `e'` is the reduced body. This is a
bug — the spec (§4.1) treats lambdas as values in standard call-by-value.

**This breaks Church-encoded branching.** Church `if-then-else` works by passing
two lambdas (branches) to an eliminator, which selects one. Normalizing under
binders eagerly evaluates BOTH branches' bodies, including recursive ones,
causing fuel exhaustion. See Tests.lean `toZero` example: `toZero 1 = none`.

**The fix:** Change `concEval` to return `λ(x: τ). e` as-is (a value), without
reducing `e`. `absEval` should KEEP normalizing under binders (needed for
precision: `succ 2 = 3`).

**Proof impact:** The soundness proof's lam case currently compares normalized
bodies directly (`SubtypeTrans body_c' body_a'`). Without concEval normalization,
concrete lambdas have unreduced bodies. Soundness would need extensional
reasoning: concrete and abstract lambdas are related when applied to related
arguments, not by comparing bodies syntactically. This is a standard technique
but requires restructuring the lam case.

**This unblocks:** Recursive Church-encoded functions (appendVec, mapArray, etc.)
in concrete mode. Combined with the existing abstract evaluation (which already
handles `isZero (n : Nat) ⊑ Bool` correctly), this gets concrete recursive
fix working.

## North Star: abstract appendVec

The medium-term research goal is getting `appendVec` from docs/add-fix.md working
end-to-end, including with **abstract** arguments (`n : Nat, m : Nat`). Och is
useless without this — a type system that can only verify concrete computations
adds nothing over an evaluator.

Concrete appendVec (fixed n and m) should work once concEval stops normalizing
under binders (see above). Test this first as a sanity check.

For abstract appendVec, the abstract evaluator needs to handle branches where
the result type depends on which branch is taken. Currently `isZero n` for
abstract `n : Nat` correctly evaluates to `Bool` (by applying the type `Nat`
through the elimination chain). But the result of the *outer* branching
(e.g., `(isZero n) ResultType base_case recursive_case`) just gets `ResultType`
— it doesn't know that `base_case` returns `Array 0 T` and `recursive_case`
returns `Array (succ k) T`. Getting branch-precise abstract results may require
partitioning or a similar mechanism, but this is a research question, not a
known-needed feature.

## Extension roadmap

1. **Stop normalizing under binders in concEval** — the urgent fix above.
   This is a small code change but requires soundness proof restructuring.

2. **Concrete recursive fix tests** — once concEval is fixed, test `toZero`,
   `mapArray`, `appendArrays` with concrete arguments.

3. **Investigate abstract branching precision** — determine whether the current
   abstract evaluator (which gives `isZero n : Bool` for abstract `n`) is
   sufficient for typing recursive functions, or whether partitioning/narrowing
   is needed. This is research.

4. docs/add-cps.md — should be done eventually, but high risk and might make
   everything very messy.

5. docs/add-implicits.md — should be done eventually, but not if it adds
   unnecessary noise to the underlying theory.
