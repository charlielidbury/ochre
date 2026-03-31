# Extend Och gradually until it's ready

## North Star: abstract appendVec

The short-term research goal is getting `appendVec` from docs/add-fix.md working
end-to-end, including with **abstract** arguments (`n : Nat, m : Nat`). Och is
useless without this — a type system that can only verify concrete computations
adds nothing over an evaluator.

This requires **partitioning**: the abstract interpreter must recognize
Church-encoded eliminators (like `isZero n`) as branch points and split the
analysis, narrowing `n` to `0` or `succ k` in each branch. This is described
conceptually in och-spec.md §4.2 and §7.5 but is not formalized or implemented.

Concrete appendVec (fixed n and m) should work with just `fix` and enough fuel.
Test this first as a sanity check, but don't mistake it for the real goal.

## Extension roadmap

1. **fix** (general recursion) — added, soundness has 2 sorry's remaining.
   Prove these before moving on.

2. **Partitioning** — the critical missing capability. Design how the abstract
   evaluator recognizes Church-encoded eliminators, splits analysis, and narrows
   environments. This is research, not just engineering.

3. docs/add-cps.md — should be done eventually, but high risk and might make
   everything very messy.

4. docs/add-implicits.md — should be done eventually, but not if it adds
   unnecessary noise to the underlying theory.
