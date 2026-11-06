# 28. Conversion must not identify values that hold a moved-out `⊥` (lane spec)

Written on 2026-11-06 by `ochr-consistency-2`. It is the spec for a checker fix; the implementation is a separate lane, and merging it is the user's decision.

## The bug: a fifth closed proof of `False`

Found by the `model-slice` agent while writing `docs/27` (test 2 of `docs/23`). Confirmed independently on main at `10c22fd9`, against a fresh build of `Ochr.Examples.Nat` and `Ochr.Examples.Fixtures`. The probe file is `ochre-probe-bot/ochr/core/lean/Scratch/BotConvProbe.lean`.

```
def Same (n : Nat) (x : Nat)
    (h : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) },
                  match n { Z => (let y = x; ()), S _ => (x := 5; ()) }))
  : Id(Unit, match n { Z => (let y = x; ()), S _ => (x := 5; ()) },
             match n { Z => (let y = x; ()), S _ => (x := 6; ()) }) := h
def Boom : False := Same(S(Z), Z, refl)
```

What happens:

- **Verdicts.** `Same` and `Boom` are accepted, and the flipped `reject def BoomFlip` reports "expected rejection, but accepted". The control without the blocks is rejected: the hypothesis computes to `True` and the goal to `False`.
- **Why `Same` is accepted.**
  - At the generic call `n` is unknown, so each side of each `Id` is a stuck block.
  - Arm `Z` moves `x`, so the block takes `x` by move (K1).
  - So every observation leaves `x` as `⊥`. Both the hypothesis and the goal compute to the stuck `Eq(Nat, ⊥, ⊥)`; D68 (MovedBothSides) keeps it from computing to `True`.
  - `conv`'s first test, `if v == w then return true` (`Machine.lean`, `conv`), then identifies them.
- **Why `Boom` is `False`.** At `n = 1` the blocks run arm `S` directly. The hypothesis is `5 = 5`, proved by `refl`; the goal is `5 = 6`, which is `False`.

## The rule

**[Conv-bot].** A value that contains `⊥` anywhere (`Value.hasHole`) is convertible with nothing, itself included. In the checker, `conv` returns `false` when either side contains `⊥`, before any other test, the identity test included. [Conv-refl] becomes "identity, for values without `⊥`".

*Why.* `⊥` means "no information" (`docs/26`): the moved-out place stands for a value that the symbolic run has lost track of, and an instance may hold anything there. Two values that have each lost information can approximate different values at an instance, so identifying them says nothing about what they stand for. Conversion must be monotone in information (`docs/23`, the smaller (Mono)): it may answer "convertible" only where supplying the missing information could not make it false. D68 applied this to `Eq` computing to `True`; this rule applies it to conversion itself.

## What the lane must do

1. **Implement [Conv-bot] in `conv`.** Then audit every other place where a value equality (`==` on `Value`, or a cache keyed by a value) can make a type check, a `J`, an `Eq` or a goal succeed, and apply the same rule there. List each site and its verdict in the decision entry. Tests that only make the checker reject more are safe and need no change.
2. **Tests, as a twin pair** in the examples with the reasons asserted:
   - `reject def` for `Same` (and a `Boom` that would use it);
   - an accepted control where the two types are convertible without `⊥`.
   If an accepted program in the suite becomes rejected, keep it only if it is true and a twin explains the incompleteness. Otherwise investigate it: it may be a second instance of the bug.
3. **Rules and paper.**
   - Add [Conv-bot] to `RULES.md`'s conversion rules.
   - Add a `DECISIONS.md` entry: D83, unless `ochr-soundness` has taken that number. Ask it first.
   - Make the paper appendix's [Conv-refl] say "without `⊥`", and tag the rule in the checker's trace.
   - Check that the body still ends on page 25 (`ochr/core/CLAUDE.md`).
4. **Evidence.**
   - `lake build` must be green, with the verdict count before and after.
   - Give every verdict that changed, with its reason.
   - Re-run the probe, `Boom` included.

## Process

- Work in a raw `git worktree add ../ochre-bot-conv -b bot-conv origin/main`. Seed `.lake` with `cp --reflink=always -r` from the main checkout's `ochr/core/lean/.lake`.
- Build the narrowest targets first, then the full `lake build`.
- Commit on `bot-conv` and push the branch. Never use `git stash`.
- Do not merge. The orchestrator reviews, and the user decides the merge. After approval, rebase onto `origin/main` and `git merge --ff-only` in the main checkout.
