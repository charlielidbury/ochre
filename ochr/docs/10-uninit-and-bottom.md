# 10. `Uninit(E)` and ⊥: feasibility check (do not merge)

Lane: `uninit-bot` (fresh agent, worktree `ochre-uninit`, branch `uninit-bot`). Written by team-lead on 2026-10-01 from the user's requests.

**This is a feasibility check. Nothing from it lands on `ochr-core`.** Push the branch, report, and stop. The user decides afterwards.

## Why

The user rules that `Array` is the fixed-size primitive and `Vec` must be user code ("Vec should not be a primitive (this is a hard requirement). If Vec cannot be made user-land then Array needs fixing"). They want `Vec`'s spare capacity represented as uninitialised cells (`Uninit(E)`, like Rust's `MaybeUninit<T>`: no runtime tag), and leaking the contents of dropped `Uninit` cells is accepted for now.

They then observed that a moved-out place already behaves like an uninitialised one: `let y = x` leaves `x ↦ ⊥` in Ω, with no runtime tag, and the checker ensures it is never read. They asked: "could the concepts be merged somehow? or is that overly forced".

The interim `Vec` (docs/09 §7, lane `arrays-e`) uses `Array(Opt(E), cap)` with an external invariant. It hit a problem: if "cells below `len` are filled" is a proof field of the `Vec`, `get` cannot return `&E`, because a borrow into `buf` clears the proof field and nothing can restore it while the returned borrow is live (`[Repack] … field hp of MkVec: it holds ⊥`). So callers carry the invariant themselves.

## The proposed merge

`Uninit(E)` means "an `E`, or ⊥", and its empty case *is* the ⊥ a move leaves.
1. **Ordinary types.** A place of an ordinary type must not hold ⊥ whenever it is used whole: read, passed, returned, a borrow of it ending, or stored in data. This is today's rule, unchanged.
2. **`Uninit` types.** A place of type `Uninit(E)` may hold ⊥ at all of those points. That includes fields of type `Uninit(E)`, and cells of `Array(Uninit(E), n)`.
3. **Writes.** Assigning into an `Uninit(E)` place is ordinary assignment. The old content is discarded without drop, which is the leak the user accepted.
4. **Reads.** Moving out of an `Uninit(E)` place is an ordinary move, and leaves ⊥.
5. **The one new rule.** `*u` may be used at type `E` (read, borrowed as `&E`, matched) when the checker knows it is not ⊥: either Ω holds a non-⊥ value there, or a proof `h : Init(*u)` is supplied. Choose the surface form for supplying it. The criteria are no new runtime operation and the fewest rules.
6. **`Init` in proofs.** `Init(x) : Prop` computes to `⊤` on a value and to `False` on ⊥, and is stuck on an unknown value. A proof may case-split an unknown `σ : Uninit(E)` into ⊥ and a fresh `σ' : E`. Runtime code may not branch on initialisation, since there is no tag.
7. **Copies.** `Uninit(E)` is a copy type iff `E` is.

## Questions to answer

1. **Two kinds of ⊥.**
   - Lane examples-tour (branch `erased-moves`, not yet landed) just made an equation over ⊥ *stuck*. A stuck block over-approximates moves, so ⊥ on the symbolic path did not mean "moved" on the ground path, and `Eq ⊥ ⊥ = ⊤` led to a closed False (its case 11014 / probe U1).
   - Under the merge, ⊥ in an `Uninit(E)` cell is a real value, and `Eq(Uninit(E), ⊥, ⊥)` should be `⊤` (equal buffers).
   - Can these two kinds of ⊥ be told apart (the moved artefact, and the empty value) without a mode? Is the over-approximation itself what should change? Read `erased-moves`' commits and DECISIONS entry first.
2. **Vec's `get` returning `&E` without an external invariant.** Find a design that achieves it and check it. Candidates:
   - a type computed by recursion that puts "cells below `len` are `E`" in the type (`Mixed(E, len, cap)`), and whether `Array`'s natives (`GetMut`, `WithSplit`, …) can serve it or would need duplicating, which breaks "Array is the primitive";
   - a zero-cost coercion `&Slice(Uninit(E), n)` → `&Slice(E, n)` given `AllInit`, which is sound because an `&E` borrow must end whole;
   - anything better.
   Report which one works and what it costs.
3. **Path agreement.** Does rule 5 fit the checker's two evaluation paths (generic on unknown inputs, and instance)? Run the fuzzer, with a family that exercises `Uninit` if one is needed (seed 1, 2·10⁴ cases, at most 6 workers, `taskset -c 0-14`). Are there new finding kinds?
4. **Rule count and wording.** How many RULES lines change? Can the existing "partly moved out" and "borrow must be whole again" rules be restated as rule 1, so that the total goes down?
5. **Is it forced?** Give a frank verdict, compared with the alternative: an abstract `Uninit(E) := Empty | Full(x : E)` with four natives (`UNew`, `UWrite` needing `IsEmpty`, `UTake` and `UGet` needing `IsFull`), no checker change, whose model has a ghost tag that runtime code never inspects (K3).

## Deliverables

- A prototype behind a switch (`uninitTypes`, off by default) on branch `uninit-bot`, pushed. It must have:
  - tests: accepted programs, `reject def`s, and a small user-land `Vec` with push, pop and get returning `&E`;
  - a ledger row.
- A report, at most about one page, answering 1–5 with numbers, and a recommendation: merge, the four-native `Uninit`, or something else.
- The default config must stay green on the branch: `lake build`, `lake build tests fuzz`, `lake exe tests`.

## Working rules

- **Starting point.** Base the branch on `origin/ochr-core`. Lanes `erased-moves` and `arrays-e` are changing ⊥ handling and the arrays library; read their branches, but don't build on them.
- **Commits.** Commit and push the branch at checkpoints. Never `git stash`. Never push to `ochr-core`.
- **CPU.** Pin heavy commands to cores 0-14, and run one `lake build` at a time.
- **Writing.** Plain language, no hard wrapping, and no bare internal ids.
