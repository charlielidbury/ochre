# The 00-idea examples in separation logic (VeriFast)

The examples from `ochr/docs/00-idea.md`, written in C and verified with VeriFast, a separation-logic checker for C whose contracts live in `/*@ ... @*/` comments. The question they answer is "how would separation logic handle this", and in particular whether it can do it without a pure specification of the value (a ghost `N` with `plus`, a ghost `L` with `app`) kept apart from the heap.

Short answer: with the pure spec, the proofs are the same three lines as in a proof assistant plus a tax for the heap. Without it, separation logic with fractional permissions can still prove every property tried, but only as facts about heap effects or about two runs, never as an equation between two programs. Fraction-free separation logic cannot say "unchanged" about an unbounded structure without naming its contents, which is the pure spec again.

## Running

```
nix run            # verify every accepted file and print the reports
nix flake check    # the same, plus every rejection below
nix develop        # a shell with `verifast` on PATH
```

## Files

With the pure spec:

| File | What it is |
|---|---|
| `addm.c` | Peano nats on the heap (`NULL` is `Z`, a node is `S(pred)`). `addM` walks `x` to its final `Z` and moves `y` in; `add` is the by-value wrapper; `add_zero` is the doc's `AddZero`. Contracts via ghost `N` and `plus`; the lemma `plus_zero` by induction on `N`. |
| `addm-min.c` | The same with every ghost step VeriFast can do itself removed: precise predicates give auto open and close, `lemma_auto` applies `plus_zero` unasked. One `open` remains. |
| `concat.c` | Cons lists; `concatM` and `concat` likewise; `concat_left` and `concat_right` are `(a ++ b) ++ c` and `a ++ (b ++ c)` and meet one contract, the left one via `app_assoc`. |

Without any pure spec (no ghost inductive, no fixpoint, no length; every ghost argument is a node pointer):

| File | What it is |
|---|---|
| `concat-nospec-1.c` | `seg(p, last)` holds the interior tails at half permission and `lst(p, last, v)` adds the last node's tail in full. `concatM`'s contract is "the only cell you may write is the final tail, and afterwards it holds `b`". Both nestings meet one contract that pins which two cells were written and with what. |
| `concat-nospec-2.c` | Relational: `same(p, p2)` is a lockstep walk over two lists with no sequence. `assoc_two_runs` runs each nesting on its own copy and proves `same` of the results. |
| `concat-nospec-3.c` | The segment-composition lemma `lseg(a,la) * la.tail = b * lseg(b,lb) |- lseg(a,lb)`, applied in both orders under identical contracts. With no sequence there is no equation left to prove. |
| `add-nospec-1.c` | The nat version of `concat-nospec-1.c`. `add_zero` verifies with zero ghost statements in its body: its postcondition is its precondition. `add_xy` and `add_yx` get different pinned contracts and no single-run contract calls them the same number. |
| `add-nospec-2.c` | Relational commutativity: `comm_two_runs` runs `add(x, y)` and `add(y2, x2)` on two copies related by `same` and proves `same` of the results. The lemmas `rot1` and `cross` are the heap forms of `n + S m = S (n + m)` and `x + y = y + x`, by induction on the heap predicate. |
| `concat-nospec-1-naive.c` | Full-permission `lseg` with no sequence. Verifies, and so do its two impostors `concat_zeroed` and `concat_lossy` in the same file, against the same contract. |
| `concat-nospec-1-classical.c` | Fraction-free, heads kept out of the footprint. Verifies, and so do three impostors in the same file, one of which swaps two interior nodes. |

Rejected, each pinned by `nix flake check` to its exact error:

| File | Program | VeriFast says |
|---|---|---|
| `concat-nospec-1-impostor-dropc.c` | returns `a ++ b`, leaks `c` | `No matching heap chunks: lst(r, ...)` |
| `concat-nospec-1-impostor-swap.c` | computes `(a ++ c) ++ b` | `No matching heap chunks: lst(r, ...)` |
| `concat-nospec-1-impostor-head.c` | correct links, then zeroes a head | `No matching heap chunks: list_head_(r, _)` |
| `concat-nospec-1-impostor-relink.c` | rewrites a non-final tail | `No matching heap chunks: list_tail_(a, _)` |
| `concat-nospec-1-impostor-swap23.c` | swaps `a`'s second and third nodes | `No matching heap chunks: list_tail_(a, _)` |
| `addm.c` minus `//@ plus_zero(n);` | unchanged | `Cannot prove plus(n, Z) == n` |
| `concat.c` minus `//@ app_assoc(xs, ys, zs);` | unchanged | `Cannot prove app(app(xs, ys), zs) == app(xs, app(ys, zs))` |

## With the pure spec: the proof is three lines, the heap is eight

The ghost text of `addm-min.c` splits into what a proof assistant also needs and what only the heap needs:

| Ghost lines | Count | Lean has it too? |
|---|---|---|
| `inductive N`, `fixpoint plus` | 2 | yes, as `Nat` and `add` |
| `plus_zero` | 4 | yes: `addZero Z = rfl; addZero (S px) = congArg S (addZero px)` |
| `predicate nat(p; n)` | 1 | no |
| contracts for `addM`, `add`, `add_zero`, plus one `open` | 7 | no |

The last two rows are the whole cost of having a heap: one line saying which heaps represent which number, and a contract for every function that crosses that seam. The induction is done twice, once by the checker in `addM`'s body against `plus` (the recursive call is the induction hypothesis and the frame rule lifts it from `px` to `x`, the doc's steps 1 and 2) and once by the user in `plus_zero`. `AddZero` is a fact about `plus`; `add_zero` only transfers it.

## Without the pure spec: what survives and what it costs

Give `addM` its most general contract instead of a `plus` contract: the one cell you may write is the final one, and afterwards it holds `y`. Then `x + 0 = x` needs no lemma and no induction at the use site, because with `y = 0` the contract writes the one writable cell with what it already held, and every other cell was only lent at half permission. The induction is done once, in `addM`'s body. Associativity likewise: both nestings end in the identical heap, so a contract that pins which cells were written settles it, and the only lemma is segment composition, by induction on the heap predicate.

Where the two sides end in different heaps that represent the same value, as `add(x, y)` and `add(y, x)` do, no single-run contract can state the equality. It is still provable, as a theorem about two runs on two copies related by a lockstep predicate, with the pure proof's shape reappearing as heap lemmas (`rot1`, `cross`), and still with nothing sequence-shaped in the file.

What this depends on, and what a skeptic can say:

- **Fractional permissions.** "The callee cannot have changed this cell" is expressed as a permission fact. Without fractions a cell in the footprint is fully owned, so the callee may rewrite it, and a cell outside the footprint cannot be traversed. `concat-nospec-1-naive.c` and `concat-nospec-1-classical.c` show the same vocabulary without fractions admitting impostors. A spine predicate with pointer arguments pins its two end nodes and nothing between; naming k interior nodes pins k more, and an impostor swaps the next two. That is an argument from exhibited impostors, not an impossibility proof.
- **The number is existentially eliminated, not absent.** For nats `same(p, p2)` is logically "p and p2 have the same number of nodes", and `seg(p, last)` is "there is some chain". The relation is defined without numbers and the induction is on the heap chunk, but the mathematics still has a number in it.
- **It is never an equation.** `concat_left` and `concat_right` meet one contract; two runs give the same list. Neither is a term-level identity between the two programs, which is what the doc wants `Refl` to inhabit. It is the doc's `⟨Ω, e⟩` comparison done as a Hoare triple.
- **The residue.** An eight-way null-ness case split in the concat contract (an empty list has no cell to write), and ghost pointers `la`, `lb`, `lc` naming where each number ends.

What this says about the doc's design: the `nat(p, n)` seam is what makes the proofs longer than three lines, and separation logic can only remove it by moving the same information into permissions and relational predicates. A language in which the heap value is the value has no seam to move, and `AddZero` can be the three-line proof about the in-place `Add` itself. That is the claim `ochr/docs/00-idea.md` sets out to make good.

## VeriFast

Source and manual: https://github.com/verifast/verifast

The list theory is standard enough that VeriFast ships it: `list.gh` in the install defines `list<t>`, `append`, and `append_assoc`. `concat.c` defines its own `L` and `app` so the pure spec stays visible in the file. The nixpkgs package (`pkgs.verifast`, 25.08 in the pinned nixpkgs) is Linux only.
