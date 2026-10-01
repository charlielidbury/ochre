# 09. The arrays library after `&E`

Lane: `arrays-e` (fresh agent, worktree `ochre-arrays-e`, branch `arrays-e`). Written by team-lead on 2026-10-01 from the user's requests.

D66 (docs/08, landed f0bed3db) made `&A` well formed for every `A : Type₀`, including a type variable `E`. The arrays library (`ochr/core/lean/Ochr/Examples/16Arrays.lean`) and the benchmark packages still carry workarounds from before that. The user asked to "follow through all the consequences of that &E".

## 1. Generic `GetMut`

- Make `GetMut(E, n, s, i, h) : &E`, and its lemmas (`GetMutSet`, …), generic in `E`.
- Delete `GetMutB`, the `List(Entry)` copy, and point its callers at `GetMut(List(Entry), …)`.

The lead checked a generic `GetMut` (native), a runtime write through it, and a generic `GetMutSet` against ochr-core 297dff47: all are accepted. See `TG.lean` below.

## 2. Remove `Read`

User: "copying elements should be left to the caller so they are aware they are doing a copy".

- Callers write `let r = GetMut(E, n, s, i, h); clone(*r)`, or `*r` for a copy type such as `Word` (a copy type copies implicitly, as everywhere else).
- Restate every `Read` lemma and test through `GetMut`, or delete it if it only tested `Read`.
- Sites:
  - 16Arrays (14);
  - 18DependentFields (2);
  - `ochr/bench/common/ochr/GUIDE.md` and `sandbox.py`;
  - `OCHR_BOOK.md` §9;
  - the paper: `impl.typ`'s list of primitives, and any printed program.

## 3. Copy-free `Swap`, and whether `Set` stays: measure first

User: "is there even any point in having Set at all?"

**At runtime, no.** `let r = GetMut(…); *r := x` does the same thing.

**In proofs, maybe.** A native's model body is what the checker runs. `Set`'s model is the write `*s := SetS(E, n, *s, i, x, h)`, so a proof about code that calls `Set` sees `SetS`, the form every lemma (`CountSet`, `NthSetSame`, …) is stated in, by evaluation alone. A write through `GetMut` at an unknown index evaluates to a sealed `GetMut` program instead. That equals the `SetS` form only by `GetMutSet`, a lemma proved by induction, which each proof would have to invoke at each write.

`Swap` has the same issue:
- Today, `Swap` is `Read`, `Read`, `Set`, `Set`, and `SwapIsSwapS` holds by `refl`.
- Without copies, it is built from `WithSplit` and two `GetMut`s. The lead checked `SwapLt` (the `i < j` case) in `TG.lean`.
- That version satisfies `SwapIsSwapS` only by a proof, and the quicksort proofs would have to invoke it.

The alternative for both is Rust's: `slice::swap` is a primitive (a pointer swap). `Swap`, and `Set` if kept, would be natives whose *model* is the `SwapS`/`SetS` write. Model code isn't run at runtime, so the model needs no copy, and the native implementation doesn't copy either.

**Procedure:**

1. Remove `Set` from the runtime API. The model `SetS` stays. Make `Swap` the copy-free derived version: case on `i < j`, `j < i` and `i = j`, using `WithSplit` + `GetMut` + a swap through two borrows by moves (`let t = *a; *a := *b; *b := t`). Prove `SwapIsSwapS` as a lemma.
2. Migrate quicksort, the hashmap case studies and the arrays lemmas, and count the cost: how many proofs need new lemma invocations, and how many lines are added.
3. Decide by this rule. If the whole migration adds at most about 10 lemma invocations and keeps every proof, keep the removal. Otherwise:
   - keep `Swap` as a native whose model is the `SwapS` write (`implemented by "ochr_arr_swap"`);
   - keep `Set` as a native whose model is the `SetS` write;
   - leave the derived copy-free `SwapLt` as a tested example.
   Either way, report the numbers. Don't ask before deciding.

Afterwards, the paper's count of runtime primitives must be correct. It is eight today: AsSlice, Read, Set, GetMut, WithSplit, empty, push and pop.

## 4. `*f(…)` as a place

Today `*GetMut(…)` is rejected with "(surface) not a place", followed by a raw syntax-tree dump. Once `Read` and `Set` are gone, `*GetMut(E, n, s, i, h) := x` is the natural one-liner. Rust accepts `*v.get_mut(i) = x`.

- In the surface elaborator (`Surface.lean`), desugar a dereferenced call `*f(ā)` used as a place to `(let tmp = f(ā); … *tmp …)`, with a fresh name. The temporary ends at the end of the enclosing assignment, read or match, as Rust's temporaries do.
- Fix the "not a place" message so it shows the source text, not the syntax tree.
- Add tests:
  - `*GetMut(…) := x` is accepted;
  - reading a non-copy `*GetMut(…)` is rejected (it would move out through the borrow), and the message says so;
  - `clone(*GetMut(…))` is accepted.
- RULES needs no change if this is a pure surface desugaring. If it isn't, stop and report.

## 5. Notes

- Rewrite the `[K1]` note at the top of 16Arrays and the header's count of `clone`s.
- If `&Cells(E, n)` at an unknown `n` is now well formed too, say in your report whether the `SliceOf` wrapping of cell tails can go. Don't change the representation.

## 6. Generic `V` in the Ochr hashmap benchmark packages (after 1–5 land)

`ochr/bench/hashmap/SPEC.md` keeps the `ochr` and `ochr-2p` packages word-valued "pending D66"; D66 has landed. Move both to the generic API in SPEC §3:
- `Bucket(V)`;
- `contains(&m, k) : Bool`;
- `get(&m, k, h : Contains(*m, k)) : &V`, used read-only;
- `get_mut → &V`;
- `SlotMut` replaced by the generic `GetMut`;
- H rows split into their `contains` and value parts.

Update the SPEC rows that say "Pending D66". Acceptance: the reference solution passes `grade.sh`, the skeleton's holes are named, and the sandbox builds. Also update the quicksort packages and the shared GUIDE for whatever 1–4 changed.

## Landing (FF-CAS, by you)

Two other lanes are landing on `ochr-core` while you work:
- **callform** moves all syntax to call form (`f(a, b)` everywhere, no juxtaposition) and makes projections 0-based. It is nearly done.
- **examples-tour** makes reads inside statements move. It touches 16Arrays (it migrates some `Id` sides to `clone(*x)`), RULES, the paper and the book.

Write all new code in call form, with no `.1`/`.2` projections. Whoever lands second rebases and re-runs acceptance. Land 1–5 together once all of these pass:
- `lake build`, `lake build tests fuzz` and `lake exe tests` are green;
- fuzz statuses are unchanged (`--rules` and the default families, at most 6 workers);
- every program printed in the paper checks (the paper sweep), and the page count is unchanged.

Then land 6 separately. Pin heavy commands to cores 0-14 (`taskset -c 0-14`). Run one `lake build` at a time.

Scratch checks by the lead: `/home/charlielidbury/.claude/jobs/16809284/tmp/book/TG.lean`. It contains a generic `GetMutG` (native), `UseG`, a generic `GetMutSetG`, `SwapRefs`, `SwapLt`, a concrete `SwapRun` that swaps `[4, 9]` and reads `9`, and `TwoGetMut`, which is rejected because the second `GetMut` ends the first.

## 7. `Array` is fixed size; `Vec` is user code (user ruling, 2026-10-01)

The user's ruling: "the runtime representation of Array will be like Rusts [T; n]. It will not be Vec<T>. Array is used to implement Vec, it is the constant sized primitive. This means pop and push are NOT available." And: "Vec should not be a primitive (this is a hard requirement). If Vec cannot be made user-land then Array needs fixing." Also: "Replicate(E, n, x) shouldn't _need_ to be native."

The design, option A:
- **Remove `ArrPush` and `ArrPop`.** Migrate every use: `Replicate`, `Vec` and the tests in 18DependentFields, the quicksort benchmark tests (`gen_tests.py`), the GUIDE's `BumpRun`, `Two`, the paper sweep, book §9, `sandbox.py`, the notes, `docs/06`, and the paper's list of primitives.
- **One allocation native, `ArrFromFn(E, n, f : Π(i : Word). E) : Array(E, n)`.** It is Rust's `array::from_fn`: it allocates `n` cells and fills cell `i` with `f(i)`. Its model is the recursion on `n`. `ArrEmpty` becomes `ArrFromFn(E, Zero, …)`, or the literal `[]`.
- **`Replicate` in Ochr, not native:** `ArrFromFn(E, n, λ(i : Word) : E => clone(x))`.
- **Array literals.** `[a, b, c] : Array(E, W(3))` is a surface form. It is primitive, as Rust's array literal is, and its model is the `Cells` value, so lemmas fire by evaluation. Choose the simplest sound implementation (for example, an elaboration to a dedicated literal native), and report what it is and whether it adds to the native count. Use literals for the quicksort benchmark tests and every other concrete test array.
- **`Vec` as user code over `Array`:** `MkVec(len, cap, buf : Array(Opt(E), cap), …)` with proof fields saying that cells below `len` are `Some` and cells from `len` on are `None`, and `len ≤ cap`.
  - Push writes `Some(x)` into cell `len` through `GetMut`. When `len = cap`, it allocates `ArrFromFn(Opt(E), 2·cap + 1, λ…. None)`, moves the elements across (take each cell by replacing it with `None`), and drops the old buffer.
  - Pop takes cell `len - 1`.
  - Get returns `&E` from `GetMut` on the cell, with the `None` arm ruled out by the invariant.
  - This keeps the dependent-fields showcase (`buf`'s type depends on `cap`; the proof fields depend on `len` and `buf`).
  - Write lemmas for push, pop and get in the same style as the rest of 18DependentFields.
- **The cost of A** is one tag per cell at runtime. If that ever matters, the fix belongs in `Array`'s element types (a tag-free uninitialised cell type whose model is `Opt(E)`, like Rust's `MaybeUninit`), not in `Vec`. Note that in your report; don't build it.

The natives would then be `AsSlice`, `GetMut`, `WithSplit` and `ArrFromFn`, plus `Set`/`Swap` if §3's measurement keeps them, plus any literal native. Land §7 together with 1–5, or as its own FF-CAS landing right after them, under the same acceptance.
