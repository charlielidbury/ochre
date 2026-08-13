# Compiling DLLBC: what already works, and what the borrows would become

*M35 probe, branch `m35-compile-probe`. Part 1 (the borrow-free fragment) is
built and measured; the code is `Dllbc/Compile.lean`, `Dllbc/CompileCmd.lean` and
`Dllbc/Tests/CompileProbe.lean`. Part 2 (this note's main business) is a map, not
a build: the choice of borrow target is deliberately left open.*

---

## 0. The one-paragraph version

The borrow-free fragment compiles to real Lean functions today. `fn Double (n :
Nat) -> Nat { … }` becomes a Lean `def Double : Nat → Nat`, `Double(3)` becomes
`Double 3`, and the compiled function computes the same value the DLLBC executing
machine computes — checked on 45 generated programs plus the standard library.
Erasure works, but **not for the reason the design suggests**: capitalisation is
about ownership, not about relevance, and what decides erasure is the type. That
same investigation turned up a problem worth fixing before any of this scales:
in a calculus whose ⊤ *is* `Unit`, erasure is not stable under conversion, and
whether a proof is deleted depends on whether the thing it proves is true.

For the borrows, three targets were assessed against the array carve. The
recommendation is **Lean's `Array`, threaded, with segments compiled to index
windows** — because it is the only one of the three that keeps the in-place
performance the north star exists to demonstrate. It charges for that by having
no type in which to receive the disjointness the carve establishes, and the piece
of design work a real milestone would be about is *exporting* that disjointness as
a generated lemma rather than dropping it.

---

## 1. What compiles today

The pipeline is three passes:

* **`compileTy`** translates a DLLBC type to a target type, and *is* the erasure.
  A type either denotes data (`Nat`, `Bool`, `List τ`, a Σ of data, a Π between
  data) or it denotes a spec, and a spec compiles to `erased`. Everything else
  follows without a second pass: a binder whose domain erases drops itself and
  its argument at every call, a Σ whose second component erases is its first
  component, a `let` whose type erases never reaches the output.
* **`synth`/`check`** compile terms. Church-style λs mean a binder always knows
  its own domain, so almost everything synthesizes; `check` exists for a bare
  `Nil` (no element type in the syntax) and for erased positions.
* **the renderer and `compile_dllbc`** turn the result into Lean source, parse it
  with Lean's own parser and elaborate it, so the definitions land in the
  environment and can be applied and evaluated.

Recursors become three small combinators (`Rt.natrec`, `Rt.listrec`,
`Rt.boolrec`) rather than `Nat.rec`/`List.rec`, because Lean's code generator
refuses recursors — a `def` built from them would typecheck and never run, and
running it is the whole point of the differential.

### Coverage, honestly

The executing corpus is dominated by `S8Diff`, which generates 136 bodies across
three telescopes and makes 238 concrete runs. The borrow-free split is total
rather than partial, because a telescope containing `&mut` puts a `borrowT` in
every program built from it whatever the body does:

| telescope | borrow-free | compiles |
|---|---|---|
| `(v : &mut List Nat) → Unit` | 0 / 91 | — |
| `(b : &mut Nat, c : Bool) → Unit` | 0 / 13 | — |
| `(n : Nat) → Nat` | 32 / 32 generated, 15 / 15 accepted | 45 / 45 runs |

So **45 of the differential's 238 concrete runs (19%) are in the fragment, and
all 45 compile and agree**. `S9Diff`'s four whole-program callers are 0 / 4 —
every function in their pool takes a `&mut`. Beyond the differential, the whole
of `Std.lean` is in the fragment: `len`, `count`, `add`, `take`, `drop`, `eqb`,
`leb` all compile and all agree with the machine.

That 19% is not a limitation of the compiler. It is what the corpus is *for*:
DLLBC's test suite is about borrows, so the fragment without borrows is the small
part of it.

---

## 2. Two findings from Part 1 that bear on Part 2

### 2.1 Erasure is type-directed, not mode-directed

The expectation was that the capitalisation convention makes deletion mechanical:
capital binders are comptime, comptime is erased, so erasure reads off the
binder's case. `Std.addFn` refutes it — `λ (A : Nat). λ (B : Nat). natRec …`,
both binders capital, and it is the addition every program computes with.

Capitalisation says how an argument is **read** (⇝-snapshot rather than ⇒-move).
It says nothing about whether the argument is needed to produce the answer. A
proof parameter and a `Nat` parameter are both capital and only one of them
erases.

What the mode discipline *does* buy is the other half: since a capital binding is
only ever cited from ⇝ positions, deleting one cannot leave a hole in Ω — nothing
downstream was going to move out of it. So the discipline makes deletion **safe**;
it does not make it **decidable**. The type does that.

### 2.2 Erasure is not stable under conversion, and the instability is truth-sensitive

This is the sharper finding, and it is about the calculus rather than about the
compiler. DLLBC is type-in-type with no `Prop`, no proof irrelevance and no
irrelevance marker. Its ⊤ *is* `Unit` and its ⊥ *is* `Bot`. So a spec and a
datatype are not two kinds of thing — a spec *reduces to* one:

```
compileTy (Le 1 2)             = erased
compileTy (nf (Le 1 2))        = Unit                      -- data!
compileTy (Sorted [1,2])       = erased
compileTy (nf (Sorted [1,2]))  = Unit × (Unit × Unit)      -- data, with structure
compileTy (nf (Le 2 1))        = erased                    -- Bot has no constructor
```

All four are asserted in the probe. Read the first and the last together: **a
false proposition erases and a true one does not.** Whether a proof is deleted
depends on whether the thing it proves holds.

This compiler dodges it by never normalizing a type — its only type reduction is
β at the head, so it always reads the type as written. That is a correct dodge
and it is not a fix, because the checker *does* convert, and any two types the
checker considers equal ought to erase the same way. Two ways out:

1. **An irrelevance marker.** A `Prop`-like universe, or a `⟨irrelevant⟩` marker
   on a type, decided syntactically and preserved by conversion. This is the
   standard answer and it is a calculus change, not a compiler change.
2. **Erase on the written type, by fiat**, and accept that a program which
   ascribes `Unit` where another ascribes `Le 1 2` compiles differently. Cheap,
   and it makes erasure depend on how a program is spelled, which will eventually
   surface as a bug report about a program that got slower after a refactor.

**Recommendation: do this before scaling codegen, not after.** It is cheap to
state and invasive to land, and every compiled program written in the meantime
would carry proofs as runtime data whenever a spec happens to be closed —
including, notably, every `Sorted` obligation on a concrete list.

---

## 3. The three candidate targets for the borrow fragment

The fragment is `&m`, `*b`, `:=`, take-and-refill, reborrows, borrow-mode match,
and the array **carve** — two disjoint `&mut` segments of one array, live at
once. The carve is the acid test, because it is the one construct where the three
options genuinely diverge.

Each option below has a runnable experiment in `Tests/CompileProbe.lean` §8: the
smallest program that exhibits the option's characteristic cost, hand-translated
and checked against what the DLLBC machine actually does.

### (a) Functional state-threading with backward functions — the Aeneas shape

Every `&mut τ` argument becomes an ordinary `τ` argument holding the value at
entry. A function that only writes through its borrows returns the new values of
everything it borrowed. A function that *returns* a borrow needs two functions: a
forward one computing what the returned borrow initially holds, and a **backward**
one that takes the returned borrow's final value and says what each captured
owner becomes. The caller inserts the backward call at the point the loan ends —
which sounds like guesswork and is not, because DLLBC's checker computes loan
ends already (`endLoan`, `reachesLoan`); a compiler would be exporting
information it has rather than inferring it. The experiment translates
`S9Diff.chooseCaller` this way — `choose_fwd`, `choose_back`, and the caller
sequencing them — and it agrees with the machine (`(7, 0)` on both sides).

**What the carve becomes: split and append of values.** `split_at_mut` becomes a
forward function producing two actual lists and a backward function
re-concatenating them. That is the problem. `design-arrays-slices.md` §8.3 states
the calculus's own erasure claim — "a carve compiles to pointer arithmetic, and
rejoin compiles to nothing", and this is "the strongest single argument for the
whole approach over the M23 stopgap", whose `split_off`/`append_back` "genuinely
mutate the runtime shape and walk `O(i)` cells". Option (a) reinstates exactly
that O(n) split and O(n) append. It is the option that discards the thing the
in-place north star exists to demonstrate.

**Machinery cost: moderate for codegen, and the honest framing is that Aeneas
already did it.** But note what the repo's `aeneas/` subtree measures: 16 Rocq
files, ~15.8k lines, and it is the *metatheory* of the LLBC translation for a core
without calls or shared borrows — a measure of what the approach costs to
*verify*, not what it costs to *build*. Also note what Aeneas itself does with
its output: it emits pure F\*/Lean **for proving**, and relies on `rustc` for the
executable. Under (a), "the λ compiled down to a Lean function" gives you a Lean
function that models the program rather than one that is the program.

### (b) Lean `Array`, threaded, with segments as index windows

Lean's `Array` is a real dynamic array whose `set`/`swap` mutate in place when the
reference count is one (FBIP). So a threaded array really is an in-place array,
and a compiled in-place quicksort really would sort in place. `&mut Array n T`
becomes nothing at all: the array is threaded as a value and linearity is
enforced by the runtime's refcount rather than by a type.

**What the carve becomes: index windows.** There is no Lean value that is "the
left half of `arr`, mutably", so `let l = &mut (*a)[0;k]; let r = &mut (*a)[k;rest];`
becomes: keep one array, represent `l` as `(lo=0, cnt=k)` and `r` as
`(lo=k, cnt=rest)`, and give every slice-taking function the shape
`(arr, lo, cnt) → arr`. Two *live* borrows become two *sequential* calls, each
taking and returning the whole array. For quicksort that is exactly right — the
two recursive calls are sequential anyway — and the experiment runs it:
`sortSeg (sortSeg #[5,3,1,9,7,2] 0 3) 3 6 = #[1,3,5,2,7,9]`.

**What breaks.** Two things, and the first is the serious one. *Disjointness
stops being a type.* DLLBC discharges it once, with a `Le` term at the carve, and
from then on it is "a shape being read" (¶5). At the target it is arithmetic on
index arguments that nothing checks: the experiment asserts that the very same
`sortSeg`, given overlapping windows (`0 3` then `2 6`), is accepted by every type
in sight and silently destroys the first result. Second, *frame conditions come
back*. `Sorted (*v)` becomes a statement about `arr` restricted to `[lo, lo+cnt)`,
and the `↝`-obligation pinning the untouched remainder becomes an explicit
`∀ i, i < lo ∨ i ≥ lo+cnt → arr'[i] = arr[i]` in every specification — which is
the frame condition the borrow discipline was designed to make free, arriving as
a bill at the target.

**Machinery cost: small for codegen, large for specs.** The codegen is nearly
bookkeeping the compiler already has — the extent map *is* the segment table, and
it already carries every `(lo, cnt)` the target needs. The spec translation is
its own milestone.

### (c) `ST` / `IO` reference cells

`ST.Ref σ τ` is a first-class mutable cell, so the pointer half of the fragment
translates one-for-one and beautifully: `*b` is `b.get`, `*b := v` is `b.set v`,
passing a borrow is passing a ref, and — the case that costs option (a) a whole
second function — *returning* a borrow is returning a ref. The experiment shows
`Choose` needing no translation at all: `let r := if c then a else b; r.set 7` is
the same program in both languages. No backward functions, no threading, no
loan-end analysis.

**What the carve becomes: the wall.** `ST.Ref σ (Array τ)` is one cell holding
one array. There is no `ST.Ref` to a *slice*. To get two disjoint mutable
segments you need either index windows over the cell's contents — which is option
(b) with a monad wrapped round it, inheriting all of (b)'s costs — or a genuine
separation logic over the ST heap, which Lean does not have in mature form today.

**And the verification cost is decisive.** A program in `ST` is opaque to
equational reasoning: to prove `Sorted` you either build a pure model and prove
the `ST` program refines it, or you adopt a program logic. The first is option (a)
with extra steps. And it is precisely what the project has already ruled out —
SUGGESTIONS' 2026-07-28 redirect says routing verification through a pure model
"is Aeneas rebuilt in one language" and "never exercises dependent-types-×-mutation
where it is hard". Option (c) forces that routing back on you at the target, one
level down where it is harder to see.

---

## 4. The pick

**Take (b): Lean `Array`, threaded, segments compiled to index windows.** Keep
(a) available as a *proof* device — a pure model to relate a compiled program to
when that is the convenient way to state something — but not as the target.

The reasoning in one line: (b) is the only one of the three that delivers what the
calculus's own erasure story already promises. `design-arrays-slices.md` §8.3 says
a range borrow should compile to a `(base + lo, cnt)` pair computed by two
instructions and a rejoin should compile to nothing. Lean's FBIP `Array` gives
exactly that. Option (a) gives up the in-place performance that is the north
star's whole point; option (c) gives the prettiest translation of the pointer
fragment and then walls on the array fragment, which is the fragment quicksort is
about.

**The bill (b) charges, and how to pay it.** The one real loss is that the target
has no type in which to receive the disjointness the carve establishes. The
answer is not to drop that information — it is to **emit** it. Compile a carved
segment to `(arr, lo, cnt)` *plus a generated Lean lemma* stating that the windows
a program uses are pairwise disjoint and in bounds, with the proof built from the
`Le` terms the carve already consumed. The checker has the evidence; the compiler
would be re-exporting it, not inventing it. That turns (b)'s silent-wrong-answer
failure mode into a discharged obligation, and it is the piece of design work a
real milestone should be about.

---

## 5. What a real M35 would cost

Ordered as I would do it, with the reason for the order.

1. **Fix erasure's conversion-instability first** (§2.2). A calculus change — an
   irrelevance marker or a `Prop` universe — not a compiler change. Doing it
   after the codegen scales means every program compiled in the meantime carries
   proofs as data whenever a spec is closed, and re-deciding erasure later
   changes the runtime representation of everything.
2. **The pointer fragment under (b)-as-threading** — `&mut` on non-array data,
   `*`, `:=`, calls, reborrows, borrow-mode match. The mechanical part is "which
   owner does this borrow resolve to, and where does its loan end", and the
   checker computes both already; the work is exporting them from the loan
   machinery rather than deriving them. One milestone.
3. **The array carve.** Codegen is nearly free — the extent map already holds
   every `(lo, cnt)` the target needs. The milestone is the disjointness-lemma
   export of §4, and that is a design question before it is an implementation.
4. **Specs.** Translating `↝`-obligations and exit snapshots into frame
   conditions over index windows. Probably the largest of the four, and the one
   that decides whether a compiled quicksort's *proof* survives compilation or
   only its code does.

What Part 1 says about the size of all this: the borrow-free compiler is 424
lines of code (782 with its commentary) across two files, and it was not the hard
part. Nothing in it walled. Every difficulty this
probe met was about *what a type means* — whether it is a spec, whether it erases,
whether conversion preserves that — and none was about the mechanics of emitting
Lean. That is the useful prior for the rest: the codegen is cheap, and the
semantics of erasure and of the borrow-to-window translation is where the
milestone actually lives.
