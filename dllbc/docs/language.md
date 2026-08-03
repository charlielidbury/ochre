# Programming in DLLBC

This is a working programmer's introduction to DLLBC. It is linear: read it top to bottom,
and nothing is used before it is introduced. Each chapter introduces one thing, says
precisely what it is, and shows it in real code — every example in this document is either
verbatim from the test suite or a fragment of something that is. It is not a specification
and contains no theory; the design document (`dllbc-arrows.md`) exists for that.

**What you need to already know.** DLLBC assumes fluency in two things it does not teach.
From **Rust**: ownership and moves, `&mut` borrows, pattern `match`, and the general
experience of a borrow checker rejecting your program (look up: the Rust book, chapters 4
and 6). From **Lean (or any dependent type theory)**: propositions as types, `Π` and `Σ`
types, inductive datatypes and their recursors, and proof terms as first-class values
(look up: "Theorem Proving in Lean 4", chapters 2, 4, 7). If both of those lists read as
familiar, you have everything this document requires.

**What DLLBC is.** One language in which programs, types, and proofs are the same kind of
thing. You write an imperative function that mutates through borrows, Rust-style; its
return type is a proposition about what it did; the body constructs the proof as an
ordinary value and returns it. There is no separate annotation language, no verification
condition generator, and no model of your program in some other system — the checker reads
the function you wrote.

---

## 1. Declarations

A DLLBC program is a set of function declarations. A declaration gives a name, a
parameter list, a return type, and a body:

```
fn set_at [i] (v : &mut List Nat, i : Nat, x : Nat, hi : Le (S i) (len *v)) -> …
   { … }
```

Read the parameter list left to right; each parameter's type may mention the parameters
before it — `hi`'s type mentions `i` and `v`. That one rule is pervasive; most of the
language's power routes through it. (Error messages and the design documents call the
parameter list a *telescope* — same thing. And ignore the `[i]` for now; it is
chapter 9's.)

The basis is small and fixed. Types: `Unit`, `Bool`, `Nat`, `List T`, `Array n T`, `Π`,
`Σ`, and the equality type `Id A a b`. Values are built from constructors: `unit`, `True`
/ `False`, `Z` / `S(n)` (numerals like `3` are sugar), `Nil` / `Cons(h, t)`,
`Pair(a, b)` for `Σ`, and `Refl` for `Id`. There are no user-defined datatypes yet; in
practice the basis plus `Nat`-indexed arrays covers a lot.

Bodies are sequences of statements ending in an expression:

```
let x = e;        -- bind
p := e;           -- assign through a place
f(a, b);          -- call, result discarded
result            -- the final expression is the return value
```

Calls use parentheses with no space — `split_off(&mut *v, i, hi)`. Pure functions from
the library apply by juxtaposition, Lean-style — `add i (S j)`, `le_trans a b c h1 h2`.

## 2. Ownership

Rust's rules, with one boundary drawn differently. Using a value **moves** it; a moved
variable is dead and the checker rejects later uses. But *small* things copy instead of
moving: numbers, booleans, and — importantly — **proofs**. Data (lists, arrays, pairs of
data) always moves. So you can pass an index or a `Le` proof twice without thinking, but
passing a list consumes it.

One consequence you will meet in chapter 11: passing a proof to a call moves it *if the
call's parameter binds it dependently* — treat proofs you will need twice like data and
capture what you need from them first.

## 3. Borrows and mutation

`&mut e` borrows a place; `*b` reads or writes through the borrow; borrows end
automatically when something demands the borrowed value back. All Rust-familiar:

```
let b = &mut v;
*b := Cons(1, Nil);      -- write through
let n = len *b;          -- read through
```

Reborrowing a component works the way you expect: `&mut *tl` reborrows the payload.
Matching *through* a borrow gives you borrows of the fields:

```
match v {                 -- v : &mut List Nat
  Nil => …,
  Cons(hd, tl) => …       -- hd : &mut Nat, tl : &mut List Nat
}
```

The idiom Rust forbids and DLLBC leans on is **take-and-refill**: move the payload out
through a borrow, leave something in its place, put something back later.

```
let tail = *v;            -- take the whole payload (Rust's E0507 — legal here)
*v := Nil;                -- refill
```

The obligation is simply that the borrow holds a value of the right type again by the
time the function returns; between the take and the refill it may hold anything or
nothing.

## 4. Types that compute

Types are expressions in the same language, so a type can mention values — including the
current payload of a borrow, written `*v`:

```
fn set_at [i] (v : &mut List Nat, i : Nat, x : Nat, hi : Le (S i) (len *v)) -> …
```

`Le a b` is the ≤ proposition on `Nat`, and it *computes*: `Le 1 (S j)` unfolds, by
running its definition, to a trivially-true type, while `Le (S i) Z` unfolds to `Bot`,
the empty type. `len`, `count`, `take`, `drop`, `append`, `add`, `leb`, `eqb`, `Sorted`
are all in the same standard vocabulary — ordinary computable functions, usable in types
and in code alike.

A parameter like `hi` is a **precondition**: callers must supply a proof value, and there
is no proof of a false `Le`, so `set_at` simply cannot be called out of bounds. Inside
the body, `hi` is an ordinary value you can pass along. Dead branches discharge with the
empty type's eliminator: if some hypothesis has computed to `Bot`, the branch returns
`botElim T h` at any type `T` — "this cannot happen, and here is why".

Equality is `Id A a b`, and its proof is `Refl` — accepted whenever the checker can
*compute* the two sides to the same value. Much more follows from that than you might
expect, because so much of the vocabulary computes.

## 5. Writing proofs

Proof terms live in `pure{ … }` blocks — the borrow-free fragment. You have `λ`, `Π`,
`Σ`, application, and one workhorse: `elim`, structural recursion with an explicit
motive. The standard library's own `le_refl` is the complete idiom:

```
def le_refl : Term := pure{
  λ (n : Nat). elim n return (λ (m : Nat). Le m m) {
    Z => unit,
    S (k) ih => ih } }
```

Read: by induction on `n`, prove `Le n n`; at `Z` the goal computes to a trivial type
(`unit` inhabits it); at `S k` the induction hypothesis `ih` is exactly the goal. The
motive after `return` is written by you, always — nothing is inferred. Nested `elim`s
express nested induction (see `le_trans` in `StdLemmas.lean` for the canonical
three-level example).

The equation toolkit is `Refl`, `id_sym`, `id_trans`, and `id_congr` (map a function
across an equation). Most proofs about this vocabulary are chains of those four plus
library lemmas, with computation silently closing the gaps.

**The standard library is `Dllbc/StdLemmas.lean`.** Before proving anything about `Le`,
`count`, `append`, `Sorted`, or their `Array` counterparts, look there — the lemma you
want likely exists, and its statement (every `def foo` has a `foo_ty` companion) shows
you the naming conventions. Library lemmas are cited in bodies by name, applied like any
function.

## 6. Postconditions

A return type may describe the function's *effect*. For a `&mut` parameter `v`, the
return type reads `*v` as the payload **at exit**, and `old *v` as the payload **at
entry**. This is the heart of the language. A complete verified function, from the suite:

```
fn append_back [v] (v : &mut List Nat, w : List Nat)
    -> Id (List Nat) (*v) (append (old *v) w)
    { match v {
        Nil => { *v := w; Refl },
        Cons(hd, tl) => {
          let y = append (*tl) w;
          let h = append_back(&mut *tl, w);
          id_congr (List Nat) (List Nat) (λ (a : List Nat). Cons (*hd) a) (*tl) y h
        }
    } }
```

The type says: on exit, `*v` equals the entry value with `w` appended. The `Nil` branch
writes `w` and proves it by `Refl` — after the write, both sides *compute* to `w`. The
`Cons` branch recurses on the tail and lifts the tail's evidence through `Cons` with
`id_congr`. Nothing else: no invariant annotations, no ghost state. The body computes the
new state and constructs the proof about it, interleaved.

To return a value *and* evidence, use `Σ` — the caller receives a pair and destructures
it with an ordinary `match`:

```
fn split_off [i] (v : &mut List Nat, i : Nat, hi : Le i (len *v))
    -> Σ (ret : List Nat) → Σ (h1 : Id (List Nat) (*v) (take i (old *v)))
         → Id (List Nat) ret (drop i (old *v))
```

```
let res = split_off(&mut *v, i, hi);
match res { Pair(tail, ev) => match ev { Pair(h1, h2) => … } }
```

After that call the caller *knows*, via `h1` and `h2`, exactly what `*v` and `tail` are
in terms of the entry value — and that knowledge is a value it can use, return, or feed
to a lemma. A callee's return type is the caller's **only** knowledge of what the call
did; anything you will need downstream must be in it. When designing a signature, work
backward from what the caller has to prove.

## 7. Branching on tests

Branching on a comparison must *teach the branch something*, or the proof cannot use the
test. Name the branch equation:

```
if e : leb x p {
  -- e : Id Bool (leb x p) True
  … leb_true_le x p e …        -- : Le x p
} else {
  -- e : Id Bool (leb x p) False
  … leb_false_gt x p e …       -- : Le (S p) x
}
```

Without the `e :`, the branch knows nothing it can cite — a bare `Refl` for that equation
is *rejected* inside the branch, correctly, because `leb x p` on unknown values does not
compute. `leb_true_le` and `leb_false_gt` convert the equation into the order facts
proofs actually want. The same binder works on `match` (`match e : x { … }`). Omit it
when the branch needs nothing; it costs nothing either way.

## 8. Recursion

Recursion must visibly decrease. The `[i]` after the function name declares *which
argument* decreases; at every recursive call, the value passed there must be a strict
structural piece of what the parameter held — typically because you matched it first:

```
fn split_off [i] (v : …, i : Nat, hi : …) -> …
  { match i {
      Z => …,
      S(i2) => … split_off(&mut *tl, i2, …) …    -- i2 < S(i2): accepted
  } }
```

A `&mut` parameter can be the decreasing one (`append_back [v]` recurses on `&mut *tl`,
the payload's tail). At the recursive call site you may **use your own return type** as
the description of what the recursive call did — that is what makes the `Cons` branch of
`append_back` work, and it is sound precisely because of the declared decrease.

For algorithms whose recursion is not structural (quicksort recurses on *both* halves),
thread **fuel**: a `Nat` that ticks down once per level, with a *sufficiency* hypothesis
making the fuel-exhausted-early case impossible:

```
fn quicksortA [fuel] (fuel : Nat, n : Nat, hfuel : Le n fuel, a : &mut (Array n Nat)) -> …
  { … match fuel {
        Z => botElim … ,                  -- unreachable: hfuel makes Le 1 Z, i.e. Bot
        S(f2) => … quicksortA(f2, k, …, &mut *l) …
  } … }
```

Callers at the top level pass `fuel = n` and `le_refl n`. This is ordinary total
correctness; the fuel is bookkeeping, not a caveat.

## 9. Arrays

`Array n T` is a fixed-length flat array; `n` is part of the type. Element access takes
the bound as evidence, and writes go through element borrows:

```
let x = (*a)[i | h];      -- h : Le (S i) n — the same bound shape as everywhere else
(*mid)[0] := x;           -- write at an index place
```

The distinctive operation is the **carve**: borrowing a *range* of an array, which
splits it into independently borrowable segments.

```
let hd = &mut (*t)[Z ; 1 ; m2];    -- [start ; length ; length-of-the-rest]
let tl = &mut (*t)[S Z ; m2];      -- the rest, starting after it
```

Both borrows are live at once — two disjoint `&mut` views of one array, the thing Rust's
`split_at_mut` needs `unsafe` for — and the disjointness is carried by the arithmetic in
the brackets. When the extents don't line up definitionally, supply the evidence: a `Le`
license for containment, and, when the array's length is a variable, the equation that
justifies the decomposition — which is usually something a callee just returned to you:

```
let lo  = &mut (*tl)[Z ; k3 ; S r2 | le_add k3 (S r2) | hdec];
let mid = &mut (*tl)[k3 ; 1 ; r2];
let hi  = &mut (*tl)[S k3 ; r2];
```

(`hdec : Id Nat m2 (add k3 (S r2))` — the length decomposes as the three extents.) A
trailing-open form `a[lo ; ..]` means "to the end of the segment".

Two rules of thumb make array programs go through, and both come from how the checker
sees lengths. **Access at your own zero**: you cannot hold evidence about two unrelated
variable indices into one array, so structure the program as carves whose segments you
then index at `0` — peel a head, work on the tail, swap only with a segment boundary.
**Carve at flex lengths**: matching an array's length (`match n { S(m2) => … }`) pins it,
and a pinned length blocks carving at a variable offset. So *select* (match, peel, scan)
in one function and *carve at a returned index* in its caller — the call boundary resets
the length to flexible. This is why the array quicksort is three functions (scan,
partition, sort) and not one.

## 10. Bigger proofs: two idioms

**A body can only speak about the current state.** `old *v` exists in *types*; the body
cannot write it, and once a call or a write replaces a value, nothing in the body can
name what it was. So when a proof must span a mutation, **stage it**: build a λ that
captures the about-to-be-lost value while it is live, and apply the λ afterward.

```
-- before the recursive call: *tl still denotes the entry tail
let mkC = (λ (t2 : Array m2 Nat).
           λ (hc : Π (q : Nat) → Id Nat (countA q m2 t2) (countA q m2 (*tl))). …);
let res = splitA(f2, m2, hfuel, p, &mut *tl);     -- *tl is now the sorted tail
… mkC (*tl) hcnt2 …                               -- but mkC remembers the entry
```

Every large verified function in the suite carries one to four of these builders; they do
no mathematical work, only naming. (The same dodge covers proofs consumed by calls:
capture what you need from a proof *before* the call that moves it.)

**Shape the ensures as a decomposition.** Return the equation that describes how the
result decomposes (`Id Nat n (add k (S jj))` from a partition), because the caller's next
act is a carve at exactly that decomposition, and a decomposition-shaped ensures
transports onto the carved pieces for free. If gluing your callee's evidence onto your
own state starts requiring transport lemmas, the signature is shaped wrong — restate it
the way the caller will consume it.

For a worked example of everything at once, read `quicksortA` in
`Dllbc/Tests/S25ArrSort.lean` — sixty lines that use every chapter of this document, with
comments explaining each move. It is the program this language was built to make
writable; when you can read it, you are done here.

## 11. Running your code

DLLBC is embedded in Lean. A declaration is a Lean definition using the `decl{ … }`
macro, and checking is a Lean test:

```lean
def splitA : Decl := decl{ fn splitA [fuel] (…) -> … { … } }

example : checkFnOk splitA = true := by native_decide
example : checkFnOk partitionA [partitionA, splitA] = true := by native_decide
```

The optional list is the *table* of declarations the function may call (include the
function itself if it recurses through the table). `checkFnOk` runs the checker; the
`example` makes your build fail if the program stops checking. Build with
`lake build Dllbc.Tests.<YourFile>` — module builds run the checker natively and take
seconds; a verified quicksort checks in milliseconds.

Checked programs also **run**. The executing machine runs the same declarations on
concrete inputs:

```lean
def runQsA (l : List Nat) : Option (List Nat) :=
  match Dllbc.Tests.S9Diff.runExec arrTbl (qsCallerA l) with
  | .ok env => (env.lookup "y").bind arrOfV
  | .error _ => none

-- runQsA [3,1,4,1,5,9,2] = some [1,1,2,3,4,5,9]
```

(`qsCallerA` is a small caller term binding an array and invoking the sort; copy the
pattern from `S25ArrSort.lean`.) Checking and execution are two modes of one machine, and
the suite continuously tests that they agree — what the checker accepts, the machine
runs, and the postconditions you proved are true of what it computes. That agreement is
the point of the whole language; you get to rely on it.

**Where to go next**: the test suites are the extended examples — `S23Direct.lean` for
List programs (every function in chapters 6–8 lives there), `S24Arrays.lean` for the
carve, `S25ArrSort.lean` for the full array quicksort; and `StdLemmas.lean` for every
lemma cited anywhere. All of them are written to be read.
