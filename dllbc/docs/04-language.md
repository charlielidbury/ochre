# Programming in DLLBC

This is a working programmer's introduction to DLLBC. It is linear: read it top to
bottom, and nothing is used before it is introduced. Each chapter introduces one thing,
says precisely what it is, and shows it in real code — every example is either verbatim
from the test suite or a fragment of something that is, and the notation in this book IS
the implementation's surface syntax. It is not a specification and contains no theory;
the design documents (`suspensions.md`, `functions-are-comptime.md`, `dllbc-arrows.md`)
exist for that.

**What you need to already know.** DLLBC assumes fluency in two things it does not
teach. From **Rust**: ownership and moves, `&mut` borrows, pattern `match`, and the
general experience of a borrow checker rejecting your program (look up: the Rust book,
chapters 4 and 6). From **Lean (or any dependent type theory)**: propositions as types,
`Π` and `Σ` types, inductive datatypes and their recursors, and proof terms as
first-class values (look up: "Theorem Proving in Lean 4", chapters 2, 4, 7). If both of
those lists read as familiar, you have everything this document requires.

**What DLLBC is.** One language in which programs, types, and proofs are the same kind
of thing. You write an imperative function that mutates through borrows, Rust-style; its
return type is a proposition about what it did; the body constructs the proof as an
ordinary value and returns it. There is no separate annotation language, no verification
condition generator, and no model of your program in some other system — the checker
reads the function you wrote.

---

## 1. The core: λ, Π, and the mode law

Strip away every convenience and DLLBC is a small λ-calculus plus one law about names.

The basis is small and fixed. Types: `Unit`, `Bool`, `Nat`, `List T`, `Array n T`, `Π`,
`Σ`, and the equality type `Id A a b`. Values are built from constructors: `unit`,
`True` / `False`, `Z` / `S(n)` (numerals like `3` are sugar), `Nil` / `Cons(h, t)`,
`Pair(a, b)` for `Σ`, and `Refl` for `Id`. There are no user-defined datatypes yet; in
practice the basis plus `Nat`-indexed arrays covers a lot.

**One function type, one function term.** `Π` is the function type and `λ` is the
function term, and there is nothing else. `Π (x : A) → R` is a function from `A` to
`R`, where `R` may mention `x`; each binder scopes over everything to its right. A
multi-argument function is exactly this nesting, and a comma list is notation for it —
`(v : &mut List Nat, i : Nat)` is `Π (v : &mut List Nat) → Π (i : Nat) → …`. Every λ
binder carries its type, written at the binder; the checker reads the type you wrote
and never guesses one.

**THE MODE LAW.** Everything in the language is either *comptime knowledge* — types,
proofs, snapshots, functions: erased before runtime, read without being consumed,
usable in types — or *runtime state* — data and borrows: present when the program runs,
moved or lent when used. And the law is:

> **Every binder spells its mode by its case, and every position that is not a binder
> spells it on its type.**

A **capital** binder binds comptime knowledge. A **lowercase** binder binds runtime
state. This is one rule with no exceptions, and it reaches every binder there is — a
`let`, a function parameter, a λ or Π binder, a match arm's binder. The style
convention layered on it: PascalCase for the capital names (`Hfuel`, `V0`, `SplitOff`),
snake_case for the runtime ones (`fuel`, `tl`, `hi`).

Two immediate consequences you will use constantly:

  * **`let X = e` is a comptime binding**: `e` is evaluated as knowledge, `X` is
    erased, never consumed, and citable as often as you like. **`let x = e` is a
    runtime binding**: `e` is evaluated as state, and using `x` moves or lends it.
    One sentence covers both machines: *a capital `let` reads its right-hand side as
    knowledge; a lowercase `let` reads it as state.*
  * A capital argument position (a capital parameter of a function you call) reads its
    argument as knowledge — nothing is consumed. A lowercase position moves or lends.

**Application is juxtaposition, and the comma form is the same term.** `Double i`,
`Add i (S j)`, `LeTrans a b c h1 h2` — and `F(a, b)` is sugar for exactly `F a b`; the
two spellings elaborate to the identical syntax tree, so use whichever reads better.
Parenthesise compound arguments: `SplitOff (&m *tl) i2 hi` or `SplitOff(&m *tl, i2, hi)`.

**Ascription states a type.** `(t : T)` checks `t` against `T` on the spot. `(3 : Nat)`
is the trivial case; the load-bearing one is ascribing a λ its Π — that pairing is what
the next chapter's `fn` unfolds to — and ascribing a proof its proposition, which is
this language's `Qed`.

## 2. Functions

A DLLBC program is a sequence of definitions and a thing to run:

```
fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : …) -> … { … };
fn Main() -> Nat { … };
…the thing to run…
```

**`fn` is notation, not a construct.** A definition is a capital `let` of a λ ascribed
its Π:

```
let Quicksort = (λ (fuel : Nat, v : &mut List Nat, Hfuel : …) { …body… }
                  : Π (fuel : Nat) → Π (v : &mut List Nat) → …);
```

That single fact explains everything about how functions behave:

  * **Function names are capital, because a function is comptime knowledge.** The
    checker knows it; the compiled program keeps only its code. `fn quicksort` is
    refused with the fix in the message.
  * **`let F = Main` is legal** — copying knowledge costs nothing — and so is passing
    a function to another function at a capital parameter: `Twice(Inc, 3)`.
  * **Definitions sit in order.** Each may call the ones above it and cannot mention
    the ones below; a `let` cannot see later `let`s, so there are no forward
    references and nothing to declare in advance.
  * **Calling never consumes.** The call reads the function binding as knowledge —
    that is what capital means — so a function can be called any number of times.

**The return type is optional, and leaving it off leaves off the ascription.** `fn Idf
(x : Nat) { x }` is `let Idf = λ (x : Nat) { x }` — the λ on its own, with no `: Π …`
wrapped around it. That ascription is what makes a function *opaque*: with one, the
body is checked once, at the definition, and every caller sees only the signature.
Without one the function is transparent — its body goes wherever it is called and is
checked there. So an unsealed function that is never called is never checked, and one
that is called in three places is checked three times, against what is true at each of
them. Write `-> R` when you want the definition to stand on its own and its callers to
be held to a signature; leave it off for a small helper you would rather have inlined.

A recursive definition still needs one. `[k]` says which argument shrinks, and what the
checker recurses on is built out of the return type, so there is nothing to build
without it: `fn Count [n] (n : Nat) { n }` is refused, with that as the message.

**The last `fn` in a block may drop its `;`.** A block can end with a definition instead
of an expression:

```
let v = 0;
fn Helper (x : Nat) -> Nat { x }
```

and such a block's value is `()`. `fn` is the only statement that may end a block this
way — `let x = e` still needs something after it.

Bodies are sequences of statements ending in an expression:

```
let x = e;        -- runtime bind        let X = e;   -- comptime bind
p := e;           -- assign through a place
F(a, b);          -- call, result discarded
result            -- the final expression is the return value
```

**What differs between functions is what their binders are.** A function whose binders
are all knowledge or plain data — `Len`, `Add`, `Count`, `Take`, `Leb`, the whole
standard vocabulary — is mathematical: no borrows, no mutation, usable *everywhere*,
including inside types. A function that binds a `&mut` is imperative: it may borrow,
mutate, and call others, and it can be *called* but never used in a type — a borrow is
not something a type can compute with. That is a fact about its signature, not a second
species of function.

**The λ law.** A λ is knowledge, so it must land somewhere that receives knowledge:

> a λ literal needs a comptime destination — a capital `let`, a capital parameter, a
> `Σ0` component or tail (chapter 7), or an ascription. (A fifth, the recursor arm, is
> written for you by `fn`.)

Constructing a λ anywhere runtime state is expected is refused, with that list in the
message. This is checkable law, not convention: the kernel cannot build a function
value out of runtime evaluation at all.

**What a λ can see.** A λ body may reference its own binders and the capital bindings
in scope — nothing more, nothing less. Citing a lowercase name inside a λ body is
refused; when you want a runtime value inside a λ, *name the snapshot first*:

```
let H0 = *hd;                       -- the payload, as knowledge, now
… λ (A : List Nat). Cons H0 A …     -- the λ captures H0
```

That two-line shape is the language's one mechanism for baking state into a function,
and chapter 7 shows it earning its keep in a real proof.

## 3. Ownership

Rust's rules, with one boundary drawn differently. Using a runtime value **moves** it;
a moved variable is dead and the checker rejects later uses. But *small* things copy
instead of moving: numbers, booleans, and — importantly — **proofs**. Data (lists,
arrays, anything with a list or an array inside it) always moves. So you can pass an
index or a `Le` proof twice without thinking, but passing a list consumes it.

**A pair copies when its parts do.** `Σ (x : A). B` is Copy exactly when each of its two positions is either Copy in its own right or *erased*, and a position is erased when the pair's type marks it comptime — a capital binder marks the first component, `Σ0` marks the tail — and what the marked position holds is a proof rather than data. So `Σ0 (n : Nat). Le n MAX`, the way you write a bounded machine integer, is Copy: a number beside a bound you never pay for, and you can pass it to two calls the way Rust passes a `usize`. `Σ (a : Nat). List Nat` is not, and neither is a slice `Σ (c : Nat). &mut (Array c T)` — a borrow is neither small nor erased, and copying one would hand out two owners of the same memory. Marking a `List` comptime does not buy you a copy either: the marker says the component is erased, and a list is still a list at run time. This is Rust's `#[derive(Copy)]`, reached by reading the type rather than by declaring a trait.

Capital bindings go one step further than copying: they are *never touched at all* — a
citation of `Hfuel` reads knowledge and leaves nothing behind to consume, which is why
quicksort can hand its sufficiency proof to both recursive calls and still cite it
afterwards:

```
fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suff) -> …
```

The working guidance: a proof you will use once can live at a lowercase name (the suite
does this constantly — `let h = AppendBack(…)`, used once in the next line); a proof
you will thread, reuse, or keep past a mutation belongs at a capital one.

## 4. Borrows and mutation

`&m e` mints a mutable borrow of a place; `*b` reads or writes through it; borrows end
automatically when something demands the borrowed value back. The *type* of a borrow is
spelled `&mut List Nat` — the operation and the type are different spellings, so a type
never reads as an action.

```
let b = &m v;
*b := Cons(1, Nil);      -- write through
let n = Len *b;          -- read through
```

Reborrowing a component works the way you expect: `&m *tl` reborrows the payload.
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

**A borrow can owe back something other than what it was lent.** `&mut List Nat` means
"give back a `List Nat`". The general form names the payload it received and states
what is owed:

```
fn ToNat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () }
```

`v` arrives holding a `Bool` and must hold a `Nat` at return — a strong update across a
call boundary, checked at the return. The owed type may mention the snapshot it binds
(`&mut (s : List Nat ~> Σ (l : List Nat). Id Nat (Len l) (Len s))`), which is how a
borrow carries a contract of its own, separate from the function's return type.

## 5. Types that compute

Types are expressions in the same language, so a type can mention values — including
the current payload of a borrow, written `*v`:

```
fn SetAt [i] (v : &mut List Nat, i : Nat, x : Nat, hi : Le (S i) (Len *v)) -> …
```

`Le a b` is the ≤ proposition on `Nat`, and it *computes*: `Le 1 (S j)` unfolds, by
running its definition, to a trivially-true type, while `Le (S i) Z` unfolds to `Bot`,
the empty type. `Len`, `Count`, `Take`, `Drop`, `Append`, `Add`, `Leb`, `Eqb`, `Sorted`
are all in the same standard vocabulary — ordinary computable functions, usable in
types and in code alike, and capital because functions are knowledge.

A parameter like `hi` is a **precondition**: callers must supply a proof value, and
there is no proof of a false `Le`, so `SetAt` simply cannot be called out of bounds.
Dead branches discharge with the empty type's eliminator: if some hypothesis has
computed to `Bot`, the branch returns `botElim T h` at any type `T` — "this cannot
happen, and here is why".

Equality is `Id A a b`, and its proof is `Refl` — accepted whenever the checker can
*compute* the two sides to the same value. Much more follows from that than you might
expect, because so much of the vocabulary computes.

## 6. Writing proofs

Proofs are pure values — λ-terms in the borrow-free fragment. You have `λ`, `Π`, `Σ`,
`×` (the non-dependent pair, which is how conjunction is written — `Sorted`'s `Cons`
case is `Bound H T × Sorted T`), application, and one workhorse: `elim`, structural
recursion with an explicit motive.
The standard library's `LeRefl` is, verbatim, the complete idiom:

```
-- Proves `N ≤ N`, for any `N`.
λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
  Z => unit,
  S (K) Ih => Ih }
```

Read: by induction on `N`, prove `Le N N`; at `Z` the goal computes to a trivial type
(`unit` inhabits it); at `S K` the induction hypothesis `Ih` is exactly the goal. Every
binder is capital because everything in sight is knowledge. The motive after `return`
is written by you, always — nothing is inferred. Nested `elim`s express nested
induction (see `LeTrans` in `StdLemmas.lean` for the canonical three-level example).

The equation toolkit is `Refl`, `IdSym`, `IdTrans`, and `IdCongr` (map a function
across an equation). Most proofs about this vocabulary are chains of those four plus
library lemmas, with computation silently closing the gaps.

**The standard library is `Dllbc/StdLemmas.lean`.** Before proving anything about `Le`,
`Count`, `Append`, `Sorted`, or their `Array` counterparts, look there — the lemma you
want likely exists, and every lemma's statement is written right next to its proof.
Library lemmas are cited in bodies by name, applied like any function.

One honest caveat, the single place where a proof's case follows its *use*: a proof you
plan to **match on** (destructing an equation's `Refl` so the checker learns from it)
must live at a lowercase name — matching is a runtime observation, and you cannot
observe the erased. Proofs you *cite* (pass to lemmas, thread through calls) follow the
ordinary guidance of chapter 3.

## 7. Postconditions

A return type may describe the function's *effect*. For a `&mut` parameter `v`, `*v` in
the return type means the payload **as the function returns it**; `old *v` is the one
exception — the payload as it was when the borrow was received. This is the heart of
the language.

**In a body there is no `old`.** A body can only speak about the state it is in. When a
proof must span a mutation, name the value first, with a comptime `let`:

```
let V0 = *v;            -- the payload as it is now — erased, never consumed
… mutate through v …
… a proof about V0 …    -- still means what it meant
```

A comptime binding never goes stale — mutation mints new values rather than rewriting
old ones — and the one ordering rule is the only trap: **take the snapshot before
taking a reborrow of the same place.**

A complete verified function, from the suite:

```
fn AppendBack [fuel] (fuel : Nat, v : &mut List Nat, w : List Nat, Hf : Le (Len *v) fuel)
    -> Id (List Nat) (*v) (Append (old *v) w)
    { match v {
        Nil => { *v := w; Refl },
        Cons(hd, tl) => match fuel {
          Z => botElim Unit Hf,
          S(f2) => {
            let y = Append (*tl) w;
            let h = AppendBack(f2, &m *tl, w, Hf);
            let H0 = *hd;
            IdCongr (List Nat) (List Nat) (λ (A : List Nat). Cons H0 A) (*tl) y h
          }
        }
    } }
```

The type says: on exit, `*v` equals the entry value with `w` appended. The `Nil` branch
writes and proves it by `Refl` — after the write, both sides compute to `w`. The `Cons`
branch recurses on the tail and lifts the tail's evidence through `Cons` — and note the
chapter-2 idiom doing real work: `H0` names the head's payload so the congruence λ can
capture it. Nothing else: no invariant annotations, no ghost state.

To return a value *and* evidence, use `Σ` — the caller destructures with a `match`, and
**a match arm's binder must spell the component's mode**: capital over a proof
component, lowercase over data, refused one character off in either direction.

**A `match` scrutinee is an expression.** `match SplitOff(&m *tl, i2, hi) { … }` matches the call's result where it stands; there is no need to name an intermediate you will not mention again. The one thing to know is what happens when the scrutinee is a plain variable, which is *nothing*: that case is untouched, and it has to be, because matching a variable holding a **borrow** reborrows — the arm binders come back as borrows of the fields — while an expression is a value that gets bound to a local first. So `match v { … }` on a `&mut` still means what §4 says it means, and `match f(…) { … }` is the new spelling.

**Destructuring is a `let`.** A pattern on the left of a `let` is the one-branch match written as a statement: the *rest of the block* becomes the arm, so what used to nest reads top to bottom.

```
let Pair(rr, q) = SplitOff(&m *tl, i2, hi);
let Pair(H1, h2) = q;
…                                            -- still at the same indentation
```

Both spellings produce the same program — this is shorthand, not a second mechanism — and the same binder rules apply, mode-spelling included. Nothing here asks whether the constructor you wrote is the type's only one: `let Cons(h, t) = l;` is accepted by the grammar and then refused by the ordinary exhaustiveness check, with `non-exhaustive — no branch for constructor 'Nil' of the scrutinee's type`. A destructuring `let` on a borrow reborrows exactly as the match it stands for does, so `let Pair(l, xs) = v;` on a `v : &mut Σ (l : Nat). …` hands you borrows of both fields and you write through them.

**A pattern argument may itself be a pattern.** `Cons(Pair(k, v), tl) => …` reads a field of a field, in match arms and in the destructuring `let` alike, and a nullary constructor may be written bare: `Cons(Z, tl) => …`.

```
let Pair(rr, Pair(H1, h2)) = SplitOff(&m *tl, i2, hi);
```

A nested pattern is the fresh binder and the inner match it stands for, and that is worth knowing rather than taking on faith, because two consequences follow from it. **Exhaustiveness is checked at every level.** `Cons(Z, tl) => …` is an inner match on a `Nat` with only the `Z` branch, so it is refused — `no branch for constructor 'S'` — and it is not made exhaustive by any other arm. DLLBC matches are one arm per constructor of the *scrutinee's* type; there is no cross-arm grouping and no pattern matrix, so a discrimination deeper than the head is a decision you make explicitly and the checker holds you to. **And borrow mode goes all the way down**: every level of the pattern is a match on the level above, so `let Pair(n, Pair(l, xs)) = v;` on a `&mut` hands you borrows of all three fields and every write lands.

The branch-equation form does *not* take nested patterns. `match h : x { … }` binds one `h` whose type is the equation between the scrutinee and that arm's constructor, and there is no such equation at a nested position — write the inner match yourself, with its own `match h2 : …` where you want one.

**`Σ0` — the subset type.** A Σ chain's components spell their modes on their binders,
but the final position — the tail — has no binder, so it spells its mode on the
*former*: `Σ0 (x : A). P` is the pair whose second projection is comptime — DLLBC's
subset type (Lean's `Subtype`, Coq's `sig`), with comptime as the erasure. Quicksort's
own ensures, from the suite:

```
Σ0 (Hs : Sorted (*v)). Π (N : Nat) → Id Nat (Count N (*v)) (Count N (old *v))
```

— a sortedness proof paired with a permutation proof, all of it erased knowledge riding
on a runtime result. This is where trailing proofs live; an ordinary `Σ` tail is
runtime-moded, and putting a proof there is refused with a message that names `Σ0` as
the fix.

The pair family is complete in three spellings, each saying exactly what it can:
`Σ (x : A). B` — dependent, the binder spells its component's mode; `Σ0 (x : A). P`
— the tail comptime, spelled on the former, since a tail has no binder; `A × B` — no
dependency at all, so no binder and nothing to spell (the library's own `Sorted`
writes its conjunction this way).

**A Σ binds with a dot, and a Π with an arrow.** The punctuation tells you which former you are reading before the head letter does, and it is not an arbitrary split: a Π *is* a function, so `Π (x : A) → B` uses the arrow for the thing itself, while a Σ builds a *pair* and would only be borrowing the function arrow to mean something else. The dot is the surface's own convention rather than a new one — `λ (x : A). t` has bound with a dot from the start, and a Σ binder is the same kind of binder doing the same job. The two other arrows in a signature are unrelated to both: `~>` separates a borrow's snapshot from what it owes back, and `->` gives a `fn` its return type.

**A callee's return type is the caller's only knowledge of what the call did.** A
function is written once, checked once against its signature, and from then on every
caller sees the signature and nothing else. **What you keep is what you ascribe** — a
fact not written into the return type is gone. It is why signatures are worth designing
(work backward from what the caller has to prove) and why callers stay cheap to check
no matter how large the callee is.

## 8. Branching on tests

Branching on a comparison must *teach the branch something*, or the proof cannot use
the test. Name the branch equation:

```
if e : Leb x p {
  -- e : Id Bool (Leb x p) True
  … LebTrueLe x p e …        -- : Le x p
} else {
  -- e : Id Bool (Leb x p) False
  … LebFalseGt x p e …       -- : Le (S p) x
}
```

Without the `e :`, the branch knows nothing it can cite — a bare `Refl` for that
equation is *rejected* inside the branch, correctly, because `Leb x p` on unknown
values does not compute. `LebTrueLe` and `LebFalseGt` convert the equation into the
order facts proofs actually want. The same binder works on `match`
(`match e : x { … }`). Omit it when the branch needs nothing.

## 9. Recursion

Recursion is structural, and the `[i]` after the function name says **which argument
you are recursing on**. Match it, and the recursive call is available in each branch at
the piece the match bound — for a `Nat` the predecessor, for a list the tail.

At the recursive call site you may **use your own return type** as the description of
what the recursive call did — that is what makes `AppendBack`'s `Cons` branch work.
There is nothing to justify separately: the recursive call *is* the induction
hypothesis for the piece you matched.

**What `[i]` unfolds to.** Chapter 2 said a definition is a `let` of a λ — and a `let`
is not in scope in its own right-hand side, so a recursive `fn` cannot be that. It is
the other thing your prerequisites already contain: the datatype's **recursor**. The
motive is your ascribed Π with the scrutinee's binder peeled off; the arms are your
whole body with the `match` on the scrutinee resolved per constructor; and every
self-call becomes the induction-hypothesis binder `Ih` — knowledge, like every function
value. A self-call at anything but the matched piece, or in the base branch, is refused
rather than repaired.

**Recursion is eager.** Running a recursion on an actual number runs it to the end —
the zero case included — and what comes out is always a finished value. Unfinished
recursion exists only inside the checker, where an unknown symbolic number makes it
stand for "the recursive result", which is exactly what proofs need.

Recurse on a **counter**, not on a borrow: a `&mut` parameter's payload shrinks as you
walk it, but a borrow is not something you can do induction over. For everything that
is not structural — quicksort recurses on *both* halves, `AppendBack` walks a borrow —
thread **fuel**: a `Nat` that ticks down once per level, with a *sufficiency*
hypothesis making the fuel-exhausted case impossible:

```
fn Quicksort [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : %suff) -> %qret
  { … match fuel {
        Z => botElim … ,                  -- unreachable: Hfuel makes it Bot
        S(f2) => … Quicksort(f2, &m *lo, …) …
  } … }
```

`Hfuel` is capital for chapter 3's reason: both recursive calls receive it and the
proof afterwards still cites it. Callers at the top level pass `fuel = Len *v` and a
reflexivity proof. This is ordinary total correctness; the fuel is bookkeeping, not a
caveat.

## 10. Arrays

`Array n T` is a fixed-length flat array; `n` is part of the type. Element access takes
the bound as evidence, and writes go through element borrows:

```
let x = (*a)[i | h];      -- h : Le (S i) n — the same bound shape as everywhere else
(*mid)[0] := x;           -- write at an index place
```

The distinctive operation is the **carve**: borrowing a *range* of an array, which
splits it into independently borrowable segments.

```
let hd = &m (*t)[Z ; 1 ; m2];      -- [start ; length ; length-of-the-rest]
let tl = &m (*t)[S Z ; m2];        -- the rest, starting after it
```

Both borrows are live at once — two disjoint `&mut` views of one array, the thing
Rust's `split_at_mut` needs `unsafe` for — and the disjointness is carried by the
arithmetic in the brackets. When the extents don't line up definitionally, supply the
evidence: a `Le` license for containment, and, when the array's length is a variable,
the equation that justifies the decomposition — usually something a callee just
returned to you. A trailing-open form `a[lo ; ..]` means "to the end of the segment".

Two rules of thumb make array programs go through. **Access at your own zero**: you
cannot hold evidence about two unrelated variable indices into one array, so structure
the program as carves whose segments you then index at `0`. **Carve at flex lengths**:
matching an array's length pins it, and a pinned length blocks carving at a variable
offset — so *select* in one function and *carve at a returned index* in its caller.
This is why the array quicksort is three functions (scan, partition, sort) and not one.

## 11. Bigger proofs: two idioms

**Name what you are about to lose.** A body speaks about the state it is in, so a proof
spanning a mutation needs the earlier value to still have a name — chapter 7's `V0`
pattern, and its λ-capture variant from chapter 2 (`let H0 = *hd; … λ A. Cons H0 A`).
Take the snapshot before the reborrow; beyond that there is nothing to arrange — a
capital binding is erased, never consumed, and cannot go stale.

**Shape the ensures as a decomposition.** Return the equation that describes how the
result decomposes (`Id Nat n (Add k (S jj))` from a partition), because the caller's
next act is a carve at exactly that decomposition, and a decomposition-shaped ensures
transports onto the carved pieces for free. If gluing your callee's evidence onto your
own state starts requiring transport lemmas, the signature is shaped wrong — restate it
the way the caller will consume it.

For a worked example of everything at once, read `QuicksortA` in
`Dllbc/Tests/ArraySort.lean` — the program this language was built to make writable;
when you can read it, you are done here.

## 12. Running your code

DLLBC is embedded in Lean, and the whole surface is **one macro**: `prog{ … }`
elaborates the notation of this book — all of it, exactly as written — into the
calculus's one syntax tree. A program is definitions plus the thing to run, and
checking it is a Lean test:

```lean
def entrypoint : Term := prog{
  fn SplitA [fuel] (…) -> … { … };
  fn PartitionA [fuel] (…) -> … { … };
  fn QuicksortA [fuel] (…) -> … { … };
  …the thing to run…
}

example : progOk entrypoint = true := by native_decide
```

There is no table of declarations and no registration step: the `fn` statements
desugar to the `let`-chain of chapter 2, in order, and the checker walks the resulting
single term against nothing at all. Pure terms — lemmas, types, standalone λs — are the
same macro with no `fn` in it; the entire standard library is written that way.

`progRejects t "needle"` is the assertion for a program you expect to be *refused*, and
it checks the message says why — use it, because a test that only knows a program
failed will happily keep passing when it starts failing for a different reason.
`native_decide` makes your build fail if the program stops checking; module builds run
the checker natively and take seconds, and a verified quicksort checks in milliseconds.

Checked programs also **run**: `runProgram` evaluates the same term concretely,
`progRuns` asserts completion, `progRunsTo` pins the final environment. Checking and
execution are two modes of one machine, and the suite continuously tests that they
agree — what the checker accepts, the machine runs, and the postconditions you proved
are true of what it computes. That agreement is the point of the whole language; you
get to rely on it. (Today's interpreter evaluates comptime terms instead of erasing
them, which costs time and changes nothing observable; compiled output drops them.)

**Recursive comptime functions evaluate EAGERLY, and the cost model follows from that.** When a recursor's arm names its recursive result, the normalizer runs the recursive call and forces the answer to a value — constructors all the way down, closures left closed — before the arm is entered. So you may mention the result as many times as you like: the textbook `mod`, whose step tests `S (Mod a' b) = b` and then also returns `S (Mod a' b)`, is linear, and the accumulator rewrite that used to be REQUIRED (carry the would-be-duplicated value as an argument so the call occurs once) is now merely one way to write it. Until 2026-08-17 that rewrite was mandatory: the normalizer substituted without sharing, re-derived the whole recursion beneath every second occurrence, and the textbook spelling was silently exponential — a build that never finished rather than an error, ~86 s at dividend 20 against divisor 32 and days at 32. What eager costs instead is that a named recursive result is computed in full even down a branch that discards it, so an early-exit-shaped recursion pays for its whole depth; what it does not cost is the arm that never names the result at all, which makes no call, because a `Nat` case split in this calculus can only be spelled as a recursion and charging it for one would be inventing work the program never asked for.

One Lean-side convenience appears throughout the suite: `%e` inside `prog{ … }` splices
a Lean expression of type `Term` — a shared signature, a lemma, a program fragment —
into the notation. It is how the suite reuses one return type across a definition and
its callers without writing it twice.

**Where to go next**: the test suites are the extended examples — `Tests/Direct.lean`
for List programs (every function in chapters 7–9 lives there), `Tests/Arrays.lean` for
the carve, `Tests/ArraySort.lean` for the full array quicksort, `Tests/Functions.lean`
for chapter 2's ground truth, `Tests/KernelFloor.lean` for the mode law's one-character
test pairs; and `StdLemmas.lean` for every lemma cited anywhere. All of them are
written to be read.
