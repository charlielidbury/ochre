# The Ochr book

How to write Ochr programs and proofs. This is everything you need to start. You never need the paper, `RULES.md`, or the checker's Lean source: they explain *why* Ochr works, and this book explains how to *use* it. When this book isn't enough, read the checked examples in `ochr/core/lean/Ochr/Examples/` (`00Std.lean` … `18DependentFields.lean`). Every program there is accepted, and every `reject def` there is refused, with a comment saying why.

## 1. The idea in one paragraph

Ochr is Rust-style in-place programming (owned data, `&` mutable borrows, moves) inside a Lean-style dependent type theory. Types are programs: a statement about an in-place function is written by *running the function inside the type*, for example "after `Sort` runs on a copy of `*s`, the copy is sorted". There is no separate specification language and no pure model you must write. Checking is evaluation. The checker runs each definition on symbolic inputs: an unknown argument is an abstract value `σ0`, and a computation that needs to know it (a `match`) is *stuck*, shown as `⌈…⌉`. Two types are equal when they evaluate to the same normal form. A proof makes progress by matching on unknowns, which splits into cases and lets stuck computations continue.

## 2. Files, blocks, and checking

An Ochr program lives in `ochr` blocks inside an ordinary Lean file:

```
import Ochr.Test
import Ochr.Examples.«00Std»         -- the Std library (Word, Bool, List, Box, AddM, …)
import Ochr.Examples.«16Arrays»      -- only if you need arrays
open Ochr.Test

ochr MyBlock uses Std {
  def Inc (x : &Word) : Unit := *x := Succ(*x)
  -- more declarations …
}
```

- A block sees the accepted declarations of the blocks it `uses`, transitively, plus the always-present `Prelude` (`Pair`, `False`, `True`, `And`). For arrays, write `uses Index, Arrays, ArrayLemmas`.
- Every block is checked when the file is elaborated, in the editor as you type or in `lake build` / `lake env lean File.lean`. A rejected `def` is an error underlining the responsible piece of source, with the reason. Nothing else needs running.
- Declarations are checked top to bottom. A helper must come before its first use, and there is no mutual recursion between top-level declarations.
- A rejected declaration doesn't exist for later ones: everything that mentions it fails with `unknown constant X`. Fix the first error first.
- `reject def …` declares a negative test. It is silent while it is rejected, and an error if it is accepted.
- **Holes.** Write `?` (or `sorry`) anywhere a term is expected. The rest of the definition is checked around it, and the build warns at the hole with the goal:
  ```
  warning: hole
  n : Word ↦ σ0
  ⊢ Eq(Word, ⌈Len(Word, σ0)⌉, Zero)
  ```
  This is how you see a goal. A finished program has no holes.
- **Hover** over any term in the editor to see its value and type on each case-split path, what a borrow points to, or a proof's goal.

In a benchmark package, use the commands its `ASSIGNMENT.md` names (`lake -q build`, `lake -q exe check`, `./grade.sh`).

## 3. Syntax

```
def F (x : A) (y : &B) : C := body            -- function (parameters always named and typed)
def G (n : Word) : Word by n := body           -- recursive, decreasing on n (§6)
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)   -- a proposition
copy inductive Word := Zero | Succ(pred : Word)                       -- a copy type (§5)
reject def Bad (…) : T := …                    -- negative test: must be rejected
```

| Form | Meaning |
|---|---|
| `f(a, b)` | call. Always saturated; **no space** before `(` |
| `C(a, b)`, `C` | constructor; the type's parameters are inferred (`Cons(x, Nil)`) |
| `match p { C1(x, y) => t, C2 => u, }` | case analysis on a **place** `p`. Arms are separated by commas; a trailing comma is allowed; `_` ignores a field; `S n =>` is the same as `S(n) =>` |
| `match h {}` | no arms: `h`'s type is empty (`False`, or an equation between different constructors) |
| `let x = t; u`, `let x : T = t; u` | binding; annotate when the type can't be inferred (proofs, matches) |
| `t; u` | sequence |
| `( … )` | grouping; multi-line bodies go in parentheses |
| `&p`, `*p`, `p := t` | borrow, dereference, assignment |
| `&*x` | reborrow: not a separate operator, just `&` applied to the place `*x`. It borrows what `x` points to, and `x` stays usable afterwards |
| `clone(p)` | explicit copy. Built in, so the copy is *definitionally* equal to the original (`Id(Nat, clone(x), x)` holds by `refl`, even when `x` is unknown). A user-defined recursive `Clone` would get stuck on an unknown `x`, and that equation would need an inductive proof, invoked explicitly |
| `λ(x : A) (y : B) : C => t` | closure |
| `fix f (x : A) : C by x := t` | local recursive function; put it in parentheses inside a `let` |
| `Π(x : A) (y : B). C`, `A → B` | function types |
| `(a, b)`, `A × B`, `let (a, b) = p; u` | pairs (`Pair`, constructor `Mk(fst, snd)`) |
| `p.1`, `p.2` | field projection, counted from 1. Only works on a value whose constructor is known; otherwise `match` |
| `Eq(A, a, b)`, `refl` | equality, and its proof |
| `Id(A, t, u)` | the programs `t` and `u` have the same result and the same effect (§7) |
| `⊤`, `False`, `P ∧ Q`, `⟨h, k⟩`, `let ⟨h, k⟩ = p; u` | true, false, conjunction, its proof, taking it apart |
| `rewrite h in t`, `rewrite ← h in t`, `split F in t` | proof steps (§8) |
| `?`, `sorry` | hole (§2) |
| `Type`, `Type₁`, `Prop` | universes: `Type : Type₁`, `Prop : Type₁` |
| `-- …`, `/- … -/` | comments |

Layout convention: one match arm per line with a trailing comma, and a multi-statement arm in `( … ),`.

Reserved names, which you can't declare: `Nat`, `Unit`, `Z`, `S`, `refl`, `Id`, `Eq`, `cong`, `J`, `clone`, `trans`, `symm`.

## 4. Data

- **Built in:** `Unit` (value `()`), and `Nat` (`Z`, `S(n)`, numerals `0`, `1`, …). `Nat` is *not* a copy type, so reading one moves it. It is the type for in-place unary arithmetic examples.
- **Std** (`uses Std`):
  - `copy inductive Word := Zero | Succ(pred : Word)` is the number type for keys, values, indices and lengths. It is a copy type, unary in the logic and a machine word at runtime. Numerals are `Nat`, so write `Succ(Zero)`, or `W(7)` from the arrays library's `Index`.
  - `Bool := false | true`, `List(A) := Nil | Cons(h, t)`, `Box(A) := MkBox(x)`.
  - `AddM(&x, y)` and `Add(x, y)` on `Nat`.
- **Your own types:** `inductive Opt (A : Type) := None | Some(v : A)`. Fields are data: other inductives, the type itself, numbers, function types reached through a type parameter (`Box(Π(n : Word). Word)`), and borrows nowhere. Parameters are types in `Type`.
- **Dependent fields:** a field's type may mention earlier fields: `inductive Vec (E : Type) := MkVec(n : Word, items : Array(E, n))`. You may break the dependency temporarily, writing the fields one at a time in either order: `match *v { MkVec(n, items) => (n := W(2); items := two) }`. It must hold again wherever the value is used whole (read, passed, returned, borrow ended), or you get a `[Repack]` error naming the field and both types. A proof field (`h : Sorted(xs)`) is cleared when the data it mentions changes, and must be re-assigned before the value is used whole. Examples: `18DependentFields.lean`.
- **No `if`:** match on a `Bool`, or on a decision type such as `Dec(Le(a, b), Lt(b, a))` (`Yes(h)` / `No(k)`), which also gives you the proof.

## 5. Ownership: moves, copies, borrows

These are the rules you'll hit most:

1. **Reading a place moves it** unless its type is a copy type. Copy types: `Unit`, `Word`, `Bool`, propositions, types, `copy` inductives, and non-recursive inductives whose fields are copies (such as `Opt(Word)`). Reading a moved place is an error: `[Read] x was moved out`. Use `clone(p)` for an explicit copy.
2. **A borrow variable moves when you pass it.** `Inc(x); Inc(x)` fails at the second `x`. Pass a reborrow to keep `x`: `Inc(&*x); Inc(x)`.
3. **`x : &T` is a mutable borrow.** The function may read and write `*x`. There are no shared borrows: a read-only function still takes `&`, and "it doesn't change anything" is a statement you prove when it matters.
4. **Borrows end automatically** when the owner, or anything containing it, is used again. Using a borrow after that is an error. This is Rust's borrow checker, enforced on symbolic runs.
5. **Moving out through a borrow is allowed if you refill it** before the borrow ends:
   ```
   def Swap (A : Type) (a : &A) (b : &A) : Unit := (let t = *a; *a := *b; *b := t)
   ```
6. **Matching on a place gives sub-places, not copies.** In `match *l { Cons(h, t) => … }`, `t` *is* the tail inside `*l`, so `&t` borrows into the list:
   ```
   def Len (A : Type) (l : &List(A)) : Word by l := (
     match *l {
       Nil => Zero,
       Cons(_, t) => Succ(Len(A, &t)),
     }
   )
   ```
7. **Returning a borrow:** a function whose result is `&T` must take a borrow parameter, and the result points into it.
   ```
   def Last (l : &List(Word)) : &List(Word) by l := (
     match *l {
       Nil => l,
       Cons(_, t) => Last(&t),
     }
   )
   ```
   You can never return a borrow of a local.
8. **Moving a cursor down** works as in Rust: `match *x { Cons(_, t) => (x := &t; *x := Nil), … }`.
9. **Borrowable types** are anything in `Type`: data, functions, and type parameters `A : Type` (`Swap` above is generic). Proofs, propositions and types can't be borrowed.
10. **Closures capture values, never borrows**, and may run again. So a closure body may not move a captured value out; `clone` it.
11. **Types and proofs never move anything.** Reads inside them copy, and whatever they run happens on a private copy of the state, so statements can freely mention `*x`.

## 6. Recursion

- **Structural only.** A recursive function declares `by x`. Every recursive call passes, in that position, a strict sub-part of `x`'s value on entry: a field reached by `match` (`k'` in `Succ(k')`), or a borrow of one (`&t`). A function without `by` can't call itself.
- **No recursion on a measure** (such as a length that shrinks arbitrarily). Add a *fuel* parameter that drops by one per call and starts large enough, then prove the fuel suffices.
- **Local recursion:** `let go = (fix go (k : Word) : Word by k := match k { Zero => Zero, Succ(k') => go(k') }); go(n)`.

## 7. Statements: types that run your code

A proposition is a type of sort `Prop`. You write one as a program that computes a type:

```
def Le (a : Word) (b : Word) : Prop by a := match a { Zero => ⊤, Succ(a') => match b { Zero => False, Succ(b') => Le(a', b') } }
```

**`Eq` computes**:
- `Eq(A, a, a)` is `⊤`;
- equal constructors give a conjunction of field equations;
- different constructors give `False`;
- a `Unit` value is always `()`.

So `refl` proves any equation whose two sides evaluate to the same normal form.

**The copy idiom.** To state a property of an in-place function, run it on a local copy inside the statement:

```
def Push (A : Type) (l : &List(A)) (x : A) : Unit := *l := Cons(x, *l)

def PushLen (A : Type) (l : &List(A)) (x : A) :
    Eq(Word, (let c = *l; Push(A, &c, x); Len(A, &c)), Succ(Len(A, l))) := refl
```

`c` is a copy of the current `*l` (inside a statement, reading data copies it; the same `let` in runtime code would move), `Push` mutates the copy, and the right-hand side still sees the original `*l`. (This one is proved by `refl` because both sides compute to the same thing.) You can also mutate `*l` itself inside a side. Each side of `Eq` runs on its own private copy of the whole state, with the ordinary rules, so a write is seen by the rest of that side and by nothing else: `Eq(Word, (Push(A, &*l, x); Len(A, l)), Succ(Len(A, l)))` states the same thing. Reborrow (`&*l`) for every use of `l` but the side's last, since passing `l` itself hands over the borrow.

**`Id(A, t, u)`** says that the programs `t` and `u`, each run on its own copy of the current state, return equal results of type `A` *and* leave equal contents in every place they write or borrow:

```
def Inc (x : &Word) : Unit := *x := Succ(*x)
def IncTwice (x : &Word) : Id(Unit, (Inc(&*x); Inc(x)), *x := Succ(Succ(*x))) := refl
def AddMZero (x : &Nat) : Id(Unit, AddM(x, 0), ()) by x := (   -- Std
  match *x {
    Z => refl,
    S p => AddMZero(&p),
  }
)
```

`Id` computes to a conjunction of `Eq`s, one for the result and one per affected place, and is proved like one.

**`Eq` versus `Id`.** They compare different things:

- **`Eq(A, a, b)` compares two values.** It is propositional equality, Lean's `a = b`. Each side is evaluated on its own private copy of the state, and only the resulting values are compared. If a side has effects, they happen inside that copy and are thrown away with it. `Eq` is the primitive: it computes by structure (equal constructors give the equations between their fields, different constructors give `False`), and `refl` proves it when both sides normalise to the same value.
- **`Id(A, t, u)` compares two programs: their results and their effects.** Each side runs on its own copy of the state. Then `Id` compares the results *and* the final contents of every place either side may affect (its *footprint*: places assigned or borrowed, and what borrow parameters point to). It isn't a separate primitive. It computes to the conjunction
  `Eq(A, result of t, result of u) ∧ Eq(T₁, final w₁ after t, final w₁ after u) ∧ …`, one conjunct per footprint place.
- **So `Id` is `Eq` plus the effects.** For programs that change nothing, `Id(A, t, u)` is just `Eq(A, t, u)`. For a `Unit`-returning program (`Id(Unit, AddM(x, 0), ())`), the result conjunct is trivially `⊤`, and the statement is entirely about the effect.
- **Rule of thumb:** use `Eq` to say what something *computes*, and `Id` to say what it *does*. In Rust terms, `Eq` compares return values, and `Id` compares return values and the final state of every `&mut` the code touched. In Aeneas terms, `Id` compares a function's forward result *and* its backward functions.

## 8. Proofs

A proof is a program whose type is the statement. It never runs at runtime.

- **`refl`** proves goals whose sides evaluate to the same thing. A goal that reads `⊤` is `refl` too.
- **Case split.** `match x { Zero => …, Succ(x') => … }` refines `x` to each constructor, in the goal and in every hypothesis, so stuck computations continue. `match` needs a place. To split on a call's result, bind it first: `let d = LeDec(a, b); match d { Yes(h) => …, No(k) => … }`. Matching a place whose content is a stuck call generalises that call and splits on its result.
- **Induction is recursion.** A lemma declared `by x` calls itself on a sub-part of `x`, and that call's type is the induction hypothesis. For a borrowed structure, call the lemma on a borrow of the field (`AddMZero(&p)` above): the result covers the whole.
- **Lemmas are functions.** Call them to get facts: `LeTrans(a, b, c, h1, h2)`. To use a lemma about in-place code inside another proof, call it on the same copy: `(let c = *s; F(&c); Lemma(n, &c))`.
- **Contradiction.** `match h {}` when `h`'s type is empty. A hypothesis `Eq(Word, Zero, Succ(n))` *is* `False` after computation, so `match h {}` closes it.
- **Conjunction.** `⟨p, q⟩` builds one; `let ⟨p, q⟩ = h; …` takes it apart.
- **Intermediate facts.** `let h : P = (t); …` proves `P` once and names it, like Lean's `have`.

```
def CountDown (k : Word) : Word by k := match k { Zero => Zero, Succ(k') => CountDown(k') }

def CountDownZero (k : Word) : Eq(Word, CountDown(k), Zero) by k := (
  match k {
    Zero => refl,
    Succ(k') => CountDownZero(k'),
  }
)
```

### Tactic mode

There is none. A proof is always a term, and there is no `by { … }` block: `by` after a signature names the decreasing argument (§6). Instead, a few terms work like tactics. Each reads the goal it is checked against and hands a changed goal to its body, so you write them outermost first, in the order you would run the tactics. The goal comes from the signature, from the parameter type when the proof is a call's argument, or from an annotation `let h : G = (…); …`.

- **`rewrite h in t`**, for `h : Eq(A, a, b)`, proves the goal `G` from `t : G'`, where `G'` is `G` with `b` replaced by `a`. `rewrite ← h in t` replaces `a` by `b`. Rewrites chain: `rewrite h1 in rewrite ← h2 in t`. Occurrences inside a stuck `match` aren't found, so state helper lemmas about *calls*.
- **`split F in t`** finds the first stuck call of `F` in the goal, splits on its result, and checks `t` in every case. `split F { C1 => t1, C2(x) => t2 }` gives one proof per case.
- **`?`** stands for the rest of the proof. The warning shows the goal at that point and the values in scope, as Lean's goal view does after a tactic.
- **Reading a failed proof.** `the body of P has type A, but the goal is B` gives both normal forms. A goal stuck on `⌈F(σ3, …)⌉` is waiting for a case split on something `F` matches on.

```
def Pred (n : Word) (h : Eq(Word, n, Succ(Zero))) : Eq(Word, Succ(Zero), n) := rewrite h in refl
```

For a reader who knows Lean's tactics:

| Lean | Ochr |
|---|---|
| `rfl`, `unfold`, `dsimp only [f]` | `refl`. Types are compared after evaluation, so unfolding needs nothing written |
| `exact t`, `apply L` | the term `t`, or the call `L(…)` with every argument given |
| `intro h` | a parameter `(h : P)` of the `def` |
| `cases x`, `induction x` | `match x { … }`, plus a recursive call for the induction hypothesis (§6) |
| `obtain ⟨p, q⟩ := h` | `let ⟨p, q⟩ = h; …` |
| `constructor` | `⟨p, q⟩`, or a call to the constructor |
| `have h : P := t` | `let h : P = (t); …` |
| `rw [h]`, `rw [← h]` | `rewrite h in …`, `rewrite ← h in …` |
| `split` (on a `match` in the goal) | `split F in …` |
| `contradiction`, `nomatch h` | `match h {}` |
| `simp`, `omega`, `grind` | none: state the lemma and call it |
| `sorry` | `sorry` or `?` |

## 9. The arrays library

`import Ochr.Examples.«16Arrays»` and `uses Index, Arrays, ArrayLemmas`. Read `16Arrays.lean`: every declaration is short and checked.

- **`Index`** (numbers):
  - `Le(a, b)`, `Lt(a, b)`, propositions;
  - `LeDec(a, b) : Dec(Le(a, b), Lt(b, a))` and `LtDec(i, n) : Dec(Lt(i, n), Le(n, i))`, comparisons that return the proof;
  - `Leb`, `Eqb` (`Bool`), `WAdd`, `Sub`, `W(n)`;
  - facts: `LeRefl`, `LeStep`, `LeTrans`, `LeAddL`, `AddRS`, `AddZeroR`, `AddOneR`, `SubPos`, `SubOneLe`.
- **Model** (pure, used in statements):
  - `Slice(E, n)` is a view of `n` elements, and `Array(E, n)` is an owned array;
  - `Nth(E, n, s, i, h)` is element `i`, given `h : Lt(i, n)`;
  - `SetS` replaces an element;
  - `TakeS`, `DropS` and `JoinS` split and join;
  - `SnocS`, `PopS`.
- **Runtime operations**, the only way code touches an array:
  - `AsSlice(E, n, &a)`;
  - `Read(E, n, s, i, h)`, `Set(E, n, s, i, x, h)`;
  - `GetMut(n, s, i, h)`, a borrow of a `Word` element;
  - `WithSplit(E, R, n, k, s, h, f)` runs `f` on two disjoint borrows, the first `k` elements and the rest. It is Ochr's `split_at_mut`;
  - `ArrEmpty`, `ArrPush`, `ArrPop`;
  - `Swap(E, n, s, i, j, hi, hj)`, `Replicate`, `Fill`, `FillFrom`.
- **Lemmas:**
  - `NthSetSame`, `NthSetOther`;
  - `JoinTakeDrop`, `TakeJoin`, `DropJoin`;
  - `Count(q, n, s)` (occurrences of `q`), with `CountJoin`, `CountSet`, `CountSwap`;
  - `SwapIsSwapS`, `GetMutSet`.
- **Rule:** runtime code only *borrows* views. It never reads one by value or matches on its representation. Statements and proofs may do both freely (`Nth(E, n, *s, i, h)` in a type is fine).

```
def Bump (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) : Unit := (
  let x = Read(Word, n, &*s, i, h);
  Set(Word, n, s, i, Succ(x), h)
)

def SetThenRead (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) :
    Eq(Word, (let c = *s; Set(Word, n, &c, i, W(7), h); Read(Word, n, &c, i, h)), W(7)) := (
  NthSetSame(Word, n, *s, i, W(7), h)
)

def ZeroBoth (n : Word) (k : Word) (s : &Slice(Word, n)) (h : Le(k, n)) : Unit := (
  WithSplit(Word, Unit, n, k, s, h, λ(l : &Slice(Word, k)) (r : &Slice(Word, Sub(n, k))) : Unit => (
    Fill(Word, k, l, Zero);
    Fill(Word, Sub(n, k), r, Zero)
  ))
)
```

## 10. Errors and what to do

| Message | Fix |
|---|---|
| `unknown constant X` | `X` is undefined, misspelled, declared later, or was itself rejected |
| `[Read] x was moved out or its borrow ended (reading ⊥)` | `clone` it, pass `&*x` instead of `x`, or read once and reuse the binding |
| `(surface) not a place` | `match` needs a place: `let v = call(…); match v { … }` |
| `the body of P has type A, but the goal is B` | your proof proves `A`; compare with `B`, and case-split or rewrite until they meet |
| `argument i (h) has type A, expected B` | wrong argument type, often a proof that needs a `rewrite` first |
| `[Repack] … field x … holds a value of type T, but its type from the earlier fields is U` | a dependent field doesn't match its index where the value must be whole |
| `[Drop] … dies while a value in flight borrows it` | you tried to return or pass a borrow of a local that is going out of scope |
| a message naming a rule (`[Rec]`, `[Access]`, …) | the hover shows the values involved; the matching example file shows the accepted pattern |
| parse error near `(` | remove the space before `(` in a call; parenthesize `fix`/`λ` inside `let … ;` |

## 11. Limitations to plan around

- No automation: every case split, induction and rewrite is written out. Keep lemmas small, and state them about calls so `rewrite` can find them.
- Structural recursion only: use fuel for measures.
- No shared borrows, and no borrows inside data (`Option<&T>` can't be written): use a precondition instead, e.g. `get_mut(m, k, h : Contains(*m, k)) : &V`.
- `t.1` on a pair that is still unknown is an error: `match` on it, or `let (a, b) = p`.
- `Word` is unary: concrete runs (`refl` on closed inputs) are fast only for small numbers.
