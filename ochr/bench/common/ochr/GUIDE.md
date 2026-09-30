# Ochr: a working guide

This guide teaches enough Ochr to start on the assignment. The language reference is `docs/RULES.md` (dense: read it when this guide is not precise enough). The examples tour in `checker/Ochr/Examples/00Std.lean` … `15BorrowTypes.lean` shows every feature with checked examples, each file opening with what it covers; `checker/Ochr/Examples/16Arrays.lean` is the arrays library. When in doubt, find an example in the tour: every program there is checked, and the `reject def`s show what the checker refuses and why.

## 1. What Ochr is

Ochr is a small language that combines Rust-style mutable borrows with a Lean-style dependent type theory. Programs mutate data in place through borrows (`&x`), and the same programs can appear inside types: a type is a program, and the checker evaluates it. So a property of an in-place function is stated by running the function inside the statement, for example "after `QuickSort` runs on a copy `c` of the array, `c` is sorted". There is no separate specification language.

Checking is running. The checker is an evaluator (a machine) that runs programs on symbolic inputs: a parameter's value is an abstract value `σ`, and a computation that cannot continue because it needs to know `σ` (a `match` on it) gets *stuck*. A stuck call is kept as a *sealed program*, printed `⌈…⌉`: the closed program that would compute the value once `σ` is known. Two types are equal when they evaluate to the same normal form. A proof splits on abstract values with `match`, which refines `σ` to each constructor in turn, so stuck programs can run further.

## 2. Workflow

- Your solution is the `.lean` file named in `SOLUTION_FILES`. It holds `ochr` blocks: `ochr Name uses A, B { declarations }`. A block sees the declarations of the blocks it uses (transitively) that were accepted, and the library `Prelude` (`Pair`, `False`, `True`, `And`) always.
- `lake -q build` elaborates your file. The checker runs as each `ochr` block is elaborated, and every declaration it rejects is reported as an error at the declaration's name, with the reason. (Use `-q`: without it, lake also replays the library's own verdict tables.)
- `lake -q exe check` prints the checker's verdict on every declaration: `ok` or `FAIL`, what was expected (`def`: accepted, `reject def`: rejected), and for a rejection the reason. It reads your file itself, so it works while declarations are still rejected. The checker is compiled, so this is fast; the tests take a few seconds.
- `lake -q exe check BlockName` checks only the named blocks (and what they use). Use it while you work on proofs, to skip the tests.
- `lake -q exe check --trace Name` prints the checker's trace for one declaration: the goal after evaluation, the case splits, the types of calls. This is how you see what a stuck goal looks like.
- `./grade.sh` is the grade. Its last line is `GRADE: PASS` or `GRADE: FAIL: <reasons>`.
- A declaration that is rejected is invisible to the declarations after it: if `QuickSort` is rejected, everything that mentions it fails with `unknown constant QuickSort`. Fix the first failure first.
- Declarations are checked in order, so a helper must come before its first use. There is no mutual recursion between top-level declarations.

## 3. Syntax

Declarations (inside a block):

```
def F (x : A) (y : &B) : C := body            -- a function; parameters are named and typed
def G (n : Word) (s : &Slice(Word, n)) : Unit by n := body   -- `by n`: recursive, decreasing on n
inductive List (A : Type) := Nil | Cons(h : A, t : List(A))  -- data (sort Type by default)
inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)   -- a proposition
```

Terms:

| Form | Meaning |
|---|---|
| `f(a, b)` | a call, always saturated; no space before `(` |
| `C(a, b)`, `C` | a constructor; the type's parameters are inferred (`Cons(1, Nil)`) |
| `match p { C1(x, y) => t, C2 => u, }` | case analysis on a place `p`; `x`, `y` are the *field places* `p.x`, `p.y`, not copies; `_` ignores a field; a trailing comma is allowed |
| `match h {}` | no arms: `h` has an empty type (`False`, or `Le(Succ(a), Zero)`, …); proves anything |
| `let x = t; u`, `let x : T = t; u` | local binding (the annotation is needed when the type cannot be inferred, e.g. for a proof or a `match`) |
| `t; u` | sequence |
| `&p`, `*p`, `p := t` | borrow, dereference, assignment (to a place) |
| `&*s` | reborrow: a new borrow of what `s` borrows, leaving `s` usable afterwards |
| `clone(p)` | an explicit copy |
| `λ(x : A) (y : B) : C => t` | a closure (captures values, never borrows) |
| `Π(x : A) (y : B). C`, `A → B` | function types |
| `(a, b)`, `A × B` | pairs (`Pair`); take them apart with `match p { Mk(a, b) => … }` or `let (a, b) = p; …` |
| `Eq A a b`, `refl` | equality and its proof |
| `Id A t u` | the programs `t` and `u` have the same result and the same effect (§6) |
| `⊤`, `False`, `P ∧ Q`, `⟨h, k⟩` | true, false, conjunction, a proof of a conjunction |
| `let ⟨h, k⟩ = p; u` | take a conjunction apart |
| `rewrite h in t`, `rewrite ← h in t` | rewriting (§7) |
| `split F in t`, `split F { C(x) => t, … }` | split the goal on a stuck call of `F` (§7) |
| `Nat`, `Z`, `S n`, numerals | unary natural numbers (built in) |
| `Unit`, `()` | the unit type |

Layout conventions (the tour's): one declaration per line group, a multi-line body in parentheses `:= ( … )`, one match arm per line with a trailing comma, a multi-statement arm in `( … ),`, and matches inside types and argument lists on one line without a trailing comma. Line breaks are whitespace. Comments are `-- …` and `/- … -/`.

Numbers: `Word` (`Zero | Succ(pred : Word)`) is the type of keys, values, indices and lengths. It is unary in the logic and a machine word in the cost model, and it is a *copy* type (§4). `W(7)` (from the library `Index`) is the `Word` for the numeral 7. `Nat` is a separate built-in type that you will rarely need.

## 4. Borrows, moves and copies

- `&p` borrows the place `p`; the borrow is ended automatically when `p` (or anything containing it) is used again, which is Rust's borrow checker done at run time on symbolic values. Using a borrow after it has been ended is an error.
- A borrow parameter `x : &T` is a `&mut`: the function may read and write `*x`. There are no shared borrows, so a function that only reads a structure still takes `&` and must be shown not to change it when that matters.
- A function may return a borrow (`: &T`) only if it takes a borrow parameter; the result borrows from it.
- Reading a place moves its value out unless the type is a copy type (D53): `Word`, `Unit`, propositions, types, inductives declared `copy`, and non-recursive inductives whose fields are copies (such as `Opt` with a `Word` field, or `Dec`). Reading a moved-out place is an error (`[Read] x was moved out`). Use `clone(p)` for an explicit copy, or reborrow `&*s` instead of moving `s`.
- Inside types and proofs nothing is moved: those reads always copy (they run on a private copy of the state and leave no trace).
- A closure captures values, never borrows; a closure may run again, so its body may not move a captured value out (use `clone`).
- A match on a place borrows into it: in `match *s { MkSlice(c) => … }`, `c` is the place `(*s).c`.

## 5. Recursion is structural

A recursive function declares its decreasing parameter, `by x`, and every recursive call must pass, in that position, a strict sub-value of `x`'s value on entry (a field reached by matching, e.g. `k'` in `Succ(k')`), or a borrow of one. There is no recursion on a measure (such as a length that shrinks by an arbitrary amount): the usual workaround is an extra *fuel* parameter that decreases by one per call and starts large enough (for example at the length). A function without `by` cannot call itself. A recursive call may also appear inside a closure in the body.

## 6. Statements about in-place code

Types are programs, so a statement can run the in-place code. Two forms recur:

- **On a copy.** `(let c = *s; F(&c); P(c))` copies the current contents of `*s` into a local `c`, runs `F` on it in place, and states `P` of the result. `*s` itself is untouched, so the same statement can still mention the contents before as `*s`: `(let c = *s; F(&c); Perm(n, c, *s))`.
- **`Id A t u`** says that the programs `t` and `u`, each run on its own copy of the current state, return equal results *and* leave equal contents in every place they may write (their footprint: places they assign or borrow, and what borrow parameters point to). For example `Id Unit (F(s)) (*s := G(*s))` says that `F` has exactly the effect of writing `G`'s result. `Id` evaluates to a conjunction of `Eq`s, one per observed place, so it is proved like any conjunction of equations.

`Eq` computes: `Eq A a a` is `⊤` (proved by `refl`); `Eq D (C(a1, a2)) (C(b1, b2))` is `Eq _ a1 b1 ∧ Eq _ a2 b2`; `Eq D (C1 …) (C2 …)` for different constructors is `False`; `Eq Unit a b` is `⊤`. So `refl` proves an equation whenever both sides evaluate to the same normal form, and many "obvious" equations are `refl` after the right `match`.

## 7. Proofs

A proof is a program whose type is the statement; it is erased when the program runs.

- **Case split.** `match x { Zero => …, Succ(x') => … }` in a proof refines `x` to each constructor, in the goal and in every hypothesis. Matching on a place whose content is stuck (a sealed program) first generalises that program to a fresh abstract value, then splits. To split on the result of a call, bind it and match: `let d = LeDec(a, b); match d { Yes(h) => …, No(k) => … }`; code that makes the same call becomes unstuck in each arm.
- **Induction** is recursion: a proof declared `by x` may call itself on a strict sub-value of `x`, and that call's type is the induction hypothesis. A proof about a borrowed place can call itself (or another lemma) on a borrow of a field, `Lemma(&p)`, and the result is about the whole: `AddMZero` in `00Std.lean` is the pattern.
- **Lemmas** are ordinary functions returning propositions; call them to get facts: `LeTrans(a, b, c, h1, h2)`. A lemma about in-place code can be called on a borrow of a local copy inside a proof: `(let c = *s; F(&c); Lemma(n, &c))` has `Lemma`'s statement about the contents after `F`.
- **False.** `match h {}` for `h` of an empty type. A contradictory equation between different constructors is `False` by computation, so it matches with no arms too.
- **Conjunctions.** Build with `⟨p, q⟩`; take apart with `let ⟨p, q⟩ = h; …`.
- **Rewriting.** For `h : Eq A a b`, `rewrite h in t` proves the goal `G` from `t : G'`, where `G'` is `G` with every occurrence of `b` replaced by `a`; `rewrite ← h in t` replaces `a` by `b`. The goal must be known (the declaration's type, a call's argument, or `let x : T = (rewrite …); …`). A rewrite that finds no occurrence is an error, and occurrences hidden inside a stuck `match` are not found, so state helper facts about calls rather than about inline matches. Several rewrites chain: `rewrite h1 in rewrite ← h2 in t`. Examples: `05Equality.lean`, and the lemma library in `16Arrays.lean`.
- **`split F in t`** splits the goal on the first stuck call of `F` it contains, as a `match` on that call's result would; `split F { C1 => t1, C2(x) => t2 }` gives each arm. Examples: `08CaseSplits.lean`.
- **`J`** (transport) exists but `rewrite` is almost always easier.

When a proof is rejected, `lake -q exe check --trace Name` shows the goal in evaluated form. A goal that is stuck on `⌈F(σ3, …)⌉` is waiting for a case split on something `F` matches on.

## 8. The checker's messages

- `unknown constant X`: `X` is not defined, or was rejected (see its own verdict first).
- A hole, `?` (or `sorry`), is a value of whatever type its context requires: the goal in tail position, a parameter's type as a call's argument, or an annotation's type. The declaration is accepted, and the build warns at the hole with the goal: the bindings in scope, with their types and values, then `⊢ goal`. So a hole is how you see a goal: write `?` where a proof is needed and build. A hole whose type the context does not give (`let y = ?`) is an error. A finished solution has no holes.
- `the body of X has type A, but the goal is B`: the proof proves `A`; the statement needs `B`. Compare the two normal forms.
- `argument i (h) has type A, expected B`: a call's argument has the wrong type.
- `[Read] x was moved out (D53)`: `x` was already moved; `clone` it, reborrow, or read it once.
- `[K2]` / `[K3]` errors: runtime code touched the array representation directly (§9).
- Messages naming a rule (`[Rec]`, `D48`, …) refer to `docs/RULES.md`.

## 9. The arrays library (`ArrayLemmas`)

Blocks `Index`, `Arrays` and `ArrayLemmas` in `checker/Ochr/Examples/16Arrays.lean`. Read that file: every declaration is short and checked. In outline:

- **Numbers (`Index`).** `Le(a, b)`, `Lt(a, b)` (propositions, by recursion); `LeDec(a, b) : Dec(Le(a, b), Lt(b, a))` and `LtDec(i, n) : Dec(Lt(i, n), Le(n, i))`, comparisons that return the proof (`Yes(h)` / `No(k)`); `Leb`, `Eqb` (booleans); `WAdd`, `Sub`, `W`; and facts: `LeRefl`, `LeStep`, `LeTrans`, `LeAddL`, `AddRS`, `AddZeroR`, `AddOneR`, `SubPos`, `SubOneLe`.
- **The model (`Arrays`).** `Slice(E, n)` is a view of `n` elements, `Array(E, n)` an owned array. The pure functions on views: `Nth(E, n, s, i, h)` is element `i` (with `h : Lt(i, n)`), `SetS` replaces an element, `TakeS`/`DropS` split at `k` and `JoinS` joins, `SnocS`/`PopS` work at the end.
- **The natives (`Arrays`),** the only way runtime code reaches an array: `AsSlice(E, n, &a)` (the view of an array), `Read(E, n, s, i, h)`, `Set(E, n, s, i, x, h)`, `GetMut(n, s, i, h)` (a borrow of element `i`, for `Word` elements), `WithSplit(E, R, n, k, s, h, f)` (runs `f` on borrows of the first `k` elements and of the rest, then puts them back: the `split_at_mut` of Ochr), `ArrEmpty`, `ArrPush`, `ArrPop`. Built from them: `Swap(E, n, s, i, j, hi, hj)`, `Replicate`, `Fill`, `FillFrom`.
- **Lemmas (`ArrayLemmas`).** `NthSetSame`, `NthSetOther`, `JoinTakeDrop`, `TakeJoin`, `DropJoin`; counting: `Count(q, n, s)` (how many elements equal `q`), `Ind`, `CountJoin`, `CountSet`, `CountSwap`; `SwapS` (the model of `Swap`) with `SwapIsSwapS`; `GetMutSet` (writing through `GetMut` is `Set`).
- **The rules.** The representation is abstract: outside *model code* (the natives' bodies, and *model functions*, which take or return a view by value and so never run at runtime), runtime code only borrows views. It never reads a view by value, matches on `MkSlice`/`MkC`/`MkArray`, or builds one. Statements and proofs may do all of this freely: `Nth(E, n, *s, i, h)` is fine in a type. A function that takes `(v : Slice(E, n))` by value is a model function: it may match on the representation, and it can be used in statements and other model code but not called from runtime code.

Examples (all checked):

```
-- Reading and writing through the natives.
def Bump (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) : Unit := (
  let x = Read(Word, n, &*s, i, h);
  Set(Word, n, s, i, Succ(x), h)
)

-- A bounds proof from a runtime comparison.
def ReadOr (n : Word) (s : &Slice(Word, n)) (i : Word) (d : Word) : Word := (
  let dec = LtDec(i, n);
  match dec {
    Yes(h) => Read(Word, n, s, i, h),
    No(k) => d,
  }
)

-- Two disjoint borrows at once, scoped by a continuation.
def ZeroBoth (n : Word) (k : Word) (s : &Slice(Word, n)) (h : Le(k, n)) : Unit := (
  WithSplit(Word, Unit, n, k, s, h, λ(l : &Slice(Word, k)) (r : &Slice(Word, Sub(n, k))) : Unit => (
    Fill(Word, k, l, Zero);
    Fill(Word, Sub(n, k), r, Zero)
  ))
)

-- A statement about in-place code, run on a copy, proved by a library lemma.
def SetThenRead (n : Word) (s : &Slice(Word, n)) (i : Word) (h : Lt(i, n)) :
    Eq Word (let c = *s; Set(Word, n, &c, i, W(7), h); Read(Word, n, &c, i, h)) (W(7)) := (
  NthSetSame(Word, n, *s, i, W(7), h)
)

-- A concrete run, checked by evaluation.
def BumpRun : Id Word (let a = ArrPush(Word, W(1), ArrPush(Word, Zero, ArrEmpty(Word), W(4)), W(9)); Bump(W(2), AsSlice(Word, W(2), &a), Succ(Zero), refl); Read(Word, W(2), AsSlice(Word, W(2), &a), Succ(Zero), refl)) (W(10)) := refl

-- Induction on a number, a rewrite, a conjunction, and an empty case.
def CountDown (k : Word) : Word by k := (
  match k {
    Zero => Zero,
    Succ(k') => CountDown(k'),
  }
)

def CountDownZero (k : Word) : Eq Word (CountDown(k)) Zero by k := (
  match k {
    Zero => refl,
    Succ(k') => CountDownZero(k'),
  }
)

def UseRewrite (a : Word) (b : Word) (h : Eq Word a b) (p : Le(a, W(3))) : Le(b, W(3)) := rewrite h in p

def Both (a : Word) (h : Le(a, W(3)) ∧ Le(W(3), W(5))) : Le(a, W(5)) := (
  let ⟨h1, h2⟩ = h;
  LeTrans(a, W(3), W(5), h1, h2)
)

def NotLtZero (a : Word) (h : Lt(a, Zero)) : Eq Word a Zero := match h {}
```

## 10. Limitations to plan around

- No recursion on a measure: use fuel (§5).
- No shared borrows: read-only functions take `&` and their not changing anything is a statement to prove.
- No automation: every case split, induction and rewrite is written out. Keep lemmas small and state them about calls, so that `rewrite` can find them.
- `Word` is unary: concrete runs are fast only for small numbers (the tests use numbers below 100).
- No projections of stuck pairs (`t.1` on a pair that is not yet a constructor value is an error): return separate results, or `match` on the pair.
- `&E` is not well formed for a type variable `E`, and a returned borrow must come from a borrow parameter.
- A field of an inductive cannot have a type computed by a function applied to a parameter (such as `Array(E, cap)`); the assignment's types show the workaround where it matters.
