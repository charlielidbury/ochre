# DLLBC, Take Two: One Grammar, Four Arrows

*A standalone presentation of the Dependent Low-Level Borrow Calculus: a language with full dependent types and Rust-style ownership, in which type checking is symbolic execution. Built around one syntactic category and four evaluation arrows that carry all behavioral variation.*

---

## Plan of the Document

Each section is written incrementally and reviewed before the next. Sections marked ▢ are planned but not yet written.

1. **The language at a glance** — one syntactic category; declarations; the four arrows and the construct/arrow table. *(written below)*
2. **First programs** — moves, borrows, writes through borrows; ⇐ as fill-only and the drop reorganization; the take-and-refill idiom (`*x` under ⇒); reborrow as `&mut *x`; the self-reborrow, rejected. *(written below)*
3. **Match** — owned and borrow modes; refinement as ⇜ at the scrutinee (and at derefs); contract-free siblings and strong updates; the join by reorganization and generalization. *(written below)*
4. **Worked examples, ascending** — list `push` (take/rebuild, safe here and not in Rust); Σ-paired `Vec` push in place (dependent siblings, order forced by types). *(written below)*
5. **Boundaries** — snapshots in signatures; telescopes and comptime deref; the `↝` type; calls as wires; the audit at return. *(written below)*
6. **Entangled calls** — `choose`; loan groups; opaque ending; the precision spectrum. *(written below)*
7. **Inductive declarations** — the CIC scheme; comptime index arguments; generated recursors and `T.copy`; *unrestricted* as a derivability fact. *(written below)*
8. ▢ **Recursion and termination** — `[k]`, the snapshot-subterm guard, measures as the future escape hatch.
9. ▢ **The comptime fragment as a type theory** — conversion (Ω-free over substituted terms), universes, K, elaboration of match to eliminators.
10. ▢ **Deferred** — shared borrows; borrow-capturing λ's and the capture rule that returns with them; erasure and quantities; unified `fn`/λ; traits.

Metatheory remains deliberately deferred throughout.

---

## 0. Orientation

Five sentences of context, so that §1's vocabulary stands on its own; every notion here receives a full treatment in its planned section.

DLLBC programs execute against an **environment Ω** mapping variables to **values**, which are trees — constructors applied to values, plus a few ownership-tracking forms. There is no heap and no addresses: a mutable reference is modeled by moving ownership of a subtree to the reference (`borrowₘ ℓ v`) and leaving a marker (`loanₘ ℓ`) where it was; ⊥ marks a vacant slot. Types may mention program values, but only as **snapshots** — the (possibly symbolic, σ) value a variable held at a fixed moment — never as locations, so mutation can never make a type stale. The type checker *is* a symbolic interpreter running the same rules as the evaluator over symbolic values; **unrestricted** types (those whose values contain no borrows or loans) are the fragment where the ownership machinery is vacuous, and it is on this fragment that types, indices, and proofs live. Contracts appear only at abstraction **boundaries** — function signatures, written as telescopes whose borrow entries carry an obligation type `&mut (s : τ ↝ S)` — while inside a function body, borrowing is contract-free and the interpreter simply watches.

---

## 1. The Language at a Glance

### 1.1 One grammar

There is a single syntactic category of terms; types are terms (of universe sort), and the borrow machinery consists of ordinary term formers within it. Stratification into "pure" and "runtime" is not syntactic — it is recovered semantically, as the fragment on which certain arrows are defined (§1.3).

```
t, τ, S ::=
    x                              variable
    Typeᵢ                          universe, i ∈ ℕ

    Π (x : τ) → τ′                 dependent function type
    λ (x : τ). t                   function (no capture of runtime variables)
    t t′                           application

    T                              inductive type (declared)
    T.c                            constructor (declared)
    match t { C(x̄) => t′, … }     pattern match, one constructor deep

    let x = t ; t′                 declaration
    t := t′ ; t′′                  assignment
    &mut t                         mutable borrow
    &mut (s : τ ↝ S)               borrow type; s (the snapshot) bound in S
    *t                             dereference
```

Three grammar-level decisions, each argued in later sections but recorded here:

*No capture.* A λ may mention global declarations and enclosing **pure** variables (snapshots, type parameters); it may not close over runtime variables. Callers pack data into arguments. Consequence: every function value is unrestricted, and closure formation is inert (§2). The capture rule returns, richer, with borrow-capturing closures (§10).

*No `copy`, no `take`, no `reborrow`.* All three are derived. `take` is `*x` read under ⇒ (destructive read through a borrow, leaving a hole). `reborrow` is `&mut *x`. `copy` is a *generated function* `T.copy : T → T × T` (consume-and-rebuild, §7), used via the idiom `match T.copy x { Pair(l, r) => { x := l ; …r… } }` — and rarely needed at all, because type-level reads go through snapshots (⇝) at no runtime cost.

*One grammar, positional restrictions in the rules.* The targets of `:=` and the subjects of `&mut` are syntactically arbitrary terms; the ⇐ rules are simply only *defined* on the shapes a location can take — a variable under zero or more peels, `x`, `*x`, `**x`, … Writing through anything else is spelled with a `let` first: `let tmp = f a ; *tmp := v`. There is no field path in any position — field access is match's job (§3). This keeps the grammar to a single category, with the arrows (not the syntax) determining where each construct is meaningful — the table below is exactly that determination.

### 1.2 Declarations

```
D ::=
    inductive T (Δ_par) : Δ_ind → Typeᵢ := | C₁ : Δ₁ → T x̄ t̄₁ | …
    fn f [k] : Δ → τ = t
```

Inductive declarations follow the CIC scheme (parameters, indices, strict positivity); each declaration generates its recursors and, on hereditarily borrow-free instantiations, its copy function (§7). Function declarations carry a telescope Δ — each borrow entry binding both the argument and its snapshot for everything downstream — and a decreasing-argument index `[k]`, vacuous for non-recursive bodies (§8). Whether `fn` can collapse into a top-level `let` of a λ is an open unification, shelved (§10).

### 1.3 The four arrows

All evaluation and checking is organized by four judgment forms over one grammar:

| | **read** | **write** |
|---|---|---|
| **runtime** | Ω ⊢ t **⇒** v ⊣ Ω′ — consume-read: evaluate `t` to a value, with move semantics | Ω ⊢ t **⇐** v ⊣ Ω′ — destructive write: push `v` into the location `t` denotes |
| **comptime** | Ω ⊢ t **⇝** v ⊣ Ω′ — comptime read: evaluate in the borrow-free fragment | Ω ⊢ x **⇜** t ⊣ Ω′ — comptime write: refine the snapshot layer by substitution |

The comptime pair is not a second semantics: it is the **same machine restricted to the borrow-free, assignment-free fragment** — comptime evaluation threads Ω over pure entries; it excludes the constructs that *touch the loan state* (minting a borrow, consuming through one — though not `*t` as pure projection; see §5), and it excludes `:=` outright, so a ⇝-evaluation's only footprint on Ω is the fresh pure entries its `let`s introduce. (The comptime *write* ⇜ is unaffected: it is the checker's refinement judgment, fired at match branch entry — never the elaboration of a surface `:=`.) "No side effects at the type level" is a fragment property, not a separate rule set. It is also future-proofing: one can imagine a later version making **erasure** formal, in which type annotations, indices, and everything else evaluated only by the comptime arrows is deleted before the program runs. In that future it is essential that comptime evaluation has no effect on the state the runtime sees — types will not exist at runtime, so nothing the runtime depends on may have happened inside them. The fragment restriction is that guarantee, stated today. A second dividend lands in §9: conversion compares substituted terms with no Ω in sight, which an assigning ⇝ would forbid.

Which arrows are defined on which constructs is the language's skeleton:

| construct | ⇒ | ⇐ | ⇝ | ⇜ | note |
|---|---|---|---|---|---|
| `x` | ✓ | ✓ | ✓ | ✓ | ⇒ is the move; ⇐ fills a vacant slot (a *drop* reorganization vacates it first if needed); ⇝ reads the snapshot; ⇜ **is refinement** |
| `Typeᵢ` | ✗ | ✗ | ✓ | ✗ | comptime value; no runtime representation (pre-erasure aspiration) |
| `Π (x : τ) → τ′` | ✗ | ✗ | ✓ | ✗ | as above |
| `λ (x : τ). t` | ✓ | ✗ | ✓ | ✗ | no capture ⇒ formation is inert: Ω′ = Ω under ⇒ as well |
| `t t′` | ✓ | ✗ | ✓ | ✗ | ⇒: the call rule (arguments by ⇒, group minted from signature); ⇝: β/ι-reduction |
| `T` | ✗ | ✗ | ✓ | ✗ | a comptime value |
| `T.c` | ✓ | ✗ | ✓ | ✗ | constructor values exist in both worlds; ⇒ on the applied form consumes its fields |
| `match t { … }` | ✓ | ✗ | ✓ | ✗ | ⇒: two modes by scrutinee type, branch entry refines by ⇜; ⇝: ι-reduction, stuck on symbolic |
| `let x = t ; t′` | ✓ | ✗ | ✓ | ✗ | sequencing in both fragments |
| `t := t′ ; t′′` | ✓ | ✗ | ✗ | ✗ | ⇒: RHS by ⇒, target by ⇐; excluded from the comptime fragment — pure code sequences with `let`, never `:=` |
| `&mut t` | ✓ | ✗ | ✗ | ✗ | mints a loan; `&mut *x` is reborrow |
| `&mut (s : τ ↝ S)` | ✗ | ✗ | ✓ | ✗ | the borrow *type* is comptime even though borrow *values* are excluded from the fragment |
| `*t` | ✓ | ✓ | ✓ | ✓ | the peel, arrow-generic: under ⇒ reads through destructively (take); under ⇐ locates through non-destructively (write-through); under ⇝ projects the payload snapshot; under ⇜ refines it |

Two regularities to notice, since they organize everything that follows. **Down the columns**: the ⇝ column is the ⇒ column minus the borrowing rows, minus assignment, and minus consumption — the comptime fragment made visible. **Across the rows**: several constructs mean different things under different arrows (`*t` reads destructively, locates non-destructively, or projects a snapshot; `match` destructures or reborrows by mode; `x` is a move, a target, a snapshot, or a refinement site) — one grammar, with the arrows carrying all the behavioral variation. The remainder of this document is the unpacking of this table, one region at a time.

---

## 2. First Programs

We now run the machine. Each program below is annotated with the environment Ω after each step, in comments; the prose names which arrow each step exercises. Numerals abbreviate `Nat` values (`0` for `Z`, `1` for `S Z`, …). One standing convention throughout: **reorganization is lazy**. The environment may be rewritten between any two steps — ending a loan, dropping a displaced value — but the checker does so only when some rule's premise demands it, never eagerly. The traces show reorganizations at the moment they are forced.

### 2.1 Moves, and the vacant slot

A bare use of a variable is a ⇒-read: it consumes.

```rust
let x = 3;
// Ω = x ↦ 3
let y = x;
// Ω = x ↦ ⊥, y ↦ 3
```

The use of `x` on the second line is the judgment `Ω ⊢ x ⇒ 3 ⊣ Ω[x ↦ ⊥]`: the value moves out, and ⊥ — the vacant slot — is left behind. ⊥ is not a value of any type; it is the *absence* of one, and every read-shaped rule excludes it, so a second use of `x` is simply stuck: there is no rule. A vacant slot is not dead, though — it can be refilled:

```rust
x := 7;
// Ω = x ↦ 7, y ↦ 3
```

This is the one and only mode of ⇐ — **fill**: the write's premise is that the target slot is ⊥, and the value drops in. Writing onto a slot that is *not* vacant is handled the same way everything else is handled: a reorganization, inserted lazily, vacates it first (§2.3).

### 2.2 Borrowing, writing through, and ending

```rust
let x = 3;
// Ω = x ↦ 3
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 3
*b := 7;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 7
// forced reorganization before the next line: End-Mut on ℓ
// Ω = x ↦ 7, b ↦ ⊥
let y = x;
// Ω = x ↦ ⊥, b ↦ ⊥, y ↦ 7
```

Line two mints a fresh loan identifier ℓ: ownership of `3` transfers to `b`, and the marker `loanₘ ℓ` parks at `x`, rendering it unusable — not vacant (⊥ says "nothing here"; a loan says "something is owed here") but equally excluded from every read rule. Line three writes *through* the borrow: under ⇐, the `*` peels one indirection **without consuming `b`** — the target is located, not read — and the payload is replaced in place. Note there is no contract governing this write; within a body, borrowing is contract-free, and the checker (a symbolic interpreter running these very rules) simply watches the payload change.

Line four is where laziness pays out. The move needs to ⇒-read `x`, but `x` holds a loan — no rule applies. The environment reorganizes first: **End-Mut** takes the borrow's current payload, plugs it back where the loan marker sits, and kills the borrow (`b ↦ ⊥`). End-Mut is itself just a ⇐-fill at the loan marker followed by the kill — the write arrow, aimed at the environment's own bookkeeping. Then the move proceeds. Nothing marked *when* ℓ had to end; the demand for `x` did.

### 2.3 Drop

Fill demands a vacant target. When a write aims at a live value, a **drop** reorganization is forced first — the lazy machinery again, now vacating instead of ending:

```rust
let x = 3;
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 3
// forced before the next line: drop b's contents — End-Mut ℓ returns 3 to x, then the dead borrow is discarded
// Ω = x ↦ 3, b ↦ ⊥
b := 9;
// Ω = x ↦ 3, b ↦ 9
```

Drop is a total procedure, not a choice: **end the displaced value's loans, innermost first — each end requires both the loan and its borrow to be entries in Ω — then discard what remains.** A value containing no borrows and no loans skips straight to the discard, so ordinary code pays nothing. A chain-link value like `borrowₘ ℓ 3` dies naturally: ending ℓ sends the payload home to `x` *before* the slot is vacated, so no ownership is ever stranded. And if some loan in the displaced value *cannot* be ended — its other end is not in Ω — then no rule applies and the program is rejected, the same stuckness discipline as everything else in the calculus. Section 2.5 exhibits the one program shape that gets rejected this way, and why rejecting it is a bargain.

(Readers from Rust may recognize drop by name: overwriting a slot runs `Drop` on the old contents. Ours is that operation, with "return what you borrowed" playing the role of the destructor.)

### 2.4 Take and refill: reading through a borrow

What does `*b` mean in *read* position — under ⇒? The peel is arrow-generic, and ⇒ is consumption, so: it moves the payload out **through** the borrow, leaving a hole inside it.

```rust
let x = Cons(3, Nil);
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (Cons 3 Nil)
let tail = *b;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ ⊥, tail ↦ Cons 3 Nil
*b := Cons(7, tail);
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (Cons 7 (Cons 3 Nil)), tail ↦ ⊥
```

Between the take and the refill, `b` holds a hole — a state both Rust (error E0507) and LLBC (a premise of its move rule) forbid, because in their setting a panic in the gap would end the loan with the owner recovering garbage. DLLBC has no panic, and a hole cannot escape: ⊥ satisfies no read rule, no boundary can be crossed while an argument borrow holds one (§5), and End-Mut's plug-back of ⊥ would merely leave the *owner* vacant — a fillable slot, not a corruption. While the hole is open, the only applicable rule at `b` is the ⇐-fill through it. Holes are inert, transient, and local; and the take-and-refill above is the update-in-place idiom this calculus is built to make routine — no list node was copied, and the value's journey out and back is, under compilation, no journey at all.

### 2.5 Reborrow, and the self-reborrow

`&mut` composed with the peel gives the last first-class idiom: `&mut *b` borrows the *payload* of a borrow — a **reborrow**. The parent is suspended, not consumed; it recovers when the child's loan ends.

```rust
let x = 3;
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 3
let c = &mut *b;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (loanₘ ℓ′), c ↦ borrowₘ ℓ′ 3
```

`b` now holds a loan marker where its payload was: unusable until ℓ′ ends, but alive — the chain reads x → ℓ → ℓ′ → the value. This is the operation Rust inserts silently at nearly every call site, so that passing a reference does not consume it.

The reborrow composes with drop into the calculus's classic stress test — the *self-reborrow*, a program this calculus deliberately **rejects**:

```rust
let x = 3;
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ 3
let c = &mut *b;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (loanₘ ℓ′), c ↦ borrowₘ ℓ′ 3
b := c;
// REJECTED: the RHS ⇒-consumes c, so borrowₘ ℓ′ 3 is in flight, not an entry in Ω;
// drop must vacate b, which requires ending ℓ′, whose borrow is the in-flight value;
// end-rules match only entries — no rule applies.
```

The chain to be dropped runs *through the value being written*: `b`'s payload is `loanₘ ℓ′`, and ℓ′'s borrow is exactly the in-flight RHS. Ending cannot fire, drop is stuck, the program is rejected. Other calculi in this family accept this program — LLBC calls its version "twisted" — at the price of a dedicated mechanism: *ghost variables*, inaccessible environment entries that retain overwritten values so that a chain may pass through a name no program can utter. We decline to pay. The rejected idiom is the borrow *cursor* — `b := advance(&mut *b)` in a loop — and this calculus has no loops: cursors are written recursively, where each step passes the tail borrow as an *argument*, a fresh binder, no overwrite, no drop, nothing to ghost. In residual straight-line cases the workaround is one keystroke — `let b2 = advance(&mut *b)` — a fresh name instead of reassignment. What the rejection buys: no ghost entries in Ω, no inaccessible-name convention, no collectability story, and drop as a total procedure rather than a choice.

The section's real lesson survives the rejection intact: the borrow machinery has no rules of its own beyond bookkeeping. Every step in every trace above is ⇒ for the moves, ⇐-fill for every write, and two reorganizations — End-Mut and drop — aimed at an environment that remembers who owes whom.

---

## 3. Match

Inductive values are read by `match`, and `match` is the *only* eliminator: there is no field projection, no tag test, no destructor syntax. Consequently matching must work everywhere data is — including behind borrows — and the rule for matching through a mutable borrow is the load-bearing wall of the calculus. As with everything else, one syntax carries the variation: the scrutinee must be a variable (a restriction with a reason, §3.2), patterns bind constructor fields one level deep (`Cons(hd, tl)`; a bare `Nil` abbreviates `Nil()`), and what the binders *mean* is read off the scrutinee's type — an owned value is destructured, a borrow is matched *through*.

### 3.1 Owned mode: destructuring

Matching an owned value is functional pattern matching with move semantics: the scrutinee is ⇒-consumed, and its fields move into the binders.

```rust
let p = Pair(3, 7);
// Ω = p ↦ Pair 3 7
match p {
  Pair(a, b) => {
    // Ω = p ↦ ⊥, a ↦ 3, b ↦ 7
    a + b
  }
}
```

Nothing here is new: the match is a ⇒-read of `p` followed by fills of the binders. On concrete values this is ι-reduction wearing binder syntax; the comptime arrow ⇝ evaluates the same construct the same way on the pure fragment.

### 3.2 Symbolic scrutinees, and refinement as ⇜

Inside a function body, arguments are *symbolic*: the checker — a symbolic interpreter running the same rules — knows their types but not their values. A symbolic value σ is an entry of the environment's pure layer, written inline where it sits:

```rust
fn is_zero (n : Nat) = {
  // Ω = n ↦ (σ : Nat)
  match n {
    Z => {
      // ⇜ at n: σ := Z, everywhere
      // Ω = n ↦ ⊥
      true
    }
    S(m) => {
      // ⇜ at n: σ := S σ′ (σ′ fresh), everywhere
      // Ω = n ↦ ⊥, m ↦ (σ′ : Nat)
      false
    }
  }
}
```

Entering a branch performs a **comptime write at the scrutinee**: the judgment Ω ⊢ n ⇜ S σ′ ⊣ Ω′, which substitutes `S σ′` for σ in *every* entry and *every* type in Ω — the environment's knowledge is upgraded wholesale, not locally. This is dependent elimination in the Agda style — by unification and substitution, not by threading equality proofs — and it is why the scrutinee must be a variable: substitution is defined on variables, and an arbitrary expression has no substitutable identity. It is also, verbatim, what LLBC's symbolic interpreter does when matching a symbolic scrutinee; the observation that this mechanism *is* dependent pattern matching is the founding identification of this calculus.

Note the two layers of new names in the `S` branch. The binder `m` is a runtime entry, holding a value that can be moved, borrowed, matched. The symbolic σ′ is a pure entry, and it can outlive `m`: move `m` away, and σ′ persists wherever types and other entries mention it. Snapshots have independent lives.

### 3.3 Borrow mode: matching through

When the scrutinee is a mutable borrow, the same pattern means something stronger: the binders become **reborrows of the fields**, and the parent suspends until they die.

```rust
fn zero_head (b : &mut List Nat) = {
  // Ω = b ↦ borrowₘ ℓ (σ : List Nat)
  match b {
    Nil => {
      // ⇜ at *b: σ := Nil
      // Ω = b ↦ borrowₘ ℓ Nil
      ()
    }
    Cons(hd, tl) => {
      // ⇜ at *b: σ := Cons σ₁ σ₂ (σ₁, σ₂ fresh), everywhere
      // Ω = b ↦ borrowₘ ℓ (Cons (loanₘ ℓ₁) (loanₘ ℓ₂))   [suspended]
      //     hd ↦ borrowₘ ℓ₁ (σ₁ : Nat)
      //     tl ↦ borrowₘ ℓ₂ (σ₂ : List Nat)
      // forced before the next line: drop hd's payload (a plain Nat — discard)
      *hd := 0;
      // Ω = …, hd ↦ borrowₘ ℓ₁ 0, …
      // forced at branch exit (at latest, by return): End-Mut ℓ₁, then ℓ₂
      // Ω = b ↦ borrowₘ ℓ (Cons 0 σ₂)
      ()
    }
  }
}
```

Three things happened at the `Cons` boundary, and each is an instance of machinery already introduced. **Refinement**: ⇜ fires exactly as in §3.2, but at the *payload* — the deref cell of the ⇜ column — refining σ in the parent's borrow and everywhere else at once. **Reborrowing**: each field binder is a whole-value borrow of its component, a fresh loan (ℓ₁, ℓ₂) parked in the parent's value tree; the parent is suspended — its payload is now a `Cons` of loan markers, and no rule reads through a loan, so the intermediate states of the children are unobservable through `b`. **Contract-freedom**: the loans ℓ₁, ℓ₂ carry no obligations, and the write `*hd := 0` is a *strong update* — it replaces the payload and, in general, its type, with the checker simply tracking the new state. The suspension is what makes this sound: nothing can examine the parent until the children's loans end, and when they do, End-Mut plugs each final payload into its marker. The single point where `b`'s contents are ever *judged* is the function boundary — at return, `b` must hold a value of the type its signature owes (here `List Nat`, and `Cons 0 σ₂` converts) — a story told properly in §5.

The nullary branch shows the degenerate case for free: `Nil()` binds nothing, issues no loans, and the refinement alone updates the parent's payload.

Field access needs no other mechanism. There is no `b.head` in any position; "borrow the second field" *is* `match b { Cons(_, tl) => … }`, and the match hands over every sibling at once — which is more, not less, than a field projection offers, since disjoint siblings can now be mutated in the same breath. Section 4 exploits exactly this.

### 3.4 Variant change through the parent

The branch is not confined to updating fields; it may replace the parent's payload with a different variant outright. The drop discipline of §2.3 handles the displaced children without a special case:

```rust
    Cons(hd, tl) => {
      // Ω = b ↦ borrowₘ ℓ (Cons (loanₘ ℓ₁) (loanₘ ℓ₂)), hd ↦ …ℓ₁…, tl ↦ …ℓ₂…
      // forced before the next line: drop b's payload —
      //   End-Mut ℓ₁ (hd's payload returns, hd dies), End-Mut ℓ₂ (likewise, tl dies),
      //   then Cons σ₁ σ₂ is loan-free and is discarded
      // Ω = b ↦ borrowₘ ℓ ⊥, hd ↦ ⊥, tl ↦ ⊥
      *b := Nil;
      // Ω = b ↦ borrowₘ ℓ Nil
      ()
    }
```

The write's fill premise forces a drop of the old payload; drop's total procedure ends the children's loans first (both ends are in Ω — no self-reborrow pathology is possible here), the reassembled `Cons` is then owned and loan-free, and it is discarded. No borrow ever survives pointing into a value of the wrong shape, and no rule was added to say so: the fill premise, the drop procedure, and End-Mut compose into exactly the soundness condition other systems state by hand.

### 3.5 Matches anywhere, and the join

LLBC restricts disjunctions to terminal position, deferring what it calls the merge problem. Here match may occur anywhere, and the price is paid at the exit: the continuation after a match is checked in a *single* environment, so the branches' final environments must be brought into agreement. The join is deliberately the crudest sound one, built from parts already on the table:

1. **Reorganize** each branch's environment — end loans, drop dead values, lazily as ever — until all branches have the *same shape*: the same entries, with the same borrow/loan structure.
2. **Generalize** where values still differ: entries that disagree only in pure values (one branch left a payload `7`, another `3`) are replaced by a fresh symbolic value (σ : Nat) — knowledge deliberately forgotten, the ⇜ of refinement run backwards. In particular the scrutinee's branch-local refinements (σ := Nil versus σ := Cons σ₁ σ₂) are forgotten this way: the join re-generalizes to a fresh σ′.
3. Everything is up to renaming of loan identifiers and symbolic names, since branches mint fresh ones independently.

If reorganization cannot bring the shapes into agreement — one branch returns a borrow into `x`, another does not — the match is rejected in that position; moving it to terminal position, where each branch simply flows to the function boundary and no join is needed, is always available and is exactly LLBC's regime. The information loss in step 2 is the same loss a shared match motive imposes in any dependent type theory; a program that needs branch-specific knowledge downstream should return evidence of it — which, in a language where types are first-class, is what Σ-types are for.

---

## 4. Worked Examples, Ascending

Section 3.3's `zero_head` was the first real program; the two here ascend. The first is the calculus's flagship *small* program — five lines that Rust rejects and we accept, with the acceptance falling out of decisions already made. The second is the flagship *dependent* program: an in-place update of an invariant-carrying pair, where the contract-free regime of §3.3 turns out to be not a simplification but a necessity.

### 4.1 List push, by take and rebuild

```rust
fn push (e : T, v : &mut List T) = {
  // Ω = e ↦ (σₑ : T), v ↦ borrowₘ ℓ (σ : List T)
  let tail = *v;
  // Ω = e ↦ (σₑ : T), v ↦ borrowₘ ℓ ⊥, tail ↦ (σ : List T)
  *v := Cons(e, tail);
  // Ω = e ↦ ⊥, tail ↦ ⊥, v ↦ borrowₘ ℓ (Cons σₑ σ)
  // at return: v holds a List T — Cons σₑ σ converts ✓ (the boundary audit, §5)
}
```

The first line is `*v` under ⇒: the payload moves out through the borrow, leaving a hole. The second consumes `e` and `tail` into a fresh cell and ⇐-fills it back through `v` — the hole's one legal successor. No list node is copied; under compilation the "journey out and back" is no journey at all, and the cell construction is the single allocation the operation inherently needs.

Rust rejects this program (error E0507: cannot move out of `*v`), and its standard library sells the workaround (`mem::replace`, the `Option::take` dance). LLBC's move rule forbids it too. Their reason is the same: in a language with panics, the gap between the take and the refill is observable — unwinding would end the loan with the owner recovering garbage. Here the gap is unobservable by construction: there is no panic; ⊥ satisfies no read rule; and a function cannot return while an argument borrow holds a hole, because the boundary audit (§5) has nothing of the owed type to check. The two deletions — panic from the language, contracts from intra-body loans — were each made on independent grounds, and this program is where they pay jointly.

### 4.2 Vec push, in place

Now the dependent version. Two declarations, in the scheme of §1.2:

```rust
inductive Vec (T : Type₀) : Nat → Type₀ :=
  VNil  : Vec T Z
  VCons : Π (n : Nat) → T → Vec T n → Vec T (S n)
```

and a dependent pair Σ (l : Nat). Vec T l — a declared two-field inductive, constructor `Pair`, whose second field's type mentions the first. This is the type of "a vector that carries its own length," and the two fields are *coupled*: not every length-vector pair inhabits it, only the honest ones.

The task: push an element, mutating both fields in place — no new pair, no vector copy.

```rust
fn push (e : T, v : &mut Σ (l : Nat). Vec T l) = {
  // Ω = e ↦ (σₑ : T), v ↦ borrowₘ ℓ₀ (σ : Σ (l : Nat). Vec T l)
  match v {
    Pair(l, xs) => {
      // ⇜ at *v: σ := Pair σₗ σᵥ, everywhere
      // Ω = v ↦ borrowₘ ℓ₀ (Pair (loanₘ ℓ₁) (loanₘ ℓ₂))   [suspended]
      //     l  ↦ borrowₘ ℓ₁ (σₗ : Nat)
      //     xs ↦ borrowₘ ℓ₂ (σᵥ : Vec T σₗ)
      *xs := VCons(*l, e, *xs);
      // the three arguments, in their three modes:
      //   *l  — the index, a comptime position: ⇝-projects σₗ, consuming nothing
      //   e   — ⇒-moved
      //   *xs — ⇒-taken through the reborrow (hole), then the ⇐-fill closes it
      // Ω = e ↦ ⊥, xs ↦ borrowₘ ℓ₂ (VCons σₗ σₑ σᵥ : Vec T (S σₗ))   — strong update
      *l := S(*l);
      // RHS first: *l ⇒-takes σₗ (hole in l); then the fill
      // Ω = l ↦ borrowₘ ℓ₁ (S σₗ)
      // forced at branch exit: End-Mut ℓ₁, ℓ₂
      // Ω = v ↦ borrowₘ ℓ₀ (Pair (S σₗ) (VCons σₗ σₑ σᵥ))
      // at return: Pair (S σₗ) (… : Vec T (S σₗ))  :  Σ (l : Nat). Vec T l   ✓
      ()
    }
  }
}
```

Read the state between the two writes: `xs` holds a `Vec T (S σₗ)` while `l` still holds `σₗ`. **The pair's invariant is broken** — the components, at that instant, do not form an inhabitant of the Σ-type. This is exactly what in-place update of coupled data *means*: some component must change first, and between the first change and the last, the invariant does not hold. Three features of the calculus conspire to make this both expressible and sound:

*Contract-free siblings.* Suppose the loans ℓ₁ and ℓ₂ each carried a contract stating what they must hold at their end. What would ℓ₂'s say? "A vector whose length matches whatever ℓ₁ ends with" — a promise about another loan's *future*. Independent per-loan contracts cannot state the coupling, and the honest formalization of "the future value of" is prophecy, which this calculus's snapshot discipline exists to refuse. Contract-freedom dissolves the problem: the sibling writes are unchecked strong updates, and the *joint* condition is checked once, at the boundary, when both final values are in hand and forming the pair is a matter of conversion — `Vec T (S σₗ)` against index `S σₗ`, by arithmetic.

*Suspension.* The broken state is unobservable: `v`'s payload is loan markers, no rule reads through a loan, and nothing can examine the pair until both children's loans have ended — by which time the invariant holds again. The encapsulation that made contract-freedom sound in §3.3 is the same encapsulation that makes invariant-breaking safe here.

*The comptime deref.* `VCons`'s first argument is an index — a comptime position, ⇝-evaluated — so `*l` there is a *projection of the snapshot*, consuming nothing: the runtime `Nat` behind `l` has exactly one runtime consumer (`S(*l)`, on the next line), while every type-level mention rides the snapshot for free. This is the cell of the arrow table that lets dependent code be written against borrowed data without a single spurious copy; its full story is §5's.

Finally, the order of the two writes is forced, and by the types rather than by a rule. Swap them, and the constructor application is ill-typed *as a term*: the index position would ⇝-read `S σₗ` while the tail still has type `Vec T σₗ` — an off-by-one caught at the exact line that commits it. The signature said nothing about order; the dependency did. That is the division of labor this calculus is after: the ownership machinery makes the mutation safe, and the dependent types make it *correct*.

---

## 5. Boundaries

Inside a body, borrowing is contract-free: the checker watches every step. Contracts exist for **opacity** — the places it cannot watch. There are two: **function boundaries** (a body is checked once, against a signature; callers see only the signature) and **borrows stored under a type constructor** (an element of `List (&mut …)` needs a standalone type). Only there does a borrow's type carry a contract.

### 5.1 The ↝ type

> &mut (s : τ ↝ S)

"Exclusive access to a value of type τ; across this boundary, a value of type S is owed." The binder `s` names the payload *at entry*, for use in `S` — which is checked at *exit*, when the entry payload is otherwise long gone. The obligation is type-changing: `S` need not be τ.

```rust
fn push (n : Nat, e : T, v : &mut (Vec T n ↝ Vec T (S n))) = { … }
```

Pushing changes the type: the caller knows, from the signature alone, that the vector behind `v` is one longer at exit. We write `&mut (τ ↝ S)` when `S` ignores `s`, and `&mut τ` when moreover `S = τ`. Where LLBC's toolchain synthesizes a *backward function* to describe what flows back through a borrow, here that description is the obligation: ↝ is the backward function's type, moved into the signature.

### 5.2 Telescopes, and *b in types

A signature is a telescope: each argument's type may mention earlier arguments. For borrow arguments, later types reach the payload with the comptime deref — evaluated (⇝) at call entry, so it denotes the entry snapshot:

```rust
fn nth (b : &mut List T, i : Fin (len *b)) → &mut T
```

Out-of-bounds is unrepresentable: `Fin (len *b)` replaces the error monad. The division of labor is exact: **`*b` means the payload now** (⇝-projected wherever the type is consulted); **`s` means the payload at entry** (bound once, for the one position — the obligation — that must outlive its moment). And since `Σ (l : &mut List T). Fin (len *l)` is likewise well-formed, the telescope pattern "a borrow, plus data typed by its payload" is an ordinary first-class type. This is a payoff of the value semantics: a borrow *carries* its payload, so `*l` in a type is a pure projection — `*(borrowₘ ℓ v) ⇝ v` — never a store lookup, never stale.

### 5.3 Calls: consume and promise

A call is checked against the signature alone — recursion forces this (the checker cannot unroll), and all calls get it uniformly. The rule: ⇒-consume the arguments; for each argument borrow, annotate its loan with the owed type from the signature, instantiated at the actual arguments; mint a fresh symbolic value for the result.

```rust
let x = Cons(1, Nil);
let b = &mut x;
// Ω = x ↦ loanₘ ℓ, b ↦ borrowₘ ℓ (Cons 1 Nil)
push(7, b);
// b is consumed into the call; the signature's promise survives at the loan:
// Ω = x ↦ loanₘ ℓ [owed: List T]
// forced before the next line: End ℓ — the promise is collected
let y = x;
// Ω = x ↦ ⊥, y ↦ (σ′ : List T)
```

Ending a call-annotated loan is where the caller learns what the callee did: a fresh value arrives at the owed type — an existential, opened at loan-end. How much the caller learns is exactly how much the signature says: under `&mut List T`, only that σ′ is a list; under §5.1's `Vec` signature, its precise new length. The spec is the type, and precision is bought by strengthening it — the reader may see already that a Σ-typed obligation could pin the exit payload completely; sharpening obligations to that point is deferred.

### 5.4 The audit at return

The callee's side is symmetric, and it is the *only* check in the whole borrow story. Before returning: every argument borrow must hold a value of its owed type, verified by conversion. This is the single point where the body's strong updates, reassemblies, and holes are judged — a hole (⊥) satisfies no type, so a function cannot return one; the broken invariants of §4.2 must be mended by here; and a body may pass through any number of states its signature could never describe, because the signature only ever speaks about this one.

---

## 6. Entangled Calls

Section 5's calls were *wires*: each returned or retained borrow corresponds to one argument loan, and the ↝ obligation says everything. Some functions break the correspondence:

```rust
fn choose (c : Bool, x : &mut T, y : &mut T) → &mut T = {
  match c { True => x, False => y }
}
```

The returned borrow points into `x` or `y` depending on `c`. No per-borrow promise can say where the written value will land — and treating the loans independently is *unsound*: if `x`'s loan could end while the returned borrow lives, the caller would recover `x` while an exclusive borrow into (possibly) `x` is still active. What must be recorded is the **grouping** and an ending **order**.

### 6.1 Loan groups

A call whose borrows are entangled mints a **loan group**: a node in Ω tying the loans it captured to the borrows it issued.

```rust
let a = 0; let b = 0;
let pa = &mut a; let pb = &mut b;
// Ω = a ↦ loanₘ ℓₐ, b ↦ loanₘ ℓᵦ, pa ↦ borrowₘ ℓₐ 0, pb ↦ borrowₘ ℓᵦ 0
let r = choose(true, pa, pb);
// Ω = a ↦ loanₘ ℓₐ, b ↦ loanₘ ℓᵦ, r ↦ borrowₘ ℓᵣ (σ : Nat),
//     A(ρ) { captured: ℓₐ [owed: Nat], ℓᵦ [owed: Nat] ; issued: ℓᵣ }
*r := 7;
// Ω = …, r ↦ borrowₘ ℓᵣ 7, …
// forced before the next line: End ℓᵣ (its payload is surrendered to the group),
// then End A(ρ): each captured loan receives a fresh existential at its owed type
// Ω = a ↦ (σₐ : Nat), b ↦ (σᵦ : Nat), r ↦ ⊥
let z = a;
// Ω = a ↦ ⊥, …, z ↦ (σₐ : Nat)
```

The ending discipline is the group's whole content: **every issued borrow ends first** (its payload surrendered and discarded), **then the group ends**, releasing each captured loan with a fresh, unconstrained existential. The ordering is the soundness argument made structural — `a` cannot recover while `r` lives, because ℓₐ is held by the group and the group cannot end before ℓᵣ. A wire is the degenerate group — one captured, one issued, existential constrained to the surrendered value — so §5 and §6 are one mechanism at two precisions.

### 6.2 The cost, and the precision spectrum

Opacity is real: after `*r := 7`, the caller cannot prove `z = 7` — which input received the write is exactly what the group forgot. The general remedy is to index precision by the status of the callee's *backward flow* — what the group does at its end. It may be a **parameter** (the opaque group above: an abstraction boundary, the caller learns only types), a **definition** (transparent: the flow is definitionally the callee's body, full precision, no annotation), or a **spec** (a stated obligation — for `choose`, a function from the surrendered value to the pair released, `λ r. if c then (r, σᵧ) else (σₓ, r)` — checked against the body, hiding the rest). The trichotomy is the familiar one from proof assistants: `Parameter`, transparent `Definition`, module-sealed interface. This document's core is the parameter case; the other two are sharpenings of the group-end rule, deferred.

---

## 7. Inductive Declarations

### 7.1 The scheme

Declarations follow the CIC scheme: uniform **parameters**, per-constructor **indices**, constructors strictly positive.

```rust
inductive Nat : Type₀ :=
  Z : Nat
  S : Nat → Nat

inductive List (T : Type₀) : Type₀ :=
  Nil  : List T
  Cons : T → List T → List T

inductive Vec (T : Type₀) : Nat → Type₀ :=
  VNil  : Vec T Z
  VCons : Π (n : Nat) → T → Vec T n → Vec T (S n)
```

One reading convention with runtime consequences: **a constructor argument that appears in the result's index is a comptime position.** `VCons`'s `n` exists so that the result type can say `Vec T (S n)`; at a constructor application it is ⇝-evaluated (so `VCons(*l, e, t)` projects a snapshot rather than consuming a `Nat`), and under an eventual erasure it is deleted. The remaining arguments are runtime fields, ⇒-consumed at construction and released by match.

Parameters may be instantiated at *any* type, including affine ones: `List (&mut T)`, `Option (&mut T)`. The classification is computed per instantiation — an inductive value is unrestricted iff its declaration is borrow-free and its parameters are instantiated at unrestricted types — and owned match respects it automatically, since moving fields out is always lawful. The one restriction is inherited from the snapshot discipline: *indices* must be unrestricted, since index positions are comptime and snapshots are copies.

### 7.2 What a declaration generates

Each declaration yields, mechanically:

**Recursors** (`Nat.rec`, `List.rec`, …) — the CIC eliminators, one per universe as needed. `match` is the surface of elimination; its relationship to the recursors (and the K principle that relationship requires) is §9's subject. The recursors also settle a design question by making it moot: the pure fragment has no `fix`, and needs none — every structurally recursive pure function (`len`, `update`, `+`) is definable from recursors, exactly as in CIC, where `fix`/`match` is a convenience layer over them.

**A copy function**, on borrow-free declarations, by consume-and-rebuild:

```rust
fn Nat.copy (n : Nat) → Pair Nat Nat = {
  match n {
    Z    => Pair(Z, Z),
    S(m) => match Nat.copy m { Pair(a, b) => Pair(S a, S b) }
  }
}
```

Owned match consumes; each branch rebuilds the original *and* a duplicate. Generation is compositional — `List T`'s copy calls `T.copy` — and therefore **succeeds exactly on the unrestricted types**: borrow types have no copy, and the failure propagates. This turns the classification of §0 from a primitive judgment into a derivability fact: *τ is unrestricted iff `τ.copy` is generatable.*

There is no `copy` primitive in the kernel; the generated function and the write-back idiom (`match T.copy x { Pair(kept, given) => { x := kept ; …given… } }`) are the whole story. The need is rarer than Rust habit suggests: type-level reads ride snapshots via ⇝ at no runtime cost (§5.2), so copying arises only when a *runtime* consumer needs a value its owner also keeps — and there, one match is the honest price of the duplication.