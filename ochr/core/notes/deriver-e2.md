# deriver-e2: returned borrows (`TailM`, `AddM'`, `AddMEq`, `AddMEqOwned`) under RULES.md v0

## Summary

1. **Verdict:** E2 derives. `TailM`, `AddM'`, `AddMEq` and `AddMEqOwned` all check, and `AddMEq`'s S arm is bare recursion: the induction hypothesis and the refined goal are both `Eq Nat (S A(σ',τ)) (S B(σ')[τ])`, symbol for symbol. This needs v0 read charitably in three substantive places (F1, F2, F5) and two wording ones (F6, F7).
2. **Most important finding:** the loan-hole form of [Close] works because a filled hole records only the *final content* of the returned borrow. When the goal's sealed program is re-run after the split, its own continuation `*r := τ` fills the hole of the new inner stuck call, which is exactly what `AddM'`'s real code `*t := y` does at the call site. But v0 treats the hole as a *loan*, and that breaks in two places: a sealed program whose hole is still open cannot be normalised (this happens at any [Split] while a returned borrow is live, F3), and with two borrow arguments the same loan appears twice (F4).
3. **RULES.md must change:** [Seal] re-runs its own output forever as written (F1). [Reorg], [Pop] and "borrow-free" must see loans inside sealed programs (F2). A hole whose borrow is outside a [Seal] run must be inert, i.e. a hole is a variable and filling it is substitution (F3; this revisits D4's representation of the hole, not D4 itself). The "owner" wording in §4 is vacuous as written (F5).
4. **Confidence:** high for the four derivations and for F1–F3, each of which has a concrete run below. Medium for the proposed fixes: I checked them on E2 and on two extra programs (`Probe`, §7.2; `AddM1`, §8), nothing else.
5. **Not checked:** [Join] with holed sealed programs (E3), functions with two or more borrow arguments that return a borrow (sketch only, F4), [Split] on a neutral that is not an abstract value (F10), any metatheory.

## 0. Notation

- Environments: `{ x° ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ }`. `|` separates frames, oldest first. Types are omitted from bindings. The ghost `x°` sits in its own frame below the function's frame; that frame is "the caller's frame" for [Pop] (F7).
- `σ`, `τ`: abstract values for the contents of `x` and `y` at entry. `σ'`: the tail after the split `σ := S σ'`. `0` is `Z`, `1` is `S Z`.
- Callee parameters inside nested runs are renamed `x₁, y₁` (first nested frame), `x₂, y₂` (second). In [App] typing, the callee's parameters bound at the call site are `x', y'`.
- `_ᵢ ↦ borrow_ℓ v`: an anonymous pending binding created by [Pop].
- A **hole** is the `loan_k` that [Close] puts inside a backward sealed program when the call returns a borrow: a slot waiting for the final content of the returned `borrow_k`.
- Each machine step is one line: `Ω, term // [Rule] comment`. `stuck` marks a [Match] on a neutral inside a call.

Sealed-program abbreviations (the binders `c`, `r` are compared up to renaming):

```
U(v, w)  :=  ⌈let c = v; AddM &c w⌉                   : Unit   AddM's result (≡ () by [Seal] at Unit)
A(v, w)  :=  ⌈let c = v; AddM &c w; c⌉                 : Nat    AddM's effect: final content of the borrowed place
T(v)     :=  ⌈let c = v; let r = TailM &c; *r⌉         : Nat    TailM's result content: what the returned borrow points at
B(v)[h]  :=  ⌈let c = v; let r = TailM &c; *r := h; c⌉ : Nat    TailM's effect, given the final content h of the returned borrow
```

While the returned borrow `borrow_k` is live, the effect is `B(v)[loan_k]` (hole open). When `borrow_k` ends with content `w`, it becomes `B(v)[w]` (hole filled).

## 1. `TailM`

```
TailM : Π(x : &Nat). &Nat
TailM x := match *x { Z => x | S p => TailM &p }
```

### 1.1 Entry and split

```
{} ⊢ fix TailM (x : &Nat) : &Nat := match *x { Z => x | S p => TailM &p }  :  Π(x : &Nat). &Nat   // [Lam]
  recursion (RULES §6): the one recursive call passes &p, and p = (*x).1 is a pattern variable of a match on the parameter's content ✓
  Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ }                              // [Lam] &-parameter: the ghost holds loan_0, x holds borrow_0 of an abstract σ
  goal at entry: &Nat                                                   // nothing to run
  Ω₀ ⊢ match *x { Z => x | S p => TailM &p } : &Nat                     // [Split] content(Ω₀, *x) = σ is abstract
    arm Z, σ := Z: §1.2
    arm S, σ := S σ': §1.3
```

### 1.2 Z arm: hand back the borrow you were given

```
{ x° ↦ loan_0 | x ↦ borrow_0 Z } ⊢ match *x {…} ⇓ borrow_0 Z : &Nat ⊣ { x° ↦ loan_0 }
  { x° ↦ loan_0 | x ↦ borrow_0 Z },  match *x {…}    // [Match] content(*x) = Z: first arm
  { x° ↦ loan_0 | x ↦ borrow_0 Z },  x
  { x° ↦ loan_0 | x ↦ ⊥ },           borrow_0 Z      // [Read] x holds a borrow: moved out
  result type &Nat ≡ goal &Nat ✓
  { x° ↦ loan_0 },                   borrow_0 Z      // [Pop] x is ⊥: nothing to drop
```

Ledger: `loan_0` (in `x°`) ↔ `borrow_0` (the result). The function returns the very borrow it was given; its loan is still the caller's.

### 1.3 S arm: the recursive call is closed off, and [Pop] parks the parent borrow

```
{ x° ↦ loan_0 | x ↦ borrow_0 (S σ') } ⊢ match *x {…} ⇓ borrow_k T(σ') : &Nat ⊣ { x° ↦ loan_0, _₀ ↦ borrow_0 (S B(σ')[loan_k]) }
  { x° ↦ loan_0 | x ↦ borrow_0 (S σ') },                        match *x {…}         // [Match] content S σ': second arm, p := (*x).1
  { x° ↦ loan_0 | x ↦ borrow_0 (S σ') },                        TailM &(*x).1        // [App] typing, value from the machine:
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1) },                    TailM (borrow_1 σ')  // [Borrow] &(*x).1: content σ'; loan_1 stays in the tail, the S stays in x
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1) | x₁ ↦ borrow_1 σ' }, match *x₁ {…}        // [App] unfold the fix once, push a frame
    stuck                                                                             // [Match] content(*x₁) = σ'
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1) },                    TailM (borrow_1 σ')  // [Close] discard the partial run
      I = {1}, u₁ = σ', L = let c = σ', C = TailM &c; result type &Nat: fresh k
  { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[loan_k]) },             borrow_k T(σ')       // [Close] returns borrow_k ⌈L; let r = C; *r⌉; loan_1 filled with ⌈L; let r = C; *r := loan_k; c⌉
  result type: the codomain &Nat (no dependency) ≡ goal &Nat ✓
  { x° ↦ loan_0, _₀ ↦ borrow_0 (S B(σ')[loan_k]) },             borrow_k T(σ')       // [Pop] x is a borrow whose content contains loan_k (inside a sealed program, F2): it becomes a pending binding in the caller's frame
```

Ledger at the end: `loan_0` (in `x°`) ↔ `borrow_0` (in `_₀`); `loan_k` (the hole inside `B(σ')[·]` in `_₀`) ↔ `borrow_k` (the result). The chain is acyclic. When the caller ends `borrow_k` with content `w`, the hole becomes `w`, `_₀`'s content is loan-free, `_₀` ends, and `x° ↦ S B(σ')[w]`.

`TailM` is accepted. Nothing checks "lifetimes": returning a borrow of a local is caught by [Pop] ("a dropped owned binding must contain no loans"), and returning a borrow derived from the parameter goes through, as above.

## 2. `AddM'`

```
AddM' : Π(x : &Nat) (y : Nat). Unit
AddM' x y := let t = TailM x; *t := y
```

```
{} ⊢ λ(x : &Nat) (y : Nat). let t = TailM x; *t := y  :  Π(x : &Nat) (y : Nat). Unit                 // [Lam]
  Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ }
  goal at entry: Unit
  Ω₀ ⊢ let t = TailM x; *t := y ⇓ () : Unit ⊣ { x° ↦ B(σ)[τ] }
    { x° ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ },                    TailM x              // [Let] first the bound term; [App] typing
    { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ },                             TailM (borrow_0 σ)   // [Read] x holds a borrow: moved into the argument
    { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ },           match *x₁ {…}        // [App] unfold, push a frame
      stuck                                                                          // [Match] content(*x₁) = σ
    { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ },                             TailM (borrow_0 σ)   // [Close] discard; L = let c = σ, C = TailM &c; result &Nat: fresh k
    { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ },                       borrow_k T(σ)        // [Close] loan_0 filled with the holed effect program
    result type &Nat ✓
    { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k T(σ) },    *t := y              // [Let] bind t
    { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k T(σ) },    *t := τ              // [Read] y is borrow-free: copied
    { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k τ },       ()                   // [Assign] through t; the old content T(σ) is borrow-free and dropped
    { x° ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ },                            ()                   // [Let] drop t → [Pop] borrow_k's content τ is loan-free: it ends, the hole loan_k becomes τ
    result type Unit ≡ goal ✓
  { x° ↦ B(σ)[τ] },                                              ()                   // [Pop] x is ⊥, y is borrow-free
```

`AddM'` is accepted. Its effect on the caller is `B(σ)[τ] = ⌈let c = σ; let r = TailM &c; *r := τ; c⌉`: "take σ, borrow its tail, write τ there, give back the whole". The sealed program names `TailM`, not `AddM'`, because [Close] seals the innermost stuck call and `AddM'` itself never got stuck (§6.3 says why this matters).

## 3. Normal forms of the sealed programs (the [Seal] runs used later)

### 3.0 [Seal] as written never stops (F1)

A sealed program whose head call is stuck runs back to itself. Take `B(σ)[τ]`:

```
⟨{}, let c = σ; let r = TailM &c; *r := τ; c⟩
  { c ↦ σ },                                   let r = TailM &c; *r := τ; c   // [Let]
  { c ↦ loan_1 },                              TailM (borrow_1 σ)             // [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 σ },            match *x₁ {…}                  // [App]
    stuck                                                                     // [Match] σ
  { c ↦ B(σ)[loan_k] },                        borrow_k T(σ)                  // [Close] discard, fresh k
  { c ↦ B(σ)[loan_k], r ↦ borrow_k T(σ) },     *r := τ                        // [Let]
  { c ↦ B(σ)[loan_k], r ↦ borrow_k τ },        c                              // [Assign]
  { c ↦ B(σ)[τ], r ↦ ⊥ },                      c                              // [Reorg] c's content contains loan_k (inside a sealed program; F2: v0 only triggers on content *being* a loan): end borrow_k
  { c ↦ B(σ)[τ], r ↦ ⊥ },                      B(σ)[τ]                        // [Read] borrow-free: copied
  {},                                          B(σ)[τ]                        // [Let]×2 drop r (⊥), c (no loans)
completes with v = B(σ)[τ], the program we started from (up to renaming of c, r)
[Seal] as written: nf(B(σ)[τ]) = nf(v) = nf(B(σ)[τ]) = …   no end
```

The same happens for `U`, `A` and `T` (their runs are the inner steps of §3.3–3.5 with `σ` in place of `S σ'`). **Working reading used below (F1):** `nf(⌈t⌉)` is the value the run of `t` completes with, with values of type Unit replaced by `()`. Sealed programs created by [Close] during that run are normal by construction (their head call's body has just got stuck on exactly those argument values), so they are not re-run. Refinement re-normalises the sealed programs that mention the refined variable, innermost first.

### 3.1 `A(Z, τ) ≡ τ`

```
⟨{}, let c = Z; AddM &c τ; c⟩ ⇓ τ
  { c ↦ Z },                                    AddM &c τ; c       // [Let]
  { c ↦ loan_1 },                               AddM (borrow_1 Z) τ   // [Borrow]; τ is already a value
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z, y₁ ↦ τ },     match *x₁ {…}      // [App] unfold, push
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z, y₁ ↦ τ },     *x₁ := y₁          // [Match] content Z: first arm
  { c ↦ loan_1 | x₁ ↦ borrow_1 τ, y₁ ↦ τ },     ()                 // [Read] y₁ copied; [Assign] through x₁
  { c ↦ τ },                                    ()                 // [Pop] borrow_1's content τ is loan-free: ends into loan_1; y₁ dropped
  { c ↦ τ },                                    τ                  // [Let] (`;` discards ()), [Read] c copied
  {},                                           τ                  // [Let] drop c
```

### 3.2 `B(Z)[τ] ≡ τ`

```
⟨{}, let c = Z; let r = TailM &c; *r := τ; c⟩ ⇓ τ
  { c ↦ loan_1 },                    TailM (borrow_1 Z)   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z },  match *x₁ {…}        // [App]
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z },  x₁                   // [Match] content Z: first arm
  { c ↦ loan_1 | x₁ ↦ ⊥ },           borrow_1 Z           // [Read] moved
  { c ↦ loan_1 },                    borrow_1 Z           // [Pop]
  { c ↦ loan_1, r ↦ borrow_1 Z },    *r := τ              // [Let]
  { c ↦ loan_1, r ↦ borrow_1 τ },    c                    // [Assign]
  { c ↦ τ, r ↦ ⊥ },                  c                    // [Reorg] c's content is loan_1: end borrow_1 (content τ, loan-free)
  { c ↦ τ, r ↦ ⊥ },                  τ                    // [Read] copied
  {},                                τ                    // [Let]×2
```

### 3.3 `A(S σ', τ) ≡ S A(σ', τ)`

```
⟨{}, let c = S σ'; AddM &c τ; c⟩ ⇓ S A(σ', τ)
  { c ↦ loan_1 },                                                      AddM (borrow_1 (S σ')) τ   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ'), y₁ ↦ τ },                       match *x₁ {…}              // [App]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ'), y₁ ↦ τ },                       AddM &(*x₁).1 y₁           // [Match] content S σ': second arm
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2), y₁ ↦ τ },                   AddM (borrow_2 σ') τ       // [Borrow] the tail; [Read] y₁ copied
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2), y₁ ↦ τ | x₂ ↦ borrow_2 σ', y₂ ↦ τ }, match *x₂ {…}     // [App]
    stuck                                                                                          // [Match] σ'
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2), y₁ ↦ τ },                   AddM (borrow_2 σ') τ       // [Close] discard; L = let c = σ', C = AddM &c τ; result Unit
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S A(σ', τ)), y₁ ↦ τ },                 U(σ', τ)                   // [Close] returns U(σ', τ); loan_2 filled with A(σ', τ)
  { c ↦ S A(σ', τ) },                                                  U(σ', τ)                   // [Pop] borrow_1's content is loan-free: ends into loan_1; y₁ dropped
  { c ↦ S A(σ', τ) },                                                  S A(σ', τ)                 // [Let] (`;`), [Read] c copied
  {},                                                                  S A(σ', τ)                 // [Let] drop c
```

### 3.4 `B(S σ')[τ] ≡ S B(σ')[τ]` (runs `TailM` on `S σ'`, closes off the inner call on `σ'`)

```
⟨{}, let c = S σ'; let r = TailM &c; *r := τ; c⟩ ⇓ S B(σ')[τ]
  { c ↦ loan_1 },                                                     TailM (borrow_1 (S σ'))   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ') },                              match *x₁ {…}             // [App]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ') },                              TailM &(*x₁).1            // [Match] content S σ': second arm
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) },                          TailM (borrow_2 σ')       // [Borrow] the tail
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) | x₂ ↦ borrow_2 σ' },       match *x₂ {…}             // [App]
    stuck                                                                                       // [Match] σ'
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) },                          TailM (borrow_2 σ')       // [Close] discard; L = let c = σ', C = TailM &c; result &Nat: fresh k
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S B(σ')[loan_k]) },                   borrow_k T(σ')            // [Close] loan_2 filled with the holed effect program
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[loan_k]) },                    borrow_k T(σ')            // [Pop] x₁'s content contains loan_k: pending binding in the caller's (top) frame
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[loan_k]), r ↦ borrow_k T(σ') }, *r := τ                  // [Let]
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[loan_k]), r ↦ borrow_k τ },    c                         // [Assign] through r; T(σ') dropped
    // [Reorg] c's content is loan_1: end borrow_1. Its content contains loan_k, so end borrow_k first (recursive clause; needs F2 to see inside the sealed program)
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[τ]), r ↦ ⊥ },                  c                         // [Reorg] end borrow_k: content τ is loan-free; the hole becomes τ
  { c ↦ S B(σ')[τ], _₁ ↦ ⊥, r ↦ ⊥ },                                  c                         // [Reorg] end borrow_1 (the same step [Pop]'s eager clause for _₁ would take)
  { c ↦ S B(σ')[τ], _₁ ↦ ⊥, r ↦ ⊥ },                                  S B(σ')[τ]                // [Read] copied
  {},                                                                 S B(σ')[τ]                // [Let] drop r; drop c and _₁
```

Ledger through the run: `loan_1` (c) ↔ `borrow_1` (x₁, then `_₁`); `loan_2` (in `borrow_1`'s content) ↔ `borrow_2` (argument, consumed by [Close]); `loan_k` (hole inside `B(σ')[·]` in `_₁`) ↔ `borrow_k` (r). Everything ends by the final read of `c`.

This is the step the whole example turns on. The outer program's continuation `*r := τ` is not kept in the output: it writes `τ` through the borrow that the *inner* stuck call returned, which fills the inner call's hole. The `S` stays outside, carried by the pending binding `_₁`.

### 3.5 `T(S σ') ≡ T(σ')` (used in §8)

```
⟨{}, let c = S σ'; let r = TailM &c; *r⟩ ⇓ T(σ')
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[loan_k]), r ↦ borrow_k T(σ') },  *r                  // §3.4's steps up to and including binding r
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[loan_k]), r ↦ borrow_k T(σ') },  T(σ')               // [Read] *r: content T(σ') is borrow-free: copied; r keeps its borrow
  { c ↦ loan_1, _₁ ↦ borrow_1 (S B(σ')[T(σ')]) },                       T(σ')               // [Let] drop r → [Pop] borrow_k ends; the hole becomes T(σ') (nothing was written)
  { c ↦ S B(σ')[T(σ')], _₁ ↦ ⊥ },                                       T(σ')               // [Pop] _₁'s content is now loan-free: it ends into loan_1
  {},                                                                   T(σ')               // [Let] drop c (no loans)
```

## 4. `AddMEq`

```
AddMEq : Π(x : &Nat) (y : Nat). Id Unit (AddM x y) (AddM' x y)
AddMEq x y := match *x { Z => refl | S p => AddMEq &p y }
```

### 4.1 Entry goal

```
{} ⊢ fix AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM x y) (AddM' x y) := match *x { Z => refl | S p => AddMEq &p y }   // [Lam]
  recursion (RULES §6): AddMEq &p y with p = (*x).1 ✓
  Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ }
  goal at entry: Ω₀ ⊢ Id Unit (AddM x y) (AddM' x y) ≡ G₀
    W = W(AddM x y, AddM' x y) = {x°}     // no &_ and no := in either term; x is the only free borrow-typed variable; loan_0 sits in the ghost x°
    T_W = Nat                             // the ghost's type
    ⟦AddM x y⟧^W  = ((), A(σ, τ))         // run (a)
    ⟦AddM' x y⟧^W = ((), B(σ)[τ])         // run (b)
    Id Unit (AddM x y) (AddM' x y)
      ≡ Eq (Unit × Nat) ((), A(σ, τ)) ((), B(σ)[τ])     // Id computes
      ≡ Eq Unit () () ∧ Eq Nat A(σ, τ) B(σ)[τ]            // Eq on pairs
      ≡ ⊤ ∧ Eq Nat A(σ, τ) B(σ)[τ]                         // Eq Unit
      ≡ Eq Nat A(σ, τ) B(σ)[τ]   =: G₀                     // ⊤ ∧ P ≡ P
```

Run (a), on a private copy of Ω₀:

```
⟨Ω₀, AddM x y⟩
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ },                              AddM (borrow_0 σ) τ   // [Read] x moved, y copied
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ, y₁ ↦ τ },    match *x₁ {…}         // [App]
    stuck                                                                             // [Match] σ
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ },                              AddM (borrow_0 σ) τ   // [Close] discard; L = let c = σ, C = AddM &c τ; result Unit
  { x° ↦ A(σ, τ) | x ↦ ⊥, y ↦ τ },                             U(σ, τ)               // [Close] returns U(σ, τ); loan_0 filled with A(σ, τ)
  resolve: no live borrows
  observation: (U(σ, τ), x°) = ((), A(σ, τ))                                          // [Seal] at Unit
```

Run (b), on a private copy of Ω₀:

```
⟨Ω₀, AddM' x y⟩
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ },                                               AddM' (borrow_0 σ) τ            // [Read]
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ, y₁ ↦ τ },                     let t = TailM x₁; *t := y₁      // [App] unfold, push
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                              TailM (borrow_0 σ)              // [Let], [Read] x₁ moved
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ | x₂ ↦ borrow_0 σ },            match *x₂ {…}                   // [App]
    stuck                                                                                                          // [Match] σ
  { x° ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                              TailM (borrow_0 σ)              // [Close] discard only TailM's partial run (the innermost stuck call); fresh k
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                        borrow_k T(σ)                   // [Close]
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k T(σ) },     *t := y₁                        // [Let]
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k τ },        ()                              // [Read] y₁ copied, [Assign]
  { x° ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                             ()                              // [Let] drop t: borrow_k ends, the hole becomes τ
  { x° ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ },                                              ()                              // [Pop] AddM' frame
  resolve: no live borrows
  observation: ((), B(σ)[τ])
```

### 4.2 Split

```
Ω₀ ⊢ match *x { Z => refl | S p => AddMEq &p y } : G₀     // [Split] content(Ω₀, *x) = σ
  arm Z: σ := Z applied to Ω₀ and G₀   (§4.3)
  arm S: σ := S σ' applied to Ω₀ and G₀ (§4.4)
```

### 4.3 Z arm

```
{ x° ↦ loan_0 | x ↦ borrow_0 Z, y ↦ τ } ⊢ refl : G_Z
  G_Z = G₀[σ := Z] = Eq Nat A(Z, τ) B(Z)[τ]     // Refinement: both sealed programs mention σ, re-normalised
      ≡ Eq Nat τ τ                               // §3.1, §3.2
  [Match] content(*x) = Z: first arm, refl
  refl : Eq Nat τ τ ≡ G_Z ✓
```

Sanity check (adequacy on this instance): re-running the `Id` from the refined environment gives the same thing. `AddM x y` unfolds, writes `τ` over `Z` through `borrow_0`, and the frame's pop ends `borrow_0` into `x°`: `((), τ)`. `AddM' x y`: `TailM` unfolds and returns `borrow_0 Z` itself, `*t := τ`, dropping `t` ends `borrow_0` into `x°`: `((), τ)`.

### 4.4 S arm

The refined goal:

```
Ω_S = { x° ↦ loan_0 | x ↦ borrow_0 (S σ'), y ↦ τ }
G_S = G₀[σ := S σ'] = Eq Nat A(S σ', τ) B(S σ')[τ]     // Refinement: both sealed programs mention σ, re-normalised
    ≡ Eq Nat (S A(σ', τ)) (S B(σ')[τ])                   // §3.3; §3.4 (runs TailM on S σ', closes off the inner call on σ')
    ≡ Eq Nat A(σ', τ) B(σ')[τ]                            // Eq Nat (S a) (S b) ≡ Eq Nat a b
```

The recursive call:

```
Ω_S ⊢ match *x { Z => refl | S p => AddMEq &p y } : G_S
  [Match] content(*x) = S σ': second arm, p := (*x).1
  Ω_S ⊢ AddMEq &(*x).1 y ⇓ ⌈let c = σ'; AddMEq &c τ⌉ : IH ⊣ Ω_out           // [App]
    arguments:
      { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ },   borrow_1 σ'        // [Borrow] &(*x).1: loan_1 in the tail, the S stays in x
      { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ },   τ                  // [Read] y copied
    result type: the codomain at the call site, parameters bound to the arguments:
      Ω_IH = { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ borrow_1 σ', y' ↦ τ }
      IH = Ω_IH ⊢ Id Unit (AddM x' y') (AddM' x' y')
        W = {x°}                         // x' is the only free borrow-typed variable. Its loan_1 sits in x's content; x is a borrow whose loan_0 sits in the ghost x°, which is owned. (F5 on the wording.)
        T_W = Nat
        ⟦AddM x' y'⟧^W  = ((), S A(σ', τ))   // run (c)
        ⟦AddM' x' y'⟧^W = ((), S B(σ')[τ])   // run (d)
        IH ≡ Eq (Unit × Nat) ((), S A(σ', τ)) ((), S B(σ')[τ])
           ≡ Eq Nat (S A(σ', τ)) (S B(σ')[τ])      // Eq on pairs, Eq Unit, ⊤ ∧ P
    result value (the machine runs the proof term too):
      { … | x ↦ borrow_0 (S loan_1), y ↦ τ | x₁ ↦ borrow_1 σ', y₁ ↦ τ },  match *x₁ {…}    // [App] unfold AddMEq
        stuck                                                                               // [Match] σ'
      { x° ↦ loan_0 | x ↦ borrow_0 (S ⌈let c = σ'; AddMEq &c τ; c⌉), y ↦ τ },  ⌈let c = σ'; AddMEq &c τ⌉   // [Close] loan_1 filled with the proof's "effect" (F8)
  conversion: IH ≡ G_S. Both are Eq Nat (S A(σ', τ)) (S B(σ')[τ]), symbol for symbol (up to renaming the binders c, r) ✓
```

Run (c), on a private copy of `Ω_IH`:

```
⟨Ω_IH, AddM x' y'⟩
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                          AddM (borrow_1 σ') τ   // [Read]
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ | x₁ ↦ borrow_1 σ', y₁ ↦ τ }, match *x₁ {…}        // [App]
    stuck                                                                                                             // [Match] σ'
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                          AddM (borrow_1 σ') τ   // [Close] discard; L = let c = σ', C = AddM &c τ
  { x° ↦ loan_0 | x ↦ borrow_0 (S A(σ', τ)), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                        U(σ', τ)               // [Close] loan_1 filled with A(σ', τ)
  resolve: end borrow_0 (content S A(σ', τ), loan-free) → x° ↦ S A(σ', τ)
  observation: ((), S A(σ', τ))
```

Run (d), on a private copy of `Ω_IH`:

```
⟨Ω_IH, AddM' x' y'⟩
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                                      AddM' (borrow_1 σ') τ          // [Read]
  { … | x' ↦ ⊥, y' ↦ τ | x₁ ↦ borrow_1 σ', y₁ ↦ τ },                                                      let t = TailM x₁; *t := y₁     // [App]
  { … | x' ↦ ⊥, y' ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                                                                TailM (borrow_1 σ')            // [Let], [Read] x₁ moved
  { … | x₁ ↦ ⊥, y₁ ↦ τ | x₂ ↦ borrow_1 σ' },                                                              match *x₂ {…}                  // [App]
    stuck                                                                                                                                   // [Match] σ'
  { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                    TailM (borrow_1 σ')            // [Close] discard; L = let c = σ', C = TailM &c; fresh k
  { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[loan_k]), y ↦ τ | x' ↦ ⊥, y' ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },             borrow_k T(σ')                 // [Close] loan_1 filled with the holed effect program
  { … | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k T(σ') },                                                             *t := y₁                       // [Let]
  { … | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k τ },                                                                 ()                             // [Read] y₁ copied, [Assign]
  { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[τ]), y ↦ τ | x' ↦ ⊥, y' ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                  ()                             // [Let] drop t: borrow_k ends, the hole becomes τ
  { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[τ]), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                                   ()                             // [Pop] AddM' frame
  resolve: end borrow_0 (content S B(σ')[τ], loan-free) → x° ↦ S B(σ')[τ]
  observation: ((), S B(σ')[τ])
```

Ledger in run (d): `loan_0` (x°) ↔ `borrow_0` (caller's x, holding the `S`); `loan_1` (tail of that `S`) ↔ `borrow_1` (x', then x₁, then x₂, consumed by [Close]); `loan_k` (hole in `B(σ')[·]`) ↔ `borrow_k` (t). Ending order: `borrow_k` when `t` drops, then `borrow_0` at resolve.

Both arms check, so `AddMEq` is accepted with the proof exactly as written: no congruence lemma, no `cong S`, no auxiliary fact about `TailM`.

## 5. `AddMEqOwned`

```
AddMEqOwned : Π(x : Nat). Id Unit (AddM &x 0) (AddM' &x 0)
AddMEqOwned x := AddMEq &x 0
```

```
{} ⊢ λ(x : Nat). AddMEq &x 0 : Π(x : Nat). Id Unit (AddM &x 0) (AddM' &x 0)      // [Lam]
  Ω₀ = { x ↦ σ }                                                                  // owned parameter: no ghost
  goal at entry: Ω₀ ⊢ Id Unit (AddM &x 0) (AddM' &x 0) ≡ G
    W = {x}              // x appears under &_; its root owned place is x
    ⟦AddM &x 0⟧^W:
      { x ↦ loan_1 },                                    AddM (borrow_1 σ) Z      // [Borrow]; 0 is the value Z
      { x ↦ loan_1 | x₁ ↦ borrow_1 σ, y₁ ↦ Z },          match *x₁ {…}            // [App]
        stuck                                                                     // [Match] σ
      { x ↦ loan_1 },                                    AddM (borrow_1 σ) Z      // [Close] discard; L = let c = σ, C = AddM &c Z
      { x ↦ A(σ, Z) },                                   U(σ, Z)                  // [Close]
      observation ((), A(σ, Z))
    ⟦AddM' &x 0⟧^W:
      { x ↦ loan_1 },                                    AddM' (borrow_1 σ) Z             // [Borrow]
      { x ↦ loan_1 | x₁ ↦ borrow_1 σ, y₁ ↦ Z },          let t = TailM x₁; *t := y₁       // [App]
      { x ↦ loan_1 | x₁ ↦ ⊥, y₁ ↦ Z },                   TailM (borrow_1 σ)               // [Let], [Read]
      { x ↦ loan_1 | x₁ ↦ ⊥, y₁ ↦ Z | x₂ ↦ borrow_1 σ }, match *x₂ {…}                    // [App]
        stuck                                                                             // [Match] σ
      { x ↦ loan_1 | x₁ ↦ ⊥, y₁ ↦ Z },                   TailM (borrow_1 σ)               // [Close] discard; fresh k
      { x ↦ B(σ)[loan_k] | x₁ ↦ ⊥, y₁ ↦ Z },             borrow_k T(σ)                    // [Close]
      { x ↦ B(σ)[loan_k] | x₁ ↦ ⊥, y₁ ↦ Z, t ↦ borrow_k Z }, ()                            // [Let], [Read] y₁ copied, [Assign]
      { x ↦ B(σ)[Z] | x₁ ↦ ⊥, y₁ ↦ Z },                  ()                               // [Let] drop t: the hole becomes Z
      { x ↦ B(σ)[Z] },                                   ()                               // [Pop]
      observation ((), B(σ)[Z])
    G ≡ Eq (Unit × Nat) ((), A(σ, Z)) ((), B(σ)[Z]) ≡ Eq Nat A(σ, Z) B(σ)[Z]
  Ω₀ ⊢ AddMEq &x 0 : IH                                                          // [App]
    { x ↦ loan_1 }, arguments borrow_1 σ and Z                                   // [Borrow]
    Ω_IH = { x ↦ loan_1 | x' ↦ borrow_1 σ, y' ↦ Z }
    W = {x}              // x' is free and borrow-typed; its loan_1 sits in the owned x
    ⟦AddM x' y'⟧^W  = ((), A(σ, Z))       // the run above from its second line, with x' moved instead of &x borrowed
    ⟦AddM' x' y'⟧^W = ((), B(σ)[Z])       // likewise
    IH ≡ Eq Nat A(σ, Z) B(σ)[Z]
  IH ≡ G, symbol for symbol ✓
```

The two footprint clauses (the syntactic `&x` in the goal, the owner of the borrow-typed parameter in the IH) pick the same place. `AddMEqOwned` is accepted. (The call also runs `AddMEq` and leaves `x ↦ ⌈let c = σ; AddMEq &c Z; c⌉`; see F8.)

## 6. The central question: do the goal and the IH land on the same normal form?

**Yes.** In `AddMEq`'s S arm both are `Eq Nat (S A(σ', τ)) (S B(σ')[τ])`, so the conversion is syntactic identity and the proof is bare recursion.

### 6.1 Why the loan-hole form makes them meet

The two sides reach `B(σ')[τ]` by different routes.

- **IH side (run (d)).** At the call site the caller's environment already holds `x ↦ borrow_0 (S loan_1)`. `TailM` on `borrow_1 σ'` gets stuck at once and is closed off: `loan_1` receives `B(σ')[loan_k]`. Then `AddM'`'s *real code* `*t := y` writes `τ` through `borrow_k`, and dropping `t` fills the hole: `B(σ')[τ]`. The `S` is the caller's, sitting in `borrow_0`.
- **Goal side (§3.4).** Refinement re-runs `B(S σ')[τ]` from its source. `TailM` on `S σ'` takes one step, and the inner `TailM` on `σ'` is closed off with a *new* hole `k`. Now the outer program's own continuation `*r := τ` writes `τ` through the new `borrow_k`, and ending it fills the new hole: `B(σ')[τ]`. The `S` is carried out of `TailM`'s frame by the pending binding `_₁` that [Pop] created.

The two meet because a filled hole records only the returned borrow's **final content**, not the code that produced it. On the goal side the writer is the sealed program's continuation, on the IH side it is `AddM'`'s body; both write `τ`, so both holes hold `τ`. Put differently: re-running a sealed program *moves its continuation into the inner stuck call*, which is exactly what the machine does to `AddM'`'s continuation at the call site. The borrow structure does the congruence twice: once as the caller's `borrow_0 (S loan_1)` and once as the pending `_₁ ↦ borrow_1 (S …)`.

### 6.2 What this relies on

1. Refinement re-runs a sealed program from source (so the continuation is re-executed, not frozen).
2. The hole is filled with the final content only.
3. [Pop] parks a borrow whose content still has a loan as a pending binding, so the `S` survives the pop of `TailM`'s frame.
4. The IH's footprint is the *caller's* root `x°` (via the owner chain `x' → loan_1 in x → loan_0 in x°`), not a ghost of the callee.
5. [Close] seals the *innermost* stuck call. This one is load-bearing: if the outer `AddM'` call were sealed instead, the IH would contain `S ⌈let c = σ'; AddM' &c τ; c⌉`, while re-running the goal's `⌈let c = S σ'; AddM' &c τ; c⌉` would get stuck inside the same outer call and re-seal it with no `S` surfaced; the two would not meet. D4's "innermost" is confirmed by E2.

## 7. The hole questions

### 7.1 When a hole is filled, is the result well-defined and canonical?

**In E2, yes.**

- *Well-defined.* `loan_k` occurs once (`TailM` has one borrow argument), and `borrow_k` ends only once its content is loan-free ([Reorg]'s precondition, [Pop]'s condition), so filling substitutes one loan-free value for one occurrence.
- *No re-normalisation is ever needed after filling.* The hole sits in the continuation `*r := h`, never in the head call's arguments. So filling cannot unstick the head call, and a filled program whose head was stuck is still a normal form (§3.0 shows it runs to itself). Filling is plain substitution.
- *Canonical with respect to how the content was produced.* Only the final content matters. For example `let t = TailM x; *t := 5; *t := y` gives `t ↦ borrow_k 5` then `t ↦ borrow_k τ` ([Assign] twice); dropping `t` fills the hole with `τ`: the same `B(σ)[τ]` as `AddM'`.
- *Canonical with respect to ending order.* The hole is reachable only by ending `borrow_k`, so no other ending can see or change it first.
- *Not complete.* "Borrow the tail and write nothing" gives `B(σ)[T(σ)]`, which is not definitionally `σ`. The equation is provable by the same bare recursion (§8.2). This is an ordinary missing definitional equation, like Lean's `0 + n`, not a defect.

**In general, no (F4).** With two or more borrow arguments and a borrow result, [Close] writes the same `loan_k` into every backward program (`⌈L; let r = C; *r := loan_k; cᵢ⌉` for each `i ∈ I`). "The hole becomes w" must then mean *every* occurrence, so the hole is a variable rather than a linear loan, and "the owner" of `borrow_k` is not unique.

### 7.2 Can a sealed program with an unfilled hole ever be compared or normalised?

**Compared: no.** Formed types come from two places. Observations resolve every borrow first, so every hole is filled. Reads of a place end the loans in its content first (with F2), so a read never returns an open hole. An open hole therefore lives only in Ω, never in a formed type. (This is an argument from the rules, not a proof.)

**Normalised: yes, and v0 is undefined there.** Refinement re-normalises *every* sealed program that mentions the refined variable, including holed ones still sitting in Ω. This happens at any [Split] while a returned borrow is live:

```
Probe : Π(n : Nat). Unit
Probe n := let m = n; let t = TailM &m; match n { Z => () | S q => () }
```

```
{ n ↦ σ },                                              let m = n; …             // [Lam]
{ n ↦ σ, m ↦ σ },                                       TailM &m                 // [Let], [Read] n copied
{ n ↦ σ, m ↦ loan_1 },                                  TailM (borrow_1 σ)       // [Borrow]
    stuck                                                                        // [App], [Match] σ
{ n ↦ σ, m ↦ B(σ)[loan_k] },                            borrow_k T(σ)            // [Close] fresh k
{ n ↦ σ, m ↦ B(σ)[loan_k], t ↦ borrow_k T(σ) },         match n {…}              // [Let]
  [Split] content(n) = σ. Arm Z: refine σ := Z in Ω; m's B(σ)[loan_k] and t's T(σ) mention σ and are re-normalised:
  ⟨{}, let c = Z; let r = TailM &c; *r := loan_k; c⟩
    { c ↦ loan_1, r ↦ borrow_1 Z },        *r := loan_k        // as in §3.2
    { c ↦ loan_1, r ↦ borrow_1 loan_k },   c                   // [Assign] the embedded value loan_k
    [Reorg] c's content is loan_1: end borrow_1. Its content loan_k is a loan: end borrow_k first. Find the unique borrow_k: there is none in this run (it is t's, outside the sealed program).   ✗ undefined
```

**Fix (F3):** in a [Seal] run, a loan whose borrow is not in the run's environment is *inert*: it behaves as an abstract value (it counts as loan-free, is copied, and is never ended). With that:

```
    { c ↦ loan_1, r ↦ borrow_1 loan_k },   c
    { c ↦ loan_k, r ↦ ⊥ },                 c          // [Reorg] end borrow_1; its content, the inert loan_k, counts as loan-free
    {},                                    loan_k     // [Read] (inert: copied like an abstract value), [Let]×2
  so B(Z)[loan_k] ≡ loan_k; and T(Z) ≡ Z (the §3.2 run up to binding r, then *r copies Z and dropping r gives c back its Z):
  Arm Z environment: { n ↦ Z, m ↦ loan_k, t ↦ borrow_k Z }
```

This is exactly (up to renaming the loan) the environment that running `let t = TailM &m` directly on `m = Z` produces (`TailM` hands back the borrow it was given, so `m` holds the loan). In arm S the same fix gives `B(S σ')[loan_k] ≡ S B(σ')[loan_k]` (the §3.4 run with the inert `loan_k` for `τ`; the inner hole receives `loan_k`) and `T(S σ') ≡ T(σ')`. Direct execution from `m = S σ'` gives `m ↦ loan_1, _ ↦ borrow_1 (S B(σ')[loan_k]), t ↦ borrow_k T(σ')`, which is the same environment once the pending `borrow_1` is ended ([Reorg] allows ending a loan at any time). So with the fix, refinement agrees with running the refined program, a hole is a variable, and filling a hole is substitution for that variable. Canonicity of filling then reduces to the RULES §7 adequacy conjecture (the machine commutes with substitution), with no new metatheory.

### 7.3 Is `*r` in `⌈L; let r = C; *r⌉` a legal read?

**Yes.** §3.5 runs it. `r` holds `borrow_k v` with `v` borrow-free (a sealed `Nat`), so [Read] of `*r` copies `v` and `r` keeps its borrow. At the end of `let r`, dropping `r` ends `borrow_k`; the hole in `c` receives the unchanged `v`; `c` then contains no loans and its drop is legal. No `⊥` is read, nothing is moved out of a borrow, and no loan is outstanding when an owned binding is dropped. Order matters and is right: `r` is dropped before `c` because `let r` is nested inside `let c`.

## 8. Two extra checks: reading through the returned borrow

Both are also bare recursion. They exercise `T` (the content read through the returned borrow) together with the hole.

### 8.1 `AddM1`: read, then write back through the returned borrow

```
AddM1 : Π(x : &Nat). Id Unit (AddM x 1) (let t = TailM x; *t := S *t)
AddM1 x := match *x { Z => refl | S p => AddM1 &p }
```

```
Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ }
W = {x°}          // x is free and borrow-typed. `*t` is on the left of :=, but t is local to the term (F9: v0 does not say to skip it)
⟦AddM x 1⟧ = ((), A(σ, 1))                     // run (a) with 1 for τ
⟦let t = TailM x; *t := S *t⟧:
  { x° ↦ loan_0 | x ↦ ⊥ },                               TailM (borrow_0 σ)    // [Let], [Read] x moved
    stuck                                                                      // [App], [Match] σ
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥ },                         borrow_k T(σ)         // [Close] fresh k
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, t ↦ borrow_k T(σ) },      *t := S *t            // [Let]
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, t ↦ borrow_k T(σ) },      *t := S T(σ)          // [Read] *t: borrow-free content, copied
  { x° ↦ B(σ)[loan_k] | x ↦ ⊥, t ↦ borrow_k (S T(σ)) },  ()                    // [Assign]
  { x° ↦ B(σ)[S T(σ)] | x ↦ ⊥ },                         ()                    // [Let] drop t: the hole becomes S T(σ)
  observation ((), B(σ)[S T(σ)])
G₀ ≡ Eq Nat A(σ, 1) B(σ)[S T(σ)]
arm Z:  A(Z, 1) ≡ 1 (§3.1);  B(Z)[S T(Z)] ≡ B(Z)[S Z] ≡ S Z  (innermost first: T(Z) ≡ Z, §7.2; then §3.2)
        G_Z ≡ Eq Nat 1 1;  refl ✓
arm S:  A(S σ', 1) ≡ S A(σ', 1) (§3.3);  B(S σ')[S T(S σ')] ≡ B(S σ')[S T(σ')] (§3.5) ≡ S B(σ')[S T(σ')] (§3.4 with S T(σ') for τ)
        G_S ≡ Eq Nat (S A(σ', 1)) (S B(σ')[S T(σ')])
        IH at Ω_IH = { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1) | x' ↦ borrow_1 σ' }:
          left:  run (c) with 1 for τ → ((), S A(σ', 1))
          right: { … x ↦ borrow_0 (S loan_1) | x' ↦ ⊥ },                       TailM (borrow_1 σ')   // [Let], [Read]
                   stuck                                                                             // [App], [Match] σ'
                 { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[loan_k]) | x' ↦ ⊥ },    borrow_k T(σ')        // [Close]
                 { …, t ↦ borrow_k (S T(σ')) },                                ()                    // [Let], [Read] *t copied, [Assign]
                 { x° ↦ loan_0 | x ↦ borrow_0 (S B(σ')[S T(σ')]) | x' ↦ ⊥ },   ()                    // [Let] drop t
                 resolve: x° ↦ S B(σ')[S T(σ')]  → ((), S B(σ')[S T(σ')])
          IH ≡ Eq Nat (S A(σ', 1)) (S B(σ')[S T(σ')]) ≡ G_S ✓
```

Note: refinement must normalise the value in the hole (`T(S σ')`) as well as the program around it. v0's [Seal] does ("`t` with its embedded values normalised").

### 8.2 `TailNoop`: borrowing the tail and writing nothing changes nothing

```
TailNoop : Π(x : &Nat). Id Unit (let t = TailM x; ()) ()
TailNoop x := match *x { Z => refl | S p => TailNoop &p }
```

```
Ω₀ = { x° ↦ loan_0 | x ↦ borrow_0 σ },  W = {x°}
left:  as in 8.1 without the assignment: dropping t fills the hole with the unchanged T(σ) → ((), B(σ)[T(σ)])
right: () ; resolve: end borrow_0 → x° ↦ σ → ((), σ)
G₀ ≡ Eq Nat B(σ)[T(σ)] σ
arm Z:  B(Z)[T(Z)] ≡ B(Z)[Z] ≡ Z;  G_Z ≡ Eq Nat Z Z;  refl ✓
arm S:  B(S σ')[T(S σ')] ≡ B(S σ')[T(σ')] ≡ S B(σ')[T(σ')];  G_S ≡ Eq Nat (S B(σ')[T(σ')]) (S σ')
        IH at Ω_IH = { x° ↦ loan_0 | x ↦ borrow_0 (S loan_1) | x' ↦ borrow_1 σ' }:
          left:  [Close] fills loan_1 with B(σ')[loan_k]; dropping t fills the hole with T(σ'); resolve → x° ↦ S B(σ')[T(σ')]
          right: (); resolve ends borrow_1 (σ' back into loan_1), then borrow_0 → x° ↦ S σ'
          IH ≡ Eq Nat (S B(σ')[T(σ')]) (S σ') ≡ G_S ✓
```

## 9. Findings

Each: where in RULES.md, what I assumed, simplest fix. F1–F3 affect E2 directly; the rest are wording or lie just outside E2.

- **F1. [Seal] never stops.** §3 [Seal], "if it completes with v, the result is nf(v)". Every sealed program whose head call is stuck runs back to itself (§3.0), so `nf` recurses forever; since [Close] turns every stuck call into a value, the "otherwise" branch never fires. *Assumed:* `nf(⌈t⌉)` is the run's value with Unit values replaced by `()`, and sealed programs created by [Close] in that run are not re-run. *Fix:* "the result is `v` (at type Unit, `()`). Sealed programs made by [Close] are normal by construction; refinement re-runs those that mention the refined variable, innermost first." Probably also hit by E1.
- **F2. Loans inside sealed programs are invisible.** §2 "borrow-free"; §3 [Reorg] ("whose content … is `loan_ℓ`", and "w must itself contain no loans"); [Pop] ("content still contains loans"); [Read]. E2 needs "contains" to see inside sealed programs at `TailM`'s [Pop] (§1.3) and when ending `borrow_1` in §3.4. The trigger ("is" vs "contains") also breaks an ordinary program: in `λ(n : Nat). let m = n; let t = TailM &m; *t := 5; m`, the final read of `m` finds `B(σ)[loan_k]`, which is neither borrow-free (so no copy) nor a borrow (so no move), and [Reorg] does not fire because the content is not itself a loan. Run concretely (e.g. `n = S Z`), the same program is fine, because the loans are then on the path (`m ↦ loan_1`). *Fix:* say "contains" everywhere, including inside sealed programs, and let [Reorg] fire when the accessed content contains `loan_ℓ` anywhere.
- **F3. A sealed program with an open hole cannot be normalised.** §3 [Seal] and Refinement. This happens at any [Split] on a variable that a live holed program mentions (`Probe`, §7.2): the [Seal] run tries to end `borrow_k`, which is outside the run. *Fix:* "in a [Seal] run, a loan whose borrow is not in the run's environment is inert and behaves as an abstract value". Then `B(Z)[loan_k] ≡ loan_k`, refinement agrees with direct execution, a hole is a variable, and filling is substitution (canonicity of filling = the adequacy conjecture of RULES §7).
- **F4. With two or more borrow arguments the hole is duplicated.** §3 [Close], second bullet; §4 "the owner". The same `loan_k` goes into every `⌈L; let r = C; *r := loan_k; cᵢ⌉`, so "the hole becomes w" must fill every occurrence (else a hole outlives its borrow), and `borrow_k` has several owners, so `W` must take all of them. This is D5's own revisit condition ("the footprint misses writes through a function returning a borrow"). I did not find a bad derivation: once a [Split] decides which argument the result points into, F3's refinement leaves the hole in one owner only, and before that both owners' programs differ syntactically whenever the hole's value does. *Fix:* fill every occurrence; `owner(borrow_k)` is the set of owned places containing an occurrence. Not derived in full (e.g. `pick (a b : &Nat) (n : Nat) : &Nat := match n { Z => a | S _ => b }`).
- **F5. "Owner" is vacuous as worded.** §4 Footprint: "the owned place that holds its loan once all borrows in Ω are ended": once all borrows are ended there are no loans. *Assumed (and used for the IH, §4.4):* follow the chain. Find the binding whose content contains `loan_ℓ` (possibly inside a sealed program or a pending binding); if that binding is itself a borrow, repeat with its loan; stop at an owned variable or a ghost. *Fix:* state it that way.
- **F6. "Restore Ω to just before the call" (§3 [Close]).** It must mean *after* the arguments were evaluated (borrow arguments already moved out of their variables); restoring to before argument evaluation would leave `x ↦ borrow_0 σ` alongside a filled `loan_0`. *Fix:* "restore Ω to its state after the arguments were evaluated".
- **F7. Where frames and pending bindings live.** §5 [Lam] does not say which frame the ghost `x°` is in, and [Pop] sends pending bindings to "the caller's frame". *Assumed:* the ghost is in a frame below the function's frame that is never popped (in `TailM` it still holds `loan_0` at the end, §1.3, and popping it would be rejected), and in a [Seal] run the caller's frame is the run's top frame. *Fix:* say so in [Lam] and [Pop]. Note: [Pop]'s eager clause ("a pending binding ends as soon as its content becomes loan-free") is load-bearing and should stay: in §3.5, `c` still holds `loan_1` when it is dropped unless the pending `_₁` has already ended, and [Pop] would then reject the drop.
- **F8. The checker runs proofs.** §5 [App]: "the result value comes from the machine". In `AddMEq`'s S arm (§4.4) and in `AddMEqOwned` (§5), the call to the lemma `AddMEq` gets stuck and is closed off, so the borrowed place is overwritten with `⌈let c = σ'; AddMEq &c τ; c⌉`. As far as the checker knows, citing a lemma that takes a borrow changes the borrowed place. It is harmless in E2 (the arm's output environment is never observed), but a proof that cites such a lemma and then states something about that place gets stuck. *Candidate fix:* a call whose result type is a proposition is not run: evaluate its arguments and end its borrow arguments unchanged. This is Lean's behaviour and is consistent if proofs are erased at runtime.
- **F9. Footprint of places rooted in the term's own locals.** §4 Footprint: "the root owned place of every place … on the left of :=". In `let t = TailM x; *t := S *t` (§8.1) the place `*t` is rooted in `t`, which does not exist in Ω when `W` is computed. *Assumed:* skip it; `x`'s owner already covers the write. *Fix:* "free places only; writes through term-local borrows are covered by the owners of the term's free borrow-typed variables".
- **F10. [Split] on a neutral that is not an abstract value.** §5 [Split] defines refinement only for `σ := Z | S σ'`. Returned borrows make `match *t {…}` with `content(*t) = T(σ)` natural (the tail is always `Z`, but the checker sees `T(σ)`). Not needed for E2. The usual answer is to generalise the neutral to a fresh `σ` with an equation; not designed here.

### Which decision this points at

F2, F3 and F4 have one cause: D4 represents the hole as a **loan** placed inside a sealed program, and loans are linear markers that [Reorg] must pair with a unique borrow in the current environment. Every problem above is a place where the hole needs to behave like a **variable**: it is copied into several programs (F4), it survives into a run that does not contain its borrow (F3), and it has to be found inside syntax (F2). The minimal change keeps D4 and changes only the hole: [Close] mints a fresh variable `h_k` tied to `borrow_k`; ending `borrow_k` with content `w` substitutes `h_k := w` (no re-run is needed, §7.1); [Reorg] fires when an accessed content mentions an `h_k` whose borrow is in Ω; inside a [Seal] run an `h_k` is just an abstract value. This is not the "prophecy variables" alternative that D4 rejected, because only [Close] mints a hole, so concrete runs never create one and "concrete in, concrete out" is kept.
