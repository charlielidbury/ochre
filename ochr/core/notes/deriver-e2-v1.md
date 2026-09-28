# deriver-e2-v1: returned borrows under RULES.md v1

## Summary

1. **Verdict:** E2 derives under v1. The main line needs only the natural reading of two unstated details: which call is "the head call" (H3), and that [Call-type] binds parameters in a pushed frame (H5). `TailM`, `AddM'`, `AddMEq` and `AddMEqOwned` check, and `AddMEq`'s S arm is bare recursion: the induction hypothesis (IH) and the refined goal are both `Eq Nat (S A(σ',τ)) (S B(σ')[τ])`. `Probe`, `AddM1`, `TailNoop`, and two new probes (`AddM''`: a hole filled by a [Close]; `TailM2`: a reborrow of a returned borrow) also check. For two borrow parameters I used `MinTail(a, b)`, which returns a borrow to the tail of whichever argument reaches `Z` first. `MinEq : Id Unit (SetMin(a, b, y)) (let t = MinTail(a, b); *t := y)` is bare recursion with a nested match, and the hole sits in both owners until a split decides which one the result points into.
2. **Most important finding:** every v1 change that E2 exercises works as intended, and together they retire all nine of my round-1 findings that v1 addresses (F10 stays open). [End] without a side condition makes `TailM`'s frame pop put the hole straight into the generic caller's owned place, so there are no pending bindings, and v0's load-bearing eager clause (my old F7) is gone. The head-call guard of [Seal] keeps a sealed program that is stuck on a *second* variable sealed, in exactly the form a fresh [Close] on those inputs would produce; that agreement is what makes `MinEq`'s two-level split line up (H6). Inert loans make `Probe` agree with direct execution exactly, without v0's pending-binding discrepancy. I found no unsoundness.
3. **RULES.md must change:** wording only. `⋆` is missing from the value grammar (H1). "Inert, like abstract values" must be honoured by [Access], [Read] and [Drop], and `Probe` needs all three (H2). "The head call of `t`" is undefined (H3). [Rec]'s "recursive position" is undefined when several arguments shrink (H4). [Call-type] should say that the parameters are bound in a frame pushed on the caller's Ω (H5). [Access] for [Match] should cover a loan at the head of the content (H8), and, once round-1 F10 is designed, loans inside a neutral scrutinee (H7). H6 (refinement commutes with closing off) deserves a stated lemma.
4. **Confidence:** high for all derivations here (each machine step is shown for the E2 examples, `Probe` and `MinTail`/`MinEq`; the extra probes reuse runs shown in full). Medium that H6 holds beyond these examples: it is an instance of the adequacy conjecture, which I did not prove.
5. **Not checked:** a replay of meta-model's C2 `Bad` under v1 (saturated calls make it form its type after the split; I did not build a variant); [Split] on a neutral that is not an abstract value (round-1 F10, still open, H7); stuck blocks inside types; any metatheory.

## 0. Notation

As in round 1 (`notes/deriver-e2.md` §0), with v1 changes:
- There are no ghosts. [Def] checks a definition at its generic call, so the caller's side of a borrow parameter `x` is an ordinary owned variable `c` (and `d` for a second parameter) in the frame below the function's frame.
- Calls are saturated: `AddM(x, y)`. Loans are variables; `[End ℓ]` substitutes the content for every `loan_ℓ` (§3 of RULES).
- `⋆` is the value a proof call returns under P5.
- Sealed-program abbreviations (binders `c`, `r` up to renaming):

```
A(v, w)  :=  ⌈let c = v; AddM(&c, w); c⌉                  AddM's effect on its borrowed place
T(v)     :=  ⌈let c = v; let r = TailM(&c); *r⌉           content of the borrow TailM returns
B(v)[h]  :=  ⌈let c = v; let r = TailM(&c); *r := h; c⌉   TailM's effect, given the final content h of the returned borrow
```

`[Close]`'s Unit row returns `()` (no `U(v, w)` any more) and fills the loan with `A(v, w)`.

## 1. `TailM`

```
TailM : Π(x : &Nat). &Nat
TailM(x) := match *x { Z => x | S p => TailM(&p) }
```

```
⊢ fix TailM (x : &Nat) : &Nat := match *x { Z => x | S p => TailM(&p) }                       // [Def]
  generic call: { c ↦ σ }, TailM(&c)
  { c ↦ loan_0 },                          TailM(borrow_0 σ)      // [Borrow] &c ([Access]: no loans on the path or inside σ)
  { c ↦ loan_0 | x ↦ borrow_0 σ },         match *x {…}           // body in a pushed frame
  goal = [Call-type] of TailM(&c) = &Nat
  [Split] content(*x) = σ, abstract
```

Z arm (`σ := Z`):

```
{ c ↦ loan_0 | x ↦ borrow_0 Z },  match *x {…}      // [Access] (no loans on the path x, *x); [Match] head Z: first arm
{ c ↦ loan_0 | x ↦ borrow_0 Z },  x
{ c ↦ loan_0 | x ↦ ⊥ },           borrow_0 Z        // [Access] (nothing inside borrow_0 Z to end); [Read] a borrow: moved
result type &Nat ≡ goal ✓
{ c ↦ loan_0 },                   borrow_0 Z        // pop: [Drop] x = ⊥, nothing
```

S arm (`σ := S σ'`): the recursive call is closed off, and the frame pop is a plain [End]:

```
{ c ↦ loan_0 | x ↦ borrow_0 (S σ') },                        match *x {…}           // [Match] head S: second arm, p := (*x).1
{ c ↦ loan_0 | x ↦ borrow_0 (S σ') },                        TailM(&(*x).1)
{ c ↦ loan_0 | x ↦ borrow_0 (S loan_1) },                    TailM(borrow_1 σ')     // [Access]; [Borrow] the tail
  [Rec]: the argument is a borrow whose content σ' is a strict subterm of the entry value σ = S σ' ✓
{ c ↦ loan_0 | x ↦ borrow_0 (S loan_1) | x₁ ↦ borrow_1 σ' }, match *x₁ {…}          // [Call] (&Nat is not a proposition): push, run
  stuck                                                                              // [Match] head σ'
{ c ↦ loan_0 | x ↦ borrow_0 (S loan_1) },                    TailM(borrow_1 σ')     // [Close] discard the partial run; I = {1}, L = let c = σ', C = TailM(&c)
{ c ↦ loan_0 | x ↦ borrow_0 (S B(σ')[loan_k]) },             borrow_k T(σ')         // [Close] &T row, fresh k: loan_1 := B(σ')[loan_k]
  [Call-type]: &Nat ✓;  both sealed programs are normal ([Seal]: the head call TailM(&c) is stuck on σ' and is not closed off, so the run does not complete)
result type &Nat ≡ goal ✓
{ c ↦ S B(σ')[loan_k] },                                     borrow_k T(σ')         // pop: [Drop] x → [End 0]: loan_0 := S B(σ')[loan_k]; loan_k travels with it
```

Ledger at the end: `loan_k` (inside `B(σ')[·]` inside `c`) ↔ `borrow_k` (the result); `owners(k) = {c}`. v0 needed an anonymous pending binding `_₀ ↦ borrow_0 (S B(σ')[loan_k])` here; v1's [End] simply substitutes, and the returned borrow's hole lands in the caller's owned place under the `S`. `TailM` is accepted.

## 2. `AddM'`

```
AddM' : Π(x : &Nat) (y : Nat). Unit
AddM'(x, y) := let t = TailM(x); *t := y
```

```
⊢ fix AddM' (x : &Nat) (y : Nat) : Unit := let t = TailM(x); *t := y                        // [Def]
  generic call: { c ↦ σ }, AddM'(&c, τ)                    // y is not a borrow parameter: its argument is a fresh τ
  { c ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ },                    let t = TailM(x); …     // [Borrow] &c; push
  goal: Unit
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ },                             TailM(borrow_0 σ)      // [Let]; [Access]; [Read] x: a borrow, moved
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ },           match *x₁ {…}          // [Call]
    stuck                                                                            // [Match] σ
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ },                             TailM(borrow_0 σ)      // [Close] discard; L = let c = σ, C = TailM(&c)
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ },                       borrow_k T(σ)          // [Close] &T row, fresh k
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k T(σ) },    *t := y                // [Let] bind t
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k T(σ) },    *t := τ                // [Access]; [Read] y: borrow-free, copied
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ, t ↦ borrow_k τ },       ()                     // [Access] (no loan on the path t, *t; none inside T(σ)); [Assign]: [Drop] T(σ), write τ
  { c ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ },                            ()                     // [Let] [Drop] t → [End k]: loan_k := τ; B(σ)[τ] re-normalised: head stuck, unchanged
  result type Unit ≡ goal ✓
  { c ↦ B(σ)[τ] },                                           ()                     // pop
```

`AddM'` is accepted, and its effect on the generic caller is `B(σ)[τ]`.

## 3. Normal forms under v1's [Seal]

### 3.0 The head-call guard: a stuck sealed program stays put

```
nf B(σ)[τ]:  ⟨{}, let c = σ; let r = TailM(&c); *r := τ; c⟩
  { c ↦ loan_1 },                  TailM(borrow_1 σ)    // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 σ }, match *x₁ {…}        // the head call TailM(&c) unfolds
    stuck                                                // [Match] σ; the head call is not eligible for [Close]
  run does not complete → nf = B(σ)[τ] (values inside already normal)     // [Seal]
```

The same holds for `A(σ, w)`, `T(σ)` and every sealed program [Close] creates: its head call has just got stuck on exactly these inputs. v0's regress (round-1 F1) is gone.

### 3.1 `A(Z, τ) ≡ τ`

```
⟨{}, let c = Z; AddM(&c, τ); c⟩
  { c ↦ loan_1 },                               AddM(borrow_1 Z, τ)   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z, y₁ ↦ τ },     match *x₁ {…}         // head call unfolds
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z, y₁ ↦ τ },     *x₁ := y₁             // [Match] Z
  { c ↦ loan_1 | x₁ ↦ borrow_1 τ, y₁ ↦ τ },     ()                    // [Read] y₁ copied; [Access]; [Assign] ([Drop] Z)
  { c ↦ τ },                                    c                     // pop: [Drop] x₁ → [End 1]; [Drop] y₁
  { c ↦ τ },                                    τ                     // [Access]; [Read] copied
  {},                                           τ                     // [Let] [Drop] c: owned, no loans ✓
```

### 3.2 `B(Z)[τ] ≡ τ` and `T(Z) ≡ Z`

```
⟨{}, let c = Z; let r = TailM(&c); *r := τ; c⟩
  { c ↦ loan_1 },                    TailM(borrow_1 Z)   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 Z },  match *x₁ {…}       // head call unfolds
  { c ↦ loan_1 | x₁ ↦ ⊥ },           borrow_1 Z          // [Match] Z; [Read] x₁ moved
  { c ↦ loan_1, r ↦ borrow_1 Z },    *r := τ             // pop ([Drop] ⊥); [Let] bind r
  { c ↦ loan_1, r ↦ borrow_1 τ },    c                   // [Access]; [Assign]
  { c ↦ τ, r ↦ ⊥ },                  c                   // [Access] for reading c: loan_1 is c's content → [End 1]
  { c ↦ τ, r ↦ ⊥ },                  τ                   // [Read] copied
  {},                                τ                   // [Let]×2: [Drop] r (⊥), c
```

`T(Z)`: the same run up to binding `r`; then `*r` copies `Z` ([Access] finds nothing to end), [Drop] `r` ends `borrow_1` and `c ↦ Z`, [Drop] `c`. Value `Z`.

### 3.3 `A(S σ', τ) ≡ S A(σ', τ)`

```
⟨{}, let c = S σ'; AddM(&c, τ); c⟩
  { c ↦ loan_1 },                                                     AddM(borrow_1 (S σ'), τ)   // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ'), y₁ ↦ τ },                      match *x₁ {…}              // head call unfolds
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ'), y₁ ↦ τ },                      AddM(&(*x₁).1, y₁)         // [Match] S, p := (*x₁).1
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2), y₁ ↦ τ },                  AddM(borrow_2 σ', τ)       // [Access]; [Borrow]; [Read] y₁
  { … | x₂ ↦ borrow_2 σ', y₂ ↦ τ },                                   match *x₂ {…}              // [Call]: an inner call, eligible for [Close]
    stuck                                                                                        // [Match] σ'
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2), y₁ ↦ τ },                  AddM(borrow_2 σ', τ)       // [Close] discard; L = let c = σ', C = AddM(&c, τ)
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S A(σ', τ)), y₁ ↦ τ },                ()                         // [Close] Unit row: result (), loan_2 := A(σ', τ)
  { c ↦ S A(σ', τ) },                                                 c                          // pop: [Drop] x₁ → [End 1]; [Drop] y₁
  {},                                                                 S A(σ', τ)                 // [Read] copied; [Let] [Drop] c
```

### 3.4 `B(S σ')[τ] ≡ S B(σ')[τ]` (the step the example turns on)

```
⟨{}, let c = S σ'; let r = TailM(&c); *r := τ; c⟩
  { c ↦ loan_1 },                                                     TailM(borrow_1 (S σ'))    // [Let], [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ') },                              match *x₁ {…}             // head call unfolds
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S σ') },                              TailM(&(*x₁).1)           // [Match] S
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) },                          TailM(borrow_2 σ')        // [Access]; [Borrow]
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) | x₂ ↦ borrow_2 σ' },       match *x₂ {…}             // [Call], eligible
    stuck                                                                                       // [Match] σ'
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S loan_2) },                          TailM(borrow_2 σ')        // [Close] discard; L = let c = σ', C = TailM(&c)
  { c ↦ loan_1 | x₁ ↦ borrow_1 (S B(σ')[loan_j]) },                   borrow_j T(σ')            // [Close] &T row, fresh j: loan_2 := B(σ')[loan_j]
  { c ↦ S B(σ')[loan_j] },                                            borrow_j T(σ')            // pop: [Drop] x₁ → [End 1]; loan_j travels into c
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j T(σ') },                        *r := τ                   // [Let]
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j τ },                            c                         // [Access] (path r, *r; content T(σ'): no loans); [Assign]
  { c ↦ S B(σ')[τ], r ↦ ⊥ },                                          c                         // [Access] for reading c: loan_j occurs inside content(c) → [End j]
  { c ↦ S B(σ')[τ], r ↦ ⊥ },                                          S B(σ')[τ]                // [Read] copied
  {},                                                                 S B(σ')[τ]                // [Let]×2
```

v0 needed its pending binding and the recursive clause of [Reorg] here. v1 needs one [End] at the frame pop and one [Access] before the final read. The outer continuation `*r := τ` fills the inner call's fresh hole, and the `S` stays outside.

### 3.5 `T(S σ') ≡ T(σ')`

```
⟨{}, let c = S σ'; let r = TailM(&c); *r⟩
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j T(σ') },   *r        // §3.4 up to and including binding r
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j T(σ') },   T(σ')     // [Access] (nothing on the path r, *r or inside T(σ')); [Read] copied, r keeps its borrow
  { c ↦ S B(σ')[T(σ')] },                         T(σ')     // [Let] [Drop] r → [End j]: loan_j := T(σ')
  {},                                             T(σ')     // [Let] [Drop] c: no loans ✓
```

In v0 this run needed [Pop]'s eager clause, since otherwise `c` still held `loan_1` when it was dropped (round-1 F7). In v1 the loan travelled into `c` at the frame pop, so the problem cannot arise.

## 4. `AddMEq`

```
AddMEq : Π(x : &Nat) (y : Nat). Id Unit (AddM(x, y)) (AddM'(x, y))
AddMEq(x, y) := match *x { Z => refl | S p => AddMEq(&p, y) }
```

### 4.1 Entry goal at the generic call

```
⊢ fix AddMEq (x : &Nat) (y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) := match *x {…}          // [Def]
  generic call: { c ↦ σ }, AddMEq(&c, τ)
  Ω₀ = { c ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ }                                                   // [Borrow] &c; push
  goal = [Call-type] = Id Unit (AddM(x, y)) (AddM'(x, y)) evaluated at Ω₀
    W = owners(0) = {c}      // free places: x is a borrow-typed variable holding borrow_0; loan_0 occurs in the owned c. y: none of the three clauses. No &_ or := in either term.
    T_W = Nat
    ⟦AddM(x, y)⟧^W  = ((), A(σ, τ))       // run (a)
    ⟦AddM'(x, y)⟧^W = ((), B(σ)[τ])       // run (b)
    Id ≡ Eq (Unit × Nat) ((), A(σ, τ)) ((), B(σ)[τ])
       ≡ Eq Unit () () ∧ Eq Nat A(σ, τ) B(σ)[τ]         // Eq on pairs
       ≡ ⊤ ∧ Eq Nat A(σ, τ) B(σ)[τ]                      // Eq A a b ≡ ⊤ when a ≡ b
       ≡ Eq Nat A(σ, τ) B(σ)[τ]   =: G₀                  // ⊤ ∧ P ≡ P
```

Run (a), on a private copy of `Ω₀`:

```
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ },                              AddM(borrow_0 σ, τ)   // [Access]; [Read] x moved, y copied
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ, y₁ ↦ τ },    match *x₁ {…}         // [Call] (Unit is not a proposition)
    stuck                                                                             // [Match] σ
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ },                              AddM(borrow_0 σ, τ)   // [Close] discard
  { c ↦ A(σ, τ) | x ↦ ⊥, y ↦ τ },                             ()                    // [Close] Unit row: result (), loan_0 := A(σ, τ)
  end every borrow: none live.  observation ((), A(σ, τ))
```

Run (b), on a private copy of `Ω₀`: the §2 body run, from `AddM'(borrow_0 σ, τ)` pushed on `Ω₀`:

```
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ },                                               AddM'(borrow_0 σ, τ)   // [Read]
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ borrow_0 σ, y₁ ↦ τ },                     let t = TailM(x₁); …   // [Call]
  { c ↦ loan_0 | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ | x₂ ↦ borrow_0 σ },            match *x₂ {…}          // [Let], [Read], [Call]
    stuck                                                                                                // [Match] σ
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                        borrow_k T(σ)          // [Close] (innermost stuck call: TailM), &T row
  { c ↦ B(σ)[loan_k] | … | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k τ },                   ()                     // [Let]; [Read] y₁; [Access]; [Assign]
  { c ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },                             ()                     // [Drop] t → [End k]
  { c ↦ B(σ)[τ] | x ↦ ⊥, y ↦ τ },                                              ()                     // pop
  end every borrow: none live.  observation ((), B(σ)[τ])
```

### 4.2 Split and Z arm

```
Ω₀ ⊢ match *x {…} : G₀                          // [Split] content(*x) = σ
arm Z (σ := Z): Ω_Z = { c ↦ loan_0 | x ↦ borrow_0 Z, y ↦ τ }
  G_Z = Eq Nat A(Z, τ) B(Z)[τ] ≡ Eq Nat τ τ     // refinement re-normalises: §3.1, §3.2
      ≡ ⊤                                        // Eq A a b ≡ ⊤ when a ≡ b
  [Match] head Z: `refl`;  refl : ⊤ ≡ G_Z ✓
```

### 4.3 S arm: the IH by [Call-type], the call by P5

```
arm S (σ := S σ'): Ω_S = { c ↦ loan_0 | x ↦ borrow_0 (S σ'), y ↦ τ }
  G_S = Eq Nat A(S σ', τ) B(S σ')[τ] ≡ Eq Nat (S A(σ', τ)) (S B(σ')[τ])      // §3.3; §3.4 (runs TailM on S σ', closes off the inner call on σ')
  [Match] head S: second arm, p := (*x).1;  AddMEq(&p, y)
  { c ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ },   args borrow_1 σ', τ        // [Access]; [Borrow] &(*x).1; [Read] y
  [Rec]: position 1 is a borrow whose content σ' is a strict subterm of the entry σ = S σ' ✓
  type ([Call-type]): the codomain with x', y' bound to the arguments in a pushed frame (H5):
    Ω_IH = { c ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ borrow_1 σ', y' ↦ τ }
    W = owners(1): loan_1 occurs inside the content of borrow_0, so owners(1) = owners(0) = {c}
    ⟦AddM(x', y')⟧  = ((), S A(σ', τ))          // run (c)
    ⟦AddM'(x', y')⟧ = ((), S B(σ')[τ])          // run (d)
    IH ≡ Eq (Unit × Nat) ((), S A(σ', τ)) ((), S B(σ')[τ]) ≡ Eq Nat (S A(σ', τ)) (S B(σ')[τ])
  value ([Call], P5): the codomain is a proposition, so the body is not run:
  { c ↦ loan_0 | x ↦ borrow_0 (S σ'), y ↦ τ },       ⋆                         // [End 1]: the borrow argument comes back unchanged
  conversion: IH ≡ G_S, symbol for symbol ✓
  { c ↦ S σ' },                                     ⋆                         // pop: [End 0]; the generic caller's place is untouched by the lemma call (round-1 F8 fixed)
```

Run (c), on a private copy of `Ω_IH`:

```
  { c ↦ loan_0 | x ↦ borrow_0 (S loan_1), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                           AddM(borrow_1 σ', τ)   // [Read]
  { … | x' ↦ ⊥, y' ↦ τ | x₁ ↦ borrow_1 σ', y₁ ↦ τ },                                         match *x₁ {…}          // [Call]
    stuck                                                                                                           // [Match] σ'
  { c ↦ loan_0 | x ↦ borrow_0 (S A(σ', τ)), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                         ()                     // [Close] Unit row: loan_1 := A(σ', τ)
  end every borrow: [End 0] → c ↦ S A(σ', τ).  observation ((), S A(σ', τ))
```

Run (d), on a private copy of `Ω_IH`:

```
  { … | x' ↦ ⊥, y' ↦ τ | x₁ ↦ borrow_1 σ', y₁ ↦ τ },                                         let t = TailM(x₁); …   // [Read], [Call]
  { … | x₁ ↦ ⊥, y₁ ↦ τ | x₂ ↦ borrow_1 σ' },                                                 match *x₂ {…}          // [Let], [Read], [Call]
    stuck                                                                                                           // [Match] σ'
  { c ↦ loan_0 | x ↦ borrow_0 (S B(σ')[loan_k]), y ↦ τ | x' ↦ ⊥, y' ↦ τ | x₁ ↦ ⊥, y₁ ↦ τ },  borrow_k T(σ')         // [Close] &T row: loan_1 := B(σ')[loan_k]
  { … | x₁ ↦ ⊥, y₁ ↦ τ, t ↦ borrow_k τ },                                                    ()                     // [Let]; [Read] y₁; [Access]; [Assign]
  { c ↦ loan_0 | x ↦ borrow_0 (S B(σ')[τ]), y ↦ τ | x' ↦ ⊥, y' ↦ τ },                        ()                     // [Drop] t → [End k]; pop AddM'
  end every borrow: [End 0] → c ↦ S B(σ')[τ].  observation ((), S B(σ')[τ])
```

`AddMEq` is accepted with the proof as written. D16 removed `Eq Nat (S a) (S b) ≡ Eq Nat a b`; E2 never needed it, because the IH and the goal agree *including* the `S`.

## 5. `AddMEqOwned`

```
⊢ fix AddMEqOwned (x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) := AddMEq(&x, 0)                // [Def]
  generic call AddMEqOwned(σ): no borrow parameter, no generic caller variable;  Ω₀ = { x ↦ σ }
  goal: W = {x}      // the free place x appears under &_ and is rooted at an owned variable
    ⟦AddM(&x, 0)⟧:  { x ↦ loan_1 }, AddM(borrow_1 σ, Z)                         // [Access]; [Borrow]
                    { x ↦ loan_1 | x₁ ↦ borrow_1 σ, y₁ ↦ Z }, match *x₁ {…}       // [Call]
                      stuck                                                      // [Match] σ
                    { x ↦ A(σ, Z) }, ()                                          // [Close] Unit row
                    observation ((), A(σ, Z))
    ⟦AddM'(&x, 0)⟧: { x ↦ loan_1 }, AddM'(borrow_1 σ, Z)                        // [Borrow]
                    … the §2 body run with borrow_1 σ and Z …                    // [Close] of TailM gives x ↦ B(σ)[loan_k]; *t := Z; [End k]
                    { x ↦ B(σ)[Z] }, ()
                    observation ((), B(σ)[Z])
    G ≡ Eq Nat A(σ, Z) B(σ)[Z]
  body: AddMEq(&x, 0)
    { x ↦ loan_1 }, args borrow_1 σ, Z                                           // [Access]; [Borrow]
    type: Ω_IH = { x ↦ loan_1 | x' ↦ borrow_1 σ, y' ↦ Z };  W = owners(1) = {x}
      the same two runs from the call onward → IH ≡ Eq Nat A(σ, Z) B(σ)[Z]
    value: P5, not run: [End 1] → { x ↦ σ }, ⋆
  IH ≡ G, symbol for symbol ✓
```

Here the goal's footprint comes from the `&_` clause and the IH's from the borrow-typed-variable clause, and both give `{x}`.

## 6. `Probe`: a split while a returned borrow is live (inert loans)

```
Probe : Π(n : Nat). Unit
Probe(n) := let m = n; let t = TailM(&m); match n { Z => () | S q => () }
```

```
⊢ fix Probe (n : Nat) : Unit := …                                          // [Def]: generic call Probe(σ), no borrow parameters
{ n ↦ σ },                                          let m = n; …          // push
{ n ↦ σ, m ↦ σ },                                   TailM(&m)             // [Let]; [Read] n copied
{ n ↦ σ, m ↦ loan_1 },                              TailM(borrow_1 σ)     // [Access]; [Borrow]
  stuck                                                                   // [Call], [Match] σ
{ n ↦ σ, m ↦ B(σ)[loan_k] },                        borrow_k T(σ)         // [Close] &T row
{ n ↦ σ, m ↦ B(σ)[loan_k], t ↦ borrow_k T(σ) },     match n {…}           // [Let]; [Access] (nothing on the path n)
[Split] content(n) = σ. Both sealed programs mention σ and are re-normalised in each arm.
```

Arm Z. `B(Z)[loan_k]`, with `loan_k` inert (its borrow is `t`'s, outside the run):

```
⟨{}, let c = Z; let r = TailM(&c); *r := loan_k; c⟩
  { c ↦ loan_2, r ↦ borrow_2 Z },       *r := loan_k        // as §3.2
  { c ↦ loan_2, r ↦ borrow_2 loan_k },  c                   // [Access] (path r, *r: no loans; content Z); [Assign] the inert loan
  { c ↦ loan_k, r ↦ ⊥ },                c                   // [Access] for reading c: [End 2]; loan_k travels. loan_k is now inside content(c), but inert: not ended (H2)
  { c ↦ loan_k, r ↦ ⊥ },                loan_k              // [Read]: an inert loan counts as borrow-free and is copied (H2)
  {},                                   loan_k              // [Let]×2: [Drop] r; [Drop] c holding an inert loan is not an error (H2)
so B(Z)[loan_k] ≡ loan_k, and T(Z) ≡ Z (§3.2)
arm Z environment: { n ↦ Z, m ↦ loan_k, t ↦ borrow_k Z }  ⊢ () : Unit ✓
```

This is, up to renaming the loan, exactly what running `TailM(&m)` on `m = Z` produces: `TailM` hands back the borrow it was given, so `m` holds the bare loan.

Arm S. `B(S σ')[loan_k]` (the §3.4 run with the inert `loan_k` in place of `τ`):

```
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j T(σ') },   *r := loan_k      // §3.4 up to binding r (inner [Close] mints j)
  { c ↦ S B(σ')[loan_j], r ↦ borrow_j loan_k },  c                 // [Assign]
  { c ↦ S B(σ')[loan_k], r ↦ ⊥ },                c                 // [Access]: [End j]; the inert loan_k travels into the inner hole
  {},                                            S B(σ')[loan_k]   // [Read] (inert: copied), [Let]×2
so B(S σ')[loan_k] ≡ S B(σ')[loan_k], and T(S σ') ≡ T(σ') (§3.5)
arm S environment: { n ↦ S σ', m ↦ S B(σ')[loan_k], t ↦ borrow_k T(σ') } ⊢ () : Unit ✓
```

Direct execution of `TailM(&m)` on `m = S σ'` gives the same thing, including the `S` in `m`: the inner call is closed off with a fresh `k`, and the frame pop's [End] moves the hole into `m`. In round 1 the two differed by a pending binding; in v1 they are identical. After either arm, the [Let] drops end `borrow_k` into `m` and drop `m` with no loans. `Probe` is accepted.

## 7. More probes (compact; every run is an instance of §3–§4)

### 7.1 `AddM1`: read, then write back through the returned borrow

```
AddM1 : Π(x : &Nat). Id Unit (AddM(x, 1)) (let t = TailM(x); *t := S *t)
AddM1(x) := match *x { Z => refl | S p => AddM1(&p) }
```

```
Ω₀ = { c ↦ loan_0 | x ↦ borrow_0 σ };  W = owners(0) = {c}     // t is bound inside the term, so `*t` is not a free place: v1 fixed round-1 F9
right run: TailM closes (c ↦ B(σ)[loan_k], t ↦ borrow_k T(σ)); [Read] *t copies T(σ); [Assign] t ↦ borrow_k (S T(σ)); [Drop] t → [End k]
G₀ ≡ Eq Nat A(σ, 1) B(σ)[S T(σ)]
Z:  A(Z, 1) ≡ 1;  B(Z)[S T(Z)] ≡ B(Z)[1] ≡ 1  (values kept normal: T(Z) ≡ Z first; §3.1, §3.2);  G_Z ≡ ⊤;  refl ✓
S:  G_S ≡ Eq Nat (S A(σ', 1)) (S B(σ')[S T(σ')])          // §3.3; §3.5 then §3.4 with S T(σ') for τ
    IH (AddM1(&(*x).1), not run by P5): Ω_IH = { c ↦ loan_0 | x ↦ borrow_0 (S loan_1) | x' ↦ borrow_1 σ' }, W = {c}
      left: run (c) with 1 for τ → ((), S A(σ', 1))
      right: TailM(x') closes: loan_1 := B(σ')[loan_k]; *t := S *t; [End k] → x ↦ borrow_0 (S B(σ')[S T(σ')]); [End 0] → ((), S B(σ')[S T(σ')])
    IH ≡ G_S ✓
```

### 7.2 `TailNoop`: borrowing the tail and writing nothing changes nothing

```
TailNoop : Π(x : &Nat). Id Unit (let t = TailM(x); ()) ()
TailNoop(x) := match *x { Z => refl | S p => TailNoop(&p) }
```

```
W = {c};  left: [Drop] t → [End k] with the unchanged T(σ) → ((), B(σ)[T(σ)]);  right: [End 0] → ((), σ)
G₀ ≡ Eq Nat B(σ)[T(σ)] σ
Z:  B(Z)[Z] ≡ Z;  G_Z ≡ ⊤ ✓
S:  G_S ≡ Eq Nat (S B(σ')[T(σ')]) (S σ')
    IH: left → c ↦ S B(σ')[T(σ')];  right: end every borrow ([End 1] then [End 0], in either order: substitution commutes) → c ↦ S σ'
    IH ≡ G_S ✓
```

### 7.3 `AddM''`: the hole filled by a [Close], not by an [End]

```
AddM''(x, y) := let t = TailM(x); AddM(t, y)
AddMEq2 : Π(x : &Nat) (y : Nat). Id Unit (AddM(x, y)) (AddM''(x, y))
AddMEq2(x, y) := match *x { Z => refl | S p => AddMEq2(&p, y) }
```

```
right run at Ω₀ = { c ↦ loan_0 | x ↦ borrow_0 σ, y ↦ τ }:
  … TailM closes: c ↦ B(σ)[loan_k], t ↦ borrow_k T(σ)
  { … , t ↦ ⊥ },                        AddM(borrow_k T(σ), τ)      // [Read] t moved; [Read] y
  { … | x₂ ↦ borrow_k T(σ), y₂ ↦ τ },   match *x₂ {…}               // [Call]
    stuck                                                           // [Match]: the head of T(σ) is a neutral
  { c ↦ B(σ)[A(T(σ), τ)] | … },         ()                          // [Close] Unit row: loan_k := A(T(σ), τ), substituted into c's program; re-normalised: head stuck
  observation ((), B(σ)[A(T(σ), τ)])
G₀ ≡ Eq Nat A(σ, τ) B(σ)[A(T(σ), τ)]
Z:  T(Z) ≡ Z, A(Z, τ) ≡ τ, B(Z)[τ] ≡ τ;  G_Z ≡ Eq Nat τ τ ≡ ⊤ ✓
S:  T(S σ') ≡ T(σ'); A(T(σ'), τ) stays sealed (its head call is stuck on the neutral T(σ')); B(S σ')[A(T(σ'), τ)] ≡ S B(σ')[A(T(σ'), τ)] (§3.4)
    G_S ≡ Eq Nat (S A(σ', τ)) (S B(σ')[A(T(σ'), τ)])
    IH at Ω_IH: TailM(x') closes: loan_1 := B(σ')[loan_k]; AddM(t, y) closes: loan_k := A(T(σ'), τ); [End 0] → ((), S B(σ')[A(T(σ'), τ)])
    IH ≡ G_S ✓
```

### 7.4 `TailM2`: a reborrow of a returned borrow ([End] carries a loan into a hole)

```
TailM2 : Π(x : &Nat). &Nat
TailM2(x) := let t = TailM(x); &*t
```

```
[Def]: { c ↦ loan_0 | x ↦ borrow_0 σ }
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, t ↦ borrow_k T(σ) },         &*t          // TailM closes, as in §2
  { c ↦ B(σ)[loan_k] | x ↦ ⊥, t ↦ borrow_k loan_u },       borrow_u T(σ) // [Access] (path t, *t; content T(σ)); [Borrow] *t, fresh u
  { c ↦ B(σ)[loan_u] | x ↦ ⊥ },                            borrow_u T(σ) // [Let] [Drop] t → [End k]: its content is the bare loan_u, which v1 substitutes into the hole
  result type &Nat ✓;  owners(u) = {c}
```

v0 would have needed a pending binding (`borrow_k`'s content held a loan) or would have refused the drop. In v1 the hole is simply re-pointed from `k` to `u`. `TailM2` never appears in a normal form: its body is never stuck at its own top, so `Id Unit (let t = TailM2(x); *t := y) (AddM'(x, y))` computes to `Eq Nat B(σ)[τ] B(σ)[τ] ≡ ⊤` at entry and needs no induction at all.

## 8. Two borrow parameters: `MinTail`, `SetMin`, `MinEq`

The lead suggested "pick the one whose content is `Z`". To get something recursive to prove, I walk both numbers in step and return a borrow to the tail of whichever reaches `Z` first (at depth 0 this *is* "pick the one that is `Z`, preferring `a`"). `SetMin` is the direct-style version that writes `y` there, and `MinEq` says the two agree.

```
MinTail : Π(a : &Nat) (b : &Nat). &Nat
MinTail(a, b) := match *a { Z => a | S p => match *b { Z => b | S q => MinTail(&p, &q) } }

SetMin : Π(a : &Nat) (b : &Nat) (y : Nat). Unit
SetMin(a, b, y) := match *a { Z => *a := y | S p => match *b { Z => *b := y | S q => SetMin(&p, &q, y) } }

MinEq : Π(a : &Nat) (b : &Nat) (y : Nat). Id Unit (SetMin(a, b, y)) (let t = MinTail(a, b); *t := y)
MinEq(a, b, y) := match *a { Z => refl | S p => match *b { Z => refl | S q => MinEq(&p, &q, y) } }
```

Abbreviations (`L₂ := let c₁ = v; let c₂ = w`):

```
SMa(v, w, z) := ⌈L₂; SetMin(&c₁, &c₂, z); c₁⌉          SMb(v, w, z) := ⌈L₂; SetMin(&c₁, &c₂, z); c₂⌉
MT(v, w)     := ⌈L₂; let r = MinTail(&c₁, &c₂); *r⌉
Ma(v, w)[h]  := ⌈L₂; let r = MinTail(&c₁, &c₂); *r := h; c₁⌉      Mb(v, w)[h] := ⌈…; *r := h; c₂⌉
```

### 8.1 `MinTail` at its generic call: one hole, two owners

```
⊢ fix MinTail (a : &Nat) (b : &Nat) : &Nat := …                                                       // [Def]
  generic call: { c ↦ σ, d ↦ ρ }, MinTail(&c, &d)
  { c ↦ loan_0, d ↦ loan_1 | a ↦ borrow_0 σ, b ↦ borrow_1 ρ },   match *a {…}                        // [Borrow]×2; push. goal &Nat
  [Split] σ
  Z:   { … | a ↦ ⊥, b ↦ borrow_1 ρ },  borrow_0 Z                                                    // [Match] Z; [Read] a moved
       { c ↦ loan_0, d ↦ ρ },           borrow_0 Z  : &Nat ✓                                          // pop: [Drop] b → [End 1]
  S:   [Match] head S, p := (*a).1;  match *b {…}: [Split] ρ
    S/Z: { c ↦ loan_0, d ↦ loan_1 | a ↦ borrow_0 (S σ'), b ↦ ⊥ },  borrow_1 Z                        // [Match] Z; [Read] b moved
         { c ↦ S σ', d ↦ loan_1 },                                  borrow_1 Z : &Nat ✓               // pop: [Drop] a → [End 0]
    S/S: [Match] head S, q := (*b).1;  MinTail(&p, &q)
         { … | a ↦ borrow_0 (S loan_2), b ↦ borrow_1 (S loan_3) },  MinTail(borrow_2 σ', borrow_3 ρ')    // [Access]; [Borrow]×2
         [Rec] position 1 (H4): content σ' is a strict subterm of the entry σ = S σ' ✓
         { … | … | a₁ ↦ borrow_2 σ', b₁ ↦ borrow_3 ρ' },            match *a₁ {…}                       // [Call]
           stuck                                                                                     // [Match] σ'
         { … | a ↦ borrow_0 (S loan_2), b ↦ borrow_1 (S loan_3) },  MinTail(borrow_2 σ', borrow_3 ρ')    // [Close] discard; I = {1, 2}, L = L₂(σ', ρ'), C = MinTail(&c₁, &c₂)
         { … | a ↦ borrow_0 (S Ma(σ', ρ')[loan_k]), b ↦ borrow_1 (S Mb(σ', ρ')[loan_k]) },  borrow_k MT(σ', ρ')   // [Close] &T row, fresh k: loan_2 and loan_3 each get their program, loan_k occurs in both
         { c ↦ S Ma(σ', ρ')[loan_k], d ↦ S Mb(σ', ρ')[loan_k] },    borrow_k MT(σ', ρ') : &Nat ✓        // pop: [End 0], [End 1]; loan_k travels into both
         owners(k) = {c, d}
```

`MinTail` is accepted. The final line is the situation D18 is about: one returned borrow, whose hole occurs in two owners.

### 8.2 `SetMin` at its generic call

```
generic call { c ↦ σ, d ↦ ρ }, SetMin(&c, &d, τ);  frame { a ↦ borrow_0 σ, b ↦ borrow_1 ρ, y ↦ τ };  goal Unit
Z:    *a := y → a ↦ borrow_0 τ; pop: [End 0], [End 1] → { c ↦ τ, d ↦ ρ }, () ✓
S/Z:  *b := y → b ↦ borrow_1 τ; pop → { c ↦ S σ', d ↦ τ }, () ✓
S/S:  SetMin(&p, &q, y): [Borrow]×2, [Rec] position 1 ✓, [Call], stuck on σ', [Close] Unit row: loan_2 := SMa(σ', ρ', τ), loan_3 := SMb(σ', ρ', τ)
      pop → { c ↦ S SMa(σ', ρ', τ), d ↦ S SMb(σ', ρ', τ) }, () ✓
```

### 8.3 Normal forms

(N-a) `Ma(Z, ρ)[τ] ≡ τ`, `Mb(Z, ρ)[τ] ≡ ρ`:

```
⟨{}, L₂(Z, ρ); let r = MinTail(&c₁, &c₂); *r := τ; c₁⟩
  { c₁ ↦ loan_1, c₂ ↦ loan_2 },                                MinTail(borrow_1 Z, borrow_2 ρ)   // [Let]×2, [Borrow]×2
  { c₁ ↦ loan_1, c₂ ↦ loan_2 | a₁ ↦ borrow_1 Z, b₁ ↦ borrow_2 ρ }, match *a₁ {…}                   // head call unfolds
  { c₁ ↦ loan_1, c₂ ↦ loan_2 | a₁ ↦ ⊥, b₁ ↦ borrow_2 ρ },       borrow_1 Z                        // [Match] Z; [Read] a₁ moved
  { c₁ ↦ loan_1, c₂ ↦ ρ, r ↦ borrow_1 Z },                     *r := τ                           // pop: [Drop] b₁ → [End 2]; [Let]
  { c₁ ↦ loan_1, c₂ ↦ ρ, r ↦ borrow_1 τ },                     c₁                                // [Assign]
  { c₁ ↦ τ, c₂ ↦ ρ, r ↦ ⊥ },                                   τ                                 // [Access]: [End 1]; [Read]
  {},                                                          τ                                 // [Let]×3
for Mb the last read is c₂: [Access] finds nothing to end, value ρ; then [Drop] r ends borrow_1 into c₁.  Likewise SMa(Z, ρ, τ) ≡ τ, SMb(Z, ρ, τ) ≡ ρ (SetMin's Z arm writes c₁; its pop ends both borrows).
```

(N-b) the guard: after `σ := S σ'` alone, all four programs stay sealed:

```
⟨{}, L₂(S σ', ρ); let r = MinTail(&c₁, &c₂); *r := τ; c₁⟩
  { c₁ ↦ loan_1, c₂ ↦ loan_2 | a₁ ↦ borrow_1 (S σ'), b₁ ↦ borrow_2 ρ }, match *a₁ {…}             // head call unfolds
  { c₁ ↦ loan_1, c₂ ↦ loan_2 | a₁ ↦ borrow_1 (S σ'), b₁ ↦ borrow_2 ρ }, match *b₁ {…}             // [Match] S
    stuck                                                                                        // [Match] ρ, in the head call's own body: not eligible for [Close]
  run does not complete → nf = Ma(S σ', ρ)[τ]; likewise Mb, SMa, SMb at (S σ', ρ)
```

This is exactly what a fresh [Close] of `MinTail(borrow (S σ'), borrow ρ)` would produce, because that call's body also gets stuck on `ρ` and `L` records `S σ'` unrefined. Refinement and closing off agree on partially known inputs (H6).

(N-c) `Ma(S σ', Z)[τ] ≡ S σ'`, `Mb(S σ', Z)[τ] ≡ τ`: the head call takes `*a₁`'s S arm, then `*b₁`'s Z arm, and returns `b₁` (moved, `borrow_2 Z`). Its pop drops `a₁` ([End 1], so `c₁ ↦ S σ'`). Then `*r := τ` writes `borrow_2 τ`, and reading `c₁` gives `S σ'` (nothing to end); for `Mb`, reading `c₂` ends `borrow_2` and gives `τ`. Likewise `SMa(S σ', Z, τ) ≡ S σ'` and `SMb(S σ', Z, τ) ≡ τ`.

(N-d) `Ma(S σ', S ρ')[τ] ≡ S Ma(σ', ρ')[τ]` and `Mb(S σ', S ρ')[τ] ≡ S Mb(σ', ρ')[τ]`: the fresh hole is filled in *both* owners by one [End]:

```
⟨{}, L₂(S σ', S ρ'); let r = MinTail(&c₁, &c₂); *r := τ; c₁⟩
  { c₁ ↦ loan_1, c₂ ↦ loan_2 | a₁ ↦ borrow_1 (S σ'), b₁ ↦ borrow_2 (S ρ') },       match *a₁ {…}      // [Let]×2, [Borrow]×2; head call unfolds
  { … | a₁ ↦ borrow_1 (S σ'), b₁ ↦ borrow_2 (S ρ') },                               MinTail(&(*a₁).1, &(*b₁).1)   // [Match] S; [Match] S
  { … | a₁ ↦ borrow_1 (S loan_3), b₁ ↦ borrow_2 (S loan_4) },                       MinTail(borrow_3 σ', borrow_4 ρ')   // [Access]; [Borrow]×2
  { … | … | a₂ ↦ borrow_3 σ', b₂ ↦ borrow_4 ρ' },                                   match *a₂ {…}      // [Call], eligible
    stuck                                                                                                 // [Match] σ'
  { … | a₁ ↦ borrow_1 (S Ma(σ', ρ')[loan_j]), b₁ ↦ borrow_2 (S Mb(σ', ρ')[loan_j]) }, borrow_j MT(σ', ρ')   // [Close] discard; &T row, fresh j
  { c₁ ↦ S Ma(σ', ρ')[loan_j], c₂ ↦ S Mb(σ', ρ')[loan_j] },                         borrow_j MT(σ', ρ')   // pop: [End 1], [End 2]
  { c₁ ↦ S Ma(σ', ρ')[loan_j], c₂ ↦ S Mb(σ', ρ')[loan_j], r ↦ borrow_j τ },         c₁                    // [Let]; [Assign]
  { c₁ ↦ S Ma(σ', ρ')[τ], c₂ ↦ S Mb(σ', ρ')[τ], r ↦ ⊥ },                            c₁                    // [Access]: loan_j inside content(c₁) → [End j], which substitutes into c₂ as well
  {},                                                                               S Ma(σ', ρ')[τ]       // [Read]; [Let]×3 (c₂ now has no loans, so its drop is legal)
for Mb, the final read of c₂ triggers the same [End j].  Likewise SMa(S σ', S ρ', τ) ≡ S SMa(σ', ρ', τ), SMb(…) ≡ S SMb(σ', ρ', τ) (§3.3's shape, [Close] Unit row with two loans).
```

In v0 this run needed a pending binding for each of `a₁` and `b₁`, and the second owner's drop would have hit a still-open duplicated hole (round-1 F4).

### 8.4 `MinEq`: bare recursion with a nested match

```
⊢ fix MinEq (a : &Nat) (b : &Nat) (y : Nat) : Id Unit (SetMin(a, b, y)) (let t = MinTail(a, b); *t := y) := …   // [Def]
  generic call { c ↦ σ, d ↦ ρ }, MinEq(&c, &d, τ)
  Ω₀ = { c ↦ loan_0, d ↦ loan_1 | a ↦ borrow_0 σ, b ↦ borrow_1 ρ, y ↦ τ }
  W = owners(0) ∪ owners(1) = {c, d};  T_W = Nat × Nat (Ω order)
  left:  { c ↦ loan_0, d ↦ loan_1 | a ↦ ⊥, b ↦ ⊥, y ↦ τ },   SetMin(borrow_0 σ, borrow_1 ρ, τ)      // [Read]×3
         … | a₁ ↦ borrow_0 σ, b₁ ↦ borrow_1 ρ, y₁ ↦ τ },     match *a₁ {…}                          // [Call]
           stuck                                                                                      // [Match] σ
         { c ↦ SMa(σ, ρ, τ), d ↦ SMb(σ, ρ, τ) | … },          ()                                     // [Close] discard; Unit row
         observation ((), SMa(σ, ρ, τ), SMb(σ, ρ, τ))
  right: { … | a ↦ ⊥, b ↦ ⊥, y ↦ τ },                          MinTail(borrow_0 σ, borrow_1 ρ)        // [Let]; [Read]×2
           stuck                                                                                      // [Call], [Match] σ
         { c ↦ Ma(σ, ρ)[loan_k], d ↦ Mb(σ, ρ)[loan_k] | … },   borrow_k MT(σ, ρ)                     // [Close] &T row: the hole in both owners
         { … | …, t ↦ borrow_k τ },                             ()                                    // [Let]; [Read] y; [Access]; [Assign]
         { c ↦ Ma(σ, ρ)[τ], d ↦ Mb(σ, ρ)[τ] | … },              ()                                    // [Drop] t → [End k]: both occurrences
         observation ((), Ma(σ, ρ)[τ], Mb(σ, ρ)[τ])
  G₀ ≡ Eq Nat SMa(σ, ρ, τ) Ma(σ, ρ)[τ] ∧ Eq Nat SMb(σ, ρ, τ) Mb(σ, ρ)[τ]                              // Eq on pairs; Eq Unit () () ≡ ⊤; ⊤ ∧ P ≡ P
  [Split] σ
  Z (σ := Z):   G_Z ≡ Eq Nat τ τ ∧ Eq Nat ρ ρ ≡ ⊤ ∧ ⊤ ≡ ⊤  (N-a);  refl ✓
  S (σ := S σ'): G₀[σ := S σ'] is unchanged except σ ↦ S σ' (N-b).  [Match] S, p := (*a).1;  match *b: [Split] ρ
    S/Z (ρ := Z):   G ≡ Eq Nat (S σ') (S σ') ∧ Eq Nat τ τ ≡ ⊤  (N-c);  refl ✓
    S/S (ρ := S ρ'): G_SS ≡ Eq Nat (S SMa(σ', ρ', τ)) (S Ma(σ', ρ')[τ]) ∧ Eq Nat (S SMb(σ', ρ', τ)) (S Mb(σ', ρ')[τ])   (N-d)
      [Match] S, q := (*b).1;  MinEq(&p, &q, y)
      { c ↦ loan_0, d ↦ loan_1 | a ↦ borrow_0 (S loan_2), b ↦ borrow_1 (S loan_3), y ↦ τ },  args borrow_2 σ', borrow_3 ρ', τ   // [Access]; [Borrow]×2; [Read]
      [Rec] position 1 ✓
      type: Ω_IH = { … | a ↦ borrow_0 (S loan_2), b ↦ borrow_1 (S loan_3), y ↦ τ | a' ↦ borrow_2 σ', b' ↦ borrow_3 ρ', y' ↦ τ }
        W = owners(2) ∪ owners(3) = owners(0) ∪ owners(1) = {c, d}
        left:  SetMin(a', b', y') is stuck on σ' → [Close] Unit row: loan_2 := SMa(σ', ρ', τ), loan_3 := SMb(σ', ρ', τ)
               end every borrow: [End 0], [End 1] → c ↦ S SMa(σ', ρ', τ), d ↦ S SMb(σ', ρ', τ)
        right: MinTail(a', b') is stuck on σ' → [Close] &T row, fresh k: loan_2 := Ma(σ', ρ')[loan_k], loan_3 := Mb(σ', ρ')[loan_k]
               t ↦ borrow_k τ ([Assign]); [Drop] t → [End k], both occurrences; [End 0], [End 1] → c ↦ S Ma(σ', ρ')[τ], d ↦ S Mb(σ', ρ')[τ]
        IH ≡ Eq Nat (S SMa(σ', ρ', τ)) (S Ma(σ', ρ')[τ]) ∧ Eq Nat (S SMb(σ', ρ', τ)) (S Mb(σ', ρ')[τ])
      value: P5, not run: [End 2], [End 3] → ⋆
      IH ≡ G_SS, symbol for symbol ✓
```

`MinEq` is accepted. The proof mirrors the program's own match structure and uses no lemma about `MinTail`. The S arm with `ρ` still unknown works only because (N-b) leaves the goal's sealed programs in exactly the form the IH will later produce.

### 8.5 Owner sets at a call site: a lemma applied to the returned borrow

When a statement's only free borrow is the returned one, the owner set does the work that the parameters did above.

```
WriteTwice : Π(t : &Nat) (y : Nat). Id Unit (*t := y; *t := y) (*t := y)
WriteTwice(t, y) := refl
  [Def]: generic call { e ↦ υ }, WriteTwice(&e, τ): { e ↦ loan_0 | t ↦ borrow_0 υ, y ↦ τ };  W = owners(0) = {e} (`*t` is a free place rooted at t);  both sides → e ↦ τ;  goal ≡ Eq Nat τ τ ≡ ⊤;  refl ✓

Use(a, b, y) := let t = MinTail(a, b); WriteTwice(t, y)          (in any context with a ↦ borrow_0 σ, b ↦ borrow_1 ρ)
  after the let: { c ↦ Ma(σ, ρ)[loan_k], d ↦ Mb(σ, ρ)[loan_k] | …, t ↦ borrow_k MT(σ, ρ) }
  WriteTwice(t, y): [Read] t moved; type at { … | t' ↦ borrow_k MT(σ, ρ), y' ↦ τ }
    W = owners(k) = {c, d}               // loan_k occurs in two owned places
    both sides: t' ↦ borrow_k τ; end every borrow: [End k] → c ↦ Ma(σ, ρ)[τ], d ↦ Mb(σ, ρ)[τ]
    type ≡ Eq Nat Ma[τ] Ma[τ] ∧ Eq Nat Mb[τ] Mb[τ] ≡ ⊤
  value: P5: [End k] with the unchanged MT(σ, ρ) → c ↦ Ma(σ, ρ)[MT(σ, ρ)], d ↦ Mb(σ, ρ)[MT(σ, ρ)]
```

The observation includes both owners automatically, and D16's reflexivity rule removes the padding. This is the shape of meta-model's C2; with `W = {c, d}` the unsound single-owner reading is not available.

## 9. Round-1 findings under v1

| round 1 | v1 | where checked |
|---|---|---|
| F1 [Seal] regress | fixed by the head-call guard (D9) | §3.0, N-b |
| F2 loans inside sealed programs invisible | fixed: loans are variables (D11), and [Access] ends loans inside the content (D19) | §1, §3.4 |
| F3 open hole cannot be normalised | fixed by inert outside loans, modulo wording (H2) | §6 |
| F4 duplicated hole | fixed: [End] substitutes every occurrence, and owners are sets (D18) | §8.1, N-d, §8.4, §8.5 |
| F5 "owner" vacuous | fixed by the recursive definition of `owners` | §4.3, §8.4 |
| F6 "just before the call" | fixed ("after its arguments are evaluated") | all [Close] steps |
| F7 ghost frame, pending bindings, eager clause | obsolete: no ghosts, no pending bindings | §1, §3.5 |
| F8 proofs are run | fixed by P5 (D14) | §4.3, §5, §8.5 |
| F9 footprint of term-local places | fixed ("free place") | §7.1 |
| F10 [Split] on a neutral that is not an abstract value | open | H7 |

## 10. Findings (v1)

No unsoundness and no failed derivation. Each finding gives the place in RULES.md, what I assumed, and the simplest fix.

- **H1. `⋆` is not a value.** §3 [Call] returns `⋆` under P5, but §2's value grammar has no `⋆`, and the value of `refl` is never stated. *Assumed:* `⋆` is the single erased value of every proof, and `refl` evaluates to it. *Fix:* add `⋆` to §2.
- **H2. "Inert, like abstract values" has to reach three rules.** §3 [Seal]. In `Probe`'s Z arm (§6) the run ends with `c ↦ loan_k` (inert). [Access] must not try to end `loan_k` (its borrow is not in the run). [Read] must copy it, although §2 says a value containing a loan is not borrow-free, and it is not a borrow either. [Drop] of `c` must not report "a loan in a dropped owned value". *Assumed:* all three treat an inert loan as an abstract value, which is what "like abstract values" suggests. *Fix:* one sentence: "for [Access], [Read], [Drop] and borrow-freeness, an inert loan is an abstract value".
- **H3. "The head call of `t`" is undefined.** §3 [Seal]. *Assumed:* for a program made by [Close] it is `C`; for a closed-off stuck block it is the call to the anonymous function. *Fix:* say so; every sealed program has one by construction.
- **H4. [Rec]'s "recursive position" for n-ary functions.** §5 [Rec]. `MinTail`, `SetMin` and `MinEq` shrink both borrow parameters. *Assumed:* one position is fixed per definition (I used the first), as in Lean's structural recursion. *Fix:* "a definition has one recursive position, the same for all its recursive calls".
- **H5. [Call-type] should say where the parameters are bound.** §5. "B evaluated at Ω with each xᵢ bound to aᵢ's value": the IH's footprint needs the parameters in a frame *pushed on* the caller's Ω, so that `owners(1)` can follow `loan_1` into `x`'s `borrow_0` and then to `c` (§4.3, §8.4). Substituting values into `B` would lose that. *Fix:* "bound in a frame pushed on Ω (the caller's frames stay visible for owners)". [Def] already says "pushed frame" for the body.
- **H6. State the lemma that refinement commutes with closing off.** §6 (metatheory). Because the head-call guard keeps the *source* syntax of a sealed program whose refined head is stuck on another variable (N-b), two things hold. Successive refinements compose (refine `σ`, then `ρ` = refine both). And a refined stuck program is syntactically what a fresh [Close] on the refined inputs produces. `MinEq`'s S arm relies on the first; every IH-vs-goal comparison relies on the second. It is an instance of the adequacy conjecture and deserves its own statement, since it is the property that makes "bare recursion" work.
- **H7. A match on a place whose content is a sealed program with a live hole.** §3 [Access], §5 [Split]. For [Match], [Access] ends only loans "on the path", so v1 accepts reaching `match m {…}` with `m ↦ B(σ)[loan_k]` while `t` is live (Rust rejects this; D11's permissiveness). If `σ = Z`, the head of `m` *is* `t`'s final value, so matching now would inspect a value that is not yet determined. It is harmless today only because nothing can split on a sealed-program head (round-1 F10: [Split] needs an abstract `σ`), and in a call body the stuck match is discarded by [Close]. *Fix, when F10 is designed:* before a match whose scrutinee's head is a neutral, end the loans inside that neutral (as [Read] does).
- **H8. [Access] for [Match] on a bare loan.** §3 [Access]. After `Probe`'s Z-arm refinement, `m ↦ loan_k`. A later `match m` needs `borrow_k` ended first, but the loan is `m`'s content, not "on the path to" `m`. *Assumed:* the path includes the content's head (meta-model C5 says "path and root"). *Fix:* "on the path to `p`, including the head of `content(p)`".
- **H9. (low) "Tail position" and enclosing lets.** §5 [Split]. `Probe`'s match is followed only by [Let]'s drops. Both readings (tail, or closed off as a stuck block with the arms still checked) accept `Probe` with the same arm checks, so nothing depends on it. *Fix:* say that trailing [Let] drops do not make a match non-tail.
