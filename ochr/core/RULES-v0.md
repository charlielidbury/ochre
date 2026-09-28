# Ochr core, rule set v0

Status: first draft by the lead. Expect it to be wrong in places; that is what the derivers and breakers are for.

## 0. Principles

- **P1 Evaluation, not rewriting.** There is one deterministic call-by-value machine. Definitional equality is "same normal form", where normal forms are what the machine produces on symbolic inputs (normalisation by evaluation). With effects, rewriting-anywhere is not confluent; a fixed evaluation order is.
- **P2 Types read values.** A term inside a type is run hypothetically, on a private copy of the current environment. It may read, borrow and write places, but nothing it does persists, and a type that has been formed is a closed statement about values: later mutation never changes it.
- **P3 Data is copied, borrows are moved.** Reading a place whose content contains no borrow copies it (runtime moves are an optimisation licensed by an affine usage check that lives outside the core). Reading a place holding a borrow moves the borrow out. Reborrowing is explicit: `&*x`, or `&p` for a sub-place `p`.
- **P4 Close off stuck calls.** When a call's body gets stuck on an abstract value, the call is replaced by *sealed programs*: closed source programs that own their state, standing for the call's result and for the final content of each place it borrowed. Sealed programs are neutral terms. They are the backward functions of Aeneas, written in the source language.
- **P5 Frame.** A call can affect only what it is passed (no globals, no interior mutability, no unsafe). This is what makes P4 sound.
- **P6 `Id` observes.** `Id A t u` is not primitive. At an environment Ω it computes to an ordinary equation `Eq` between the *observations* of `t` and `u`: each one's result paired with the final contents of the places the two computations may write.

## 1. Syntax

```
terms  t, u, A, B ::= x                          variable (reading a place: see places)
                    | Prop | Type                 sorts (Prop has definitional proof irrelevance)
                    | Π(x : A). B | λ(x : A). t | t u
                    | fix f (x : A) : B := t      structural recursion (see §6)
                    | Nat | Z | S t | Unit | ()
                    | Eq A t u | refl | ⊤ | ⊥ | t ∧ u | ⟨t, u⟩ | J ...   standard propositional equality (in Prop)
                    | A × B | (t, u)              pairs (used by observations)
                    | &A                          borrow type (A borrow-free; see scope)
                    | p                           read a place
                    | &p                          borrow a place
                    | p := t                      assign
                    | let x = t; u                x is a mutable place in u
                    | t; u                        sequence (= let _ = t; u)
                    | match p { Z => t | S y => u }   case on the content of a place; y is the sub-place p.1
                    | Id A t u                    effect-sensitive equality (derived, §4)
places p ::= x | *p | p.1
```

Scope of the core: the only inductive types are `Nat` and `Unit` (plus pairs and the Prop connectives). `&A` appears only as the type of a variable, parameter or result, never inside another type (no borrows inside data, no borrows of borrows, closures capture only borrow-free values). No shared borrows, no loops.

Pattern variables are **sub-places**, not copies: in `match p { S y => u }`, `y` is an alias for `p.1`. Through a borrow, `match *x { S y => ... }` makes `y` the place `(*x).1`, and `&y` reborrows it.

## 2. Runtime structures

```
values    v, w ::= Z | S v | () | (v, w) | λ-closures | fix-closures | types (as values)
                 | borrow_ℓ v          a borrow; the borrowed content lives *in* the borrow (LLBC style)
                 | loan_ℓ              the hole left behind at the borrowed place
                 | ⊥                   moved out / ended
                 | n
neutrals  n    ::= σ                   abstract value (Lean's fvar)
                 | n v                 stuck application of an abstract function
                 | ⌈t⌉                 sealed program: a closed program t whose run is stuck; may contain loan_k holes
environment Ω  ::= frames of bindings  x : A ↦ v, separated by |
                   ghost owners  x° : A ↦ v  (the caller's side of a borrow parameter, see §5)
                   anonymous pending borrows  _ ↦ borrow_ℓ v  (see [Pop])
```

A value is **borrow-free** if it contains no `borrow`, `loan`. Types of results of `Id` must be borrow-free.

## 3. The machine: ⟨Ω, t⟩ ⇓ r, where r is ⟨Ω', v⟩ or `stuck`

Big-step, deterministic. `content(Ω, p)`: follow `x`, `*p` (through `borrow_ℓ v` to `v`), `p.1` (through `S v` to `v`).

- **[Reorg] end a loan on demand.** Accessing a place whose content, or a prefix of whose path, is `loan_ℓ`: end borrow ℓ first. Find the unique `borrow_ℓ w`; `w` must itself contain no loans (end those first, recursively); replace `borrow_ℓ w` by `⊥` and `loan_ℓ` by `w`. (Aeneas's End-Mut, applied lazily.) Ending loans is also allowed at any other time; the lazy strategy is canonical.
- **[Read]** `⟨Ω, p⟩`: let `v = content(Ω, p)`. If `v` is borrow-free: `⇓ ⟨Ω, v⟩` (copy). If `v` is a borrow: `⇓ ⟨Ω[p ↦ ⊥], v⟩` (move). Reading `⊥` is stuck-with-error (a type error, not a neutral).
- **[Borrow]** `⟨Ω, &p⟩ ⇓ ⟨Ω[p ↦ loan_ℓ], borrow_ℓ v⟩`, `v = content(Ω, p)`, ℓ fresh.
- **[Assign]** `⟨Ω, p := t⟩`: `⟨Ω, t⟩ ⇓ ⟨Ω₁, v⟩`, then `⇓ ⟨Ω₁[p ↦ v], ()⟩`. The old content is dropped (dropping a borrow ends it).
- **[Let]** `⟨Ω, let x = t; u⟩`: `⟨Ω, t⟩ ⇓ ⟨Ω₁, v⟩`; `⟨Ω₁, x ↦ v; u⟩ ⇓ ⟨Ω₂, w⟩`; then drop `x` from Ω₂ (see [Pop] for what dropping means).
- **[App]** `⟨Ω, t u⟩`: evaluate `t` to a closure `λ(x:A).b` (or a `fix`, unfolded once), `u` to `w`; push a frame `[x ↦ w]`; run `b`. If it completes with `v`, pop the frame ([Pop]) and return `v`. If it gets stuck on a neutral match, use [Close].
- **[Pop] dropping bindings.** A dropped owned binding must contain no loans (else the program is rejected: something borrows a dying place). A dropped borrow whose content is loan-free ends (content goes to its loan). A dropped borrow whose content still contains loans (because a borrow into it was returned) moves into the caller's frame as an anonymous pending binding `_ ↦ borrow_ℓ v`; it ends as soon as its content becomes loan-free.
- **[Match]** `⟨Ω, match p { Z => t | S y => u }⟩`: content `Z` → run `t`; content `S v` → run `u[y := p.1]`; content a neutral → `stuck`.
- **[Close] close off a stuck call.** Suppose the body of the call `f w₁ … wₙ` gets stuck. Discard the partial run (restore Ω to just before the call). Let the borrow arguments be `wᵢ = borrow_ℓᵢ uᵢ` (i ∈ I) and write the *canonical call* `C := f a₁ … aₙ` with `aᵢ = &cᵢ` for i ∈ I and `aᵢ = wᵢ` otherwise, and the prefix `L := let cᵢ = uᵢ (i ∈ I)`.
  - Result type borrow-free: the call returns `⌈L; C⌉`, and each `loan_ℓᵢ` is filled with `⌈L; C; cᵢ⌉`.
  - Result type `&T`: take a fresh `k`. The call returns `borrow_k ⌈L; let r = C; *r⌉`, and each `loan_ℓᵢ` is filled with `⌈L; let r = C; *r := loan_k; cᵢ⌉` (a sealed program with a hole: when borrow k ends with final content `w`, the hole becomes `w`).
  - "Filled" means: the borrow `borrow_ℓᵢ` was consumed by the call, and the loan's place now holds the given value.
  - `f` is the function's name if it is a top-level definition, else its closure; abstract functions `σ_f` close off immediately.
- **[Seal] normalising sealed programs.** `nf(⌈t⌉)`: run `t` from the empty environment; if it completes with `v`, the result is `nf(v)`; otherwise `⌈t'⌉` where `t'` is `t` with its embedded values normalised. At type `Unit` every value normalises to `()`.
- **Refinement.** Substituting `σ := Z` or `σ := S σ'` into a value re-normalises every sealed program that mentions `σ`.

## 4. Observation and `Id`

**Footprint.** For terms `t, u` at Ω, `W(t, u)` is the set of owned places they may write: the root owned place of every place appearing under `&_` or on the left of `:=` in `t` or `u`, and the owner of every borrow-typed variable free in `t` or `u`. The **owner** of a borrow is the owned place (a variable not of borrow type, or a ghost `x°`) that holds its loan once all borrows in Ω are ended. The footprint is syntactic, so it is stable under refinement and does not depend on unrelated places in Ω.

**Observation.** `⟦t⟧_Ω^W`: run `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩` (if `t` itself gets stuck outside any call, close it off as if it were the body of a nullary call); end every borrow in Ω' (resolve); the observation is the tuple `(v, Ω'_resolved(k) for k ∈ W)`.

**`Id` computes.**

```
Ω ⊢ Id A t u  ≡  Eq (A × T_W) ⟦t⟧_Ω^W ⟦u⟧_Ω^W        where W = W(t, u), both sides run from the same Ω
```

**`Eq` computes observationally** (conversion rules, all in Prop, which has definitional proof irrelevance):

```
Eq (A × B) (a, b) (a', b') ≡ Eq A a a' ∧ Eq B b b'
Eq Unit a b ≡ ⊤
Eq Nat Z Z ≡ ⊤        Eq Nat (S a) (S b) ≡ Eq Nat a b        Eq Nat Z (S b) ≡ ⊥ ≡ Eq Nat (S a) Z
⊤ ∧ P ≡ P ≡ P ∧ ⊤
```

`refl : Eq A a a`; `J` / transport as in CIC; `⟨h₁, h₂⟩ : P ∧ Q`. Consistency is inherited from the proof-irrelevant set model of Lean, in which each of these conversions identifies two propositions with the same truth value.

## 5. Typing: Ω ⊢ t ⇓ v : A ⊣ Ω'

Typing is the machine run on symbolic inputs, with case splitting and type information. It returns the result value (later types may depend on it) and the output environment.

- **[Lam] checking `λ(x:A). t` (or `fix`) against `Π(x:A). B`.** Open a frame. If `A = &T`: bind a ghost owner `x° : T ↦ loan_0` and `x : &T ↦ borrow_0 σ`. Otherwise bind `x : A ↦ σ`. Evaluate the goal `B` *once, at entry* (P2: the goal is a snapshot). Check the body; its result's type must be convertible to the entry goal (as refined by any case splits on the way).
- **[Split] a match in the checked term on an abstract value.** Check each arm with the refinement (`σ := Z`, resp. `σ := S σ'`) applied to Ω, to the goal and to every stored type.
- **[Join] a match that is not in tail position.** The arms' output environments are joined by anti-unification: positions where the arms' values differ become fresh abstract values. The loan/borrow structure must be identical in all arms, after ending whatever loans can be ended; otherwise the program is rejected and the programmer duplicates the continuation into the arms by hand.
- **[App] typing a call `f u` with `f : Π(x:A). B`.** The result *value* comes from the machine (unfold, or [Close] if stuck). The result *type* is `B` evaluated at the call site, with `x` bound to the argument (a borrow argument is moved into `x`). This is where an induction hypothesis gets its type, and it is evaluated in the *caller's* environment, so the caller's borrow structure around the argument is visible to it. (Soundness of this rests on the frame lemma, §7.)
- **[Ref] reading ⊥ or dropping an owned place with an outstanding loan** is a type error. This is the borrow checker.

## 6. Recursion

`fix f (x : A) : B := t`: every recursive call must pass, in the recursive position, either `&y` or `y` where `y` is a pattern variable (sub-place) bound by a match on the content of the parameter, possibly through several matches. Note (from 01 §8): the measure is the value at entry; a write to the parameter before the match can break this, and the symbolic execution is where that gap is closed.

## 7. Metatheory to establish (conjectures for now)

- **Canonical observation.** The resolved observation does not depend on the order in which loans are ended.
- **Frame.** Running a computation in a larger environment is the same as running it in the minimal environment containing its footprint and wrapping the result back into the larger one. [App] and [Close] rest on this.
- **Model.** A translation into CIC (with proof-irrelevant Prop) in which places become state-passing, sealed programs become applications of backward functions, and `Id` becomes `Eq` on observations; typing and conversion are preserved. Consistency follows. The programmer never sees the backward functions; only the metatheory does.
- **Adequacy.** For every instantiation of the abstract values, concrete evaluation agrees with the symbolic normal form (the symbolic machine commutes with substitution).

## 8. Examples (the test suite)

```
Add      : Π(x : Nat) (y : Nat). Nat
Add x y  := AddM &x y; x

AddMZero : Π(x : &Nat). Id Unit (AddM x 0) ()
AddMZero x := match *x { Z => refl | S p => AddMZero &p }

AddZero  : Π(x : Nat). Id Nat (Add x 0) x
AddZero x := match x { Z => refl | S p => AddZero p }

TailM    : Π(x : &Nat). &Nat           -- borrow of the final Z node
TailM x  := match *x { Z => x | S p => TailM &p }

AddM'    : Π(x : &Nat) (y : Nat). Unit
AddM' x y := let t = TailM x; *t := y

AddMEq   : Π(x : &Nat) (y : Nat). Id Unit (AddM x y) (AddM' x y)
AddMEq x y := match *x { Z => refl | S p => AddMEq &p y }

AddMEqOwned : Π(x : Nat). Id Unit (AddM &x 0) (AddM' &x 0)
AddMEqOwned x := AddMEq &x 0
```

- E1: `AddM`, `AddMZero`, `Add`, `AddZero`.
- E2: `TailM`, `AddM'`, `AddMEq`, `AddMEqOwned` (returned borrow).
- E3: `AddToOne b x1 x2 y := let r = match b {...}; AddM r y` (needs a Bool, or encode with Nat) must be rejected by [Join]; the hand-duplicated version accepted.
- E4: `Twice (f : Π(_:Unit). Unit) := f (); f ()` with an abstract `f`.
- E6 (must be rejected or unprovable): use of a moved borrow; a proof formed after a mutation checked against the entry goal (`λx:&Nat. (*x := 5; refl) : Π(x:&Nat). Id Nat *x 5`); `Id Nat Z (S Z)`; `Id Unit (AddM &x 0) (AddM &x 1)`.
