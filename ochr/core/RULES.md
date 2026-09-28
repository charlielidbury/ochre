# Ochr core, rule set v1.1

v1.1 (from breaker-close A1, A4): [Close] states its precondition (argument contents are loan-free, which [Access] guarantees); [Rec] requires `f` to occur only as the head of a call.

Supersedes v0 (kept as `RULES-v0.md`). Changes are driven by round-1 reports in `notes/` and logged in `DECISIONS.md` (D9 onwards). Universes: `Prop : Type_0 : Type_1 …`, never `Type : Type`. The model (notes/meta-model.md) needs `propext`, which Lean has.

## 0. Principles

- **P1 Evaluation, not rewriting.** One deterministic call-by-value machine. Definitional equality is "same normal form", normal forms being what the machine produces on symbolic inputs.
- **P2 A formed type is a closed statement.** A type is evaluated once, when it is formed, against the current environment. Everything it mentions from outside is captured by value (a Π-type is a closure, like a λ). Later mutation never changes it. The only thing ever evaluated "later" is a Π-type's *parameters*, bound at each call.
- **P3 Data is copied, borrows are moved.** Reading a place whose content has no borrows copies it. Reading a place holding a borrow moves the borrow out. Reborrowing is explicit (`&*x`, `&p`).
- **P4 Close off stuck computations.** A call whose body is stuck on an abstract value is replaced by *sealed programs*: closed source programs that own their state, one for the result and one for the final content of each place the call borrowed.
- **P5 Proofs are not run.** A call whose result type is a proposition is erased at runtime, so the machine does not run it either: its borrow arguments come back unchanged.
- **P6 `Id` observes.** `Id A t u` computes to `Eq` between the observations of `t` and `u`, each run on its own copy of the current environment.

## 1. Syntax

```
terms  t, u, A, B ::= x | Prop | Type_i
                    | Π(x₁:A₁ … xₙ:Aₙ). B            n-ary dependent function type
                    | fix f (x₁:A₁ … xₙ:Aₙ) : B := t  n-ary, possibly recursive function (λ when f is unused)
                    | t(u₁, …, uₙ)                    saturated call
                    | Nat | Z | S t | Unit | () | A × B | (t, u) | t.1 | t.2
                    | Eq A t u | refl | J(A, P, h, t) | ⊤ | P ∧ Q | ⟨h, k⟩     (Eq, ⊤, ∧ live in Prop)
                    | &A                                borrow type (A borrow-free)
                    | p | &p | p := t | let x = t; u | t; u
                    | match p { Z => t | S y => u }      y is the sub-place p.1, not a copy
                    | Id A t u
places p ::= x | *p | p.1
```

Scope: inductive types are `Nat` and `Unit`, plus pairs and the Prop connectives. `&A` is the type of a variable, parameter or result only, never inside another type (no borrows inside data, closures capture no borrows). No shared borrows, no loops. `Prop` has definitional proof irrelevance and is erased at runtime.

## 2. Runtime structures

```
values    v, w ::= Z | S v | () | (v, w) | closures | types | borrow_ℓ v | loan_ℓ | ⊥ | n
neutrals  n    ::= σ | ⌈t⌉
environment Ω  ::= a stack of frames of bindings  x : A ↦ v
```

- `borrow_ℓ v`: a borrow; the borrowed content lives in the borrow (LLBC). `loan_ℓ`: the placeholder at the borrowed place. **A loan is a variable bound by its borrow**: it may occur anywhere inside a value, including inside sealed programs, and more than once inside sealed programs.
- `σ`: an abstract value (Lean's fvar). `⌈t⌉`: a *sealed program*, a closed program whose run is stuck.
- `⊥`: a place that has been moved out of.
- A value is *borrow-free* if it contains no `borrow_ℓ` and no `loan_ℓ`.

## 3. The machine: ⟨Ω, t⟩ ⇓ ⟨Ω', v⟩, or stuck

- **[End ℓ]** Replace `borrow_ℓ v` by `⊥` and substitute `v` for every occurrence of `loan_ℓ`. (No side condition: loans inside `v` travel with it. Loans are variables.)
- **[Access]** Before reading, borrowing, assigning or matching a place `p`: end every borrow whose loan occurs on the path to `p`; before reading, borrowing or assigning `p` also end every borrow whose loan occurs inside `content(p)`. (This is the borrow checker: the ended borrower becomes `⊥`, and any later use of it is an error.)
- **[Read]** `p`: content borrow-free → copy; content a borrow → move (`p ↦ ⊥`). Reading `⊥` is an error.
- **[Borrow]** `&p` ⇓ `borrow_ℓ v`, with `p ↦ loan_ℓ`, ℓ fresh.
- **[Assign]** `p := t`: evaluate `t` to `v`; drop the old content of `p` ([Drop]); `p ↦ v`; result `()`.
- **[Let]** `let x = t; u`: evaluate `t` to `v`, bind `x ↦ v`, run `u`, [Drop] `x`.
- **[Drop]** Dropping a value: each borrow in it ends ([End]); a loan in a dropped *owned* value is an error (something borrows a dying place).
- **[Call]** `f(w₁,…,wₙ)` with `f = fix f (x̄:Ā):B := b`: push a frame `x̄ ↦ w̄`, run `b`, pop the frame ([Drop] its bindings), return the result. If `B` is a proposition, do not run `b`: return `⋆` and end every borrow argument unchanged (P5). If `b` gets stuck on a neutral, use [Close].
- **[Match]** `match p {…}`: head of `content(p)` is `Z` → first arm; `S v` → second arm with `y := p.1`; a neutral → stuck.
- **[Close]** The call `f(w̄)`, after its arguments are evaluated, has a stuck body. Precondition: every argument's content is loan-free (guaranteed by [Access], which ended those loans when the argument was read or borrowed; without it a live loan would be copied into a sealed program, breaker-close A1). Discard the partial run. Let `I` be the positions holding borrows, `wᵢ = borrow_ℓᵢ uᵢ`. Write `L := let cᵢ = uᵢ (i ∈ I)` and `C := f(ā)` with `aᵢ = &cᵢ` for i ∈ I, `aᵢ = wᵢ` otherwise. Then the call returns, and each `loan_ℓᵢ` is substituted (the borrow having been consumed), according to the result type `B`:

  | `B` | result | each `loan_ℓᵢ` becomes |
  |---|---|---|
  | `Unit` | `()` | `⌈L; C; cᵢ⌉` |
  | borrow-free `D` | `⌈L; C⌉` | `⌈L; C; cᵢ⌉` |
  | `&T` (fresh k) | `borrow_k ⌈L; let r = C; *r⌉` | `⌈L; let r = C; *r := loan_k; cᵢ⌉` |

- **[Seal]** Values are kept in normal form. `nf(⌈t⌉)`: run `t` from the empty environment, with the *head call of `t` not eligible for [Close]* (calls inside its body are); loans whose borrow is outside the run are inert, like abstract values. If the run completes, `nf(⌈t⌉)` is its value; otherwise `⌈t'⌉` with the values inside `t` normalised. Substituting a refinement `σ := Z` or `σ := S σ'`, or ending a loan, re-normalises.
- **Stuck blocks.** A stuck match that is not the body of a call (in a type-level term, or a non-tail match in a checked program after its arms have been checked, §5) is closed off as the body of a call to an anonymous function of its free places: borrow variables it uses and places it writes become borrow arguments, places it only reads become value arguments.

## 4. Observation and `Id`

- **Owners.** `owners(ℓ)` is a *set*: for each occurrence of `loan_ℓ` (a hole may occur several times, inside sealed programs), follow it outward. An occurrence inside the content of `borrow_m` contributes `owners(m)`; an occurrence inside an owned binding `x` contributes `x`.
- **Footprint.** `W(t, u)`: for every *free* place of `t` or `u` that appears under `&_`, on the left of `:=`, or is a borrow-typed variable, its owners (for a place rooted at an owned variable `x`, that is `{x}`; for one rooted at a borrow variable holding `borrow_ℓ`, `owners(ℓ)`). Observing only some owners of a hole is unsound (meta-model C2).
- **Observation.** `⟦t⟧_Ω^W`: on a private copy of `Ω`, run `t` (closing it off as a stuck block if needed) to `⟨Ω', v⟩`, end every borrow in `Ω'`, and return `(v, Ω'(k) for k ∈ W)` in the order of Ω.
- **`Id` computes.** `Id A t u ≡ Eq (A × T_W) ⟦t⟧^W ⟦u⟧^W`, `W = W(t,u)`, both run from the same Ω on independent copies (when `W` is empty the pair is just `A`). `A` must be borrow-free.
- **`Eq` computes** (all in Prop):
  ```
  Eq (A × B) (a, b) (a', b') ≡ Eq A a a' ∧ Eq B b b'
  Eq A a b ≡ ⊤          when a ≡ b
  ⊤ ∧ P ≡ P ≡ P ∧ ⊤
  ```
  `refl : ⊤`. `J` / transport and `cong` as in CIC. Each conversion identifies two propositions with the same truth value, so the proof-irrelevant set model of Lean validates it.

## 5. Typing

Typing is the machine on symbolic inputs, plus case splitting.

- **[Call-type]** At Ω, the type of `f(ā)` with `f : Π(x̄:Ā). B` is `B` evaluated at Ω with each `xᵢ` bound to `aᵢ`'s value (a borrow argument moved into `xᵢ`). Each `aᵢ` must have type `Aᵢ`. The free variables of `B` other than `x̄` were captured when the Π-type was formed (P2).
- **[Def]** `fix f (x̄:Ā):B := b` is checked at its *generic call*: an environment with a fresh owned place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ`, and the call `f(ā)` with `aᵢ = &cᵢ` or `σᵢ`. The goal is the [Call-type] of that call. The body runs in a pushed frame; its result's type must convert to the goal (as refined by splits).
- **[Split]** When the checked program matches on a place whose content head is an abstract `σ`: check each arm with the refinement `σ := Z` (resp. `S σ'`) applied to Ω, the goal and all stored types. If the match is not in tail position, the rest of the program is checked once, from the state in which the match is closed off as a stuck block (§3). No anti-unification.
- **[Rec]** In the body of `fix f`, `f` occurs only as the head of a call (it never escapes as a value; breaker-close A4), and each recursive call must pass, in the recursive position, a value (or a borrow whose content is a value) that is a *strict subterm of that parameter's entry value* `σ`, as refined so far.
- **Errors (the borrow checker):** reading `⊥`, a loan in a dropped owned value, an argument not of the parameter's type.

## 6. Metatheory to establish

Canonical observation (independence from loan-ending order); frame lemma; model into CIC with proof-irrelevant Prop (backward functions appear only there); consistency; adequacy (the symbolic machine commutes with substitution, so concrete runs agree with symbolic normal forms).

## 7. Examples

As in v0 §8, with `λ` written as non-recursive `fix` and calls saturated: `AddM(x, y)`, `AddMZero(x)`, `Add(x, y) := AddM(&x, y); x`, `AddZero`, `TailM`, `AddM'`, `AddMEq`, `AddMEqOwned`. `AddZero`'s S arm is `cong S (AddZero(p))` (no Nat-specific Eq rule in v1).
