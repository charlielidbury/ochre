# Ochr core, rule set v2.0

History: v2.0 also has D49 (clarifications of D45 from the paper pass): a proof scrutinee's type is its stored type as refined, which must normalise to an inductive head (a neutral type is a type error, failing safe); a match on a several-constructor Prop inductive is erased and each arm must be a declared proof; data fields of a proof are bound to fresh abstract values; constructors take their inductive's parameters as leading arguments (surface syntax may omit inferable ones) and values record them; a zero-arm match yields ⋆; a proof's value is always ⋆. v2.0 also has D48 (reviewer-3): `&A` is well-formed only for a data type `A` (a declared Type₀ inductive or instance of one, `Nat`, `Unit`, `×`; never a universe, Π-type or proposition), and `&` appears only at the top of a syntactically declared type, never produced by computation; conversion compares Π-types by generic instantiation of their binders. v2.0 (D45–D47, user request 2026-09-29: uniform inductive definitions over a small rule count): the propositional connectives are ordinary inductive definitions — `False` (no constructors), `True`, `And` — via inductive declarations that may be in `Prop`, may have zero constructors, and may take uniform parameters; matching on a Prop-sorted scrutinee is by its type (subsingleton elimination); distinct constructors are disjoint in `Eq`. `Eq` stays primitive. v1.9 also has D44 (reviewer-2): a function type whose codomain is a borrow `&T` must have at least one borrow parameter (Ochr has no `'static` borrows; a returned borrow derives from a borrow argument, Rust's lifetime-elision rule). v1.9 (D41): fail-safe for erasure — an erased term may not write, borrow or move a place that outlives it except by passing it to an erased call; checked by the machine. v1.8 also has D40 (a stuck block is erased iff each arm is, lean-checker P2). v1.8 (D37–D39, breaker-fresh-v16 X3–X5): generalisation records are global and fresh abstract values are never reused, even across private copies; the observation of a borrow-typed result writes a fresh abstract value through it first; [Seal]'s head guard also covers neutral-headed calls. v1.7 also has D36: inductive declarations are strictly positive in the simplest form (constructor fields are first-order data: earlier inductives, the type itself, `Nat`, `Unit`, `×`; no `Π`, no `&`). v1.7 (D35, formal-appendix BoomL/BoomB): erasure is a purely syntactic property — a function's class (top-level or local) is read from its codomain *term* and that term's declared sort, never by evaluating it; a stuck block is erased exactly when its match would be; [Close]'s row is read from the declared codomain. v1.6 (D34, lean-checker G1): generalising a sealed program in [Split] is recorded as a refinement of that neutral, so later re-derivations of the same closed program are replaced too; general inductive types (several constructors and fields) are in scope. v1.5 (D28–D33, from breaker-fresh F1–F5 and reviewer-1): erasure is decided per definition and per syntactic position, never from a normal form, and universes are not cumulative; matching ends loans anywhere inside a neutral head; closures are compared by the observation of their generic call; `f` is not in scope without `by`; pattern variables are resolved to sub-places before captures and footprints; type-level matches are type-checked like any term; an error while normalising a sealed program is a type error. v1.4 (D27, from deriver-e5): proof parameters are bound to ⋆ at the generic call; parameter types are evaluated left to right and stored with their bindings; a neutral of sort Prop is a type; reading `p.1` needs a known `S` head. v1.3 (D26): P2 and P5 merge into one principle, *erased terms run on a private copy*, replacing v1.2's static [Proof] check (meta-model-v1 R1/§1.5); a call with a neutral head closes off at once; [Rec] covers calls inside nested functions; Π-types capture no borrows. v0 → `RULES-v0.md`. v1 after round 1 (DECISIONS D9–D19). v1.1: [Close] precondition, [Rec] head-only (breaker-close A1, A4). v1.2 after round 2 (D20–D24): proofs may not write outside themselves (P5 becomes a theorem), [Call-type] after arguments, arguments in temporaries, stuck blocks capture like closures, generalise-then-split, explicit `J` endpoints, declared decreasing parameter, all types formed on a private copy, wording fixes (deriver-e1-v1 G1–G10, deriver-e2-v1 H1–H9, breaker-close-v1 N1–N8).

Universes: `Prop : Type_0 : Type_1 …`, never `Type : Type`. `Prop` has definitional proof irrelevance and is erased at runtime. The model (notes/meta-model.md) needs `propext`.

## 0. Principles

- **P1 Evaluation, not rewriting.** One deterministic call-by-value machine. Definitional equality is "same normal form", normal forms being what the machine produces on symbolic inputs. The normal form of a function value is the observation of its generic call (as in [Def] and `Id`: its result together with the final contents of the generic owned places `cᵢ`), plus its captured values; so two functions are convertible only if they have the same effects (D30). A comparison that needs itself (a recursive function whose generic call is stuck on its own sealed call) answers "not convertible": sound and incomplete; assuming equality coinductively would identify any two recursive functions of the same type (lean-checker, v1.5 round).
- **P2 Erased terms leave no trace.** Types and proofs are erased at runtime. *Which* terms are erased is a syntactic property, never decided from a normal form (D28, D35): a function (top-level or local) returns types if its codomain term is syntactically a sort, and returns proofs if its codomain term's *declared* sort is `Prop` (the sort obtained by typing the codomain term from the declared types of its heads, without normalising it); a call is erased iff its callee's class says so. Any other term is erased iff it stands in a type position (an annotation, a Π domain or codomain, the type slots of `Eq`, `Id`, `J`, `let x : T`) or its declared type has sort `Prop`. A stuck block is erased exactly when *each of its arms* would be erased by this rule (not by the call rule applied to its computed codomain, and not by a type inferred from the arms, which is computed: lean-checker P2); an annotated `let x : T = match …` with `T` of declared sort `Prop` is erased as a whole, on both paths. Universes are not cumulative (`Prop` is not a subtype of `Type_0`); this is load-bearing. Erased terms so the machine evaluates them on a *private copy* of the environment, argument evaluation included, and discards the copy. A formed type is therefore a closed statement: everything it mentions from outside is captured by value (a Π-type is a closure over values, and may not capture a borrow), later mutation never changes it, and only a Π-type's parameters are bound later, at each call. A proof may mutate places it creates itself on its copy, but (D41) an erased term may not write, borrow or move a place that outlives it except by passing it to an erased call, and the machine checks this: an erased term that would do so is a type error. So running a proof and skipping it are indistinguishable, and the machine may skip it; and any disagreement between two evaluation paths about *whether* a term is erased becomes a type error on the path that erases it, never a closed proof of false.
- **P3 Data is copied, borrows are moved.** Reading a place whose content has no borrows copies it. Reading a place holding a borrow moves the borrow out. Reborrowing is explicit (`&*x`, `&p`).
- **P4 Close off stuck computations.** A call whose body is stuck on an abstract value is replaced by *sealed programs*: closed source programs that own their state, one for the result and one for the final content of each place the call borrowed.
- **P5 (merged into P2 in v1.3.)**
- **P6 `Id` observes.** `Id A t u` computes to `Eq` between the observations of `t` and `u`, each run on its own copy of the current environment.

## 1. Syntax

```
terms  t, u, A, B ::= x | Prop | Type_i
                    | Π(x₁:A₁ … xₙ:Aₙ). B                   n-ary dependent function type
                    | fix f (x₁:A₁ … xₙ:Aₙ) : B by xⱼ := t  n-ary function; `by xⱼ` names the decreasing parameter; without `by`, `f` is not in scope in `t` (a λ); `f` is never in scope in `Ā` or `B`
                    | t(u₁, …, uₙ)                          saturated call
                    | Nat | Z | S t | Unit | () | A × B | (t, u) | t.1 | t.2
                    | Eq A t u | refl | J(A, a, b, P, h, t)                       (Eq is primitive, in Prop)
                    | D(ā) | C(t₁, …, tₖ) | match p {}                                 inductive types (with parameters ā), constructors, zero-arm match
                    | &A                                      borrow type (A borrow-free)
                    | p | &p | p := t | let x = t; u | let x : A = t; u | t; u
                    | match p { Z => t | S y => u }            y is the sub-place p.1, not a copy
                    | C(t₁, …, tₖ) | match p { C₁(ȳ₁) => t₁ | … }   general inductives: constructors; one arm per constructor, ȳ the field places p.g
                    | Id A t u
places p ::= x | *p | p.1 | p.g                              (p.g: field g of a constructor value)
declarations  inductive D (a₁ : A₁ …) : s := C₁(g₁ : B₁, …) | …   s ∈ {Type₀, Prop}; zero or more constructors; uniform parameters ā (D45, D46); fields first-order data or parameters (D36)
library       inductive False : Prop                              (no constructors)
              inductive True : Prop := I                          (refl is notation for I)
              inductive And (P : Prop) (Q : Prop) : Prop := Intro(l : P, r : Q)   (P ∧ Q, ⟨h, k⟩ are notation)
```

A Π-type whose codomain is `&T` must have at least one parameter of borrow type (D44). Scope: user-declared inductive types with several constructors and several fields, whose field types are first-order data (inductives already declared, the type being declared, `Nat`, `Unit`, `×`; no `Π` and no `&`: strict positivity in its simplest form, D36) (sub-places `p.f`; [Split] refines `σ` to `C(σ₁…σₖ)`; [Rec] strict subterms range over all fields), `Nat`, `Unit`, pairs and the Prop connectives. `&A` is the type of a variable, parameter or result only, never inside another type (no borrows inside data; closures capture no borrows). No shared borrows, no loops.

## 2. Runtime structures

```
values    v, w ::= Z | S v | () | (v, w) | ⋆ | closures | types | borrow_ℓ v | loan_ℓ | ⊥ | n
neutrals  n    ::= σ | ⌈t⌉
environment Ω  ::= a stack of frames of bindings  x : A ↦ v
```

- `borrow_ℓ v`: a borrow; the borrowed content lives in the borrow (LLBC). `loan_ℓ`: the placeholder at the borrowed place. **A loan is a variable bound by its borrow**: it may occur anywhere inside a value, and more than once inside sealed programs.
- `σ`: an abstract value (Lean's fvar). `⌈t⌉`: a *sealed program*, a closed program whose run is stuck; a sealed program of sort `Prop` (e.g. a stuck call of a Prop-valued function such as `Le(σ, σ')`) is a type. `⋆`: the (irrelevant) value of a proof, e.g. of `refl`.
- `⊥`: a place that has been moved out of.
- A value is *borrow-free* if it contains no `borrow_ℓ` and no live `loan_ℓ` (inert loans, see [Seal], count as borrow-free).

## 3. The machine: ⟨Ω, t⟩ ⇓ ⟨Ω', v⟩, or stuck

- **[End ℓ]** Replace `borrow_ℓ v` by `⊥` and substitute `v` for every occurrence of `loan_ℓ`. No side condition: loans inside `v` travel with it.
- **[Access]** Before reading, borrowing, assigning or matching a place `p`: end every borrow whose loan occurs on the path to `p`, at the head of `content(p)`, or anywhere inside a neutral at the head of `content(p)` (a loan's position inside a neutral is unknown, so it is treated as the head); before reading, borrowing or assigning `p`, also end every borrow whose loan occurs anywhere inside `content(p)`. This is the borrow checker: an ended borrower becomes `⊥`, and any later use of it is an error.
- **[Read]** `p`: content borrow-free → copy; content a borrow → move (`p ↦ ⊥`). Reading `⊥` is an error, and so is reading `p.1` when the head of `content(p)` is not `S` (e.g. after the parent was reassigned).
- **[Borrow]** `&p` ⇓ `borrow_ℓ v`, with `p ↦ loan_ℓ`, ℓ fresh.
- **[Assign]** `p := t`: evaluate `t` to `v`; drop the old content of `p` ([Drop]); `p ↦ v`; result `()`.
- **[Let]** `let x = t; u`: evaluate `t` to `v`, bind `x ↦ v`, run `u`, [Drop] `x`.
- **[Drop]** Dropping a value: each borrow in it ends ([End]); a live loan in a dropped *owned* value is an error (something borrows a dying place).
- **[Call]** `f(u₁,…,uₙ)` with `f = fix f (x̄:Ā):B … := b`: evaluate the arguments left to right, each into a fresh temporary binding of the current frame (so that [Access] can see and end them); then push a frame `x̄ ↦ w̄` (moving the temporaries' contents), run `b`, pop the frame ([Drop] its bindings), return the result. A call to a function whose class (P2) is "returns proofs" or "returns types" is erased: by P2 it is typed on a private copy and leaves the environment unchanged; a proof call returns `⋆`. A call whose head is a neutral (an abstract function `σ_f`, or a sealed program) is stuck at once and closed off, except as the head call of a sealed program being normalised, where [Seal]'s guard applies and the sealed program stays as it is (D39). If `b` gets stuck on a neutral, use [Close].
- **[Match]** `match p {…}`: head of `content(p)` is `Z` → first arm; `S v` → second arm with `y := p.1`; a neutral → stuck.
- **[Close]** The call `f(w̄)`, at the point where its arguments have been evaluated, has a stuck body. Precondition: every argument's content is loan-free (guaranteed by [Access]). Discard the partial run. Let `I` be the positions holding borrows, `wᵢ = borrow_ℓᵢ uᵢ`. With fixed names `cᵢ`, write `L := let cᵢ = uᵢ (i ∈ I)` and `C := f(ā)` with `aᵢ = &cᵢ` for i ∈ I, `aᵢ = wᵢ` otherwise. The call returns, and each `loan_ℓᵢ` is substituted (its borrow having been consumed), according to the *declared* result type `B` (syntactically `Unit`, `&T`, or anything else):

  | `B` | result | each `loan_ℓᵢ` becomes |
  |---|---|---|
  | `Unit` | `()` | `⌈L; C; cᵢ⌉` |
  | borrow-free `D` | `⌈L; C⌉` | `⌈L; C; cᵢ⌉` |
  | `&T` (fresh k) | `borrow_k ⌈L; let r = C; *r⌉` | `⌈L; let r = C; *r := loan_k; cᵢ⌉` |

  `f` is a top-level name, or, for a stuck block, the anonymous function below.
- **[Seal]** Values are kept in normal form. For a sealed program `⌈L; C; K⌉` with head call `C`: run it from the empty environment, with `C` itself not eligible for [Close] (calls made inside `C`'s body are). A loan whose borrow lives outside the run is *inert*: it behaves like an abstract value ([Access] does not end it, [Read] copies it, [Drop] does not complain). If the run completes, the normal form is its value; if it gets stuck, it is the sealed program with its embedded values normalised; if it hits a borrow error, that is a type error at the point that triggered the normalisation. Substituting a refinement (`σ := Z`, `σ := S σ'`) or ending a loan re-normalises.
- **Stuck blocks.** A stuck match that is not the body of a call (in a type-level term, or a non-tail match in a checked program after [Split], §5) is closed off as a call to an anonymous function of its free places, which it captures as Rust infers closure captures, on maximal place prefixes: a place the block moves out of in any arm is passed by value (moved); otherwise a place it writes or borrows (appears under `&_` or left of `:=`) in any arm is passed as `&`; otherwise a place it reads is passed by value (copied). Its result type is the match's type (annotate with `let x : T = …` if it cannot be inferred from the arms). Before captures are computed, every pattern variable is resolved to the sub-place it denotes (`p ↦ (*x).1`), so a write through a pattern variable is a write to the scrutinee's place (D32). Only matches whose arms have been checked by [Split] are closed off this way; this includes matches inside types, since types are type-checked like any other term (D33).

## 4. Observation and `Id`

- **Owners.** `owners(ℓ)` is a *set*: for each occurrence of `loan_ℓ`, follow it outward. An occurrence inside the content of `borrow_m` contributes `owners(m)`; one inside an owned binding `x` contributes `x`.
- **Footprint.** `W(t, u)`: after resolving pattern variables to the sub-places they denote, for every *free* place of `t` or `u` that appears under `&_`, on the left of `:=`, or is a borrow-typed variable, its owners (`{x}` for a place rooted at an owned variable `x`; `owners(ℓ)` for one rooted at a borrow variable holding `borrow_ℓ`). Observing only some owners of a hole is unsound (meta-model C2).
- **Observation.** `⟦t⟧_Ω^W`: on a private copy of `Ω`, run `t` (closing it off as a stuck block if needed) to `⟨Ω', v⟩`; if `v` is a borrow `borrow_k u` (a borrow-typed result, as when comparing borrow-returning functions by D30), first observe `u` as the result and write a fresh abstract value through the borrow (`*r := σ_new`), so that where the borrow points is observed through its owners (D38); end every borrow in `Ω'`, and return `(v, Ω'(k) for k ∈ W)` in the order of Ω.
- **`Id` computes.** `Id A t u ≡ Eq (A × T_W) ⟦t⟧^W ⟦u⟧^W`, `W = W(t,u)`, both run from the same Ω on independent copies (when `W` is empty the pair is just `A`). `A` must be borrow-free.
- **`Eq` computes** (all in Prop):
  ```
  Eq (A × B) (a, b) (a', b') ≡ And(Eq A a a', Eq B b b')
  Eq A a b ≡ True       when a ≡ b
  Eq D (C ā) (C' b̄) ≡ False   when C ≠ C' are distinct constructors of D (D47)
  And(True, P) ≡ P ≡ And(P, True)
  ```
  `refl : True` (it is `True`'s constructor `I`). `J(A, a, b, P, h, t) : P(b)` for `h : Eq A a b`, `t : P(a)` (endpoints explicit, since `Eq A a a` computes to `⊤`). Each conversion identifies two propositions with the same truth value, so the proof-irrelevant set model of Lean validates it.

## 5. Typing

Typing is the machine on symbolic inputs, plus case splitting. The typing rules for the basic forms (read, borrow, assign, constructors, pairs, `refl`, `J`, `Eq`, `Id`, Π, universes) are the evident ones and are listed in the paper; the rules below are the non-standard ones.

- **[Call-type]** At the point where the arguments of `f(ā)` have been evaluated (the point [Close] restores to), with `f : Π(x̄:Ā). B`: push a frame binding each `xᵢ` to `aᵢ`'s value (a borrow argument moved into `xᵢ`), evaluate `B` there on a private copy, and pop. That is the call's type. Each `aᵢ` must have type `Aᵢ`, evaluated with the earlier parameters bound. The free variables of `B` other than `x̄` were captured when the Π-type was formed (P2).
- **[Def]** `fix f (x̄:Ā):B … := b` is checked at its *generic call*: an environment with a fresh owned place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ`, and the call `f(ā)` with `aᵢ = &cᵢ` for borrow parameters, `aᵢ = ⋆` for parameters whose type is a proposition (proof irrelevance: every proof value is ⋆, so sealed programs embedding proofs compare equal), and `aᵢ = σᵢ` otherwise. Parameter types are evaluated left to right with the earlier parameters bound, and stored with their bindings, where [Split] refines them. The goal is the [Call-type] of that call. The body runs in the pushed frame, which is then popped with [Drop]; the result's type must convert to the goal (as refined by splits).
- **[Split]** (A match's result type is the same in every arm after refinement, or given by an annotation `let x : T = match …`, which each arm is checked against, refined.) When the checked program matches on a place whose content head is an abstract `σ`: check each arm with the refinement `σ := Z` (resp. `S σ'`, σ' fresh) applied to Ω, the goal and all stored types. If the head is a neutral that is not an abstract value (a sealed program), first generalise it: record the refinement `⌈n⌉ := σ` for a fresh `σ` of the matched place's type, which replaces every occurrence of that closed program in Ω, the goal and all stored types, *and every occurrence later re-derived* when sealed programs are re-normalised (a sealed program is a closed deterministic computation, so every derivation of it denotes the same value), then split on `σ`. Refinements are thus knowledge about neutrals, abstract values and sealed programs alike (D34). Generalisation records are global: one made while forming a type on a private copy survives the copy, and fresh abstract values are never reused (D37). If the match is not in tail position (trailing drops do not count), the rest of the program is checked once, from the state in which the match is closed off as a stuck block (§3).
- **[Rec]** In the body of `fix f … by xⱼ`, including inside nested functions and block arms, `f` occurs only as the head of a call, and every recursive call passes, in position `j`, a value (or a borrow whose content is a value) that is a *strict subterm of `xⱼ`'s entry value* `σⱼ`, as refined so far.
- **Errors (the borrow checker):** reading `⊥`, a live loan in a dropped owned value, an argument not of the parameter's type.

## 6. Metatheory to establish

Canonical observation (independence from loan-ending order); frame lemma; refinement commutes with closing off (deriver-e2-v1 H6); model into CIC with proof-irrelevant Prop and propext (backward functions appear only there); consistency; adequacy (the symbolic machine commutes with substitution, so concrete runs agree with symbolic normal forms).

## 7. Examples

```
AddM(x : &Nat, y : Nat) : Unit by x := match *x { Z => *x := y | S p => AddM(&p, y) }
Add(x : Nat, y : Nat) : Nat := AddM(&x, y); x
AddMZero(x : &Nat) : Id Unit (AddM(x, 0)) () by x := match *x { Z => refl | S p => AddMZero(&p) }
AddZero(x : Nat) : Id Nat (Add(x, 0)) x := match x { Z => refl | S p => AddMZero(&p) }     // the pure theorem, by the in-place lemma on the predecessor field; no cong
AddZero'(x : Nat) : Id Nat (Add(x, 0)) x := AddMZero(&x)
TailM(x : &Nat) : &Nat by x := match *x { Z => x | S p => TailM(&p) }
AddM'(x : &Nat, y : Nat) : Unit := let t = TailM(x); *t := y
AddMEq(x : &Nat, y : Nat) : Id Unit (AddM(x, y)) (AddM'(x, y)) by x := match *x { Z => refl | S p => AddMEq(&p, y) }
AddMEqOwned(x : Nat) : Id Unit (AddM(&x, 0)) (AddM'(&x, 0)) := AddMEq(&x, 0)
```
E5 (dependent types through mutation; notes/deriver-e5.md):
```
Le(a : Nat, b : Nat) : Prop by a := match a { Z => True | S a' => match b { Z => False | S b' => Le(a', b') } }
LeAdd(n : Nat, m : Nat) : Le(n, Add(n, m)) by n := match n { Z => refl | S n' => LeAdd(n', m) }
SubM(x : &Nat, y : Nat, h : Le(y, *x)) : Unit by y := match y { Z => () | S q => match *x { Z => () | S p => *x := p; SubM(x, q, h) } }
AddSub(x : &Nat, y : Nat) : Unit := let old = *x; AddM(&*x, y); SubM(x, old, LeAdd(old, y))
AddSubId(x : &Nat, y : Nat) : Id Unit (AddSub(x, y)) (*x := y) by x := match *x { Z => refl | S p => let c = p; AddSubId(&c, y) }
```
Plus E3 (`AddToOne`, now accepted), E4 (`Twice`, `TwiceM`, `TwiceMZero`), E6 (must be rejected), and the regression attacks in `notes/`.

## 8. Inductive definitions (v2.0: D45–D47)

- **Declarations.** Constructors take the inductive's parameters as leading arguments in the core (`Nil(A)`, `Intro(P, Q; h, k)`), which surface syntax may omit when inferable from the fields or an annotation; constructor values record them (D49). `inductive D (a₁ : A₁ … aₘ : Aₘ) : s := C₁(ḡ₁ : B̄₁) | … | Cₙ(ḡₙ : B̄ₙ)`, `n ≥ 0`, `s ∈ {Type₀, Prop}`. Parameters are uniform (every constructor returns `D(ā)`; no indices). Field types are first-order data (declared inductives, `D(ā)` itself, `Nat`, `Unit`, `×`) or parameters; no `Π`, no `&` (D36). Nat and Unit are ordinary declarations; `False`, `True`, `And` are library declarations (§1). `Eq` stays primitive: it computes observationally (§4) and the core has no indexed families.
- **Prop inductives are erased.** A value of a type of sort `Prop` is a proof, and its value is `⋆` (proof irrelevance); a term of declared type `D(ā)` with `D : … → Prop` is erased (P2, D42).
- **Matching on a proof is by type (D45).** A `match` whose scrutinee's type — its stored type as refined by [Split], which must normalise to an inductive head `D(ā)`, a still-neutral type being a type error (D49) — has sort `Prop` does not inspect the scrutinee's content (which is always `⋆`): with zero constructors it has zero arms (`match p {}`) and is well typed at any result type; with one constructor its single arm binds proof fields as places holding `⋆` and data fields as places holding fresh abstract values (D49); with several constructors the match is erased and every arm must be a declared proof. A zero-arm match is unreachable and yields `⋆` at any type. [Split] on such a scrutinee is likewise by type. A zero-arm match is unreachable at runtime and is erased (vacuously, D40).
- **Subsingleton elimination (D45).** A `match` on a scrutinee of a `Prop` inductive may produce a result whose type is not a proposition only if the inductive has zero constructors, or exactly one constructor all of whose fields are propositions (Lean's rule; `False`, `True`, `And` qualify, `Or` would not). Otherwise proof irrelevance plus large elimination is inconsistent (e.g. distinguishing `Inl` from `Inr` of `Or(True, True)`).
- **Constructor disjointness (D47).** `Eq D (C ā) (C' b̄) ≡ False` for distinct constructors `C ≠ C'` of the same inductive (in particular `Eq Nat Z (S b) ≡ False`). Injectivity (`Eq D (C ā) (C b̄) ≡ And(Eq …)`) is not added. The unit laws `And(True, P) ≡ P ≡ And(P, True)` make `True` and `And` kernel-known library types (as Lean's kernel knows `Nat`); this is the one non-uniform point.
