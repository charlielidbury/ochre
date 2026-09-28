# Simplifier (minimality critic): report on RULES.md v0

1. **Verdict:** v0's spine (one machine, snapshot types, [Close] into sealed programs, `Id` as `Eq` on observations) is already minimal. Around it, about a quarter of the items (76 → 57 by the tally in §4) can go with E1/E2 intact. Two of them, D6 and anonymous pending bindings, are exactly the "rule that exists to patch one case" that BRIEF.md warns about.
2. **Most important finding:** D6 (the observational `Eq` conversions) is not used by any borrow example. In `AddMZero`, `AddMEq` and `AddMEqOwned`, the induction hypothesis and the goal normalise to the *same* `Eq` term with plain CIC `Eq`, so the environment does all the congruence (§6.1, §6.4, §6.5). D6 only serves the pure wrapper `AddZero`, which can use `cong S` from `J` instead (§6.2). Deleting D6 also deletes `Prop`, `⊤`, logical `⊥`, `∧` and `⟨_,_⟩`, and it removes a real problem: v0 gives no way to check `refl` against a goal that D6 has already reduced to `⊤`.
3. **What must change in RULES.md:** delete D6 and its connectives. Delete anonymous pending bindings: loans become variables and ending a borrow substitutes its content, loans inside it included (§2.2). The same change repairs deriver-e2's F2–F4. Fold ghost owners and [Lam]'s snapshot into [App]: a definition is checked at its generic call, which is built by the same `L; C` construction as [Close] (§2.3). Move [Join] out of the core: [Split] runs the rest of the program once per arm, and E3's rejection becomes a property of the checker, not the calculus. This touches the user's D7, so the lead has to decide it. Merge [Close]'s two forms, the footprint's two clauses, and λ into n-ary `fix`. Drop Unit η and the `n v` neutral, which nothing uses. D3 (copy data on read) stays, but its stated rationale needs correcting (§2.7).
4. **Confidence:** high for D6, the ghost/[Lam]/[App] merge, moving [Join] out, `n v` and Unit η; each was traced through E1/E2 by hand (§6). Medium for the loan-carrying end rule: it gives the same results on E1/E2 and is more uniform than v0, but once data has two fields it accepts some programs Rust rejects.
5. **Not checked:** nothing is mechanised. E3/E4/E6 were only spot-checked against v1. I did not reread the Aeneas paper to confirm how it handles branches (§2.6 relies on memory there and says so). The issue that a proof call seals the place it borrows (§8.4) and the clause for a type-level term stuck outside any call (§8.1) are flagged, not solved.

## 0. Method and notation

I traced every E1/E2 definition through v0 by hand and recorded which rule fires at each step. Then I re-traced under the proposed v1. The key derivations are in §6. Abbreviations used throughout (the primed versions replace `σ` by `σ'`):

- `U := ⌈let c = σ; AddM &c 0⌉` and `N := ⌈let c = σ; AddM &c 0; c⌉`: the result and the back-projection of `AddM` stuck on `σ` with `y = 0`.
- `UA`, `A`: the same with `σ_y` in place of `0`.
- `B := ⌈let c = σ; let r = TailM &c; *r := σ_y; c⌉`: the back-projection of `AddM'`.
- `Tr := ⌈let c = σ; let r = TailM &c; *r⌉` and `Tk := ⌈let c = σ; let r = TailM &c; *r := loan_k; c⌉`: the two [Close] outputs for `TailM` stuck on `σ`.

Terms. *Admissible rule*: a rule that adds no new derivable judgements, because any derivation that uses it can be rewritten without it. *η for Unit*: every value of type Unit is convertible to `()`. *Anti-unification*: computing the most specific common generalisation of two values by replacing the positions where they differ with fresh variables.

## 1. Audit table

One row per concept or rule of v0. The "E1/E2 uses it?" column asks whether any derivation of E1/E2 fires it.

| v0 item | E1/E2 uses it? | Derivable or mergeable? | Patch for one case? | Verdict |
|---|---|---|---|---|
| P1 evaluation, not rewriting | yes, everywhere | no | no | keep |
| P2 snapshot types | yes: [Lam] goal, IH type | [Lam]'s snapshot and [App]'s call-site type are one rule (§2.3) | no | keep, restated |
| P3 / D3: copy data, move borrows | moving a borrow: yes. Copying data that is then read twice in one run: **no** | no | no | keep; fix the rationale (§2.7) |
| P4 close off | yes | no | no | keep |
| P5 frame | metatheory only | it is §7's lemma, not a rule | no | move to §7 |
| P6 `Id` observes | yes | no | no | keep |
| `Prop`, definitional proof irrelevance | **no**; only D6's consistency argument uses it | — | serves D6 | delete (§2.1) |
| `Type` | J's motive | — | no | keep, as the one sort |
| unary Π / λ / application | the examples are n-ary; partial application `AddM x` would make a closure capture a borrow, which the scope forbids | λ is a non-recursive `fix` | — | n-ary `fix` only (§2.9) |
| `fix` + guard (§6) | yes | no | no | keep |
| `Nat`, `Unit` | yes | no | no | keep |
| `Eq`, `refl` | yes | no | no | keep, MLTT-style |
| `J` | under v1, only via `cong` in `AddZero` | — | no | keep |
| `⊤`, `⊥`, `∧`, `⟨_,_⟩` | **no**; they are only targets of D6 | — | serve D6 | delete |
| `A × B`, `(t, u)` | yes, to carry observations | no | no | keep |
| `&A`, `p`, `&p`, `:=`, `let`, `;`, `match`; places `x`, `*p`, `p.1` | yes | `;` is already sugar | no | keep |
| `Id A t u` | yes | computes (§4 of v0) | no | keep |
| values `Z`, `S`, `()`, pairs, closures, types | yes | λ- and fix-closures are one form | no | keep |
| `borrow_ℓ`, `loan_ℓ` | yes | no | no | keep |
| runtime `⊥` (moved or ended) | yes: moved borrow arguments | in this scope it is only ever the whole content of a borrow variable | no | keep; its clash with the logical `⊥` disappears with D6 |
| neutral `σ` | yes | no | no | keep |
| neutral `n v` | **no** | equals `⌈L; σ_f a⌉`, because abstract functions close off at once | yes, in effect | delete |
| neutral `⌈t⌉` | yes | no | no | keep |
| ghost owners `x°` | yes | an ordinary variable of the generic caller (§2.3) | no | merge away |
| anonymous pending bindings | yes, once: normalising `B` at `S σ'` (§6.3) | equals ending the borrow and letting the loans inside travel with it | **yes**: Aeneas's End-Mut side condition | delete (§2.2) |
| [Reorg] | yes | merges with [Pop], [Assign]'s drop and resolution into one [End] | its recursive side condition exists for pending bindings | merge |
| [Read], [Borrow], [Assign], [Let], [Match] | yes | — | no | keep |
| [App] (machine) | yes | — | no | keep |
| [Pop] | yes | its three cases become [Drop] + [End] | third case = pending bindings | merge |
| [Close], borrow-free form | yes (`AddM`) | both forms are one rule with a type-directed "port" (§2.5) | no | merge |
| [Close], `&T` form with loan hole | yes (`TailM`) | the loan hole reuses [End]; a λ would need a new rule | no | keep the loan hole |
| [Close], "name if top-level, else closure" | no (presentation only) | names are abbreviations | — | delete |
| [Seal] | yes | merges with Refinement: "values are kept in normal form" | no | keep, merged |
| [Seal]'s Unit η | **no** (§2.8) | — | no | move out |
| Refinement | yes | substitution followed by [Seal] | no | merge into [Seal] |
| footprint, two clauses | yes, both: the `&` clause for `AddMEqOwned`, the owner clause for `AddMZero` and `AddMEq` | one clause via `owner` (§2.4) | no | merge |
| observation: run, then end all borrows | yes | — | no | keep |
| observation: "stuck outside any call" clause | **no** | wrong as worded (§8.1) | — | keep, corrected |
| `Id` ≡ `Eq` on observations | yes | — | no | keep |
| D6: five `Eq` conversions (Z/S disjointness counted once) + `⊤ ∧ P` | only `AddZero`'s S arm | `cong S`, defined from `J` | **yes** | delete (§2.1) |
| [Lam] | yes | [App]'s type rule applied at the generic call (§2.3) | no | merge into [Def] |
| [Split] | yes | — | no | keep; it runs the rest of the program once per arm |
| [Join] | **no**: every match in E1/E2 is in tail position | admissible over the forking [Split] | serves E3 | move out (§2.6) |
| [App] (typing) | yes | — | no | keep; it absorbs [Lam] |
| [Ref] | yes: moved borrows | "reading ⊥ is an error" is stated twice (§3 and §5 of v0) | no | keep, stated once |
| §7 conjectures | — | — | — | keep; the canonical-observation conjecture becomes easier (§2.2) |

## 2. The candidates, one by one

### 2.1 D6 (observational `Eq`), `Prop`, `⊤`, `⊥`, `∧`, `⟨_,_⟩`: delete

**Where D6 fires in v0.** It fires in exactly one step of E1/E2: `AddZero`'s S arm, where the goal is `Eq Nat (S N') (S σ')` and the hypothesis is `Eq Nat N' σ'`. D6's `Eq Nat (S a) (S b) ≡ Eq Nat a b` bridges the two. Elsewhere D6 only rewrites both sides of an already-matching pair: in `AddMZero`, `AddMEq` and `AddMEqOwned`, the refined goal and the IH's type are the *same* `Eq (Unit × Nat) (…) (…)` term before any `Eq` rule runs (derivations §6.1, §6.4, §6.5). The IH is evaluated in the caller's environment, where the `S` already sits in `x ↦ borrow₀ (S loan₁)`, and resolving the borrows carries it into the observed place. That is BRIEF.md's headline claim, and it needs no `Eq` computation at all.

**Without D6.** `Eq`, `refl` and `J` behave as in MLTT, and `refl : Eq A a b` checks iff `a ≡ b`. `AddZero` becomes `match x { Z => refl | S p => cong S (AddZero p) }`, where `cong` is an ordinary definition by `J`. No rule is added. This is exactly 01 §0's original proof. The contrast between the two proofs is the story the paper wants to tell. In `AddZero` the `S` sits in the *result* (`Add` owns a copy of `x`), so `cong` is the honest proof. In `AddMZero` the `S` sits in the *environment*, and the environment does the work. D6 hides that contrast.

**A problem v0 has because of D6.** In `AddMZero`'s Z arm the goal `Eq (Unit × Nat) ((), Z) ((), Z)` normalises under D6 to `⊤ ∧ ⊤ ≡ ⊤`. v0 types `refl` only as `refl : Eq A a a`. Conversion is "same normal form", so checking `refl` against `⊤` means finding some `A` and `a` for which `Eq A a a` normalises to `⊤`. That search is not algorithmic, and it fails whenever `a` is neutral, because `Eq Nat σ σ` does not reduce. So v0 needs either a second `refl` rule ("`refl` checks against any goal whose normal form is `⊤`") or a `tt : ⊤` constructor, and the latter changes E1's proof text. Without D6 there is one `refl` rule.

**What a reviewer would say about D6.** It is a fragment of observational type theory for three hand-picked types. A reviewer will ask why constructor injectivity and disjointness hold for `Nat` but not for every inductive type, and why there is no η for pairs of neutrals. Answering properly means adopting full OTT (Pujet–Tabareau), which is a paper of its own.

**`Prop` goes with it.** D6's consistency argument is the only use of definitional proof irrelevance in v0. Plain `Eq`/`J` is consistent by the ordinary set model. `Prop` will probably come back with proof erasure, which is also the natural fix for §8.4. It should come back with that motivation, not D6's.

**E1/E2 still go through:** yes. See §6.1–§6.5. Only `AddZero`'s proof text changes.

**Honest cost.** deriver-e1 (N4) shows that under v0 the cross proof `AddZero x := AddMZero &x` checks, because D6's pair, Unit and `⊤ ∧ P` rules collapse `Eq (Unit × Nat) (U, N) ((), σ)` to `Eq Nat N σ`. Under v1 that cross proof needs `cong snd (AddMZero &x)`, i.e. a pair projection `snd` (the standard eliminator for `×`, one rule plus its β-rule). E1 does not require the cross proof, but the paper would probably like to show it. That is one standard eliminator against D6's five non-standard conversions, ⊤, ∧ and a second `refl` rule.

### 2.2 Anonymous pending bindings: delete by letting an ended borrow carry its loans

**Where they arise.** A pending binding appears when a borrow is dropped while its content still contains a loan. That happens only when a function returns a reborrow of part of a borrowed parameter, as in `TailM`'s S arm when that arm is actually run rather than closed off. In E1/E2 this happens once: normalising `B[σ := S σ']` for `AddMEq`'s S-arm goal (§6.3). v0 needs them because of Aeneas's End-Mut side condition: a borrow may end only once its content is free of loans.

**Proposal.** One rule: `[End ℓ]` replaces `borrow_ℓ w` by `⊥` and `loan_ℓ` by `w`, with no side condition. Any loans inside `w` move along with it. Dropping a borrow always ends it. For this to work, an access (read, borrow, assign) must end the loans on the accessed place's path *and inside its content* before it proceeds. v0 needs that anyway, because v0's [Read] is undefined on content such as `S loan_k` (§8.2).

**E1/E2.** §6.3 shows that `B[σ := S σ']` normalises to `S B'` under both v0 and v1. v0 gets there through the pending binding and the recursive side condition. v1 gets there by moving `S Tk'` into `c` when `TailM`'s frame pops, and ending `k` when `c` is read.

**Uniformity argument.** In v0, the situation "the tail of `c` is borrowed by `t`" has two representations, depending on how `t` was made:
- via `&c.1`: `c ↦ S loan_k`;
- via `TailM &c`: `c ↦ loan₁` plus `_ ↦ borrow₁ (S loan_k)`.

The two behave differently: in the first, matching on `c`'s head leaves `t` alive; in the second, it ends `t`. v1 has one representation, the first.

**The same move fixes deriver-e2's F2–F4.** deriver-e2 finds that v0's loan-in-a-sealed-program breaks because loans are linear markers: a hole can be duplicated by [Close] (F4), can outlive its borrow into a [Seal] run (F3), and has to be found inside syntax (F2). Their fix is a new hole-variable `h_k`. With [End] defined as substitution, v1 needs no new concept: *a loan is a variable standing for its borrow's final content, and [End] substitutes it everywhere*. [Borrow] creates one occurrence; only [Close] duplicates. Inside a [Seal] run a loan whose borrow is absent is inert (an abstract value). So one decision, "loans are variables, ending is substitution", deletes pending bindings and the recursive side condition, and repairs F2–F4.

**Bonus for the metatheory.** Resolution, which ends every borrow, becomes substitution of each borrow's content for its loan along an acyclic graph. The order of endings visibly does not matter, which is the easy half of §7's canonical-observation conjecture. v0's recursive side condition instead fixes an order, and canonicity then has to be proved.

**Risk.** Once data has two fields, v1 lets a program use a field of `c` that `t` does not point into, even while `t` (returned by a function) is live. Rust rejects such programs. The concrete machine tracks the exact cell `t` points to, so this is memory-safe. The symbolic side stays conservative, because after [Close] the whole content of `c` is a sealed program that holds `loan_k`. This is a question for breaker-frame.

### 2.3 Ghost owners, [Lam]'s snapshot goal, [App]'s call-site type: one rule

**Ghost owners are the generic caller's variables.** v0's [Lam], for a parameter `x : &T`, binds `x° ↦ loan₀` and `x ↦ borrow₀ σ`. That is exactly what [Borrow] produces when a caller holding `c₀ ↦ σ` evaluates `&c₀`. So v1 has a rule [Def]: `fix f (x̄:Ā) : B := t` is checked by running the *canonical call* of `f` on fresh `σ̄`. This is the same `L; C` that [Close] builds: `L = let cᵢ = σᵢ` for each borrow parameter, and `C = f a₁ … aₙ`. The ghost is then `cᵢ`, an ordinary owned variable in the generic caller's frame.

**The snapshot goal and the call-site type are one rule.** v0's [Lam] says "evaluate `B` once, at entry"; v0's [App] says "evaluate `B` at the call site, with `x` bound to the argument". At the generic call, the entry *is* the call site. v1 therefore has a single rule, [Call type]: the type of a call is `B` evaluated in the call's frame, meaning the callee's frame on top of the caller's environment. P2 (snapshot) becomes a consequence: `B` is evaluated once, at the moment its binder is bound.

**E1/E2.** The environments are literally v0's, with `x°` renamed to `c₀` (§6.0).

**What this deletes:** ghost owners as a special form of environment entry; the `&T` special case of [Lam]; and the separate snapshot clause. It also has [Def] and [Close] share one construction, which reads well to a reviewer: "a function is checked at the same generic call it is closed off to".

### 2.4 Footprint: keep it syntactic, state it as one clause

**Nothing that falls out of the machine works.** I checked four alternatives:
- (a) "Places the run changed" is not stable under refinement: `AddM` with `y = Z` writes `Z` over `Z`.
- (b) "Places the run touched" is not stable either: a branch that never uses `x` drops out.
- (c) "Owners of all free variables" is stable, but it breaks `AddZero`. `W = {x}` gives the goal `Eq (Nat × Nat) (N, σ) (σ, σ)` and the IH `Eq (Nat × Nat) (N', σ') (σ', σ')`, which then needs congruence through a pair.
- (d) "All of Ω" is the option D5 already rejects.

So v0's syntactic write-footprint is the right one.

**Both of v0's clauses are load-bearing.** The `&` clause is used by `AddMEqOwned` and by E6's `AddM &x 0` versus `AddM &x 1`. Without it that pair would compare `()` with `()` and be provable by `refl`. The owner clause is used by `AddMZero` and `AddMEq`.

**Merged form.** `W(t, u) = { owner(x) | x free in t or u, and x is written: it occurs under &, on the left of :=, or has a borrow type }`. `owner(x) = x` when `x` is owned. When `x` holds `borrow_ℓ`, `owner(x)` is the variable that holds `loan_ℓ`, or, if that variable itself holds a borrow `borrow_m`, the owner reached through `m`. Moving a borrow counts as a write, because it hands over write access. Moving or copying data does not. (It becomes a set of owners once [Close] duplicates a loan; §4.4.)

**Not recommended.** 01 §2's rule, which forbids `&` and `:=` on ambient variables inside types, would delete the `&` clause. But it breaks P2's uniformity, since a type-level term would no longer be "the machine run on a private copy". It would also make `AddMEqOwned` need congruence through a pair.

### 2.5 [Close]'s two forms: one rule with a type-directed port

Write the canonical program as `L; let r = C`. A result type `R` determines a *port*, a triple `(wrap, get, put)`:

| result type `R` | wrap(v) | get(r) | put(r) |
|---|---|---|---|
| borrow-free | `v` | `r` | `()` |
| `&T` | `borrow_k v` (`k` fresh) | `*r` | `*r := loan_k` |

**[Close]** (one rule): the call returns `wrap(⌈L; let r = C; get(r)⌉)`, and each `loan_ℓᵢ` is filled with `⌈L; let r = C; put(r); cᵢ⌉`. In words, a returned borrow is a lens: its initial content goes out through `get`, and its final content comes back in through `put`. A borrow-free result is the trivial lens. For the borrow-free row this is v0's first form up to let-η (`let r = C; r` is `C`).

**Loan hole versus λ (01 §9).** Keep the loan hole. When `borrow_k` ends, the hole is filled by the ordinary [End] rule, wherever the hole happens to be. A λ-valued fill (`λfinal. …`) would need a new rule, "when borrow `k` ends, apply the fill function". With v1's [End], a loan inside a sealed program is not even a special feature: sealed programs embed values, values may contain loans, and so sealed programs may contain loans.

### 2.6 [Join]: move out of the core

- **Not used by E1/E2.** Every match in E1/E2 is the whole body of its arm-bearing function (`AddM`, `AddMZero`, `AddZero`, `TailM`, `AddMEq`); `Add` and `AddM'` have no match. [Join] fires only for a match with a continuation after it, which is E3.
- **The core rule it sits on top of.** Let [Split] fork the *rest of the check*: at a match on σ in the checked term, everything after the match (its continuation) is checked once per refinement. This is the "programmer duplicates the continuation into the arms" behaviour of D7, done by the calculus. The typing judgement becomes a tree of paths (as in symbolic execution); each leaf's result is checked against the goal refined along its path. I believe this is also what Aeneas's symbolic interpreter does for branches (continuation-passing, one continuation run per branch; joins were introduced for loops), but I did not reread the paper to confirm it.
- **[Join] is admissible over it,** given the substitution property (§7 "Adequacy": typing is stable under substituting values for σ). A Join derivation checks the continuation once with anti-unified values (fresh σ where the arms differ); substituting each arm's values gives a derivation of each forked path. So [Join] never accepts more than forking; it only accepts less (E3). Admissible rules do not belong in a diamond core.
- **What this changes.** E3 (`AddToOne`) is *accepted* by the v1 core and *rejected* by a checker that uses D7's join. D7 is marked "user's choice", so this needs the lead's (or user's) call on what D7 decided: the language's acceptance set, or the checker's algorithm. My recommendation: the core forks; the shipped checker uses D7's join for predictability and error placement; the paper states the checker is sound (not complete) for the core. If the user meant D7 as a property of the language, [Join] must stay in the core and my deletion is withdrawn.

### 2.7 D3 (copy data on read): cannot be removed; its rationale should change

- **Not needed by E1/E2.** No E1/E2 run reads the same borrow-free place twice: each goal side is a separate run from the same Ω, so `Id Nat (Add x 0) x` using `x` on both sides is fine under moves. Under "everything moves" (the user's original choice), [Read] would have one case instead of two, and the core would *be* the efficient runtime (no out-of-core affine check needed for adequacy).
- **D3's first stated reason is already dissolved by D5.** "With moves, `Id Nat x 3` consumes `x` on one side only, so the observations differ in whether `x` is dead." With the write-footprint, moving an owned `x` is a read, so `x ∉ W` and its deadness is never observed: `Id Nat x 3` at `{x ↦ σ}` observes `σ` against `3`.
- **Why it still cannot go.** The theorem-prover half is not linear. Proof terms are used many times (`h` passed to two lemmas, `⟨h, h⟩`), closures are called twice (E4's `Twice f := f (); f ()`), and statements like `x + x = 2x` should not need a hand-written `Copy : &Nat → Nat`. The only alternative to "copy what holds no borrow" is a type-directed split (copy `Prop`/`Type`/functions, move data), which is the mode split D3 exists to avoid. So D3 is the smallest rule that meets end goal 2 for a theorem prover.
- **Proposed rewrite of D3's "Why":** "The prover half needs non-linear use of proofs, types and closures; 'copy whatever holds no borrow' covers data, proofs and closures with one rule. (The 'dead on one side' argument no longer applies once D5's footprint only observes written places.)"

### 2.8 Unit η in [Seal]: move out

- **Not needed by E1/E2.** The result component of every observation in E1/E2 matches *syntactically* between goal and IH without η: both carry `U'` (or `UA'`) on the left and `()` on the right (§6.1, §6.4, §6.5). In the Z arms the sealed result reruns to `()` by [Seal] itself. `AddZero` never observes a Unit.
- **Cost of keeping it:** it is the only type-directed clause in an otherwise untyped normaliser (`nf` has to know the type of the sealed program). A reviewer will ask why Unit and not pairs.
- **Where it will matter:** `Id Unit (AddM x 0) (AddM x 0; ())` is unprovable without it (result `U` against `()`). It belongs with Lean-style η for structures, as one extension, when an example needs it.

### 2.9 Smaller items

- **λ into n-ary `fix`.** v0's syntax is unary, but [Close] and the examples use n-ary calls (`f w₁ … wₙ`, `AddM x y`). Curried, `AddM x` is a closure capturing a borrow, which the scope forbids. Fix: `fix f (x₁:A₁)…(xₙ:Aₙ) : B := t`, `Π(x₁:A₁)…(xₙ:Aₙ). B`, saturated application `t u₁ … uₙ`; `λ` is a `fix` whose name is unused. One function former instead of two, one closure value instead of two, and a scope gap closed.
- **`n v` (stuck application of an abstract function): delete.** v0's [Close] already says abstract functions close off immediately, so `σ_f v` is `⌈L; σ_f a⌉`; `n v` is never produced.
- **"`f` is the name if top-level, else the closure" in [Close]: delete.** Names are abbreviations for closures (δ); the canonical call's head is always the closure value. Canonical bound names (`cᵢ`, `r`) make sealed-program comparison purely syntactic, with no α-conversion.
- **Refinement into [Seal].** "Values are kept in normal form; substituting into a value re-normalises it" is one sentence; refinement is its instance.
- **[Reorg] + [Pop] + [Assign]'s drop + resolution → [End] + [Drop]** (with §2.2). [Drop v]: a borrow ends; an owned value that still contains a loan is rejected. Used at let-exit, frame pop, and on the old content in [Assign]. Resolution is "[End] every borrow".
- **"Ending loans is also allowed at any other time" (in [Reorg]): delete from the rule.** It reintroduces nondeterminism into a deterministic machine, and as stated it is false (ending a loan early can turn a later use of the borrow into an error). It is the §7 canonicity conjecture, restated as "ending a loan earlier either errors or yields the same observation".
- **[Ref]:** state "reading ⊥ is an error" once. (Optional further merge: if dropping an owned place *ended* its loans instead of rejecting, the borrower becomes ⊥ and [Ref] is the single clause "⊥ has no type". It needs [End] to reach a borrow held in the value being returned, which is fiddly; I would not do it in v1.)

## 3. Kept after scrutiny (and why)

- **Runtime `⊥`.** In scope, it only ever fills a whole borrow-typed variable, so it could be binding removal instead; but it is Aeneas's notation, reviewers know it, and removing it saves nothing real. With D6 gone the clash with logical `⊥` disappears.
- **Syntactic footprint** (§2.4). **Loan holes** rather than λ-valued fills (§2.5). **D3** (§2.7).
- **Pairs `A × B`.** The observation carrier. Some product is needed (the alternative, `∧` of equations, needs `Prop`); no pair eliminator is needed by E1/E2.
- **`Type`** (the motive of `J`), **`J`** (for `cong`; and a prover without it is not a prover), **`Eq`/`refl`**.
- **[Close], [Seal], [Split].** The two answers to "the machine met σ": in checking mode fork, in conversion mode seal the call. Different operations; merging them would hide the point of 01 §3.
- **The recursion guard (§6).** Consistency needs termination.
- **The observation clause for a term stuck outside any call** (§8.1): not used by E1/E2, but deleting it would make some well-formed-looking types ill-formed (e.g. `Id Nat (match x { Z => Z | S _ => Z }) Z` at `x ↦ σ`), which cuts into end goal 2. Keep it, corrected.

## 4. Proposed v1 (replacement for RULES.md §0–§5; §6–§8 unchanged except as noted)

### 4.0 Principles
- **P1 Evaluation, not rewriting.** (unchanged)
- **P2 Types are evaluated when bound.** A type is evaluated once, in the frame that binds it (a definition's generic call, a call site, a `let`), on a private copy of the environment. The result is a value; later mutation cannot change it.
- **P3 Data is copied, borrows are moved; reborrowing is explicit.** (unchanged; D3's rationale per §2.7)
- **P4 Close off stuck calls** into sealed programs. (unchanged)
- **P5 `Id` is `Eq` on observations.** (v0's P6; v0's P5 "Frame" moves to §7 as the hypothesis of P4)

### 4.1 Syntax
```
t, u, A, B ::= x | Type
             | Π(x₁:A₁)…(xₙ:Aₙ). B | fix f (x₁:A₁)…(xₙ:Aₙ) : B := t | t u₁ … uₙ     n-ary, calls saturated; λ = fix with unused f
             | Nat | Z | S t | Unit | () | A × B | (t, u)
             | Eq A t u | refl | J …                                               MLTT equality, in Type
             | &A | p | &p | p := t | let x = t; u | match p { Z => t | S y => u }
             | Id A t u
places p   ::= x | *p | p.1                                   t; u  :=  let _ = t; u
```
Scope as v0 (`&A` only as the type of a variable, parameter or result; no borrows in data; closures capture only borrow-free values; no shared borrows, no loops). Pattern variables are sub-places, as v0.

### 4.2 Runtime
```
values  v, w ::= Z | S v | () | (v, w) | closure | type | borrow_ℓ v | loan_ℓ | ⊥ | σ | ⌈t⌉
Ω            ::= frames of bindings x : A ↦ v, separated by |
```
Loans may occur anywhere inside a value, including inside the values embedded in a sealed program. Borrows occur only as the whole content of a variable (scope). A value is borrow-free if it contains no borrow and no loan.

### 4.3 Machine `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩ | stuck`
- **[End ℓ]** Replace `borrow_ℓ w` by `⊥` and substitute `w` for *every* occurrence of `loan_ℓ` (loans inside `w` go with it). A loan is a variable standing for its borrow's final content: [Borrow] creates one occurrence, only [Close] duplicates one (one per borrow argument, deriver-e2 F4).
- **Access.** Before [Read], [Borrow] or [Assign] on `p`: [End] every loan on `p`'s path or inside `content(Ω, p)` whose borrow is in Ω (so overwriting a loaned place first ends the loan, breaker-frame (1)). Before [Match] on `p`: the same for loans on `p`'s path.
- **[Drop v]** If `v` is a borrow, [End] it. If `v` is owned and contains a loan, reject (something borrows a dying place). Used at `let`-exit, frame pop, and on the old content in [Assign].
- **[Read]** `v = content(Ω, p)`: borrow-free → `⟨Ω, v⟩` (copy); a borrow → `⟨Ω[p ↦ ⊥], v⟩` (move); `⊥` → error.
- **[Borrow]** `⟨Ω, &p⟩ ⇓ ⟨Ω[p ↦ loan_ℓ], borrow_ℓ content(Ω, p)⟩`, ℓ fresh.
- **[Assign]** `⟨Ω, p := t⟩`: `⟨Ω, t⟩ ⇓ ⟨Ω₁, v⟩`; [Drop] the old content; `⇓ ⟨Ω₁[p ↦ v], ()⟩`.
- **[Let]** as v0, dropping `x` by [Drop].
- **[Match]** content `Z` → `t`; `S v` → `u[y := p.1]`; a neutral → stuck.
- **[App]** `t u₁ … uₙ`: evaluate `t` to a closure (a `fix` unfolds once), the `uᵢ` to `wᵢ`; push a frame `x̄ ↦ w̄`; run the body; on completion [Drop] the frame and return; if stuck, [Close].
- **Canonical call** of `f` on `w₁ … wₙ`, where `wᵢ = borrow_ℓᵢ uᵢ` for `i ∈ I`: `L := let cᵢ = uᵢ (i ∈ I)`, `C := f a₁ … aₙ` with `aᵢ = &cᵢ` (i ∈ I), else `wᵢ`. Used by [Close] and [Def].
- **[Close]** The body of `f w̄` is stuck (or `f` is an abstract `σ_f`): restore Ω to just before the call. With the port `(wrap, get, put)` of the result type (table in §2.5), the call returns `wrap ⌈L; let r = C; get(r)⌉`, and each `loan_ℓᵢ` is filled with `⌈L; let r = C; put(r); cᵢ⌉` (the borrow `borrow_ℓᵢ` was consumed by the call).
- **[Seal]** Values are kept in normal form. `nf ⌈L; let r = C; k⌉`: run it from `∅`, unfolding `C` itself without closing it off (calls *inside* `C`'s body close off as usual; deriver-e1 F1: otherwise `nf` loops). If the run completes with `v`, the result is `nf v`; if it gets stuck, the result is `⌈…⌉` with its embedded values normalised. In the run, a loan whose borrow is not in the run's environment is inert, i.e. an abstract value (deriver-e2 F3). Substituting into a value (e.g. refinement `σ := S σ'`, or [End] filling a loan) is followed by `nf`. Definitional equality is syntactic equality of normal forms (canonical names `cᵢ`, `r` make α unnecessary).

### 4.4 Observation and `Id`
- **owners(x)** = `{x}` if `x` is owned; if `x` holds `borrow_ℓ`: each variable whose content holds an occurrence of `loan_ℓ`, replaced by its own owners if it holds a borrow itself (deriver-e1 F4; a set because of deriver-e2 F4).
- **Footprint** `W(t, u) = ⋃ { owners(x) | x free in t or u, occurring under &, on the left of :=, or of borrow type }`, ordered as in Ω. Locals of `t` are not observed; every write `t` makes to the ambient Ω goes through such a free variable (breaker-frame (2)).
- **Observation** `⟦t⟧_Ω^W`: `⟨Ω, t⟩ ⇓ ⟨Ω', v⟩`; [End] every borrow in Ω'; the tuple `(v, content(k) for k ∈ W)` (for `W = ∅`, just `v`). If `t` gets stuck outside any call: λ-lift `t` over its free variables, passing each variable of `W` by borrow, and apply [Close] to that call (§8.1).
- **`Id A t u ≡ Eq (A × T_W) ⟦t⟧ ⟦u⟧`**, `W = W(t, u)`; each side runs on its own copy of the same Ω (breaker-frame (3)). `A` borrow-free.
- **`refl : Eq A a b`** iff `a ≡ b`. `J` as in MLTT.

### 4.5 Typing `Ω ⊢ t ⇓ v : A ⊣ Ω'`
- **[Call type]** The type of a call `f w̄` with `f : Π(x̄:Ā). B` is `B` evaluated in the call's frame (`x̄ ↦ w̄` pushed on the caller's Ω; borrow arguments moved in).
- **[Def]** `fix f (x̄:Ā) : B := t` is checked by running the canonical call of `f` on fresh abstract values `σ̄` in checking mode: the body runs in that call's frame and its result must have the call's [Call type] (as refined along the path).
- **[App]** A call's value comes from the machine (unfold, or [Close]); its type from [Call type]. This is where an induction hypothesis gets its type, in the caller's borrow structure.
- **[Split]** A match in the checked term on an abstract `σ` forks the rest of the check: once with `σ := Z`, once with `σ := S σ'`, applied to Ω, the goal and every stored type.
- **[Ref]** Reading `⊥` is a type error (with [Drop]'s rejection, this is the borrow checker).

### 4.6 Moved out of the core (to an "extensions" section)
[Join] (admissible, §2.6; D7's checker algorithm); η for Unit (§2.8); `Prop` with proof irrelevance (return with proof erasure, §8.4); D6 (subsumed by `cong`).

### 4.7 Tally

| part | v0 | v1 |
|---|---|---|
| term formers + places | 29 + 3 | 23 + 3 |
| value forms + environment entry kinds | 13 + 3 | 11 + 1 |
| machine rules (+ shared canonical-call definition) | 12 | 10 + 1 |
| observation / `Id` / `Eq` rules | 11 | 4 |
| typing rules | 5 | 4 |
| **total** | **76** | **57** |

(Counting: v0's two [Close] forms and Refinement count separately; D6 counts as its five `Eq` conversions (Z/S disjointness once) plus `⊤ ∧ P`; the two footprint clauses and the two observation cases count separately; v1's [Call type] is counted inside [App].)

## 5. E3, E4, E6 under v1 (spot checks only)

- **E3** (`AddToOne`, a match that picks one of two borrows, followed by `AddM r y`): the v1 core **accepts** it. [Split] forks, and each path runs `AddM r y` on its own borrow. A checker using D7's join rejects it, exactly as before, because the arms' loan shapes differ. The hand-duplicated version is accepted by both. This is the only expected outcome in the suite that changes, and it changes only at the level of the core (§2.6).
- **E4** (`Twice f := f (); f ()`, `f` abstract): `f` is a closure, so it is borrow-free and D3 copies it on each read. `σ_f ()` closes off at once to `⌈σ_f ()⌉` (no borrow arguments, so nothing is filled). The only change from v0 is the spelling of this neutral (v0's `n v`).
- **E6**:
  - Using a moved borrow reads `⊥`, a [Ref] error.
  - `λx:&Nat. (*x := 5; refl) : Π(x:&Nat). Id Nat *x 5`. At [Def]'s frame `{c₀ ↦ loan₀ | x ↦ borrow₀ σ}`, `W = owners(x) = {c₀}`, so the goal is `Eq (Nat × Nat) (σ, σ) (5, σ)`. The goal is a snapshot, so after `*x := 5` `refl` is still checked against it, and fails.
  - `Id Nat Z (S Z) ≡ Eq Nat Z (S Z)`: `refl` fails, and there is no closed proof because plain `Eq`/`J` is consistent (set model).
  - `Id Unit (AddM &x 0) (AddM &x 1) ≡ Eq (Unit × Nat) (U, N) (U₁, N₁)` with `N₁ = ⌈let c = σ; AddM &c 1; c⌉`. The two sides are not convertible, and in the model `N = σ ≠ S σ = N₁`, so the equation is false.

## 6. E1/E2 under v1: the derivations that the proposals touch

v1's [Close] writes `⌈L; let r = C; r⌉` and `⌈L; let r = C; (); cᵢ⌉` for a borrow-free result. Below I keep §0's shorter v0 spellings (`U = ⌈L; C⌉`, `N = ⌈L; C; c⌉`). Goal and hypothesis always come from the same [Close], so they agree syntactically in either spelling. [Seal] is v1's version: it unfolds the sealed program's own call without closing it off (deriver-e1 F1).

### 6.0 [Def] gives exactly v0's [Lam] environment (ghost = generic caller variable)
```
⊢ fix AddMZero (x : &Nat) : Id Unit (AddM x 0) () := match *x { Z => refl | S p => AddMZero &p }   // [Def]
  canonical call on fresh σ: L = let c₀ = σ, C = AddMZero &c₀
  ⟨∅, let c₀ = σ⟩ ⇓ ⟨{c₀ ↦ σ}, ()⟩                                          // [Let]
  ⟨{c₀ ↦ σ}, &c₀⟩ ⇓ ⟨{c₀ ↦ loan₀}, borrow₀ σ⟩                                // [Borrow]
  call frame: {c₀ ↦ loan₀ | x ↦ borrow₀ σ}                                  // = v0 [Lam]'s {x° ↦ loan₀, x ↦ borrow₀ σ}, with x° renamed c₀
  goal = [Call type]: Id Unit (AddM x 0) () in that frame
    W = owners(x) = {c₀}
    ⟦AddM x 0⟧ = (U, N)                                                     // [Read] moves x; [App] body stuck on σ; [Close]: returns U, loan₀ := N
    ⟦()⟧ = ((), σ)                                                          // resolve: [End 0], c₀ ↦ σ
    goal ≡ Eq (Unit × Nat) (U, N) ((), σ)
  body: match *x                                                            // [Split] σ := Z (§6.1a) | σ := S σ' (§6.1b)
```

### 6.1a `AddMZero`, Z arm
```
{c₀ ↦ loan₀ | x ↦ borrow₀ Z} ⊢ refl : Eq (Unit × Nat) ((), Z) ((), Z)       // refl: both sides identical
  nf N[σ := Z] = Z                                                          // [Seal]
    ⟨∅, let c = Z; AddM &c 0; c⟩
    ⟨{c ↦ loan₁}, AddM (borrow₁ Z) 0; c⟩                                     // [Let]; [Borrow]
    ⟨{c ↦ loan₁ | x ↦ borrow₁ Z, y ↦ 0}, match *x {…}⟩                      // [App] unfold C itself
    ⟨{c ↦ loan₁ | x ↦ borrow₁ Z, y ↦ 0}, *x := y⟩                           // [Match] Z arm
    ⟨{c ↦ loan₁ | x ↦ borrow₁ Z, y ↦ 0}, ()⟩                                 // [Read] y; [Assign] through x
    ⟨{c ↦ Z}, (); c⟩                                                         // [Drop] AddM's frame: [End 1]
    ⟨{c ↦ Z}, Z⟩                                                             // [Read] c
  nf U[σ := Z] = ()                                                         // the same run, whose result is ()
```

### 6.1b `AddMZero`, S arm: the IH's type *is* the refined goal, with no `Eq` rule
```
{c₀ ↦ loan₀ | x ↦ borrow₀ (S σ')} ⊢ AddMZero &(*x).1 : Eq (Unit × Nat) (U', S N') ((), S σ')   // [App]
  refined goal:
    nf N[σ := S σ'] = S N'                                                  // [Seal]
      ⟨∅, let c = S σ'; AddM &c 0; c⟩
      ⟨{c ↦ loan₁}, AddM (borrow₁ (S σ')) 0; c⟩                             // [Let]; [Borrow]
      ⟨{c ↦ loan₁ | x ↦ borrow₁ (S σ'), y ↦ 0}, match *x {…}⟩               // [App] unfold C itself
      ⟨{c ↦ loan₁ | x ↦ borrow₁ (S loan₂), y ↦ 0}, AddM (borrow₂ σ') 0⟩     // [Match] S arm, p = (*x).1; [Borrow] &p; [Read] y
      ⟨{c ↦ loan₁ | x ↦ borrow₁ (S N'), y ↦ 0}, U'⟩                          // [Close] (a call inside C): stuck on σ'; loan₂ := N'
      ⟨{c ↦ S N'}, U'; c⟩                                                    // [Drop] AddM's frame: [End 1]
      ⟨{c ↦ S N'}, S N'⟩                                                     // [Read] c; nf N' = N' (its own call is stuck)
    nf U[σ := S σ'] = U'                                                    // the same run, whose result is U'
  argument: ⟨{c₀ ↦ loan₀ | x ↦ borrow₀ (S loan₁)}, borrow₁ σ'⟩              // [Borrow] &(*x).1
  type: [Call type] in {c₀ ↦ loan₀ | x ↦ borrow₀ (S loan₁) | x' ↦ borrow₁ σ'}
    W = owners(x') = {c₀}                   // loan₁ is in x, which holds borrow₀, whose loan₀ is in c₀
    ⟦AddM x' 0⟧ = (U', S N')
      ⟨{… | x' ↦ ⊥}, AddM (borrow₁ σ') 0⟩                                    // [Read] moves x'
      ⟨{c₀ ↦ loan₀ | x ↦ borrow₀ (S N') | x' ↦ ⊥}, U'⟩                       // [App] stuck on σ'; [Close]: loan₁ := N'
      c₀ ↦ S N'                                                             // resolve: [End 0]
    ⟦()⟧ = ((), S σ')                                                       // resolve: [End 1], x ↦ borrow₀ (S σ'); [End 0], c₀ ↦ S σ'
    type ≡ Eq (Unit × Nat) (U', S N') ((), S σ')                            // symbol for symbol the refined goal
```
No `Eq` conversion was used, and no Unit η either: `U'` appears on both sides.

### 6.2 `AddZero` with `cong` instead of D6
```
⊢ fix AddZero (x : Nat) : Id Nat (Add x 0) x := match x { Z => refl | S p => congS (AddZero p) }   // [Def]
  call frame {x ↦ σ}                                                        // no borrow parameters, L is empty
  goal: W(Add x 0, x) = ∅                                                   // x owned, not under & or :=
    ⟦Add x 0⟧ = N
      ⟨{x ↦ σ} | {x' ↦ σ, y ↦ 0}, AddM &x' y; x'⟩                           // [Read] x (copy); [App] unfold Add
      ⟨… | {x' ↦ loan₁, y ↦ 0}, AddM (borrow₁ σ) 0; x'⟩                     // [Borrow]; [Read] y
      ⟨… | {x' ↦ N, y ↦ 0}, U; x'⟩                                           // [App] stuck on σ; [Close]: loan₁ := N
      ⟨{x ↦ σ}, N⟩                                                           // [Read] x'; [Drop] Add's frame
    ⟦x⟧ = σ;  goal ≡ Eq Nat N σ
  Z arm: goal ≡ Eq Nat Z Z (nf N[Z] = Z, §6.1a)                             // refl
  S arm: {x ↦ S σ'} ⊢ congS (AddZero x.1) : Eq Nat (S N') (S σ')            // [App] congS; goal refined by §6.1b
    {x ↦ S σ'} ⊢ AddZero x.1 : Eq Nat N' σ'                                 // [App]: [Read] x.1 copies σ'; [Call type] in {x ↦ S σ' | x' ↦ σ'}: W = ∅, ⟦Add x' 0⟧ = N', ⟦x'⟧ = σ'
    congS : Π(a b : Nat)(h : Eq Nat a b). Eq Nat (S a) (S b)                // an ordinary definition by J; a, b implicit
```
v0 instead reduces the goal with D6 (`Eq Nat (S a) (S b) ≡ Eq Nat a b`) and accepts the bare `AddZero p`. That is the only step of E1/E2 where D6 is load-bearing.

### 6.3 Normalising `B` at `S σ'`: no pending binding needed
Here `Tr'`/`Tk'` are §0's `Tr`/`Tk` at `σ'`, and `B' = Tk'[loan_k := σ_y]`.
```
nf ⌈let c = S σ'; let r = TailM &c; *r := σ_y; c⌉ = S B'                          // [Seal]
  ⟨∅, let c = S σ'; …⟩
  ⟨{c ↦ loan₁}, let r = TailM (borrow₁ (S σ')); *r := σ_y; c⟩                     // [Let]; [Borrow]
  ⟨{c ↦ loan₁ | x ↦ borrow₁ (S σ')}, match *x { Z => x | S p => TailM &p }⟩       // [App] unfold C itself
  ⟨{c ↦ loan₁ | x ↦ borrow₁ (S loan₂)}, TailM (borrow₂ σ')⟩                        // [Match] S arm; [Borrow] &(*x).1
  ⟨{c ↦ loan₁ | x ↦ borrow₁ (S Tk')}, borrow_k Tr'⟩                               // [Close], &Nat port: inner call stuck on σ'; k fresh; loan₂ := Tk'
  ⟨{c ↦ S Tk'}, borrow_k Tr'⟩                                                      // [Drop] TailM's frame: [End 1]; S Tk' (holding loan_k) moves into c
      // v0 here: x's content holds loan_k, so [Pop] parks it as _ ↦ borrow₁ (S Tk') and c stays loan₁
  ⟨{c ↦ S Tk', r ↦ borrow_k Tr'}, *r := σ_y; c⟩                                    // [Let]
  ⟨{c ↦ S Tk', r ↦ borrow_k σ_y}, c⟩                                               // [Assign] through r; [Drop] Tr' (borrow-free)
  ⟨{c ↦ S B', r ↦ ⊥}, c⟩                                                           // access c: its content holds loan_k, so [End k]
      // v0 here: c is loan₁; [Reorg] ends borrow₁, but its content holds loan_k, so first k (recursive side condition), then 1
  ⟨{c ↦ S B', r ↦ ⊥}, S B'⟩                                                        // [Read] c (copy); nf B' = B'
```
The same `S B'` as v0, with one rule ([End]) in place of [Pop]'s third case plus [Reorg]'s recursion.

### 6.4 `AddMEq`: goal and IH agree in both arms
Call frame of [Def]: `{c₀ ↦ loan₀ | x ↦ borrow₀ σ, y ↦ σ_y}`, `W = {c₀}`. The goal is `Eq (Unit × Nat) (UA, A) ((), B)`, where the right side comes from the run in the IH below with `σ` in place of `σ'`.
```
Z arm: {c₀ ↦ loan₀ | x ↦ borrow₀ Z, y ↦ σ_y} ⊢ refl : Eq (Unit × Nat) ((), σ_y) ((), σ_y)        // refl
  nf A[σ := Z] = σ_y, nf UA[σ := Z] = ()                                      // as §6.1a with σ_y for 0
  nf B[σ := Z] = σ_y                                                          // [Seal]
    ⟨{c ↦ loan₁ | x ↦ borrow₁ Z}, match *x {…}⟩                               // [Let]; [Borrow]; [App] unfold C itself
    ⟨{c ↦ loan₁}, borrow₁ Z⟩                                                   // [Match] Z arm; [Read] moves x; [Drop] frame (x is ⊥)
    ⟨{c ↦ loan₁, r ↦ borrow₁ σ_y}, c⟩                                          // [Let]; [Assign] *r := σ_y
    ⟨{c ↦ σ_y, r ↦ ⊥}, σ_y⟩                                                    // access c: [End 1]; [Read] c

S arm: {c₀ ↦ loan₀ | x ↦ borrow₀ (S σ'), y ↦ σ_y} ⊢ AddMEq &(*x).1 y : Eq (Unit × Nat) (UA', S A') ((), S B')   // [App]; goal refined by §6.1b and §6.3
  argument: x ↦ borrow₀ (S loan₁); borrow₁ σ', σ_y                             // [Borrow]; [Read] y
  type: [Call type] in Ω₁ = {c₀ ↦ loan₀ | x ↦ borrow₀ (S loan₁), y ↦ σ_y | x' ↦ borrow₁ σ', y' ↦ σ_y}
    W = owners(x') = {c₀}
    ⟦AddM x' y'⟧ = (UA', S A')                                                 // as §6.1b with σ_y for 0
    ⟦AddM' x' y'⟧ = ((), S B')
      ⟨Ω₁' | {x'' ↦ borrow₁ σ', y'' ↦ σ_y}, let t = TailM x''; *t := y''⟩      // [Read] x' (move), y' (copy); [App] unfold AddM'
      ⟨… | {x'' ↦ ⊥, y'' ↦ σ_y}, let t = TailM (borrow₁ σ'); *t := y''⟩        // [Read] moves x''
      ⟨{c₀ ↦ loan₀ | x ↦ borrow₀ (S Tk'), …} | …, let t = borrow_k Tr'; …⟩      // [App] stuck on σ'; [Close], &Nat port: loan₁ := Tk'
      ⟨… | {…, t ↦ borrow_k σ_y}, ()⟩                                           // [Let]; [Read] y''; [Assign] *t; [Drop] Tr'
      ⟨{c₀ ↦ loan₀ | x ↦ borrow₀ (S B'), …}, ()⟩                                // [Drop] t at let-exit: [End k] turns Tk' into B'; [Drop] AddM''s frame
      c₀ ↦ S B'                                                                // resolve: [End 0]
    type ≡ Eq (Unit × Nat) (UA', S A') ((), S B')                               // symbol for symbol the refined goal
```

### 6.5 `AddMEqOwned`: the merged footprint picks the same place on both sides
```
⊢ fix AddMEqOwned (x : Nat) : Id Unit (AddM &x 0) (AddM' &x 0) := AddMEq &x 0          // [Def]
  call frame {x ↦ σ}
  goal: W = owners(x) = {x}                                  // x occurs under &
    ⟦AddM &x 0⟧ = (U, N)                                     // [Borrow] x ↦ loan₁; [App] stuck; [Close]: loan₁ := N
    ⟦AddM' &x 0⟧ = ((), B₀)                                  // as §6.4 with σ, 0: x ↦ B₀ = B[σ_y := 0]
    goal ≡ Eq (Unit × Nat) (U, N) ((), B₀)
  {x ↦ σ} ⊢ AddMEq &x 0 : Eq (Unit × Nat) (U, N) ((), B₀)   // [App]
    argument: x ↦ loan₁; borrow₁ σ, 0                        // [Borrow]
    type: [Call type] in {x ↦ loan₁ | x' ↦ borrow₁ σ, y' ↦ 0}
      W = owners(x') = {x}                                   // x' is borrow-typed and its loan₁ is in x
      ⟦AddM x' y'⟧ = (U, N);  ⟦AddM' x' y'⟧ = ((), B₀)       // the same [Close] outputs as the goal
      type ≡ goal
```
The two clauses of v0's footprint (the `&` clause for the goal, the owner clause for the IH) must pick the same place `x`. One `owners` definition makes that automatic.

## 7. The elevator pitch, and what a reviewer would find ad hoc

**Pitch (as a reviewer would summarise v1).** Ochr is a dependently typed language with Rust-style mutable borrows. Definitional equality is decided by running one deterministic, LLBC-style machine on symbolic inputs (normalisation by evaluation), so there is no rewriting and no confluence to prove. A type is evaluated once, in the frame that binds it, which makes it a closed statement about values that later mutation cannot change. When a call gets stuck on a symbolic value, the machine replaces it with *sealed programs*: the same call, re-run on owned copies of its borrowed arguments, standing for its result and for the final content of each place it borrowed. These are Aeneas's backward functions, written in the source language. A definition is type-checked by running that same canonical call on fresh symbolic values. Effect-sensitive equality `Id A t u` is ordinary equality between *observations*: each side's result, paired with the final contents of the places it may write. The payoff is that a borrowed tail stays inside its parent in the environment, so the induction hypothesis about the tail, evaluated in the caller's environment, *is* the goal about the whole. In-place programs are then proved by the same structural recursion as pure ones.

**What a reviewer would call ad hoc in v0** (and whether v1 fixes it):
1. D6's `Eq` rules: a hand-picked fragment of observational type theory for `Nat`, `Unit` and pairs, which raises "why not all inductives?". **Fixed** (deleted).
2. `refl` against a goal D6 has reduced to `⊤`: no rule. **Fixed.**
3. Two unrelated `⊥`s: "moved out" and "False". **Fixed** (logical `⊥` goes).
4. Two kinds of nameless environment entry, ghost owners and pending borrows, each with its own rules. **Fixed**: the ghost is an ordinary variable of the generic caller, and pending bindings are gone.
5. [Close] as a case split on the result type. **Softened** to one rule with a port table; a reviewer may still see two cases.
6. Unit η inside an untyped normaliser. **Fixed** (moved out).
7. [Join] by anti-unification inside a "minimal" core. **Fixed** (it becomes an admissible, algorithmic rule).
8. "Ending loans is also allowed at any other time" inside a deterministic machine. **Fixed** (moved to §7 as a theorem, restated).
9. The "stuck outside any call" clause, "as if it were the body of a nullary call". **Corrected** (§8.1).
10. Unary syntax with n-ary [Close]. **Fixed.**
11. Still ad hoc in v1: the footprint is a syntactic analysis ("occurs under `&` or on the left of `:=`"). §2.4 shows it cannot be semantic, but a reviewer will still ask for its justification. The answer is stability under refinement, and it should be stated in the paper.

## 8. Gaps in v0 found along the way (not minimality, but they affect v1's text)

- **8.1 A term stuck outside any call.** v0: "close it off as if it were the body of a nullary call". A nullary call has no borrow arguments, so [Close] would fill no loans, and the closure would capture `t`'s borrow-typed free variables, which the scope forbids. Correct version (01 §5's "smallest unit with a known footprint"): λ-lift `t` over its free variables, passing the variables in `W` by borrow, and apply the ordinary [Close] to that call. The fill lands in the immediate loan, and resolution carries it out to the owner, exactly as for real calls. Not used by E1/E2.
- **8.2 [Read] is undefined on content that holds a loan without being one** (e.g. `S loan_k`). v0 creates exactly such content itself, in `AddMZero`'s S arm (`x ↦ borrow₀ (S loan₁)`). v1's access rule covers it. This agrees with deriver-e2's F2.
- **8.3 Unary syntax** (§2.9). Also deriver-e1's F2.
- **8.4 A proof call seals the place it borrows.** In the checked term, `AddMZero &p` is run by the machine for its value. It gets stuck, and [Close] fills `loan₁` with `⌈let c = σ'; AddMZero &c; c⌉`. So after any lemma call on a borrow, the checker has forgotten the borrowed content. This is invisible in E1/E2, where the recursive calls are in tail position (deriver-e1 N1 agrees), but any proof that calls a lemma on `&x` and then continues will hit it. The natural fix is proof erasure (`Prop`): the machine does not run calls whose result is a proof. That requires such calls to have no effects, which draws a line by *type*, not by the programmer; it must be checked against end goal 2. This is the right motivation for bringing `Prop` back (§2.1).
- **8.5 [Split] refines only an abstract `σ`.** A match on a sealed program in a checked term (e.g. on the content behind a returned borrow, `⌈…; *r⌉`) has no rule. It needs generalisation (abstract the neutral, then split), as Lean's `cases h : e` does.
- **8.6 [Seal] on a program with an open hole.** Handled in v1 by "a loan whose borrow is absent is inert" (deriver-e2 F3). In v0, the run writes `loan_k` into a place and later tries to end a borrow that is not there.
- **8.7 [Seal] loops on its own call** (deriver-e1 F1): folded into v1's [Seal] (§4.3).

## 9. Ranked proposals (one line each; the most impact per unit of risk first)

1. **Delete D6** (five `Eq` conversions + `⊤ ∧ P`) together with `Prop`, `⊤`, logical `⊥`, `∧`, `⟨_,_⟩`. `AddMZero`/`AddMEq`/`AddMEqOwned` are unchanged (goal ≡ IH already, §6.1/§6.4/§6.5); `AddZero` uses `congS` from `J` (§6.2). This also removes the `refl`-against-`⊤` gap.
2. **Merge ghost owners + [Lam]'s snapshot into [App]:** check a definition at its generic canonical call (the `L; C` of [Close]); one [Call type] rule gives both the goal and the IH (§2.3, §6.0).
3. **Delete anonymous pending bindings:** loans are variables and [End] substitutes (loans inside the content travel with it). One representation of "the tail is borrowed", and it also fixes deriver-e2's F2–F4 (§2.2, §6.3).
4. **Move [Join] out of the core:** [Split] forks the rest of the check; [Join] is admissible and becomes D7's checker algorithm. E3 is accepted by the core. **Needs the lead's or user's call on D7** (§2.6).
5. **Merge [Reorg], [Pop], [Assign]'s drop and resolution** into [End] + [Drop] + one access rule (§2.9, §4.3).
6. **Merge [Close]'s two forms** into one rule with a type-directed port `(wrap, get, put)`; keep the loan hole rather than a λ (§2.5).
7. **Merge the footprint's two clauses** into one via `owners` (§2.4); keep it syntactic.
8. **λ → n-ary `fix`, saturated calls** (one function former; closes the currying/scope gap) (§2.9).
9. **Delete the `n v` neutral** and the "name vs closure" case in [Close] (§2.9).
10. **Move Unit η out of [Seal]** (not used; the only type-directed clause of `nf`) (§2.8).
11. **Merge Refinement into [Seal]; state [Ref]'s "reading ⊥" once; move "end loans at any other time" to §7 as a theorem** (§2.9).

**Kept after scrutiny:** D3 copy-on-read (needed by the prover half and by E4; correct the rationale, §2.7); runtime `⊥`; the syntactic footprint; loan holes; pairs; `Type`; `J`; [Close]; [Seal]; [Split]; the recursion guard.

**Proposed decision-log entries** (for the lead): D6 revisited, "`cong` is cheaper than the conversions; the borrow examples never needed them". D3's "Why" rewritten as in §2.7. New: "Loans are variables; ending a borrow substitutes its content everywhere; no side condition (deletes pending bindings; fixes deriver-e2 F2–F4). Revisit if two-field data makes the extra permissiveness over Rust unsound". New: "[Split] forks; [Join] is the checker's algorithm (D7), admissible over the core".
