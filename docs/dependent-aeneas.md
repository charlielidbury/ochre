# Dependent Aeneas

*Working note — using Aeneas's symbolic execution, by itself, as a dependent type checker.*

This is a design sketch capturing a chat exploration so we can iterate on a written artifact rather than re-deriving it each time. It is **not** formalized and is deliberately hand-wavy in places; open questions are tracked in §9. The driving example (in-place quicksort over mutable slices, §7) is chosen because it touches every component at once.

---

## 1. The one-line idea

Aeneas's symbolic interpreter (§4 of the paper) is already a **bidirectional elaborator**: forward symbolic execution is the checking pass, the emitted λ-term is the elaborated core term, and *rejection is already in there* — the "no outer loans" / freshness side-conditions are typing errors. Today every rejection condition is about **ownership**. We make three changes:

1. **Delete the translation.** No λ-term output. Keep only the environment evolution and the side-conditions — use the symbolic interpreter as a pure **accept/reject** checker.
2. **Add Agda-style dependent types.** Π / Σ / inductive families / a universe / definitional equality. **No refinements, no SMT.** The *only* solver is conversion (`≡`); remaining obligations are discharged by **user-written proof terms**.
3. **Remove panic.** Aeneas's error monad exists to mirror Rust faithfully; we are designing a new language, so every primitive is **total** (§2).

Result: a dependent type checker for a subset of Rust in which **borrows are checked operationally** (the borrow tree) rather than via a separation logic, with **one language** (§4). This is exactly Ochre's "typing = abstract interpretation" thesis, instantiated on Aeneas's borrow machinery.

---

## 2. Scope and non-goals (the relaxations, and the one removal)

Recorded decisions, so iteration stays on the same ground.

Things we **do not require**:

- **Decidability.** The checker may diverge. The guarantee is conditional: *if it accepts, the program is safe.* A non-terminating conversion check just never answers.
- **Runtime termination.** Circular / non-terminating programs are accepted.
- **Consistency (yet).** General recursion + `Type : Type` ⇒ the logic is inconsistent until a termination check is added. We want **type safety**, not logical soundness — these differ *exactly* at termination (§3).
- **Refinements / SMT.** Bounds etc. are expressed structurally (`Fin n`), not as predicates; obligations are discharged by conversion + proof terms.

The one thing we **remove** versus Aeneas:

- **Partiality.** Aeneas carries an error monad (`result`, `Fail`/`Return`) to mirror Rust's panics (overflow, out-of-bounds, `unwrap`). We do not simulate Rust, so we drop it: **every primitive is total**, and partiality is always an explicit proof argument — `get : (v : Vec n T) → Fin n → T`, `div : ℕ → (d : ℕ) → d ≠ 0 → ℕ`. There is no `panic`, no `Fail`, no `result` monad. Consequences: the value semantics is total (only divergence remains), conversion is just normalization of a total deterministic language, and "precondition obligations" are not a separate notion — they are ordinary function arguments.

---

## 3. The soundness statement we are aiming for

We want **type safety**, not logical soundness. They come apart precisely at termination, which is why dropping termination costs nothing.

"Explode at runtime" = reach a **stuck** configuration: `(Ω̂, s)` where `s` is not terminal and no reduction rule applies — deref of `⊥` (use-after-move / use-after-end), a `match` whose scrutinee hits no branch (variant confusion), a missing field/index projection. With panic removed there is no `Fail`/`panic` state at all, so the only non-stuck-non-value outcome is **divergence**.

> **Theorem (safety, target).** Let `Ω̂ ⊨ Ω` be the *realization* relation: the concrete environment `Ω̂` instantiates each `(σ:τ)` in the symbolic context `Ω` by a concrete value of type `τ`, and matches its borrow/loan structure. If `Ω ⊢ s ⊣ Ω'` (the checker accepts, evolving `Ω` to `Ω'`) and `Ω̂ ⊨ Ω`, then
>
> - **Progress:** `s` is terminal, or `(Ω̂, s) →` steps (never stuck); and
> - **Preservation:** if `(Ω̂, s) → (Ω̂₁, s₁)` then `∃ Ω₁. Ω₁ ⊢ s₁ ⊣ Ω'` and `Ω̂₁ ⊨ Ω₁`.
>
> Hence an accepted program **either diverges or reaches a value of its declared type** — full stop. No stuck states, no panic.

Three notes:

- This is the **§4-simulates-§3 theorem that Aeneas asserts but never proves** (their implementation is trusted; "after every rule we verify a large number of invariants"). The dependent layer adds two lemmas: **conversion is sound for the value semantics** (`τ ≡ τ'` ⇒ they classify the same concrete values), and **dependent-match telescope substitution is sound** (the branches unification prunes really are unreachable).
- It is **compositional**: each function is checked once against its region-signature (the `A(ρ)` wand); sound wands compose, so the simulation holds per-function and composes without inlining. A recursive call is "assume the signature you separately checked" — sound for *safety* regardless of whether the recursion terminates.
- Total primitives make **progress unconditional**: a well-typed non-value term always steps.

---

## 4. One language; relevance is positional

Types and terms are a single language: **a type may mention any term**, including one that manipulates references. Conversion (`≡`) is decided by evaluating the terms a type mentions, and three properties of Aeneas's semantics make that sound:

- **Deterministic.** The value semantics is deterministic; reorganizations are administrative and commute. The value a term computes is unique.
- **Total.** With panic removed (§2), the value semantics is total — only divergence remains.
- **Reference-inert.** Aeneas's thesis: references have no semantic content, so *every term already has a pure value meaning*, which is what conversion uses.

A type could only fail to have a value meaning if it depended on **aliasing or pointer identity**. Aeneas is address-free and tree-shaped, so identity is unobservable and such a type cannot even be written — which is what lets types range over the full language.

Concretely, there are two *orthogonal judgments* over the one syntax:

1. **Conversion** compares the **symbolic values** `σ` the executor tracks. A reference value `borrowᵐ ℓ σ` is compared by its pointee `σ`, ignoring the generative loan-id `ℓ` (sound because identity is unobservable). References therefore contribute only their pointee to conversion; in practice conversion rarely sees one, since an index comparison `Vec n T ≡ Vec n' T` reduces to `n ≡ n'` over ordinary total data. Conversion is **normalization of a total deterministic language** (which may diverge — accepted, §2).
2. **The borrow discipline** reads the reference structure.

These are orthogonal, and two things hide under one careless word ("relevance"). Keeping them apart is what makes §6 work:

- **Erasure / computational relevance** governs *runtime representation* only: a value is `@1` (carried at runtime) or `@0` (erased, present only for checking).
- **Ownership** is about *borrow values*: the borrow discipline tracks every `borrowˢ`/`borrowᵐ`/loan **wherever it occurs — including inside an erased proof.** A borrow is a borrow; the check is static and needs no runtime witness.

So the rule for whether an occurrence touches ownership is **containment, not position**:

- *Mentioning* a value or index in a type — `Vec n T`, or the type `Sorted (*b)` referring to `b`'s pointee — is **free**: no ownership, no consumption. This is "dependent types for free," and it must stay free or you could not form types about borrowed data.
- *Containing* a borrow **value** in a term — a witness that packages an actual `borrowˢ ℓ` — **holds** that borrow, whether or not the enclosing term is erased.

An erased proof can therefore hold a borrow: it registers a static loan, the checker blocks any conflicting mutation, and at runtime both the proof and the borrow are gone while the verified program simply never performs the blocked mutation. Relevance is then mostly *inferred from use* and surfaces to the programmer only as the slice-vs-array choice below.

### Where relevance is visible: slices vs arrays

The one place relevance surfaces for the programmer is the same choice Rust already makes:

```
array   Array N T   :  N is a type parameter — erased.  No `len`; cannot branch on N.
slice   Slice T  ≜  Σ (n : ℕ). &ᵐ Vec n T
                    :  n is a stored field — relevant.  `len s = s.1` (a real read); `&mut`
                       freezes n, so it is usable in the body's type throughout the borrow.
```

You do not annotate a multiplicity; you choose whether the length is a **stored field** (slice — readable, branchable) or a **type parameter** (array — erased), exactly as a Rust programmer chooses between `[T]` and `[T; N]`. `Slice T` is an **ordinary dependent pair**, with a borrow as its second component.

**Quicksort forces the slice.** The pivot is runtime data, so sub-slice lengths are runtime data; the erased-array model cannot even type the result of a runtime split. So quicksort takes a `Slice T`, and `len` reads the field.

### The boundary

This leans hard on **no observable pointer identity**. Interior mutability / `unsafe` (`RefCell`, aliased `&mut`) makes aliasing observable, and then "a reference erases to its pointee" is no longer sound — two equal-pointee references could behave differently. So this design is sound for the **safe-Rust subset Aeneas targets**; recovering interior mutability (a stated Ochre goal) would need a separate account of identity. Tracked in §9.

---

## 5. Borrows as a substructural modality over the dependent context

With the translation gone, `&ᵐ` / `&ˢ` are best read as a **resource modality on the dependent context**:

- **`&ˢ τ`** — duplicable read access; the value (hence its dependent *index*) is **stable**, so the index may be mentioned in types freely. *Dependency is free under shared borrows.*
- **`&ᵐ τ`** — a **typed hole** in the context with fill-type `τ`; the index is **pinned to `τ` for the borrow's lifetime**; ending the borrow discharges `convert(current, τ)`.
- **Region abstraction `A(ρ)`** — the Π-elimination machinery for resource-consuming functions; the "magic wand."

Two parts of §4 of the paper collapse:

- The **backward function** is no longer a *synthesized term*; it becomes a **conversion / proof obligation at `End-Abstraction`** (see the next subsection).
- The **projector apparatus** shrinks to **loan ↔ region routing**: which region owns which loan and at what fill-type each must be returned.

Sketch rules (house notation: conclusion first, premises indented; see `notation.md`):

```
[E-Assign] (dependent)
Ω ⊢ p := rv  ⊣  Ω'
  Ω ⊢ rv ↝ v ⊣ Ω₁              // evaluate the rhs symbolically (total — no Fail)
  Ω₁ ⊢ p : τ_p                 // expected type at the place
  Ω₁ ⊢ v : τ_v                 // synthesised type of the value
  Ω₁ ⊢ τ_v ≡ τ_p               // definitional equality — the only "solver"
  no outer loans on the old value at p   // Aeneas's existing ownership check
  Ω' = Ω₁[p ↦ v],  old value retained as ghost x_old
```

```
[E-Match] (dependent — telescope substitution)
Ω ⊢ match p with … | Cᵢ x⃗ → sᵢ | …  ⊣  Ω'
  Ω ⊢ p ⇒ˢ (σ : D a⃗)          // read scrutinee's symbolic value & type
  for each constructor Cᵢ of D:
    σ unifies with Cᵢ σ⃗ᵢ  ⟹  Ωᵢ = Ω[σ := Cᵢ σ⃗ᵢ]   // substitute into the WHOLE telescope
    σ fails to unify        ⟹  branch i is dead (absurd / `()`), no obligation
    Ωᵢ ⊢ sᵢ ⊣ Ω'                                    // each live branch reaches the same Ω'
```

```
[End-Mut] (dependent — backward function as an obligation, no codegen)
A(ρ), Ω  ↪  Ω'
  A(ρ) owns borrowᵐ ℓ (σ_now : τ_now)         // current contents of the borrow
  ℓ is the loan of place x, expecting fill-type τ_x    // recorded at borrow creation
  Ω ⊢ τ_now ≡ τ_x                              // contents convert to the origin's type
  // a relational postcondition, if any, is discharged here:
  //   Ω ⊢ pf : P(σ_init, σ_now)               where σ_init = old (*x)   (next subsection)
  Ω' = Ω[x ↦ σ_now],  A(ρ) discharged
```

### `old`, and the backward function as a specification

A `&mut` separates the value a place had *when borrowed* from the value it has *when given back*. The mechanism that names the former is `old`:

- **`old *v`** is the **entry snapshot** — the symbolic value σ₀ that `*v` held when the borrow was taken. It is exactly Aeneas's `x_old` ghost (§3.4): an **erased** name in the type context (`@0`), **not a runtime copy.** Nothing is cloned; the array is mutated in place. σ₀ persists only for the proof to point at.

Aeneas's **backward function** for `f(v: &mut T)` is the map "value when borrowed ↦ value written back":

```
f_back  :  (value when borrowed)  ↦  (value at give-back)
        =        old *v           ↦         *v
```

So `old *v` is *literally the input to the backward function*, and the final `*v` is *its output*. `old` exists **because we deleted the backward function as a term**: with the translation you would state specs about `f_back` (e.g. `Sorted (quicksort_back σ₀)`); having no such term, we **name both endpoints** — `old *v` for the input, `*v` for the output — and relate them with a proposition. The postcondition `P(old *v, *v)` *is* the backward function's specification; we specify its graph instead of computing it.

Mechanically:

- **At a definition**, we *prove* it: entry binds `*v = σ₀`, the body mutates to `*v = σ'`, and `P(σ₀, σ')` is the discharged obligation (the `[End-Mut]` premise). Here σ' is the actual computed result.
- **At a call** `f(v)` where `*v = σ_a`: instantiate `old *v := σ_a`; when the borrow is given back — Aeneas's `End-Abstract-Mut`, which **replaces the written-back location with a fresh symbolic value to account for modification** — mint a fresh σ_b for `*v`; and *assume* `P(σ_a, σ_b)`. We never compute `f_back`; we mint σ_b and assume its spec.

> backward function = the opaque relation `old *v → *v`;  postcondition = its specification;  `old *v` = its argument;  the fresh post-value = its result.

This is the Aeneas style (a fresh value at write-back), not RustHorn's prophecy (which names only the final value, forward). We hold both endpoints symbolically, so we just relate them. And **composing backward functions becomes composing postconditions** — the value-level proof chain of §7. `old` is also the `&mut` analog of "the input argument" for a by-value function: `f(x : Vec n T) → Σ y. Perm x y` relates output to input directly because `x` is in scope as a value; with `&mut`, entry and exit values of the same place differ, so you need `old *v` to name the former.

---

## 6. Specifying behaviour: borrow-carrying certificates

A fact about a *mutable* value is dangerous — it goes stale the moment the value changes. The device that makes such a fact sound is to **tie proof-validity to borrow-validity**: a certificate that *holds a shared borrow* of its subject is valid for exactly as long as the subject cannot be mutated, and mutating requires dropping the certificate first. The borrow checker becomes the enforcer of proof freshness — for free, where a separation-logic system would need framing.

We write the certificate with sugar:

```
P(&*v)   ≜   { hold (b : &ˢ Vec n T) = &*v  ;  proof : P(*b) }
```

i.e. a value carrying a **shared borrow** `b` of `v` together with **erased evidence** `P(*b)`. The borrow (relevant or erased — §4) does the freezing; the evidence is the proof. This desugars to a dependent pair `Σ (b : &ˢ Vec n T). P(*b)`, but the Σ never appears in a signature.

Design choices baked in here, with rationale:

- **Keep `P` a value-level predicate** (`Sorted : Vec n T → Prop`, `Perm : Vec n T → Vec n T → Prop`, …). The mathematical content — "this *value* is sorted" — is about a value, and values are immutable, so `Sorted σ` is an eternal, proof-irrelevant fact. That is what internal proofs manipulate. The borrow is *orthogonal packaging* added by the `P(&·)` sugar, and the sugar works for **any** predicate (and any conjunction of them), so `Perm`, `Distinct`, etc. compose freely before being attached to a borrow.
- **Why not weld the borrow into the predicate** (`data Sorted (b : &ˢ τ)`)? It only freezes if the constructor *stores* `b` — and once it stores `b`, it *is* this Σ, just named per-predicate and no longer reusable, and you lose a value-level proof-irrelevant `Sorted` for internal reasoning and composition. Welding is fine if you will *only ever* use sortedness through a borrowed view; most developments want the value-level layer.
- **Certificates are borrow-scoped, not eternal.** `P(&*v)` is valid exactly while its borrow is live; mutating `v` (which ends the borrow) invalidates it — unlike `2+2=4`, true forever. Shared-borrow certificates are still freely *duplicable*, but every copy dies together on mutation (they share one loan). A `&ᵐ`-carrying certificate would additionally be affine. So proof-irrelevance is **conditional**: full for borrow-free proofs, borrow-scoped for borrow-carrying ones — which is exactly right, since "currently sorted" *should* be perishable.
- `P(&*v)` is also **more precise than an existential** `Σ (b : &ˢ). P(*b)`: it names *which* borrow (of `v`) is frozen, rather than asserting some sorted view exists.

### Two mechanisms keep a proof fresh

This is the key distinction for reading the next section. A proof about mutable data stays valid by one of two means:

- **Eager-pin (value facts).** A fact about a *specific value* σ is eternal. When a function returns a fact "about `*v`", the checker resolves `*v` to the concrete return-moment value σ₁ and the held proof is `… σ₁ …`, immune to later mutation of `v`. **No borrow** is held. Used for *intermediate* facts you only reason with.
- **Borrow-freeze (certificates).** A fact you want tied to the *live place* (so the caller can use it against the actual `v`) is carried with a shared borrow that freezes `v`, as above. Used for *results* the caller will hold.

Functions that hand a `&mut` back (because the caller will keep mutating) export **eager-pinned value facts**; functions that are *done* and want to certify their result downgrade to a **borrow-freeze certificate**.

---

## 7. Worked example: in-place quicksort over mutable slices

### 7.1 Vocabulary (value-level, eternal, proof-irrelevant)

```
Sorted        : Vec n T → Prop
Perm          : Vec n T → Vec n T → Prop                    -- same length
AllLE         : Vec a T → Vec b T → Prop                    -- ∀ i j. xs[i] ≤ ys[j]

-- the three lemmas that do all the work (pure core):
perm_AllLE    : Perm xs xs' → Perm ys ys' → AllLE xs ys → AllLE xs' ys'   -- AllLE is perm-stable
concat_sorted : Sorted xs → Sorted ys → AllLE xs ys → Sorted (xs ++ ys)
perm_concat   : Perm xs xs' → Perm ys ys' → Perm (xs ++ ys) (xs' ++ ys')
```

### 7.2 The three signatures

```
partition (v : &ᵐ Vec n T) {n ≥ 2}
  : Σ (k : Fin n). Perm (old *v) (*v) ∧ AllLE (take k *v) (drop k *v) ∧ 0 < k
  -- hands &mut v BACK (quicksort still needs to mutate). Facts are value-level,
  -- EAGER-PINNED to *v-at-return = σ₁. k is relevant; the proofs are erased.

split_at_mut (v : &ᵐ Vec n T) (k : Fin (n+1))
  : Σ (lo : &ᵐ Vec k T) (hi : &ᵐ Vec (n−k) T). (*lo ≐ take k *v) ∧ (*hi ≐ drop k *v)
  -- ≐ is definitional: the executor just learns the two halves; almost no "proof".
  -- discharges the index obligation k + (n−k) ≡ n here. Region A(ρ) holds the
  -- reassembly: returning lo, hi (at any access level) reconstitutes v.

quicksort (v : &ᵐ Vec n T) : SortedPerm (old *v) (&*v)
  where SortedPerm a ≜ λ x. Sorted x ∧ Perm a x
  -- terminal: BORROW-FREEZE certificate carrying a shared borrow of v plus
  -- Sorted(*v) ∧ Perm (old *v) (*v). Downgrades &mut v → shared while held.
```

The asymmetry is the §6 distinction in action: partition and split are mid-pipeline (the caller keeps mutating), so they hand `&mut` back and export eager-pinned value facts; quicksort is done, so it returns a borrow-freeze certificate.

### 7.3 The flow

```
fn quicksort (v : &ᵐ Vec n T) -> SortedPerm (old *v) (&*v) {
  // σ₀ ≜ old *v  (entry ghost, pinned)
  if len(v) ≤ 1 { return freeze(v) ⟨sorted_≤1, perm_refl⟩ }   // base case

  let ⟨k, hperm, hle, _⟩ = partition(v);
      //  *v ≐ σ₁     hperm : Perm σ₀ σ₁     hle : AllLE (take k σ₁) (drop k σ₁)

  let ⟨lo, hi, hlo, hhi⟩ = split_at_mut(v, k);
      //  σ_lo ≜ *lo ≐ take k σ₁     σ_hi ≜ *hi ≐ drop k σ₁      (so AllLE σ_lo σ_hi  =  hle)

  let clo = quicksort(lo);      // clo : SortedPerm σ_lo (&*lo) — holds a shared borrow of lo
  let chi = quicksort(hi);      // chi : SortedPerm σ_hi (&*hi) — holds a shared borrow of hi
      // unwrap their evidence to value level:
      //   Sorted σ_lo', Perm σ_lo σ_lo'   (σ_lo' ≜ *lo now)
      //   Sorted σ_hi', Perm σ_hi σ_hi'

  // combine — all value-level, eternal:
  //   AllLE σ_lo' σ_hi'                 ← perm_AllLE (Perm σ_lo σ_lo') (Perm σ_hi σ_hi') hle
  //   Sorted (σ_lo' ++ σ_hi')           ← concat_sorted (Sorted σ_lo') (Sorted σ_hi') (AllLE …)
  //   Perm σ₀ (σ_lo' ++ σ_hi')          ← trans hperm (perm_concat (Perm σ_lo σ_lo') (Perm σ_hi σ_hi'))
  //   and  *v ≐ σ_lo' ++ σ_hi'          (reassembly)  ⇒  Sorted(*v) ∧ Perm σ₀ (*v)

  return combine(clo, chi) ⟨concat_sorted …, perm_proof …⟩
}
```

### 7.4 How proofs and witnesses pass

- **partition → quicksort:** an erased Σ of *value facts* (`Perm σ₀ σ₁`, `AllLE (take k σ₁) (drop k σ₁)`) plus the relevant index `k`. No borrow — `&mut v` flows back so quicksort can keep mutating; the facts are eager-pinned to σ₁, so they survive the subsequent mutation.
- **split → quicksort:** almost nothing *to prove* — the executor just *learns* `σ_lo = take k σ₁`, `σ_hi = drop k σ₁` (definitional), plus the two `&mut` halves and the region `A(ρ)`. The only real obligation is `k + (n−k) ≡ n`.
- **recursive quicksort → quicksort:** the *certificates* `clo`, `chi`. Each is used **two ways**: its erased evidence is *unwrapped* to value level for the combine, and its shared borrow is *retained*. The returned cert over `v` **bundles `clo` and `chi`** — their two shared sub-borrows jointly *are* a shared borrow of `v`, so the cert freezes `v` by holding the pieces. Certs nest.
- **quicksort → caller:** the bundled cert `SortedPerm σ₀ (&*v)`. The caller holds shared, sorted `v`; to mutate again they drop it, which drops both sub-borrows, ends `A(ρ)`, and reconstitutes `v` mutably.

Borrow choreography underneath: `&mut v` → (partition borrows and returns it) → `&mut v` → split → `&mut lo`, `&mut hi` → each recursion downgrades its half to a shared borrow inside its cert → parent cert holds both = shared `v`. `A(ρ)` from the split stays open exactly as long as the returned cert lives.

The two load-bearing assumptions: **`AllLE` permutation-stability** is what carries the pivot bound from the unsorted halves (where partition established it) to the sorted halves (where `concat_sorted` needs it); and **`split_at_mut`'s region must support a shared-level reassembly**, so two shared sub-certs compose into one cert over the parent. These are the first two things to nail down.

---

## 8. Where the components actually interact (distilled)

1. **Disjoint `&mut` split is free** — the value model has no addresses, so `split_at_mut` needs no `unsafe` and no disjointness reasoning. (Biggest single win; the reason this substrate fits.)
2. **Dependent indices bite only at reassembly**, as a conversion `k + m ≡ n` at `End-Abstraction`. The *encoding* (`Vec (k+m)` vs `Vec n` with `n−k`) decides definitional-vs-lemma; no SMT means "needs a lemma" is the honest default.
3. **`Fin n` replaces refinements, and total primitives replace the error monad.** Bounds-safety is structural — an out-of-bounds access is not *checked*, it is *not expressible*. The safety theorem's only non-value outcome is divergence.
4. **`&mut` pins its index** for the borrow's lifetime; partition/swap are length-preserving so they are obligation-free. Only length-*changing* ops (e.g. `push`, not in quicksort) would force an existential `&ᵐ (Σ n. Vec n T)`.
5. **Two freshness mechanisms** (§6): intermediate facts are *eager-pinned* value facts (eternal, no borrow); results are *borrow-freeze* certificates (`P(&*v)`, tied to the live place). The first is what flows *between* the three functions; the second is what quicksort *returns*.
6. **`old *v` is the backward function's input** (§5): the relational spec relates `old *v → *v`; we specify that graph rather than synthesize a term. Composing backward functions = composing postconditions, which is the §7.3 proof chain.
7. **Ownership tracks borrow values everywhere, even in erased proofs** (§4); relevance/erasure is orthogonal and governs only runtime representation. *Mentioning* is free; *containing a borrow* holds it. One language, one syntax.
8. **Termination is never consulted for safety** — recursion is admitted unconditionally; well-foundedness re-enters only to make the correctness proof a *theorem* rather than a safe coincidence.

---

## 9. Open questions / to pin down

- **`split_at_mut` rule, precisely** — how the coercion (`k+m≡n`) enters a borrow rule, and **shared-level reassembly**: the region `A(ρ)` must let two *shared* sub-certs recombine into one cert over the parent. This is the load-bearing borrow-mechanic for §7.
- **The mention-vs-contain rule, formally** — state that ownership tracks borrow *values* wherever they occur (including erased proofs) while erasure governs only runtime representation, and that *mentioning* a value/index is free. Prove the two stay orthogonal under every rule.
- **Conversion-on-values, formally** — conversion compares symbolic values modulo loan-ids; prove it sound for the value semantics (the "references erase to their pointee" lemma). The load-bearing lemma behind §4.
- **`AllLE`-style perm-stability as a pattern** — the general shape "a spec established before a sub-call survives the sub-call's mutation because it is permutation- (or otherwise) stable". Worth isolating; it is how *any* relational spec composes across recursion.
- **Proof-irrelevance, conditional** — borrow-free proofs are irrelevant/eternal; borrow-carrying certificates are borrow-scoped resources. What universe structure captures the split cleanly?
- **Relevance inference** — confirm it never needs an explicit annotation beyond the slice-vs-array (stored-field-vs-parameter) choice.
- **Interior-mutability boundary** — §4 is sound only under no-observable-identity. What would an account of identity (`RefCell`, aliased `&mut`) need, and is the address-free restriction acceptable as a stage, given `RefCell` is a stated Ochre goal?
- **Dependent pattern matching through `&mut`** — matching `*p` refines the *pinned* index; the resulting equations (`n ≡ succ m`) must thread into the region-end conversion. Check it composes (it should reject putting a `Nil` back through `&ᵐ Vec (succ m) T`).
- **Minimal dependent core** — Π, Σ, inductive families, an identity/`Id` type, a universe. What is the smallest core that types the quicksort proof?
- **Termination, later** — well-founded recursion on the length index, to recover a *consistent* logic. Out of scope for safety; required for the correctness proof to carry meaning.

---

## 10. Relationship to the original Ochre spec

Same founding thesis — *typing = abstract interpretation* (`what-is-ochre.md`) — but a different point in the design space, worth tracking as an explicit fork:

- **Original Ochre:** sets-of-values + structural subtyping + strong mutation (a variable's type narrows to a singleton after assignment). The recorded unsoundness was **subtyping-preservation failing under environment narrowing**.
- **This sketch:** Agda-style **conversion** (definitional equality), **no subtyping**. This sidesteps the exact failure mode — no subtyping means no narrowing-of-subtypes to preserve.
- **Staging:** rather than Och → Ochr → Ochre, this aims **straight at the mutable-reference system** by importing Aeneas's region/wand machinery for the borrow layer.

The cost of the fork is real and should be decided deliberately: dropping subtyping/unions loses the "precise unions preserve fine-grained type information" ergonomic that was a selling point of Ochre. Open question: is conversion-only acceptable for Ochre's ergonomic goals, or do we need a subtyping-flavored conversion (and then: does the narrowing unsoundness return)?
