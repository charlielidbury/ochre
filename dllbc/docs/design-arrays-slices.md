# Arrays, Range Places, and Proof-Licensed Carving

*A design note for DLLBC, in the voice and numbering conventions of `dllbc-arrows.md`. References of the form §N are to that document; references of the form ¶N are internal to this one. Nothing here is implemented; everything here is meant to be implementable from the text alone.*

---

## ¶0. Thesis, and why now

The verified in-place quicksort (M22, closed) sorts a `&mut List Nat` addressed by a pair of comptime indices `(lo, cnt)`. Every predicate in its postcondition is range-scoped — `SortedR cnt lo (*v)` — and every lemma in its library carries a range-fits bound `Le (add lo cnt) (len *v)`. The reason is structural and unavoidable in the present calculus: **a segment of a list is not a place.** A prefix is not a subterm of a right-nested `Cons` tree, and neither is a middle; only a suffix is. So the recursion cannot hand a sub-segment to its callee. It hands the *whole* list plus two numbers, and the callee's contract must therefore describe the whole list — including the part it must not touch.

That is the frame problem, and the calculus currently pays for it three times over. It pays in the **predicate library** (every predicate indexed by a range, `AllLeR`/`AllGtR`/`SortedR` in bounded-Π form). It pays in the **arithmetic** (the M22-c pain diary's lemma-guarded subtraction for the right-segment reindex; the `noAbove`/`noBelow` multiset detour, needed because positional bounds are not permutation-invariant once positions are absolute). And it pays in **length lemmas** (`len_partitionRangeL`, `len_sortRangeL`) whose entire job is to transport a bound across a mutation that obviously preserves length.

M23's ownership-splitting stopgap — `split_off`/`append_back`, take-and-refill of the tail by value — buys segment-shaped recursion at the price of writing a different program: the list's runtime shape mutates, and each split walks `O(i)` cells. It is the right stopgap and the wrong destination.

This note designs the destination. The claim in one paragraph:

> Add an `Array n T` former whose values are flat runs of element slots, and extend the place grammar with an **index step** `a[i]` and a **range step** `a[lo ; cnt]`. A range is then a place, so a range borrow is an ordinary `&mut`. Two range borrows of one array coexist not because the checker believes an aliasing argument but because, after a **carve** — a lazy reorganization that splits an array node into segments — they are literally *different subterms of one value tree*, and §3.3's suspension machinery already knows what to do with those. The carve is the only new rule, and it is the one that consumes evidence: it fires only when handed a comptime proof `Le (add lo cnt) n`, whose content is exactly the existence of the residue the carve introduces. **Proofs license reorganizations; reorganizations restore structural disjointness; the borrow machinery is unchanged.**

And the payoff, which is larger than "quicksort gets nicer": when a callee is handed a *sub-slice* rather than a whole array plus indices, the untouched residue never enters the call. It is still sitting in the caller's value tree, pinned to the very σ it held before. The §6.1 group-end replaces one loan's payload, not the whole array's. **The frame is preserved by construction rather than described by a contract** — which is the structural obstacle M22's central finding named ("issued borrow payloads are minted as opaque σs"), attacked from the side rather than head-on.

### 0.1 What is actually new here, and what is not

Stated up front because ¶7 surveys a crowded field and the crowd has most of the pieces. Every system in that field separates the same three concerns:

* **(i) an interval-arithmetic disjointness predicate** — `hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁`, in Low\*, in VST, in rustc's constant-index path, derivable in Iris;
* **(ii) an exclusivity discipline** that makes coexistence a question worth asking — Rust's borrow checker, separation logic's `∗`, Verus's linear ghost tokens;
* **(iii) a recombination story** — `array_app` read backwards, Iris's magic wand, Aeneas's backward function, Creusot's prophecies, RustBelt's inheritance-at-lifetime-death.

The claim is a **conjunction**, not a component: no prior system routes (i) through the *program's own dependent proofs* in order to license (ii) inside the operational semantics. Rust hardwires (i) and only for constants. Separation logic discharges (i) in the meta-logic, by a proof the programmer writes in a proof mode, not one the checker consumes. Low\* has (i) and (iii) but no (ii) at all — its buffers may overlap freely, so disjointness is never a *permission* question, only a framing one. Verus's tracked layer has (ii) and (iii) with genuine user-discharged obligations, but on ghost tokens detached from the type of any surface `&mut`. The conjunction that is missing everywhere is: ownership-transferring, exclusivity-enforcing range borrows, whose coexistence is licensed by comptime evidence the *checker* consumes, over a heapless value-tree semantics.

And the concession that belongs in the same breath, because it is the one a reader will reach for: **Rust 1.86 already ships this API surface.** `get_disjoint_mut` takes `Range` indices, returns `Result<[&mut _; N], GetDisjointMutError>`, and gives you exactly the coexisting disjoint mutable subslices this design is about. It checks the disjointness **at runtime** and can fail. So DLLBC is not inventing a capability; it is moving an existing capability's check from run time to compile time, and deleting the failure mode. That is a smaller claim than "new expressive power" and it is the honest one — but it is not a small claim, because *why* Rust must check at runtime is that it has no comptime fragment to pay a proof from, and having one is the entire premise of this calculus.

---

## ¶1. The `Array` former

### 1.1 The type, and its values

```
inductive-free basis addition:

    Array : Nat → Type₀ → Type₀
```

`Array n T` is the type of exactly `n` element slots of type `T`, laid out flat. `n` is a **comptime index** in §7.1's sense — unrestricted, ⇝-evaluated, erased — and it is the *only* place a length ever lives. There is no `alen` recursion over a value: the length of an array is read off its type, never computed from its contents. (Half the M22 lemma library exists to transport lengths across mutations. With the obligation type of a borrow fixed at `Array n T ↝ Array n T`, length preservation is a *typing* fact and those lemmas evaporate. ¶6 counts the survivors.)

An array **value** in Ω is a sequence of **segments**:

```
    Arr⟨ c₁ ▷ b₁ , … , c_k ▷ b_k ⟩        with  c₁ + … + c_k = n

    segment body b ::=  [v₁ … v_c]        an owned run of c element values
                     |  σ                  an opaque run, sctx σ = Array c T
                     |  neutral            any pure value at Array c T (an arrCat spine)
                     |  loanₘ ℓ            the run is on loan to ℓ
                     |  ⊥                  the run has been moved out (a hole)
```

The first three are **owned** bodies and are what the carve rule of ¶3 is defined on; the last two are the ownership machinery, unchanged from §0's inventory.

The one system that has the same idea — a *takeover marker living inside the aggregate's own typed value* — is RefinedRust (PLDI'24), and it is worth naming because it is the limit case this design generalizes. In its `Vec::get_unchecked_mut` case study, borrowing element `i` out of an `arrayₙ T` produces an array snapshot with the borrowed slot replaced by a prophecy variable `*γᵢ` (via `yoinked` and `blocked'κ`), recombined when the lifetime ends. That is `Arr⟨…, 1 ▷ loanₘ ℓ, …⟩` in different notation: the aggregate stays whole, and the hole is *in it*, not described beside it.

The limit is sharper than "one element at a time," and it is what makes ¶3 a generalization rather than a re-run: **`blocked` applies to the whole array**, so a second borrow at `j ≠ i` is *not typable at all*. RefinedRust can put one hole in an array; it cannot put two. Everything ¶3.4 is about begins one step past where RefinedRust stops — and the side conditions there go to Coq tactics, not to a checker premise.

Each segment carries its own **extent** `c` — a comptime `Nat` value sitting in the tree. Canonical form is a single segment; a fresh array from a literal is `Arr⟨n ▷ [v₁ … vₙ]⟩` and a seeded argument's payload is `Arr⟨n ▷ σ⟩` (which the traces below abbreviate to plain `σ` when no carve has happened, since the two are the same state).

Two normalizations, both lazy in §2's sense — performed when a rule's premise demands them, never eagerly:

* **Merge**: two adjacent segments with owned bodies collapse into one, of the summed extent, whose body is their concatenation. `Arr⟨1 ▷ [3], 2 ▷ [7,2]⟩ ⇒ Arr⟨3 ▷ [3,7,2]⟩`; two adjacent σ's give `Arr⟨add c₁ c₂ ▷ arrCat σ₁ σ₂⟩` — there is no *name* for their concatenation, but there is a term for it (¶1.3), which is all merge needs.
* **Drop-empty**: a segment of extent `Z` is deleted.

Merging is what makes the *carve history* invisible once the loans are gone: an array that has been split and rejoined is the same value as one that never was, so `canonicalize` still decides Ω-equality and the golden-trace test suite survives (¶8 revisits this — it is the property a binary-concatenation representation would have cost us).

### 1.2 Why the basis, and not §7's scheme

`Array` does **not** arrive as an `inductive` declaration. Two reasons, both about the value representation rather than the type.

The first is the whole point of the exercise. Every CIC-scheme inductive with a length index is right-nested — `VCons : Π n → T → Vec T n → Vec T (S n)` builds a spine, and a spine's prefixes and middles are not subterms. That is precisely the defect that forces M22's range indices. A former whose values are *flat runs* is not expressible in the scheme, so it goes in the basis, alongside `Id` (§10) — the v0 basis's other genuinely non-schematic member.

The second is the mechanization's existing shape: `Vec` lives in the calculus only as its recursive-family encoding via large elimination (§4.2's note), which computes `Vec T (S n) = T × Vec T n`. Encoding `Array` the same way would produce nested pairs — the spine again, with extra steps.

The cost is honest and belongs in the ledger (¶8): the basis grows by one type former, one constructor family, and one computing constant.

### 1.3 The two views: cons for lemmas, `arrCat` for borrows

An array admits two eliminations, and the design leans on both.

**The cons view** is the recursor, and it exists so that the pure library over arrays can be written exactly like the pure library over lists:

```
    arrRec : Π (T : Type₀) (P : Π (n : Nat) → Array n T → Type₀)
           → P Z (Arr⟨⟩)
           → (Π (n : Nat) (x : T) (xs : Array n T) → P n xs → P (S n) (acons x xs))
           → Π (n : Nat) (a : Array n T) → P n a
```

where `acons x xs` is the array whose first slot is `x`. Every lemma in the quicksort library — `count`, `Sorted`, `Bound`, the order stack — transfers to arrays by replacing `listRec` with `arrRec` and `Cons` with `acons`. Nothing about the migration requires re-deriving that mathematics (¶6).

**The split view** is the constant

```
    arrCat : Π (T : Type₀) (m k : Nat) → Array m T → Array k T → Array (add m k) T
```

which *computes*: `arrCat (Arr⟨…⟩) (Arr⟨…⟩)` reduces to the segment-list concatenation, and `arrCat` applied to two σ's is a legitimate stuck neutral. This is the comptime shadow of the segment structure — and the division is exactly §3.2's knowledge/state line:

> The segment list is **state**. It lives in Ω, it records who currently has what, it is rearranged by carves and ends. The `arrCat` neutral is **knowledge**. It lives in types and snapshots, it records what the value *is*, and it never mentions a marker or a hole.

⇝ on an array value is the bridge: it folds the segment list into an `arrCat` spine, and is *stuck* — exactly as §5.2 says of any suspended borrow — if any segment body is a marker or a hole. A suspended array has no snapshot; only a collapsed one does.

The bridge lemma between the two views is the semantic content of the whole design and should be stated once, in the library, where a mechanization can cite it:

```
    arrCat_take_drop : Π (T) (n k : Nat) (a : Array n T) → Le k n
                     → Id (Array n T) a (arrCat (aTake k a) (aDrop k a))
```

A carve is sound *because* this holds. A soundness proof that shows carve preserves the ⇝-snapshot has shown exactly this and nothing more (¶8).

### 1.4 `ctorSig`, exhaustiveness, and the absence of match

The constructor of `Array n T` is the literal `Arr`, whose field telescope for a *concrete* `n` is `T` repeated `n` times; for a symbolic `n` there is no constructor signature, and correctly so — one cannot write an array literal of unknown length. `typeCtors (Array n T)` is therefore `some ["Arr"]` only at concrete `n`, and `none` otherwise.

Which raises the question of `match`, and the answer is a small surprise: **arrays are never matched.** §3's rule that match is the only eliminator was a statement about *inductive* data, where the constructor tag carries information. An array has one constructor and no tag; the information in an array is positional, and positions are reached by the place grammar of ¶2, not by patterns. The elimination an array needs — "give me the sub-run at `[lo, lo+cnt)`" — is the carve, which is a reorganization, not a branch. There is nothing for a match to do, no exhaustiveness obligation to discharge, and no join to pay for. That is a simplification, not a gap; but it is a genuine departure from §3's framing and belongs in ¶8's ledger as such.

---

## ¶2. Places over arrays

### 2.1 The path grammar

§1.1's positional restriction — "the ⇐ rules are only *defined* on the shapes a location can take, a variable under zero or more peels" — generalizes. A place is a variable under a **path**, and a path is a sequence of steps:

```
    step ::=  *              peel a borrow            (§2)
           |  [t]            index step, t : Nat      (new)
           |  [t ; t′]       range step               (new)

    place ::= x  step*
```

Surface precedence: index and range steps bind tighter than the peel, so a reborrow of a range through a borrow is written `&mut (*v)[lo ; cnt]`, and `*v[i]` would mean `*(v[i])` (peel the borrow *stored at* slot `i`) — which is also meaningful, and is how an `Array n (&mut T)` is reached.

Two conventions, both argued from the M22 diary:

* **Offset and count, not lower and upper.** `a[lo ; cnt]` has type `Array cnt T`, read straight off the syntax with no arithmetic. The Rust-shaped `a[lo .. hi]` is sugar for `a[lo ; sub hi lo]` plus an obligation `Le lo hi`, and is *discouraged*: it reintroduces the subtraction that the milestone's pain diary already identified as a recurring tax (the right-segment reindex needed a lemma-guarded `sub`). Every rule below is stated in offset-and-count and never produces a `sub`.
* **`a[i]` is not `a[i ; 1]`.** They carve identically, but the range place's payload is an `Array 1 T` while the index place's payload is the element itself, of type `T`. Keeping both spares every element access an `Array 1 T ≅ T` coercion.

### 2.2 The arrow table, extended

The new steps are arrow-generic, exactly as `*` is (§1.3's table):

| construct | ⇒ | ⇐ | ⇝ | ⇜ | note |
|---|---|---|---|---|---|
| `t[i]` | ✓ | ✓ | ✓ | ✓ | ⇒ moves the element out (a hole in the slot), or copies it under §2.1's index-kind refinement; ⇐ fills the slot; ⇝ projects `aget i` of the snapshot; ⇜ refines the element's σ |
| `t[lo ; cnt]` | ✓ | ✓ | ✓ | ✓ | ⇒ moves the whole run out, leaving a hole of extent `cnt`; ⇐ fills a run; ⇝ projects `aslice lo cnt`; ⇜ refines |
| `&mut t[…]` | ✓ | ✗ | ✗ | ✗ | mints a range (or element) loan, after a carve |

Each of the four columns behaves the way the corresponding column behaves at `*`, which is the regularity §1.3 asks the reader to notice. In particular the ⇒/⇐ pair at a range place is the take-and-refill idiom of §2.4 generalized from "the payload of a borrow" to "a run of an array": between the take and the refill, the array holds a hole of known extent, no rule reads it, and the refill is its one legal successor. That is how a rotation or a memmove is written without a copy.

### 2.3 `get` and `set` are not primitives

They are the two arrows at the index place:

```rust
let x = a[i];        // ⇒ at an index place: read the element
a[i] := v;           // ⇐ at an index place: write the element
let e = &mut a[i];   // &mut at an index place: an element cursor
```

`get` is a ⇒-read (a move for data, a copy for index-kind values by §2.1); `set` is a ⇐-fill (with §2.3's drop forced first if the slot is live); the cursor is an ordinary borrow. No kernel primitive is added for any of them, and the current `nth`/`nth2`/`set` library — 26 lines of recursive cursor plus a pure `set` model — is *deleted*, not ported. §3's "field access needs no other mechanism" now reads the same way about element access.

---

## ¶3. Carve — the proof-licensed reorganization

This is the design's one new rule, and the research object. Everything before it is representation; everything after it is consequence.

### 3.1 Extent trees, and what disjointness means

At any moment, an array node's segment list induces an **extent map**: a list of triples `(offset, count, status)` with `status ∈ {owned, loaned ℓ, hole}`, offsets running consecutively from the node's base. `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩` induces `[(0,1,owned), (1,2,loaned ℓ)]`.

The extent map is *the* aliasing invariant, and it is maintained by construction rather than checked: segments partition the array, so **no two loans of one array can overlap, ever, because two segments cannot overlap.** There is no disjointness *test* anywhere in the checker. There is only the question of whether a requested range can be *made* into a segment, which is what carve answers.

That division is worth stating flatly, because it is what makes the design cheap:

> The tree does the aliasing. The proofs do the arithmetic.

**This generalizes the in-repo prior art exactly.** The `aeneas/` mechanization decides place disjointness *syntactically*: `PathToSubtree.v` defines a value path as a `list nat` and proves a completeness trichotomy — any two paths are `Eq`, one is a `StrictPrefix` of the other, or they are `Disj`, where

```
    vdisj p q  :=  ∃ r p′ q′ i j.  i ≠ j  ∧  p = r ++ i :: p′  ∧  q = r ++ j :: q′
```

(`PathToSubtree.v:66-67`, completeness at `:120-140`). Two places diverge at some node, and there the disjointness question is settled by a *decidable* `i ≠ j` on constructor-child indices. That is precisely the special case this design extends: the carve's obligation replaces `i ≠ j` on two child indices with `hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁` on two child *ranges*, and replaces decidable inequality with a program-supplied `Le` derivation. **Aeneas's disjointness is structural and decidable; ours is structural and propositional.** The trichotomy itself survives unchanged — segments of one array node are pairwise `Disj` by construction, which is why ¶3.1's "no disjointness test" claim is not a cheat.

### 3.2 The rule

```
                    Ω(p) = an array node of type Array n T
                    the extent map has an OWNED leaf L at (b, m)                     (1)
                    e ⊢ Le b lo  ×  Le (add lo cnt) (add b m)                        (2)
                    the decomposition transitions on lo and on m succeed             (3)
    ─────────────────────────────────────────────────────────────────────────────  CARVE
       L : Array m T  ↦  ⟨ lo′ ▷ L₁ , cnt ▷ L₂ , rest ▷ L₃ ⟩

              where   lo ≡ add b lo′        and       m ≡ add lo′ (add cnt rest)
              are the equations premise (3) solved — not differences it computed.
```

Premise by premise.

**(1) Leaf selection.** Scan the extent map for an owned leaf containing the requested range. A leaf that is loaned or holed is not a candidate — which is how overlapping requests are rejected, structurally, with no arithmetic at all (¶3.5). When offsets are symbolic the scan cannot decide containment by computation; premise (2) decides it instead, and the *evidence's type is the selector* — see below.

**(2) The containment obligation.** Two `Le`s. In the overwhelmingly common case the leaf is the whole array (`b = Z`, `m = n`), `Le Z lo` is `⊤` definitionally, and the obligation collapses to the single

```
    Le (add lo cnt) n
```

which is, character for character, the bound the M22 quicksort already threads through every call as `hbnd`. The evidence `e` is a comptime term, ⇝-read and checked by `hasType` against the obligation type — the same machinery §5.3 uses for any dependent argument. Three supply routes, in the order the checker tries them:

1. **Conversion alone.** When `lo`, `cnt`, `n` are concrete, `Le (add lo cnt) n` normalizes to `⊤` (Std's `Le` is a large elimination), and `⋆` inhabits it. The site needs no annotation. Every literal-indexed array access is free.
2. **A named proof at the site.** `&mut a[lo ; cnt | h]`, where `h` is any term of the obligation type — typically a telescope parameter. This is the symbolic case and it is where the borrow checker literally consumes dependent evidence.
3. **Nothing else.** There is no inference, no arithmetic decision procedure, no `omega`. A range whose bound is neither computable nor cited is rejected, with an error naming the obligation. That is the stuckness discipline of §2.3 applied to a new rule, and it keeps the checker a symbolic interpreter rather than a solver.

When several leaves are candidates (symbolic offsets, so the scan cannot narrow), the checker forms each candidate's obligation type and checks `e` against each; the first that types selects the leaf. This is deterministic without a tie-break rule, because leaves are disjoint: a term of type `Le b₁ lo × Le (add lo cnt) (add b₁ m₁)` cannot also inhabit a disjoint leaf's obligation unless `cnt = Z`, and the empty carve is a no-op either way.

**(3) The decomposition transitions.** This is the subtle premise, and the one that pays for itself.

Naively, the three pieces have extents `sub lo b`, `cnt`, and `sub (add b m) (add lo cnt)` — two subtractions, and every subsequent type-level fact about the carved tree drags them along. Instead, observe what `Le a b` *means* when `Le` is DLLBC's computing predicate: it is precisely the assertion that `b` decomposes as `a` plus something. So make the carve perform the decomposition rather than the subtraction, using one library lemma:

```
    le_split : Π (a b : Nat) → Le a b → Σ (d : Nat). Id Nat b (add a d)
```

(by double `natRec`, in the shape M15's surface authors comfortably). The carve applies it **twice**, once to each component of the obligation, and the two `Le`s of premise (2) turn out to be exactly the two numbers the rule needs:

* `le_split b lo (fst e)` yields `lo′` with `lo ≡ add b lo′` — **the leaf-relative offset**, which is why the rule never subtracts a base;
* `le_split (add lo cnt) (add b m) (snd e)` yields `rest` with `add b m ≡ add (add lo cnt) rest`, which with the first equation and `add_cancel_l` (one more library lemma, and the only new arithmetic this design asks for — it follows from `natRec` plus the S-injectivity M10 already derives) gives `m ≡ add lo′ (add cnt rest)` — **the residue**.

Two mechanization points, because both are places a reader will reasonably expect trouble and find none. First: the checker **unpacks** each `le_split` result itself, minting a fresh σ for the witness and a fresh hypothesis for the equation, exactly as a symbolic match on a Σ does. It does *not* need §9's missing comptime Σ-eliminator, because no program term ever projects these — they are machine-internal. (Task M23-i has since landed `sigmaRec` anyway, so the point is moot in the other direction too.) Second: the witness is introduced as a *symbolic* `Nat`, never computed; if the checker ever evaluated it, it would be evaluating `sub`, and the whole premise would be pointless.

Each equation is then discharged by the §10 refl-match **solution transition** — the exact machinery M10 built, used unchanged. Two outcomes, and they are M10's two outcomes:

* The equation's right-hand side is **flex** — the leaf's extent `m` is a bare σ, which is the case whenever the length came from a telescope parameter, i.e. always in the programs this is for. The solution transition refines `σ_m := add lo′ (add cnt rest)` everywhere, with the occurs check as usual. From that moment the decomposition holds *definitionally*, and every extent in the carved tree is a **given**, never a computed difference. No `sub` is produced anywhere, by this rule or by anything downstream of it.
* It is **rigid** — a compound neutral like `add σₐ σ_b`, or a concrete numeral. Concrete is fine (both sides compute, and the transition is a no-op). A compound neutral is stuck, and the carve is rejected with an error saying so. The remedy is the one the north star already uses: take the length as a parameter. This is a real restriction on what signatures are carvable and belongs in ¶8.

A note for the mechanizer, since it is where a plausible implementation would go wrong: refining `σ_m` is a refinement of a **length index**, not of a value snapshot, and it must go through `refineSym` like any other — reaching Ω, `sctx`, obligations, group owed types, `retTyVal`, `selfBack`, and **`selfRec`**, per the M10 "refinement reaches all σ-bearing state" invariant.

That last member is why this deserves more than a passing mention. `St.selfRec` is the recursion guard's tracked decreasing snapshot (§8), and it joined `refineSym`'s target list only recently. A carve whose index refinement reached every component *except* that one would not fail loudly — it would silently corrupt the termination guard for **any function recursing on an array**, which is to say for the entire class of program this design exists to serve. The guard compares the actual at the declared decreasing position against a snapshot; leave that snapshot un-refined while the length index moves underneath it and the comparison is being made against a value that no longer exists.

What keeps this a single invariant rather than a per-feature audit is §9's swept-state principle: *any checker component that must observe a value across a refinement has to live in the σ-bearing state `refineSym` sweeps.* The carve's index refinement is that principle's fifth independent consumer, after obligations, instantiated call types, `retTyVal`/`selfBack`, and the recursion guard. The practical form is worth stating flatly for whoever implements: **`refineSym`'s target list is the checklist** — not a list to reason about case by case, but the one place to look, and the one place a new `St` field must be added. It satisfies §3.2's knowledge/state assertion trivially (`add lo′ (add cnt rest)` is marker-free), which is worth *checking* rather than assuming: this is the first refinement in the calculus fired by an **ownership** operation rather than by a match, and the invariant's whole point is that ownership operations must not smuggle state into σ's. They do not here — the substituted term is arithmetic, and it is true of the value timelessly.

**The effect.** `L`'s segment is replaced by three, with the extents premise (3) produced: `lo′`, `cnt`, `rest`. The bodies follow the body of `L`:

* `L = [v₁ … v_m]` (an owned literal run): split the run positionally.
* `L = σ`: refine `σ := arrCat σ₁ (arrCat σ₂ σ₃)` with `σ₁ : Array lo′ T`, `σ₂ : Array cnt T`, `σ₃ : Array rest T` fresh — again ordinary ⇜, again marker-free, again knowledge (the array *is* the concatenation of its parts, at entry and forever).

Degenerate carves are no-ops: when the request coincides with the leaf, no split and no refinement happen at all. This matters for `split_at_mut` (¶5), whose second borrow is always degenerate.

**The obligation layer: take Low\*'s, verbatim.** Premise (2) needs a small library of interval facts, and there is no reason to invent one. `LowStar.Monotonic.Buffer` has been carrying HACL\* — a production cryptographic library — on exactly four lemmas about `gsub`, and they should be transcribed rather than rediscovered. In DLLBC spelling, over ranges `(lo, cnt)` of one array:

```
    range_disjoint   : Le (add lo₁ cnt₁) lo₂  ⊎  Le (add lo₂ cnt₂) lo₁  →  Disj (lo₁,cnt₁) (lo₂,cnt₂)
    range_empty      : Disj (lo₁, Z) (lo₂, cnt₂)                          -- a zero-length range is disjoint from everything
    range_includes   : Le lo₁ lo₂ → Le (add lo₂ cnt₂) (add lo₁ cnt₁)     -- the dual order: containment
                     → Incl (lo₁,cnt₁) (lo₂,cnt₂)
    carve_carve      : (a[lo₁ ; cnt₁])[lo₂ ; cnt₂]  ≡  a[add lo₁ lo₂ ; cnt₂]   -- sub-of-sub collapses
```

`range_disjoint` is `loc_disjoint_gsub_buffer` (whose F\* hypothesis is literally `i₁+len₁ ≤ i₂ ∨ i₂+len₂ ≤ i₁`, plus in-bounds); `range_empty` is the `len = 0` degenerate case baked into `ubuffer_disjoint'`; `range_includes` is `loc_includes_gsub_buffer_l`; `carve_carve` is `gsub_gsub`, which in F\* carries an `SMTPat` so it fires automatically. The fourth is the one a DLLBC implementer will underestimate: **sub-of-sub collapse is what makes nested carving cheap**, because without it every sub-slice of a sub-slice accumulates a chain of offsets that no conversion will see through. Here it should hold *definitionally* — `carve_carve` is a consequence of `add`-associativity on the extents premise (3) already put in normal form — and if it does not, that is a signal premise (3) is wrong rather than that a lemma is missing.

The argument for the wholesale transcription is not elegance, it is evidence: this is the only interval API in the survey that has been driven at production scale, and the shape of what is *missing* from a first attempt is exactly what a decade of HACL\* proofs would have found. (What does **not** transfer is Low\*'s framing calculus — the forty-odd `modifies_*` lemmas that dominate its interface. That machinery exists to reason about a heap; ¶3.6 is the argument that a heapless ownership tree does not need it.)

### 3.3 The borrow, and the lifecycle

With the carve done, `&mut a[lo ; cnt]` is *ordinary §2.2*: the middle segment's body moves into the borrow, `loanₘ ℓ` parks in its place, and the extent stays on the segment.

```rust
let a = [3, 1, 2];
// Ω = a ↦ Arr⟨3 ▷ [3,1,2]⟩
let m = &mut a[1 ; 2];
// carve: leaf (0,3) owned; obligation Le (add 1 2) 3 ⇝ ⊤, discharged by ⋆
//        residue transition: n = 3 concrete, both sides compute — nothing refined
// Ω = a ↦ Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩, m ↦ borrowₘ ℓ (Arr⟨2 ▷ [1,2]⟩)
(*m)[0] := 7;
// an index place under a peel: ⇐-fill, drop of the displaced 1 first (a Nat — discard)
// Ω = a ↦ Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩, m ↦ borrowₘ ℓ (Arr⟨2 ▷ [7,2]⟩)
let x = a[0];
// the read demands a's node; a loan marker is in owned position, so §2.2 forces
// End-Mut ℓ first: the payload plugs into the marker, m dies
// Ω = a ↦ Arr⟨1 ▷ [3], 2 ▷ [7,2]⟩, m ↦ ⊥
// merge (lazy, forced by the index-place read wanting a run): Arr⟨3 ▷ [3,7,2]⟩
// then the read itself: Nat is index-kind, so §2.1's copy-on-read applies
// Ω = a ↦ Arr⟨3 ▷ [3,7,2]⟩, m ↦ ⊥, x ↦ 3
```

Every step after the carve is a rule that already exists. End-Mut is End-Mut — a ⇐-fill at the marker plus the kill (§2.2). The forcing is §2.2's owned-position rule verbatim: a marker inside a segment body is in owned position of `a`'s value, so a demand for `a` ends it, innermost first. Drop (§2.3) needs no new case: an array node being displaced is a value with markers in owned position, and drop's total procedure ends them and discards the rest.

**Rejoin is merge.** There is no rejoin rule. When the last marker under an array node is gone, the merge normalization collapses the segments, and the array is a run again — indistinguishable from one that was never carved. That is the property the segment representation was chosen for (¶1.1).

*A mechanization note on when merge fires, which is later than this section's traces suggest.* The traces above force merge at an owner demand or at the audit, and it would be natural to implement it as though those were the only triggers. They are not, and the gap has already been closed twice in the list world: two demand-ending sites now fire on **parked** loans — M22-a's `&mut`-on-parked, and M23-ii's `collapseCDerefs` on a *comptime deref through* one. Both will fire on carved segments the moment a caller reads across the array, and both are correct and necessary: they are what makes a recovered `Arr⟨…⟩` readable at all. The consequence for an implementer is that **merge must be robust to being triggered mid-body by a comptime read**, not only by owner demand or by the boundary. Anything that assumes segments are only ever re-merged at a collapse point will be wrong on the first `Sorted (*v)` written between two carves.

**The split/join shape is Verus's, deliberately.** Verus's `PointsToRaw` — its tracked ghost permission over raw memory — is the closest existing thing to what carve does, and it is worth copying the shape rather than improvising one:

```
    split (tracked self, range : Set<int>) -> (res : (Self, Self))
      requires  range.subset_of(self.dom())
      ensures   res.0.dom() == range,  res.1.dom() == self.dom().difference(range)

    join  (tracked self, tracked other) -> (joined : Self)
      ensures   joined.dom() == self.dom() + other.dom()
```

Three features to steal, and one to decline. **Steal**: split is *the only way* to obtain two capabilities, so disjointness is free by construction rather than checked — which is ¶3.1's whole argument, already validated in another system. **Steal**: the residue is an explicit output of the split, not an implicit remainder — carve's third segment is `self.dom().difference(range)`. **Steal**: join's postcondition is the union, i.e. rejoin is total and needs no side condition — which is why ¶3.3 has no rejoin rule. **Decline**: Verus's domain is an arbitrary `Set<int>`, so a permission may be split along a non-contiguous set. That is more general than a segment list can represent, and buying the generality would cost the extent map its interval structure and the design its whole cheapness (¶8.4 keeps non-contiguous ranges out of scope for exactly this reason).

The one real difference is placement, and it is the difference this design exists for: Verus's obligation `range.subset_of(self.dom())` is discharged by the SMT solver in *ghost proof code the user writes around raw pointers*, and never touches the type of a surface `&mut`. Carve's obligation is discharged in the checker, at the borrow, and the thing being licensed is a surface borrow.

### 3.4 Two disjoint ranges, symbolically

The case the whole design exists for. Inside a body, with a symbolic length:

```rust
fn halves (a : &mut Array n Nat, k : Nat, h : Le k n) = {
  // Ω = a ↦ borrowₘ ℓ₀ (σ : Array σₙ Nat), k ↦ (σₖ : Nat), h ↦ (σₕ : Le σₖ σₙ)
  // (n is a telescope parameter, so its snapshot is a bare σₙ — flex)

  let l = &mut (*a)[Z ; k];
  // carve at (Z, σₖ): leaf (0, n) owned
  //   obligation:  Le Z Z × Le (add Z σₖ) σₙ  ≡  ⊤ × Le σₖ σₙ  — discharged by h ✓
  //   offset:      le_split on the first component ⇒ lo′ = Z (nothing to do)
  //   residue:     le_split on the second ⇒ rest, with Id σₙ (add σₖ rest);
  //                σₙ is flex ⇒ the refl-match solution transition refines
  //                σₙ := add σₖ rest, EVERYWHERE (Ω, sctx, obligations, retTyVal…)
  //   split of σ:  ⇜ refines σ := arrCat σ_l σ_r  (σ_l : Array σₖ, σ_r : Array rest)
  // Ω = a ↦ borrowₘ ℓ₀ (Arr⟨σₖ ▷ loanₘ ℓ₁, rest ▷ σ_r⟩)      [suspended]
  //     l ↦ borrowₘ ℓ₁ (σ_l : Array σₖ Nat)

  let r = &mut (*a)[k ; rest];
  // carve at (σₖ, rest): the extent scan finds the OWNED leaf at exactly (σₖ, rest)
  //   obligation:  Le σₖ σₖ × Le (add σₖ rest) (add σₖ rest)  — both by le_refl, ⋆
  //   DEGENERATE: request = leaf, so no split and NO refinement fire
  // Ω = a ↦ borrowₘ ℓ₀ (Arr⟨σₖ ▷ loanₘ ℓ₁, rest ▷ loanₘ ℓ₂⟩)  [suspended]
  //     l ↦ borrowₘ ℓ₁ (σ_l : Array σₖ Nat)
  //     r ↦ borrowₘ ℓ₂ (σ_r : Array rest Nat)

  // …l and r are now two live, independent, contract-free mutable borrows…

  // forced at the audit (§5.4): collapse a's payload — End-Mut ℓ₁, then ℓ₂
  // Ω = a ↦ borrowₘ ℓ₀ (Arr⟨σₖ ▷ σ_l′, rest ▷ σ_r′⟩)
  // ⇝ of that payload: arrCat σ_l′ σ_r′ : Array (add σₖ rest) Nat ≡ Array σₙ Nat ✓
}
```

Read the two carves against each other, because the contrast is the design. The **first** does everything: it consumes the proof, refines the length index, and splits the value. The **second** does nothing — its obligation is `le_refl` twice, its leaf is exactly its request, and no refinement fires. That asymmetry is not an accident of this example; it is the general shape of an exhaustive split, and it is why `split_at_mut` costs one proof rather than two (¶5).

Read also what the audit sees. The obligation type for `a` is `Array n Nat`; the collapsed payload's snapshot is `arrCat σ_l′ σ_r′` at `Array (add σₖ rest) Nat`; and these convert **definitionally**, because the residue transition refined `σₙ := add σₖ rest` at the carve. Had the carve computed `rest := sub n k` instead, this final conversion would have needed `add k (sub n k) ≡ n`, which is not definitional and would have required a cited lemma at every audit of every array-mutating function in the program. That is the entire argument for premise (3), and it is worth the machinery.

### 3.5 What is rejected, and how

Four rejections, each falling out of a premise rather than a check:

* **Overlap.** `let p = &mut a[0 ; 3]; let q = &mut a[2 ; 3];` — after the first carve the extent map is `[(0,3,loaned ℓ₁), (3,rest,owned)]`, and no *owned* leaf contains `[2,5)`. Premise (1) fails. No arithmetic was performed and no proof could have helped: the answer is that the ownership is elsewhere, and the error should say exactly that (`range [2,5) meets loan ℓ₁ at [0,3)`).
* **Out of range.** `&mut a[lo ; cnt]` with `add lo cnt > n` — premise (2) has no inhabitant, and none can be supplied, because `Le (add lo cnt) n` computes to `⊥`.
* **Unproved bound.** The same obligation, symbolic, with no evidence cited — premise (2) fails for want of a term. This is the *interesting* rejection: the program is not wrong, it is unjustified. The fix is to thread the bound, which is what the north star's `hbnd` already is.
* **Rigid length.** Premise (3) is stuck. Reject, with the remedy in the message.

And one non-rejection worth naming, because it is the one Rust cannot express: **an interior range and a suffix range of one array, taken in either order, both live, both writable.** That is `split_at_mut`'s generalization, and here it is not a library function with an `unsafe` interior but two applications of one rule.

**A note on what this replaces.** M13 recorded the finding that "two sequential `nth` calls CANNOT give two live cursors; one call returning the pair is the answer to disjointness," and built `nth2` accordingly. That finding was about *calls*: each `nth` consumes the whole borrow into a group, so the second has nothing left to take. It was never about disjointness as such — the two cursors `nth2` returns are disjoint *structurally*, because they land in different `Cons` cells, and the checker knows this without being told. What `nth2`'s signature carries is

```rust
nth2 (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j, p2 : Le (S j) (len *v)) → …
```

— and `pij : Le (S i) j` together with `p2 : Le (S j) (len *v)` is, on the nose, the containment obligation the carve rule demands of two element ranges at `i` and `j`. The evidence has been threaded through every swap site since M13, discharging a different job: making the recursion's `botElim` branches type-check. Range places take the same terms and give them their real job, and the "one call returning a pair" workaround dissolves, because a *place* borrow consumes nothing and two of them need no call at all.

### 3.6 Interaction with §6 loan groups

A call that receives two range borrows of one array captures two loans whose markers sit in one owner's value tree. Nothing in §6.1 needs changing: the group ties captured loans to issued borrows, issued borrows end first, then the group ends and each captured loan receives its release. Marker positions are irrelevant to the discipline — the group does not care that ℓ₁ and ℓ₂ happen to be siblings.

One consequence is a genuine **precision gain**, and it is the mechanical form of ¶0's thesis. Compare, at a caller:

```rust
// TODAY (whole borrow + indices):
quicksort(&mut *v, f2, lo, i, bl);
// the group captures ℓ(*v); at the end the WHOLE payload becomes one fresh σ′.
// Everything the caller knew about the untouched part of v is gone; the callee's
// return type must therefore describe the whole list, range-indexed.

// WITH RANGE PLACES:
quicksort(&mut (*v)[lo ; i | bl]);
// the group captures only the middle segment's loan; at the end only THAT
// segment's body becomes a fresh σ′. Ω = … Arr⟨lo ▷ σₚ, i ▷ σ′, rest ▷ σₛ⟩ …
// σₚ and σₛ are the SAME σ's as before the call. The frame is not described.
// It is simply still there.
```

The §5.4 exit-snapshot convention does the rest: the call mints one σ shared between the loan's release and the returned evidence's subject, so `σ′` arrives already carrying the callee's postcondition. The caller therefore holds, definitionally, `arrCat σₚ (arrCat σ′ σₛ)` together with `Sorted σ′` and `Π n. count n σ′ = count n σ_old` — and gluing those into a statement about the whole is a pure lemma about `arrCat`, with no range indices in sight.

**This needs no new caller-side machinery, which was checked rather than hoped.** The load-bearing step above is that a *segment's* loan can be captured by a call without the parent array riding along — and that is not a new capability, it is exactly what borrow-mode match field loans already do. `processArgs` captures per-argument-borrow loans and nothing in it walks to a parent or a sibling; the property is exercised on every recursive call of `nthS`, `partScan` and `twoRec`, with the executing differential agreeing. The §5.4 pinning half transfers on the same terms: `shareCaller` in the S19 suite already tests, for lists, precisely the property the array version needs — a caller forwarding a callee's evidence about the callee's *own* exit, and checking only because of the σ-sharing. So ¶3.6's claim rests on machinery that exists, is tested, and is agnostic to whether the loan sits at a `Cons` field or at an array segment.

The full group lifecycle, traced, with a two-slice callee (`fn merge_into (l : &mut Array p Nat, r : &mut Array q Nat) → Unit`):

```rust
// Ω = a ↦ Arr⟨σₚ ▷ σ_l, σ_q ▷ σ_r⟩            (already carved, both owned)
let l = &mut a[Z    ; p];
let r = &mut a[p    ; q];
// two degenerate carves — the leaves ARE the requests, both obligations by le_refl
// Ω = a ↦ Arr⟨σₚ ▷ loanₘ ℓ₁, σ_q ▷ loanₘ ℓ₂⟩,
//     l ↦ borrowₘ ℓ₁ σ_l, r ↦ borrowₘ ℓ₂ σ_r
merge_into(l, r);
// §5.3: both borrows ⇒-consumed into the call; a group is minted
// Ω = a ↦ Arr⟨σₚ ▷ loanₘ ℓ₁, σ_q ▷ loanₘ ℓ₂⟩, l ↦ ⊥, r ↦ ⊥,
//     A(ρ) { captured: ℓ₁ [owed: Array σₚ Nat], ℓ₂ [owed: Array σ_q Nat] ; issued: [] }
let z = a[0];
// the read demands a's node; ℓ₁ is in owned position ⇒ End ℓ₁ ⇒ End A(ρ):
// no issued borrows to surrender, so the group ends immediately, releasing BOTH
// captured loans at their owed types (§5.4 pins each to its callee's exit σ)
// Ω = a ↦ Arr⟨σₚ ▷ σ_l′, σ_q ▷ σ_r′⟩
// merge (forced by the index read): Arr⟨add σₚ σ_q ▷ arrCat σ_l′ σ_r′⟩
// Ω = a ↦ Arr⟨…⟩, z ↦ aget Z (arrCat σ_l′ σ_r′)
```

Two things to read off it. The group's atomic release now touches **two markers in one owner's tree**, which is new only in arity — §6.1's ordering discipline is untouched, because marker position was never part of it. And the extents `σₚ`, `σ_q` survive the whole round trip untouched: the ¶3.8 rule guarantees that a release cannot change a segment's length, so the merge always type-checks and the array's own index `add σₚ σ_q` never needs re-deriving.

The over-approximation §6.1 already flags (a group releases atomically where the concrete machine ends lazily) acquires a new instance here — several captured loans in one owner — but not a new character. Any simulation relation that reconciled the old case reconciles this one.

### 3.7 Interaction with the §5.4 audit

The audit is unchanged in structure and gains one obligation in substance.

`collapseArg` already End-Muts every loan marker in an argument borrow's payload; markers inside segment bodies are found by the same traversal (a segment is an ordinary node with the marker in a field), so §3.3's field-loan collapse and a carve's range-loan collapse are the same code path — as §2.2 promised when it generalized owned position.

What is new is that the collapsed payload is a *segment list*, and the owed type is `Array n T`. Conversion must therefore see through the fold: `⇝` of `Arr⟨c₁ ▷ b₁, …⟩` is `arrCat b₁ (arrCat b₂ …)`, `arrCat` computes on run-headed arguments, and stays neutral on σ's. The audit's conversion then succeeds definitionally precisely when the extents add up definitionally — which premise (3) arranged. This is the single place where the residue-transition decision pays out, and it pays out at every array-mutating function in the program.

The §6.2 spec/`back` machinery needs no change and, notably, needs *less use*: a declared backward spec exists to describe what flows back through a borrow that the caller cannot see. When the borrow spans a segment and the residues never left, there is less to describe. ¶6 develops this into the migration's headline.

### 3.8 The extent is not negotiable

One new well-formedness rule on the borrow type, and it is the source of the length lemmas' evaporation. §5.1's obligation is type-*changing* — `&mut (s : τ ↝ S)` permits `S ≠ τ`, and `Vec T n ↝ Vec T (S n)` is its flagship. For a borrow whose loan sits at an array **segment**, that freedom is bounded:

> If `ℓ` is a range loan at a segment of extent `c`, its obligation type `S` must be an `Array c T′` — the *same* `c`. The element type and any refinement may change; the extent may not.

The reason is arithmetic rather than moral: the parent array's own type index is `add`-composed from its segments' extents, and it is not the borrow's to alter. A `Vec`-style length change is expressed the way §5.1 already recommends for it — by moving the length *inside* the value (`Σ (n : Nat). Array n T`), where it is data, not by letting a segment's obligation renegotiate its neighbour's offsets.

The dividend is immediate and large: a function `fn f (s : &mut Array c Nat)` **cannot** change its slice's length, the audit enforces it by conversion, and no `len_f` lemma is ever written or applied. Every one of M22's length-preservation lemmas and its `le_rw_l`/`le_rw_r` transport chains is a workaround for the absence of exactly this rule.

---

## ¶4. Slices are derived, and should stay that way

A slice is a borrow of a range place. That is the whole definition, and the three things one might expect to be primitive all fall out:

**The fat pointer.** `&mut (s : Array cnt T ↝ S)` carries `cnt` as a comptime index in the type. Under erasure (§1.3's aspiration) the index is deleted from the *type* and survives as the length word of the runtime representation — the borrow erases to a base pointer, the index erases to a length, and the pair is exactly Rust's `&mut [T]`. The "fat" half of the fat pointer is not extra machinery; it is the index that was already there.

**Sub-slicing.** `&mut (*s)[lo ; cnt]` — a carve inside the slice's own payload. Slices nest without a rule.

**Runtime-length slices.** A slice whose length is not known to the caller is `Σ (c : Nat). &mut (Array c T)` — an ordinary Σ over a borrow, which §5.2 already declares well-formed ("`Σ (l : &mut List T). Fin (len *l)` is likewise well-formed"). No new type.

What a primitive slice would buy is nothing the above does not, and what it would cost is a second former with its own subtyping story against arrays. Decline. The one honest gap: **shared slices (`&[T]`) need shared borrows**, which are deferred wholesale with §10, and the design below says nothing about them beyond the observation in ¶8 that read-only sharing needs no disjointness proof at all and should be strictly easier when it arrives.

---

## ¶5. `split_at_mut`, and why it needs no trust

```rust
fn split_at_mut (a : &mut Array n T, k : Nat, h : Le k n)
    -> Σ (l : &mut (Array k T)) → &mut (Array (sub n k) T)
  = Pair( &mut (*a)[Z ; k | h] ,
          &mut (*a)[k ; rest] )
```

with the return type more honestly written after the carve has run, as `Σ (l : &mut (Array k T)) → &mut (Array rest T)` where `rest` is the residue the carve introduced — the `sub` in the signature above is the caller-facing spelling and, per ¶2.1, is sugar the callee never sees.

**Checking story**, step by step, and every step is a rule already stated:

1. The first borrow carves at `(Z, k)`. Obligation `Le Z Z × Le (add Z k) n ≡ ⊤ × Le k n`, discharged by `h`. Residue transition refines `σₙ := add k rest`.
2. The second borrow carves at `(k, rest)`. The extent scan finds the owned leaf at exactly `(k, rest)` — degenerate, no split, obligation by `le_refl`. **The second half is free.**
3. Both borrows are issued into the result, so the return is a §6.1 multi-issued group: two issued loans, one captured (`a`), exactly `nth2`'s shape (§6.1 names `nth2` "this calculus's `split_at_mut`" — the name is now literal).
4. The callee audit (§6.1's per-branch rule) exempts `a`: it is the captured owner of both field reborrows, reached by `reachesLoan` through the markers parked in its payload. The two issued payloads are audited against `Array k T` and `Array rest T`, which they hold by construction.

**Why no `unsafe`.** Rust's `split_at_mut` is raw pointers inside because both halves would be reborrows through the same place `*self`, with no distinguishing projection — and `places_conflict` classifies two runtime-indexed projections as conflicting under the borrow-checking bias (¶7). The ranges genuinely are disjoint; what fails is that no *type* records it. Rust's escape is to move ownership of `&mut self` **into** the call so that the checker sees a move and two unrelated returns rather than two reborrows, with the actual argument audited once inside an `unsafe` block.

Here the two borrows are not two borrows of one place. After the carve they are borrows of two *different segments*, which are different subterms of one value tree — `Disj` in the `PathToSubtree` trichotomy sense (¶3.1) — and the ownership machinery cannot represent them overlapping. The `Le` proof was consumed at step 1 to license the reorganization; from step 2 onward disjointness is not a claim being trusted but a shape being read. **The trust Rust localizes in an `unsafe` block is here discharged by one `Le` term at one carve** — and, unlike `get_disjoint_mut`'s runtime pairwise check, it is discharged before the program runs and cannot fail at run time.

**Caveat, stated because ¶3.6 makes it matter.** Calling `split_at_mut` is not the same as carving inline. The call mints a group, and a group is §6.2's opacity: at the group's end the caller learns only what the signature says. An *inline* pair of carves keeps everything transparent — the residues stay pinned, the sub-borrows' work is visible to the enclosing body. So the advice the calculus should give is the opposite of Rust's: **carve inline; reach for the function only when you want the abstraction boundary**, and pay §6.2's spectrum when you do.

---

## ¶6. Migration: what the M23 quicksort becomes

The exercise that makes this concrete. Today's north star, with the pieces that change marked:

```rust
fn quicksortSorted (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                    hfuel : Le cnt fuel, hbnd : Le (add lo cnt) (len *v))
  -> Σ (sortedpart : SortedR cnt lo (*v)) → (Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v)))
```

and after migration:

```rust
fn quicksort (v : &mut Array n Nat, fuel : Nat, hfuel : Le n fuel)
  -> Σ (_ : Sorted (*v)) → (Π (x : Nat) → Id Nat (count x (*v)) (count x (old *v)))
{ match fuel {
    Z => …,                              // n ≤ 0 by hfuel: the array is empty, Sorted ⋆
    S(f2) => {
      let p = partition(v);              // the pivot's index, Σ-paired with its bounds
      match p { Pair(i, hi) => {
        // a three-way carve — left half, pivot slot, right half — then two calls:
        let left  = &mut (*v)[Z    ; i    | hi];  // everything below the pivot
        let right = &mut (*v)[S(i) ; rest    ];   // everything above (degenerate leaf)
        let cl = quicksort(left,  f2, …);
        let cr = quicksort(right, f2, …);
        Pair(sorted_arrCat … cl … cr … , perm_arrCat … cl … cr …)
      } }
    }
} }
```

Note what the recursive calls' arguments are: sub-slices, with no offsets and no counts. `quicksort` sorts *its argument*, entire.

**What disappears.**

* `lo` and `cnt` — both parameters, and every occurrence of them in every predicate and lemma. The callee sorts *the whole of its argument*, because its argument is the segment.
* `hbnd : Le (add lo cnt) (len *v)` as a *precondition of a model function* — it survives, but transformed: it is now the *license for the carve* at the recursive call site, and it is consumed there rather than threaded into a pure lemma. Same term, different job.
* The range-scoped predicate family. `SortedR cnt lo l` becomes `Sorted a`. `AllLeR`/`AllGtR` become `AllLe`/`AllGt`. The bounded-Π encoding (`Π k. Le (S k) w → …`) that M22-c adopted *because* the comptime Σ-eliminator is missing was forced by the need to quantify over positions *within a range of a bigger list*; over a whole array there is no range to quantify within, and the predicates return to their direct recursive form. (The missing Σ-eliminator remains a real gap for other reasons — §9's list — but it stops distorting these definitions.)
* The permutation-survival keystone. M22-c's hardest single result — that positional `AllLeR` is not permutation-invariant, so bounds must be routed through the multiset predicates `noAbove`/`noBelow`, with off-end positions reading `Z` and the range-fits bound carried through three lemmas — exists entirely because "the range [lo, lo+cnt) of this list" is not permutation-stable when the *list* is what gets permuted. Sorting a segment permutes the segment. The keystone's problem statement does not arise.
* Every length-preservation lemma: `len_partitionRangeL`, `len_sortRangeL`, and the `le_rw_l`/`le_rw_r` transport chains built on them — roughly thirty lines of the current quicksort body, visible at `S19Partition.lean:692-714`. A borrow of type `&mut (Array n Nat ↝ Array n Nat)` *cannot* change the length; the audit enforces it; nothing needs proving.
* The right-segment reindex and its lemma-guarded subtraction (the M22-c diary's named tax). The right sub-slice is a segment with its own zero; there is no reindexing.

**What survives untouched.**

* The count-based permutation story, verbatim. `Perm s l := Π n. Id (count n s) (count n l)` is representation-agnostic; `count` over an array is `count` over its cons view; and the one lemma that replaces `count_append`/`take`/`drop` is `count_arrCat : count x (arrCat a b) = add (count x a) (count x b)`, which is the same induction.
* The order stack — `Le`, `leb`, `eqb`, `le_trans`, the reflection lemmas, `le_refl` — untouched. It is about `Nat`, not about containers.
* Fuel-structural recursion and partial correctness. Termination remains §8's business.
* **The delegation discipline — but in M23's corrected form, not M22's.** An earlier draft of this document said the leaf "still needs a back-carrying callee or the three-feature arc." That is now wrong, and by a correction this design should be glad of. M23's leaf stage refined the diagnosis M22's finding rested on: opacity is a property of borrows **issued by a call** — `buildResult` mints their payloads as fresh σ because signature-only checking cannot say what they hold — and *not* of inline mutation. A leaf that does its own cursor work through the body's own match-field borrows writes into a suspension the audit itself collapses, so its exit is a constructor tree over known snapshots, fully provable, nothing minted. Provable inline leaves are therefore a **program-level choice** — be the cursor rather than call one — and the bridging equation is an ordinary body-cited lemma. Issued-payload pinning survives only at reduced scope, for bodies that insist on calling a cursor.

  This matters here beyond bookkeeping. A range place is precisely the apparatus for *being* the cursor: `(*v)[i]` reaches an element without calling anything, so the corrected discipline and the carve rule push in the same direction. What survives untouched is the narrower true statement — evidence about a *call's* exit still comes from the callee's postcondition — and that is exactly the part ¶3.6 relies on.

**What does NOT dissolve, stated plainly because ¶0's framing invites the overclaim.** Two problems live here and only one of them goes away.

The **frame** problem dissolves, and completely rather than partially: M22's locality stratum — `nth_swapL_lt`/`_gt`, `nth_partScanRangeL_lt`/`_ge`, `nth_sortRangeL_lt`/`_ge`, the whole "positions outside the range are unchanged" layer — becomes *unnecessary*, not merely easier. Those lemmas exist to prove that something the mutation could have touched was not touched. With range places the σ's naming the untouched segments never moved, so there is nothing to prove: the statement they establish is the shape of the tree.

The **gluing** problem does not dissolve at all. A caller holding `Sorted σ′` still has to reassemble it to `Sorted (arrCat σₚ (arrCat σ′ σₛ))`, and "a pure lemma about `arrCat`" is doing quiet work in that sentence — it is the real mathematical content of quicksort's correctness and no representation choice makes it free. What the migration buys is that the lemma is the *textbook* one rather than an index-simulated one.

And this can now be checked rather than asserted, because M23 landed the List-world counterpart while this document was being written (`sorted_append_pivot`, `StdLemmas.lean:3657`):

```
    Π (a b : List Nat) (p : Nat) →
      Sorted a → Ub p a → Sorted b → Lb p b → Sorted (append a (Cons p b))
```

Set `append ↦ arrCat` and `Cons p b ↦ arrCat (asingle p) r` and it *is* the array lemma, hypothesis for hypothesis — not merely the same shape but the same statement modulo the container, with `Ub`/`Lb` already playing the roles this document called `AllLe`/`AllGt`. So the migration **inherits** that proof rather than opening a stratum. Claim exactly that and no wider: **one stratum deleted outright** (locality), **one inherited** (the pivot glue), **none invented**.

**What gets built.** The glue moves from index arithmetic to concatenation:

```
    sorted_arrCat : Π (l r : Array _ Nat) (p : Nat) →
                      Sorted l → Ub p l → Sorted r → Lb p r
                    → Sorted (arrCat l (arrCat (asingle p) r))
```

— deliberately written in `sorted_append_pivot`'s own binder order and vocabulary, since the point is that it is that lemma with the container swapped. This is the textbook quicksort correctness statement, in the textbook shape. M22-c's `glue` — a nested `leb`-elim dispatcher over three directional lemmas with a subtraction-guarded reindex — is what the same content looks like when the concatenation is simulated by indices into a larger list.

**Honest accounting of the migration's own cost.** Three things get harder, not easier:

1. The partition leaf must now produce its pivot index *together with* the two carve licenses (`Le i n` and its complement), because the recursive calls carve at exactly that index. Today the index is a plain `Nat` pinned by a Σ; tomorrow it must be Σ-paired with bounds. That is more signature, and it is the honest price of the recursion being over real segments.
2. Both sub-slices must be carved **before** either call, not one per call: the second carve needs an *owned* leaf, and after the first call the first segment is loaned to a live group. That is the shape the snippet above already has, and it is a better shape — but it is a different shape from today's sequential reborrows, and it means the pivot element sits between two live borrows as a third segment that neither call can see. (Which is correct: the pivot is in its final position and must not move. The calculus is enforcing that, for free, by the same mechanism that keeps the halves apart.)
3. The pure library gains an array layer. `arrRec`, `aget`, `aTake`/`aDrop`, `arrCat` and their lemma stack are new, even though each mirrors a list counterpart. Call it a week of the kind of work M16–M18 already showed is mechanical in the M15 surface.

---

## ¶7. Prior art, honestly

The standing instruction is to steal shamelessly and reinvent as little as possible. ¶0.1 states the conjunction that is actually new; this section is the receipts, and it corrects three things an earlier draft of this document got wrong.

The honest summary: **the carve rule is separation logic's array split with the side condition relocated from a proof-mode goal into a type-checking premise.** Low\*'s `gsub`/`loc_disjoint` supplies the arithmetic layer (adopted wholesale, ¶3.2), Verus's `PointsToRaw` supplies the split/join shape (adopted, ¶3.3), VST's `array_at lo hi` supplies the first-class-residue idea, RefinedRust supplies the marker-inside-the-aggregate representation at element granularity (¶1.1), and Aeneas supplies the path-disjointness trichotomy the rule generalizes (¶3.1). Almost nothing here is invented; the contribution is the wiring.

**Separation logic (the source).** The canonical array law is Iris's `array_app`:

```
    l ↦∗ vs   ⊣⊢   l ↦∗ take n vs   ∗   (l +ₗ n) ↦∗ drop n vs
```

where `l ↦∗{dq} vs` is *definitionally* the iterated points-to `[∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{dq} v`. Worth stating precisely, because the expectation is otherwise: HeapLang's array library has **no `array_split` and no subrange lemma at all** — the full inventory is nil/singleton/app/cons/cons_frame/update_array/pointsto_seq_array. `array_app` is what there is. Three features, and ¶3 inherits all three. It is a **bi-entailment**, so split and rejoin are one law read in two directions — which is why ¶3.3 has no rejoin rule. It is stated **at one split point**, exhaustively; an arbitrary `[lo,hi)` is obtained by `take`/`drop` rewriting plus two applications, leaving two residue assertions and manual offset arithmetic to carry. And **disjointness is not a side condition at all** — it is a theorem of pointer arithmetic, baked into the injectivity of `+ₗ` and absorbed by `∗`. ¶3.1's "the tree does the aliasing, the proofs do the arithmetic" is that division transplanted: the segment partition plays `∗`, and premise (2) plays the in-bounds obligation.

The single-cell law is the more revealing ancestor, because it is where the *residue* first goes anonymous:

```
    update_array :  l ↦∗{dq} vs  -∗  (l +ₗ off) ↦{dq} v  ∗
                    (∀ v′, (l +ₗ off) ↦{dq} v′ -∗ l ↦∗{dq} <[off:=v′]> vs)
```

"The array minus cell `off`" is never named as an assertion; it exists only as a **magic wand** — a continuation that re-absorbs an updated element. That wand is the direct ancestor of Aeneas's backward function, of §6.2's declared `back`, and of the loan marker itself. This design's departure is to *name* the residue instead (¶3.3), which is what allows two range borrows to be live at once — you cannot hold two wands over one array and still have an array.

**VST** has the arbitrary-subrange rules natively, and is the closest sep-logic shape to `&mut a[lo ; cnt]` as a *type*: `array_at sh t gfs lo hi v p` is an assertion about a subrange of one object, with `split2_array_at` (side condition `lo ≤ mid ≤ hi`), `split3seg_array_at` (three-way `[lo,ml) ∗ [ml,mr) ∗ [mr,hi)`, side condition `lo ≤ ml ≤ mr ≤ hi`) and `split3_array_at` (prefix ∗ one element ∗ suffix), at `floyd/field_at.v:685`, `:705`, `:731`. Three things to steal, and ¶3 steals all three: each is stated as an **equation**, so split and rejoin are one lemma read both ways; the side condition is **pure linear arithmetic on bounds**, which is precisely the `Le` evidence premise (2) consumes; and the residue is **explicit and two-piece**. If ¶3's segment list has a direct ancestor, `split3seg_array_at` is it — a fact worth knowing before believing the representation is novel.

What VST does *not* have is the thing ¶3.6 turns on: holding `[lo₁,hi₁)` and `[lo₂,hi₂)` while the remainder is **implicitly retained by the owner**. In VST the residues are standalone assertions that pile up in the proof context and must be threaded by hand. That is the one place this design appears to go past its ancestor, and it is exactly the position ¶9(b) flags as either the insight or the blind spot.

**RustBelt** — and this is the first correction to an earlier draft of this section — **has no array or slice types at all.** λRust's grammar is fixed-arity products and sums (`τ ::= T | bool | int | ownₙ τ | &κμ τ | Π τ⃗ | Σ τ⃗ | ∀ | μ`), and slices were not among the POPL'18 case studies. What the lifetime logic does contribute is the general principle

```
    LftL-bor-split :   &κ_full (P ∗ Q)  ⇛  &κ_full P  ∗  &κ_full Q
```

— a full borrow splits along *any* `∗`-decomposition, so composing it with `array_app` does give subrange borrows semantically. But there is no syntactic rule and no checker: the split is a manual Iris proof step, and RustHornBelt (PLDI'22) is what actually exercised it for `index_mut`/`IterMut` with prophecies for recombination. One honest detail matters for us: in RustBelt's `index_mut` narrative the un-returned residue is **dropped** (affine logic) and recovered only from the inheritance `[†κ] ⇛ ▷P` when the lifetime dies. Nobody keeps a *usable* residue live during the borrow — which is exactly what two simultaneous range borrows require, and exactly what ¶3.3's named residue provides.

**Low\*/`LowStar.Monotonic.Buffer` (the arithmetic layer, adopted wholesale).** A Low\* buffer *value* is literally the triple this design's range place denotes: `b_max_length`, `b_offset`, `b_length`. `mgsub b i len` is the ghost sub-buffer (`msub` the stateful one), with precondition `i + len ≤ length b`. The disjointness rule is

```
    loc_disjoint_gsub_buffer :
      i₁ + len₁ ≤ length b  ∧  i₂ + len₂ ≤ length b  ∧  (i₁ + len₁ ≤ i₂  ∨  i₂ + len₂ ≤ i₁)
      ⊢  loc_disjoint (loc_buffer (mgsub b i₁ len₁)) (loc_buffer (mgsub b i₂ len₂))
```

carrying an `SMTPat` so Z3 applies it automatically, over the model `ubuffer_disjoint'` = same-allocation ∧ interval disjointness, with `len = 0` trivially disjoint. Plus `gsub_gsub` (sub-of-sub collapses to a single offset), `loc_includes_gsub_buffer_l` (the containment dual), and a genuinely range-grained footprint `loc_buffer_from_to b from to` with its own disjoint/includes lemmas. These four are ¶3.2's obligation layer, transcribed.

Two honest qualifications, both important. First: **Low\* has no linearity or exclusivity whatsoever.** `mgsub` is *non-consuming* — it leaves `b` fully usable — nothing stops a program holding two overlapping sub-buffers, and overlapping writes are not prevented. `loc_disjoint` is a hypothesis of frame lemmas, not a permission; violate it and you lose frame conclusions, not memory safety. So Low\* supplies concerns (i) and (iii) of ¶0.1 and not (ii), and the one-line contrast is:

> Low\* answers *"what did this modify?"*. DLLBC asks *"may this coexist?"*.

Second: **the arithmetic is not where the burden lives.** The `.fsti` carries a handful of `gsub` lemmas and forty-odd `modifies_*` lemmas — `modifies_trans`, `modifies_loc_includes`, `modifies_buffer_elim`, `modifies_loc_buffer_from_to_intro` — over a `loc` commutative monoid. Framing *composition* is what a Low\* development pays for. That machinery exists because there is a heap to frame over; ¶3.6 is the argument that a heapless ownership tree does not need it, and it is the design's one substantive claim of improvement over its nearest neighbour — entirely downstream of §0's no-heap decision rather than of anything invented here. Hence the instruction to an implementer: **steal Low\*'s predicate and obligation shapes; do not steal its architecture.**

**Rust (the shape being imitated, and the exact line it cannot cross).** `&mut [T]` is a two-word fat pointer `(data_ptr, len)` — the length lives in the *reference*, not the referent — so a subrange reborrow is already pure value arithmetic on `(ptr + lo, cnt)`, the same triple as `gsub` and as a range place. Rust has the representation; what it lacks is the typing.

The borrow checker's conflict test is `places_conflict` (`rustc_borrowck/places_conflict.rs`), which walks two projection lists in lockstep and classifies each pair as `Arbitrary`, `EqualOrDisjoint`, or `Disjoint`. What it can do is more than usually credited, and the nuance matters:

* `ConstantIndex` vs `ConstantIndex`: compared numerically, `if o1 == o2 { EqualOrDisjoint } else { Disjoint }`.
* `ConstantIndex` vs `Subslice { from, to }`: `if (from..to).contains(&offset) { EqualOrDisjoint } else { Disjoint }`.
* `Index` vs `Index` (runtime indices): `EqualOrDisjoint`, which under the borrow-checking bias `PlaceConflictBias::Overlap` means **conflict**.

So rustc *already performs interval-disjointness reasoning* — it is a real, safe, static split — but only where the bounds are compile-time constants, which in practice means slice patterns (`[a, b, rest @ ..]`). The moment an index is a variable it gives up, and the give-up is more total than "no proof channel": **the index operand is discarded from the analysis entirely**, which is why borrowck's diagnostics print `a[_]`. There is nothing there to attach a proof to, and the place language has syntax rather than propositions in any case. **Proof-conditioned disjointness is precisely the replacement of that hardwired constant-only test with a user-suppliable derivation** — and note it is an *extension* of something rustc does, not the introduction of something alien to it.

`split_at_mut` is therefore safe outside and raw pointers inside — `from_raw_parts_mut(ptr, mid)` and `from_raw_parts_mut(ptr.add(mid), len - mid)` under an `unsafe` block whose SAFETY comment simply asserts non-overlap. The Rustonomicon is explicit that teaching borrowck this is "pretty clearly hopeless." Note *why* the one-call-returning-a-pair trick works: ownership of `&mut self` moves **into** the call, and two fresh fat pointers come out, so the checker never sees two reborrows of one place — it sees a move and two unrelated returns. The split is legitimized at function-boundary granularity by an unsafe-audited contract, not by a rule.

Rust's general answer, where the library needed one, is `get_disjoint_mut` (stabilized 1.86, renamed from `get_many_mut`): `Result<[&mut _; N], GetDisjointMutError>`, a **runtime** pairwise overlap-and-bounds check, with `get_disjoint_unchecked_mut` as the unsafe variant that makes non-overlap a caller UB-obligation. It accepts `Range` indices. That is ¶0.1's concession in its concrete form.

On the proposal landscape, briefly, since "someone must have proposed this" is the natural next thought. **View types / partial borrows** (Matsakis 2021; rfcs#1215) are at field-of-struct granularity, not ranges, and have not landed. **Generativity / branded indices** (the `indexing` crate; GhostCell, ICFP'21) tie an `Index<'id>` to one container by a lifetime brand, making in-bounds a type-level invariant and eliminating bounds checks — but the brand's own documentation is explicit that indices "do not track mutability or exclusive access," and range access still goes through `&mut Container`. So it solves the **bounds** half of premise (2) and none of the aliasing half, which makes it a genuine partial precedent rather than a competitor. **Polonius/NLL** refine *when* borrows are live, not *whether* places overlap. Nothing pending makes `split_at_mut` derivable.

**Aeneas / LLBC (the system this project is measured against).** Three separate findings, and an earlier draft of this section got two of them wrong.

*In the mechanized semantics there are no aggregates of any kind* — not arrays, not slices, not even tuples or structs. The in-repo `aeneas/` subtree (the `mechanized-llbc` development for the 2024 symbolic-semantics paper) has value grammar `VBottom | VInt | VBool | VMutLoan ℓ | VMutBorrow ℓ v` (`LLBC.v:16-23`), HLPL+ adding only `VLoc | VPtr` (`HLPL_plus.v:19-27`). `Field (nat)` is *declared* in the projection grammar (`lang.v:11`) and **matched nowhere** — dead syntax. A case-insensitive grep for `array`, `slice`, `split_at` or `subslice` across all 15,816 lines of `.v` returns nothing. So the in-repo prior art on this topic ends at the `PathToSubtree` trichotomy quoted in ¶3.1, which is genuinely the right structural ancestor and is why ¶3.1 can claim there is no disjointness *test*. Encouragingly, the generic `Class Value` framework there (arity/children, `PathToSubtree.v:439`) would happily admit an n-ary array node; what it has no form for is a projection that descends by a *runtime-computed* index.

*Upstream, arrays bypass places entirely — by an explicit micro-pass.* Charon **does** have `ProjectionElem::Index { offset, from_end }` and `Subslice { from, to, from_end }`, but Aeneas requires `--index-to-function-calls`, which **erases them** into calls to `BuiltinFunId::Index` (`ArrayIndexMut`, `SliceSubSliceMut`, `ArrayToSliceMut`, …). The symbolic interpreter therefore never sees an index projection at all: `InterpPaths.ml`'s `project_value` matches only `Field`, `Deref`, `PtrMetadata`. So `a[i]` is a **whole-value opaque call** — a fresh region abstraction swallows the entire `&mut a`, and the pure translation emits a forward and a backward function.

*And here is the sharpest finding, which corrects this document's own earlier framing.* A **range borrow does exist** in Aeneas: `SliceIndexRangeUsizeSlice.index_mut` takes a `Range` and returns a sub-slice with back `List.setSlice!`, guarded by `r.start ≤ r.end ∧ r.end ≤ s.length`. What does not exist is **coexistence**: the parent `&mut` is consumed and later reconstructed, one range at a time, so two live disjoint subranges are *unrepresentable*. Disjointness therefore never arises as a proposition anywhere in the system. That is the precise gap — not "Aeneas has no ranges," which would be false, but "Aeneas has no two-at-once."

Two honesty notes on what is trusted, both correcting an earlier draft. The Lean models are **not axioms** — they are definitions with *proved* spec theorems; what is trusted is the modelling step, since nothing connects them to any loan semantics. And the trust is load-bearing in a visible way: `split_at_mut`'s backward function re-appends the halves when the length guard holds and **silently returns the original slice unchanged when it does not** (a bare `else s`), sound only because Aeneas-generated code always satisfies the guard — a source comment says exactly this. A backward function total by fiat is not something any borrow semantics would license; it is the seam where the model is glued on. Relatedly: the OOPSLA'24 soundness theorem covers the **borrow discipline**, not the array builtins.

None of this is a criticism — punting is a legitimate choice for a translation-based tool — but it settles the positioning: the range-place design is not a reimplementation of something Aeneas has. It is the thing Aeneas assumes.

**Verus.** Two layers, and conflating them would flatter the comparison. At the **safe-Rust layer** the borrow checker is inherited from rustc unmodified, `&mut [T]` is viewed functionally as `slice@ : Seq<T>`, and `split_at_mut` is an `assume_specification` — an **axiom** — with `requires mid ≤ len`, subrange views for the two results, and the recombination `final(slice)@ == final(ret.0)@ + final(ret.1)@`, which is a back function wearing two-state-postcondition clothes. There is no mutable sub-range primitive at all (`slice_subrange` is shared-only), and no `vstd` route to "two `&mut` subranges given a user `Le` proof." At the **tracked-permission layer**, `PointsToRaw::split`/`join` (¶3.3) is the real thing: an affine token over an address set, split by a user-discharged `range.subset_of(self.dom())`, residue by set difference, coexistence free by construction. This is the closest existing instance of "proof-conditioned disjointness," and ¶3.3 adopts its shape. Its limitation for our purposes is placement, not power: it lives in ghost proof code around raw pointers, never in the type of a surface `&mut`.

**Dafny (the anti-pattern, stated because it is instructive).** `array<T>` framing is a `modifies` clause over a **set of objects**, and an array is one object — so a method touching `a[lo..hi]` must declare `modifies a`, licensing writes to every cell, and then pin the untouched part in its *postcondition*: `forall i :: 0 <= i < lo ==> a[i] == old(a[i])`. Two range views of one array cannot be framed separately at all, and disjointness of two arrays is reference inequality `a != b`, never index arithmetic. That is the frame described by contract in its purest form — precisely what ¶0 claims range places delete. Anyone wanting to see the cost of *not* having this design should read a Dafny array method's postcondition.

**Creusot.** `&mut T` is a prophecy pair (current, final) and slices are `Seq`; `split_at_mut` is a trusted extern-spec at one split point with obligation `mid ≤ len`, and rejoin is the parent's prophecy *defined by* the children's (`(^self)@.subsequence(…) == (^l)@`). `Range<usize>` **is** an index for `index_mut`, so — as in Aeneas — a genuine range borrow exists, one at a time, with the whole `&mut` consumed; the residue is a `resolve_elsewhere` forall-equation over snapshots, a quantifier rather than a capability. Disjointness never arises as an obligation. rustc guarantees the aliasing; Creusot translates it.

**Viper and Prusti** deserve separating, because the capability is real and the exposure is not. Viper's **quantified permissions** — `forall i :: lo ≤ i < hi ==> acc(loc(a,i).val)`, with an injectivity obligation Viper *requires* for every quantified `acc` — split by splitting the quantifier's domain, discharge the arithmetic by SMT, compose two arbitrary disjoint ranges freely, and represent the residue as the complementary-domain quantifier. That is a complete answer at the intermediate-language level. But Prusti never exposed it to Rust `&mut`: the Place Capability Graphs paper (arXiv:2503.21691) states that the implementation "did not implement… slices, arrays, or closures." The machinery exists in the IVL and is unreachable from the surface language — which is a recurring shape in this survey rather than an isolated accident.

**RefinedRust** is treated in ¶1.1, where it belongs: the only system that puts the takeover marker *inside* the aggregate's typed value, and unable to put two of them there. Its Iris cousin **RustHornBelt** (PLDI'22) does achieve genuine element-granular borrow subdivision with prophecy-based rejoin for `Vec::index_mut` and `IterMut` — but as a bespoke Iris proof about one unsafe library, splitting exhaustively into *all* elements, and never as a rule a checker applies.

**What none of them does.** Line the systems up against ¶0.1's three concerns and the gap is a hole in a table, not a missing idea. Mechanized LLBC decides disjointness syntactically and has no aggregates. Aeneas and Creusot have real range borrows but only one at a time, the parent consumed and reconstructed. rustc erases the index and launders the split through `unsafe`; `get_disjoint_mut` does it dynamically. Iris splits definitionally at one exhaustive point. VST has the arbitrary-subrange rules with pure-arithmetic side conditions — the closest — but its residues pile up in a proof context. Viper's quantified permissions do the whole job at the IVL level and Prusti never exposed them to Rust. Low\* has the arithmetic and no exclusivity to enforce. Verus's `PointsToRaw` has the linearity and the residue but lives on ghost tokens over raw pointers with no bridge back to two safe `&mut [T]`. RefinedRust puts one hole in an array and cannot put two.

**No prior system makes program-supplied dependent evidence license the coexistence of two surface mutable borrows inside the operational semantics and the borrow checker itself.** That is available here only because DLLBC has a comptime fragment inside the same language as its ownership discipline — which is the whole reason the calculus exists, and is therefore the right place for the idea to be tried. Note the recurring shape in the list above, since it is the most useful thing the survey turned up: the capability keeps existing one level below the surface language (Viper's QPs, Verus's tracked tokens, RustHornBelt's prophecies) and keeps failing to reach the type of a `&mut`. The bet this design makes is that a language whose proof layer and whose ownership layer are the *same* language does not have that level to fall through.

---

## ¶8. Costs, obligations, and non-goals

### 8.1 Kernel surface added

| addition | kind |
|---|---|
| `Array : Nat → Type₀ → Type₀` | type former, fixed basis (not §7's scheme) |
| `Arr` literal + segment structure | value form (a reserved node; every generic walker traverses it unchanged) |
| `arrCat`, `arrRec`, `aget` | computing constants in the basis |
| index step `[t]`, range step `[t ; t′]` | place-path grammar |
| CARVE | one reorganization, three premises |

Five entries, of which exactly one — CARVE — has semantic content. The rest are representation. That ratio is the design's main defence: nothing in the borrow machinery changed, because the carve's job is to hand the *existing* machinery a tree it already knows how to handle.

Two §7 obligations come along with basis membership and must be *written* rather than *generated*, which is the concrete form of ¶9(c)'s worry. **`Array.copy`**: §7.2's consume-and-rebuild, over the cons view, calling `T.copy` per element — which means §7.2's derivability fact ("τ is unrestricted iff `τ.copy` is generatable") continues to hold for arrays only by hand-checked coincidence rather than by construction. **The unrestricted classification**: `Array n T` is unrestricted iff `T` is, which is the same rule §7.1 states for parameters, but stated again rather than computed. Neither is hard; both are drift surface.

### 8.2 Soundness obligations created

For whoever writes the metatheory, the new proof burden in full:

1. **Carve is snapshot-preserving.** `⇝(carve(A, lo, cnt)) = ⇝(A)`. This is `arrCat_take_drop` (¶1.3) and nothing more. It is the one obligation that is genuinely about arrays.
2. **Carve's refinements are knowledge, not state.** Two refinements fire: the index refinement `σ_m := add lo′ (add cnt rest)` and the value refinement `σ := arrCat σ₁ (arrCat σ₂ σ₃)`. Both substituends are marker-free, so §3.2's asserted invariant holds — but this is the first ownership operation that refines, and the assertion should be *exercised* on it rather than assumed to still hold.
3. **Range-loan collapse is owned-position collapse.** A marker in a segment body is in owned position; §2.2's move rule and §5.4's `collapseArg` reach it by the existing traversal. What must be checked is the *transitivity* invariant §5.3 records for executing mode ("any operation that hands out a value peeled from a demand-ended suspension must drive it to owned-marker-free normal form first"): a segment list can hold several markers at once, so a partial collapse is now easy to write by accident. Each executing former must preserve full collapse, and a negative test per rule branch — the M20 lesson — should cover the multi-marker case specifically.
4. **Merge is confluent and value-preserving.** The normalization that makes a rejoined array indistinguishable from an uncarved one. Straightforward, but load-bearing: it is what keeps `canonicalize` a decision procedure for Ω-equality, and hence what keeps the golden-trace suite and the differential harness working.
5. **The group over-approximation, with several captured loans in one owner.** A new instance of §6.1's existing reconciliation problem, not a new problem.

Note what is *not* on the list: there is no disjointness soundness theorem, because there is no disjointness judgment. That absence is the design's point.

### 8.3 Erasure

Everything the design adds is comptime and erases. The length index is a §7.1 index position (erased). The `Le` evidence is a proof (erased). The residue's extent `rest` is a comptime `Nat` (erased). The **carve itself is erased entirely** — it rearranges the checker's bookkeeping and produces no runtime action, because at runtime an array is a contiguous buffer and a range borrow is a `(base + lo, cnt)` pair computed by two machine instructions. The segment list has no runtime existence at all; it is the compile-time record of who holds which part of a buffer that was never restructured.

This is the strongest single argument for the whole approach over the M23 stopgap: `split_off`/`append_back` genuinely mutate the runtime shape and walk `O(i)` cells. A carve compiles to pointer arithmetic, and rejoin compiles to nothing.

### 8.4 What stays out of scope

* **Growth and reallocation.** `Array n T` is fixed-length by construction. `Vec T` is `Σ (n : Nat). Array n T` plus a capacity discipline; push/pop and reallocation are a separate design, and the interesting part of them (proving `Vec`'s internals safe, per `what-is-ochre.md`'s first stated goal) presupposes this one.
* **Two-dimensional and strided views.** `Array n (Array m T)` works and carves at the outer level. A transposed or strided view is a *non-contiguous* range, which the segment representation cannot express, and which the extent-map disjointness argument would not survive. Out.
* **Shared borrows.** Deferred with §10. The observation to record: read-only sharing needs no *disjointness* at all — two shared range borrows may overlap freely — so of the carve's three premises, a shared carve keeps (2), the in-bounds obligation, and drops (1)'s requirement that the leaf be unloaned. Which strongly suggests shared slices are the easier half and should not be designed until the mutable rule has been built and lived with; the temptation to generalize premise (1) to a permission lattice up front should be resisted.
* **Non-contiguous and dynamic-shape ranges.** A range whose bounds are not comptime terms. Out by construction: the design's entire arithmetic lives in the comptime fragment.
* **Rigid-length signatures.** A function whose array length is a compound neutral cannot carve (¶3.2, premise 3). The remedy is stylistic — take the length as a parameter — but it is a genuine restriction on what signatures are writable, and if it turns out to bite, the escape is the same one M10 built for its rigid cases: name the equation and carry it, rather than solving it.

---

## ¶9. The three decisions I am least sure of

Recorded for the user, plainly, in decreasing order of how much would have to change if they are wrong.

**(a) The residue transition — refining a *length index* to make the carve's arithmetic definitional (¶3.2, premise 3).** This is the most aggressive idea here and the one that buys the most: it deletes every `sub` from the design and makes the audit's rejoin conversion definitional rather than lemma-mediated. But it means the carve *refines the type index of an array from inside an ownership rule*, which is a new kind of act in this calculus — every prior refinement was fired by a match on a value. It restricts carving to arrays whose length is flexible (a bare σ), which pushes shape onto every signature. And I have argued, but not tested, that it respects §3.2's knowledge/state invariant. The conservative alternative is to compute the residue as `sub`, accept the arithmetic tax, and keep the ownership rules refinement-free. That alternative is strictly simpler and strictly more painful, and I do not know which way the milestone would break.

**(b) How the residue is represented (¶1.1, ¶3.3).** This is the decision the survey shows is genuinely open, because **all the plausible answers exist in the wild** and they disagree:

* **One piece, possibly non-contiguous.** Verus's `PointsToRaw::split` returns the residue as `self.dom().difference(range)` — a single token over a set. Maximally general; costs the extent map its interval structure, and with it ¶3.1's cheapness.
* **Two pieces, prefix and suffix.** VST's `split3_array_at` and iterated Iris `array_app` both leave `take lo vs` and `drop hi vs` as two standalone assertions. This is the classical answer and the closest to what a proof engineer expects.
* **Implicit in the owner — the residue is never named.** Iris's `update_array` leaves only a magic wand; Aeneas leaves only a backward function; RustBelt *drops* the residue and recovers it from lifetime-death inheritance. Cheapest representation, and fatally wrong for us: you cannot hold two wands over one array and still have an array, which is exactly what two live range borrows require.

I chose a fourth position — **named, but living in the owner's value tree as segments** — which is prefix-and-suffix in substance while keeping both pieces attached to the thing they are pieces of. That is what makes ¶3.6's frame preservation automatic (the residues never leave, so nothing has to describe them) and what keeps merge able to erase the carve's history.

The survey's verdict on this point is worth quoting as evidence rather than reassurance: what VST — the system with the closest rules — lacks is exactly "hold `[lo₁,hi₁)` and `[lo₂,hi₂)` with the remainder implicitly retained by the owner." In VST the residues are standalone assertions that accumulate in the proof context and must be threaded by hand. So the fourth position is a real gap in the literature and not an oversight of mine. That is genuinely encouraging and genuinely not decisive: an unoccupied position in a well-explored field is either an insight or a place everyone else found a reason to avoid, and I cannot tell which from inside the design. This is the one I would most want a second opinion on before anyone implements.

The sub-question rides along: n-ary segments with explicit extents, versus a binary `arrCat` node. I took segments to keep Ω canonical — with a binary node one array value has many trees, and every Ω comparison (`canonicalize`, the golden-trace suite, the differential harness's simulation relation) would need quotienting by associativity. But segments carry their extents redundantly, and redundancy in a state representation is exactly where desynchronization bugs live.

**(c) `Array` in the fixed basis rather than as a §7 declaration.** I argued that no CIC-scheme inductive can have flat values and that flatness is the entire point. That argument is sound but it widens the kernel at precisely the moment §7 is trying to establish that declarations generate everything (recursors, `copy`, the unrestricted classification). An array's `copy`, its recursor, and its unrestricted-iff-`T`-is classification all now have to be *written* rather than *generated*, and each is a place where the basis and the scheme can drift apart. The alternative — find a scheme extension that admits flat n-ary values — is a real research question I did not attempt, and if it has an answer, it is a better one than mine.

*(A fourth, smaller: whether element access `a[i]` should be a one-slot carve, as designed, or a cheaper dedicated rule. Uniformity says carve; but every element read then fires a refinement, and in a loop-free recursive cursor that is a lot of σ churn for what compiles to one load.)*

---

## Appendix A. Mechanization map

Where each part of this design lands in the current tree, for whoever builds it. Nothing here is a new subsystem; the point of the appendix is that the list is short.

**`Dllbc/Value.lean` — the value layer.** No new `Val` constructor. An array node is `ctor "Arr" segs` and a segment is `ctor "§seg" [cVal, body]`, both reserved names with no `ctorSig` entry, so no program can write or match them. Every existing generic walker then works unchanged and *must not be touched*: `loanIds`, `symIds`, `renumber`, `loanToPvar`, `hasStateMarker`, `beq`. `pretty` should learn the `Arr⟨c ▷ b, …⟩` rendering, since the trace suite is the test suite.

**`Dllbc/Pure.lean` — the comptime layer.** `ctorSig` gains `"Arr"` (field telescope `T` repeated `n` times, at concrete `n` only; `none` at symbolic `n`). `typeCtors` gains `Array` ↦ `some ["Arr"]` at concrete `n`, `none` otherwise. `whnfV` gains ι-rules for the two new constants: `arrCat` on run-headed arguments (segment-list concatenation), and `arrRec` on the cons view. Everything else — `substPure`, `nfV`, `convert` — is untouched, which is the load-bearing claim: array snapshots are ordinary neutral spines.

**`Dllbc/Machine.lean` — places.** `Pos` (line ~484) grows from `⟨root, derefs : Nat⟩` to `⟨root, path : List Step⟩` with `Step ::= peel | idx Val | rng Val Val`; `placeToPos` gains the two term shapes; `navRead`/`navWrite` gain the segment cases. This is the widest-reaching change in the tree, because `Pos` is threaded through `getAtPos`/`setAtPos`/`writeR`/`writeC`/the `&mut` rule — but it is mechanical, and the existing `derefs : Nat` is exactly `List Step` restricted to `peel`.

**`Dllbc/Machine.lean` — the carve.** One new function, sitting alongside `drop` and `endLoan` as a third reorganization, called from `navRead`/`navWrite` when a step lands on an array node that is not already segmented at the requested boundary. It calls `hasType` for premise (2) (the same call the audit makes), the M10 refl-match solution path for premise (3), and `refineSym` for both refinements — which means it inherits the "reaches all σ-bearing state" invariant for free, and inherits the §3.2 marker-free assertion as a live check.

**`Dllbc/Boundary.lean` — the audit.** `collapseArg`'s `firstLoanMarker` already finds markers inside `ctor` fields, so range-loan collapse needs no new code. What is new is the ¶3.8 extent check on the obligation type at `seedTelescope`, and the merge normalization before the `hasType` in `auditObligation` (or, equivalently, inside `⇝` — the latter is cleaner, since merge is then part of what "the snapshot of an array" means rather than a step the audit remembers to take).

**`Dllbc/Std.lean` — the library.** Three tiers. The carve's own arithmetic: `le_split`, `add_cancel_l`. The ¶3.2 obligation layer transcribed from Low\*: `range_disjoint`, `range_empty`, `range_includes`, `carve_carve` — build these four *first* and in that order, since they are the interface premise (2) is stated against and the fourth is the one that decides whether nested carving is cheap. Then the array layer proper: `arrRec` spines, `aget`, `aTake`/`aDrop`, `arrCat_take_drop`, and the transfer of `count`/`Sorted`/`Bound` from `listRec` to `arrRec`. This is the bulk of the *work* and none of the *risk*; M16–M18 established that this shape of library goes through in the M15 surface at roughly first-try.

**Test architecture.** The golden-Ω traces of §2–§3 are unaffected (no existing program carves). The new traces are ¶3.3 and ¶3.4, which are written above in exactly the form `expectEnv` consumes. The differential harness (M8/M9) should gain array bodies before anything else is believed: the multi-marker collapse of ¶8.2's obligation 3 is precisely the bug class a per-rule-branch negative test exists to catch, and M20's lesson was that the branch nobody tested is the branch that lied.
