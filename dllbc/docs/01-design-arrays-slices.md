# Arrays, Range Places, and Proof-Licensed Carving

*A design note for DLLBC, in the voice and numbering conventions of `dllbc-arrows.md`. References of the form §N are to that document; references of the form ¶N are internal to this one.*

> **STATUS: built, run, and amended from measurement (M24–M25, merged at `00cdbb69`).** This note was written before any of it existed. It has since been implemented in full — the carve machinery, route (a) with the cited-equation rule, the transferred library, and a verified in-place array quicksort that both *checks* and *runs*, cross-differential green on eleven inputs against M23's List implementation, two programs sharing no code, no predicates and no container.
>
> The design held. All four rulings survived contact; ¶1.3's transfer promise verified verbatim at twenty-one items; ¶6's three-way carve landed in this document's exact notation. What did not hold is recorded **in place and labelled**, from the implementation's own ledger (`DELTAS.md`, which remains as the historical record). Corrections read *"an earlier draft said X; it is Y, because Z."*
>
> **Two of this note's claims did not merely need refining — they reversed, and are struck through where they stood rather than quietly rewritten.** ¶5 recommended carving inline and reaching for a function boundary only when you want abstraction; the truth is the opposite, and a body following that advice cannot be written at all (¶5.1). ¶6 claimed "one stratum deleted, one inherited, **none invented**"; one *is* invented, at the leaf's interface (¶6.1). Both are the same fact seen from two directions: **carving is a within-body mechanism, and function boundaries are where its guarantees stop and start again.** A reader who takes nothing else from this pass should take that.
>
> Two soundness findings — ¶3.2a's cited-equation rule and ¶3.6's polarity inversion — are the reason this pass exists at all, and neither was predictable from the desk.
>
> Where this note now says "is", it has been run. Where it says "would", it has not.

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

Each segment carries its own **extent** `c` — a comptime `Nat` value sitting in the tree. Canonical form is a single segment; a fresh array from a literal is `Arr⟨n ▷ [v₁ … vₙ]⟩` and a seeded argument's payload is `Arr⟨n ▷ σ⟩`.

*Amended (R2): the abbreviation is the implementation.* The draft said an uncarved array's `Arr⟨n ▷ σ⟩` "abbreviates to plain σ, since the two are the same state", and the implementation took that literally — the segment wrapper appears **only when carved, and always with ≥ 2 segments**. The consequence is that a carve cannot read a node's total extent off a wrapper, and does not need to: every array-shaped value determines its own extent (a run knows its length, a segment list sums, an `arrCat` spine carries both halves) **except a bare σ**, whose extent lives in its `sctx` type. So the extent query is partial by design. Stamping every array with its length would have doubled the representation's one redundancy to no purpose.

Two normalizations, both lazy in §2's sense — performed when a rule's premise demands them, never eagerly:

* **Merge**: two adjacent segments **whose bodies are runs** collapse into one, of the summed extent, holding the concatenated run. `Arr⟨1 ▷ [3], 2 ▷ [7,2]⟩ ⇒ Arr⟨3 ▷ [3,7,2]⟩`.

  *Corrected (R4).* An earlier draft had two adjacent σ's merging into one segment bodied by `arrCat σ₁ σ₂`. They stay two segments. The pair already types against `Array (add c₁ c₂) T` by the extent-consistency check, and ⇝ folds them to that very `arrCat` anyway — so merging bought nothing and cost merge its best property: leaving σ's alone keeps it a **pure function of the value tree**, with no element types, no fuel and no `sctx`. The consequence is not local; see R9 in ¶8.2, where "only runs merge" is what makes the checking and executing modes end at genuinely different — and both correct — value trees.

  *Corrected (R5): "owned" means MARKER-FREEDOM, not "the body is not itself a marker".* An element cursor parks its marker *inside* a one-slot run — `1 ▷ [loanₘ ℓ]` — because ¶2.1 puts the element, not an `Array 1 T`, at an index place. The shallow test calls that body owned, merges it into its neighbour's run, and then hands the **marker out as an element** on the next read: the silent-marker class §3.2 and §5.2 both warn about, reached by a new route. This is the correction most likely to be re-introduced by someone optimizing merge.
* **Drop-empty**: a segment of extent `Z` is deleted. *This one turned out to be actively wrong at runtime* — it is the root of all four sites in ¶3.6's polarity finding, and survives only in weakened, mode-gated form. Read that entry before touching it.

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

**Verified, in full and verbatim (R11).** This was the claim ¶6's whole cost estimate rested on, so it was measured rather than assumed. The complete quicksort library now exists over arrays — the predicates (`countA`, `BoundA`, `SortedA`, `UbA`, `LbA`, `asingle`), the glue stack (`sorted_headA`/`tailA`, `ub_headA`/`tailA`, `lb_headA`/`tailA`, `lb_boundA`, `bound_arrCat`, `sorted_arrCat`), the count layer (`count_arrCat`, `count_acons_hit`/`miss`), and M23's permutation keystone (`noAbove_of_ubA`, `ub_of_noAboveA`, `ub_permA` and the three `Lb` mirrors). **Twenty-one definitions and proofs, every one its list counterpart with `listRec ↦ arrRec` and `Cons ↦ acons` and nothing else changed.** The entire permutation layer and `count_arrCat` checked first try, as did five of the seven glue lemmas. The keystone is the one worth dwelling on: it cost M22 its hardest single result, and it transfers unchanged — so "positional bounds are not permutation-invariant" has no analogue here at all.

**What the promise omitted (R10): three ι-rules are what make the transfer *mechanical* rather than merely possible.** The mathematics does transfer, but only if the array constants **compute the way the list constructors do**; otherwise every step of a transferred proof wants a transport lemma its list original never needed. Two rules are the obvious ones — `arrCat` computes on an `acons`-headed left argument (`arrCat (acons x xs) b ⇝ acons x (arrCat xs b)`, which is exactly `append (Cons h t) u ⇝ Cons h (append t u)`), and `arrRec` fires on the cons view, so a predicate over arrays unfolds on an `acons` precisely as its counterpart unfolds on a `Cons`. Without them `SortedA (arrCat (acons h t) …)` does not unfold, and `sorted_append_pivot`'s proof turns entirely on that unfolding.

The third was invisible until the glue was written, and it is a lesson about this document rather than about arrays: a nonempty **run** on the left with a non-run on the right must peel its head into an `acons`. `asingle p` computes to the run `[p]`, so **¶6's own chosen spelling `arrCat (asingle p) r` was stuck for symbolic `r`** — the notation could not reach the cons view it is notation *for*. The rule is the same one read through the other view: a literal is a cons spine that happens to be written flat.

**The split view** is the constant

```
    arrCat : Π (m k : Nat) → Array m T → Array k T → Array (add m k) T
```

*Corrected (C1): no element-type argument.* The draft wrote `arrCat` and `acons` with a leading `T`; neither has one. An `Array` is never applied, so these two constants' result types are always *checked* against an expectation and never synthesized — the element type is recovered from the expected type. More decisively, the merge normalization and the ⇝ fold would each have had to **manufacture a `T` they cannot read off a value tree**, since Ω records extents and not element types. `aget` keeps its `T` (its result type genuinely *is* `T` and must be synthesized), and so does `arrRec`, whose premise types mention it.

`arrCat` *computes*: `arrCat (Arr⟨…⟩) (Arr⟨…⟩)` reduces to the segment-list concatenation, and `arrCat` applied to two σ's is a legitimate stuck neutral. This is the comptime shadow of the segment structure — and the division is exactly §3.2's knowledge/state line:

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

**The range step's full built form has four slots, three of them optional** (¶3.2 justifies each; they are collected here because the grammar is the reader's first encounter with them):

```
    a[ lo ; cnt ; rest | h | heq ]
         │     │    │     │    └── the cited decomposition — Id Nat ⟨leaf extent⟩ (add cnt rest)
         │     │    │     └─────── the containment evidence — premise (2)
         │     │    └───────────── the residue's extent, SUPPLIED (route (a), G1)
         │     └────────────────── the request's width
         └──────────────────────── the request's offset

    a[ lo ; .. ]     "to the end of the segment starting at lo"
```

Omitting `h` means conversion alone must discharge premise (2); omitting `heq` means the decomposition must hold by conversion; omitting `rest` means the checker mints the residue itself, which is what the original design did and what ¶3.2's soundness finding restricts. Each optional slot is the same house pattern as §1.2's `[k]` and §3.2's `match h :` — an optional surface element naming something the checker already knows, declared rather than inferred, costing nothing when absent.

*A limit worth knowing before reaching for it (G6):* `a[lo ; ..]` reads the count off the segment **starting at** `lo`, and a zero-extent residue is dropped by ¶1.1's drop-empty, so at a concrete length there may be no segment there at all. Every residue in the built quicksort is therefore named explicitly. `..` is the partial closure of the residue-naming problem; route (a)'s `rest` slot supersedes it wherever the length is nameable, which is everywhere that matters.

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

At any moment, an array node's segment list induces an **extent map**: a list of triples `(offset, count, status)` with `status ∈ {owned, loaned ℓ, hole}`, offsets running consecutively from the node's base. `Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩` induces `[(0,1,owned), (1,2,loaned ℓ)]`. *Owned* here is ¶1.1's corrected sense — **marker-freedom anywhere in the body**, not merely "the body is not itself a marker"; an element cursor's marker hides one level down inside a one-slot run.

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
                    the extent map has a leaf L at (b, m) containing the request     (1)
                    e ⊢ Le lo′ m  ×  Le (S^cnt lo′) m         (leaf-RELATIVE)        (2)
                    the decomposition transitions on lo and on m succeed             (3)
    ─────────────────────────────────────────────────────────────────────────────  CARVE
       L : Array m T  ↦  ⟨ lo′ ▷ L₁ , cnt ▷ L₂ , rest ▷ L₃ ⟩

              where   lo ≡ add b lo′        and       m ≡ add lo′ (add cnt rest)
              are the equations premise (3) solved — not differences it computed.
```

*The premise-(2) line above is amended; the draft wrote it in absolute coordinates as `Le b lo × Le (add lo cnt) (add b m)`. Both changes are spelling, neither alters what the premise means, and without them it is not dischargeable at all — see R7 below.*

Premise by premise.

**(1) Leaf selection.** Scan the extent map for a leaf containing the requested range. When offsets are symbolic the scan cannot decide containment by computation; premise (2) decides it instead.

Three amendments here, all found by running programs:

*The evidence's type is not the selector (C7).* The draft proposed disambiguating candidate leaves by checking the evidence against each. What actually disambiguates is the **supplied decomposition**: selection prefers the leaf whose extent already *is* `add cnt rest`, then any non-empty leaf. The reason is a case the draft could not have seen, because it only exists at concrete lengths: a **zero-extent segment shares its base with the segment after it**, so a node holding one has two leaves at that base and base alignment picks the wrong one. Zero-extent segments are unreachable symbolically — a residue σ is never *known* to be zero — and routine concretely, since every runtime-computed split has an empty side eventually.

*A loaned leaf is not automatically a rejection (C4).* A request **contained** in a loaned leaf ends that loan and retries; only a request that **straddles** a segment boundary is rejected. This is the calculus's existing character rather than a new decision, and it was probed rather than assumed: `let p = &mut x; let q = &mut x;` is accepted on `main` today, leaving the first borrow dead. Two live overlapping mutable borrows remain unrepresentable; only the *moment* of rejection differs from the draft — at the dead borrow's next use, not at its creation. It is also what makes ¶3.6's own group trace work, since `let z = a[0]` must end the group to read across it.

*The scan itself reads a place, so it must demand-end first (C6).* §5.2's rule is "any rule that READS a place ends the suspensions parked there before it looks", and consulting the extent map is reading. The draft's implicit assumption — that a carve meets either an owned leaf or a loaned one — misses the case where the **whole payload** is out on loan, which has exactly one producer: a reborrow into a call. `f(&mut *v)` parks a marker at `*v`, and the group's release plugs the payload back only on demand, so there is no array value to read the extents from. That case is precisely "a recursive array program carves the argument it just handed to its recursive call" — which is every such program, and none existed until the quicksort did.

**(2) The containment obligation.** Two `Le`s. In the overwhelmingly common case the leaf is the whole array (`lo′ = lo`, `m = n`), `Le lo n` is discharged alongside, and the obligation collapses to the single

```
    Le (S^cnt lo) n           — e.g. Le (S i) n at an element place a[i]
```

which is, character for character, the bound the M22 quicksort already threads through every call as `hbnd`, and the cursor bound the swap sites have threaded since M13.

**Two spelling fixes, and they are the ledger's best entry (R7).** Neither changes what the premise means; without both, it cannot be discharged at all.

*Leaf-relative, not absolute.* `Le` computes by double `natRec`, so `Le (add b cnt) (add b m)` is **stuck on a symbolic base `b`** and never converts with the `Le cnt m` a program can supply. Premise (3)'s own logic is that offsets are leaf-relative; premise (2) now is too.

*A concrete count unrolls into successors.* `add` recurses on its **first** argument, so `add lo cnt` is stuck whenever `lo` is symbolic — and at every `a[i]` the count is literally 1, making the obligation read `Le (add i (S Z)) n`, which no program writes and no library lemma produces. Unrolled, `a[i]`'s obligation is `Le (S i) n`.

That second fix is where this document nearly told a lie in the one place it was trying to be exact. ¶3.5 claims that `nth2`'s `pij : Le (S i) j` and `p2 : Le (S j) (len *v)` are "on the nose, the containment obligation the carve rule demands", and that range places "take the same terms and give them their real job." Written the obvious way the obligation was `Le (add i (S Z)) n` and the claim would have been **false** — not approximately, but as a matter of which characters are on the page. It is now literally true, and only because the spelling was fixed. The same unrolling is needed for the extent map's **running base**, found by the three-way carve: the segment after a width-1 pivot has base `add i 1`, stuck on symbolic `i`, so `(*a)[S i ; ..]` could not find the segment it had just created.

A companion shape fix (R8): **extent sums are right-nested with no trailing `Z`.** `add` recurses left, so `add rest Z` is stuck the moment `rest` is symbolic and `Array (add k (add rest Z))` never converts with the owed `Array (add k rest)`. This presented as premise (3) failing and was only the sum being shaped wrong. Right-nesting also matches the `arrCat` spine the ⇝ fold builds and the `m ≡ add lo′ (add cnt rest)` the transition solves, so all three agree.

The evidence `e` is a comptime term, ⇝-read and checked by `hasType` against the obligation type — the same machinery §5.3 uses for any dependent argument. Three supply routes, in the order the checker tries them:

1. **Conversion alone.** When `lo`, `cnt`, `n` are concrete, `Le (add lo cnt) n` normalizes to `⊤` (Std's `Le` is a large elimination), and `⋆` inhabits it. The site needs no annotation. Every literal-indexed array access is free.
2. **A named proof at the site.** `&mut a[lo ; cnt | h]`, where `h` is any term of the obligation type — typically a telescope parameter. This is the symbolic case and it is where the borrow checker literally consumes dependent evidence.
3. **Nothing else.** There is no inference, no arithmetic decision procedure, no `omega`. A range whose bound is neither computable nor cited is rejected, with an error naming the obligation. That is the stuckness discipline of §2.3 applied to a new rule, and it keeps the checker a symbolic interpreter rather than a solver.

One case skips premise (2) and premise (1)'s ownership test entirely (R6): a **degenerate** request, where the request coincides with the leaf. Not merely the split is skipped — the ownership test is too. Between ¶2.2's take and its refill the segment holds a hole, and the ⇐-fill is that hole's one legal successor; testing ownership first rejected the refill.

**(3) The decomposition transitions.** This is the subtle premise, and the one that pays for itself.

Naively, the three pieces have extents `sub lo b`, `cnt`, and `sub (add b m) (add lo cnt)` — two subtractions, and every subsequent type-level fact about the carved tree drags them along. Instead, observe what `Le a b` *means* when `Le` is DLLBC's computing predicate: it is precisely the assertion that `b` decomposes as `a` plus something. So make the carve perform the decomposition rather than the subtraction, using one library lemma:

```
    le_split : Π (a b : Nat) → Le a b → Σ (d : Nat). Id Nat b (add a d)
```

(by double `natRec`, in the shape M15's surface authors comfortably). The carve applies it **twice**, once to each component of the obligation, and the two `Le`s of premise (2) turn out to be exactly the two numbers the rule needs:

* `le_split b lo (fst e)` yields `lo′` with `lo ≡ add b lo′` — **the leaf-relative offset**, which is why the rule never subtracts a base. (The surface writes offsets *absolutely*, `a[lo ; cnt]`; premise (2) is stated *relatively*. This step is the bridge, and R7's amendment is about how the `Le` that `e` is checked against is spelled once the bridge has been crossed — not about removing it.)
* `le_split (add lo cnt) (add b m) (snd e)` yields `rest` with `add b m ≡ add (add lo cnt) rest`, which with the first equation and `add_cancel_l` (one more library lemma, and the only new arithmetic this design asks for — it follows from `natRec` plus the S-injectivity M10 already derives) gives `m ≡ add lo′ (add cnt rest)` — **the residue**.

Two mechanization points, because both are places a reader will reasonably expect trouble and find none. First: the checker **unpacks** each `le_split` result itself, minting a fresh σ for the witness and a fresh hypothesis for the equation, exactly as a symbolic match on a Σ does. It does *not* need §9's missing comptime Σ-eliminator, because no program term ever projects these — they are machine-internal. (Task M23-i has since landed `sigmaRec` anyway, so the point is moot in the other direction too.) Second: the witness is introduced as a *symbolic* `Nat`, never computed; if the checker ever evaluated it, it would be evaluating `sub`, and the whole premise would be pointless.

Each equation is then discharged by the §10 refl-match **solution transition** — the exact machinery M10 built, used unchanged. Two outcomes, and they are M10's two outcomes:

* The equation's right-hand side is **flex** — the leaf's extent `m` is a bare σ, which is the case whenever the length came from a telescope parameter, i.e. always in the programs this is for. The solution transition refines `σ_m := add lo′ (add cnt rest)` everywhere, with the occurs check as usual. From that moment the decomposition holds *definitionally*, and every extent in the carved tree is a **given**, never a computed difference. No `sub` is produced anywhere, by this rule or by anything downstream of it.
* It is **rigid** — a compound neutral like `add σₐ σ_b`, or a concrete numeral. Concrete is fine (both sides compute, and the transition is a no-op). A compound neutral is stuck, and the carve is rejected with an error saying so.

*The flex restriction bites wider than the draft says (T2).* ¶3.2 and ¶8.4 state it for the *signature* case ("rigid length — take the length as a parameter"). It applies to **every segment's extent**, not only an array's declared length. A segment whose extent is a constructor tree (`S i`) or a compound neutral (`add p q`) cannot be sub-carved at a symbolic offset, because the equation then relates two rigid terms. A segment whose extent is a bare σ — a telescope parameter, or a residue a previous carve minted — carves freely. This is why a three-way split **cannot be reached by re-associating a two-way one**, and it has a consequence for program shape that ¶5 develops (R12): matching an array's length to peel a head makes the extent rigid, and forecloses carving at a symbolic offset in that same body.

### 3.2a Route (a): the program supplies the residue — and must cite its decomposition

The draft left a hole it did not notice, and closing it turned up the lane's one soundness finding. Both belong here because both are premise (3).

**The hole (G1): the residue has no surface name.** ¶3.4 writes `&mut (*a)[k ; rest]`, ¶5 returns `&mut (Array rest T)`, ¶6 writes `&mut (*v)[S(i) ; rest]`. In every case `rest` is a σ *the checker minted inside premise (3)*, with no binder any program can write. ¶5 half-notices ("more honestly written after the carve has run") and does not resolve it.

**The fix — route (a):** the program **supplies** the residue's extent, `a[lo ; cnt ; rest]`. Premise (3) then solves `m ≡ add lo′ (add cnt rest)` against a term the program wrote instead of minting a σ nothing can name. Same solution transition, still no `sub`, and it reduces to the minting behaviour when the slot is omitted. It is ¶8.4's own filed escape hatch — "name the equation and carry it, rather than solving it" — and the third instance of a house pattern (§1.2's `[k]`, §3.2's `match h :`): an optional surface element reifying something the checker already knows, declared rather than inferred, free when absent. Not a binder, deliberately: that is the scope-weird pattern already rejected once when `old *v` was chosen over it.

**The payoff is in the ordering.** The supplied equation is solved *before* premise (2) is formed, so the obligation is stated over an already-decomposed extent and frequently computes away entirely. ¶6's pivot carve asks `Le 1 rest`, unwritable; with `rest := S j` supplied it becomes `Le 1 (S j)` ⇝ `Le Z j` ⇝ ⊤ and needs no evidence at all. ¶3.2 says `Le a b` "is precisely the assertion that `b` decomposes as `a` plus something" — so supplying the decomposition supplies most of the proof. Route (a) does not merely make the obligation writable; it deletes it.

#### The soundness finding, and the ruling (C8)

**Premise (3), as drafted, refined a universal and held no caller to it.**

The transition solves the supplied residue by unifying against the leaf's extent. When that extent is a **telescope parameter's σ** — always, in exactly the programs route (a) exists for — that is a refinement of a *universally quantified* length against terms that may be unrelated existentials, and **nothing records the induced constraint in the signature**. So callers are never held to it:

```rust
fn resCarve (n : Nat, i : Nat, j : Nat, a : &mut (Array n Nat)) -> Unit {
  let l = &mut (*a)[Z ; i ; S j | le_add i (S j)]; () }
```

checks — and so does a caller passing `n = 2, i = 5, j = 5` with a two-element array. *Executing* that caller gets stuck. So `checkFn` accepted a program the concrete machine cannot run, which is M8/M9's differential property **failing** rather than over-approximating. (The concrete-length case was always safe; unification fails honestly there. Only the symbolic-parameter case refined.)

**The ruling.** The calculus has litigated this exact sin before: a body imposing an unrecorded constraint on its callers is M7/M8's signature-inferred constrained wire, whose lesson (M17) is that cross-boundary constraints must be **declared and checked, never inferred**. So:

> **Premise (3) MUST REFUSE to refine a telescope-parameter σ directly. It MAY solve along a CITED equation.**

That keeps §3.2's own line intact — refinement carries equation *solutions*, and a cited, checked `Id` is legitimate ⇜ knowledge with recorded provenance, where an unrecorded unification against a universal is not.

**Built** as a fourth optional slot, `a[lo ; cnt ; rest | h | heq]` — the house pattern's fourth instance. Premise (3) now: if the decomposition holds by **conversion**, nothing is asserted and nothing is demanded (the common case — a leaf whose extent is a constructor tree, `S m` against `add 1 m`, stays free); otherwise the equation must be cited, is checked by `hasType` against `Id Nat ⟨leaf extent⟩ (add cnt rest)`, and the same refl-match solution transition then runs, now licensed. The refusal is a few lines; the citation reuses M10's machinery.

**Two measurements say the rule is not a tax.** First, the programs had *already written the equations* — the partition returns `Id Nat n (add k (S jj))` and the splitter `Id Nat m (add k r)`, added as honesty decoration when the hole was merely known, and made load-bearing by the ruling. Second, and this is the number to remember: **exactly two carves in the entire lane need a citation; every other one converts.** A decomposition a program cannot prove is one it had no business asserting.

The three probes the ruling asked for all landed: an uncited carve is REJECTED ("premise (3) may not impose it by refining a telescope parameter's σ"); a *wrongly* cited one is rejected on the citation's **type**, so the equation is a license and not a token; the cited caller is accepted *and executes*, restoring the differential property for this shape; and the original counterexample — `n = 2` with `i = j = 5` — is now rejected **at its own boundary**, because `Refl` cannot inhabit `Id Nat 2 (add 5 (S 5))`. The constraint is recorded in the signature it violates, which is the whole point.

A note for the mechanizer, since it is where a plausible implementation would go wrong: refining `σ_m` is a refinement of a **length index**, not of a value snapshot, and it must go through `refineSym` like any other — reaching Ω, `sctx`, obligations, group owed types, `retTyVal`, `selfBack`, and **`selfRec`**, per the M10 "refinement reaches all σ-bearing state" invariant.

That last member is why this deserves more than a passing mention. `St.selfRec` is the recursion guard's tracked decreasing snapshot (§8), and it joined `refineSym`'s target list only recently. A carve whose index refinement reached every component *except* that one would not fail loudly — it would silently corrupt the termination guard for **any function recursing on an array**, which is to say for the entire class of program this design exists to serve. The guard compares the actual at the declared decreasing position against a snapshot; leave that snapshot un-refined while the length index moves underneath it and the comparison is being made against a value that no longer exists.

What keeps this a single invariant rather than a per-feature audit is §9's swept-state principle: *any checker component that must observe a value across a refinement has to live in the σ-bearing state `refineSym` sweeps.* The carve's index refinement is that principle's fifth independent consumer, after obligations, instantiated call types, `retTyVal`/`selfBack`, and the recursion guard. The practical form is worth stating flatly for whoever implements: **`refineSym`'s target list is the checklist** — not a list to reason about case by case, but the one place to look, and the one place a new `St` field must be added. It satisfies §3.2's knowledge/state assertion trivially (`add lo′ (add cnt rest)` is marker-free), which is worth *checking* rather than assuming: this is the first refinement in the calculus fired by an **ownership** operation rather than by a match, and the invariant's whole point is that ownership operations must not smuggle state into σ's. They do not here — the substituted term is arithmetic, and it is true of the value timelessly.

**The effect.** `L`'s segment is replaced by three, with the extents premise (3) produced: `lo′`, `cnt`, `rest`. The bodies follow the body of `L`:

* `L = [v₁ … v_m]` (an owned literal run): split the run positionally.
* `L = σ`: refine `σ := arrCat σ₁ (arrCat σ₂ σ₃)` with `σ₁ : Array lo′ T`, `σ₂ : Array cnt T`, `σ₃ : Array rest T` fresh — again ordinary ⇜, again marker-free, again knowledge (the array *is* the concatenation of its parts, at entry and forever).

Degenerate carves are no-ops (and skip the ownership test — R6, above): when the request coincides with the leaf, no split and no refinement happen at all. This matters for `split_at_mut` (¶5), whose second borrow is always degenerate.

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
// CORRECTED (C2) — the draft ended ℓ here. It does not.
// §2.2 ends "every loan marker in owned position WITHIN THE VALUE IT IS ABOUT
// TO MOVE", and the value about to move is one element, which carries no marker.
// So the read succeeds, m STAYS LIVE, and Nat being index-kind it copies:
// Ω = a ↦ Arr⟨1 ▷ [3], 2 ▷ loanₘ ℓ⟩, m ↦ borrowₘ ℓ (Arr⟨2 ▷ [7,2]⟩), x ↦ 3
let y = a;                          // NOW the whole array moves
// forced: End-Mut ℓ — the payload plugs into the marker, m dies, then merge
// Ω = a ↦ ⊥, m ↦ ⊥, y ↦ Arr⟨3 ▷ [3,7,2]⟩
```

That correction is worth more than its size. Implementing §2.2 *precisely* gives strictly more than the draft's trace claimed: **an element and a disjoint range of one array, both live simultaneously** — which is this document's headline arriving a full paragraph before ¶3.4 sets out to demonstrate it. The draft was not describing a limitation of the design; it was describing a rule it had applied too eagerly. Rejoin is unaffected and is now shown on the demand that genuinely wants the whole array.

Every step after the carve is a rule that already exists. End-Mut is End-Mut — a ⇐-fill at the marker plus the kill (§2.2). The forcing is §2.2's owned-position rule verbatim: a marker inside a segment body is in owned position of `a`'s value, so a demand for `a` ends it, innermost first. Drop (§2.3) needs no new case: an array node being displaced is a value with markers in owned position, and drop's total procedure ends them and discards the rest.

**Rejoin is merge.** There is no rejoin rule. When the last marker under an array node is gone, the merge normalization collapses the segments, and the array is a run again — indistinguishable from one that was never carved. That is the property the segment representation was chosen for (¶1.1).

*A previous amendment to this section warned that merge "must be robust to being triggered mid-body by a comptime read, not only by owner demand or the boundary", and listed the trigger sites. **The implementation dissolved the warning rather than satisfying it (R3), and the way it did so is the better lesson**: the way to be robust to a trigger list is to not have one.* Merge is a **read-normalization**. Every carve merges before it scans; every place operation merges after it finishes; and **rejoin is merge at `sendPayloadToLoan`** — the single moment a payload plugs back into its marker, which every End-Mut path funnels through, whether it originates at an owner demand, at the §5.4 audit collapse, or at a §6.1 group release. No site can be forgotten because no site is listed. An enumerated-trigger design would have been correct on the day it was written and wrong on the first site added afterwards; this one cannot be.

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
  //   obligation:  Le Z σₙ × Le σₖ σₙ  (leaf-relative, R7) — discharged by h ✓
  //   offset:      le_split on the first component ⇒ lo′ = Z (nothing to do)
  //   residue:     le_split on the second ⇒ rest, with Id σₙ (add σₖ rest);
  //                σₙ is flex ⇒ the refl-match solution transition refines
  //                σₙ := add σₖ rest, EVERYWHERE (Ω, sctx, obligations, retTyVal…)
  //   split of σ:  ⇜ refines σ := arrCat σ_l σ_r  (σ_l : Array σₖ, σ_r : Array rest)
  // Ω = a ↦ borrowₘ ℓ₀ (Arr⟨σₖ ▷ loanₘ ℓ₁, rest ▷ σ_r⟩)      [suspended]
  //     l ↦ borrowₘ ℓ₁ (σ_l : Array σₖ Nat)

  let r = &mut (*a)[k ; rest];
  // carve at (σₖ, rest): the extent scan finds the leaf at exactly (σₖ, rest)
  //   DEGENERATE: request = leaf, so premise (2) and the ownership test are
  //   skipped entirely (R6), and no split and no refinement fire
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

* **Overlap.** `let p = &mut a[0 ; 3]; let q = &mut a[2 ; 3];` — after the first carve the extent map is `[(0,3,loaned ℓ₁), (3,rest,owned)]`, and `[2,5)` is contained in **neither leaf**: it straddles the boundary. Premise (1) fails, and the rejection is simply "no leaf contains it".

  *Corrected (C3): no owned-versus-loaned test is involved.* The draft reasoned that no *owned* leaf contains the request. That test is unnecessary — two segments cannot overlap, so a range crossing a segment boundary has no leaf at all, whatever its status. The rejection is cheaper than the draft claimed, and it is a nicer fact besides: overlap is refused by the *partition* rather than by an ownership check on top of it. (C4 above is the complement: a request contained **within** one loaned leaf is not overlap at all, and demand-ends instead of rejecting.)
* **Out of range.** `&mut a[lo ; cnt]` with `add lo cnt > n` — premise (2) has no inhabitant, and none can be supplied, because `Le (add lo cnt) n` computes to `⊥`.
* **Unproved bound.** The same obligation, symbolic, with no evidence cited — premise (2) fails for want of a term. This is the *interesting* rejection: the program is not wrong, it is unjustified. The fix is to thread the bound, which is what the north star's `hbnd` already is.
* **Rigid length.** Premise (3) is stuck. Reject, with the remedy in the message.

And one non-rejection worth naming, because it is the one Rust cannot express: **an interior range and a suffix range of one array, taken in either order, both live, both writable.** That is `split_at_mut`'s generalization, and here it is not a library function with an `unsafe` interior but two applications of one rule.

**A note on what this replaces.** M13 recorded the finding that "two sequential `nth` calls CANNOT give two live cursors; one call returning the pair is the answer to disjointness," and built `nth2` accordingly. That finding was about *calls*: each `nth` consumes the whole borrow into a group, so the second has nothing left to take. It was never about disjointness as such — the two cursors `nth2` returns are disjoint *structurally*, because they land in different `Cons` cells, and the checker knows this without being told. What `nth2`'s signature carries is

```rust
nth2 (v : &mut List Nat, i : Nat, j : Nat, pij : Le (S i) j, p2 : Le (S j) (len *v)) → …
```

— and `pij : Le (S i) j` together with `p2 : Le (S j) (len *v)` is, on the nose, the containment obligation the carve rule demands of two element ranges at `i` and `j`. The evidence has been threaded through every swap site since M13, discharging a different job: making the recursion's `botElim` branches type-check. Range places take the same terms and give them their real job, and the "one call returning a pair" workaround dissolves, because a *place* borrow consumes nothing and two of them need no call at all.

**Half of that came true literally, and half of it is refuted. Both matter.**

*Vindicated (R7):* the obligation the carve forms at `a[i]` **is** `Le (S i) n`, character for character the term the swap sites have threaded since M13 — but only once premise (2)'s spelling is fixed. Written the obvious way it was `Le (add i (S Z)) n`, and this paragraph's central claim would have been false in the one place it was supposed to be exact.

*Refuted (R13):* **two independent symbolic indices into one array are unreachable, so `swap(a[i], a[j])` at two runtime cursors is not writable at all.** This was probed with M13's terms verbatim, `pij` and `pjn` — precisely the ones promised their "real job" above. `(*a)[i | h]` works. The second read does not. After the first carve the leaves are `[0,i)`, `[i,i+1)`, `[S i, rest)`; the second request lands in the third, so premise (2) is formed **leaf-relatively** against an offset `d` the machine minted while solving `j ≡ add (S i) d` — and no program term can have type `Le (S d) rest`, because `d` has no surface name. **That is G1's wall arriving at the OFFSET rather than the extent**, and route (a) closes only the extent half. Route (a) cannot rescue it either: the second request does not *start* a segment, so there is no leaf for a supplied residue to decompose.

So the honest statement is narrower than the draft's. Two disjoint range borrows of one array: yes, that is ¶3.4, built and running. Two *element* cursors at independently-computed symbolic indices: no. What is writable is a scan in which **every element access is at index 0 of a segment the program itself carved** — and ¶6 says "the right sub-slice is a segment with its own zero; there is no reindexing" as though it were a convenience, when it is a *hard constraint that determines the algorithm*. ¶6 records what that cost.

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

The over-approximation §6.1 already flags (a group releases atomically where the concrete machine ends lazily) acquires a new instance here — several captured loans in one owner. **The draft added "but not a new character; any simulation relation that reconciled the old case reconciles this one." That sentence was rhetorical, and it was wrong twice.**

#### The relation had to be extended, and its correctness now depends on ¶8.2's obligation 4 (R9)

Arrays are the first values in this calculus whose **state form is coarser than their value**. Merge concatenates runs but must leave a σ body alone (¶1.1's R4), so a checking-mode group release — a fresh existential at the segment's owed type — *blocks* exactly the rejoin the concrete run performs. Checking mode ends at `Arr⟨1 ▷ [3], 1 ▷ σ₀, 1 ▷ [2]⟩` where executing mode ends at `[3, 9, 2]`, and **both are right**. The relation's array case now splits a concrete run along the symbolic extents and matches segment-wise.

The consequence deserves alarm rather than a footnote, and is flagged for whoever writes the metatheory: **¶8.2's obligation 4 (merge is value-preserving) is no longer an item on a list — it is a premise of the differential harness's own correctness.** The relation's array case is *defined* by that splitting, which is sound exactly when merge preserves values. If obligation 4 fails, the harness does not go red. **It goes silently green on a mismatch.** That inversion is the thing to know before trusting the differential over any array body.

#### The polarity finding: the first time the CONCRETE side was the wrong one (C9)

§6.1 flags the group-release approximation as a *checking-side* over-approximation, and every prior member of that family has been one. This is not.

In executing mode a carving callee left the caller's array segmented, and the caller's next carve then read the wrong leaf: the array quicksort type-checked and **could not be run**. Checking mode never saw it, because §6.2's opacity re-mints the callee's payload as a fresh σ at the declared type, so the caller always sees an *uncarved* array.

> The re-mint is not an approximation of what execution does. It is a **repair** of it. The checker was right and the machine was wrong, and no amount of checking could have revealed that.

That is the strongest argument this document's differential-first stance has ever received, and it was not available from the desk. A design note can reason about whether the checker over-approximates the machine; it cannot discover that the machine is the one that is broken.

**The root was ¶1.1's `drop-empty`, in four independent sites.** The normalization discards a zero-extent segment and unwraps a lone survivor, and the rest of the machine depends on the structure it discards. Every site is unreachable **symbolically** — a residue σ is never *known* to be zero — and routine **concretely**, since a runtime-computed split has an empty side constantly. That asymmetry is exactly why the symbolic suite stayed green throughout, and it is the general hazard: a normalization justified on symbolic values, applied to concrete ones.

1. **Leaf-selection collision** — closed as C7 above. Written for the citation path, load-bearing here: without it, keeping zero-extent segments at all is unusable.
2. **The lone-survivor unwrap** — a node whose only surviving segment was one live borrow collapsed to a bare `loanₘ ℓ`, and the next carve's demand-end, *doing precisely what §5.2 says*, ended that borrow. A survivor carrying a marker is now kept. One line, ungated: the full suite is green with zero test edits, so it is not merely checking-identical but **mode-independent**.
3. **The dropped residue piece** — a carve discarded a zero-extent residue, leaving no segment at that base for a later request to name. Kept, but **executing-gated**: keeping it unconditionally stops all three programs checking. This is the one place the two modes genuinely want different value trees.
4. **The abutting zero-width request** — `Le (add lo Z) (add b m)` holds at a leaf's *far end*, so a zero-width request (which is what an empty right half is) selected the leaf it abuts and demand-ended the borrow pinned there. A zero-width request now gets its own zero-extent segment, inserted without touching any leaf.

Plus the mechanism those four were hiding: a **scope-aware release at call return** (executing only), ending loans held by slots at or above the callee's frame offset while keeping any the result issues. Measured necessary — removing it once all four sites are closed puts the differential back in the red.

**Result: the array quicksort runs.** `[3,1,4,1,5,9,2]` sorts to `[1,1,2,3,4,5,9]`, and the cross-differential against M23's List quicksort is green on eleven shared inputs — two implementations sharing no code, no predicates and no container, agreeing with each other and with a trusted sort.

*A method note, recorded because it is the transferable part.* Three scope-aware releases were built and all three failed before the diagnosis was right, and each failure was read as "architectural" until the navigation error was instrumented to **name the dying borrow**. The investigation twice recorded a conclusion a later probe refuted. What finally worked was **counting sites rather than estimating effort**: each site is small, and there is reliably one more than you think.

### 3.7 Interaction with the §5.4 audit

The audit is unchanged in structure and gains one obligation in substance.

`collapseArg` already End-Muts every loan marker in an argument borrow's payload; markers inside segment bodies are found by the same traversal (a segment is an ordinary node with the marker in a field), so §3.3's field-loan collapse and a carve's range-loan collapse are the same code path — as §2.2 promised when it generalized owned position.

What is new is that the collapsed payload is a *segment list*, and the owed type is `Array n T`. Conversion must therefore see through the fold: `⇝` of `Arr⟨c₁ ▷ b₁, …⟩` is `arrCat b₁ (arrCat b₂ …)`, `arrCat` computes on run-headed arguments, and stays neutral on σ's. The audit's conversion then succeeds definitionally precisely when the extents add up definitionally — which premise (3) arranged. This is the single place where the residue-transition decision pays out, and it pays out at every array-mutating function in the program.

**And there is a second place the fold has to happen, which the draft missed entirely (C5).** §5.4's *exit-snapshot substitution* — the one that defines `σ_exit` as the borrow's collapsed final payload — injected that payload **raw**. So after any carve, the exit snapshot of `*v` was a `§segs` node, while `countA`/`SortedA`/`UbA` are `arrRec`s that compute on the cons view and are stuck on one. **Every postcondition naming `*v` was unstateable**, with a rejection that reads like the predicate being wrong rather than the snapshot being in the wrong form. The fix is one word — fold before substituting — and an unfoldable (still suspended) payload is left alone and rejected at `hasType`, the documented behaviour, so nothing became more permissive.

*Why it hid until a real program existed* is the part worth recording, because it is the same hazard as ¶3.6's four sites. Merge concatenates adjacent **runs** and deliberately leaves a σ body alone (R4). A carve at **concrete** extents therefore rejoins to a plain run and never needs the fold — which is every test written before the quicksort, the two-element sort included. A **symbolic** segment cannot merge, and that is what every program with a runtime-computed split point is made of. R9's "arrays are the first values whose state form is coarser than their value" had exactly one consumer, and it had never been exercised.

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

*Amended (G2): "no new type" is right; "no new machinery" would not have been.* The type is indeed well-formed, but the machine had never seen **a borrow under a type constructor at a telescope position** — §5's own second opacity, declared and never exercised. It is now built on both sides and green: the telescope seeds the parameter as a genuine pair (a length σ the body can name, plus a borrow carrying an ordinary obligation), a call site captures the borrow's loan while checking the length like any other argument, and a callee destructures with an ordinary owned match. This is ¶4's runtime-length slice, delivered.

*And it does **not** solve the residue-naming problem, which is what the probe was for.* A caller must **produce** the length to construct the pair, so the Σ-slice serves exactly those slices whose length was already nameable — the case that never needed it. Passing an unnamed residue is rejected, correctly, and no right term exists to write. A second, independent wall: a *recursive* slice-taking callee needs a fuel bound **about** the slice's length, and that length lives inside the Σ where no telescope entry can mention it. Route (a) is the answer to residue naming; the Σ-slice is a useful thing that is not that answer.

What a primitive slice would buy is nothing the above does not, and what it would cost is a second former with its own subtyping story against arrays. Decline. The one honest gap: **shared slices (`&[T]`) need shared borrows**, which are deferred wholesale with §10, and the design below says nothing about them beyond the observation in ¶8 that read-only sharing needs no disjointness proof at all and should be strictly easier when it arrives.

---

## ¶5. `split_at_mut`, and why it needs no trust

```rust
fn split_at_mut (a : &mut Array n T, k : Nat, h : Le k n)
    -> Σ (l : &mut (Array k T)). &mut (Array (sub n k) T)
  = Pair( &mut (*a)[Z ; k | h] ,
          &mut (*a)[k ; rest] )
```

with the return type more honestly written after the carve has run, as `Σ (l : &mut (Array k T)). &mut (Array rest T)` where `rest` is the residue the carve introduced — the `sub` in the signature above is the caller-facing spelling and, per ¶2.1, is sugar the callee never sees.

**Checking story**, step by step, and every step is a rule already stated:

1. The first borrow carves at `(Z, k)`. Obligation `Le Z Z × Le (add Z k) n ≡ ⊤ × Le k n`, discharged by `h`. Residue transition refines `σₙ := add k rest`.
2. The second borrow carves at `(k, rest)`. The extent scan finds the owned leaf at exactly `(k, rest)` — degenerate, no split, obligation by `le_refl`. **The second half is free.**
3. Both borrows are issued into the result, so the return is a §6.1 multi-issued group: two issued loans, one captured (`a`), exactly `nth2`'s shape (§6.1 names `nth2` "this calculus's `split_at_mut`" — the name is now literal).
4. The callee audit (§6.1's per-branch rule) exempts `a`: it is the captured owner of both field reborrows, reached by `reachesLoan` through the markers parked in its payload. The two issued payloads are audited against `Array k T` and `Array rest T`, which they hold by construction.

**Why no `unsafe`.** Rust's `split_at_mut` is raw pointers inside because both halves would be reborrows through the same place `*self`, with no distinguishing projection — and `places_conflict` classifies two runtime-indexed projections as conflicting under the borrow-checking bias (¶7). The ranges genuinely are disjoint; what fails is that no *type* records it. Rust's escape is to move ownership of `&mut self` **into** the call so that the checker sees a move and two unrelated returns rather than two reborrows, with the actual argument audited once inside an `unsafe` block.

Here the two borrows are not two borrows of one place. After the carve they are borrows of two *different segments*, which are different subterms of one value tree — `Disj` in the `PathToSubtree` trichotomy sense (¶3.1) — and the ownership machinery cannot represent them overlapping. The `Le` proof was consumed at step 1 to license the reorganization; from step 2 onward disjointness is not a claim being trusted but a shape being read. **The trust Rust localizes in an `unsafe` block is here discharged by one `Le` term at one carve** — and, unlike `get_disjoint_mut`'s runtime pairwise check, it is discharged before the program runs and cannot fail at run time.

**Caveat, stated because ¶3.6 makes it matter.** Calling `split_at_mut` is not the same as carving inline. The call mints a group, and a group is §6.2's opacity: at the group's end the caller learns only what the signature says. An *inline* pair of carves keeps everything transparent — the residues stay pinned, the sub-borrows' work is visible to the enclosing body. This document therefore gave the following advice, and gave it as a recommendation rather than an observation:

> ~~So the advice the calculus should give is the opposite of Rust's: **carve inline; reach for the function only when you want the abstraction boundary**, and pay §6.2's spectrum when you do.~~

### 5.1 CORRECTION: that advice is inverted (R12)

**The recommendation above is withdrawn.** Not softened, not qualified — reversed. In the built array quicksort the function boundary is not an abstraction you pay for when you happen to want one; **it is what makes the program possible at all**, and a body that follows the struck-out advice cannot be written.

The reason was not visible from the desk, and it is a two-step trap:

1. A body that peels a head must first match its own length (`match n { S(m2) => … }`), because only the supplied-residue form converts against the resulting rigid extent — the index place `a[i]` has no residue slot and is rejected outright.
2. But matching the length is exactly what T2's rigid-extent restriction then punishes: from that moment the array can no longer be carved at a symbolic offset.

**So one body cannot both select a pivot and carve at the returned index.** Inlining is not a transparency-versus-abstraction trade here. It is a dead end.

§6.2's opacity is the way out, and it is the *only* way out. A call re-mints the caller's payload as a fresh σ at the declared type, so an array the callee matched, peeled and re-carved comes back **uncarved and with a flex length** — precisely the state a three-way carve needs. The partition is a separate declaration for that reason, and not for modularity.

The corrected advice, then: **reach for the function boundary when a body would otherwise have to both rigidify an extent and carve at a symbolic offset** — which, for any program that computes a split point and then recurses on the pieces, is always. Carve inline within a single rigidity regime; cross a boundary to change regimes. Opacity is normally the thing this calculus works around; twice now it has turned out to be doing real work — here, and in ¶3.6's polarity finding, where the same re-mint repairs the executing machine rather than merely forgetting for the checker.

---

## ¶6. Migration: what the M23 quicksort becomes

The exercise that makes this concrete. Today's north star, with the pieces that change marked:

```rust
fn quicksortSorted (v : &mut List Nat, fuel : Nat, lo : Nat, cnt : Nat,
                    hfuel : Le cnt fuel, hbnd : Le (add lo cnt) (len *v))
  -> Σ (sortedpart : SortedR cnt lo (*v)). (Π (n : Nat) → Id Nat (count n (*v)) (count n (old *v)))
```

and after migration:

```rust
fn quicksort (v : &mut Array n Nat, fuel : Nat, hfuel : Le n fuel)
  -> Σ (_ : Sorted (*v)). (Π (x : Nat) → Id Nat (count x (*v)) (count x (old *v)))
{ match fuel {
    Z => …,                              // n ≤ 0 by hfuel: the array is empty, Sorted ⋆
    S(f2) => {
      let p = partition(v);              // the pivot index AND the right half's length
      match p { Pair(i, Pair(j, hlen)) => {
        // the three-way carve, in this document's own notation — and it is what landed:
        let left  = &mut (*v)[Z   ; i ; S j | le_add i (S j) | hlen];
        let pivot = &mut (*v)[i   ; 1 ; j];       // obligation ⊤ — no evidence needed
        let right = &mut (*v)[S i ; j];
        let cl = quicksort(left,  f2, …);
        let cr = quicksort(right, f2, …);
        Pair(sorted_arrCat … cl … cr … , perm_arrCat … cl … cr …)
      } }
    }
} }
```

Note what the recursive calls' arguments are: sub-slices, with no offsets and no counts. `quicksort` sorts *its argument*, entire.

*Three amendments are already visible in that sketch, and each is developed below:* the partition returns **two** numbers, not an index and a license (G3); the three-way carve is one carve of each piece rather than a two-way split re-associated (T2); and the first piece cites `hlen`, because premise (3) may not refine the parameter `n` on its own authority (C8). Two other things the draft's sketch got wrong survive only as corrections in the ledger below: `match fuel` **consumes** `fuel`, and the emptiness test cannot be `match n` at all (R14).

**What disappears.**

* `lo` and `cnt` — both parameters, and every occurrence of them in every predicate and lemma. The callee sorts *the whole of its argument*, because its argument is the segment.
* `hbnd : Le (add lo cnt) (len *v)` as a *precondition of a model function* — it survives, but transformed: it is now the *license for the carve* at the recursive call site, and it is consumed there rather than threaded into a pure lemma. Same term, different job.
* The range-scoped predicate family. `SortedR cnt lo l` becomes `Sorted a`. `AllLeR`/`AllGtR` become `AllLe`/`AllGt`. The bounded-Π encoding (`Π k. Le (S k) w → …`) that M22-c adopted *because* the comptime Σ-eliminator is missing was forced by the need to quantify over positions *within a range of a bigger list*; over a whole array there is no range to quantify within, and the predicates return to their direct recursive form. (The missing Σ-eliminator remains a real gap for other reasons — §9's list — but it stops distorting these definitions.)
* The permutation-survival keystone. M22-c's hardest single result — that positional `AllLeR` is not permutation-invariant, so bounds must be routed through the multiset predicates `noAbove`/`noBelow`, with off-end positions reading `Z` and the range-fits bound carried through three lemmas — exists entirely because "the range [lo, lo+cnt) of this list" is not permutation-stable when the *list* is what gets permuted. Sorting a segment permutes the segment. The keystone's problem statement does not arise.
* Every length-preservation lemma: `len_partitionRangeL`, `len_sortRangeL`, and the `le_rw_l`/`le_rw_r` transport chains built on them — roughly thirty lines of the current quicksort body, visible at `S19Partition.lean:692-714`. A borrow of type `&mut (Array n Nat ↝ Array n Nat)` *cannot* change the length; the audit enforces it; nothing needs proving.
* The right-segment reindex and its lemma-guarded subtraction (the M22-c diary's named tax). The right sub-slice is a segment with its own zero; there is no reindexing.

**What survives untouched.**

> **CORRECTION to this heading, before its list (G4).** The three-way framing — *what disappears / what survives untouched / what gets built* — is where this section's largest error lives, and it lives in the framing rather than in any sentence, which is why it took a built program to surface. The list below is accurate about the **predicate strata**. It is silent about the **leaf program**, and silence in a "what survives" list reads as survival. It does not survive: **the partition does not transfer at all.** M23's partition is a relational take-and-rebuild over a linked list returning two lists *by value* — §4.1's idiom, which this document's own text endorses. The array quicksort needs the opposite: an in-place scan returning a pivot *index*, because the recursive calls carve at that index. There is no list program to port. Cost 4 below measures it.

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

Set `append ↦ arrCat` and `Cons p b ↦ arrCat (asingle p) r` and it *is* the array lemma, hypothesis for hypothesis — not merely the same shape but the same statement modulo the container, with `Ub`/`Lb` already playing the roles this document called `AllLe`/`AllGt`. So the migration **inherits** that proof rather than opening a stratum. Verified: it is one of R11's twenty-one, and it transferred by container swap alone.

### 6.1 CORRECTION: the headline accounting was wrong by one stratum (R15)

This document's most-quoted single claim — the one the previous amendment pass sharpened and called "the crispest form the migration argument has taken" — was:

> ~~Claim exactly that and no wider: **one stratum deleted outright** (locality), **one inherited** (the pivot glue), **none invented**.~~

**The first two are verified. The third is false, and it is withdrawn.** The corrected claim is:

> **One stratum deleted, one inherited, ONE INVENTED — at the leaf's interface.**

The reason is instructive rather than embarrassing, and it sharpens the design's real boundary rather than blunting it.

A split point is a statement about two parts of one array, and the honest way to name the parts is to carve — which is this document's whole claim, and it **holds for the sort**, whose sub-slices are its own carves. It does **not** hold across a *function boundary*, for three independent reasons, each probed: the return type is fixed before the carve that would name the parts exists; `Array n` and `Array (add k r)` convert only after the *caller's* carve has refined `n`, so the equation cannot even be **stated** in the signature; and the parts cannot be returned by value either, because reading a segment **moves** it and leaves the borrow holding a hole.

So the partition's interface needs one positional predicate for the scan and one for its result, plus five crossing lemmas — a stratum, invented, that no amount of carving inside the sort removes.

The invented stratum is small, for a reason worth keeping: the result predicate's skip-zero case yields `LbA`, the *library* predicate, so the bridge to `sorted_arrCat` is a single lemma with no monotonicity layer. Every crossing is an induction on the left array and nothing else, the same `arrRec` shape as `bound_arrCat`. The stratum is new; the **kind** of work is not.

**What the correction sharpens.** "None invented" claimed that carving dissolves positional reasoning outright. It does not — it dissolves it *within a body*, and hands it back at every **function boundary**, because a signature must describe a split that only the caller's carve can name. That is a more precise and more useful statement than the one it replaces: the design's benefit is scoped to a rigidity regime, exactly as ¶5's corrected advice says from the other direction. Both corrections are the same fact seen twice — **carving is a within-body mechanism, and boundaries are where its guarantees stop and start again.**

**What gets built.** The glue moves from index arithmetic to concatenation:

```
    sorted_arrCat : Π (l r : Array _ Nat) (p : Nat) →
                      Sorted l → Ub p l → Sorted r → Lb p r
                    → Sorted (arrCat l (arrCat (asingle p) r))
```

— deliberately written in `sorted_append_pivot`'s own binder order and vocabulary, since the point is that it is that lemma with the container swapped. This is the textbook quicksort correctness statement, in the textbook shape. M22-c's `glue` — a nested `leb`-elim dispatcher over three directional lemmas with a subtraction-guarded reindex — is what the same content looks like when the concatenation is simulated by indices into a larger list.

**Honest accounting of the migration's own cost.** The draft listed three things that get harder. There are **five**, the largest of them unlisted, and the three it did list need amending.

1. **The partition must return the pivot index *and* the residue extents — not licenses (G3).** The draft said it must return the index "together with the two carve licenses (`Le i n` and its complement)". A license alone **cannot be stated**, because the thing it would have to be a license *about* — the extent of what is left after the first carve — is a σ the checker minted and no program can name. With route (a) the shape is: the partition returns the pivot index `i` **and the right half's length `j`**, and the caller carves `[Z ; i ; S j | le_add i (S j)]`, `[i ; 1 ; j]`, `[S i ; j]`. The first license is `le_add`, which the M22 library already had; the second is ⊤. Cheaper than the draft feared, and differently shaped.

2. **Both sub-slices carved before either call** — as drafted, and confirmed. The pivot element sits between two live borrows as a third segment neither call can see, which is correct: the pivot is in its final position and must not move, and the calculus enforces that for free by the same mechanism that keeps the halves apart. What the draft did not know is that a three-way carve **cannot be reached by re-associating a two-way one** (T2), so this is not a convenience — it is the only route.

3. **The pure library's array layer is mechanical, and measured so.** Twenty-one items, container swap only, most first try (R11 in ¶1.3). The draft's "call it a week of the kind of work M16–M18 showed is mechanical" was right, with the one omission R10 records: three ι-rules are what make it mechanical rather than merely possible.

4. **THE PARTITION DOES NOT TRANSFER. It is a new program (G4)** — and this is the largest of the five, unlisted because the ledger's "what disappears / survives / gets built" framing quietly counted the leaf as surviving. M23's partition is a relational take-and-rebuild over a linked list returning two lists **by value** — §4.1's idiom, which this document's own text endorses. The array quicksort needs the opposite: an **in-place scan returning a pivot index**, because the recursive calls carve at that index. There is no list program to port.

   Measured (R17): the partition layer is **21 new pure items** (2 predicates, 5 crossings, 8 projections, 4 count lemmas, 2 nil lemmas) plus three declarations, and **every pure item checked first try**. The programs did not — but every program failure was a machine gap (C5, C6, C7) or a spelling (R7's `S k` versus `add k 1`). *Nothing in the mathematics was hard; everything in the plumbing was new.* That is the shape of this whole lane in one line.

   And R13 determines the algorithm, not merely its difficulty: two independent symbolic cursors are unreachable, so **Lomuto's inner loop is not writable at all**. What is writable is a scan where every element access is at index 0 of a segment the program carved — so the built splitter peels the head, splits the tail recursively, and performs at most **one swap per level**, with the boundary element reached by a three-way carve so that both sides of the exchange sit at their own segment's zero.

5. **The staging tax, counted rather than estimated (R16).** Six filings for `old`-on-consumed-things now exist; the array quicksort's body carries **four staged builders** and the splitter one, against four in M23's list quicksort. None does mathematical work.

   The strongest single case: the permutation conjunct's far endpoint is `countA q n (old *a)`, `id_trans` takes its three points explicitly, and **no body term can write `old *a`** — so the endpoint must be captured in a closure built before the partition call, while `*a` still *is* the entry value. Two further consumption facts cost a debugging cycle each and belong beside it: `match fuel { S(f2) => … }` **consumes** `fuel`, and passing a **proof** to a call **moves** it, so the fuel bound must be captured before the partition takes it. M23's list quicksort hit neither, because it never mentions `fuel` after the match and its partition takes no proof.

**One more thing the draft could not have known (R14): there is no η at length zero, so a sort's base case is a lemma.** `SortedA Z σ` is a stuck `arrRec` — the recursor fires on the array constructor, never on the length index — so an opaque length-zero payload does not compute to `Unit`, and a base case cannot be discharged by the trivial term. Two nil lemmas carry `Id Nat n Z` and kill the cons case by no-confusion. This also determines how the sort tests emptiness: `match n` would refine the length to `S m2` and thereby block the three-way carve (T2), so the built sort branches on `leb 1 n` and converts `Le n Z` into `Id Nat n Z`. **Every list program in the corpus matches its scrutinee; the array sort cannot** — which is as clean a statement as exists of what changes when the container carries its length in its type.

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
| `arrCat`, `arrRec`, `aget`, `acons` | computing constants in the basis (no `T` on the first and last — C1) |
| index step `[t]`, range step `[t ; t′ ; t″ \| e \| eq]` | place-path grammar, three optional slots |
| CARVE | one reorganization, three premises |
| **`Le` and `add` move into the kernel** | *added by the implementation* — R1 |

Six entries now, of which exactly one — CARVE — has semantic content. The rest are representation. That ratio was the design's main defence and it survived: nothing in the borrow machinery changed, because the carve's job is to hand the *existing* machinery a tree it already knows how to handle.

**The one addition the draft did not foresee (R1).** `Le` and `add` had to move from the library into the kernel, because the carve's premises are *stated* against both — premise (2) **is** a `Le`, premise (3) decomposes an extent with `add` — and a kernel rule cannot cite a library it does not import. The forcing argument is sharper than mere layering: two syntactically different `add`s would never convert, which would break exactly the conversion the residue-transition decision exists to make definitional. This is recorded as §9's filed "`Le` as a primitive former" pressure arriving from a **second independent direction**, which strengthens that filing rather than settling it.

Two §7 obligations come along with basis membership and must be *written* rather than *generated*, which is the concrete form of ¶9(c)'s worry. **`Array.copy`**: §7.2's consume-and-rebuild, over the cons view, calling `T.copy` per element — which means §7.2's derivability fact ("τ is unrestricted iff `τ.copy` is generatable") continues to hold for arrays only by hand-checked coincidence rather than by construction. **The unrestricted classification**: `Array n T` is unrestricted iff `T` is, which is the same rule §7.1 states for parameters, but stated again rather than computed. Neither is hard; both are drift surface.

### 8.2 Soundness obligations created

For whoever writes the metatheory, the new proof burden in full:

1. **Carve is snapshot-preserving.** `⇝(carve(A, lo, cnt)) = ⇝(A)`. This is `arrCat_take_drop` (¶1.3) and nothing more. It is the one obligation that is genuinely about arrays.
2. **Carve's refinements are knowledge, not state.** Two refinements fire: the index refinement `σ_m := add lo′ (add cnt rest)` and the value refinement `σ := arrCat σ₁ (arrCat σ₂ σ₃)`. Both substituends are marker-free, so §3.2's asserted invariant holds — but this is the first ownership operation that refines, and the assertion should be *exercised* on it rather than assumed to still hold.
3. **Range-loan collapse is owned-position collapse.** A marker in a segment body is in owned position; §2.2's move rule and §5.4's `collapseArg` reach it by the existing traversal. What must be checked is the *transitivity* invariant §5.3 records for executing mode ("any operation that hands out a value peeled from a demand-ended suspension must drive it to owned-marker-free normal form first"): a segment list can hold several markers at once, so a partial collapse is now easy to write by accident. Each executing former must preserve full collapse, and a negative test per rule branch — the M20 lesson — should cover the multi-marker case specifically.
4. **Merge is confluent and value-preserving. — PROMOTED: this is now a premise of the differential harness's own correctness, not an item on a list.** The draft called it "straightforward, but load-bearing". It is load-bearing in a worse way than that: the simulation relation's array case is *defined* by splitting a concrete run along the symbolic extents (R9, ¶3.6), which is sound exactly when merge preserves values. **If obligation 4 fails, the harness does not go red — it goes silently green on a mismatch.** Establish this one before trusting the differential over any array body.
5. **The group over-approximation, with several captured loans in one owner.** The draft called this "a new instance of §6.1's existing reconciliation problem, not a new problem." Half right. The arity is not new; the **polarity** is (¶3.6's C9). This is the first member of the family in which the *concrete* side was the wrong one, so a metatheory that assumes the checker always over-approximates the machine will not fit it.

Note what is *not* on the list: there is no disjointness soundness theorem, because there is no disjointness judgment. That absence is the design's point, and it survived implementation intact — the two soundness findings that did surface were about *evidence provenance* (C8) and *value-tree structure* (C9), neither about disjointness.

### 8.3 Erasure

Everything the design adds is comptime and erases. The length index is a §7.1 index position (erased). The `Le` evidence is a proof (erased). The residue's extent `rest` is a comptime `Nat` (erased). The **carve itself is erased entirely** — it rearranges the checker's bookkeeping and produces no runtime action, because at runtime an array is a contiguous buffer and a range borrow is a `(base + lo, cnt)` pair computed by two machine instructions. The segment list has no runtime existence at all; it is the compile-time record of who holds which part of a buffer that was never restructured.

This is the strongest single argument for the whole approach over the M23 stopgap: `split_off`/`append_back` genuinely mutate the runtime shape and walk `O(i)` cells. A carve compiles to pointer arithmetic, and rejoin compiles to nothing.

### 8.4 What stays out of scope

* **Growth and reallocation.** `Array n T` is fixed-length by construction. `Vec T` is `Σ (n : Nat). Array n T` plus a capacity discipline; push/pop and reallocation are a separate design, and the interesting part of them (proving `Vec`'s internals safe, per `what-is-ochre.md`'s first stated goal) presupposes this one.
* **Two-dimensional and strided views.** `Array n (Array m T)` works and carves at the outer level. A transposed or strided view is a *non-contiguous* range, which the segment representation cannot express, and which the extent-map disjointness argument would not survive. Out.
* **Shared borrows.** Deferred with §10. The observation to record: read-only sharing needs no *disjointness* at all — two shared range borrows may overlap freely — so of the carve's three premises, a shared carve keeps (2), the in-bounds obligation, and drops (1)'s requirement that the leaf be unloaned. Which strongly suggests shared slices are the easier half and should not be designed until the mutable rule has been built and lived with; the temptation to generalize premise (1) to a permission lattice up front should be resisted.
* **Non-contiguous and dynamic-shape ranges.** A range whose bounds are not comptime terms. Out by construction: the design's entire arithmetic lives in the comptime fragment.
* **Rigid extents — wider than "rigid-length signatures" (T2).** The draft stated this for a function's declared length and guessed the escape correctly: "name the equation and carry it, rather than solving it" is exactly route (a), now built. What the draft understated is the reach. The restriction applies to **every segment's extent**, not only an array's declared length: a segment whose extent is a constructor tree (`S i`) or a compound neutral (`add p q`) cannot be sub-carved at a symbolic offset. Consequences elsewhere in this note: a three-way carve cannot be reached by re-associating a two-way one, matching an array's length forecloses carving it in the same body (¶5's R12), and the sort cannot test emptiness with `match n` (¶6's R14).

* **Structural recursion through a carved payload (T1) — filed, not built.** §8's guard counts only constructor fields as subterms and deliberately refuses application spines. A carve's body split refines the payload σ to an `arrCat` **spine**, so from that moment no sub-slice is a structural predecessor of its parent. The built quicksort is unaffected — it decreases on `fuel`, which is M23's shape anyway — but "recurse on the sub-slice, no fuel needed" is closed unless the guard learns that `arrCat`'s array arguments are subterms of their concatenation. That is true, and specific to this former, which is why it is filed rather than dismissed.

---

## ¶9. The three decisions I was least sure of — and how they went

*Written before implementation; the verdicts are added from it. The scoreboard, first: **(a) was right in substance and wrong in authority**, and the correction is the lane's one soundness finding. **(b) held**, and the fourth position turned out to be the load-bearing one. **(c) held with a cost that was named accurately.***

Recorded for the user, plainly, in decreasing order of how much would have to change if they are wrong.

**(a) The residue transition — refining a *length index* to make the carve's arithmetic definitional (¶3.2, premise 3).** This is the most aggressive idea here and the one that buys the most: it deletes every `sub` from the design and makes the audit's rejoin conversion definitional rather than lemma-mediated. But it means the carve *refines the type index of an array from inside an ownership rule*, which is a new kind of act in this calculus — every prior refinement was fired by a match on a value. It restricts carving to arrays whose length is flexible (a bare σ), which pushes shape onto every signature. And I have argued, but not tested, that it respects §3.2's knowledge/state invariant. The conservative alternative is to compute the residue as `sub`, accept the arithmetic tax, and keep the ownership rules refinement-free. That alternative is strictly simpler and strictly more painful, and I do not know which way the milestone would break.

> **VERDICT: the mechanism was right; its authority was not.** No `sub` appears anywhere in the built system, the audit's rejoin conversion is definitional, and the knowledge/state invariant held — the substituted term is arithmetic and the assertion never fired. The worry I named was the wrong one. The real defect was that premise (3) refined a **universally quantified** length and *recorded nothing in the signature*, so callers were never held to the constraint the body imposed: `checkFn` accepted programs the concrete machine gets stuck on. The ruling — **refuse to refine a telescope-parameter σ; solve along a CITED equation** — restores it, at a measured cost of **two citations lane-wide**. See ¶3.2a.
>
> Worth naming as a lesson about this kind of document: I flagged the right decision as risky and then guessed wrong about *why*. The flag still did its job — it is what made the finding legible when it surfaced — but "I am unsure about X" is not the same as knowing which part of X will break, and a design note should not pretend otherwise.

**(b) How the residue is represented (¶1.1, ¶3.3).** This is the decision the survey shows is genuinely open, because **all the plausible answers exist in the wild** and they disagree:

* **One piece, possibly non-contiguous.** Verus's `PointsToRaw::split` returns the residue as `self.dom().difference(range)` — a single token over a set. Maximally general; costs the extent map its interval structure, and with it ¶3.1's cheapness.
* **Two pieces, prefix and suffix.** VST's `split3_array_at` and iterated Iris `array_app` both leave `take lo vs` and `drop hi vs` as two standalone assertions. This is the classical answer and the closest to what a proof engineer expects.
* **Implicit in the owner — the residue is never named.** Iris's `update_array` leaves only a magic wand; Aeneas leaves only a backward function; RustBelt *drops* the residue and recovers it from lifetime-death inheritance. Cheapest representation, and fatally wrong for us: you cannot hold two wands over one array and still have an array, which is exactly what two live range borrows require.

I chose a fourth position — **named, but living in the owner's value tree as segments** — which is prefix-and-suffix in substance while keeping both pieces attached to the thing they are pieces of. That is what makes ¶3.6's frame preservation automatic (the residues never leave, so nothing has to describe them) and what keeps merge able to erase the carve's history.

The survey's verdict on this point is worth quoting as evidence rather than reassurance: what VST — the system with the closest rules — lacks is exactly "hold `[lo₁,hi₁)` and `[lo₂,hi₂)` with the remainder implicitly retained by the owner." In VST the residues are standalone assertions that accumulate in the proof context and must be threaded by hand. So the fourth position is a real gap in the literature and not an oversight of mine. That is genuinely encouraging and genuinely not decisive: an unoccupied position in a well-explored field is either an insight or a place everyone else found a reason to avoid, and I cannot tell which from inside the design. This is the one I would most want a second opinion on before anyone implements.

> **VERDICT: held, and it is the load-bearing choice.** The owner-retained residue is what makes ¶3.6's frame preservation automatic and what let the sort's sub-slices be its own carves — the "one stratum deleted" half of ¶6's accounting, verified. Nobody else occupying the position turned out to be opportunity rather than warning.
>
> Two costs arrived that the entry did not anticipate, both from the *segment list* half rather than the *owner-retained* half. Keeping extents in the tree means keeping **zero-extent** segments meaningful, and discarding them is the root of all four sites in ¶3.6's polarity finding — a normalization justified on symbolic values and wrong on concrete ones. And "only runs merge" (R4) makes the checking and executing modes end at genuinely different value trees, which is what forced the simulation relation to compare arrays up to the fold and promoted ¶8.2's obligation 4 into a premise of the harness's own correctness. The position held; the representation under it needed three corrections.

The sub-question rides along: n-ary segments with explicit extents, versus a binary `arrCat` node. I took segments to keep Ω canonical — with a binary node one array value has many trees, and every Ω comparison (`canonicalize`, the golden-trace suite, the differential harness's simulation relation) would need quotienting by associativity. But segments carry their extents redundantly, and redundancy in a state representation is exactly where desynchronization bugs live.

**(c) `Array` in the fixed basis rather than as a §7 declaration.** I argued that no CIC-scheme inductive can have flat values and that flatness is the entire point. That argument is sound but it widens the kernel at precisely the moment §7 is trying to establish that declarations generate everything (recursors, `copy`, the unrestricted classification). An array's `copy`, its recursor, and its unrestricted-iff-`T`-is classification all now have to be *written* rather than *generated*, and each is a place where the basis and the scheme can drift apart. The alternative — find a scheme extension that admits flat n-ary values — is a real research question I did not attempt, and if it has an answer, it is a better one than mine.

> **VERDICT: held, and the named cost was the cost.** The flat n-ary value is what makes prefixes and middles first-class, and nothing in the implementation wanted a spine. The predicted drift surface is exactly where the work went: `arrRec` had to be given ι-rules by hand (R10), and getting them *wrong* would not have failed loudly — it would have made every transferred proof want a transport lemma its list original never needed. The basis grew by one more than the draft budgeted (`Le` and `add`, R1), for a reason the draft could not have seen: a kernel rule cannot cite a library, and two syntactically different `add`s never convert.
>
> *(The fourth, smaller question — whether element access should be a one-slot carve — resolved itself. It is a one-slot carve, and the σ churn I worried about never materialized, because ¶2.1's `a[i]` puts the element rather than an `Array 1 T` at the place. What that choice did cost is R5: the marker then hides one level down inside a one-slot run, and a shallow "owned" test hands it out as an element.)*

---

## Appendix A. Mechanization map — as predicted, and as it landed

*Written as a forecast for whoever would build it. Kept because the forecast was largely accurate, and annotated where it was not — a map that was wrong in a specific place is more useful than one silently rewritten to match the territory.*

**The forecast held on the big claim:** nothing here was a new subsystem, and the list stayed short. The three places it was wrong are marked below, and all three are the same kind of wrong — a step assumed to be free that turned out to have a case in it.

**`Dllbc/Value.lean` — the value layer.** No new `Val` constructor. An array node is `ctor "Arr" segs` and a segment is `ctor "§seg" [cVal, body]`, both reserved names with no `ctorSig` entry, so no program can write or match them. Every existing generic walker then works unchanged and *must not be touched*: `loanIds`, `symIds`, `renumber`, `loanToPvar`, `hasStateMarker`, `beq`. `pretty` should learn the `Arr⟨c ▷ b, …⟩` rendering, since the trace suite is the test suite.

**`Dllbc/Pure.lean` — the comptime layer.** `ctorSig` gains `"Arr"` (field telescope `T` repeated `n` times, at concrete `n` only; `none` at symbolic `n`). `typeCtors` gains `Array` ↦ `some ["Arr"]` at concrete `n`, `none` otherwise. `whnfV` gains ι-rules for the two new constants: `arrCat` on run-headed arguments (segment-list concatenation), and `arrRec` on the cons view. Everything else — `substPure`, `nfV`, `convert` — is untouched, which is the load-bearing claim: array snapshots are ordinary neutral spines.

**`Dllbc/Machine.lean` — places.** `Pos` (line ~484) grows from `⟨root, derefs : Nat⟩` to `⟨root, path : List Step⟩` with `Step ::= peel | idx Val | rng Val Val`; `placeToPos` gains the two term shapes; `navRead`/`navWrite` gain the segment cases. This is the widest-reaching change in the tree, because `Pos` is threaded through `getAtPos`/`setAtPos`/`writeR`/`writeC`/the `&mut` rule — but it is mechanical, and the existing `derefs : Nat` is exactly `List Step` restricted to `peel`.

**`Dllbc/Machine.lean` — the carve.** One new function, sitting alongside `drop` and `endLoan` as a third reorganization, called from `navRead`/`navWrite` when a step lands on an array node that is not already segmented at the requested boundary. It calls `hasType` for premise (2) (the same call the audit makes), the M10 refl-match solution path for premise (3), and `refineSym` for both refinements — which means it inherits the "reaches all σ-bearing state" invariant for free, and inherits the §3.2 marker-free assertion as a live check.

> **⚠ Wrong in two places.** The carve does not merely *consult* the node — it **reads a place**, so it must demand-end suspensions first, including the case where the whole payload is out on loan (C6). And premise (3) may not call `refineSym` on a telescope parameter's σ at all without a cited equation (C8) — which is the opposite of the "inherits the invariant for free" framing above. Inheriting the sweep was free; inheriting the *authority to refine* was not.

**`Dllbc/Boundary.lean` — the audit.** `collapseArg`'s `firstLoanMarker` already finds markers inside `ctor` fields, so range-loan collapse needs no new code. What is new is the ¶3.8 extent check on the obligation type at `seedTelescope`, and the merge normalization before the `hasType` in `auditObligation` (or, equivalently, inside `⇝` — the latter is cleaner, since merge is then part of what "the snapshot of an array" means rather than a step the audit remembers to take).

> **✓ Right, including the parenthetical.** Putting the fold inside `⇝` *is* cleaner and is what landed. But there is a second site the forecast missed entirely: §5.4's **exit-snapshot substitution** injects the collapsed payload raw, and folding there too is what makes any postcondition over a carved array stateable at all (C5). "Equivalently, inside ⇝" was right about the audit's own conversion and silent about the substitution beside it.

**`Dllbc/Std.lean` — the library.** Three tiers. The carve's own arithmetic: `le_split`, `add_cancel_l`. The ¶3.2 obligation layer transcribed from Low\*: `range_disjoint`, `range_empty`, `range_includes`, `carve_carve` — build these four *first* and in that order, since they are the interface premise (2) is stated against and the fourth is the one that decides whether nested carving is cheap. Then the array layer proper: `arrRec` spines, `aget`, `aTake`/`aDrop`, `arrCat_take_drop`, and the transfer of `count`/`Sorted`/`Bound` from `listRec` to `arrRec`. This is the bulk of the *work* and none of the *risk*; M16–M18 established that this shape of library goes through in the M15 surface at roughly first-try.

**Test architecture.** The golden-Ω traces of §2–§3 are unaffected (no existing program carves). The new traces are ¶3.3 and ¶3.4, which are written above in exactly the form `expectEnv` consumes. The differential harness (M8/M9) should gain array bodies before anything else is believed: the multi-marker collapse of ¶8.2's obligation 3 is precisely the bug class a per-rule-branch negative test exists to catch, and M20's lesson was that the branch nobody tested is the branch that lied.

> **✓ Right, and the advice was worth more than it knew.** Array bodies in the differential are what found ¶3.6's polarity inversion, which no amount of checking could have produced. But the forecast under-specified *which* array bodies: every defect in this ledger that hid until late — C5, C6, and all four of C9's sites — is invisible at **concrete** extents and routine at **symbolic** ones, or the exact reverse. A suite of concrete-extent tests (which is what the first milestone naturally writes, `sort2` included) exercises none of the symbolic paths; a symbolic suite never constructs a zero-extent segment. **The generalizable rule is that arrays need the differential run at both, and neither is the default.**

---

## Appendix B. The ledger this note was amended from

`DELTAS.md`, in this directory, is the implementation's own record — eight corrections, seventeen refinements, six gaps, two restrictions, written while the work happened and addressed to this pass. Everything in it has now been applied above. It is kept, unedited, as the historical account: this note says what the design *is*, and that file says what it took to find out. Where the two differ in emphasis, the ledger is the primary source, and its `HANDOFF` section records the state of the lane at the moment the quicksort leaf was still unbuilt — which is worth reading by anyone who wants to see how accurately a mid-flight brief predicted its own completion.
