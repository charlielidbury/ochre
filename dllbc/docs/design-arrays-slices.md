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

A note for the mechanizer, since it is where a plausible implementation would go wrong: refining `σ_m` is a refinement of a **length index**, not of a value snapshot, and it must go through `refineSym` like any other — reaching Ω, `sctx`, obligations, group owed types, `retTyVal`, `selfBack`, per the M10 "refinement reaches all σ-bearing state" invariant. It satisfies §3.2's knowledge/state assertion trivially (`add lo′ (add cnt rest)` is marker-free), which is worth *checking* rather than assuming: this is the first refinement in the calculus fired by an **ownership** operation rather than by a match, and the invariant's whole point is that ownership operations must not smuggle state into σ's. They do not here — the substituted term is arithmetic, and it is true of the value timelessly.

**The effect.** `L`'s segment is replaced by three, with the extents premise (3) produced: `lo′`, `cnt`, `rest`. The bodies follow the body of `L`:

* `L = [v₁ … v_m]` (an owned literal run): split the run positionally.
* `L = σ`: refine `σ := arrCat σ₁ (arrCat σ₂ σ₃)` with `σ₁ : Array lo′ T`, `σ₂ : Array cnt T`, `σ₃ : Array rest T` fresh — again ordinary ⇜, again marker-free, again knowledge (the array *is* the concatenation of its parts, at entry and forever).

Degenerate carves are no-ops: when the request coincides with the leaf, no split and no refinement happen at all. This matters for `split_at_mut` (¶5), whose second borrow is always degenerate.

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

**Why no `unsafe`.** Rust's `split_at_mut` is unsafe internally because Rust's borrow checker reasons about *paths*, and `&mut v[0..k]` and `&mut v[k..]` are two borrows of the same path `v`; nothing in the type of the pair records that the two pointers cannot alias, so the implementation drops to raw pointers and the disjointness is a comment. Here the two borrows are not two borrows of one path: after the carve they are borrows of two *different segments*, which are different subterms of one value tree, and the ownership machinery cannot represent them overlapping. The `Le` proof was consumed at step 1 to license the reorganization; from step 2 onward disjointness is not a claim being trusted but a shape being read. **The trust that Rust localizes in an `unsafe` block is here discharged by one `Le` term at one carve.**

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
* **The delegation discipline.** M22's central finding stands: an inline pointer-write's exit is opaque, so a direct-proving body delegates its mutation to a callee whose exit is provable. Range places do not repeal that — they change *what must be delegated*. The **leaf** (the swap) still needs a back-carrying callee or the three-feature arc (pin the issued payload, prove the bridging equation, audit-rewrite along cited bridges). The **recursion** does not, because the caller's knowledge of a sorted sub-slice is the callee's own postcondition attached to a σ that never lost its neighbours.

**What gets built.** The glue moves from index arithmetic to concatenation:

```
    sorted_arrCat : Sorted l → Sorted r → AllLe p l → AllGt p r
                  → Sorted (arrCat l (arrCat (asingle p) r))
```

which is the textbook quicksort correctness lemma, in the textbook shape, for the first time in this project. M22-c's `glue` — a nested `leb`-elim dispatcher over three directional lemmas with a subtraction-guarded reindex — is what that lemma looks like when the concatenation is simulated by indices.

**Honest accounting of the migration's own cost.** Three things get harder, not easier:

1. The partition leaf must now produce its pivot index *together with* the two carve licenses (`Le i n` and its complement), because the recursive calls carve at exactly that index. Today the index is a plain `Nat` pinned by a Σ; tomorrow it must be Σ-paired with bounds. That is more signature, and it is the honest price of the recursion being over real segments.
2. Both sub-slices must be carved **before** either call, not one per call: the second carve needs an *owned* leaf, and after the first call the first segment is loaned to a live group. That is the shape the snippet above already has, and it is a better shape — but it is a different shape from today's sequential reborrows, and it means the pivot element sits between two live borrows as a third segment that neither call can see. (Which is correct: the pivot is in its final position and must not move. The calculus is enforcing that, for free, by the same mechanism that keeps the halves apart.)
3. The pure library gains an array layer. `arrRec`, `aget`, `aTake`/`aDrop`, `arrCat` and their lemma stack are new, even though each mirrors a list counterpart. Call it a week of the kind of work M16–M18 already showed is mechanical in the M15 surface.

---

## ¶7. Prior art, honestly

The standing instruction is to steal shamelessly and reinvent as little as possible. The honest summary of what follows is that **the carve rule is separation logic's array split with the side condition relocated from a proof-mode goal into a type-checking premise**, and that **Low\*'s `gsub`/`loc_disjoint` is its closest living relative**. What is new here is not the rule but its *placement*: discharged once, by the borrow checker, at the moment ownership is divided — rather than re-discharged at every framing step downstream.

**Separation logic (the source).** The canonical array law is Iris's `array_app`:

```
    l ↦∗ vs   ⊣⊢   l ↦∗ take n vs   ∗   (l +ₗ n) ↦∗ drop n vs
```

Three features to note, because ¶3 inherits all three. It is stated **at a split point**, not for an arbitrary subrange — a middle range is obtained by iterating it, and the leftovers are the frame. Recombination is the *same* law read right to left, which is why ¶3.3 has no rejoin rule (merge is the law's converse, and both directions are structural). And **disjointness is not a side condition of the split at all** — it is built into `∗`. Arithmetic side conditions appear only when you index (`n < |vs|`). ¶3.1's "the tree does the aliasing, the proofs do the arithmetic" is that division, transplanted: the segment partition plays `∗`, and premise (2) plays `n < |vs|`. RustBelt handles `&mut [T]` by splitting a full borrow over an array predicate; it works, but it works *in the logic*, with the split discharged by a proof the programmer writes, not by a checker premise the programmer merely feeds.

**Low\*/`LowStar.Buffer` (the closest relative).** `gsub b i len` is a ghost sub-buffer (with `sub` the runtime counterpart), and framing runs through `loc_buffer` / `loc_disjoint` / `modifies`. Disjointness of two sub-buffers is a *lemma with an arithmetic hypothesis* of the shape `i₁ + l₁ ≤ i₂ ∨ i₂ + l₂ ≤ i₁` — the same proposition premise (2) demands, in the same form. So Low\* has already established that proof-conditioned subrange aliasing is workable at scale (HACL\* is the evidence). The difference is where the obligation lives and how often it is paid: Low\* reasons over a heap with locations, so the disjointness fact must be *re-composed* at every `modifies`-clause junction, and the `modifies` reasoning is famously the bulk of a Low\* development. Here the obligation is discharged once, at the carve, and the ownership tree carries the consequence — because there is no heap, and hence nothing to frame *over*. That is the design's one honest claim of improvement over its nearest neighbour, and it is entirely downstream of §0's no-heap decision rather than of anything invented in this document.

**Rust (the shape being imitated, and its limit).** `split_at_mut` is safe on the outside and raw-pointer arithmetic on the inside. The borrow checker tracks loans by *place path*, and MIR does have a `Subslice` projection, but `places_conflict` can only rule out overlap for **constant** indices — which is why `[a, b, rest @ ..]` patterns give disjoint borrows and `&mut v[..k]` / `&mut v[k..]` do not. There is no mechanism for a runtime-valued disjointness fact, because there is no mechanism for a proof. Rust's actual answer, where the standard library needed one, is `get_disjoint_mut` (formerly `get_many_mut`): a **runtime check** returning an `Option`. That is the cleanest possible statement of the gap this design fills — Rust pays a branch and a failure mode where DLLBC pays a `Le` term, and Rust must, because it has no comptime fragment to pay from. (Proposals in the "view types" line aim at the same target from the type side; none has landed.)

**Aeneas / LLBC (the system this project is measured against).** Aeneas has arrays and slices, but not as a borrow-splitting rule. `Array T N` and `Slice T` are **builtin** types, and the operations — index, index-mut, array-to-slice, and `split_at_mut` itself — are **assumed functions** whose forward and backward definitions are hand-written in each backend's primitives library, over a `Seq`/`List` model with index arithmetic. So a slice's framing in Aeneas is a *model function on sequences* (`update`, `take`/`drop`-style reassembly), trusted at the primitive and reasoned about downstream exactly as M22 already does. There is, to the best of this note's reading, **no range place and no partial borrow of a container anywhere in the LLBC semantics** — the borrow machinery is over whole values, and the in-repo Rocq mechanization (`aeneas/`, which covers the proven LLBC# ≤ LLBC+ core with HLPL+/LLBC islands and no calls) does not reach arrays at all. This matters for the project's positioning: the range-place design is not a re-implementation of something Aeneas has, it is the thing Aeneas assumes.

**Verus.** Two mechanisms, and only one is relevant. `&mut` on a container is modeled by `Seq` plus `old(v)`, and disjoint mutation of two halves is normally *not* expressed as two borrows at all — it is index reasoning on one sequence, i.e. M22's situation. Genuine disjointness comes from `tracked` ghost permissions (`PointsTo` and friends), which split and recombine explicitly. That is proof-conditioned aliasing, but the "proof" is a resource-algebra manipulation the user performs, not an arithmetic proposition the checker consumes. Closer to Iris than to this design; more expressive, and much more to carry.

**Dafny (the anti-pattern, stated because it is instructive).** `array<T>` framing is a `modifies` clause over a **set of objects**, so a method that touches `a[lo..hi]` must declare `modifies a` — the whole array — and then pin the untouched part in its *postcondition*: `forall k :: 0 <= k < lo ==> a[k] == old(a[k])`. That is the frame described by contract, in its purest form, and it is precisely what ¶0 claims range places delete. Anyone who wants to see the cost of *not* having this design should read a Dafny array method's postcondition.

**Creusot / Prusti.** Creusot gives `&mut T` a prophecy pair (current, final) and models slices as `Seq`; `split_at_mut` gets a specification relating the two halves' prophecies to the parent's, trusted at the primitive. Prusti is similar in the relevant respect. Both confirm the pattern: everyone who wants `split_at_mut` either trusts it or proves it in a logic; nobody checks it.

**What none of them solves, and therefore what is genuinely at stake here.** Every system above either (a) trusts the split as a primitive (Aeneas, Creusot, Prusti, Rust's std), (b) proves it in a separate logic whose obligations must then be threaded through all downstream framing (Iris/RustBelt, Low\*, Verus), or (c) checks it at runtime (Rust's `get_disjoint_mut`). None of them has a **borrow checker that takes a proof term as an input and licenses an ownership split on the strength of it.** That is the one thing ¶3 proposes, and it is only available because DLLBC has a comptime fragment inside the same language as the ownership discipline — which is the whole reason the calculus exists.

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
2. **Carve's refinements are knowledge, not state.** Two refinements fire: the index refinement `σₙ := add lo (add cnt rest)` and the value refinement `σ := arrCat σ₁ (arrCat σ₂ σ₃)`. Both substituends are marker-free, so §3.2's asserted invariant holds — but this is the first ownership operation that refines, and the assertion should be *exercised* on it rather than assumed to still hold.
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
* **Shared borrows.** Deferred with §10. The observation to record: read-only sharing needs no disjointness at all — two shared range borrows may overlap freely — so shared slices should be strictly easier than mutable ones when §10 arrives, and the carve rule's proof premise simply does not fire for them.
* **Non-contiguous and dynamic-shape ranges.** A range whose bounds are not comptime terms. Out by construction: the design's entire arithmetic lives in the comptime fragment.
* **Rigid-length signatures.** A function whose array length is a compound neutral cannot carve (¶3.2, premise 3). The remedy is stylistic — take the length as a parameter — but it is a genuine restriction on what signatures are writable, and if it turns out to bite, the escape is the same one M10 built for its rigid cases: name the equation and carry it, rather than solving it.

---

## ¶9. The three decisions I am least sure of

Recorded for the user, plainly, in decreasing order of how much would have to change if they are wrong.

**(a) The residue transition — refining a *length index* to make the carve's arithmetic definitional (¶3.2, premise 3).** This is the most aggressive idea here and the one that buys the most: it deletes every `sub` from the design and makes the audit's rejoin conversion definitional rather than lemma-mediated. But it means the carve *refines the type index of an array from inside an ownership rule*, which is a new kind of act in this calculus — every prior refinement was fired by a match on a value. It restricts carving to arrays whose length is flexible (a bare σ), which pushes shape onto every signature. And I have argued, but not tested, that it respects §3.2's knowledge/state invariant. The conservative alternative is to compute the residue as `sub`, accept the arithmetic tax, and keep the ownership rules refinement-free. That alternative is strictly simpler and strictly more painful, and I do not know which way the milestone would break.

**(b) Segment lists as the Ω representation, versus a binary `arrCat` node (¶1.1).** I chose n-ary segments with explicit extents mainly to keep Ω canonical: with a binary split node, one array value has many trees, and *every* Ω comparison — `canonicalize`, the golden-trace suite, the differential harness's simulation relation — would need quotienting by associativity. That seemed like an unacceptable tax on the existing test architecture. But segments carry their extents redundantly (the count is derivable from the types of the bodies, most of the time), and redundancy in a state representation is exactly where desynchronization bugs live. Someone who cares less about the trace suite might reasonably choose the binary node and a normal form.

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

**`Dllbc/Std.lean` — the library.** `le_split`, `add_cancel_l`, then the array layer: `arrRec` spines, `aget`, `aTake`/`aDrop`, `arrCat_take_drop`, and the transfer of `count`/`Sorted`/`Bound` from `listRec` to `arrRec`. This is the bulk of the *work* and none of the *risk*; M16–M18 established that this shape of library goes through in the M15 surface at roughly first-try.

**Test architecture.** The golden-Ω traces of §2–§3 are unaffected (no existing program carves). The new traces are ¶3.3 and ¶3.4, which are written above in exactly the form `expectEnv` consumes. The differential harness (M8/M9) should gain array bodies before anything else is believed: the multi-marker collapse of ¶8.2's obligation 3 is precisely the bug class a per-rule-branch negative test exists to catch, and M20's lesson was that the branch nobody tested is the branch that lied.
