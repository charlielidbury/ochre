# Primitive arrays in Ochr: design probe

Status: design only (2026-09-29, arrays-primitive probe). Nothing is implemented, and RULES, DECISIONS, the checker and the paper are unchanged. Assumes RULES v2.1 plus D52 and D53 (runtime reads move; `clone` is built in; `Nat` is not a copy type). The rival route (arrays defined in Ochr code, with a primitive runtime) is probed separately; comparative points are marked **[vs library]**. DLLBC lessons are cited by their ledger names in `dllbc/docs/01-design-arrays-slices.md`.

**Summary.** `Array(T, n)` is a kernel type former. Its values in Ω are *segment lists*: the positions `[0, n)` are cut at boundaries, and each segment holds one of three things:
- a known element;
- a slice `σ[a..b]` of an array the machine cannot see inside;
- a loan.

Places `p[i | h]` and `p[i..j | h]` carry erased bounds proofs. Borrowing `&a[0..m]` leaves `σ[m..n]`, literally, in the owner, so "the rest was not touched" holds by definition, as the `S` around a borrowed predecessor field does for `Nat`.

The machine never *decides* arithmetic. It compares boundaries by syntactic equality and by the structural order [Rec] already uses. Where those cannot tell, it ends borrows (fail-safe) or leaves a stuck projection (incomplete, never wrong). It does *name* three library functions (`Le`, `Sub`, `Add`), as it already names `True` and `And`.

Frames are free. Gluing lemmas and pointwise facts at unrelated symbolic indices stay lemmas. One of them, read-after-write at a different index, is an axiom unless the optional ordering hints (§1.9) are added. Verdict (§6): worth a staged implementation.

## 0. What the primitive is for

In `AddMZero`, the recursive call borrows the predecessor field of `*x`, and the `S` around it stays with the owner: the environment performs the frame step. Borrowing the first `m` elements of an array should do the same, leaving the other `n − m` visibly unchanged in the owner.

A right-nested definition (`Vec(T, S m) = T × Vec(T, m)`, or a list) cannot do this for a prefix or a middle, because a prefix is not a sub-place of nested pairs. **[vs library]** A prefix must then be lent through a function that returns a borrow. That function's backward function, a sealed program, holds the suffix, so "the suffix is unchanged" becomes a lemma: provable in Ochr, but still a lemma.

The primitive's job is to make ranges into places. Its design stance, the user's, is that arrays model memory. There are no owned sub-arrays: a range can be borrowed, cloned or overwritten, never moved out and owned. Moving a whole array moves the buffer.

## 1. The design

### 1.1 The type

- **The former.** `Array(T, n)` holds exactly `n` elements of type `T`, where `T` is a data type (D48) and `n : Nat` stands in a type position (erased). It is a data type in `Type₀`, so `&Array(T, n)` is well formed. It is not an inductive declaration: there are no indices, and its values are flat.
- **The length lives only in types, and nothing recomputes it.** The owner's stored type keeps `n`. A borrowed range's type is fixed when the borrow is taken, and [End] is substitution, so nothing re-types the array when a range comes back. DLLBC's exit audit did re-type it, which is why its extents had to add up definitionally, and why it refined length indices at cuts (C8, T2, R12). Ochr never solves or refines a length.
- **Not a copy type** (D53): reading a whole array at runtime moves it.

### 1.2 Values

```
array value   V ::= ⟨b₀ | s₁ | b₁ | … | s_m | b_m⟩      b₀ = Z, b_m = n; each bₖ a Nat value (maybe neutral)
segment body  s ::= e                                 one element (width 1: b_{k+1} = S bₖ)
                  | A[a..b]                             positions a..b of atom A, in A's own coordinates
                  | loan_ℓ                              the range is lent out
array atom    A ::= σ | ⌈t⌉ | lit(v₁ … v_k) | init(f, k) | cat(V)      cat(V): a loan-free list that could not be cut (stuck)
element       e ::= v | A[i]                            A[i]: a neutral of type T
```

`σ[a..b]` is a *projection* of `σ`, not a fresh abstract value. Creating it needs no refinement and no new name, and every path that derives it gets the same neutral. DLLBC did the opposite: it refined `σ := arrCat σ₁ σ₂` with fresh values.

- **Merge (canonical form).** Values are kept in normal form, as follows.
  - Adjacent segments `A[a..b] | b | A[b'..c]` with `b ≡ b'` merge into `A[a..c]`. An element `A[i]` counts as the segment `A[i..S i]`.
  - `A[Z..n]`, where `n` is `A`'s length, is `A`, and so is the one-segment list `⟨Z | A | n⟩`.
  - A literal sliced at numerals is a literal.
  - A zero-width segment is dropped only if it holds no loan. This is DLLBC's C9 lesson: dropping zero-width segments caused four runtime bugs there, and a loan must stay bound.

  Merging compares normal forms syntactically and does no arithmetic.
- **One representation.** A segment list that holds loans is an ordinary value that contains loans; loans may occur anywhere (RULES §2). Once its loans have ended, its canonical form is what types and `Eq` see. DLLBC needed a state form, a knowledge form (an `arrCat` spine) and a fold between them, and that fold produced two late findings (C5, R9). Ochr needs no fold, because its snapshots are values.
- **Two coordinate systems.** Boundaries use the array's own coordinates. The bounds inside `A[a..b]` use `A`'s coordinates. The two coincide for an array cut in place, and differ once a slice is handed to a callee (§1.5).

### 1.3 Places and obligations

```
places p ::= x | *p | p.g | p[x | h] | p[x..y | h]     x, y variables or numerals; h a proof (erased)
```

- **The two places.**
  - `p[i | h]` has type `T` and needs `h : Lt(i, n)`, where `Lt(i, n)` is notation for `Le(S i, n)`.
  - `p[i..j | h]` has type `Array(T, Sub(j, i))` and needs `h : Le(i, j) ∧ Le(j, n)`.

  In both, `n` comes from `p`'s *stored type*. That type must normalise to an `Array` head; a neutral stored type is a type error. This is D49's reading: it consults a normal form, but a less refined path only rejects. The obligation is formed from `n` and the index values, and `h` is checked against it by conversion. The surface syntax may omit `h` when the obligation normalises to `True`, as it does at every numeral index.
- **Indices are variables or numerals.** `a[f(x)]` is sugar for `let i = f(x); a[i]`, so evaluating a place has no effects. A pattern variable that resolves to `p[i].g` embeds `i`'s *value* at the time of the match (D32 stays syntactic, and a later `i := …` does not move the place).
- **Kernel-known functions.** `Le`, `Sub` and `Add` are ordinary library functions that the kernel knows by name (§2).

### 1.4 The machine on array places

`≼` is the **structural order** on `Nat` normal forms: `x ≼ y` when `x ≡ Z`, or `x ≡ y`, or `y ≡ S y'` and `x ≼ y'`. It is decided by syntax, it is sound for `≤`, and substitution preserves it. It is [Rec]'s subterm order, plus the fact that `Z` is least.

- **[Locate]** A request `[i, j)` is made on `content(p) = ⟨b₀ | … | b_m⟩`; an element place requests `[i, S i)`.
  - `s` is the largest index with `bₛ ≼ i`, and `t` is the smallest with `j ≼ b_t`. The obligation `h` supplies `j ≼ b_m`, and this is the only use of a proof.
  - The *window* is segments `s+1 … t`. The request is *exact* if `bₛ ≡ i` and `b_t ≡ j`.
- **[Access]**, extended. Before `p[i..j]` or `p[i]` is read, borrowed, assigned or matched:
  - end the loans on the path to `p`, as today;
  - end the loans in the window's segments and, except for a match, inside their contents.

  Loans outside the window stay live: their segments lie structurally before `i` or after `j`. Where `≼` cannot tell, the window grows and that loan ends. This is **fail-safe**: ending a borrow early can only turn a later use of it into an error.
- **[Cut]** Applies to a borrow, assign or move whose request is not exact. The window, which is now loan-free, is concatenated into `W` and replaced by `W↾[bₛ, i) | i | W↾[i, j) | j | W↾[j, b_t)`. `W↾[a, b)` works segment by segment:
  - a segment structurally inside `[a, b)` is kept;
  - a slice `A[x..y]` with `x ≼ a ≼ y` becomes `A[x..a]` and `A[a..y]`, the cut point written as given;
  - anything undecided becomes the stuck `cat(W)[a..b]`.

  A copying read does not cut: it returns `W↾[i, j)`, or the element, and leaves the state unchanged.
- **[Read]**
  - `p[i]` copies if `T` is a copy type or the read is erased. Otherwise it moves (D53), leaving `⊥` that must be refilled before an enclosing borrow ends.
  - A runtime read of `p[i..j]` is an **error** unless it is erased or under `clone`: there are no owned sub-arrays.
  - A read whose window may contain `⊥` (through a `cat`) is an error.
- **[Borrow]** `&p[i..j]` (or `&p[i]`) runs [Access] and then [Cut].
  - The exact window's body moves into `borrow_ℓ`, in its own coordinates (§1.5).
  - The window becomes the single segment `loan_ℓ`, keeping its boundaries `i` and `j`.
  - The borrow has type `&Array(T, Sub(j, i))` (respectively `&T`).
- **[Assign]** `p[i] := t` and `p[i..j] := t` run [Access] and [Cut], [Drop] the window, then store `t`'s value there. The value must have type `T` (respectively `Array(T, Sub(j, i))`), so a range cannot change its length.
- **[End]** and **[Drop]** are unchanged: substitute and merge; a live loan in an owned array fails.

**Example.** Start from `c ↦ σ : Array(Nat, σₙ)`.
- `&c[0..σₘ]` leaves `c ↦ ⟨Z | loan₁ | σₘ | σ[σₘ..σₙ] | σₙ⟩`.
- Then `&c[σₘ..σₙ]` is exact and ends nothing: two live borrows, which is `split_at_mut` inline with nothing trusted.
- Then `&c[S σₘ..σₙ]` is placed by `σₘ ≼ S σₘ` and cuts the second segment, and `loan₁` survives.
- Then `&c[σₖ]`, with `σₖ` unrelated to the other indices, cannot be placed, so `loan₁` ends.

### 1.5 Coordinates

A callee indexes a slice from zero, so at an instance (a sealed program re-run on the content `σ[i..j]`), its `a[0]` is position `i + 0` of `σ`. There are two readings.
- **Flatten** (recommended). `A[a..b][c..d] ⟶ A[Add(a, c)..Add(a, d)]` and `A[a..b][r] ⟶ A[Add(a, r)]`. Here the kernel-known `Add` normalises on *both* arguments: `Add(x, Z) = x`, `Add(Z, y) = y`, `Add(S x, y) = S Add(x, y)`, `Add(x, S y) = S Add(x, y)`. These four rules are confluent and terminating, and each is a theorem about the library's `Add`.
  - Numeral offsets from a symbolic base are then structural, which covers a callee's `a[0]` and `a[1..]`.
  - So are symbolic offsets from a numeral base, which covers induction over the cons view.
  - `σ + σ'` stays the neutral `⌈Add(σ, σ')⌉`.
- **Nest.** Keep `A[a..b][c..d]` as is. Then `Add` is not in the kernel, and the two paths still agree. The cost is that the sub-of-sub identity becomes an axiom, and every cons-view induction needs a transport along it.

When a slice at `i ≠ Z` is borrowed, its segment list is rebased by subtracting `i` from each boundary. That subtraction is done structurally, as `S^a(x) ⊖ S^b(x)`; otherwise the list becomes `cat(W)`. So a callee loses exactness when the caller's cuts sit at unrelated symbolic points. This is incompleteness only.

### 1.6 `Eq` and `Id`

- **[Eq-Arr]** `Eq (Array(T, n)) V W`, after merging:
  - is `True` when `V ≡ W`;
  - otherwise, if the two boundary lists align structurally, is the `And` of per-segment equations, which the unit laws then shrink to the segments that differ;
  - otherwise stays `Eq`;
  - at length `Z` is `True`. This is the one η-like rule. It holds because `⟦T⟧⁰` is a singleton, and it makes a sort's base case definitional where DLLBC needed a lemma (R14).
- **`Id`** needs nothing new. The footprint roots at the owner and observations end every borrow, so an array owner's observation computes to equations about the changed segments only.

### 1.7 Closing off, splitting, recursion

- **[Close]** is unchanged.
  - A range borrow passed to a stuck call has loan-free content, and its loan becomes `⌈let c = W; f(&c); c⌉`, of type `Array(T, Sub(j, i))`, between untouched segments.
  - Several ranges of one array passed to one call get one fill each; they share one owner (D18 unchanged).
- **[Seal]** Substitution into a projection re-normalises it. Projection normalisation fires only on facts that substitution preserves, and its stuck forms keep all their inputs, so it commutes with substitution (§4.2).
- **[Split]** Nothing new.
  - Arrays are never matched: positions are reached by places.
  - Matching an element whose content is the neutral `A[i]` generalises it ([Split-gen], D34).
  - Matching the length refines the stored type, and rigidifies nothing, so a body may match its length and still cut at symbolic points (unlike DLLBC, T2 and R12).
- **[Rec]** A range `V[a..b]` is a strict subterm of `V` when `Z ≼ a` and `b ≼ n`, one of them strictly. So recursion on `a[1..n]` is structural, and recursion on `a[0..k]` for a computed `k` is not (quicksort needs fuel). Recursion on the length needs no extension.

### 1.8 Construction, `len`, `clone`

- **Construction.** Literals `[t₁, …, t_k] : Array(T, k)`, and `Init(n, f)` for `f : Π(i : Nat). T`, whose value is the atom `init(f, n)`, with `init(f, n)[i] ⟶ f(i)`. The calls have no effects: `f` takes no borrows and closures capture none.
- **`clone`.** `clone(p)` and `clone(p[i..j])` (D53) copy the canonical value; a clone of a slice is the same slice.
- **`Len`** is unnecessary. Lengths are explicit parameters, which at runtime are the fat pointer's length word. A `Len(a)` returning the type index would read an erased value and gain nothing.
- **Deallocation** is [Drop].

### 1.9 Several borrows, ordering hints, `Vec`

- **Several ranges inline.** `let l = &(*a)[0..k | h₁]; let r = &(*a)[k..n | h₂];` leaves both live, because the second request is exact against the first.
- **A function returning both** (`split_at_mut`) needs the ROADMAP's multi-result signature `(&A₁, &A₂)`: bound at once, with one [Close] hole per result. A transparent `SplitAtMut` only cuts and never gets stuck, so its calls simply run.
- **Two live element borrows at unrelated symbolic indices** are rejected: the second request cannot be placed, so the first loan ends. This is DLLBC's R13 wall, which ruled out Lomuto scans. What remains possible: clone-swaps for copy types, and accesses at the zero of a range the program cut.
- **Ordering hints** (optional, not in stage 1). A place `p[j | h, d]` takes `d : Le(b, j)` or `d : Le(S j, b)` for an existing boundary `b`. [Locate] reads `d`'s *stored type* as one more `≼` fact. The decision is read from a declaration-shaped type, and it fails safe: a neutral type gives no hint.
- **`Vec(T)`** is out of scope. It is `(cap, len, Array(T, cap), len ≤ cap)`, which needs dependent fields (the ROADMAP's subset types) and uninitialised capacity. Nothing here blocks it.

## 2. What the primitive brings into the kernel and the trusted base

| # | Item | Avoidable? How, and what it costs |
|---|---|---|
| 1 | Type former `Array(T, n)`, with its sort and its data-type rule | No |
| 2 | Value forms: segment lists; atoms `lit`, `init` and `cat`; projections `A[a..b]` and `A[i]` | `cat` can go if every access at an undecided position is rejected, but that also rejects reads that would have produced a correct neutral |
| 3 | Place steps `p[i \| h]` and `p[i..j \| h]`: index variables inside places, and an erased proof slot | No. It reaches pattern resolution (index values embedded) and stuck-block captures, which truncate at the first index step and capture the whole array place: safe, but coarser than necessary |
| 4 | [Locate], [Cut] and merge: a normaliser over boundaries | No |
| 5 | The structural order `≼` (`Z` least, `x ≼ S^k x`) | Partly. Syntactic equality alone suffices if programs cut only at zero or at an existing boundary and index relative to a nested borrow (DLLBC's "index 0 of a carved segment"). That style is then forced everywhere; B2's right half, for instance, would collapse the array and lose the pivot frame |
| 6 | `Le`, known to the kernel by name (bounds obligations) | No. A primitive `InBounds` would be the same thing under another name. `Le` is only named, never decided: it evaluates by its definition, and on neutral arguments it is a sealed program |
| 7 | `Sub`, known by name (range lengths) | Yes, with offset-count places `p[i; c] : Array(T, c)` and obligation `Le(Add(c, i), n)`. Then users write every count, and `Sub` moves into user code: quicksort's right half is `a[S k; Sub(n, S k)]` |
| 8 | `Add`, known by name, with the four rules of §1.5 | Yes, by nesting instead. The sub-of-sub identity then becomes an axiom, and every cons-view induction needs a transport |
| 9 | A decision procedure or normaliser for index arithmetic (linear arithmetic, `omega`, associativity or commutativity) | **Not needed.** The only decisions are `≡` and `≼`; every other fact is a proof the program supplies |
| 10 | Comparisons that yield proofs (a dependent `if`) | Not needed in the kernel. A `Bool` comparison, D34's generalisation record and one lemma suffice (B4) |
| 11 | Axiom `SetGetOther`: after `a[i] := v`, reading `a[j]` gives the old element when `i ≠ j` | Yes, with ordering hints (§1.9) and a trichotomy lemma: each arm then places `j` and reads it definitionally. Without hints it is an axiom, true in the model |
| 12 | Axiom `ProjProj` (sub-of-sub) | Only under nesting; flattening removes it |
| 13 | Array extensionality | None of B1–B4 needs it |
| 14 | [Eq-Arr] | Yes, but the headline goes with it: every frame component would then need a lemma |
| 15 | [Rec] extension (strict sub-range) | Yes: recurse on the length, or on fuel |
| 16 | `Init` and literals | No |
| 17 | `clone` for arrays and slices (D53's built-in, extended) | No: runtime range reads are forbidden, so copying needs it |
| 18 | `Len` | Avoided: lengths are explicit parameters |
| 19 | Well-formedness condition 7: segments partition `[0, n)`, each body has the type of its width, and a loan in an array is a whole segment | No; the preservation proof needs it |
| 20 | Unary `Nat` indices | Out of scope. A `usize` primitive would need kernel-*evaluated* arithmetic (as Lean's GMP `Nat` is), still with no decision procedure. That is where modelling a systems language will eventually bring real arithmetic into the kernel |

### The arithmetic question, settled

**Can kernel arithmetic be avoided entirely?** It never has to be decided, but it does have to be named, and normalising it is optional.

- **Deciding it: avoided.** There is no solver. The only index decisions are `≡` and `≼`, the order [Rec] already has. Every other fact is supplied by the program as a proof. The machine never looks inside a proof: it checks an obligation's proof by conversion, and reads a hint's stored type.
- **Naming it: not avoided.** The kernel's rules must *state* bounds and range lengths, so `Le`, and `Sub` or `Add`, become library functions the kernel knows by name. They are ordinary recursive definitions, run by the ordinary machine, and the model interprets them by those definitions, so nothing about them is trusted. They get the status `True` and `And` already have (D49(6)). DLLBC met the same fact (R1): a kernel rule cannot cite a library it does not know, and two syntactically different `add`s never convert.
- **Normalising it: recommended.** A callee's `a[0]` at a caller's cut `σᵢ` must be recognised as position `σᵢ`, so either the four `Add` rules or axioms are needed.

The brief's strategy had three parts. Splits form a tree, so siblings are identified structurally. Lengths flow through stored types and are never recomputed. Facts at symbolic indices become lemmas. The design follows it, with one correction: a tree of splits is not enough, because one position is reached by different routes (a caller's absolute `S k` and a callee's relative `0` in `a[k..n]`, or a sub-of-sub range and a direct one), and identifying those needs `+` on normal forms or an axiom. Keeping projections in their atom's own coordinates makes sub-of-sub a normal-form computation rather than a walk up a tree.

**What it costs the user.**
1. A bounds proof at every symbolic access, from a small `Nat` library proved in Ochr (`LeRefl`, `LeTrans`, `LtLe`, and facts about `Sub` and `Add`).
2. Lengths passed in the exact form the kernel builds, such as `Sub(n, S k)`.
3. Statements that cut where the program cut (`X[0..k]`, `X[k]`, `X[S k..n]`), rather than pointwise statements, which need item 11.
4. Staging: a lemma about a call's result is taken before the call consumes its argument, because Ochr has no dependent results.

## 3. Benchmarks

The surface syntax is the current one, plus `Array(T, n)`, `p[i | h]`, `p[i..j | h]` and `clone`. The benchmarks assume a library of `Le`, `LeB : Bool`, `Sub`, `Add`, `EqB` and `Mod`, with the lemmas `LeRefl`, `LeTrans`, `LtLe`, `LeBSound`, `EqBSound`, `ModLt` and `SubFuel`. All of it is Ochr code proved by recursion, and none of it is kernel.

### B1: borrow a prefix, call an arbitrary `f`, and the rest is unchanged

```
def Frame (n : Nat) (m : Nat) (h : Le(m, n)) (a : Array(Nat, n)) (f : Π(x : &Array(Nat, m)). Unit) :
    Id (Array(Nat, Sub(n, m)))
       (let c = a; f(&c[0..m | h]); c[m..n | ⟨h, LeRefl(n)⟩])
       (a[m..n | ⟨h, LeRefl(n)⟩]) := refl

def FrameM (n : Nat) (m : Nat) (h : Le(m, n)) (a : &Array(Nat, n)) (f : Π(x : &Array(Nat, m)). Unit) :
    Id Unit (f(&(*a)[0..m | h]))
            ((*a)[0..m | h] := (let d = clone((*a)[0..m | h]); f(&d); d)) := refl
```

At the generic call (`a ↦ σ`, `f ↦ σ_f`):
- In `Frame`, the left side cuts `c` to `⟨Z | loan₁ | σₘ | σ[σₘ..σₙ] | σₙ⟩`.
- The call `σ_f(…)` has a neutral head, so it closes off at once and fills `loan₁` with `⌈let d = σ[0..σₘ]; σ_f(&d); d⌉`.
- `c[σₘ..σₙ]` is an exact window, so it reads `σ[σₘ..σₙ]`.
- The right side reads `σ[σₘ..σₙ]`. The footprint is empty, so `Id ≡ True`.
- `FrameM` states the law with the effect observed: lending the prefix to `f` is the same as replacing it with what `f` does to a copy of it. Both sides leave the owner as `⟨Z | ⌈…σ_f…⌉ | σₘ | σ[σₘ..σₙ] | σₙ⟩`.

**Holds by definition:** both statements. The obligation `Le(0, m) ∧ Le(m, n)` converts to `h`'s type by the unit law (D50). The only lemma is `LeRefl(n)`, for `Le(σₙ, σₙ)` (see §6).

**Needs a lemma or a hint:** the pointwise form, "element `j ≥ m` is unchanged". Without a hint, `σⱼ` cannot be placed after `σₘ`, so the read is the stuck `cat(…)[σⱼ]`, and the statement needs `SetGetOther`-style reasoning. With the hint `c[j | hjn, hj]`, where `hj : Le(m, j)`, the read is `σ[σⱼ]` by definition.

### B2: quicksort

```
def QS (f : Nat) (n : Nat) (a : &Array(Nat, n)) (hf : Le(n, f)) : Unit by f := (
  match f {
    Z => (),
    S f' => match n {
      Z => (),
      S _ => (
        let hk = PartLt(n, *a, refl);         // hk : Lt(K, n) for the K below; staged before *a is consumed
        let k = Partition(n, &*a, refl);      // the pivot is now at k
        QS(f', k, &(*a)[0..k | LtLe(k, n, hk)], LeTrans(S(k), n, f, hk, hf));
        QS(f', Sub(n, S(k)), &(*a)[S(k)..n | ⟨hk, LeRefl(n)⟩], SubFuel(n, k, f', hf))
      ),
    },
  }
)
```

**Partition.** It has DLLBC's shape:
- clone the head `x`;
- split the tail `&(*a)[1..n]` recursively, recursing on the length (structural);
- then `match k { Z => 0, S _ => (swap a[0] and a[k] with clone reads; k) }`.

Matching `k` puts the swap position at `S k'`, structurally after the boundary `1`, so both writes cut exactly.

`PartLt(n, x, hne) : Lt((let b = x; Partition(n, &b, hne)), n)` is a statement about `Partition` itself, as `AddMZero` is about `AddM`. Its type at the call site mentions the sealed program that `k` holds.

**Trace** (arm `S f'`, `S m`):
- `Partition` closes off, leaving `*a ↦ P` and `k ↦ K`.
- `&(*a)[0..K]` cuts. The recursive call closes off on the fuel and fills the loan with `F_L = ⌈let c = P[0..K]; QS(f', K, &c, ⋆); c⌉`.
- `&(*a)[S K..n]` is placed by `K ≼ S K`.
- The final array is `⟨Z | F_L | K | P[K] | S K | F_R | n⟩`.

**Specs, by recursion on the length.** The match refines `a`'s stored type, so every obligation at a numeral index computes to `True`, and `Sub(S m, 1)` computes to `m`.

```
def Sorted (n : Nat) (a : Array(Nat, n)) : Prop by n := (
  match n {
    Z => True,
    S m => match m {
      Z => True,
      S _ => And(Le(a[0], a[1]), Sorted(m, a[1..n | ⟨refl, LeRefl(n)⟩])),
    },
  }
)
def Count (x : Nat) (n : Nat) (a : &Array(Nat, n)) : Nat by n := (
  match n {
    Z => 0,
    S m => Add(EqN(x, clone((*a)[0])), Count(x, m, &(*a)[1..n | ⟨refl, LeRefl(n)⟩])),
  }
)
def QSSorted (f : Nat) (n : Nat) (a : Array(Nat, n)) (hf : Le(n, f)) :
    Sorted(n, (let b = a; QS(f, n, &b, hf); b)) by f := …
def QSPerm (f : Nat) (n : Nat) (a : Array(Nat, n)) (hf : Le(n, f)) (x : Nat) :
    Id Nat (let b = a; QS(f, n, &b, hf); Count(x, n, &b)) (let b = a; Count(x, n, &b)) by f := …
```

**The proof.** `QSSorted`'s proof runs `QS`'s steps on a local, then applies the glue lemma `SortedCut(n, x, k, hk, hl : Sorted(k, x[0..k]), hr : Sorted(Sub(n, S k), x[S k..n]), hu : Ub(x[k], k, x[0..k]), hb : Lb(x[k], …, x[S k..n])) : Sorted(n, x)` to the final array.
- `x[0..K]`, `x[K]` and `x[S K..n]` reduce, through exact windows, to `F_L`, `P[K]` and `F_R`.
- The induction hypotheses `QSSorted(f', K, P[0..K], …)` and `QSSorted(f', Sub(n, S K), P[S K..n], …)` have exactly `F_L` and `F_R` in their types, since they are the same closed programs.
- `hu` and `hb` come from `PartOk` together with `UbPerm`/`LbPerm`.

| Fact | Status |
|---|---|
| Neither call moves the pivot, and each half is untouched by the other call | **Free** (visible in the value) |
| The halves have lengths `K` and `Sub(n, S K)`, and keep them | **Free** (fixed by the borrow types) |
| The induction hypotheses are about the goal's exact pieces | **Free** (the same sealed programs) |
| `SortedCut` and `CountCut` | Lemmas, by induction over the cons view. Flattening with numeral offsets is needed; under nesting, `ProjProj` is needed too |
| `UbPerm`, `LbPerm` | Lemmas about `Count` and `Le` |
| `PartLt`, `PartOk` | Lemmas: the invented stratum, as in DLLBC (R15). In the shape above no axiom is needed; a Lomuto partition needs hints or `SetGetOther` |
| Fuel arithmetic | `Nat` lemmas |

**The recursion is not structural.** `K` is a sealed program, and `≼` cannot show `K ≺ n`, so `QS` and `QSSorted` recurse on fuel instead (measure recursion is a ROADMAP item). **[vs DLLBC]** There is no wall from matching the length and then cutting at a symbolic index (T2, R12), and no citation at cuts (C8), because no length is ever refined.

### B3: insert into a computed bucket

```
inductive Bucket := BNil | BCons(k : Nat, v : Nat, t : Bucket)

def InsertB (b : &Bucket) (k : Nat) (v : Nat) : Unit by b := (
  match *b {
    BNil => *b := BCons(k, v, BNil),
    BCons(k', v', t) => (
      let e = EqB(k', k);
      match e { true => v' := v, false => InsertB(&t, k, v) }
    ),
  }
)

def Insert (cap : Nat) (hc : Lt(0, cap)) (slots : &Array(Bucket, cap)) (k : Nat) (v : Nat) : Unit := (
  let i = Mod(k, cap);
  InsertB(&(*slots)[i | ModLt(k, cap, hc)], k, v)
)
```

- **The obligation.** It is `Lt(⌈Mod(σₖ, σ_cap)⌉, σ_cap)`, and `ModLt`'s type evaluates to the same normal form.
- **The run.** The element borrow cuts the array. `InsertB` matches the neutral `σ[I]` and closes off, leaving the owner as `⟨σ[0..I] | ⌈let d = σ[I]; InsertB(&d, k, v); d⌉ | σ[S I..cap]⟩`.
- **Free:** every other slot, and the slot-level law "`Insert` is a one-slot update", which is `refl`, shaped like `FrameM`.
- **Lemma:** `FindB` after `InsertB`, by bare recursion, like `InsertMEq`.
- **The pointwise `Find` spec.** It splits on `EqB(Mod(q, cap), Mod(k, cap))`, which D34 generalises.
  - The `true` arm transports the index to `I` (by `EqBSound` and `J`), and then the read is definitional.
  - In the `false` arm, `J ≠ I` cannot be placed, so the read is `cat(…)[J]`, and the arm needs `SetGetOther`: an **axiom**, or a lemma once hints exist.
- **[vs DLLBC]** DLLBC's packed-invariant walls (`14-packed-borrows.md`) do not arise, because Ochr has no dependent fields, so the invariant is an ordinary lemma. They will return with subset types.

### B4: a bounds proof from a runtime comparison

```
def Get (n : Nat) (a : &Array(Nat, n)) (i : Nat) (d : Nat) : Nat := (
  let b = LeB(S(i), n);
  match b {
    true => clone((*a)[i | LeBSound(S(i), n, refl)]),
    false => d,
  }
)
def LeBSound (x : Nat) (y : Nat) (e : Id Bool (LeB(x, y)) true) : Le(x, y) by x := …   // bare recursion; match e {} where Eq Bool false true ≡ False
```

- **Why `refl` checks.** In the `true` arm, [Split-gen] has recorded `⌈LeB(S σᵢ, σₙ)⌉ := σ_b := true`. So `LeBSound`'s parameter type re-derives that sealed program, maps it to `true`, and computes to `Eq Bool true true ≡ True`, which `refl` proves.
- **Kernel support: none.** It takes one lemma per comparison function. `if h : i < n { … }` would be sugar for exactly this.

## 4. The principles

### 4.1 Read from syntax, or fail-safe

| Decision | Read from | Fail-safe? |
|---|---|---|
| Erasure | Unchanged. Indices are data, `\| h` is a proof position, and range lengths are type positions | Syntactic |
| A place's obligation | `p`'s stored type, which must have an `Array` head (D49) | A neutral type is a type error |
| [Locate]: the window, and which loans end | `≡` and `≼` on the boundaries | Yes. An undecided comparison widens the window, so more loans end (a later use is an error) or the result is a stuck `cat` (a correct neutral) |
| [Cut], merge | `≡` and `≼` | Yes. Undecided means stuck, never a different piece |
| A window that may contain `⊥` | The same | An error |
| [Close]'s row, a function's class, owners | Unchanged | — |
| Hints (optional) | A proof's stored type | A neutral type is no hint |

Substitution preserves `≡` and `≼`, so a more refined path decides a superset of what a less refined path decides. No path ever picks a *different* segment.

### 4.2 The generic call and its instances

1. **Window.** The generic call may end a loan that an instance keeps. The observations still agree by canonical observation, because when and in what order borrows end does not matter. A later use of the ended borrow is rejected on the generic path, so acceptance there implies agreement. This rests on the canonical-observation conjecture, which Ochr already depends on.
2. **Cut.** The generic `cat(W)[a..b]` and an instance's structural cut must agree after substitution. This needs **projection normalisation to commute with substitution**: `nf(V[a..b])θ = nf(Vθ[aθ..bθ])`. It holds if every reduction fires only on facts that substitution preserves (`≡`, `≼`, numerals, the `Add` rules), and every stuck form keeps its inputs. It is the array instance of "refinement commutes with closing off". It should be fuzzed before it is believed.
3. **Coordinates.** At the generic call `σ'[0]`; at an instance `σ[i..j][0]`. Flattening sends both to `σ[i]` by the same rule.
4. **`⊥`.** A read of a window that may hold `⊥` is rejected on the generic path, even if an instance would accept it. That is rejection only.
5. **Length zero.** The zero-length clause of [Eq-Arr] fires once `σₙ := Z`, and commutes with substitution.

DLLBC's C9 (a normalisation justified on symbolic values and wrong on concrete ones) would live in merge and zero-width dropping here. So loaned zero-width segments are kept, and the differential must run arrays at both concrete and symbolic lengths.

### 4.3 The set model

- **Arrays.** `⟦Array(T, n)⟧ = ⟦T⟧^n`. A segment list denotes the concatenation of its segments.
- **Projections.** `A[a..b]` denotes a slice. It is total, because the place that created it carried `a ≤ b ≤ |A|`. `init(f, n)` denotes `(f 0, …, f (n−1))`.
- **Range loans.** A range loan's backward function is slice replacement. Fills are values of the slice type, as today.
- **Arithmetic.** `Le`, `Sub` and `Add` denote their definitions. The machine's structural facts (`Z` least, `x ≤ S^k x`, the `Add` rules, `x ⊖ x = 0`) are theorems about ℕ.
- **[Eq-Arr].** It identifies propositions with equal truth values: concatenation is injective at equal cuts, and `⟦T⟧⁰` is a singleton. So it needs `propext`, as D47 and D52 do.
- **Axioms.** The axioms (`SetGetOther`, and `ProjProj` under nesting) are theorems of the model.
- **Well-formedness.** Preservation needs condition 7 (§2, item 19).

## 5. Paper cost

**Body** (currently about 24 of 25 pages):

| Where | What | Size |
|---|---|---|
| Syntax and value figures | `Array(T, n)`, the two places, segments and projections | 3 lines |
| §4 | [Locate], [Cut], the extended [Access], merge, and B1's trace | ≈0.5 page |
| §5 | [Eq-Arr] | ≈0.1 page |
| §6 | obligations from stored types; [Rec] | ≈0.1 page |
| §9 | `Le`/`Sub`/`Add` as the second non-uniform point; R13; no `Vec` | ≈0.2 page |
| Related work | DLLBC's carve, VST `split3seg`, Aeneas (one range at a time), RefinedRust (one hole) | ≈0.15 page |

The total is about **1.1 to 1.3 pages**. That means cutting about a page elsewhere, or moving B1's trace to the appendix, which leaves about 0.7 page.

**Appendix**, about **2 to 2.5 pages**:
- the full rules: values, content through segments, [Locate], [Cut], merge, flattening, the place rules, [Eq-Arr], the obligations in [T-Read], [T-Borrow] and [T-Assign], [Rec], and well-formedness condition 7;
- notes with a counterexample for each fail-safe choice: a zero-width loan, a refused overlap, and a read meeting `⊥`.

**Meta section:** one more conjectured property (item 2 of §4.2).

## 6. Risks, open questions, verdict

**Risks.**
1. **The normaliser is new attack surface.** It is the kernel's first normalisation that consults the normal forms of *numbers*. Every two-path bug so far was a normal-form consultation that was not monotone. Every consultation here is monotone, but the commutation property is unproved.
2. **Places now contain terms.** That touches pattern resolution (D32), footprints, captures (D22) and the order of [Access]. Each change is small; together they are the kind of cross-cutting change that produced BoomL and BoomB.
3. **Incompleteness at symbolic offsets.** It shows up as stuck `cat` reads after writes at unrelated positions, as `Add(σ, σ')` neutrals, and as `Le(x, x)` that does not compute. DLLBC's experience: "nothing in the mathematics was hard; everything in the plumbing was new".
4. **The R13 wall.** Without hints, in-place scans must use clone-swaps or cut-relative indexing.
5. **Kernel-known arithmetic.** `Le`/`Sub`/`Add` become a second non-uniform point after `True`/`And`, which a reviewer may call ad hoc. The answer: Lean's kernel knows `Nat.add`, `Nat.sub` and `Nat.ble` too.
6. **Unary indices.** They cost checker time: DLLBC's hashmap differential shrank from capacity 32 to 8. And they are not `usize`.
7. **The first axiom.** `SetGetOther` (without hints) would be Ochr's first axiom. It is standard and true in the model, but it changes the calculus's character.
8. **Paper space.** About one more page in a full body.

**Open questions.**
- Ranges by endpoints or by offset and count? (`Sub`, or `Add` only.)
- Should `Le(x, x) ≡ True` be a conversion rule? It would remove every `LeRefl` in §3.
- Should hints go in stage 1? They lift R13, and they turn `SetGetOther` into a lemma.
- Are flattening, the `Add` rules and merge confluent together? This is a completeness question, not a soundness one.
- How do `Vec` (which needs dependent fields) and shared slices (which need no disjointness) layer on top?

**Verdict: worth implementing, staged.** This assumes the library probe confirms it cannot make B1's frame definitional. I expect it cannot: right-nested values have no prefix sub-places, so there the frame is a provable lemma, not a definition.

The primitive delivers what the thesis needs: the untouched parts of an in-place algorithm's array stay in the environment, literally, as the predecessor field does for `Nat`. It needs no arithmetic decision procedure. And it avoids DLLBC's three worst walls:
- length refinement at cuts (C8, T2, R12): lengths are never solved;
- the state/knowledge fold (C5, R9): snapshots are values;
- the audit re-typing a carved payload (`14-`, `s1P2a`): nothing re-types the owner.

What it does not make free is index algebra. Gluing, read-after-write at unrelated indices and pointwise statements remain lemmas or axioms, as in DLLBC ("the frame dissolves, gluing does not").

**Stage 1:**
- the former, segment lists, and projections in atom coordinates;
- [Locate], [Cut] and merge with `≡` and `≼` only;
- flattening with the `Add` rules, and [Eq-Arr];
- `Le`/`Sub` obligations;
- `Init`, literals and `clone`;
- fuel or length recursion, with no hints;
- `SetGetOther` as a declared axiom.

Measure it on B1–B4 and the two case studies before adding hints or the [Rec] extension.

**Confidence.** This design has not met a checker, and DLLBC's desk design reversed twice on contact. I expect it to break in three places: moves out of elements inside windows that were never cut; zero-width segments at concrete lengths; and callees losing exactness where a caller cut at unrelated symbolic points.
