# Arrays as a library: a user-defined model, a primitive runtime

Design probe (arrays-library), 2026-09-29, against RULES v2.1 with D52 and D53 assumed. The rival route (arrays as kernel primitives) is arrays-primitive's note. Evidence: a scratch probe of 68 declarations, run through the checker at 96d788a1 (D52 build), all verdicts as expected, not committed (§7).

**Verdict.** The route works. Arrays become about ten native functions behind an `implemented by` link, over a model written in ordinary Ochr. The kernel changes are all static: two declaration flags, the link attribute, and the data universe that D48 already needs. No machine rule changes. The probe checks, in today's checker: B1's "the rest is unchanged" for an opaque callee, with one library lemma; quicksort's program, which runs to the right answer inside the checker; element borrows; and a dependent `if` producing bounds proofs. It is weaker than primitives in two places. First, sub-range borrows are scoped continuations, not places. Second, three or four facts that a segment representation would give by definition are one-induction library lemmas: split-then-join is the identity, the suffix of a join is the joined suffix, and get-after-set. Recommendation: implement this route first (§6).

## 1. The design

### 1.1 The logical model

A list is the obvious model and it is Lean's. In a list a suffix is a sub-place (`xs.t.t…`) but a prefix is not. Three candidates:

- **M1, a list, length computed** (`Vector(T)` wraps `List(T)`, `Len` is a function). This is right for growable vectors, and element and suffix borrows are ordinary returned borrows (probe `NthMut`, `DropMut`, both the `TailM` shape). It is wrong for views. A callee given `&List(T)` may, in the model, change its length, so after an opaque callee the logic cannot recover the old suffix by position: `B1DropOpaque` is rejected. Bounds proofs are also snapshots of the old contents, `Lt(i, Len(*xs))`, so they go stale after any write (`StaleBound` is rejected: the second write needs a new proof about `Len(⌈…*r := 5…⌉)`). This is DLLBC's length-lemma tax.
- **M2, fixed-length cells by large elimination**: `Cells(T, n) := match n { Z => Unit, S m => T × Cells(T, m) }`. The length is in the type, so no function of type `Π(x : &Slice(Cells(T, k))). Unit` can change it, and a bounds proof `Lt(i, n)` mentions only `n`: writes never make it stale (the probe's `Swap` reuses both bounds proofs after its writes). Values are nested pairs; a prefix is still not a place.
- **Prefix as a place** (a concatenation tree `Leaf | Cat(l, r)`, or a zipper). A split point becomes a place, but the shape becomes part of the value: `Cat(Take σ, Drop σ)` and `Leaf(σ)` are different constructors, so by D47 the logic *disproves* that a do-nothing split leaves the array unchanged, a fact the runtime cannot observe. If the shape moves into the type (a zipper indexed by its focus), the borrow's type fixes it, and refocusing needs a continuation anyway. Rejected.

**Decision.** Owned, growable `Vector(T)` uses M1. Views (what sub-range borrows and element access work on) use M2. Two models means bridging lemmas (`ToCells`/`FromCells` round trips, §3.5), but each is the natural model for its job, as in Rust's `Vec<T>` and `[T]`.

`&Cells(T, n)` at a symbolic `n` is rejected today (D48: `⌈Cells(σ)⌉` is not known to be data; probe `CellsBorrow`). The probe works around this for a fixed element type by boxing each tail, `Cell(R) := MkC(h : Nat, t : Box(R))`, so that every borrow is of an inductive head (`&Box(Cells(n))`, admitted). With the data universe (K1, §1.5) the boxes go and `T` is generic.

### 1.2 Sub-range borrows

[End] only substitutes a borrow's final content for its loan. It cannot run put-back code. That decides the question.

- **Returning several borrows (the ROADMAP's multi-result design) is not expressible for a prefix.** [Close]'s fill for a returned borrow is "re-run the call, write the hole through the returned borrow, read the owner". Each returned borrow must therefore point at a *place* of the owner, and in M1 or M2 no place holds exactly a prefix. Restructuring the owner so that one does (a `Cat` node) is the shape leak above. Suffixes and single elements *are* places, so `SuffixMut` and `GetMut` are ordinary returned borrows.
- **Continuation passing is expressible today** (probed). `WithSplit(…, s, k, h, f)` moves the view's model out, builds the two pieces as locals, calls `f(&l, &r)`, and after `f` returns writes `Join(l, r)` back. The put-back is ordinary code *after a call returns*, which Ochr has; it never needs to run inside [End].
- **Declared backward functions (optional K5)** would give returned sub-range borrows. A primitive would declare its fill instead of having [Close] synthesise it: `SplitAtMut` returns `borrow_k₁ ⌈TakeS(σ)⌉`, `borrow_k₂ ⌈DropS(σ)⌉` and leaves `⌈JoinS(loan_k₁, loan_k₂)⌉` in the owner. That is a sealed program with two holes, which the machine already allows. Owners, footprints and the frame property are unchanged, and the native code realises `JoinS` by aliasing. This is one new rule, a lens, and the only way to lift the continuation costs below.

The model of `WithSplit` must be **lazy**: the pieces are separate by-value calls `TakeS(…, clone(v))` and `DropS(…, v)`, each closed off as a leaf when stuck, not one `SplitVec` whose stuck result would stop the model before `f` runs. Laid out this way, at the caller `f` really runs on sealed pieces, and the result is `*s = ⌈JoinS(f's fill of ⌈TakeS(σ)⌉, ⌈DropS(σ)⌉)⌉`. The untouched suffix is literally `⌈DropS(σ)⌉`.

Continuation costs, each measured:
1. **Closures capture no borrows**, so a continuation cannot use the caller's other borrows. They must be threaded through the primitive's signature, which fixes the arity, or passed by value.
2. **A continuation is checked at its own generic call** ([T-Fix]), so it knows nothing about what its borrows hold. A captured fact about `Take(1, *a)` does not reach `*l` (`ContNoFacts` is rejected, with `hi` of type `Le(1, Len(⌈Take(1, σ0)⌉))` where `Le(1, Len(σ1))` was expected). Facts must travel in the continuation's type (`WithSplitH`/`ContFacts` pass). In M2 the most common facts, lengths, travel for free in the borrow types. `ZeroAll` recurses structurally through a split with no threaded proof.
3. The continuation's result is data (`R : Type`). Proofs never need `WithSplit`: erased code works on the model directly (`TakeC`, `DropC`).

This also answers DLLBC's two structural walls. DLLBC's "a body cannot both match its length and carve at a symbolic index" (¶5.1, T2) does not arise: [Split] refines `n := S m` everywhere, and the split point enters as data, so the probe's `QS` matches `n` and then splits at a computed `k` in one body. DLLBC's "two live symbolic cursors are unwritable" (R13) does arise: a second `GetMut` on the same view ends the first borrow ([Access]). So a swap is two copy reads and two element writes, and the partition does one swap per level (DLLBC's shape).

### 1.3 Runtime primitives and the link

`def f … := b implemented by "sym"` means: the checker checks `b` and runs `b` everywhere (both evaluation paths, every conversion, every sealed program) and never runs `sym`; the compiler calls `sym` instead of compiling `b`. Model bodies are never run at runtime, so they may be as wasteful as proofs need: `clone` the whole array, rebuild it.

That freedom buys one definitional fact. A read through a returned element borrow leaves a put-back program in the owner (`ReadNoop` is rejected: `*xs` becomes `⌈let c1 = σ0; let r = NthMut(&c1, σ1, ⋆); *r := ⌈…*r⌉; c1⌉`, not `σ0`). A **copy-read primitive** whose model is `NthS(clone(*s), i, h)` passes the array by value to the stuck call, so no borrow is closed off and `*s` stays `σ` (`GetCNoop` passes).

**Representation relation ≈** (between concrete machine values and native memory). `MkVector(xs)` ≈ a (ptr, len, cap) triple with len = |xs| and slot i ≈ xs[i]. The content `MkSlice(c)` of a borrowed view ≈ a pointer whose slot i ≈ the i-th component of `c` (i < n). A borrow `&Slice(Cells(T, n))` is that pointer, and `n` is an ordinary runtime argument the program already holds (Ochr has no erased data parameters), so the pair is Rust's `&mut [T]`. An element borrow ≈ a pointer to its slot. Elements relate by their own ≈. For `Nat`, that is its native representation, which is a separate link and not specific to arrays.

**[Link]** For each `implemented by` function `f` and every concrete call `f(w̄)` (no σ, no sealed program) with w̄ ≈ w̄♮, if the machine runs the model to ⟨Ω', v⟩, then `sym(w̄♮)` terminates and:
- returns v♮ ≈ v;
- leaves every buffer reachable from a borrowed argument ≈ the final content the machine leaves behind that borrow;
- writes nothing else.

For a returned borrow the pointer is the slot whose final content [End] substitutes for the hole. For `WithSplit` and `WithSlice` the obligation is relational: it must hold for every continuation f ≈ f♮ that itself satisfies [Link] (by induction on the program), with the two views ptr and ptr+k.

**Testing.** Use a differential in which the checker's machine is the reference interpreter. Run the model on small concrete inputs and the native code (C or Rust, or a stand-in backed by Lean's `Array`) on the related inputs, then compare results and final buffers. For the higher-order primitives, generate continuations from a small grammar: write `l[i]`, write `r[j]`, split again, return a read. The probe's `QSRun` is the model half of such a test: `QS(4, 4, [3,1,4,2])` evaluates to `[1,2,3,4]` by `refl`, and `QSRunWrong` is rejected with `False ∧ False`. DLLBC's cross-program differential is the precedent.

### 1.4 The boundary: no owned sub-arrays at runtime

The objection was that owning part of an array suggests it can be moved elsewhere cheaply, which real memory does not allow. Here, **runtime code never owns a sub-array, and never sees the representation**:
- The only owned array value is a whole `Vector`, a heap buffer; moving it moves a pointer.
- A part of an array is only ever a `Slice`, which is *unsized*: runtime code can only borrow it and hand the borrow to primitives or to other functions.
- The owned pieces inside `WithSplit`'s model exist only in a body the runtime never runs. They are a proof device, as Lean's `Array` is a `List` in the logic.

The rules:
- **[Abstract]** A declaration may be marked `abstract`. Its constructors, and matches whose arms name them, may occur in a *runtime* position (not erased, P2) only inside an `implemented by` body of the same block. In erased positions (types, proofs) they are unrestricted, so proofs reason about the model directly. A declaration whose body uses an abstract constructor at a runtime position must be `implemented by`.
- **[Unsized]** An inductive may be marked `unsized`. `&A` is well formed for an unsized `A`. An unsized type is not in `Data`, so it never instantiates a type variable `T : Data`: generic code that moves a `T` never moves a view (Rust's implicit `Sized` bound). In a runtime position outside an `implemented by` body, a place of unsized type occurs only as `&p`. Reading, moving, assigning and matching it are errors. Constructing one is already excluded by [Abstract].

With these, runtime code cannot walk the model of a flat buffer, cannot take a view's contents out, and cannot overwrite a view wholesale. Everything representation-dependent is behind a link.

### 1.5 Kernel changes

| | change | why | needed by primitives too? |
|---|---|---|---|
| K1 | a `Data` universe (the D48 open item): `&T` for `T : Data`; a data-valued type function (`Cells`) is borrowable at symbolic arguments | generic element borrows `&T`; symbolic-length views | yes for generic `&T`; its lengths come from the kernel instead |
| K2 | `unsized` flag and [Unsized] | views are borrow-only | the analogous rule for range places |
| K3 | `abstract` flag, [Abstract], the `implemented by` attribute | the boundary and the link | no |
| K5 (optional) | declared backward functions | returned sub-range borrows instead of continuations | no (places) |
| K6 (shared) | recursion on a measure | quicksort without runtime fuel | yes |

The view wrapper takes the model *type* as a parameter, `unsized abstract inductive Slice (R : Data) := MkSlice(c : R)` used at `R := Cells(T, n)`, as the probe's `Box` did. So no relaxation of D36's first-order fields is needed: a parameter field is already allowed. Dependent fields (the ROADMAP item) are *not* needed. A proof field about `items` would forbid borrowing into `items`, which kills element borrows.

## 2. What is primitive or trusted, and what stays user code

**Trusted:** the native bodies of
- the views: `GetMut` (element borrow), `Read` (copy read), `WithSplit` (two sub-views, scoped);
- the vector: `VNew`, `VPush`, `VPop`, `VLen`, `VGetMut`, `WithSlice` (the whole vector as one view), and `Vector`'s drop glue (free);

together with the relation ≈ and [Link] for each: nine functions plus drop glue. The growth policy of `VPush` is native. Nothing else is trusted for arrays. Nat's native representation, if Nat is not compiled unary, is the same kind of link, and it is not array-specific.

**Static (checked, not trusted):** K1–K3.

**User code (checked; compiled from source, or erased):**
- the index type `Nat` and bounds as `Lt(i, n)` proofs;
- `Le`, `Lt`, `Add`, `Sub`, `Mod`;
- comparisons yielding proofs (`LtDec`, B4);
- the models `Cells`, `TakeC`, `DropC`, `JoinC`, `NthC`, `SetC`, `List`, `Len`, `ToCells`/`FromCells`;
- every spec function (`Sorted`, `Count`, `Find`) and every lemma;
- `Swap`, `Set`, `Fill`, `Replicate` (by `VPush`), resize. The probe's `Swap` is plain user code over `Read` and `GetMut`.

The length of a view is the `n` in its type, which the program holds: no primitive. `VLen` exists only because a vector's model length is computed.

## 3. Benchmarks

Syntax: current (comma-separated arms, bodies in parentheses) plus `abstract`, `unsized`, `implemented by` and `T : Data`. `View(T, n)` abbreviates `Slice(Cells(T, n))`. The probe checked the Nat-element versions with boxed tails and `&Box(Cells(n))`.

### 3.1 B1: borrow the first k, call f, the rest is unchanged

```
def WithSplit (T : Data) (R : Type) (n : Nat) (k : Nat) (s : &View(T, n)) (h : Le(k, n))
    (f : Π(l : &View(T, k)) (r : &View(T, Sub(n, k))). R) : R implemented by "slice_with_split" := (
  let v = *s;
  let l = TakeS(T, n, k, clone(v), h);
  let r = DropS(T, n, k, v, h);
  let res = f(&l, &r);
  *s := JoinS(T, n, k, l, r, h);
  res
)

def B1Join (T : Data) (n : Nat) (k : Nat) (g : Π(x : &View(T, k)). Unit) (s : &View(T, n)) (h : Le(k, n)) :
    Id Unit (WithSplit(T, Unit, n, k, s, h, λ(l : &View(T, k)) (r : &View(T, Sub(n, k))) : Unit => g(l)))
      (*s := JoinS(T, n, k, (let c = TakeS(T, n, k, *s, h); g(&c); c), DropS(T, n, k, *s, h), h)) := refl

def B1 (T : Data) (n : Nat) (k : Nat) (g : Π(x : &View(T, k)). Unit) (s : &View(T, n)) (h : Le(k, n)) :
    Eq (View(T, Sub(n, k)))
      (let c = *s; WithSplit(T, Unit, n, k, &c, h, λ(l : &View(T, k)) (r : &View(T, Sub(n, k))) : Unit => g(l)); DropS(T, n, k, c, h))
      (DropS(T, n, k, *s, h)) := (
  DropJoinS(T, n, k, (let c = TakeS(T, n, k, *s, h); g(&c); c), DropS(T, n, k, *s, h), h)
)
```

**By definition:** the join form. After the call, `*s` is the join of g's result on the old prefix with the old suffix, literally (`B1JoinC`, `B1Join`: `refl`, g opaque).
**One lemma:** the projection form, the suffix of `*s` equal to the old suffix. It needs `DropJoin : Eq _ (DropC(n, k, JoinC(n, k, l, r, h), h)) r`, one induction on `k` (12 lines), plus its view wrapper (`DropJoinB`, one `J`). It holds for *any* `l : Cells(T, k)`, so it holds for any g, because the new prefix's length is its type (`B1Proj` passes). In M1 this form is unprovable for opaque g (`B1DropOpaque` is rejected). Even a do-nothing continuation needs `DropAppendTake` plus a length hypothesis (`B1Drop` rejected, `B1DropLemma` passes).
**Primitives:** the projection is definitional (a segment boundary).

### 3.2 B2: quicksort

The probe's program (checked), condensed. `Partition` peels the head and splits the tail with one swap per level. The probe decides `k ≤ m` and `1 ≤ Sub(S m, k)` with runtime `LeDec` rather than the lemmas written here.

```
def QS (fuel : Nat) (n : Nat) (s : &View(Nat, n)) : Unit by fuel := (
  match fuel {
    Z => (),
    S f => match n {
      Z => (),
      S m => (
        let k = Partition(m, &*s);
        WithSplit(Nat, Unit, S m, k, s, PartLe(…),
          λ(l : &View(Nat, k)) (r : &View(Nat, Sub(S m, k))) : Unit => (
            QS(f, k, l);
            WithSplit(Nat, Unit, Sub(S m, k), 1, r, RestNonEmpty(…),
              λ(p : &View(Nat, 1)) (rr : &View(Nat, Sub(Sub(S m, k), 1))) : Unit =>
                QS(f, Sub(Sub(S m, k), 1), rr))))
      ),
    },
  }
)
```

The recursion is not structural: the pieces are `⌈TakeS(…)⌉`, not subterms. The probe recurses on runtime fuel, which [Rec] accepts inside nested λs through the captured `f`. K6 would remove the fuel, as it would for primitives. `QS` is generic in `n`, so the unnormalised lengths `Sub(Sub(S m, k), 1)` never need converting. A function demanding a specific length expression would need a cast continuation (`J` transports the model value, so its round trip is definitional).

The statement (a sketch, not checked):
```
def QSSorted (fuel : Nat) (n : Nat) (s : &View(Nat, n)) (hf : Le(n, fuel)) :
    Sorted(n, Model((QS(fuel, n, &*s); *s))) by fuel := …
def QSPerm (fuel : Nat) (n : Nat) (s : &View(Nat, n)) (q : Nat) :
    let old = *s;
    Eq Nat (Count(q, n, Model((QS(fuel, n, &*s); *s)))) (Count(q, n, Model(old))) by fuel := …
```

The proof mirrors `QS`: build the pieces as locals of the proof, call the induction hypotheses on them, glue. **Free:**
- The left piece's final content is exactly the left call's result on `⌈TakeS(k, Part(σ))⌉`, and the right call cannot touch it: no locality lemmas (DLLBC's deleted stratum).
- The pivot cell is literally `⌈TakeS(1, DropS(k, Part(σ)))⌉`.
- Every piece's length is its type, and bounds proofs never go stale.
- `Sorted` and `Count` are ordinary recursion over the model.

**Lemmas:**
- the round trips `JoinTakeDrop` (needed to split `Count(Part(σ))`), `TakeJoin` and `DropJoin`;
- `CountJoin`;
- `SortedJoinPivot` and the bound glue (as for any quicksort);
- the partition's own spec.

**Primitives, by contrast:** `JoinTakeDrop` and the projections would be definitional, if symbolic segment canonicalisation works. But `Sorted`/`Count` over a primitive array need a recursor with its own ι-rules (DLLBC R10: three).

### 3.3 B3: hashmap insert into a bucket in place

```
inductive Entry := MkE(key : Nat, val : Nat)
inductive HashMap := MkHM(slots : Vector(List(Entry)), size : Nat)

def Insert (hm : &HashMap) (k : Nat) (v : Nat) (hcap : Lt(0, VSize(SlotsOf(*hm)))) : Unit := (
  match *hm {
    MkHM(slots, size) => (
      let cap = VLen(List(Entry), &slots);                    -- model VSize(clone(*v)): ⌈VSize(σs)⌉, no put-back
      let i = Mod(clone(k), cap);
      let b = VGetMut(List(Entry), &slots, i, ModLt(k, VSize(slots), hcap));
      let fresh = InsertB(b, k, v);                           -- in-place bucket insert, user code
      match fresh { true => size := S size, false => () }
    ),
  }
)
```

`cap` and the `VSize(slots)` in the proof are the same sealed program, because `VLen`'s model reads by copy (checked shape: `GetCNoop`). The `M1` element borrow is the checked `NthMut`. `hcap` is refined by the split on `*hm`.

**By definition:** the bucket write lands inside `slots` as `⌈…let r = VGetMut(&c, i, ⋆); *r := ⌈InsertB fill⌉; c⌉`.
**Lemmas:**
- `GetMutSet` (in place = functional, the `AddMEq` shape);
- `NthSetSame` and `NthSetOther` (Lean's `getElem_set_self`/`_ne`);
- `ModLt` and the bucket lemmas.

The invariant (cap > 0, keys in their slot) is a precondition, not packed, until dependent fields exist. **Primitives:** the frame for another slot `Mod(q, cap)` still needs a comparison with `i` and a lemma. B3 is roughly even.

### 3.4 B4: a bounds proof from a runtime comparison (checked)

```
inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

def LtDec (i : Nat) (n : Nat) : Dec(Lt(i, n), Le(n, i)) by i := (
  match i {
    Z => match n { Z => No(refl), S _ => Yes(refl) },
    S i' => match n { Z => No(refl), S n' => LtDec(i', n') },
  }
)

def GetOr (T : Data) (n : Nat) (s : &View(T, n)) (i : Nat) (d : T) : T := (
  let dec = LtDec(clone(i), clone(n));
  match dec { Yes(h) => Read(T, n, s, i, h), No(k) => d }
)
```

Today's inductives already express it: `Dec` is `Type₀` data with proof fields of parameter type (D36 allows parameter fields), and an arm binds its field as ⋆ at the parameter type (D49). At runtime `Dec` is a boolean. The recursive case converts because `Lt(S i', S n')` computes to `Lt(i', n')`. The probe checks `Dec`, `LtDec`, `LeDec` and `GetOr`.

**Finding (checker incompleteness).** A value that embeds a proof argument ⋆ breaks two things:
- a match on a `Dec` whose parameters mention a sealed program embedding ⋆, such as the result of a bounds-checked `Read`;
- a λ that captures such a sealed program.

Both fail with "cannot infer the type of the value ⋆". Minimal repro: `H(x : Nat, h : ⊤) : Nat by x` stuck on `x`, then `let y = H(x, refl); let d = LeDec(y, x); match d {…}`. The same with `Apply(λ(u : Unit) : Nat => y)` also fails. A split directly on `y` works. The workaround is to route the value through a function parameter (the probe's `Place`, `Finish`, `PartitionAt`, and the λ in `QS`). The case studies will hit this on every bounds-checked read that feeds a decision.

### 3.5 The lemma library users would rely on

| layer | items | lines (est.) |
|---|---|---|
| model: `Cells`, Take/Drop/Join, Nth/Set, `ToCells`/`FromCells` | 8 | 80 |
| round trips: JoinTakeDrop, TakeJoin, DropJoin (checked, 12 lines), To/FromCells ×2 | 5 | 70 |
| get/set: GetMutSet, NthSetSame, NthSetOther | 3 | 45 |
| counting: CountJoin, CountSet, CountSwap | 3 | 40 |
| order glue: SortedJoinPivot, AllLe/AllGe over Join, bound transfer by counting | 6 | 90 |
| vector: SizePush, NthPush (old/new), SizePop | 4 | 45 |
| Nat: Le refl/trans, Sub facts, ModLt, `LtDec` | 6 | 60 |

About 35 items and 430 lines, each an induction of the `AddMEq` or `DropJoin` kind. For comparison, DLLBC's array layer was 21 transferred items plus 21 for the partition, and its hashmap about 60 lemmas in 2,300 lines (a heavier encoding).

## 4. The principles

**Decisions read from syntax and declarations.**
- [Abstract] reads constructor names (declarations), the position's class (P2, syntactic), and the enclosing declaration's attribute.
- [Unsized] reads the declared flag of the head of a place's type. It is stable under refinement for D49's reason: refinement changes a type's parameters, never its head. And a stuck type of sort `Data` can never become unsized, since unsized types are not in `Data`. The generic call and every instance therefore decide the same way.
- More importantly, neither rule changes evaluation: the checker's machine runs model bodies everywhere. A misclassification could only accept a program whose native run is unfaithful. It could never yield a false proof.

**Generic path vs instance paths.** Nothing new in the logic. Primitives are ordinary definitions on both paths, and continuations are closures checked at their generic call like every closure. The two-path hazard moves to *machine vs native code*, and there it is [Link]: every concrete run of a model must agree with its native body. That is a finite list of functional-correctness claims about small functions, testable by differential. The checker must never run native code: Lean's kernel likewise ignores `implemented_by`.

**What the link costs the paper's claims.** It is not logical soundness: the logic never sees native code. It is runtime faithfulness. For user code, "the in-place program is what proofs are about" still holds. For the nine primitives the proofs are about a copying model, and the compiled code is a different program related by a trusted refinement. That is the two-program pattern the paper criticises, confined to a library written once, never paid per development. The paper must say so plainly next to §9's "the checked machine is not yet the compiled program". The primitive route puts the same trust into "the compiler implements the machine's segment rules", which the paper already assumes. The trust is comparable; this route's is explicit and enumerable.

## 5. Paper cost

The body would present:
- arrays as a library inside the case-study section, about 0.5 page of code, which the case studies need anyway;
- one paragraph on `implemented by` and the boundary (about 0.3 page);
- scope lines for K1 and K2 in §3 (about 0.2 page);
- optionally a row in the why-each-condition figure. The boundary is about faithfulness, not consistency, so it could instead be a sentence.

That is about 1 page including the case study, and about 0.5 page specific to arrays. The appendix would need K1–K3's rules (about 0.5 page). The body is at 24/25. The primitive route adds place forms, segment values, [Access]/[End] on segments, canonical forms and `Eq` on arrays: plausibly 2–3 pages of rules (arrays-primitive's note has the estimate).

## 6. Risks, open questions, verdict

1. **Continuations are second-class.**
   - They cannot capture borrows.
   - They are re-checked generically, so content facts must be threaded through their types (lengths come free).
   - A three-way split nests two continuations.
   - The result is data.

   Quicksort tolerates this (checked). Code holding several sub-range borrows alongside borrows of other structures would not. K5 removes all of these but adds a rule.
2. **Definitional gaps vs primitives.** Every split leaves a `JoinS` spine in the owner, even with a do-nothing continuation (`SplitNoop` is rejected). So after any split, "the array is still σ" is a lemma (`JoinTakeDrop`), and statements must be written against the join form. Projection after join and get-after-set are lemmas too.
3. **Reads through element borrows** leave put-back programs (`ReadNoop`). Copy-read primitives fix this for reads. Shared borrows would fix it generally, for both routes.
4. **Two models** (List for vectors, Cells for views) and the bridge between them.
5. **K1 is an open design problem** (D48). Without it, arrays are monomorphic and use the probe's boxed-tail encoding, which works today.
6. **The link for higher-order primitives is relational**, so tests only cover generated continuations.
7. **D53:** Nat indices move, so runtime reuse needs `clone`. Model bodies clone freely, which is harmless because they never run.
8. **The ⋆ incompleteness** (§3.4) should be fixed before the case studies.

**Verdict.** Worth implementing, and first. It delivers B1–B4. It adds no machine rule; its kernel changes are one universe (needed anyway), two flags and an attribute. It keeps user predicates as ordinary recursion, and it fits the page budget. Its honest weaknesses are scoped sub-range borrows and a handful of one-induction round-trip lemmas that segments would give by definition. Build K3 and K2, and the probe's model as `Std`'s array library. Run both case studies. Revisit primitives, or add K5, if continuation plumbing or round-trip lemmas dominate the case studies' line counts.

## 7. The probe

A scratch file (not committed, deleted) ran two blocks through the checker at 96d788a1:
- **Lists (M1), 36 declarations:** `Dec`, `LtDec`, `Nth`, `NthMut`, `GetOr`, `DropMut`, `WithSplit` (continuation), `B1Join` (refl), `Fill`/`FillRun` (fuel recursion through a continuation). Rejections as expected: `B1DropRefl`, `B1DropOpaque`, `SplitNoop`, `ReadNoop`, `StaleBound`, `ContNoFacts`, `B1Drop`, and the D48 rejection of `&Cells(σ)`.
- **Cells (M2), 32 declarations:** `GetMut`, `TakeC`/`DropC`/`JoinC`, `DropJoin`, `WithSplit`, `B1Proj` (opaque g, one lemma), `B1JoinC` (refl), `ZeroAll` (structural), `Swap`, `SplitP`, `Partition`, `QS`, and `QSRun` (runs to the sorted array; the wrong answer is rejected).
- **A repro file:** two failures, the ⋆ finding.
