# Arrays as a library: a user-defined model, a primitive runtime

Design probe (arrays-library), 2026-09-29, against RULES v2.1 with D52 and D53 assumed. The rival route (arrays as kernel primitives) is arrays-primitive's note.

This is v2. It folds in two decisions from the user:
1. An array's length lives only in its type: `Array(T, n)`, no runtime length. Code that needs `n` holds it as a Nat parameter or field, and growable vectors are user-defined.
2. No recursion over arrays: recursive functions recurse over an index (a Nat).

Evidence: two scratch probes of 68 and 44 declarations, run through the checker at the D52 build. Every verdict was as expected. The probes are not committed (§9).

**Verdict.** The route works under both decisions. Arrays become seven native functions plus drop glue, behind an `implemented by` link, over a model written in ordinary Ochr. The fixed-length type needs no dependent fields: the model `Cells(T, n)` is exactly `n` elements by construction.

The probes check, in today's checker:
- B1's "the rest is unchanged" for an opaque callee, with one library lemma;
- a Lomuto partition that recurses over a countdown index, with every bound discharged by an index lemma;
- quicksort over views, sorting an owned `Array(4)` inside the checker;
- a fixed-capacity container;
- B4.

Three extensions are still needed.
- **Recursion on a measure** (§5.2). Quicksort's recursive lengths are not structural subterms, so it needs strong recursion on its length.
- **Dependent fields**, for user-defined growable vectors and a resizable hashmap (§3). It is one extension that also covers proof fields, but for arrays only its Σ shape is usable.
- **A small relaxation of D36**, so that a struct can hold an `Array(T, n)` field.

The route is weaker than primitives in two places. Sub-range borrows are scoped continuations, not places. And a few facts that segments give by definition are one-induction lemmas. Recommendation: implement this route first (§8).

## 1. The design

### 1.1 The logical model

In a list, a suffix is a sub-place (`xs.t.t…`) but a prefix is not. Three candidates:

- **A list with a length parameter** (`Array(T, n) := Mk(items : List(T))`). Nothing ties `n` to `items` unless a proof field `h : Eq Nat (Len(items)) n` does. That is a dependent field, which D36 rejects today (probe `LArr`: "unknown constant items"). Even with dependent fields it is the wrong shape: the proof mentions `items`, so `items` becomes frozen (§3), and element borrows die. A list without the length (Lean's `Array`) contradicts decision 1. It also fails B1: an opaque callee may change a list's length (probe `B1DropOpaque`, rejected), and bounds proofs `Lt(i, Len(*xs))` go stale after every write (probe `StaleBound`, rejected).
- **Fixed-length cells by large elimination**: `Cells(T, n) := match n { Z => Unit, S m => T × Cells(T, m) }`. The length parameter is enforced by construction, with no proof field and no dependent field. A bounds proof `Lt(i, n)` mentions only the index and `n`, so no write can make it stale (the probe's `Swap` and `Scan` reuse their bounds across swaps). No function of type `Π(x : &Slice(T, k)). Unit` can change the length. **Chosen.**
- **Prefix as a place** (a concatenation tree, or a zipper). The split shape becomes part of the value. `Cat(Take σ, Drop σ)` and `Leaf(σ)` are distinct constructors, so by D47 the logic *disproves* that a split which changes nothing leaves the array unchanged, a fact the runtime cannot observe. Rejected.

Two types share the model, as Rust has `Box<[T]>` and `[T]`, but neither stores a length:
- `Array(T, n)` is owned and sized. At runtime it is a pointer to a heap block of `n` elements. Moving it moves the pointer.
- `Slice(T, n)` is a view: *unsized*, only ever behind `&`. At runtime it is a pointer into some block.

```
unsized abstract inductive SliceOf (R : Data) := MkSlice(c : R)
abstract inductive ArrayOf (R : Data) : Data := MkArray(s : SliceOf(R))
def Slice (T : Data) (n : Nat) : Type := SliceOf(Cells(T, n))      -- abbreviations: they unfold only to
def Array (T : Data) (n : Nat) : Data := ArrayOf(Cells(T, n))      -- abstract heads, never to Cells
def AsSlice (T : Data) (n : Nat) (a : &Array(T, n)) : &Slice(T, n) implemented by "arr_as_slice" := (
  match *a { MkArray(s) => &s }                                    -- a sub-place: an ordinary returned borrow
)
```

The wrappers take the model *type* as a parameter, so D36 accepts them as they are. `&Cells(T, n)` at a symbolic `n` is rejected today, because D48 cannot tell that `⌈Cells(σ)⌉` is data. The probe therefore boxes each tail, `Cell(R) := MkC(h : Nat, t : Box(R))`, which works today for a fixed element type. With the data universe (K1) the boxes go and `T` is generic.

### 1.2 Sub-range borrows

[End] only substitutes a borrow's final content for its loan. It cannot run put-back code.

- **Returning several borrows (the ROADMAP's multi-result design) cannot express a prefix.** [Close]'s fill for a returned borrow is: re-run the call, write the hole through the returned borrow, read the owner. So every returned borrow must point at a *place* of the owner, and no place holds a prefix. Suffixes and single elements are places, so `GetMut` and a suffix borrow are ordinary returned borrows.
- **Continuation passing is expressible today** (probed). `WithSplit(…, s, k, h, f)` moves the model out, builds the two pieces as locals, calls `f(&l, &r)`, and after `f` returns writes `Join(l, r)` back. The put-back is ordinary code after a call returns.
- **Declared backward functions (optional K5)** would allow returned sub-range borrows. `SplitAtMut` would return `borrow_k₁ ⌈TakeS(σ)⌉` and `borrow_k₂ ⌈DropS(σ)⌉`, and leave `⌈JoinS(loan_k₁, loan_k₂)⌉` in the owner: a sealed program with two holes, which the machine already allows. It adds one rule.

The model of `WithSplit` must be **lazy**. The pieces are separate by-value calls, `TakeS(…, clone(v))` and `DropS(…, v)`, each closed off as a leaf, so that at the caller `f` really runs. The result is `*s = ⌈JoinS(f's fill of ⌈TakeS(σ)⌉, ⌈DropS(σ)⌉)⌉`, whose suffix is literally `⌈DropS(σ)⌉`.

The costs of continuations, each measured:
1. **Closures capture no borrows.** Other borrows must be threaded through the primitive's signature, or passed by value.
2. **A continuation is checked at its own generic call.** A captured fact about `Take(1, *a)` does not reach `*l` (probe `ContNoFacts`, rejected). Facts travel in the continuation's type. With `Slice(T, n)` the commonest fact, the length, travels for free.
3. **The continuation's result is data.** Proofs never need `WithSplit`, because erased code works on the model directly.

### 1.3 Runtime primitives and the link

`def f … := b implemented by "sym"`: the checker checks `b` and runs it everywhere (both evaluation paths, conversion, sealed programs) and never runs `sym`. The compiler calls `sym` instead of compiling `b`. Model bodies never run at runtime, so they may clone and rebuild freely.

That freedom buys a definitional fact. A read through a returned element borrow leaves a put-back program in the owner (probe `ReadNoop`, rejected). A copy-read primitive whose model is `NthC(clone(*s), i, h)` gives the stuck call a value, not a borrow, so `*s` stays `σ` (probe `GetCNoop`).

**Representation ≈.**
- An owned `MkArray(MkSlice(c))` ≈ a pointer to a heap block whose slot i ≈ component i of `c`.
- A borrowed view whose content is `MkSlice(c)` ≈ a pointer, possibly into the middle of a block, with slot i ≈ component i.
- No length appears anywhere: the program's own `n` bounds every access, by proof.
- Elements relate by their own ≈; Nat's native representation is a separate link, not array-specific.

**[Link]** For each `implemented by` function and every concrete call with arguments related by ≈: if the machine runs the model to ⟨Ω', v⟩, the native code terminates, returns v♮ ≈ v, leaves every block reachable from a borrowed argument ≈ the final content the machine leaves behind that borrow, and writes nothing else.
- For a returned borrow, the pointer is the slot whose final content [End] substitutes for the hole.
- For `WithSplit` the obligation is relational: it holds for every continuation that itself satisfies [Link] (by induction on the program), with the two views at ptr and ptr + k.

**Testing.** Differential: the checker's machine is the reference interpreter. Run the model and the native code on related small inputs, and compare results and blocks. For `WithSplit`, generate continuations from a small grammar. The probe's `SortRun` is the model half of such a test: an owned `Array(4)` holding [3,1,4,2] sorts to [1,2,3,4] by `refl`, and the wrong answer is rejected with `False ∧ False`.

### 1.4 The boundary: no owned sub-arrays at runtime

The user's objection was that owning part of an array suggests it can be moved elsewhere cheaply. Here, **runtime code never owns a sub-array and never sees the representation.**
- The only owned array value is a whole `Array(T, n)`, a block pointer.
- A part of an array is only ever a `Slice`, which runtime code can only borrow.
- The owned pieces inside `WithSplit`'s model exist only in a body the runtime never runs.

- **[Abstract]** Constructors of an `abstract` declaration, and matches whose arms name them, may occur in a runtime position (not erased, P2) only inside an `implemented by` body of the same block. In erased positions they are unrestricted, so proofs reason about the model directly.
- **[Unsized]** `&A` is well formed for an `unsized` A. An unsized type is not in `Data`, so it never instantiates a `T : Data`: generic code that moves a `T` never moves a view (Rust's implicit `Sized`). In a runtime position outside an `implemented by` body, a place of unsized type occurs only as `&p`: no read, move, assign or match.

A single `Array` type, with moves banned only through derefs, would not be enough. Generic code over `A : Data` that moves through `*x` would move a view when instantiated at `A := Array(T, k)`. Hence the two types.

## 2. What is primitive or trusted, and what stays user code

**Trusted:** the native bodies of seven functions, plus drop glue:
- views: `GetMut` (element borrow), `Read` (copy read), `WithSplit` (two sub-views, scoped), `AsSlice` (the identity on the pointer);
- growth: `ArrEmpty : Array(T, 0)`, `ArrPush(T, n, a : Array(T, n), x : T) : Array(T, S n)`, `ArrPop(T, n, a : Array(T, S n)) : Array(T, n) × T`;
- drop glue: free the block.

Also trusted: the relation ≈ and [Link] for each. Nothing else about arrays is trusted.

**Static (checked):** K1–K4, and K6–K7 if adopted (§5.3).

**User code:**
- `Nat`, the bounds `Lt(i, n)`, `Le`, `Add`, `Sub`, `Mod`, and comparisons that yield proofs (`LtDec`, B4);
- the model: `Cells`, `TakeC`/`DropC`/`JoinC`, `NthC`/`SetC`, `Snoc`;
- every spec and every lemma;
- `Swap`, `Set`, `Fill`, `Replicate` (by `ArrPush`, recursing on `n`);
- the growable `Vec`, the hashmap and its resize.

## 3. Dependent fields, and growable vectors

`Vec(T) := Mk(n : Nat, items : Array(T, n))` stores its length as a field: the "code holds `n` as a field" case. It needs **dependent fields**: a field whose type mentions an earlier field. D36 rejects this today (probe `Vec`: "unknown constant n"). This is the same extension as proof fields (`h : Eq Nat (Len(items)) n`, `h : Sorted(xs)`): both are telescopic constructor types. The rules:

1. **[Ind]** checks the field types as a telescope. Each earlier field is bound to a fresh abstract value, as [Def] binds parameters. Positivity is unchanged: earlier fields occur only as arguments inside later field types.
2. **Field types** are computed from the earlier fields' current contents: `type(p.items) = Array(T, content(p.n))`. [Split] refines `σ := Mk(σ₁, σ₂)` with `Δ(σ₂) = Array(T, σ₁)`.
3. **[Frozen] (the new condition).** A field that a later field's type mentions (an *index field*) may not be borrowed, assigned or moved out alone, in any position; the value may only be replaced whole, and [T-Ctor] rechecks it. Reading is fine: erased reads copy, and runtime reads clone (D53). Without this, `(*v).n := 7`, or an opaque callee given `&(*v).n`, would leave `items : Array(T, old n)` claiming length 7. The rule is syntactic: which fields are index fields is read from the declaration.
4. **Injectivity (D52) must be restricted.** `Eq D (Mk(v̄)) (Mk(w̄))` cannot become a conjunction of per-field equations when a field's type depends on earlier fields that differ: `Eq (Array(T, n₁)) a₁ a₂` is ill-typed when `n₁ ≢ n₂`. Decompose only while the earlier fields on both sides are convertible, and otherwise leave the equation as is. This is fail-safe and incomplete. OTT's full rule needs a dependent conjunction, which Ochr lacks. Proof fields are ⋆ on both sides (D27), so they never block.
5. **[Close], sealed programs, observation and the set model (Σ-types) are unchanged.**

**Same extension, opposite consequences.** [Frozen] freezes whatever a later field's type mentions.
- In the Σ shape the frozen field is `n`, a Nat nobody borrows, so `&(*v).items` is fine: its type `Array(T, n)` cannot change while `n` is frozen.
- In the proof-field shape the frozen field is `items`, the data itself, so there are no element borrows and no in-place updates, only whole rebuilds with a new proof.

So arrays use the Σ shape plus `Cells`, never a proof field. A proof field whose invariant is re-checked at the end of the borrow would be DLLBC's packed-invariant audit wall (the pin lane); that is out of scope.

**What growth needs from the runtime.**

```
def Push (T : Data) (v : &Vec(T)) (x : T) : Unit := (
  match *v { Mk(n, items) => *v := Mk(S (clone(n)), ArrPush(T, clone(n), items, x)) }
)
```

`items` is moved out through the borrow and `*v` is made whole again (D53). The only primitive is `ArrPush`, which takes the array **by value**, and that is what makes `realloc` safe. Reading `items` ends every borrow into it ([Access]), so no live pointer can dangle when the block moves.

Neither the array nor `Vec` stores a capacity, so amortised O(1) growth needs the allocator to keep it: the native `ArrPush` grows the block geometrically and asks the allocator for its usable size (a `malloc_usable_size`-style query, or a hidden header word). The model never sees it. A capacity visible to the user (`Mk(cap, n, h : Le(n, cap), items : Array(Slot(T), cap))`) would need an uninitialised-slot type; that is out of scope. `ArrPop` needs no allocator support. Dropping a block needs no size, as with `free`.

A container holding an array at a *fixed* capacity needs no dependent field. It does need the field type `Array(T, cap)`, a type function applied to a parameter, which D36 rejects today (probe `HM0`, `HM1`). The workaround works today: take the model type as a parameter, `HMOf(R) := MkHM(slots : ArrayOf(R), size : Nat)` with `HM(cap) := HMOf(Cells(cap))`, and an element borrow through it checks (`HMSlot`). **K4** makes this direct: a field type may call an earlier data-valued type function on parameters. Positivity is unaffected, because the function was declared earlier and cannot mention the type being declared. With dependent fields, K4's arguments may also be earlier fields.

## 4. Benchmarks

Syntax: current, plus `abstract`, `unsized`, `implemented by`, `T : Data`, and the §5.2 recursion form `by n <` / `f(…) by h`. The probe checked Nat-element versions with boxed tails.

### 4.1 B1: borrow the first k, call f, the rest is unchanged

```
def WithSplit (T : Data) (R : Type) (n : Nat) (k : Nat) (s : &Slice(T, n)) (h : Le(k, n))
    (f : Π(l : &Slice(T, k)) (r : &Slice(T, Sub(n, k))). R) : R implemented by "slice_with_split" := (
  let v = *s;
  let l = TakeS(T, n, k, clone(v), h);
  let r = DropS(T, n, k, v, h);
  let res = f(&l, &r);
  *s := JoinS(T, n, k, l, r, h);
  res
)

def B1 (T : Data) (n : Nat) (k : Nat) (g : Π(x : &Slice(T, k)). Unit) (s : &Slice(T, n)) (h : Le(k, n)) :
    Eq (Slice(T, Sub(n, k)))
      (let c = *s; WithSplit(T, Unit, n, k, &c, h, λ(l : &Slice(T, k)) (r : &Slice(T, Sub(n, k))) : Unit => g(l)); DropS(T, n, k, c, h))
      (DropS(T, n, k, *s, h)) := (
  DropJoinS(T, n, k, (let c = TakeS(T, n, k, *s, h); g(&c); c), DropS(T, n, k, *s, h), h)
)
```

- **By definition:** after the call, `*s` is the join of g's result on the old prefix with the old suffix (probe `B1JoinC`: `refl`, g opaque).
- **One lemma:** the suffix of `*s` equals the old suffix. This is `DropJoin`, one induction on `k` (12 lines), valid for any g because the new prefix's length is its type (probe `B1Proj`).
- **Primitives:** definitional (a segment boundary).

### 4.2 B2: quicksort, recursing over indices only

The partition is Lomuto over two indices (checked; the probe differs only in names and the boxed encoding):

```
-- i < j, rem + j = n; recursion is on the countdown rem, structurally. Pivot at 0.
def Scan (n : Nat) (s : &Slice(Nat, n)) (p : Nat) (i : Nat) (j : Nat) (rem : Nat)
    (hij : Lt(i, j)) (hr : Eq Nat (Add(rem, j)) n) : Nat by rem := (
  match rem {
    Z => (
      let hin : Lt(i, n) = J(Nat, j, n, λ(z : Nat) : Prop => Lt(i, z), hr, hij);
      Swap(Nat, n, s, 0, i, LeTrans(1, S i, n, refl, hin), hin);
      i
    ),
    S r => (
      let hjn : Lt(j, n) = J(Nat, S (Add(r, j)), n, λ(z : Nat) : Prop => Lt(j, z), hr, LeAddL(r, j));
      let hr2 : Eq Nat (Add(r, S j)) n = J(Nat, S (Add(r, j)), Add(r, S j), λ(z : Nat) : Prop => Eq Nat z n, AddRS(r, j), hr);
      let x = Read(Nat, n, &*s, j, hjn);
      let b = Leb(x, p);
      match b {
        true => (Swap(Nat, n, &*s, S i, j, LeTrans(S (S i), S j, n, hij, hjn), hjn); Scan(n, s, p, S i, S j, r, hij, hr2)),
        false => Scan(n, s, p, i, S j, r, LeStep(S i, j, hij), hr2),
      }
    ),
  }
)

def Partition (m : Nat) (s : &Slice(Nat, S m)) : Nat := (
  let p = Read(Nat, S m, &*s, 0, refl);
  Scan(S m, s, p, 0, 1, m, refl, AddOneR(m))
)
```

Every bound is discharged by an index lemma, and none mentions the contents, so the swaps never invalidate one. The index lemmas are `LeRefl`, `LeStep`, `LeTrans`, `LeAddL`, `AddRS`, `AddOneR` and `SubPos`, each 5–10 lines and checked. The element comparison is a `Bool` (`Leb`): a `Dec` here would trip the ⋆ incompleteness (§4.4).

Quicksort itself recurses on the length:

```
def QS (n : Nat) (s : &Slice(Nat, n)) : Unit by n < := (
  match n {
    Z => (),
    S m => (
      let hk : Le(Partition(m, &*s), m) = PartLe(m, &*s);     -- a lemma about the call, stated before it
      let k = Partition(m, &*s);                               -- the same sealed program as in hk's type
      WithSplit(Nat, Unit, S m, k, s, LeStep(k, m, hk),
        λ(l : &Slice(Nat, k)) (r : &Slice(Nat, Sub(S m, k))) : Unit => (
          QS(k, l) by hk;                                      -- Lt(k, S m) is Le(k, m)
          WithSplit(Nat, Unit, Sub(S m, k), 1, r, SubPos(m, k, hk),
            λ(p : &Slice(Nat, 1)) (rr : &Slice(Nat, Sub(Sub(S m, k), 1))) : Unit =>
              QS(Sub(Sub(S m, k), 1), rr) by RestLt(m, k, hk))))
    ),
  }
)

def SortA (n : Nat) (a : &Array(Nat, n)) : Unit := QS(n, AsSlice(Nat, n, a))
```

**The recursion principle it needs.** The recursive lengths are `k` and `m − k` (from `S m = k + 1 + (m − k)`). Both are below `S m`, but neither is a structural subterm of it: `k` is the partition's result, a sealed program, and `Sub(Sub(S m, k), 1)` is not a subterm either. Structural recursion therefore fails. The probe uses a fuel Nat instead, `QS(fuel, n, s) by fuel`, which is checked and runs, but in Ochr fuel is a runtime argument, since there are no erased data parameters. What quicksort needs is **strong (course-of-values) recursion on a Nat**, rule [Rec-<] in §5.2.

The probe gets `Le(k, m)` from a runtime `LeDec` rather than from `PartLe`. `PartLe`, one induction mirroring `Scan`, is not written.

**The statement** (a sketch, not checked):
- `Sorted(n, ModelS((QS(n, &*s); *s)))`;
- for every q, `let old = *s; Eq Nat (Count(q, n, ModelS((QS(n, &*s); *s)))) (Count(q, n, ModelS(old)))`.

`Sorted` and `Count` recurse over `n` (an index) in the model. The proofs mirror `QS`: they build the pieces as locals and call the induction hypotheses on them.

**Free:**
- The left piece's final content is exactly the left call's result on `⌈TakeS(k, Part(σ))⌉`, and the right call cannot touch it, so no locality lemmas are needed.
- The pivot cell is literally `⌈TakeS(1, DropS(k, Part(σ)))⌉`.
- Every piece's length is its type.
- Bounds are never stale.

**Lemmas:**
- *Quicksort level:* `JoinTakeDrop`, `CountJoin`, `SortedJoinPivot`, and the count-based bound transfer.
- *Partition level:* Lomuto's invariant is positional (cells 1..i are ≤ p, cells i+1..j−1 are > p), so it needs range predicates over `NthC`, `CountSwap`, and a bridge from the ranges to `TakeC`/`DropC`: about six lemmas. This is DLLBC's R15 stratum, found in the same place: the partition's interface.

**Primitives:** `JoinTakeDrop` and the projections are definitional if symbolic segment merging works. But `Sorted` and `Count` over a primitive array need a recursor with ι-rules (DLLBC R10).

### 4.3 B3: hashmap insert into a bucket in place

```
inductive HashMap (cap : Nat) := MkHM(slots : Array(List(Entry), cap), size : Nat)   -- K4; today HMOf(R), checked

def Insert (cap : Nat) (hm : &HashMap(cap)) (k : Nat) (v : Nat) (hcap : Lt(0, cap)) : Unit := (
  match *hm {
    MkHM(slots, size) => (
      let i = Mod(clone(k), clone(cap));
      let b = GetMut(List(Entry), cap, AsSlice(List(Entry), cap, &slots), i, ModLt(k, cap, hcap));
      let fresh = InsertB(b, k, v);               -- recursion over the bucket list, not an array
      match fresh { true => size := S size, false => () }
    ),
  }
)
```

The capacity is a runtime Nat held as a parameter (fixed capacity) or as an index field (resizable: `MkHM(cap : Nat, slots : Array(List(Entry), cap), size : Nat)`, dependent fields). The bound `Lt(Mod(k, cap), cap)` mentions only `cap`.

- **By definition:** the bucket write lands inside `slots`.
- **Lemmas:** `GetMutSet` (in place = functional, the `AddMEq` shape), and `NthSetSame`/`NthSetOther` (Lean's `getElem_set_self`/`_ne`).
- **Resize:** allocate by `ArrPush` in a loop over a counter, re-insert by recursion over the old index. It needs dependent fields for the new capacity.
- **Primitives:** the frame for another slot `Mod(q, cap)` still needs a comparison and a lemma, so B3 is roughly even.

### 4.4 B4: a bounds proof from a runtime comparison (checked)

```
inductive Dec (P : Prop) (Q : Prop) := Yes(h : P) | No(k : Q)

def LtDec (i : Nat) (n : Nat) : Dec(Lt(i, n), Le(n, i)) by i := (
  match i {
    Z => match n { Z => No(refl), S _ => Yes(refl) },
    S i' => match n { Z => No(refl), S n' => LtDec(i', n') },
  }
)

def GetOr (T : Data) (n : Nat) (s : &Slice(T, n)) (i : Nat) (d : T) : T := (
  let dec = LtDec(clone(i), clone(n));
  match dec { Yes(h) => Read(T, n, s, i, h), No(k) => d }
)
```

Today's inductives express this: `Dec` is `Type₀` data whose fields have parameter types (D36 allows that), and an arm binds its field as ⋆ at the parameter type (D49). At runtime it is a boolean.

**Finding (checker incompleteness).** "cannot infer the type of the value ⋆" in two situations:
- a match on a `Dec` whose parameters mention a sealed program that embeds a proof argument;
- a λ that captures such a sealed program.

Minimal repro: `H(x : Nat, h : ⊤) : Nat by x`, then `let y = H(x, refl); let d = LeDec(y, x); match d {…}`. It also fails with `Apply(λ(u : Unit) : Nat => y)`. A split directly on `y` works. The workaround is to pass the value through a parameter. In `QS`, `k` embeds `Read`'s bounds proofs, so the probe applies a λ to `k` to pass it in. The case studies will hit this bug.

### 4.5 The lemma library users would rely on

| layer | items | lines (est.) |
|---|---|---|
| model: `Cells`, Take/Drop/Join, Nth/Set, `Snoc`/`Unsnoc` | 8 | 80 |
| round trips: JoinTakeDrop, TakeJoin, DropJoin (checked, 12 lines) | 3 | 40 |
| get/set: GetMutSet, NthSetSame, NthSetOther | 3 | 45 |
| counting: CountJoin, CountSet, CountSwap | 3 | 40 |
| order glue: SortedJoinPivot, AllLe/AllGe over Join, bound transfer by counting | 6 | 90 |
| growth: NthSnoc (old/new), SnocUnsnoc | 3 | 35 |
| Nat: LeRefl, LeStep, LeTrans, LeAddL, AddRS, AddOneR, SubPos (checked), ModLt, `LtDec` | 9 | 75 |

That is about 35 items and 400 lines, plus about six positional lemmas per index-style partition. Every lemma recurses over a Nat.

## 5. The principles and the kernel changes

### 5.1 The principles

**Decisions read from syntax and declarations.**
- [Abstract] reads constructor names, the position's class (P2), and the enclosing attribute.
- [Unsized] reads a declared flag on the head of the place's type. That head is stable under refinement (D49's argument). A stuck type of sort `Data` can never become unsized.
- [Frozen] reads which fields later field types mention.
- [Rec-<] reads the declared type of the decrease proof.

None of them changes evaluation: the checker runs model bodies everywhere. A misclassification by [Abstract] or [Unsized] could only accept a program whose native run is unfaithful, never a false proof. [Frozen] and [Rec-<], by contrast, guard logical soundness (§5.2, §3).

**Generic path vs instance paths.** Nothing new in the logic. Primitives are ordinary definitions on both paths, and continuations are closures, checked at their generic call like every closure. The two-path hazard moves to *machine vs native code*, and [Link] covers it. The checker must never run native code; Lean's kernel likewise ignores `implemented_by`.

**What the link costs the paper's claims.** It costs runtime faithfulness, not logical soundness.
- For user code, "the in-place program is what proofs are about" still holds.
- For the seven primitives, proofs are about a copying model, and the compiled code is a different program related by a trusted refinement. That is the two-program pattern the paper criticises, but confined to a library written once, and the paper must say so next to §9's "the checked machine is not yet the compiled program".
- The primitive route puts comparable trust into "the compiler implements the segment rules".

### 5.2 [Rec-<]: strong recursion on a Nat (K6)

`fix f (x̄ : Ā) : B by xⱼ < := t`, with `Aⱼ = Nat`. Every recursive call is written `f(ū) by h`, where `h` is a proof, erased, whose type converts to `Lt(uⱼ, σⱼ)`, and `σⱼ` is `xⱼ`'s entry value as refined so far. As in [Rec], `f` occurs only as a call head, including inside nested λs.

- **`Lt` must be kernel-known.** It is the library's `Lt`, pinned the way `True` and `And` are. If a user could redefine it as `⊤`, then `Loop(n) : False by n < := Loop(n) by refl` would be accepted.
- **Model.** Strong recursion on Nat is definable in CIC by structural recursion on a bound (fuel := σⱼ + 1), so the rule is justified by translation, with no new axiom.
- **Machine.** Each unfolding strictly decreases a Nat, so [Seal] normalisation terminates. The decrease proof is checked once, at the generic call. Instances just run.

Both routes need this rule for quicksort. Under decision 2 it is the only non-structural pattern in the case studies: `Scan` and `Resize` count down structurally.

### 5.3 The kernel changes

| | change | why | primitives need it too? |
|---|---|---|---|
| K1 | `Data` universe (D48's open item) | generic `&T`; `&Cells(T, n)` without boxes | yes, for generic `&T` |
| K2 | `unsized` flag, [Unsized] | views are borrow-only | an analogous rule for range places |
| K3 | `abstract`, [Abstract], `implemented by` | the boundary and the link | no |
| K4 | field types may call earlier data-valued type functions on parameters | `MkHM(slots : Array(T, cap), …)`; today's workaround is a model-type parameter | yes, for arrays in structs |
| K5 (optional) | declared backward functions | returned sub-range borrows instead of continuations | no (range places) |
| K6 | [Rec-<] | quicksort without runtime fuel | yes |
| K7 | dependent fields with [Frozen] and restricted injectivity | `Vec(T)`, resizable hashmap | yes: `Vec` is user-defined in both routes |

K4, K6 and K7 are the ROADMAP's "dependent fields" and "recursion on a measure", now sharpened. Neither is specific to this route.

## 6. Paper cost

The body would present arrays as a library inside the case-study section: about 0.5 page, which the case studies need anyway. It would add one paragraph on `implemented by` and the boundary (about 0.3 page), and scope lines for K1, K2 and K4 (about 0.2 page). K6 and K7 are paid by both routes: [Rec-<] is a few lines, and dependent fields with [Frozen] about 0.3 page.

In total, about 0.5 page specific to arrays, plus about 0.5 page of appendix rules. The body is at 24/25 pages. The primitive route adds place forms, segment values, [Access]/[End] on segments, canonical forms and `Eq` on arrays: plausibly 2–3 pages (arrays-primitive has the estimate).

## 7. Risks and open questions

1. **Continuations are second-class.** They cannot capture borrows, they are re-checked generically, a three-way split nests two of them, and their result is data. Quicksort tolerates this (checked); code holding sub-range borrows alongside other borrows would not. K5 removes all four costs.
2. **Definitional gaps compared with primitives.** Every split leaves a `JoinS` spine in the owner, even when the continuation changes nothing (probe `SplitNoop`). So "still σ" is a lemma, and statements target the join form. Projection-after-join and get-after-set are lemmas too.
3. **Reads through element borrows** leave put-back programs. Copy-read primitives fix this for reads; shared borrows would fix it generally.
4. **Dependent fields** are needed for anything growable, and the restricted injectivity leaves some `Eq` on `Vec` values stuck.
5. **Capacity lives in the allocator.** Amortised growth assumes an allocator that reports usable block size (or a hidden header).
6. **K1 is open** (D48). Without it, arrays are monomorphic with boxed tails, which works today.
7. **The link for higher-order primitives is relational**, so tests cover only generated continuations.
8. **D53:** indices and lengths move, so runtime reuse needs `clone`.
9. **The ⋆ incompleteness** (§4.4) should be fixed before the case studies.

## 8. Verdict

Worth implementing, and first. It meets both user decisions: the length exists only in the type, with no dependent fields for the fixed-length type, and all runtime recursion is over indices. The kernel changes are static (K1–K4) or shared with primitives (K6, K7). It keeps user predicates as ordinary recursion, and it fits the page budget. Its honest weaknesses are scoped sub-range borrows and a few one-induction round-trip lemmas.

Suggested order:
1. Build K3, K2 and K4, with the model as `Std`'s array library.
2. Add K6.
3. Run quicksort; then add K7 and run the hashmap with resize.
4. Revisit primitives, or add K5, if continuation plumbing or round-trip lemmas dominate the case studies' line counts.

## 9. The probes

Scratch files, not committed and deleted, run through the checker at the D52 build.

- **v1, lists (36 declarations).** Checked: `Dec`, `LtDec`, `NthMut`, `GetOr`, `DropMut`, `WithSplit`, `B1Join` (`refl`), fuel recursion through a continuation. Rejected as expected: `B1DropOpaque`, `SplitNoop`, `ReadNoop`, `StaleBound`, `ContNoFacts`.
- **v1, cells (32).** Checked: `GetMut`, Take/Drop/Join, `DropJoin`, `B1Proj` (opaque g, one lemma), `B1JoinC` (`refl`), `ZeroAll`, `Swap`, and a peel-the-head partition with `QS`, which runs to the sorted array.
- **v2 (44).** Checked: `Array`/`Slice` over `Cells` with no length field; `AsSlice`; the index lemmas; `Scan` and `Partition` (Lomuto, structural on a countdown, bounds by lemma); `QS` over views (fuel, `LeDec` bound); `SortA` on an owned `Array(4)` ([3,1,4,2] to [1,2,3,4]); `HMOf`/`HMSlot`. Rejected as expected: `LArr` (proof field), `Vec` (Σ field), `HM0`/`HM1` (D36), `SortRunWrong`.
- **A repro file:** the ⋆ finding.
