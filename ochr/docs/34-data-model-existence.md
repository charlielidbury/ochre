# 34. The data model exists: what `exists_dataModel` owes, two constructions, a recommendation

Design note, task 1 of the data-model lane (branch `spine-datamodel`, from `spine` at d67b1d51). Nothing here is proved yet. Checker verdicts quoted below were obtained by running the checker on the probe program in the appendix at that commit. Claims about the model are marked *argued* (read off the Lean definitions, not kernel-checked) unless said otherwise.

## 1. What `exists_dataModel` owes today

The statement (`Meaning/Consistency.lean`):

```
theorem exists_dataModel (items : List Item) (fuel : Nat) :
    ∃ (dm : DataModel) (D : MState → Decisions),
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm ∧ dm.read.WholeFields
```

`Covered dm P` is `∀ d ∈ P.inds, dm.covers d`, and `covers` is a field the model chooses. For a covered declaration the laws are the fields of `DataModel` (`Meaning/Data.lean`):

- `read_eq`: the model's reading (`read`, a `DataRead`) reads an element of `car d ps` as `(tag x, fields x)`. For a model whose reading is the default `readOf car tag fields` this is `simp`. For the generic model the reading is given from outside (the class `DataGeneric.Reading`), and the law is the argument `hR : Coherent Γ` of `genericModel`: the generic model's fields are meanings encoded at that same reading, so model and reading must be a fixed point.
- `tag_pack`, `fields_pack`, `pack_fields`: packing and unpacking are inverse; every element is a constructor applied to its fields.
- `pack_isSome`: packing succeeds exactly when the constructor exists, the number of fields is its arity, and each field is a member, at the model's reading, of `fieldTy d ps c i` at the earlier fields.
- `rank_lt`: a field whose declared type is a direct occurrence of the declaration, at the parameters `recArgs` gives, packs an element of smaller `rank`.
- `DataRead.WholeFields` (`Sem.lean`): for every `d ps A a`, every field the reading returns is whole.

What the statement does not say, though the rest of the proof relies on it:

- **(O1) Faithfulness.** `fieldTy` must be the meaning of the declared field types and `paramTy` of the declared parameter types. The step lemma `fieldTypesOf_step_stmt` (`Steps/Statements.lean`) says the checker's field types mean `K.dm.fieldTy`, for every run context with `CtxOk`, and `CtxOk` asks of the data model only `covers`. `DataGeneric.FieldsFaithful` names the obligation; no statement requires it.
- **(O2) `recArgs` is honest.** Its default is `fun _ _ _ _ _ => none`, which makes `rank_lt` vacuous.
- **(O3) The semantic [Rec].** The reference run's guarded fixpoint (`Run.lean`, the `.fix` clause) reads `semRank` of the decreasing argument (`Places.lean`: the rank, by the model, of the element the value packs, found by the value's own declaration). The checker's [Rec] accepts a recursive call at any strict subterm of the entry value, through any fields (RULES.md [Rec]). The model must make `semRank` decrease along every such path. No law says so.
- **(O4) Parameters read back from their codes** (`ParamsCoded`), which `ctor_mem_tyM` needs for a constructor value to be a member of its type.
- `false_means_empty` needs nothing more: for any lawful model, a declaration with no constructors has an empty carrier (`pack_fields`, `pack_isSome`).

What the generic model (`DataGeneric.lean`) still has open, by its own account: `Coherent`; a constructed field is read at the stand-in code `opq`, not at the run's code, so recursive and nested fields are not the run's meanings; `rank_lt` does not cover nested paths; `FieldsFaithful`'s recursive and nested part (the assembly reading signatures off field-type terms and showing they are the run's readings).

## 2. Findings, before any construction

### 2.1 As stated, `exists_dataModel` holds of a model that ignores the program (argued; easy to kernel-check)

Take `covers d := True`, `fieldTy := err` everywhere, `car d ps :=` the indices of `d`'s constructors with no fields, `pack d ps c [] := c` when constructor `c` has no fields (else `none`), `fields := []`, `rank := 0`, default `recArgs` and reading. `err` has no members, so `pack_isSome`'s right side holds exactly for a fieldless constructor with no fields; every other law is immediate; `WholeFields` holds because no reading returns a field. Any `D` will do. So the statement is true and says nothing about the program. At this model `fieldTypesOf_step` is false (the checker's type for `Pair(Nat, Nat)`'s first field means `Nat`, not `err`), so the assembly cannot use a model that `exists_dataModel` merely asserts.

**Fix (spine-owned statement):** `exists_dataModel` must conclude faithfulness (O1), honest recursion data or a better rank law (O2, O3, see 2.2), and `CtxOk` must carry the same faithfulness, not only `covers`. Faithfulness has to be stated against the reference run of the declared field and parameter type terms, under the model itself (a field type `List(A)` means `dm.tyM List [A]`), so the statement is about a model together with the program meaning of the items before each declaration (type functions in field types read earlier globals).

### 2.2 The rank law does not give guarded recursion through nesting (checker verdicts checked; model side argued)

The checker accepts, and computes to 3 (`F3` accepted by `refl`, `F2` rejected):

```
inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
def CountF (f : List(Rose(Nat))) : Nat by f := (
  match f { Nil => 0, Cons(t, rest) => match t { Node(a, k) => S(CountF(k)) } })
def F3 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 3) := refl
```

The recursive call is at `k = f.0.1`, a list of the same type nested inside `f`'s head. `semRank` ranks a `List(Rose(Nat))` value by `List`'s rank. Any rank that `List` gives its own elements from their own spine (the generic model's `crank`, the first stage, is length plus one) gives `k` the same rank as `f` here (both have length 1), so the model's guarded fixpoint runs out one call early and the model's `CountF(...)` is `S(S(S(c)))` with `c` the classical filler of D60, not provably `3`. `rank_lt` is satisfied by such a model: it speaks only of direct recursive fields of one declaration. So (O3) is not a consequence of the interface, and the generic model's rank is wrong for an accepted program.

**Fix:** a rank that decreases along every field step, whatever declaration the step passes through. The uniform choice is the height of the value's meaning as a tree: every field of a constructor value is a proper subtree of its meaning, so every strict subterm has smaller height, through nesting and across declarations, with nothing to prove per declaration. `semRank` would read the height of the meaning (with a number's height its value), and `rank`, `recArgs` and `rank_lt` would leave `DataModel`. That changes `Places.lean` and `Data.lean` (not this lane's files).

### 2.3 Parameters above level 0 cannot be coded, so some accepted constructor values are members of no code (argued from the definitions; to be kernel-checked)

`Fording.lean`'s `InductiveModel` block, accepted by the checker:

```
inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
def te : TEq(Type, Word, Word) := MkTEq[Type, Word, Word](refl)
inductive HL (f : Π(x : Word). Type) := MkHL(y : Word)
def hl : HL(λ(x : Word) : Type => Word) := MkHL[λ(x : Word) : Type => Word](Zero)
```

`te`'s first parameter runs to the type value `Type₀`, `.ty (TyM.univ 1)` = `.ty (.t1 _ .univ1)` (`Run.lean`, the `.sort` clause). A data code holds its parameters as `Par0`, which holds a level-0 type or a coded level-0 element only (`Sem.lean`), and `parOf` (`Data.lean`) turns any other parameter into `.val .bad`, whose meaning is `.err`. The encoding of every element at `tyM TEq ps` therefore has `.err` where the run's constructor value has `.ty (.t1 _ .univ1)`, and `Code0.enc` never produces `.ty _` at that position. So for every data model and every reading, the run's meaning of `te` is not a member of its declared type, and `Assembly.defn_member` is false for this program. This is not about the construction: it is the code layering (D59: `Code0 : Type → Type 1` cannot hold a `Code1`). `hl` and `G (F : Π(X : Type). Type)` in the same block are the same case wherever their parameter means a level-1 value (`.el1 C f`), which `Code0.enc` never produces either.

**Fix (spine decision):** either a data code may hold large parameters (a change to the code families' universes, which D59 chose to avoid), or a constructor value records its parameters as its type's code reads them back (so a large parameter is recorded as the code records it, and `car` depends on the parameters only through what the code keeps), or the checker forbids parameters above `Type₀`'s elements in data declarations (it would reject `TEq`, `HL`, `G`).

### 2.4 Model and reading are a fixed point only because a data value's meaning holds its carrier element (argued)

A field type may read earlier fields (the telescope, D64): equations (`VecF`'s `h : Eq(Word, n, Succ(m))`, the suite's Forded families), type functions (`MkBW(b : Bool, x : BF(b))`, accepted), and value parameters of occurrences (`VecF(A, m)`). The run computes such a field type from the earlier fields' meanings. A data field's meaning is `Sem.dat name ps c fs (some ⟨car, x⟩)`: its fields as the reading gives them, and **its element of the final carrier**. So the carrier's telescope at a later field depends on the reading and on the final carrier of the earlier field's type, while the reading of an element depends on its carrier. When the earlier field's type is fixed before the declaration (`Word`, `Bool`), building in program order resolves this. When it is not, it does not:

```
inductive Single (A : Type) (a : A) := MkS(x : A, e : Eq(A, x, a))
def S1 : Single(Nat, 0) := MkS(0, refl)
def S2 : Single(Single(Nat, 0), S1) := MkS(S1, refl)       -- accepted
```

At the parameters of `S2`, the field `e`'s type is the proposition that `x`'s meaning equals `S1`'s, and `x`'s meaning contains an element of `car Single [Nat, 0]` and its fields as the reading gives them. So `car Single [Single(Nat, 0), S1]` depends on the finished carrier and reading of `Single` at other parameters: induction-recursion within one declaration. No measure on elements (stage, rank) orders it: the dependence is on every element of the earlier field's type, not on smaller ones. An order on types exists in principle (parameters' components before the type), but non-uniform recursion (`VecF(A, m)`, `NL(Pair(A, A))`) moves parameters around inside one carrier's construction, and a nested instance (`List(Rose(A))`) makes an earlier declaration's reading depend on a later one's. I could not find a measure that a Lean construction could recurse on. This is what `Coherent` hides.

The root is the element inside the meaning (`el`). Lean's model has no such thing: an element of an inductive type is a ZFC tree, its own meaning (docs/31 D32 says the same of our values; `el` is what remains of the earlier encoding). Without `el`, a whole data value's meaning is a tree of meanings, a field type is computed from trees, and membership of data can be a predicate on trees defined before any carrier exists (section 4).

## 3. The two constructions, item by item

**(a) Finish the generic construction** (`DataGeneric.lean`): carriers by stages over every parameter tuple at once, colimit as a quotient by raw meaning, nesting through each earlier declaration's carrier as a functor of its leaf types (`NModel`), field types as codes read off the declaration (`PCode`: `ext`, `par`, `self`, `nest`), leaves encoded at a given reading.

**(b) Lean's way, adapted** (Carneiro §5.2): erase what varies to get one plain tree type, and carve out each type's members with a predicate. Taken literally, one native Lean tree type with leaves cannot live in `Type`: leaves have arbitrary small types (a type parameter instantiated at a function type, `EqF(Π(x : Word). Word, …)`, accepted; a type-function field that computes to a function type at an instance, `MkBH(b : Bool, x : BG(b))`, accepted), and a non-uniform type parameter is an index of type `Type`, which Lean itself only allows in `Type 1` (checked: `inductive NL3 : Type → Type` with a constructor over `{α : Type}` is rejected, "invalid universe level"). Two adapted forms:

- **(b1)** a native tree of shapes only (constructor tags and children) with the leaves filled by a type-valued function by structural recursion on the shape. This is (a) with stages indexed by shapes instead of numbers: no quotient, and a structural height. It keeps `el`, so it has 2.4's fixed point exactly as (a) does.
- **(b2)** the meanings themselves (`Sem`, already a native tree type) as the skeleton, with `el` removed from `Sem.dat`. Membership of `D(ps)` is the least predicate `Good d ps` on meanings closed under the constructors (a constructor value of `d` at `ps` whose fields are members of the field types the run computes from the earlier fields; at a data-shaped field type, membership is `Good` again), defined impredicatively in `Prop`, so no universe or positivity question arises. The carrier, which Lean needs in `Type` only for function types and universes, is a small copy: a type in bijection with `{s // Good d ps s}`, built by stages whose fields hold earlier stages (data-shaped fields) or leaves (other fields), with a meaning function by recursion on the stage and no reading; injectivity by construction, surjectivity by induction on `Good`. The reading is the bijection.

| | (a) generic, finished | (b2) meanings as skeleton |
|---|---|---|
| Recursive `List(A)` | `self` code, stages, colimit (done) | `Good List [A]` requires `Good List [A]` of the tail |
| Nested `Rose(A)` | through `List`'s `NModel`; the field lives in `List`'s carrier over the leaf code `opq(car Rose)`, a different Lean type from the run's `car List [Rose(A)]` (the leaf environment holds codes), so a transport or a leaf environment of types is needed | `Good Rose ps` requires `Good List [Rose(A)]` of the forest, which requires `Good Rose ps` of each tree: one simultaneous least fixed point, nothing to transport |
| Parameters | blanked fixed parameters, leaf environment for nestable ones; non-uniform recursion free (stages at every tuple) | parameters are indices of `Good`; non-uniform recursion free |
| Large parameters (2.3) | fails for any model | fails for any model |
| Dependent `V := MkV(n : Nat, x : Fin1(n))` | `ext` code at the earlier meaning `el0 Nat n`, no reading involved | `x` a member of the run's type at `n`'s meaning |
| Dependent on data (`VecF` over `Word`, `BW`, `Single`) | carriers depend on the reading: 2.4 | field types computed from trees; no reading |
| `Prop`-sorted | `tyB true`, `PLift (Nonempty _)` (done) | `tyM` is the proposition that `Good` is inhabited; constructor values are `•` as now |
| Function-typed fields | positivity (`Check.lean`, `firstOrderTerm`, D36) admits no `Π` in a field type and never the declared type under a `Π`, codomain included, so no function-indexed children; functions occur only as leaves (above), `El` of a function code | the same; a function leaf's meaning is `el0 C f` |
| Universe levels | carriers at level 0 (`Code0`); fields level 0 by (I6); parameters may be level 1 or 2 (2.3) | `Good` on `Sem` in `Prop`; the copy in `Type` because every leaf is level 0 by (I6) |
| `Coherent` / `read_eq` | the fixed point of 2.4 | by construction (the reading is the bijection) |
| `WholeFields` | by induction on rank, after the fixed point | members are whole, by induction on `Good` |
| Rank (2.2) | per-declaration `crank`, wrong for `CountF`; a height through `NModel` leaves needs a new interface operation | height of the meaning; nothing per declaration |
| Faithfulness (O1) | the assembly reads `PCode`s off field-type terms and proves `interp` is the run's reading, with the run under the model being built | `Good` uses the run's field types, so the run must be read without the finished model (below) |

**What (b2) still has to solve (argued).** The run reads the data model when it computes a field type: data codes hold carriers and decoded value parameters, and a field type that applies a function to a field (`Eq(Word, n, WAdd(m, k))`, `Vec(Nat, LenL(A, xs))`, `Cells(E, n)`) decodes the field's meaning into a carrier. So `Good`'s operator needs a reading of field types that uses the model only through names, parameters' meanings and memberships, plus a lemma that the run under the finished model agrees with it. Built in program order, decoding at earlier declarations is available at parameters that do not mention the declaration being built. What remains is a field-type term applying a function to data whose type mentions the declaration (or a later one) through a parameter, at such an instance (`Mk(xs : List(A), v : Vec(Nat, LenL(A, xs)))` used at `A := itself(…)`). That needs an order on parameters (components before the type), which I believe exists and have not designed. It is a much smaller residual than 2.4: equations (`Single`), value parameters (`VecF`) and type functions that only inspect structure need no carrier at all.

## 4. Recommendation

**Independently of the construction**, fix the statement: faithfulness in `exists_dataModel` and `CtxOk` (2.1), a rank law covering every field path (2.2), and a decision on large parameters (2.3). All three are spine-owned.

**For the construction, (b2), conditional on removing `el` from `Sem.dat`.** It is Lean's model completed (an element of a data type is its tree), the structurally uniform endpoint the earlier decisions (D32, D61) were moving toward. It removes, rather than proves, the three hardest open items of (a): `Coherent` (the reading is a bijection by construction), the rank on nested paths (height of the meaning), and the nested seam (`opq`, leaf environments of codes against the run's carriers). What stays is faithfulness, which (a) owes too, and the residual of section 3. It is also less code: one predicate, one stage construction without nesting functors or raw meanings relative to leaves.

**If `el` stays**, (a) repaired: real codes in place of `opq` (the code of a `self`/`nest` occurrence built from the stage's carrier and coded parameters), a height through `NModel` leaves, and `Coherent` built by a stratified recursion over parameters. The last is the research risk of 2.4 and I would not start it before a concrete model of `Single(Single(Nat, 0), S1)` and `VecF` over `Word` shows the order works. (b1) is not worth it: it rebuilds (a) to gain a structural height and lose the quotient, and keeps 2.4.

## 5. What would change outside this lane's files

- `Consistency.lean`, `Steps/Statements.lean` (`CtxOk`): faithfulness in `exists_dataModel` and in `CtxOk` (2.1).
- `Places.lean` (`semRank`), `Data.lean` (`rank`, `recArgs`, `rank_lt`): rank as the height of the meaning (2.2).
- `Sem.lean` (`Par0`, `Code0.data`), `Data.lean` (`parOf`, `parsOf`, `ctorM`): large parameters (2.3).
- For (b2): `Sem.lean`: `Sem.dat` without `el` (or `el` always `none`); `Code0.enc` at a data code without the element; the codec laws (`Code0.enc_inj`, `dec_enc`, `Apply`'s `Lvl` laws) then need the reading injective, which a model provides (`pack_fields`; a non-carrier type read as `(0, [el0 A a])`), so `DataRead` becomes a reading with its injectivity, or the laws take it as a hypothesis. `Data.lean`: `ctorM` without packing; `Sem.elt`, `ctor_mem_tyM` (membership of a whole constructor value is `Good`, through the bijection), `pmem`/`MovedOf` (mechanical: `el` disappears from the patterns). `Run.lean`, `Places.lean`: the [Rec] rank. The four core lemmas' data cases and `Mono`'s toy values: mechanical, as D32's re-proof was.

## 6. What I judge most likely false or stuck

- **False:** `defn_member` for programs with parameters above level 0 (2.3), at every data model. High confidence; kernel-checkable on `te`.
- **False:** guarded recursion sound for `CountF` with any per-declaration rank, in particular the generic model's (2.2). High confidence.
- **Useless as stated:** `exists_dataModel` (2.1). Certain.
- **Stuck:** `Coherent` for the generic model as designed, in general (2.4). The fixed point probably exists (the set model does), but I see no recursion a Lean construction could use; `Single(Single(Nat, 0), S1)` is the smallest declaration showing it.
- **Open, smaller:** (b2)'s residual, a field type applying a function to parameter-typed data at an instance that mentions the declaration itself.

## Next (task 2), as I would run it

A concrete program with `List`, `Rose` (and `CountF`), `V`, a `Prop`-sorted declaration, `Single` at `Single(Nat, 0)`, `VecF` over `Word`, `BW` and `BH`, each beside the checker's verdict (asserted at build), with a hand-built model satisfying every `DataModel` law, `read_eq`, `WholeFields` and pack/read round trips, `#print axioms` on each. Plus three kernel-checked counterexamples: the degenerate model of 2.1, the rank of 2.2 (a lawful model under which `CountF`'s recursive call does not decrease `semRank`), and `te`'s non-membership (2.3). Under (b2) the hand-built model would be built in the (b2) shape where the current `Sem` allows it, to check the design before asking for the `Sem` change.

## Appendix: the probe program (all verdicts as marked)

```
ochr DMProbe1 uses Nats, Lists, Bools {
  inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
  def CountF (f : List(Rose(Nat))) : Nat by f := (
    match f { Nil => 0, Cons(t, rest) => match t { Node(a, k) => S(CountF(k)) } })
  def F3 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 3) := refl
  reject def F2 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 2) := refl
  inductive Single (A : Type) (a : A) := MkS(x : A, e : Eq(A, x, a))
  def S1 : Single(Nat, 0) := MkS(0, refl)
  def S2 : Single(Single(Nat, 0), S1) := MkS(S1, refl)
  def BF (b : Bool) : Type := (match b { false => Nat, true => Unit })
  inductive BW := MkBW(b : Bool, x : BF(b))
  def BW1 : BW := MkBW(true, ())
  def BW0 : BW := MkBW(false, 5)
  def BG (b : Bool) : Type := (match b { false => Nat, true => (Π(n : Nat). Nat) })
  inductive BH := MkBH(b : Bool, x : BG(b))
}
```

`TEq`, `te`, `HL`, `hl`, `G`, `EqF`, `ef`, `NL` are in `Examples/Fording.lean` (`InductiveModel`), accepted and asserted by the build.
