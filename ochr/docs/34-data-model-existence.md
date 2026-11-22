# 34. The data model exists: what `exists_dataModel` owes, two constructions, a recommendation

Design note of the data-model lane (branch `spine-datamodel`, from `spine` at d67b1d51). Sections 1–6 are task 1 (the design, before any code); sections 7–10 are task 2 (records against the current definitions, the large-parameter design, the faithfulness draft, and the prototype of the recommended construction); sections 12–15 are task 3 (the residual settled, K3 attacked, the rank the recursion knot needs, and the porting guide for the spine lead). Section 17 is the port itself, done by this lane: **BUILT** (`lake build OchrMeaning` green on the (b2) data layer). Section 18 (existence lane `exists2`) is how existence is proved: the statement repaired, two kernel-checked instances, what they taught, the plan. Kernel-checked unless marked *argued*. The checker's verdicts on every probe program are asserted by the build (`Meaning/DataModel/Probes.lean`). Sections 1–16 are kept as written; where they name a prototype file (`Proto/…`), §17 says where it went.

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

### 2.1 As stated, `exists_dataModel` holds of a model that ignores the program (kernel-checked: `Counterexamples.degenerate_meets`)

Take `covers d := True`, `fieldTy := err` everywhere, `car d ps :=` the indices of `d`'s constructors with no fields, `pack d ps c [] := c` when constructor `c` has no fields (else `none`), `fields := []`, `rank := 0`, default `recArgs` and reading. `err` has no members, so `pack_isSome`'s right side holds exactly for a fieldless constructor with no fields; every other law is immediate; `WholeFields` holds because no reading returns a field. Any `D` will do. So the statement is true and says nothing about the program. At this model `fieldTypesOf_step` is false (the checker's type for `Pair(Nat, Nat)`'s first field means `Nat`, not `err`), so the assembly cannot use a model that `exists_dataModel` merely asserts.

**Fix (spine-owned statement):** `exists_dataModel` must conclude faithfulness (O1), honest recursion data or a better rank law (O2, O3, see 2.2), and `CtxOk` must carry the same faithfulness, not only `covers`. Faithfulness has to be stated against the reference run of the declared field and parameter type terms, under the model itself (a field type `List(A)` means `dm.tyM List [A]`), so the statement is about a model together with the program meaning of the items before each declaration (type functions in field types read earlier globals).

### 2.2 The rank law does not give guarded recursion through nesting (kernel-checked: `RankCounterexample.semRank_eq`)

The checker accepts, and computes to 3 (`F3` accepted by `refl`, `F2` rejected):

```
inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
def CountF (f : List(Rose(Nat))) : Nat by f := (
  match f { Nil => 0, Cons(t, rest) => match t { Node(a, k) => S(CountF(k)) } })
def F3 : Eq(Nat, CountF(Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)), 3) := refl
```

The recursive call is at `k = f.0.1`, a list of the same type nested inside `f`'s head. `semRank` ranks a `List(Rose(Nat))` value by `List`'s rank. Any rank that `List` gives its own elements from their own spine (the generic model's `crank`, the first stage, is length plus one) gives `k` the same rank as `f` here (both have length 1), so the model's guarded fixpoint runs out one call early and the model's `CountF(...)` is `S(S(S(c)))` with `c` the classical filler of D60, not provably `3`. `rank_lt` is satisfied by such a model: it speaks only of direct recursive fields of one declaration. So (O3) is not a consequence of the interface, and the generic model's rank is wrong for an accepted program.

**Fix:** a rank that decreases along every field step, whatever declaration the step passes through. The uniform choice is the height of the value's meaning as a tree: every field of a constructor value is a proper subtree of its meaning, so every strict subterm has smaller height, through nesting and across declarations, with nothing to prove per declaration. `semRank` would read the height of the meaning (with a number's height its value), and `rank`, `recArgs` and `rank_lt` would leave `DataModel`. That changes `Places.lean` and `Data.lean` (not this lane's files).

### 2.3 Parameters above level 0 cannot be coded, so some accepted constructor values are members of no code (kernel-checked: `Counterexamples.ctorM_large_not_mem`)

`Fording.lean`'s `InductiveModel` block, accepted by the checker:

```
inductive TEq (U : Type₁) (a : U) (b : U) := MkTEq(h : Eq(U, a, b))
def te : TEq(Type, Word, Word) := MkTEq[Type, Word, Word](refl)
inductive HL (f : Π(x : Word). Type) := MkHL(y : Word)
def hl : HL(λ(x : Word) : Type => Word) := MkHL[λ(x : Word) : Type => Word](Zero)
```

`te`'s first parameter runs to the type value `Type₀`, `.ty (TyM.univ 1)` = `.ty (.t1 _ .univ1)` (`Run.lean`, the `.sort` clause). A data code holds its parameters as `Par0`, which holds a level-0 type or a coded level-0 element only (`Sem.lean`), and `parOf` (`Data.lean`) turns any other parameter into `.val .bad`, whose meaning is `.err`. The encoding of every element at `tyM TEq ps` therefore has `.err` where the run's constructor value has `.ty (.t1 _ .univ1)`, and `Code0.enc` never produces `.ty _` at that position. So for every data model and every reading, the run's meaning of `te` is not a member of its declared type, and `Assembly.defn_member` is false for this program. This is not about the construction: it is the code layering (D59: `Code0 : Type → Type 1` cannot hold a `Code1`). `hl` and `G (F : Π(X : Type). Type)` in the same block are the same case wherever their parameter means a level-1 value (`.el1 C f`), which `Code0.enc` never produces either.

**Fix (spine decision):** settled in §8 (the checker is not restricted): a data type's code keeps a small record of what its field types read of the parameters (K3), and a constructor value records that record.

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

## 7. Task 2, part 1: records against the current definitions (kernel-checked, standard axioms)

All in `Meaning/DataModel/`, beside the checker's verdicts in `Probes.lean`.

- **`Counterexamples.degenerate_meets`**: `exists_dataModel`'s statement holds of `degenerate` (every field type `err`, carriers the fieldless constructors) for every list of items; its field types are `err`, which no checker field type means (`degenerate_fieldTy`).
- **`RankCounterexample`**: `dmK`, a data model covering `List` and `Rose` with every `DataModel` law proved (its reading its own, `List`'s tail announced by `recArgs`, ranked by length), reading the program's types at the run's codes (`tyM_rose`, `tyM_listRose`, `fieldTy_honest`, `recArgs_honest`). For `CountF`'s argument `f` and the forest `k` its recursive call is at (`k_in_f`: two field steps), both members of `List(Rose(Nat))` (`f_mem`, `k_mem`), `semRank_eq : semRank k = semRank f`. The checker accepts `CountF` and computes `3` by `refl` (`Probes.lean`, `F3`; `F2` with `2` rejected).
- **`Counterexamples.ctorM_large_not_mem`**: for every data model, a constructor value whose first parameter is `Type` (what the run gives `te`'s first parameter) is not a member of its type's code (`dat_large_not_mem`, any level-1 or level-2 type value as a parameter).
- **The W-type shape** (the team lead's check on the height): a field that is a function into the declared type is rejected by positivity, directly (`WT`) and through a type function (`WT2`), both asserted. Data values are finite trees, so the height of a meaning is a natural number and decreases along every field.

## 8. Parameters above level 0: what a data type's code stores (task 2, part 2)

**What cannot be stored.** A `Type₀` code cannot hold `Type₀` as a value: `Type₀`'s carrier is the type of all `Type₀` codes, so a code holding an element of it would be as large as the collection it belongs to (D59's `Code0 : Type → Type 1` is forced: `univ1 : Code1 ((A : Type) × Code0 A)` needs `Code0 A : Type 1`). Lean's set model agrees: `TEq(U, a, b)` is a small set that does not contain `U`. So no data type's code stores a parameter above level 0. Since types travel through universes (`te4 := IdT(TEq(Type, Word, Word), te)`, accepted), a type's code must determine its members exactly, so a constructor value's meaning cannot record such a parameter either: the members of `TEq(U, …)` over every `U` would not form a small set, and a type passed through `Type₀` would change its members.

**What must be stored**: the declaration, the carrier, and a small *record* of what the declaration's field types read of the parameters. The probes show how much that is:
- `te2`/`te3` (accepted/rejected): an equation between two level-1 closures. The field's type depends on the large values (the truth of their equation).
- `HL3` (accepted; `h3bad` rejected): a field `y : App0(f)` with `App0(f) := f(Zero)`. The field's type is a code computed from the large parameter, not a truth value.
- `H` (accepted): the same with non-uniform recursion at the large parameter.

**Options.**
- **(K1) Small parameters as they are, large ones by a marker.** This is the current `parOf` with constructor values recording their parameters as the code reads them back. It costs least, but it is unsound for accepted programs: at markers, `te3`'s type has the same members as `te2`'s, while its declared field type is false, so no lawful model exists (`pack_isSome` fails at `te3`'s parameters), and `HL3`'s field types differ at `λ.Word` and `λ.Unit` with equal markers.
- **(K2) K1 plus the truth of each equation field.** It covers `TEq` at every `U`. It fails on `HL3`, whose field type is a code, not a truth value.
- **(K3) Records** (chosen, built in the prototype). A record keeps what the field types read:
  - a type parameter's entry (its code, or its declaration and record);
  - a value parameter read small (its constructor tree and leaves);
  - for a large parameter, only the codes and propositions the field types compute from it, as functions of the earlier fields read small (`teqRec`: the truth of `a = b`; `U` is dropped, `teqRecOf_U`).

  Recursive and nested children's records are computed by the declaration's signature and never stored: a record holding its own children's records would be a non-well-founded value, which is D61's cycle again. A record is small (`Rec := List Step → Entry`, in `Type 1`), so codes stay small. A constructor value records its type's record instead of its parameters (D32's self-description, by record).

  Cost (spine-owned):
  - `Code0.data d (r : Rec) A` replaces `Par0`;
  - `Sem.dat` records `r`;
  - `tyM d ps` builds the record from the parameters by the declaration's field types (faithfulness);
  - `unifyTyS` and `hint.data` give a record (a constructor with omitted parameters takes the hint's record directly).

**Built (prototype, kernel-checked):**
- `te` is a member of `TEq(Type, Word, Word)` (`te_mem`, `te_memTy`).
- An equation between one level-1 value and itself has a member (`te2_mem`); between two different values the type is empty (`te3_empty`).
- `te4`: the type is its code, an element of `Type₀`'s carrier with nothing dropped, and `te` encodes an element of its carrier.

**What keeps small keys faithful.** The run computes a later field's type from the earlier fields' full meanings; the record is keyed by their small readings. On well-typed earlier fields nothing is lost: two members of one type with the same small reading are equal (`mem_small_inj`, proved generically).

## 9. Faithfulness, drafted (task 2, part 3)

`Meaning/DataModel/Faithful.lean` (definitions, type-checked; for the spine lead to restate):
- `FieldsFaithful K ρ` and `ParamsFaithful K ρ`: at well-typed parameters and earlier fields (`ParamsTyped`, `FieldsTyped`), the reference run of the declared type term, in the frame the checker's `fieldTele` evaluates it in (`teleFrame`: the fields, the later ones `moved`, then the parameters, each at its type), is defined and means `K.dm.fieldTy` (`K.dm.paramTy`). Definedness is asked, so a run made undefined cannot make it vacuous.
- `ExistsDataModel items fuel`: `exists_dataModel` restated with the checker's decisions (not an existential `D`) and faithfulness at every checker state over the program's Σ and every assignment, the run context being the program meaning's (type functions in field types read earlier globals). `CtxFaithful K ρ` is what `CtxOk` should carry beside `covers`.
- What replaces `recArgs`: nothing. `rank`, `recArgs` and `rank_lt` go, and `semRank` reads `semHeight` (a constructor value one more than its fields, a number its value), whose law `semHeight_field_lt` is proved for every field of every declaration.

## 10. The prototype of (b2) (task 2, part 4)

`Meaning/DataModel/Proto/` holds local copies of the definitions that change, nothing of the spine's edited. Every theorem below is kernel-checked. `#print axioms` gives `propext` alone for the stage and membership laws, and `propext`, `Classical.choice`, `Quot.sound` where the encoding's classical carrier test enters.

- `Core.lean`:
  - `Val`, a meaning without the packed element;
  - codes with records (`Code`, `Entry`, `Rec`, level-1 `Code1` for large parameter values);
  - `Small`, the small reading;
  - `depth`, with `depth_field_lt`;
  - `whole`.
- `Stages.lean`:
  - a signature of field shapes (a leaf's code, or a data field's declaration and record), with stages built together with their meanings;
  - a later field's shape reads an earlier field's meaning small, so no field needs masking;
  - `tele_image` characterizes a telescope's meanings.
- `Carrier.lean`:
  - stage injectivity (`lvl_inj`) and realizability, monotone in the stage (`rz_le`);
  - every member realized at the stage equal to its depth (`rz_depth`);
  - members are whole (`mem_whole`);
  - **the carrier holds each member once and its meaning function is a bijection onto the members** (`meanC_inj`, `mem_iff_meanC`).
- `Members.lean`:
  - **`mem_iff`**: the members are the least set closed under the constructors, which is `DataModel`'s four packing laws in one statement on meanings, with no reading;
  - types as codes (`tyOf`, `encC`, `memTy`, `memTy_tyOf`);
  - `mem_small_inj`.
- `Program.lean`, `Examples.lean`: the probe programs' declarations, records and signature, and their values as members:
  - `Word`, `Bool`;
  - `List(Nat)`;
  - `Rose(Nat)` nested through `List`;
  - `CountF`'s argument and recursive argument, both members, the recursive one of smaller depth (`countF_decreases`; contrast `semRank_eq`);
  - **`S2 : Single(Single(Nat, 0), S1)`** (`s2_mem`, with no fixed point: §2.4's smallest hard case);
  - `te`, `te2`, `te3`, `te4`;
  - `VecF(Nat, Succ(Zero))` over `Word` (`v1_mem`);
  - `BW` and `BH` (type-function fields over a `Bool` field, a function-valued leaf);
  - `IsZ` (`Prop`-sorted: inhabited at `Zero`, empty at `Succ(Zero)`);
  - `V := MkV(n : Nat, x : Fin1(n))`.

**No law failed.** What the prototype does not cover:
- function types' telescopes (`Code.fn C` stands in, as their structure is not this lane's subject);
- data types at carrier level 1;
- faithfulness: the signature and records are written by hand, and that they are the run's readings is §9's statement.

**The residual** (§3; `RV`, `rv1 : RV(RV(Nat))` accepted, asserted; settled in §12). It is real at the level of faithfulness: computing `RV`'s field type at `RV(Nat)` runs `LenL` on a `List(RV(Nat))` field, which decodes it into `List`'s carrier at `RV(Nat)`'s record. In the prototype's terms that carrier exists before `RV`'s record at `RV(RV(Nat))` is needed: its stages need only the signature at records nested strictly inside (`RV(Nat)`'s, inside `RV(RV(Nat))`'s entry for `A`). This suggests the faithful signature is definable by recursion on records (the structural order of `Entry`), which non-uniform recursion does not disturb: a child's record is built from entries of the parent's. *Argued, not built.*

## 11. Task 3 in brief

- **The residual is settled (§12):** no recursion on records is needed. A closure applied to a decoded member is its body's run on the member, so the signature is defined on meanings, and the run's carrier-based reading agrees at every well-typed input. This is kernel-checked for `RE` at `RE(Nat)`, where `List`'s carrier is built from `RE`'s own signature. What the port needs instead is the closure lemma the recursion knot needs anyway.
- **K3 attacked (§13):** six adversarial cases were probed (assertions in `Probes.lean`), and the accepted ones were checked in the prototype. None is a counterexample. One sharpened the design: a record keeps its field codes along the whole unfolding, not at the root only (`H`). One is a standing condition: the checker must never decide that type formers are injective, and today it does not.
- **The rank the recursion knot needs (§15):** `semHeight` gives decrease along every path of field steps and finiteness. It does not give the semantic [Rec] link from the checker's strict subterm to a field path, and it never decreases through applications, which [Rec] does not need.
- **The porting guide is §14.**

## 12. The residual, settled (kernel-checked: `Proto/Residual.lean`, now `DataModel/Residual.lean`)

**The worry.** `RE (A : Type) := MkRE(xs : List(A), v : Eq(Word, LenL(A, xs), Succ(Zero)))` is accepted. So are `re0 : RE(Nat)` and `re1 : RE(RE(Nat))`, and `reBad` (empty list) is rejected. It is §3's residual with a field type that the function's result decides (`RV`'s equation was trivially true). The reference run computes `v`'s type by applying `LenL`'s meaning to `xs`'s meaning decoded into `List`'s carrier at `A`'s record. `LenL`'s meaning is a Lean function on carriers (D59's closures). At `A := RE(Nat)` that carrier is built from `RE`'s own signature, so read naively the signature is defined through a carrier built from it.

**The finding: no recursion on records is needed.** A closure is built from its body's run on the encoding of its argument (`closureAt`: `f a := dec (run body (enc a))`; in the prototype `lenC := lenV ∘ meanC`). Applied to the decoding of a member, it is therefore the body's run on the member itself, because decoding then encoding is the identity on members (the bijection). So:
- the signature is defined on meanings alone, with no carrier: `reRec` keys the equation by `xs` read small (`lenS`);
- the run's carrier-based reading (`runRE`: decode, apply the closure, compare) agrees with it at every well-typed `xs` and every parameter (`re_faithful`);
- in particular it agrees at `A := RE(Nat)`, where `List`'s carrier is built from `RE`'s own signature (`re_faithful_nested`);
- the probe's values check out: `re1_mem`, and `reBad_empty` (the type is empty at the empty list).

The nested form cannot arise: applying a function to a nested field names the declaration in the function's argument, which positivity rejects (`RoseL`, asserted). `Rose`'s nested field reads no carrier (`rose_faithful`).

**What the port needs in its place.** The definitional order: define the signature on meanings, then the carriers, then the closures. That holds if the field types' reading uses, for every global function, its body's run on meanings. Two ways to have that:
- **(a) A locality lemma for the run in the data model, then recursion on records.** Two models agreeing on the records an input reaches give the same run. The membership half is kernel-checked here: `mem_congr` says two signatures agreeing on a set of records closed under data fields have the same members there. So the members of `List` at `RE(Nat)`'s record are fixed by `RE`'s signature at `RE(Nat)`'s record, whatever it says at `RE(RE(Nat))`'s.
- **(b) The run-level form of the closure fact, used directly** (preferred). A global closure applied to a member argument is its body's run on the argument's meaning. That is `closureAt`'s defining property plus the round trip, and the recursion knot needs it anyway. With it, the faithful signature is the run's reading with calls evaluated by bodies, no carrier involved, and faithfulness at well-typed inputs is that lemma.

**Verdict:** the residual does not make the existence proof impossible as designed. The decoding it needs is discharged by the bijection; what remains is the closure lemma (b).

## 13. Where K3 could be wrong: the adversarial list (`Probes.lean` `DMProbeAdv`, all asserted; `Proto/Adversarial.lean`, now `DataModel/Adversarial.lean`)

1. **Records identify types the checker keeps apart.** A record keeps only what field types read, so K3 makes `Tag(Zero)` and `Tag(Succ(Zero))` one type (`Tag (n : Word) := MkTag(x : Word)`), `PH(Type)` and `PH(Prop)` one type (`PH (U : Type₁) := MkPH`), and `TEq(Type, Word, Word)` and `TEq(Π(x : Word). Type, λx.Word, λx.Word)` one type (both records say "true"). That is unsound exactly if the checker can prove two such types different. It cannot: an equation between two different applications of type formers is stuck, never `False`. `TagNe`, `ListNe`, `PHNe`, `TEqNe`, `TEqNe2` and `TagAB` (two declarations with the same shape) are all rejected, each with `h : Eq(Type, …)` and goal `False`. Lean's set model makes the same identifications. **Not a counterexample**, but a standing condition: if the checker ever decides type-former injectivity, K3 breaks for large parameters, and no small code can repair it.
2. **Parameters that are functions.** `FP (f : Π(x : Word). Word) := MkFP(y : Word, e : Eq(Word, f(y), y))` is accepted: a function-valued (level-0) parameter applied in an equation. The record keeps the equation as a function of `y` read small. `fp_mem` passes.
3. **A large parameter typing another, used in a field's type.** `LB (U : Type₁) (F : Π(x : U). Type) (a : U) := MkLB(y : AppU(U, F, a))` is rejected ("κ is not a type: its declared type is not a sort"), asserted as a control.
4. **A type function applied to a large parameter, its result matched.** `MM (G : Π(X : Type). Word) := MkMM(y : MG(G))` is accepted, with `MG(G) := match G(Word) {Zero => Word, Succ(k) => Unit}`; `mm0` and `mm1` are accepted and `mm0Bad` rejected. The record keeps the code the match gives: `mm0_mem`, `mm1_mem`, and `mm0Bad_not` (rejected, and not a member).
5. **Non-uniform recursion at a large parameter that a field type applies.** `H (f : Π(x : Word). Type) := HB | HS(y : App0(f), r : H(λx. f(Succ(x))))` is accepted, and `hh := HS(Zero, HB)` is accepted. **This one sharpens K3:** a record keeping only the root's field codes (`f(0)`) cannot give the child's (`f(1)`). The record must keep the codes along the whole unfolding: `hRec`, the sequence `f(0), f(1), …`, small. A child's record is the parent's shifted (`shiftRec`), and `shift_hRec` proves that shift is the record of the child's own parameter. `hh_mem` passes. §14 makes this the canonical record layout.
6. **A record at a partly moved or open value** (*argued*). A value records its type's record, fixed when it is built from the parameters; writes change fields, never the record. Later field types of an open value are read from the record at the current earlier fields' small readings. Those fields are whole values of their declared types ([Open] writes them whole), so `mem_small_inj` makes the small reading lose nothing. A moved earlier part reads `other`. The checker never computes a field type from a moved sibling ([Read] refuses; the join's drop does not compute types), so that reading is never compared. Not built: it needs the run.

No accepted declaration found whose record cannot tell apart what the checker distinguishes.

## 14. Porting guide, for the spine lead

What changes, in the order to change it, with the prototype lemma that replaces each core lemma. The prototype's proofs need not be read: each generic file moves over by renaming `Val` to `Sem`, `Ty` to `TyM` and `Code` to `Code0`.

### 14.1 Definitions, file by file

1. **`Sem.lean`**
   - Add `Small`, `Step := Nat × Nat × List Small`, and `Entry` to the `Code0` mutual block (`Entry := none | leaf (B) (c : Code0 B) | data (d : IndDecl) (r : List Step → Entry)`), with `Rec := List Step → Entry`.
   - `Code0.data (d : IndDecl) (r : Rec) (A : Type)` replaces `(ps : List Par0)`. Delete `Elt0`, `Par0`, `Par0.sems`.
   - `Sem.dat (name : String) (r : Rec) (c : Nat) (fs : List Sem)`: no parameter list, no packed element.
   - `DataRead` becomes a structure: `read : IndDecl → Rec → (A : Type) → A → Sem` (an element's whole meaning), `inj : ∀ d r A, Function.Injective (read d r A)`.
   - `Code0.enc R (.data d r A) a := R.read d r A a`. `Code0.enc_inj`, `dec_enc` and `enc_of_dec` are unchanged in form; `enc_inj` takes the data case from `R.inj`.
   - `TyM.dataName? R` becomes `TyM.dataRec? : TyM → Option (String × Rec)` (no reading needed).
   - Delete `Sem.elt`.
   - `DataRead.WholeFields R` becomes `∀ d r A a, (R.read d r A a).whole`.
   - `Sem.le`'s `dat` clause relates any two `dat`s with equal name, record and constructor, fieldwise (it no longer requires `none`).
   - Add `Sem.small` and `semHeight` (`DataModel/Faithful.lean`).
2. **`Pi.lean`**: `TyS.data R` becomes `TyS.dataRec`.
3. **The data model** (`Data.lean`, with the prototype's `Stages`, `Carrier`, `Members` as new library files). The interface shrinks to what the program decides:
   - `DataModel := { covers, sig : IndDecl → Rec → Nat → Nat → List Small → Shape, recOf : IndDecl → List Sem → Rec, paramTy }`. `Shape := leaf (B) (c : Code0 B) | sub (d : IndDecl) (r : Rec)`.
   - **Everything else is defined, and its laws are library theorems** (no field to prove):
     - `car d r` (the stage equal to the depth), `meanC`, `Mem` (`mem_iff`);
     - `read := ⟨fun d r A a => if h : A = car d r then meanC (cast h a) else .el0 A a, _⟩` (injectivity from `meanC_inj`);
     - `tyOf d r := .t0 (car d r) (.data d r (car d r))`;
     - `tyM d ps := tyOf d (recOf d ps)`, or `prop (Nonempty (car d (recOf d ps)))` for a `Prop`-sorted declaration;
     - `fieldTyR d r c i e` is the shape's type (a leaf's code, a `sub`'s `tyOf`), and `fieldTy d ps c i earlier := fieldTyR d (recOf d ps) c i (earlier.map Sem.small)`;
     - `ctorM d ps c fs := .dat d.name (recOf d ps) c fs`: no packing, no case split.
   - **Deleted:** `readOf`, `pack`, `tag`, `fields`, `rank`, `recArgs`, `read_eq`, `tag_pack`, `fields_pack`, `pack_fields`, `pack_isSome`, `rank_lt`, `parOf`, `parsOf`, `eltOf`, `ParamsCoded`, `ctor_mem_tyM`, `Sem.not_mem_dat_none`, `small`/`El`/`enc`/`dec` of `Data.lean` (the `small` cut is not needed: a shape's leaf is a level-0 code by construction), `libModel` (the library's declarations get signatures like any other), and `DataGeneric.lean` whole.
   - `OpenIn T v` is the `dat` of `T`'s name and record with whole fields that is not a member. `MovedOf.dat` drops `el`.
   - **The record layout (canonical).** `recOf d ps path` is the entry of the closed field type reached along `path` through `d`'s self positions (each step a constructor, a field, and the earlier fields read small), computed by the reference run of the declared field-type terms at the parameters of the descendant `path` reaches. Do not keep the root only (§13.5).
   - **The signature.** `sig d r c i e` is `r [(c, i, e)]`'s entry where there is one, `sub d (r ∘ ((c, i, e) :: ·))` at a self position, and `sub e' (recOf e' args)` at a nested position, the arguments built from `tyOf d r`. A self occurrence at the same parameters gets the same record, extensionally (`shift_hRec`'s form).
   - Large parameters are never stored. They enter only through the entries the run computes from them (§8).
4. **`Apply.lean`, `Apply1.lean`**: the codecs at a data code go through `R.read`. `Lvl.Lawful` holds as now, `dec_enc` from `R.inj`. `closureAt` is unchanged.
5. **`Value.lean`** (`Value.mean`):
   - `.ind ty c _ ps fs` takes the record from the written parameters (`recOf d (meanParams …)`), or from the hint's record when parameters are omitted (`hint.dataRec`, D8). It is `.dat ty r c (meanFields d r c 0 [] fs)`, the fields read at `fieldTyR d r c i`.
   - `.tInd` is `.ty (tyM d (meanParams …))`.
6. **`Places.lean`**:
   - `semRank := semHeight` (no data model, no `Γ`);
   - `dataTyS n r` is `tyOf` of the declaration named `n` at `r`, and `contentTyS` reads a `dat` field's own record;
   - `reDat n r c fs := .dat n r c fs` (no repacking);
   - `fieldHint` reads `fieldTyR` at the value's record.
7. **`Run.lean`**:
   - `.tind` is unchanged in form.
   - `.ctor` builds `.dat d.name r c fs` at type `tyOf d r`, where `r` is the written parameters' record, else the hint's record, else the record of the parameters `unifyTyS` solves.
   - `rankOf` reads `semHeight`.
   - **`unifyTyS` is the one design point.** Its `.tind` case read parameters off a data field's code (`R.data`), and a record keeps no parameter list. Two cases remain available:
     - a type parameter's entry, which the canonical record keeps, so give the record a parameter key per type parameter;
     - a self occurrence at the declaration's own parameters, whose record is the value's record.

     A value parameter (read small) or a large parameter cannot be solved from a field's type. The run must then take the record from the hint. Check the suite for unannotated constructor values whose value parameters only a field's type determines. That is the first thing I would expect to differ from the checker.
8. **The core lemmas** (`Locality`, `LocalityRun`, `RunPres*`, `RunOrd`, `RunCongr`, `SubstDefs`, `RunSubst`, `HintIndep`, `AssignCongr`): every case that builds or takes apart a data meaning loses `el` and reads a record instead of parameters. `RunCongr`'s rank case no longer reads the data model. Mechanical, as D32's re-proof was.
9. **`Mono.lean`, `BotWrite.lean`, `WF.lean`, `State.lean`**:
   - toy values (`pv`) lose `el`;
   - `mean_updAt_bot` gets simpler (`reDat` does not repack);
   - `pmem` is unchanged in form.
10. **`Steps/`**:
    - `CtxOk` gains `faithful : CtxFaithful K ρ` (`Faithful.lean`);
    - `fieldTypesOf_step_stmt` is stated on `fieldTyR` at the value's record;
    - `Records.lean`'s `enc_whole_lvl0` takes `WholeFields` from `mem_whole`.
11. **`Consistency.lean`**:
    - `exists_dataModel` becomes `ExistsDataModel` (covers and faithfulness only; the laws are theorems);
    - `false_means_empty` holds because a declaration with no constructors has no stage element (`mem_iff` at `Fin 0`).

### 14.2 Which lemma replaces which

| Core (today) | Prototype (to port) |
|---|---|
| `ctor_mem_tyM`, `ParamsCoded` | `memTy_tyOf` with `mem_iff` (a constructor value recording `r` is a member iff its fields fit) |
| `pack_isSome`, `tag_pack`, `fields_pack`, `pack_fields` | `mem_iff`; for elements, `meanC_inj`, `mem_iff_meanC` |
| `read_eq`, `DataGeneric.Coherent` | none: the reading is `meanC` |
| `rank_lt`, `recArgs`, `gRank_lt`, `crank_self` | `semHeight_field_lt` (prototype: `depth_field_lt`) |
| `DataRead.WholeFields` at the model | `mem_whole` |
| `Code0.enc_inj` (data case) | `meanC_inj` |
| `parts_ctorM` | `rfl` |
| `DataGeneric`'s `gPack_isSome`, `sraw_*`, `NModel`, `view`/`unview`, `progEnv_car` | `tele_image`, `lvl_inj`, `rz_succ_iff`, `rz_le`, `rz_depth` (nesting needs no functor: a nested field is a `sub` like any data field) |
| `FieldsFaithful` (DataGeneric) | `Faithful.FieldsFaithful`; small keys: `mem_small_inj`; residual: `re_faithful` with §12's lemma |
| `libModel_fieldTy_pair` | the faithfulness instance for `Pair`'s signature |

### 14.3 What I expect to break

- **The core lemmas**: the data cases only, mechanically.
- **The regress files that build hand models or packed values.** These need their models rewritten as signatures: `DataCodes`, `CodeRuns`, `DataOfChoice`, `DataOfChoice_189132fd`, `SiblingAccess` (its `ctorMOld` record of the old semantics stays as history), `PartlyMoved`, `OpenWriteDep`, `PartialMoveDep`, `Adequacy_flipped`, `ShapeAgree`, `CodeClosures`, `StepKinds`, `DepSitesMore`, `CE4_flipped`, `JoinProbes`, `PartMoveRead`, `UntypedNil`.
- **`DataModel/RankCounterexample.lean` and `Counterexamples.lean`** record the old definitions. Delete them with the port, or keep them pinned as history.
- **`unifyTyS`** (above): the one place where I expect the run and the checker to disagree on an accepted program until the record layout gives it what it needs.
- **What should get simpler:** `mean_updAt_bot`, `RunCongr`'s rank case, `Places`' navigation (no repacking), and everything that cast between carriers.

## 15. The rank the recursion knot needs

The knot asks for two things:
- a strict part of a value, reached by any path of field steps through any nesting, has strictly smaller rank, under every assignment, including where the entry value has moved or open parts elsewhere;
- every value has a finite rank.

`semHeight` (`Faithful.lean`) is a function of the meaning alone, natural-number valued:

| meaning | `semHeight` |
|---|---|
| `dat …` (whole, partly moved or open alike) | one more than the largest height of its fields |
| a whole number `el0 Nat n` | `n` |
| `moved`, `•`, a function `el0 C f`, a type value, `err` | `0` |
| an unknown | the height of its assigned element (the meaning under the assignment) |

**What it gives.**
- Every field of a `dat` has smaller height, through every declaration and every nesting (`semHeight_field_lt`). So along any path of field steps the height strictly decreases.
- This holds for every meaning, so under every assignment, and wherever moved or open parts sit elsewhere in the value: a partly moved or open value is still a `dat`.
- A number's predecessor has smaller height, so a recursion through a number's predecessor decreases too.
- Heights are natural numbers, so every value's rank is finite.
- The W-type shape that would break this is rejected by the checker (§7).

**What it does not give.**
- **The link from the checker to the meaning.** That a recursive call [Rec] accepts, at a strict subterm of `xⱼ`'s entry value as refined so far, has as its argument's meaning a value reached from the entry value's meaning by field steps. Under an assignment that holds only if the assignment satisfies the recorded refinements (`TypedAssignment.refs`), so "every assignment" must be every typed assignment satisfying the records. That is the semantic [Rec] lemma, separate from the height.
- **Decrease through a function application.** A function stored in a field is a leaf of height 0, and what it returns is unrelated. [Rec] never counts an application's result as a strict subterm, and positivity rejects the shapes that would need it.
- **Agreement between a number's two forms.** A whole number is `el0 Nat n` and a partly moved one is a `dat "Nat"`. Their heights agree along predecessor steps (`S(⊥)` has height 1), but a lemma that the run's step from `el0 Nat (n+1)` gives `el0 Nat n` is the run's business, not the height's.

## 16. Next

- ~~The port is the spine lead's (§14).~~ The port was done by this lane (§17).
- On the ported definitions: the generic signature from the declarations, with records by the run along paths (faithfulness by construction where the signature is the run's reading), then §12's closure lemma, then `exists_dataModel` from the library's laws.

## 17. Built: the port (branch `spine-datamodel`)

`lake build OchrMeaning` is green on the (b2) data layer. What landed, and where it differs from the guide (§14).

### 17.1 Definitions

As §14.1, file by file:
- `Sem.lean`: `Small`, `RStep` (§14's `Step`, renamed: `Ochr.Step` is the checker's path step), `Entry` and `Code0.data d r A` in one mutual block, `Rec`, `Sem.dat name r c fs`, `DataRead` a structure, `TyM.dataRec?`, `Sem.small`.
- `DataLib/{Stages,Carrier,Members}.lean`: the prototype's library over `Sem` and `Code0` (the prototype's `depth` was dropped: the rank is `semHeight`, in `Places.lean`).
- `Data.lean`: `DataModel := { covers, sig, recOf, paramTy }`; `car`, `meanC`, `Mem`, `read`, `tyR`, `tyM`, `shapeTy`, `fieldTyR`, `fieldTy`, `entryTy`, `ctorR`, `ctorM` are definitions, and their laws are theorems (`mem_tyR`, `tyR_prop`, `read_wholeFields`, `mem_iff_meanC`, `read_car`). `paramKey j` is where a record keeps type parameter `j`'s entry.
- `Value.lean`, `Places.lean`, `Run.lean` as §14. One difference: the constructor clause takes the record known before the fields from the written parameters, or, for a declaration with no parameters, `recOf d []`; only otherwise from the hint (as the value's meaning already did; this keeps the run hint-independent on parameterless types, `HintIndep`). The clause's result is `ctorOut`.
- Deleted: `DataGeneric.lean`, `DataModel/Proto/`, the old data model's fields and laws.

### 17.2 The core lemmas

`meanV_congr`, `run_congr`, `meanV_substLoan`, `run_substLoan` and `run_congrA` are on the standard axioms. The data cases lost `el` and read a record; `RunCongr`'s rank case no longer reads the data model.

### 17.3 Statements changed (the port forced each)

- `Steps/Statements.lean`: `CtxOk` gains `faithful : CtxFaithful K` (`DataModel/Faithful.lean`). It holds at every Δ and every assignment (the runs of declared types read neither, and the steps change Δ), and has three parts: `FieldsFaithful`, `ParamsFaithful` (§9), and, new, `RecordsFaithful`: the record at parameters keeps each level-0 type parameter's entry at `paramKey`, which is what the constructor clause reads back off a field's type. `fieldTypesOf_step_stmt` reads the fields at `recOf d (meanParams …)`.
- `Consistency.lean`: `DataFaithful dm D P` (was an opaque placeholder): `CtxFaithful` at every state over `P`'s declarations whose globals extend `P`'s (the decisions read the globals). `exists_dataModel` is stated at the checker's decisions and owes `Covered` and `DataFaithful`; `WholeFields` is no longer asked (it is `read_wholeFields`). `false_means_empty` is proved (a declaration with no constructors has no member, `mem_iff`).
- The second prover's files were repaired only where the data layer forced it: `Steps/DropOne.lean` (two data cases: records instead of parameters; `ctorM` is always the tree, so `ctorM_partial` went) and `Steps/DropOneAsm.lean` (the `CtxOk` constructor). `Steps/PlaceTyping.lean`, `Steps/Eq.lean` and `Steps/Records.lean` (docstrings) likewise.

### 17.4 The records, as runs the model now gets right

- **`CountF` computes `3`** (`Regress/DataCodes.lean`, `countF_three`): the closure built by stages along `Π(f : List(Rose(Nat))). Nat`'s code, the stage chosen by the height of the argument's meaning, applied to `F3`'s forest. The recursive call's forest is two field steps down, so two stages lower in height (`stage_count`). `Len([3, 4]) = 2` likewise (`len_member`).
- **`te : TEq(Type, Word, Word)` is a member of its type** (`DataModel/Examples.lean`, `te_ctorM_memTy`): the run's `ctorM` at parameters whose first is `Type`.
- **The degenerate model no longer meets the existence statement** (`DataModel/Degenerate.lean`): it covers every program, and it is not faithful at any program declaring a `Nat` field (`degenerate_not_dataFaithful`).
- The join's drop of a field is below its input (`Mono.JoinDropCounterexample.drop_below`, replacing `joinDrop_not_below`), and `pmem` as first stated holds of a partly moved member (`Regress/PartlyMoved.first_stated_holds`).
- The old counterexamples are kept against a frozen copy of the layer before the port (`DataModel/Old.lean`: `Sem.lean` and `Data.lean` at 34ecffdd under `Ochr.Meaning.Old`): `Counterexamples` (`degenerate_meets`, restated over the declarations the old statement asked to cover; `ctorM_large_not_mem`), `RankCounterexample` (`semRank_eq`), `PartlyMoved.old_pmem_false`, `SiblingAccess.old_collapse`.
- Every regress run evaluates on the new layer (`CodeRuns`, `DataCodes`, `StaticLend`, `CallInPlace*`, `EntryCheck`, `OneCtorEntry`, `PartMoveRead`, `DepSites*`, the rest). Results that changed: the join drop and `pmem` above; `Adequacy_flipped.ctor_no_hint` now asks that the declaration have parameters (without, the record is known before the fields).
- The prototype's examples, residual and adversarial list are on the real layer: `DataModel/Program.lean` (a data model of the probe programs, `dmP`), `Examples.lean`, `Residual.lean`, `Adversarial.lean`.

### 17.4a Two requirements from the proof lead, after the port

- **The run types an embedded value by what it is**, as the checker's `valType?` does: a number at `Nat`, `()` at `Unit`, a constructor value at the type its record names (`Run.lean`'s `.val` clause and `RunCongr.valT`). Its own commit, after the port, so its regressions are attributable: a numeral runs at `Nat` (`CodeRuns.run_num`), and `CallInPlace`'s `let y = 2` binds `y` at `Nat`. With it the base case of the substitution lemma for unknowns holds wherever `DeltaOk` does (`SubstAbs.absFill_shape`, replacing `absFill_shape_false` and `run_substAbs_false`).
- **The levels sort soundness reads** (`Levels.lean`): the codes of `Nat`, `Unit` and a proposition; `Sort l` at `sortSucc l`; a data type at its declaration's sort; a Π-type at its declared sort; a member of `Sort l` is a code of level `l`; only a code of level `0` has `⋆` as a member (a data type's members are trees). All hold on the new codes.

### 17.4b The closure lemma (`Closure.lean`, `ClosureCE.lean`)

The knot's two closure statements (`Steps/FixKnot.lean`: `closure_mem_of_total`, `closure_apply`) are false as stated, each at a small closure (`ClosureCE.lean`, kernel-checked): a closure is built strictly, so `closure_apply` at a function defined only at the arguments applied fails (the closure is `err`); `closure_mem_of_total` fails at sort `0` with a codomain that is not a proposition, at a returned borrow (`OutGood` asks neither the returned label nor the backward function's injectivity), and at a codomain above the closure's level. The forms that hold, for any closure meaning (captures included: the function `g` is arbitrary), on the standard axioms:
- `closure_mem_of_total'`: at `1 ≤ l ≤ 3`, a data codomain whose code fits the level, and a function defined and good at every member argument with one final content per borrow parameter, the closure is a member of its code; `closure_mem_prop'` at sort `0`, the codomain a proposition.
- `closure_apply'`: such a closure applied at member arguments whose domains fit the level is its function's result, at the codomain (a canonical code), as `callOf` reads it.
- **The weakened stage closure** (`ClosureStage.lean`), the knot's stage-`b` meaning: a function good only at arguments whose decreasing component has rank below `b` is not an element of its type (a closure is built strictly), so the stage-`b` closure is typed at a weakened function type, the true codomain below the bound and `Unit` above (`True` at sort `0`), and its function is the stage below the bound and a trivial output above (`()`, the borrow arguments handed back unchanged). It is then an honest element built by the ordinary strict construction (`stage_mem`, `stage_mem_prop`), and applied below the bound it gives the stage's result at the true codomain (`stage_apply`); no fill is needed. At a returned borrow the carrier also asks a returned label and an injective backward function, which `OutGood` does not (`ClosureRef.lean`, `RetGood`); above the bound the borrow's content type is `Unit`, so the trivial output meets it. The knot's statements in the forms that hold are `Steps/FixKnotStage.lean` (`MemBelow'`, `OutGood'`, `PiFits`).
- **The run's stages are the weakened closures** (`Run.lean`'s `.fix`, `RunCongr.fixStage`): stage `k + 1` binds `self` to stage `k`'s closure at the weakened type at bound `k`, so the knot's stage-`b` global is the run's own `self`, and the knot's induction is on "stage `b` is good below `b`" (no stage-stability lemma). The fill of D60 (`mkTelFillL`, `closureFillAt`) is deleted. The hand-built recursions (`Regress/CodeClosures` `Double`, `Regress/DataCodes` `Len`, `CountF`) are built the same way and give the same answers.
- **Adopted into the knot** (after the change of form on `spine-slice`, a6228063): `Steps/Statements.lean`'s `MemBelow` is the bounded membership on the weakened stage closure (with `OutGood'`, `PiFits`, `PiCallable`), `GlobalsOk` asks neither the stored type nor the closure of the definition being checked, `Steps/FixKnot.lean` holds the true forms of the closure statements and the induction in the run's shape (`stages_below`, `knot_member`), and `Assembly.step_member_fix` is assembled through them; `fix_split` (a leaf) is restated to give `PiFits` and the step on `OutGood'`.

### 17.4c The slice's read lemma, the field step, nested parameters

- `DataModel/ReadMember.follow_below_member` (the slice's statement, standard axioms): a meaning below a whole member, read along a path with no strict prefix reading `⋆`; the member's read along the same path is above it and a member of the type the run gives it (a data field by its own record, any other field at the declaration's field type at the member's own earlier fields). It needs `ReadCoherent` on a set of declarations and records containing the root's code (closed under the signature's data and proof fields, each found in `Γ` by name, none named `Nat`, canonical shapes).
- The run's named field step reads a constructor value of the declaration it names, never a number, as `stepV` (Good's (N) already says no constructor value is of a declaration named `Nat`); `StepKinds`' failure became `succField_reads_nothing`.
- `unifyTyS` reads a type parameter back through the records' entries at any depth (`ParamSolve.nested_solves`: `List(List(A))`).

### 17.5 The design point: parameters solved from a field (`DataModel/ParamSolve.lean`)

The checker solves an unwritten parameter from a field's type by reading the field type's parameter list (`Machine.unifyParams`). The model reads back only what the record keeps: a level-0 type parameter's entry.
- **On the suite and the case studies the two agree.** Traced (a temporary trace in `evalCtor`, not committed) over every example and case study as the build elaborates it, and over `lake exe tests` as far as `Quicksort.ScanLeft`: every constructor solved from its fields with no parameter written and no hint naming the type has only type parameters, read as a field's own type (`Opt.Some`, `Pair.Mk`, `List.Cons`, `Box.MkBox`, `And.Intro`) or as a direct argument of a field's type (`ArrayOf.MkArray(s : SliceOf(R))`, `Cell.MkC(h, t : SliceOf(R))`, `GBucket.GCons(…, t : GBucket(V))`). The model reads both (`cell_solves`).
- **They disagree off the suite.** Three constructed programs the checker accepts (`DMProbeSolve`, asserted): `SW` (`Wrap`'s value parameter from `t : Tag(3)`), `SH` (`HW`'s function parameter from `t : HL(F0)`), `SO` (`Opt2`'s value parameter from `t : Tag(3)`, where `Opt2`'s record depends on it through another constructor's equation). The model's run of each fails (`sw_fails`, `sh_fails`, `so_fails`), so `evalCtor_step_stmt` is false there. Solving `n := 3` from `Tag(3)` uses the injectivity of `Tag`, which the model does not have (`Tag(3)` and `Tag(4)` are one type: `opt2_record_not_determined`).
- **The options**, a shared decision: (1) the checker infers from fields only parameters whose declared type is a sort, so a value or large parameter is written or comes from the expected type (rejects `SW`, `SH`, `SO`, nothing in the suite); (2) the record keeps every level-0 value parameter small at `paramKey` too, so `Tag` becomes injective in the model in its value parameters (fixes `SW` and `SO`, not `SH`: a large parameter has no small reading). (1) is the uniform one: the checker's inference then uses only what the model's types keep.
- **Built: option (2)** (the lead's "3b"). `Entry` gains `small (s : Small)`; a record keeps, at `paramKey j`, a value parameter of a level-0 type read small; the run's `unifyArgsTyS` solves a parameter variable standing at such a position to the meaning rebuilt from the small reading (`ofSmall`, with `(ofSmall s).small = s`). `RecordsFaithful` becomes three clauses: type entries kept (as before), value parameters kept small (`values`), and records read value parameters only small (`smallOnly`), so the rebuilt parameter gives the written one's record. `SW` and `SO` now run to the checker's answer (`ParamSolve.sw_ctor`, `so_ctor`); `SH` still fails. That `smallOnly` holds of the canonical model is a guess: a member of a data type is determined by its small reading and its type, and the run's `Eq` in a field type compares members of one type. **The residual rule for the checker**: from a field's type, infer an unwritten parameter only where it stands (at any depth) as an argument at a position declared `Prop`, `Type₀`, or a type in `Prop`/`Type₀`; a parameter standing only at positions typed in `Type₁` or above (a type in `Type₁`, a value of such a type, a function into a universe, `SH`) must be written or come from the expected type.
- Also found: the declarations written by hand in the earlier records numbered a field type's variables earlier fields first; the checker numbers the parameters first (`Machine.fieldTele`). `Program.lean` now follows the checker; no theorem read the variables.

## 18. How existence is proved: the statement repaired, two instances, the plan (existence lane `exists2`, 2026-11-21)

### 18.1 The statement was false, and what changed

`Assembly.exists_dataModel` asks `DataFaithful` at every prefix of the program, hence `RecordsFaithful`. As it stood after §17 that had no instance at any context declaring an inductive (`Exists/RecordsCE.lean`, proof at 1765a998): the raw data code of a `Prop`-sorted declaration over the model's own carrier was a member of `Type₀` (every data code had level 1), no shape means it but a leaf holding it, and `LeafOk` forbids that leaf; `types` forced it at `paramKey 0`, which `leafOk` read as a field key. It was a fault of the model, not only of wording: `MkBox[A](x)` at `A :=` that code fails strictly where the checker accepts. The orchestrator's rulings:
- **(M-a)** a `Prop`-sorted declaration's data code has no level (`Sem.lean`, `Code0.level`), so it is in no universe;
- **(S)** `RecLeafOk` asks `LeafOk` at genuine field keys only; `types` at type parameters of a full-length list; `leafOk` at full-length lists; `ParamsTyped` is membership only (its "or any type value" disjunct is deleted: the run reads a parameter strictly, so it served nothing).

The "no `Accepted` hypothesis" worry is not a problem: `ProgState.step` keeps only items `checkItem` accepts, so `P.inds` holds only declarations `checkInd` passed (positivity included, names unique).

### 18.2 Two instances (kernel-checked, standard axioms, in the default build)

- `Exists/PreludeModel.lean`: the library (`Pair`, `False`, `True`, `And`). `RecordsFaithful`, `FieldsFaithful`, `ParamsFaithful`, `CtxFaithful` at every run context with the model and the library's declarations, under any decisions; `DataFaithful` at every state declaring them; `instance_data` at the checker's decisions.
- `Exists/Step2.lean`: the library and `Bool`, `List`, `def EvT (b : Bool) : Type`, `Rose` (nested in `List`), `TF := MkTF(b : Bool, x : EvT(b))`, `Ev (n : Nat) : Prop` (a value parameter, a self-occurrence at an earlier field, an equation keyed by it, a proof field that is no index), `Q : Prop := MkQ(h : And(Q, True))`. The same bundles, `TF`'s field at `EvT` meaning a closure whose call runs (`instance_data_evt`). No hypothesis on the decisions was needed: every field-type run lemma (`Exists/RunLemmas.lean`) holds under every decision table. Not exercised: `EvT`'s meaning as `defMeaning` computes it (a closure with the same behaviour stands in), piece 5's monotonicity (`Q`'s and `Ev`'s truths are computed outright), an equation side calling a function.

The declarations of both are the checker's, asserted natively (`prelude_inds`, `step2_inds`): that a program state is what `progMeaning` produces needs the checker run in the kernel, which it cannot do.

### 18.3 What the instances taught

1. **`Prop`-sorted declarations are built truth-first, all of them.** At a `Prop`-sorted declaration nested at a `Prop` parameter (`Q` above, accepted) the knot is not guarded: `And`'s record at `Q`'s proposition keeps that proposition as a leaf, which reads `Q`'s record at every depth (`Exists/PropNestCE.not_guarded`, for every faithful record function of `And`). So: the least truth predicate first (impredicative), records whose own occurrences are leaves holding it, then the theorem that the record means the predicate (`ev_tyR`, `q_tyR`). In general the predicate is a fixed point only if every earlier declaration's membership is monotone in its nestable `Prop` parameters: an induction over the declarations (piece 5).
2. **A field typed by a call of a global reads the program meaning of the global** (`ProgState.baseC`). So a declaration's canonical record is a function of the earlier globals' meanings, which are computed under the same model at earlier declarations: well founded by program order through pieces 1 and 2.
3. **Faithfulness there needs the global to return members of `Type₀` or not run** (`Step2.EvTGood`): a global returning a type of another level, or a junk code, has no faithful record. For the program meaning this is the strict run's closure formation (membership of the function type) with `app_mem'` and the stored type's code being the closure's (`fix_split`'s first claim). It does not need `defn_member`, so there is no circle.
4. **A call's value depends on the callee and the argument values only** (`RunLemmas.callOf_val`), so a record keyed by small readings can follow it.

### 18.4 The plan for the general proof

- **The interpreter (piece 3).** For a data-sorted declaration, the canonical field type is read syntactically along the spine of inductive formers in the field-type term (where the declaration itself can occur, only at nestable positions: `.place (.var j)` is the parameter, `M(ā)` is `FTy.data M` at `M`'s canonical record at the arguments, the declaration's own occurrences through the knot's record function), and is the run's result elsewhere (a type function's call, an equation, a value argument, `Nat`, `Unit`), at a canonical frame: the parameters, and earlier fields rebuilt from the projected small readings. Its agreement with the run at every typed frame, by induction on the term with `runT_tind`, `runT_eq`, `runT_call_const`, `runT_teleFrame_param`/`field` (all proved), and three lemmas not yet proved:
  - **members of one type with equal small readings are equal** (`mem_small_inj`, argued in §8; by induction on membership);
  - **frame locality**: a run reads a frame only at the variables its term mentions (the canonical frame and the actual one differ only at earlier fields that are no index; step 2 avoided it because its one such field is a proof, which is `•`). As first written it was false and needs three hypotheses it lacked; restated and under proof, §18.5;
  - **the stored global meanings are well behaved** (18.3 point 3).
- **Guardedness (piece 4)**, for data-sorted declarations only, by structural induction along the same spine: the declaration's records enter only at nestable parameters (D107), which `SemAgree` and `recK_agree` carry.
- **Truth-first (piece 5)** with the monotonicity induction.
- **The records' parameter clauses (6), parameter types (7), the checker's facts (8a, 8b), the assembly (9)** as `Exists/Decomposition.lean` states them.

### 18.5 Frame locality: false as first written, restated (exists3, 2026-11-21)

`General.runT_frameLocal` (two states differing at frame-0 bindings `X` the term does not mention, each holding a whole member of its type at every future, give the same result) is false as written, on three counts:
1. **The states' borrow records were not compared** (kernel-checked: `Exists/FrameLocalCE.frameLocal_false`). `DiffAt` fixed the shape, the counter and the frames, not `lent`, `heldTy`, `heldMem`. A place is read at the typed future, which gives each live label its recorded member, so a binding reading a live label is read differently at two states that differ only there: one frame `{y, x}`, `y` the holder of label `0`, `x` reading `0`; `X` empty; reading `x` gives `1` and `2`.
2. **A value at `X` may read the future, and `Id` observes it** (argued, not checked). `Id`'s observation reads every position the state had, after the side's run and after ending every borrow; a side that makes and ends a borrow substitutes its label in every position's meaning, so an `X` binding reading a label the run later makes reads differently in the two sides of one `Id` on one state and the same on the other. The canonical frame's values are constants (`faithBind`), so the restatement asks constant values.
3. **The decisions may name a place at `X`** (argued). The run accesses, drops, invalidates or re-points the places `Decisions.joinMoves`, `blockCaps`, `invalidated`, `rePointed` give, and nothing tied them to the term: a table naming a field of an `X` binding makes the drop's path update defined on one side and not the other. The restatement assumes `DecLocal`: those places are rooted at the term's free variables (or, for the join and the entry, at places already moved, which a whole value has none of), and an invalidated place shares the written place's root. For the chain's decisions `invalidated` is empty; that the checker's `jdMoves`, `typeState` and the static captures name only such places is an obligation on the checker's decisions, not yet stated as a leaf.

Relation to the other frame results: independent. `Steps/FrameFrag.run_frameS_lf` relates a body's run in place and in its closure (two layouts, a renaming of labels), and `FrameLocCE` refutes the old form of that through a dead label read at two futures; here the layout and the future are the same and only values at unmentioned bindings differ, so `FrameLocCE`'s mechanism does not apply (count 1 is its cousin: a record the relation forgot). `GlobalsLocal.meanV_clo_closed` is about a closure with no capture, not a frame.

The restatement (`FrameLocal/`): an EQUATION, `runT … t (qset Q β' s) = (runT … t s).map (qset Q β')`, where `qset Q β'` replaces the bindings at positions `Q` by `β'` and forgets any borrow held there. At `β' := β`, with `qset Q β s = s`, it says the final state is fixed by `qset Q β` again, so the invariant (the bindings at `Q` unchanged, no borrow held there) needs no separate preservation lemma. Built (no `sorry`, default build): the transform's algebra against every primitive of the state (`FrameLocal/Qset.lean`: writes, pushes, drops, `under`, `mapVals`, [End], [Access], take/hold), the run's primitives and strict tests (`FrameLocal/Prims.lean`: contents, reads, writes, invalidation, `StateOk`, the folds), and free variables under binders (`FrameLocal/Vars.lean`). Also built: calls, the join's drop, [Entry], `Id`'s observation, captures (`FrameLocal/Join.lean`), and the statement's hypotheses (`FrameLocal/Setup.lean`). Left: the induction over the run's mutual block (`FrameLocal/Run.lean`, outside the build: fifteen clauses proved, the borrow and binding forms, matches, constructors, calls, `Id`, closures open; `HANDOFF.md` has the recipes). (It assumed, besides `DecLocal`, that a closure's captures are free variables of its term; `capOrder` is now a structurally recursive insertion sort with the same order, and the fact is the lemma `mem_capOrder`. `List.mergeSort` was not usable: it is irreducible, and existing proofs compute captures of concrete terms by `rfl` and `decide`.)

exists4: the clauses most likely to refute the restatement were done first, and went through. `Id` (count 2's place): with constant values at `Q`, the two sides' observations at a varied position read the same constant on each side (`β`'s at one state, `β'`'s at the other), and off `Q` the transform changes nothing, so the proposition is the same (`observation_qset_iff`; the typing of the written values reads types only at re-pointed places, outside `Q`). The two matches (count 3's place): the join drops only the entry's moved places, which a whole binding has none of, and places rooted at the match's free variables (`joinMoves_avoid`), so the drop is defined on both sides or on neither. Both rest on `DecLocal`; whether the checker's decisions satisfy it is now the open question about this statement.

**Proved (exists4): `FrameLocal.runT_qset`**, in the default build, standard axioms; it assumes `DecLocal` (and, as every run lemma, that the globals carry no label). One gap in the plan, closed without changing the statement: a Π's parameter binders and a closure's stages are functions of the earlier arguments, defined at every argument list, and at a list of the wrong length the domain's or body's variables name other bindings of the frame (`extendBy` pushes the wrong number), possibly varied ones. So the two sides' binders and stages agree only at argument lists of the right length, and "equal by funext" was false. Every consumer (the telescope code `telL`, `piProp`, `PiOk`, a closure's element `mkTelL`, the pushed parameters) reads them only at the right length, so the consumers agree (`FrameLocal/Agree.lean`). The closure's body runs one frame up, under a fresh bottom frame, so `Q` moves up a frame there (`FrameLocal/Fix.lean`: `fixBodyAt_qset`, `fixStage_qset` by induction on the stage).

**What frame locality asks of the checker** (exists4, `FrameLocal/DecAt.lean`). The run consults the decisions `DecLocal` constrains only at three kinds of node: a match (the join's drop, `joinMoves` = the checker's `Decide.jdMoves`; [Entry]'s captures, `blockCaps` = `BlockCaps.staticBlockCaps`), `J` (the same two, at the `J` term and at its transported term), and `Id` (the re-pointed bindings of a side, `rePointed` = `Decide.typeState`'s `repointed`); plus `invalidated` everywhere (a property of that function alone, and the chain's table invalidates nothing: `chainDecisions_inv`). `DecAt D t` is exactly that obligation at one node, and a term without such a node (`hasDecNode = false`) asks nothing (`decAt_of_hasDecNode`). The field and parameter types of `Step2.lean`'s declarations have no such node (a `#guard` in the build), so there frame locality needs nothing of the checker. In general a field type may contain any of them (an equation side is arbitrary code, `Probes.DMXFrame`), so the obligation for the machine lane is: `DecAt (chainDecisions fuel st)` at every node of every accepted declaration's field and parameter types. Not yet done: `runT_qset` still assumes the global `DecLocal`; threading the node-wise hypothesis through its induction is mechanical (the handoff has the recipe).

### 18.6 The knot: false as first written, and two shapes the interpreter cannot build (exists5, 2026-11-22)

`General.knot_exists` (pieces 3 and 4 for a data-sorted declaration) is false as written (kernel-checked: `Exists/KnotCE.knotOld_false`, standard axioms). It had no hypothesis that `d` is accepted, and its only hypothesis on the earlier declarations' records, `hpar`, compares a value parameter by equality. A value parameter can hold a member of `d` itself, and a member carries its record (`Sem.dat d.name r c fs`). So an earlier record can read the knot's record, at any depth, through a value parameter, and `hpar` still holds. The counterexample: `Pt (A : Type) (a : A) := MkPt` and `D2 := D2Leaf | D2Node(x : D2, p : Pt(D2, x))`. The checker accepts both (asserted natively in the file). Take `Pt`'s record at `[A, v]` to hold, at the empty path, the flip of `v`'s own record at the step past field `p`'s key. If a knot `S` existed, field `x`'s run makes `D2Leaf` at `recK S []` a member. Field `p`'s run then gives `Pt` at `[D2's code, D2Leaf]`, and the knot's record past `p`'s key is that record (`recK_cont`). So the knot's record at one path equals its own flip.

Two more shapes the checker accepts defeat the planned interpreter (the field type read along its spine, the run's result elsewhere, at a canonical frame) without making the statement false:
1. **An equation side reading an earlier field whose type mentions `d` or a nestable parameter.** Examples: `LD := LDLeaf | LDNode(xs : List(LD), e : Eq(Nat, match xs {Nil => 0, Cons(h, t) => 1}, 1))`, and `W (A : Type) := WL | WN(ws : List(A), e : Eq(Nat, match ws {…}, 1))` nested as `UW := MkUW(w : W(UW))`. The knot needs every field's kind (what its key holds) to be independent of the record (`KnotSpec.guarded` at depth 0). Here the kind is the proposition the run computes, and whether that run is defined depends on the record: its strict tests read the members' records. A depth-guarded knot cannot follow this. Following it would need a new whole-run lemma relating runs under different records (values carry records and the strict tests read them), larger than frame locality. Each example has a hand-chosen field type, so the statement is not false there.
2. **A data-sorted `d` nested through a `Prop`-sorted declaration at a `Prop` parameter.** Example: `PP (A : Type) : Prop := MkPP(x : A)`, `Q (P : Prop) := MkQ(h : P)`, `D := MkD(q : Q(PP(D)))`. `Q`'s record at that parameter holds the proposition "`D` is inhabited", which no depth bound fixes (`SemAgree` relates codes of data-sorted declarations only). This is `PropNestCE` again, now for a data-sorted `d`. A fixed point exists (any truth works), but it needs the truth chosen first.

Lean's kernel rejects every one of these declarations (checked with the local toolchain). `D2`, `LD` and `LQ` get "nested inductive datatypes parameters cannot contain local variables". The `Prop` nesting gets "mutually inductive types must live in the same universe". Lean accepts nested occurrences whose parameters are closed (`Pl D []`, `Pn E 3`).

**Adopted by the lead, subject to measurement on the checker** (2026-11-22): two checker rules in Lean's spirit.
- **(B)** A variable counts as mentioning everything its declared type mentions. Then no equation side, call argument or value argument in a field type reads an earlier field whose type mentions `d`, and a parameter read so is not nestable. This rule is weaker than Lean's: `Pn(E, m)` with `m : Nat` stays accepted.
- **(A)** A data-sorted declaration does not occur inside an argument at a `Prop` parameter.

Under (A) and (B), every non-spine node of a field type (an equation, a call, a value argument) reads only bindings whose values and types are fixed across the knot's comparisons. Its result is then the run at a canonical frame under the earlier model, with no dependence on the record. Agreement with the actual run takes frame locality (`runT_qset`, swapping the bindings the node does not read) and a model congruence: a term that names no part of `d` runs the same under two models differing only at `d`'s records. That congruence is piece 1/2 of `Decomposition.lean` in a narrowed form. `hpar` stays as it is: value arguments then never carry the record. The restated `knot_exists` also needs:
- the parameter types of earlier declarations to depend only on the parameters their type terms mention (a value argument's run reads its parameter type as its hint, and the constructor and value clauses read the hint);
- `DecLocal`, or `DecAt` at the non-spine nodes;
- the globals to carry no label.

`GlobalsTyped` is not needed for the agreement itself, only for `Lvl0`. If (B) is refused instead: `hpar` must compare value parameters by their small readings (what the canonical records read of them), and the relational run lemma above is needed.

**Built (exists5), default build, standard axioms.** `Knot/Swap.runT_stateOf_swap` is frame locality between two one-frame states that differ at a set of binding indices. `Knot/Grammar.lean` holds the field-type grammar `Spine` with (A), (B) and (B2), the variables that vary between the knot's comparisons, and `ParamTyLocal`. `Knot/Interp.lean` holds the interpreter and the canonical frame. `Knot/Guard.knotK` is the knot, and its guardedness is proved (`ftyK_agree`) from `Spine`, `hpar` and `ParamTyLocal`. The canonical frames at agreeing parameters are equal, not merely agreeing: everything in them that could differ varies, and is a dummy. `General.knot_exists` is restated with `knotK` as its witness. Its agreement half is proved along the spine (`Knot/Agree.knotK_agree`), assuming one fact, `SteadyAt`: each steady node's run in the actual frame gives its value at the canonical frame. `SteadyAt` needs frame locality (`runT_stateOf_swap`), a model congruence for terms that do not name `d`, `GlobalsTyped` (so that the bindings swapped hold members of their types) and the `teleFrame` repair below; `HANDOFF.md` has the plan. A second obstacle was found while setting it up: `teleFrame` typed the field being typed (a `moved` binding) by its own type, read from the knot's record, so the canonical frame would be self-referential, and frame locality swaps only whole bindings. The repair (the later fields typed `err`, as the checker binds them) was ruled and is built: §18.7.

### 18.7 The frame a field type is evaluated in: the fields not yet bound are typed `err` (exists6, 2026-11-22; docs/31 D160)

Ruled by the lead on `exists5`'s proposal (§18.6, last paragraph). `teleFrame` now types the field being typed and every later field `err` (value `moved`, read `other`), as the checker's `fieldTele` binds them (no type, `⊥`, `other`); before, it typed them by the model's own field types, so the field being typed carried its own type. The checker's frame is pinned by `Exists/TeleFrameGuard.lean` on a declaration with a dependent field and one with three fields and a parameter: the frame matches `teleFrame` binding for binding (the checker's frame sits above one more frame, which binds the parameters; that predates the change). Everything that used `teleFrame` builds unchanged, the two instances included. The knot's canonical frame (`Knot.canFrame`) already bound the later fields so; the actual frame and the canonical one now agree there exactly.

### 18.8 The knot exists (exists6, 2026-11-22)

`Knot.knot_exists` (`Exists/Knot/Exists.lean`, default build, standard axioms) is pieces 3 and 4 for a data-sorted declaration: a guarded knot whose field types are the reference run's readings of the declared field types, in the frame the checker types a field in, at the knot's own records. It assumes five named facts: `GrammarOk` (the checker's grammar, below), `hpar` (the earlier declarations' records are parametric in their nestable parameters), `ParamTyLocal` (the earlier parameter types read only the parameters their type terms mention), `DecLocal` (the checker's decisions are local, frame locality's obligation) and label-free globals. The witness is `knotK`; guardedness is `ftyK_agree` (exists5), agreement along the spine is `knotK_agree` (exists5), and agreement at the steady nodes is `steadyAt_knotK`.

**The steady nodes** (`Knot/Steady.lean`). The actual frame and the canonical one are one-frame states whose binding lists are equal except at the earlier fields that vary or are no index and at the parameters that vary. At those, both hold whole members of their types with the same declared readings (the actual frame's are the given fields and parameters; the canonical frame's are `0 : Nat`). A steady node reads none of them, so frame locality (`runT_stateOf_swap`) gives the same run in both. A steady node avoids the declaration, so the model congruence gives the same run under the knot's model and the earlier one.

**The model congruence** (`Knot/Congr.lean`, `runT_congrR`, no assumed fact). A term that avoids `d` runs the same under a model and under the same model with `d`'s records replaced. Attacked before it was proved. The strict tests read whole states, but only through the reading and open membership, and open membership does not depend on the model at all (`omem_indep`: it reads the signature, which is the same for every model). Values carry records, but a member's test reads the record the value carries. A type function's result may mention `d` without naming it, but a call applies the global's meaning, which neither model changes. One gap was found and closed: `Avoids` as first written allowed an embedded sealed program naming `d` in its term (`avoidsOld_gap`, kernel-checked); it now asks no embedded value at all, which declared field types never hold.

**Two restatements.** (1) The earlier fields are asked to be members of their field types at the knot's model, which is what `FieldsFaithful` hands its consumer (`FieldsTyped`), instead of fitting the knot's shapes. Fitting gives membership only away from junk leaves, which needed `GlobalsTyped`; `knot_exists` no longer assumes it. (2) The grammar is one decidable fact about the checker. `spineB` decides `Spine` from syntax, the declarations and the declared parameter type terms (`spineB_sound`), and `GrammarOk Γ d` is that check at every field of every constructor (a `Decidable` instance). `checker6` reads `Knot/Grammar.lean` as its specification; until the checker enforces `GrammarOk`, it is counted as assumed.

### 18.9 `Prop`-sorted declarations: two findings, and a rule requested (exists6, 2026-11-22)

**Nesting across sorts** (`Exists/CrossSortCE.lean`, the checker's verdicts and stored nestable sets asserted). Rule (A) checks the sort of the declaration at an occurrence, not where that declaration passes the parameter on. The checker accepts `PP (A : Type) : Prop := MkPP(x : A)`, `E (A : Type) := MkE(p : PP(A))`, `D := MkD(e : E(D))`; `Wrap (P : Prop) := MkWrap(h : P)`, `QW : Prop := MkQW(w : Wrap(QW))`; and `E2 (P : Prop) : Prop := MkE2(w : Wrap(P))`, `Q : Prop := MkQ(e : E2(Q))`. Lean's kernel rejects `D`, `QW` and `Q` ("mutually inductive types must live in the same universe"). Consequence: `mono_prop`'s hypothesis cannot hold for `E2`, whose shape at `w` is a data sub-record that depends on `P`. **Corrected claim**: exists6 first argued that `knot_exists`'s hypothesis `hpar` is false for `E` in every program declaring `E`. That was wrong. A faithful record may keep `PP(A)` as `PP`'s sub-record rather than as a proposition leaf, and the canonical one does. `CrossSortCE.hpar_E` and `fields_E` check, with `E`'s parameter nestable as the checker stores it today, that the canonical records are parametric and faithful at `E`'s field. The knot does not need (A*).

**Rule (A*), adopted by the lead** (2026-11-22, subject to measurement): Lean's rule, a nested occurrence passes only through declarations of the occurring declaration's sort. (i) At an occurrence `M(…d…)`, `M` has `d`'s sort. (ii) A parameter is nestable only if it is passed only to declarations of its own declaration's sort. Both are decidable predicates in `Knot/Grammar.lean` (`occSortB`, `NestSortB`, `AStarOk`), `checker6`'s specification. Today `E`, `E2` (by (ii)) and `QW` (by (i)) fail them (asserted). It is what the truth-first construction needs.

**`truth_exists` as written is false** (`Exists/TruthCE.truthOld_false`, kernel-checked). It assumed nothing of the earlier records. Take `N (P : Prop) : Prop := MkN(h : P)` and `Q : Prop := MkQ(h : N(Q))` (both accepted, by Lean too), with `N`'s record at `P` holding the leaf `¬P`. Then any faithful record of `Q` makes `Q` inhabited exactly when it is not. The contradiction comes from the faithfulness clause alone. The restatement adds that the earlier records are monotone in their nestable `Prop` parameters (`mono_prop`'s hypothesis, supplied by the assembly's induction) and the grammar fact under (A*). Then the one-step operator is monotone and its least fixed point is the truth predicate.

**`mono_prop`, proved** (`Exists/PropMono.lean`), and generalized: the shapes at the stronger parameters are the same, weaker proposition leaves, or sub-records of a `Prop`-sorted declaration whose inhabitation is implied (`ShapeLe`). The step is direct: the same constructor with the same fields. Its content is its hypothesis, which (A*) makes attainable: every shape a nestable `Prop` parameter reaches is then a proposition leaf or a `Prop`-sorted sub-record.

**`truth_exists` restated** (`General.lean`, `sorry`; plan in `HANDOFF.md`). It adds rule (A*), the earlier records' `ShapeLe`-monotonicity, frame locality's facts and local parameter types. It also returns `d`'s own records monotone, so that the induction over declarations continues. The grammar fact for a `Prop`-sorted declaration is still to be added. The least fixed point of a monotone operator on predicates is built (`Exists/Truth.lean`, `lfpP_fixed`).

### 18.10 The grammar's condition (B2) weakened; what it still excludes (exists7, 2026-11-22)

**What (B2) was for.** The knot reads a value argument of a nested occurrence `M(ā)` by running it at its hint, `M`'s parameter type at the earlier arguments. When that type mentions an earlier argument that varies (the code of `d` itself, at a nestable parameter), the hint varies between the knot's comparisons, and so could the value; the value is then a parameter of `M`'s record, which the guardedness argument compares by equality. (B2) excluded the case. The checker does not enforce it and Lean does not ask it: `NF (A : Type) (n : Nat) (f : NegF(A, n)) := MkNF(y : A)` with `DF := LeafF | NodeF(p : NF(DF, 0, ()))` is accepted by both (the checker's agent reported it after D121; Lean's kernel accepts the analogue, checked locally).

**Weakened** (`Knot/Grammar.lean`, `Knot/HintFree.lean`, default build, standard axioms). Out of tail position the run reads its hint in three clauses only: a constructor whose parameters are not written (of a declaration with parameters), which takes its record from the hint; an embedded value; and `clone`, `peek`, `inplace`, which hand the hint to their argument. Every other clause runs its subterms at hints of its own or at none (`tailHint false`). So a value argument headed by none of these runs the same at every hint (`runT_hintFree`). (B2) is now: the hint is steady, OR the value argument does not read its hint (`hintFreeB`). Guardedness (`Guard.itpArgs_agree`) uses the second disjunct directly; agreement never used (B2). `knot_exists` is unchanged in statement and assumptions; `GrammarOk` now holds at `DF` and at `DK2 := LK2 | NK2(p : PK(DK2, Nil[Nat]))` (`Exists/HintShapes.lean`, asserted).

**What it still excludes.** A value argument headed by a constructor whose parameter is not written, at a hint computed from the type being declared: `TK (X : Type) : Type := List(Nat)`, `PK (A : Type) (t : TK(A)) := MkPK(y : A)`, `DK := LK | NK(p : PK(DK, Cons(0, Nil[Nat])))`; likewise `DT3` through a type function whose other arm reads the parameter. Both are accepted by the checker and by Lean. The run gives the bare `Cons` the record of its hint, `PK`'s parameter type at `DK`'s code, and the knot knows that type only through `ParamTyLocal`, which lets it read `A`. A hand-chosen model in which `PK`'s parameter type at `A` is `List(Nat)` with `A`'s record at its parameter key would make the value carry the knot's record, as in `KnotCE`. The canonical model does not do that (`TK` ignores its argument), but seeing so needs facts about a global's meaning and a run's dynamic reads that the knot does not have. The neighbours are rejected: a value argument may not name the type (`Pl(DL, Nil[DL])`, D36/D71), and a parameter no field determines must be written (`PT(DT, MkTg(3))`, resolution). So the unwritten parameter is always fixed by the constructor's fields; only the run reads it from the hint. In Lean the elaborated term writes every parameter (`@List.cons Nat 0 []`), and the kernel never reads an expected type. A ruling was requested (§18.10 is where it will be recorded).

### 18.11 `Prop`-sorted declarations: the truth-first construction, proved (exists7, 2026-11-22)

`Knot.truth_exists` (`Exists/Knot/TruthExists.lean`, default build, standard axioms) is pieces 3 and 4 for a `Prop`-sorted declaration, in the same form as `knot_exists`: a spec whose records' field types are the reference run's readings of the declared field types at those records. It also returns `d`'s code at its records as the proposition of a truth predicate, and those records monotone in `d`'s nestable `Prop` parameters (what the next declarations' `hmono` reads). It assumes the grammar fact `PGrammarOk` (about the checker), `DecLocal` (an obligation on the decisions), and for the assembly: the earlier `Prop`-sorted records monotone (`hmono`), `ParamTyLocal`, label-free globals.

**The construction.** A `Prop`-sorted declaration's code `uTyR d r = TyM.prop (Nonempty (ucar d r))` keeps nothing of its record but whether it is inhabited. So fix a truth predicate `T`, and read every occurrence `d(ā)` as the proposition `T ā` (`TruthInterp.lean`: `semP`, `itpP`, `ftyP`, a copy of the knot's interpreter with that one change). The field types then read no record of `d`, so the record `truthRec T` they make needs no knot (a `KnotSpec` whose field types ignore the record function; guardedness is reflexivity). The one-step operator is "`d` is inhabited at `truthRec T`". It is monotone (`TruthMono.ftyP_le`): along a `PSpine`, a varying argument is a parameter, `d` itself, or a `Prop`-sorted declaration applied, so its value is a proposition that only weakens (`semP_le`). `d`'s own occurrence is the leaf `T ā`. An earlier `Prop`-sorted declaration's record weakens by `hmono`, and its inhabitation follows (`inhabited_mono`). The steady nodes and the fields that do not vary are unchanged, as for the knot. One subtlety: a declaration nested at its own nestable parameter, `D(D(P))`, reads `T` at arguments that hold `T`. So the operator is monotone only on predicates monotone in their arguments. The truth predicate is the least fixed point on that sub-lattice, which is closed under intersections (`Truth.lfpM`, `lfpM_fixed`).

**Agreement.** At the fixed point, `d`'s code at `truthRec` is `TyM.prop (truthP ā)` (`uTyR_truthRec`), which is exactly what the interpreter reads for `d(ā)`. So the actual run agrees with the interpreter along the spine (`TruthAgree.semP_run`, as `semT_run`). The steady nodes agree by the knot's argument, which was generalized to any spec, its canonical frame typed by the spec's own field types (`Steady.steadyAt_spec`, `Agree.SteadyAtS`; `steadyAt_knotK` is now its instance).

**Against exists6's restatement.** Rule (A*) at the earlier declarations (`hstar`) is not assumed: `PSpine` carries what (A*) says for `d` itself, and the earlier declarations enter only through `hmono`. The monotonicity is asked and returned at the genuine keys (`es.length = i`), which is all that fitting reads (`PropMono.fitsM_mono'`). The third conclusion reads `(S.fty …).mean`, as `knot_exists`'s does.

**Also weakened in `Spine` (A).** It had also asked that a varying type argument stand at a parameter declared `Type`. The knot never used that, and it would exclude `d (P : Prop) := MkD(q : Q(P))`. Only "a varying applied declaration is data-sorted" remains.

## Appendix: the probe programs

In `Meaning/DataModel/Probes.lean`, checked when the file is elaborated, every verdict and every rejection's reason asserted by the build: `DMProbeAdv` (§13: the stuck type equations, `RE`, `RoseL`, `FP`, `H`, `LB`, `MM`), `DMProbeNest` (`Rose`, `CountF`, `F3`/`F2`, `Single`, `S1`, `S2`, `BW`, `BH`, the rejected W-type shapes `WT`, `WT2`) and `DMProbeLarge` (`TEq`, `te`, `te2`, `te3` rejected, `te4`, `LP`, `HL3`, `h3`, `h3bad` rejected, `H`, `RV`, `rv0`, `rv1`). `TEq`, `te`, `HL`, `hl`, `G`, `EqF`, `ef`, `NL` are also in `Examples/Fording.lean` (`InductiveModel`).
