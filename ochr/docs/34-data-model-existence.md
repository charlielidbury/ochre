# 34. The data model exists: what `exists_dataModel` owes, two constructions, a recommendation

Design note of the data-model lane (branch `spine-datamodel`, from `spine` at d67b1d51). Sections 1–6 are task 1 (the design, before any code); sections 7–10 are task 2 (records against the current definitions, the large-parameter design, the faithfulness draft, and the prototype of the recommended construction), kernel-checked unless marked *argued*. The checker's verdicts on every probe program are asserted by the build (`Meaning/DataModel/Probes.lean`).

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

**The residual** (§3; `RV`, `rv1 : RV(RV(Nat))` accepted, asserted). It is real at the level of faithfulness: computing `RV`'s field type at `RV(Nat)` runs `LenL` on a `List(RV(Nat))` field, which decodes it into `List`'s carrier at `RV(Nat)`'s record. In the prototype's terms that carrier exists before `RV`'s record at `RV(RV(Nat))` is needed: its stages need only the signature at records nested strictly inside (`RV(Nat)`'s, inside `RV(RV(Nat))`'s entry for `A`). This suggests the faithful signature is definable by recursion on records (the structural order of `Entry`), which non-uniform recursion does not disturb: a child's record is built from entries of the parent's. *Argued, not built.*

## 11. Next

With the prototype validated, the port is the spine lead's (§8's cost list, plus `Sem.dat` without `el` and `semRank` by height). On the ported definitions, the general existence proof is then:
- the generic signature from the declarations (`self`, `nest`, closed fields), with records computed by the run (faithfulness by construction where the signature *is* the run's reading, the residual by recursion on records);
- `ExistsDataModel` from the prototype's generic laws, which carry over unchanged.

## Appendix: the probe programs

In `Meaning/DataModel/Probes.lean`, checked when the file is elaborated, every verdict and every rejection's reason asserted by the build: `DMProbeNest` (`Rose`, `CountF`, `F3`/`F2`, `Single`, `S1`, `S2`, `BW`, `BH`, the rejected W-type shapes `WT`, `WT2`) and `DMProbeLarge` (`TEq`, `te`, `te2`, `te3` rejected, `te4`, `LP`, `HL3`, `h3`, `h3bad` rejected, `H`, `RV`, `rv0`, `rv1`). `TEq`, `te`, `HL`, `hl`, `G`, `EqF`, `ef`, `NL` are also in `Examples/Fording.lean` (`InductiveModel`).
