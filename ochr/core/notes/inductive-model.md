# Inductive types: a model and the conditions it derives

Written by the `inductive-model` lane on 2026-10-30, toward the consistency goal, in the style of `depfields-model.md`, `split-model.md`, `rec-model.md`, `erasure-model.md`, `closeoff-model.md` and `frame-model.md`. Branch `inductive-model`, off main `41205bdb` (the theory chain). **Result: no hole.** Every derived condition is enforced by the checker; two conditions are enforced more strictly than the model needs (candidate simplifications); the probes are a registered regression block, `InductiveModel` in `Examples/Fording.lean` (24 declarations; total 1,763 → 1,787).

## 1. The model

Following A.6 (Werner, Carneiro), an inductive declaration `inductive D (x̄ : X̄) : s := C₁(ḡ₁ : B̄₁) | … | Cₘ(ḡₘ : B̄ₘ)` denotes, at once for every value of its parameters, a family of sets:

- **`s = Type₀`**: the least fixed point, over the whole family `ā ↦ D(ā)`, of the operator that sends a family `X` to the tagged disjoint union `⊎ᵢ {Cᵢ} × Σ(g₁ : B₁)…(gₖ : Bₖ)`, where each field type `B_j` is read with the parameters at `ā`, the earlier fields at their values, and every occurrence `D(b̄)` read as `X(b̄)`. Non-uniform occurrences (`b̄ ≠ ā`, D71) make the fixed point simultaneous over the family; that is still a monotone operator on families, so the least fixed point exists (Dybjer's indexed inductive definitions; Carneiro §5 reduces Lean's indices to exactly this).
- **`s = Prop`**: the same least fixed point, truncated: `{•}` if it is inhabited, `∅` otherwise.
- **An equation field** `h : Eq(T, a, b)` denotes `{•}` if `a` and `b` denote the same element and `∅` otherwise, so a constructor whose equation is false contributes nothing.
- **A constructor value** `C(ā; v̄)` is the tagged tuple; it records `ā` only because its type does, and nothing in a program can read a recorded parameter except through its type.

Elimination: a `match` on a data value takes the arm its tag names (the tags are disjoint, the tuples injective); a `match` on a proof cannot see a tag, since every proof is `•`.

## 2. The conditions the model needs

For the operator to be monotone (so the least fixed point exists and the set is well defined):

- **(P1) Strict positivity.** `X` occurs in a field type only as the whole type, or inside another family at a position that is itself positive (a nestable parameter). Never left of a `Π`, never under `&`, never inside a type function that may use its argument negatively.
- **(P2) Non-uniform arguments do not mention `X`.** An occurrence `D(b̄)` may take any `b̄`, but `b̄` itself must not mention `D` (else the index set depends on the family being defined: induction-recursion, which the model does not cover).
- **(P3) No call of a parameter in a field type.** A type operator passed as a parameter may be anything, including a negative one, so applying it to `X` (or to anything) in a field type is unconstrained; it may only index the family.

For the definition to be well-founded as a definition:

- **(I1) Parameter types do not mention `D`.** They are fixed before `D` exists.
- **(T1) Fields form a telescope.** A field's type mentions only the parameters and the fields before it (Σ is read left to right).
- **(U1) Universe bound.** Every field of a `Type₀` (or `Prop`) inductive lives in `Prop` or `Type₀`, so the least fixed point is a set in the same universe (Ochr's universes are not cumulative and `Prop : Type₁` sits beside `Type₀`). Parameters may be of any universe: they only index.

For elimination to be sound:

- **(S1) Large elimination only from subsingletons.** A match on a proof can produce data, or a type, only if the proposition has at most one constructor and all that constructor's fields are proofs, so that no two proofs could be told apart (proof irrelevance identifies them). Lean's rule is weaker (it also allows data fields that appear in the indices); Ochr's is stricter, which is sound.
- **(S2) No induction on proofs.** A proof is `•`, so its structure cannot be read; recursion on it would have no measure. (Recursion is never on a proof, RULES note 21.) A recursive subsingleton with no base case (`Inf`) is empty; eliminating it is harmless, and building one needs a recursion [Rec] refuses.

For `Eq` on constructor values:

- **(E1) Disjointness and injectivity** hold in the model because the union is tagged and tuples are injective, at one type `D(ā)`; for a dependent constructor, injectivity is a dependent conjunction, so splitting only when the index fields agree (D64's restriction) is sound and incomplete.
- **(E2) Ignoring recorded parameters is sound.** Two values compared at one type record the same parameters, and no code reads a recorded parameter, so conversion and `Eq` may ignore them (`ParamConv` shows the type check that keeps values at different parameters apart).
- **(E3) Equations at non-data types are harmless.** `Eq` decides only by conversion (`⊤`) or by distinct constructors of one inductive (`False`); at a function type, a sort or a proposition it is otherwise stuck. So an equation field over any type adds no rule that could prove `False`.

## 3. Against the current rules

| Derived condition | Enforced by | Probe |
|---|---|---|
| (P1) strict positivity | `firstOrderTerm` (no `Π`, `&`, sort; fields are first-order data, parameters or earlier type functions), K4's nesting condition (`paramNestable`, `nestViolation`), and K4's check that a type-function field does not compute to a `Π`, a sort or `&` | existing `Positivity*` blocks; `NegV` |
| (P2) non-uniform arguments | `firstOrderArgs`: at a value parameter, any erased term not mentioning `D`; at a type parameter, a first-order type | `G`, `NL` (accepted), `NegV` (rejected) |
| (P3) no call of a parameter | `firstOrderTerm` accepts only calls of earlier *global* type functions | `HL` (accepted), `HL2` (rejected) |
| (I1) parameter types | arity: `D` cannot be applied without all its parameters, so a parameter type mentioning `D` is ill-formed | `PD` (rejected) |
| (T1) telescope | `IndDecl.fieldRefs`, before anything is evaluated | `LateEq` (rejected) |
| (U1) universe bound | `checkInd`'s `sortOf T > 1` on each field at the generic telescope; `d.sort ≤ 1`; [T-Ref] for `&` | existing `Universes`, `Sorts` |
| (S1) subsingleton elimination | `largeElim` (zero constructors, or one whose fields are all proofs by `fieldTermIsProp`), applied whenever a match on a proof produces a non-proof | `UseIsZ`, `TOf` (accepted); `TT`, `TT0` (rejected) |
| (S2) no recursion on proofs | [Rec]'s decreasing parameter must be a `Type₀` inductive | `FromInf` (accepted), `InfLoop` (rejected), `FordLe.LeZ` |
| (E1) disjointness, injectivity | `mkEqM` (`distinctCtors` within one inductive; injectivity at the equation's parameters; D64's restriction for dependent constructors) | `FordVec`, `InjSame`, `InjLen` |
| (E2) recorded parameters | the type check at every use (`expectTy`); `valType?` reads recorded parameters when present | `FordVec.ParamConv` |
| (E3) equations at any type | `mkEqM` decides only by conversion or by constructors of one inductive | `TEq`/`te`/`teBad`, `EqF`/`ef`/`efBad` |

No derived condition is missing from the checker. Copy-ness was checked too (an untyped value's copy-ness comes from its recorded parameters, a stuck field type is not a copy type, so the generic path is never more lenient than an instance) and needs nothing new.

## 4. Candidate simplifications (described, not implemented)

- **The equation-field restriction "`T` is first-order data" (D71) is not needed, and is bypassed anyway.** A field `h : Eq(U, a, b)` with `U` a *type parameter* passes the check, since a parameter counts as first-order; instantiating `U` at `Type`, `Prop` or a function type then gives an equation between types, propositions or functions (`TEq(Type, Word, Word)`, `EqF(Π(x : Word). Word, …)`), which the probes show is harmless (E3). The restriction protects nothing the model needs, and it does not constrain what it says it constrains. Either drop it (an equation field over any borrow-free type, still with no part mentioning `D`), or state in the paper that it is a syntactic convenience, not a soundness condition. Figure 16 already records that no proof of `False` forced it.
- **[Ind-decl]'s premise order.** The paper evaluates parameter types with `D ∉ Σ`; the checker adds `D` (without constructors) to the signature *before* the parameter telescope. This is harmless, since any mention of `D` in a parameter type needs all of `D`'s parameters and is ill-formed by arity (`PD`), but reordering `checkInd` to check parameter types first would make the checker match the rule literally and give `PD` the rule's own reason.

## 5. Open

As with every model lane, the argument assumes the stability conjecture where refinement meets a match (a field type re-normalised under refinement keeps its meaning); `split-model`'s (S) and the heap-slice proofs cover that part. Completeness gaps noted by the probes, all shared with or stricter than Lean: large elimination from a Forded proposition with several constructors at an index where all but one are impossible (`TT0`); Prop inductives whose fields live in `Type₁` (Lean allows them by impredicativity, Ochr's (U1) does not).
