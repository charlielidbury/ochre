import Ochr.Meaning.Consistency
import Ochr.Meaning.DataModel.Canonical.Knot

/-!
# The existence proof, decomposed (statements; each with the author's belief)

`Assembly.exists_dataModel` (`Consistency.lean`) on the ported layer (docs/34 §18): for every program
there is a data model covering its declarations and faithful to every prefix (`DataFaithful`, at
`chainDecisions fuel`). With the universal signature a model is only its records and parameter
types, so the construction is: the CANONICAL records of each declaration, by program order, each
declaration's by the knot of `Canonical/Knot.lean`, and `Prop`-sorted declarations by their truth
predicates (`Exists/Proto/PropSorted.lean`). The pieces, in the order a successor should prove them:

1. `runT_congrDM` (below, stated): the run reads the model's records and parameter types only at
   declarations of `K.Γ`. BELIEVED TRUE, mechanical (every read follows a `K.Γ.find?`: `.tind`,
   `.ctor`, `.val`'s types, `meanV`'s `.ind`/`.tInd`, `runParams`, `runFields`; the carriers, the
   members, the reading and `tyR` are the universal signature's, definitionally the same for every
   model). Template: `AssignCongr.lean` (`runT_congrA`), with the `.fix` helpers.
2. The same with `K.Γ` narrowed to the declarations a term can reach (`DataFaithful` runs a
   declaration's field types under a `Γ` holding LATER declarations too): two contexts whose `Γ`s
   find the same declaration at every name the term mentions or a value it navigates carries give
   the same run. BELIEVED TRUE for field-type terms of accepted declarations (they navigate only
   into values of declarations known when they were checked); the statement needs a
   `Term.declNames`. Not stated here.
3. (Step 2's findings, exists2 2026-11-21, `Step2.lean`.) A field typed by a call of a global type
   function reads the PROGRAM MEANING of that global (`ProgState.baseC`): the canonical record of
   such a declaration is a function of the earlier globals' meanings, which are computed under the
   same model at earlier declarations (well founded by program order, through 1 and 2). And it is
   faithful only if each such global, applied at members, returns members of `Type₀` or does not run
   (`Step2.EvTGood`): a global returning a type of another level, or a junk code, has no faithful
   record. For the program meaning this is the strict run's closure formation (membership of the
   function type) with `app_mem'` and the stored type's code being the closure's (`fix_split`'s
   first claim): an obligation of 3 not listed before. A call's value depends on the callee and the
   argument values only (`RunLemmas.callOf_val`), so the record can be keyed by small readings.
   The canonical field type of an accepted declaration: an interpreter over the first-order
   fragment `Check.firstOrderTerm` admits (a parameter: its value as a type; `M(ā)`: `FTy.data M`
   at `M`'s canonical record at the arguments' meanings, the declaration's own occurrences through
   the record function the knot passes; anything else, an equation, a type-function call, `Nat`,
   `Unit`: the run's result as a `FTy.ty`, an equation keyed by its sides' small readings). Its
   agreement with the run wherever the run is defined: BELIEVED TRUE given 1–2 and the unfolding
   of `.tind`/`.place`/`.eq`; the equation case needs "members of one type with equal small
   readings are equal" at the earlier fields (the data layer's argument, `../HANDOFF.md`).
4. Guardedness of that field type from the checker's nesting rule as D107 states it (the greatest
   fixed point of nestable parameters, `Positivity.lean`): the bridge from the checker to the knot.
   For DATA-sorted declarations, BELIEVED TRUE (the knot's records enter only through `M(ā)` chains
   at nestable parameters, read by continuation, `recK_agree`); the hard declarations are instances
   (`Proto/Hard.lean`). FALSE for a `Prop`-sorted declaration nested at a `Prop` parameter
   (exists2, 2026-11-21; `PropNestCE.not_guarded`, kernel-checked): `Q : Prop := MkQ(h : And(Q,
   True))` is accepted, and `And`'s record at `Q`'s proposition keeps that proposition as a leaf,
   which reads `Q`'s record at every depth. Such declarations go through 5, not the knot.
5. `Prop`-sorted declarations, ALL of them, truth-first: the truth predicate as the least predicate
   closed under the constructors (impredicative), then records whose own occurrences are leaves
   `prop T` (no self-reference, no knot), then `Nonempty car ↔ T` (`Proto/PropSorted.ev_mem_iff`
   for `Ev`). That `T` is a fixed point needs the one-step operator monotone, which at a nesting
   like `Q`'s is the monotonicity of each EARLIER declaration's membership in its nestable `Prop`
   parameters: its own induction over the declarations, not covered by `Ev` (which nests nowhere).
   BELIEVED TRUE, larger than first thought.
6. The records' parameter clauses (`RecordsFaithful`). AS FIRST STATED, FALSE for every model at
   any non-empty `Γ` (`RecordsCE.recordsFaithful_false`, at 1765a998): `types` forced a leaf over a
   `Prop`-sorted declaration's raw data code at `paramKey 0`, and `leafOk` read `paramKey 0` as a
   field key. Repaired by the rulings (M-a) (that raw code has no level, so it is in no universe) and
   (S) (`RecLeafOk` at genuine field keys; `types` at type parameters of a full-length list).
   Restated, BELIEVED TRUE: `types` by continuation (the canonical record's
   `paramKey`/`paramContStep` are the parameter's kind and record), `values` (`.small`), `smallOnly`
   (`Proto/ValueParams.recK_small` generically, given field types that read value parameters only
   small), `leafOk` (a canonical record stores a data code at the model's carrier as `.data`:
   `FTy.kind` through `dataView`).
7. Parameter types (`ParamsFaithful`): `paramTy d j ps` := the run's reading of the parameter type
   at `ps`, by program order; no knot (a parameter type cannot mention its declaration). BELIEVED
   TRUE given 1–2.
8. The machine fact the lead routed to the machine-only lane: a declaration's field-type decisions
   do not change when Σ grows past it (`DataFaithful` asks every state extending the prefix).
9. Assembly: `exists_dataModel` from 1–8, by induction on the items (`covers := True`).

What consumers additionally ask (checked 2026-11-21, exists2): `ReadCoherent` and `MemReads` are gone
(the typed read, docs/31 D99); `FieldLevelsFaithful` is stated in `Faithful.lean` and asked by no
consumer yet (BELIEVED TRUE: a proof field's canonical type is a proposition leaf, any other field's a
data or non-proposition leaf; needs `fieldProof` to agree with the checker's `fieldTermIsProp`).
-/

namespace Ochr.Meaning.DataModel.Exists.Decomposition

open Ochr Ochr.Meaning

/-- Two data models agree on a context's declarations: the same records and parameter types there. -/
def AgreeDM (K : RunCtx) (dm' : DataModel) : Prop :=
  ∀ d ∈ K.Γ, dm'.recOf d = K.dm.recOf d ∧ dm'.paramTy d = K.dm.paramTy d

/-- **(1) The data-model congruence.** BELIEVED TRUE, mechanical (see the module docstring). -/
theorem runT_congrDM (K : RunCtx) (dm' : DataModel) (h : AgreeDM K dm') (ρ : Assignment) (φ : Future) :
    ∀ (tl : Bool) (hint : TyS) (t : Term) (s : SState),
      runT K ρ φ tl hint t s = runT { K with dm := dm' } ρ φ tl hint t s := by
  sorry

end Ochr.Meaning.DataModel.Exists.Decomposition
