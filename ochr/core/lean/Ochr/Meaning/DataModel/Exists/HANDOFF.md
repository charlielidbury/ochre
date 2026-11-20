# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists`, worktree `/home/charlielidbury/repos/ochre-exists`. Design note: `ochr/docs/34-data-model-existence.md` (§1–17 are the layer before this lane; the port below is "§18" in docstrings, not yet written into the note). This file is enough to continue the existence proof alone; deleted when the lane's work is merged. Last updated 2026-11-20 after the port (part 1 4c749d49, part 2 928da269).

## What this lane found (all reported; the lead decided)

- **The checker accepted closed proofs of `False`** through a positivity hole (self occurrences were exempt from the nesting condition): `ConsistencyCE.lean` (Curry), `Positivity.lean` (`Chain`, `TyFn`, `PropRoute`, and the D107 agent's independent `SecondHole`), all `#guard`ed natively, flipping to rejected when D107 lands. `Positivity.lean`'s docstring is the condition the existence proof needs (semantic, and the greatest-fixed-point syntactic rule D107 implements) and the must-stay battery.
- **The old existence statement was false for every model** at `Box (A : Type) := MkBox(x : A)` three ways (junk type parameter; parameter list too short; the frame's readings): kernel-checked at 8b5f60f2 (`StatementCE.lean`, removed at the port because it targets the old definitions; read it in that commit). Repaired at the port (below).
- **Decisions taken**: a leaf's type is its code (2a), the parameter list has the declaration's length (2b), the frame binds as `fieldTele` (2c), faithfulness is conditional on the run being defined (2d; the consumers get definedness from simulating the checker's `evalType`; shared owed caveat: the checker's frame sits on the current state, faithfulness speaks of a one-frame state, a special case of the open frame property), records as path functions with a universal signature (the port). The `Eq` relaxation (an equation's type as a nestable position) is optional for D107.

## The ported layer (what a successor builds on)

- `Sem`: `Entry := none | leaf B c | data d | small s` (no record inside an entry).
- `DataLib/Universal.lean`: keys (`kindKey c i es`, `contStep`, `paramKey`, `paramContStep`), `contRec`, `projIdx` (earlier fields projected to index fields), `uShape`/`uSig` (one signature for every model), `uShape_idx` (`FieldTyIdx` at every record), `uShape_data`, `uShape_leaf`.
- `Data.lean`: `DataModel := {covers, recOf, paramTy}`; `dm.sig := uSig` (a definition); `shapeTy` (leaf = its code); `paramTyOf r j` (a parameter's type by continuation); `LeafOk`, `RecLeafOk` (no leaf holding a data code over the model's own carrier); `fitsOneM_mem` asks `LeafOk`.
- `Run.lean`: only `unifyArgsTyS`'s last clause changed (reads `paramTyOf`).
- `DataModel/Faithful.lean`: `teleFrame dm D d ps c e` (fields at `prop`/`other` by `fieldProof D` = the decisions' reading of a field place, parameters at `paramDecls`), `FieldsFaithful`/`ParamsFaithful` conditional and length-fixed, `RecordsFaithful` (`types` by `paramTyOf`, `values`, `smallOnly`, new `leafOk`), `CtxFaithful K` (same signature as before, so `Steps/` and `Consistency.lean` were not edited).
- `DataModel/CtorMem.lean`: `ctorOut_mem` etc. take `RecLeafOk`. `ReadMember.lean`: `ShapeCanon dm` (leaf clause = not the model's own data code), `TyIn dm` (only data codes with a constructor member).
- `DataModel/Canonical/Layout.lean`: `ucar`, `uTyR` (`tyR_eq_uTyR`: every model's), `shapeTyP` (`shapeTy_eq_shapeTyP`), `dataView` (a type that is a data code at the model's carrier), `FTy` (a field type as the construction reads it) with `kind`/`cont`/`mean`, and `shapeTyP_uShape` (a record holding a field type's kind and continuation means it).
- `DataModel/Canonical/Knot.lean`: `KnotSpec` (field types as functions of the declaration's own record function, guarded), `approx`, `recK`, `approx_stab`, `recK_kind`/`recK_cont`/`recK_param`/`recK_paramCont`/`recK_contRec` (the fixed point), `recK_agree` (parametric in nestable parameters), `recK_shape` (faithful at a field), helpers (`parTy`, `pEntryTy`, agreement lemmas).
- `Exists/Proto/`: instances. `Hard.lean` (`List`, `Box`, `Duo`, `Rose`, `DD`, `RN`, `BB`, `NN`, `RP`, `HN`), `Examples.lean` (memberships `rose_example`, `dd_example`; shape-reading idioms), `PropSorted.lean` (`Ev` by its truth predicate: `ev_mem_iff`, `ev_tyR`), `ValueParams.lean` (`G1`/`T1`: `recK_small`, `t1_g_faithful`).
- Hand models (`DataModel/Program.lean` etc.) are records of paths now; results whose statements changed are listed in 928da269's message.

## The decomposition

`Exists/Decomposition.lean`: the nine pieces with the author's belief in each (all believed true); `runT_congrDM` (piece 1, the data-model congruence) is stated there with `sorry`. Order: 1 (mechanical, `AssignCongr.lean` is the template), 2 (Γ narrowed to reachable names; needs a `Term.declNames`), 3 (the canonical field-type interpreter over `Check.firstOrderTerm`'s fragment, and its agreement with the run), 4 (guardedness from D107's rule: the bridge from the checker to the knot), 5 (`Prop`-sorted truth predicates, generally), 6 (record clauses), 7 (parameter types), 8 (machine fact, the machine-only lane's), 9 (assembly by induction on the items). Riskiest: 3 (the interpreter must agree with the run on every first-order field type, including a type function returning data, whose result's record is then a continuation, and equations keyed by small readings) and 4 (stating guardedness against D107's exact rule once it lands; check its relaxations against `recK_agree`).

## Idioms and traps of the new layout

- A record for a hand model: a path-recursive function, keys PROJECTED (`projIdx`: non-index earlier fields read `.other`), continuation steps end their small list in `.proof` (`contStep`), parameters at `(j, 0, [.other])` and `(j, 0, [.other, .other]) :: q`. Or `Canonical.recK` with a `KnotSpec`.
- A shape at a canonical record: `uShape_data`/`uShape_leaf` with `recK_kind`, `recK_contRec`, then `kind_nondata` (a non-data code is a leaf), `kind_data`/`cont_data` (a data code at the model's carrier is `.data` with its record) (`Proto/Examples.lean`).
- `dataView` is classical: prove `dataView T = none` for a concrete non-data code by `dataView_nondata`, and `= some (d, r)` for `uTyR d r` by `dataView_uTyR`.
- Two records equal only extensionally (a mutual pair of path functions against a record built through `recK`): prove by `funext` and induction on the path (`Program.forestR_eq`).
- `Sem.whole (.ty T)`: `unfold Sem.whole; exact trivial`. `Sem.updAt … [] v = some (f v)` is `rfl` (its equation lemmas fail to generate).
- Checker decisions: `chainDecisions` is classical (fuel-free); facts about specific decisions need `FuelAgree` (`DecisionsFF.lean`), no longer `rfl`.
- A `#guard` on the checker is native; the kernel cannot run `checkInd`/`checkProgram`.
- Doc comments cannot precede an `ochr` block (use `--`). No Mathlib: no `Set`, no `List.Forall₂`.

## Status

Port green (`lake build OchrMeaning`), core lemmas on the standard axioms. Next: the decomposition's pieces in order, starting with `runT_congrDM`. Item 3 of the lane's brief (`FieldLevelsFaithful`, `ReadCoherent`) after the main line. The design note's §18 (how existence is proved) is owed at the end.
