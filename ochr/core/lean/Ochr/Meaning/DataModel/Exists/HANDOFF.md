# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists`, worktree `/home/charlielidbury/repos/ochre-exists`. Design note: `ochr/docs/34-data-model-existence.md`; the data layer's own note: `../HANDOFF.md`. Started 2026-11-20. Kept current at each milestone; deleted when the lane's work is merged.

## Files (none imported by `Ochr/Meaning.lean`; build each by name)

- `ConsistencyCE.lean`: **the checker accepts a closed proof of `False`** (`Boom`), natively checked (`#guard accepts …`). A positivity hole: a self occurrence `Q(Q(A, b), B1)` nests `Q` at `Q`'s own parameter `A`, which `Q` passes to a type function `FB(A, b)` that is a Π-type only at `b := B1` (stuck at the generic `b`). `nestViolation`/`firstOrderArgs` skip the nesting condition when `m == n`. Curry's paradox follows; `Delta(ι(Delta))` diverges (undecided), but `Lem(Delta)` is a proof the checker never runs. No set model of `Q` exists, so no data model is faithful to it.
- `StatementCE.lean`: kernel-checked (standard axioms) counterexamples to `FieldsFaithful` at `Box (A : Type) := MkBox(x : A)` for EVERY data model, and the lift to `exists_dataModel` at the program `[Box]` (acceptance of `Box` a hypothesis, `#guard`ed natively):
  1. `fieldsFaithful_false_junk`: a type parameter that is a junk code (`.data d r X`, `X` not the model's carrier; `Type₀`'s carrier holds it) runs to itself, and `shapeTy` never gives a data code with a foreign carrier (`shapeTy_ne_junk`, Cantor).
  2. `fieldsFaithful_false_short`: `ParamsTyped` does not fix the length; at `ps = []` the field type reads the field `⊥`, the run is undefined.
  3. `fieldsFaithful_false_frame` (`run_dl_undefined`): `teleFrame` binds parameters at `other` (move), the checker's `fieldTele` at their declared readings (a type parameter copies), so `DL (A : Type) := MkDL(e : Eq(Nat, (let x = A; let y = A; 0), 0))` (accepted) has no run in `teleFrame`.
- `Positivity.lean`: D107's input (the condition the existence proof needs of an accepted declaration, semantic and syntactic, in its docstring) and the battery: three more accepted proofs of `False` through the same hole (`Chain`, `TyFn`, `PropRoute`), the declarations that must stay accepted (`MustStay`), and controls (`Controls`). All verdicts `#guard`ed; the four paradox blocks flip to rejected when D107 lands.
- `Proto/` (the prototype of the record layout, task 3 of the lead's 2026-11-20 decisions; standard axioms, no `sorry`):
  - `Layout.lean`: keys (`kindKey`, `contStep`, `paramKey`, `paramContStep`), the universal signature `uShape`/`uSig` (reads the record alone; projects to index fields: `uShape_idx` is `FieldTyIdx`), `ucar`, `uTyR`, `shapeTyP` (2a), `FTy` (a field type as the construction reads it: a declaration at a record, or a type) with `kind`/`cont`, and `shapeTyP_uShape` (a record holding a field type's kind and continuation means it).
  - `Knot.lean`: the generic knot (`KnotSpec`, `approx`, `recK`), stabilization (`approx_stab`), the fixed point (`recK_kind`, `recK_cont`, `recK_param`, `recK_paramCont`), parametricity (`recK_agree`), faithfulness at a field (`recK_shape`); helpers (`parTy`, `pEntryTy`, agreement lemmas).
  - `Hard.lean`: `List`, `Box`, `Duo`, `Rose`, `DD`, `RN`, `BB`, `NN`, `RP`, `HN` as knot instances (guardedness proved for each).
  - `Examples.lean`: shapes read off canonical records, and memberships (`rose_example`: a rose tree with a nested forest; `dd_example`: `DNode(DLeaf) : DD(Nat)`).
  - `PropSorted.lean`: `Prop`-sorted declarations through their truth predicate (impredicative least fixed point), no knot: `Ev`, `ev_mem_iff`, `ev_tyR` (`uTyR Ev (recK evK [n]) = prop (evT [n])`).
  - `ValueParams.lean`: a value parameter whose argument is a value of the declaration being defined (`G1 (A) (a : A) := MkG1(x : A, e : Eq(A, x, a))`, `T1 := Leaf1 | Node1(t : T1, g : G1(T1, t))`): records read value parameters only through small readings (`recK_small`, the generic `smallOnly`), so `T1`'s knot stays guarded and `g`'s type at the actual `t` is the canonical one (`t1_g_faithful`).
  - `Statement.lean`: faithfulness restated (2b length, 2c `fieldTele`'s readings: `teleFrameR`, `paramDecls`; 2d conditional): `FieldsFaithfulR`, `ParamsFaithfulR`, `CtxFaithfulR`.
- `Probes.lean`: checker verdicts asserted by the build: `DMXFrame` (counterexample 3's programs), `DMXShapes` (the shapes a construction must cover: `DD(DD(A))`, non-uniform nesting `RN`, `BB`, nesting through two declarations `RP`, `NN`, recursive `Prop` field `Ev`, a type function returning data `TF`).

## Traps

- `Sem.whole (.ty T)` does not close by `simp [Sem.whole]` or `trivial` (well-founded definition): `unfold Sem.whole; exact trivial` (`whole_ty`).
- `Sem.updAt`'s equation lemmas fail to generate; `Sem.updAt dm Γ T f [] v = some (f v)` is `rfl` (`updAt_nil`).
- Checker decisions at fixed fuel reduce by `rfl` at an arbitrary state (`checker_flags`, `checker_dl`); the checker's runs (`checkInd`, `checkProgram`) do not reduce in the kernel (`decide +kernel` gets stuck): assert them natively with `#guard`.
- A `let` binding a structure literal across lines inside a tactic block mis-parses; write it as an anonymous constructor on one line.
- A `generalize` of the program meaning (`progMeaning … = P`) avoids max-recursion in unification.

## Requirements the construction must meet beyond the statement

- `FieldTyIdx` (`origin/rules-trial`, `Rules/SoundEq.lean`): a field's type reads, of the earlier fields, only the index fields, at EVERY record and every pair of field lists. Not a consequence of faithfulness (the lead, 2026-11-20): make the canonical signature project the earlier fields' small readings to `d.indexFields c` before reading the record, so it holds by construction.
- `FieldLevelsFaithful`, `ReadCoherent` (`Faithful.lean`, `ReadMember.lean`): item 3, after the main line. `ReadCoherent.canon` must admit a leaf whose code is a data code with a foreign carrier (counterexample 1).
- The data layer's argument for "a member is determined by its small reading and its type" is in `../HANDOFF.md` (last section); it says to define the canonical record through small readings (e.g. an equation as `propEntry (va.small = vb.small)`), agreeing with the run only at typed parameters.
- `LibOkT`, `UnitOk`: not this lane's (argued from faithfulness in `../HANDOFF.md`).

## Decisions (the lead, 2026-11-20)

Positivity fix: D107 (checker lane, `positivity1`), input in `Positivity.lean`. 2a–2c: yes. 2d: yes in principle, after the consumers' list. Records as path functions: yes in direction, PROTOTYPE FIRST (done, `Proto/`), report before porting. The congruence lemma: go ahead when waiting. This lane now OWNS the data layer's files (`Sem`, `Data`, `DataLib/*`, `DataModel/*`, `Places`, the data clauses of `Run.lean`); statement changes under `Steps/` or in `Consistency.lean`'s chain go through the lead.

## Findings of the prototype

- `Prop`-sorted declarations need their truth predicates first: `D3 (n) : Prop := D3Z | D3S(w : PB2(D3(n)))` with `PB2 (P : Prop) := MkPB2(x : P)` is accepted, and the run's type of `w` is a DATA type whose record holds `D3`'s own proposition as an opaque leaf; a leaf is fixed before the carriers, so it cannot be read off `D3`'s carrier. Defining the predicate impredicatively first (least predicate closed under the constructors) and putting it in the leaves removes the knot for `Prop`-sorted declarations altogether; `prop (Nonempty car) = prop predicate` by `propext` (`ev_tyR`). Monotonicity of the one-step operator is what positivity gives.
- The knot needs guardedness at RELATED parameters, not only related records: `DD(DD(A))` passes the declaration's own record inside a parameter.

- Decisions: `exists_dataModel` will name `chainDecisions fuel` (fuel-free, classical; `origin/spine-lead` `DecisionsFF.lean`). Still a function of the state: the canonical record comes from field-type runs under ONE table, while `DataFaithful` asks every state extending the program's Σ, so the construction needs the decisions on a declaration's field-type terms not to change when Σ grows past it (a machine fact, owed). `StatementCE`'s lift used `rfl` on `checkerDecisions` at fixed fuel; under `chainDecisions` those facts need `FuelAgree` for the one decision (historical: the statement is being replaced).

## Status and next steps

Reported the condition and battery (770ba363). Next: report the prototype, the port's change list and the 2d consumers' list; then the port and the congruence lemma.
