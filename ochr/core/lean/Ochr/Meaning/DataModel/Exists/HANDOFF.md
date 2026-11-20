# Existence of the data model: handoff (working file)

Lane: prove `Assembly.exists_dataModel` (`Meaning/Consistency.lean`). Branch `spine-exists`, worktree `/home/charlielidbury/repos/ochre-exists`. Design note: `ochr/docs/34-data-model-existence.md`; the data layer's own note: `../HANDOFF.md`. Started 2026-11-20. Kept current at each milestone; deleted when the lane's work is merged.

## Files (none imported by `Ochr/Meaning.lean`; build each by name)

- `ConsistencyCE.lean`: **the checker accepts a closed proof of `False`** (`Boom`), natively checked (`#guard accepts …`). A positivity hole: a self occurrence `Q(Q(A, b), B1)` nests `Q` at `Q`'s own parameter `A`, which `Q` passes to a type function `FB(A, b)` that is a Π-type only at `b := B1` (stuck at the generic `b`). `nestViolation`/`firstOrderArgs` skip the nesting condition when `m == n`. Curry's paradox follows; `Delta(ι(Delta))` diverges (undecided), but `Lem(Delta)` is a proof the checker never runs. No set model of `Q` exists, so no data model is faithful to it.
- `StatementCE.lean`: kernel-checked (standard axioms) counterexamples to `FieldsFaithful` at `Box (A : Type) := MkBox(x : A)` for EVERY data model, and the lift to `exists_dataModel` at the program `[Box]` (acceptance of `Box` a hypothesis, `#guard`ed natively):
  1. `fieldsFaithful_false_junk`: a type parameter that is a junk code (`.data d r X`, `X` not the model's carrier; `Type₀`'s carrier holds it) runs to itself, and `shapeTy` never gives a data code with a foreign carrier (`shapeTy_ne_junk`, Cantor).
  2. `fieldsFaithful_false_short`: `ParamsTyped` does not fix the length; at `ps = []` the field type reads the field `⊥`, the run is undefined.
  3. `fieldsFaithful_false_frame` (`run_dl_undefined`): `teleFrame` binds parameters at `other` (move), the checker's `fieldTele` at their declared readings (a type parameter copies), so `DL (A : Type) := MkDL(e : Eq(Nat, (let x = A; let y = A; 0), 0))` (accepted) has no run in `teleFrame`.
- `Probes.lean`: checker verdicts asserted by the build: `DMXFrame` (counterexample 3's programs), `DMXShapes` (the shapes a construction must cover: `DD(DD(A))`, non-uniform nesting `RN`, `BB`, nesting through two declarations `RP`, `NN`, recursive `Prop` field `Ev`, a type function returning data `TF`).

## Traps

- `Sem.whole (.ty T)` does not close by `simp [Sem.whole]` or `trivial` (well-founded definition): `unfold Sem.whole; exact trivial` (`whole_ty`).
- `Sem.updAt`'s equation lemmas fail to generate; `Sem.updAt dm Γ T f [] v = some (f v)` is `rfl` (`updAt_nil`).
- Checker decisions at fixed fuel reduce by `rfl` at an arbitrary state (`checker_flags`, `checker_dl`); the checker's runs (`checkInd`, `checkProgram`) do not reduce in the kernel (`decide +kernel` gets stuck): assert them natively with `#guard`.
- A `let` binding a structure literal across lines inside a tactic block mis-parses; write it as an anonymous constructor on one line.
- A `generalize` of the program meaning (`progMeaning … = P`) avoids max-recursion in unification.

## Status and next steps

Reported to the lead (2026-11-20): the consistency counterexample, the three statement defects with repairs, and the record-layout design question. Waiting on: the checker fix for positivity; the restatement of faithfulness (conditional form, length, `teleFrame`'s readings); `shapeTy` of a data-coded leaf; the record layout (records as path functions, no record inside an entry).
