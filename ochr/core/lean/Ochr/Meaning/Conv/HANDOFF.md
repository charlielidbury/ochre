# The soundness of conversion (N3): handoff (conv1, 2026-11-28)

Branch `spine-conv1` (worktree `../ochre-conv1`, from `origin/spine` 73f1a1075). Build `cd ochr/core/lean && taskset -c 0-14 lake build OchrMeaning` (the `Conv` files are imported by `Ochr/Meaning.lean`). Report: `scratchpad/reports/conv1.md`; docs/31 D280, D281.

## Files (read in this order)

| File | What | Status |
|---|---|---|
| `Rules.lean` | the relations: conversion (`ConvV`/`ConvH`/`ConvL`/`ConvT`/`ConvTL`) and `Eq` (`EqTo`/`EqL`), one constructor per paper rule; `Premises` (the function rules' and [Eq-inj]'s computations left abstract) | the trial's `Rules/Conv.lean`, ported unchanged (today's `conv`/`convT` have the same cases) |
| `Statement.lean` | the claim `Alike` (consumer form: `NoProp` + `Fit` at one hint and type ⇒ equal meanings), `AlikeL`, `NamesKept` (D103), `machPremisesR`, `machPremises` | definitions |
| `Hyps.lean` | the named hypotheses, classed and documented: `PremFn`, `PremPi`, `UnitOk`, `CodeOk`, `LibOk`, `FieldTysSound`, `FieldTyIdx`, `SideOkV`; `isCode`, `Closed` | definitions |
| `Refine.lean` | **B for `conv`**: `conv_refine` (derivation + `NamesKept`), `conv_namesKept` | PROVED, assumes nothing |
| `RefineEq.lean` | **B for `mkEqM`**: `mkEqM_refine` (derivation + `Reach`); `FieldTysKept` | PROVED from `FieldTysKept` (checker; read true; pinned in `Attack.lean`'s `ConvGrowAt`) |
| `Sound.lean` | **A for plain values** (no code, no constructor value): `Plain`, `Plain.beq_eq`, the congruences (`alike_succ`, `_tRef`, `_borrow`, `_gloan`, `_tEq`, `_tInd`, `meanParams_alike`), `convV_alike_plain` | PROVED from `PremFn`, `UnitOk` |
| `SoundEq.lean` | **A for `Eq` on plain sides**: `eqTo_plain` (every rule) | PROVED from `PremFn`, `UnitOk`, `LibOk` |
| `Compose.lean` | `conv_sound_plain`, `mkEqM_sound_plain`; with the unit laws and `True`/`False` discharged: `conv_sound_plain'` (assumes `PremFn`, `LibDecls`, `LibAnd`), `mkEqM_sound_plain'` (+ `FieldTysKept`) | composed |
| `FieldIdx.lean` | `fieldTyIdx` | PROVED, nothing assumed (`DataLib.uShape_idx`) |
| `Lib.lean` | `lib_true`, `lib_false` (`LibOk`'s two fields) | PROVED given the `Prelude`'s shapes |
| `Unit.lean` | `unitOk_plain` (the unit laws on plain values), `plain_hint` | PROVED from `LibOk`, `AndParams` |
| `Attack.lean`, `Probe.lean` | attacks on the real checker, verdicts and reasons asserted | built |

## What is open, in the order to take it

1. **Constructor values** (the rest of "values without code"; [Eq-inj]). The congruence of two convertible constructor values `C(fs)`, `C(gs)` both fitting `T`: the meanings are `ctorR d r c (meanFields d r c 0 [] ·)` with `d` the program's declaration by name and `r` pinned to `T`'s record by membership (`ReadMember.mem_dat_inv`); each field is read at hint `fieldTyR d r c i e` and, as a member's field, fits `T`'s declaration's shape at `r` (`DataLib.mem_iff`, `FitsM`), so it is a member of `shapeReadTy` of that shape (`DataModel.fits_readTy`) unless the shape is a junk leaf. Three obstacles, each a premise the claim must carry, found while porting the trial's `alike_ind`:
   - (a) **junk leaves** (finding H9): `shapeReadTy` is `none` at a leaf holding a data code over the model's own carrier, and `hwt_of_fit` asks nothing there; canonical records have none (`CtxFaithful`'s `RecordsFaithful.leafOk`, for the program's declarations at typed parameters). So the value must record typed parameters (a checker invariant, like `NoProp`; D105, T-Ctor) and the record is then canonical;
   - (b) **the declaration in `T`'s code** (`T.dataCode? = (d', r)`) need not be the program's `d` of that name (`mem_dat_inv` gives `d'.name = t` only); membership reads `d'` only through its constructors' number and arities and `d'.indexFields` (`DataLib.mem_iff`, `uShape`), so agreement of those with `d`'s suffices, true when `T` is the meaning of a checker type (`.tInd` finds `d` by name), not for an arbitrary code (an unknown type's assignment);
   - (c) the types at which an `Eq`'s sides and an inductive type's arguments are compared (`capTy A`, `paramTy`) must satisfy (b) when those parts are constructor values: true at reached states (a constructor value converts only to its own `D(ps)`), so a class condition on values (`.tEq A a b` with a constructor-valued side has `A` an inductive type) carries it.
   Plan: claim `Alike` with the extra premises "constructor values record typed parameters" (value, hereditary) and a class `FO'` with (c); the `.ind` congruence uses (a) via `CtxFaithful.leafOk` and (b) via `T` from (c); then [Eq-inj] (`fields_alike` of the trial's `SoundEq`, with `FieldTysSound`).
2. (DONE: `Unit.unitOk_plain`.)
3. **`LibOk.and`**: `prop (Nonempty car)` at `And`'s record equals `prop (p ∧ q)`: the record's field shapes at the parameters are the parameters' leaves (`RecordsFaithful.types`; for `dmPre`, `twoK`).
4. **`FieldTysKept`** (checker): `fieldTele` pushes and pops a frame around `evalType`s (statements, restored by `restoreKeep`). Pinned by guard; a proof is a machine-lane item (the `quiet_*` lemmas of `Steps/Machine/StepInv.lean` are the pattern).
5. **The function rules** (`PremFn`, `PremPi`): reductions to (II) at the generic state; state them as such once `EvalAt` is usable at `convFnRun`'s and `convPi`'s fresh frames.
6. **Code** (`CodeOk`): the trial's step 7 (a run congruence for two [Close]-shaped texts differing by convertible embedded values; `RunSubst`'s induction with a third base case).

## Traps

- `lake env lean` scratch files have `autoImplicit` on; build the module. `Ochr.Env.values` is in `Meaning/WF.lean`.
- `rename_i` after `cases pa <;> cases pb` grabbed proof names, not values: name cases explicitly (`disj_plain_absurd`).
- `meanV`'s `.tEq` clause: `rw [meanV_tEq']` rewrites only the first occurrence; the `SideOk` it produces is at `(meanV err A).asTy`, which is `capTy A` only by unfolding (`replace sa : SideOk _ (capTy …) _ := sa`).
- `simp only [meanV, hd]` on `.tInd` leaves `if paramsOk … (meanParams …)`; rewrite with `if_pos` before rewriting `meanParams` (the decidability instance blocks `rw` inside the condition).
- Conv's wrapper (D103): `rw [Ochr.conv.eq_1]`, `Runs.bind_inv (runs_get_bind.mp h)`, `Runs.onFail_inv`, then `runs_restoreNames_pure` (in `Refine.lean`); the inner block is matched literally by `conv_inner`'s hypothesis.

# conv2's section (2026-11-28; branch `spine-conv2`, worktree `../ochre-conv2`)

Report: `scratchpad/reports/conv2.md`; docs/31 D282.

## Files added

| File | What | Status |
|---|---|---|
| `Ctor.lean` | `FO` (values that hold no code: plain and constructor values); `alike_ind` ([Conv-cong] at constructor values); `FO.beq_alike` (`==` ignores recorded parameters, so it is likeness, not equality); `unitOk_fo`; `convV_alike_fo` (N3 for `FO` values) | PROVED; `alike_ind` assumes NOTHING; `convV_alike_fo` from `PremFn`, `UnitOk FO` |
| `CtorEq.lean` | `FieldTysOk` (conv1's `FieldTysSound` restated at typed parameters/fields, with a level), `IndAt`, `InjAtInd`, `LeafsOk`; `disj_fo_absurd` ([Eq-disj] at constructor values); `eqTo_fo`/`eqL_fo` (every `Eq` rule on `FO` sides, [Eq-inj] with D64) | PROVED from the named facts |
| `ComposeFO.lean` | `conv_sound_fo'` (3 facts, as for plain values), `mkEqM_sound_fo` (7 facts; `LeafsOk` and the declarations' prefix discharged from `CtxS`) | composed |
| `FieldLen.lean` | `machPremises_len`: `FieldTysOk`'s length half for the machine | PROVED, assumes nothing |
| `AttackCtor.lean` | blocks `ConvAtkTy` (constructor values at a type unknown), `ConvAtkCtor`, `ConvAtkMoved` (partly moved owners in `Id`), `ConvAtkCode` (code inside compared values; D64 at index fields only convertible) | verdicts and reasons asserted |

## Settled
- Premise (b) (a type code's declaration vs the program's): the simulation's statement does NOT change (D282). [Conv-cong] needs neither of conv1's premises; [Eq-inj] needs them only at `mkEqM`'s fallback to the values' recorded parameters, dead on the suite (probe: fallback → error, every verdict unchanged). PROPOSAL for main, BUILT on branch `conv2-eqargs` (D283; worktree `../ochre-conv2-probe`): the fallback deleted, every verdict unchanged, `OchrMeaning` green with `IndAt`/`InjAtInd` gone. If main lands it, take `conv2-eqargs`'s `Rules.lean`, `CtorEq.lean`, `ComposeFO.lean` diffs onto `spine`.

## Open, in the order to take it
1. **The `Id` step's partly moved sides** (report, "for the theory" 5): decide (i) widen the strict `Eq`'s side condition to open members, or (ii) prove `mkEqM`'s deterministic choice never leaves a partly moved side stuck. Then extend `eqTo_fo` (the congruence for partly moved trees is `alike_ind`'s proof with `OMem` fields, non-dependent constructors only).
2. **`IndAt` at the consumers** (the `.eq` step, `Id`'s conjuncts, `substV`'s re-made `Eq`s, `J`, `symm`, `trans`): a constructor-valued side's type is its inductive applied (typing); or land the fallback's deletion and drop `IndAt`/`InjAtInd`.
3. **`FieldTysSoundT`** (the meaning half of `FieldTysOk`; the length half is PROVED, `FieldLen`): (II) for `fieldTele`'s typed runs + `FieldsFaithful`.
4. **`CodeOk`**: a run congruence for texts that differ by alike embedded values with alike types (and up to embedded constructor values' recorded parameters).
5. **`PremFn`**: the reduction of the report's task 5 (`CallFnGW` at `typed = false` from the generic state, the closure call step, `PremPi`'s transfer, the end-all step).

## Traps (added)
- `meanFields` and `meanV` unfold by `show` with the explicit next-step form (no equation lemmas needed); `FitsM`'s successor case destructures with `obtain ⟨f, fs', hfs, h1, h2⟩` directly.
- A recursive call inside a mutual theorem whose section variables are implicit takes NO named section arguments (`FO.hint (v := a) p`, not `(K := K)`).
- Structural recursion over `EqTo`/`EqL` works for a mutual pair; a THIRD theorem in the block that receives a sub-derivation and passes it on unchanged breaks it (inline it instead).
- `SideOkV` is a `def`: `generalize` does not see the `meanV` inside it; give the side as `.inr (show meanV … ∈ₛ … by rw …)`.
- `uShape`'s match on an `Entry` constructor needs `dsimp only` before `rw [if_pos …]`.
