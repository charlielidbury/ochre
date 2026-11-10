# 30. `Id` adequacy: what a context can observe (an audit for Target C)

Written on 2026-11-09 by an audit agent dispatched by the lead session. It audits Target C of `docs/18` (`Id` adequacy) against the substitution principle: every way two terms that the checker proves equal by `Id` can still be told apart by the rest of a program, with a probe for each, fixes, and a sharper statement of Target C. No checker code was changed. The fixes were measured on scratch copies of the checker that are not part of the repo.

**Bases.**
- Main at `7568feb3`. The checker is unchanged through `ea899cf3`; only docs and `Ochr/Model/Safety.lean` moved.
- D84: a snapshot of the uncommitted working tree of `../ochre-d84` taken at 16:24 on 2026-11-09, meaning branch `d84` at `127dc1aa` plus a 1,685-line diff (sha256 `f3fa7b259e47…`). It builds green: 109 jobs, every suite verdict as expected. D84 may have moved on since.

**Probes.** Each probe is an `ochr` block with:
- the `Id` lemma;
- a distinguishing context, either as a pair of programs (one accepted, one rejected) or as two accepted closed programs that compute different values;
- a flipped copy of the lemma (`reject def Flip…`), whose "expected rejection, but accepted" proves the lemma is accepted.

They live in the session scratchpad (`…/scratchpad/idaudit/P01_Moves.lean` … `P09_StuckRePoint.lean`), which is not durable, so the text that matters is reproduced below. Run them with `lake env lean <probe>` from `ochr/core/lean` after `lake build Ochr.Examples.Nat Ochr.Examples.Fixtures`.

## Summary

1. **No closed proof of `False` was found.** In every gap, `Id`'s meaning is computed soundly, and what fails is substitution. Two consistency checks behave fail-safe: a stuck match that re-points a borrow (P09), and a lemma instantiated at a call site where its arguments alias (P06).
2. **As drafted, Target C is false for the suite's central idiom, the paper's first lemma included.** The draft observes errors, and quantifies over every accepted position holding `t`. The counterexample:
   - `symm(AddMZero(x)) : Id(Unit, (), AddM(x, 0))` is accepted;
   - the position `(); *x := 5` is accepted;
   - replacing `()` there by `AddM(x, 0)` gives a program that writes through a borrow it has moved (P05).
   The channel is a borrow variable that one side consumes and the other does not. D84 leaves it open on purpose: its read footprint excludes borrow variables. Closing it inside `Id` flips 81 suite verdicts (variant C below): 28 directly, `AddMZero` first, and 53 more that cite one of them, `Quicksort.QSCorrect` among them. So no change to `Id` makes the draft true without giving up the in-place lemmas: the statement must change.
3. **Recommended: state Target C over contexts where both fillings are accepted.** This is typed contextual equivalence, the standard notion. By Target B neither filling then goes wrong, so errors cannot differ, and every channel that shows only as an error drops out. One gap remains, and it is a value channel: where a borrow binding points after a side re-points it (the lead's `RePoint`, a swap of two borrows, a cursor moved down). The fix is [Obs-ref], the lead's candidate in a precise form: write one fresh abstract value through each borrow binding a side assigns, when it holds a borrow after both sides. It costs no suite verdict (variant B).
4. **Under the recommended statement, Target C does not need D84's read footprint.** Moves of owned places show only as errors. D84 makes `Id` finer than Target C needs: for example `Id(Unit, F(x), F(y))` becomes `False`, although the two are equivalent in typed contexts. That is incompleteness, not unsoundness, so D84's footprint gain should be kept or dropped on D84's own grounds (consistency at the join).
5. **If errors must stay observable (contexts with an unaccepted filling), there is a coherent alternative**, (S) below. It adds a side condition, that the borrow variables a hole mentions whole are not used after it, which also dissolves the re-pointing gap, and three fixes:
   - D84 for owned moves;
   - F3, owners of borrows read through: no suite verdict (variant A);
   - F4, borrows ended inside a side: four suite verdicts (variant D).

## The channels

"Strong" is Target C as drafted in `docs/18`: any accepted position holding `t`, with errors observable. "Typed" is the recommended statement (§ Target C): both fillings accepted. A gap is a pair where `Id` holds but substitution fails. "Error-only" means the difference shows only as an error or a rejection, never as a different value.

| # | Channel | main | D84 | Strong | Typed | Probe |
|---|---|---|---|---|---|---|
| 1 | Result | covered | covered | – | – | suite |
| 2 | Final contents of places written or borrowed, all owners (O4) | covered | covered | – | – | suite |
| 3 | Owned place only read, copied | nothing to observe | same | – | – | – |
| 4 | Owned place only read, moved: a call argument, a field, a closure capture (G1) | **gap** | covered | gap on main | error-only | P01 |
| 5 | Where a live borrow binding points: re-point, swap, cursor (G2) | **gap** | **gap** | gap | **gap** | P02, P08 |
| 6 | A borrow binding consumed by one side: passed whole, moved into a `let` (G3; `AddMZero`) | **gap** | **gap** | gap, unfixable inside `Id` | error-only | P03 (a, b), P05 |
| 7 | A borrow binding ended inside a side: [Drop] of the local it was re-pointed at, [Access] of its lender, a reborrow ended through its parent (G4) | **gap** | **gap** | gap | error-only | P03 (c, d, e) |
| 8 | A borrow left partly moved: moved out through `*y`, not refilled (G5) | **gap** | **gap** | gap | error-only | P04 |
| 9 | A dependent value left open, or with a proof field invalidated | covered (`Id` repacks its owners: an error; suite `Fording.IdLie`) | same | – | – | – |
| 10 | A lemma used where its parameters alias (G6) | not an `Id` gap: a condition on Target C's instances | same | (gap if allowed) | error-only | P06 |
| 11 | Function values, returned or stored, called at any argument | covered ([Conv-fun], frame property) | same | – | – | P07 |
| 12 | Sealed programs and holes: `t` closes off where `u` runs; holes left in fills | covered at closed instances (a sealed program means its program); compared by text when open | same | – | – | P09 |
| 13 | A stuck block that re-points a borrow | fail-safe: the block takes the binding by move, so later uses are rejected | same | – | – | P09 |
| 14 | Statements and private copies; proofs erased; η at `Unit` | not a runtime position (P2); every proof is `⋆`; values at `Unit` are `()` | same | – | – | – |
| 15 | Abstract values, generalisation and η-records | knowledge, with no runtime trace; records surviving a side's copy (D37) is by design and keeps O1 | same | – | – | – |
| 16 | Using a proof of `Id` (`J`, `rewrite`, `cong`, `symm`) | transports only along the observed equations; no rule assumes `Id` is a congruence | same | – | – | – |
| 17 | Extra owners at a call site (O4) | a consistency obligation (footprint coverage), not an adequacy channel | same | – | – | – |

Rows 1–3, 9 and 11–17 are channels that `Id` covers, or that no context can observe. The reason is given in the row; the less obvious ones are argued in § Channels that are covered.

## The gaps

### G1. Moves of owned places (row 4; the lead's gap 1)

```
def F (n : Nat) : Unit := ()
def T (x : Nat) (y : Nat) : Id(Unit, F(x), F(y)) := refl                      -- main: accepted; D84: rejected (False ∧ False)
def TF (p : Nat × Nat) : Id(Unit, (let a = p.0; ()), ()) := refl                -- main: accepted; D84: rejected (stuck)
def TC (m : Nat) : Id(Unit, (let f = (λ(u : Unit) : Nat => clone(m)); ()), ()) := refl   -- main: accepted; D84: rejected (False)
reject def CT (x : Nat) (y : Nat) : Nat := (F(x); x)      def CU (x : Nat) (y : Nat) : Nat := (F(y); x)
```

Each `Id` is accepted on main: a read is not in the footprint. A context that reads the moved place is rejected after one side and accepted after the other (`CT` and `CU`; likewise for `TF` and `TC` in P01). D84 rejects all three: an owned non-proof root that a side reads is in the footprint, and `⊥` against a value is `False`. `TF` stays stuck rather than `False`, because `u`'s copy of `p` was never η-refined. The difference is error-only.

### G2. Where a borrow binding points (row 5; the lead's gap 2)

```
def RePoint (x : Nat) (z : Nat) (y : &Nat) : Id(Unit, (y := &x; ()), (y := &z; ())) := refl
def SwapB (y1 : &Nat) (y2 : &Nat) : Id(Unit, (let t = y1; y1 := y2; y2 := t), ()) := refl
def CursorSite : Nat := (let c = S(Z); let y = &c; let h : Id(Unit, (y := &(*y).0), ()) = refl; *y := 7; clone(c))
```

All three are accepted on main and on D84 (P02). The swap is the cleanest witness, because it ends no borrow and moves no loan: it only permutes which binding holds which borrow. The distinguishing contexts are accepted with both fillings, and they compute different values:

```
def SwapCT : Id(Nat, (let a = 0; let b = 0; let y1 = &a; let y2 = &b; (let t = y1; y1 := y2; y2 := t); *y1 := 7; clone(a)), 0) := refl
def SwapCU : Id(Nat, (let a = 0; let b = 0; let y1 = &a; let y2 = &b; (); *y1 := 7; clone(a)), 7) := refl
def SwapDiffer (h : Id(Nat, ⟨SwapCT's left side⟩, ⟨SwapCU's left side⟩)) : False := h      -- accepted
def CursorCT : Id(Nat, (let c = S(Z); let y = &c; (y := &(*y).0); *y := 7; clone(c)), S(7)) := refl
def CursorCU : Id(Nat, (let c = S(Z); let y = &c; (); *y := 7; clone(c)), 7) := refl
def RePointCtx (x z : Nat) (y : &Nat) (h : Id(Nat, ((y := &x; ()); *y := 7; clone(x)), ((y := &z; ()); *y := 7; clone(x))))
  : Eq(Nat, 7, x) ∧ (Eq(Nat, 7, x) ∧ Eq(Nat, z, 7)) := h                        -- accepted: the checker computes the fillings apart
```

The re-pointing also shows as an error. With `RePointRetCT (y : &Nat) : &Nat := (let x = 0; (y := &x; ()); y)`, returning `y` while the local it points at dies is rejected, and the `()` filling is accepted. This is the only value channel found, so it is the only gap under the recommended statement. Observation principle O2 ("where a borrow sits does not matter") is false for a borrow binding that the continuation can still use.

### G3. A borrow binding consumed by one side (row 6)

```
def G (y : &Nat) : Unit := ()
def MoveB (y : &Nat) : Id(Unit, G(y), ()) := refl                  reject def MoveBCT (y : &Nat) : Unit := (G(y); *y := 5)
def MoveL (y : &Nat) : Id(Unit, (let z = y; ()), ()) := refl       reject def MoveLCT (y : &Nat) : Unit := ((let z = y; ()); *y := 5)
def AddMZeroSym (x : &Nat) : Id(Unit, (), AddM(x, 0)) := symm(AddMZero(x))
def AddMZeroCU (x : &Nat) : Unit := ((); *x := 5)                  reject def AddMZeroCT (x : &Nat) : Unit := (AddM(x, 0); *x := 5)
reject def RunT : Id(Nat, (let c = 3; let x = &c; AddM(x, 0); *x := 5; clone(c)), 5) := refl      -- RunU, with (), is accepted
```

All are accepted on main and on D84. The footprint observes the owners of a borrow variable passed whole, which is the right thing for its target's contents, but not the variable's own fate. D84's read clause skips borrow variables (`!isRefTy && !b.val.isBorrow`). Closing this channel inside `Id` is not viable. Variant C observes it: every borrow binding of the frame that holds a borrow when `Id` is formed must hold one after both sides or after neither, and otherwise the `Id` is `False`. It flips 81 suite verdicts. 28 flip directly:
- 24 are lemmas whose one side passes the borrow whole and whose other side does not: `Nats.AddMZero`, `AddMS`, `AddSubId`, `AddSubIdReborrow`, `TwiceMZero`, `AppendMNil` (twice), `InsertMEq`, `InsertMIsInsert`, `Array.GetMutSet`, `GetMutRead`, `ArrayBench.B1Join`, `ReturnedBorrows.TailNoop`, and the four `Equality.IdIsConj` statements, among others;
- the other four are G4's in-body kills (below).

The other 53 cite a flipped lemma: `AddZero`, `AppendNil`, the dependent-field vector lemmas, and Quicksort's permutation and sortedness proofs up to `QSCorrect`. Lemmas whose two sides both consume the borrow, such as `AddMEq` with `AddM(x, y)` against `AddM'(x, y)`, are untouched. The program-level idiom is a reborrow, `AddM(&*x, 0)` (P05: `AddMZeroRe` is accepted, and `AddM(&*x, 0); *x := 5` is accepted). With it the consumed borrow is a temporary that dies with the hole, and the channel is invisible. The difference is error-only.

### G4. A borrow binding ended inside a side (row 7)

```
def KillDrop (y : &Nat) : Id(Unit, (let l = 0; y := &l; ()), ()) := refl    -- the [Drop] of l ends y (D65 amended); reject def KillDropCT … ; *y := 5
def KillRead (x : Nat) : Unit := (let y = &x; let h : Id(Unit, (let a = clone(x); ()), ()) = refl; *y := 5)
reject def KillReadCT (x : Nat) : Unit := (let y = &x; (let a = clone(x); ()); *y := 5)      def KillReadCU (x : Nat) : Unit := (let y = &x; (); *y := 5)
def KillRe (x : Nat) : Unit := (let y = &x; let v = &*y; let h : Id(Unit, *y := 5, *v := 5) = refl; *v := 6)
reject def KillReCT (x : Nat) : Unit := (let y = &x; let v = &*y; *y := 5; *v := 6)          def KillReCU (x : Nat) : Unit := (let y = &x; let v = &*y; *v := 5; *v := 6)
```

All are accepted on main and on D84. A side that only copies `x` ends a borrow of `x` held elsewhere in the frame ([Access]), and a later use of that borrow is rejected. The footprint, even D84's, cannot see this: `x`'s contents are the same on both sides once borrows end. The `KillRead` and `KillRe` kinds arise only for an `Id` formed inside a body, since a lemma's parameters never alias (G6). The difference is error-only.

### G5. A borrow left partly moved (row 8)

```
def MoveThru (y : &Nat) : Id(Unit, (let a = *y; ()), ()) := refl
def MoveThruR (y : &Nat) : Id(Nat, *y, clone(*y)) := refl
reject def MoveThruCT (y : &Nat) : Unit := (let a = *y; ())        def MoveThruCU (y : &Nat) : Unit := ()
```

Both are accepted on main and on D84. Reading `*y` moves out through the borrow. [Obs] lets a borrow end over a moved-out part (the `observing` flag, D68), and the footprint does not hold `y`'s owner, because `y` is only read through. So the `⊥` left behind is never compared, while a context in which `y`'s borrow ends (the function's return) is rejected. O3's parenthesis ("a read that moves leaves `⊥`, which must be refilled before the borrow over it ends, and refilling is a write") holds of an accepted program, not of an `Id` side. The difference is error-only.

### G6. A lemma used where its parameters alias (row 10)

```
def KR (x : Nat) (y : &Nat) : Id(Unit, (let a = clone(x); ()), ()) := refl
def KV (x : Nat) (y : &Nat) : Id(Nat, (*y := 5; clone(x)), (let a = clone(x); *y := 5; a)) := refl
def UseKR (x : Nat) : Unit := (let y = &x; let h = KR(x, y); ())             -- accepted, and true there
def KVCT (x : Nat) : Nat := (let y = &x; *y := 5; clone(x))                  reject def KVCU (x : Nat) : Nat := (let y = &x; let a = clone(x); *y := 5; a)
```

A lemma speaks about its own frame. At its generic call and at every actual call, the parameters are separate bindings, so `KR` and `KV` are true. Their instance at `UseKR` is computed in the callee's frame, where `x` is a copy, and it is true there. Pasting the lemma's sides into a context where `y` borrows `x` is outside what the lemma says. In the probe, the difference shows only as the rejection of one filling. Target C must therefore take instances that are separated as the generic call is (§ Target C). That aliasing only ever shows as an error is a conjecture, supported by `KV` and by the exclusivity argument: in an aliased context, a side that accesses `x` ends `y`, so every use of `y` must precede every access to `x`, in both fillings.

## Channels that are covered

- **Function values** (P07). The re-pointing pair under `λ`, `λ(x z : Nat) (y : &Nat) => ((y := &x; ()); *y := 7)` against the same with `&z`, is convertible, and correctly so: a caller passes `y` in, and the callee's re-pointing of its own parameter is invisible (`CallRPEq`, accepted). Functions that differ in their effect on the caller stay apart (`FnWrite` is rejected; `FnWriteKept` is accepted). A call's frame insulates the caller from every channel in G1–G5, so [Conv-fun]'s observation of the generic call is adequate for call contexts.
- **Stuck blocks** (P09). The re-pointing pair inside a stuck match closes off with `y` taken by move. After the block, `y` is `⊥` on the symbolic path, so `…; *y := 7` is rejected (`RPB`). The `Id` over the block computes to sealed equations that hold at every instance, not to `False` (`RPBnF (…) (h : Id(…)) : False := h` is rejected on main and on D84). This is fail-safe and incomplete.
- **Using an `Id` proof.** `Id` computes to a conjunction of `Eq`s over the observed values, so `J`, `rewrite` and `symm` transport only along those equations. `cong(f, h)` needs `h : Eq(A, a, b)` over values. No rule substitutes equal computations into a context, so a gap cannot be turned into a proof of `False` through a proof of `Id`: the gaps say only that `Id` is weaker than contextual equivalence, and nothing in the logic assumes otherwise.
- **Abstract values and records.** A side's η-refinements and generalisation records survive its copy (D37, D79). They are facts about neutrals, true at every instance, and they leave nothing at runtime.

## Fix proposals, ranked by cost

The costs were measured on the D84 snapshot, built whole with each fix applied. The variant copies log a flipped verdict as a warning instead of an error, so that every module still builds. A rejected lemma is not exported, so a flip can cascade to the declarations that cite it, and those count as flips too. Each variant was checked against the probes, to confirm that the fix rejects the gap's `Id` and keeps its controls. The variants are a scratch script (`…/scratchpad/variants/patch.py`), not proposed code.

**F0. Restate Target C over typed contexts** (§ Target C).
- Cost: no checker change and no verdict.
- Effect: removes every error-only channel (G1, G3, G4, G5, G6) from Target C's obligations.
- D84: independent. Under this statement, D84's read footprint is not needed for adequacy.

**F1. [Obs-ref]: observe a re-pointed borrow binding by its target.** It closes G2, the one gap left under F0.
- *Rule.* For every binding of the frame in which `Id` is formed whose declared type is a borrow type and which a side assigns whole (`y := …`), if it holds a borrow after both sides, each side's observation writes the same fresh abstract value `σ_y : T` through it (`*y := σ_y`) before its borrows end. This is what [Obs-borrow] does for a borrow-typed result (D38). The footprint already holds the owners of `y`'s target at formation (`y` is assigned) and of every place a side borrows. So after the write, those owners show where `y` points.
- *A binding that holds a borrow after one side only.* Nothing is written for it. Under F0, a continuation that uses it is rejected after the other side.
- *Measured.* Variant B rejects `RePoint`, `SwapB` and `CursorSite`, keeps their controls (`SameTargetFix`, `AddMZeroReFix`, `AssignBot`), and flips no suite verdict. It also rejects P02's `SwapCtxT`, `Id(Unit, (swap; *y1 := 7), *y2 := 7)`, rightly: after the swap, `y1` points where `y2` did, and a later `*y1 := 8` tells the two apart. A scan of every `Id` in the suite for whole assignments finds one side that re-points a borrow binding, `Drops.AssignBot`, and both of its sides point the binding at the same place.
- *D84.* Independent: it creates no `⊥` and needs no definiteness of `⊥`.
- *Policy.* Which bindings are observed is read from syntax (assigned whole) and declared types (`&T`), the same on both paths, like the footprint's roots. Whether a binding holds a borrow after both sides is read from the run, so the rule is "Two paths, value-dependent by design", with this argument for `notes/two-paths-census.md`:
  - The symbolic path ends borrows at least as early as an instance does, so "held after both" on the symbolic path implies it at every instance.
  - The converse fails: `x := Pick(n, &a, &b); clone(b)` ends `x` symbolically, but at `n = 0` it does not.
  - Where an instance writes through a binding that the symbolic path did not, the symbolic owners hold the ended borrow's sealed fills, which already distinguish the sides whenever their targets differ at the instance.
  - That last step is an obligation to prove, not a proof.

**F1′. The cheap alternative to F1: an `Id` side may not assign a borrow binding of the enclosing frame.**
- Cost: one verdict, `Drops.AssignBot`, which would then be rejected.
- Policy: read from syntax and declared types alone.
- Trade-off: F1 is preferred. It costs nothing measured, and it keeps true statements like `AssignBot` provable.

The remaining fixes matter only under (S), the strong reading with a side condition.

**F2. D84's read footprint (owned moves, G1).**
- In progress on branch `d84`, and it rejects all three G1 probes.
- Its cost belongs to the D84 lane.

**F3. A borrow variable read through puts its owners in the footprint (G5).**
- *Change.* The footprint's second pass counts every read occurrence rooted at a borrow variable, not only whole ones. That reverses D68's "one only read through does not".
- *Measured.* Variant A: under D84's `eq(⊥, v) = False`, `MoveThru` and `MoveThruR` compute to `False`. No suite verdict flips: an extra owner equation over unchanged contents is `True` by conversion, and the unit laws absorb it.
- *Main and D84.* On main without D84 the extra equation over a `⊥` is stuck, which rejects too, but it would also make true statements stuck, so F3 should land after D84.
- *Alternative.* Drop the `observing` exemption for borrows held by bindings of the frame. A side that leaves one partly moved is then an error instead of `False`.
- *Policy.* The footprint's roots are read from syntax.

**F4. A side may not end a borrow held by a binding of the enclosing frame, except by moving or assigning that binding itself (G4).**
- *Change.* Inside an observation, an [Access] or [Drop] that ends such a borrow is an error.
- *Measured.* Variant D approximates it by treating "held by a binding that no side mentions whole at formation, held after one side and not the other" as `False`. It rejects `KillRead` and `KillRe`, and flips four suite verdicts: `ClosingOff.CoInert`, `CoWrittenFirst`, `CoPerArm` and `CoBlockBorrow`.
  - Each forms `Id(Nat, clone(c), 7)` in a body while `t = TailM(&c)` holds a borrow into `c`. The side `clone(c)` ends `t` and the side `7` does not.
  - Each is true under the typed statement, since nothing uses `t` afterwards.
  - Under (S) each would need `t` ended before the statement.
- *Why an error and not `False`.* An end by [Access] is not definite on the symbolic path (the `Pick` example above), so making it `False` could make a statement `False` symbolically that is true at an instance.
- *Policy.* A check inside the run that only rejects: value-dependent by design and fail-safe.

**F5. Observe borrow consumption (G3) inside `Id`. Not viable.**
- *Measured.* Variant C flips 81 suite verdicts, 28 directly and 53 by citation, starting with `AddMZero` (G3).
- *Why.* Consumption is the suite's idiom, and the lemmas it flips are the ones users want.
- *Replacement.* (S)'s side condition below.

Ranked by cost: F0 (0), F1 (0 measured), F3 (0 measured), F1′ (1), F4 (4 measured, approximated), F2 (D84's own cost), F5 (81, rejected).

## Target C, drafted

**Programs, runs, outcomes.**
- A *program* is a list of declarations, each accepted.
- A *closed run* of a program is a call of one of its definitions at closed arguments built by accepted code, executed by the erased runtime of Target B (concrete, with explicit errors, and runtime `J`, D85).
- Its *outcome* is either an error, or a result together with the final contents of the places its borrow arguments lend. Every other place is dropped when the call returns.
- Two outcomes are *the same* when both are errors, or both return with equal results and equal final contents. Equality of closed values is `Eq`'s meaning in the set model: identity on data, equal meanings for functions.

**Contexts.**
- A *context* `C` is a program with one hole `□` at a runtime position of a definition body: not erased (P2), so not inside a type, a proof, or a side of `Eq`, `Id` or `J`.
- `C[s]` is the program with `□` replaced by `s`, the free variables of `s` being bound by `C` at the hole.

**Uses.** A proved `Id(A, t, u)` is used at a hole in one of two ways.
- *(L) A lemma.* `L (x̄ : Ā) : Id(A, t, u)` is accepted and hole-free. A use of `L` is an injective renaming `θ` of `x̄` to variables bound at the hole, such that every time a run reaches the hole, the state is an *instance of `L`'s generic call* there:
  - the values of `θ(x̄)` lie in the meanings of `Ā`, and the hypotheses (the proof parameters' propositions) are true;
  - the parameters are separated as at the generic call: no place of one parameter holds a live loan of another parameter's borrow.

  A call of `L` always satisfies separation, by the frame property; a use pasted into a context need not, hence the condition.
- *(B) In a body.* `Id(A, t, u)` is formed in an accepted definition, at a program point where a proof of it is accepted. Its use is a hole at that point, with `θ` the identity: every run that reaches the point is an instance of the symbolic state at which the `Id` was computed.

**Target C (typed).** If `L` (or the in-body `Id`) is used at the hole of `C` under `θ`, and `C[tθ]` and `C[uθ]` are both accepted, then for every closed run, the outcomes of `C[tθ]` and `C[uθ]` are the same. By Target B, neither outcome is an error. So the statement says: the same result and the same final state, and, trivially, the same errors.

**What it does not say.**
- It says nothing about a position where only one filling is accepted. Whether a refactoring type-checks is the checker's to decide, not `Id`'s.
- The draft's stronger reading, one filling accepted and errors observable in the other, is false (G3, `AddMZeroSym`). A proof of `Id(A, u, t)` is usually had from one of `Id(A, t, u)` (`AddMZeroSym` is `symm(AddMZero(x))`), so the one-sided reading fails in both directions.

**(S), if errors must be observable.** Allow `C[uθ]` to be unaccepted and compare outcomes including errors, under a side condition: no borrow variable that `tθ` or `uθ` mentions whole (assigned, or read whole) is used by `C` after the hole. That is, the hole consumes the borrow bindings it mentions whole, as a call consumes the borrows passed to it. A lemma's borrow parameters instantiated by fresh reborrows (`AddM(&*x, 0)`) meet the condition automatically. Under (S):
- G2 and G3 disappear: the bindings they re-point or consume are mentioned whole;
- G1 needs D84 (F2);
- G5 needs F3;
- G4 needs F4;
- G6's separation condition is needed as stated above.

**Obligations of a proof (typed statement).**
1. *The context lemma.* An accepted continuation observes a hole only through its result, the contents of the places it reaches (all owners, O4), and where the borrow bindings it uses point. Moves, borrows ended, and borrows left partly moved show only as rejections. This is the lemma `docs/18` § `Id` adequacy calls for, made precise. With F1, `Id` compares all three.
2. *[Obs-ref] at two paths.* The argument under F1, to be proved alongside footprint coverage.
3. *Separation at uses of lemmas.* An aliased use shows only as a rejection of one filling (G6). This is a conjecture, supported by the probe and by exclusivity.
4. *Footprint coverage and the injectivity of contexts.* Already in `docs/18`'s list, for O3 and O4.

**What changes in `docs/18`'s principles.**
- O2 becomes: a borrow binding left live by both sides and assigned by one is observed by writing through it; one consumed or ended by a side is invisible, because a typed continuation cannot use it.
- O3's parenthesis is right only under the typed statement, and should say so.

## After D84 (2026-11-10)

Re-run on main at `7ae8cf00`, where D84 has landed: [Join], `⊥` as a value of its own, [Id-typestate] with its no-ending clause, and [Obs-ref]. D84's DECISIONS entry states Target C as typed contextual equivalence plus a *resource lemma*: if `Id(A, t, u)` is well formed and proved at the use, and `C[t]` is accepted, then `C[u]` is accepted or is rejected only because `u`'s values are not convertible with `t`'s. The same probes were run, unchanged, against a fresh build of `Ochr.Examples.Nat`, `Fixtures` and `Word`, and two new probes attack the resource lemma (`R01_DeclCopy.lean`, `R02_DeclGrain.lean`, in the same scratchpad folder).

**Counterexample to the resource lemma.** A proof by `refl` between convertible values, where one filling is accepted and the other is rejected by a move error. It is not a proof of `False`: Target C, over contexts where both fillings are accepted, is untouched.

```
ochr R01DeclCopy uses WordType {
  def TT (n : Nat) : Type := match n { Z => Word, S _ => Nat }
  def g (u : Unit) : TT(0) := Zero
  def IdG : Id(Word, Zero, g(())) := refl                                   -- accepted (FlipIdG fires)
  def CT (u : Unit) : Word := (let v = Zero; let a = v; v)                  -- accepted (FlipCT fires)
  reject def CU (u : Unit) : Word := (let v = g(()); let a = v; v)          -- rejected: [Read] v was moved out
  reject def CU2 (u : Unit) : Word := (let v = g(()); let f = (λ(w : Unit) : Word => v); f(()))
                                                                            -- rejected: [D53] a closure's body moves a captured value out
}
```

Both sides of `IdG` move nothing and leave the same type-state, and both evaluate to `Zero`, so `refl` proves it. The context `let v = □; let a = v; v` is accepted with `t = Zero` and rejected with `u = g(())`. The reason is that copy-or-move is read from a `let`'s right-hand side's *declared* type (P3, D80). `Zero` reads as `Word`, a copy type. `g(())` reads as `TT(0)`, a type function's call, which the reader takes as its arms `Word | Nat`, not a copy type, although `TT(0)` computes to `Word`. The twin with arms that are both `Word` (`TW`, `gw`, `CUW`) is accepted with either filling.

The same cause reaches [Join]'s grain (`R02_DeclGrain.lean`). A field step is kept only through a declared type that reads as a one-constructor inductive, not computed by a match (D84's `jdGrain`):

```
def TP (n : Nat) : Type := match n { Z => Nat × Nat, S _ => Nat × Nat }
def gp (u : Unit) : TP(0) := (Z, Z)
def IdP : Id(Nat × Nat, (Z, Z), gp(())) := refl                             -- accepted
def PT (u : Unit) : Nat := (let v = (Z, Z); let a = v.0; v.1)               -- accepted
reject def PU (u : Unit) : Nat := (let v = gp(()); let a = v.0; v.1)        -- rejected: [Match] on v, which was moved out
```

D84 notes that option (i) costs "only fields reached through a type-level match whose arms agree". `PU` shows that this cost is a resource-lemma counterexample, not only incompleteness.

**What the type-state misses.** A side's *declared reading*: what the one reader of declared types (P2, D80) makes of the side's own type. That reading decides how the rest of the frame may use the result: copy or move, η at `Unit`, a closure's Fn rule over a capture, and the grain of later moves. `Id` asks only that both sides have type `A` up to conversion. Two candidate fixes, both read from syntax and declared types, neither measured (no time before the deadline):
- **[Id-typestate], fifth component.** Each side's declared reading must equal the other's: `IdG` and `IdP` become ill-formed, with a hint to ascribe the side (`(g(()) : Word)`), if an ascription is read as the declared type.
- **Weaken the lemma.** Add "or because `u`'s declared type reads differently from `t`'s" to the resource lemma's escape clause, beside non-convertible values.

The first keeps the lemma's promise. Its cost is the suite's `Id`s whose sides read differently but are provable. None is known; `Moves84`'s grain tests are the likeliest.

**The channel table, re-run.** Every gap of § The channels is now closed, either as a static [Id-typestate] error naming the component and the place, or (for a two-sided re-point) as an unprovable [Obs-ref] equation.

| Gap | Probe | On `7ae8cf00` |
|---|---|---|
| G1, owned moves | `T`, `TF`, `TC` | ill-formed: "the left side of Id moves x" (and `p.0`, `m`) |
| G2, where a borrow points | `RePoint` | well formed, and computes to `Eq(Nat, σ3, σ0) ∧ Eq(Nat, σ1, σ3)`: not provable |
| G2 | `SwapB`, `CursorSite`, `SwapCtxT` | ill-formed: "the left side re-points the borrow y1" (`y`) and the right does not |
| G2 | `RePointCtx` | ill-formed: no-ending clause (`clone(x)` ends `y`) |
| G3, consumption | `MoveB`, `MoveL`, `AddMZero2`, `AddMZeroSym`, `RPB0` | ill-formed: "consumes the borrow" |
| G3 | `AddMZeroRe` (a reborrow) | accepted, as intended |
| G4, ending inside a side | `KillRead`, `KillRe` | ill-formed: no-ending clause |
| G4 | `KillDrop` | ill-formed: one-sided re-point |
| G5, left partly moved | `MoveThru`, `MoveThruR` | ill-formed: "leaves moved, through a borrow, *y" |
| G6, aliasing at a use | `KR`, `KV` | accepted (true in the lemma's frame); the aliased context still shows the difference only as one filling's rejection |
| Function values | P07 | unchanged, covered |
| Stuck re-pointing | P09 | `RPB0` is now ill-formed (the block consumes `y`); otherwise unchanged and fail-safe |
| [Obs-ref] controls | `SameTargetFix`, `AddMZeroReFix` | accepted |

No closed proof of `False` was found. The resource lemma's counterexample (3) in D84's entry, which differs by conversion, is consistent with what is found here. `R01` and `R02` are new: they differ with *convertible* values.
