# A model of `Id` and observation

Theory lane, 2026-10-29, branch `split-model` (second task; the first is `notes/split-model.md`). Target: footprints and owners, "all owners observed", owned locals observed, [Obs-borrow], `Id`'s private copies, and the `PickX`/`PickY` and `Pick` examples. Method as for the split model: principles, derived rules, comparison with paper A.3 (§ "Observation, `Id` and conversion") and `Obs.lean`, probes with explicit verdicts and a rejected control.

## 1. The model

A state Ω has *owned* positions (bindings and temporaries holding values) and *borrows* (`borrow_ℓ w`, with `loan_ℓ` somewhere in an owned value or inside another borrow's content). The *resolution* ρ_Ω ends every borrow: it puts each borrow's current content where its loan is, outermost first. Resolution is the meaning of a state: two states with the same resolution are the same state to every program that runs after all its borrows end.

An *observation* of a computation `t` from Ω is the pair (ρ(v), ρ(Ω_t)), the resolved result and the resolved final state, of running `t` on a private copy. `Id(A, t, u)` should say: t and u, run from the same Ω, end in the same observation.

What makes this computable is that most of ρ(Ω_t) and ρ(Ω_u) is the same, so only some positions need comparing. The derived rules say which.

## 2. Principles

- **(I) Independence.** The two sides run from the same Ω on independent copies, and neither sees the other's effects. They are evaluated in the same world: no refinement separates them, so a generalisation record one side makes may be reused by the other (split-model principle G holds within a world).
- **(R) Resolved, not represented.** Observations compare resolved values, never the representation of a state, so where a borrow sits, whether a loan has been substituted yet, and which frame a value is in do not matter. This is why `Id` ends every borrow before reading (`endAll`), and why owners, not borrows, are observed: a borrow is gone after resolution, and what it wrote is in the owned position its loan leads to.
- **(F) Footprint sufficiency.** A position whose resolved final content cannot differ between the two sides need not be observed. A position can differ only if one side writes it, directly or through a borrow. So observe the owners of every place a side writes or borrows, and of every borrow variable a side hands on whole (the callee may write through it). A place a side only reads is not observed: a read does not change the resolved content, and a read that *moves* leaves `⊥`, which must be restored before the borrow over it ends (a borrow is whole again when it ends, D53), and restoring it is a write, which is observed.
- **(A) All owners.** A loan can sit in several owned positions at once: a borrow returned by a stuck call leaves its hole in every argument the call might have returned it from. Each of them holds a function of what was written through the borrow, so each must be observed; observing one is observing the hole in only one of the places its write lands.
- **(O) One order.** The conjunction `Id` computes must come out in the same order on both evaluation paths, since `∧` is not commutative by conversion; so it is ordered by syntax, not by Ω.

## 3. Derived rules vs. the checker

| Derived | Checker / paper | Verdict |
|---|---|---|
| (I) each side on its own copy, same Ω | `observe` runs under `onCopy`, both sides from the state at `idType` | matches |
| (I) records shared between sides (same world) | `onCopy`/`restoreKeep` keeps `neutrals` | matches |
| (R) end every borrow before reading | `observe` → `endAll` | matches |
| (R) observe owners, not borrows | `footprint` → `owners` (A.3 "Owners") | matches |
| (F) owners of written/borrowed places and of borrow variables handed on whole | `footprint`: `k == .borrow ∨ .assign`, then `(isRefTy ∨ isBorrow) ∧ k == .read ∧ q = var` | matches |
| (F) a place only read is not observed, and a move is not a write | D68's rule, A.3 "A place that is only read contributes nothing" | matches; see §4 P3 for why the `⊥`-borrow-variable clause is safe |
| (A) every owner of a loan | `owners` follows each occurrence of `loan_ℓ` outward | matches (`BadD18`, `ClosedD18` pin the counterexample) |
| (O) syntactic order, owners deduplicated | `footprint` orders by first write/borrow, then by whole reads, without repeats | matches |
| [Obs-borrow]: a borrow-typed result is observed through a written fresh value | `convFnRun` writes one shared `σw` before ending borrows | matches (`ConvPick` pins `PickX`/`PickY`) |
| a moved-out owned place is still observed, its equation stuck | `own(x) = {x}` for owned `x` even when `⊥`; `mkEqM` checks `⊥` first | matches |
| an owner's type when both sides consumed it | `idType` falls back to `Unit`, with a hole on a side | safe: `mkEqM` returns the stuck `Eq` whenever either side has `⊥`, before reading any type, so the fallback type is never used to decide |

I found no derived obligation the checker lacks.

### Why the generic footprint is at least the instance's (census site 14)

The two-paths census argues that the footprint at the generic call contains an instance's, and refinement turns the extra equations into `⊤`. The model gives the argument in two parts.
- The footprint's *roots* are read off syntax (place occurrences and their kinds), so they are the same on both paths. Only the owners a root contributes can differ, through `owners(ℓ)`.
- At the generic call, a borrow parameter's loan sits in one fresh cell. At an instance it may sit in several owners (A), or in one owner holding more than the borrowed part (two borrow parameters into two fields of one pair). Every extra owner's resolved content is a function of what was written through the borrow plus parts no side writes. So if the generic proves the written values equal, each extra owner's equation holds too, by congruence on the written part and reflexivity on the rest.

That is a semantic argument (it holds in the model). Whether conversion always *computes* those extra equations to `⊤` is the stability conjecture again; probe P4 below is one instance where it does.

## 4. Probes

All run on the built tree with verdicts printed by `#eval (Ochr.Test.run …)`, each with `def Control : False := refl`, rejected every time (so no stale build).

- **P3, an owner observed at an instance but not at the generic call.** The footprint gives `own(x) = ∅` to a borrow variable `x : &T` holding `⊥`. If a stuck block earlier in a statement moved `x` at the generic call (one arm moves it) but not at an instance (the taken arm does not), the instance would observe `x`'s owner and the generic would not, and an `Id` could be `⊤` generically and `False` at the instance. Tried twice:
  - `Id` side writes `*x := Zero` in a stuck arm. Rejected at the generic call: "no such place *x: its path does not exist in ⊥".
  - `Id` side passes `x` whole (`Zap(x)`) in a stuck arm. Rejected: "[Read] x was moved out or its borrow ended (reading ⊥)".

  Both fail safe, for the same reason. **Derived:** a footprint root is put there by an occurrence that the side's run (or its stuck block's capture) accesses, so a successful observation never writes through a `⊥` root. The `∅` clause only covers re-initialising a moved borrow variable (`x := &d`), which writes nothing through the old borrow. The honest statement without the first block (`L2`) observes `x`'s owner and is correctly not provable by `refl`.
- **P4, two borrow parameters that share one owner at the instance.** `W2(x, y : &Word) : Id(Unit, (*x := Zero; *y := Zero), (*y := Zero; *x := Zero)) := refl` is accepted, and its instance at `&a, &b` (two fields of one pair) computes to `⊤`: one owner, deduplicated, whose fields injectivity compares separately. Consistent with the site-14 argument.
- **P5, a generalisation shared across sides.** `S5(g, n) : Id(Word, match g(n) { Zero => Zero, Succ(p) => Succ(p) }, g(n))` is true, and rejected: side `t` is a stuck block over the generalised `σ3`, side `u` is `σ3`, and they are not convertible (no η for a match). An incompleteness, not a hole; recorded in §6.

The known counterexamples (`BadD18`/`ClosedD18` for all owners, `ConvPick` for [Obs-borrow], the `Pick` naturality example) are registered tests and still rejected in the green build.

## 5. Choke point landed: `obsResult`

The checker had two observations of a result: `observe` (`Id`'s sides) and a local `obs` inside `convFnRun` ([Conv-fun]). Both held the result as a temporary, ended every borrow and read it back, and [Conv-fun]'s also did [Obs-borrow]. They differed in one flag: `observe` set `observing` around `endAll`, so a borrow may end over a moved-out part and read as `⊥` (D68); `convFnRun` never touched it.

Landed: `obsResult (r, σw?, observing)` in the evaluator block, the one place a result is observed, with [Obs-borrow] inside it. `observe` calls it with `observing := true`, `convFnRun` with the flag its caller left (exactly its old behaviour). It also restores the flag afterwards instead of resetting it to `false`, so an observation nested inside another's borrow ends keeps the outer one's flag. The paper's [Obs] text now says the two rules are one operation shared by `Id` and [Conv-fun], with `obsResult` in its pointer.

Verdict-neutral: `lake build` green (97 jobs), every assertion and the total guard unchanged.

## 6. Candidate simplifications and incompletenesses (not implemented)

- **One flag, one rule.** [Conv-fun] observes with whatever `observing` its caller left, `Id` with `true`. The paper states one [Obs]. Either [Conv-fun] should also read a borrow ended over a moved-out part as `⊥` (one rule; risky without a verdict check, since it may admit more conversions), or the paper should say that only `Id`'s observation tolerates `⊥`. Describing only.
- **`own(x) = ∅` for a `⊥` borrow variable** is reachable only through re-initialisation (P3). The paper could say so, which turns a clause that looks like a two-paths risk into an evidently safe one.
- **No η for a match** (P5): `match g(n) { Zero => Zero, Succ(p) => Succ(p) }` is not convertible with `g(n)`. Lean would not identify these by conversion either; noting it because a generalisation record shared across sides makes it look as if they should meet.

## 7. Open questions

- **Stability** again: the site-14 argument shows the extra instance equations are *true*; that conversion *computes* them to `⊤` is the stability conjecture.
- **The `Pick` example** (paper's argument that naturality must be stated up to resolution) is consistent with principle (R): it is equality before resolution that fails. The model supports stating Conjecture 3 on resolved states, as the paper does.
- A generator aimed at (A) (stuck calls returning borrows into several arguments, then statements observing a subset of the owners) is the cheap falsifier for this area.
