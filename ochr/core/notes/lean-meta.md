# lean-meta: mechanised first-order metatheory of Ochr core v1.3 (running log)

Package: `ochr/core/meta-lean/` (Lake package `OchrMeta`, Lean 4.33, no Mathlib). Build: `lake build` in that directory. Branch `ochr-core-meta`.

## Status table (updated at each milestone)

| Item | Status |
|---|---|
| FO syntax, values, environments | done (`Syntax`, `Val`, `Env`) |
| the machine `exec` / `Eval`, fuelled interpreter `run`, `run_sound` | done (`Machine`, `Interp`) |
| [Seal] normalisation `norm`, owners, canonical renaming | done (`Interp`) |
| tests `e1e2_runs`, `close_eqs`, `owners_pick`, `access_inner`, `erase_natural` | pass (`Tests/Basic`) |

## Design decisions of the mechanisation (and why)

1. **Clocked functional big-step semantics.** `exec P n s t : Res` (results `ok s v | stuck | err | oof`) is the machine; `Eval P s t r := r ≠ oof ∧ ∃ n, exec P n s t = r`. One clause per rule of RULES §3. `run_sound` is then immediate. Chosen over an inductive relation because every theorem below is a *commutation* of the machine with a state transformation, and the fuel induction makes those equations (not just simulations), with `stuck`/`err` propagation handled once by `Res.bind`.
2. **Sealed programs are structural.** `Val.sealed f args k w` stands for `⌈L; C; K⌉`: `args` are the contents `uᵢ` (borrow positions) / values `wⱼ` (elsewhere), `k ∈ {res, fin i, cur, back i}` is the row of the [Close] table, `w` is the value written back through a returned borrow (`loan_k` at [Close] time). The term `L; C; K` is rebuilt by `sealTerm` when [Seal] re-runs it.
3. **A global fresh-loan counter** lives in the state. Fresh names then do not depend on the part of the environment a run cannot see, which is what lets the frame lemma be an equation. The price: comparing runs that allocate different numbers of loans (a [Close] against the concrete run it stands for) needs an injective renaming (`≈`).
4. **Borrows are held only at the top level of a binding** (RULES §1 scope: no borrows inside data). "Live loan" = its borrow is held by some binding. [End ℓ] clears the holder and substitutes, as RULES says; it refuses (error) if the borrowed content contains a borrow, which cannot happen in a well-formed state and makes [Access] terminate by a plain measure (number of `borrow` constructors).
5. **Values in flight.** Arguments live in temporaries `tmp i` of the caller's frame (RULES [Call]). The value returned by a `let`/frame pop is passed to [Drop] as `extra`, so that dropping a place whose loan is held by the returned borrow is the error RULES [Drop] requires (`let a = Z; &a`). The right-hand side of `p := t` is *not* visible to [Access] of `p`: this is what lets `r := &(*r).1` (reborrow-and-replace) run; RULES does not say either way (see Findings, F1).
6. **Erased terms are skipped.** `erase t` and calls whose result type is `prop` return `⋆` and leave the state unchanged, arguments included. Under v1.3 P2 (a private copy, discarded) this is exactly the run's effect on the state; the private run only matters for *typing* errors, which belong to the checker, not to this fragment.
7. **Stuck results do not carry a state.** [Close] restores the call-point state, so "discard the partial run" is literal: the body's partial state is simply not in `Res.stuck`.
8. **`match` arms use substitution** `ts[y := p.1]`; source programs are assumed to use distinct bound names (Barendregt), since substitution of a place for `y` is not capture-avoiding.
9. **Stuck blocks** (a non-tail stuck match closed off as an anonymous function) are not a machine rule here: in FO the author lambda-lifts by hand, and the block becomes an ordinary [Close] of a named function. A top-level stuck match returns `stuck`.

## Findings (rules / meta-model-v1 underspecified or wrong)

- **F1 (underspecified): is the right-hand side of `p := t` visible to [Access]?** RULES [Call] puts arguments in temporaries so [Access] can see them; [Assign] is silent. If the value `v` of `t` is visible, `r := &(*r).1` ends the new borrow (its loan sits inside `content(r)`), so the traversal idiom is rejected; if it is invisible (my choice), it runs, and the old borrow of `r` ends into the owner with the new loan inside it. Soundness is unaffected either way (the frame lemma and the invariants below hold for both readings); it is a completeness choice the paper should state.
- **F2 (underspecified): [Drop] of a place whose loan is held by the value being returned.** RULES says a live loan in a dropped owned value is an error, but the only borrow that can be live at that moment is the returned value, which is not in Ω. The mechanisation treats the value in flight as live (so `let a = Z; &a` errors, as intended).
