import Ochr.Meaning.Steps.Form

/-!
# The form of a step in tail position, with worlds (lead16, 2026-11-21; docs/31 D131)

`Steps/Form.lean` states a step against ONE run of the checker that returns a value (`eval`). In tail
position the checker runs differently (`Machine.checkTail`): it hands each path's result to a
continuation `k` at that path's end, and on an unknown scrutinee it SPLITS: each arm runs in its own
world (`enterWorld`, `inWorld`), under that world's refinement (`refine`: `σ := Z`, or `σ := S(σ')` with
a fresh unknown `σ'`), and `k` runs at each world's leaf. The run as a whole returns nothing; what it
established is that `k` succeeded at every leaf.

The reference does not split: under an assignment `ρ` the scrutinee has one tag, so its run follows ONE
path, the one through the world `ρ` falls in. So the tail form says: some leaf of the checker's run, at
which `k` ran successfully on the leaf's value and type, and at which `Out` holds against the reference's
run of the whole term. Nothing in `Out` or `Ext` changes:

- the world's fresh unknowns are the extension of the assignment (`Ext`'s `ρ'` agrees with `ρ` below the
  starting state's unknowns and is free above: the fresh `σ'` gets its value there, `ρ σ - 1` for a
  number), and of `Δ` (`Ext`'s `Δ'`: the fresh unknown's type);
- the world's refinement is its path condition, asked of `ρ'` by the leaf's `Pre` (`TypedAssignment.refs`:
  `ρ' σ` is the meaning of the refinement's value): that is what makes the leaf the one `ρ` selects;
- the leaf's state, with the value in flight, is related to the reference's state after the whole term
  (`Out`'s `Rel`), and the checker's value at the leaf means the reference's result under `ρ'`.

`TailSim` is the statement for a term in tail position, from every related good reference state, as
`Form.Sim` is for `eval`; the reference runs the term in tail position at the hint the goal gives, as the
body of a function runs (`RunCongr.fixBodyAt`: `runT … true …`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **A tail step's conclusion**: some leaf `stl` of the checker's run where the continuation `k` ran
successfully on the leaf's value `v` at its type `T`, with `Out` there against the reference computation
`x` (the run of the whole term from `s`). The assignment `ρ'` that `Out` extends `ρ` to gives the world's
fresh unknowns their values; the leaf's `Pre` asks the world's refinements of it. -/
def TailOut (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState) (x : SM Res)
    (k : Value → Value → M Unit) : Prop :=
  ∃ (stl : MState) (v T : Value), (∃ bk stk, Runs (k v T) stl bk () stk) ∧ Out K ρ φ π st stl s x v (some T)

/-- **A term in tail position, simulated**: from every reference state related to the checker's state and
good, the checker's successful `checkTail` of `t` with the continuation `k` makes the reference's run of `t`
in tail position (at the hint the goal gives) succeed at the leaf of the world the assignment selects. -/
def TailSim (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) (st : MState) (t : Term)
    (k : Value → Value → M Unit) : Prop :=
  ∀ (s : SState) (π : Nat → Nat) (bh : Nat) (st' : MState),
    Pre K ρ st → Rel K ρ φ π st s → Strict.SGood K.dm K.Γ φ s →
    Runs (Ochr.checkTail fuel t k) st bh () st' →
    TailOut K ρ φ π st s (runT K ρ φ true (hintM K ρ st.goal) t) k

end Ochr.Meaning.Steps.Form
