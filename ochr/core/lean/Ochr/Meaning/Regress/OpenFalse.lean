import Ochr.Meaning.Regress.EvalMemGap
import Ochr.Meaning.Steps.MachineMono

/-!
# Two open statements false as stated (sixth lead's inventory, `Meaning/OPEN.md`; kernel-checked)

Found while making the inventory of open statements; each fails for a missing hypothesis that its
use site has, not for a fault of the checker or the model.

1. `MachineMono.grows_restoreKeep` (`restoreKeep saved` only extends the tables, from ANY state):
   `restoreKeep` takes the globals and declarations from `saved`, so from a state whose globals
   differ it does not keep them (`grows_restoreKeep_false`). Every use restores a snapshot of the
   same run, whose globals are the current state's; the statement needs that hypothesis.
2. `Assembly.typedFutureF_exists` (a state good with values in flight has a typed future): a
   flight can type a label at an empty type, and then `GoodF` holds vacuously (membership is asked
   only at typed futures, of which there are none) while no typed future exists
   (`typedFutureF_exists_false`, the empty frame with the label `0` typed `False`).
3. `eval_step_stmt` at a typed hole (`eval_hole_false`): the checker's `?` succeeds with a fresh
   unknown, and the reference has no clause for it, so "the reference's run succeeds" fails. The
   chain's `NoHoles` never reaches the evaluation statements.
4. Not a statement: the reference trusts an ascription (`run_ascribe_trusted`), so it is not strict
   (route (C) of docs/31 D83).
-/

namespace Ochr.Meaning.Regress.OpenFalse
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Regress.EvalMemGap
open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out)

/-! ## 1. `grows_restoreKeep` -/

/-- A snapshot with one global. -/
def saved1 : MState := { globals := [{ name := "g", ty := .tNat, fn? := none, val := .zero }] }

theorem okRK : isOk (Ochr.restoreKeep saved1) S0 10 = true := by decide +kernel

/-- **`grows_restoreKeep` is false**: restoring a snapshot with a global, from the empty frame
(which has none), changes the globals. -/
theorem grows_restoreKeep_false : ¬ GrowsM (Ochr.restoreKeep saved1) := by
  intro h
  have hg := (h S0 10 () _ (runs_out (Ochr.restoreKeep saved1) S0 10 okRK)).globals
  have e : (outSt (Ochr.restoreKeep saved1) S0 10).globals.length = 1 := by decide +kernel
  rw [hg] at e
  simp [S0] at e

/-! ## 2. `typedFutureF_exists` -/

/-- `Good` gives `GoodF` at any flight: a future typed at the flight is typed. -/
theorem goodF_of_good (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (st : MState)
    (fl : Flight) (hg : Good dm C Γ ρ st) : GoodF dm C Γ ρ st fl :=
  ⟨hg.1, ⟨fun φ hφ => hg.2.1.pos φ hφ.1, hg.2.1.absTy, hg.2.1.goal⟩, hg.2.2⟩

/-- **`typedFutureF_exists` is false at every context**: the empty frame with `0` in flight and the
label `0` typed `False` is good with that flight (vacuously), and no future gives `0` a member of
`False`. The statement needs the flight's types inhabited (its use site's flight is a borrow's
content type, inhabited by the borrow's record). -/
theorem typedFutureF_exists_false (K : RunCtx) (ρ : Assignment) :
    ¬ ∀ (st : MState) (fl : Flight), GoodF K.dm K.M K.Γ ρ st fl → ∃ ψ, TypedFutureF K.dm K.M K.Γ ρ st fl ψ := by
  intro h
  obtain ⟨ψ, -, hψ⟩ := h (S0.withTemp .zero) [(0, TyM.prop False)]
    (goodF_of_good _ _ _ ρ _ _ (good_S0T K ρ))
  obtain ⟨⟨a⟩, -⟩ := hψ 0 (TyM.prop False) (by simp)
  exact a

/-! ## 3. The evaluation statement at a typed hole -/

/-- A typed hole `?` at `Nat`, from the empty frame with `0` in flight. -/
abbrev hl : M (Value × Option Value) := Ochr.eval 10 true (.prim "hole" []) (some .tNat)

theorem okH : isOk hl (S0.withTemp .zero) 10 = true := by decide +kernel

/-- The reference has no clause for a hole: its run fails. -/
theorem run_hole_none (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState) :
    runT K ρ φ tl h (.prim "hole" []) s = none := by
  simp [runT, SM.fail]

/-- **`eval_step_stmt` is false at a typed hole** (fuel 10, any context admitting the state, its
decisions aligned after): the checker's typed run of `?` at `Nat` succeeds (a fresh unknown,
docs/07), and the statement concludes that the reference's run succeeds, which it never does. The
chain assumes `NoHoles` of the program (`consistency_rel`) and never passes it down; the evaluation
statements need "the term holds no hole". -/
theorem eval_hole_false (K : RunCtx) (ρ : Assignment) (φ : Future) (hctx : CtxOk K ρ (S0.withTemp .zero))
    (hD : DecTab K.D (outSt hl (S0.withTemp .zero) 10)) : ¬ eval_step_stmt K ρ φ 10 := by
  intro hs
  have hrel : Rel K ρ φ id (S0.withTemp .zero) (SM' K ρ (S0.withTemp .zero)) :=
    Rel.start K ρ φ _ (fun l hl => by
      exfalso
      simp [SState.Live, SState.liveLabels, SM', MState.sstate, Env.shape, S0, MState.withTemp, valAt,
        SState.positions] at hl)
  have hr : Runs hl (S0.withTemp .zero) 10 ((outVal hl (S0.withTemp .zero) 10).1, (outVal hl (S0.withTemp .zero) 10).2)
      (outSt hl (S0.withTemp .zero) 10) := by
    have := runs_out hl _ 10 okH; revert this; generalize outVal hl (S0.withTemp .zero) 10 = p; intro this; exact this
  obtain ⟨ρ', Δ', π', -, -, -, -, r, s', hrun, -⟩ :=
    hs _ (outSt hl (S0.withTemp .zero) 10) true (.prim "hole" []) (some .tNat)
      (outVal hl (S0.withTemp .zero) 10).1 (outVal hl (S0.withTemp .zero) 10).2 (good_S0T K ρ) hctx _ id hrel
      (fun h => by cases h) hD 10 hr
  rw [run_hole_none] at hrun
  cases hrun

/-! ## 4. The reference run is not strict: an ascription is trusted

The orchestrator's route (C) for untyped runs (docs/31 D83): if the reference run failed wherever a
value is not a member of the type it is given, "the reference run succeeds" (`hok`) would carry the
membership the untyped run never checks. Today it does not: the reference's `.ascribe` types any
value at the annotation. -/

/-- **The reference runs `(0 : Unit)` to `0` typed `Unit`** (where the ascription is neither a
statement nor erased): a successful run whose result is no member of its type. A strict `.ascribe`
fails here, so the untyped `let x = (0 : Unit); x` would have no successful reference run, and the
untyped step, stated under `hok`, would owe nothing there. -/
theorem run_ascribe_trusted (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.ascribe (.val .zero) (.val .tUnit)) = (false, false)) :
    ∃ R : TyS, runT K ρ φ tl h (.ascribe (.val .zero) (.val .tUnit)) s = some ((.el0 Nat 0, R), s) ∧
      R.m = TyM.unit ∧ ¬ (Sem.el0 Nat 0 ∈ₛ[K.dm.read] R.m) := by
  refine ⟨{ TyS.plain TyM.unit with label := none }, ?_, rfl, ?_⟩
  · simp [runT, SM.erasedIf, SM.stmtIf, hfl, SM.onCopy, bind, pure, meanV, Sem.asTy]
  · rintro ⟨a, ha⟩
    exact unit_ne_nat (Sem.el0.inj ha).1

end Ochr.Meaning.Regress.OpenFalse
