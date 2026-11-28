import Ochr.Meaning.Consistency
import Ochr.Meaning.Steps.CallRanSim
import Ochr.Meaning.Steps.KnotR

/-!
# The top of the proof from `master`: the fundamental lemma's context at the program's contexts (lead43, 2026-11-28; docs/31 D253)

The top runs the general simulation (`Master.master`) at the context of each definition's check and applies the
fundamental lemma (`Strict.fund_all`) to the reference runs it gives; both need `Strict.FundCtx` of that context.

**FINDING (D253), repaired in the model by the orchestrator's ruling.** `FundCtx.globals` asks a good result of
`K.C.global n` for EVERY name `n` (it must: the reference's `.const n` returns `K.C.global n` for any `n`). The program
meaning gave a name that is no global `(err, err)`, which is no good result (`goodRes_err_false`), so `FundCtx` was FALSE
at every context `ProgState.ctx` builds, at the first item of every program included, and `fund_all` and every step
assuming `FundCtx` were vacuous there. The regression against the old reading: `not_fundCtx_of_errName` (any context
giving some name `(err, err)`). Repaired: `ProgState.baseC` gives such a name `ProgState.dfltGlobal`, `•` at `True`.

**What is left is a real obligation** (`fundCtx_progCtx`, PROVED here): `FundCtx` at the context of each item holds
exactly when the earlier items' meanings are members of their types with no label, and no data declaration of the
program is at `Type₁`. The first is the outer induction's hypothesis (the knot's output, consumed here); the second is a
fact about the checker (`checkInd` rejects a sort above `Type₀`), named at the top (`Top.SortsG`).
-/

namespace Ochr.Meaning.Steps.Form.Top

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

/-- `err` at the error type is no good result. -/
theorem goodRes_err_false (R : DataRead) : ¬ Strict.GoodRes R (.err, .plain TyM.err) := by
  rintro (⟨a, _⟩ | h | ⟨_, ⟨T, h⟩ | h⟩)
  · exact a.elim
  · cases h
  · cases h
  · cases h

/-- **REGRESSION (docs/31 D253): a context giving some name `(err, err)` fails `FundCtx`** — what the program meaning's
context did at every name that is no global, before `ProgState.dfltGlobal`. -/
theorem not_fundCtx_of_errName (K : RunCtx) (n : String) (hn : K.C.global n = (.err, .plain TyM.err)) :
    ¬ Strict.FundCtx K := by
  intro h
  have hg := (h.globals n).1
  rw [hn] at hg
  exact goodRes_err_false _ hg

/-- The default meaning is a good result with no label. -/
theorem goodRes_dfltGlobal (R : DataRead) : Strict.GoodRes R ProgState.dfltGlobal := .inl (Strict.proof_mem_true R)

/-- **`FundCtx` at a program meaning's context** (PROVED; the obligation the repair leaves, docs/31 D253): from the
stage's meanings being members of their types with no label (the outer induction's hypothesis), and no data
declaration of the list at `Type₁`. -/
theorem fundCtx_progCtx (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) (st : MState)
    (hmem : Assembly.MeansMember dm P) (hlab : ∀ e ∈ P.means, e.2.2.label = none) (hsorts : ∀ d ∈ Γ, d.sort ≠ 2) :
    Strict.FundCtx (P.ctx dm D Γ st) := by
  refine ⟨fun n => ?_, hsorts⟩
  show Strict.GoodRes dm.read (P.globalMean n, P.globalTy n) ∧ (P.globalTy n).label = none
  unfold ProgState.globalMean ProgState.globalTy
  cases e : P.means.find? (·.1 == n) with
  | none => exact ⟨goodRes_dfltGlobal _, rfl⟩
  | some x =>
    obtain ⟨m, s, T⟩ := x
    have hx := List.mem_of_find?_eq_some e
    exact ⟨.inl (hmem m s T hx), hlab _ hx⟩

end Ochr.Meaning.Steps.Form.Top
