import Ochr.Meaning.Steps.TopAssembly
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# The top's links attacked (lead44, 2026-11-28; docs/31 D256 on)

Regressions against the links of `consistency_of_master` as lead43 stated them, each kernel-checked here or guarded on
the real checker, with the repair it forced.
-/

namespace Ochr.Meaning.Steps.Form.Top.Attack

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

/-- `⊥` is no number. -/
theorem moved_not_mem_nat (R : DataRead) : ¬ Sem.moved ∈ₛ[R] TyM.nat := by
  rintro ⟨n, h⟩
  cases h

/-- **ConstLeafAt as lead43 stated it forces `⊥` into the goal** (docs/31 D256): its result `r` was quantified with no
tie to the checker's value (`GoodRes` admits `r.1 = moved`), so wherever the step's own conclusion holds at the leaf
(`Pre` there, which `eval_all` gives), the link asserts that `⊥` is a member of the constant's type. -/
theorem constLeafAt_old_forces_moved {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {P : ProgState}
    {d : Def} {st' : MState} {w : ConstWit}
    (h : ∀ (ρ' : Assignment) (Δ' : Nat → TyS) (r : Res),
      Pre { P.ctx dm D Γ st' with Δ := Δ' } ρ' (w.st₂.withTempT w.v (some w.T)) →
      StrAgree { P.ctx dm D Γ st' with Δ := Δ' } ρ' w.T r.2 → Strict.GoodRes dm.read r →
      r.1 ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ st') w.goal).m)
    (ρ' : Assignment) (Δ' : Nat → TyS)
    (hpre : Pre { P.ctx dm D Γ st' with Δ := Δ' } ρ' (w.st₂.withTempT w.v (some w.T))) :
    Sem.moved ∈ₛ[dm.read] (globalTyS (fun _ => .err) (P.ctx dm D Γ st') w.goal).m :=
  h ρ' Δ' (.moved, Value.tyS ({ P.ctx dm D Γ st' with Δ := Δ' } : RunCtx).dm ({ P.ctx dm D Γ st' with Δ := Δ' } : RunCtx).M
      ({ P.ctx dm D Γ st' with Δ := Δ' } : RunCtx).Γ ρ' w.T) hpre rfl (Or.inr (Or.inl rfl))

/-! ## A constant's decisions: before its entry and after (docs/31 D256)

`checkDef` appends a constant's entry to Σ only after its body's check, so the state its body's run ends in (`w.st₂`,
`grows_eval`: an evaluation keeps Σ) lacks the constant, while the state after the item (`st'`) has it. The checker's own
decision on the constant's name differs between the two, so `DecTab (D st') w.st₂`, which lead43's `ConstStartAt`
asserted, is false at every constant whose name is read as more than `.any`: at `def one : Nat := S(Z)` the reading is
`.any` before and `.other` after. Repaired: the constant's body is simulated at `P.ctx … w.st₂`
(`ConstStartAt`, `ConstLeafAt`, `ConstMeanAt`). -/

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt)

/-- Σ after `def one : Nat := S(Z)` from the empty Σ. -/
def stOne : MState := outSt (checkItem (.defn ProgSanity.oneDef)) {} 100000

#guard isOk (checkItem (.defn ProgSanity.oneDef)) {} 100000
#guard (stOne.globals.map (·.name)) == ["one"]
-- the state its body's run ends in has the empty Σ: the name reads as `.any` there
#guard (checkerDecisions₀ ({} : MState) 100).declOf [] (.const "one") matches .any
-- after the item it is a global, read by its stored type: not `.any`
#guard (checkerDecisions₀ stOne 100).declOf [] (.const "one") matches .other

end Ochr.Meaning.Steps.Form.Top.Attack
