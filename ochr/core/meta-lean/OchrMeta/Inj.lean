import OchrMeta.WF
import OchrMeta.Close

/-! # Lemmas 3 and 4 (injectivity), first-order form

In the model, a call returning a borrow into its arguments has a *backward function* from the
final value `w` the caller leaves in the returned borrow to the final contents of the borrowed
places; [Call-type] is sound only if the caller's context around those contents is jointly
injective in `w` (meta-model-v1 §2.4).  In the machine the backward function is literally
substitution: after the call the environment holds `loan_q` where the returned borrow `q` will
land, and ending `q` substitutes its final value (`close_back` shows the sealed programs compute
the same).  So:

* **Lemma 4 (`back_inj`)**: the backward function is injective because `loan_q` occurs in the
  environment: no rule discards a returned borrow's loan (Lemma 0's `owned` invariant).
* **Lemma 3 (`ctx_inj`)**: the owners' contexts are jointly injective provided the observed owners
  include one that contains `loan_q`; observing only owners that do not contain it gives a
  constant context (`ctx_needs_all_owners`, meta-model C2). -/

namespace OchrMeta

/-- Substituting into an occurrence is injective. -/
theorem Val.substLoan_inj {q : Nat} {w₁ w₂ : Val} :
    ∀ {v : Val}, q ∈ v.loans → Val.substLoan q w₁ v = Val.substLoan q w₂ v → w₁ = w₂ := by
  intro v hq h
  induction v with
  | loan m =>
    simp [Val.loans] at hq; subst hq
    simpa [Val.substLoan] using h
  | succ v ih => exact ih (by simpa [Val.loans] using hq) (by simpa [Val.substLoan] using h)
  | borrow m v ih => exact ih (by simpa [Val.loans] using hq) (by simpa [Val.substLoan] using h)
  | pair a b iha ihb =>
    simp only [Val.substLoan, Val.pair.injEq] at h
    simp only [Val.loans, List.mem_append] at hq
    rcases hq with hq | hq
    · exact iha hq h.1
    · exact ihb hq h.2
  | sealed g a k x iha ihx =>
    simp only [Val.substLoan, Val.sealed.injEq] at h
    simp only [Val.loans, List.mem_append] at hq
    rcases hq with hq | hq
    · exact iha hq h.2.1
    · exact ihx hq h.2.2.2
  | _ => simp [Val.loans] at hq

/-- The context of a set `W` of owners around the loan `q`: their contents with `q := w`. -/
def ctx (E : Env) (W : List Var) (q : Nat) (w : Val) : List (Option Val) :=
  W.map fun o => ((E.head?.getD []).lookup o).map (Val.substLoan q w)

/-- **Lemma 3.**  The owners' context is injective in the returned borrow's final value as soon as
one observed owner contains its loan. -/
theorem ctx_inj {E : Env} {W : List Var} {q : Nat} {o : Var} {c : Val} (ho : o ∈ W)
    (hc : (E.head?.getD []).lookup o = some c) (hq : q ∈ c.loans) : Function.Injective (ctx E W q) := by
  intro w₁ w₂ h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
  have := congrArg (fun L => L[i]?) h
  simp only [ctx, List.getElem?_map, hi, Option.map_some, hc, Option.some.injEq] at this
  exact Val.substLoan_inj hq this

/-- **C2 (negative).**  If no observed owner contains the loan, the context is constant: observing a
proper subset of the owners is unsound for [Call-type]. -/
theorem ctx_needs_all_owners {E : Env} {W : List Var} {q : Nat}
    (hW : ∀ o ∈ W, ∀ c, (E.head?.getD []).lookup o = some c → q ∉ c.loans) (w₁ w₂ : Val) :
    ctx E W q w₁ = ctx E W q w₂ := by
  simp only [ctx]
  apply List.map_congr_left
  intro o ho
  cases h : (E.head?.getD []).lookup o with
  | none => rfl
  | some c => simp [Val.substLoan_of_not_mem c (hW o ho c h)]

theorem Env.substLoan_inj {E : Env} {q : Nat} (hq : q ∈ E.loans) :
    Function.Injective (fun w => E.substLoan q w) := by
  intro w₁ w₂ h
  obtain ⟨F, hF, b, hb, hqb⟩ := Env.mem_loans'.mp hq
  have hF' : Frame.mapVals (Val.substLoan q w₁) F = Frame.mapVals (Val.substLoan q w₂) F := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hF
    have h2 := congrArg (fun E' : Env => E'[i]?) h
    simp only [Env.substLoan, Env.mapVals, List.getElem?_map, hi, Option.map_some, Option.some.injEq] at h2
    exact h2
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have h3 := congrArg (fun F' : Frame => F'[j]?) hF'
  simp only [Frame.mapVals, List.getElem?_map, hj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h3
  exact Val.substLoan_inj hqb h3.2

/-- **Lemma 4 (backward functions are injective).**  In a well-formed state with a returned borrow
`borrow_q c` in flight, the environment's dependence on the value finally written through that
borrow (ending `q` substitutes it for every `loan_q`) is injective: the loan occurs somewhere,
because no rule discards a live borrow's loan (Lemma 0, `owned`). -/
theorem back_inj {s : St} {q : Nat} {c : Val} (h : WFv s [.borrow q c]) :
    Function.Injective (fun w => s.env.substLoan q w) :=
  Env.substLoan_inj (h.owned q (by simp [Val.held]))

end OchrMeta
