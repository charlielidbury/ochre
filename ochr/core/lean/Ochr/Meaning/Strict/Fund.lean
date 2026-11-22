import Ochr.Meaning.Strict.Clauses2

/-!
# THE FUNDAMENTAL LEMMA (on the strict run `runT`)

From a model state whose positions hold members of their types (`SGood`), a successful strict run
returns a member of the type it returns (or `⊥`, or a value with no data at `err`), whose borrow label,
if any, records that type and is live or unread, and leaves such a state (`fund_all`, one induction
over the term). A proof's run means its proposition is true (`erasedS_clause_true`).

Hypotheses: the context (`FundCtx`: the data layer's read lemma, the globals' membership, no data
declaration at `Type₁`) and the embedded values (`Term.valsOk`: the lemma at each `.val`, decision 5).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A `.prim` that is none of the run's primitives fails. -/
theorem runS_prim_other (n : String) (args : List Term) (tl : Bool) (hint : TyS) (s : SState)
    (h1 : ∀ h, ¬ (n = "symm" ∧ args = [h])) (h2 : ∀ h k, ¬ (n = "trans" ∧ args = [h, k]))
    (h3 : ∀ h u, ¬ (n = "rewrite" ∧ args = [h, u])) (h4 : ∀ h u, ¬ (n = "rewriteR" ∧ args = [h, u]))
    (h5 : ∀ A a b P h t, ¬ (n = "J" ∧ args = [A, a, b, P, h, t]))
    (h6 : ∀ u, ¬ (n = "clone" ∧ args = [u])) (h7 : ∀ u, ¬ (n = "peek" ∧ args = [u]))
    (h8 : ∀ u, ¬ (n = "inplace" ∧ args = [u])) (h9 : ∀ f u, ¬ (n = "split" ∧ args = [.const f, u])) :
    runT K ρ φ tl hint (.prim n args) s = none := by
  rw [runT]
  · rfl
  · exact fun h e1 e2 => h1 h ⟨e1, e2⟩
  · exact fun h k e1 e2 => h2 h k ⟨e1, e2⟩
  · exact fun h u e1 e2 => h3 h u ⟨e1, e2⟩
  · exact fun h u e1 e2 => h4 h u ⟨e1, e2⟩
  · exact fun A a b P h t e1 e2 => h5 A a b P h t ⟨e1, e2⟩
  · exact fun u e1 e2 => h6 u ⟨e1, e2⟩
  · exact fun u e1 e2 => h7 u ⟨e1, e2⟩
  · exact fun u e1 e2 => h8 u ⟨e1, e2⟩
  · exact fun f u e1 e2 => h9 f u ⟨e1, e2⟩
/-- The `.prim` clauses: the four equality rules, `J`, the in-place reads, `split f in u` (its term's run, docs/31
D175), and failure otherwise. -/
theorem fund_prim (hc : FundCtx K) (n : String) (args : List Term) (ha : ∀ t ∈ args, Fund K ρ φ t) :
    Fund K ρ φ (.prim n args) := by
  by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
  · obtain ⟨h, rfl, rfl⟩ := e1; exact fund_symm h
  by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
  · obtain ⟨h, k, rfl, rfl⟩ := e2; exact fund_trans h k
  by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
  · obtain ⟨h, u, rfl, rfl⟩ := e3; exact fund_rewrite h u
  by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
  · obtain ⟨h, u, rfl, rfl⟩ := e4; exact fund_rewriteR h u
  by_cases e5 : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
  · obtain ⟨A, a, b, P, h, t, rfl, rfl⟩ := e5; exact fund_J hc (ha t (by simp))
  by_cases e6 : ∃ u, n = "clone" ∧ args = [u]
  · obtain ⟨u, rfl, rfl⟩ := e6
    intro tl hint s s' r hs h; rw [runT] at h; exact fund_inPlace hc (ha u (by simp)) tl hint s s' r hs h
  by_cases e7 : ∃ u, n = "peek" ∧ args = [u]
  · obtain ⟨u, rfl, rfl⟩ := e7
    intro tl hint s s' r hs h; rw [runT] at h; exact fund_inPlace hc (ha u (by simp)) tl hint s s' r hs h
  by_cases e8 : ∃ u, n = "inplace" ∧ args = [u]
  · obtain ⟨u, rfl, rfl⟩ := e8
    intro tl hint s s' r hs h; rw [runT] at h; exact fund_inPlace hc (ha u (by simp)) tl hint s s' r hs h
  by_cases e9 : ∃ f u, n = "split" ∧ args = [.const f, u]
  · obtain ⟨f, u, rfl, rfl⟩ := e9
    intro tl hint s s' r hs h; rw [runT] at h; exact fund_erasedS (ha u (by simp) tl hint) s s' r hs h
  intro tl hint s s' r hs h
  rw [runS_prim_other n args tl hint s (fun h e => e1 ⟨h, e⟩) (fun h k e => e2 ⟨h, k, e⟩)
    (fun h u e => e3 ⟨h, u, e⟩) (fun h u e => e4 ⟨h, u, e⟩) (fun A a b P h t e => e5 ⟨A, a, b, P, h, t, e⟩)
    (fun u e => e6 ⟨u, e⟩) (fun u e => e7 ⟨u, e⟩) (fun u e => e8 ⟨u, e⟩) (fun f u e => e9 ⟨f, u, e⟩)] at h
  cases h

variable (K ρ φ) in
/-- The precondition on embedded values (decision 5): the lemma at each `.val`. -/
abbrev ValsP : Value → Prop := fun v => Fund K ρ φ (.val v)

mutual
/-- **THE FUNDAMENTAL LEMMA.** From a good state, every successful strict run of a term (at any hint,
in or out of tail position) returns a good result, its label recording its type and live or unread,
and leaves a good state; given the context (`FundCtx`) and the lemma at the term's embedded values. -/
theorem fund_all (hc : FundCtx K) : ∀ (t : Term), t.valsOk (ValsP K ρ φ) → Fund K ρ φ t
  | .place p, _ => fund_place hc p
  | .borrow p, _ => fund_borrow hc p
  | .assign _ u, h => fund_assign hc (fund_all hc u h)
  | .letIn _ u w, h => fund_letIn hc (fund_all hc u h.1) (fund_all hc w h.2)
  | .seq u w, h => fund_seq (fund_all hc u h.1) (fund_all hc w h.2)
  | .matchNat _ z u, h => fund_matchNat hc (fund_all hc z h.1) (fund_all hc u h.2)
  | .const n, _ => fund_const hc n
  | .val _, h => h
  | .sort l, _ => fund_sort l
  | .pi hs ds c, _ => fund_pi hs ds c
  | .fix .., _ => fund_fix hc
  | .call f args _, h => fund_call hc (fund_all hc f h.1) (fund_list hc args h.2)
  | .nat, _ => fund_nat
  | .zero, _ => fund_zero
  | .succ u, h => fund_succ (fund_all hc u h)
  | .unit, _ => fund_unit
  | .tt, _ => fund_tt
  | .eq A a b, _ => fund_eq A a b
  | .cong f h, _ => fund_cong f h
  | .ref A, h => fund_ref (fund_all hc A h)
  | .id A t u, _ => fund_id A t u
  | .ascribe u _, h => fund_ascribe (fund_all hc u h.1)
  | .prim n args, h => fund_prim hc n args (fund_list hc args h)
  | .tind n args, _ => fund_tind hc n args
  | .ctor _ _ _ _ args, h => fund_ctor (fund_list hc args h.2)
  | .matchInd _ _ arms, h => fund_matchInd hc (fund_arms hc arms h)
termination_by structural t => t

theorem fund_list (hc : FundCtx K) : ∀ (ts : List Term), Term.valsOkList (ValsP K ρ φ) ts → ∀ t ∈ ts, Fund K ρ φ t
  | [], _ => fun _ h' => absurd h' List.not_mem_nil
  | t :: ts, h => fun t' h' =>
    (List.mem_cons.mp h').elim (fun e => e ▸ fund_all hc t h.1) (fun h' => fund_list hc ts h.2 t' h')
termination_by structural ts => ts

theorem fund_arms (hc : FundCtx K) : ∀ (arms : List (Hint × Term)), Term.valsOkArms (ValsP K ρ φ) arms →
    ∀ a ∈ arms, Fund K ρ φ a.2
  | [], _ => fun _ h' => absurd h' List.not_mem_nil
  | (x, t) :: ts, h => fun a h' =>
    (List.mem_cons.mp h').elim (fun e => e ▸ fund_all hc t h.1) (fun h' => fund_arms hc ts h.2 a h')
termination_by structural arms => arms
end

end

end Ochr.Meaning.Strict
