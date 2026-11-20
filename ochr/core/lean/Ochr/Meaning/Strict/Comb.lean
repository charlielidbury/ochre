import Ochr.Meaning.Strict.OpsPlace

/-!
# The fundamental lemma: what it takes of the context, and the combinators

`FundCtx`: the data layer's read lemma (`MemReads`), the globals' membership, and no declaration at
`Type₁` (the model reads every data declaration as a `Type₀` code). `ValsOk`: the orchestrator's
decision 5, a precondition on the TERM: each embedded value satisfies the lemma at its `.val`
(discharged by the simulation from an invariant on the code the state holds).

The combinators: a strict clause owes only the state and its label (`fund_strictS`); an erased term
owes its clause's lemma, and is `⋆` at `prop True` (`fund_erasedS`); a statement position runs on a
copy (`fund_stmtIf`).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

/-- **What the fundamental lemma takes of the context.** -/
structure FundCtx (K : RunCtx) : Prop where
  /-- the data layer's read lemma (`ReadMember.follow_below_member` under `ReadCoherent`) -/
  reads : MemReads K.dm K.Γ
  /-- each global's meaning is a member of its type, and holds no borrow (`CtxOk.globals`) -/
  globals : ∀ n, GoodRes K.dm.read (K.C.global n) ∧ (K.C.global n).2.label = none
  /-- no data declaration at `Type₁` (the model reads a data declaration as a `Type₀` code) -/
  sorts : ∀ d ∈ K.Γ, d.sort ≠ 2

mutual
/-- Every value embedded in the term (not inside another value) satisfies `P`. -/
def _root_.Ochr.Term.valsOk (P : Value → Prop) : Term → Prop
  | .val v => P v
  | .assign _ t | .succ t | .ref t => t.valsOk P
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.valsOk P ∧ u.valsOk P
  | .matchNat _ z s => z.valsOk P ∧ s.valsOk P
  | .pi _ ds c => Term.valsOkList P ds ∧ c.valsOk P
  | .fix _ _ ds c _ b => Term.valsOkList P ds ∧ c.valsOk P ∧ b.valsOk P
  | .call f as _ => f.valsOk P ∧ Term.valsOkList P as
  | .eq a b c | .id a b c => a.valsOk P ∧ b.valsOk P ∧ c.valsOk P
  | .prim _ as | .tind _ as => Term.valsOkList P as
  | .ctor _ _ _ ps as => Term.valsOkList P ps ∧ Term.valsOkList P as
  | .matchInd _ _ arms => Term.valsOkArms P arms
  | _ => True
termination_by structural t => t

def _root_.Ochr.Term.valsOkList (P : Value → Prop) : List Term → Prop
  | [] => True
  | t :: ts => t.valsOk P ∧ Term.valsOkList P ts
termination_by structural ts => ts

def _root_.Ochr.Term.valsOkArms (P : Value → Prop) : List (Hint × Term) → Prop
  | [] => True
  | (_, t) :: ts => t.valsOk P ∧ Term.valsOkArms P ts
termination_by structural ts => ts
end

theorem _root_.Ochr.Term.valsOkList_mem {P : Value → Prop} : ∀ {ts : List Term}, Term.valsOkList P ts → ∀ t ∈ ts, t.valsOk P
  | [], _, _, h => absurd h List.not_mem_nil
  | t :: ts, ⟨h1, h2⟩, t', h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact h1
    · exact Term.valsOkList_mem h2 t' h

section
variable {dm : DataModel} {Γ : List IndDecl} {φ : Future}

/-- A run keeps the invariant, and its result's label records its type and is live or unread. -/
def PresLab (dm : DataModel) (Γ : List IndDecl) (φ : Future) (x : SM Res) : Prop :=
  ∀ s s' r, SGood dm Γ φ s → x s = some (r, s') → LabOk dm s' r ∧ LoU s' r.2.label ∧ SGood dm Γ φ s'

theorem FundAt.presLab {x : SM Res} (h : FundAt dm Γ φ x) : PresLab dm Γ φ x :=
  fun s s' r hs hx => (h s s' r hs hx).2

theorem ite_none_some {α : Type _} {p : Prop} [Decidable p] {a : Option α} {b : α}
    (h : (if p then a else none) = some b) : p ∧ a = some b := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact ⟨hp, h⟩
  · rw [if_neg hp] at h; cases h

theorem strictS_some {R : DataRead} {x : SM Res} {s s' : SState} {r : Res} (h : SM.strictS R x s = some (r, s')) :
    x s = some (r, s') ∧ r.1 ∈ₛ[R] r.2.m := by
  unfold SM.strictS at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p =>
    rw [hx] at h
    obtain ⟨r0, s0⟩ := p
    simp only at h
    by_cases hm : r0.1 ∈ₛ[R] r0.2.m
    · rw [if_pos hm] at h; cases h; exact ⟨rfl, hm⟩
    · rw [if_neg hm] at h; cases h

/-- **A strict clause**: its result is a member by its test. -/
theorem fund_strictS {x : SM Res} (hx : PresLab dm Γ φ x) : FundAt dm Γ φ (SM.strictS dm.read x) := by
  intro s s' r hs h
  obtain ⟨h, hm⟩ := strictS_some h
  exact ⟨.inl hm, hx s s' r hs h⟩

theorem proof_mem_true (R : DataRead) : Sem.proof ∈ₛ[R] TyM.prop True := ⟨⟨trivial⟩, rfl⟩

/-- An erased proof's run, taken apart: its clause ran (on a copy) to `⋆`. -/
theorem erasedS_proof_some {fl : Bool × Bool} {x : SM Res} {s s' : SState} {r : Res} (hp : fl.2 = true)
    (h : SM.erasedS fl x s = some (r, s')) :
    ∃ T s₁, x s = some ((.proof, T), s₁) ∧ r = (.proof, .plain (TyM.prop True)) ∧ s' = s := by
  unfold SM.erasedS at h
  rw [if_pos hp] at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p =>
    rw [hx] at h
    obtain ⟨⟨v, T⟩, s₁⟩ := p
    simp only at h
    by_cases ht : v.isProof = true
    · rw [if_pos ht] at h
      cases h
      have hv : v = .proof := by cases v <;> simp_all [Sem.isProof]
      subst hv
      exact ⟨T, s₁, rfl, rfl, rfl⟩
    · rw [if_neg ht] at h; cases h

/-- **A proof's run means its proposition is true**: where the clause obeys the lemma, an erased proof
that runs ran its clause to `⋆` at a type of which `⋆` is a member, or at `err` (a field of `⋆`). -/
theorem erasedS_clause_true {fl : Bool × Bool} {x : SM Res} (hx : FundAt dm Γ φ x) (hp : fl.2 = true)
    {s s' : SState} {r : Res} (hs : SGood dm Γ φ s) (h : SM.erasedS fl x s = some (r, s')) :
    ∃ T s₁, x s = some ((.proof, T), s₁) ∧ (Sem.proof ∈ₛ[dm.read] T.m ∨ T.m = TyM.err) := by
  obtain ⟨T, s₁, hx₁, -, -⟩ := erasedS_proof_some hp h
  refine ⟨T, s₁, hx₁, ?_⟩
  rcases (hx s s₁ _ hs hx₁).1 with hg | hg | ⟨he, -⟩
  · exact .inl hg
  · cases hg
  · exact .inr he

/-- **An erased term**: a proof is `⋆` at `prop True`, the state unchanged; a statement is its
clause's, label dropped, the state unchanged; otherwise the clause itself. -/
theorem fund_erasedS {fl : Bool × Bool} {x : SM Res} (hx : FundAt dm Γ φ x) : FundAt dm Γ φ (SM.erasedS fl x) := by
  intro s s' r hs h
  by_cases hp : fl.2 = true
  · obtain ⟨T, s₁, -, rfl, hss⟩ := erasedS_proof_some hp h
    exact ⟨.inl (proof_mem_true _), (fun l hl => by cases hl), (fun l hl => by cases hl), hss ▸ hs⟩
  · have h' : SM.stmtIf fl.1 x s = some (r, s') := by
      unfold SM.erasedS at h; rw [if_neg hp] at h; exact h
    rcases SM.stmtIf_some h' with ⟨-, h'⟩ | ⟨-, hss, hl, r₀, s₀, h0, rfl⟩
    · exact hx s s' r hs h'
    · exact ⟨(hx s s₀ r₀ hs h0).1, (fun l hl' => by cases hl'), (fun l hl' => by cases hl'), hss ▸ hs⟩

end

end Ochr.Meaning.Strict
