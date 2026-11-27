import Ochr.Meaning.Steps.FrameSimple

/-!
# The frame property, by induction over the term (lead35; docs/31 D225)

`RunFrameI` for every term with no function formed in the body and no `Id` (`Term.frameFree`: no `.fix`, no `.pi`, no
`.id`): the clause lemmas assembled by structural induction over the term, its lists and a match's arms, as the strict
fundamental lemma's `Strict.fund_all` is. The excluded forms are ruling R2's and R7's (a closure or a function type
formed in the body, hosted by the structural frame) and `Id`'s (the observation, ruling R3).
-/

namespace Ochr

mutual
/-- A term with no function formed in it (`.fix`), no function type (`.pi`) and no `Id` (outside embedded values,
whose meanings are their own runs). -/
def Term.frameFree : Term → Bool
  | .id .. | .fix .. | .pi .. => false
  | .assign _ t | .succ t | .ref t => t.frameFree
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => t.frameFree && u.frameFree
  | .matchNat _ z s => z.frameFree && s.frameFree
  | .call f as _ => f.frameFree && Term.frameFreeList as
  | .eq a b c => a.frameFree && b.frameFree && c.frameFree
  | .ctor _ _ _ ps as => Term.frameFreeList ps && Term.frameFreeList as
  | .prim _ as | .tind _ as => Term.frameFreeList as
  | .matchInd _ _ as => Term.frameFreeArms as
  | _ => true
termination_by structural t => t

def Term.frameFreeList : List Term → Bool
  | [] => true
  | a :: as => a.frameFree && Term.frameFreeList as
termination_by structural as => as

def Term.frameFreeArms : List (Hint × Term) → Bool
  | [] => true
  | (_, a) :: as => a.frameFree && Term.frameFreeArms as
termination_by structural as => as
end

end Ochr

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

mutual
/-- **The frame property at every term with no function formed in it and no `Id`** (the induction over `runT`, one
clause lemma per form). -/
theorem termFrame_all (hc : FundCtx K) (hs₀ : FrameStart s₀ ks) :
    ∀ (t : Term), t.frameFree = true → t.valsOk (ValsP K ρ φ) → TermFrame K ρ φ σ s₀ ks t
  | .place p, _, _ => runFrameI_place hs₀ p
  | .borrow p, _, _ => runFrameI_borrow hs₀ p
  | .assign _ u, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_assign hs₀ (fund_all hc u hv) (termFrame_all hc hs₀ u hf hv)
  | .letIn _ u w, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_letIn hs₀ (fund_all hc u hv.1) (termFrame_all hc hs₀ u hf.1 hv.1) (termFrame_all hc hs₀ w hf.2 hv.2)
  | .seq u w, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_seq hs₀ (termFrame_all hc hs₀ u hf.1 hv.1) (termFrame_all hc hs₀ w hf.2 hv.2)
  | .matchNat _ z u, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_matchNat (fun n => (hc.globals n).2) hs₀ (termFrame_all hc hs₀ z hf.1 hv.1)
      (termFrame_all hc hs₀ u hf.2 hv.2)
  | .matchInd _ _ arms, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_matchInd (fun n => (hc.globals n).2) hs₀ (termFrame_arms hc hs₀ arms hf hv)
  | .const n, _, _ => runFrameI_const (fun n => (hc.globals n).2) n
  | .val v, _, _ => runFrameI_val v
  | .sort _, _, _ => runFrameI_sort
  | .pi .., hf, _ => by simp [Term.frameFree] at hf
  | .fix .., hf, _ => by simp [Term.frameFree] at hf
  | .id .., hf, _ => by simp [Term.frameFree] at hf
  | .call f args _, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_call hs₀ (termFrame_all hc hs₀ f hf.1 hv.1) (termFrame_list hc hs₀ args hf.2 hv.2)
  | .nat, _, _ => runFrameI_nat
  | .zero, _, _ => runFrameI_zero
  | .succ u, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_succ (termFrame_all hc hs₀ u hf hv)
  | .unit, _, _ => runFrameI_unit
  | .tt, _, _ => runFrameI_tt
  | .eq A a b, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_eq (termFrame_all hc hs₀ A hf.1.1 hv.1) (termFrame_all hc hs₀ a hf.1.2 hv.2.1)
      (termFrame_all hc hs₀ b hf.2 hv.2.2)
  | .cong _ h, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_cong (termFrame_all hc hs₀ h hf.2 hv.2)
  | .ref A, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_ref (termFrame_all hc hs₀ A hf hv)
  | .ascribe u A, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_ascribe (termFrame_all hc hs₀ u hf.1 hv.1) (termFrame_all hc hs₀ A hf.2 hv.2)
  | .prim _ args, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_prim hs₀ (termFrame_list hc hs₀ args hf hv)
  | .tind _ args, hf, hv => by
    simp only [Term.frameFree] at hf
    exact runFrameI_tind (termFrame_list hc hs₀ args hf hv)
  | .ctor _ _ _ ps args, hf, hv => by
    simp only [Term.frameFree, Bool.and_eq_true] at hf
    exact runFrameI_ctor (termFrame_list hc hs₀ ps hf.1 hv.1) (termFrame_list hc hs₀ args hf.2 hv.2)
termination_by structural t => t

theorem termFrame_list (hc : FundCtx K) (hs₀ : FrameStart s₀ ks) :
    ∀ (ts : List Term), Term.frameFreeList ts = true → Term.valsOkList (ValsP K ρ φ) ts →
      ∀ t ∈ ts, TermFrame K ρ φ σ s₀ ks t
  | [], _, _ => fun _ h' => absurd h' List.not_mem_nil
  | t :: ts, hf, hv => by
    simp only [Term.frameFreeList, Bool.and_eq_true] at hf
    exact fun t' h' => (List.mem_cons.mp h').elim (fun e => e ▸ termFrame_all hc hs₀ t hf.1 hv.1)
      (fun h' => termFrame_list hc hs₀ ts hf.2 hv.2 t' h')
termination_by structural ts => ts

theorem termFrame_arms (hc : FundCtx K) (hs₀ : FrameStart s₀ ks) :
    ∀ (arms : List (Hint × Term)), Term.frameFreeArms arms = true → Term.valsOkArms (ValsP K ρ φ) arms →
      ∀ a ∈ arms, TermFrame K ρ φ σ s₀ ks a.2
  | [], _, _ => fun _ h' => absurd h' List.not_mem_nil
  | (x, t) :: ts, hf, hv => by
    simp only [Term.frameFreeArms, Bool.and_eq_true] at hf
    exact fun a h' => (List.mem_cons.mp h').elim (fun e => e ▸ termFrame_all hc hs₀ t hf.1 hv.1)
      (fun h' => termFrame_arms hc hs₀ ts hf.2 hv.2 a h')
termination_by structural arms => arms
end

end

/-- **`RunFrameI` for every term with no function formed in the body and no `Id`** (the brief's task 2; the paper's
frame property (FR) on that fragment, over the internal relation): from related states, the in-place run and the
closure's run agree. Hypotheses: the run's context (`FundCtx`: globals are members with no label, no data declaration
at `Type₁`), the call point (`FrameStart`), the term's embedded values good (`valsOk`), the internal relation at the
start. -/
theorem runFrameI_frameFree (K : RunCtx) (ρ : Assignment) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat)
    (tl : Bool) (hint : TyS) (t : Term) (s s' : SState) (hc : FundCtx K) (hs₀ : FrameStart s₀ ks)
    (hv : t.valsOk (ValsP K ρ φ)) (hf : t.frameFree = true) (hI : FrameInv K φ σ s₀ ks s s') :
    FrameAgreeI K φ σ s₀ ks (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s') :=
  termFrame_all hc hs₀ t hf hv tl hint s s' hI

end Ochr.Meaning.Steps.Form.FrameEnd
