import Ochr.Meaning.SitesWrite
import Ochr.Meaning.AccessAbsorb
import Ochr.Meaning.PosLib

/-!
# The checker's sites against its paths, at one position

`Value.sitesOf` records where a borrow is lent in a value, at canonical paths; `Value.follow`
follows a place's path. Two facts tie them, both by the same walk down the value:

* **Nothing exists below a loan** (`loanSite_blocks`): a loan site blocks every path whose key
  strictly extends the site's.
* **A fill's hole has a site at or above the fill** (`site_of_fillHole`): where a path reaches a
  value with a live hole, the hole's borrow has a site at that path or at a mark above it.
-/

namespace Ochr.Meaning

open Ochr.Meaning.Steps

theorem follow_gloan_cons (m : Nat) (w : Value) (s₁ : Step) (ss : List Step) :
    (Value.gloan m w).follow (s₁ :: ss) = w.follow (s₁ :: ss) := by
  simp only [Value.follow, stepV]

/-- A key list that extends a non-empty one comes from a path with the same first key. -/
theorem pathKey_cons_prefix {k : Option (Nat × Nat)} {K : List (Option (Nat × Nat))} {ss : List Step}
    (h : k :: K <+: pathKey ss) (hne : k :: K ≠ pathKey ss) :
    ∃ s₁ ss', ss = s₁ :: ss' ∧ s₁.key = k ∧ K <+: pathKey ss' ∧ K ≠ pathKey ss' := by
  cases ss with
  | nil => obtain ⟨t, ht⟩ := h; simp [pathKey] at ht
  | cons s₁ ss' =>
    simp only [pathKey, List.map_cons] at h hne
    obtain ⟨t, ht⟩ := h
    simp only [List.cons_append, List.cons.injEq] at ht
    refine ⟨s₁, ss', rfl, ht.1.symm, ⟨t, ht.2⟩, fun e => hne ?_⟩
    rw [ht.1, e]; rfl

mutual
/-- **Nothing exists below a loan**: a loan site of `l`, in a value read at `path`, is at
`path ++ ψ₀` and blocks every path whose key strictly extends `ψ₀`'s. -/
theorem loanSite_blocks (l : Nat) (pos : Pos) : ∀ (path : List Step) (v : Value) (x : Site),
    x ∈ Value.sitesOf l pos path v → x.fill = false →
    ∃ ψ₀, x.path = path ++ ψ₀ ∧ ∀ ss, pathKey ψ₀ <+: pathKey ss → pathKey ψ₀ ≠ pathKey ss → v.follow ss = none
  | path, .loan m, x, h, _ => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h
      refine ⟨[], by simp, fun ss _ hne => ?_⟩
      cases ss with
      | nil => exact absurd rfl hne
      | cons s₁ ss' => simp [Value.follow, stepV]
    · cases h
  | path, .gloan m w, x, h, hf => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; cases hf
    · obtain ⟨ψ₀, hx, hb⟩ := loanSite_blocks l pos path w x h hf
      refine ⟨ψ₀, hx, fun ss hpre hne => ?_⟩
      cases ss with
      | nil =>
        have := hpre.length_le
        simp [pathKey] at this
        subst this
        exact absurd rfl hne
      | cons s₁ ss' => rw [follow_gloan_cons]; exact hb _ hpre hne
  | path, .sealed t, x, h, hf => by
    simp only [Value.sitesOf] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; cases hf
    · cases h
  | path, .borrow b w, x, h, hf => by
    simp only [Value.sitesOf] at h
    obtain ⟨ψ₀, hx, hb⟩ := loanSite_blocks l pos (path ++ [.deref]) w x h hf
    refine ⟨.deref :: ψ₀, by rw [hx]; simp, fun ss hpre hne => ?_⟩
    obtain ⟨s₁, ss', rfl, hk, hpre', hne'⟩ := pathKey_cons_prefix hpre hne
    rw [key_none_deref hk]
    simp only [Value.follow, stepV, Option.bind_some]
    exact hb ss' hpre' hne'
  | path, .succ w, x, h, hf => by
    simp only [Value.sitesOf] at h
    obtain ⟨ψ₀, hx, hb⟩ := loanSite_blocks l pos (path ++ [.proj 0]) w x h hf
    refine ⟨.proj 0 :: ψ₀, by rw [hx]; simp, fun ss hpre hne => ?_⟩
    obtain ⟨s₁, ss', rfl, hk, hpre', hne'⟩ := pathKey_cons_prefix hpre hne
    cases s₁ with
    | deref => simp [Step.key] at hk
    | proj i =>
      simp only [Step.key, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      simp only [Value.follow, stepV, Option.bind_some]
      exact hb ss' hpre' hne'
    | field g => simp [Value.follow, stepV]
  | path, .ind ty c hh ps fs, x, h, hf => by
    simp only [Value.sitesOf] at h
    obtain ⟨j, w, hj, ψ₀, hx, hb⟩ := loanSite_blocks_fields l pos path ty c 0 fs x h hf
    refine ⟨.field ⟨ty, c, 0 + j, ""⟩ :: ψ₀, by rw [hx], fun ss hpre hne => ?_⟩
    obtain ⟨s₁, ss', rfl, hk, hpre', hne'⟩ := pathKey_cons_prefix hpre hne
    cases s₁ with
    | deref => simp [Step.key] at hk
    | proj i =>
      simp only [Step.key, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hc, hi⟩ := hk
      subst hc
      simp only [Nat.zero_add] at hi
      subst hi
      simp only [Value.follow, stepV, hj, Option.bind_some]
      exact hb ss' hpre' hne'
    | field g =>
      simp only [Step.key, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hc, hi⟩ := hk
      simp only [Value.follow, stepV]
      split
      · simp only [Nat.zero_add] at hi
        rw [hi, hj, Option.bind_some]
        exact hb ss' hpre' hne'
      · rfl
  | _, .zero, _, h, _ | _, .unit, _, h, _ | _, .gfn _, _, h, _ | _, .clo _ _ _, _, h, _ | _, .bot, _, h, _
  | _, .abs _, _, h, _ | _, .proof, _, h, _ | _, .tNat, _, h, _ | _, .tUnit, _, h, _ | _, .tEq _ _ _, _, h, _
  | _, .tRef _, _, h, _ | _, .tPi _ _ _, _, h, _ | _, .sort _, _, h, _ | _, .tInd _ _, _, h, _ => by
    simp [Value.sitesOf] at h

theorem loanSite_blocks_fields (l : Nat) (pos : Pos) (path : List Step) (ty : String) (c : Nat) :
    ∀ (i : Nat) (ws : List Value) (x : Site), x ∈ Value.sitesOfFields l pos path ty c i ws → x.fill = false →
      ∃ j w, ws[j]? = some w ∧ ∃ ψ₀, x.path = path ++ .field ⟨ty, c, i + j, ""⟩ :: ψ₀ ∧
        ∀ ss, pathKey ψ₀ <+: pathKey ss → pathKey ψ₀ ≠ pathKey ss → w.follow ss = none
  | _, [], x, h, _ => by simp [Value.sitesOfFields] at h
  | i, w :: ws, x, h, hf => by
    simp only [Value.sitesOfFields, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨ψ₀, hx, hb⟩ := loanSite_blocks l pos (path ++ [.field ⟨ty, c, i, ""⟩]) w x h hf
      exact ⟨0, w, rfl, ψ₀, by rw [hx]; simp, hb⟩
    · obtain ⟨j, w', hj, ψ₀, hx, hb⟩ := loanSite_blocks_fields l pos path ty c (i + 1) ws x h hf
      exact ⟨j + 1, w', by simpa using hj, ψ₀, by rw [hx, show i + 1 + j = i + (j + 1) by omega], hb⟩
end

/-! ## A loan in a value's list of loans is one `hasLoan` sees -/

/-- The atoms `hasLoan l` tests. -/
def loanAt (l : Nat) : Value → Bool
  | .loan m | .gloan m _ => m == l
  | _ => false

mutual
theorem anyAtom_of_mem_loans (l : Nat) : ∀ (v : Value), l ∈ v.loans → v.anyAtom (loanAt l) = true
  | .loan m, h => by
    simp only [Value.loans, List.mem_singleton] at h; subst h; simp [Value.anyAtom, loanAt]
  | .gloan m w, h => by
    simp only [Value.loans, List.mem_cons] at h
    rcases h with rfl | h
    · simp [Value.anyAtom, loanAt]
    · rw [Value.anyAtom]; simp [anyAtom_of_mem_loans l w h]
  | .succ w, h | .tRef w, h | .borrow _ w, h => by
    simp only [Value.loans] at h; rw [Value.anyAtom]; simp [anyAtom_of_mem_loans l w h]
  | .tEq A a b, h => by
    simp only [Value.loans, List.mem_append] at h
    rw [Value.anyAtom]
    rcases h with (h | h) | h
    · simp [anyAtom_of_mem_loans l A h]
    · simp [anyAtom_of_mem_loans l a h]
    · simp [anyAtom_of_mem_loans l b h]
  | .clo cs t rd, h | .tPi cs t rd, h => by
    simp only [Value.loans, List.mem_append] at h
    rw [Value.anyAtom]
    rcases h with h | h
    · simp [anyAtomList_of_mem_loans l cs h]
    · simp [Term_anyAtom_of_mem_loans l t h]
  | .sealed t, h => by
    simp only [Value.loans] at h; rw [Value.anyAtom]; simp [Term_anyAtom_of_mem_loans l t h]
  | .ind _ _ _ ps fs, h => by
    simp only [Value.loans, List.mem_append] at h
    rw [Value.anyAtom]
    rcases h with h | h
    · simp [anyAtomList_of_mem_loans l ps h]
    · simp [anyAtomList_of_mem_loans l fs h]
  | .tInd _ fs, h => by
    simp only [Value.loans] at h; rw [Value.anyAtom]; simp [anyAtomList_of_mem_loans l fs h]
  | .zero, h | .unit, h | .gfn _, h | .bot, h | .abs _, h | .proof, h | .tNat, h | .tUnit, h
  | .sort _, h => by simp [Value.loans] at h

theorem anyAtomList_of_mem_loans (l : Nat) : ∀ (vs : List Value), l ∈ Value.loansList vs →
    Value.anyAtomList (loanAt l) vs = true
  | [], h => by simp [Value.loansList] at h
  | v :: vs, h => by
    simp only [Value.loansList, List.mem_append] at h
    rw [Value.anyAtomList]
    rcases h with h | h
    · simp [anyAtom_of_mem_loans l v h]
    · simp [anyAtomList_of_mem_loans l vs h]

theorem Term_anyAtom_of_mem_loans (l : Nat) : ∀ (t : Term), l ∈ t.loans → t.anyAtom (loanAt l) = true
  | .val v, h => by simp only [Term.loans] at h; rw [Term.anyAtom]; exact anyAtom_of_mem_loans l v h
  | .assign _ t, h | .succ t, h | .ref t, h => by
    simp only [Term.loans] at h; rw [Term.anyAtom]; exact Term_anyAtom_of_mem_loans l t h
  | .letIn _ t u, h | .seq t u, h | .cong t u, h | .ascribe t u, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with h | h
    · simp [Term_anyAtom_of_mem_loans l t h]
    · simp [Term_anyAtom_of_mem_loans l u h]
  | .matchNat _ z s, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with h | h
    · simp [Term_anyAtom_of_mem_loans l z h]
    · simp [Term_anyAtom_of_mem_loans l s h]
  | .pi _ ds c, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with h | h
    · simp [Term_anyAtomList_of_mem_loans l ds h]
    · simp [Term_anyAtom_of_mem_loans l c h]
  | .fix _ _ ds c _ b, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with (h | h) | h
    · simp [Term_anyAtomList_of_mem_loans l ds h]
    · simp [Term_anyAtom_of_mem_loans l c h]
    · simp [Term_anyAtom_of_mem_loans l b h]
  | .call f as _, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with h | h
    · simp [Term_anyAtom_of_mem_loans l f h]
    · simp [Term_anyAtomList_of_mem_loans l as h]
  | .eq a b c, h | .id a b c, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with (h | h) | h
    · simp [Term_anyAtom_of_mem_loans l a h]
    · simp [Term_anyAtom_of_mem_loans l b h]
    · simp [Term_anyAtom_of_mem_loans l c h]
  | .ctor _ _ _ ps as, h => by
    simp only [Term.loans, List.mem_append] at h
    rw [Term.anyAtom]
    rcases h with h | h
    · simp [Term_anyAtomList_of_mem_loans l ps h]
    · simp [Term_anyAtomList_of_mem_loans l as h]
  | .prim _ as, h | .tind _ as, h => by
    simp only [Term.loans] at h; rw [Term.anyAtom]; exact Term_anyAtomList_of_mem_loans l as h
  | .matchInd _ _ as, h => by
    simp only [Term.loans] at h; rw [Term.anyAtom]; exact Term_anyAtomArms_of_mem_loans l as h
  | .place _, h | .borrow _, h | .const _, h | .sort _, h | .nat, h | .zero, h | .unit, h | .tt, h => by
    simp [Term.loans] at h

theorem Term_anyAtomList_of_mem_loans (l : Nat) : ∀ (ts : List Term), l ∈ Term.loansList ts →
    Term.anyAtomList (loanAt l) ts = true
  | [], h => by simp [Term.loansList] at h
  | t :: ts, h => by
    simp only [Term.loansList, List.mem_append] at h
    rw [Term.anyAtomList]
    rcases h with h | h
    · simp [Term_anyAtom_of_mem_loans l t h]
    · simp [Term_anyAtomList_of_mem_loans l ts h]

theorem Term_anyAtomArms_of_mem_loans (l : Nat) : ∀ (as : List (Hint × Term)), l ∈ Term.loansArms as →
    Term.anyAtomArms (loanAt l) as = true
  | [], h => by simp [Term.loansArms] at h
  | (_, t) :: as, h => by
    simp only [Term.loansArms, List.mem_append] at h
    rw [Term.anyAtomArms]
    rcases h with h | h
    · simp [Term_anyAtom_of_mem_loans l t h]
    · simp [Term_anyAtomArms_of_mem_loans l as h]
end

theorem hasLoan_of_mem_loans {l : Nat} {v : Value} (h : l ∈ v.loans) : v.hasLoan l = true := by
  have := anyAtom_of_mem_loans l v h
  unfold Value.hasLoan
  refine (congrArg (fun P => v.anyAtom P) ?_).trans this
  funext x; cases x <;> rfl

/-- A closure or Π-type recording a declared type that holds `l` (docs/31 D46). -/
def rdHasLoan (l : Nat) : Value → Bool
  | .clo _ _ rd | .tPi _ _ rd => Value.anyAtomRd (loanAt l) rd
  | _ => false

mutual
/-- **The converse of `anyAtom_of_mem_loans`, outside recorded readings**: a loan or mark of `l`
that `hasLoan` sees is in `loans`, unless it sits in a closure's recorded declared type, which
`loans` does not walk. -/
theorem mem_loans_of_anyAtom (l : Nat) : ∀ (v : Value), v.anyAtom (rdHasLoan l) = false →
    v.anyAtom (loanAt l) = true → l ∈ v.loans
  | .loan m, _, h => by
    simp only [Value.anyAtom, loanAt, Bool.or_false, beq_iff_eq] at h; subst h; simp [Value.loans]
  | .gloan m w, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Value.loans, List.mem_cons]
    rcases h with h | h
    · left; simp only [loanAt, beq_iff_eq] at h; exact h.symm
    · exact .inr (mem_loans_of_anyAtom l w hr.2 h)
  | .succ w, hr, h | .tRef w, hr, h | .borrow _ w, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans]; exact mem_loans_of_anyAtom l w hr h
  | .tEq A a b, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (.inl (mem_loans_of_anyAtom l A hr.1.1 h))
    · exact .inl (.inr (mem_loans_of_anyAtom l a hr.1.2 h))
    · exact .inr (mem_loans_of_anyAtom l b hr.2 h)
  | .clo cs t rd, hr, h | .tPi cs t rd, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (mem_loansList_of_anyAtom l cs hr.2.1.1 h)
    · exact .inr (Term_mem_loans_of_anyAtom l t hr.2.1.2 h)
    · rw [hr.1] at h; cases h
  | .sealed t, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans]; exact Term_mem_loans_of_anyAtom l t hr h
  | .ind _ _ _ ps fs, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_loansList_of_anyAtom l ps hr.1 h)
    · exact .inr (mem_loansList_of_anyAtom l fs hr.2 h)
  | .tInd _ fs, hr, h => by
    rw [Value.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff, loanAt, rdHasLoan, Bool.false_or] at h hr
    simp only [Value.loans]; exact mem_loansList_of_anyAtom l fs hr h
  | .zero, _, h | .unit, _, h | .gfn _, _, h | .bot, _, h | .abs _, _, h | .proof, _, h | .tNat, _, h
  | .tUnit, _, h | .sort _, _, h => by simp [Value.anyAtom, loanAt] at h

theorem mem_loansList_of_anyAtom (l : Nat) : ∀ (vs : List Value), Value.anyAtomList (rdHasLoan l) vs = false →
    Value.anyAtomList (loanAt l) vs = true → l ∈ Value.loansList vs
  | [], _, h => by simp [Value.anyAtomList] at h
  | v :: vs, hr, h => by
    rw [Value.anyAtomList] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Value.loansList, List.mem_append]
    rcases h with h | h
    · exact .inl (mem_loans_of_anyAtom l v hr.1 h)
    · exact .inr (mem_loansList_of_anyAtom l vs hr.2 h)

theorem Term_mem_loans_of_anyAtom (l : Nat) : ∀ (t : Term), t.anyAtom (rdHasLoan l) = false →
    t.anyAtom (loanAt l) = true → l ∈ t.loans
  | .val v, hr, h => by
    rw [Term.anyAtom] at h hr; simp only [Term.loans]; exact mem_loans_of_anyAtom l v hr h
  | .assign _ t, hr, h | .succ t, hr, h | .ref t, hr, h => by
    rw [Term.anyAtom] at h hr; simp only [Term.loans]; exact Term_mem_loans_of_anyAtom l t hr h
  | .letIn _ t u, hr, h | .seq t u, hr, h | .cong t u, hr, h | .ascribe t u, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loans_of_anyAtom l t hr.1 h)
    · exact .inr (Term_mem_loans_of_anyAtom l u hr.2 h)
  | .matchNat _ z s, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loans_of_anyAtom l z hr.1 h)
    · exact .inr (Term_mem_loans_of_anyAtom l s hr.2 h)
  | .pi _ ds c, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loansList_of_anyAtom l ds hr.1 h)
    · exact .inr (Term_mem_loans_of_anyAtom l c hr.2 h)
  | .fix _ _ ds c _ b, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (.inl (Term_mem_loansList_of_anyAtom l ds hr.1.1 h))
    · exact .inl (.inr (Term_mem_loans_of_anyAtom l c hr.1.2 h))
    · exact .inr (Term_mem_loans_of_anyAtom l b hr.2 h)
  | .call f as _, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loans_of_anyAtom l f hr.1 h)
    · exact .inr (Term_mem_loansList_of_anyAtom l as hr.2 h)
  | .eq a b c, hr, h | .id a b c, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with (h | h) | h
    · exact .inl (.inl (Term_mem_loans_of_anyAtom l a hr.1.1 h))
    · exact .inl (.inr (Term_mem_loans_of_anyAtom l b hr.1.2 h))
    · exact .inr (Term_mem_loans_of_anyAtom l c hr.2 h)
  | .ctor _ _ _ ps as, hr, h => by
    rw [Term.anyAtom] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loans, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loansList_of_anyAtom l ps hr.1 h)
    · exact .inr (Term_mem_loansList_of_anyAtom l as hr.2 h)
  | .prim _ as, hr, h | .tind _ as, hr, h => by
    rw [Term.anyAtom] at h hr; simp only [Term.loans]; exact Term_mem_loansList_of_anyAtom l as hr h
  | .matchInd _ _ as, hr, h => by
    rw [Term.anyAtom] at h hr; simp only [Term.loans]; exact Term_mem_loansArms_of_anyAtom l as hr h
  | .place _, _, h | .borrow _, _, h | .const _, _, h | .sort _, _, h | .nat, _, h | .zero, _, h | .unit, _, h
  | .tt, _, h => by simp [Term.anyAtom] at h

theorem Term_mem_loansList_of_anyAtom (l : Nat) : ∀ (ts : List Term), Term.anyAtomList (rdHasLoan l) ts = false →
    Term.anyAtomList (loanAt l) ts = true → l ∈ Term.loansList ts
  | [], _, h => by simp [Term.anyAtomList] at h
  | t :: ts, hr, h => by
    rw [Term.anyAtomList] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loansList, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loans_of_anyAtom l t hr.1 h)
    · exact .inr (Term_mem_loansList_of_anyAtom l ts hr.2 h)

theorem Term_mem_loansArms_of_anyAtom (l : Nat) : ∀ (as : List (Hint × Term)), Term.anyAtomArms (rdHasLoan l) as = false →
    Term.anyAtomArms (loanAt l) as = true → l ∈ Term.loansArms as
  | [], _, h => by simp [Term.anyAtomArms] at h
  | (_, t) :: as, hr, h => by
    rw [Term.anyAtomArms] at h hr
    simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at h hr
    simp only [Term.loansArms, List.mem_append]
    rcases h with h | h
    · exact .inl (Term_mem_loans_of_anyAtom l t hr.1 h)
    · exact .inr (Term_mem_loansArms_of_anyAtom l as hr.2 h)
end

theorem rdHasLoan_eq (l : Nat) : rdHasLoan l = Value.rdLoan l := by
  funext v
  cases v <;> try rfl
  all_goals
    simp only [rdHasLoan, Value.rdLoan]
    exact congrArg (Value.anyAtomRd · _) (funext fun x => by cases x <;> rfl)

/-- `hasLoan` is `loans`, outside recorded readings. -/
theorem mem_loans_of_hasLoan {l : Nat} {v : Value} (hr : v.anyAtom (rdHasLoan l) = false)
    (h : v.hasLoan l = true) : l ∈ v.loans := by
  apply mem_loans_of_anyAtom l v hr
  unfold Value.hasLoan at h
  refine (congrArg (fun P => v.anyAtom P) ?_).trans h
  funext x; cases x <;> rfl

/-! ## Positions, holders and sites in the checker's environment -/

/-- A position that holds a borrow is a position of the environment (elsewhere `valAt` reads the
default value, `()`, which holds none). -/
theorem mem_allPos_of_shape {env : Env} {p : Pos} {l : Nat} (h : Env.shape env p = some l) : p ∈ allPos env := by
  rw [shape_eq_shapeOf] at h
  rw [allPos_eq, List.mem_flatMap]
  cases p with
  | bind f i =>
    rw [valAt_bind_eq] at h
    cases hf : env[f]? with
    | none => simp [hf] at h; cases h
    | some fr =>
      cases hb : fr.binds[i]? with
      | none => simp [hf, hb] at h; cases h
      | some b =>
        have hfs : f < env.size := by
          rcases Nat.lt_or_ge f env.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hf
        have his : i < fr.binds.size := by
          rcases Nat.lt_or_ge i fr.binds.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hb
        refine ⟨f, List.mem_range.mpr hfs, ?_⟩
        simp only [hf, Option.map_some, Option.getD_some, frameAllPos, List.mem_append, List.mem_map, List.mem_range]
        exact .inl ⟨i, his, rfl⟩
  | temp f i =>
    rw [valAt_temp_eq] at h
    cases hf : env[f]? with
    | none => simp [hf] at h; cases h
    | some fr =>
      cases hb : fr.temps[i]? with
      | none => simp [hf, hb] at h; cases h
      | some b =>
        have hfs : f < env.size := by
          rcases Nat.lt_or_ge f env.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hf
        have his : i < fr.temps.size := by
          rcases Nat.lt_or_ge i fr.temps.size with h' | h'
          · exact h'
          · simp [Array.getElem?_eq_none h'] at hb
        refine ⟨f, List.mem_range.mpr hfs, ?_⟩
        simp only [hf, Option.map_some, Option.getD_some, frameAllPos, List.mem_append, List.mem_map, List.mem_range]
        exact .inr ⟨i, his, rfl⟩

/-- A site of the environment at `pos` is a site of the value there. -/
theorem mem_sitesOf_at {env : Env} {l : Nat} {x : Site} {pos : Pos} (h : x ∈ Env.sitesOf env l) (hx : x.pos = pos) :
    x ∈ (valAt env pos).sitesOf l pos [] := by
  unfold Env.sitesOf at h
  obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp h
  have := (sitesOf_prefix l p [] (valAt env p) x hp).1
  subst hx; rw [this]; exact hp

theorem mem_env_sitesOf {env : Env} {l : Nat} {x : Site} {pos : Pos} (hp : pos ∈ allPos env)
    (h : x ∈ (valAt env pos).sitesOf l pos []) : x ∈ Env.sitesOf env l := by
  unfold Env.sitesOf
  exact List.mem_flatMap.mpr ⟨pos, hp, h⟩

/-- A label held somewhere in the environment is live. -/
theorem liveLoan_of_shape {env : Env} {p : Pos} {l : Nat} (h : Env.shape env p = some l) : liveLoan env l = true := by
  have hp := mem_allPos_of_shape h
  rw [shape_eq_shapeOf] at h
  unfold liveLoan findBorrow
  rw [Option.isSome_iff_exists]
  have : ((allPos env).find? fun p => (valAt env p).holdsBorrow l).isSome := by
    rw [List.find?_isSome]
    refine ⟨p, hp, ?_⟩
    cases hv : valAt env p with
    | borrow l' w => rw [hv] at h; simp only [shapeOf, Option.some.injEq] at h; subst h; simp [Value.holdsBorrow]
    | _ => rw [hv] at h; simp [shapeOf] at h
  exact Option.isSome_iff_exists.mp this

/-! ## Live loans and a fill's holes -/

theorem mem_liveLoansIn_foldl (env : Env) (l : Nat) :
    ∀ (xs acc : List Nat), (l ∈ acc ∨ (l ∈ xs ∧ liveLoan env l = true)) →
      l ∈ xs.foldl (fun acc l => if !acc.contains l && liveLoan env l then acc ++ [l] else acc) acc
  | [], acc, h => by
    rcases h with h | ⟨h, -⟩
    · exact h
    · cases h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons]
    apply mem_liveLoansIn_foldl env l xs
    rcases h with h | ⟨h, hl⟩
    · left; split <;> simp_all
    · rcases List.mem_cons.mp h with rfl | h'
      · left
        by_cases hc : acc.contains l = true
        · simp only [hc, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact List.contains_iff_mem.mp hc
        · simp only [hc, Bool.not_false, Bool.true_and, hl, ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self l)
      · right; exact ⟨h', hl⟩

theorem mem_liveLoansIn_foldl_inv (env : Env) (l : Nat) :
    ∀ (xs acc : List Nat), l ∈ xs.foldl (fun acc l => if !acc.contains l && liveLoan env l then acc ++ [l] else acc) acc →
      l ∈ acc ∨ (l ∈ xs ∧ liveLoan env l = true)
  | [], acc, h => .inl h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_liveLoansIn_foldl_inv env l xs _ h with h | ⟨h, hl⟩
    · split at h
      · rename_i hc
        rcases List.mem_append.mp h with h | h
        · exact .inl h
        · simp only [List.mem_singleton] at h; subst h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          exact .inr ⟨List.mem_cons_self .., hc.2⟩
      · exact .inl h
    · exact .inr ⟨List.mem_cons_of_mem _ h, hl⟩

theorem mem_liveLoansIn_inv {env : Env} {v : Value} {l : Nat} (h : l ∈ liveLoansIn env v) :
    l ∈ v.loans ∧ liveLoan env l = true := by
  rcases mem_liveLoansIn_foldl_inv env l v.loans [] h with h | h
  · cases h
  · exact h

theorem mem_liveLoansIn {env : Env} {v : Value} {l : Nat} (h : l ∈ v.loans) (hl : liveLoan env l = true) :
    l ∈ liveLoansIn env v :=
  mem_liveLoansIn_foldl env l v.loans [] (.inr ⟨h, hl⟩)

/-- A fill's holes are live loans of the value. -/
theorem fillHoles_sub (env : Env) : ∀ (v : Value) (l : Nat), l ∈ Ochr.fillHoles env v → l ∈ liveLoansIn env v
  | .loan m, l, h => by
    unfold Ochr.fillHoles at h
    split at h
    · rename_i hm
      simp only [List.mem_singleton] at h; subst h
      exact mem_liveLoansIn (by simp [Value.loans]) hm
    · cases h
  | .gloan m w, l, h => by
    unfold Ochr.fillHoles at h
    rcases List.mem_append.mp h with h | h
    · split at h
      · rename_i hm
        simp only [List.mem_singleton] at h; subst h
        exact mem_liveLoansIn (by simp [Value.loans]) hm
      · cases h
    · have hw := mem_liveLoansIn_inv (fillHoles_sub env w l h)
      exact mem_liveLoansIn (by simp [Value.loans, hw.1]) hw.2
  | .sealed t, l, h => by unfold Ochr.fillHoles at h; exact h
  | .zero, l, h | .succ _, l, h | .unit, l, h | .gfn _, l, h | .clo .., l, h | .borrow .., l, h
  | .bot, l, h | .abs _, l, h | .proof, l, h | .tNat, l, h | .tUnit, l, h | .tEq .., l, h | .tRef _, l, h
  | .tPi .., l, h | .sort _, l, h | .ind .., l, h | .tInd .., l, h => by
    simp [Ochr.fillHoles] at h


/-! ## A fill's hole has a site at or above the fill -/

theorem follow_proof : ∀ (ss : List Step) (c : Value), Value.proof.follow ss = some c → c = .proof
  | [], c, h => by simp [Value.follow] at h; exact h.symm
  | s₁ :: ss, c, h => by
    cases s₁ with
    | deref => simp [Value.follow, stepV] at h
    | proj i => simp only [Value.follow, stepV, Option.bind_some] at h; exact follow_proof ss c h
    | field g => simp only [Value.follow, stepV, Option.bind_some] at h; exact follow_proof ss c h

theorem mem_liveLoansIn_inv' {env : Env} {v : Value} {l : Nat} (h : l ∈ liveLoansIn env v) : l ∈ v.loans := by
  unfold liveLoansIn at h
  suffices ∀ (xs acc : List Nat), l ∈ xs.foldl (fun acc l => if !acc.contains l && liveLoan env l then acc ++ [l] else acc) acc →
      l ∈ acc ∨ l ∈ xs by
    rcases this v.loans [] h with h | h
    · cases h
    · exact h
  intro xs
  induction xs with
  | nil => intro acc h; exact .inl h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | h
    · split at h
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · simp only [List.mem_singleton] at h; subst h; exact .inr (List.mem_cons_self ..)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **A fill's hole has a site at or above the fill**: where a path reaches a value with a live
hole `l`, the borrow `l` has a site at that path or at a mark of `l` above it. -/
theorem site_of_fillHole (env : Env) (l : Nat) (pos : Pos) : ∀ (v : Value) (path ss : List Step) (c : Value),
    v.follow ss = some c → l ∈ Ochr.fillHoles env c →
    ∃ x ∈ v.sitesOf l pos path, ∃ ψ, x.path = path ++ ψ ∧ pathKey ψ <+: pathKey ss
  | v, path, [], c, hf, hl => by
    simp only [Value.follow, Option.some.injEq] at hf
    subst hf
    cases v with
    | loan m =>
      unfold Ochr.fillHoles at hl
      split at hl
      · simp only [List.mem_singleton] at hl; subst hl
        exact ⟨⟨pos, path, false⟩, by simp [Value.sitesOf], [], by simp, List.nil_prefix⟩
      · cases hl
    | gloan m w =>
      by_cases hm : m = l
      · subst hm
        exact ⟨⟨pos, path, true⟩, by simp [Value.sitesOf], [], by simp, List.nil_prefix⟩
      · unfold Ochr.fillHoles at hl
        have hw : l ∈ Ochr.fillHoles env w := by
          rcases List.mem_append.mp hl with h | h
          · split at h
            · simp only [List.mem_singleton] at h; exact absurd h.symm hm
            · cases h
          · exact h
        obtain ⟨x, hx, ψ, hxp, hk⟩ := site_of_fillHole env l pos w path [] w (by simp [Value.follow]) hw
        exact ⟨x, by simp only [Value.sitesOf, if_neg hm]; exact hx, ψ, hxp, hk⟩
    | sealed t =>
      unfold Ochr.fillHoles at hl
      have hlo := hasLoan_of_mem_loans (mem_liveLoansIn_inv' hl)
      exact ⟨⟨pos, path, true⟩, by simp [Value.sitesOf, hlo], [], by simp, List.nil_prefix⟩
    | _ => simp [Ochr.fillHoles] at hl
  | v, path, s₁ :: ss, c, hf, hl => by
    cases v with
    | gloan m w =>
      by_cases hm : m = l
      · subst hm
        exact ⟨⟨pos, path, true⟩, by simp [Value.sitesOf], [], by simp, List.nil_prefix⟩
      · rw [follow_gloan_cons] at hf
        obtain ⟨x, hx, ψ, hxp, hk⟩ := site_of_fillHole env l pos w path (s₁ :: ss) c hf hl
        exact ⟨x, by simp only [Value.sitesOf, if_neg hm]; exact hx, ψ, hxp, hk⟩
    | borrow b w =>
      cases s₁ with
      | deref =>
        simp only [Value.follow, stepV, Option.bind_some] at hf
        obtain ⟨x, hx, ψ, hxp, hk⟩ := site_of_fillHole env l pos w (path ++ [.deref]) ss c hf hl
        refine ⟨x, by simpa [Value.sitesOf] using hx, .deref :: ψ, by rw [hxp]; simp, ?_⟩
        simp only [pathKey, List.map_cons]
        exact List.cons_prefix_cons.mpr ⟨rfl, hk⟩
      | proj _ | field _ => simp [Value.follow, stepV] at hf
    | succ w =>
      cases s₁ with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.follow, stepV, Option.bind_some] at hf
          obtain ⟨x, hx, ψ, hxp, hk⟩ := site_of_fillHole env l pos w (path ++ [.proj 0]) ss c hf hl
          refine ⟨x, by simpa [Value.sitesOf] using hx, .proj 0 :: ψ, by rw [hxp]; simp, ?_⟩
          simp only [pathKey, List.map_cons]
          exact List.cons_prefix_cons.mpr ⟨rfl, hk⟩
        | succ _ => simp [Value.follow, stepV] at hf
      | deref | field _ => simp [Value.follow, stepV] at hf
    | ind ty c' hh ps fs =>
      have key : ∀ (i : Nat) (w : Value), fs[i]? = some w → w.follow ss = some c → (Step.key s₁ = some (c', i)) →
          ∃ x ∈ (Value.ind ty c' hh ps fs).sitesOf l pos path, ∃ ψ, x.path = path ++ ψ ∧ pathKey ψ <+: pathKey (s₁ :: ss) := by
        intro i w hi hfw hk
        have : sizeOf w < sizeOf (Value.ind ty c' hh ps fs) := by
          have := List.sizeOf_lt_of_mem (List.mem_of_getElem? hi)
          simp only [Value.ind.sizeOf_spec]; omega
        obtain ⟨x, hx, ψ, hxp, hk'⟩ := site_of_fillHole env l pos w (path ++ [.field ⟨ty, c', i, ""⟩]) ss c hfw hl
        refine ⟨x, ?_, .field ⟨ty, c', i, ""⟩ :: ψ, by rw [hxp]; simp, ?_⟩
        · simp only [Value.sitesOf]
          exact (mem_sitesOfFields l pos path ty c' 0 fs x).mpr ⟨i, w, hi, by simpa using hx⟩
        · simp only [pathKey, List.map_cons]
          rw [hk]
          exact List.cons_prefix_cons.mpr ⟨rfl, hk'⟩
      cases s₁ with
      | deref => simp [Value.follow, stepV] at hf
      | proj i =>
        cases c' with
        | zero =>
          simp only [Value.follow, stepV] at hf
          cases hi : fs[i]? with
          | none => simp [hi] at hf
          | some w => rw [hi, Option.bind_some] at hf; exact key i w hi hf rfl
        | succ _ => simp [Value.follow, stepV] at hf
      | field g =>
        simp only [Value.follow, stepV] at hf
        split at hf
        · rename_i hg
          simp only [Bool.and_eq_true, beq_iff_eq] at hg
          cases hi : fs[g.idx]? with
          | none => simp [hi] at hf
          | some w =>
            rw [hi, Option.bind_some] at hf
            exact key g.idx w hi hf (by simp [Step.key, hg.2])
        · simp at hf
    | proof =>
      cases s₁ with
      | deref => simp [Value.follow, stepV] at hf
      | proj _ | field _ =>
        simp only [Value.follow, stepV, Option.bind_some] at hf
        rw [follow_proof ss c hf] at hl
        simp [Ochr.fillHoles] at hl
    | _ => simp [Value.follow, stepV] at hf
termination_by v => sizeOf v

/-! ## A borrow is found only at a root -/

theorem valueAnyAtomList_of_mem {P : Value → Bool} {u : Value} : ∀ {vs : List Value}, u ∈ vs → u.anyAtom P = true →
    Value.anyAtomList P vs = true
  | v :: vs, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [Value.anyAtomList, h]
    · simp [Value.anyAtomList, valueAnyAtomList_of_mem hm h]

theorem anyAtom_of_stepV {P : Value → Bool} : ∀ (st : Step) (v u : Value), stepV st v = some u →
    u.anyAtom P = true → v.anyAtom P = true
  | st, .gloan m w, u, h, hu => by
    have : stepV st (.gloan m w) = stepV st w := by cases st <;> rfl
    rw [this] at h
    rw [Value.anyAtom]; simp [anyAtom_of_stepV st w u h hu]
  | .deref, .borrow _ w, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h
    rw [Value.anyAtom]; simp [hu]
  | .proj 0, .succ w, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h
    rw [Value.anyAtom]; simp [hu]
  | .proj i, .ind t 0 hh ps fs, u, h, hu => by
    simp only [stepV] at h
    rw [Value.anyAtom]
    have hm := List.mem_of_getElem? h
    simp only [Bool.or_eq_true]
    exact .inr (.inr (valueAnyAtomList_of_mem hm hu))
  | .field g, .ind t c hh ps fs, u, h, hu => by
    simp only [stepV] at h
    split at h
    · rw [Value.anyAtom]
      have hm := List.mem_of_getElem? h
      simp only [Bool.or_eq_true]
      exact .inr (.inr (valueAnyAtomList_of_mem hm hu))
    · cases h
  | .proj _, .proof, u, h, hu | .field _, .proof, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h; exact hu
  | .deref, .zero, _, h, _ | .deref, .succ _, _, h, _ | .deref, .unit, _, h, _ | .deref, .gfn _, _, h, _
  | .deref, .clo .., _, h, _ | .deref, .loan _, _, h, _ | .deref, .bot, _, h, _ | .deref, .abs _, _, h, _
  | .deref, .sealed _, _, h, _ | .deref, .proof, _, h, _ | .deref, .tNat, _, h, _ | .deref, .tUnit, _, h, _
  | .deref, .tEq .., _, h, _ | .deref, .tRef _, _, h, _ | .deref, .tPi .., _, h, _ | .deref, .sort _, _, h, _
  | .deref, .ind .., _, h, _ | .deref, .tInd .., _, h, _ => by simp [stepV] at h
  | .proj _, .zero, _, h, _ | .proj (_ + 1), .succ _, _, h, _ | .proj _, .unit, _, h, _ | .proj _, .gfn _, _, h, _
  | .proj _, .clo .., _, h, _ | .proj _, .borrow .., _, h, _ | .proj _, .loan _, _, h, _ | .proj _, .bot, _, h, _
  | .proj _, .abs _, _, h, _ | .proj _, .sealed _, _, h, _ | .proj _, .tNat, _, h, _ | .proj _, .tUnit, _, h, _
  | .proj _, .tEq .., _, h, _ | .proj _, .tRef _, _, h, _ | .proj _, .tPi .., _, h, _ | .proj _, .sort _, _, h, _
  | .proj _, .ind _ (_ + 1) .., _, h, _ | .proj _, .tInd .., _, h, _ => by simp [stepV] at h
  | .field _, .zero, _, h, _ | .field _, .succ _, _, h, _ | .field _, .unit, _, h, _ | .field _, .gfn _, _, h, _
  | .field _, .clo .., _, h, _ | .field _, .borrow .., _, h, _ | .field _, .loan _, _, h, _ | .field _, .bot, _, h, _
  | .field _, .abs _, _, h, _ | .field _, .sealed _, _, h, _ | .field _, .tNat, _, h, _ | .field _, .tUnit, _, h, _
  | .field _, .tEq .., _, h, _ | .field _, .tRef _, _, h, _ | .field _, .tPi .., _, h, _ | .field _, .sort _, _, h, _
  | .field _, .tInd .., _, h, _ => by simp [stepV] at h

theorem anyAtom_of_follow {P : Value → Bool} : ∀ (ss : List Step) (v u : Value), v.follow ss = some u →
    u.anyAtom P = true → v.anyAtom P = true
  | [], v, u, h, hu => by simp [Value.follow] at h; subst h; exact hu
  | s₁ :: ss, v, u, h, hu => by
    simp only [Value.follow] at h
    cases hs : stepV s₁ v with
    | none => simp [hs] at h
    | some v' => rw [hs, Option.bind_some] at h; exact anyAtom_of_stepV s₁ v v' hs (anyAtom_of_follow ss v' u h hu)


/-! ## What a path reaches holds no loan its root does not -/

theorem mem_loansList_of_mem {l : Nat} {u : Value} : ∀ {vs : List Value}, u ∈ vs → l ∈ u.loans → l ∈ Value.loansList vs
  | v :: vs, hm, h => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [Value.loansList, h]
    · simp [Value.loansList, mem_loansList_of_mem hm h]

theorem loans_of_stepV {l : Nat} : ∀ (st : Step) (v u : Value), stepV st v = some u → l ∈ u.loans → l ∈ v.loans
  | st, .gloan m w, u, h, hu => by
    have : stepV st (.gloan m w) = stepV st w := by cases st <;> rfl
    rw [this] at h
    simp only [Value.loans, List.mem_cons]; exact .inr (loans_of_stepV st w u h hu)
  | .deref, .borrow _ w, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h; simpa [Value.loans] using hu
  | .proj 0, .succ w, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h; simpa [Value.loans] using hu
  | .proj i, .ind t 0 hh ps fs, u, h, hu => by
    simp only [stepV] at h
    simp only [Value.loans, List.mem_append]
    exact .inr (mem_loansList_of_mem (List.mem_of_getElem? h) hu)
  | .field g, .ind t c hh ps fs, u, h, hu => by
    simp only [stepV] at h
    split at h
    · simp only [Value.loans, List.mem_append]
      exact .inr (mem_loansList_of_mem (List.mem_of_getElem? h) hu)
    · cases h
  | .proj _, .proof, u, h, hu | .field _, .proof, u, h, hu => by
    simp only [stepV, Option.some.injEq] at h; subst h; exact hu
  | .deref, .zero, _, h, _ | .deref, .succ _, _, h, _ | .deref, .unit, _, h, _ | .deref, .gfn _, _, h, _
  | .deref, .clo .., _, h, _ | .deref, .loan _, _, h, _ | .deref, .bot, _, h, _ | .deref, .abs _, _, h, _
  | .deref, .sealed _, _, h, _ | .deref, .proof, _, h, _ | .deref, .tNat, _, h, _ | .deref, .tUnit, _, h, _
  | .deref, .tEq .., _, h, _ | .deref, .tRef _, _, h, _ | .deref, .tPi .., _, h, _ | .deref, .sort _, _, h, _
  | .deref, .ind .., _, h, _ | .deref, .tInd .., _, h, _ => by simp [stepV] at h
  | .proj _, .zero, _, h, _ | .proj (_ + 1), .succ _, _, h, _ | .proj _, .unit, _, h, _ | .proj _, .gfn _, _, h, _
  | .proj _, .clo .., _, h, _ | .proj _, .borrow .., _, h, _ | .proj _, .loan _, _, h, _ | .proj _, .bot, _, h, _
  | .proj _, .abs _, _, h, _ | .proj _, .sealed _, _, h, _ | .proj _, .tNat, _, h, _ | .proj _, .tUnit, _, h, _
  | .proj _, .tEq .., _, h, _ | .proj _, .tRef _, _, h, _ | .proj _, .tPi .., _, h, _ | .proj _, .sort _, _, h, _
  | .proj _, .ind _ (_ + 1) .., _, h, _ | .proj _, .tInd .., _, h, _ => by simp [stepV] at h
  | .field _, .zero, _, h, _ | .field _, .succ _, _, h, _ | .field _, .unit, _, h, _ | .field _, .gfn _, _, h, _
  | .field _, .clo .., _, h, _ | .field _, .borrow .., _, h, _ | .field _, .loan _, _, h, _ | .field _, .bot, _, h, _
  | .field _, .abs _, _, h, _ | .field _, .sealed _, _, h, _ | .field _, .tNat, _, h, _ | .field _, .tUnit, _, h, _
  | .field _, .tEq .., _, h, _ | .field _, .tRef _, _, h, _ | .field _, .tPi .., _, h, _ | .field _, .sort _, _, h, _
  | .field _, .tInd .., _, h, _ => by simp [stepV] at h

theorem loans_of_follow {l : Nat} : ∀ (ss : List Step) (v u : Value), v.follow ss = some u → l ∈ u.loans → l ∈ v.loans
  | [], v, u, h, hu => by simp [Value.follow] at h; subst h; exact hu
  | s₁ :: ss, v, u, h, hu => by
    simp only [Value.follow] at h
    cases hs : stepV s₁ v with
    | none => simp [hs] at h
    | some v' => rw [hs, Option.bind_some] at h; exact loans_of_stepV s₁ v v' hs (loans_of_follow ss v' u h hu)

theorem follow_append : ∀ (v : Value) (a b : List Step), v.follow (a ++ b) = (v.follow a).bind (·.follow b)
  | v, [], b => by simp [Value.follow]
  | v, s₁ :: a, b => by
    simp only [List.cons_append, Value.follow]
    cases stepV s₁ v with
    | none => rfl
    | some w => simp only [Option.bind_some]; exact follow_append w a b

end Ochr.Meaning
