import OchrMeta.Canon
import OchrMeta.Interp
import OchrMeta.WF

/-! # Property 7: the order in which borrows end does not change the resolved state

`end_comm` (T1(a)) is the two-step diamond, for two held borrows whose contents do not each
contain the other's loan.  In a well-formed state that side condition always holds (W3: the
loans in a borrow's content are younger than it), and it survives [End], because [End]
preserves well-formedness (`endBorrow_inv`).  [End] of a borrow that is not held fails, and it
still fails after any other [End].  So two [End]s commute outright in a well-formed state
(`end_comm_wf`), and a routine induction on permutations gives full order-independence
(`endSeq_perm`).  The only side condition is well-formedness (`WFv s V`, any values in flight,
so it applies inside [Access]); the labels need not be held or distinct, since a sequence that
ends a label twice, or one that is not held, fails in every order.

The resolved state `endAll`, which ends the held borrows in environment order, is one such
order (`endAll_eq_endSeq`).  So:

* `end_order_indep`: in a well-formed state the resolved state exists, and ending the held
  borrows in any order, each once, reaches it;
* `endAll_endSeq`: whatever borrows were ended first, in whatever order (as [Access] does),
  resolving afterwards gives the same resolved state.

Everything is on the nose: [End] allocates no names, so no renaming is involved.  This is for
the machine of this development, whose [End] is a plain substitution (it does not re-normalise
sealed programs). -/

namespace OchrMeta

/-- End the borrows `ls`, in order. -/
def endSeq : List Nat → St → Option St
  | [], s => some s
  | l :: ls, s => (endBorrow l s).bind (endSeq ls)

theorem endBorrow_of_holderContent_none {l : Nat} {s : St} (h : s.env.holderContent l = none) :
    endBorrow l s = none := by
  unfold endBorrow; rw [h]

/-- After ending `m`, the holder of another borrow `l` holds its old content with
`loan_m` filled in. -/
theorem holderContent_endBorrow {l m : Nat} (hne : l ≠ m) {s s' : St} {cm : Val}
    (hm : s.env.holderContent m = some cm) (h : endBorrow m s = some s') :
    s'.env.holderContent l = (s.env.holderContent l).map (Val.substLoan m cm) := by
  rw [endBorrow_eq hm] at h
  split at h
  · rename_i hcm
    cases h
    exact Env.holderContent_mapVals (endMap_isBorrowOf (Ne.symm hne) hcm)
      (fun x => by simp [endMap, Val.clearB, Val.isBorrowOf, hne, Val.substLoan]) _
  · cases h

/-- Ending `m` and then a borrow `l` that is not held fails. -/
theorem endBorrow_bind_none {l m : Nat} (hne : l ≠ m) {s : St}
    (hl : s.env.holderContent l = none) : (endBorrow m s).bind (endBorrow l) = none := by
  cases h : endBorrow m s with
  | none => rfl
  | some s' =>
    cases hm : s.env.holderContent m with
    | none => rw [endBorrow_of_holderContent_none hm] at h; cases h
    | some cm =>
      simp only [Option.bind_some]
      apply endBorrow_of_holderContent_none
      rw [holderContent_endBorrow hne hm h, hl]; rfl

theorem endBorrow_wf {l : Nat} {s s' : St} {V : List Val} (hs : WFv s V)
    (h : endBorrow l s = some s') : WFv s' V :=
  wfv_iff.mpr (endBorrow_inv (wfv_iff.mp hs) h).1

/-- W3 gives `end_comm`'s side condition: a held borrow's content holds only younger loans. -/
theorem acyc_of_wf {s : St} {V : List Val} (hs : WFv s V) {l : Nat} {cl : Val}
    (hl : s.env.holderContent l = some cl) : ∀ k ∈ cl.loans, l < k := by
  obtain ⟨x, hx⟩ := Env.holderContent_mem hl
  exact hs.acyc (l, cl) (Env.mem_heldPairs_iff.mpr ⟨_, hx, by simp [Val.hp]⟩)

/-- **Two [End]s commute** in a well-formed state, for any two labels (held or not, equal or
not): both orders give the same state, or both fail. -/
theorem end_comm_wf {l m : Nat} {s : St} {V : List Val} (hs : WFv s V) :
    (endBorrow l s).bind (endBorrow m) = (endBorrow m s).bind (endBorrow l) := by
  by_cases hne : l = m
  · subst hne; rfl
  cases hl : s.env.holderContent l with
  | none =>
    rw [endBorrow_of_holderContent_none hl, endBorrow_bind_none hne hl]; rfl
  | some cl =>
    cases hm : s.env.holderContent m with
    | none =>
      rw [endBorrow_of_holderContent_none hm, endBorrow_bind_none (Ne.symm hne) hm]; rfl
    | some cm =>
      refine end_comm hne hl hm ?_
      rintro ⟨h1, h2⟩
      have := acyc_of_wf hs hm l h1
      have := acyc_of_wf hs hl m h2
      omega

theorem endSeq_wf : ∀ {ls : List Nat} {s s' : St} {V : List Val}, WFv s V →
    endSeq ls s = some s' → WFv s' V
  | [], _, _, _, hs, h => by cases h; exact hs
  | l :: ls, s, s', V, hs, h => by
    simp only [endSeq] at h
    cases he : endBorrow l s with
    | none => rw [he] at h; cases h
    | some s1 => rw [he] at h; exact endSeq_wf (endBorrow_wf hs he) h

/-- **Order-independence.** From a well-formed state, ending the borrows of two lists that are
permutations of each other gives the same state, or fails in both orders. -/
theorem endSeq_perm {L₁ L₂ : List Nat} (hp : L₁.Perm L₂) :
    ∀ {s : St} {V : List Val}, WFv s V → endSeq L₁ s = endSeq L₂ s := by
  induction hp with
  | nil => intros; rfl
  | cons x _ ih =>
    intro s V hs
    simp only [endSeq]
    cases he : endBorrow x s with
    | none => rfl
    | some s1 => exact ih (endBorrow_wf hs he)
  | swap x y l =>
    intro s V hs
    simp only [endSeq]
    rw [← Option.bind_assoc, ← Option.bind_assoc, end_comm_wf hs]
  | trans _ _ ih1 ih2 => intro s V hs; exact (ih1 hs).trans (ih2 hs)

/-! ## The resolved state is one of the orders -/

theorem find?_held {p : Var × Val → Bool} (hp : ∀ x v, p (x, v) = !v.hd.isEmpty) :
    ∀ E : Bs, (E.find? p = none ∧ HE E = []) ∨
      ∃ x l c rest, E.find? p = some (x, .borrow l c) ∧ HE E = l :: rest
  | [] => Or.inl ⟨rfl, rfl⟩
  | (x, v) :: E => by
    cases v with
    | borrow l c =>
      exact Or.inr ⟨x, l, c, HE E, by simp [List.find?, hp, Val.hd], by simp [HE_cons, Val.hd]⟩
    | _ => simpa [List.find?, hp, Val.hd] using find?_held hp E

theorem find?_held_some {p : Var × Val → Bool} (hp : ∀ x v, p (x, v) = !v.hd.isEmpty) {E : Bs}
    {x : Var} {l : Nat} {c : Val} (h : E.find? p = some (x, .borrow l c)) : ∃ rest, HE E = l :: rest := by
  rcases find?_held hp E with ⟨hf, -⟩ | ⟨x', l', c', rest, hf, hE⟩
  · rw [hf] at h; cases h
  · rw [hf] at h; cases h; exact ⟨rest, hE⟩

theorem find?_held_none {p : Var × Val → Bool} (hp : ∀ x v, p (x, v) = !v.hd.isEmpty) {E : Bs}
    (h : ∀ x l c, E.find? p = some (x, .borrow l c) → False) : HE E = [] := by
  rcases find?_held hp E with ⟨-, hE⟩ | ⟨x, l, c, rest, hf, -⟩
  · exact hE
  · exact (h x l c hf).elim

theorem Val.hd_clearB (l : Nat) (v : Val) : (Val.clearB l v).hd = v.hd.filter (· != l) := by
  cases v with
  | borrow k c =>
    by_cases h : k = l
    · subst h; rw [Val.clearB_borrow]; simp [Val.hd]
    · rw [Val.clearB_eq_self (by simp [Val.isBorrowOf, h])]; simp [Val.hd, h]
  | _ => rfl

theorem HE_map_filter {l : Nat} {g : Val → Val} (hg : ∀ v, (g v).hd = v.hd.filter (· != l)) :
    ∀ E : Bs, HE (E.map fun b => (b.1, g b.2)) = (HE E).filter (· != l)
  | [] => rfl
  | b :: E => by simp only [List.map_cons, HE_cons, List.filter_append, hg, HE_map_filter hg E]

/-- [End ℓ] removes `ℓ` from the held borrows and keeps the rest, in order. -/
theorem held_endBorrow {l : Nat} {s s' : St} (h : endBorrow l s = some s') :
    s'.env.held = s.env.held.filter (· != l) := by
  unfold endBorrow at h
  split at h
  · cases h
  · obtain ⟨hw, e1, -, -⟩ := endWith_spec h
    simp only [Env.held_eq, e1, Env.clearHolder, Env.flatten_mapVals, List.map_map, Function.comp_def]
    exact HE_map_filter (g := fun v => Val.substLoan l _ (Val.clearB l v))
      (fun v => by rw [Val.hd_substLoan hw, Val.hd_clearB]) _

theorem Frame.held_length_le : ∀ F : Frame, (HE F).length ≤ F.nb
  | [] => Nat.le_refl _
  | (x, v) :: F => by
    have := Frame.held_length_le F
    cases v <;> simp [HE_cons, Val.hd, Frame.nb, Val.nb] at this ⊢ <;> omega

theorem Env.held_length_le : ∀ Ω : Env, Ω.held.length ≤ Ω.nb
  | [] => Nat.le_refl _
  | F :: Ω => by
    have h1 := Frame.held_length_le F
    have h2 := Env.held_length_le Ω
    simp only [Env.held_eq, List.flatten_cons, HE_append, List.length_append, Env.nb] at h2 ⊢
    omega

theorem endAllN_eq_endSeq : ∀ (n : Nat) {s : St} {V : List Val}, WFv s V →
    s.env.held.length < n → endAllN n s = endSeq s.env.held s
  | 0, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, s, V, hs, hn => by
    have hnd : s.env.held.Nodup := (List.nodup_append.mp hs.uniq).1
    rw [endAllN]
    split
    · rename_i x l c hf
      obtain ⟨rest, hE⟩ := find?_held_some (fun x v => by cases v <;> rfl) hf
      rw [← Env.held_eq] at hE
      rw [hE] at hnd hn ⊢
      simp only [endSeq]
      cases he : endBorrow l s with
      | none => rfl
      | some s1 =>
        have h1 : s1.env.held = rest := by
          rw [held_endBorrow he, hE, List.filter_cons_of_neg (by simp)]
          refine List.filter_eq_self.mpr fun a ha => ?_
          have : a ≠ l := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ha)
          simpa using this
        have := endAllN_eq_endSeq n (endBorrow_wf hs he) (by rw [h1]; simpa using hn)
        rw [h1] at this
        exact this
    · rename_i hf
      rw [Env.held_eq, find?_held_none (fun x v => by cases v <;> rfl) hf]; rfl

/-- The resolved state (every held borrow ended, in environment order) is `endSeq` of the
held borrows. -/
theorem endAll_eq_endSeq {s : St} {V : List Val} (hs : WFv s V) :
    endAll s = endSeq s.env.held s :=
  endAllN_eq_endSeq _ hs (Nat.lt_succ_of_le (Env.held_length_le _))

/-- From a well-formed state, ending the held borrows in any order gives the resolved state:
`L` is any ordering of the held borrows, each once. -/
theorem endSeq_eq_endAll {s : St} {V : List Val} (hs : WFv s V) {L : List Nat}
    (hL : L.Perm s.env.held) : endSeq L s = endAll s := by
  rw [endAll_eq_endSeq hs]; exact endSeq_perm hL hs

/-! ## The resolved state exists -/

theorem Frame.holderContent_none {l : Nat} :
    ∀ {F : Frame}, F.holderContent l = none → l ∉ HE F
  | [], _ => by simp
  | (x, v) :: F, h => by
    cases v with
    | borrow m c =>
      simp only [Frame.holderContent] at h
      split at h
      · cases h
      · rename_i hm
        simp [HE_cons, Val.hd, Ne.symm hm, Frame.holderContent_none h]
    | _ => simpa [HE_cons, Val.hd] using Frame.holderContent_none (F := F) h

theorem Env.holderContent_some {l : Nat} : ∀ {Ω : Env}, l ∈ Ω.held → ∃ c, Ω.holderContent l = some c
  | [], h => by simp [Env.held_eq] at h
  | F :: Ω, h => by
    simp only [Env.held_eq, List.flatten_cons, HE_append, List.mem_append] at h
    simp only [Env.holderContent]
    cases hF : F.holderContent l with
    | some c => exact ⟨c, rfl⟩
    | none =>
      rcases h with h | h
      · exact absurd h (Frame.holderContent_none hF)
      · exact Env.holderContent_some (by rwa [Env.held_eq])

/-- In a well-formed state a held borrow can be ended. -/
theorem endBorrow_isSome {l : Nat} {s : St} {V : List Val} (hs : WFv s V) (hl : l ∈ s.env.held) :
    ∃ s', endBorrow l s = some s' := by
  obtain ⟨c, hc⟩ := Env.holderContent_some hl
  obtain ⟨x, hx⟩ := Env.holderContent_mem hc
  have hsh := forall_flatten.mp hs.shallowE _ hx
  have hc0 : c.nb = 0 := Val.sh_borrow hsh
  rw [endBorrow_eq hc, if_pos hc0]
  exact ⟨_, rfl⟩

theorem endSeq_isSome : ∀ {L : List Nat} {s : St} {V : List Val}, WFv s V → L.Nodup →
    (∀ l ∈ L, l ∈ s.env.held) → ∃ s', endSeq L s = some s'
  | [], s, _, _, _, _ => ⟨s, rfl⟩
  | l :: L, s, V, hs, hnd, hL => by
    obtain ⟨s1, h1⟩ := endBorrow_isSome hs (hL l List.mem_cons_self)
    simp only [endSeq, h1, Option.bind_some]
    refine endSeq_isSome (endBorrow_wf hs h1) (List.nodup_cons.mp hnd).2 fun k hk => ?_
    rw [held_endBorrow h1, List.mem_filter]
    have : k ≠ l := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hk)
    exact ⟨hL k (List.mem_cons_of_mem _ hk), by simpa using this⟩

/-- **Property 7, in full.** From a well-formed state the resolved state exists, and ending
the held borrows in any order (each once) reaches it. -/
theorem end_order_indep {s : St} {V : List Val} (hs : WFv s V) :
    ∃ s', endAll s = some s' ∧ ∀ L : List Nat, L.Perm s.env.held → endSeq L s = some s' := by
  have hnd : s.env.held.Nodup := (List.nodup_append.mp hs.uniq).1
  obtain ⟨s', h⟩ := endSeq_isSome hs hnd fun _ h => h
  refine ⟨s', by rw [endAll_eq_endSeq hs, h], fun L hL => ?_⟩
  rw [endSeq_eq_endAll hs hL, endAll_eq_endSeq hs, h]

/-! ## Ending some borrows first does not change the resolved state -/

theorem endSeq_append : ∀ (L M : List Nat) (s : St), endSeq (L ++ M) s = (endSeq L s).bind (endSeq M)
  | [], _, _ => rfl
  | l :: L, M, s => by
    simp only [List.cons_append, endSeq]
    cases endBorrow l s with
    | none => rfl
    | some s1 => exact endSeq_append L M s1

theorem held_of_endBorrow {l : Nat} {s s' : St} (h : endBorrow l s = some s') : l ∈ s.env.held := by
  cases hc : s.env.holderContent l with
  | none => rw [endBorrow_of_holderContent_none hc] at h; cases h
  | some c =>
    obtain ⟨x, hx⟩ := Env.holderContent_mem hc
    rw [Env.held_eq, mem_HE]; exact ⟨_, hx, by simp [Val.hd]⟩

/-- A sequence of [End]s that succeeds ends distinct held borrows, and leaves the others held. -/
theorem endSeq_spec : ∀ {L : List Nat} {s s' : St}, endSeq L s = some s' →
    L.Nodup ∧ (∀ l ∈ L, l ∈ s.env.held) ∧ s'.env.held = s.env.held.filter (fun k => !L.contains k)
  | [], s, s', h => by cases h; exact ⟨List.nodup_nil, by simp, (List.filter_eq_self.mpr (by simp)).symm⟩
  | l :: L, s, s', h => by
    simp only [endSeq] at h
    cases h1 : endBorrow l s with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1, Option.bind_some] at h
      obtain ⟨hnd, hL, hh⟩ := endSeq_spec h
      have e1 := held_endBorrow h1
      refine ⟨List.nodup_cons.mpr ⟨fun hl => ?_, hnd⟩, ?_, ?_⟩
      · have := hL l hl; rw [e1] at this; simp at this
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact held_of_endBorrow h1
        · have := hL k hk; rw [e1] at this; exact (List.mem_filter.mp this).1
      · rw [hh, e1, List.filter_filter]
        apply List.filter_congr
        intro k _
        by_cases hk : k = l <;> simp [hk]

/-- **Property 7, as [Access] uses it.** From a well-formed state, whatever borrows have been
ended first, and in whatever order, resolving afterwards gives the same resolved state. -/
theorem endAll_endSeq {s s' : St} {V : List Val} (hs : WFv s V) {L : List Nat}
    (h : endSeq L s = some s') : endAll s' = endAll s := by
  obtain ⟨hnd, hL, hh⟩ := endSeq_spec h
  have hnd0 : s.env.held.Nodup := (List.nodup_append.mp hs.uniq).1
  have hperm : (L ++ s.env.held.filter (fun k => !L.contains k)).Perm s.env.held := by
    refine List.Perm.trans ?_ (List.filter_append_perm (fun k => L.contains k) s.env.held)
    refine List.Perm.append_right _ ?_
    refine (List.perm_ext_iff_of_nodup hnd (hnd0.sublist (List.filter_sublist))).mpr fun a => ?_
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨fun ha => ⟨hL a ha, ha⟩, fun ha => ha.2⟩
  rw [endAll_eq_endSeq (endSeq_wf hs h), hh, ← endSeq_eq_endAll hs hperm, endSeq_append, h]
  rfl

end OchrMeta
