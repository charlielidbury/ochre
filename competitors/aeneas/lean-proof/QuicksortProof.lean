/-
  Total-correctness proof of the **Aeneas-generated** in-place quicksort.

  Every theorem in this file is stated about the *generated* definitions from
  `Quicksort.lean` (`quicksort.quicksort`, `quicksort.partition`,
  `quicksort.partition_loop`, `quicksort.partition_loop.body`) — NOT a hand
  re-implementation. We import the generated module and reason about its
  `Slice`-based, `partial_fixpoint` definitions with Aeneas's own proof
  framework: the `step` tactic, the `⦃ ⦄` weakest-precondition triple, and the
  `Aeneas.Std` spec lemmas (`split_at_mut.spec`, `swap`/`update`/`index_usize`
  specs, `loop.spec_decr_nat`).

  Because the Aeneas triple `e ⦃ s' => P s' ⦄` unfolds to `theta e P`, and
  `theta` sends BOTH `fail` and `div` to `False`, proving the triple is *total
  correctness*: it simultaneously shows the generated function terminates with
  `ok` (no panic, no divergence) AND that the postcondition holds.

  Headline result (`quicksort_correct`, at the bottom):

      quicksort.quicksort s ⦃ s' =>
        List.Pairwise (· ≤ ·) s'.val ∧ s'.val.Perm s.val ⦄

  The final `#print axioms` line shows the proof rests only on Lean's standard
  axioms (propext / Classical.choice / Quot.sound) — no `sorry`, no extra axiom.
-/
import Quicksort
import Aeneas
namespace Aeneas.Std
open Result Error WP quicksort
set_option maxHeartbeats 4000000

theorem swap_val' {α} [Inhabited α] (s : Slice α) (a b : Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    core.slice.Slice.swap s a b ⦃ s' =>
      s'.val = (s.val.set a.val (s.val[b.val]'hb)).set b.val (s.val[a.val]'ha) ∧
      s'.length = s.length ⦄ := by
  simp only [core.slice.Slice.swap, Bind.bind, bind]
  have ⟨av, hav⟩ := spec_imp_exists (Slice.index_usize_spec s a ha)
  simp only [hav]
  have ⟨bv, hbv⟩ := spec_imp_exists (Slice.index_usize_spec s b hb)
  simp only [hbv]
  have ⟨s1, hs1⟩ := spec_imp_exists (Slice.update_spec s a (s.val[b.val]) ha)
  simp only [hs1]
  have hlen1 : b.val < s1.length := by rw [hs1.2, Slice.set_length]; exact hb
  have ⟨s', hs'⟩ := spec_imp_exists (Slice.update_spec s1 b (s.val[a.val]) hlen1)
  rw [hs1.2] at hs'
  simp only [hs', spec_ok]
  refine ⟨?_, ?_⟩
  · simp only [hs1.2, Slice.set_val_eq]
  · simp only [hs1.2, Slice.length, Slice.set_val_eq, List.length_set]

theorem set_set_perm' {α} [BEq α] [LawfulBEq α] (l : List α) (i j : Nat)
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i (l[j]'hj)).set j (l[i]'hi)).Perm l := by
  rw [List.perm_iff_count]; intro a
  have hjlen : j < (l.set i (l[j]'hj)).length := by simp [hj]
  rw [List.count_set hjlen, List.count_set hi]
  have key : (l.set i (l[j]'hj))[j]'hjlen = (l[j]'hj) := by rw [List.getElem_set]; split <;> rfl
  rw [key]
  have cj : (if (l[j]'hj == a) = true then 1 else 0) ≤ List.count a l := by
    by_cases h : (l[j]'hj == a) = true
    · have : l[j]'hj = a := by simpa using h
      simp only [h, if_true]; rw [← this]; exact List.count_pos_iff.mpr (List.getElem_mem hj)
    · simp [h]
  have ci : (if (l[i]'hi == a) = true then 1 else 0) ≤ List.count a l := by
    by_cases h : (l[i]'hi == a) = true
    · have : l[i]'hi = a := by simpa using h
      simp only [h, if_true]; rw [← this]; exact List.count_pos_iff.mpr (List.getElem_mem hi)
    · simp [h]
  omega

theorem swap_props {α} [Inhabited α] [BEq α] [LawfulBEq α] (s : Slice α) (a b : Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    core.slice.Slice.swap s a b ⦃ s' =>
      s'.length = s.length ∧
      s'.val.Perm s.val ∧
      s'.val[a.val]! = s.val[b.val]! ∧
      s'.val[b.val]! = s.val[a.val]! ∧
      (∀ k, k ≠ a.val → k ≠ b.val → s'.val[k]! = s.val[k]!) ⦄ := by
  apply WP.spec_mono (swap_val' s a b ha hb)
  rintro s' ⟨hval, hlen⟩
  have hperm : s'.val.Perm s.val := by rw [hval]; exact set_set_perm' s.val a.val b.val ha hb
  refine ⟨hlen, hperm, ?_, ?_, ?_⟩
  · rw [hval]
    by_cases hab : a.val = b.val
    · simp_lists [hab]
    · simp_lists
  · rw [hval]
    by_cases hab : a.val = b.val
    · simp_lists [hab]
    · simp_lists
  · intro k hka hkb; rw [hval]; simp_lists

theorem partition_loop_body_spec (s0 : Slice Std.U32) (len : Std.Usize) (pivot : Std.U32)
    (hlen : len.val = s0.length) (hlen1 : 1 ≤ len.val)
    (s' : Slice Std.U32) (i' j' : Std.Usize)
    (hsl : s'.length = len.val) (hpm : s'.val.Perm s0.val)
    (hi'j' : i'.val ≤ j'.val) (hj' : j'.val ≤ len.val - 1)
    (hlst : s'.val[len.val - 1]! = s0.val[len.val - 1]!)
    (hlo' : ∀ k, k < i'.val → s'.val[k]! ≤ pivot)
    (hhi' : ∀ k, i'.val ≤ k → k < j'.val → pivot < s'.val[k]!) :
    partition_loop.body len pivot s' i' j' ⦃ r =>
      match r with
      | .done y =>
        y.1.length = len.val ∧ y.1.val.Perm s0.val ∧ y.2.val ≤ len.val - 1 ∧
        y.1.val[len.val - 1]! = s0.val[len.val - 1]! ∧
        (∀ k, k < y.2.val → y.1.val[k]! ≤ pivot) ∧
        (∀ k, y.2.val ≤ k → k < len.val - 1 → pivot < y.1.val[k]!)
      | .cont st =>
        (st.1.length = len.val ∧ st.1.val.Perm s0.val ∧
         st.2.1.val ≤ st.2.2.val ∧ st.2.2.val ≤ len.val - 1 ∧
         st.1.val[len.val - 1]! = s0.val[len.val - 1]! ∧
         (∀ k, k < st.2.1.val → st.1.val[k]! ≤ pivot) ∧
         (∀ k, st.2.1.val ≤ k → k < st.2.2.val → pivot < st.1.val[k]!)) ∧
        (len.val - 1) - st.2.2.val < (len.val - 1) - j'.val ⦄ := by
  unfold partition_loop.body
  step as ⟨ i1, hi1 ⟩
  by_cases hcond : j' < i1
  · simp only [hcond, if_true]
    have hjlt : j'.val < len.val - 1 := by
      have h : j'.val < i1.val := by simpa using hcond
      omega
    have hjb : j'.val < s'.length := by omega
    have hib : i'.val < s'.length := by omega
    step as ⟨ i2, hi2 ⟩
    by_cases hle : i2 ≤ pivot
    · simp only [hle, if_true]
      step with swap_props s' i' j' hib hjb as ⟨ s2, hslen2, hsperm2, hsa, hsb, hsk ⟩
      step as ⟨ i4, hi4 ⟩
      step as ⟨ j1, hj1 ⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hslen2, hsl]
      · exact hsperm2.trans hpm
      · simp [hi4, hj1]; omega
      · simp [hj1]; omega
      · rw [hsk (len.val - 1) (by omega) (by omega)]; exact hlst
      · intro k hk
        simp only [hi4] at hk
        by_cases hki : k = i'.val
        · subst hki; rw [hsa]
          have : s'.val[j'.val]! = i2 := by rw [hi2]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjb]
          rw [this]; exact hle
        · rw [hsk k hki (by omega)]; exact hlo' k (by omega)
      · intro k hk1 hk2
        simp only [hi4] at hk1
        simp only [hj1] at hk2
        by_cases hkj : k = j'.val
        · subst hkj; rw [hsb]
          rcases Nat.lt_or_ge i'.val j'.val with hlt | hge
          · exact hhi' i'.val (le_refl _) hlt
          · exfalso; omega
        · rw [hsk k (by omega) hkj]; exact hhi' k (by omega) (by omega)
      · simp [hj1]; omega
    · -- no swap: i2 > pivot, keep s', i', j+1
      simp only [hle, if_false]
      step as ⟨ j1, hj1 ⟩
      refine ⟨hsl, hpm, ?_, ?_, hlst, hlo', ?_, ?_⟩
      · simp [hj1]; omega
      · simp [hj1]; omega
      · intro k hk1 hk2
        simp only [hj1] at hk2
        by_cases hkj : k = j'.val
        · subst hkj
          have heq : s'.val[j'.val]! = i2 := by rw [hi2]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjb]
          rw [heq]; simp at hle; exact hle
        · exact hhi' k hk1 (by omega)
      · simp [hj1]; omega
  · simp only [hcond, if_false]
    simp only [spec_ok]
    have hjeq : j'.val = len.val - 1 := by
      have h : ¬ (j'.val < i1.val) := by simpa using hcond
      omega
    refine ⟨hsl, hpm, ?_, hlst, hlo', ?_⟩
    · omega
    · intro k hk1 hk2; exact hhi' k hk1 (by omega)

theorem partition_loop_spec (s0 : Slice Std.U32) (len : Std.Usize) (pivot : Std.U32)
    (s : Slice Std.U32) (i j : Std.Usize)
    (hlen : len.val = s0.length) (hlen1 : 1 ≤ len.val)
    (hslen : s.length = len.val) (hperm : s.val.Perm s0.val)
    (hij : i.val ≤ j.val) (hj : j.val ≤ len.val - 1)
    (hlast : s.val[len.val - 1]! = s0.val[len.val - 1]!)
    (hlo : ∀ k, k < i.val → s.val[k]! ≤ pivot)
    (hhi : ∀ k, i.val ≤ k → k < j.val → pivot < s.val[k]!) :
    partition_loop s len pivot i j ⦃ p =>
      p.1.length = len.val ∧ p.1.val.Perm s0.val ∧ p.2.val ≤ len.val - 1 ∧
      p.1.val[len.val - 1]! = s0.val[len.val - 1]! ∧
      (∀ k, k < p.2.val → p.1.val[k]! ≤ pivot) ∧
      (∀ k, p.2.val ≤ k → k < len.val - 1 → pivot < p.1.val[k]!) ⦄ := by
  unfold partition_loop
  apply loop.spec_decr_nat
    (measure := fun (st : Slice Std.U32 × Std.Usize × Std.Usize) => (len.val - 1) - st.2.2.val)
    (inv := fun (st : Slice Std.U32 × Std.Usize × Std.Usize) =>
      st.1.length = len.val ∧ st.1.val.Perm s0.val ∧
      st.2.1.val ≤ st.2.2.val ∧ st.2.2.val ≤ len.val - 1 ∧
      st.1.val[len.val - 1]! = s0.val[len.val - 1]! ∧
      (∀ k, k < st.2.1.val → st.1.val[k]! ≤ pivot) ∧
      (∀ k, st.2.1.val ≤ k → k < st.2.2.val → pivot < st.1.val[k]!))
  · rintro ⟨s', i', j'⟩ hinv
    obtain ⟨hsl, hpm, hi'j', hj', hlst, hlo', hhi'⟩ := hinv
    have H := partition_loop_body_spec s0 len pivot hlen hlen1 s' i' j' hsl hpm hi'j' hj' hlst hlo' hhi'
    apply WP.spec_mono H
    rintro r hr
    cases r with
    | done y => exact hr
    | cont st => exact hr
  · exact ⟨hslen, hperm, hij, hj, hlast, hlo, hhi⟩
theorem partition_spec (s : Slice Std.U32) (hs : 1 ≤ s.length) :
    partition s ⦃ p =>
      p.1.val < s.length ∧ p.2.length = s.length ∧ p.2.val.Perm s.val ∧
      (∀ k, k < p.1.val → p.2.val[k]! ≤ p.2.val[p.1.val]!) ∧
      (∀ k, p.1.val < k → k < s.length → p.2.val[p.1.val]! ≤ p.2.val[k]!) ⦄ := by
  unfold partition
  step as ⟨ i, hi ⟩
  step as ⟨ pivot, hpivot ⟩
  have hlenval : (s.len).val = s.length := by simp
  have hpiv_eq : pivot = s.val[s.length - 1]! := by
    rw [hpivot]; simp [hi, hlenval, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show s.length - 1 < s.length by omega)]
  have Hloop := partition_loop_spec s s.len pivot s 0#usize 0#usize
    hlenval.symm (by simp [hlenval]; omega) (by simp [hlenval]) (List.Perm.refl _)
    (by simp) (by simp) rfl (by simp) (by simp)
  have ⟨⟨s1, i1⟩, hHeq, hHpost⟩ := spec_imp_exists Hloop
  simp only [hHeq]
  obtain ⟨hs1len, hs1perm, hi1le, hs1last, hs1lo, hs1hi⟩ := hHpost
  simp only [hlenval] at hs1len hi1le hs1last hs1lo hs1hi
  have hs1len' : s1.length = s.length := hs1len
  have hi1lt : i1.val < s.length := by omega
  have hi1b : i1.val < s1.length := by omega
  step as ⟨ i2, hi2 ⟩
  have hi2lt : i2.val < s1.length := by rw [hi2]; simp only [hi, hlenval]; omega
  step with swap_props s1 i1 i2 hi1b hi2lt
    as ⟨ s2, hs2len, hs2perm, hs2a, hs2b, hs2k ⟩
  -- s2[i1] = s1[len-1] = pivot
  have hi2eq : i2.val = s.length - 1 := by rw [hi2]; simp [hi, hlenval]
  have hpivot_at : s2.val[i1.val]! = pivot := by
    rw [hs2a, hi2eq, hs1last]; exact hpiv_eq.symm
  refine ⟨hi1lt, ?_, ?_, ?_, ?_⟩
  · simp [hs2len, hs1len]
  · exact hs2perm.trans hs1perm
  · intro k hk
    rw [hpivot_at]
    have hkne1 : k ≠ i1.val := by omega
    have hkne2 : k ≠ i2.val := by rw [hi2eq]; omega
    rw [hs2k k hkne1 hkne2]
    exact hs1lo k hk
  · intro k hk1 hk2
    rw [hpivot_at]
    by_cases hkl : k = s.length - 1
    · -- s2[len-1] = s1[i1]; pivot ≤ s1[i1] since i1 < len-1 (as i1 < k = len-1)
      subst hkl
      have hkeq2 : s.length - 1 = i2.val := hi2eq.symm
      rw [hkeq2, hs2b]
      exact le_of_lt (hs1hi i1.val (le_refl _) (by omega))
    · have hkne1 : k ≠ i1.val := by omega
      have hkne2 : k ≠ i2.val := by rw [hi2eq]; omega
      rw [hs2k k hkne1 hkne2]
      exact le_of_lt (hs1hi k (by omega) (by omega))
theorem quicksort_spec (s : Slice Std.U32) :
    quicksort s ⦃ s' => List.Pairwise (· ≤ ·) s'.val ∧ s'.val.Perm s.val ⦄ := by
  generalize hn : s.length = n
  induction n using Nat.strong_induction_on generalizing s with
  | _ n IH =>
    unfold quicksort
    by_cases hsmall : s.len ≤ 1#usize
    · simp only [hsmall, if_true, WP.spec_ok]
      refine ⟨?_, List.Perm.refl _⟩
      have hle1 : s.val.length ≤ 1 := by simpa [Slice.length] using hsmall
      match hv : s.val, hle1 with
      | [], _ => simp
      | [a], _ => simp
    · simp only [hsmall, if_false]
      have hge : 1 ≤ s.length := by simp [Slice.length] at hsmall ⊢; omega
      subst hn
      step with partition_spec s hge as ⟨ p, s1, hplt, hs1len, hs1perm, hplo, hphi ⟩
      have hps1 : p.val ≤ s1.length := by rw [hs1len]; omega
      step with core.slice.Slice.split_at_mut.spec s1 p hps1
        as ⟨ lo, hi, back, hlolen, hhilen, hloval, hhival, hback ⟩
      -- recurse on lo : lo.length = p < s.length
      have hlo_len : lo.length = p.val := hlolen
      have hlo_lt : lo.length < s.length := by rw [hlo_len]; omega
      step with IH lo.length hlo_lt lo rfl as ⟨ lo1, hlo1sorted, hlo1perm ⟩
      -- split hi 1 : hi.length = s1.length - p ≥ 1
      have hhi_len : hi.length = s1.length - p.val := hhilen
      have hhi_ge : 1 ≤ hi.length := by rw [hhi_len, hs1len]; omega
      have hhi1 : (1#usize).val ≤ hi.length := by simpa using hhi_ge
      step with core.slice.Slice.split_at_mut.spec hi 1#usize hhi1
        as ⟨ piv, upper, back1, hpivlen, hupperlen, hpivval, hupperval, hback1 ⟩
      -- recurse on upper : upper.length = hi.length - 1 < s.length
      have hupper_len : upper.length = hi.length - 1 := by simpa using hupperlen
      have hupper_lt : upper.length < s.length := by
        rw [hupper_len, hhi_len, hs1len]; omega
      step with IH upper.length hupper_lt upper rfl as ⟨ upper1, hupp1sorted, hupp1perm ⟩
      -- compute the value through the two back-functions
      have hlo1leq : lo1.val.length = lo.val.length := hlo1perm.length_eq
      have hupp1leq : upper1.val.length = upper.val.length := hupp1perm.length_eq
      have hlo1len : lo1.length = p.val := by
        simp only [Slice.length] at hlo1leq hlolen ⊢; omega
      have hupp1len : upper1.length = hi.length - 1 := by
        simp only [Slice.length] at hupp1leq hupper_len ⊢; omega
      -- back1 (piv, upper1)
      have hb1 := (hback1 piv upper1 hpivlen hupp1len).1
      have hb1len := (hback1 piv upper1 hpivlen hupp1len).2
      -- back (lo1, back1 (piv, upper1))
      have hb := (hback lo1 (back1 (piv, upper1)) hlo1len (by rw [hb1len]; exact hhi_len)).1
      -- the result value
      have hresult : (back (lo1, back1 (piv, upper1))).val = lo1.val ++ (piv.val ++ upper1.val) := by
        rw [hb, hb1]
      rw [hresult]
      -- PERMUTATION
      have hpu : (piv.val ++ upper1.val).Perm hi.val := by
        have : (piv.val ++ upper1.val).Perm (piv.val ++ upper.val) :=
          List.Perm.append (List.Perm.refl _) hupp1perm
        refine this.trans ?_
        rw [hpivval, hupperval, List.take_append_drop]
      have hperm : (lo1.val ++ (piv.val ++ upper1.val)).Perm s.val := by
        have h1 : (lo1.val ++ (piv.val ++ upper1.val)).Perm (lo.val ++ hi.val) :=
          List.Perm.append hlo1perm hpu
        refine h1.trans ?_
        rw [hloval, hhival, List.take_append_drop]
        exact hs1perm
      refine ⟨?_, hperm⟩
      -- SORTEDNESS
      have hpb : p.val < s1.length := by rw [hs1len]; omega
      set pv := s1.val[p.val]'hpb with hpvdef
      have hpivval' : piv.val = [pv] := by
        rw [hpivval, hhival]
        have hd : 0 < (List.drop p.val s1.val).length := by simp [Slice.length] at hpb ⊢; omega
        rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem hd]
        simp [List.getElem_drop, hpvdef]
      -- bound: all of lo1 ≤ pv
      have hlo_le : ∀ a ∈ lo1.val, a ≤ pv := by
        intro a ha
        have ha' : a ∈ lo.val := (hlo1perm.mem_iff).mp ha
        rw [hloval, List.mem_take_iff_getElem] at ha'
        obtain ⟨k, hk, hak⟩ := ha'
        rw [← hak]
        have hkp : k < p.val := by simp [Slice.length] at hk ⊢; omega
        have hkb : k < s1.length := by rw [hs1len]; omega
        have := hplo k hkp
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hkb] at this
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hpb] at this
        simpa [hpvdef] using this
      -- bound: pv ≤ all of upper1
      have hup_ge : ∀ b ∈ upper1.val, pv ≤ b := by
        intro b hb
        have hb' : b ∈ upper.val := (hupp1perm.mem_iff).mp hb
        rw [hupperval, hhival, List.mem_iff_getElem] at hb'
        obtain ⟨k, hk, hbk⟩ := hb'
        have hklen : k < s1.val.length - p.val - 1 := by
          simpa [Slice.length, List.length_drop] using hk
        have hkb : 1 + (p.val + k) < s1.val.length := by omega
        -- b = (drop 1 (drop p s1))[k] = s1[1 + (p + k)]
        have hbval : b = s1.val[1 + (p.val + k)]'hkb := by
          rw [← hbk]; simp only [List.getElem_drop]; congr 1; omega
        rw [hbval]
        have hpk : p.val < 1 + (p.val + k) := by omega
        have hkbs : 1 + (p.val + k) < s.length := by
          have : s1.length = s.length := hs1len; simp only [Slice.length] at this ⊢; omega
        have hh := hphi (1 + (p.val + k)) hpk hkbs
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hpb] at hh
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hkb] at hh
        simpa [hpvdef] using hh
      -- assemble
      rw [List.pairwise_append]
      refine ⟨hlo1sorted, ?_, ?_⟩
      · -- Pairwise (piv ++ upper1) = Pairwise ([pv] ++ upper1)
        rw [hpivval', List.singleton_append, List.pairwise_cons]
        exact ⟨hup_ge, hupp1sorted⟩
      · -- cross: ∀ a ∈ lo1, ∀ c ∈ piv++upper1, a ≤ c
        intro a ha c hc
        rw [hpivval', List.singleton_append, List.mem_cons] at hc
        rcases hc with hcpv | hcup
        · subst hcpv; exact hlo_le a ha
        · exact le_trans (hlo_le a ha) (hup_ge c hcup)

/-- **Headline correctness theorem for the Aeneas-generated quicksort.**

    Stated directly about the generated `quicksort.quicksort` (note the fully
    qualified name — this is the `Slice U32 → Result (Slice U32)`,
    `partial_fixpoint` function produced by Charon+Aeneas, imported from
    `Quicksort.lean`, not a re-implementation). Total correctness:

    * the call never panics and never diverges (the triple is `False` on
      `fail`/`div`), i.e. it returns `ok s'`, and
    * the returned slice `s'` is sorted ascending and is a permutation of the
      input slice `s`. -/
theorem quicksort_correct (s : Slice Std.U32) :
    quicksort.quicksort s ⦃ s' =>
      List.Pairwise (· ≤ ·) s'.val ∧ s'.val.Perm s.val ⦄ :=
  quicksort_spec s

end Aeneas.Std

-- The proof depends only on Lean's standard axioms — no `sorry`, no extra axiom.
#print axioms Aeneas.Std.quicksort_correct
