import Ochr.Meaning.Run

/-!
# Frame locality, part 0: a term's free variables and its subterms' (exists3, 2026-11-21)

`Term.freeVars` reads the free occurrences off `placeOccs`, at a depth that counts the binders above
an occurrence. A subterm under `n` binders has its free variable `v` as the variable `v - n` of the
term, or as one of the `n` bound ones (`freeVars_sub`).
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr

/-- An occurrence `n` binders deeper. -/
def shOcc (n : Nat) (x : Nat × Place × PKind) : Nat × Place × PKind := (x.1 + n, x.2)

mutual
theorem placeOccs_add : ∀ (t : Term) (c n : Nat), t.placeOccs (c + n) = (t.placeOccs c).map (shOcc n)
  | t, c, n => by
    cases t with
    | place p => simp [Term.placeOccs, shOcc]
    | borrow p => simp [Term.placeOccs, shOcc]
    | assign p u => simp [Term.placeOccs, placeOccs_add u, shOcc]
    | letIn h u v =>
      simp only [Term.placeOccs, placeOccs_add u c n, List.map_append]
      rw [Nat.add_right_comm, placeOccs_add v (c + 1) n]
    | seq u v => simp only [Term.placeOccs, placeOccs_add u c n, placeOccs_add v c n, List.map_append]
    | matchNat p z s =>
      simp only [Term.placeOccs, placeOccs_add z c n, placeOccs_add s c n, List.map_append, List.map_cons]; rfl
    | pi hs ds cod =>
      simp only [Term.placeOccs, placeOccsDoms_add ds c n, List.map_append]
      rw [Nat.add_right_comm, placeOccs_add cod (c + ds.length) n]
    | fix f hs ds cod d b =>
      simp only [Term.placeOccs, placeOccsDoms_add ds c n, List.map_append]
      rw [Nat.add_right_comm c n, placeOccs_add cod (c + ds.length) n, Nat.add_right_comm (c + ds.length) n,
        placeOccs_add b (c + ds.length + 1) n]
    | call g as h => simp only [Term.placeOccs, placeOccs_add g c n, placeOccsList_add as c n, List.map_append]
    | succ u => simp only [Term.placeOccs, placeOccs_add u c n]
    | ref u => simp only [Term.placeOccs, placeOccs_add u c n]
    | cong a b => simp only [Term.placeOccs, placeOccs_add a c n, placeOccs_add b c n, List.map_append]
    | ascribe a b => simp only [Term.placeOccs, placeOccs_add a c n, placeOccs_add b c n, List.map_append]
    | eq a b d =>
      simp only [Term.placeOccs, placeOccs_add a c n, placeOccs_add b c n, placeOccs_add d c n, List.map_append]
    | id a b d =>
      simp only [Term.placeOccs, placeOccs_add a c n, placeOccs_add b c n, placeOccs_add d c n, List.map_append]
    | ctor ty k h ps as => simp only [Term.placeOccs, placeOccsList_add ps c n, placeOccsList_add as c n, List.map_append]
    | prim nm as => simp only [Term.placeOccs, placeOccsList_add as c n]
    | tind nm as => simp only [Term.placeOccs, placeOccsList_add as c n]
    | matchInd p ty as =>
      simp only [Term.placeOccs, placeOccsArms_add as c n, List.map_cons]; rfl
    | _ => simp [Term.placeOccs]

theorem placeOccsList_add : ∀ (ts : List Term) (c n : Nat),
    Term.placeOccsList (c + n) ts = (Term.placeOccsList c ts).map (shOcc n)
  | [], _, _ => rfl
  | t :: ts, c, n => by simp only [Term.placeOccsList, placeOccs_add t c n, placeOccsList_add ts c n, List.map_append]

theorem placeOccsDoms_add : ∀ (ts : List Term) (c n : Nat),
    Term.placeOccsDoms (c + n) ts = (Term.placeOccsDoms c ts).map (shOcc n)
  | [], _, _ => rfl
  | t :: ts, c, n => by
    simp only [Term.placeOccsDoms, placeOccs_add t c n, List.map_append]
    rw [Nat.add_right_comm, placeOccsDoms_add ts (c + 1) n]

theorem placeOccsArms_add : ∀ (ts : List (Hint × Term)) (c n : Nat),
    Term.placeOccsArms (c + n) ts = (Term.placeOccsArms c ts).map (shOcc n)
  | [], _, _ => rfl
  | (h, t) :: ts, c, n => by simp only [Term.placeOccsArms, placeOccs_add t c n, placeOccsArms_add ts c n, List.map_append]
end

theorem mem_foldl_dedup {α β : Type} [BEq α] [LawfulBEq α] (x : α) :
    ∀ (l : List (α × β)) (acc : List α),
      x ∈ l.foldl (fun acc (o : α × β) => if acc.contains o.1 then acc else acc ++ [o.1]) acc ↔ x ∈ acc ∨ ∃ y, (x, y) ∈ l
  | [], acc => by simp
  | (o, y) :: l, acc => by
    simp only [List.foldl_cons]
    rw [mem_foldl_dedup x l]
    by_cases h : acc.contains o
    · simp only [h, if_true, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h1 | ⟨y', h1⟩)
        · exact .inl h1
        · exact .inr ⟨y', .inr h1⟩
      · rintro (h1 | ⟨y', ⟨rfl, rfl⟩ | h1⟩)
        · exact .inl h1
        · exact .inl (List.contains_iff_mem.mp h)
        · exact .inr ⟨y', h1⟩
    · simp only [h, Bool.false_eq_true, if_false, List.mem_append, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false]
      constructor
      · rintro ((h1 | rfl) | ⟨y', h1⟩)
        · exact .inl h1
        · exact .inr ⟨y, .inl ⟨rfl, rfl⟩⟩
        · exact .inr ⟨y', .inr h1⟩
      · rintro (h1 | ⟨y', ⟨rfl, rfl⟩ | h1⟩)
        · exact .inl (.inl h1)
        · exact .inl (.inr rfl)
        · exact .inr ⟨y', h1⟩

/-- **A term's free variables**, read off its occurrences at depth 0. -/
theorem mem_freeVars (t : Term) (v : Nat) :
    v ∈ t.freeVars ↔ ∃ c p k, (c, p, k) ∈ t.placeOccs 0 ∧ c ≤ p.root ∧ v = p.root - c := by
  unfold Term.freeVars Term.freeOccs
  rw [mem_foldl_dedup]
  simp only [List.not_mem_nil, false_or, List.mem_filterMap]
  constructor
  · rintro ⟨y, ⟨c, p, k⟩, hm, he⟩
    dsimp only at he
    split at he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      exact ⟨c, p, k, hm, by omega, he.1.symm⟩
    · cases he
  · rintro ⟨c, p, k, hm, hc, rfl⟩
    exact ⟨(p, k), (c, p, k), hm, by simp [hc]⟩

/-- **A subterm's free variables**: a subterm whose occurrences are the term's, `n` binders deeper. -/
theorem freeVars_sub {t u : Term} {n : Nat} (h : ∀ x ∈ u.placeOccs n, x ∈ t.placeOccs 0) :
    ∀ v ∈ u.freeVars, v < n ∨ v - n ∈ t.freeVars := by
  intro v hv
  obtain ⟨c, p, k, hm, hc, rfl⟩ := (mem_freeVars u v).mp hv
  have hm' : (c + n, p, k) ∈ t.placeOccs 0 := h _ (by
    rw [show n = 0 + n from (Nat.zero_add n).symm, placeOccs_add u 0 n]
    exact List.mem_map.mpr ⟨(c, p, k), hm, by simp [shOcc]⟩)
  by_cases hr : c + n ≤ p.root
  · exact .inr ((mem_freeVars t _).mpr ⟨c + n, p, k, hm', hr, by omega⟩)
  · exact .inl (by omega)

end Ochr.Meaning.DataModel.Exists.FrameLocal
