import Ochr.Meaning.Strict.Good

/-!
# Writing `⊥` keeps open membership

A move out of a part, the join's drop and D112's invalidation write `⊥` at a path (`Sem.updAt` with
the constant `moved`). Where the write is defined it leaves a value below the old one (`MovedOf`),
not whole; an OPEN member stays an open member (`omem_updAt_moved`): a moved field is `OField.moved`,
a field below the old one stays below the same completion, a later field's completion stays a
completion (⊥ is below anything), and a tree field read at its own record is written by induction.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning Ochr.Meaning.DataModel

section
variable {dm : DataModel} {Γ : List IndDecl}

mutual
theorem movedOf_trans : ∀ {a b c : Sem}, MovedOf Γ a b → MovedOf Γ b c → MovedOf Γ a c
  | _, _, _, .moved _, _ => .moved _
  | _, _, _, .refl _, h => h
  | _, _, _, .dat h1, h2 => by
    cases h2 with
    | refl => exact .dat h1
    | dat h2 => exact .dat (movedOfList_trans h1 h2)
    | succ h2 =>
      cases h1 with
      | cons hf hnil => cases hnil; exact .succ (movedOf_trans hf h2)
  | _, _, _, .succ h1, h2 => by
    cases h2 with
    | refl => exact .succ h1

theorem movedOfList_trans : ∀ {a b c : List Sem}, MovedOfList Γ a b → MovedOfList Γ b c → MovedOfList Γ a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h hs, .cons h' hs' => .cons (movedOf_trans h h') (movedOfList_trans hs hs')
end

theorem movedOfList_set : ∀ (fs : List Sem) (i : Nat) (fi x : Sem), fs[i]? = some fi → MovedOf Γ x fi →
    MovedOfList Γ (fs.set i x) fs
  | [], _, _, _, h, _ => by simp at h
  | f :: fs, 0, fi, x, h, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    exact .cons hx (movedOfList_refl' Γ fs)
  | f :: fs, i + 1, fi, x, h, hx => by
    simp only [List.getElem?_cons_succ] at h
    exact .cons (.refl f) (movedOfList_set fs i fi x h hx)

theorem whole_set_not {fs : List Sem} {i : Nat} {fi x : Sem} (h : fs[i]? = some fi) (hx : ¬ x.whole) :
    ¬ ∀ f ∈ fs.set i x, f.whole := by
  intro hall
  have hi : i < fs.length := by
    rcases (List.getElem?_eq_some_iff.mp h) with ⟨hi, -⟩; exact hi
  exact hx (hall x (List.mem_iff_getElem.mpr ⟨i, by simpa using hi, by simp⟩))

theorem eq_el0_of_asNat {x : Sem} {n : Nat} (h : x.asNat = some n) : x = .el0 Nat n := by
  unfold Sem.asNat Sem.as at h
  split at h
  · rename_i B b
    split at h
    · rename_i hB; subst hB; cases h; rfl
    · cases h
  · cases h

theorem succAt_not_whole (r : Rec) {x : Sem} (hx : ¬ x.whole) : Sem.succAt r x = .dat "Nat" r 1 [x] := by
  unfold Sem.succAt
  cases hn : x.asNat with
  | some n => exact absurd (by rw [eq_el0_of_asNat hn]; trivial) hx
  | none => simp only; rw [if_neg hx]

end

end Ochr.Meaning.Strict
