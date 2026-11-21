import Ochr.Meaning.Strict.Good
import Ochr.Meaning.BotWrite
import Ochr.Meaning.DataModel.ReadMember

/-!
# Writing `⊥` keeps open membership

A move out of a part, the join's drop and D112's invalidation write `⊥` at a path (`Sem.updAt` with
the constant `moved`). Where the write is defined it leaves a value below the old one (`MovedOf`),
not whole (`updAt_moved_props`), and OPEN membership is closed under moving parts out
(`omem_movedOf`), so an open member stays an open member (`omem_updAt_moved`). Field by field: `⊥`
stays `⊥` (only `⊥` is below it), a field below a completion stays below it, a later field's
completion stays a completion (the earlier fields went below theirs), and a field read at a type keeps
that type: a tree keeps its name and record, and `readTy` reads a field only through that head
(`readTy_eq_of_head`); a number becoming its tuple form is read alike unless its field is a tree field
(`readTy_eq_of_not_sub`, `readTy_of_not_dat`), where no number is an open member
(`el0_not_mem_rawTy`, `readTy_el0_succ`).
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
  | some n => exact absurd (by rw [eq_el0_of_asNat hn]; simp [Sem.whole]) hx
  | none => simp only; rw [if_neg hx]

/-- One step of a write that is not `*`, taken apart: a number's predecessor, a tree named `Nat`'s one
field (rebuilt at its own record), or a constructor value's field. -/
theorem updAt_cons_cases {U : TyS} {f : Sem → Sem} {st : Step} {sts : List Step} {x y : Sem}
    (hst : st ≠ .deref) (h : Sem.updAt dm Γ U f (st :: sts) x = some y) :
    (∃ n w, st = .proj 0 ∧ x = .el0 Nat (n + 1) ∧
        Sem.updAt dm Γ (.plain TyM.nat) f sts (.el0 Nat n) = some w ∧ y = Sem.succ w) ∨
    (∃ r w w', st = .proj 0 ∧ x = .dat "Nat" r 1 [w] ∧
        Sem.updAt dm Γ (.plain TyM.nat) f sts w = some w' ∧ y = Sem.succAt r w') ∨
    (∃ n r c fs fi fi', x = .dat n r c fs ∧ fs[st.fieldIdx]? = some fi ∧
        Sem.updAt dm Γ U f sts fi = some fi' ∧ y = .dat n r c (fs.set st.fieldIdx fi')) := by
  cases st with
  | deref => exact absurd rfl hst
  | proj i =>
    rw [Sem.updAt.eq_def] at h
    simp only at h
    split at h
    · rename_i n heq1 heq2
      obtain ⟨w, h1, rfl⟩ := Option.map_eq_some_iff.1 h
      exact .inl ⟨n, w, heq1, eq_el0_of_asNat heq2, h1, rfl⟩
    · split at h
      · rename_i r w _
        split at h
        · rename_i heq
          obtain ⟨w', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          exact .inr (.inl ⟨r, w, w', heq, rfl, h1, rfl⟩)
        · cases h
      · rename_i n r c fs _ _
        split at h
        · rename_i fi hfi
          obtain ⟨fi', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          exact .inr (.inr ⟨n, r, c, fs, fi, fi', rfl, hfi, h1, rfl⟩)
        · cases h
      · cases h
  | field g =>
    rw [Sem.updAt.eq_def] at h
    simp only at h
    split at h
    · cases h
    · rename_i n r c fs _
      split at h
      · rename_i fi hfi
        obtain ⟨fi', h1, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .inr (.inr ⟨n, r, c, fs, fi, fi', rfl, hfi, h1, rfl⟩)
      · cases h
    · cases h

/-- A non-`*` step of a write of `⊥`, given the write's facts below it. -/
theorem updAt_moved_step {U : TyS} {st : Step} {sts : List Step} {x y : Sem} (hst : st ≠ .deref)
    (ih : ∀ {U' : TyS} {a b : Sem}, Sem.updAt dm Γ U' (fun _ => .moved) sts a = some b → MovedOf Γ b a ∧ ¬ b.whole)
    (h : Sem.updAt dm Γ U (fun _ => .moved) (st :: sts) x = some y) : MovedOf Γ y x ∧ ¬ y.whole := by
  rcases updAt_cons_cases hst h with ⟨n, w, -, rfl, h1, rfl⟩ | ⟨r, w, w', -, rfl, h1, rfl⟩ |
      ⟨n, r, c, fs, fi, fi', rfl, hfi, h1, rfl⟩
  · obtain ⟨hm, hw⟩ := ih h1
    rw [Sem.succ_eq_succAt, succAt_not_whole _ hw]
    exact ⟨.succ hm, fun h => hw (by simpa [Sem.whole] using h)⟩
  · obtain ⟨hm, hw⟩ := ih h1
    rw [succAt_not_whole _ hw]
    exact ⟨.dat (.cons hm .nil), fun h => hw (by simpa [Sem.whole] using h)⟩
  · obtain ⟨hm, hw⟩ := ih h1
    refine ⟨.dat (movedOfList_set fs _ fi fi' hfi hm), ?_⟩
    simp only [Sem.whole]
    exact whole_set_not hfi hw

/-- **A write of `⊥` leaves a value below the old one, and not whole** (a `⊥` lands inside, so a
successor of the result is the tuple form, `succAt_not_whole`). -/
theorem updAt_moved_props : ∀ (steps : List Step) {U : TyS} {x y : Sem},
    Sem.updAt dm Γ U (fun _ => .moved) steps x = some y → MovedOf Γ y x ∧ ¬ y.whole
  | [], _, _, _, h => by
    rw [Sem.updAt_nil'] at h; cases h; exact ⟨.moved _, fun h => by simp [Sem.whole] at h⟩
  | st :: sts, _, _, _, h => by
    by_cases hst : st = .deref
    · subst hst; rw [Sem.updAt_deref'] at h; exact updAt_moved_props sts h
    · exact updAt_moved_step hst (fun h' => updAt_moved_props sts h') h

/-! ## Open fields below their old earlier fields -/

/-- A field stays open after the earlier fields go below theirs (a completion of the old earlier
fields is one of the new, `MovedOf` being transitive). -/
theorem oField_weaken {d : IndDecl} {r : Rec} {c i : Nat} {e e₂ : List Sem} {f : Sem}
    (h : dm.OField Γ d r c i e f) (he : MovedOfList Γ e₂ e) : dm.OField Γ d r c i e₂ f := by
  cases h with
  | moved => exact .moved
  | fits e' t hl ht hmo hfit => exact .fits e' t (movedOfList_trans he hl) ht hmo hfit
  | «at» e' U hl hU hO => exact .at e' U (movedOfList_trans he hl) hU hO

/-! ## The type a read gives a rewritten field -/

/-- No number is a member of a data code over its own carrier (its members are trees). -/
theorem el0_not_mem_rawTy {A : Type} {a : A} {d : IndDecl} {r : Rec} : ¬ (Sem.el0 A a ∈ₛ[dm.read] dm.rawTy d r) := by
  rintro ⟨x, hx⟩
  have hx' : dm.read.read d r (dm.car d r) x = Sem.el0 A a := hx
  rw [dm.read_car x] at hx'
  have hm : dm.Mem d r (dm.meanC x) := (dm.mem_iff_meanC d r _).2 ⟨x, rfl⟩
  obtain ⟨_, _, he, -⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
  rw [hx'] at he; cases he

/-! The three facts below are everything the proof uses of `readTy`; each is proved by unfolding it,
and each says `readTy` reads the field only through its HEAD (is it a `.dat`, and if so its name
and record) and through the shape. -/

/-- **`readTy` reads a field's head only**: two fields both constructor values with the same name and
record, or neither a constructor value, are read at the same type. -/
theorem readTy_eq_of_head {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f f' : Sem}
    (h : (∃ nm r' c₁ gs c₂ gs', f = .dat nm r' c₁ gs ∧ f' = .dat nm r' c₂ gs') ∨
      ((∀ nm r' c₁ gs, f ≠ .dat nm r' c₁ gs) ∧ ∀ nm r' c₁ gs, f' ≠ .dat nm r' c₁ gs)) :
    dm.readTy Γ d r c i e f = dm.readTy Γ d r c i e f' := by
  rcases h with ⟨nm, r', c₁, gs, c₂, gs', rfl, rfl⟩ | ⟨hf, hf'⟩
  · unfold DataModel.readTy
    generalize dm.sig.shape d r c i (e.map Sem.small) = sh
    cases sh <;> rfl
  · unfold DataModel.readTy
    generalize dm.sig.shape d r c i (e.map Sem.small) = sh
    cases sh with
    | sub d' r₀ =>
      cases f with
      | dat nm r' c₁ gs => exact absurd rfl (hf nm r' c₁ gs)
      | _ =>
        cases f' with
        | dat nm r' c₁ gs => exact absurd rfl (hf' nm r' c₁ gs)
        | _ => rfl
    | _ => rfl

/-- **Off a tree-typed shape `readTy` does not read the field.** -/
theorem readTy_eq_of_not_sub {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} (f f' : Sem)
    (hs : ∀ d' r₀, dm.sig.shape d r c i (e.map Sem.small) ≠ .sub d' r₀) :
    dm.readTy Γ d r c i e f = dm.readTy Γ d r c i e f' := by
  unfold DataModel.readTy
  generalize dm.sig.shape d r c i (e.map Sem.small) = sh at hs
  cases sh with
  | sub d' r₀ => exact absurd rfl (hs d' r₀)
  | _ => rfl

/-- **A field that is no constructor value is read at its shape's type.** -/
theorem readTy_of_not_dat {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem}
    (hf : ∀ nm r' c₁ gs, f ≠ .dat nm r' c₁ gs) :
    dm.readTy Γ d r c i e f = dm.shapeReadTy (dm.sig.shape d r c i (e.map Sem.small)) := by
  unfold DataModel.readTy
  generalize dm.sig.shape d r c i (e.map Sem.small) = sh
  cases sh with
  | sub d' r₀ =>
    cases f with
    | dat nm r' c₁ gs => exact absurd rfl (hf nm r' c₁ gs)
    | _ => rfl
  | _ => rfl

/-- A number rewritten to its tuple form is read at the same type, where the number was an open
member of the type its read gave it (at a tree-typed shape it cannot be: no number is a member of
`rawTy`). From the three facts above, not `readTy`'s definition. -/
theorem readTy_el0_succ {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {n : Nat} {w : Sem} {U : TyM}
    (hU : dm.readTy Γ d r c i e (.el0 Nat (n + 1)) = some U) (hO : dm.OMem Γ U (.el0 Nat (n + 1))) :
    dm.readTy Γ d r c i e (.dat "Nat" natRec 1 [w]) = some U := by
  by_cases hs : ∃ d' r₀, dm.sig.shape d r c i (e.map Sem.small) = .sub d' r₀
  · obtain ⟨d', r₀, hs⟩ := hs
    rw [readTy_of_not_dat (fun _ _ _ _ h => by cases h), hs] at hU
    simp only [DataModel.shapeReadTy, Option.some.injEq] at hU
    subst hU
    cases hO with
    | mem hm => exact absurd hm el0_not_mem_rawTy
  · rw [← hU]
    exact readTy_eq_of_not_sub _ _ (fun d' r₀ h => hs ⟨d', r₀, h⟩)

/-! ## Open membership is closed under moving parts out -/

/-- One field moved below its old value stays open where the old one was, given that the move keeps
open membership at every type (`ih`): `⊥` stays `⊥`; a completion stays a completion; a field read
at a type keeps that type (a tree keeps its name and record, `readTy_eq_of_head`; a number's tuple
form is read alike, `readTy_el0_succ`). -/
theorem oField_movedOf_of {d : IndDecl} {r : Rec} {c k : Nat} {e : List Sem} {f g : Sem} (hfg : MovedOf Γ f g)
    (ih : ∀ {U : TyM}, dm.OMem Γ U g → dm.OMem Γ U f) (h : dm.OField Γ d r c k e g) :
    dm.OField Γ d r c k e f := by
  cases h with
  | moved => cases hfg <;> exact .moved
  | fits e' t hl ht hmo hfit => exact .fits e' t hl ht (movedOf_trans hfg hmo) hfit
  | «at» e' U hl hU hO =>
    cases hfg with
    | moved => exact .moved
    | refl => exact .at e' U hl hU hO
    | dat _ => exact .at e' U hl ((readTy_eq_of_head (.inl ⟨_, _, _, _, _, _, rfl, rfl⟩)).trans hU) (ih hO)
    | succ _ => exact .at e' U hl (readTy_el0_succ hU hO) (ih hO)

mutual
/-- **Open membership is closed under moving parts out**: a value below an open member (`MovedOf`) is
an open member of the same type. -/
theorem omem_movedOf : ∀ {s' s : Sem}, MovedOf Γ s' s → ∀ {T : TyM}, dm.OMem Γ T s → dm.OMem Γ T s'
  | _, _, .moved _, T, _ => .moved T
  | _, _, .refl _, _, h => h
  | _, _, .dat hl, _, h => by
    cases h with
    | mem hm => exact omem_of_below (.dat hl) (mem_whole dm.read_wholeFields hm) hm
    | succ n hT hw =>
      cases hl with
      | cons hf hnil => cases hnil; exact .succ n hT (omem_movedOf hf hw)
    | dat hdc hc hlen hfs =>
      exact .dat hdc hc ((movedOfList_length hl).trans hlen) (oFields_movedOf hl hfs .nil)
  | _, _, .succ hs, _, h => by
    cases h with
    | mem hm => exact omem_of_below (.succ hs) (mem_whole dm.read_wholeFields hm) hm

/-- The same, field by field, the earlier fields below theirs. -/
theorem oFields_movedOf : ∀ {fs gs : List Sem}, MovedOfList Γ fs gs → ∀ {d : IndDecl} {r : Rec} {c k : Nat}
    {e e' : List Sem}, dm.OFields Γ d r c k e gs → MovedOfList Γ e' e → dm.OFields Γ d r c k e' fs
  | _, _, .nil, _, _, _, _, _, _, _, _ => .nil
  | _, _, .cons hf hl, _, _, _, _, _, _, h, he => by
    cases h with
    | cons hg hgs =>
      exact .cons (oField_movedOf_of hf (fun hO => omem_movedOf hf hO) (oField_weaken hg he))
        (oFields_movedOf hl hgs (movedOfList_append he (.cons hf .nil)))
end

/-- **Writing `⊥` at a path of an open member leaves an open member**, where the write is defined (the
model lemma of the orchestrator's write rule, 2026-11-21: the run tests that the write is defined at
every typed future; this says the result is then open): the result is below the old value
(`updAt_moved_props`), and open membership is closed under that (`omem_movedOf`). -/
theorem omem_updAt_moved (steps : List Step) {U : TyS} {T : TyM} {x y : Sem} (hx : dm.OMem Γ T x)
    (h : Sem.updAt dm Γ U (fun _ => .moved) steps x = some y) : dm.OMem Γ T y :=
  omem_movedOf (updAt_moved_props steps h).1 hx

end

end Ochr.Meaning.Strict
