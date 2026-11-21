import Ochr.Meaning.DataModel.Exists.Proto.Examples
import Ochr.Meaning.BotWrite

/-!
# Prototype: `Prop`-sorted declarations, by their truth predicates (no knot)

A `Prop`-sorted declaration's type at parameters means `prop (Nonempty car)` (`uTyR`): a
proposition, opaque, which a data type over a `Prop` parameter keeps as a leaf. `D3 (n) : Prop :=
D3Z | D3S(w : PB2(D3(n)))` with `PB2 (P : Prop) := MkPB2(x : P)` (accepted, `Exists/Probes.lean`'s
companions) makes `D3`'s field type a DATA type whose record holds `D3`'s own proposition as a
leaf; a leaf is fixed before the carriers, so it cannot be read off `D3`'s carrier while that is
built. So a `Prop`-sorted declaration's records are built from its TRUTH PREDICATE, defined first,
impredicatively, as the least predicate closed under its constructors (`evT`), and then its own
occurrences in its field types are leaves holding that predicate: no knot at all. That the code
then means the predicate (`ev_tyR`: `uTyR Ev (recK evK [n]) = prop (evT [n])`, by `propext`) is
what makes the leaf faithful to the run, which reads the occurrence as `uTyR`.

Shown on `Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))`.
-/

namespace Ochr.Meaning.DataModel.Exists.Proto

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- `Ev`, as the checker records it (fields `var 1 …` after the parameter `var 0`; the last field
innermost). -/
def evD : IndDecl :=
  { name := "Ev", params := [(hn "n", .nat)], sort := 0,
    ctors := [("EvZ", [("h", .eq .nat (.place (.var 0)) .zero)]),
      ("EvSS", [("m", .nat), ("h", .tind "Ev" [.place (.var 3)]),
        ("e", .eq .nat (.place (.var 0)) (.succ (.succ (.place (.var 3)))))])] }

theorem evD_idx : evD.indexFields 1 = [0] := by decide

/-- One unfolding of `Ev`, its own occurrences read by `S`. -/
def evF (S : List Sem → Prop) (ps : List Sem) : Prop :=
  parSem ps 0 = .el0 Nat 0 ∨ ∃ k : Nat, S [.el0 Nat k] ∧ parSem ps 0 = .el0 Nat (k + 2)

/-- **`Ev`'s truth predicate**: the least predicate closed under its constructors. -/
def evT (ps : List Sem) : Prop := ∀ S : List Sem → Prop, (∀ ps', evF S ps' → S ps') → S ps

theorem evF_mono {S S' : List Sem → Prop} (h : ∀ ps, S ps → S' ps) (ps : List Sem) : evF S ps → evF S' ps
  | .inl h0 => .inl h0
  | .inr ⟨k, hk, he⟩ => .inr ⟨k, h _ hk, he⟩

theorem evT_closed (ps : List Sem) (h : evF evT ps) : evT ps :=
  fun S hS => hS ps (evF_mono (fun _ hT => hT S hS) ps h)

theorem evT_unfold (ps : List Sem) (h : evT ps) : evF evT ps :=
  h (evF evT) (fun ps' hps => evF_mono (fun ps'' => evT_closed ps'') ps' hps)

/-- `Ev`'s field types: leaves throughout, its own occurrence holding the truth predicate. -/
noncomputable def evK : KnotSpec where
  d := evD
  N := fun _ => false
  fty := fun _ ps c i es =>
    if c = 0 ∧ i = 0 then .ty (TyM.prop (parSem ps 0 = .el0 Nat 0))
    else if c = 1 ∧ i = 0 then .ty TyM.nat
    else if c = 1 ∧ i = 1 then .ty (TyM.prop (evT [ofSmall (es.getD 0 .other)]))
    else if c = 1 ∧ i = 2 then .ty (TyM.prop (parSem ps 0 = (ofSmall (es.getD 0 .other)).succ.succ))
    else .ty TyM.err
  pEntry := fun ps _ => .small (parSem ps 0).small
  guarded := fun n R R' _ ps _ps' hp c i es => by
    have : ps = _ps' := by
      apply List.ext_getElem?
      intro j
      rcases h1 : ps[j]? with _ | v
      · rw [List.getElem?_eq_none_iff] at h1; rw [eq_comm, List.getElem?_eq_none_iff, ← hp.1]; exact h1
      · rcases h2 : _ps'[j]? with _ | v'
        · rw [List.getElem?_eq_none_iff] at h2; have := hp.1; rw [List.getElem?_eq_none_iff.2 (by omega)] at h1
          cases h1
        · have := hp.2 j v v' h1 h2; simp only [Bool.false_eq_true, if_false] at this; rw [this]
    subst this
    exact FTyAgree.refl _ _
  pEntry_agree := fun n ps ps' hp j => by
    rw [eq_parSem hp 0 rfl]

/-- A field whose type is a leaf code (not a data code) has that leaf as its shape. -/
theorem recK_shape_leaf (S : KnotSpec) (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i)
    {B : Type} (cd : Code0 B) (hcd : cd.isData = false)
    (hF : S.fty (recK S) ps c i (projIdx S.d c es) = .ty (.t0 B cd)) :
    uShape S.d (recK S ps) c i es = .leaf B cd := by
  apply uShape_leaf
  rw [recK_kind S ps c i _ (by rw [projIdx_len, h]), hF]
  exact kind_nondata hcd

theorem projIdx_ev1 (sm : Small) : projIdx evD 1 [sm] = [sm] := by
  simp [projIdx, evD_idx]

theorem projIdx_ev2 (sm sh : Small) : projIdx evD 1 [sm, sh] = [sm, .other] := by
  simp [projIdx, evD_idx]

section
variable (n : Sem)

theorem ev_shape0 : uShape evD (recK evK [n]) 0 0 [] = .leaf _ (.prop (n = .el0 Nat 0)) :=
  recK_shape_leaf evK [n] 0 0 [] rfl _ rfl (by simp [evK, parSem, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape10 : uShape evD (recK evK [n]) 1 0 [] = .leaf Nat .nat :=
  recK_shape_leaf evK [n] 1 0 [] rfl _ rfl (by simp [evK, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape11 (sm : Small) : uShape evD (recK evK [n]) 1 1 [sm] = .leaf _ (.prop (evT [ofSmall sm])) :=
  recK_shape_leaf evK [n] 1 1 [sm] rfl _ rfl (by simp [evK, projIdx_ev1, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape12 (sm sh : Small) :
    uShape evD (recK evK [n]) 1 2 [sm, sh] = .leaf _ (.prop (n = (ofSmall sm).succ.succ)) :=
  recK_shape_leaf evK [n] 1 2 [sm, sh] rfl _ rfl (by simp [evK, projIdx_ev2, parSem, TyM.prop, TyM.nat] <;> rfl)

theorem parSem_one : parSem [n] 0 = n := rfl

/-- **`Ev`'s carrier at its canonical record is inhabited exactly when its truth predicate holds.** -/
theorem ev_mem_iff : (∃ v, DataLib.Mem uSig evD (recK evK [n]) v) ↔ evT [n] := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (DataLib.mem_iff uSig evD _ v).1 hv
    apply evT_closed
    match c, hc, hf with
    | 0, _, hf =>
      obtain ⟨f, _, rfl, h1, -⟩ := hf
      have h1' : FitsOneM uSig (uShape evD (recK evK [n]) 0 0 []) f := h1
      rw [ev_shape0] at h1'
      obtain ⟨⟨h⟩, -⟩ := h1'
      exact .inl h
    | 1, _, hf =>
      obtain ⟨f0, _, rfl, h0, f1, _, rfl, h1, f2, _, rfl, h2, -⟩ := hf
      have h0' : FitsOneM uSig (uShape evD (recK evK [n]) 1 0 []) f0 := h0
      rw [ev_shape10] at h0'
      obtain ⟨k, rfl⟩ := h0'
      have h1' : FitsOneM uSig (uShape evD (recK evK [n]) 1 1 [(Sem.el0 Nat k).small]) f1 := h1
      rw [ev_shape11] at h1'
      obtain ⟨⟨hk⟩, -⟩ := h1'
      have h2' : FitsOneM uSig (uShape evD (recK evK [n]) 1 2 [(Sem.el0 Nat k).small, f1.small]) f2 := h2
      rw [ev_shape12] at h2'
      obtain ⟨⟨he⟩, -⟩ := h2'
      refine .inr ⟨k, hk, ?_⟩
      rw [parSem_one, he]
      show (Sem.el0 Nat k).succ.succ = _
      rw [Sem.succ_el0, Sem.succ_el0]
    | k + 2, hc, _ => simp [evD] at hc; omega
  · intro hT
    rcases evT_unfold [n] hT with h0 | ⟨k, hk, he⟩
    · refine ⟨_, (DataLib.mem_iff uSig evD _ _).2 ⟨⟨0, by decide⟩, [.proof], rfl, .proof, [], rfl, ?_, rfl⟩⟩
      show FitsOneM uSig (uShape evD (recK evK [n]) 0 0 []) _
      rw [ev_shape0]
      exact ⟨⟨h0⟩, rfl⟩
    · refine ⟨_, (DataLib.mem_iff uSig evD _ _).2 ⟨⟨1, by decide⟩, [.el0 Nat k, .proof, .proof], rfl,
        .el0 Nat k, _, rfl, ?_, .proof, _, rfl, ?_, .proof, [], rfl, ?_, rfl⟩⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 0 []) _
        rw [ev_shape10]; exact ⟨k, rfl⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 1 [(Sem.el0 Nat k).small]) _
        rw [ev_shape11]; exact ⟨⟨hk⟩, rfl⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 2 [(Sem.el0 Nat k).small, Sem.proof.small]) _
        rw [ev_shape12]
        refine ⟨⟨?_⟩, rfl⟩
        rw [← parSem_one n, he]
        show _ = (Sem.el0 Nat k).succ.succ
        rw [Sem.succ_el0, Sem.succ_el0]

/-- **`Ev(n)` means its truth predicate**: the code the run gives `Ev(n)` (`uTyR` at the canonical
record) is the proposition the records' leaves hold, so a leaf holding it is faithful. -/
theorem ev_tyR : uTyR evD (recK evK [n]) = TyM.prop (evT [n]) := by
  unfold uTyR
  rw [if_pos (by rfl)]
  congr 1
  apply propext
  rw [← ev_mem_iff]
  constructor
  · rintro ⟨x⟩; exact ⟨_, (DataLib.mem_iff_meanC uSig _ _ _).2 ⟨x, rfl⟩⟩
  · rintro ⟨v, hv⟩; obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig _ _ _).1 hv; exact ⟨x⟩

end

end Ochr.Meaning.DataModel.Exists.Proto
