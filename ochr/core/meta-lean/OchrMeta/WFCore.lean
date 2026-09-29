import OchrMeta.FrameCall

/-! # Lemma 0, part 1: the invariant on a list of bindings

The invariant of Lemma 0 (`WFv`, in `WF.lean`) depends on the environment only through the
list of its bindings (`Ω.flatten`), and on that list only up to permutation.  `Inv E V n` is
that invariant stated on a list of bindings `E`, values in flight `V` and counter `n`; every
machine step is then a small edit of the list: move a value between the environment and
flight, drop a value, overwrite a binding at a path, or end a borrow ([End]). -/

namespace OchrMeta

/-- The borrow a value holds at its top (a copy of `Val.held`, which lives in `WF.lean`). -/
def Val.hd : Val → List Nat
  | .borrow l _ => [l]
  | _ => []

/-- The held borrow with its content (a copy of `Val.heldPairs`). -/
def Val.hp : Val → List (Nat × Val)
  | .borrow l c => [(l, c)]
  | _ => []

/-- A copy of `Val.Shallow`. -/
def Val.Sh (v : Val) : Prop := v.nb = 0 ∨ ∃ l c, v = .borrow l c ∧ c.nb = 0

abbrev Bs := List (Var × Val)

def HE (E : Bs) : List Nat := E.flatMap fun b => b.2.hd
def HV (V : List Val) : List Nat := V.flatMap Val.hd

structure Inv (E : Bs) (V : List Val) (n : Nat) : Prop where
  fresh : ∀ b ∈ E, ∀ l ∈ b.2.names, l < n
  freshV : ∀ v ∈ V, ∀ l ∈ v.names, l < n
  sh : ∀ b ∈ E, b.2.Sh
  shV : ∀ v ∈ V, v.Sh
  uniq : (HE E ++ HV V).Nodup
  live : ∀ b ∈ E, ∀ l ∈ b.2.loans, l ∈ HE E ∨ l ∈ HV V
  owned : ∀ l, l ∈ HE E ∨ l ∈ HV V → ∃ b ∈ E, l ∈ b.2.loans
  clean : ∀ v ∈ V, v.loans = []
  acyc : ∀ b ∈ E, ∀ p ∈ b.2.hp, ∀ m ∈ p.2.loans, p.1 < m
  tmps : ∀ b ∈ E, (∃ i, b.1 = .tmp i) → b.2.loans = []

/-! ## Values -/

theorem Val.mem_hd {v : Val} {l : Nat} : l ∈ v.hd ↔ ∃ c, v = .borrow l c := by
  cases v <;> simp [Val.hd] <;> exact eq_comm

theorem Val.hd_of_nb {v : Val} (h : v.nb = 0) : v.hd = [] := by
  cases v <;> simp_all [Val.hd, Val.nb]

theorem Val.hd_names {v : Val} {l : Nat} (h : l ∈ v.hd) : l ∈ v.names := by
  cases v <;> simp_all [Val.hd, Val.names]

theorem Val.hd_length (v : Val) : v.hd.length ≤ 1 := by
  cases v <;> simp [Val.hd]

theorem Val.mem_hp {v : Val} {p : Nat × Val} (h : p ∈ v.hp) : v = .borrow p.1 p.2 := by
  cases v <;> simp_all [Val.hp]

theorem Val.hp_loans {v : Val} {p : Nat × Val} (h : p ∈ v.hp) : ∀ m ∈ p.2.loans, m ∈ v.loans := by
  rw [Val.mem_hp h]; simp [Val.loans]

theorem Val.hp_fst_names {v : Val} {p : Nat × Val} (h : p ∈ v.hp) : p.1 ∈ v.names := by
  rw [Val.mem_hp h]; simp [Val.names]

theorem Val.names_nil_wf {v : Val} (h1 : v.nb = 0) (h2 : v.loans = []) : v.names = [] := by
  induction v <;> simp_all [Val.nb, Val.loans, Val.names]

theorem Val.isBorrowOf_iff {v : Val} {l : Nat} : v.isBorrowOf l = true ↔ l ∈ v.hd := by
  cases v with
  | borrow m c => simp only [Val.isBorrowOf, Val.hd, beq_iff_eq, List.mem_singleton]; exact eq_comm
  | _ => simp [Val.isBorrowOf, Val.hd]

theorem Val.nb_of_sh {v : Val} (h : v.Sh) (hd : v.hd = []) : v.nb = 0 := by
  rcases h with h | ⟨l, c, rfl, _⟩
  · exact h
  · simp [Val.hd] at hd

theorem Val.sh_of_nb {v : Val} (h : v.nb = 0) : v.Sh := Or.inl h

theorem Val.sh_borrow {l : Nat} {c : Val} (h : (Val.borrow l c).Sh) : c.nb = 0 := by
  rcases h with h | ⟨l', c', he, hc⟩
  · simp [Val.nb] at h
  · cases he; exact hc

/-! ## Loan substitution -/

theorem Val.loans_substLoan {l : Nat} {w v : Val} {m : Nat}
    (h : m ∈ (Val.substLoan l w v).loans) : (m ∈ v.loans ∧ m ≠ l) ∨ (l ∈ v.loans ∧ m ∈ w.loans) := by
  induction v with
  | loan k =>
    simp only [Val.substLoan] at h
    split at h
    · rename_i hk; subst hk; right; simp [Val.loans, h]
    · rename_i hk; simp [Val.loans] at h; subst h; left; simp [Val.loans, hk]
  | _ => simp_all [Val.substLoan, Val.loans] <;> grind

theorem Val.loans_substLoan_keep {l : Nat} {w v : Val} {m : Nat} (h : m ∈ v.loans) (hm : m ≠ l) :
    m ∈ (Val.substLoan l w v).loans := by
  induction v with
  | loan k =>
    simp only [Val.loans, List.mem_singleton] at h; subst h
    simp [Val.substLoan, hm, Val.loans]
  | _ => simp_all [Val.substLoan, Val.loans] <;> grind

theorem Val.loans_substLoan_new {l : Nat} {w v : Val} {m : Nat} (h : l ∈ v.loans) (hm : m ∈ w.loans) :
    m ∈ (Val.substLoan l w v).loans := by
  induction v with
  | loan k =>
    simp only [Val.loans, List.mem_singleton] at h; subst h
    simp [Val.substLoan, hm]
  | _ => simp_all [Val.substLoan, Val.loans] <;> grind

theorem Val.substLoan_of_not_mem {l : Nat} {w v : Val} (h : l ∉ v.loans) : Val.substLoan l w v = v := by
  induction v with
  | loan k =>
    simp only [Val.loans, List.mem_singleton] at h
    simp [Val.substLoan, Ne.symm h]
  | _ => simp_all [Val.substLoan, Val.loans]

theorem Val.hd_substLoan {l : Nat} {w : Val} (hw : w.nb = 0) (v : Val) :
    (Val.substLoan l w v).hd = v.hd := by
  cases v with
  | loan k =>
    simp only [Val.substLoan]; split
    · exact Val.hd_of_nb hw
    · rfl
  | _ => rfl

theorem Val.hp_substLoan {l : Nat} {w : Val} (hw : w.nb = 0) (v : Val) :
    (Val.substLoan l w v).hp = v.hp.map fun p => (p.1, Val.substLoan l w p.2) := by
  cases v with
  | loan k =>
    simp only [Val.substLoan]; split
    · cases w <;> simp_all [Val.hp, Val.nb]
    · rfl
  | _ => rfl

theorem Val.sh_substLoan {l : Nat} {w v : Val} (hw : w.nb = 0) (h : v.Sh) : (Val.substLoan l w v).Sh := by
  rcases h with h | ⟨m, c, rfl, hc⟩
  · exact Or.inl (by rw [Val.nb_substLoan l w hw]; exact h)
  · exact Or.inr ⟨m, _, rfl, by rw [Val.nb_substLoan l w hw]; exact hc⟩

theorem Val.clearB_of_not_hd {l : Nat} {v : Val} (h : l ∉ v.hd) : Val.clearB l v = v := by
  apply Val.clearB_eq_self
  cases hb : v.isBorrowOf l
  · rfl
  · exact absurd (Val.isBorrowOf_iff.mp hb) h

theorem Val.clearB_borrow (l : Nat) (c : Val) : Val.clearB l (.borrow l c) = .moved := by
  simp [Val.clearB, Val.isBorrowOf]

/-! ## Held names -/

@[simp] theorem HE_nil : HE [] = [] := rfl
@[simp] theorem HV_nil : HV [] = [] := rfl
@[simp] theorem HE_cons (b : Var × Val) (E : Bs) : HE (b :: E) = b.2.hd ++ HE E := by simp [HE]
@[simp] theorem HV_cons (v : Val) (V : List Val) : HV (v :: V) = v.hd ++ HV V := by simp [HV]
@[simp] theorem HE_append (A B : Bs) : HE (A ++ B) = HE A ++ HE B := by simp [HE]
@[simp] theorem HV_append (A B : List Val) : HV (A ++ B) = HV A ++ HV B := by simp [HV]

theorem mem_HE {E : Bs} {l : Nat} : l ∈ HE E ↔ ∃ b ∈ E, l ∈ b.2.hd := by simp [HE]
theorem mem_HV {V : List Val} {l : Nat} : l ∈ HV V ↔ ∃ v ∈ V, l ∈ v.hd := by simp [HV]

theorem HE_perm {E E' : Bs} (h : E.Perm E') : (HE E).Perm (HE E') := h.flatMap_right _
theorem HV_perm {V V' : List Val} (h : V.Perm V') : (HV V).Perm (HV V') := h.flatMap_right _

theorem HE_map {g : Var × Val → Var × Val} {E : Bs} (h : ∀ b ∈ E, (g b).2.hd = b.2.hd) :
    HE (E.map g) = HE E := by
  induction E with
  | nil => rfl
  | cons b E ih =>
    simp only [List.map_cons, HE_cons]
    rw [h b List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem HE_names {E : Bs} {l : Nat} (h : l ∈ HE E) : ∃ b ∈ E, l ∈ b.2.names := by
  obtain ⟨b, hb, hl⟩ := mem_HE.mp h; exact ⟨b, hb, Val.hd_names hl⟩

/-! ## Structural edits of the invariant -/

namespace Inv
variable {E E' : Bs} {V V' : List Val} {n : Nat}

theorem perm (h : Inv E V n) (hE : E.Perm E') (hV : V.Perm V') : Inv E' V' n where
  fresh b hb := h.fresh b (hE.mem_iff.mpr hb)
  freshV v hv := h.freshV v (hV.mem_iff.mpr hv)
  sh b hb := h.sh b (hE.mem_iff.mpr hb)
  shV v hv := h.shV v (hV.mem_iff.mpr hv)
  uniq := ((HE_perm hE).append (HV_perm hV)).nodup_iff.mp h.uniq
  live b hb l hl := by
    rcases h.live b (hE.mem_iff.mpr hb) l hl with h1 | h1
    · exact Or.inl ((HE_perm hE).mem_iff.mp h1)
    · exact Or.inr ((HV_perm hV).mem_iff.mp h1)
  owned l hl := by
    have : l ∈ HE E ∨ l ∈ HV V := by
      rcases hl with h1 | h1
      · exact Or.inl ((HE_perm hE).mem_iff.mpr h1)
      · exact Or.inr ((HV_perm hV).mem_iff.mpr h1)
    obtain ⟨b, hb, hlb⟩ := h.owned l this
    exact ⟨b, hE.mem_iff.mp hb, hlb⟩
  clean v hv := h.clean v (hV.mem_iff.mpr hv)
  acyc b hb := h.acyc b (hE.mem_iff.mpr hb)
  tmps b hb := h.tmps b (hE.mem_iff.mpr hb)

theorem bump (h : Inv E V n) {n' : Nat} (hn : n ≤ n') : Inv E V n' where
  fresh b hb l hl := Nat.lt_of_lt_of_le (h.fresh b hb l hl) hn
  freshV v hv l hl := Nat.lt_of_lt_of_le (h.freshV v hv l hl) hn
  sh := h.sh
  shV := h.shV
  uniq := h.uniq
  live := h.live
  owned := h.owned
  clean := h.clean
  acyc := h.acyc
  tmps := h.tmps

/-- A loan-free binding moves from the environment into flight. -/
theorem move_out {b : Var × Val} (h : Inv (b :: E) V n) (hb : b.2.loans = []) : Inv E (b.2 :: V) n where
  fresh b' hb' := h.fresh b' (List.mem_cons_of_mem _ hb')
  freshV v hv := by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.fresh b (by simp)
    · exact h.freshV v hv
  sh b' hb' := h.sh b' (List.mem_cons_of_mem _ hb')
  shV v hv := by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.sh b (by simp)
    · exact h.shV v hv
  uniq := by
    have := h.uniq
    simp only [HE_cons, HV_cons, List.nodup_append] at this ⊢
    grind
  live b' hb' l hl := by
    have := h.live b' (List.mem_cons_of_mem _ hb') l hl
    simp only [HE_cons, HV_cons, List.mem_append] at this ⊢
    grind
  owned l hl := by
    have : l ∈ HE (b :: E) ∨ l ∈ HV V := by
      simp only [HE_cons, HV_cons, List.mem_append] at hl ⊢; grind
    obtain ⟨b', hb', hlb⟩ := h.owned l this
    rcases List.mem_cons.mp hb' with rfl | hb'
    · simp [hb] at hlb
    · exact ⟨b', hb', hlb⟩
  clean v hv := by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hb
    · exact h.clean v hv
  acyc b' hb' := h.acyc b' (List.mem_cons_of_mem _ hb')
  tmps b' hb' := h.tmps b' (List.mem_cons_of_mem _ hb')

/-- A value in flight is bound (it is loan-free, by `clean`). -/
theorem move_in {v : Val} (h : Inv E (v :: V) n) (x : Var) : Inv ((x, v) :: E) V n where
  fresh b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.freshV v (by simp)
    · exact h.fresh b hb
  freshV v' hv' := h.freshV v' (List.mem_cons_of_mem _ hv')
  sh b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.shV v (by simp)
    · exact h.sh b hb
  shV v' hv' := h.shV v' (List.mem_cons_of_mem _ hv')
  uniq := by
    have := h.uniq
    simp only [HE_cons, HV_cons, List.nodup_append] at this ⊢
    grind
  live b hb l hl := by
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [h.clean v (by simp)] at hl
    · have := h.live b hb l hl
      simp only [HE_cons, HV_cons, List.mem_append] at this ⊢
      grind
  owned l hl := by
    have : l ∈ HE E ∨ l ∈ HV (v :: V) := by
      simp only [HE_cons, HV_cons, List.mem_append] at hl ⊢; grind
    obtain ⟨b', hb', hlb⟩ := h.owned l this
    exact ⟨b', List.mem_cons_of_mem _ hb', hlb⟩
  clean v' hv' := h.clean v' (List.mem_cons_of_mem _ hv')
  acyc b hb p hp m hm := by
    rcases List.mem_cons.mp hb with rfl | hb
    · have := Val.hp_loans hp m hm
      simp [h.clean v (by simp)] at this
    · exact h.acyc b hb p hp m hm
  tmps b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact fun _ => h.clean v (by simp)
    · exact h.tmps b hb

/-- A value in flight that holds no borrow is dropped. -/
theorem drop_flight {v : Val} (h : Inv E (v :: V) n) (hv : v.hd = []) : Inv E V n where
  fresh := h.fresh
  freshV v' hv' := h.freshV v' (List.mem_cons_of_mem _ hv')
  sh := h.sh
  shV v' hv' := h.shV v' (List.mem_cons_of_mem _ hv')
  uniq := by have := h.uniq; simpa [hv] using this
  live b hb l hl := by have := h.live b hb l hl; simpa [hv] using this
  owned l hl := h.owned l (by simpa [hv] using hl)
  clean v' hv' := h.clean v' (List.mem_cons_of_mem _ hv')
  acyc := h.acyc
  tmps := h.tmps

/-- A loan-free, borrow-free value is put in flight. -/
theorem add_flight {v : Val} (h : Inv E V n) (hl : v.loans = []) (hn : v.nb = 0) : Inv E (v :: V) n where
  fresh := h.fresh
  freshV v' hv' := by
    rcases List.mem_cons.mp hv' with rfl | hv'
    · simp [Val.names_nil_wf hn hl]
    · exact h.freshV v' hv'
  sh := h.sh
  shV v' hv' := by
    rcases List.mem_cons.mp hv' with rfl | hv'
    · exact Val.sh_of_nb hn
    · exact h.shV v' hv'
  uniq := by have := h.uniq; simpa [Val.hd_of_nb hn] using this
  live b hb l hl := by have := h.live b hb l hl; simpa [Val.hd_of_nb hn] using this
  owned l hl := h.owned l (by simpa [Val.hd_of_nb hn] using hl)
  clean v' hv' := by
    rcases List.mem_cons.mp hv' with rfl | hv'
    · exact hl
    · exact h.clean v' hv'
  acyc := h.acyc
  tmps := h.tmps

theorem add_bind {v : Val} (h : Inv E V n) (hl : v.loans = []) (hn : v.nb = 0) (x : Var) :
    Inv ((x, v) :: E) V n := (h.add_flight hl hn).move_in x

theorem drop_bind {x : Var} {v : Val} (h : Inv ((x, v) :: E) V n) (hl : v.loans = []) (hn : v.nb = 0) :
    Inv E V n := (h.move_out (b := (x, v)) hl).drop_flight (Val.hd_of_nb hn)

/-- [End ℓ] of a borrow held by a binding that has been removed from the environment: its
content replaces every `loan_ℓ`. -/
theorem end_ {x : Var} {l : Nat} {d : Val} (h : Inv ((x, .borrow l d) :: E) V n) :
    Inv (E.map fun b => (b.1, Val.substLoan l d b.2)) V n := by
  have hd0 : d.nb = 0 := Val.sh_borrow (h.sh (x, .borrow l d) List.mem_cons_self)
  have hdl : ∀ m ∈ d.loans, l < m := fun m hm =>
    h.acyc (x, .borrow l d) List.mem_cons_self (l, d) (by simp [Val.hp]) m hm
  have hdn : ∀ m ∈ d.names, m < n := fun m hm =>
    h.fresh (x, .borrow l d) List.mem_cons_self m (by simp [Val.names, hm])
  have hHE : HE (E.map fun b => (b.1, Val.substLoan l d b.2)) = HE E := by
    exact HE_map (fun b _ => Val.hd_substLoan hd0 b.2)
  have hu := h.uniq
  simp only [HE_cons, Val.hd, List.cons_append, List.nodup_cons, List.mem_append] at hu
  refine ⟨?_, h.freshV, ?_, h.shV, ?_, ?_, ?_, h.clean, ?_, ?_⟩
  · intro b hb m hm
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    rcases Val.names_substLoan hm with hm | hm
    · exact h.fresh b0 (List.mem_cons_of_mem _ hb0) m hm
    · exact hdn m hm
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    exact Val.sh_substLoan hd0 (h.sh b0 (List.mem_cons_of_mem _ hb0))
  · rw [hHE]; exact hu.2
  · intro b hb m hm
    rw [hHE]
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    have key : m ≠ l → m ∈ HE E ∨ m ∈ HV V := by
      intro hml
      have := h.live b0 (List.mem_cons_of_mem _ hb0)
      rcases Val.loans_substLoan hm with ⟨hm1, _⟩ | ⟨_, hm2⟩
      · have := this m hm1
        simp only [HE_cons, Val.hd, List.singleton_append, List.mem_cons] at this
        grind
      · have := h.live _ (List.mem_cons_self) m (by simp [Val.loans, hm2])
        simp only [HE_cons, Val.hd, List.singleton_append, List.mem_cons] at this
        grind
    rcases Val.loans_substLoan hm with ⟨_, hml⟩ | ⟨_, hm2⟩
    · exact key hml
    · exact key (Nat.ne_of_gt (hdl m hm2))
  · intro m hm
    rw [hHE] at hm
    have hml : m ≠ l := by rintro rfl; grind
    have := h.owned m (by simp only [HE_cons, Val.hd, List.singleton_append, List.mem_cons]; grind)
    obtain ⟨b0, hb0, hmb⟩ := this
    rcases List.mem_cons.mp hb0 with rfl | hb0
    · -- `m` occurs in the ended content: it reappears where `loan_l` occurs
      obtain ⟨b1, hb1, hlb⟩ := h.owned l (Or.inl (by simp [Val.hd]))
      rcases List.mem_cons.mp hb1 with rfl | hb1
      · exact absurd (hdl l (by simpa [Val.loans] using hlb)) (Nat.lt_irrefl l)
      · exact ⟨_, List.mem_map_of_mem hb1, Val.loans_substLoan_new hlb (by simpa [Val.loans] using hmb)⟩
    · exact ⟨_, List.mem_map_of_mem hb0, Val.loans_substLoan_keep hmb hml⟩
  · intro b hb p hp m hm
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    simp only [Val.hp_substLoan hd0, List.mem_map] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    have hac := h.acyc b0 (List.mem_cons_of_mem _ hb0) p0 hp0
    rcases Val.loans_substLoan hm with ⟨hm1, _⟩ | ⟨hl1, hm2⟩
    · exact hac m hm1
    · exact Nat.lt_trans (hac l hl1) (hdl m hm2)
  · intro b hb ht
    simp only [List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    have := h.tmps b0 (List.mem_cons_of_mem _ hb0) ht
    simp only
    rw [Val.substLoan_of_not_mem (by simp [this]), this]

/-- [End ℓ] in place: the (unique) holder of `ℓ` becomes `⊥` and its content replaces every
`loan_ℓ`. -/
theorem endMap {x : Var} {l : Nat} {d : Val} (h : Inv E V n) (hx : (x, .borrow l d) ∈ E) :
    Inv (E.map fun b => (b.1, Val.substLoan l d (Val.clearB l b.2))) V n := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  have h' : Inv ((x, .borrow l d) :: (A ++ B)) V n := h.perm List.perm_middle (List.Perm.refl _)
  have hnot : ∀ b ∈ A ++ B, l ∉ b.2.hd := by
    intro b hb hl
    have hu := h'.uniq
    simp only [HE_cons, Val.hd, List.cons_append, List.nodup_cons, List.mem_append] at hu
    exact hu.1 (Or.inl (Or.inr (mem_HE.mpr ⟨b, hb, hl⟩)))
  have h2 := (h'.end_.add_bind (v := .moved) (by simp [Val.loans]) (by simp [Val.nb]) x).perm
    (List.Perm.cons _ (by rw [List.map_append])) (List.Perm.refl _)
  refine h2.perm ?_ (List.Perm.refl _)
  rw [List.map_append, List.map_cons]
  have e : ∀ C : Bs, (∀ b ∈ C, l ∉ b.2.hd) →
      C.map (fun b => (b.1, Val.substLoan l d (Val.clearB l b.2))) =
      C.map (fun b => (b.1, Val.substLoan l d b.2)) := by
    intro C hC
    apply List.map_congr_left
    intro b hb
    rw [Val.clearB_of_not_hd (hC b hb)]
  rw [e A (fun b hb => hnot b (List.mem_append_left _ hb)),
    e B (fun b hb => hnot b (List.mem_append_right _ hb))]
  simp only [Val.clearB_borrow, Val.substLoan]
  exact List.perm_middle.symm

end Inv

end OchrMeta
