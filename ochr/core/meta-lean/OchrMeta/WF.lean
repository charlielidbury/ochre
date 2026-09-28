import OchrMeta.WFClose

/-! # Lemma 0 (invariance): every run preserves the well-formedness invariants

meta-model-v1 §2.1 lists W1 (unique holders), W2 (bound loans), W3 (acyclicity) and W4 (clean
crossings).  In this machine they read as follows, for a state with values `V` in flight
(results produced but not yet bound):

* `fresh`: every name is below the fresh-name counter;
* `shallowE`/`shallowV`: no borrows inside data (a value is a borrow of borrow-free content, or
  borrow-free);
* `uniq` (W1): each borrow has one holder (a binding or a value in flight);
* `live` (W2): every loan occurring in the environment is live: its borrow is held;
* `owned`: no dangling borrows: every held borrow's loan occurs in the environment;
* `clean` (W4): values in flight carry no loans;
* `acyc` (W3, as an order): loans inside a borrow's content are younger (larger) than it;
* `tmps`: the argument temporaries `tmp i` of [Call] are loan-free (they are values in flight
  parked in the environment; `takeTemps` moves them back into flight).

Lemma 0 holds for *source* programs: terms that do not name the machine's temporaries
(`Term.NoTmp`).  Without that side condition it is false: from `⟨[[]], 0⟩`, the call
`f(0, &tmp 0)` of an opaque `f(x : Nat, y : &Nat) : Nat` borrows the first argument's temporary
(`tmp 0 ↦ loan_0`), `takeTemps` puts `loan_0` in flight next to `borrow_0 0`, and [Close]
consumes the borrow, leaving the result `⌈f(loan_0, 0)⌉` with a loan whose borrow is gone.

The proof is in `WFCore`/`WFSet`/`WFOps`/`WFClose`, on the list of bindings `Ω.flatten`
(`Inv`); `wfv_iff` translates.
-/

namespace OchrMeta

/-- The borrow a value holds at its top, if any. -/
def Val.held : Val → List Nat
  | .borrow l _ => [l]
  | _ => []

/-- The held borrow with its content. -/
def Val.heldPairs : Val → List (Nat × Val)
  | .borrow l c => [(l, c)]
  | _ => []

/-- Borrows only at the top, with borrow-free content (RULES §1: no borrows inside data). -/
def Val.Shallow (v : Val) : Prop := v.nb = 0 ∨ ∃ l c, v = .borrow l c ∧ c.nb = 0

def Env.held (Ω : Env) : List Nat := Ω.flatten.flatMap fun b => b.2.held
def Env.heldPairs (Ω : Env) : List (Nat × Val) := Ω.flatten.flatMap fun b => b.2.heldPairs

/-- Lemma 0's invariant for a state `s` with the values `V` in flight. -/
structure WFv (s : St) (V : List Val) : Prop where
  fresh : ∀ l, (l ∈ s.env.names ∨ ∃ v ∈ V, l ∈ v.names) → l < s.next
  shallowE : ∀ F ∈ s.env, ∀ b ∈ F, b.2.Shallow
  shallowV : ∀ v ∈ V, v.Shallow
  uniq : (s.env.held ++ V.flatMap Val.held).Nodup
  live : ∀ l ∈ s.env.loans, l ∈ s.env.held ++ V.flatMap Val.held
  owned : ∀ l ∈ s.env.held ++ V.flatMap Val.held, l ∈ s.env.loans
  clean : ∀ v ∈ V, v.loans = []
  acyc : ∀ p ∈ s.env.heldPairs, ∀ m ∈ p.2.loans, p.1 < m
  tmps : ∀ F ∈ s.env, ∀ b ∈ F, (∃ i, b.1 = .tmp i) → b.2.loans = []

/-- A well-formed state (nothing in flight). -/
def WF (s : St) : Prop := WFv s []

/-! ## Source programs: no machine temporaries -/

/-- A variable a source program may name: anything but an argument temporary `tmp i`. -/
def Var.NoTmp : Var → Prop
  | .tmp _ => False
  | _ => True

/-- A place is tmp-free when its root is (a place names no other variable). -/
def Place.NoTmp (p : Place) : Prop := p.root.NoTmp

mutual
/-- `t` names no argument temporary: in no place, `let` binder or match alias. -/
def Term.NoTmp : Term → Prop
  | .read p => p.NoTmp
  | .borrow p => p.NoTmp
  | .assign p t => p.NoTmp ∧ t.NoTmp
  | .letIn x t u => x.NoTmp ∧ t.NoTmp ∧ u.NoTmp
  | .seq t u => t.NoTmp ∧ u.NoTmp
  | .zero => True
  | .succ t => t.NoTmp
  | .unit => True
  | .pair t u => t.NoTmp ∧ u.NoTmp
  | .mtch p tz y ts => p.NoTmp ∧ tz.NoTmp ∧ y.NoTmp ∧ ts.NoTmp
  | .call _ args _ => Term.NoTmpList args
  | .erase t => t.NoTmp
def Term.NoTmpList : List Term → Prop
  | [] => True
  | t :: ts => t.NoTmp ∧ Term.NoTmpList ts
end

/-- Every body of a program is tmp-free. -/
def Prog.NoTmp (P : Prog) : Prop := ∀ f d, P.find f = some d → ∀ b, d.body = some b → b.NoTmp

theorem Place.root_substVar (y : Var) (q : Place) :
    ∀ p : Place, (Place.substVar y q p).root = if p.root = y then q.root else p.root
  | .var x => by by_cases h : x = y <;> simp [Place.substVar, Place.root, h]
  | .deref p => by simp only [Place.substVar, Place.root]; exact Place.root_substVar y q p
  | .fst p => by simp only [Place.substVar, Place.root]; exact Place.root_substVar y q p
  | .snd p => by simp only [Place.substVar, Place.root]; exact Place.root_substVar y q p

theorem Place.noTmp_substVar {y : Var} {q : Place} (hq : q.NoTmp) {p : Place} (hp : p.NoTmp) :
    (Place.substVar y q p).NoTmp := by
  unfold Place.NoTmp at *
  rw [Place.root_substVar]
  split
  · exact hq
  · exact hp

mutual
theorem Term.noTmp_substVar {y : Var} {q : Place} (hq : q.NoTmp) :
    ∀ {t : Term}, t.NoTmp → (t.substVar y q).NoTmp
  | .read p, h => Place.noTmp_substVar hq h
  | .borrow p, h => Place.noTmp_substVar hq h
  | .assign p t, h => ⟨Place.noTmp_substVar hq h.1, Term.noTmp_substVar hq h.2⟩
  | .letIn x t u, h => by
    refine ⟨h.1, Term.noTmp_substVar hq h.2.1, ?_⟩
    by_cases hx : x = y
    · simp only [hx, if_true]; exact h.2.2
    · simp only [hx, if_false]; exact Term.noTmp_substVar hq h.2.2
  | .seq t u, h => ⟨Term.noTmp_substVar hq h.1, Term.noTmp_substVar hq h.2⟩
  | .zero, _ => trivial
  | .succ t, h => Term.noTmp_substVar (t := t) hq h
  | .unit, _ => trivial
  | .pair t u, h => ⟨Term.noTmp_substVar hq h.1, Term.noTmp_substVar hq h.2⟩
  | .mtch p tz z ts, h => by
    refine ⟨Place.noTmp_substVar hq h.1, Term.noTmp_substVar hq h.2.1, h.2.2.1, ?_⟩
    by_cases hz : z = y
    · simp only [hz, if_true]; exact h.2.2.2
    · simp only [hz, if_false]; exact Term.noTmp_substVar hq h.2.2.2
  | .call f args c, h => Term.noTmpList_substVar hq (ts := args) h
  | .erase t, h => Term.noTmp_substVar (t := t) hq h
theorem Term.noTmpList_substVar {y : Var} {q : Place} (hq : q.NoTmp) :
    ∀ {ts : List Term}, Term.NoTmpList ts → Term.NoTmpList (Term.substVarList y q ts)
  | [], _ => trivial
  | _ :: _, h => ⟨Term.noTmp_substVar hq h.1, Term.noTmpList_substVar hq h.2⟩
end

theorem Term.noTmpList_mem : ∀ {ts : List Term}, Term.NoTmpList ts → ∀ t ∈ ts, t.NoTmp
  | [], _ => by simp
  | t :: ts, h => by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · exact Term.noTmpList_mem h.2 u hu

/-! ## `WFv` is `Inv` on the list of bindings -/

theorem Val.held_eq : Val.held = Val.hd := by funext v; cases v <;> rfl
theorem Val.heldPairs_eq : Val.heldPairs = Val.hp := by funext v; cases v <;> rfl

theorem Env.held_eq (Ω : Env) : Ω.held = HE Ω.flatten := by simp only [Env.held, HE, Val.held_eq]

theorem Frame.mem_loans_iff {F : Frame} {l : Nat} : l ∈ F.loans ↔ ∃ b ∈ F, l ∈ b.2.loans := by
  induction F with
  | nil => simp [Frame.loans]
  | cons b F ih => obtain ⟨x, v⟩ := b; simp [Frame.loans, ih]

theorem Env.mem_loans_iff {Ω : Env} {l : Nat} : l ∈ Ω.loans ↔ ∃ b ∈ Ω.flatten, l ∈ b.2.loans := by
  induction Ω with
  | nil => simp [Env.loans]
  | cons F Ω ih =>
    simp only [Env.loans, List.mem_append, ih, Frame.mem_loans_iff, List.flatten_cons]
    constructor
    · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
      · exact ⟨b, Or.inl hb, h⟩
      · exact ⟨b, Or.inr hb, h⟩
    · rintro ⟨b, hb, h⟩
      rcases hb with hb | hb
      · exact Or.inl ⟨b, hb, h⟩
      · exact Or.inr ⟨b, hb, h⟩

theorem Env.mem_names_iff {Ω : Env} {l : Nat} : l ∈ Ω.names ↔ ∃ b ∈ Ω.flatten, l ∈ b.2.names := by
  simp [Env.names]

theorem Env.mem_heldPairs_iff {Ω : Env} {p : Nat × Val} :
    p ∈ Ω.heldPairs ↔ ∃ b ∈ Ω.flatten, p ∈ b.2.hp := by
  simp [Env.heldPairs, Val.heldPairs_eq]

theorem forall_flatten {Ω : Env} {P : Var × Val → Prop} :
    (∀ F ∈ Ω, ∀ b ∈ F, P b) ↔ ∀ b ∈ Ω.flatten, P b := by
  simp only [List.mem_flatten]
  constructor
  · rintro h b ⟨F, hF, hb⟩; exact h F hF b hb
  · intro h F hF b hb; exact h b ⟨F, hF, hb⟩

theorem wfv_iff {s : St} {V : List Val} : WFv s V ↔ Inv s.env.flatten V s.next := by
  have hH : s.env.held ++ V.flatMap Val.held = HE s.env.flatten ++ HV V := by
    rw [Env.held_eq, HV, Val.held_eq]
  constructor
  · intro h
    refine ⟨fun b hb l hl => h.fresh l (Or.inl (Env.mem_names_iff.mpr ⟨b, hb, hl⟩)),
      fun v hv l hl => h.fresh l (Or.inr ⟨v, hv, hl⟩), forall_flatten.mp h.shallowE, h.shallowV,
      hH ▸ h.uniq, ?_, ?_, h.clean, ?_, forall_flatten.mp h.tmps⟩
    · intro b hb l hl
      have := h.live l (Env.mem_loans_iff.mpr ⟨b, hb, hl⟩)
      rw [hH] at this; simpa using this
    · intro l hl
      have := h.owned l (by rw [hH]; simpa using hl)
      exact Env.mem_loans_iff.mp this
    · intro b hb p hp m hm
      exact h.acyc p (Env.mem_heldPairs_iff.mpr ⟨b, hb, hp⟩) m hm
  · intro h
    refine ⟨?_, forall_flatten.mpr h.sh, h.shV, hH ▸ h.uniq, ?_, ?_, h.clean, ?_,
      forall_flatten.mpr h.tmps⟩
    · rintro l (hl | ⟨v, hv, hl⟩)
      · obtain ⟨b, hb, hl⟩ := Env.mem_names_iff.mp hl; exact h.fresh b hb l hl
      · exact h.freshV v hv l hl
    · intro l hl
      obtain ⟨b, hb, hl⟩ := Env.mem_loans_iff.mp hl
      rw [hH]; simpa using h.live b hb l hl
    · intro l hl
      rw [hH] at hl
      exact Env.mem_loans_iff.mpr (h.owned l (by simpa using hl))
    · intro p hp m hm
      obtain ⟨b, hb, hp⟩ := Env.mem_heldPairs_iff.mp hp
      exact h.acyc b hb p hp m hm

/-! ## The induction on fuel -/

theorem St.setPlace_of_lookup {s s2 : St} {x : Var} {π : List Proj} {b new : Val}
    (hb : s.lookup x = some b) (h : s.setPlace x π new = some s2) :
    ∃ b', b.set π new = some b' ∧ s2 = s.setVar x b' := by
  simp only [St.setPlace, hb, Option.bind_some] at h
  cases hs : b.set π new with
  | none => rw [hs] at h; cases h
  | some b' => rw [hs] at h; cases h; exact ⟨b', rfl, rfl⟩

theorem Inv.flight_nb {E : Bs} {v : Val} {n : Nat} (h : Inv E [v] n) (hv : v.nb = 0) : Inv E [] n :=
  h.drop_flight (Val.hd_of_nb hv)

theorem exec_inv (P : Prog) (hP : P.NoTmp) : ∀ n, EvInv Term.NoTmp (exec P n) := by
  intro n
  induction n with
  | zero => intro s t s' v _ _ h; simp [exec] at h
  | succ n ih =>
    intro s t s' v ht hs h
    cases t with
    | read p =>
      simp only [exec] at h
      obtain ⟨s1, c, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨a1, a2, a3, b, hb, hg, hd⟩ := access_inv true p.root p.path _ s rfl hs h1
      have hcl : c.loans = [] := List.eq_nil_iff_forall_not_mem.mpr fun l hl => by
        simpa using access_clean a1 hb hg (hd rfl) l hl
      obtain ⟨R, hR, hset⟩ := St.lookup_perm hb
      have hbR : Inv ((p.root, b) :: R) [] s1.next := a1.perm hR (List.Perm.refl _)
      have hsh := hbR.sh _ List.mem_cons_self
      split at h2
      · cases h2
      · rename_i l w
        rcases Val.get_sh hsh hg with hπ | hnb
        · rw [hπ] at hg
          have hbc := Val.get_nil hg
          subst hbc
          split at h2
          · cases h2
          · rename_i s2 hsp
            simp only [Res.ok.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
            obtain ⟨b', hb', rfl⟩ := St.setPlace_of_lookup hb hsp
            rw [hπ] at hb'
            rw [Val.set_nil hb']
            obtain ⟨e1, e2, e3⟩ := hset .moved
            rw [e3]
            refine ⟨?_, by omega, by rw [e2, a3]⟩
            exact ((hbR.move_out (b := (p.root, .borrow l w)) hcl).add_bind (v := .moved) rfl rfl
              p.root).perm e1.symm (List.Perm.refl _)
        · simp [Val.nb] at hnb
      · simp only [Res.ok.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        have hchd : c.hd = [] := by cases c <;> simp_all [Val.hd]
        have hcnb : c.nb = 0 := by
          rcases Val.get_sh hsh hg with hπ | hnb
          · rw [hπ] at hg; rw [Val.get_nil hg] at hchd ⊢; exact Val.nb_of_sh hsh hchd
          · exact hnb
        exact ⟨a1.add_flight hcl hcnb, by omega, a3⟩
    | borrow p =>
      simp only [exec] at h
      obtain ⟨s1, c, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨a1, a2, a3, b, hb, hg, hd⟩ := access_inv true p.root p.path _ s rfl hs h1
      have hcl : c.loans = [] := List.eq_nil_iff_forall_not_mem.mpr fun l hl => by
        simpa using access_clean a1 hb hg (hd rfl) l hl
      obtain ⟨R, hR, hset⟩ := St.lookup_perm hb
      have hbR : Inv ((p.root, b) :: R) [] s1.next := a1.perm hR (List.Perm.refl _)
      split at h2
      · cases h2
      · rename_i hc
        have hcnb : c.nb = 0 := Classical.byContradiction fun hn => hc (Or.inr hn)
        split at h2
        · cases h2
        · rename_i s2 hsp
          simp only [Res.ok.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
          obtain ⟨b', hb', rfl⟩ := St.setPlace_of_lookup hb hsp
          obtain ⟨e1, e2, e3⟩ := hset b'
          have hx : ∀ i, p.root ≠ .tmp i := by
            intro i e
            have hp : p.NoTmp := by simpa [Term.NoTmp] using ht
            unfold Place.NoTmp at hp; rw [e] at hp; exact hp
          refine ⟨(hbR.set_loan hg hb' hcnb hcl hx).perm e1.symm (List.Perm.refl _), ?_, ?_⟩
          · show s.next ≤ s1.next + 1; omega
          · show (s1.setVar p.root b').env.length = s.env.length; rw [e2, a3]
    | assign p t =>
      simp only [exec] at h
      have ht' : p.NoTmp ∧ t.NoTmp := by simpa [Term.NoTmp] using ht
      obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨i1, i2, i3⟩ := ih s t s1 v1 ht'.2 hs h1
      obtain ⟨s2, c, h3, h4⟩ := Res.bind_eq_ok h2
      obtain ⟨a1, a2, a3, b, hb, hg, hd⟩ := access_inv true p.root p.path _ s1 rfl i1 h3
      have hcl : ∀ l ∈ c.loans, l ∈ v1.hd := fun l hl => by
        simpa using access_clean a1 hb hg (hd rfl) l hl
      obtain ⟨R, hR, hset⟩ := St.lookup_perm hb
      have hbR : Inv ((p.root, b) :: R) [v1] s2.next := a1.perm hR (List.Perm.refl _)
      split at h4
      · cases h4
      · rename_i hc
        split at h4
        · cases h4
        · rename_i s3 hsp
          split at h4
          · cases h4
          · rename_i s4 hdv
            simp only [Res.ok.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
            obtain ⟨b', hb', rfl⟩ := St.setPlace_of_lookup hb hsp
            obtain ⟨e1, e2, e3⟩ := hset b'
            -- the old content `c` still counts as a binding, next to the new one
            have hpre : Inv ((p.root, c) :: (s2.setVar p.root b').env.flatten) []
                (s2.setVar p.root b').next := by
              rw [e3]
              refine Inv.perm ?_ (List.Perm.cons _ e1.symm) (List.Perm.refl _)
              by_cases hπ : p.path = []
              · rw [hπ] at hg hb'
                obtain rfl := Val.get_nil hg
                rw [Val.set_nil hb']
                exact (hbR.move_in p.root).perm (List.Perm.swap _ _ _) (List.Perm.refl _)
              · have hv1 : v1.nb = 0 := Classical.byContradiction fun hn => hc ⟨hπ, hn⟩
                have hv1l : v1.loans = [] := i1.clean v1 (by simp)
                have hc0 : c.loans = [] := List.eq_nil_iff_forall_not_mem.mpr fun l hl => by
                  have := hcl l hl; rw [Val.hd_of_nb hv1] at this; simp at this
                have hcnb : c.nb = 0 := (Val.get_sh (hbR.sh _ List.mem_cons_self) hg).resolve_left hπ
                exact ((hbR.flight_nb hv1).set_clean hg hb' hπ hc0 hv1l hv1).add_bind hc0 hcnb p.root
            obtain ⟨d1, d2, d3⟩ := dropVal_inv hpre (by simp) hdv
            refine ⟨d1.add_flight rfl rfl, ?_, ?_⟩
            · rw [d2, e3]; omega
            · rw [d3, e2, a3, i3]
    | letIn x t u =>
      simp only [exec] at h
      have ht' : x.NoTmp ∧ t.NoTmp ∧ u.NoTmp := by simpa [Term.NoTmp] using ht
      obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨i1, i2, i3⟩ := ih s t s1 v1 ht'.2.1 hs h1
      obtain ⟨b1, b2, b3⟩ := St.bind_inv i1 x
      obtain ⟨s2, w, h3, h4⟩ := Res.bind_eq_ok h2
      obtain ⟨j1, j2, j3⟩ := ih _ u s2 w ht'.2.2 b1 h3
      split at h4
      · cases h4
      · rename_i c s3 hu
        split at h4
        · cases h4
        · rename_i s4 hdv
          simp only [Res.ok.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
          obtain ⟨u1, u2, u3⟩ := St.unbind_perm hu
          have hpre : Inv ((x, c) :: s3.env.flatten) [w] s3.next := u3 ▸ j1.perm u1 (List.Perm.refl _)
          obtain ⟨d1, d2, d3⟩ := dropVal_inv hpre (by simp [HV, Val.isBorrowOf_iff]) hdv
          exact ⟨d1, by omega, by omega⟩
    | seq t u =>
      simp only [exec] at h
      have ht' : t.NoTmp ∧ u.NoTmp := by simpa [Term.NoTmp] using ht
      obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨i1, i2, i3⟩ := ih s t s1 v1 ht'.1 hs h1
      split at h2
      · cases h2
      · rename_i s2 hdv
        obtain ⟨d1, d2, d3⟩ := dropVal_inv (i1.move_in .hole) (by simp) hdv
        obtain ⟨j1, j2, j3⟩ := ih s2 u s' v ht'.2 d1 h2
        exact ⟨j1, by omega, by omega⟩
    | zero => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact ⟨hs.add_flight rfl rfl, Nat.le_refl _, rfl⟩
    | unit => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact ⟨hs.add_flight rfl rfl, Nat.le_refl _, rfl⟩
    | erase t => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
                 exact ⟨hs.add_flight rfl rfl, Nat.le_refl _, rfl⟩
    | succ t =>
      simp only [exec] at h
      obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨i1, i2, i3⟩ := ih s t s1 v1 ht hs h1
      split at h2
      · rename_i hv
        simp only [Res.ok.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        exact ⟨(i1.flight_nb hv).add_flight (by simpa [Val.loans] using i1.clean v1 (by simp))
          (by simpa [Val.nb] using hv), i2, i3⟩
      · cases h2
    | pair t u =>
      simp only [exec] at h
      have ht' : t.NoTmp ∧ u.NoTmp := by simpa [Term.NoTmp] using ht
      obtain ⟨s1, v1, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨i1, i2, i3⟩ := ih s t s1 v1 ht'.1 hs h1
      obtain ⟨s2, w, h3, h4⟩ := Res.bind_eq_ok h2
      split at h4
      · rename_i hvw
        simp only [Res.ok.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
        -- the first component is borrow-free, so it does not matter while the second runs
        obtain ⟨j1, j2, j3⟩ := ih s1 u s2 w ht'.2 (i1.flight_nb hvw.1) h3
        refine ⟨(j1.flight_nb hvw.2).add_flight ?_ ?_, by omega, by omega⟩
        · simp [Val.loans, i1.clean v1 (by simp), j1.clean w (by simp)]
        · simp [Val.nb, hvw.1, hvw.2]
      · cases h4
    | mtch p tz y ts =>
      simp only [exec] at h
      have ht' : p.NoTmp ∧ tz.NoTmp ∧ y.NoTmp ∧ ts.NoTmp := by simpa [Term.NoTmp] using ht
      obtain ⟨s1, c, h1, h2⟩ := Res.bind_eq_ok h
      obtain ⟨a1, a2, a3, -⟩ := access_inv false p.root p.path _ s rfl hs h1
      split at h2
      · obtain ⟨j1, j2, j3⟩ := ih s1 tz s' v ht'.2.1 a1 h2
        exact ⟨j1, by omega, by omega⟩
      · obtain ⟨j1, j2, j3⟩ :=
          ih s1 _ s' v (Term.noTmp_substVar (y := y) (q := .fst p) ht'.1 ht'.2.2.2) a1 h2
        exact ⟨j1, by omega, by omega⟩
      · split at h2 <;> cases h2
    | call f args cc =>
      simp only [exec] at h
      have ht' : Term.NoTmpList args := by simpa [Term.NoTmp] using ht
      split at h
      · cases h
      · rename_i d hd
        split at h
        · simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨hs.add_flight rfl rfl, Nat.le_refl _, rfl⟩
        · obtain ⟨s1, u1, h1, h2⟩ := Res.bind_eq_ok h
          obtain ⟨e1, e2, e3⟩ := execArgs_inv ih args 0 (Term.noTmpList_mem ht') hs h1
          split at h2
          · cases h2
          · rename_i ws s2 htk
            obtain ⟨k1, k2, k3⟩ := takeTemps_inv _ e1 htk
            obtain ⟨c1, c2, c3⟩ :=
              callWith_inv ih cc f d (fun b hb => hP f d hd b hb) (by simpa using k1) h2
            exact ⟨c1, by omega, by omega⟩

/-- **Lemma 0.** A run of a source term from a well-formed state ends in a well-formed state
with its result in flight; the counter only grows; the number of frames is preserved. -/
theorem exec_wf (P : Prog) (hP : P.NoTmp) : ∀ (n : Nat) (s : St) (t : Term) (s' : St) (v : Val),
    t.NoTmp → WF s → exec P n s t = .ok s' v →
      WFv s' [v] ∧ s.next ≤ s'.next ∧ s'.env.length = s.env.length := by
  intro n s t s' v ht hs h
  obtain ⟨r1, r2, r3⟩ := exec_inv P hP n s t s' v ht (wfv_iff.mp hs) h
  exact ⟨wfv_iff.mpr r1, r2, r3⟩

/-- The frame pop of [Call] (dropping each binding of the top frame, the result `v` in flight)
preserves the invariant and removes one frame. -/
theorem popFrame_wf {s s' : St} {v : Val} (h : WFv s [v]) (hp : popFrame v s = some s') :
    WFv s' [v] ∧ s'.next = s.next ∧ s'.env.length + 1 = s.env.length := by
  obtain ⟨r1, r2, r3⟩ := popFrame_inv (wfv_iff.mp h) hp
  exact ⟨wfv_iff.mpr r1, r2, r3⟩

end OchrMeta
