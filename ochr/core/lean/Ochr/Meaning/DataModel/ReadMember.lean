import Ochr.Meaning.Places

/-!
# Reading along a path keeps membership, at a member (the slice's read lemma; docs/34 §17)

`follow_below_member`, the statement `Steps/Slice/ReadTyping.lean` asks of the data layer: a meaning
`s` below a whole member `w` of `T` (partial membership's member disjunct, `MovedOf`), read along a
path on which no strict prefix reads `⋆`; then the same path on `w` is defined and gives `w'` above
the read, a member of the type `U` the run gives on `w`. `U` is the field's type at `w`'s own
earlier fields: a data field is typed by its own record (`contentTyS`, by content), which a
member's field carries; any other field by the declaration's field type at `w`'s earlier fields.

The coherence it needs of the data model and `Γ` (`ReadCoherent`), on a set `P` of declarations and
records closed under the signature's data and proof fields, which contains the root's code: each
is found in `Γ` by its name, none is named `Nat`, and the signature's shapes there are canonical.
-/

namespace Ochr.Meaning.DataModel

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-- A shape is canonical: a leaf's code is not a data code, a data field's declaration is not
`Prop`-sorted, a proof field's is. -/
def ShapeCanon : Shape → Prop
  | .leaf _ c => c.isData = false
  | .sub d _ => d.sort ≠ 0
  | .prf d _ => d.sort = 0

/-- **What reading along paths needs of the data model and `Γ`**, on a set `P` of declarations and
records closed under the data and proof fields of the signature. -/
structure ReadCoherent (dm : DataModel) (Γ : List IndDecl) (P : IndDecl → Rec → Prop) : Prop where
  closed : ∀ d r c i e d' r', P d r →
    (dm.sig.shape d r c i e = .sub d' r' ∨ dm.sig.shape d r c i e = .prf d' r') → P d' r'
  found : ∀ d r, P d r → Γ.find? (·.name == d.name) = some d
  notNat : ∀ d r, P d r → d.name ≠ "Nat"
  canon : ∀ d r c i e, P d r → ShapeCanon (dm.sig.shape d r c i e)

/-- The declaration and record of a data code. -/
def _root_.Ochr.Meaning.Code0.dataCode? : {A : Type} → Code0 A → Option (IndDecl × Rec)
  | _, .data d r _ => some (d, r)
  | _, _ => none

def _root_.Ochr.Meaning.Code1.dataCode? : {A : Type 1} → Code1 A → Option (IndDecl × Rec)
  | _, .lift _ c => c.dataCode?
  | _, _ => none

def _root_.Ochr.Meaning.Code2.dataCode? : {A : Type 2} → Code2 A → Option (IndDecl × Rec)
  | _, .lift _ c => c.dataCode?
  | _, _ => none

/-- The data code a type is (at any carrier level, lifts included). -/
def _root_.Ochr.Meaning.TyM.dataCode? : TyM → Option (IndDecl × Rec)
  | .t0 _ c => c.dataCode?
  | .t1 _ c => c.dataCode?
  | .t2 _ c => c.dataCode?

/-- The fields of a member fit their shapes at the earlier fields, one by one. -/
theorem fitsM_get (S : Sig) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), FitsM S d r c i n e fs →
      ∀ (j : Nat) (f : Sem), fs[j]? = some f → FitsOneM S (S.shape d r c (i + j) (e ++ (fs.take j).map Sem.small)) f
  | 0, _, _, fs, h, j, f, hf => by
    have : fs = [] := h
    subst this; simp at hf
  | n + 1, i, e, fs, ⟨f0, fs', hfs, h1, h2⟩, j, f, hf => by
    subst hfs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      simpa using h1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hf
      have := fitsM_get S d r c n (i + 1) (e ++ [f0.small]) fs' h2 j f hf
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa [List.take_succ_cons] using this

variable (dm : DataModel)

/-- A member of a data type at any level is a member of its declaration at its record, which the
tree records. -/
theorem mem_dat_inv {T : TyM} {n : String} {r : Rec} {c : Nat} {gs : List Sem}
    (h : Sem.dat n r c gs ∈ₛ[dm.read] T) :
    ∃ d, T.dataCode? = some (d, r) ∧ dm.Mem d r (.dat n r c gs) ∧ d.name = n := by
  have key : ∀ (d : IndDecl) (r' : Rec) (A : Type) (a : A), dm.read.read d r' A a = .dat n r c gs →
      r' = r ∧ dm.Mem d r (.dat n r c gs) ∧ d.name = n := by
    intro d r' A a ha
    change dm.readFn d r' A a = _ at ha
    unfold readFn at ha
    split at ha
    · have hm : dm.Mem d r' (.dat n r c gs) := (dm.mem_iff_meanC d r' _).2 ⟨_, ha⟩
      obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d r' _).1 hm
      simp only [Sem.dat.injEq] at he
      obtain ⟨hn, hr, -⟩ := he
      subst hr
      exact ⟨rfl, hm, hn.symm⟩
    · cases ha
  cases T with
  | t0 A c0 =>
    obtain ⟨a, ha⟩ := h
    cases c0 with
    | data d r' A =>
      obtain ⟨rfl, hm, hn⟩ := key d r' A a ha
      exact ⟨d, rfl, hm, hn⟩
    | prop _ => cases ha
    | nat => cases ha
    | unit => cases ha
    | pi _ _ => cases ha
    | err => exact a.elim
  | t1 A c1 =>
    obtain ⟨a, ha⟩ := h
    cases c1 with
    | lift A' c0 =>
      cases c0 with
      | data d r' A =>
        obtain ⟨rfl, hm, hn⟩ := key d r' _ a.down ha
        exact ⟨d, rfl, hm, hn⟩
      | prop _ => cases ha
      | nat => cases ha
      | unit => cases ha
      | pi _ _ => cases ha
      | err => exact a.down.elim
    | univ0 => cases ha
    | univ1 => cases ha
    | pi _ _ => cases ha
  | t2 A c2 =>
    obtain ⟨a, ha⟩ := h
    cases c2 with
    | lift A' c1 =>
      cases c1 with
      | lift A'' c0 =>
        cases c0 with
        | data d r' A =>
          obtain ⟨rfl, hm, hn⟩ := key d r' _ a.down.down ha
          exact ⟨d, rfl, hm, hn⟩
        | prop _ => cases ha
        | nat => cases ha
        | unit => cases ha
        | pi _ _ => cases ha
        | err => exact a.down.down.elim
      | univ0 => cases ha
      | univ1 => cases ha
      | pi _ _ => cases ha
    | univ2 => cases ha
    | pi _ _ => cases ha

variable {dm} {Γ : List IndDecl} {P : IndDecl → Rec → Prop}

/-- A type all of whose data codes are in `P`. -/
def TyIn (P : IndDecl → Rec → Prop) (U : TyM) : Prop := ∀ d r, U.dataCode? = some (d, r) → P d r

theorem encLeaf_not_dat : ∀ {B : Type} (c : Code0 B) (b : B) (n : String) (r : Rec) (c' : Nat) (fs : List Sem),
    encLeaf c b ≠ .dat n r c' fs
  | _, .prop _, _, _, _, _, _ => by simp [encLeaf]
  | _, .nat, _, _, _, _, _ => by simp [encLeaf]
  | _, .unit, _, _, _, _, _ => by simp [encLeaf]
  | _, .pi _ _, _, _, _, _, _ => by simp [encLeaf]
  | _, .data _ _ _, _, _, _, _, _ => by simp [encLeaf]
  | _, .err, b, _, _, _, _ => nomatch b

/-- **A field of a member is a member of the type the run reads it at**: by its own record when it
is a constructor value, else at the declaration's field type at the member's earlier fields. -/
theorem field_mem (hcoh : ReadCoherent dm Γ P) {d : IndDecl} {r : Rec} {c : Nat} {gs : List Sem}
    (hP : P d r) (hm : dm.Mem d r (.dat d.name r c gs)) (i : Nat) (f : Sem) (hf : gs[i]? = some f) :
    f ∈ₛ[dm.read] (contentTyS dm Γ d.name r c i (gs.take i) f).m ∧
      TyIn P (contentTyS dm Γ d.name r c i (gs.take i) f).m := by
  obtain ⟨⟨c', hc'⟩, fs, he, hfits⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
  simp only [Sem.dat.injEq, true_and] at he
  obtain ⟨hc, hfs⟩ := he
  subst hfs
  subst hc
  have hfit := fitsM_get dm.sig d r c _ 0 [] gs hfits i f hf
  simp only [Nat.zero_add, List.nil_append] at hfit
  have hcan := hcoh.canon d r c i ((gs.take i).map Sem.small) hP
  have hfd : Γ.find? (·.name == d.name) = some d := hcoh.found d r hP
  -- the type at the member's own earlier fields, for a field that is not a constructor value
  have hother : ∀ (hnd : ∀ n r c fs, f ≠ .dat n r c fs),
      contentTyS dm Γ d.name r c i (gs.take i) f = .plain (dm.fieldTyR d r c i (gs.take i)) := by
    intro hnd
    unfold contentTyS
    split
    · rename_i n r c fs; exact absurd rfl (hnd _ _ _ _)
    · rename_i n r c fs _; exact absurd rfl (hnd _ _ _ _)
    · simp only [hfd]; rfl
  revert hfit hcan
  generalize hsh : dm.sig.shape d r c i ((gs.take i).map Sem.small) = sh
  intro hfit hcan
  have hft : dm.fieldTyR d r c i (gs.take i) = dm.shapeTy sh := by
    simp only [DataModel.fieldTyR, ← hsh, Sem.smallList_eq]
  cases sh with
  | leaf B cd =>
    obtain ⟨b, rfl⟩ := hfit
    rw [hother (fun n r c fs => encLeaf_not_dat cd b n r c fs), hft]
    simp only [ShapeCanon] at hcan
    cases cd with
    | data _ _ _ => simp [Code0.isData] at hcan
    | err => exact b.elim
    | prop _ => exact ⟨⟨b, rfl⟩, fun _ _ h => by cases h⟩
    | nat => exact ⟨⟨b, rfl⟩, fun _ _ h => by cases h⟩
    | unit => exact ⟨⟨b, rfl⟩, fun _ _ h => by cases h⟩
    | pi _ _ => exact ⟨⟨b, rfl⟩, fun _ _ h => by cases h⟩
  | sub d' r' =>
    have hP' : P d' r' := hcoh.closed d r c i _ d' r' hP (.inl hsh)
    have hm' : dm.Mem d' r' f := hfit
    obtain ⟨c'', fs', rfl, _⟩ := (DataLib.mem_iff dm.sig d' r' f).1 hm'
    have hnn : d'.name ≠ "Nat" := hcoh.notNat d' r' hP'
    have hfd' : Γ.find? (·.name == d'.name) = some d' := hcoh.found d' r' hP'
    have hs : (d'.sort == 0) = false := by simpa [ShapeCanon] using hcan
    have hct : contentTyS dm Γ d.name r c i (gs.take i) (.dat d'.name r' c'' fs') = .plain (dm.tyR d' r') := by
      unfold contentTyS
      split
      · rename_i h; simp only [Sem.dat.injEq] at h; exact absurd h.1 hnn
      · rename_i h; simp only [Sem.dat.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
        simp only [dataTyS, hfd']
      · rename_i h; exact absurd rfl (h _ _ _ _)
    rw [hct]
    refine ⟨(dm.mem_tyR d' r' hs _).2 hm', fun d'' r'' h => ?_⟩
    simp only [DataModel.tyR, hs, Bool.false_eq_true, if_false, TyM.dataCode?, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hP'
  | prf d' r' =>
    obtain ⟨rfl, hv⟩ := hfit
    rw [hother (fun n r c fs h => by cases h), hft]
    have hs : (d'.sort == 0) = true := by simpa [ShapeCanon] using hcan
    simp only [DataModel.shapeTy, hs, if_true]
    rw [dm.tyR_prop d' r' hs]
    exact ⟨⟨⟨hv⟩, rfl⟩, fun _ _ h => by cases h⟩

theorem movedOfList_get : ∀ {fs gs : List Sem}, MovedOfList Γ fs gs → ∀ (i : Nat) (f : Sem), fs[i]? = some f →
    ∃ g, gs[i]? = some g ∧ MovedOf Γ f g
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons h1 h2, 0, f, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact ⟨_, rfl, h1⟩
  | _ :: _, _ :: _, .cons _ h2, i + 1, f, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact movedOfList_get h2 i f h

theorem movedOfList_refl : ∀ (fs : List Sem), MovedOfList Γ fs fs
  | [] => .nil
  | f :: fs => .cons (.refl f) (movedOfList_refl fs)

/-- A non-`*` step on a constructor value not named `Nat` reads field `i` of it, whatever the
fields are. -/
theorem step_dat (T : TyS) (st : Step) (n : String) (r : Rec) (c : Nat) (fs : List Sem) (hn : n ≠ "Nat")
    (s1 : Sem) (T1 : TyS) (h : Sem.step dm Γ T st (.dat n r c fs) = some (s1, T1)) (hst : st ≠ .deref) :
    ∃ i, fs[i]? = some s1 ∧ ∀ (U : TyS) (gs : List Sem),
      Sem.step dm Γ U st (.dat n r c gs) = (gs[i]?).map (fun g => (g, contentTyS dm Γ n r c i (gs.take i) g)) := by
  have hsf : ∀ (c' i : Nat) (h : Sem.stepField dm Γ c' i (.dat n r c fs) = some (s1, T1)),
      c = c' ∧ fs[i]? = some s1 ∧ ∀ (gs : List Sem), Sem.stepField dm Γ c' i (.dat n r c gs)
        = (gs[i]?).map (fun g => (g, contentTyS dm Γ n r c i (gs.take i) g)) := by
    intro c' i h
    simp only [Sem.stepField] at h
    split at h
    · rename_i hc
      subst hc
      obtain ⟨f, hf, he⟩ := Option.map_eq_some_iff.mp h
      have hfs : f = s1 := (Prod.mk.inj he).1
      subst hfs
      exact ⟨rfl, hf, fun gs => by simp [Sem.stepField]⟩
    · cases h
  cases st with
  | deref => exact absurd rfl hst
  | proj i =>
    cases i with
    | zero =>
      have e : ∀ (U : TyS) (gs : List Sem), Sem.step dm Γ U (.proj 0) (.dat n r c gs) = Sem.stepField dm Γ 0 0 (.dat n r c gs) := by
        intro U gs
        simp only [Sem.step, Sem.asNat_dat]
        split
        · rename_i h'; simp only [Sem.dat.injEq] at h'; exact absurd h'.1 hn
        · rfl
      rw [e] at h
      obtain ⟨rfl, hf, hall⟩ := hsf 0 0 h
      exact ⟨0, hf, fun U gs => by rw [e, hall]⟩
    | succ i =>
      obtain ⟨rfl, hf, hall⟩ := hsf 0 (i + 1) h
      exact ⟨i + 1, hf, fun U gs => hall gs⟩
  | field g =>
    have e : ∀ (U : TyS) (gs : List Sem), Sem.step dm Γ U (.field g) (.dat n r c gs) =
        if n = g.ty ∧ n ≠ "Nat" then Sem.stepField dm Γ g.ctor g.idx (.dat n r c gs) else none := fun _ _ => rfl
    rw [e] at h
    split at h
    · rename_i hc
      obtain ⟨hcc, hf, hall⟩ := hsf g.ctor g.idx h
      exact ⟨g.idx, hf, fun U gs => by rw [e, if_pos hc, hall]⟩
    · cases h

/-- **One step**: a meaning below a whole member, not `⋆`, stepped; the member steps too, to a
whole member of the type the run gives it, above the meaning's step. -/
theorem step_below_member (hcoh : ReadCoherent dm Γ P) (Ts U : TyS) (st : Step) (s w s1 : Sem) (T1 : TyS)
    (hU : TyIn P U.m) (hw : w.whole) (hsw : MovedOf Γ s w) (hm : w ∈ₛ[dm.read] U.m) (hnp : s ≠ .proof)
    (h : Sem.step dm Γ Ts st s = some (s1, T1)) :
    ∃ w1 U1, Sem.step dm Γ U st w = some (w1, U1) ∧ MovedOf Γ s1 w1 ∧ w1.whole ∧
      w1 ∈ₛ[dm.read] U1.m ∧ TyIn P U1.m := by
  -- `*` is the identity
  by_cases hst : st = .deref
  · subst hst
    simp only [Sem.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, U, rfl, hsw, hw, hm, hU⟩
  -- the field read of a constructor value of `P` (not named `Nat`)
  have hdatcase : ∀ (n : String) (r : Rec) (c : Nat) (fs gs : List Sem), s = .dat n r c fs → w = .dat n r c gs →
      MovedOfList Γ fs gs → ∃ w1 U1, Sem.step dm Γ U st w = some (w1, U1) ∧ MovedOf Γ s1 w1 ∧ w1.whole ∧
        w1 ∈ₛ[dm.read] U1.m ∧ TyIn P U1.m := by
    intro n r c fs gs hs hw' hfg
    subst hs; subst hw'
    obtain ⟨d, hdc, hmd, hdn⟩ := mem_dat_inv dm hm
    have hP : P d r := hU d r hdc
    have hn : n ≠ "Nat" := hdn ▸ hcoh.notNat d r hP
    obtain ⟨i, hfi, hall⟩ := step_dat Ts st n r c fs hn s1 T1 h hst
    obtain ⟨g, hgi, hmo⟩ := movedOfList_get hfg i s1 hfi
    subst hdn
    obtain ⟨hgm, hgP⟩ := field_mem hcoh hP hmd i g hgi
    have hw' : ∀ f ∈ gs, f.whole := by simpa [Sem.whole] using hw
    refine ⟨g, _, by rw [hall U gs, hgi]; rfl, hmo, hw' g (List.mem_of_getElem? hgi), hgm, hgP⟩
  cases hsw with
  | moved =>
    exfalso
    cases st with
    | deref => exact hst rfl
    | proj i => cases i <;> simp [Sem.step, Sem.stepField, Sem.asNat, Sem.as] at h
    | field g => simp [Sem.step, Sem.stepField] at h
  | refl =>
    -- `s = w`: a number, or a constructor value
    cases s with
    | dat n r c fs => exact hdatcase n r c fs fs rfl rfl (movedOfList_refl fs)
    | el0 A a =>
      cases st with
      | deref => exact absurd rfl hst
      | proj i =>
        cases i with
        | zero =>
          simp only [Sem.step] at h
          split at h
          · rename_i m hmN
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨_, .plain TyM.nat, by simp only [Sem.step, hmN], .refl _, by simp [Sem.whole], ⟨m, rfl⟩,
              fun _ _ h => by cases h⟩
          · cases h
          · simp [Sem.stepField] at h
        | succ i => simp [Sem.step, Sem.stepField] at h
      | field g => simp [Sem.step, Sem.stepField] at h
    | proof => exact absurd rfl hnp
    | _ => cases st <;> first | exact absurd rfl hst | (rename_i i; cases i <;> simp [Sem.step, Sem.stepField, Sem.asNat, Sem.as] at h) | simp [Sem.step, Sem.stepField] at h
  | dat hfg => exact hdatcase _ _ _ _ _ rfl rfl hfg
  | @succ s' m hs' =>
    cases st with
    | deref => exact absurd rfl hst
    | proj i =>
      cases i with
      | zero =>
        have e : Sem.step dm Γ Ts (.proj 0) (.dat "Nat" natRec 1 [s']) = some (s', .plain TyM.nat) := by
          simp [Sem.step, Sem.asNat_dat]
        rw [e] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨.el0 Nat m, .plain TyM.nat, by simp [Sem.step, Sem.asNat, Sem.as], hs', by simp [Sem.whole], ⟨m, rfl⟩,
          fun _ _ h => by cases h⟩
      | succ i => simp [Sem.step, Sem.stepField] at h
    | field g => simp [Sem.step] at h

/-- The induction along the path, the meaning and the member followed at their own types. -/
theorem follow_below_member_gen (hcoh : ReadCoherent dm Γ P) :
    ∀ (ss : List Step) (Ts U : TyS) (s w x : Sem) (T' : TyS), TyIn P U.m → w.whole → MovedOf Γ s w →
      w ∈ₛ[dm.read] U.m →
      (∀ k < ss.length, ∀ y V, Sem.follow dm Γ Ts s (ss.take k) = some (y, V) → y ≠ .proof) →
      Sem.follow dm Γ Ts s ss = some (x, T') →
      ∃ w' U', Sem.follow dm Γ U w ss = some (w', U') ∧ MovedOf Γ x w' ∧ w' ∈ₛ[dm.read] U'.m
  | [], Ts, U, s, w, x, T', _, _, hsw, hm, _, hf => by
    simp only [Sem.follow, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨w, U, rfl, hsw, hm⟩
  | st :: sts, Ts, U, s, w, x, T', hU, hw, hsw, hm, hnp, hf => by
    simp only [Sem.follow] at hf
    obtain ⟨⟨s1, T1⟩, h1, hf'⟩ := Option.bind_eq_some_iff.mp hf
    have hs0 : s ≠ .proof := hnp 0 (by simp) s Ts rfl
    obtain ⟨w1, U1, hw1, hmo, hwh, hm1, hU1⟩ := step_below_member hcoh Ts U st s w s1 T1 hU hw hsw hm hs0 h1
    obtain ⟨w', U', hfw, hmo', hm'⟩ := follow_below_member_gen hcoh sts T1 U1 s1 w1 x T' hU1 hwh hmo hm1
      (fun k hk y V hy => hnp (k + 1) (by simp; omega) y V (by simp [Sem.follow, h1, hy])) hf'
    exact ⟨w', U', by simp [Sem.follow, hw1, hfw], hmo', hm'⟩

/-- **The slice's read lemma** (`Steps/Slice/ReadTyping.lean`, `follow_below_member`), with the
coherence it needs (`ReadCoherent` on a set `P` containing the root's data code): `s` below the
whole member `w` of `T`, read along `ss` with no strict prefix reading `⋆`, gives `x`; the same
path on `w` gives `w'` above `x`, a member of the type `U` the run gives on `w` (a data field by its
own record, any other field at the declaration's field type at `w`'s own earlier fields). When `x`
is `⋆`, so is `w'` (only `⋆` is above `⋆` in `MovedOf`). `hcov` is not needed. -/
theorem follow_below_member (dm : DataModel) (Γ : List IndDecl) (_hcov : ∀ d ∈ Γ, dm.covers d)
    (T : TyS) (s w : Sem) (ss : List Step) (x : Sem) (T' : TyS)
    (hw : w.whole) (hsw : DataModel.MovedOf Γ s w) (hm : w ∈ₛ[dm.read] T.m)
    (hnp : ∀ k < ss.length, ∀ y U, Sem.follow dm Γ T s (ss.take k) = some (y, U) → y ≠ .proof)
    (hf : Sem.follow dm Γ T s ss = some (x, T'))
    (P : IndDecl → Rec → Prop) (hcoh : ReadCoherent dm Γ P) (hT : TyIn P T.m) :
    ∃ w' U, Sem.follow dm Γ T w ss = some (w', U) ∧ DataModel.MovedOf Γ x w' ∧ w' ∈ₛ[dm.read] U.m :=
  follow_below_member_gen hcoh ss T T s w x T' hT hw hsw hm hnp hf

end Ochr.Meaning.DataModel
