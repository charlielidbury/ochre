import Ochr.Meaning.Conv.Unit

/-!
# N3 at constructor values: the congruence (conv2, 2026-11-28)

[Conv-cong] at two constructor values (`ConvH.ind`): the same declaration and constructor, fields
pairwise convertible, recorded parameters ignored. Proved for the claim as it stands (`Alike`: any
hint, any type both fit), with NO premise beyond the fields' own claims:
* both trees are members of the type `T` (a tree fits only as a member), so their records are
  `T`'s (`ReadMember.mem_dat_inv`), whatever record their parameters or the hint gave;
* each field fits the shape `T`'s declaration gives it at that record (`DataLib.mem_iff`), the SAME
  shape on both sides once the earlier fields agree; the fields are compared at that shape's type,
  while each is read at the hint the PROGRAM's declaration gives it (the claim lets the two differ,
  so the declaration `T` carries need not be the program's: conv1's premise (b) is not needed here);
* a junk leaf (a data code over the model's own carrier, which `shapeReadTy` does not type) fits
  only tagged elements `.el0 B b` (`encLeaf`), which are members of a code over a FOREIGN carrier
  (`foreignTy`: a declaration with no constructor has an empty carrier, so it is not `B`): conv1's
  premise (a) is not needed either.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.DataModel

/-- **Values that hold no code** (no closure, Π-closure or sealed program): `Plain`'s formers and
constructor values (whose recorded parameters are not compared, and are not asked anything). -/
inductive FO : Value → Prop
  | zero : FO .zero
  | unit : FO .unit
  | gfn (n : String) : FO (.gfn n)
  | loan (l : Nat) : FO (.loan l)
  | bot : FO .bot
  | abs (s : Nat) : FO (.abs s)
  | proof : FO .proof
  | tNat : FO .tNat
  | tUnit : FO .tUnit
  | sort (l : Nat) : FO (.sort l)
  | succ {a : Value} : FO a → FO (.succ a)
  | tRef {a : Value} : FO a → FO (.tRef a)
  | borrow {l : Nat} {a : Value} : FO a → FO (.borrow l a)
  | gloan {l : Nat} {a : Value} : FO a → FO (.gloan l a)
  | tEq {A a b : Value} : FO A → FO a → FO b → FO (.tEq A a b)
  | tInd {n : String} {as : List Value} : (∀ a ∈ as, FO a) → FO (.tInd n as)
  | ind {t : String} {c : Nat} {h : Hint} {ps fs : List Value} : (∀ f ∈ fs, FO f) → FO (.ind t c h ps fs)

theorem Plain.fo : ∀ {v : Value}, Plain v → FO v
  | _, .zero => .zero
  | _, .unit => .unit
  | _, .gfn n => .gfn n
  | _, .loan l => .loan l
  | _, .bot => .bot
  | _, .abs s => .abs s
  | _, .proof => .proof
  | _, .tNat => .tNat
  | _, .tUnit => .tUnit
  | _, .sort l => .sort l
  | _, .succ p => .succ p.fo
  | _, .tRef p => .tRef p.fo
  | _, .borrow p => .borrow p.fo
  | _, .gloan p => .gloan p.fo
  | _, .tEq p q r => .tEq p.fo q.fo r.fo
  | _, .tInd ps => .tInd fun a h => (ps a h).fo

/-! ## A code over a foreign carrier: what a junk leaf's values are members of -/

/-- A declaration with no constructor. -/
def emptyDecl : IndDecl := { name := "" }

/-- Its carrier is empty, at every record. -/
theorem car_empty (dm : DataModel) (r : Rec) (x : dm.car emptyDecl r) : False := by
  obtain ⟨⟨c, hc⟩, -, -, -⟩ := (DataLib.mem_iff dm.sig emptyDecl r _).1 ((dm.mem_iff_meanC emptyDecl r _).2 ⟨x, rfl⟩)
  exact absurd hc (by simp [emptyDecl])

/-- A data code over the carrier `B` that is not its declaration's carrier: its members are the
tagged elements `.el0 B b` (`DataModel.readFn`'s second branch). -/
noncomputable def foreignTy (B : Type) : TyM := .t0 B (.data emptyDecl (fun _ => .none) B)

theorem el0_mem_foreign (dm : DataModel) {B : Type} (b : B) : Sem.el0 B b ∈ₛ[dm.read] foreignTy B := by
  refine ⟨b, ?_⟩
  show dm.readFn emptyDecl (fun _ => .none) B b = _
  have hB : B ≠ dm.car emptyDecl (fun _ => .none) := fun h => car_empty dm _ (cast h b)
  simp only [DataModel.readFn, dif_neg hB]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **Two alike fields that fit one shape mean the same**, at the hint they are read at, whatever
the shape: a `sub` at its data type, a `prf` as `•`, a leaf at its code, a junk leaf at a foreign
carrier's code. -/
theorem fitsOne_eq {f g : Value} {H : TyS} {sh : DataLib.Shape} (ih : Alike K ρ φ f g)
    (nf : NoProp K f) (ng : NoProp K g)
    (hf : DataLib.FitsOneM K.dm.sig sh (meanV K ρ φ H f)) (hg : DataLib.FitsOneM K.dm.sig sh (meanV K ρ φ H g)) :
    meanV K ρ φ H f = meanV K ρ φ H g := by
  cases sh with
  | sub d r =>
    have hU : K.dm.shapeReadTy (.sub d r) = some (K.dm.rawTy d r) := rfl
    exact ih H _ nf ng (.inr (.inl (K.dm.fits_readTy hf hU))) (.inr (.inl (K.dm.fits_readTy hg hU)))
  | prf d r => rw [hf.1, hg.1]
  | leaf B cd =>
    by_cases hown : K.dm.OwnCarrier cd
    · obtain ⟨b, hb⟩ := hf
      obtain ⟨b', hb'⟩ := hg
      obtain ⟨d3, r3, hdc, -⟩ := hown
      cases cd with
      | data d3' r3' A =>
        simp only [DataLib.encLeaf] at hb hb'
        exact ih H (foreignTy _) nf ng (.inr (.inl (hb ▸ el0_mem_foreign K.dm b)))
          (.inr (.inl (hb' ▸ el0_mem_foreign K.dm b')))
      | _ => simp [Code0.dataCode?] at hdc
    · have hU : K.dm.shapeReadTy (.leaf B cd) = some (.t0 B cd) := by
        simp only [DataModel.shapeReadTy, if_neg hown]
      exact ih H _ nf ng (.inr (.inl (K.dm.fits_readTy hf hU))) (.inr (.inl (K.dm.fits_readTy hg hU)))

/-- **Alike fields that fit one telescope mean the same**: the fields of two constructor values,
each read at the hint the program's declaration `d` gives it at the record `r` and the earlier
fields, and fitting the shapes `T`'s declaration `d₁` gives at `r` (the same shapes on both sides,
the earlier fields being equal by induction). -/
theorem meanFields_alike (d d₁ : IndDecl) (r : Rec) (c : Nat) :
    ∀ (fs gs : List Value) (i n : Nat) (e : List Sem), AlikeL K ρ φ fs gs → NoPropL K fs → NoPropL K gs →
      DataLib.FitsM K.dm.sig d₁ r c i n (e.map Sem.small) (meanFields K ρ φ d r c i e fs) →
      DataLib.FitsM K.dm.sig d₁ r c i n (e.map Sem.small) (meanFields K ρ φ d r c i e gs) →
      meanFields K ρ φ d r c i e fs = meanFields K ρ φ d r c i e gs
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h, _, _, _, _ => h.elim
  | _ :: _, [], _, _, _, h, _, _, _, _ => h.elim
  | f :: fs, g :: gs, i, n, e, ⟨hfg, hrest⟩, ⟨nf, nfs⟩, ⟨ng, ngs⟩, hF, hG => by
    show meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f ::
        meanFields K ρ φ d r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f]) fs =
      meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g ::
        meanFields K ρ φ d r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g]) gs
    cases n with
    | zero => exact absurd hF (by simp [DataLib.FitsM, meanFields])
    | succ n =>
      obtain ⟨f0, fs0, hfs, h1, h2⟩ := hF
      obtain ⟨g0, gs0, hgs, k1, k2⟩ := hG
      have hfs' : meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f ::
          meanFields K ρ φ d r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f]) fs = f0 :: fs0 := hfs
      have hgs' : meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g ::
          meanFields K ρ φ d r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g]) gs = g0 :: gs0 := hgs
      simp only [List.cons.injEq] at hfs' hgs'
      obtain ⟨rfl, rfl⟩ := hfs'
      obtain ⟨rfl, rfl⟩ := hgs'
      have e1 := fitsOne_eq hfg nf ng h1 k1
      rw [← e1] at k2 ⊢
      congr 1
      refine meanFields_alike d d₁ r c fs gs (i + 1) n _ hrest nfs ngs ?_ ?_
      · simpa [List.map_append] using h2
      · simpa [List.map_append] using k2

/-- A constructor value's meaning that fits a type is a tree: its declaration is found, is not a
proposition, and the tree is a member of the type at the type's record. -/
theorem ind_fit_tree {h : TyS} {T : TyM} {t : String} {c : Nat} {hh : Hint} {ps fs : List Value}
    (nv : NoProp K (.ind t c hh ps fs)) (fv : Fit K.dm.read T (meanV K ρ φ h (.ind t c hh ps fs))) :
    ∃ d r d₁, K.Γ.find? (·.name == t) = some d ∧ T.dataCode? = some (d₁, r) ∧ d₁.name = t ∧
      meanV K ρ φ h (.ind t c hh ps fs) = .dat t r c (meanFields K ρ φ d r c 0 [] fs) ∧
      DataLib.FitsM K.dm.sig d₁ r c 0 (DataLib.arity d₁ c) [] (meanFields K ρ φ d r c 0 [] fs) := by
  rcases meanV_ind_cases K ρ φ h t c hh ps fs with he | ⟨d, r, hd, he⟩
  · rw [he] at fv; exact absurd fv err_not_fit
  have hs : (d.sort == 0) = false := by
    have := nv.1 d hd; simpa using this
  have hn : d.name = t := by simpa using List.find?_some hd
  rw [hs] at he
  simp only [Bool.false_eq_true, if_false, DataModel.ctorR, hn] at he
  rw [he] at fv
  rcases fv with hm | hm | ⟨-, X, hX, -⟩
  · cases hm
  · obtain ⟨d₁, hT, hmem, hn₁⟩ := mem_dat_inv K.dm hm
    obtain ⟨⟨c', hc'⟩, fs', he', hfits⟩ := (DataLib.mem_iff K.dm.sig d₁ r _).1 hmem
    simp only [Sem.dat.injEq] at he'
    obtain ⟨-, -, rfl, rfl⟩ := he'
    exact ⟨d, r, d₁, hd, hT, hn₁, he, hfits⟩
  · cases hX

/-- **[Conv-cong] at constructor values, for the claim**: two constructor values of one declaration
and constructor whose fields are pairwise alike are alike. Assumes nothing (the recorded parameters
and hints are not compared; membership in the one type pins the records). -/
theorem alike_ind {t : String} {c : Nat} {hh hh' : Hint} {ps qs fs gs : List Value}
    (ih : AlikeL K ρ φ fs gs) : Alike K ρ φ (.ind t c hh ps fs) (.ind t c hh' qs gs) := by
  intro h T nv nw fv fw
  obtain ⟨d, r, d₁, hd, hT, -, ev, hF⟩ := ind_fit_tree nv fv
  obtain ⟨d', r', d₂, hd', hT', -, ew, hG⟩ := ind_fit_tree nw fw
  rw [hd] at hd'
  cases hd'
  rw [hT] at hT'
  simp only [Option.some.injEq, Prod.mk.injEq] at hT'
  obtain ⟨rfl, rfl⟩ := hT'
  rw [ev, ew, meanFields_alike d d₁ r c fs gs 0 _ [] ih nv.2 nw.2 hF hG]

/-! ## [Conv-refl] on values that hold no code: `==` ignores the parameters a constructor value
records, so it is not equality; it makes the two values alike, by the congruences -/

mutual
theorem FO.beq_alike : ∀ {v w : Value}, FO v → Value.beq v w = true → Alike K ρ φ v w
  | .zero, _, _, h => by rw [Plain.beq_eq .zero h]; exact Alike.rfl' _
  | .unit, _, _, h => by rw [Plain.beq_eq .unit h]; exact Alike.rfl' _
  | .gfn n, _, _, h => by rw [Plain.beq_eq (.gfn n) h]; exact Alike.rfl' _
  | .loan l, _, _, h => by rw [Plain.beq_eq (.loan l) h]; exact Alike.rfl' _
  | .bot, _, _, h => by rw [Plain.beq_eq .bot h]; exact Alike.rfl' _
  | .abs s, _, _, h => by rw [Plain.beq_eq (.abs s) h]; exact Alike.rfl' _
  | .proof, _, _, h => by rw [Plain.beq_eq .proof h]; exact Alike.rfl' _
  | .tNat, _, _, h => by rw [Plain.beq_eq .tNat h]; exact Alike.rfl' _
  | .tUnit, _, _, h => by rw [Plain.beq_eq .tUnit h]; exact Alike.rfl' _
  | .sort l, _, _, h => by rw [Plain.beq_eq (.sort l) h]; exact Alike.rfl' _
  | .succ a, w, .succ pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    exact alike_succ (FO.beq_alike pa h)
  | .tRef a, w, .tRef pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    exact alike_tRef (FO.beq_alike pa h)
  | .borrow l a, w, .borrow pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact alike_borrow (FO.beq_alike pa h)
  | .gloan l a, w, .gloan pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact alike_gloan (FO.beq_alike pa h)
  | .tEq A a b, w, .tEq pA pa pb, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact alike_tEq (FO.beq_alike pA h1) (FO.beq_alike pa h2) (FO.beq_alike pb h3)
  | .tInd n as, w, .tInd pas, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact alike_tInd (FO.beqList_alike pas h)
  | .ind t c hh ps fs, w, .ind pfs, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact alike_ind (FO.beqList_alike pfs h)

theorem FO.beqList_alike : ∀ {as bs : List Value}, (∀ a ∈ as, FO a) → Value.beqList as bs = true →
    AlikeL K ρ φ as bs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => by simp [Value.beqList] at h
  | _ :: _, [], _, h => by simp [Value.beqList] at h
  | a :: as, b :: bs, pas, h => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    exact ⟨FO.beq_alike (pas a (List.mem_cons_self ..)) h.1,
      FO.beqList_alike (fun x hx => pas x (List.mem_cons_of_mem _ hx)) h.2⟩
end

end

/-! ## The unit laws on values that hold no code -/

theorem FO.mkAnd {p q : Value} (hp : FO p) (hq : FO q) : FO (Ochr.mkAnd p q) := by
  unfold Ochr.mkAnd
  split
  · exact hq
  · exact hp
  · exact .tInd fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hp
      · exact hq

theorem FO.unitTop : ∀ (v : Value), FO v → FO (unitTop v) := by
  intro v
  induction v using unitTop.induct with
  | case1 p q ihp ihq =>
    intro h
    rw [Ochr.unitTop]
    cases h with
    | tInd hs => exact FO.mkAnd (ihp (hs p (by simp))) (ihq (hs q (by simp)))
  | case2 v hv => intro h; rw [Ochr.unitTop.eq_2 v hv]; exact h

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- A value that holds no code means the same at every hint, unless it is a constructor value (under
borrows and marks), whose meaning is never a type value. -/
theorem FO.hint : ∀ {v : Value}, FO v →
    (∀ h h', meanV K ρ φ h v = meanV K ρ φ h' v) ∨ (∀ h X, meanV K ρ φ h v ≠ .ty X)
  | _, .zero | _, .unit | _, .gfn _ | _, .loan _ | _, .bot | _, .abs _ | _, .proof | _, .tNat
  | _, .tUnit | _, .sort _ | _, .succ _ | _, .tRef _ | _, .tEq _ _ _ | _, .tInd _ => .inl fun _ _ => rfl
  | .borrow l a, .borrow p => by
    rcases FO.hint (v := a) p with e | e
    · exact .inl fun h₁ h₂ => e h₁ h₂
    · exact .inr fun h₁ X => e h₁ X
  | .gloan l a, .gloan p => by
    rcases FO.hint (v := a) p with e | e
    · exact .inl fun h₁ h₂ => e h₁ h₂
    · exact .inr fun h₁ X => e h₁ X
  | .ind t c hh ps fs, .ind _ => .inr fun h X he => by
    rcases meanV_ind_cases K ρ φ h t c hh ps fs with e | ⟨d, r, -, e⟩
    · rw [e] at he; cases he
    · rw [e] at he; split at he <;> cases he

/-- The unit laws applied to both sides keep the claim (any class). -/
theorem alike_of_unitTop_Q {Q : Value → Prop} (hu : UnitOk K ρ φ Q) {v w : Value} (pv : Q v) (pw : Q w)
    (ih : Alike K ρ φ (unitTop v) (unitTop w)) : Alike K ρ φ v w := by
  intro h T nv nw fv fw
  obtain ⟨nv', ev⟩ := hu.keep h T v pv nv fv
  obtain ⟨nw', ew⟩ := hu.keep h T w pw nw fw
  rw [← ev, ← ew]
  exact ih h T nv' nw' (ev ▸ fv) (ew ▸ fw)

/-- A value that holds no code and means a type value at one hint means it at every hint. -/
theorem FO.ty_uniform {v : Value} (pv : FO v) {h₀ : TyS} {X : TyM} (e : meanV K ρ φ h₀ v = .ty X) :
    ∀ h, meanV K ρ φ h v = .ty X := by
  rcases FO.hint (K := K) (ρ := ρ) (φ := φ) pv with u | u
  · exact fun h => (u h h₀).trans e
  · exact absurd e (u h₀ X)

/-- **(H3) PROVED on values that hold no code** (`unitOk_plain`'s proof, with `FO.ty_uniform` for
`plain_hint`: `And`'s arguments mean propositions, so they are not constructor values), from the
library's connectives (`LibOk`) and `And`'s parameters being propositions (`AndParams`). -/
theorem unitOk_fo (hl : LibOk K ρ φ) (ha : AndParams K) : UnitOk K ρ φ FO := by
  refine ⟨fun h T v pv nv fv => ?_⟩
  induction v using unitTop.induct generalizing h T with
  | case1 p q ihp ihq =>
    cases pv with
    | tInd hs =>
    have pp : FO p := hs p (by simp)
    have pq : FO q := hs q (by simp)
    have np : NoProp K p := nv.1
    have nq : NoProp K q := nv.2.1
    rcases meanV_tInd_cases K ρ φ h "And" [p, q] with he | ⟨d, hd, hpk⟩
    · rw [he] at fv; exact absurd fv ty_err_not_fit
    have m0 := hpk 0 _ rfl
    have m1 := hpk 1 _ rfl
    have m0' : meanV K ρ φ (.plain (K.dm.paramTy d 0 [])) p ∈ₛ[K.dm.read] TyM.univ 0 := by
      have e := ha d hd 0 ((meanParams K ρ φ d 0 [] [p, q]).take 0) (by decide)
      rw [e] at m0; exact m0
    have m1' : ∃ hq, meanV K ρ φ hq q ∈ₛ[K.dm.read] TyM.univ 0 := by
      have e := ha d hd 1 ((meanParams K ρ φ d 0 [] [p, q]).take 1) (by decide)
      rw [e] at m1; exact ⟨_, m1⟩
    obtain ⟨p', hp'⟩ := mem_univ0' m0'
    obtain ⟨hq₀, m1''⟩ := m1'
    obtain ⟨q', hq'⟩ := mem_univ0' m1''
    have ep : ∀ h₀, meanV K ρ φ h₀ p = .ty (TyM.prop p') := pp.ty_uniform hp'
    have eq : ∀ h₀, meanV K ρ φ h₀ q = .ty (TyM.prop q') := pq.ty_uniform hq'
    obtain ⟨np', eup⟩ := ihp (.plain (TyM.univ 0)) (TyM.univ 0) pp np
      (.inr (.inl (by rw [ep]; exact ty_univ0_mem p')))
    obtain ⟨nq', euq⟩ := ihq (.plain (TyM.univ 0)) (TyM.univ 0) pq nq
      (.inr (.inl (by rw [eq]; exact ty_univ0_mem q')))
    have up : ∀ h₀, meanV K ρ φ h₀ (unitTop p) = .ty (TyM.prop p') :=
      (FO.unitTop p pp).ty_uniform (eup.trans (ep _))
    have uq : ∀ h₀, meanV K ρ φ h₀ (unitTop q) = .ty (TyM.prop q') :=
      (FO.unitTop q pq).ty_uniform (euq.trans (eq _))
    have hand := hl.and p q p' q' ep eq h
    rw [Ochr.unitTop, hand]
    unfold Ochr.mkAnd
    split
    · rename_i hT
      have e1 : p' = True := prop_inj' ((up (.plain TyM.err)).symm.trans (by rw [hT]; exact hl.tru _))
      subst e1
      refine ⟨nq', ?_⟩
      rw [uq]
      congr 2
      exact propext ⟨fun hq => ⟨trivial, hq⟩, fun hq => hq.2⟩
    · rename_i hT _
      have e1 : q' = True := prop_inj' ((uq (.plain TyM.err)).symm.trans (by rw [hT]; exact hl.tru _))
      subst e1
      refine ⟨np', ?_⟩
      rw [up]
      congr 2
      exact propext ⟨fun hp => ⟨hp, trivial⟩, fun hp => hp.1⟩
    · exact ⟨⟨np', nq', trivial⟩, hl.and _ _ p' q' up uq h⟩
  | case2 v hv =>
    rw [Ochr.unitTop.eq_2 v hv]
    exact ⟨nv, rfl⟩

end

/-! ## N3 for values that hold no code (part A): plain values and constructor values -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {G : Premises} {gs : List GDef}

mutual
/-- **N3 for values that hold no code** (part A): a derivation of `v ≡ w` in the machine's instance,
both holding no code, makes them alike, given [Conv-fun]'s premise (only between two globals here)
and the unit laws. Constructor values by `alike_ind` (nothing assumed); `==` by `FO.beq_alike`. -/
theorem convV_alike_fo (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ FO) :
    ∀ {v w : Value}, ConvV Syn.machine G gs v w → FO v → FO w → Alike K ρ φ v w
  | _, _, .refl h, pv, _ => FO.beq_alike pv h
  | _, _, .unit _ _ d, pv, pw =>
    alike_of_unitTop_Q hu pv pw (convH_alike_fo hp hu d (FO.unitTop _ pv) (FO.unitTop _ pw))

theorem convH_alike_fo (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ FO) :
    ∀ {v w : Value}, ConvH Syn.machine G gs v w → FO v → FO w → Alike K ρ φ v w
  | _, _, .refl h, pv, _ => FO.beq_alike pv h
  | _, _, .succ d, .succ pa, .succ pb => alike_succ (convV_alike_fo hp hu d pa pb)
  | _, _, .tRef d, .tRef pa, .tRef pb => alike_tRef (convV_alike_fo hp hu d pa pb)
  | _, _, .tInd d, .tInd pa, .tInd pb => alike_tInd (convL_alike_fo hp hu d pa pb)
  | _, _, .tEq d1 d2 d3, .tEq p1 p2 p3, .tEq q1 q2 q3 =>
    alike_tEq (convV_alike_fo hp hu d1 p1 q1) (convV_alike_fo hp hu d2 p2 q2)
      (convV_alike_fo hp hu d3 p3 q3)
  | _, _, .borrow d, .borrow pa, .borrow pb => alike_borrow (convV_alike_fo hp hu d pa pb)
  | _, _, .ind _ d, .ind pa, .ind pb => alike_ind (convL_alike_fo hp hu d pa pb)
  | _, _, .sealed _, pv, _ => nomatch pv
  | _, _, .piCong _ _ _, pv, _ => nomatch pv
  | _, _, .pi _, pv, _ => nomatch pv
  | _, _, .fn _ _ _ _ _ _ h, _, _ => hp _ _ h

theorem convL_alike_fo (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ FO) :
    ∀ {as bs : List Value}, ConvL Syn.machine G gs as bs → (∀ a ∈ as, FO a) → (∀ b ∈ bs, FO b) →
      AlikeL K ρ φ as bs
  | _, _, .nil, _, _ => trivial
  | _, _, .cons d ds, pa, pb =>
    ⟨convV_alike_fo hp hu d (pa _ (List.mem_cons_self ..)) (pb _ (List.mem_cons_self ..)),
      convL_alike_fo hp hu ds (fun a h => pa a (List.mem_cons_of_mem _ h))
        (fun b h => pb b (List.mem_cons_of_mem _ h))⟩
end

end

end Ochr.Meaning.Conv
