import Ochr.Meaning.ClosureCE

/-!
# The closure lemma (the knot's data-layer half; docs/31 D73, D79)

A closure's meaning is built along its type's code from a function on meanings (its body's run,
the stages of a recursion, captures included: `closureAt R l φ ds out g` for ANY `g`). Here, in the
forms that hold (`ClosureCE.lean` records where the statements of `Steps/FixKnot.lean` fail):

* `closure_mem_of_total'`: a closure whose function is defined and good at every member argument
  (`OutGood`, and one final content per borrow parameter, as the run's bodies give) is a member of
  its code, at a data codomain whose code fits the closure's level; `closure_mem_prop'` at sort `0`,
  a codomain that is a proposition.
* `closure_apply'`: such a closure applied at member arguments (whose domains fit the level) is its
  function's result there, at the codomain the code reaches, as a call reads it (`callOf`).

The recursion stages appear only through `g`: their closures are built in `ClosureStage.lean`.
-/

namespace Ochr.Meaning

open Ochr Ochr.Meaning.Steps

universe u

/-- What the closure lemma needs of a level beside lawfulness, for the codes that fit it. -/
structure Lvl.Fits (L : Lvl.{u}) (Fit : TyM → Prop) : Prop where
  enc_mem : ∀ (T : TyM) (x : (L.codeOf T).1), L.enc (L.codeOf T).2 x ∈ₛ[L.read] T
  dec_mem : ∀ (T : TyM) (s : Sem), Fit T → s ∈ₛ[L.read] T → ∃ x, L.dec (L.codeOf T).2 s = some x
  fit_of : ∀ (T : TyM), (L.codeOf T).1 → Fit T
  toTy_code : ∀ (T : TyM), Fit T → T.Canon → L.toTy (L.codeOf T).2 = T

section
variable (R : DataRead)

theorem lvl0_fits : (lvl0 R).Fits (LevelFit 1) where
  enc_mem T x := by
    cases T with
    | t0 A c => exact ⟨x, rfl⟩
    | t1 A c => exact x.elim
    | t2 A c => exact x.elim
  dec_mem T s hT hs := by
    cases T with
    | t0 A c =>
      show ∃ x, Code0.dec R c s = some x
      have hs' : ∃ a, Code0.enc R c a = s := hs
      unfold Code0.dec; rw [dif_pos hs']; exact ⟨_, rfl⟩
    | t1 A c => exact absurd hT (by simp [LevelFit])
    | t2 A c => exact absurd hT (by simp [LevelFit])
  fit_of T x := by
    cases T with
    | t0 A c => simp [LevelFit]
    | t1 A c => exact x.elim
    | t2 A c => exact x.elim
  toTy_code T hT _ := by
    cases T with
    | t0 A c => rfl
    | t1 A c => exact absurd hT (by simp [LevelFit])
    | t2 A c => exact absurd hT (by simp [LevelFit])

theorem lvl1_fits : (lvl1 R).Fits (LevelFit 2) where
  enc_mem T x := by
    cases T with
    | t0 A c => exact ⟨x.down, rfl⟩
    | t1 A c => exact ⟨x, rfl⟩
    | t2 A c => exact x.down.elim
  dec_mem T s hT hs := by
    cases T with
    | t0 A c =>
      obtain ⟨a, ha⟩ := hs
      show ∃ x, Code1.dec R (.lift A c) s = some x
      unfold Code1.dec; rw [dif_pos ⟨⟨a⟩, ha⟩]; exact ⟨_, rfl⟩
    | t1 A c =>
      show ∃ x, Code1.dec R c s = some x
      have hs' : ∃ a, Code1.enc R c a = s := hs
      unfold Code1.dec; rw [dif_pos hs']; exact ⟨_, rfl⟩
    | t2 A c => exact absurd hT (by simp [LevelFit])
  fit_of T x := by
    cases T with
    | t0 A c => simp [LevelFit]
    | t1 A c => simp [LevelFit]
    | t2 A c => exact x.down.elim
  toTy_code T hT hc := by
    cases T with
    | t0 A c => rfl
    | t1 A c =>
      cases c with
      | lift => exact hc.elim
      | _ => rfl
    | t2 A c => exact absurd hT (by simp [LevelFit])

theorem lvl2_fits : (lvl2 R).Fits (LevelFit 3) where
  enc_mem T x := by
    cases T with
    | t0 A c => exact ⟨x.down.down, rfl⟩
    | t1 A c => exact ⟨x.down, rfl⟩
    | t2 A c => exact ⟨x, rfl⟩
  dec_mem T s _ hs := by
    cases T with
    | t0 A c =>
      obtain ⟨a, ha⟩ := hs
      show ∃ x, Code2.dec R (.lift _ (.lift A c)) s = some x
      unfold Code2.dec; rw [dif_pos ⟨⟨⟨a⟩⟩, ha⟩]; exact ⟨_, rfl⟩
    | t1 A c =>
      obtain ⟨a, ha⟩ := hs
      show ∃ x, Code2.dec R (.lift A c) s = some x
      unfold Code2.dec; rw [dif_pos ⟨⟨a⟩, ha⟩]; exact ⟨_, rfl⟩
    | t2 A c =>
      show ∃ x, Code2.dec R c s = some x
      have hs' : ∃ a, Code2.enc R c a = s := hs
      unfold Code2.dec; rw [dif_pos hs']; exact ⟨_, rfl⟩
  fit_of T _ := by cases T <;> simp [LevelFit]
  toTy_code T _ hc := by
    cases T with
    | t0 A c => rfl
    | t1 A c =>
      cases c with
      | lift => exact hc.elim
      | _ => rfl
    | t2 A c =>
      cases c with
      | lift => exact hc.elim
      | _ => rfl

end

/-! ## Building the element: `mkTelL` along `telL`, at a good total function -/

section
variable (L : Lvl.{u})

/-- `mkFin` decodes a list meeting `goods`, entry by entry, and hands back the rest. -/
def MkFinOk {Fin : Type u} (mkFin : List Sem → Option (Fin × List Sem)) (goods : List (Sem → Prop)) : Prop :=
  ∀ (fs rest : List Sem), fs.length = goods.length →
    (∀ (j : Nat) (gd : Sem → Prop) (f : Sem), goods[j]? = some gd → fs[j]? = some f → gd f) →
    ∃ fin, mkFin (fs ++ rest) = some (fin, rest)

theorem mkFinOk_start : MkFinOk (fun fs => some (PUnit.unit.{u + 1}, fs)) ([] : List (Sem → Prop)) := by
  intro fs rest hl _
  have : fs = [] := List.eq_nil_of_length_eq_zero hl
  subst this
  exact ⟨_, rfl⟩

/-- A parameter's step keeps it: a borrow parameter's final content is decoded at its code. -/
theorem mkFinOk_ext (b : Bool) (Fin T : Type u) (c : L.Code T) (mkFin : List Sem → Option (Fin × List Sem))
    (goods : List (Sem → Prop)) (h : MkFinOk mkFin goods) :
    MkFinOk (extMkL b Fin T mkFin (L.dec c)) (if b then goods ++ [fun f => ∃ y, L.dec c f = some y] else goods) := by
  cases b with
  | false => exact h
  | true =>
    intro fs rest hl hg
    simp only [if_true, List.length_append, List.length_singleton] at hl hg
    rcases List.eq_nil_or_concat fs with rfl | ⟨fs0, t, rfl⟩
    · simp at hl
    simp only [List.concat_eq_append] at hl hg ⊢
    replace hl : fs0.length = goods.length := by simpa using hl
    have hg0 : ∀ (j : Nat) (gd : Sem → Prop) (f : Sem), goods[j]? = some gd → fs0[j]? = some f → gd f := by
      intro j gd f hj hf
      have hjl : j < fs0.length := (List.getElem?_eq_some_iff.mp hf).1
      exact hg j gd f (by rw [List.getElem?_append_left (by omega)]; exact hj)
        (by rw [List.getElem?_append_left hjl]; exact hf)
    obtain ⟨y, hy⟩ : ∃ y, L.dec c t = some y :=
      hg goods.length (fun f => ∃ y, L.dec c f = some y) t (by simp)
        (by rw [List.getElem?_append_right (by omega)]; simp [hl])
    obtain ⟨fin, hfin⟩ := h fs0 (t :: rest) hl hg0
    refine ⟨(fin, y), ?_⟩
    rw [List.append_assoc, List.singleton_append]
    simp [extMkL, hfin, hy]

/-- The arguments after `acc` are members of their domains, each at the arguments before it. -/
def DomMembersFrom (ds : List PiDom) (acc rest : List Sem) : Prop :=
  rest.length = ds.length ∧
    ∀ (i : Nat) (a : Sem) (d : PiDom), rest[i]? = some a → ds[i]? = some d → a ∈ₛ[L.read] d.dom (acc ++ rest.take i)

/-- The final contents read at the future: as many as the borrow parameters left (after the ones
`goods` already covers), the ones `goods` covers meeting it, the others members of their domains. -/
def FinalsOk (ds : List PiDom) (acc rest : List Sem) (goods : List (Sem → Prop)) (fs : List Sem) : Prop :=
  fs.length = goods.length + (ds.filter (·.isRef)).length ∧
    (∀ (j : Nat) (gd : Sem → Prop) (f : Sem), goods[j]? = some gd → fs[j]? = some f → gd f) ∧
    ∀ (i : Nat) (d : PiDom), ds[i]? = some d → d.isRef = true →
      ∃ f, fs[goods.length + ((ds.take i).filter (·.isRef)).length]? = some f ∧
        f ∈ₛ[L.read] d.dom (acc ++ rest.take i)

end

section
variable (L : Lvl.{u})

/-- **The element is built** along `telL`, at a data codomain, when the function is defined at
every argument tuple extending `acc` whose entries are members of their domains, with a result in
the codomain (whose code fits the level) and final contents of their types. -/
theorem mkTelL_telL_some {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future) (g : List Sem → Option BodyOut)
    (out : PiCod) (hdata : out.isRef = false) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
      (goods : List (Sem → Prop)), MkFinOk mkFin goods →
      (∀ rest, DomMembersFrom L ds acc rest → ∃ o, g (acc ++ rest) = some o ∧ Fit (out.cod (acc ++ rest)) ∧
        o.result ∈ₛ[L.read] out.cod (acc ++ rest) ∧ FinalsOk L ds acc rest goods (o.finals.map (· φ))) →
      (mkTelL L φ (telL L ds acc Fin out).2 acc mkFin g).isSome
  | [], acc, Fin, mkFin, goods, hmk, H => by
    obtain ⟨o, hg, hfit, hres, hfin⟩ := H [] ⟨rfl, fun i a d ha _ => by simp at ha⟩
    simp only [List.append_nil] at hg hfit hres
    obtain ⟨r, hr⟩ := hF.dec_mem _ _ hfit hres
    obtain ⟨fin, hfin'⟩ := hmk (o.finals.map (· φ)) [] (by simpa using hfin.1) hfin.2.1
    simp only [List.append_nil] at hfin'
    rcases out with ⟨isRef, cod⟩
    simp only at hdata
    subst hdata
    show ((g acc).bind (mkLeafDataL L φ Fin mkFin (L.codeOf (cod acc)).2)).isSome
    rw [hg, Option.bind_some]
    unfold mkLeafDataL
    rw [hr, hfin']
    rfl
  | p :: ps, acc, Fin, mkFin, goods, hmk, H => by
    show (mkTelL L φ (.param Fin p.isRef _ (L.codeOf (p.dom acc)).2 _ fun a =>
      (telL L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).2)
      acc mkFin g).isSome
    simp only [mkTelL]
    rw [dif_pos]
    · rfl
    intro x
    refine mkTelL_telL_some hF φ g out hdata ps _ _ _ _ (mkFinOk_ext L p.isRef Fin _ _ mkFin goods hmk) ?_
    intro rest' hrest'
    have hm : DomMembersFrom L (p :: ps) acc (L.enc (L.codeOf (p.dom acc)).2 x :: rest') := by
      refine ⟨by simp [hrest'.1], fun i a d ha hd => ?_⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hd
        subst ha; subst hd
        simpa using hF.enc_mem (p.dom acc) x
      | succ i =>
        simp only [List.getElem?_cons_succ] at ha hd
        have := hrest'.2 i a d ha hd
        simpa [List.take_succ_cons] using this
    obtain ⟨o, hg, hfit, hres, hl, hgd, href⟩ := H _ hm
    have e : acc ++ L.enc (L.codeOf (p.dom acc)).2 x :: rest' = acc ++ [L.enc (L.codeOf (p.dom acc)).2 x] ++ rest' := by simp
    rw [e] at hg hfit hres
    refine ⟨o, hg, hfit, hres, ?_, ?_, ?_⟩
    · cases hp : p.isRef <;> simp [hp] at hl ⊢ <;> omega
    · intro j gd f hj hf
      cases hp : p.isRef
      · simp only [hp, Bool.false_eq_true, if_false] at hj
        exact hgd j gd f hj hf
      · simp only [hp, if_true] at hj
        by_cases hjl : j < goods.length
        · rw [List.getElem?_append_left hjl] at hj
          exact hgd j gd f hj hf
        · have hje : j = goods.length := by
            have := (List.getElem?_eq_some_iff.mp hj).1; simp at this; omega
          subst hje
          rw [List.getElem?_append_right (Nat.le_refl _)] at hj
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          obtain ⟨f', hf', hmem⟩ := href 0 p rfl hp
          simp only [List.take_zero, List.filter_nil, List.length_nil, Nat.add_zero] at hf'
          rw [hf'] at hf
          cases hf
          exact hF.dec_mem _ _ (hF.fit_of _ x) (by simpa using hmem)
    · intro i d hd hdr
      obtain ⟨f, hf, hmem⟩ := href (i + 1) d (by simpa using hd) hdr
      refine ⟨f, ?_, by simpa [List.take_succ_cons] using hmem⟩
      rw [← hf]
      congr 1
      cases hp : p.isRef <;> simp [hp, List.take_succ_cons] <;> omega

end

/-! ## The closure lemma at a level -/

section
variable (L : Lvl.{u})

/-- A good total function is good from the start of the telescope. -/
theorem goodFrom_start {Fit : TyM → Prop} (φ : Future) (g : List Sem → Option BodyOut) (ds : List PiDom) (out : PiCod)
    (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length) :
    ∀ rest, DomMembersFrom L ds [] rest → ∃ o, g ([] ++ rest) = some o ∧ Fit (out.cod ([] ++ rest)) ∧
      o.result ∈ₛ[L.read] out.cod ([] ++ rest) ∧ FinalsOk L ds [] rest [] (o.finals.map (· φ)) := by
  intro rest hrest
  have hm : DomMembers L.read ds rest := ⟨hrest.1, fun i a d ha hd => by simpa using hrest.2 i a d ha hd⟩
  obtain ⟨o, hg, ⟨hres, hfin⟩, hlen⟩ := htot rest hm
  refine ⟨o, by simpa using hg, by simpa using hcod rest hm, by simpa using hres, ?_, ?_, ?_⟩
  · simp [hlen]
  · intro j gd f hj; simp at hj
  · intro i d hd hdr
    obtain ⟨f, hf, hmem⟩ := hfin i d hd hdr
    exact ⟨f φ, by simp [hf], by simpa using hmem φ⟩

/-- **The closure lemma, membership half, at a level**: a closure whose function is defined and
good at every member argument (one final content per borrow parameter) is a member of its code, at
a data codomain whose code fits the level. -/
theorem closureL_mem_of_total (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future)
    (g : List Sem → Option BodyOut) (ds : List PiDom) (out : PiCod) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length) :
    closureL L φ (telL L ds [] PUnit out).2 g ∈ₛ[L.read] piTyL L (telL L ds [] PUnit out).2 := by
  have hs := mkTelL_telL_some L hF φ g out hdata ds [] PUnit _ [] (mkFinOk_start)
    (goodFrom_start L φ g ds out hcod htot)
  obtain ⟨F, hF'⟩ := Option.isSome_iff_exists.mp hs
  unfold closureL
  rw [hF']
  exact (hL.mem_pi _ _ _).2 ⟨F, hL.enc_pi _ _ F⟩

/-- Applying along `telL` at a data codomain gives the codomain's code at the arguments. -/
theorem applyTelL_telL_data (hL : L.Lawful) (out : PiCod) (hdata : out.isRef = false) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (readFin : Fin → List Sem)
      (F : (telL L ds acc Fin out).1) (args : List Sem) (r : AppResultL L),
      applyTelL L (telL L ds acc Fin out).2 readFin F args = some r →
      ∃ res fins, r = .data res (L.toTy (L.codeOf (out.cod (acc ++ args))).2) fins
  | [], acc, Fin, readFin, F, args, r, h => by
    rcases out with ⟨isRef, cod⟩
    simp only at hdata
    subst hdata
    cases args with
    | nil =>
      simp only [telL, applyTelL, Option.some.injEq] at h
      subst h
      exact ⟨_, _, by rw [List.append_nil]⟩
    | cons a as => simp [telL, applyTelL] at h
  | p :: ps, acc, Fin, readFin, F, args, r, h => by
    cases args with
    | nil => simp [telL, applyTelL] at h
    | cons a as =>
      rw [show (telL L (p :: ps) acc Fin out).2 = .param Fin p.isRef _ (L.codeOf (p.dom acc)).2 _ fun a =>
          (telL L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).2
          from rfl] at h
      erw [applyTelL.eq_3] at h
      cases hx : L.dec (L.codeOf (p.dom acc)).2 a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        dsimp only at h
        obtain ⟨res, fins, e⟩ := applyTelL_telL_data hL out hdata ps _ _ _ _ as r h
        refine ⟨res, fins, ?_⟩
        rw [e, hL.enc_of_dec _ hx, List.append_assoc, List.singleton_append]

end

section
variable (L : Lvl.{u})

/-- Member arguments whose domains fit the level fit the code. -/
theorem argsFit_telL (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (out : PiCod) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (args : List Sem), DomMembersFrom L ds acc args →
      (∀ (i : Nat) (d : PiDom), ds[i]? = some d → Fit (d.dom (acc ++ args.take i))) →
      ArgsFitL L (telL L ds acc Fin out).2 args
  | [], acc, Fin, args, hm, _ => by
    have : args = [] := List.eq_nil_of_length_eq_zero (by simpa using hm.1)
    subst this
    rcases out with ⟨isRef, cod⟩
    cases isRef <;> trivial
  | p :: ps, acc, Fin, [], hm, _ => by simp [DomMembersFrom] at hm
  | p :: ps, acc, Fin, a :: as, hm, hfit => by
    have ha : a ∈ₛ[L.read] p.dom acc := by simpa using hm.2 0 a p rfl rfl
    obtain ⟨x, hx⟩ := hF.dec_mem _ _ (by simpa using hfit 0 p rfl) ha
    have hex : L.enc (L.codeOf (p.dom acc)).2 x = a := hL.enc_of_dec _ hx
    refine ⟨x, hx, ?_⟩
    apply argsFit_telL hL hF out ps _ _ as
    · refine ⟨by simpa using hm.1, fun i a' d ha' hd => ?_⟩
      have := hm.2 (i + 1) a' d (by simpa using ha') (by simpa using hd)
      rw [hex]; simpa [List.take_succ_cons] using this
    · intro i d hd
      have := hfit (i + 1) d (by simpa using hd)
      rw [hex]; simpa [List.take_succ_cons] using this

/-- **The closure lemma, application half, at a level**: a closure whose function is defined and
good at every member argument, applied at member arguments whose domains fit the level, is its
function's result there, at the codomain (a canonical code that fits the level), as a call reads
it. -/
theorem closureL_apply (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future)
    (g : List Sem → Option BodyOut) (ds : List PiDom) (out : PiCod) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers L.read ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → Fit (d.dom ((args.map (·.1)).take i)))
    (hcanon : (out.cod (args.map (·.1))).Canon) (hg : g (args.map (·.1)) = some o) :
    ∃ s', callOfL L (telL L ds [] PUnit out).2 (closureL L φ (telL L ds [] PUnit out).2 g) args s =
      some ((o.result, .plain (out.cod (args.map (·.1)))), s') := by
  have hs := mkTelL_telL_some L hF φ g out hdata ds [] PUnit _ [] (mkFinOk_start)
    (goodFrom_start L φ g ds out hcod htot)
  obtain ⟨F, hF'⟩ := Option.isSome_iff_exists.mp hs
  have hfit : ArgsFitL L (telL L ds [] PUnit out).2 (args.map (·.1)) :=
    argsFit_telL L hL hF out ds [] PUnit _ ⟨hmem.1, fun i a d ha hd => by simpa using hmem.2 i a d ha hd⟩
      (fun i d hd => by simpa using hdom i d hd)
  obtain ⟨o', r, hg', hap, hm⟩ := applyTelL_mkTelL L hL φ g (telL L ds [] PUnit out).2 [] _ (fun _ => []) F
    (args.map (·.1)) finInv_start hF' hfit
  simp only [List.nil_append] at hg'
  rw [hg] at hg'
  cases hg'
  obtain ⟨res, fins, rfl⟩ := applyTelL_telL_data L hL out hdata ds [] PUnit _ F _ r hap
  obtain ⟨hres, -⟩ := hm
  subst hres
  have hT : L.toTy (L.codeOf (out.cod ([] ++ args.map (·.1)))).2 = out.cod (args.map (·.1)) := by
    rw [List.nil_append]; exact hF.toTy_code _ (hcod _ hmem) hcanon
  have happ : applyFnL L (telL L ds [] PUnit out).2 (closureL L φ (telL L ds [] PUnit out).2 g) (args.map (·.1)) =
      some (.data o.result (out.cod (args.map (·.1))) fins) := by
    unfold applyFnL closureL
    rw [hF']
    simp only [hL.unpack_pack, Option.bind_some]
    rw [hap, hT]
  unfold callOfL
  simp only [happ]
  exact ⟨_, rfl⟩

end

/-! ## The closure lemma, at the declared sort -/

section
variable (R : DataRead)

/-- **The closure lemma, membership half** (the corrected form of `Steps.closure_mem_of_total`,
`ClosureCE`): at a data sort `1 ≤ l ≤ 3`, a data codomain whose code fits the level, and a function
defined and good at every member argument with one final content per borrow parameter, the closure
is a member of its code. Any closure meaning, captures included: `g` is arbitrary. -/
theorem closure_mem_of_total' (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : 1 ≤ l ∧ l ≤ 3) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers R ds args → LevelFit l (out.cod args))
    (htot : ∀ args, DomMembers R ds args →
      ∃ o, g args = some o ∧ OutGood R ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length) :
    closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out := by
  obtain ⟨h1, h3⟩ := hl
  rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
  · exact closureL_mem_of_total (lvl0 R) (lvl0_lawful R) (lvl0_fits R) φ g ds out hdata hcod htot
  · exact closureL_mem_of_total (lvl1 R) (lvl1_lawful R) (lvl1_fits R) φ g ds out hdata hcod htot
  · exact closureL_mem_of_total (lvl2 R) (lvl2_lawful R) (lvl2_fits R) φ g ds out hdata hcod htot

/-- **The closure lemma, application half** (the corrected form of `Steps.closure_apply`,
`ClosureCE`): such a closure, applied at member arguments whose domains fit the level, is its
function's result there, at the codomain the code reaches (canonical), as a call reads it. -/
theorem closure_apply' (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : 1 ≤ l ∧ l ≤ 3) (hdata : out.isRef = false)
    (hcod : ∀ args, DomMembers R ds args → LevelFit l (out.cod args))
    (htot : ∀ args, DomMembers R ds args →
      ∃ o, g args = some o ∧ OutGood R ds out args o ∧ o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers R ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom ((args.map (·.1)).take i)))
    (hcanon : (out.cod (args.map (·.1))).Canon) (hg : g (args.map (·.1)) = some o) :
    ∃ s', callOf R (closureAt R l φ ds out g, .plain (piTyAt R l ds out)) args s =
      some ((o.result, .plain (out.cod (args.map (·.1)))), s') := by
  obtain ⟨h1, h3⟩ := hl
  rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
  · exact closureL_apply (lvl0 R) (lvl0_lawful R) (lvl0_fits R) φ g ds out hdata hcod htot args s o hmem hdom hcanon hg
  · exact closureL_apply (lvl1 R) (lvl1_lawful R) (lvl1_fits R) φ g ds out hdata hcod htot args s o hmem hdom hcanon hg
  · exact closureL_apply (lvl2 R) (lvl2_lawful R) (lvl2_fits R) φ g ds out hdata hcod htot args s o hmem hdom hcanon hg

/-- A Π into a proposition holds when its body holds at every member argument tuple. -/
theorem piProp_of (Q : List Sem → Prop) :
    ∀ (ds : List PiDom) (acc : List Sem), (∀ rest, DomMembersFrom (lvl1 R) ds acc rest → Q (acc ++ rest)) →
      piProp R ds acc Q
  | [], acc, h => by
    have := h [] ⟨rfl, fun i a d ha _ => by simp at ha⟩
    simp only [List.append_nil] at this
    exact this
  | p :: ps, acc, h => fun a => by
    apply piProp_of Q ps _
    intro rest hr
    have := h ((p.dom acc).code1.2.enc R a :: rest) ⟨by simp [hr.1], fun i a' d ha' hd => by
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha' hd
        subst ha'; subst hd
        simpa using (lvl1_fits R).enc_mem (p.dom acc) a
      | succ i =>
        simp only [List.getElem?_cons_succ] at ha' hd
        simpa [List.take_succ_cons] using hr.2 i a' d ha' hd⟩
    simpa using this

/-- **The closure lemma at sort `0`**: a closure into propositions is `⋆`, a member of its type (the
proposition that its codomain holds everywhere) when its function is defined at every member
argument with a result in the codomain, a proposition. -/
theorem closure_mem_prop' (φ : Future) (ds : List PiDom) (out : PiCod) (g : List Sem → Option BodyOut)
    (hdata : out.isRef = false)
    (hprop : ∀ args, DomMembers R ds args → ∃ P, out.cod args = TyM.prop P)
    (htot : ∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ o.result ∈ₛ[R] out.cod args) :
    closureAt R 0 φ ds out g ∈ₛ[R] piTyAt R 0 ds out := by
  have hQ : piProp R ds [] (fun acc => if out.isRef then False else (out.cod acc).true) := by
    apply piProp_of R _ ds []
    intro rest hr
    have hm : DomMembers R ds rest := ⟨hr.1, fun i a d ha hd => by simpa using hr.2 i a d ha hd⟩
    obtain ⟨P, hP⟩ := hprop rest hm
    obtain ⟨o, -, hres⟩ := htot rest hm
    rw [hP] at hres
    obtain ⟨⟨hp⟩, -⟩ := hres
    simp only [hdata, Bool.false_eq_true, if_false, List.nil_append, hP]
    exact hp
  exact ⟨⟨hQ⟩, rfl⟩

end

end Ochr.Meaning
