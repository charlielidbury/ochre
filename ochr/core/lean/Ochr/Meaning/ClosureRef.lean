import Ochr.Meaning.Closure

/-!
# The closure lemma at a returned borrow (`Π(x̄ : Ā). &U`)

A function returning a borrow is an element of its code's carrier when, at each argument tuple, it
returns a label `k` and the result decodes, and its backward function (the borrow parameters' final
contents, read at the future that fixes `k` to the value the caller leaves in the returned borrow)
is total and injective (`mkLeafRefL`). `OutGood` asks neither the label nor injectivity
(`ClosureCE.closure_mem_ref_false`); `RetGood` is the extension. Here, the forms that hold:

* `closure_mem_of_total_ref'`: a closure whose function is defined and good (`OutGood`, `RetGood`,
  one final content per borrow parameter) at every member argument is a member of its code, at a
  returned borrow whose content code fits the closure's level.
* `closure_apply_ref'`: such a closure applied at member arguments (domains fitting the level) is
  its function's result, at the codomain the code reaches, with a fresh label, as a call reads it.
-/

namespace Ochr.Meaning

open Ochr Ochr.Meaning.Steps

universe u

section
variable (L : Lvl.{u})

/-- One parameter's step of `FinalsOk` (the parameter step of `mkTelL_telL_some`, factored). -/
theorem finalsOk_step {Fit : TyM → Prop} (hF : L.Fits Fit) (p : PiDom) (ps : List PiDom) (acc : List Sem)
    (x : (L.codeOf (p.dom acc)).1) (rest' : List Sem) (goods : List (Sem → Prop)) (fs : List Sem)
    (h : FinalsOk L (p :: ps) acc (L.enc (L.codeOf (p.dom acc)).2 x :: rest') goods fs) :
    FinalsOk L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 x]) rest'
      (if p.isRef then goods ++ [fun f => ∃ y, L.dec (L.codeOf (p.dom acc)).2 f = some y] else goods) fs := by
  obtain ⟨hl, hgd, href⟩ := h
  refine ⟨?_, ?_, ?_⟩
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

/-- One parameter's step of `DomMembersFrom`: an encoded element of the first domain and members
after it. -/
theorem domMembersFrom_cons {Fit : TyM → Prop} (hF : L.Fits Fit) (p : PiDom) (ps : List PiDom) (acc : List Sem)
    (x : (L.codeOf (p.dom acc)).1) (rest' : List Sem)
    (h : DomMembersFrom L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 x]) rest') :
    DomMembersFrom L (p :: ps) acc (L.enc (L.codeOf (p.dom acc)).2 x :: rest') := by
  refine ⟨by simp [h.1], fun i a d ha hd => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hd
    subst ha; subst hd
    simpa using hF.enc_mem (p.dom acc) x
  | succ i =>
    simp only [List.getElem?_cons_succ] at ha hd
    have := h.2 i a d ha hd
    simpa [List.take_succ_cons] using this

/-- What the returned-borrow leaf asks at an argument tuple extending `acc`: the function is
defined, its result in the (fitting) codomain, a returned label `k`, the final contents good at
every member value left in the borrow, and the backward function injective. -/
def RefLeafOk {Fit : TyM → Prop} (φ : Future) (g : List Sem → Option BodyOut) (out : PiCod) (ds : List PiDom)
    (acc rest : List Sem) (goods : List (Sem → Prop)) : Prop :=
  ∃ o, g (acc ++ rest) = some o ∧ Fit (out.cod (acc ++ rest)) ∧ o.result ∈ₛ[L.read] out.cod (acc ++ rest) ∧
    ∃ k, o.retLabel = some k ∧
      (∀ v, v ∈ₛ[L.read] out.cod (acc ++ rest) → FinalsOk L ds acc rest goods (o.finals.map (· (φ.upd k v)))) ∧
      ∀ v w, v ∈ₛ[L.read] out.cod (acc ++ rest) → w ∈ₛ[L.read] out.cod (acc ++ rest) →
        o.finals.map (· (φ.upd k v)) = o.finals.map (· (φ.upd k w)) → v = w

/-- **The element is built** along `telL` at a returned borrow, when the function meets the
returned-borrow leaf at every member argument tuple extending `acc`. -/
theorem mkTelL_telL_some_ref (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future)
    (g : List Sem → Option BodyOut) (out : PiCod) (href : out.isRef = true) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (mkFin : List Sem → Option (Fin × List Sem))
      (readFin : Fin → List Sem) (goods : List (Sem → Prop)), MkFinOk mkFin goods → FinInv mkFin readFin →
      (∀ rest, DomMembersFrom L ds acc rest → RefLeafOk L (Fit := Fit) φ g out ds acc rest goods) →
      (mkTelL L φ (telL L ds acc Fin out).2 acc mkFin g).isSome
  | [], acc, Fin, mkFin, readFin, goods, hmk, hinv, H => by
    obtain ⟨o, hg, hfit, hres, k, hk, hfin, hinj⟩ := H [] ⟨rfl, fun i a d ha _ => by simp at ha⟩
    simp only [List.append_nil] at hg hfit hres hfin hinj
    obtain ⟨r, hr⟩ := hF.dec_mem _ _ hfit hres
    rcases out with ⟨isRef, cod⟩
    simp only at href
    subst href
    simp only at hfit hres hfin hinj hr
    have hback : ∀ v : (L.codeOf (cod acc)).1,
        ∃ fin, mkFin (o.finals.map (· (φ.upd k (L.enc (L.codeOf (cod acc)).2 v)))) = some (fin, []) := by
      intro v
      have hv := hfin _ (hF.enc_mem _ v)
      obtain ⟨fin, hfin'⟩ := hmk _ [] (by simpa using hv.1) hv.2.1
      exact ⟨fin, by simpa using hfin'⟩
    have hall : ∀ v, (mkBackAtL L φ Fin mkFin (L.codeOf (cod acc)).2 o k v).isSome := by
      intro v; obtain ⟨fin, h⟩ := hback v; simp [mkBackAtL, h]
    have hget : ∀ v fin, mkFin (o.finals.map (· (φ.upd k (L.enc (L.codeOf (cod acc)).2 v)))) = some (fin, []) →
        (mkBackAtL L φ Fin mkFin (L.codeOf (cod acc)).2 o k v).get (hall v) = fin := by
      intro v fin h; simp [mkBackAtL, h]
    have hinj' : ∀ v w, (mkBackAtL L φ Fin mkFin (L.codeOf (cod acc)).2 o k v).get (hall v) =
        (mkBackAtL L φ Fin mkFin (L.codeOf (cod acc)).2 o k w).get (hall w) → v = w := by
      intro v w hvw
      obtain ⟨fv, hfv⟩ := hback v
      obtain ⟨fw, hfw⟩ := hback w
      rw [hget v fv hfv, hget w fw hfw] at hvw
      subst hvw
      have h1 := hinv _ _ _ hfv
      have h2 := hinv _ _ _ hfw
      simp only [List.append_nil] at h1 h2
      have he := hinj _ _ (hF.enc_mem _ v) (hF.enc_mem _ w) (h1.symm.trans h2)
      have := congrArg (L.dec (L.codeOf (cod acc)).2) he
      rw [hL.dec_enc, hL.dec_enc] at this
      exact Option.some.inj this
    show ((g acc).bind (mkLeafRefL L φ Fin mkFin (L.codeOf (cod acc)).2)).isSome
    rw [hg, Option.bind_some]
    unfold mkLeafRefL
    simp only [hk, hr]
    rw [dif_pos hall, dif_pos hinj']
    rfl
  | p :: ps, acc, Fin, mkFin, readFin, goods, hmk, hinv, H => by
    show (mkTelL L φ (.param Fin p.isRef _ (L.codeOf (p.dom acc)).2 _ fun a =>
      (telL L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).2)
      acc mkFin g).isSome
    simp only [mkTelL]
    rw [dif_pos]
    · rfl
    intro x
    refine mkTelL_telL_some_ref hL hF φ g out href ps _ _ _ _ _ (mkFinOk_ext L p.isRef Fin _ _ mkFin goods hmk)
      (finInv_ext L hL p.isRef Fin _ _ mkFin readFin hinv) ?_
    intro rest' hrest'
    obtain ⟨o, hg, hfit, hres, k, hk, hfin, hinj⟩ := H _ (domMembersFrom_cons L hF p ps acc x rest' hrest')
    have e : acc ++ L.enc (L.codeOf (p.dom acc)).2 x :: rest' = acc ++ [L.enc (L.codeOf (p.dom acc)).2 x] ++ rest' := by simp
    rw [e] at hg hfit hres hinj
    refine ⟨o, hg, hfit, hres, k, hk, fun v hv => ?_, hinj⟩
    exact finalsOk_step L hF p ps acc x rest' goods _ (hfin v (by rw [e]; exact hv))

/-- A good total function meets the returned-borrow leaf from the start of the telescope. -/
theorem refLeafFrom_start {Fit : TyM → Prop} (φ : Future) (g : List Sem → Option BodyOut) (ds : List PiDom)
    (out : PiCod) (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ RetGood L.read out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length) :
    ∀ rest, DomMembersFrom L ds [] rest → RefLeafOk L (Fit := Fit) φ g out ds [] rest [] := by
  intro rest hrest
  have hm : DomMembers L.read ds rest := ⟨hrest.1, fun i a d ha hd => by simpa using hrest.2 i a d ha hd⟩
  obtain ⟨o, hg, ⟨hres, hfin⟩, ⟨k, hk, hinj⟩, hlen⟩ := htot rest hm
  refine ⟨o, by simpa using hg, by simpa using hcod rest hm, by simpa using hres, k, hk, fun v _ => ⟨?_, ?_, ?_⟩,
    fun v w hv hw h => hinj φ v w (by simpa using hv) (by simpa using hw) h⟩
  · simp [hlen]
  · intro j gd f hj; simp at hj
  · intro i d hd hdr
    obtain ⟨f, hf, hmem⟩ := hfin i d hd hdr
    exact ⟨f (φ.upd k v), by simp [hf], by simpa using hmem (φ.upd k v)⟩

/-- **The closure lemma, membership half, at a returned borrow, at a level.** -/
theorem closureL_mem_of_total_ref (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future)
    (g : List Sem → Option BodyOut) (ds : List PiDom) (out : PiCod) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ RetGood L.read out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length) :
    closureL L φ (telL L ds [] PUnit out).2 g ∈ₛ[L.read] piTyL L (telL L ds [] PUnit out).2 := by
  have hs := mkTelL_telL_some_ref L hL hF φ g out href ds [] PUnit _ (fun _ => []) [] mkFinOk_start finInv_start
    (refLeafFrom_start L φ g ds out hcod htot)
  obtain ⟨F, hF'⟩ := Option.isSome_iff_exists.mp hs
  unfold closureL
  rw [hF']
  exact (hL.mem_pi _ _ _).2 ⟨F, hL.enc_pi _ _ F⟩

end

section
variable (L : Lvl.{u})

/-- Applying along `telL` at a returned borrow gives the codomain's code at the arguments. -/
theorem applyTelL_telL_ref (hL : L.Lawful) (out : PiCod) (href : out.isRef = true) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (readFin : Fin → List Sem)
      (F : (telL L ds acc Fin out).1) (args : List Sem) (r : AppResultL L),
      applyTelL L (telL L ds acc Fin out).2 readFin F args = some r →
      ∃ (U : Type u) (c : L.Code U) (fwd : U) (back : U → List Sem), r = .ref U c fwd back ∧
        (⟨U, c⟩ : (A : Type u) × L.Code A) = L.codeOf (out.cod (acc ++ args))
  | [], acc, Fin, readFin, F, args, r, h => by
    rcases out with ⟨isRef, cod⟩
    simp only at href
    subst href
    cases args with
    | nil =>
      simp only [telL, applyTelL, Option.some.injEq] at h
      subst h
      exact ⟨_, _, _, _, rfl, by rw [List.append_nil]⟩
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
        obtain ⟨U, c, fwd, back, e, ec⟩ := applyTelL_telL_ref hL out href ps _ _ _ _ as r h
        refine ⟨U, c, fwd, back, e, ?_⟩
        rw [ec, hL.enc_of_dec _ hx, List.append_assoc, List.singleton_append]

/-- **The closure lemma, application half, at a returned borrow, at a level**: the call gives the
function's result, at the codomain, under a fresh label. -/
theorem closureL_apply_ref (hL : L.Lawful) {Fit : TyM → Prop} (hF : L.Fits Fit) (φ : Future)
    (g : List Sem → Option BodyOut) (ds : List PiDom) (out : PiCod) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers L.read ds args → Fit (out.cod args))
    (htot : ∀ args, DomMembers L.read ds args →
      ∃ o, g args = some o ∧ OutGood L.read ds out args o ∧ RetGood L.read out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers L.read ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → Fit (d.dom ((args.map (·.1)).take i)))
    (hcanon : (out.cod (args.map (·.1))).Canon) (hg : g (args.map (·.1)) = some o) :
    ∃ k s', callOfL L (telL L ds [] PUnit out).2 (closureL L φ (telL L ds [] PUnit out).2 g) args s =
      some ((o.result, ⟨out.cod (args.map (·.1)), some k⟩), s') := by
  have hs := mkTelL_telL_some_ref L hL hF φ g out href ds [] PUnit _ (fun _ => []) [] mkFinOk_start finInv_start
    (refLeafFrom_start L φ g ds out hcod htot)
  obtain ⟨F, hF'⟩ := Option.isSome_iff_exists.mp hs
  have hfit : ArgsFitL L (telL L ds [] PUnit out).2 (args.map (·.1)) :=
    argsFit_telL L hL hF out ds [] PUnit _ ⟨hmem.1, fun i a d ha hd => by simpa using hmem.2 i a d ha hd⟩
      (fun i d hd => by simpa using hdom i d hd)
  obtain ⟨o', r, hg', hap, hm⟩ := applyTelL_mkTelL L hL φ g (telL L ds [] PUnit out).2 [] _ (fun _ => []) F
    (args.map (·.1)) finInv_start hF' hfit
  simp only [List.nil_append] at hg'
  rw [hg] at hg'
  cases hg'
  obtain ⟨U, c, fwd, back, rfl, ec⟩ := applyTelL_telL_ref L hL out href ds [] PUnit _ F _ r hap
  obtain ⟨k, -, hfwd, -⟩ := hm
  have hT : L.toTy c = out.cod (args.map (·.1)) := by
    have := congrArg (fun q : (A : Type u) × L.Code A => L.toTy q.2) ec
    simp only at this
    rw [this, List.nil_append]; exact hF.toTy_code _ (hcod _ hmem) hcanon
  have happ : applyFnL L (telL L ds [] PUnit out).2 (closureL L φ (telL L ds [] PUnit out).2 g) (args.map (·.1)) =
      some (.ref U c fwd back) := by
    unfold applyFnL closureL
    rw [hF']
    simp only [hL.unpack_pack, Option.bind_some]
    exact hap
  unfold callOfL
  simp only [happ, hfwd, hT]
  exact ⟨_, _, rfl⟩

end

/-- **The closure lemma, membership half, at a returned borrow** (`ClosureCE.closure_mem_ref_false`
corrected): at a data sort `1 ≤ l ≤ 3`, a codomain whose content code fits the level, and a function
defined and good at every member argument (`OutGood`, a returned label with an injective backward
function, `RetGood`, and one final content per borrow parameter), the closure is a member of its code. -/
theorem closure_mem_of_total_ref' (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : 1 ≤ l ∧ l ≤ 3) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers R ds args → LevelFit l (out.cod args))
    (htot : ∀ args, DomMembers R ds args →
      ∃ o, g args = some o ∧ OutGood R ds out args o ∧ RetGood R out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length) :
    closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out := by
  obtain ⟨h1, h3⟩ := hl
  rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
  · exact closureL_mem_of_total_ref (lvl0 R) (lvl0_lawful R) (lvl0_fits R) φ g ds out href hcod htot
  · exact closureL_mem_of_total_ref (lvl1 R) (lvl1_lawful R) (lvl1_fits R) φ g ds out href hcod htot
  · exact closureL_mem_of_total_ref (lvl2 R) (lvl2_lawful R) (lvl2_fits R) φ g ds out href hcod htot

/-- **The closure lemma, application half, at a returned borrow**: such a closure, applied at
member arguments whose domains fit the level, is its function's result there, at the codomain the
code reaches (canonical), under a fresh label, as a call reads it. -/
theorem closure_apply_ref' (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hl : 1 ≤ l ∧ l ≤ 3) (href : out.isRef = true)
    (hcod : ∀ args, DomMembers R ds args → LevelFit l (out.cod args))
    (htot : ∀ args, DomMembers R ds args →
      ∃ o, g args = some o ∧ OutGood R ds out args o ∧ RetGood R out args o ∧
        o.finals.length = (ds.filter (·.isRef)).length)
    (args : List Res) (s : SState) (o : BodyOut) (hmem : DomMembers R ds (args.map (·.1)))
    (hdom : ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom ((args.map (·.1)).take i)))
    (hcanon : (out.cod (args.map (·.1))).Canon) (hg : g (args.map (·.1)) = some o) :
    ∃ k s', callOf R (closureAt R l φ ds out g, .plain (piTyAt R l ds out)) args s =
      some ((o.result, ⟨out.cod (args.map (·.1)), some k⟩), s') := by
  obtain ⟨h1, h3⟩ := hl
  rcases (show l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl
  · exact closureL_apply_ref (lvl0 R) (lvl0_lawful R) (lvl0_fits R) φ g ds out href hcod htot args s o hmem hdom hcanon hg
  · exact closureL_apply_ref (lvl1 R) (lvl1_lawful R) (lvl1_fits R) φ g ds out href hcod htot args s o hmem hdom hcanon hg
  · exact closureL_apply_ref (lvl2 R) (lvl2_lawful R) (lvl2_fits R) φ g ds out href hcod htot args s o hmem hdom hcanon hg

end Ochr.Meaning
