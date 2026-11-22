import Ochr.Meaning.DataModel.Exists.Knot.TruthInterp
import Ochr.Meaning.DataModel.Exists.Knot.Agree

/-!
# Truth first, part 3: the field types are monotone in the truth predicate and the parameters (exists7)

`ftyP_le`: at a weaker truth predicate (`T → T'`, `T'` monotone in its arguments) and weaker parameters
(`PropLe d`: a weaker proposition at a nestable parameter), every field's shape is weaker (`ShapeLe`):
the same, a weaker proposition leaf, or a `Prop`-sorted sub-record inhabited when the first is. Along
the spine of a `Prop`-sorted declaration's field type (`PSpine`) a varying argument is a parameter, `d`
itself, or a `Prop`-sorted declaration applied, so its value is a proposition that only weakens
(`semP_le`); `d`'s own occurrence is the leaf `T ā`; an earlier `Prop`-sorted declaration's record weakens
by the earlier records' monotonicity (`hmono`). The steady nodes, and the fields that do not vary, are
unchanged (`semP_quiet`, `ftyP_quiet`), as for the knot.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

/-! ## A quiet term reads neither the truth predicate nor a varying parameter -/

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}

mutual
theorem semP_quiet {T T' : List Sem → Prop} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') :
    ∀ {t : Term}, PSpine K.Γ d c t → Quiet d c t → ∀ h, semP K ρ d T ps s h t = semP K ρ d T' ps' s h t
  | _, .nat, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, hq, h => by
    rw [semP_var K ρ d T ps s h v hv, semP_var K ρ d T' ps' s h v hv]
    have := hq.2 v (FrameLocal.root_mem_place (.var v))
    unfold varVaries at this
    rw [if_pos hv] at this
    exact hps _ this
  | _, .tind n as M hM hargs, hq, h => by
    rw [semP_tind, semP_tind, hM]
    obtain ⟨hn, hqa⟩ := quiet_args hq
    simp only [if_neg (ne_of_find hM hn)]
    rw [itpArgsP_quiet hps hargs hqa []]
  | _, .call _ _ _ _, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ _, _, _ => by
    rw [semP_other K ρ d T ps s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e),
      semP_other K ρ d T' ps' s _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]

theorem itpArgsP_quiet {T T' : List Sem → Prop} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') :
    ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, PSpineArgs K.Γ d c M j pre as → (∀ a ∈ as, Quiet d c a) →
      ∀ vpre, itpArgsP K ρ d T ps s M j vpre as = itpArgsP K ρ d T' ps' s M j vpre as
  | _, _, _, _, .nil _ _ _, _, vpre => by rw [itpArgsP_nil, itpArgsP_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hq, vpre => by
    have e : argSemP K ρ d T ps s M j vpre a = argSemP K ρ d T' ps' s M j vpre a := by
      rw [argSemP_eq, argSemP_eq, if_pos hty, if_pos hty]
      exact semP_quiet hps ha (hq a (List.mem_cons_self ..)) _
    rw [itpArgsP_cons, itpArgsP_cons, e,
      itpArgsP_quiet hps hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
  | _, _, _, _, .value M j pre a as hty _ hrest, hq, vpre => by
    have e : argSemP K ρ d T ps s M j vpre a = argSemP K ρ d T' ps' s M j vpre a := by
      rw [argSemP_eq, argSemP_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    rw [itpArgsP_cons, itpArgsP_cons, e,
      itpArgsP_quiet hps hrest (fun b hb => hq b (List.mem_cons_of_mem _ hb)) _]
end

theorem itpP_quiet {T T' : List Sem → Prop} {ps ps' : List Sem} {s : SState} (hps : PsSteady d ps ps') {t : Term}
    (ht : PSpine K.Γ d c t) (hq : Quiet d c t) (h : TyS) :
    itpP K ρ d T ps s h t = itpP K ρ d T' ps' s h t := by
  cases ht with
  | tind n as M hM hargs =>
    rw [itpP_tind, itpP_tind, hM]
    obtain ⟨hn, hqa⟩ := quiet_args hq
    simp only [if_neg (ne_of_find hM hn)]
    rw [itpArgsP_quiet hps hargs hqa []]
  | _ =>
    rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e),
      semP_quiet hps (by constructor <;> assumption) hq h]

/-- **A field that does not vary has the same field type at every truth predicate**, and at parameters
equal where they do not vary. -/
theorem ftyP_quiet (hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT)
    (hpty : ParamTyLocal K.dm K.Γ) (hdΓ : d ∈ K.Γ) {T T' : List Sem → Prop} {ps ps' : List Sem}
    (hl : ps.length = ps'.length) (hps : PsSteady d ps ps') :
    ∀ (i : Nat) (es : List Small), fieldVaries d c i = false →
      ftyP K ρ d T ps c i es = ftyP K ρ d T' ps' c i es := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro es hv
    rw [ftyP_eq, ftyP_eq]
    cases hFT : fieldTerm d c i with
    | none => rfl
    | some FT =>
      dsimp only
      rw [canFrame_eq hpty hdΓ hl hps (tyOf' := fun j => if _h : j < i then
          shapeTyP (shapeOf (ftyP K ρ d T' ps' c j (es.take j))) else TyM.err)
        (fun j hj hvj _ => by simp only [dif_pos hj]; rw [ih j hj _ hvj])]
      exact itpP_quiet hps (hspine c i FT hFT) (quiet_of_fieldVaries hv hFT) _

end

/-! ## Weaker values, weaker arguments -/

/-- A value weaker than another: equal, or a proposition implied by the first. -/
def SemLe (v v' : Sem) : Prop :=
  v = v' ∨ ∃ P P' : Prop, (P → P') ∧ v = .ty (TyM.prop P) ∧ v' = .ty (TyM.prop P')

/-- The arguments of `M(…)` so far, the second weaker: at `M`'s nestable parameters `SemLe`, elsewhere
equal, equal wherever the argument is steady, and all equal unless `M` is `Prop`-sorted. -/
def ArgLe (d : IndDecl) (c : Nat) (M : IndDecl) (pre : List Term) (vs vs' : List Sem) : Prop :=
  vs.length = vs'.length ∧ vs.length = pre.length ∧ (∀ k v v', vs[k]? = some v → vs'[k]? = some v' →
    (if nestOf M k then SemLe v v' else v = v') ∧ (∀ a, pre[k]? = some a → Steady d c a → v = v')) ∧
  (vs = vs' ∨ M.sort = 0)

theorem ArgLe.nil (d : IndDecl) (c : Nat) (M : IndDecl) : ArgLe d c M [] [] [] :=
  ⟨rfl, rfl, fun k v v' h => by simp at h, .inl rfl⟩

theorem ArgLe.snoc {d : IndDecl} {c : Nat} {M : IndDecl} {pre : List Term} {vs vs' : List Sem}
    (h : ArgLe d c M pre vs vs') (a : Term) (v v' : Sem)
    (h1 : if nestOf M pre.length then SemLe v v' else v = v') (h2 : Steady d c a → v = v')
    (h3 : v = v' ∨ M.sort = 0) :
    ArgLe d c M (pre ++ [a]) (vs ++ [v]) (vs' ++ [v']) := by
  refine ⟨by simp [h.1], by simp [h.2.1], fun k w w' hw hw' => ?_, ?_⟩
  · by_cases hk : k < vs.length
    · rw [List.getElem?_append_left hk] at hw
      rw [List.getElem?_append_left (by rw [← h.1]; exact hk)] at hw'
      obtain ⟨e1, e2⟩ := h.2.2.1 k w w' hw hw'
      exact ⟨e1, fun b hb => e2 b (by rwa [List.getElem?_append_left (by rw [← h.2.1]; exact hk)] at hb)⟩
    · have hk' : k = vs.length := by
        have := (List.getElem?_eq_some_iff.1 hw).1; simp at this; omega
      subst hk'
      rw [List.getElem?_append_right (Nat.le_refl _)] at hw
      rw [h.1, List.getElem?_append_right (Nat.le_refl _)] at hw'
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hw hw'
      subst hw hw'
      refine ⟨by rw [h.2.1]; exact h1, fun b hb hs => ?_⟩
      rw [h.2.1, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at hb
      subst hb; exact h2 hs
  · rcases h.2.2.2 with e | e
    · rcases h3 with e' | e'
      · exact .inl (by rw [e, e'])
      · exact .inr e'
    · exact .inr e

theorem ArgLe.propLe {d : IndDecl} {c : Nat} {M : IndDecl} {pre : List Term} {vs vs' : List Sem}
    (h : ArgLe d c M pre vs vs') : PropLe M vs vs' := by
  refine ⟨h.1.symm, fun j v v' hv hv' => ?_⟩
  have := (h.2.2.1 j v v' hv hv').1
  unfold nestOf at this
  split at this
  · rename_i hn
    rcases this with e | ⟨P, P', hPP, e1, e2⟩
    · exact .inl e.symm
    · exact .inr ⟨hn, P, P', e1, e2, hPP⟩
  · exact .inl this.symm

theorem psSteady_of_propLe {d : IndDecl} {ps ps' : List Sem} (hp : PropLe d ps ps') : PsSteady d ps ps' := by
  intro j hj
  have hN := (paramVaries_false hj).1
  rcases h1 : ps[j]? with _ | v
  · have h2 : ps'[j]? = none := by rw [List.getElem?_eq_none_iff] at h1 ⊢; rw [hp.1]; exact h1
    simp [List.getD_eq_getElem?_getD, h1, h2]
  · rcases h2 : ps'[j]? with _ | v'
    · have : ps[j]? = none := by rw [List.getElem?_eq_none_iff] at h2 ⊢; rw [← hp.1]; exact h2
      rw [this] at h1; cases h1
    · rcases hp.2 j v v' h1 h2 with e | ⟨hn, -⟩
      · simp [List.getD_eq_getElem?_getD, h1, h2, e]
      · rw [hN] at hn; cases hn

/-- **Inhabitation is monotone in weaker shapes** at the genuine keys (`mono_prop` at the universal
signature). -/
theorem inhabited_mono {M : IndDecl} {r r' : Rec}
    (h : ∀ c i es, es.length = i → ShapeLe (uShape M r c i es) (uShape M r' c i es)) :
    Nonempty (ucar M r) → Nonempty (ucar M r') := by
  rw [nonempty_iff_mem, nonempty_iff_mem]
  rintro ⟨v, hv⟩
  obtain ⟨c, fs, rfl, hf⟩ := (DataLib.mem_iff uSig M r v).1 hv
  exact ⟨_, (DataLib.mem_iff uSig M r' _).2 ⟨c, fs, rfl, fitsM_mono' (h c) _ 0 [] fs rfl hf⟩⟩

/-- What the monotonicity of the field types rests on. -/
structure MonoHyp (K : RunCtx) (d : IndDecl) (T T' : List Sem → Prop) (ps ps' : List Sem) : Prop where
  hs : d.sort = 0
  hdΓ : d ∈ K.Γ
  hT : ∀ qs, T qs → T' qs
  hT' : ArgMono (PropLe d) T'
  hp : PropLe d ps ps'
  hmono : ∀ M ∈ K.Γ, M ≠ d → M.sort = 0 → ∀ qs qs', PropLe M qs qs' → ∀ c i es, es.length = i →
    ShapeLe (uShape M (K.dm.recOf M qs) c i es) (uShape M (K.dm.recOf M qs') c i es)
  hpty : ParamTyLocal K.dm K.Γ

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}
variable {T T' : List Sem → Prop} {ps ps' : List Sem} {s : SState}

/-- The hints of the next argument agree when the earlier arguments its parameter type mentions are
steady (and so equal). -/
theorem hint_eqP (hpty : ParamTyLocal K.dm K.Γ) {M : IndDecl} (hM : M ∈ K.Γ) {j : Nat} {pre : List Term}
    {vs vs' : List Sem} (h : ArgLe d c M pre vs vs') (hj : vs.length = j)
    (hh : ∀ u ∈ (paramTerm M j).freeVars, u < j → ∀ a, pre[j - 1 - u]? = some a → Steady d c a) :
    K.dm.paramTy M j vs = K.dm.paramTy M j vs' := by
  apply hpty M hM j vs vs' hj (by rw [← h.1]; exact hj)
  intro u hu hlt
  rcases e1 : vs[j - 1 - u]? with _ | v
  · have : vs'[j - 1 - u]? = none := by
      rw [List.getElem?_eq_none_iff] at e1 ⊢; rw [← h.1]; exact e1
    rw [this]
  · have hk : j - 1 - u < vs'.length := by rw [← h.1, hj]; omega
    obtain ⟨a, ha⟩ : ∃ a, pre[j - 1 - u]? = some a := by
      have : j - 1 - u < pre.length := by rw [← h.2.1, hj]; omega
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have := (h.2.2.1 _ v _ e1 (List.getElem?_eq_getElem hk)).2 a ha (hh u hu hlt a ha)
    rw [List.getElem?_eq_getElem hk, this]

mutual
theorem semP_le (H : MonoHyp K d T T' ps ps') :
    ∀ {t : Term}, PSpine K.Γ d c t → ∀ h,
      SemLe (semP K ρ d T ps s h t) (semP K ρ d T' ps' s h t) ∧
        (Steady d c t → semP K ρ d T ps s h t = semP K ρ d T' ps' s h t)
  | t, ht, h => by
    by_cases hst : Steady d c t
    · have e := semP_quiet (T := T) (T' := T') (ρ := ρ) (s := s) (psSteady_of_propLe H.hp) ht (steady_quiet hst) h
      exact ⟨.inl e, fun _ => e⟩
    · refine ⟨?_, fun h' => absurd h' hst⟩
      cases ht with
      | nat => exact absurd (steady_nat d c) hst
      | unit => exact absurd (steady_unit d c) hst
      | call _ _ _ hs => exact absurd hs hst
      | eq _ _ _ hs => exact absurd hs hst
      | param v hv =>
        rw [semP_var K ρ d T ps s h v hv, semP_var K ρ d T' ps' s h v hv]
        rcases e1 : ps[d.params.length - 1 - v]? with _ | w
        · have e2 : ps'[d.params.length - 1 - v]? = none := by
            rw [List.getElem?_eq_none_iff] at e1 ⊢; rw [H.hp.1]; exact e1
          exact .inl (by simp [List.getD_eq_getElem?_getD, e1, e2])
        · rcases e2 : ps'[d.params.length - 1 - v]? with _ | w'
          · have : ps[d.params.length - 1 - v]? = none := by
              rw [List.getElem?_eq_none_iff] at e2 ⊢; rw [← H.hp.1]; exact e2
            rw [this] at e1; cases e1
          · simp only [List.getD_eq_getElem?_getD, e1, e2, Option.getD_some]
            rcases H.hp.2 _ w w' e1 e2 with e | ⟨-, P, P', h1, h2, hPP⟩
            · exact .inl e.symm
            · exact .inr ⟨P, P', hPP, h1, h2⟩
      | tind n as M hM hargs =>
        have hMΓ := (find_name hM).2
        rw [semP_tind, semP_tind, hM]
        have hA := itpArgsP_le H hMΓ hargs [] [] (ArgLe.nil d c M) rfl
        simp only [List.nil_append] at hA
        by_cases hMd : M = d
        · subst hMd
          simp only []
          refine .inr ⟨_, _, fun hT0 => H.hT' _ _ hA.propLe (H.hT _ hT0), rfl, rfl⟩
        · simp only [if_neg hMd]
          rcases hA.2.2.2 with e | hMs
          · exact .inl (by rw [e])
          · rw [uTyR_prop hMs, uTyR_prop hMs]
            exact .inr ⟨_, _, inhabited_mono (H.hmono M hMΓ hMd hMs _ _ hA.propLe), rfl, rfl⟩

theorem itpArgsP_le (H : MonoHyp K d T T' ps ps') {M : IndDecl} (hMΓ : M ∈ K.Γ) :
    ∀ {j : Nat} {pre as : List Term}, PSpineArgs K.Γ d c M j pre as →
      ∀ (vs vs' : List Sem), ArgLe d c M pre vs vs' → vs.length = j →
      ArgLe d c M (pre ++ as) (vs ++ itpArgsP K ρ d T ps s M j vs as) (vs' ++ itpArgsP K ρ d T' ps' s M j vs' as)
  | _, _, _, .nil _ _ _, vs, vs', h, _ => by simpa [itpArgsP_nil] using h
  | _, _, _, .type _ j pre a as hty ha hn hA hrest, vs, vs', h, hj => by
    -- the argument runs with no hint (docs/31 D172), so the two sides' hints agree outright
    rw [itpArgsP_cons, itpArgsP_cons, argSemP_eq, argSemP_eq, if_pos hty, if_pos hty]
    have hpl : pre.length = j := by rw [← h.2.1, hj]
    have e : SemLe (semP K ρ d T ps s (.plain TyM.err) a) (semP K ρ d T' ps' s (.plain TyM.err) a) ∧
        (Steady d c a → semP K ρ d T ps s (.plain TyM.err) a = semP K ρ d T' ps' s (.plain TyM.err) a) :=
      semP_le H ha _
    have h1 : if nestOf M pre.length then
        SemLe (semP K ρ d T ps s (.plain TyM.err) a) (semP K ρ d T' ps' s (.plain TyM.err) a)
        else semP K ρ d T ps s (.plain TyM.err) a = semP K ρ d T' ps' s (.plain TyM.err) a := by
      by_cases hst : Steady d c a
      · have := e.2 hst; split
        · exact .inl this
        · exact this
      · rw [hpl, if_pos (hn hst)]; exact e.1
    have h3 : semP K ρ d T ps s (.plain TyM.err) a = semP K ρ d T' ps' s (.plain TyM.err) a ∨
        M.sort = 0 := by
      by_cases hst : Steady d c a
      · exact .inl (e.2 hst)
      · exact .inr (hA hst).2
    have h' := h.snoc a _ _ h1 e.2 h3
    have := itpArgsP_le H hMΓ hrest _ _ h' (by simp [hj])
    simpa [List.append_assoc] using this
  | _, _, _, .value _ j pre a as hty ha hrest, vs, vs', h, hj => by
    -- the argument runs with no hint (docs/31 D172), so the two sides' values agree outright
    rw [itpArgsP_cons, itpArgsP_cons, argSemP_eq, argSemP_eq, if_neg (by simp [hty]), if_neg (by simp [hty])]
    have h' := h.snoc a (valOf K ρ s (.plain TyM.err) a) (valOf K ρ s (.plain TyM.err) a)
      (by split <;> first | exact .inl rfl | rfl) (fun _ => rfl) (.inl rfl)
    have := itpArgsP_le H hMΓ hrest _ _ h' (by simp [hj])
    simpa [List.append_assoc] using this
end

end

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat}
variable {T T' : List Sem → Prop} {ps ps' : List Sem} {s : SState}

theorem shapeOf_data_prop {M : IndDecl} (hMs : M.sort = 0) (r : Rec) : shapeOf (.data M r) = .prf M r := by
  simp [shapeOf, FTy.kind, FTy.cont, hMs]

theorem itpP_le (H : MonoHyp K d T T' ps ps') {t : Term} (ht : PSpine K.Γ d c t) (h : TyS) :
    ShapeLe (shapeOf (itpP K ρ d T ps s h t)) (shapeOf (itpP K ρ d T' ps' s h t)) := by
  have ht0 := ht
  cases ht with
  | tind n as M hM hargs =>
    have hMΓ := (find_name hM).2
    rw [itpP_tind, itpP_tind, hM]
    have hA := itpArgsP_le (ρ := ρ) (s := s) H hMΓ hargs [] [] (ArgLe.nil d c M) rfl
    simp only [List.nil_append] at hA
    by_cases hMd : M = d
    · subst hMd
      simp only [if_true, shapeOf_prop]
      exact .inr (.inl ⟨_, _, fun hT0 => H.hT' _ _ hA.propLe (H.hT _ hT0), rfl, rfl⟩)
    · simp only [if_neg hMd]
      rcases hA.2.2.2 with e | hMs
      · rw [e]; exact .inl rfl
      · rw [shapeOf_data_prop hMs, shapeOf_data_prop hMs]
        refine .inr (.inr ⟨M, _, _, fun hv => ?_, rfl, rfl⟩)
        rw [← nonempty_iff_mem] at hv ⊢
        exact inhabited_mono (H.hmono M hMΓ hMd hMs _ _ hA.propLe) hv
  | _ =>
    rw [itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), itpP_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e)]
    rcases (semP_le (ρ := ρ) (s := s) H ht0 h).1 with e | ⟨P, P', hPP, e1, e2⟩
    · rw [e]; exact .inl rfl
    · rw [e1, e2]; simp only [Sem.asTy, shapeOf_prop]; exact .inr (.inl ⟨P, P', hPP, rfl, rfl⟩)

/-- **The field types weaken** with the truth predicate and the parameters. -/
theorem ftyP_le (hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT) (H : MonoHyp K d T T' ps ps')
    (i : Nat) (es : List Small) :
    ShapeLe (shapeOf (ftyP K ρ d T ps c i es)) (shapeOf (ftyP K ρ d T' ps' c i es)) := by
  rw [ftyP_eq, ftyP_eq]
  cases hFT : fieldTerm d c i with
  | none => exact .inl rfl
  | some FT =>
    dsimp only
    rw [canFrame_eq H.hpty H.hdΓ H.hp.1.symm (psSteady_of_propLe H.hp) (tyOf' := fun j => if _h : j < i then
        shapeTyP (shapeOf (ftyP K ρ d T' ps' c j (es.take j))) else TyM.err)
      (fun j hj hvj _ => by
        simp only [dif_pos hj]
        rw [ftyP_quiet hspine H.hpty H.hdΓ H.hp.1.symm (psSteady_of_propLe H.hp) j _ hvj])]
    exact itpP_le H (hspine c i FT hFT) _

end

/-! ## The truth predicate: the least fixed point -/

section
variable (K : RunCtx) (ρ : Assignment) (d : IndDecl)

theorem propLe_refl (M : IndDecl) (ps : List Sem) : PropLe M ps ps :=
  ⟨rfl, fun _ v v' h1 h2 => .inl (by rw [h1] at h2; cases h2; rfl)⟩

theorem uShape_truthRec (T : List Sem → Prop) (ps : List Sem) (c i : Nat) (es : List Small) (hl : es.length = i) :
    uShape d (truthRec K ρ d T ps) c i es = shapeOf (ftyP K ρ d T ps c i (projIdx d c es)) :=
  uShape_recK (truthSpec K ρ d T) d ps c i es hl

/-- What the truth-first construction assumes of the earlier declarations and of `d`. -/
structure TruthHyp (K : RunCtx) (d : IndDecl) : Prop where
  hs : d.sort = 0
  hdΓ : d ∈ K.Γ
  hspine : ∀ c i FT, fieldTerm d c i = some FT → PSpine K.Γ d c FT
  hmono : ∀ M ∈ K.Γ, M ≠ d → M.sort = 0 → ∀ qs qs', PropLe M qs qs' → ∀ c i es, es.length = i →
    ShapeLe (uShape M (K.dm.recOf M qs) c i es) (uShape M (K.dm.recOf M qs') c i es)
  hpty : ParamTyLocal K.dm K.Γ

variable {K ρ d}

theorem truthRec_le (G : TruthHyp K d) {T T' : List Sem → Prop} (hT : ∀ qs, T qs → T' qs)
    (hT' : ArgMono (PropLe d) T') {ps ps' : List Sem} (hp : PropLe d ps ps') :
    ∀ c i es, es.length = i →
      ShapeLe (uShape d (truthRec K ρ d T ps) c i es) (uShape d (truthRec K ρ d T' ps') c i es) := by
  intro c i es hl
  rw [uShape_truthRec K ρ d T ps c i es hl, uShape_truthRec K ρ d T' ps' c i es hl]
  exact ftyP_le G.hspine ⟨G.hs, G.hdΓ, hT, hT', hp, G.hmono, G.hpty⟩ i _

theorem truthOp_mono (G : TruthHyp K d) : ∀ X Y : List Sem → Prop, ArgMono (PropLe d) X → ArgMono (PropLe d) Y →
    (∀ ps, X ps → Y ps) → ∀ ps, truthOp K ρ d X ps → truthOp K ρ d Y ps :=
  fun _ _ _ hY hXY ps => inhabited_mono (truthRec_le G hXY hY (propLe_refl d ps))

theorem truthOp_pres (G : TruthHyp K d) : ∀ X, ArgMono (PropLe d) X → ArgMono (PropLe d) (truthOp K ρ d X) :=
  fun _ hX _ _ hp => inhabited_mono (truthRec_le G (fun _ h => h) hX hp)

/-- **The truth predicate** of `d`: the least fixed point of `truthOp` among argument-monotone
predicates. -/
def truthP (K : RunCtx) (ρ : Assignment) (d : IndDecl) : List Sem → Prop := lfpM (PropLe d) (truthOp K ρ d)

theorem truthP_fixed (G : TruthHyp K d) : truthOp K ρ d (truthP K ρ d) = truthP K ρ d :=
  lfpM_fixed (truthOp_mono G) (truthOp_pres G)

/-- **`d`'s code at the truth record is its truth predicate.** -/
theorem uTyR_truthRec (G : TruthHyp K d) (ps : List Sem) :
    uTyR d (truthRec K ρ d (truthP K ρ d) ps) = TyM.prop (truthP K ρ d ps) := by
  rw [uTyR_prop G.hs]
  show TyM.prop (truthOp K ρ d (truthP K ρ d) ps) = _
  rw [truthP_fixed G]

/-- **The truth record is monotone in the parameters** (for the next declarations' `hmono`). -/
theorem truthRec_mono (G : TruthHyp K d) {ps ps' : List Sem} (hp : PropLe d ps ps') :
    ∀ c i es, es.length = i →
      ShapeLe (uShape d (truthRec K ρ d (truthP K ρ d) ps) c i es) (uShape d (truthRec K ρ d (truthP K ρ d) ps') c i es) :=
  truthRec_le G (fun _ h => h) (lfpM_argMono _) hp

end

end Ochr.Meaning.DataModel.Exists.Knot
