import Ochr.Meaning.DataModel.Exists.Knot.Guard
import Ochr.Meaning.DataModel.Exists.Piece3

/-!
# The knot, part 5: the actual frame against the canonical one (exists5; the first lemmas)

At the knot's own records, the actual frame a field type runs in (`teleFrame`, at fields `e` fitting
the knot's shapes) and the canonical frame (`canFrame`, rebuilt from the key) hold the same binding at
every earlier field that is an index and does not vary: the same type (`fieldTy_knot_shape`: the knot's
record holds, at the field's key, the field type its own `fty` gives, so `uShape` there is `shapeOf`
of it) and the same value (`rebuild_eq`: one member of a level-0 type per small reading).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical
open Classical

/-- **At a knot's record, the universal shape is the shape of the knot's own field type.** -/
theorem uShape_recK (S : KnotSpec) (d : IndDecl) (ps : List Sem) (c j : Nat) (x : List Small) (hx : x.length = j) :
    uShape d (recK S ps) c j x = shapeOf (S.fty (recK S) ps c j (projIdx d c x)) := by
  have hl : (projIdx d c x).length = j := by rw [projIdx_len, hx]
  unfold uShape shapeOf
  rw [recK_kind S ps c j _ hl, recK_contRec S ps c j _ hl]
  cases (S.fty (recK S) ps c j (projIdx d c x)).kind <;> rfl

/-- The type an earlier field is bound at in the actual frame, at a knot's record: the shape type of
the knot's field type at the projected readings of the fields before it. -/
theorem fieldTy_knot (S : KnotSpec) (dm : DataModel) (d : IndDecl) (hR : dm.recOf d = recK S)
    (ps : List Sem) (c j : Nat) (e : List Sem) (hj : j ≤ e.length) :
    dm.fieldTy d ps c j (e.take j) =
      shapeTyP (shapeOf (S.fty (recK S) ps c j ((projIdx d c (e.map Sem.small)).take j))) := by
  unfold DataModel.fieldTy DataModel.fieldTyR
  rw [hR, shapeTy_eq_shapeTyP]
  show shapeTyP (uShape d (recK S ps) c j ((e.take j).map Sem.small)) = _
  rw [uShape_recK S d ps c j _ (by simp; omega), List.map_take, Piece3.projIdx_take]

/-- Every shape's type is a level-0 code. -/
theorem uTyR_t0 (d : IndDecl) (r : Rec) : ∃ (A : Type) (cd : Code0 A), uTyR d r = .t0 A cd := by
  unfold uTyR; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem shapeTyP_t0 (sh : Shape) : ∃ (A : Type) (cd : Code0 A), shapeTyP sh = .t0 A cd := by
  cases sh with
  | leaf B c => exact ⟨_, _, rfl⟩
  | sub d r =>
    simp only [shapeTyP]
    by_cases h : (d.sort == 0) = true
    · rw [if_pos h]; exact ⟨_, _, rfl⟩
    · rw [if_neg h]; exact uTyR_t0 d r
  | prf d r =>
    simp only [shapeTyP]
    by_cases h : (d.sort == 0) = true
    · rw [if_pos h]; exact uTyR_t0 d r
    · rw [if_neg h]; exact ⟨_, _, rfl⟩

/-- **The rebuilt member is the member**: a member of a shape's type with the given small reading. -/
theorem rebuild_eq (K : RunCtx) (sh : Shape) {v : Sem} (hv : v ∈ₛ[K.dm.read] shapeTyP sh) :
    rebuild K (shapeTyP sh) v.small = v := by
  have hex : ∃ w, w ∈ₛ[K.dm.read] shapeTyP sh ∧ w.small = v.small := ⟨v, hv, rfl⟩
  unfold rebuild
  rw [dif_pos hex]
  obtain ⟨A, cd, hA⟩ := shapeTyP_t0 sh
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = w at h1 h2 ⊢
  rw [hA] at h1 hv
  exact Piece3.memTy_small_inj K.dm cd h1 hv h2

/-! ## Along the spine, the run is the interpreter (given the steady nodes) -/

theorem steady_nat (d : IndDecl) (c : Nat) : Steady d c .nat :=
  ⟨⟨rfl, rfl⟩, fun v hv => by simp [Term.freeVars, Term.freeOccs, Term.placeOccs] at hv⟩

theorem steady_unit (d : IndDecl) (c : Nat) : Steady d c .unit :=
  ⟨⟨rfl, rfl⟩, fun v hv => by simp [Term.freeVars, Term.freeOccs, Term.placeOccs] at hv⟩

theorem runParams_cons (K : RunCtx) (ρ : Assignment) (φ : Future) (M : IndDecl) (j : Nat) (vs : List Sem)
    (a : Term) (as : List Term) (s : SState) {psM : List Sem} {s' : SState}
    (h : runParams K ρ φ M j vs (a :: as) s = some (psM, s')) :
    ∃ v T s₁ rest, runT K ρ φ false (.plain TyM.err) a s = some ((v, T), s₁) ∧
      runParams K ρ φ M (j + 1) (vs ++ [v]) as s = some (rest, s') ∧ psM = v :: rest := by
  simp only [runParams, bind, SM.onCopy] at h
  revert h
  cases ha : runT K ρ φ false (.plain TyM.err) a s with
  | none => intro h; simp at h
  | some p =>
    obtain ⟨⟨v, T⟩, s₁⟩ := p
    simp only [Option.map_some]
    cases hr : runParams K ρ φ M (j + 1) (vs ++ [v]) as s with
    | none => intro h; simp [hr] at h
    | some q =>
      obtain ⟨rest, s₂⟩ := q
      intro h
      simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, T, s₁, rest, rfl, hr, rfl⟩

section
variable {K : RunCtx} {ρ : Assignment} {d : IndDecl} {c : Nat} {R : List Sem → Rec} {ps : List Sem}
variable {A F : SState} {P : Nat → Prop}

mutual
/-- **Along the spine the run's value is the interpreter's**, at a frame `A` whose parameter bindings
hold the parameters, given that every steady node's run there is its canonical value at `F`. -/
theorem semT_run (hR : (setRec K.dm d R).recOf = fun M => recFor K d R M)
    (hAs : A.shape = fun _ => none)
    (hpar : ∀ v, v < d.params.length → ∃ pos, A.varPos v = some pos ∧ A.valAt pos noFuture = ps.getD (d.params.length - 1 - v) .err)
    (hst : ∀ t h r s', Steady d c t → (∀ v ∈ t.freeVars, P v) →
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = valOf K ρ F h t) :
    ∀ {t : Term}, Spine K.Γ d c t → (∀ v ∈ t.freeVars, P v) → ∀ h r s',
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = semT K ρ d R ps F h t
  | _, .nat, hP, h, r, s', hr => by
    rw [hst _ h r s' (steady_nat d c) hP hr, semT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .unit, hP, h, r, s', hr => by
    rw [hst _ h r s' (steady_unit d c) hP hr, semT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .call _ _ _ hs, hP, h, r, s', hr => by
    rw [hst _ h r s' hs hP hr, semT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .eq _ _ _ hs, hP, h, r, s', hr => by
    rw [hst _ h r s' hs hP hr, semT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e) (fun _ e => by cases e)]
  | _, .param v hv, _, h, r, s', hr => by
    obtain ⟨pos, hpos, hval⟩ := hpar v hv
    rw [RunLemmas.runT_var _ _ _ _ _ _ _ hAs pos hpos hr, hval, semT_var K ρ d R ps F h v hv]
  | _, .tind n as M hM hargs, hP, h, r, s', hr => by
    obtain ⟨M', psM, hM', hps, -, hr1, -⟩ := RunLemmas.runT_tind _ _ _ _ _ _ _ _ hr
    have hMM : M' = M := by rw [show K.Γ = ({ K with dm := setRec K.dm d R } : RunCtx).Γ from rfl, hM'] at hM; cases hM; rfl
    subst hMM
    rw [hr1, semT_tind, hM]
    have := itpArgs_run hR hAs hpar hst hargs (fun a ha v hv => hP v (mem_freeVars_tind ha hv)) [] psM A hps
    simp only [DataModel.tyM, hR, tyR_eq_uTyR, this]

theorem itpArgs_run (hR : (setRec K.dm d R).recOf = fun M => recFor K d R M)
    (hAs : A.shape = fun _ => none)
    (hpar : ∀ v, v < d.params.length → ∃ pos, A.varPos v = some pos ∧ A.valAt pos noFuture = ps.getD (d.params.length - 1 - v) .err)
    (hst : ∀ t h r s', Steady d c t → (∀ v ∈ t.freeVars, P v) →
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t A = some (r, s') → r.1 = valOf K ρ F h t) :
    ∀ {M : IndDecl} {j : Nat} {pre as : List Term}, SpineArgs K.Γ d c M j pre as → (∀ a ∈ as, ∀ v ∈ a.freeVars, P v) →
      ∀ (vs psM : List Sem) (s' : SState), runParams { K with dm := setRec K.dm d R } ρ noFuture M j vs as A = some (psM, s') →
        psM = itpArgs K ρ d R ps F M j vs as
  | _, _, _, _, .nil _ _ _, _, vs, psM, s', h => by
    simp only [runParams, pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, itpArgs_nil]
  | _, _, _, _, .type M j pre a as hty ha _ _ hrest, hP, vs, psM, s', h => by
    obtain ⟨v, T, s₁, rest, hv, hrest', rfl⟩ := runParams_cons _ _ _ _ _ _ _ _ _ h
    have e1 : v = argSem K ρ d R ps F M j vs a := by
      rw [argSem_eq, if_pos hty]
      exact semT_run hR hAs hpar hst ha (hP a (List.mem_cons_self ..)) _ _ _ hv
    rw [itpArgs_cons, ← e1, itpArgs_run hR hAs hpar hst hrest (fun b hb => hP b (List.mem_cons_of_mem _ hb)) _ _ _ hrest']
  | _, _, _, _, .value M j pre a as hty ha _ hrest, hP, vs, psM, s', h => by
    obtain ⟨v, T, s₁, rest, hv, hrest', rfl⟩ := runParams_cons _ _ _ _ _ _ _ _ _ h
    have e1 : v = argSem K ρ d R ps F M j vs a := by
      rw [argSem_eq, if_neg (by simp [hty])]
      exact hst _ _ _ _ ha (hP a (List.mem_cons_self ..)) hv
    rw [itpArgs_cons, ← e1, itpArgs_run hR hAs hpar hst hrest (fun b hb => hP b (List.mem_cons_of_mem _ hb)) _ _ _ hrest']
end

end

/-! ## The knot's agreement with the run, given the steady nodes -/

theorem setRec_recFor (K : RunCtx) (d : IndDecl) (R : List Sem → Rec) :
    (setRec K.dm d R).recOf = fun M => recFor K d R M := by
  funext M; simp only [setRec, recFor]

/-- A parameter read in the actual frame is the parameter. -/
theorem teleFrame_param (dm : DataModel) (D : Decisions) (d : IndDecl) (ps : List Sem) (c : Nat) (e : List Sem)
    (hl : ps.length = d.params.length) (v : Nat) (hv : v < d.params.length) :
    ∃ pos, (teleFrame dm D d ps c e).varPos v = some pos ∧
      (teleFrame dm D d ps c e).valAt pos noFuture = ps.getD (d.params.length - 1 - v) .err := by
  obtain ⟨fbs, -, heq⟩ := RunLemmas.teleFrame_eq dm D d ps c e
  rw [heq]
  generalize hL : ps.zipIdx.map (fun vj => faithBind (dm.paramTy d vj.2 (ps.take vj.2)) vj.1
        ((paramDecls D d (DataLib.arity d c)).getD vj.2 .other)) = L
  have hLl : L.length = ps.length := by rw [← hL]; simp
  have hvl : v < (fbs ++ L).length := by simp [hLl]; omega
  refine ⟨_, RunLemmas.varPos_stateOf 0 _ v hvl, ?_⟩
  rw [RunLemmas.valAt_stateOf 0 _ _ (by omega)]
  have hk : (fbs ++ L).length - 1 - v = fbs.length + (d.params.length - 1 - v) := by simp [hLl]; omega
  have hj : d.params.length - 1 - v < ps.length := by omega
  rw [List.getElem_append_right (by rw [hk]; omega)]
  have : (fbs ++ L).length - 1 - v - fbs.length = d.params.length - 1 - v := by rw [hk]; omega
  simp only [this]
  subst hL
  simp only [List.getElem_map, List.getElem_zipIdx, faithBind, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]

/-- The steady nodes' agreement, the part of `knot_exists` that rests on frame locality and the model
congruence: the run of a steady node of a field type in the actual frame gives its value at the
canonical frame. Proved for the knot's own records: `Steady.steadyAt_knotK`.

The earlier fields are asked to be MEMBERS of their field types at the knot's model (what
`FieldsFaithful`'s consumer has, `FieldsTyped`), not to fit the knot's shapes (exists6: fitting gives
membership only away from junk leaves, which needed `GlobalsTyped`; membership is what frame
locality's `Good` and the rebuilt members read). -/
def SteadyAt (K : RunCtx) (ρ : Assignment) (d : IndDecl) (R : List Sem → Rec) : Prop :=
  ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term), ps.length = d.params.length →
    (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
    (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read] (setRec K.dm d R).fieldTy d ps c j (e.take j)) →
    e.length = i → fieldTerm d c i = some FT →
    ∀ (t : Term) (h : TyS) (r : Res) (s' : SState), Steady d c t → (∀ v ∈ t.freeVars, v ∈ FT.freeVars) →
      runT { K with dm := setRec K.dm d R } ρ noFuture false h t (teleFrame (setRec K.dm d R) K.D d ps c e) = some (r, s') →
      r.1 = valOf K ρ (canFrame K d ps c i (projIdx d c (e.map Sem.small)) fun j => if _h : j < i then
        shapeTyP (shapeOf (ftyK K ρ d R ps c j ((projIdx d c (e.map Sem.small)).take j))) else TyM.err) h t

/-- **The knot agrees with the run, given the steady nodes** (`SteadyAt`, the one fact left). -/
theorem knotK_agree (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hs : d.sort ≠ 0) (hdΓ : d ∈ K.Γ)
    (hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT)
    (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
    (hpty : ParamTyLocal K.dm K.Γ)
    (hst : SteadyAt K ρ d (recK (knotK K ρ d hs hdΓ hspine hpar hpty))) :
    ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
      ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
      (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read]
        (setRec K.dm d (recK (knotK K ρ d hs hdΓ hspine hpar hpty))).fieldTy d ps c j (e.take j)) →
      e.length = i → fieldTerm d c i = some FT →
      run { K with dm := setRec K.dm d (recK (knotK K ρ d hs hdΓ hspine hpar hpty)) } ρ noFuture (.plain (TyM.univ 1)) FT
        (teleFrame (setRec K.dm d (recK (knotK K ρ d hs hdΓ hspine hpar hpty))) K.D d ps c e) = some (r, s') →
        r.1.asTy = ((knotK K ρ d hs hdΓ hspine hpar hpty).fty (recK (knotK K ρ d hs hdΓ hspine hpar hpty)) ps c i
          (projIdx d c (e.map Sem.small))).mean := by
  intro ps c i e FT r s' hl hty hfit hei hFT hrun
  unfold run at hrun
  generalize recK (knotK K ρ d hs hdΓ hspine hpar hpty) = R at hst hfit hrun ⊢
  show r.1.asTy = (ftyK K ρ d R ps c i (projIdx d c (e.map Sem.small))).mean
  have hsem := semT_run (P := fun v => v ∈ FT.freeVars) (F := canFrame K d ps c i (projIdx d c (e.map Sem.small))
      fun j => if _h : j < i then shapeTyP (shapeOf (ftyK K ρ d R ps c j ((projIdx d c (e.map Sem.small)).take j))) else TyM.err)
    (setRec_recFor K d R) rfl (teleFrame_param _ _ d ps c e hl)
    (fun t h r s' hts htv htr => hst ps c i e FT hl hty hfit hei hFT t h r s' hts htv htr)
    (hspine c i FT hFT) (fun v hv => hv) _ r s' hrun
  rw [ftyK_eq, hFT]
  dsimp only
  cases hspine c i FT hFT with
  | tind n as M hM hargs =>
    rw [semT_tind, hM] at hsem
    rw [itpT_tind, hM, hsem]
    rfl
  | _ =>
    rw [itpT_other _ _ _ _ _ _ _ _ (fun _ _ e => by cases e), hsem]
    rfl

end Ochr.Meaning.DataModel.Exists.Knot
