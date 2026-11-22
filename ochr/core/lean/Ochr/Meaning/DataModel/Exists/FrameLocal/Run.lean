import Ochr.Meaning.DataModel.Exists.FrameLocal.Fix

/-!
# Frame locality, part 6: the induction over the run (exists3, exists4; complete, in the default build)

**`runT_qset`** (the restatement of `General.runT_frameLocal`, docs/34 §18.5): at a state where the
bindings at `Q` hold constant whole values the strict test admits (`Adm`), for a term none of whose
free variables names a position of `Q` (`VarsAvoid`), under local decisions (`DecLocal`), the run at
`qset Q β' s` is the run at `s` with `qset Q β'` applied to its final state. Its use: the canonical
frame of a record key and the actual frame differ only at earlier fields no field type mentions
(`IndDecl.indexFields`), whose `teleFrame` bindings are constant (`faithBind`).

Assumes, besides `DecLocal`: the globals carry no label (`hK`, as every run lemma does). (A closure's
captured indices are free variables of its term by `mem_capOrder`, since `capOrder` became an
insertion sort, exists4.)

Each clause: rewrite the scope (`Adm.scope`), then the clause's primitives' `Comm` lemmas
(`Prims.lean`, `Join.lean`), the subterms' by the induction; the state after a subterm is `Adm` again
by `Adm.next`, its fix read off the induction at `β' := β` (`fix_of_comm`), its layout by
`runT_rinv`. A Π's binders and a closure's stages are functions of the arguments that agree only at
argument lists of the right length (`Agree.lean`); every consumer reads them only there. The
closure's body runs one frame up (`Fix.lean`).
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

section
variable {Q : Pos → Prop} {β β' : Pos → SBinding}

theorem envLe_obsStep (ws : List Sem) (s : SState) (qi : Place × Nat) : EnvLe s (obsStep ws s qi) := by
  unfold obsStep
  split
  · exact envLe_setAt _ _ _
  · exact EnvLe.refl _

theorem envLe_foldl_obsStep (ws : List Sem) : ∀ (l : List (Place × Nat)) (s : SState), EnvLe s (l.foldl (obsStep ws) s)
  | [], s => EnvLe.refl s
  | a :: l, s => (envLe_obsStep ws s a).trans (envLe_foldl_obsStep ws l _)

theorem envLe_obsEnd (reps : List Place) (ws : List Sem) (s : SState) : EnvLe s (obsEnd reps ws s) :=
  (envLe_foldl_obsStep ws _ s).trans (envLe_foldl_endLabel _ _)

/-- `Id`'s typing of the written values reads the types at the re-pointed places, outside `Q`. -/
theorem obsTyped_qset (R : DataRead) {reps : List Place} (ws : List Sem) {s : SState}
    (hq : ∀ q ∈ reps, RAvoid Q s q) : obsTyped R reps ws (qset Q β s) ↔ obsTyped R reps ws s := by
  unfold obsTyped
  refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun q => forall_congr' fun w =>
    imp_congr_right fun hi => imp_congr_right fun _ => ?_)
  rw [qset_resolve]
  cases hr : resolve s q with
  | none => exact Iff.rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    rw [qset_tyAt_not s (hq q (List.mem_of_getElem? hi) pos steps hr)]

/-- **`Id`'s comparison across the transform.** Two sides' end states, each fixed by `qset Q β`,
compared at the start's positions: the comparison at `qset Q β'` of each is the comparison of the
two. Off `Q` the transform changes nothing; at `Q` both sides read the same constant, `β`'s on one
side and `β'`'s on the other. -/
theorem observation_qset_iff (φ : Future) (reps : List Place) (ws : List Sem) {s X₁ X₂ : SState}
    (h₁ : Pre Q β' X₁) (h₁' : Pre Q β X₁) (f₁ : qset Q β X₁ = X₁) (e₁ : EnvLe s X₁)
    (h₂ : Pre Q β' X₂) (h₂' : Pre Q β X₂) (f₂ : qset Q β X₂ = X₂) (e₂ : EnvLe s X₂)
    (hq : ∀ q ∈ reps, RAvoid Q s q) (r₁ r₂ : Res) :
    observation φ reps ws s.positions r₁ (qset Q β' X₁) = observation φ reps ws s.positions r₂ (qset Q β' X₂) ↔
      observation φ reps ws s.positions r₁ X₁ = observation φ reps ws s.positions r₂ X₂ := by
  rw [observation_eq, observation_eq, observation_eq, observation_eq,
    obsEnd_qset reps ws h₁ (fun q hq' => (hq q hq').of_envLe e₁),
    obsEnd_qset reps ws h₂ (fun q hq' => (hq q hq').of_envLe e₂)]
  have F₁ : qset Q β (obsEnd reps ws X₁) = obsEnd reps ws X₁ := by
    rw [← obsEnd_qset reps ws h₁' (fun q hq' => (hq q hq').of_envLe e₁), f₁]
  have F₂ : qset Q β (obsEnd reps ws X₂) = obsEnd reps ws X₂ := by
    rw [← obsEnd_qset reps ws h₂' (fun q hq' => (hq q hq').of_envLe e₂), f₂]
  have E₁ := e₁.trans (envLe_obsEnd reps ws X₁)
  have E₂ := e₂.trans (envLe_obsEnd reps ws X₂)
  simp only [List.cons.injEq, List.map_inj_left]
  refine and_congr Iff.rfl (forall_congr' fun p => imp_congr_right fun hp => ?_)
  by_cases hQ : Q p
  · obtain ⟨f, i, rfl⟩ := pos_bind h₁ hQ
    rw [qset_valAt_of _ hQ (E₁.mem hp), qset_valAt_of _ hQ (E₂.mem hp), fix_valAt F₁ hQ (E₁.mem hp),
      fix_valAt F₂ hQ (E₂.mem hp)]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [qset_valAt_not _ hQ, qset_valAt_not _ hQ]

end

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A domain term `&A` runs `A`. -/
def domTerm : Term → Term
  | .ref A => A
  | d => d

theorem runBinds_cons (s : SState) (dcs : List DeclInfo) (pre : List PBind) (d : Term) (ds : List Term) :
    runBinds K ρ φ s dcs pre (d :: ds) =
      mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) (domTerm d) (extendBy s pre acc)) ::
        runBinds K ρ φ s dcs (pre ++ [mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) (domTerm d)
          (extendBy s pre acc))]) ds := by
  cases d <;> rfl

theorem runBinds_length (s : SState) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind),
    (runBinds K ρ φ s dcs pre ds).length = ds.length
  | [], _ => by simp [runBinds]
  | d :: ds, pre => by rw [runBinds_cons, List.length_cons, runBinds_length s dcs ds]; rfl

theorem BAgree.cons {n : Nat} {b b' : PBind} {bs bs' : List PBind} (he : b.2 = b'.2)
    (hb : ∀ acc : List Sem, acc.length = n → b.1 acc = b'.1 acc) (h : BAgree (n + 1) bs bs') :
    BAgree n (b :: bs) (b' :: bs') := by
  refine ⟨by simp [h.1], fun i c c' hc hc' => ?_⟩
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hc'
    subst hc hc'
    exact ⟨he, fun acc ha => hb acc (by omega)⟩
  | succ i =>
    simp only [List.getElem?_cons_succ] at hc hc'
    obtain ⟨hd, hty⟩ := h.2 i c c' hc hc'
    exact ⟨hd, fun acc ha => hty acc (by omega)⟩

/-- The result of a Π-term across agreeing descriptions. -/
theorem pi_result (R : DataRead) (l : Nat) {ps ps' : List PiDom} {out out' : PiCod} (h : DomAgree 0 ps ps')
    (hc : CodAgree ps.length out out') (s : SState) (f : SState → SState) :
    (if PiOk R ps' [] out' then some ((Sem.ty (piTyAt R l ps' out'), TyS.plain (TyM.univ l)), f s) else none) =
      Option.map (fun x => (x.1, f x.2))
        (if PiOk R ps [] out then some ((Sem.ty (piTyAt R l ps out), TyS.plain (TyM.univ l)), s) else none) := by
  have hc' : CodAgree (([] : List Sem).length + ps.length) out out' := by simpa using hc
  rw [piOk_congr R ps ps' [] out out' h hc', piTyAt_congr R l ps ps' out out' h hc]
  split <;> rfl


/-- After a subterm: the next state is admissible, from the equation at `β` and the run's layout. -/
theorem Adm.after (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {tl : Bool} {hint : TyS} {u : Term} {a : Res} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : runT K ρ φ tl hint u s = some (a, s₁))
    (hc : Comm Q β (runT K ρ φ tl hint u) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  obtain ⟨hR₁, -, he, -⟩ := runT_rinv K ρ φ _ hK tl u hint s s₁ a hR hu
  exact ⟨hA.next he (fix_of_comm hc hA.twin.fix hu), hR₁, he⟩

/-- The join's drop names only places outside `Q`: the entry's moved places (a whole binding has
none) and places rooted at the match's free variables (`DecLocal.join`). -/
theorem joinMoves_avoid (hD : DecLocal K.D) {Q : Pos → Prop} {β β' : Pos → SBinding} {mt : Term} {S₁ : SState}
    (hA₁ : Adm K Q β β' S₁) (hVm : VarsAvoid Q S₁ mt) (sc : List DeclInfo) :
    ∀ q ∈ K.D.joinMoves sc (movedPlaces φ S₁) mt, RAvoid Q S₁ q := fun q hq =>
  (hD.join _ _ _ _ hq).elim (rAvoid_of_moved hA₁.twin.pre hA₁.twin.fix hA₁.good) (rAvoid_of_vars hVm)

/-- [Entry]'s captures name only places outside `Q` (`DecLocal.caps`). -/
theorem blockCaps_avoid (hD : DecLocal K.D) {Q : Pos → Prop} {β β' : Pos → SBinding} {mt : Term} {s : SState}
    (hA : Adm K Q β β' s) (hVm : VarsAvoid Q s mt) (sc : List DeclInfo) :
    ∀ qk ∈ (K.D.blockCaps sc (movedPlaces φ s) mt).2, RAvoid Q s qk.1 := fun qk hq =>
  (hD.caps _ _ _ _ hq).elim (rAvoid_of_moved hA.twin.pre hA.twin.fix hA.good) (rAvoid_of_vars hVm)

/-- After an arm: as `Adm.after`. -/
theorem Adm.afterArm (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {tl : Bool} {hint : TyS} {c : Nat} {arms : List (Hint × Term)} {a : Res} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : runArm K ρ φ tl hint c arms s = some (a, s₁))
    (hc : Comm Q β (runArm K ρ φ tl hint c arms) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  obtain ⟨hR₁, -, he, -⟩ := runArm_rinv K ρ φ _ hK tl arms hint c s s₁ a hR hu
  exact ⟨hA.next he (fix_of_comm hc hA.twin.fix hu), hR₁, he⟩

/-- The assignment's write, after its right-hand side `x` (a computation commuting at `β'` and at
`β`): the place is outside `Q`, and the invalidated places share its root (`DecLocal.inv`). -/
theorem assign_tail (hD : DecLocal K.D) {Q : Pos → Prop} {β β' : Pos → SBinding} {p : Place} {x : SM Res}
    {s : SState} (hA : Adm K Q β β' s) (hp : RAvoid Q s p) (cx' : Comm Q β' x s) (cx : Comm Q β x s)
    (hx : ∀ a X, x s = some (a, X) → EnvLe s X ∧ RInv (fun _ => True) X ∧ LoU X a.2.label) :
    (do
      let ((v, R), s) ← x (qset Q β' s)
      if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
        match SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) s with
        | some (r, s₁) =>
          let s₂ := invalidate K φ p s₁
          if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
        | none => none
      else none) =
    qmap Q β' (do
      let ((v, R), s) ← x s
      if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
        match SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) s with
        | some (r, s₁) =>
          let s₂ := invalidate K φ p s₁
          if InvalidateOk K φ p s₁ ∧ lentOk K φ p s₂ then some (r, s₂) else none
        | none => none
      else none) := by
  unfold Comm at cx'
  rw [cx']
  cases h1 : x s with
  | none => rfl
  | some y =>
    obtain ⟨⟨v, R⟩, X⟩ := y
    obtain ⟨e₁, hR₁, hy₁⟩ := hx _ _ h1
    have hA₁ := hA.next e₁ (fix_of_comm cx hA.twin.fix h1)
    have hpX := hp.of_envLe e₁
    simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
    rw [placeTy_qset K φ hA₁.twin.pre' hpX, propext (labTyOk_qset X R.label _)]
    split
    · have cg := comm_guarded (assignOk_qset K φ hA₁.twin.pre' hpX) fun _ => assignAt_qset K φ hA₁.twin.pre' hpX v R.label
      have cg0 := comm_guarded (Q := Q) (β := β) (assignOk_qset K φ hA₁.twin.pre hpX) fun _ =>
        assignAt_qset K φ hA₁.twin.pre hpX v R.label
      unfold Comm at cg
      rw [cg]
      cases h2 : SM.guarded (AssignOk K φ p) (assignAt K φ p v R.label) X with
      | none => rfl
      | some z =>
        obtain ⟨r, s₁⟩ := z
        have e₂ := (assignAt_rinv K φ _ (SM.guarded_some h2).2 hR₁ hy₁).2.2.1
        have hA₂ := hA₁.next e₂ (fix_of_comm cg0 hA₁.twin.fix h2)
        obtain ⟨ei, ti, oi⟩ := hA₂.twin.invalidate K φ hA₂.decl (p := p)
          (fun q hq => rAvoid_root ((hpX.of_envLe e₂)) (hD.inv _ _ _ hq))
        simp only [qmap, Option.map_some]
        rw [ei, propext oi, lentOk_qset K φ ti.pre' ti.fix hA.good hA.good']
        split <;> rfl
    · rfl

/-- After a statement position (`SM.stmtIf`): as `Adm.after`. -/
theorem Adm.afterStmt (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {b : Bool} {hint : TyS} {u : Term} {a : Sem × TyS} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : SM.stmtIf b (runT K ρ φ false hint u) s = some (a, s₁))
    (hc : Comm Q β (SM.stmtIf b (runT K ρ φ false hint u)) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  have hx : RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
    rcases SM.stmtIf_some hu with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
    · obtain ⟨hR₁, -, e₁, -⟩ := runT_rinv K ρ φ _ hK false u _ s s₁ a hR h1
      exact ⟨hR₁, e₁⟩
    · exact ⟨hR, EnvLe.refl _⟩
  exact ⟨hA.next hx.2 (fix_of_comm hc hA.twin.fix hu), hx.1, hx.2⟩

/-- After a call's head: as `Adm.after`. -/
theorem Adm.afterHead (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {hint : TyS} {f : Term} {a : Sem × TyS} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s)
    (hu : SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false hint f) s =
      some (a, s₁))
    (hc : Comm Q β (SM.headOf f (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true))
      (runT K ρ φ false hint f)) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  have hx : RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
    rcases SM.headOf_some hu with ⟨p, h1⟩ | h1
    · have h1 := (SM.guarded_some h1).2
      exact ⟨(readPlace_rinv K φ _ h1 hR).1, readPlace_envLe K φ h1⟩
    · obtain ⟨hR₁, -, e₁, -⟩ := runT_rinv K ρ φ _ hK false f _ s s₁ a hR h1
      exact ⟨hR₁, e₁⟩
  exact ⟨hA.next hx.2 (fix_of_comm hc hA.twin.fix hu), hx.1, hx.2⟩

/-- After a call's arguments: as `Adm.after`. -/
theorem Adm.afterArgs (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s s₁ : SState} {stmt : Bool} {fT : TyM} {args : List Term} {as : List Res} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) (hu : runArgs K ρ φ stmt fT [] args s = some (as, s₁))
    (hc : Comm Q β (runArgs K ρ φ stmt fT [] args) s) :
    Adm K Q β β' s₁ ∧ RInv (fun _ => True) s₁ ∧ EnvLe s s₁ := by
  obtain ⟨hR₁, e₁, -⟩ := runArgs_rinv K ρ φ _ hK stmt fT args [] s s₁ as hR hu
  exact ⟨hA.next e₁ (fix_of_comm hc hA.twin.fix hu), hR₁, e₁⟩

theorem erasedIf_qset₂ {Q : Pos → Prop} {β : Pos → SBinding} {fl : Bool × Bool} {x y : SM (Sem × TyS)} {s : SState}
    (hx : x (qset Q β s) = qmap Q β (y s)) : SM.erasedIf fl x (qset Q β s) = qmap Q β (SM.erasedIf fl y s) := by
  unfold SM.erasedIf
  split
  · rw [hx]
    cases h : y s with
    | none => rfl
    | some z =>
      obtain ⟨⟨v, R⟩, s₁⟩ := z
      cases v <;> rfl
  · unfold SM.stmtIf
    rw [hx]
    cases fl.1 <;> cases y s <;> rfl

/-- A closure's captures: accessed and moved at the term's free variables, outside `Q`. -/
theorem caps_qset {Q : Pos → Prop} {β β' : Pos → SBinding} {s : SState} (hA : Adm K Q β β' s) {T : Term}
    (hV : VarsAvoid Q s T) :
    (FoldOk (capStep K) (CapOk K φ) (capOrder T) (qset Q β' s) ↔ FoldOk (capStep K) (CapOk K φ) (capOrder T) s) ∧
      (capOrder T).foldl (capStep K) (qset Q β' s) = qset Q β' ((capOrder T).foldl (capStep K) s) := by
  have hcap : ∀ i ∈ capOrder T, ∀ pos, s.varPos i = some pos → ¬ Q pos := fun i hi =>
    hV i ((mem_capOrder T i).1 hi)
  have hT := hA.twin
  refine ⟨foldOk_qset (capStep K) (CapOk K φ) (Twin Q β β' s) (fun i => ∀ pos, s.varPos i = some pos → ¬ Q pos)
      (fun _ _ h ha => (capStep_qset K φ hA.decl h ha).2.1) (fun _ _ h ha => (capStep_qset K φ hA.decl h ha).1)
      (fun _ _ h ha => (capStep_qset K φ hA.decl h ha).2.2) _ s hT hcap,
    foldl_qset (capStep K) (Twin Q β β' s) (fun i => ∀ pos, s.varPos i = some pos → ¬ Q pos)
      (fun _ _ h ha => (capStep_qset K φ hA.decl h ha).2.1) (fun _ _ h ha => (capStep_qset K φ hA.decl h ha).1) _ s hT hcap⟩

theorem fixCod_agree {s s' : SState} {bs bs' : List PBind} {c : Term} {n : Nat}
    (h : CodAgree n (codOf K ρ φ s bs c) (codOf K ρ φ s' bs' c)) :
    ∀ args : List Sem, args.length = n → fixCod K ρ φ s bs c args = fixCod K ρ φ s' bs' c args := fun args ha => by
  simp only [fixCod]; rw [h.2 args ha]

theorem mem_placeOccsList {a : Term} {as : List Term} (ha : a ∈ as) {c : Nat} {x : Nat × Place × PKind}
    (hx : x ∈ a.placeOccs c) : x ∈ Term.placeOccsList c as := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
    rw [Term.placeOccsList, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h
    · exact .inl hx
    · exact .inr (ih h)

theorem mem_placeOccsArms {a : Hint × Term} {as : List (Hint × Term)} (ha : a ∈ as) {c : Nat}
    {x : Nat × Place × PKind} (hx : x ∈ a.2.placeOccs c) : x ∈ Term.placeOccsArms c as := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
    obtain ⟨h, t⟩ := b
    rw [Term.placeOccsArms, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | h'
    · exact .inl hx
    · exact .inr (ih h')

theorem root_mem_assign (p : Place) (u : Term) : p.root ∈ (Term.assign p u).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .assign, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

theorem Comm.eq {α : Type 3} {Q : Pos → Prop} {β : Pos → SBinding} {x : SM α} {s : SState} (h : Comm Q β x s) :
    x (qset Q β s) = qmap Q β (x s) := h

theorem root_mem_matchNat (p : Place) (z u : Term) : p.root ∈ (Term.matchNat p z u).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .scrut, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

theorem root_mem_matchInd (p : Place) (n : String) (arms : List (Hint × Term)) :
    p.root ∈ (Term.matchInd p n arms).freeVars :=
  (mem_freeVars _ _).mpr ⟨0, p, .scrut, by simp [Term.placeOccs], Nat.zero_le _, rfl⟩

mutual
theorem runT_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
 :
    ∀ (tl : Bool) (t : Term) (hint : TyS) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → VarsAvoid Q s t → RInv (fun _ => True) s → Comm Q β' (runT K ρ φ tl hint t) s
  | tl, .place p, hint, s, Q, β, β', hA, hV, _ => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    exact comm_erasedIf (comm_guarded (contentOk_qset K φ hA.twin.pre' p)
      (fun _ => readPlace_qset K φ hA.twin.pre' (rAvoid_of_vars hV (root_mem_place p)) _))
  | tl, .const n, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .sort l, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .nat, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .unit, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .zero, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .tt, hint, s, Q, β, β', _, _, _ => by unfold Comm; rw [runT]; rfl
  | tl, .val v, hint, s, Q, β, β', _, _, _ => by
    unfold Comm; rw [runT_val_def, runT_val_def]
    cases v <;> first
      | rfl
      | (simp only [strictVal, SM.strictS, pure]; split <;> (try split) <;> rfl)
  | tl, .succ u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD false u _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .ref A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf (comm_strictS (comm_bind (runT_qset hK hD false A _ s Q β β' hA
      (hV.sub fun x hx => by simpa [Term.placeOccs] using hx) hR) fun _ _ _ => comm_pure _ _))
  | tl, .seq u w, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVw : VarsAvoid Q s w := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_bind (runT_qset hK hD false u _ s Q β β' hA hVu hR) fun a s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false u _ s Q β β hA.self hVu hR)
    refine comm_bind (comm_guardMod (discardOk_qset K φ hA₁.twin.pre' a.2)
      (fun _ => discardEnd_qset hA₁.twin.pre' a.2)) fun _ s₂ h2 => ?_
    have e₂ : s₂ = discardEnd a.2 s₁ := (SM.guardMod_some h2).2
    subst e₂
    have hfix₂ : qset Q β (discardEnd a.2 s₁) = discardEnd a.2 s₁ := by
      rw [← discardEnd_qset hA₁.twin.pre a.2, hA₁.twin.fix]
    obtain ⟨hR₂, he₂, -⟩ := discardEnd_props (fun _ => True) hR₁ a.2
    have hA₂ := hA₁.next (s₁ := discardEnd a.2 s₁) he₂ hfix₂
    exact runT_qset hK hD tl w _ _ Q β β' hA₂ ((hVw.of_envLe he₁).of_envLe he₂) hR₂
  | tl, .eq A a b, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVa : VarsAvoid Q s a := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVb : VarsAvoid Q s b := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_onCopy (comm_bind (runT_qset hK hD false A _ s Q β β' hA hVA hR) fun x s₁ h1 => ?_)
    obtain ⟨hA₁, hR₁, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false A _ s Q β β hA.self hVA hR)
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD false a _ s₁ Q β β' hA₁ (hVa.of_envLe he₁) hR₁))
      fun y s₂ h2 => ?_
    have e₂ := SM.onCopy_state h2; subst e₂
    obtain ⟨va, _⟩ := y
    dsimp only
    refine comm_bind (comm_onCopy (runT_qset hK hD false b _ s₂ Q β β' hA₁ (hVb.of_envLe he₁) hR₁))
      fun z s₃ h3 => ?_
    have e₃ := SM.onCopy_state h3; subst e₃
    obtain ⟨vb, _⟩ := z
    unfold Comm; dsimp only; split <;> rfl
  | tl, .cong c h, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    have hVh : VarsAvoid Q s h := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    exact comm_onCopy (comm_bind (runT_qset hK hD false h _ s Q β β' hA hVh hR) fun _ _ _ => comm_pure _ _)
  | tl, .ascribe u A, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    refine comm_erasedIf (comm_strictS (comm_bind (comm_onCopy (runT_qset hK hD false A _ s Q β β' hA hVA hR))
      fun x s₁ h1 => ?_))
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨TA, _⟩ := x
    dsimp only
    refine comm_bind (runT_qset hK hD false u _ s₁ Q β β' hA hVu hR) fun y s₂ _ => ?_
    obtain ⟨v, R⟩ := y
    exact comm_ite (P := fun s => labTyOk s R.label TA.asTy) Iff.rfl (fun _ => rfl) (fun _ => rfl)
  | tl, .tind n args, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]
    cases hd : List.find? (fun x => x.name == n) K.Γ with
    | none => rfl
    | some d =>
      dsimp only
      refine comm_bind (runParams_qset hK hD _ args 0 [] s Q β β' hA
        (fun a ha => hV.sub fun x hx => by simpa [Term.placeOccs] using mem_placeOccsList ha hx) hR) fun _ _ _ => ?_
      unfold Comm; dsimp only; split <;> rfl
  | tl, .id A t u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only
    have hVA : VarsAvoid Q s A := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVt : VarsAvoid Q s t := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have cA := comm_onCopy (runT_qset hK hD false A (.plain TyM.err) s Q β β' hA hVA hR)
    unfold Comm at cA
    rw [cA, hA.scope]
    cases hx : (runT K ρ φ false (TyS.plain TyM.err) A).onCopy s with
    | none => rfl
    | some x =>
      obtain ⟨⟨TA, RA⟩, sA⟩ := x
      dsimp only [qmap, Option.map_some]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have ct := runT_qset hK hD false t (.plain TA.asTy) s Q β β' hA hVt hR
      have cu := runT_qset hK hD false u (.plain TA.asTy) s Q β β' hA hVu hR
      unfold Comm qmap at ct cu
      rw [ct, cu]
      cases h1 : runT K ρ φ false (.plain TA.asTy) t s with
      | none => rfl
      | some o₁ =>
        cases h2 : runT K ρ φ false (.plain TA.asTy) u s with
        | none => simp
        | some o₂ =>
          obtain ⟨r₁, X₁⟩ := o₁
          obtain ⟨r₂, X₂⟩ := o₂
          obtain ⟨hA₁, -, he₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false t _ s Q β β hA.self hVt hR)
          obtain ⟨hA₂, -, he₂⟩ := Adm.after K ρ φ hK hA hR h2 (runT_qset hK hD false u _ s Q β β hA.self hVu hR)
          have hq : ∀ q ∈ K.D.rePointed (scopeOf s) t, RAvoid Q s q := fun q hq =>
            rAvoid_of_vars hVt (hD.rep _ _ _ hq)
          have key : (∀ ws : List Sem, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws (qset Q β' s) →
              observation φ (K.D.rePointed (scopeOf s) t) ws (qset Q β' s).positions r₁ (qset Q β' X₁) =
                observation φ (K.D.rePointed (scopeOf s) t) ws (qset Q β' s).positions r₂ (qset Q β' X₂)) =
              (∀ ws : List Sem, obsTyped K.dm.read (K.D.rePointed (scopeOf s) t) ws s →
                observation φ (K.D.rePointed (scopeOf s) t) ws s.positions r₁ X₁ =
                  observation φ (K.D.rePointed (scopeOf s) t) ws s.positions r₂ X₂) := by
            rw [qset_positions]
            exact propext (forall_congr' fun ws => imp_congr (obsTyped_qset _ ws hq)
              (observation_qset_iff φ _ ws hA₁.twin.pre' hA₁.twin.pre hA₁.twin.fix he₁
                hA₂.twin.pre' hA₂.twin.pre hA₂.twin.fix he₂ hq r₁ r₂))
          simp only [Option.map_some, Option.bind_some]
          rw [key]
          split <;> rfl
  | tl, .matchNat p z u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVz : VarsAvoid Q s z := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_matchNat p z u)
    have ct := comm_guarded (tagOk_qset K φ hA.twin.pre' p) fun _ => tagOf_qset K φ hA.twin.pre' hp natTag
    unfold Comm at ct ⊢
    dsimp only
    rw [ct]
    cases h1 : SM.guarded (TagOk K φ p) (tagOf K φ p natTag) s with
    | none => rfl
    | some y =>
      obtain ⟨tg, s₀⟩ := y
      have ht := (SM.guarded_some h1).2
      have ct0 := comm_guarded (Q := Q) (β := β) (tagOk_qset K φ hA.twin.pre p) fun _ => tagOf_qset K φ hA.twin.pre hp natTag
      obtain ⟨hR₀, e₀, -⟩ := tagOf_rinv K φ _ ht hR
      have hA₀ : Adm K Q β β' s₀ := hA.next e₀ (fix_of_comm ct0 hA.twin.fix h1)
      simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      obtain ⟨hR₁, e₁', -⟩ := matchEntry_props K φ (fun _ => True) (!tl) (.matchNat p z u) hR₀
      generalize hme : matchEntry K φ (!tl) (.matchNat p z u) s₀ = me at hR₁ e₁'
      obtain ⟨S₁, L⟩ := me
      obtain ⟨L', hme', hT₁, hL, -, hok⟩ := matchEntry_qset K φ hA₀.decl hD.inv hA₀.twin hA₀.good hA₀.good' (!tl) _
        (blockCaps_avoid K φ hD hA₀ (hV.of_envLe e₀) _) hme
      rw [hme', propext hok]
      dsimp only at hR₁ e₁' ⊢
      have hA₁ : Adm K Q β β' S₁ := hA₀.next e₁' hT₁.fix
      have e₁ := e₀.trans e₁'
      rw [movedPlaces_qset K φ hT₁.pre' hT₁.fix hA.good hA.good']
      by_cases hm : MatchEntryOk K φ (!tl) (Term.matchNat p z u) s₀
      rotate_left
      · simp [optCheck, hm]
      simp only [optCheck, if_pos hm, Option.bind_some]
      have arm : ∀ w : Term, VarsAvoid Q s w →
          Comm Q β' (runT K ρ φ tl (tailHint tl hint) w) S₁ → Comm Q β (runT K ρ φ tl (tailHint tl hint) w) S₁ →
          (do
            let a ← runT K ρ φ tl (tailHint tl hint) w (qset Q β' S₁)
            optCheck (JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd)
            some ((a.1.fst, a.1.snd), L' a.1.snd.label (joinDrop K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd))) =
          Option.map (fun x => (x.fst, qset Q β' x.snd)) (do
            let a ← runT K ρ φ tl (tailHint tl hint) w S₁
            optCheck (JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd)
            some ((a.1.fst, a.1.snd), L a.1.snd.label (joinDrop K φ (movedPlaces φ S₁) (Term.matchNat p z u) a.snd))) := by
        intro w hVw cw cw0
        unfold Comm qmap at cw
        rw [cw]
        cases h2 : runT K ρ φ tl (tailHint tl hint) w S₁ with
        | none => rfl
        | some a =>
          obtain ⟨⟨r, R⟩, X⟩ := a
          obtain ⟨hA₂, -, e₂⟩ := Adm.after K ρ φ hK hA₁ hR₁ h2 cw0
          obtain ⟨ej, -, ok⟩ := joinDrop_qset K φ hA₁.decl ⟨hA₂.twin.pre, hA₂.twin.pre', hA₂.twin.fix, e₂⟩
            (movedPlaces φ S₁) (Term.matchNat p z u) (joinMoves_avoid K φ hD hA₁ (hV.of_envLe e₁) _)
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [propext ok, ej, hL]
          by_cases hj : JoinDropOk K φ (movedPlaces φ S₁) (Term.matchNat p z u) X
          · simp [optCheck, hj]
          · simp [optCheck, hj]
      have az := arm z hVz (runT_qset hK hD tl z _ S₁ Q β β' hA₁ (hVz.of_envLe e₁) hR₁)
        (runT_qset hK hD tl z _ S₁ Q β β hA₁.self (hVz.of_envLe e₁) hR₁)
      have au := arm u hVu (runT_qset hK hD tl u _ S₁ Q β β' hA₁ (hVu.of_envLe e₁) hR₁)
        (runT_qset hK hD tl u _ S₁ Q β β hA₁.self (hVu.of_envLe e₁) hR₁)
      cases tg.asNat with
      | none => rfl
      | some k =>
        cases k with
        | zero => exact az
        | succ k => exact au
  | tl, .matchInd p n arms, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVa : ∀ a ∈ arms, VarsAvoid Q s a.2 := fun a ha => hV.sub fun x hx => by
      simp only [Term.placeOccs, List.mem_cons]; exact .inr (mem_placeOccsArms ha hx)
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_matchInd p n arms)
    have ct := comm_guarded (tagOk_qset K φ hA.twin.pre' p) fun _ => tagOf_qset K φ hA.twin.pre' hp indTag
    unfold Comm at ct ⊢
    dsimp only
    rw [ct]
    cases h1 : SM.guarded (TagOk K φ p) (tagOf K φ p indTag) s with
    | none => rfl
    | some y =>
      obtain ⟨tg, s₀⟩ := y
      have ht := (SM.guarded_some h1).2
      have ct0 := comm_guarded (Q := Q) (β := β) (tagOk_qset K φ hA.twin.pre p) fun _ => tagOf_qset K φ hA.twin.pre hp indTag
      obtain ⟨hR₀, e₀, -⟩ := tagOf_rinv K φ _ ht hR
      have hA₀ : Adm K Q β β' s₀ := hA.next e₀ (fix_of_comm ct0 hA.twin.fix h1)
      simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      generalize (!tl && !tg.isProof && !oneCtor K.Γ n) = ent
      obtain ⟨hR₁, e₁', -⟩ := matchEntry_props K φ (fun _ => True) ent (.matchInd p n arms) hR₀
      generalize hme : matchEntry K φ ent (.matchInd p n arms) s₀ = me at hR₁ e₁'
      obtain ⟨S₁, L⟩ := me
      obtain ⟨L', hme', hT₁, hL, -, hok⟩ := matchEntry_qset K φ hA₀.decl hD.inv hA₀.twin hA₀.good hA₀.good' ent _
        (blockCaps_avoid K φ hD hA₀ (hV.of_envLe e₀) _) hme
      rw [hme', propext hok]
      dsimp only at hR₁ e₁' ⊢
      have hA₁ : Adm K Q β β' S₁ := hA₀.next e₁' hT₁.fix
      have e₁ := e₀.trans e₁'
      rw [movedPlaces_qset K φ hT₁.pre' hT₁.fix hA.good hA.good']
      by_cases hm : MatchEntryOk K φ ent (Term.matchInd p n arms) s₀
      rotate_left
      · simp [optCheck, hm]
      simp only [optCheck, if_pos hm, Option.bind_some]
      split
      · rename_i c hc
        have ca := runArm_qset hK hD tl (tailHint tl hint) c arms S₁ Q β β' hA₁ (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        have ca0 := runArm_qset hK hD tl (tailHint tl hint) c arms S₁ Q β β hA₁.self (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        unfold Comm qmap at ca
        rw [ca]
        cases h2 : runArm K ρ φ tl (tailHint tl hint) c arms S₁ with
        | none => rfl
        | some a =>
          obtain ⟨⟨r, R⟩, X⟩ := a
          obtain ⟨hA₂, -, e₂⟩ := Adm.afterArm K ρ φ hK hA₁ hR₁ h2 ca0
          obtain ⟨ej, -, ok⟩ := joinDrop_qset K φ hA₁.decl ⟨hA₂.twin.pre, hA₂.twin.pre', hA₂.twin.fix, e₂⟩
            (movedPlaces φ S₁) (Term.matchInd p n arms) (joinMoves_avoid K φ hD hA₁ (hV.of_envLe e₁) _)
          simp only [Option.map_some, Option.bind_some]
          rw [propext ok, ej, hL]
          by_cases hj : tg.isProof = true ∨ oneCtor K.Γ n = true ∨ JoinDropOk K φ (movedPlaces φ S₁) (Term.matchInd p n arms) X
          · simp only [if_pos hj, Option.bind_some, Option.map_some]
            cases tg <;> dsimp only <;> (try split) <;> rfl
          · simp only [if_neg hj, Option.bind_none, Option.map_none]
      · cases tg
        case proof =>
          dsimp only
          exact comm_anyArm fun c => runArm_qset hK hD tl (tailHint tl hint) c arms S₁ Q β β' hA₁
            (fun a ha => (hVa a ha).of_envLe e₁) hR₁
        all_goals rfl
  | tl, .borrow p, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_borrow p)
    have cb := comm_strictS (R := K.dm.read) (comm_guarded (contentOk_qset K φ hA.twin.pre' p) fun _ =>
      borrowPlace_qset K φ hA.twin.pre' hp)
    have cb0 := comm_strictS (R := K.dm.read) (comm_guarded (Q := Q) (β := β) (contentOk_qset K φ hA.twin.pre p) fun _ =>
      borrowPlace_qset K φ hA.twin.pre hp)
    unfold Comm at cb ⊢
    dsimp only
    rw [cb]
    cases hb : SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s with
    | none => rfl
    | some y =>
      obtain ⟨r₀, s₁⟩ := y
      have hb' := (SM.guarded_some (SM.strictS_some hb).1).2
      have e₁ := borrowPlace_envLe K φ hb'
      have hA₁ : Adm K Q β β' s₁ := hA.next e₁ (fix_of_comm cb0 hA.twin.fix hb)
      obtain ⟨ei, ti, oi⟩ := hA₁.twin.invalidate K φ hA₁.decl (p := p)
        (fun q hq => rAvoid_root (hp.of_envLe e₁) (hD.inv _ _ _ hq))
      simp only [qmap, Option.map_some]
      rw [ei, propext oi, lentOk_qset K φ ti.pre' ti.fix hA.good hA.good']
      split <;> rfl
  | tl, .assign p u, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hp : RAvoid Q s p := rAvoid_of_vars hV (root_mem_assign p u)
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have cc := contentOf_qset K φ hA.twin.pre' hp
    unfold Comm at cc ⊢
    dsimp only
    rw [cc]
    have tail := fun T => assign_tail K φ hD hA hp (runT_qset hK hD false u T s Q β β' hA hVu hR)
      (runT_qset hK hD false u T s Q β β hA.self hVu hR) fun a X h =>
        have := runT_rinv K ρ φ _ hK false u T s X a hR h
        ⟨this.2.2.1, this.1, this.2.1⟩
    by_cases hh : u.assignHinted = true
    · simp only [hh, if_true]
      cases contentOf K φ p s with
      | none => exact tail _
      | some y => exact tail _
    · simp only [hh, if_false, Bool.false_eq_true]
      exact tail _
  | tl, .letIn x u w, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVu : VarsAvoid Q s u := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have cu := runT_qset hK hD false u (.plain TyM.err) s Q β β' hA hVu hR
    unfold Comm at cu ⊢
    dsimp only
    rw [cu]
    cases h1 : runT K ρ φ false (.plain TyM.err) u s with
    | none => rfl
    | some y =>
      obtain ⟨⟨v, T⟩, X⟩ := y
      obtain ⟨hA₁, hR₁, e₁⟩ := Adm.after K ρ φ hK hA hR h1 (runT_qset hK hD false u _ s Q β β hA.self hVu hR)
      have hy₁ := (runT_rinv K ρ φ _ hK false u _ s X (v, T) hR h1).2.1
      simp only [qmap, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [hA.scope]
      generalize hb : ({ ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } : SBinding) = b
      rw [qset_pushBindShaped X hA₁.twin.pre'.pos hA₁.twin.pre'.shape b]
      have hA₂ := hA₁.push b
      have hR₂ : RInv (fun _ => True) (pushBindShaped X b) := by
        subst hb
        exact pushBindShaped_rinv hR₁ _ v rfl fun l hl => by
          rcases hy₁ l hl with ⟨h' | h', hn⟩
          · exact ⟨.inl h', hn⟩
          · exact ⟨.inr (.inr h'), hn⟩
      have hVw : VarsAvoid Q (pushBindShaped X b) w :=
        VarsAvoid.push (hV.of_envLe e₁) (fun x hx => by simp [Term.placeOccs, hx]) (envPush_pushBindShaped X b)
          hA₁.twin.pre.pos
      have cw := runT_qset hK hD tl w (tailHint tl hint) _ Q β β' hA₂ hVw hR₂
      unfold Comm at cw
      rw [cw]
      cases h2 : runT K ρ φ tl (tailHint tl hint) w (pushBindShaped X b) with
      | none => rfl
      | some z =>
        obtain ⟨⟨r, R⟩, Z⟩ := z
        obtain ⟨hA₃, -, -⟩ := Adm.after K ρ φ hK hA₂ hR₂ h2 (runT_qset hK hD tl w _ _ Q β β hA₂.self hVw hR₂)
        have hP := hA₃.twin.pre'
        simp only [qmap, Option.map_some, Option.bind_some, qset_getLast, qset_topIdx, qset_shape_eq hP.shape]
        cases hg : Z.env.getLast? with
        | none =>
          simp only [Option.map_none]
          rw [propext (letLendersOk_qset K φ hP), letLenders_qset hP, qset_dropLast]
          split <;> rfl
        | some fr =>
          simp only [Option.map_some, qframe_binds_length]
          cases Z.shape (.bind Z.topIdx (fr.binds.length - 1)) with
          | none =>
            dsimp only
            rw [propext (letLendersOk_qset K φ hP), letLenders_qset hP, qset_dropLast]
            split <;> rfl
          | some l =>
            dsimp only
            rw [qset_endLabel' hP, qset_dropLast]
            by_cases hE : EndOk K φ Z l
            · rw [if_pos ((endOk_qset K φ hP l).2 hE), if_pos hE]; rfl
            · rw [if_neg (fun h => hE ((endOk_qset K φ hP l).1 h)), if_neg hE]; rfl
  | tl, .ctor ty c x ps args, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    cases hd : List.find? (fun x => x.name == ty) K.Γ with
    | none => exact comm_fail _
    | some d =>
      dsimp only
      have hVp : ∀ a ∈ ps, VarsAvoid Q s a := fun a ha => hV.sub fun x hx => by
        simp only [Term.placeOccs, List.mem_append]; exact .inl (mem_placeOccsList ha hx)
      have hVa : ∀ a ∈ args, VarsAvoid Q s a := fun a ha => hV.sub fun x hx => by
        simp only [Term.placeOccs, List.mem_append]; exact .inr (mem_placeOccsList ha hx)
      refine comm_bind (runParams_qset hK hD d ps 0 [] s Q β β' hA hVp hR) fun psM s₁ h1 => ?_
      have e₁ := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e₁
      refine comm_bind (runFields_qset hK hD _ d c args 0 _ _ [] s₁ Q β β' hA hVa hR) fun fsol s₂ _ => ?_
      unfold Comm; dsimp only
      by_cases hP : ps.isEmpty = true ∨ paramsOk K.dm d psM
      · rw [if_pos hP, if_pos hP]
        have co : ∀ r? : Option Rec, Comm Q β' (ctorOut K.dm d c fsol.1 r?) s₂ := fun r? => by
          cases r? with
          | none => exact comm_fail _
          | some r => exact comm_pure _ _
        exact comm_strictS (co _)
      · rw [if_neg hP, if_neg hP]; rfl
  | tl, .call f args hd, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    refine comm_erasedIf ?_
    have hVf : VarsAvoid Q s f := hV.sub fun x hx => by simp [Term.placeOccs, hx]
    have hVa : ∀ a ∈ args, VarsAvoid Q s a := fun a ha => hV.sub fun x hx => by
      simp only [Term.placeOccs, List.mem_append]; exact .inr (mem_placeOccsList ha hx)
    have chead := fun (β₁ : Pos → SBinding) (hA₁ : Adm K Q β β₁ s) =>
      comm_headOf (f := f) (rd := fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true))
        (rn := runT K ρ φ false (.plain TyM.err) f) (s := s)
        (fun p hp => by
          subst hp
          exact comm_guarded (contentOk_qset K φ hA₁.twin.pre' p) fun _ =>
            readPlace_qset K φ hA₁.twin.pre' (rAvoid_of_vars hVf (root_mem_place p)) true)
        (fun _ => runT_qset hK hD false f _ s Q β β₁ hA₁ hVf hR)
    refine comm_bind (chead β' hA) fun fv s₁ h1 => ?_
    obtain ⟨hA₁, hR₁, e₁⟩ := Adm.afterHead K ρ φ hK hA hR h1 (chead β hA.self)
    refine comm_bind (runArgs_qset hK hD _ _ args [] s₁ Q β β' hA₁ (fun a ha => (hVa a ha).of_envLe e₁) hR₁)
      fun as s₂ h2 => ?_
    have hA₂ := (Adm.afterArgs K ρ φ hK hA₁ hR₁ h2
      (runArgs_qset hK hD _ _ args [] s₁ Q β β hA₁.self (fun a ha => (hVa a ha).of_envLe e₁) hR₁)).1
    unfold Comm; dsimp only
    rw [propext (borrowArgsTyped_qset hA₂.twin.pre' _ fv as)]
    split
    · exact callOf_qset hA₂.twin.pre' _ fv as
    · rfl
  | tl, .prim n args, hint, s, Q, β, β', hA, hV, hR => by
    have hall : ∀ t ∈ args, ∀ (tl : Bool) (hint : TyS) (s₁ : SState) (β₁ : Pos → SBinding), Adm K Q β β₁ s₁ →
        VarsAvoid Q s₁ t → RInv (fun _ => True) s₁ → Comm Q β₁ (runT K ρ φ tl hint t) s₁ :=
      fun t ht tl hint s₁ β₁ hA₁ hV₁ hR₁ => runAll_qset hK hD args t ht tl hint s₁ Q β β₁ hA₁ hV₁ hR₁
    have hVa : ∀ t ∈ args, VarsAvoid Q s t := fun t ht => hV.sub fun x hx => by
      simp only [Term.placeOccs]; exact mem_placeOccsList ht hx
    have prem : ∀ xs : List Term, (∀ x ∈ xs, x ∈ args) → ∀ s₁, Adm K Q β β' s₁ → EnvLe s s₁ →
        RInv (fun _ => True) s₁ →
        Comm Q β' (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
          (pure ((.proof, .plain (TyM.prop True)) : Res))) s₁ := by
      intro xs
      induction xs with
      | nil => intro _ s₁ _ _ _; exact comm_pure _ _
      | cons x xs ih =>
        intro hxs s₁ hA₁ e₁ hR₁
        have hx := hxs x (by simp)
        refine comm_bind (hall x hx false _ s₁ β' hA₁ ((hVa x hx).of_envLe e₁) hR₁) fun _ s₂ h2 => ?_
        obtain ⟨hA₂, hR₂, e₂⟩ := Adm.after K ρ φ hK hA₁ hR₁ h2
          (hall x hx false _ s₁ β hA₁.self ((hVa x hx).of_envLe e₁) hR₁)
        exact ih (fun y hy => hxs y (by simp [hy])) s₂ hA₂ (e₁.trans e₂) hR₂
    by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
    · obtain ⟨h0, rfl, rfl⟩ := e1
      rw [runT]; exact comm_onCopy (prem [h0] (by simp) s hA (EnvLe.refl _) hR)
    by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
    · obtain ⟨h0, k0, rfl, rfl⟩ := e2
      rw [runT]; exact comm_onCopy (prem [h0, k0] (by simp) s hA (EnvLe.refl _) hR)
    by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, rfl⟩ := e3
      rw [runT]; exact comm_onCopy (prem [h0, u0] (by simp) s hA (EnvLe.refl _) hR)
    by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
    · obtain ⟨h0, u0, rfl, rfl⟩ := e4
      rw [runT]; exact comm_onCopy (prem [h0, u0] (by simp) s hA (EnvLe.refl _) hR)
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ
      have hVt : VarsAvoid Q s t := hVa t (by simp)
      rw [runT]
      unfold Comm; dsimp only; rw [hA.scope]
      refine comm_erasedIf ?_
      refine comm_bind (comm_onCopy (hall A (by simp) false _ s β' hA (hVa A (by simp)) hR)) fun _ s₁ e1 => ?_
      have e := SM.onCopy_state e1; subst s₁
      refine comm_bind (comm_onCopy (hall a (by simp) false _ s β' hA (hVa a (by simp)) hR)) fun _ s₁ e1 => ?_
      have e := SM.onCopy_state e1; subst s₁
      refine comm_bind (comm_onCopy (hall b (by simp) false _ s β' hA (hVa b (by simp)) hR)) fun _ s₁ e1 => ?_
      have e := SM.onCopy_state e1; subst s₁
      refine comm_bind (comm_onCopy (hall P (by simp) false _ s β' hA (hVa P (by simp)) hR)) fun _ s₁ e1 => ?_
      have e := SM.onCopy_state e1; subst s₁
      refine comm_bind (comm_onCopy (hall h' (by simp) false _ s β' hA (hVa h' (by simp)) hR)) fun _ s₁ e1 => ?_
      have e := SM.onCopy_state e1; subst s₁
      unfold Comm; dsimp only
      obtain ⟨hR₁, e₁', -⟩ := matchEntry_props K φ (fun _ => True) true t hR
      generalize hme : matchEntry K φ true t s = me at hR₁ e₁'
      obtain ⟨S₁, L⟩ := me
      obtain ⟨L', hme', hT₁, -, -, hok⟩ := matchEntry_qset K φ hA.decl hD.inv hA.twin hA.good hA.good' true t
        (blockCaps_avoid K φ hD hA hVt _) hme
      rw [hme']
      dsimp only at hR₁ e₁' ⊢
      have hA₁ : Adm K Q β β' S₁ := hA.next e₁' hT₁.fix
      rw [movedPlaces_qset K φ hT₁.pre' hT₁.fix hA.good hA.good']
      by_cases hm : MatchEntryOk K φ true t s
      · rw [if_pos (hok.2 hm), if_pos hm]
        have ct := hall t (by simp) false (.plain TyM.err) S₁ β' hA₁ (hVt.of_envLe e₁') hR₁
        unfold Comm qmap at ct
        rw [ct]
        cases h2 : runT K ρ φ false (.plain TyM.err) t S₁ with
        | none => rfl
        | some z =>
          obtain ⟨⟨r, R⟩, X⟩ := z
          obtain ⟨hA₂, -, e₂⟩ := Adm.after K ρ φ hK hA₁ hR₁ h2
            (hall t (by simp) false _ S₁ β hA₁.self (hVt.of_envLe e₁') hR₁)
          obtain ⟨ej, -, ok⟩ := joinDrop_qset K φ hA₁.decl ⟨hA₂.twin.pre, hA₂.twin.pre', hA₂.twin.fix, e₂⟩
            (movedPlaces φ S₁) (.prim "J" [A, a, b, P, h', t]) (joinMoves_avoid K φ hD hA₁ (hV.of_envLe e₁') _)
          simp only [Option.map_some]
          rw [ej]
          by_cases hj : JoinDropOk K φ (movedPlaces φ S₁) (.prim "J" [A, a, b, P, h', t]) X
          · rw [if_pos (ok.2 hj), if_pos hj]; rfl
          · rw [if_neg (fun h => hj (ok.1 h)), if_neg hj]; rfl
      · rw [if_neg (fun h => hm (hok.1 h)), if_neg hm]; rfl
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, rfl⟩ := hc
      have hu : VarsAvoid Q s u := hVa u (by simp)
      have cu := hall u (by simp) false hint s β' hA hu hR
      have key : ∀ name : String, Comm Q β' (fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim name [u]))
          (SM.headOf u (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) (runT K ρ φ false hint u)) s) s := by
        intro name
        unfold Comm; dsimp only; rw [hA.scope]
        refine comm_erasedIf (comm_headOf (fun p hp => ?_) fun _ => cu)
        subst hp
        exact comm_guarded (contentOk_qset K φ hA.twin.pre' p) fun _ =>
          readPlace_qset K φ hA.twin.pre' (rAvoid_of_vars hu (root_mem_place p)) true
      rcases hn with rfl | rfl | rfl <;> (rw [runT]; exact key _)
    -- `split f in u`: its term's run at the form's hint and tail flag (docs/31 D175)
    by_cases hsp : ∃ f u, n = "split" ∧ args = [.const f, u]
    · obtain ⟨f, u, rfl, rfl⟩ := hsp
      have hu : VarsAvoid Q s u := hVa u (by simp)
      have cu := hall u (by simp) tl hint s β' hA hu hR
      have key : Comm Q β' (fun s => SM.erasedIf (K.D.flags (scopeOf s) (.prim "split" [.const f, u]))
          (runT K ρ φ tl hint u) s) s := by
        unfold Comm; dsimp only; rw [hA.scope]
        exact comm_erasedIf cu
      rw [runT]; exact key
    have hs' : ∀ f u, n = "split" → args = [.const f, u] → False := fun f u e1 e2 => hsp ⟨f, u, e1, e2⟩
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    have f1 : ∀ h, n = "symm" → args = [h] → False := fun h0 a b => e1 ⟨h0, a, b⟩
    have f2 : ∀ h k, n = "trans" → args = [h, k] → False := fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
    have f3 : ∀ h u, n = "rewrite" → args = [h, u] → False := fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
    have f4 : ∀ h u, n = "rewriteR" → args = [h, u] → False := fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
    rw [runT]
    all_goals first | exact comm_fail _ | exact f1 | exact f2 | exact f3 | exact f4 | exact hJ' | exact hc1 | exact hc2 | exact hc3 | exact hs'
  | tl, .pi hs ds c, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runT]; dsimp only; rw [hA.scope]
    have hB := runBinds_qset hK hD s Q β β' hA hR (.pi hs ds c) hV (K.D.paramDecls (scopeOf s) ds) ds [] []
      (BAgree.refl 0 []) (fun x hx => by simp at hx; simp [Term.placeOccs, hx])
    have hlen := runBinds_length K ρ φ s (K.D.paramDecls (scopeOf s) ds) ds []
    have hpsl : (psOf (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) ds).length = ds.length :=
      psOf_length _ _ hlen
    have hext : ∀ acc, extendBy (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) acc =
        qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) := fun acc => by
      rw [← extendBy_agree hB, qset_extendBy s hA.twin.pre.pos]
    have hcod : ∀ u : Term, (∀ x ∈ u.placeOccs ds.length, x ∈ (Term.pi hs ds c).placeOccs 0) →
        ∀ acc : List Sem, acc.length = ds.length →
          runT K ρ φ false (.plain TyM.err) u (qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) =
          qmap Q β' (runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) →
          (match runT K ρ φ false (.plain TyM.err) u (extendBy (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
            | some ((v, _), _) => v.asTy
            | none => TyM.err) =
          (match runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
            | some ((v, _), _) => v.asTy
            | none => TyM.err) := by
      intro u _ acc _ hu
      rw [hext, hu]
      cases runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) <;> rfl
    have hc0 : ∀ x ∈ c.placeOccs ds.length, x ∈ (Term.pi hs ds c).placeOccs 0 := fun x hx => by
      simp [Term.placeOccs, hx]
    have hcIH : ∀ acc : List Sem, acc.length = ds.length →
        runT K ρ φ false (.plain TyM.err) c (qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) =
          qmap Q β' (runT K ρ φ false (.plain TyM.err) c (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) :=
      fun acc ha => runT_qset hK hD false c _ _ Q β β' (hA.extend _ acc)
        (hV.extend hc0 hA.twin.pre.pos _ ha) (rinv_extendBy hR _ acc)
    unfold qmap
    refine pi_result K.dm.read _ (psOf_agree hB ds) ?_ s (qset Q β')
    rw [hpsl]
    cases c
    case ref U =>
      have hU0 : ∀ x ∈ U.placeOccs ds.length, x ∈ (Term.pi hs ds (.ref U)).placeOccs 0 := fun x hx =>
        hc0 x (by simpa [Term.placeOccs] using hx)
      exact ⟨rfl, fun acc ha => (hcod U hU0 acc ha (runT_qset hK hD false U _ _ Q β β' (hA.extend _ acc)
        (hV.extend hU0 hA.twin.pre.pos _ ha) (rinv_extendBy hR _ acc))).symm⟩
    all_goals exact ⟨rfl, fun acc ha => (hcod _ hc0 acc ha (hcIH acc ha)).symm⟩
  | tl, .fix self hs ds c dec body, hint, s, Q, β, β', hA, hV, hR => by
    unfold Comm
    rw [run_fix_def, run_fix_def]
    have hbo : bindsOf K ρ φ (qset Q β' s) ds = runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds := by
      unfold bindsOf; rw [hA.scope]
    have hbs : bindsOf K ρ φ s ds = runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds := rfl
    simp only [runDoms]
    rw [hA.scope, hbo, hbs]
    have hB := runBinds_qset hK hD s Q β β' hA hR (.fix self hs ds c dec body) hV (K.D.paramDecls (scopeOf s) ds) ds [] []
      (BAgree.refl 0 []) (fun x hx => by simp at hx; simp [Term.placeOccs, hx])
    have hlen := runBinds_length K ρ φ s (K.D.paramDecls (scopeOf s) ds) ds []
    have hpsl : (psOf (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) ds).length = ds.length :=
      psOf_length _ _ hlen
    have hext : ∀ acc, extendBy (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) acc =
        qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) := fun acc => by
      rw [← extendBy_agree hB, qset_extendBy s hA.twin.pre.pos]
    have hc0 : ∀ x ∈ c.placeOccs ds.length, x ∈ (Term.fix self hs ds c dec body).placeOccs 0 := fun x hx => by
      simp [Term.placeOccs, hx]
    have hcodIH : ∀ u : Term, (∀ x ∈ u.placeOccs ds.length, x ∈ (Term.fix self hs ds c dec body).placeOccs 0) →
        (∀ acc : List Sem, acc.length = ds.length →
          runT K ρ φ false (.plain TyM.err) u (qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) =
          qmap Q β' (runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc))) →
        ∀ acc : List Sem, acc.length = ds.length →
          (match runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
            | some ((v, _), _) => v.asTy
            | none => TyM.err) =
          (match runT K ρ φ false (.plain TyM.err) u (extendBy (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) acc) with
            | some ((v, _), _) => v.asTy
            | none => TyM.err) := by
      intro u _ hu acc ha
      rw [hext, hu acc ha]
      cases runT K ρ φ false (.plain TyM.err) u (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc) <;> rfl
    have hco : CodAgree ds.length (codOf K ρ φ s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) c)
        (codOf K ρ φ (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) c) := by
      have hcIH : ∀ acc : List Sem, acc.length = ds.length →
          runT K ρ φ false (.plain TyM.err) c (qset Q β' (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) =
            qmap Q β' (runT K ρ φ false (.plain TyM.err) c (extendBy s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) acc)) :=
        fun acc ha => runT_qset hK hD false c _ _ Q β β' (hA.extend _ acc)
          (hV.extend hc0 hA.twin.pre.pos _ ha) (rinv_extendBy hR _ acc)
      cases c
      case ref U =>
        have hU0 : ∀ x ∈ U.placeOccs ds.length, x ∈ (Term.fix self hs ds (.ref U) dec body).placeOccs 0 := fun x hx =>
          hc0 x (by simpa [Term.placeOccs] using hx)
        exact ⟨rfl, fun acc ha => hcodIH U hU0 (fun acc ha => runT_qset hK hD false U _ _ Q β β' (hA.extend _ acc)
          (hV.extend hU0 hA.twin.pre.pos _ ha) (rinv_extendBy hR _ acc)) acc ha⟩
      all_goals exact ⟨rfl, fun acc ha => hcodIH _ hc0 hcIH acc ha⟩
    have hsubB : ∀ x ∈ body.placeOccs (ds.length + 1), x ∈ (Term.fix self hs ds c dec body).placeOccs 0 :=
      fun x hx => by simp [Term.placeOccs, hx]
    have hbIH : ∀ (hint : TyS) (X : SState) (Q₁ : Pos → Prop) (β₁ β₁' : Pos → SBinding), Adm K Q₁ β₁ β₁' X →
        VarsAvoid Q₁ X body → RInv (fun _ => True) X → Comm Q₁ β₁' (runT K ρ φ true hint body) X :=
      fun hint X Q₁ β₁ β₁' hA₁ hV₁ hR₁ => runT_qset hK hD true body hint X Q₁ β₁ β₁' hA₁ hV₁ hR₁
    have hps := psOf_agree hB ds
    have hpl' : (psOf (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) ds).length = ds.length := hpsl
    have hco' := hco; rw [← hpl'] at hco'
    rw [← piTyAt_congr K.dm.read (K.D.piSort (scopeOf s) (Term.pi hs ds c)) _ _ _ _ hps hco']
    have hg : ∀ (piT : TyM) (args : List Sem),
        args.length = (psOf (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) ds).length →
        fixG K ρ φ (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds,
            fixCod K ρ φ s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) c,
            K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
          (K.D.piSort (scopeOf s) (Term.pi hs ds c)) s
          (psOf (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) ds)
          (codOf K ρ φ s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) c) piT s.nextLoan dec body args =
        fixG K ρ φ (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds,
            fixCod K ρ φ (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) c,
            K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c)
          (K.D.piSort (scopeOf s) (Term.pi hs ds c)) (qset Q β' s)
          (psOf (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) ds)
          (codOf K ρ φ (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) c)
          piT (qset Q β' s).nextLoan dec body args := by
      intro piT args ha
      unfold fixG
      exact (fixStage_qset K ρ φ hK hA hR hV ds.length hsubB hbIH
        (fb := (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds,
            fixCod K ρ φ s (runBinds K ρ φ s (K.D.paramDecls (scopeOf s) ds) [] ds) c,
            K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c))
        (fb' := (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds,
            fixCod K ρ φ (qset Q β' s) (runBinds K ρ φ (qset Q β' s) (K.D.paramDecls (scopeOf s) ds) [] ds) c,
            K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c))
        hB rfl hps hpl' hco (fixCod_agree K ρ φ hco) _ dec _ args (by rw [ha, hpl'])).symm
    rw [← closureAt_congr' K.dm.read _ φ _ _ _ _ _ _ hps hco' (hg _)]
    refine erasedIf_qset₂ ?_
    obtain ⟨hok, hmv⟩ := caps_qset K φ hA hV (T := Term.fix self hs ds c dec body)
    simp only [fixMoves]
    by_cases h : FoldOk (capStep K) (CapOk K φ) (capOrder (Term.fix self hs ds c dec body)) s
    · rw [if_pos (hok.2 h), if_pos h, hmv]
      exact comm_strictS (comm_pure _ _)
    · rw [if_neg (fun h' => h (hok.1 h')), if_neg h]; rfl

theorem runArm_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) :
    ∀ (tl : Bool) (hint : TyS) (c : Nat) (arms : List (Hint × Term)) (s : SState) (Q : Pos → Prop)
      (β β' : Pos → SBinding), Adm K Q β β' s → (∀ a ∈ arms, VarsAvoid Q s a.2) → RInv (fun _ => True) s →
      Comm Q β' (runArm K ρ φ tl hint c arms) s
  | _, _, _, [], _, _, _, _, _, _, _ => by unfold Comm; rw [runArm]; rfl
  | tl, hint, c, (h, t) :: rest, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runArm]
    by_cases hc : c = 0
    · simp only [hc, if_true]
      exact runT_qset hK hD tl t hint s Q β β' hA (hV (h, t) (by simp)) hR
    · simp only [hc, if_false]
      exact runArm_qset hK hD tl hint (c - 1) rest s Q β β' hA (fun a ha => hV a (by simp [ha])) hR

theorem runFields_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) (stmt : Bool) (d : IndDecl)
    (c : Nat) : ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem)
      (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding), Adm K Q β β' s → (∀ a ∈ args, VarsAvoid Q s a) →
      RInv (fun _ => True) s → Comm Q β' (runFields K ρ φ stmt d c i rh sol earlier args) s
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | a :: as, i, rh, sol, earlier, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runFields.eq_def]; dsimp only; rw [hA.scope]
    have ha := hV a (by simp)
    refine comm_bind (comm_stmtIf (runT_qset hK hD false a _ s Q β β' hA ha hR)) fun x s₁ h1 => ?_
    obtain ⟨hA₁, hR₁, e₁⟩ := Adm.afterStmt K ρ φ hK hA hR h1 (comm_stmtIf (runT_qset hK hD false a _ s Q β β hA.self ha hR))
    obtain ⟨v, R⟩ := x
    dsimp only
    exact comm_bind (runFields_qset hK hD stmt d c as (i + 1) rh _ (earlier ++ [v]) s₁ Q β β' hA₁
      (fun b hb => (hV b (by simp [hb])).of_envLe e₁) hR₁) fun _ _ _ => comm_pure _ _

theorem runArgs_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → (∀ a ∈ args, VarsAvoid Q s a) → RInv (fun _ => True) s →
      Comm Q β' (runArgs K ρ φ stmt fT earlier args) s
  | [], _, _, _, _, _, _, _, _ => rfl
  | a :: as, earlier, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runArgs.eq_def]; dsimp only; rw [hA.scope]
    have ha := hV a (by simp)
    refine comm_bind (comm_stmtIf (runT_qset hK hD false a _ s Q β β' hA ha hR)) fun x s₁ h1 => ?_
    obtain ⟨hA₁, hR₁, e₁⟩ := Adm.afterStmt K ρ φ hK hA hR h1 (comm_stmtIf (runT_qset hK hD false a _ s Q β β hA.self ha hR))
    exact comm_bind (runArgs_qset hK hD stmt fT as (earlier ++ [x.1]) s₁ Q β β' hA₁
      (fun b hb => (hV b (by simp [hb])).of_envLe e₁) hR₁) fun _ _ _ => comm_pure _ _

theorem runAll_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) :
    ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (tl : Bool) (hint : TyS) (s : SState) (Q : Pos → Prop)
      (β β' : Pos → SBinding), Adm K Q β β' s → VarsAvoid Q s t → RInv (fun _ => True) s →
      Comm Q β' (runT K ρ φ tl hint t) s
  | [], t, ht, _, _, _, _, _, _, _, _, _ => absurd ht List.not_mem_nil
  | a :: as, t, ht, tl, hint, s, Q, β, β', hA, hV, hR => by
    rcases List.mem_cons.mp ht with e | ht'
    · rw [e]; exact runT_qset hK hD tl a hint s Q β β' hA (e ▸ hV) hR
    · exact runAll_qset hK hD as t ht' tl hint s Q β β' hA hV hR

theorem runBinds_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D) (s : SState) (Q : Pos → Prop)
    (β β' : Pos → SBinding) (hA : Adm K Q β β' s) (hR : RInv (fun _ => True) s) (T : Term) (hV : VarsAvoid Q s T)
    (dcs : List DeclInfo) : ∀ (ds : List Term) (pre pre' : List PBind), BAgree 0 pre pre' →
      (∀ x ∈ Term.placeOccsDoms pre.length ds, x ∈ T.placeOccs 0) →
      BAgree pre.length (runBinds K ρ φ s dcs pre ds) (runBinds K ρ φ (qset Q β' s) dcs pre' ds)
  | [], pre, pre', _, _ => by simp only [runBinds]; exact BAgree.refl _ _
  | d :: ds, pre, pre', hp, hsub => by
    have hsubd : ∀ x ∈ d.placeOccs pre.length, x ∈ T.placeOccs 0 := fun x hx =>
      hsub x (by simp [Term.placeOccsDoms, hx])
    have key : ∀ u : Term, (∀ acc : List Sem, acc.length = pre.length →
        runT K ρ φ false (.plain TyM.err) u (qset Q β' (extendBy s pre acc)) =
          qmap Q β' (runT K ρ φ false (.plain TyM.err) u (extendBy s pre acc))) →
        BAgree pre.length
          (mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy s pre acc)) ::
            runBinds K ρ φ s dcs (pre ++ [mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) u
              (extendBy s pre acc))]) ds)
          (mkBind dcs pre' (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy (qset Q β' s) pre' acc)) ::
            runBinds K ρ φ (qset Q β' s) dcs (pre' ++ [mkBind dcs pre' (fun acc => runT K ρ φ false (.plain TyM.err) u
              (extendBy (qset Q β' s) pre' acc))]) ds) := by
      intro u hu
      have he : (mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy s pre acc))).2 =
          (mkBind dcs pre' (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy (qset Q β' s) pre' acc))).2 := by
        simp only [mkBind, hp.1]
      have hb : ∀ acc : List Sem, acc.length = pre.length →
          (mkBind dcs pre (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy s pre acc))).1 acc =
            (mkBind dcs pre' (fun acc => runT K ρ φ false (.plain TyM.err) u (extendBy (qset Q β' s) pre' acc))).1 acc := by
        intro acc ha
        simp only [mkBind]
        rw [← extendBy_agree hp, qset_extendBy s hA.twin.pre.pos, hu acc ha]
        cases runT K ρ φ false (.plain TyM.err) u (extendBy s pre acc) <;> rfl
      refine BAgree.cons he hb ?_
      have := runBinds_qset hK hD s Q β β' hA hR T hV dcs ds _ _ (hp.snoc he fun acc ha => hb acc (by simpa using ha))
        (fun x hx => hsub x (by simp only [Term.placeOccsDoms, List.mem_append]; right; simpa using hx))
      simpa using this
    have hd : ∀ acc : List Sem, acc.length = pre.length →
        runT K ρ φ false (.plain TyM.err) d (qset Q β' (extendBy s pre acc)) =
          qmap Q β' (runT K ρ φ false (.plain TyM.err) d (extendBy s pre acc)) := fun acc ha =>
      runT_qset hK hD false d _ _ Q β β' (hA.extend pre acc)
        (hV.extend hsubd hA.twin.pre.pos pre ha) (rinv_extendBy hR pre acc)
    cases d
    case ref A =>
      have hA' : ∀ acc : List Sem, acc.length = pre.length →
          runT K ρ φ false (.plain TyM.err) A (qset Q β' (extendBy s pre acc)) =
            qmap Q β' (runT K ρ φ false (.plain TyM.err) A (extendBy s pre acc)) := fun acc ha =>
        runT_qset hK hD false A _ _ Q β β' (hA.extend pre acc)
          (hV.extend (fun x hx => hsubd x (by simpa [Term.placeOccs] using hx)) hA.twin.pre.pos pre ha)
          (rinv_extendBy hR pre acc)
      rw [runBinds_cons, runBinds_cons]; exact key A hA'
    all_goals (rw [runBinds_cons, runBinds_cons]; exact key _ hd)

theorem runParams_qset (hK : ∀ n, (K.C.global n).2.label = none) (hD : DecLocal K.D)
    (d : IndDecl) :
    ∀ (as : List Term) (i : Nat) (earlier : List Sem) (s : SState) (Q : Pos → Prop) (β β' : Pos → SBinding),
      Adm K Q β β' s → (∀ a ∈ as, VarsAvoid Q s a) → RInv (fun _ => True) s →
      Comm Q β' (runParams K ρ φ d i earlier as) s
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, Q, β, β', hA, hV, hR => by
    unfold Comm; rw [runParams]
    refine comm_bind (comm_onCopy (runT_qset hK hD false a _ s Q β β' hA (hV a (by simp)) hR)) fun x s₁ h1 => ?_
    have e₁ := SM.onCopy_state h1; subst e₁
    obtain ⟨v, _⟩ := x
    dsimp only
    exact comm_bind (runParams_qset hK hD d as (i + 1) (earlier ++ [v]) s₁ Q β β' hA
      (fun b hb => hV b (by simp [hb])) hR) fun _ _ _ => comm_pure _ _
end

end

end Ochr.Meaning.DataModel.Exists.FrameLocal
