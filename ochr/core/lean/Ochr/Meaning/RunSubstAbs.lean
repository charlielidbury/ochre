import Ochr.Meaning.SubstAbs
import Ochr.Meaning.RunSubst

/-!
# The substitution lemma for unknowns, proved (docs/31 D77; `SubstAbs.lean`)

`RunSubst.lean`'s same-meaning substitution with the atom `.abs σ` in place of `.loan ℓ`: under an
assignment at which the filler means the unknown (`AbsFillOK`), the run of `t[σ := w]` is the run of
`t`, and a value's meaning is kept, clause by clause. The induction never looks at which atom it
replaces but in its base cases (the `.val` clause's type, `AbsFillOK.shape`; the meaning of the atom,
`AbsFillOK.mean`). This file is `RunSubst.lean`'s sections `Syntax` to `SubstMut` with the atom
renamed; the two base cases are the only proofs that differ.
-/

namespace Ochr.Meaning

open SState

/-! ## The substitution keeps every place occurrence -/

section SyntaxAbs
variable (σ : Nat) (w : Value)

mutual
theorem placeOccs_substAbs : ∀ (t : Term) (c : Nat), (Term.substAbs σ w t).placeOccs c = t.placeOccs c
  | t, c => by
    cases t with
    | assign p u => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs u]
    | letIn h u v => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs u, placeOccs_substAbs v]
    | seq u v => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs u, placeOccs_substAbs v]
    | matchNat p z s => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs z, placeOccs_substAbs s]
    | pi hs ds cod =>
      simp only [Term.substAbs, Term.placeOccs, placeOccsDoms_substAbs ds, placeOccs_substAbs cod,
        length_substAbsList ds]
    | fix f hs ds cod d b =>
      simp only [Term.substAbs, Term.placeOccs, placeOccsDoms_substAbs ds, placeOccs_substAbs cod,
        placeOccs_substAbs b, length_substAbsList ds]
    | call g as h => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs g, placeOccsList_substAbs as]
    | succ u => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs u]
    | ref u => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs u]
    | cong a b => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs a, placeOccs_substAbs b]
    | ascribe a b => simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs a, placeOccs_substAbs b]
    | eq a b d =>
      simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs a, placeOccs_substAbs b, placeOccs_substAbs d]
    | id a b d =>
      simp only [Term.substAbs, Term.placeOccs, placeOccs_substAbs a, placeOccs_substAbs b, placeOccs_substAbs d]
    | ctor ty k h ps as =>
      simp only [Term.substAbs, Term.placeOccs, placeOccsList_substAbs ps, placeOccsList_substAbs as]
    | prim n as => simp only [Term.substAbs, Term.placeOccs, placeOccsList_substAbs as]
    | tind n as => simp only [Term.substAbs, Term.placeOccs, placeOccsList_substAbs as]
    | matchInd p ty as => simp only [Term.substAbs, Term.placeOccs, placeOccsArms_substAbs as]
    | _ => simp [Term.substAbs, Term.placeOccs]

theorem placeOccsList_substAbs : ∀ (ts : List Term) (c : Nat),
    Term.placeOccsList c (Term.substAbsList σ w ts) = Term.placeOccsList c ts
  | [], _ => rfl
  | t :: ts, c => by
    simp only [Term.substAbsList, Term.placeOccsList, placeOccs_substAbs t, placeOccsList_substAbs ts]

theorem placeOccsDoms_substAbs : ∀ (ts : List Term) (c : Nat),
    Term.placeOccsDoms c (Term.substAbsList σ w ts) = Term.placeOccsDoms c ts
  | [], _ => rfl
  | t :: ts, c => by
    simp only [Term.substAbsList, Term.placeOccsDoms, placeOccs_substAbs t, placeOccsDoms_substAbs ts]

theorem placeOccsArms_substAbs : ∀ (ts : List (Hint × Term)) (c : Nat),
    Term.placeOccsArms c (Term.substAbsArms σ w ts) = Term.placeOccsArms c ts
  | [], _ => rfl
  | (h, t) :: ts, c => by
    simp only [Term.substAbsArms, Term.placeOccsArms, placeOccs_substAbs t, placeOccsArms_substAbs ts]

theorem length_substAbsList : ∀ ts : List Term, (Term.substAbsList σ w ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp only [Term.substAbsList, List.length_cons, length_substAbsList ts]
end

theorem freeVars_substAbs (t : Term) : (Term.substAbs σ w t).freeVars = t.freeVars := by
  simp only [Term.freeVars, Term.freeOccs, placeOccs_substAbs]

end SyntaxAbs

/-! ## Support: the pieces that read the term -/

section SubstAbsSame
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (σ : Nat) (w : Value) {fb : List PBind × PBind}

/-- The decisions do not see the fill in a telescope's readings (D19, R3). -/
theorem teleDecls_substAbs (hD : DecInvariantAbs K.D σ w) : ∀ (ds : List Term) (sc : List DeclInfo),
    K.D.teleDecls sc (Term.substAbsList σ w ds) = K.D.teleDecls sc ds
  | [], _ => rfl
  | d :: ds, sc => by
    simp only [Term.substAbsList, Decisions.teleDecls, hD.2.2.2.2.2.1, teleDecls_substAbs hD ds]

theorem paramDecls_substAbs (hD : DecInvariantAbs K.D σ w) (sc : List DeclInfo) (ds : List Term) :
    K.D.paramDecls sc (Term.substAbsList σ w ds) = K.D.paramDecls sc ds := by
  simp only [Decisions.paramDecls, teleDecls_substAbs K σ w hD, length_substAbsList]

theorem fixDecls_substAbs (hD : DecInvariantAbs K.D σ w) (sc : List DeclInfo) (ds : List Term) (c : Term) :
    K.D.fixDecls sc (Term.substAbsList σ w ds) (Term.substAbs σ w c) = K.D.fixDecls sc ds c := by
  simp only [Decisions.fixDecls, paramDecls_substAbs K σ w hD, teleDecls_substAbs K σ w hD, hD.2.2.2.2.2.1]

/-- Substituting for an unknown keeps which parameters are borrows: `&A` stays `&A`, and nothing else becomes one. -/
theorem psOf_substAbs : ∀ (bs : List PBind) (ds : List Term), psOf bs (Term.substAbsList σ w ds) = psOf bs ds
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, d :: ds => by
    have hd : (Term.substAbs σ w d).isRefTy = d.isRefTy := by cases d <;> rfl
    simp only [Term.substAbsList, psOf, hd, psOf_substAbs bs ds]

theorem joinDrop_substAbs (hD : DecInvariantAbs K.D σ w) (φ : Future) (t : Term) (entry : List Place) (s : SState) :
    joinDrop K φ entry (Term.substAbs σ w t) s = joinDrop K φ entry t s := by
  unfold joinDrop; rw [hD.2.2.2.1]

theorem matchEntry_substAbs (hD : DecInvariantAbs K.D σ w) (φ : Future) (ent : Bool) (t : Term) (s : SState) :
    matchEntry K φ ent (Term.substAbs σ w t) s = matchEntry K φ ent t s := by
  unfold matchEntry; simp only [hD.2.2.2.2.2.2, hD.2.1]

theorem fixMoves_substAbs (t : Term) (s : SState) : fixMoves K (Term.substAbs σ w t) s = fixMoves K t s := by
  unfold fixMoves capOrder; rw [freeVars_substAbs]

theorem substAbs_isPlace (u : Term) : (∃ p, Term.substAbs σ w u = .place p) ↔ ∃ p, u = .place p := by
  cases u <;> simp [Term.substAbs]

end SubstAbsSame

section SubstAbsSame2
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (σ : Nat) (w : Value)

theorem substAbs_not_ref {c : Term} (h : ∀ U, c ≠ .ref U) : ∀ U, Term.substAbs σ w c ≠ .ref U := by
  intro U e
  cases c with
  | ref V => exact h V rfl
  | _ => simp [Term.substAbs] at e

theorem codOf_substAbs_of {c : Term} (hc : ∀ hint, run K ρ ψ hint (Term.substAbs σ w c) = run K ρ ψ hint c)
    (hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substAbs σ w U) = run K ρ ψ hint U) (s : SState)
    (bs : List PBind) :
    codOf K ρ ψ s bs (Term.substAbs σ w c) = codOf K ρ ψ s bs c := by
  by_cases h : ∃ U, c = .ref U
  · obtain ⟨U, rfl⟩ := h
    simp only [Term.substAbs, codOf, hU U rfl]
  · have h' : ∀ U, c ≠ .ref U := fun U e => h ⟨U, e⟩
    rw [codOf_data K ρ ψ (substAbs_not_ref σ w h') s bs, codOf_data K ρ ψ h' s bs]
    simp only [hc]

theorem fixCod_substAbs_of {c : Term} (hc : ∀ hint, run K ρ ψ hint (Term.substAbs σ w c) = run K ρ ψ hint c)
    (hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substAbs σ w U) = run K ρ ψ hint U) (s : SState)
    (bs : List PBind) :
    fixCod K ρ ψ s bs (Term.substAbs σ w c) = fixCod K ρ ψ s bs c := by
  unfold fixCod; rw [codOf_substAbs_of K ρ ψ σ w hc hU]

end SubstAbsSame2

section SubstAbsPrim
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (σ : Nat) (w : Value)

theorem Term.substAbsList_isEmpty (ts : List Term) : (Term.substAbsList σ w ts).isEmpty = ts.isEmpty := by
  cases ts <;> rfl

theorem Value.substAbsList_isEmpty (vs : List Value) : (Value.substAbsList σ w vs).isEmpty = vs.isEmpty := by
  cases vs <;> rfl

theorem length_substAbsArms : ∀ ts : List (Hint × Term), (Term.substAbsArms σ w ts).length = ts.length
  | [] => rfl
  | (_, _) :: ts => by simp only [Term.substAbsArms, List.length_cons, length_substAbsArms ts]

theorem headOf_substAbs (u : Term) (rd : Place → SM (Sem × TyS)) (rn : SM (Sem × TyS)) :
    SM.headOf (Term.substAbs σ w u) rd rn = SM.headOf u rd rn := by
  cases u <;> rfl

theorem run_prim_substAbsSame (hD : DecInvariantAbs K.D σ w) (tl : Bool) (n : String) (args : List Term) (hint : TyS)
    (hfl : ∀ sc, K.D.flags sc (Term.substAbs σ w (.prim n args)) = K.D.flags sc (.prim n args))
    (hall : ∀ t ∈ args, ∀ hint, run K ρ ψ hint (Term.substAbs σ w t) = run K ρ ψ hint t) :
    runT K ρ ψ tl hint (Term.substAbs σ w (.prim n args)) = runT K ρ ψ tl hint (.prim n args) := by
  show runT K ρ ψ tl hint (.prim n (Term.substAbsList σ w args)) = _
  have hfl' : ∀ sc, K.D.flags sc (.prim n (Term.substAbsList σ w args)) = K.D.flags sc (.prim n args) := hfl
  funext s
  have hlen := length_substAbsList σ w args
  by_cases e1 : ∃ h, n = "symm" ∧ args = [h]
  · obtain ⟨h0, rfl, rfl⟩ := e1
    simp only [Term.substAbsList]
    rw [runT, runT]; simp only [hall h0 (by simp)]
  by_cases e2 : ∃ h k, n = "trans" ∧ args = [h, k]
  · obtain ⟨h0, k0, rfl, rfl⟩ := e2
    simp only [Term.substAbsList]
    rw [runT, runT]; simp only [hall h0 (by simp), hall k0 (by simp)]
  by_cases e3 : ∃ h u, n = "rewrite" ∧ args = [h, u]
  · obtain ⟨h0, u0, rfl, rfl⟩ := e3
    simp only [Term.substAbsList]
    rw [runT, runT]; simp only [hall h0 (by simp), hall u0 (by simp)]
  by_cases e4 : ∃ h u, n = "rewriteR" ∧ args = [h, u]
  · obtain ⟨h0, u0, rfl, rfl⟩ := e4
    simp only [Term.substAbsList]
    rw [runT, runT]; simp only [hall h0 (by simp), hall u0 (by simp)]
  by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
  · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ
    simp only [Term.substAbsList] at hfl' ⊢
    have hme : ∀ s, matchEntry K ψ true (Term.substAbs σ w t) s = matchEntry K ψ true t s :=
      matchEntry_substAbs K σ w hD ψ true t
    have hj : ∀ e s, joinDrop K ψ e (.prim "J" [Term.substAbs σ w A, Term.substAbs σ w a, Term.substAbs σ w b,
        Term.substAbs σ w P, Term.substAbs σ w h', Term.substAbs σ w t]) s = joinDrop K ψ e (.prim "J" [A, a, b, P, h', t]) s :=
      joinDrop_substAbs K σ w hD ψ (.prim "J" [A, a, b, P, h', t])
    rw [runT, runT]
    simp only [hfl', hall A (by simp), hall a (by simp), hall b (by simp),
      hall P (by simp), hall h' (by simp), hall t (by simp), hme, hj]
  by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
  · obtain ⟨u, hn, rfl⟩ := hc
    simp only [Term.substAbsList] at hfl' ⊢
    rcases hn with rfl | rfl | rfl <;>
      (rw [runT, runT]; simp only [hfl', hall u (by simp), headOf_substAbs])
  have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
    fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
  have hJs : ∀ (A a b P h t : Term), n = "J" → Term.substAbsList σ w args = [A, a, b, P, h, t] → False := by
    intro A a b P h t e1 e2
    have : args.length = 6 := by rw [← hlen, e2]; rfl
    obtain ⟨x1, x2, x3, x4, x5, x6, hx⟩ := list_six args this
    exact hJ' x1 x2 x3 x4 x5 x6 e1 hx
  have hcs : ∀ m, (m = "clone" ∨ m = "peek" ∨ m = "inplace") → (∀ u, n = m → args = [u] → False) ∧
      (∀ u, n = m → Term.substAbsList σ w args = [u] → False) := by
    intro m hm
    refine ⟨fun u e1 e2 => hc ⟨u, e1 ▸ hm, e2⟩, fun u e1 e2 => ?_⟩
    have : args.length = 1 := by rw [← hlen, e2]; rfl
    obtain ⟨x, hx⟩ := list_one args this
    exact hc ⟨x, e1 ▸ hm, hx⟩
  have f1 : ∀ h, n = "symm" → args = [h] → False := fun h0 a b => e1 ⟨h0, a, b⟩
  have f2 : ∀ h k, n = "trans" → args = [h, k] → False := fun h0 k0 a b => e2 ⟨h0, k0, a, b⟩
  have f3 : ∀ h u, n = "rewrite" → args = [h, u] → False := fun h0 u0 a b => e3 ⟨h0, u0, a, b⟩
  have f4 : ∀ h u, n = "rewriteR" → args = [h, u] → False := fun h0 u0 a b => e4 ⟨h0, u0, a, b⟩
  have g1 : ∀ h, n = "symm" → Term.substAbsList σ w args = [h] → False := fun h0 a b => by
    obtain ⟨x, hx⟩ := list_one args (by rw [← hlen, b]; rfl); exact e1 ⟨x, a, hx⟩
  have g2 : ∀ h k, n = "trans" → Term.substAbsList σ w args = [h, k] → False := fun h0 k0 a b => by
    obtain ⟨x, y, hx⟩ := list_two args (by rw [← hlen, b]; rfl); exact e2 ⟨x, y, a, hx⟩
  have g3 : ∀ h u, n = "rewrite" → Term.substAbsList σ w args = [h, u] → False := fun h0 u0 a b => by
    obtain ⟨x, y, hx⟩ := list_two args (by rw [← hlen, b]; rfl); exact e3 ⟨x, y, a, hx⟩
  have g4 : ∀ h u, n = "rewriteR" → Term.substAbsList σ w args = [h, u] → False := fun h0 u0 a b => by
    obtain ⟨x, y, hx⟩ := list_two args (by rw [← hlen, b]; rfl); exact e4 ⟨x, y, a, hx⟩
  rw [runT, runT]
  all_goals (first | rfl | exact f1 | exact f2 | exact f3 | exact f4 | exact hJ' | exact (hcs _ (.inl rfl)).1 | exact (hcs _ (.inr (.inl rfl))).1 | exact (hcs _ (.inr (.inr rfl))).1 | exact g1 | exact g2 | exact g3 | exact g4 | exact hJs | exact (hcs _ (.inl rfl)).2 | exact (hcs _ (.inr (.inl rfl))).2 | exact (hcs _ (.inr (.inr rfl))).2)

end SubstAbsPrim

section SubstAbsMut
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (σ : Nat) (w : Value)

mutual
/-- **Replacing an unknown by what it means keeps the run**: where the filler means the unknown
(`AbsFillOK`), the run of the substituted term is the run of the term. -/
theorem runT_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (tl : Bool) (t : Term) (hint : TyS),
    runT K ρ ψ tl hint (Term.substAbs σ w t) = runT K ρ ψ tl hint t
  | tl, t, hint => by
    cases t with
    | val v =>
      funext s
      show runT K ρ ψ tl hint (.val (Value.substAbs σ w v)) s = _
      rw [runT_val_def, runT_val_def, meanV_substAbsSame hF v hint]
      cases v with
      | abs σ' =>
        by_cases e : σ' = σ
        · subst e
          -- the filler's strict `.val` succeeds where the unknown's does (`AbsFillOK.shape`
          -- compares the two runs, success included), at the same type, with the same meaning
          have h := hF.shape hint s
          rw [run_val_def, run_val_def] at h
          simp only [Value.substAbs, if_true]
          have hR : strictVal K.dm.read (Value.abs σ') (meanV K ρ ψ hint (Value.abs σ'),
              { valT K ρ ψ hint (Value.abs σ') with label := none }) s =
              some ((meanV K ρ ψ hint (Value.abs σ'), { valT K ρ ψ hint (Value.abs σ') with label := none }), s) := rfl
          rw [hR]; rw [hR] at h
          have hm : meanV K ρ ψ hint w = meanV K ρ ψ hint (Value.abs σ') := hF.mean hint
          rw [hm] at h
          cases hw : strictVal K.dm.read w (meanV K ρ ψ hint (Value.abs σ'), { valT K ρ ψ hint w with label := none }) s with
          | none => rw [hw] at h; cases h
          | some x =>
            obtain ⟨r, s'⟩ := x
            rw [hw] at h
            obtain ⟨rfl, rfl⟩ := strictVal_some hw
            simp only [Option.map_some, Option.some.injEq] at h
            rw [h]
        · simp only [Value.substAbs, e, if_false]
      | clo caps t rd =>
        simp only [Value.substAbs, valT, strictVal, capsVals_substAbsSame hF caps, capsTys_substAbsSame hF rd,
          runT_substAbsSame hF false t]
      | sealed t =>
        simp only [Value.substAbs, valT, strictVal, runT_substAbsSame hF false t hint]
      | ind ty c h ps fs =>
        simp only [Value.substAbs, valT, strictVal, meanParams_substAbsSame hF, Value.substAbsList_isEmpty]
      | _ => rfl
    | assign p u =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      funext s
      show runT K ρ ψ tl hint (.assign p (Term.substAbs σ w u)) s = _
      have hfl : ∀ sc, K.D.flags sc (.assign p (Term.substAbs σ w u)) = K.D.flags sc (.assign p u) :=
        fun sc => hF.dec.1 sc (.assign p u)
      rw [runT, runT]; simp only [hu, hfl]
    | letIn h u v =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      have hv := fun tl' => runT_substAbsSame hF tl' v
      funext s
      show runT K ρ ψ tl hint (.letIn h (Term.substAbs σ w u) (Term.substAbs σ w v)) s = _
      have hfl : ∀ sc, K.D.flags sc (.letIn h (Term.substAbs σ w u) (Term.substAbs σ w v)) = K.D.flags sc (.letIn h u v) :=
        fun sc => hF.dec.1 sc (.letIn h u v)
      rw [runT, runT]; simp only [hu, hv, hF.dec.2.1, hfl]
    | seq u v =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      have hv := fun tl' => runT_substAbsSame hF tl' v
      show runT K ρ ψ tl hint (.seq (Term.substAbs σ w u) (Term.substAbs σ w v)) = _
      have hfl : ∀ sc, K.D.flags sc (.seq (Term.substAbs σ w u) (Term.substAbs σ w v)) = K.D.flags sc (.seq u v) :=
        fun sc => hF.dec.1 sc (.seq u v)
      rw [runT, runT]; simp only [hu, hv, hfl]
    | matchNat p z u =>
      have hz := fun tl' => runT_substAbsSame hF tl' z
      have hu := fun tl' => runT_substAbsSame hF tl' u
      have hj : ∀ e s, joinDrop K ψ e (.matchNat p (Term.substAbs σ w z) (Term.substAbs σ w u)) s
          = joinDrop K ψ e (.matchNat p z u) s := joinDrop_substAbs K σ w hF.dec ψ (.matchNat p z u)
      have hme : ∀ e s, matchEntry K ψ e (.matchNat p (Term.substAbs σ w z) (Term.substAbs σ w u)) s
          = matchEntry K ψ e (.matchNat p z u) s := fun e => matchEntry_substAbs K σ w hF.dec ψ e (.matchNat p z u)
      funext s
      show runT K ρ ψ tl hint (.matchNat p (Term.substAbs σ w z) (Term.substAbs σ w u)) s = _
      have hfl : ∀ sc, K.D.flags sc (.matchNat p (Term.substAbs σ w z) (Term.substAbs σ w u)) = K.D.flags sc (.matchNat p z u) :=
        fun sc => hF.dec.1 sc (.matchNat p z u)
      rw [runT, runT]; simp only [hz, hu, hj, hfl, hme]
    | matchInd p n arms =>
      have ha := fun tl' => runArm_substAbsSame hF tl' arms
      have hj : ∀ e s, joinDrop K ψ e (.matchInd p n (Term.substAbsArms σ w arms)) s
          = joinDrop K ψ e (.matchInd p n arms) s := joinDrop_substAbs K σ w hF.dec ψ (.matchInd p n arms)
      have hme : ∀ e s, matchEntry K ψ e (.matchInd p n (Term.substAbsArms σ w arms)) s
          = matchEntry K ψ e (.matchInd p n arms) s := fun e => matchEntry_substAbs K σ w hF.dec ψ e (.matchInd p n arms)
      funext s
      show runT K ρ ψ tl hint (.matchInd p n (Term.substAbsArms σ w arms)) s = _
      have hfl : ∀ sc, K.D.flags sc (.matchInd p n (Term.substAbsArms σ w arms)) = K.D.flags sc (.matchInd p n arms) :=
        fun sc => hF.dec.1 sc (.matchInd p n arms)
      rw [runT, runT]; simp only [ha, hj, length_substAbsArms, hfl, hme]
    | succ u =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      show runT K ρ ψ tl hint (.succ (Term.substAbs σ w u)) = _
      have hfl : ∀ sc, K.D.flags sc (.succ (Term.substAbs σ w u)) = K.D.flags sc (.succ u) :=
        fun sc => hF.dec.1 sc (.succ u)
      rw [runT, runT]; simp only [hu, hfl]
    | ref u =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      show runT K ρ ψ tl hint (.ref (Term.substAbs σ w u)) = _
      have hfl : ∀ sc, K.D.flags sc (.ref (Term.substAbs σ w u)) = K.D.flags sc (.ref u) :=
        fun sc => hF.dec.1 sc (.ref u)
      rw [runT, runT]; simp only [hu, hfl]
    | cong a b =>
      have hb := fun tl' => runT_substAbsSame hF tl' b
      show runT K ρ ψ tl hint (.cong (Term.substAbs σ w a) (Term.substAbs σ w b)) = _
      rw [runT, runT]; simp only [hb]
    | ascribe u A =>
      have hu := fun tl' => runT_substAbsSame hF tl' u
      have hA := fun tl' => runT_substAbsSame hF tl' A
      show runT K ρ ψ tl hint (.ascribe (Term.substAbs σ w u) (Term.substAbs σ w A)) = _
      have hfl : ∀ sc, K.D.flags sc (.ascribe (Term.substAbs σ w u) (Term.substAbs σ w A)) = K.D.flags sc (.ascribe u A) :=
        fun sc => hF.dec.1 sc (.ascribe u A)
      rw [runT, runT]; simp only [hu, hA, hfl]
    | eq A a b =>
      have hA := fun tl' => runT_substAbsSame hF tl' A
      have ha := fun tl' => runT_substAbsSame hF tl' a
      have hb := fun tl' => runT_substAbsSame hF tl' b
      show runT K ρ ψ tl hint (.eq (Term.substAbs σ w A) (Term.substAbs σ w a) (Term.substAbs σ w b)) = _
      rw [runT, runT]; simp only [hA, ha, hb]
    | id A a b =>
      have hA := fun tl' => runT_substAbsSame hF tl' A
      have ha := fun tl' => runT_substAbsSame hF tl' a
      have hb := fun tl' => runT_substAbsSame hF tl' b
      funext s
      show runT K ρ ψ tl hint (.id (Term.substAbs σ w A) (Term.substAbs σ w a) (Term.substAbs σ w b)) s = _
      rw [runT, runT]; simp only [hA, ha, hb, hF.dec.2.2.2.2.1]
    | tind n args =>
      have hp := fun d => runParams_substAbsSame hF d args
      show runT K ρ ψ tl hint (.tind n (Term.substAbsList σ w args)) = _
      rw [runT, runT]; simp only [hp]
    | ctor ty c h ps args =>
      have hp := fun d => runParams_substAbsSame hF d ps
      have hf := fun st d => runFields_substAbsSame hF st d c args
      show runT K ρ ψ tl hint (.ctor ty c h (Term.substAbsList σ w ps) (Term.substAbsList σ w args)) = _
      have hfl : ∀ sc, K.D.flags sc (.ctor ty c h (Term.substAbsList σ w ps) (Term.substAbsList σ w args))
          = K.D.flags sc (.ctor ty c h ps args) := fun sc => hF.dec.1 sc (.ctor ty c h ps args)
      rw [runT, runT]; rw [Term.substAbsList_isEmpty]; simp only [hp, hf, hfl]
    | call f args hd =>
      have hf := fun tl' => runT_substAbsSame hF tl' f
      have ha := fun st sh => runArgs_substAbsSame hF st sh args
      have hfl : ∀ sc, K.D.flags sc (.call (Term.substAbs σ w f) (Term.substAbsList σ w args) hd)
          = K.D.flags sc (.call f args hd) := fun sc => hF.dec.1 sc (.call f args hd)
      funext s
      show runT K ρ ψ tl hint (.call (Term.substAbs σ w f) (Term.substAbsList σ w args) hd) s = _
      rw [runT, runT]; simp only [hf, ha, hfl, headOf_substAbs]
    | pi hs ds c =>
      have hc := fun tl' => runT_substAbsSame hF tl' c
      have hbs : ∀ s, bindsOf K ρ ψ s (Term.substAbsList σ w ds) = bindsOf K ρ ψ s ds := fun s => by
        unfold bindsOf; rw [paramDecls_substAbs K σ w hF.dec, runBinds_substAbsSame hF]
      have hds : ∀ s, runDoms K ρ ψ s (Term.substAbsList σ w ds) = runDoms K ρ ψ s ds := fun s => by
        unfold runDoms; rw [hbs, psOf_substAbs]
      have hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substAbs σ w U) = run K ρ ψ hint U := by
        cases c with
        | ref U => intro U' e hint; rw [show U' = U by injection e with e; exact e.symm]; exact runT_substAbsSame hF false U hint
        | _ => intro U' e; cases e
      have hps : ∀ sc, K.D.piSort sc (.pi hs (Term.substAbsList σ w ds) (Term.substAbs σ w c))
          = K.D.piSort sc (.pi hs ds c) := fun sc => hF.dec.2.2.1 sc (.pi hs ds c)
      funext s
      show runT K ρ ψ tl hint (.pi hs (Term.substAbsList σ w ds) (Term.substAbs σ w c)) s = _
      rw [run_pi_def, run_pi_def, hps, hds, hbs, codOf_substAbs_of K ρ ψ σ w (hc false) hU]
    | fix self hs ds c dec body =>
      have hc := fun tl' => runT_substAbsSame hF tl' c
      have hbs : ∀ s, bindsOf K ρ ψ s (Term.substAbsList σ w ds) = bindsOf K ρ ψ s ds := fun s => by
        unfold bindsOf; rw [paramDecls_substAbs K σ w hF.dec, runBinds_substAbsSame hF]
      have hds : ∀ s, runDoms K ρ ψ s (Term.substAbsList σ w ds) = runDoms K ρ ψ s ds := fun s => by
        unfold runDoms; rw [hbs, psOf_substAbs]
      have hb := fun tl' => runT_substAbsSame hF tl' body
      have hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substAbs σ w U) = run K ρ ψ hint U := by
        cases c with
        | ref U => intro U' e hint; rw [show U' = U by injection e with e; exact e.symm]; exact runT_substAbsSame hF false U hint
        | _ => intro U' e; cases e
      have hps : ∀ sc, K.D.piSort sc (.pi hs (Term.substAbsList σ w ds) (Term.substAbs σ w c))
          = K.D.piSort sc (.pi hs ds c) := fun sc => hF.dec.2.2.1 sc (.pi hs ds c)
      have hmv : ∀ s, fixMoves K (.fix self hs (Term.substAbsList σ w ds) (Term.substAbs σ w c) dec
          (Term.substAbs σ w body)) s = fixMoves K (.fix self hs ds c dec body) s :=
        fixMoves_substAbs K σ w (.fix self hs ds c dec body)
      funext s
      show runT K ρ ψ tl hint (.fix self hs (Term.substAbsList σ w ds) (Term.substAbs σ w c) dec
        (Term.substAbs σ w body)) s = _
      have hfl : ∀ sc, K.D.flags sc (.fix self hs (Term.substAbsList σ w ds) (Term.substAbs σ w c) dec
          (Term.substAbs σ w body)) = K.D.flags sc (.fix self hs ds c dec body) :=
        fun sc => hF.dec.1 sc (.fix self hs ds c dec body)
      rw [run_fix_def, run_fix_def, hfl, hps, hds, hbs, codOf_substAbs_of K ρ ψ σ w (hc false) hU, fixCod_substAbs_of K ρ ψ σ w (hc false) hU, hmv,
        teleDecls_substAbs K σ w hF.dec, hF.dec.2.2.2.2.2.1, fixG_bodyEq K ρ ψ (hb true)]
    | prim n args =>
      have hall : ∀ t ∈ args, ∀ hint, run K ρ ψ hint (Term.substAbs σ w t) = run K ρ ψ hint t :=
        fun t hm hint => runAll_substAbsSame hF args t hm hint
      exact run_prim_substAbsSame K ρ ψ σ w hF.dec tl n args hint (fun sc => hF.dec.1 sc (.prim n args)) hall
    | _ => rfl

theorem meanV_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (v : Value) (hint : TyS),
    meanV K ρ ψ hint (Value.substAbs σ w v) = meanV K ρ ψ hint v
  | v, hint => by
    cases v with
    | abs σ' =>
      by_cases e : σ' = σ
      · subst e; simp only [Value.substAbs, if_true]; rw [hF.mean hint]; rfl
      · simp only [Value.substAbs, e, if_false]
    | succ u =>
      show (meanV K ρ ψ _ (Value.substAbs σ w u)).succ = (meanV K ρ ψ _ u).succ
      rw [meanV_substAbsSame hF u]
    | borrow m u =>
      show meanV K ρ ψ hint (Value.substAbs σ w u) = meanV K ρ ψ hint u
      exact meanV_substAbsSame hF u hint
    | gloan m u =>
      show meanV K ρ ψ hint (Value.substAbs σ w u) = meanV K ρ ψ hint u
      exact meanV_substAbsSame hF u hint
    | tRef A =>
      show meanV K ρ ψ _ (Value.substAbs σ w A) = meanV K ρ ψ _ A
      exact meanV_substAbsSame hF A _
    | tEq A a b =>
      show meanV K ρ ψ hint (.tEq (Value.substAbs σ w A) (Value.substAbs σ w a) (Value.substAbs σ w b)) = _
      rw [meanV, meanV, meanV_substAbsSame hF A, meanV_substAbsSame hF a, meanV_substAbsSame hF b]
    | clo caps t rd =>
      show meanV K ρ ψ hint (.clo (Value.substAbsList σ w caps) (Term.substAbs σ w t) (Value.substAbsRd σ w rd)) = _
      rw [meanV, meanV, capsVals_substAbsSame hF caps, capsTys_substAbsSame hF rd, runT_substAbsSame hF false t]
    | tPi caps t rd =>
      show meanV K ρ ψ hint (.tPi (Value.substAbsList σ w caps) (Term.substAbs σ w t) (Value.substAbsRd σ w rd)) = _
      rw [meanV, meanV, capsVals_substAbsSame hF caps, capsTys_substAbsSame hF rd, runT_substAbsSame hF false t]
    | sealed t =>
      show meanV K ρ ψ hint (.sealed (Term.substAbs σ w t)) = _
      rw [meanV, meanV, runT_substAbsSame hF false t hint]
    | ind ty c h ps fs =>
      show meanV K ρ ψ hint (.ind ty c h (Value.substAbsList σ w ps) (Value.substAbsList σ w fs)) = _
      rw [meanV, meanV]
      simp only [meanParams_substAbsSame hF, meanFields_substAbsSame hF, Value.substAbsList_isEmpty]
    | tInd n args =>
      show meanV K ρ ψ hint (.tInd n (Value.substAbsList σ w args)) = _
      rw [meanV, meanV]
      simp only [meanParams_substAbsSame hF]
    | _ => rfl

theorem runAll_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (hint : TyS),
    run K ρ ψ hint (Term.substAbs σ w t) = run K ρ ψ hint t
  | [], t, h, _ => absurd h List.not_mem_nil
  | a :: as, t, h, hint => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e]; exact runT_substAbsSame hF false a hint
    · exact runAll_substAbsSame hF as t h hint

theorem runArm_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (tl : Bool) (arms : List (Hint × Term)) (hint : TyS) (c : Nat),
    runArm K ρ ψ tl hint c (Term.substAbsArms σ w arms) = runArm K ρ ψ tl hint c arms
  | _, [], _, _ => rfl
  | tl, (h, t) :: rest, hint, c => by
    simp only [Term.substAbsArms, runArm, runT_substAbsSame hF tl t, runArm_substAbsSame hF tl rest]

theorem runArgs_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term) (earlier : List Sem),
    runArgs K ρ ψ stmt fT earlier (Term.substAbsList σ w args) = runArgs K ρ ψ stmt fT earlier args
  | [], _ => rfl
  | a :: as, earlier => by
    simp only [Term.substAbsList, runArgs, runT_substAbsSame hF false a, runArgs_substAbsSame hF stmt fT as, hF.dec.2.1]

theorem runFields_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (rh : Option Rec) (sol : List (Option Sem)) (earlier : List Sem),
    runFields K ρ ψ stmt d c i rh sol earlier (Term.substAbsList σ w args) = runFields K ρ ψ stmt d c i rh sol earlier args
  | [], _, _, _, _ => rfl
  | a :: as, i, rh, sol, earlier => by
    simp only [Term.substAbsList, runFields, runT_substAbsSame hF false a, runFields_substAbsSame hF stmt d c as, hF.dec.2.1]

theorem runParams_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem),
    runParams K ρ ψ d i earlier (Term.substAbsList σ w args) = runParams K ρ ψ d i earlier args
  | [], _, _ => rfl
  | a :: as, i, earlier => by
    simp only [Term.substAbsList, runParams, runT_substAbsSame hF false a, runParams_substAbsSame hF d as]

theorem runBinds_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (ds : List Term) (s : SState) (dcs : List DeclInfo)
    (pre : List PBind), runBinds K ρ ψ s dcs pre (Term.substAbsList σ w ds) = runBinds K ρ ψ s dcs pre ds
  | [], _, _, _ => rfl
  | d :: ds, s, dcs, pre => by
    have hd := runT_substAbsSame hF false d
    have hds := fun pre' => runBinds_substAbsSame hF ds s dcs pre'
    cases d with
    | ref A =>
      have hA := runT_substAbsSame hF false A
      simp only [Term.substAbsList, Term.substAbs, runBinds, hA, hds]
    | _ => simp only [Term.substAbsList] at hd ⊢; simp only [Term.substAbs] at hd ⊢; simp only [runBinds, hd, hds]

theorem capsVals_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (vs : List Value),
    capsVals K ρ ψ (Value.substAbsList σ w vs) = capsVals K ρ ψ vs
  | [] => rfl
  | v :: vs => by simp only [Value.substAbsList, capsVals, meanV_substAbsSame hF v, capsVals_substAbsSame hF vs]

theorem capsTys_substAbsSame (hF : AbsFillOK K ρ ψ σ w) : ∀ (rd : List (DeclInfo × Value)),
    capsTys K ρ ψ (Value.substAbsRd σ w rd) = capsTys K ρ ψ rd
  | [] => rfl
  | (d, T) :: rest => by
    simp only [Value.substAbsRd, capsTys, meanV_substAbsSame hF T, capsTys_substAbsSame hF rest]

theorem meanFields_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    meanFields K ρ ψ d r c i earlier (Value.substAbsList σ w vs) = meanFields K ρ ψ d r c i earlier vs
  | [], _, _ => rfl
  | v :: vs, i, earlier => by
    simp only [Value.substAbsList, meanFields, meanV_substAbsSame hF v, meanFields_substAbsSame hF d r c vs]

theorem meanParams_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    meanParams K ρ ψ d i earlier (Value.substAbsList σ w vs) = meanParams K ρ ψ d i earlier vs
  | [], _, _ => rfl
  | v :: vs, i, earlier => by
    simp only [Value.substAbsList, meanParams, meanV_substAbsSame hF v, meanParams_substAbsSame hF d vs]

end

/-- `runT_substAbsSame` at a position that is not a tail. -/
theorem run_substAbsSame (hF : AbsFillOK K ρ ψ σ w) (t : Term) (hint : TyS) :
    run K ρ ψ hint (Term.substAbs σ w t) = run K ρ ψ hint t :=
  runT_substAbsSame K ρ ψ σ w hF false t hint

end SubstAbsMut

section
variable (K : RunCtx) (ρ : Assignment)

/-- **Replacing an unknown by what it means keeps a value's meaning** (docs/31 D77): under an
assignment at which the filler means the unknown, its run types it as the unknown, and the decisions
do not see the substitution (`AbsFillOK`). -/
theorem meanV_substAbs (ψ : Future) (σ : Nat) (r : Value) (hF : AbsFillOK K ρ ψ σ r) (v : Value) (hint : TyS) :
    meanV K ρ ψ hint (Value.substAbs σ r v) = meanV K ρ ψ hint v :=
  meanV_substAbsSame K ρ ψ σ r hF v hint

/-- **Replacing an unknown by what it means keeps a program's run.** -/
theorem run_substAbs (ψ : Future) (σ : Nat) (r : Value) (hF : AbsFillOK K ρ ψ σ r) (tl : Bool) (t : Term)
    (hint : TyS) : runT K ρ ψ tl hint (Term.substAbs σ r t) = runT K ρ ψ tl hint t :=
  runT_substAbsSame K ρ ψ σ r hF tl t hint

end

end Ochr.Meaning
