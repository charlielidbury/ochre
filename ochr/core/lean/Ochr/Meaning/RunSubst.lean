import Ochr.Meaning.RunCongr
import Ochr.Meaning.Subst
import Ochr.Meaning.SubstDefs

/-!
# Filling a loan at a fixed future (step (A) of the substitution lemmas)

At a future `ψ` where `loan ℓ` and the filler `w` mean the same (`ψ ℓ = ⟦w⟧` at every hint) and
the run gives them the same type (`FillShape`), and where the decisions do not see the
substitution (`DecInvariant`), the run of `t[loan ℓ := w]` is the run of `t`, clause by clause:
the substitution changes only embedded values, never a place. A sealed program runs from the counter
0 (PROPOSAL 8), so the substitution does not change its starting state either.
-/

namespace Ochr.Meaning

open SState

/-! ## The substitution keeps every place occurrence -/

section Syntax
variable (l : Nat) (w : Value)

mutual
theorem placeOccs_substLoan : ∀ (t : Term) (c : Nat), (Term.substLoan l w t).placeOccs c = t.placeOccs c
  | t, c => by
    cases t with
    | assign p u => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan u]
    | letIn h u v => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan u, placeOccs_substLoan v]
    | seq u v => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan u, placeOccs_substLoan v]
    | matchNat p z s => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan z, placeOccs_substLoan s]
    | pi hs ds cod =>
      simp only [Term.substLoan, Term.placeOccs, placeOccsDoms_substLoan ds, placeOccs_substLoan cod,
        length_substLoanList ds]
    | fix f hs ds cod d b =>
      simp only [Term.substLoan, Term.placeOccs, placeOccsDoms_substLoan ds, placeOccs_substLoan cod,
        placeOccs_substLoan b, length_substLoanList ds]
    | call g as h => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan g, placeOccsList_substLoan as]
    | succ u => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan u]
    | ref u => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan u]
    | cong a b => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan a, placeOccs_substLoan b]
    | ascribe a b => simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan a, placeOccs_substLoan b]
    | eq a b d =>
      simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan a, placeOccs_substLoan b, placeOccs_substLoan d]
    | id a b d =>
      simp only [Term.substLoan, Term.placeOccs, placeOccs_substLoan a, placeOccs_substLoan b, placeOccs_substLoan d]
    | ctor ty k h ps as =>
      simp only [Term.substLoan, Term.placeOccs, placeOccsList_substLoan ps, placeOccsList_substLoan as]
    | prim n as => simp only [Term.substLoan, Term.placeOccs, placeOccsList_substLoan as]
    | tind n as => simp only [Term.substLoan, Term.placeOccs, placeOccsList_substLoan as]
    | matchInd p ty as => simp only [Term.substLoan, Term.placeOccs, placeOccsArms_substLoan as]
    | _ => simp [Term.substLoan, Term.placeOccs]

theorem placeOccsList_substLoan : ∀ (ts : List Term) (c : Nat),
    Term.placeOccsList c (Term.substLoanList l w ts) = Term.placeOccsList c ts
  | [], _ => rfl
  | t :: ts, c => by
    simp only [Term.substLoanList, Term.placeOccsList, placeOccs_substLoan t, placeOccsList_substLoan ts]

theorem placeOccsDoms_substLoan : ∀ (ts : List Term) (c : Nat),
    Term.placeOccsDoms c (Term.substLoanList l w ts) = Term.placeOccsDoms c ts
  | [], _ => rfl
  | t :: ts, c => by
    simp only [Term.substLoanList, Term.placeOccsDoms, placeOccs_substLoan t, placeOccsDoms_substLoan ts]

theorem placeOccsArms_substLoan : ∀ (ts : List (Hint × Term)) (c : Nat),
    Term.placeOccsArms c (Term.substLoanArms l w ts) = Term.placeOccsArms c ts
  | [], _ => rfl
  | (h, t) :: ts, c => by
    simp only [Term.substLoanArms, Term.placeOccsArms, placeOccs_substLoan t, placeOccsArms_substLoan ts]

theorem length_substLoanList : ∀ ts : List Term, (Term.substLoanList l w ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp only [Term.substLoanList, List.length_cons, length_substLoanList ts]
end

theorem freeVars_substLoan (t : Term) : (Term.substLoan l w t).freeVars = t.freeVars := by
  simp only [Term.freeVars, Term.freeOccs, placeOccs_substLoan]

end Syntax

/-! ## Support: the pieces that read the term -/

section SubstSame
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (l : Nat) (w : Value) {fb : List PBind × PBind}

/-- The decisions do not see the fill in a telescope's readings (D19, R3). -/
theorem teleDecls_substLoan (hD : DecInvariant K.D l w) : ∀ (ds : List Term) (sc : List DeclInfo),
    K.D.teleDecls sc (Term.substLoanList l w ds) = K.D.teleDecls sc ds
  | [], _ => rfl
  | d :: ds, sc => by
    simp only [Term.substLoanList, Decisions.teleDecls, hD.2.2.2.2.2, teleDecls_substLoan hD ds]

theorem paramDecls_substLoan (hD : DecInvariant K.D l w) (sc : List DeclInfo) (ds : List Term) :
    K.D.paramDecls sc (Term.substLoanList l w ds) = K.D.paramDecls sc ds := by
  simp only [Decisions.paramDecls, teleDecls_substLoan K l w hD, length_substLoanList]

theorem fixDecls_substLoan (hD : DecInvariant K.D l w) (sc : List DeclInfo) (ds : List Term) (c : Term) :
    K.D.fixDecls sc (Term.substLoanList l w ds) (Term.substLoan l w c) = K.D.fixDecls sc ds c := by
  simp only [Decisions.fixDecls, paramDecls_substLoan K l w hD, teleDecls_substLoan K l w hD, hD.2.2.2.2.2]

/-- Filling a loan keeps which parameters are borrows: `&A` stays `&A`, and nothing else becomes one. -/
theorem psOf_substLoan : ∀ (bs : List PBind) (ds : List Term), psOf bs (Term.substLoanList l w ds) = psOf bs ds
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, d :: ds => by
    have hd : (Term.substLoan l w d).isRefTy = d.isRefTy := by cases d <;> rfl
    simp only [Term.substLoanList, psOf, hd, psOf_substLoan bs ds]

theorem joinDrop_substLoan (hD : DecInvariant K.D l w) (φ : Future) (t : Term) (entry : List Place) (s : SState) :
    joinDrop K φ entry (Term.substLoan l w t) s = joinDrop K φ entry t s := by
  unfold joinDrop; rw [hD.2.2.2.1]

theorem fixBodyAt_bodyEq {body body' : Term} (hb : ∀ hint, run K ρ ψ hint body' = run K ρ ψ hint body)
    (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) :
    fixBodyAt K ρ ψ fb s ps out piT start body' = fixBodyAt K ρ ψ fb s ps out piT start body := by
  funext selfM args
  unfold fixBodyAt
  simp only [hb]

theorem fixStage_bodyEq {body body' : Term} (hb : ∀ hint, run K ρ ψ hint body' = run K ρ ψ hint body)
    (lv : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) :
    ∀ k, fixStage K ρ ψ fb lv s ps out piT start body' k = fixStage K ρ ψ fb lv s ps out piT start body k
  | 0 => rfl
  | k + 1 => by
    show fixBodyAt K ρ ψ fb s ps out piT start body' (closureAt lv ψ ps out (fixStage K ρ ψ fb lv s ps out piT start body' k))
      = fixBodyAt K ρ ψ fb s ps out piT start body (closureAt lv ψ ps out (fixStage K ρ ψ fb lv s ps out piT start body k))
    rw [fixStage_bodyEq hb lv s ps out piT start k, fixBodyAt_bodyEq K ρ ψ hb]

theorem fixG_bodyEq {body body' : Term} (hb : ∀ hint, run K ρ ψ hint body' = run K ρ ψ hint body)
    (lv : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) (dec : Option Nat) :
    fixG K ρ ψ fb lv s ps out piT start dec body' = fixG K ρ ψ fb lv s ps out piT start dec body := by
  cases dec with
  | none => exact congrFun (fixBodyAt_bodyEq K ρ ψ hb s ps out piT start) _
  | some j =>
    funext args
    simp only [fixG]
    exact congrFun (fixStage_bodyEq K ρ ψ hb lv s ps out piT start _) args

theorem fixMoves_substLoan (t : Term) (s : SState) : fixMoves K (Term.substLoan l w t) s = fixMoves K t s := by
  unfold fixMoves; rw [freeVars_substLoan]

theorem substLoan_isPlace (u : Term) : (∃ p, Term.substLoan l w u = .place p) ↔ ∃ p, u = .place p := by
  cases u <;> simp [Term.substLoan]

end SubstSame

section SubstSame2
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (l : Nat) (w : Value)

theorem run_pi_def (hint : TyS) (hs : List Hint) (ds : List Term) (c : Term) (s : SState) :
    run K ρ ψ hint (.pi hs ds c) s =
      some ((.ty (piTyAt (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ ψ s ds) (fixOut K ρ ψ s (bindsOf K ρ ψ s ds) c)),
        ⟨.univ (K.D.piSort (scopeOf s) (.pi hs ds c)), some (runDoms K ρ ψ s ds, fixOut K ρ ψ s (bindsOf K ρ ψ s ds) c), none, none⟩), s) := by
  rw [run]; rfl

theorem fixOut_data {c : Term} (h : ∀ U, c ≠ .ref U) (s : SState) (bs : List PBind) :
    fixOut K ρ ψ s bs c = .data fun acc => match run K ρ ψ (.plain .err) c (extendBy s bs acc) with
      | some ((v, _), _) => v.asTy
      | none => .err := by
  unfold fixOut; split
  · exact absurd rfl (h _)
  · rfl

theorem substLoan_not_ref {c : Term} (h : ∀ U, c ≠ .ref U) : ∀ U, Term.substLoan l w c ≠ .ref U := by
  intro U e
  cases c with
  | ref V => exact h V rfl
  | _ => simp [Term.substLoan] at e

theorem fixOut_subst_of {c : Term} (hc : ∀ hint, run K ρ ψ hint (Term.substLoan l w c) = run K ρ ψ hint c)
    (hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substLoan l w U) = run K ρ ψ hint U) (s : SState)
    (bs : List PBind) :
    fixOut K ρ ψ s bs (Term.substLoan l w c) = fixOut K ρ ψ s bs c := by
  by_cases h : ∃ U, c = .ref U
  · obtain ⟨U, rfl⟩ := h
    simp only [Term.substLoan, fixOut, hU U rfl]
  · have h' : ∀ U, c ≠ .ref U := fun U e => h ⟨U, e⟩
    rw [fixOut_data K ρ ψ (substLoan_not_ref l w h') s bs, fixOut_data K ρ ψ h' s bs]
    simp only [hc]

theorem fixCod_data {c : Term} (h : ∀ U, c ≠ .ref U) (s : SState) (bs : List PBind) :
    fixCod K ρ ψ s bs c = fun acc => match run K ρ ψ (.plain .err) c (extendBy s bs acc) with
      | some ((v, R), _) => ⟨v.asTy, R.shape, none, R.data⟩
      | none => .plain .err := by
  unfold fixCod; split
  · exact absurd rfl (h _)
  · rfl

theorem fixCod_subst_of {c : Term} (hc : ∀ hint, run K ρ ψ hint (Term.substLoan l w c) = run K ρ ψ hint c)
    (hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substLoan l w U) = run K ρ ψ hint U) (s : SState)
    (bs : List PBind) :
    fixCod K ρ ψ s bs (Term.substLoan l w c) = fixCod K ρ ψ s bs c := by
  by_cases h : ∃ U, c = .ref U
  · obtain ⟨U, rfl⟩ := h
    simp only [Term.substLoan, fixCod, hU U rfl]
  · have h' : ∀ U, c ≠ .ref U := fun U e => h ⟨U, e⟩
    rw [fixCod_data K ρ ψ (substLoan_not_ref l w h') s bs, fixCod_data K ρ ψ h' s bs]
    simp only [hc]

/-- What the substitution at a fixed future needs: the filler means the loan, has its type, and
the decisions do not see it. -/
structure FillOK : Prop where
  mean : ∀ hint, meanV K ρ ψ hint w = ψ l
  shape : FillShape K ρ ψ l w
  dec : DecInvariant K.D l w

end SubstSame2

section SubstPrim
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (l : Nat) (w : Value)

theorem Term.substLoanList_isEmpty (ts : List Term) : (Term.substLoanList l w ts).isEmpty = ts.isEmpty := by
  cases ts <;> rfl

theorem Value.substLoanList_isEmpty (vs : List Value) : (Value.substLoanList l w vs).isEmpty = vs.isEmpty := by
  cases vs <;> rfl

theorem length_substLoanArms : ∀ ts : List (Hint × Term), (Term.substLoanArms l w ts).length = ts.length
  | [] => rfl
  | (_, _) :: ts => by simp only [Term.substLoanArms, List.length_cons, length_substLoanArms ts]

theorem list_six {α : Type _} (xs : List α) (h : xs.length = 6) : ∃ a b c d e f, xs = [a, b, c, d, e, f] := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, f, rfl⟩

theorem list_one {α : Type _} (xs : List α) (h : xs.length = 1) : ∃ a, xs = [a] := by
  rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h
  exact ⟨a, rfl⟩

/-- Filling a loan keeps what `SM.headOf` reads: a place is not a value, so it is unchanged, and
any other term keeps its form. -/
theorem headOf_substLoan (u : Term) (rd : Place → SM (Sem × TyS)) (rn : SM (Sem × TyS)) :
    SM.headOf (Term.substLoan l w u) rd rn = SM.headOf u rd rn := by
  cases u <;> rfl

theorem run_prim_substSame (n : String) (args : List Term) (hint : TyS)
    (hfl : ∀ sc, K.D.flags sc (Term.substLoan l w (.prim n args)) = K.D.flags sc (.prim n args))
    (hall : ∀ t ∈ args, ∀ hint, run K ρ ψ hint (Term.substLoan l w t) = run K ρ ψ hint t) :
    run K ρ ψ hint (Term.substLoan l w (.prim n args)) = run K ρ ψ hint (.prim n args) := by
  show run K ρ ψ hint (.prim n (Term.substLoanList l w args)) = _
  have hfl' : ∀ sc, K.D.flags sc (.prim n (Term.substLoanList l w args)) = K.D.flags sc (.prim n args) := hfl
  funext s
  have hlen := length_substLoanList l w args
  by_cases h1 : n = "symm"
  · subst h1; rw [run, run]
  by_cases h2 : n = "trans"
  · subst h2; rw [run, run]
  by_cases h3 : n = "rewrite"
  · subst h3; rw [run, run]
  by_cases h4 : n = "rewriteR"
  · subst h4; rw [run, run]
  by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
  · obtain ⟨A, a, b, P, h', t, rfl, rfl⟩ := hJ
    simp only [Term.substLoanList] at hfl' ⊢
    rw [run, run]
    simp only [hfl', hall A (by simp), hall a (by simp), hall b (by simp),
      hall P (by simp), hall h' (by simp), hall t (by simp)]
  by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
  · obtain ⟨u, hn, rfl⟩ := hc
    simp only [Term.substLoanList] at hfl' ⊢
    rcases hn with rfl | rfl | rfl <;>
      (rw [run, run]; simp only [hfl', hall u (by simp), headOf_substLoan])
  have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
    fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
  have hJs : ∀ (A a b P h t : Term), n = "J" → Term.substLoanList l w args = [A, a, b, P, h, t] → False := by
    intro A a b P h t e1 e2
    have : args.length = 6 := by rw [← hlen, e2]; rfl
    obtain ⟨x1, x2, x3, x4, x5, x6, hx⟩ := list_six args this
    exact hJ' x1 x2 x3 x4 x5 x6 e1 hx
  have hcs : ∀ m, (m = "clone" ∨ m = "peek" ∨ m = "inplace") → (∀ u, n = m → args = [u] → False) ∧
      (∀ u, n = m → Term.substLoanList l w args = [u] → False) := by
    intro m hm
    refine ⟨fun u e1 e2 => hc ⟨u, e1 ▸ hm, e2⟩, fun u e1 e2 => ?_⟩
    have : args.length = 1 := by rw [← hlen, e2]; rfl
    obtain ⟨x, hx⟩ := list_one args this
    exact hc ⟨x, e1 ▸ hm, hx⟩
  rw [run.eq_39 K ρ ψ hint n _ h1 h2 h3 h4 hJs (hcs _ (.inl rfl)).2 (hcs _ (.inr (.inl rfl))).2
      (hcs _ (.inr (.inr rfl))).2,
    run.eq_39 K ρ ψ hint n _ h1 h2 h3 h4 hJ' (hcs _ (.inl rfl)).1 (hcs _ (.inr (.inl rfl))).1
      (hcs _ (.inr (.inr rfl))).1]

end SubstPrim

section SubstMut
variable (K : RunCtx) (ρ : Assignment) (ψ : Future) (l : Nat) (w : Value)

mutual
/-- **Filling a loan at a fixed future**: where the filler means the loan (`FillOK`), the run of
the filled term is the run of the term. -/
theorem run_substSame (hF : FillOK K ρ ψ l w) : ∀ (t : Term) (hint : TyS),
    run K ρ ψ hint (Term.substLoan l w t) = run K ρ ψ hint t
  | t, hint => by
    cases t with
    | val v =>
      funext s
      show run K ρ ψ hint (.val (Value.substLoan l w v)) s = _
      rw [run_val_def, run_val_def, meanV_substSame hF v hint]
      cases v with
      | loan l' =>
        by_cases e : l' = l
        · subst e
          have h := hF.shape hint s
          rw [run_val_def, run_val_def] at h
          simp only [Option.map_some, Option.some.injEq] at h
          simp only [Value.substLoan, if_true]
          rw [h]
        · simp only [Value.substLoan, e, if_false]
      | clo caps t rd =>
        simp only [Value.substLoan, valT, capsVals_substSame hF caps, capsTys_substSame hF rd,
          piShapeOf_substSame hF t]
      | tPi caps t rd =>
        simp only [Value.substLoan, valT, capsVals_substSame hF caps, capsTys_substSame hF rd,
          piShapeOf_substSame hF t]
      | sealed t =>
        simp only [Value.substLoan, valT, run_substSame hF t hint]
      | _ => rfl
    | assign p u =>
      have hu := run_substSame hF u
      funext s
      show run K ρ ψ hint (.assign p (Term.substLoan l w u)) s = _
      have hfl : ∀ sc, K.D.flags sc (.assign p (Term.substLoan l w u)) = K.D.flags sc (.assign p u) :=
        fun sc => hF.dec.1 sc (.assign p u)
      rw [run, run]; simp only [hu, hfl]
    | letIn h u v =>
      have hu := run_substSame hF u
      have hv := run_substSame hF v
      funext s
      show run K ρ ψ hint (.letIn h (Term.substLoan l w u) (Term.substLoan l w v)) s = _
      have hfl : ∀ sc, K.D.flags sc (.letIn h (Term.substLoan l w u) (Term.substLoan l w v)) = K.D.flags sc (.letIn h u v) :=
        fun sc => hF.dec.1 sc (.letIn h u v)
      rw [run, run]; simp only [hu, hv, hF.dec.2.1, hfl]
    | seq u v =>
      have hu := run_substSame hF u
      have hv := run_substSame hF v
      show run K ρ ψ hint (.seq (Term.substLoan l w u) (Term.substLoan l w v)) = _
      have hfl : ∀ sc, K.D.flags sc (.seq (Term.substLoan l w u) (Term.substLoan l w v)) = K.D.flags sc (.seq u v) :=
        fun sc => hF.dec.1 sc (.seq u v)
      rw [run, run]; simp only [hu, hv, hfl]
    | matchNat p z u =>
      have hz := run_substSame hF z
      have hu := run_substSame hF u
      have hj : ∀ e s, joinDrop K ψ e (.matchNat p (Term.substLoan l w z) (Term.substLoan l w u)) s
          = joinDrop K ψ e (.matchNat p z u) s := joinDrop_substLoan K l w hF.dec ψ (.matchNat p z u)
      funext s
      show run K ρ ψ hint (.matchNat p (Term.substLoan l w z) (Term.substLoan l w u)) s = _
      have hfl : ∀ sc, K.D.flags sc (.matchNat p (Term.substLoan l w z) (Term.substLoan l w u)) = K.D.flags sc (.matchNat p z u) :=
        fun sc => hF.dec.1 sc (.matchNat p z u)
      rw [run, run]; simp only [hz, hu, hj, hfl]
    | matchInd p n arms =>
      have ha := runArm_substSame hF arms
      have hj : ∀ e s, joinDrop K ψ e (.matchInd p n (Term.substLoanArms l w arms)) s
          = joinDrop K ψ e (.matchInd p n arms) s := joinDrop_substLoan K l w hF.dec ψ (.matchInd p n arms)
      funext s
      show run K ρ ψ hint (.matchInd p n (Term.substLoanArms l w arms)) s = _
      have hfl : ∀ sc, K.D.flags sc (.matchInd p n (Term.substLoanArms l w arms)) = K.D.flags sc (.matchInd p n arms) :=
        fun sc => hF.dec.1 sc (.matchInd p n arms)
      rw [run, run]; simp only [ha, hj, length_substLoanArms, hfl]
    | succ u =>
      have hu := run_substSame hF u
      show run K ρ ψ hint (.succ (Term.substLoan l w u)) = _
      have hfl : ∀ sc, K.D.flags sc (.succ (Term.substLoan l w u)) = K.D.flags sc (.succ u) :=
        fun sc => hF.dec.1 sc (.succ u)
      rw [run, run]; simp only [hu, hfl]
    | ref u =>
      have hu := run_substSame hF u
      show run K ρ ψ hint (.ref (Term.substLoan l w u)) = _
      have hfl : ∀ sc, K.D.flags sc (.ref (Term.substLoan l w u)) = K.D.flags sc (.ref u) :=
        fun sc => hF.dec.1 sc (.ref u)
      rw [run, run]; simp only [hu, hfl]
    | cong a b => rfl
    | ascribe u A =>
      have hu := run_substSame hF u
      have hA := run_substSame hF A
      show run K ρ ψ hint (.ascribe (Term.substLoan l w u) (Term.substLoan l w A)) = _
      have hfl : ∀ sc, K.D.flags sc (.ascribe (Term.substLoan l w u) (Term.substLoan l w A)) = K.D.flags sc (.ascribe u A) :=
        fun sc => hF.dec.1 sc (.ascribe u A)
      rw [run, run]; simp only [hu, hA, hfl]
    | eq A a b =>
      have hA := run_substSame hF A
      have ha := run_substSame hF a
      have hb := run_substSame hF b
      show run K ρ ψ hint (.eq (Term.substLoan l w A) (Term.substLoan l w a) (Term.substLoan l w b)) = _
      rw [run, run]; simp only [hA, ha, hb]
    | id A a b =>
      have hA := run_substSame hF A
      have ha := run_substSame hF a
      have hb := run_substSame hF b
      funext s
      show run K ρ ψ hint (.id (Term.substLoan l w A) (Term.substLoan l w a) (Term.substLoan l w b)) s = _
      rw [run, run]; simp only [hA, ha, hb, hF.dec.2.2.2.2.1]
    | tind n args =>
      have hp := fun d => runParams_substSame hF d args
      show run K ρ ψ hint (.tind n (Term.substLoanList l w args)) = _
      rw [run, run]; simp only [hp]
    | ctor ty c h ps args =>
      have hp := fun d => runParams_substSame hF d ps
      have hf := fun st d => runFields_substSame hF st d c args
      show run K ρ ψ hint (.ctor ty c h (Term.substLoanList l w ps) (Term.substLoanList l w args)) = _
      have hfl : ∀ sc, K.D.flags sc (.ctor ty c h (Term.substLoanList l w ps) (Term.substLoanList l w args))
          = K.D.flags sc (.ctor ty c h ps args) := fun sc => hF.dec.1 sc (.ctor ty c h ps args)
      rw [run, run]; simp only [hp, hf, Term.substLoanList_isEmpty, hfl]
    | call f args hd =>
      have hf := run_substSame hF f
      have ha := fun st sh => runArgs_substSame hF st sh args
      have hfl : ∀ sc, K.D.flags sc (.call (Term.substLoan l w f) (Term.substLoanList l w args) hd)
          = K.D.flags sc (.call f args hd) := fun sc => hF.dec.1 sc (.call f args hd)
      funext s
      show run K ρ ψ hint (.call (Term.substLoan l w f) (Term.substLoanList l w args) hd) s = _
      rw [run, run]; simp only [hf, ha, hfl, headOf_substLoan]
    | pi hs ds c =>
      have hc := run_substSame hF c
      have hbs : ∀ s, bindsOf K ρ ψ s (Term.substLoanList l w ds) = bindsOf K ρ ψ s ds := fun s => by
        unfold bindsOf; rw [paramDecls_substLoan K l w hF.dec, runBinds_substSame hF]
      have hds : ∀ s, runDoms K ρ ψ s (Term.substLoanList l w ds) = runDoms K ρ ψ s ds := fun s => by
        unfold runDoms; rw [hbs, psOf_substLoan]
      have hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substLoan l w U) = run K ρ ψ hint U := by
        cases c with
        | ref U => intro U' e hint; rw [show U' = U by injection e with e; exact e.symm]; exact run_substSame hF U hint
        | _ => intro U' e; cases e
      have hps : ∀ sc, K.D.piSort sc (.pi hs (Term.substLoanList l w ds) (Term.substLoan l w c))
          = K.D.piSort sc (.pi hs ds c) := fun sc => hF.dec.2.2.1 sc (.pi hs ds c)
      funext s
      show run K ρ ψ hint (.pi hs (Term.substLoanList l w ds) (Term.substLoan l w c)) s = _
      rw [run_pi_def, run_pi_def, hps, hds, hbs, fixOut_subst_of K ρ ψ l w hc hU]
    | fix self hs ds c dec body =>
      have hc := run_substSame hF c
      have hbs : ∀ s, bindsOf K ρ ψ s (Term.substLoanList l w ds) = bindsOf K ρ ψ s ds := fun s => by
        unfold bindsOf; rw [paramDecls_substLoan K l w hF.dec, runBinds_substSame hF]
      have hds : ∀ s, runDoms K ρ ψ s (Term.substLoanList l w ds) = runDoms K ρ ψ s ds := fun s => by
        unfold runDoms; rw [hbs, psOf_substLoan]
      have hb := run_substSame hF body
      have hU : ∀ U, c = .ref U → ∀ hint, run K ρ ψ hint (Term.substLoan l w U) = run K ρ ψ hint U := by
        cases c with
        | ref U => intro U' e hint; rw [show U' = U by injection e with e; exact e.symm]; exact run_substSame hF U hint
        | _ => intro U' e; cases e
      have hps : ∀ sc, K.D.piSort sc (.pi hs (Term.substLoanList l w ds) (Term.substLoan l w c))
          = K.D.piSort sc (.pi hs ds c) := fun sc => hF.dec.2.2.1 sc (.pi hs ds c)
      have hmv : ∀ s, fixMoves K (.fix self hs (Term.substLoanList l w ds) (Term.substLoan l w c) dec
          (Term.substLoan l w body)) s = fixMoves K (.fix self hs ds c dec body) s :=
        fixMoves_substLoan K l w (.fix self hs ds c dec body)
      funext s
      show run K ρ ψ hint (.fix self hs (Term.substLoanList l w ds) (Term.substLoan l w c) dec
        (Term.substLoan l w body)) s = _
      have hfl : ∀ sc, K.D.flags sc (.fix self hs (Term.substLoanList l w ds) (Term.substLoan l w c) dec
          (Term.substLoan l w body)) = K.D.flags sc (.fix self hs ds c dec body) :=
        fun sc => hF.dec.1 sc (.fix self hs ds c dec body)
      rw [run_fix_def, run_fix_def, hfl, hps, hds, hbs, fixOut_subst_of K ρ ψ l w hc hU, fixCod_subst_of K ρ ψ l w hc hU, hmv,
        teleDecls_substLoan K l w hF.dec, hF.dec.2.2.2.2.2, fixG_bodyEq K ρ ψ hb]
    | prim n args =>
      have hall : ∀ t ∈ args, ∀ hint, run K ρ ψ hint (Term.substLoan l w t) = run K ρ ψ hint t :=
        fun t hm hint => runAll_substSame hF args t hm hint
      exact run_prim_substSame K ρ ψ l w n args hint (fun sc => hF.dec.1 sc (.prim n args)) hall
    | _ => rfl

theorem meanV_substSame (hF : FillOK K ρ ψ l w) : ∀ (v : Value) (hint : TyS),
    meanV K ρ ψ hint (Value.substLoan l w v) = meanV K ρ ψ hint v
  | v, hint => by
    cases v with
    | loan l' =>
      by_cases e : l' = l
      · subst e; simp only [Value.substLoan, if_true]; rw [hF.mean hint]; rfl
      · simp only [Value.substLoan, e, if_false]
    | succ u =>
      show (meanV K ρ ψ _ (Value.substLoan l w u)).succ = (meanV K ρ ψ _ u).succ
      rw [meanV_substSame hF u]
    | borrow m u =>
      show meanV K ρ ψ hint (Value.substLoan l w u) = meanV K ρ ψ hint u
      exact meanV_substSame hF u hint
    | tRef A =>
      show meanV K ρ ψ _ (Value.substLoan l w A) = meanV K ρ ψ _ A
      exact meanV_substSame hF A _
    | tEq A a b =>
      show meanV K ρ ψ hint (.tEq (Value.substLoan l w A) (Value.substLoan l w a) (Value.substLoan l w b)) = _
      rw [meanV, meanV, meanV_substSame hF A, meanV_substSame hF a, meanV_substSame hF b]
    | clo caps t rd =>
      show meanV K ρ ψ hint (.clo (Value.substLoanList l w caps) (Term.substLoan l w t) (Value.substLoanRd l w rd)) = _
      rw [meanV, meanV, capsVals_substSame hF caps, capsTys_substSame hF rd, run_substSame hF t]
    | tPi caps t rd =>
      show meanV K ρ ψ hint (.tPi (Value.substLoanList l w caps) (Term.substLoan l w t) (Value.substLoanRd l w rd)) = _
      rw [meanV, meanV, capsVals_substSame hF caps, capsTys_substSame hF rd, run_substSame hF t]
    | sealed t =>
      show meanV K ρ ψ hint (.sealed (Term.substLoan l w t)) = _
      rw [meanV, meanV, run_substSame hF t hint]
    | ind ty c h ps fs =>
      show meanV K ρ ψ hint (.ind ty c h (Value.substLoanList l w ps) (Value.substLoanList l w fs)) = _
      rw [meanV, meanV]
      simp only [meanParams_substSame hF, meanFields_substSame hF, Value.substLoanList_isEmpty]
    | tInd n args =>
      show meanV K ρ ψ hint (.tInd n (Value.substLoanList l w args)) = _
      rw [meanV, meanV]
      simp only [meanParams_substSame hF]
    | _ => rfl

theorem runAll_substSame (hF : FillOK K ρ ψ l w) : ∀ (ts : List Term) (t : Term), t ∈ ts → ∀ (hint : TyS),
    run K ρ ψ hint (Term.substLoan l w t) = run K ρ ψ hint t
  | [], t, h, _ => absurd h List.not_mem_nil
  | a :: as, t, h, hint => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e]; exact run_substSame hF a hint
    · exact runAll_substSame hF as t h hint

theorem runArm_substSame (hF : FillOK K ρ ψ l w) : ∀ (arms : List (Hint × Term)) (hint : TyS) (c : Nat),
    runArm K ρ ψ hint c (Term.substLoanArms l w arms) = runArm K ρ ψ hint c arms
  | [], _, _ => rfl
  | (h, t) :: rest, hint, c => by
    simp only [Term.substLoanArms, runArm, run_substSame hF t, runArm_substSame hF rest]

theorem runArgs_substSame (hF : FillOK K ρ ψ l w) (stmt : Bool) (shape : Option (List PiParam × PiOut)) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem),
    runArgs K ρ ψ stmt shape i earlier (Term.substLoanList l w args) = runArgs K ρ ψ stmt shape i earlier args
  | [], _, _ => rfl
  | a :: as, i, earlier => by
    simp only [Term.substLoanList, runArgs, run_substSame hF a, runArgs_substSame hF stmt shape as, hF.dec.2.1]

theorem runFields_substSame (hF : FillOK K ρ ψ l w) (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (sol : List (Option Sem)) (earlier : List Sem),
    runFields K ρ ψ stmt d c i sol earlier (Term.substLoanList l w args) = runFields K ρ ψ stmt d c i sol earlier args
  | [], _, _, _ => rfl
  | a :: as, i, sol, earlier => by
    simp only [Term.substLoanList, runFields, run_substSame hF a, runFields_substSame hF stmt d c as, hF.dec.2.1]

theorem runParams_substSame (hF : FillOK K ρ ψ l w) (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem),
    runParams K ρ ψ d i earlier (Term.substLoanList l w args) = runParams K ρ ψ d i earlier args
  | [], _, _ => rfl
  | a :: as, i, earlier => by
    simp only [Term.substLoanList, runParams, run_substSame hF a, runParams_substSame hF d as]

theorem runBinds_substSame (hF : FillOK K ρ ψ l w) : ∀ (ds : List Term) (s : SState) (dcs : List DeclInfo)
    (pre : List PBind), runBinds K ρ ψ s dcs pre (Term.substLoanList l w ds) = runBinds K ρ ψ s dcs pre ds
  | [], _, _, _ => rfl
  | d :: ds, s, dcs, pre => by
    have hd := run_substSame hF d
    have hds := fun pre' => runBinds_substSame hF ds s dcs pre'
    cases d with
    | ref A =>
      have hA := run_substSame hF A
      simp only [Term.substLoanList, Term.substLoan, runBinds, hA, hds]
    | _ => simp only [Term.substLoanList] at hd ⊢; simp only [Term.substLoan] at hd ⊢; simp only [runBinds, hd, hds]

theorem capsVals_substSame (hF : FillOK K ρ ψ l w) : ∀ (vs : List Value),
    capsVals K ρ ψ (Value.substLoanList l w vs) = capsVals K ρ ψ vs
  | [] => rfl
  | v :: vs => by simp only [Value.substLoanList, capsVals, meanV_substSame hF v, capsVals_substSame hF vs]

theorem capsTys_substSame (hF : FillOK K ρ ψ l w) : ∀ (rd : List (DeclInfo × Value)),
    capsTys K ρ ψ (Value.substLoanRd l w rd) = capsTys K ρ ψ rd
  | [] => rfl
  | (d, T) :: rest => by simp only [Value.substLoanRd, capsTys, meanV_substSame hF T, capsTys_substSame hF rest]

theorem meanFields_substSame (hF : FillOK K ρ ψ l w) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    meanFields K ρ ψ d ps c i earlier (Value.substLoanList l w vs) = meanFields K ρ ψ d ps c i earlier vs
  | [], _, _ => rfl
  | v :: vs, i, earlier => by
    simp only [Value.substLoanList, meanFields, meanV_substSame hF v, meanFields_substSame hF d ps c vs]

theorem meanParams_substSame (hF : FillOK K ρ ψ l w) (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    meanParams K ρ ψ d i earlier (Value.substLoanList l w vs) = meanParams K ρ ψ d i earlier vs
  | [], _, _ => rfl
  | v :: vs, i, earlier => by
    simp only [Value.substLoanList, meanParams, meanV_substSame hF v, meanParams_substSame hF d vs]

theorem piShapeOf_substSame (hF : FillOK K ρ ψ l w) : ∀ (t : Term) (s : SState),
    piShapeOf K ρ ψ s (Term.substLoan l w t) = piShapeOf K ρ ψ s t
  | t, s => by
    cases t with
    | pi hs ds c =>
      have hbs := fun dcs pre => runBinds_substSame hF ds s dcs pre
      have hpd := paramDecls_substLoan K l w hF.dec (scopeOf s) ds
      have hc := run_substSame hF c
      cases c with
      | ref U =>
        have hU := run_substSame hF U
        simp only [Term.substLoan, piShapeOf, hU, hbs, hpd, psOf_substLoan]
      | _ => simp only [Term.substLoan] at hc ⊢; simp only [piShapeOf, hc, hbs, hpd, psOf_substLoan]
    | fix self hs ds c dec body =>
      have hbs := fun dcs pre => runBinds_substSame hF ds s dcs pre
      have hpd := paramDecls_substLoan K l w hF.dec (scopeOf s) ds
      have hc := run_substSame hF c
      cases c with
      | ref U =>
        have hU := run_substSame hF U
        simp only [Term.substLoan, piShapeOf, hU, hbs, hpd, psOf_substLoan]
      | _ => simp only [Term.substLoan] at hc ⊢; simp only [piShapeOf, hc, hbs, hpd, psOf_substLoan]
    | _ => simp only [Term.substLoan, piShapeOf]
end

end SubstMut

/-! ## After filling `ℓ` with a value free of `ℓ`, no `loan ℓ` is left -/

section NoLoan
variable (l : Nat) (w : Value)

mutual
theorem noLoan_substLoanV (hw : w.anyAtom (· == .loan l) = false) : ∀ v : Value,
    (Value.substLoan l w v).anyAtom (· == .loan l) = false
  | .loan l' => by
    by_cases e : l' = l
    · subst e; simp only [Value.substLoan, if_true]; exact hw
    · simp only [Value.substLoan, e, if_false]
      show (Value.beq (.loan l') (.loan l) || false) = false
      simp [Value.beq, e]
  | .succ u => by
    show (_ || (Value.substLoan l w u).anyAtom (· == .loan l)) = false
    rw [noLoan_substLoanV hw u]; rfl
  | .tRef u => by
    show (_ || (Value.substLoan l w u).anyAtom (· == .loan l)) = false
    rw [noLoan_substLoanV hw u]; rfl
  | .borrow m u => by
    show (_ || (Value.substLoan l w u).anyAtom (· == .loan l)) = false
    rw [noLoan_substLoanV hw u]; rfl
  | .tEq A a b => by
    show (_ || ((Value.substLoan l w A).anyAtom (· == .loan l) || (Value.substLoan l w a).anyAtom (· == .loan l)
      || (Value.substLoan l w b).anyAtom (· == .loan l))) = false
    rw [noLoan_substLoanV hw A, noLoan_substLoanV hw a, noLoan_substLoanV hw b]; rfl
  | .clo cs t rd => by
    show (_ || (Value.anyAtomList (· == .loan l) (Value.substLoanList l w cs)
      || (Term.substLoan l w t).anyAtom (· == .loan l) || Value.anyAtomRd (· == .loan l) (Value.substLoanRd l w rd))) = false
    rw [noLoan_substLoanVL hw cs, noLoan_substLoanT hw t, noLoan_substLoanRd hw rd]; rfl
  | .tPi cs t rd => by
    show (_ || (Value.anyAtomList (· == .loan l) (Value.substLoanList l w cs)
      || (Term.substLoan l w t).anyAtom (· == .loan l) || Value.anyAtomRd (· == .loan l) (Value.substLoanRd l w rd))) = false
    rw [noLoan_substLoanVL hw cs, noLoan_substLoanT hw t, noLoan_substLoanRd hw rd]; rfl
  | .sealed t => by
    show (_ || (Term.substLoan l w t).anyAtom (· == .loan l)) = false
    rw [noLoan_substLoanT hw t]; rfl
  | .ind ty c h ps fs => by
    show (_ || (Value.anyAtomList (· == .loan l) (Value.substLoanList l w ps)
      || Value.anyAtomList (· == .loan l) (Value.substLoanList l w fs))) = false
    rw [noLoan_substLoanVL hw ps, noLoan_substLoanVL hw fs]; rfl
  | .tInd n fs => by
    show (_ || Value.anyAtomList (· == .loan l) (Value.substLoanList l w fs)) = false
    rw [noLoan_substLoanVL hw fs]; rfl
  | .zero => rfl
  | .unit => rfl
  | .gfn _ => rfl
  | .bot => rfl
  | .abs _ => rfl
  | .proof => rfl
  | .tNat => rfl
  | .tUnit => rfl
  | .sort _ => rfl

theorem noLoan_substLoanVL (hw : w.anyAtom (· == .loan l) = false) : ∀ vs : List Value,
    Value.anyAtomList (· == .loan l) (Value.substLoanList l w vs) = false
  | [] => rfl
  | v :: vs => by
    show ((Value.substLoan l w v).anyAtom (· == .loan l) || Value.anyAtomList (· == .loan l) (Value.substLoanList l w vs)) = false
    rw [noLoan_substLoanV hw v, noLoan_substLoanVL hw vs]; rfl

theorem noLoan_substLoanRd (hw : w.anyAtom (· == .loan l) = false) : ∀ rd : List (DeclInfo × Value),
    Value.anyAtomRd (· == .loan l) (Value.substLoanRd l w rd) = false
  | [] => rfl
  | (d, v) :: rd => by
    show ((Value.substLoan l w v).anyAtom (· == .loan l) || Value.anyAtomRd (· == .loan l) (Value.substLoanRd l w rd)) = false
    rw [noLoan_substLoanV hw v, noLoan_substLoanRd hw rd]; rfl

theorem noLoan_substLoanT (hw : w.anyAtom (· == .loan l) = false) : ∀ t : Term,
    (Term.substLoan l w t).anyAtom (· == .loan l) = false
  | .val v => noLoan_substLoanV hw v
  | .assign p u => noLoan_substLoanT hw u
  | .succ u => noLoan_substLoanT hw u
  | .ref u => noLoan_substLoanT hw u
  | .letIn h a b => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b]; rfl
  | .seq a b => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b]; rfl
  | .cong a b => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b]; rfl
  | .ascribe a b => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b]; rfl
  | .matchNat p a b => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b]; rfl
  | .pi hs ds c => by
    show (Term.anyAtomList _ (Term.substLoanList l w ds) || (Term.substLoan l w c).anyAtom _) = false
    rw [noLoan_substLoanTL hw ds, noLoan_substLoanT hw c]; rfl
  | .fix f hs ds c d b => by
    show (Term.anyAtomList _ (Term.substLoanList l w ds) || (Term.substLoan l w c).anyAtom _
      || (Term.substLoan l w b).anyAtom _) = false
    rw [noLoan_substLoanTL hw ds, noLoan_substLoanT hw c, noLoan_substLoanT hw b]; rfl
  | .call f as h => by
    show ((Term.substLoan l w f).anyAtom _ || Term.anyAtomList _ (Term.substLoanList l w as)) = false
    rw [noLoan_substLoanT hw f, noLoan_substLoanTL hw as]; rfl
  | .eq a b c => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _
      || (Term.substLoan l w c).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b, noLoan_substLoanT hw c]; rfl
  | .id a b c => by
    show ((Term.substLoan l w a).anyAtom _ || (Term.substLoan l w b).anyAtom _
      || (Term.substLoan l w c).anyAtom _) = false
    rw [noLoan_substLoanT hw a, noLoan_substLoanT hw b, noLoan_substLoanT hw c]; rfl
  | .ctor ty k h ps as => by
    show (Term.anyAtomList _ (Term.substLoanList l w ps) || Term.anyAtomList _ (Term.substLoanList l w as)) = false
    rw [noLoan_substLoanTL hw ps, noLoan_substLoanTL hw as]; rfl
  | .prim n as => noLoan_substLoanTL hw as
  | .tind n as => noLoan_substLoanTL hw as
  | .matchInd p ty as => noLoan_substLoanArms hw as
  | .place _ => rfl
  | .borrow _ => rfl
  | .const _ => rfl
  | .sort _ => rfl
  | .nat => rfl
  | .unit => rfl
  | .zero => rfl
  | .tt => rfl

theorem noLoan_substLoanTL (hw : w.anyAtom (· == .loan l) = false) : ∀ ts : List Term,
    Term.anyAtomList (· == .loan l) (Term.substLoanList l w ts) = false
  | [] => rfl
  | t :: ts => by
    show ((Term.substLoan l w t).anyAtom _ || Term.anyAtomList _ (Term.substLoanList l w ts)) = false
    rw [noLoan_substLoanT hw t, noLoan_substLoanTL hw ts]; rfl

theorem noLoan_substLoanArms (hw : w.anyAtom (· == .loan l) = false) : ∀ ts : List (Hint × Term),
    Term.anyAtomArms (· == .loan l) (Term.substLoanArms l w ts) = false
  | [] => rfl
  | (h, t) :: ts => by
    show ((Term.substLoan l w t).anyAtom _ || Term.anyAtomArms _ (Term.substLoanArms l w ts)) = false
    rw [noLoan_substLoanT hw t, noLoan_substLoanArms hw ts]; rfl
end

end NoLoan

end Ochr.Meaning
