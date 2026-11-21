import Ochr.Meaning.Strict.Simple

/-!
# The fundamental lemma's cases, one per clause of the strict run

Each case: the lemma at the subterms (and the context, `FundCtx`) gives it at the term. The
induction (`Strict/Fund.lean`) assembles them.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem fund_zero : Fund K ρ φ .zero := fun tl hint =>
  show FundAt _ _ _ (pure (.el0 Nat 0, .plain TyM.nat)) from fund_pure (.inl ⟨0, rfl⟩) rfl

theorem fund_tt : Fund K ρ φ .tt := fun tl hint =>
  show FundAt _ _ _ (pure (.el0 Unit (), .plain TyM.unit)) from fund_pure (.inl ⟨(), rfl⟩) rfl

theorem fund_nat : Fund K ρ φ .nat := fun tl hint =>
  show FundAt _ _ _ (pure (.ty TyM.nat, .plain (TyM.univ 1))) from fund_pure (.inl (ty_univ1_mem _ rfl)) rfl

theorem fund_unit : Fund K ρ φ .unit := fun tl hint =>
  show FundAt _ _ _ (pure (.ty TyM.unit, .plain (TyM.univ 1))) from fund_pure (.inl (ty_univ1_mem _ rfl)) rfl

theorem fund_sort (l : Nat) : Fund K ρ φ (.sort l) := fun tl hint =>
  show FundAt _ _ _ (pure (.ty (TyM.univ l), .plain (TyM.univ (sortSucc l)))) from fund_pure (goodRes_sort l) rfl

theorem fund_const (hc : FundCtx K) (n : String) : Fund K ρ φ (.const n) := fun tl hint =>
  show FundAt _ _ _ (pure (K.C.global n)) from fund_pure (hc.globals n).1 (hc.globals n).2

/-- `Eq(A, a, b)`: a proposition, on a copy. -/
theorem fund_eq (A a b : Term) : Fund K ρ φ (.eq A a b) := fun tl hint => by
  show FundAt _ _ _ (SM.onCopy _)
  refine fund_onCopy fun s s' r h => ?_
  obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
  obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
  obtain ⟨z, s₃, h5, h6⟩ := SM.bind_some h4
  obtain ⟨-, h6⟩ := open Classical in ite_none_some h6
  simp only [Option.some.injEq] at h6
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h6
  exact ⟨.inl (ty_univ0_mem _), rfl⟩

/-- `Id(A, t, u)`: a proposition; the state is the one it started from. -/
theorem fund_id (A t u : Term) : Fund K ρ φ (.id A t u) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  simp only [Bind.bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  obtain ⟨-, h⟩ := open Classical in ite_none_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨.inl (ty_univ0_mem _), (fun l h' => by cases h'), (fun l h' => by cases h'), hs⟩

/-- A Π-type: its code at its declared sort; the state unchanged. -/
theorem fund_pi (hs : List Hint) (ds : List Term) (c : Term) : Fund K ρ φ (.pi hs ds c) := fun tl hint => by
  intro s s' r hs' h
  rw [runT] at h
  obtain ⟨-, h⟩ := open Classical in ite_none_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨goodRes_pi _ _ _, (fun l h' => by cases h'), (fun l h' => by cases h'), hs'⟩

theorem runParamsS_state (d : IndDecl) : ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s s' : SState)
    (ps : List Sem), runParams K ρ φ d i earlier args s = some (ps, s') → s' = s
  | [], i, earlier, s, s', ps, h => by
    simp only [runParams] at h
    exact (Prod.mk.inj (SM.pure_some h)).2
  | a :: as, i, earlier, s, s', ps, h => by
    simp only [runParams] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    have e1 := SM.onCopy_state h1
    subst e1
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    have e2 := runParamsS_state d as _ _ _ _ _ h3
    subst e2
    exact (Prod.mk.inj (SM.pure_some h4)).2

/-- `D(ā)`: the declaration's code at its sort (not `Type₁`); the parameters run on copies. -/
theorem fund_tind (hc : FundCtx K) (n : String) (args : List Term) : Fund K ρ φ (.tind n args) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  cases hd : K.Γ.find? (·.name == n) with
  | none => simp only [hd] at h; cases h
  | some d =>
    simp only [hd] at h
    obtain ⟨psM, s₁, h1, h2⟩ := SM.bind_some h
    have e := runParamsS_state d args 0 [] s s₁ psM h1
    subst e
    obtain ⟨-, h2⟩ := open Classical in ite_none_some h2
    simp only [Option.some.injEq] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨goodRes_tyR K.dm d _ (hc.sorts d (List.mem_of_find?_eq_some hd)), (fun l h' => by cases h'),
      (fun l h' => by cases h'), hs⟩

/-- The tail of a strict clause that runs one subterm and returns a label-free result built from it. -/
theorem presLab_bind_pure {x : SM Res} (hx : FundAt K.dm K.Γ φ x) (g : Res → Res) (hg : ∀ r, (g r).2.label = none) :
    PresLab K.dm K.Γ φ (x >>= fun r => pure (g r)) := by
  intro s s' r hs h
  obtain ⟨a, s₁, h1, h2⟩ := SM.bind_some h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h2)
  exact ⟨(fun l h' => by rw [hg] at h'; cases h'), (fun l h' => by rw [hg] at h'; cases h'), (hx s _ a hs h1).2.2.2⟩

/-- `&A`: strict at `Type₀`; the state is `A`'s run's. -/
theorem fund_ref {A : Term} (hA : Fund K ρ φ A) : Fund K ρ φ (.ref A) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  exact fund_erasedS (fund_strictS (presLab_bind_pure (hA false _) (fun r => (r.1, .plain (TyM.univ 1)))
    (fun _ => rfl))) s s' r hs h

/-- `S(u)`: strict at `Nat`. -/
theorem fund_succ {u : Term} (hu : Fund K ρ φ u) : Fund K ρ φ (.succ u) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  exact fund_erasedS (fund_strictS (presLab_bind_pure (hu false _) (fun r => (r.1.succ, .plain TyM.nat))
    (fun _ => rfl))) s s' r hs h

/-- `(u : A)`: strict at the annotation, the result's label at it; the state is `u`'s run's. -/
theorem fund_ascribe {u A : Term} (hu : Fund K ρ φ u) : Fund K ρ φ (.ascribe u A) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS (fund_strictS ?_) s s' r hs h
  intro s₀ s₁ r₀ hs₀ h₀
  obtain ⟨x, s₂, h1, h2⟩ := SM.bind_some h₀
  have e := SM.onCopy_state h1
  subst e
  obtain ⟨y, s₃, h3, h4⟩ := SM.bind_some h2
  obtain ⟨-, hlab, hlou, hs₃⟩ := hu false _ _ _ _ hs₀ h3
  obtain ⟨ht, h4⟩ := open Classical in ite_none_some h4
  simp only [Option.some.injEq] at h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
  exact ⟨fun l hl => ⟨ht l hl, (hlab l hl).2⟩, hlou, hs₃⟩

/-- The four equality rules (decision 1): the premise proofs run on a copy; `⋆` at `prop True`. -/
theorem fund_premises (xs : List Term) (x : SM Res)
    (hx : x = SM.onCopy (xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k)
      (pure (.proof, .plain (TyM.prop True))))) : FundAt K.dm K.Γ φ x := by
  subst hx
  refine fund_onCopy fun s s' r h => ?_
  induction xs generalizing s with
  | nil => obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h); exact ⟨.inl (proof_mem_true _), rfl⟩
  | cons t ts ih =>
    obtain ⟨a, s₁, -, h2⟩ := SM.bind_some h
    exact ih s₁ h2

theorem fund_cong (f h : Term) : Fund K ρ φ (.cong f h) := fun tl hint =>
  fund_premises [h] _ rfl

theorem fund_symm (h : Term) : Fund K ρ φ (.prim "symm" [h]) := fun tl hint =>
  fund_premises [h] _ rfl

theorem fund_trans (h k : Term) : Fund K ρ φ (.prim "trans" [h, k]) := fun tl hint =>
  fund_premises [h, k] _ rfl

theorem fund_rewrite (h u : Term) : Fund K ρ φ (.prim "rewrite" [h, u]) := fun tl hint =>
  fund_premises [h, u] _ rfl

theorem fund_rewriteR (h u : Term) : Fund K ρ φ (.prim "rewriteR" [h, u]) := fun tl hint =>
  fund_premises [h, u] _ rfl

/-- A place read (copy or move): `readPlace_fund_all`. -/
theorem fund_place (_hc : FundCtx K) (p : Place) : Fund K ρ φ (.place p) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  exact fund_erasedS (readPlace_fund_all p _) s s' r hs h

/-- `&p` (strict at the place's type, then D112's invalidation and the strict test below a root):
`borrow_fund`. -/
theorem fund_borrow (_hc : FundCtx K) (p : Place) : Fund K ρ φ (.borrow p) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  exact fund_erasedS (borrow_fund p) s s' r hs h

theorem assignAt_res {p : Place} {v : Sem} {lab : Option Nat} {s s' : SState} {r : Res}
    (h : assignAt K φ p v lab s = some (r, s')) : r = (.el0 Unit (), .plain TyM.unit) := by
  unfold assignAt at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; exact (Prod.mk.inj h).1.symm

/-- `p := u` (strict: the value and its label at the place's type at the write; then D112's
invalidation and the strict test below a root): `assign_tail_fund`. -/
theorem fund_assign (_hc : FundCtx K) {p : Place} {u : Term} (hu : Fund K ρ φ u) : Fund K ρ φ (.assign p u) :=
    fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₄ r₀ hs₀ h₀
  simp only [Bind.bind, Option.bind_eq_some_iff] at h₀
  obtain ⟨⟨⟨v, R'⟩, s₁⟩, h2, h₀⟩ := h₀
  dsimp only at h₀
  obtain ⟨⟨hmem, hl⟩, h₀⟩ := open Classical in ite_none_some h₀
  obtain ⟨-, hlab, hlou, hs₁⟩ := hu false _ _ _ _ hs₀ h2
  exact assign_tail_fund hs₁ hmem hl hlab hlou h₀

theorem statePres_stmtIf {b : Bool} {x : SM Res} (hx : StatePres K.dm K.Γ φ x) :
    StatePres K.dm K.Γ φ (SM.stmtIf b x) := by
  intro s s' r hs h
  rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, hss, -⟩
  · exact hx s s' r hs h
  · exact hss ▸ hs

theorem runFieldsS_pres (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term), (∀ a ∈ args, Fund K ρ φ a) → ∀ (i : Nat) (rh : Option Rec) (sol : List (Option Sem))
      (earlier : List Sem), StatePres K.dm K.Γ φ (runFields K ρ φ stmt d c i rh sol earlier args)
  | [], _, i, rh, sol, earlier, s, s', fs, hs, h => by
    simp only [runFields] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact hs
  | a :: as, ha, i, rh, sol, earlier, s, s', fs, hs, h => by
    simp only [runFields] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hs₁ := statePres_stmtIf ((ha a (List.mem_cons_self ..) false _).pres) s s₁ x hs h1
    exact runFieldsS_pres stmt d c as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ _ _ _ s₁ _ y hs₁ h3

theorem runArgsS_pres (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term), (∀ a ∈ args, Fund K ρ φ a) → ∀ (earlier : List Sem),
      StatePres K.dm K.Γ φ (runArgs K ρ φ stmt fT earlier args)
  | [], _, earlier, s, s', rs, hs, h => by
    simp only [runArgs] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact hs
  | a :: as, ha, earlier, s, s', rs, hs, h => by
    simp only [runArgs] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hs₁ := statePres_stmtIf ((ha a (List.mem_cons_self ..) false _).pres) s s₁ x hs h1
    exact runArgsS_pres stmt fT as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ s₁ _ y hs₁ h3

/-- **A constructor** (`C(ā; t̄)`; a proof at a `Prop`-sorted declaration, `refl` = `True`'s `I`
included): the parameters run on copies, the fields keep the invariant, and the value built is a
member of its type by the strict test (`CtorMem.ctorOut_mem` discharges it: fields that fit). -/
theorem fund_ctor {ty : String} {c : Nat} {x : Hint} {ps args : List Term}
    (hargs : ∀ a ∈ args, Fund K ρ φ a) : Fund K ρ φ (.ctor ty c x ps args) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  cases hd : K.Γ.find? (·.name == ty) with
  | none => simp only [hd] at h₀; cases h₀
  | some d =>
    simp only [hd] at h₀
    obtain ⟨psM, s₁, h1, h2⟩ := SM.bind_some h₀
    have e := runParamsS_state d ps 0 [] s₀ s₁ psM h1
    subst e
    obtain ⟨⟨fs, sol⟩, s₂, h3, h4⟩ := SM.bind_some h2
    have hs₂ := runFieldsS_pres _ d c args hargs 0 _ _ [] _ s₂ _ hs₀ h3
    obtain ⟨-, h4⟩ := open Classical in ite_none_some h4
    obtain ⟨h5, hm⟩ := strictS_some h4
    obtain ⟨hss, rr, -, hr⟩ := ctorOut_inv h5
    rw [hss]
    refine ⟨.inl hm, fun l h' => ?_, fun l h' => ?_, hs₂⟩ <;> (rw [hr] at h'; cases h')

end

section
open SState
universe u

/-- A call's result label (a returned borrow's, parked) is live, or nothing reads it. -/
theorem callOfLS_lou (Lv : Lvl.{u}) {C : Type u} (t : Tel Lv.Code PUnit C) (fv : Sem) (args : List Res)
    {s s' : SState} {r : Res} (hsa : ShapeAt s) (h : callOfL Lv t fv args s = some (r, s')) : LoU s' r.2.label := by
  cases happ : applyFnL Lv t fv (args.map (·.1)) with
  | none => unfold callOfL at h; dsimp only at h; rw [happ] at h; cases h
  | some res =>
    cases res with
    | data r' T' finals =>
      unfold callOfL at h; dsimp only at h; rw [happ] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun l hl => by simp [TyS.plain] at hl
    | ref U c fwd back =>
      unfold callOfL at h; dsimp only at h; rw [happ] at h
      simp only [SState.freshLoan, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [lou_setHeldMem, lou_setHeldTy, lou_setLent]
      generalize hS : (SState.mapVals _ _ : SState) = S
      have hsaS : ShapeAt S := by
        rw [← hS]
        apply shapeAt_mapVals
        intro p x hp
        obtain ⟨h1', h2'⟩ := shapeAt_takeAll _ hsa p x hp
        exact ⟨h1', Nat.lt_succ_of_lt h2'⟩
      have hnlS : S.nextLoan = (List.foldl SState.takeLabel s
          (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2) (args.zip (telRefsL Lv t (args.map (·.1)))))))).nextLoan + 1 := by
        rw [← hS]; rfl
      by_cases hne : S.env = []
      · have hfin : S.pushTempShaped (fun _ => Lv.enc c fwd) (List.foldl SState.takeLabel s
            (List.filterMap id (List.map (fun x => x.1.2.label) (List.filter (fun x => x.2) (args.zip (telRefsL Lv t (args.map (·.1)))))))).nextLoan
            = S.pushTemp (fun _ => Lv.enc c fwd) := by
          unfold SState.pushTempShaped
          dsimp only
          rw [pushTemp_getLast, hne]; rfl
        rw [hfin]
        have hnil : (S.pushTemp (fun _ => Lv.enc c fwd)).env = [] := by simp [SState.pushTemp, hne]
        intro l hl
        simp only [Option.some.injEq] at hl
        subst hl
        refine ⟨.inr fun q => indep_of_nil hnil _ q, ?_⟩
        show _ < (SState.pushTemp _ _).nextLoan
        rw [show (SState.pushTemp S _).nextLoan = S.nextLoan from rfl, hnlS]
        exact Nat.lt_succ_self _
      · intro l hl
        simp only [Option.some.injEq] at hl
        subst hl
        exact lou_live (pushTempShaped_shapeAt hsaS hne _ _ (by rw [hnlS]; exact Nat.lt_succ_self _))
          (live_pushTempShaped_self _ _ _ hne)

theorem callOfS_lou {R : DataRead} {fv : Res} {as : List Res} {s s' : SState} {r : Res} (hsa : ShapeAt s)
    (h : callOf R fv as s = some (r, s')) : LoU s' r.2.label := by
  rcases fv with ⟨fv, ⟨T, lab⟩⟩
  unfold callOf at h
  cases T with
  | t0 A c => cases c with
    | pi C t => dsimp only at h; exact callOfLS_lou (lvl0 R) t fv as hsa h
    | _ => cases h
  | t1 A c => cases c with
    | pi C t => dsimp only at h; exact callOfLS_lou (lvl1 R) t fv as hsa h
    | _ => cases h
  | t2 A c => cases c with
    | pi C t => dsimp only at h; exact callOfLS_lou (lvl2 R) t fv as hsa h
    | _ => cases h

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem headOf_some' {f : Term} {rd : Place → SM Res} {rn : SM Res} {s s' : SState} {r : Res}
    (h : SM.headOf f rd rn s = some (r, s')) : (∃ p, f = .place p ∧ rd p s = some (r, s')) ∨ rn s = some (r, s') := by
  cases f <;> first | exact .inr h | exact .inl ⟨_, rfl, h⟩

/-- **A call**: the head (a place read in place, or a run), the arguments, then the application: its
result is a member of the type it is given (`callOf_res_mem`, from `ApplyMem.app_mem'`), the state is
`callOfS_sgood`'s, a returned borrow's label is parked (`callOfS_lou`). -/
theorem fund_call (_hc : FundCtx K) {f : Term} {args : List Term} {hd : Bool} (hf : Fund K ρ φ f)
    (hargs : ∀ a ∈ args, Fund K ρ φ a) : Fund K ρ φ (.call f args hd) := fun tl hint => by
  intro s s' r hs h
  rw [runT] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  obtain ⟨fv, s₁, h1, h2⟩ := SM.bind_some h₀
  have hfv : GoodRes K.dm.read fv ∧ SGood K.dm K.Γ φ s₁ := by
    rcases headOf_some' h1 with ⟨p, -, h1⟩ | h1
    · obtain ⟨hg, -, -, hs'⟩ := readPlace_fund_all p true s₀ s₁ fv hs₀ h1; exact ⟨hg, hs'⟩
    · obtain ⟨hg, -, -, hs'⟩ := hf false _ s₀ s₁ fv hs₀ h1; exact ⟨hg, hs'⟩
  obtain ⟨as, s₂, h3, h4⟩ := SM.bind_some h2
  have hs₂ := runArgsS_pres _ _ args hargs [] s₁ s₂ as hfv.2 h3
  obtain ⟨ht, h5⟩ := open Classical in ite_none_some h4
  obtain ⟨s₄, h6⟩ := callOfS_res h5
  obtain ⟨hlab, hs₃⟩ := callOfS_sgood hs₂ hfv.1 ht h5
  exact ⟨.inl (callOf_res_mem hfv.1 h6), hlab, callOfS_lou hs₂.acyc.2.2 h5, hs₃⟩

end

end Ochr.Meaning.Strict
