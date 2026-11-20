import Ochr.Meaning.Strict.Call

/-!
# The fundamental lemma: the induction's cases (prototype)

Each case is stated as "the lemma at the subterms gives the lemma at the term" (`Fund` of the
subterms as hypotheses), which is the shape of the one induction over the run. The combinators first:
a strict clause (`fund_strictS`) owes only the invariant, its result being a member by its test; an
erased term (`fund_erasedS`) owes the lemma of its clause, and its result is `⋆` at a true
proposition.
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning

section
variable {R : DataRead} {Γ : List IndDecl}

theorem strictS_some {x : SM Res} {s s' : SState} {r : Res} (h : SM.strictS R x s = some (r, s')) :
    x s = some (r, s') ∧ r.1 ∈ₛ[R] r.2.m := by
  unfold SM.strictS at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p =>
    rw [hx] at h
    obtain ⟨r0, s0⟩ := p
    simp only at h
    by_cases hm : r0.1 ∈ₛ[R] r0.2.m
    · rw [if_pos hm] at h; cases h; exact ⟨rfl, hm⟩
    · rw [if_neg hm] at h; cases h

/-- **A strict clause**: its result is a member by its test, so it owes only the invariant. -/
theorem fund_strictS (hR : R.WholeFields) {x : SM Res} (hx : StatePres R Γ x) : FundAt R Γ (SM.strictS R x) := by
  intro s s' r hs h
  obtain ⟨h, hm⟩ := strictS_some h
  exact ⟨goodRes_of_mem hR Γ hm, hx s s' r hs h⟩

/-- An erased proof's run, taken apart: the clause ran (on a copy) to `⋆` at a proposition. -/
theorem erasedS_proof_some {fl : Bool × Bool} {x : SM Res} {s s' : SState} {r : Res} (hp : fl.2 = true)
    (h : SM.erasedS fl x s = some (r, s')) :
    ∃ T s₁, x s = some ((.proof, T), s₁) ∧ T.m.level = some 0 ∧ r = (.proof, .plain T.m) ∧ s' = s := by
  unfold SM.erasedS at h
  rw [if_pos hp] at h
  cases hx : x s with
  | none => rw [hx] at h; cases h
  | some p =>
    rw [hx] at h
    obtain ⟨⟨v, T⟩, s₁⟩ := p
    simp only at h
    by_cases ht : v.isProof = true ∧ T.m.level = some 0
    · rw [if_pos ht] at h
      cases h
      have hv : v = .proof := by cases v <;> simp_all [Sem.isProof]
      subst hv
      exact ⟨T, s₁, rfl, ht.2, rfl, rfl⟩
    · rw [if_neg ht] at h; cases h

/-- **A proof's run means its proposition is true** (C1): where the clause obeys the lemma, an erased
proof that runs returns `⋆` at a proposition of which `⋆` is a member, i.e. a true one. -/
theorem erasedS_true {fl : Bool × Bool} {x : SM Res} (hx : FundAt R Γ x) (hp : fl.2 = true)
    {s s' : SState} {r : Res} (hs : SGood R Γ s) (h : SM.erasedS fl x s = some (r, s')) :
    r.1 = .proof ∧ Sem.proof ∈ₛ[R] r.2.m ∧ r.2.m.level = some 0 := by
  obtain ⟨T, s₁, hx₁, hl, rfl, -⟩ := erasedS_proof_some hp h
  refine ⟨rfl, ?_, hl⟩
  rcases (hx s s₁ _ hs hx₁).1 with hg | hg
  · exact mem_of_pmem_proof hg
  · exact absurd hl (by simp only at hg; rw [hg]; decide)

/-- **An erased term** owes its clause's lemma: a proof's result is `⋆` at a true proposition and
the state is unchanged; a statement's is its clause's, label dropped, the state unchanged. -/
theorem fund_erasedS {fl : Bool × Bool} {x : SM Res} (hx : FundAt R Γ x) : FundAt R Γ (SM.erasedS fl x) := by
  intro s s' r hs h
  by_cases hp : fl.2 = true
  · obtain ⟨-, hm, -⟩ := erasedS_true hx hp hs h
    obtain ⟨T, s₁, -, -, rfl, hss⟩ := erasedS_proof_some hp h
    exact ⟨.inl (DataModel.pmem_of_mem R Γ (by simp [Sem.whole]) hm), hss ▸ hs⟩
  · have h' : SM.stmtIf fl.1 x s = some (r, s') := by
      unfold SM.erasedS at h; rw [if_neg hp] at h; exact h
    rcases SM.stmtIf_some h' with ⟨-, h'⟩ | ⟨-, hss, -, r₀, s₀, h0, rfl⟩
    · exact hx s s' r hs h'
    · exact ⟨(hx s s₀ r₀ hs h0).1, hss ▸ hs⟩

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **Ascription** (`(u : A)`): its result is a member of `A` by the strict test; the annotation
runs on a copy; the state is `u`'s. -/
theorem fund_ascribe (hR : K.dm.read.WholeFields) {u A : Term} (hu : Fund K ρ φ u) :
    Fund K ρ φ (.ascribe u A) := by
  intro tl hint s s' r hs h
  rw [runS] at h
  refine fund_erasedS (fund_strictS hR ?_) s s' r hs h
  intro s₀ s₁ r₀ hs₀ h₀
  obtain ⟨x, s₂, h1, h2⟩ := SM.bind_some h₀
  have e := SM.onCopy_state h1
  subst e
  obtain ⟨y, s₃, h3, h4⟩ := SM.bind_some h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
  exact (hu _ _ _ _ _ hs₀ h3).2

theorem ite_none_some {α : Type _} {p : Prop} [Decidable p] {a : Option α} {b : α}
    (h : (if p then a else none) = some b) : p ∧ a = some b := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact ⟨hp, h⟩
  · rw [if_neg hp] at h; cases h

theorem follow_deref (T : TyS) (x : Sem) : Sem.follow K.dm K.Γ T x [.deref] = some (x, T) := rfl

theorem updAt_deref (T : TyS) (v x : Sem) : Sem.updAt K.dm K.Γ T (fun _ => v) [.deref] x = some v := rfl

/-- **An assignment through a borrow** (`*r := u`, the place's path `[*]`): the right-hand side's
lemma, then [Access] (`access_sgood`), then the write of the holder's content whole with a
member of its stored type (the strict test, at the place's type at the write, `placeTy`), which
`sgood_setAt_const` shows keeps the invariant. The result is `()`. -/
theorem fund_assign_deref (hR : K.dm.read.WholeFields) {p : Place} {u : Term} (hp : p.steps.2 = [.deref])
    (hu : Fund K ρ φ u) : Fund K ρ φ (.assign p u) := by
  intro tl hint s s' r hs h
  rw [runS] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₄ r₀ hs₀ h₀
  simp only [Bind.bind, Option.bind_eq_some_iff] at h₀
  obtain ⟨⟨⟨v, R'⟩, s₁⟩, h2, h₀⟩ := h₀
  dsimp only at h₀
  obtain ⟨hmem, h₀⟩ := open Classical in ite_none_some h₀
  have hs₁ := (hu _ _ _ _ _ hs₀ h2).2
  have hres : resolve s₁ p = (s₁.varPos p.steps.1).map (·, [.deref]) := by
    unfold resolve; rw [← hp]
  cases hv : s₁.varPos p.steps.1 with
  | none =>
    rw [hv] at hres
    unfold assignAt at h₀; rw [hres] at h₀; cases h₀
  | some pos =>
    rw [hv] at hres
    simp only [Option.map_some] at hres
    obtain ⟨f, i, rfl⟩ : ∃ f i, pos = .bind f i := by
      have := varPos_bind hv
      cases pos with
      | bind f i => exact ⟨f, i, rfl⟩
      | temp => exact absurd this (by simp [IsTemp])
    -- the strict test read the place's stored type at the write
    have hT : (placeTy K φ p s₁).m = (s₁.tyAt (.bind f i)).m := by
      unfold placeTy contentOf; rw [hres]; rfl
    rw [hT] at hmem
    unfold assignAt at h₀
    rw [hres] at h₀
    simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false] at h₀
    unfold setContent at h₀
    simp only [updAt_deref, Option.some.injEq, Prod.mk.injEq] at h₀
    obtain ⟨rfl, rfl⟩ := h₀
    refine ⟨goodRes_of_mem hR K.Γ ⟨(), rfl⟩, ?_⟩
    have hs₂ := access_sgood hR hs₁ (.bind f i) (dataHit [.deref])
    have hgoal : SGood K.dm.read K.Γ ((s₁.access (.bind f i) (dataHit [.deref])).setAt (.bind f i)
        fun _ => v) := sgood_setAt_const hR hs₂ (by rw [tyAt_access]; exact hmem)
    cases R'.label <;> exact hgoal

/-! ### Lists of subterms: parameters (on copies), fields, arguments -/

theorem statePres_stmtIf {b : Bool} {x : SM Res} (hx : StatePres K.dm.read K.Γ x) :
    StatePres K.dm.read K.Γ (SM.stmtIf b x) := by
  intro s s' r hs h
  rcases SM.stmtIf_some h with ⟨-, h⟩ | ⟨-, hss, -⟩
  · exact hx s s' r hs h
  · exact hss ▸ hs

theorem runParamsS_state (d : IndDecl) : ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s s' : SState)
    (ps : List Sem), runParamsS K ρ φ d i earlier args s = some (ps, s') → s' = s
  | [], i, earlier, s, s', ps, h => by
    simp only [runParamsS] at h
    exact (Prod.mk.inj (SM.pure_some h)).2
  | a :: as, i, earlier, s, s', ps, h => by
    simp only [runParamsS] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    have e1 := SM.onCopy_state h1
    subst e1
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    have e2 := runParamsS_state d as _ _ _ _ _ h3
    subst e2
    exact (Prod.mk.inj (SM.pure_some h4)).2

theorem runFieldsS_pres (stmt : Bool) (d : IndDecl) (c : Nat) :
    ∀ (args : List Term), (∀ a ∈ args, Fund K ρ φ a) → ∀ (i : Nat) (rh : Option Rec) (sol : List (Option Sem))
      (earlier : List Sem), StatePres K.dm.read K.Γ (runFieldsS K ρ φ stmt d c i rh sol earlier args)
  | [], _, i, rh, sol, earlier, s, s', fs, hs, h => by
    simp only [runFieldsS] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact hs
  | a :: as, ha, i, rh, sol, earlier, s, s', fs, hs, h => by
    simp only [runFieldsS] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hs₁ := statePres_stmtIf ((ha a (List.mem_cons_self ..) false _).pres) s s₁ x hs h1
    exact runFieldsS_pres stmt d c as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ _ _ _ s₁ _ y hs₁ h3

theorem runArgsS_pres (stmt : Bool) (fT : TyM) :
    ∀ (args : List Term), (∀ a ∈ args, Fund K ρ φ a) → ∀ (earlier : List Sem),
      StatePres K.dm.read K.Γ (runArgsS K ρ φ stmt fT earlier args)
  | [], _, earlier, s, s', rs, hs, h => by
    simp only [runArgsS] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h)
    exact hs
  | a :: as, ha, earlier, s, s', rs, hs, h => by
    simp only [runArgsS] at h
    obtain ⟨x, s₁, h1, h2⟩ := SM.bind_some h
    obtain ⟨y, s₂, h3, h4⟩ := SM.bind_some h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (SM.pure_some h4)
    have hs₁ := statePres_stmtIf ((ha a (List.mem_cons_self ..) false _).pres) s s₁ x hs h1
    exact runArgsS_pres stmt fT as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) _ s₁ _ y hs₁ h3

/-- **A constructor** (`C(ā; t̄)`; at a `Prop`-sorted declaration a proof, so `refl`, `True`'s `I`,
is this case under `SM.erasedS`): the parameters run on copies, the fields keep the invariant by
their lemmas, and the value built is a member of its type by the strict test (which the simulation
discharges by `CtorMem.ctorOut_mem`: fields that fit). -/
theorem fund_ctor (hR : K.dm.read.WholeFields) {ty : String} {c : Nat} {x : Hint} {ps args : List Term}
    (hargs : ∀ a ∈ args, Fund K ρ φ a) : Fund K ρ φ (.ctor ty c x ps args) := by
  intro tl hint s s' r hs h
  rw [runS] at h
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
    obtain ⟨h5, hm⟩ := strictS_some h4
    obtain ⟨rfl, -⟩ := ctorOut_inv h5
    exact ⟨goodRes_of_mem hR K.Γ hm, hs₂⟩

/-- The typed future of a good state is typed: each live label reads its record. -/
theorem typedF_typedFuture (hR : K.dm.read.WholeFields) {s : SState} (hs : SGood K.dm.read K.Γ s) :
    TypedF K.dm.read K.Γ s (s.typedFuture φ) := by
  intro l hl
  show DataModel.pmem _ _ (if l ∈ s.liveLabels then s.heldMem l else φ l) _
  rw [if_pos hl]
  exact DataModel.pmem_of_mem _ _ (mem_whole hR (hs.held l hl)) (hs.held l hl)

/-- **A read of a variable in place** (`readPlace … true` at a root path, a call's head): the state
after is [Access]'s (`access_sgood`), and the value read is the binding's at the typed future
`typedFuture φ` (typed: each live label its record), so `bind` gives it. A read at a FIELD path is
open: a field of a value open in its type (`pmem` admits `OpenIn`: any whole fields) is not shown a
member of the type the read gives it (`Strict/HANDOFF.md`). -/
theorem readPlace_root_fund (hR : K.dm.read.WholeFields) {p : Place} (hp : p.steps.2 = []) :
    FundAt K.dm.read K.Γ (readPlace K φ p true) := by
  intro s s' r hs h
  unfold readPlace at h
  simp only [Bind.bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨⟨v, T, pos, steps⟩, s₁⟩, h1, h2⟩ := h
  have hres : resolve s p = (s.varPos p.steps.1).map (·, []) := by unfold resolve; rw [← hp]
  unfold contentOf at h1
  rw [hres] at h1
  cases hv : s.varPos p.steps.1 with
  | none => rw [hv] at h1; cases h1
  | some pos₀ =>
    rw [hv] at h1
    simp only [Option.map_some] at h1
    obtain ⟨f, i, rfl⟩ : ∃ f i, pos₀ = .bind f i := by
      have := varPos_bind hv
      cases pos₀ with
      | bind f i => exact ⟨f, i, rfl⟩
      | temp => exact absurd this (by simp [IsTemp])
    simp only [Sem.follow, List.isEmpty_nil, if_true, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h1
    have hs₁ := access_sgood hR hs (.bind f i) (dataHit [])
    dsimp only at h2
    generalize hs₁e : s.access (Pos.bind f i) (dataHit []) = s₁ at h2 hs₁
    by_cases hw : (s₁.valAt (.bind f i) (s₁.typedFuture φ)).whole
    · rw [if_neg (fun hn => hn hw), if_pos trivial] at h2
      simp only [Option.some.injEq] at h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      exact ⟨hs₁.bind _ (typedF_typedFuture hR hs₁) f i, hs₁⟩
    · rw [if_pos hw] at h2; cases h2

theorem headOf_some' {f : Term} {rd : Place → SM Res} {rn : SM Res} {s s' : SState} {r : Res}
    (h : SM.headOf f rd rn s = some (r, s')) : (∃ p, f = .place p ∧ rd p s = some (r, s')) ∨ rn s = some (r, s') := by
  cases f <;> first | exact .inr h | exact .inl ⟨_, rfl, h⟩

/-- **GUESS (not proved): a call keeps the invariant**, where each borrow argument's label holds its
parameter's content type (the strict test). The consumed holders read `⊥`; every position reads its
old meaning at the future with the consumed labels fixed to the finals, which are members of the
parameters' content types (`ApplyMem.app_mem_finals`), so of the labels' (`BorrowArgsTyped`): a typed
future of the state before. At a returned borrow `k`, a typed future gives `k` a partly moved member;
where it decodes, the finals are the backward function's (members, as `app_mem_finals`); where it
does not, the repaired `callOfLS` fixes them to `⊥` (with `callOfL`'s `err` this is FALSE). -/
theorem callOfS_sgood {fv : Res} {as : List Res} {s s' : SState} {r : Res} (hs : SGood K.dm.read K.Γ s)
    (hf : GoodRes K.dm.read K.Γ fv) (ht : BorrowArgsTyped K.dm.read fv as s)
    (h : callOfS K.dm.read fv as s = some (r, s')) : SGood K.dm.read K.Γ s' := by
  sorry

/-- **A call**: the head (a variable read in place, `readPlace_root_fund`, or a run, its lemma; a head
read at a field path is the open read case), the arguments (their lemmas), then the application: its
result is a member of the type it is given (`callOf_res_mem`, from `ApplyMem.app_mem'`), and the
state is `callOfS_sgood`'s (a guess). -/
theorem fund_call {f : Term} {args : List Term} {hd : Bool} (hf : Fund K ρ φ f)
    (hroot : ∀ p, f = .place p → p.steps.2 = [])
    (hargs : ∀ a ∈ args, Fund K ρ φ a) (hR : K.dm.read.WholeFields) : Fund K ρ φ (.call f args hd) := by
  intro tl hint s s' r hs h
  rw [runS] at h
  refine fund_erasedS ?_ s s' r hs h
  intro s₀ s₃ r₀ hs₀ h₀
  obtain ⟨fv, s₁, h1, h2⟩ := SM.bind_some h₀
  have hfv : GoodRes K.dm.read K.Γ fv ∧ SGood K.dm.read K.Γ s₁ := by
    rcases headOf_some' h1 with ⟨p, hfp, h1⟩ | h1
    · exact readPlace_root_fund hR (hroot p hfp) s₀ s₁ fv hs₀ h1
    · exact hf false _ s₀ s₁ fv hs₀ h1
  obtain ⟨as, s₂, h3, h4⟩ := SM.bind_some h2
  have hs₂ := runArgsS_pres _ _ args hargs [] s₁ s₂ as hfv.2 h3
  obtain ⟨ht, h5⟩ := open Classical in ite_none_some h4
  obtain ⟨s₄, h6⟩ := callOfS_res h5
  exact ⟨goodRes_of_mem hR K.Γ (callOf_res_mem hfv.1 h6), callOfS_sgood hs₂ hfv.1 ht h5⟩

end

end Ochr.Meaning.Strict
