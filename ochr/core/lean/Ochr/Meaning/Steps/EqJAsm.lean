import Ochr.Meaning.Steps.IH

/-!
# `Eq` and `J`, assembled from named obligations (docs/31 D75; area (e))

`Eq(A, a, b)` (`evalCore`'s `.eq`): on a private copy, the type (`evalType`), each side on a copy
of its own (`inStatement (eval …)`), the sides checked at the type (typed), then `mkEqM`. The
reference (`run`'s `.eq` clause) runs the same on copies and returns `⟦a⟧ = ⟦b⟧`. `J(A, a, b, P, h,
t)`: its statement positions on copies; at convertible endpoints the transported term runs at the
join's grain after its entry (`blockEntry`, static ends rule 2); at others (typed) it is closed off
as a stuck block whose one arm is the transported term ([T-J-stuck], `closeBlock`). The reference
runs the transported term whatever the endpoints ([J-run]).

Every piece but the transported term and the block is a PRIVATE computation (`KeptAfter`, `ExtOk`):
Ω is the snapshot's, the tables grow, the state after is good under an extension. The chain of
extensions composes (`ExtOk.trans`, proved); the relation survives each (`Rel.kept`, a leaf).
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! ### Private computations compose -/

theorem KeptAfter.trans {st₁ st₂ st₃ : MState} (h₁ : KeptAfter st₁ st₂) (h₂ : KeptAfter st₂ st₃) :
    KeptAfter st₁ st₃ := by
  obtain ⟨e1, g1, r1, i1, s1, t1, n1⟩ := h₁
  obtain ⟨e2, g2, r2, i2, s2, t2, n2⟩ := h₂
  refine ⟨e2.trans e1, g2.trans g1, r2.trans r1, i2.trans i1, Nat.le_trans s1 s2, fun σ hσ => ?_,
    Nat.le_trans n1 n2⟩
  rw [t2 σ (Nat.lt_of_lt_of_le hσ s1), t1 σ hσ]

theorem KeptAfter.refl (st : MState) : KeptAfter st st :=
  ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _⟩

/-- An extension of an extension is an extension. -/
theorem ExtOk.trans {st₁ st₂ st₃ : MState} {ρ₂ ρ₃ : Assignment} {Δ₂ Δ₃ : Nat → TyS}
    (hk : KeptAfter st₁ st₂) (h₁ : ExtOk K ρ st₁ st₂ ρ₂ Δ₂)
    (h₂ : ExtOk { K with Δ := Δ₂ } ρ₂ st₂ st₃ ρ₃ Δ₃) : ExtOk K ρ st₁ st₃ ρ₃ Δ₃ := by
  obtain ⟨a1, -, -⟩ := h₁
  obtain ⟨a2, c2, g2⟩ := h₂
  refine ⟨fun σ hσ => ?_, c2, g2⟩
  have hσ2 : σ < st₂.absTy.size := Nat.lt_of_lt_of_le hσ hk.2.2.2.2.1
  exact ⟨(a2 σ hσ2).1.trans (a1 σ hσ).1, (a2 σ hσ2).2.trans (a1 σ hσ).2⟩

/-! ### Leaves shared by both forms -/

/-- **The relation survives a private computation** (leaf; `Sim.Rel.private_copy` with the context
extended): Ω is the snapshot's, so every position means what it meant (its values name only old
unknowns, (WF6), where the extension agrees), and no label issued inside occurs after it; the
reference state is untouched and the renaming the same. -/
theorem Rel.kept {st st' : MState} {s : SState} {π : Nat → Nat} {ρ' : Assignment} {Δ' : Nat → TyS}
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s)
    (hk : KeptAfter st st') (he : ExtOk K ρ st st' ρ' Δ') :
    Rel { K with Δ := Δ' } ρ' φ π st' s := by
  sorry

/-- **A value that holds no loan, in flight** (leaf): counted as a temporary it changes neither the
relation (temporaries are matched by the borrows they hold) nor `Good` (it is typed by nothing and
holds no label), and the flight of a result type with no label is empty. -/
theorem inFlight_noLoan {st : MState} {s : SState} {π : Nat → Nat} (v : Value) (R : TyS)
    (hv : v.loans = []) (hR : R.label = none)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) :
    Rel K ρ φ π (st.withTemp v) s ∧ GoodF K.dm K.M K.Γ ρ (st.withTemp v) (flightOf R) := by
  sorry

/-- The state a statement position runs in (`inStatement`: a private copy, run as an erased term). -/
def copyEntry (st : MState) : MState :=
  { st with privateDepth := st.privateDepth + 1, erasedDepth := st.erasedDepth + 1 }

/-- The copy's entry keeps the tables. -/
theorem tablesGrow_copyEntry (st : MState) : TablesGrow st (copyEntry st) :=
  ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- **The copy's entry is the state** for everything the meaning, `CtxOk` and the relation read
(leaf: they read Ω, the tables, the records and the declarations, not the depths). -/
theorem copyEntry_ok {st : MState} {s : SState} {π : Nat → Nat}
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hs : Rel K ρ φ π st s) :
    Good K.dm K.M K.Γ ρ (copyEntry st) ∧ CtxOk K ρ (copyEntry st) ∧ Rel K ρ φ π (copyEntry st) s ∧
      (copyEntry st).absTy = st.absTy ∧ (copyEntry st).nextLoan = st.nextLoan ∧ (copyEntry st).env = st.env := by
  sorry

/-- **The copy restored** (leaf; `restoreKeep`, D37): the snapshot's Ω, goal, path condition and
declarations, the copy's counters, its records and the types of its new unknowns. Under an extension
for which the copy's end state (with whatever it held in flight) met `CtxOk` and was good, the
restored state does: the records the copy made are good there, and Ω's values are the snapshot's,
naming only old unknowns. -/
theorem restore_ext {st cur st' : MState} {b : Nat} {ρ' : Assignment} {Δ' : Nat → TyS}
    (hr : Runs (Ochr.restoreKeep st) cur b () st')
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hsz : st.absTy.size ≤ cur.absTy.size) (hn : st.nextLoan ≤ cur.nextLoan)
    (ha : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ)
    (hc : CtxOk { K with Δ := Δ' } ρ' cur)
    (hta : TypedAssignment K.dm ({ K with Δ := Δ' } : RunCtx).M K.Γ ρ' cur) :
    KeptAfter st st' ∧ ExtOk K ρ st st' ρ' Δ' := by
  sorry

/-- A value in flight adds unknowns to what the state names, never removes one: an assignment typed
with it counted is typed without it (leaf; `MState.Refd` is monotone in Ω's values). -/
theorem typedAssignment_of_withTemp {st : MState} {w : Value} {fl : Flight}
    (h : GoodF K.dm K.M K.Γ ρ (st.withTemp w) fl) : TypedAssignment K.dm K.M K.Γ ρ st := by
  sorry

/-! ### `Eq` -/

/-- The checks of `Eq`'s sides at the type (typed runs only). -/
def eqChecks (fuel : Nat) (typed : Bool) (Ta Tb : Option Value) (A' : Value) : M Unit :=
  if typed then do
    Ochr.expectTy fuel "the left side of Eq" Ta A'
    Ochr.expectTy fuel "the right side of Eq" Tb A'
  else pure ()

/-- The reference's `.eq` clause, whatever the tail flag (proved): the type, each side on a copy at
the type's code, the proposition that the sides' meanings are equal; the state untouched. -/
theorem runT_eq_some (tl : Bool) (hint : TyS) (A a b : Term) (s : SState) (rA ra rb : Res) (sa sb : SState)
    (hA : runT K ρ φ false (.plain .err) A s = some (rA, s))
    (ha : runT K ρ φ false (.plain .err) a s = some (ra, sa))
    (hb : runT K ρ φ false (.plain .err) b s = some (rb, sb))
    -- the strict `Eq` (model lane, "well typed inside"): its type is a type, its sides `⊥` or members
    (hok : EqOk K.dm.read rA.1 ra.1 rb.1) :
    runT K ρ φ tl hint (.eq A a b) s = some ((.ty (TyM.prop (ra.1 = rb.1)), .plain (TyM.univ 0)), s) := by
  cases tl <;> (rw [runT]; simp only [SM.onCopy, bind, hA, ha, hb, Option.map_some]; rw [if_pos hok]; rfl)

/-- **`Eq` taken apart** (leaf): `evalCore`'s `.eq` clause is, on a private copy of the state, the
type (`evalType`), each side on a copy of its own (from the state the type left, as the run's), the
checks of the sides at the type, and `mkEqM`; the copies restore the snapshot (`restoreKeep`), and
the tail flag is the snapshot's throughout. -/
theorem eq_split (fuel : Nat) {st st' : MState} {typed : Bool} {A a b : Term} {hint : Option Value} {v : Value}
    {T? : Option Value} {bh : Nat} (h : Runs (Ochr.evalCore (fuel + 1) typed (.eq A a b) hint) st bh (v, T?) st') :
    T? = some (.sort 0) ∧
    ∃ (st₁ sa st₂ sb st₃ st₄ cur : MState) (A' va vb : Value) (Ta Tb : Option Value) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : Nat),
      Runs (Ochr.evalType fuel A) (copyEntry st) b₁ A' st₁ ∧
      Runs (Ochr.eval fuel typed a none) (copyEntry st₁) b₂ (va, Ta) sa ∧ Runs (Ochr.restoreKeep st₁) sa b₃ () st₂ ∧
      Runs (Ochr.eval fuel typed b none) (copyEntry st₂) b₄ (vb, Tb) sb ∧ Runs (Ochr.restoreKeep st₂) sb b₅ () st₃ ∧
      Runs (eqChecks fuel typed Ta Tb A') st₃ b₆ () st₄ ∧
      Runs (Ochr.mkEqM fuel A' va vb) st₄ b₇ v cur ∧ Runs (Ochr.restoreKeep st) cur b₈ () st' ∧
      st₁.tailNext = st.tailNext ∧ st₂.tailNext = st.tailNext := by
  sorry

/-- **A side of a statement position** (proved from the induction hypothesis): run on a copy of its
own (`eval` at the copy's entry, `eval_step`), the copy restored (`restore_ext`): a private
computation, and the reference's run of the side out of tail position at no hint. -/
theorem side_step (fuel : Nat) (ih : StepsIHBelow fuel) {st₁ sa st₂ : MState} {typed : Bool} {a : Term}
    {va : Value} {Ta : Option Value} {b₂ b₃ : Nat}
    (hg : Good K.dm K.M K.Γ ρ st₁) (hctx : CtxOk K ρ st₁) {s : SState} {π : Nat → Nat} (hs : Rel K ρ φ π st₁ s)
    (htn : st₁.tailNext = false)
    (hok : typed = false → (runT K ρ φ false (hintM K ρ none) a s).isSome)
    (he : Runs (Ochr.eval fuel typed a none) (copyEntry st₁) b₂ (va, Ta) sa)
    (hr : Runs (Ochr.restoreKeep st₁) sa b₃ () st₂) (hDa : DecTab K.D sa) :
    KeptAfter st₁ st₂ ∧ ∃ (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat) (r : Res) (s'' : SState),
      ExtOk K ρ st₁ st₂ ρ₂ Δ₂ ∧ runT K ρ₂ φ false (hintM K ρ none) a s = some (r, s'') ∧
      meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (π₂ l)) r.2 va = r.1 := by
  obtain ⟨hgE, hcE, hsE, habs, hnl, -⟩ := copyEntry_ok K ρ φ hg hctx hs
  have htE : (copyEntry st₁).tailNext = false := htn
  have hokE : typed = false → (runT K ρ φ (copyEntry st₁).tailNext (hintM K ρ none) a s).isSome := by
    rw [htE]; exact hok
  obtain ⟨ρ₂, Δ₂, π₂, hsz, hnl2, hagree, -, r, s'', hrun, hmean, -, hc2, -, hgf⟩ :=
    (ih.at K ρ φ).eval_step (copyEntry st₁) sa typed a none va Ta hgE hcE s π hsE hokE hDa b₂ he
  rw [habs] at hsz hagree
  rw [hnl] at hnl2
  obtain ⟨hk, hext⟩ := restore_ext K ρ hr hg hctx hsz hnl2 hagree hc2 (typedAssignment_of_withTemp { K with Δ := Δ₂ } ρ₂ hgf)
  rw [htE] at hrun
  exact ⟨hk, ρ₂, Δ₂, π₂, r, s'', hext, hrun, hmean⟩

/-- **The checks are private** (leaf): `expectTy` runs a conversion (`conv_sound`'s `KeptAfter`). -/
theorem eqChecks_kept (fuel : Nat) {st st' : MState} {typed : Bool} {Ta Tb : Option Value} {A' : Value} {b : Nat}
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (h : Runs (eqChecks fuel typed Ta Tb A') st b () st')
    (hD : DecTab K.D st') :
    KeptAfter st st' ∧ ∃ (ρ' : Assignment) (Δ' : Nat → TyS), ExtOk K ρ st st' ρ' Δ' := by
  sorry

theorem grows_eqChecks (fuel : Nat) (typed : Bool) (Ta Tb : Option Value) (A' : Value) :
    GrowsM (eqChecks fuel typed Ta Tb A') := by
  unfold eqChecks
  grows_go

/-- **An untyped side runs** (leaf): an untyped `Eq` (in a re-run) whose reference run succeeds runs
each side; at no hint, under every extension of the assignment (the sides name old unknowns). -/
theorem eq_sides_ok {A a b : Term} {s : SState} {tl : Bool} {hint : TyS} (n : Nat)
    (hok : (runT K ρ φ tl hint (.eq A a b) s).isSome)
    {ρ' : Assignment} {Δ' : Nat → TyS} (ha : ∀ σ, σ < n → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ) (hint' : TyS) :
    (runT { K with Δ := Δ' } ρ' φ false hint' a s).isSome ∧
      (runT { K with Δ := Δ' } ρ' φ false hint' b s).isSome := by
  sorry

/-- **The sides** (leaf): the reference's `.eq` runs each side with no hint, as the checker's `evalCore` does
(docs/31 D172; it ran them at the code its run of the type gives), the checker's `mkEqM` at `⟦A'⟧`. Under the final assignment the type's run is the one
`evalType` related (it names old unknowns), and each side's run at the type's code gives the
meaning the checker's value has there at the outer renaming (the sides' own renamings differ only at
labels issued inside their copies, which an `Eq`'s value does not hold, D48; a typed side was checked
at `A'`, `eqChecks`, and an untyped one is read at its run's type, which is the type's code). -/
theorem eq_sides {st st₁ st₂ st₃ st₄ cur : MState} {A a b : Term} {A' va vb : Value} {s : SState}
    {π πa πb : Nat → Nat} {ρ₁ ρ₂ ρ₃ ρ₄ ρ₅ : Assignment} {Δ₁ Δ₂ Δ₃ Δ₄ Δ₅ : Nat → TyS}
    {rA ra rb : Res} {sa sb : SState} {typed : Bool} {Ta Tb : Option Value} {fuel bc : Nat}
    (k₁ : KeptAfter st st₁) (e₁ : ExtOk K ρ st st₁ ρ₁ Δ₁)
    (hA : run K ρ₁ φ (.plain .err) A s = some (rA, s))
    (hmA : meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π l)) (.plain .err) A' = rA.1)
    (k₂ : KeptAfter st₁ st₂) (e₂ : ExtOk { K with Δ := Δ₁ } ρ₁ st₁ st₂ ρ₂ Δ₂)
    (ha : runT { K with Δ := Δ₁ } ρ₂ φ false (hintM { K with Δ := Δ₁ } ρ₁ none) a s = some (ra, sa))
    (hma : meanV { K with Δ := Δ₂ } ρ₂ (fun l => φ (πa l)) ra.2 va = ra.1)
    (k₃ : KeptAfter st₂ st₃) (e₃ : ExtOk { K with Δ := Δ₂ } ρ₂ st₂ st₃ ρ₃ Δ₃)
    (hb : runT { K with Δ := Δ₂ } ρ₃ φ false (hintM { K with Δ := Δ₂ } ρ₂ none) b s = some (rb, sb))
    (hmb : meanV { K with Δ := Δ₃ } ρ₃ (fun l => φ (πb l)) rb.2 vb = rb.1)
    (hchk : Runs (eqChecks fuel typed Ta Tb A') st₃ bc () st₄)
    (k₄ : KeptAfter st₃ st₄) (e₄ : ExtOk { K with Δ := Δ₃ } ρ₃ st₃ st₄ ρ₄ Δ₄)
    (k₅ : KeptAfter st₄ cur) (e₅ : ExtOk { K with Δ := Δ₄ } ρ₄ st₄ cur ρ₅ Δ₅) :
    ∃ (rA' ra' rb' : Res) (sa' sb' : SState), runT K ρ₅ φ false (.plain .err) A s = some (rA', s) ∧
      runT K ρ₅ φ false (.plain .err) a s = some (ra', sa') ∧
      runT K ρ₅ φ false (.plain .err) b s = some (rb', sb') ∧
      ra'.1 = meanV { K with Δ := Δ₄ } ρ₄ (fun l => φ (π l))
        (.plain (meanV { K with Δ := Δ₄ } ρ₄ noFuture (.plain .err) A').asTy) va ∧
      rb'.1 = meanV { K with Δ := Δ₄ } ρ₄ (fun l => φ (π l))
        (.plain (meanV { K with Δ := Δ₄ } ρ₄ noFuture (.plain .err) A').asTy) vb := by
  sorry

/-- **The type of an `Eq` is future-free** (leaf; docs/27 Lemma 5: a type holds no live loan). -/
theorem eqType_futureFree {st : MState} {A' : Value} (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) :
    ∀ ψ, (meanV K ρ ψ (.plain .err) A').asTy = (meanV K ρ noFuture (.plain .err) A').asTy := by
  sorry

/-- **An `Eq`'s value holds no loan** (leaf): D48 keeps `&` out of its type, so its sides hold no
borrow, and a side's sealed program is closed over private copies of what it borrows
(`⌈let c1 = σ0; G(&c1)⌉`, `Regress/EqJ`). -/
theorem eq_value_noLoan (fuel : Nat) {st cur : MState} {A' va vb v : Value} {b : Nat}
    (h : Runs (Ochr.mkEqM fuel A' va vb) st b v cur) : v.loans = [] := by
  sorry

/-- **`Eq`, assembled** (no `sorry` in the body): the type, the two sides and the checks each a
private computation from the state the last left, the extensions composed (`ExtOk.trans`); `mkEqM`'s
proposition is the reference's by `eq_sides`; the outer copy restored (`restore_ext`); the relation
kept (`Rel.kept`) with the value, which holds no loan, in flight. -/
theorem eq_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : eq_step_stmt K ρ φ (fuel + 1) := by
  intro st st' typed A a b hint v T? hg hctx s π hs hok htn hD bh h
  obtain ⟨hT, st₁, sa, st₂, sb, st₃, st₄, cur, A', va, vb, Ta, Tb, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈,
    hA, hea, hra, heb, hrb, hchk, hm, hr, ht₁, ht₂⟩ := eq_split fuel h
  -- the tables only grow along the run, so the decisions are aligned after each part
  have hDcur := hD.back (hr.grows (grows_restoreKeep _))
  have hD₄ := hDcur.back (hm.grows (grows_mkEqM _ _ _ _))
  have hD₃ := hD₄.back (hchk.grows (grows_eqChecks _ _ _ _ _))
  have hDsb := hD₃.back (hrb.grows (grows_restoreKeep _))
  have hD₂ := hDsb.back ((tablesGrow_copyEntry st₂).trans (heb.grows (grows_eval _ _ _ _)))
  have hDsa := hD₂.back (hra.grows (grows_restoreKeep _))
  have hD₁ := hDsa.back ((tablesGrow_copyEntry st₁).trans (hea.grows (grows_eval _ _ _ _)))
  obtain ⟨hgE, hcE, hsE, -, -, -⟩ := copyEntry_ok K ρ φ hg hctx hs
  -- the type
  obtain ⟨k₁, ρ₁, Δ₁, e₁, rA, hrA, hmA⟩ :=
    (ih.at K ρ φ).evalType_step (copyEntry st) st₁ A A' hgE hcE s π hsE hD₁ b₁ hA
  have k₁' : KeptAfter st st₁ := k₁
  have e₁' : ExtOk K ρ st st₁ ρ₁ Δ₁ := e₁
  have hs₁ := Rel.kept K ρ φ hg hctx hs k₁' e₁'
  -- the first side
  have hoka : typed = false → (runT { K with Δ := Δ₁ } ρ₁ φ false (hintM { K with Δ := Δ₁ } ρ₁ none) a s).isSome :=
    fun ht => (eq_sides_ok K ρ φ st.absTy.size ((hok ht)) e₁'.1 _).1
  obtain ⟨k₂, ρ₂, Δ₂, πa, ra, sa', e₂, hra', hma⟩ :=
    side_step { K with Δ := Δ₁ } ρ₁ φ fuel ih e₁'.2.2 e₁'.2.1 hs₁ (ht₁.trans htn) hoka hea hra hDsa
  have hs₂ := Rel.kept { K with Δ := Δ₁ } ρ₁ φ e₁'.2.2 e₁'.2.1 hs₁ k₂ e₂
  -- the second side
  have e₁₂ := ExtOk.trans K ρ k₁' e₁' e₂
  have hokb : typed = false → (runT { K with Δ := Δ₂ } ρ₂ φ false (hintM { K with Δ := Δ₂ } ρ₂ none) b s).isSome :=
    fun ht => (eq_sides_ok K ρ φ st.absTy.size ((hok ht)) e₁₂.1 _).2
  obtain ⟨k₃, ρ₃, Δ₃, πb, rb, sb', e₃, hrb', hmb⟩ :=
    side_step { K with Δ := Δ₂ } ρ₂ φ fuel ih e₂.2.2 e₂.2.1 hs₂ (ht₂.trans htn) hokb heb hrb hDsb
  -- the checks, then `mkEqM`
  obtain ⟨k₄, ρ₄, Δ₄, e₄⟩ := eqChecks_kept { K with Δ := Δ₃ } ρ₃ fuel e₃.2.2 e₃.2.1 hchk hD₄
  obtain ⟨k₅, ρ₅, Δ₅, e₅, hmk⟩ := (ih.at { K with Δ := Δ₄ } ρ₄ φ).mkEqM_step st₄ cur A' va vb v
    e₄.2.2 e₄.2.1 (eqType_futureFree { K with Δ := Δ₄ } ρ₄ e₄.2.2 e₄.2.1) hDcur b₇ hm
  -- the chain of extensions, and the outer copy restored
  have k₁₃ := (k₁'.trans k₂).trans k₃
  have e₁₃ := ExtOk.trans K ρ (k₁'.trans k₂) e₁₂ e₃
  have k₁₄ := k₁₃.trans k₄
  have e₁₄ := ExtOk.trans K ρ k₁₃ e₁₃ e₄
  have k₁₅ := k₁₄.trans k₅
  have e₁₅ := ExtOk.trans K ρ k₁₄ e₁₄ e₅
  obtain ⟨kf, ef⟩ := restore_ext K ρ hr hg hctx k₁₅.2.2.2.2.1 k₁₅.2.2.2.2.2.2 e₁₅.1 e₁₅.2.1 e₁₅.2.2.1
  -- the reference's sides at the type
  obtain ⟨rA', ra', rb', sa'', sb'', hA', ha', hb', hva, hvb⟩ :=
    eq_sides K ρ φ k₁' e₁' hrA hmA k₂ e₂ hra' hma k₃ e₃ hrb' hmb hchk k₄ e₄ k₅ e₅
  have hsf := Rel.kept K ρ φ hg hctx hs kf ef
  obtain ⟨hrel, hgf⟩ := inFlight_noLoan { K with Δ := Δ₅ } ρ₅ φ v (.plain (TyM.univ 0))
    (eq_value_noLoan fuel hm) rfl ef.2.2 ef.2.1 hsf
  -- OWED (model lane, 2026-11-21: the strict `Eq` of "well typed inside"): the reference's `Eq` runs
  -- only where its type is a type of a universe and each side is `⊥` or a member of it. A checked
  -- `Eq` (`eqChecks`) gives it; not derived here (the step statements are the lead's to rewrite).
  have hEqOk : EqOk K.dm.read rA'.1 ra'.1 rb'.1 := sorry
  refine ⟨ρ₅, Δ₅, π, (.ty (TyM.prop (ra'.1 = rb'.1)), .plain (TyM.univ 0)), s, kf.2.2.2.2.1,
    kf.2.2.2.2.2.2, ef.1, fun _ _ => rfl,
    runT_eq_some K ρ₅ φ st.curTail _ A a b s rA' ra' rb' sa'' sb'' hA' ha' hb' hEqOk, ?_, ?_, ef.2.1, hrel, hgf⟩
  · refine (hmk _ _).trans ?_
    rw [hva, hvb]
  · intro T hT'
    rw [hT] at hT'
    cases hT'
    rfl

/-! ### `J` -/

/-- **A simulation from a later state composes with a prefix that extends** (proved): a step whose
front extended the assignment, `Δ` and the decisions and moved the reference to `s₂`, then ran as
`x` from there, runs as `y` from `s` when `y` is `x` after that front under every assignment that
agrees on the old unknowns. -/
theorem SimConclT.of_prefix {st st₂ st' : MState} {s s₂ : SState} {π π₂ : Nat → Nat} {ρ₂ : Assignment}
    {Δ₂ : Nat → TyS} {x y : Assignment → SM Res} {v : Value} {T? : Option Value}
    (hsz : st.absTy.size ≤ st₂.absTy.size) (hn : st.nextLoan ≤ st₂.nextLoan) (hπ : ∀ l, l < st.nextLoan → π₂ l = π l)
    (ha : ∀ σ, σ < st.absTy.size → ρ₂ σ = ρ σ ∧ Δ₂ σ = K.Δ σ)
    (hxy : ∀ ρ' : Assignment, (∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) → y ρ' s = x ρ' s₂)
    (h : SimConclT { K with Δ := Δ₂ } ρ₂ φ π₂ st₂ st' s₂ x v T?) :
    SimConclT K ρ φ π st st' s y v T? := by
  obtain ⟨ρ', Δ', π', r, s', sz, nl, ag, πg, hrun, hmean, hstr, hc, hrel, hgf⟩ := h
  have ag' : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ ∧ Δ' σ = K.Δ σ := fun σ hσ =>
    ⟨(ag σ (Nat.lt_of_lt_of_le hσ hsz)).1.trans (ha σ hσ).1, (ag σ (Nat.lt_of_lt_of_le hσ hsz)).2.trans (ha σ hσ).2⟩
  refine ⟨ρ', Δ', π', r, s', Nat.le_trans hsz sz, Nat.le_trans hn nl, ag',
    fun l hl => (πg l (Nat.lt_of_lt_of_le hl hn)).trans (hπ l hl), ?_, hmean, hstr, hc, hrel, hgf⟩
  rw [hxy ρ' fun σ hσ => (ag' σ hσ).1]
  exact hrun

/-- The reference's `J` clause, whatever the tail flag (proved): neither a statement nor a proof,
its statement positions on copies (each run succeeds), the motive at the first endpoint on a copy (`P(a)`, the
transported term's hint since main's D124; lead27, docs/31 D184), then its transported term after its entry,
at the join's grain. Since the orchestrator's ruling (A) (strict ends) the entry's and the join's
ends are tested (`MatchEntryOk`, `JoinDropOk`); the statement takes both (`hme`, `hjd`). -/
theorem runT_J_some (tl : Bool) (hint : TyS) (A a b P h t : Term) (s : SState)
    (hme : MatchEntryOk K φ true t s)
    (xa xP yc : Res × SState) (ea : runT K ρ φ false (.plain .err) a s = some xa)
    (eP : runT K ρ φ false (.plain .err) P s = some xP) (ec : callOf K.dm.read xP.1 [xa.1] s = some yc)
    (hjd : ∀ r R s₂, runT K ρ φ false (.plain yc.1.1.asTy) t (matchEntry K φ true t s).1 = some ((r, R), s₂) →
      JoinDropOk K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim "J" [A, a, b, P, h, t]) s₂)
    (hns : K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, h, t]) = (false, false))
    (hA : (runT K ρ φ false (.plain .err) A s).isSome)
    (hb : (runT K ρ φ false (.plain .err) b s).isSome)
    (hh : (runT K ρ φ false (.plain .err) h s).isSome) :
    runT K ρ φ tl hint (.prim "J" [A, a, b, P, h, t]) s =
      (match runT K ρ φ false (.plain yc.1.1.asTy) t (matchEntry K φ true t s).1 with
        | some ((r, R), s₂) => some ((r, R), joinDrop K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim "J" [A, a, b, P, h, t]) s₂)
        | none => none) := by
  obtain ⟨xA, eA⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨xb, eb⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨xh, eh⟩ := Option.isSome_iff_exists.mp hh
  have key : (open Classical in if MatchEntryOk K φ true t s then
      (match runT K ρ φ false (.plain yc.1.1.asTy) t (matchEntry K φ true t s).1 with
        | some ((r, R), s₂) =>
          open Classical in if JoinDropOk K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim "J" [A, a, b, P, h, t]) s₂ then
            some ((r, R), joinDrop K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim "J" [A, a, b, P, h, t]) s₂)
          else none
        | none => none) else none) =
      (match runT K ρ φ false (.plain yc.1.1.asTy) t (matchEntry K φ true t s).1 with
        | some ((r, R), s₂) => some ((r, R), joinDrop K φ (movedPlaces φ (matchEntry K φ true t s).1) (.prim "J" [A, a, b, P, h, t]) s₂)
        | none => none) := by
    rw [if_pos hme]
    cases hr : runT K ρ φ false (.plain yc.1.1.asTy) t (matchEntry K φ true t s).1 with
    | none => rfl
    | some y =>
      obtain ⟨⟨r, R⟩, s₂⟩ := y
      dsimp only
      rw [if_pos (hjd r R s₂ hr)]
  rw [← key]
  cases tl <;> (rw [runT]; simp only [SM.erasedIf, SM.stmtIf, hns, Bool.false_eq_true, if_false, SM.onCopy, bind,
    eA, ea, eb, eP, eh, ec, Option.map_some]; rfl)

/-- `J`'s computing tail (`evalCore`'s `J`, after the entry): the transported term at the join's
grain; typed, checked against `P(a)` and typed `P(b)`. -/
def jArm (fuel : Nat) (typed want : Bool) (J u : Term) (Pa Pb : Value) : M (Value × Option Value) :=
  if typed then do
    let (v, Tu) ← Ochr.joinDrop fuel J (Ochr.eval fuel true u)
    let fl ← Ochr.getFlags
    Ochr.expectTy fuel "the transported term" Tu Pa
    Ochr.setFlags fl
    pure (v, some Pb)
  else Ochr.joinDrop fuel J (do Ochr.demand want; Ochr.eval fuel false u)

theorem grows_jArm (fuel : Nat) (typed want : Bool) (J u : Term) (Pa Pb : Value) :
    GrowsM (jArm fuel typed want J u Pa Pb) := by
  unfold jArm
  grows_go

/-- **`J` taken apart** (leaf): `evalCore`'s `J`, neither a statement nor a proof (`hns`, so its motive
is not into `Prop`: `jErased` is the decision `declOf` reads, aligned), is a front that is a private
computation (the type, endpoints, motive and equation on copies, `P(a)` and `P(b)` by calls of the
motive that leave Ω as it was, the endpoints' conversion) followed by one of: at convertible
endpoints, or untyped (a run's [J-run] included), the entry of the transported term and `jArm`; or,
typed at endpoints that are not convertible, the stuck block `tJ` (the statement positions replaced by
their values, the transported term its one arm), which is neither a statement nor a proof. -/
theorem J_split (fuel : Nat) {st st' : MState} {typed : Bool} {A a b P hh u : Term} {hint : Option Value} {v : Value}
    {T? : Option Value} {bh : Nat} (s : SState)
    (hns : K.D.flags (scopeOf s) (.prim "J" [A, a, b, P, hh, u]) = (false, false)) (hctx : CtxOk K ρ st)
    (h : Runs (Ochr.evalCore (fuel + 1) typed (.prim "J" [A, a, b, P, hh, u]) hint) st bh (v, T?) st') :
    ∃ (st₁ : MState) (Pa Pb : Value) (want : Bool),
      KeptAfter st st₁ ∧ st₁.tailNext = st.tailNext ∧
      (Good K.dm K.M K.Γ ρ st → DecTab K.D st₁ → ∃ (ρ₁ : Assignment) (Δ₁ : Nat → TyS), ExtOk K ρ st st₁ ρ₁ Δ₁) ∧
      ((∃ (st₂ : MState) (caps : Array (Place × Nat)) (b₁ b₂ : Nat), Runs (Ochr.blockEntry fuel u) st₁ b₁ caps st₂ ∧
          Runs (jArm fuel typed want (.prim "J" [A, a, b, P, hh, u]) u Pa Pb) st₂ b₂ (v, T?) st') ∨
        (typed = true ∧ ∃ (tJ : Term) (arm : BlockArm) (b₁ : Nat),
          (∀ (ρ₁ : Assignment) (Δ₁ : Nat → TyS), ExtOk K ρ st st₁ ρ₁ Δ₁ →
            K.D.flags (scopeOf s) tJ = (false, false)) ∧
          (∃ A' av bv Pv hT : Value, tJ = .prim "J" [.val A', .val av, .val bv, .val Pv, .ascribe (.val .proof) (.val hT), u]) ∧
          Runs (Ochr.closeBlock fuel tJ [arm] (some Pb)) st₁ b₁ (v, T?) st' ∧ T? = some Pb)) := by
  sorry

/-- **`J`'s statement positions run** (leaf): the reference's runs of the type, the endpoints, the
motive and the equation succeed from the related state, under every assignment agreeing on the old
unknowns (typed: they ran in the front, by `evalType_step` and `eval_step`; untyped: by `hok`). -/
theorem J_stmts_run {st : MState} {typed : Bool} {A a b P hh u : Term} {s : SState} {tl : Bool} {hint : TyS}
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (hok : typed = false → (runT K ρ φ tl hint (.prim "J" [A, a, b, P, hh, u]) s).isSome)
    (ρ' : Assignment) (hρ' : ∀ σ, σ < st.absTy.size → ρ' σ = ρ σ) :
    (runT K ρ' φ false (.plain .err) A s).isSome ∧ (runT K ρ' φ false (.plain .err) a s).isSome ∧
      (runT K ρ' φ false (.plain .err) b s).isSome ∧ (runT K ρ' φ false (.plain .err) P s).isSome ∧
      (runT K ρ' φ false (.plain .err) hh s).isSome ∧
      -- the motive at the first endpoint (the transported term's hint since main's D124; lead27, docs/31 D184)
      (∀ xa xP, runT K ρ' φ false (.plain .err) a s = some xa → runT K ρ' φ false (.plain .err) P s = some xP →
        (callOf K.dm.read xP.1 [xa.1] s).isSome) := by
  sorry

/-- **The entry of the transported term** (leaf; static ends rule 2, D90): the checker's `blockEntry`
accesses the captures the stuck block would take, in its order; the reference's `matchEntry` does the
same at the aligned `blockCaps`. From related states, the states after are related, under an
extension at the unknowns an end's [Repack] makes, the tail flag untouched. -/
theorem J_entry (fuel : Nat) {st st₁ st₂ : MState} {u : Term} {caps : Array (Place × Nat)} {b : Nat}
    {s : SState} {π : Nat → Nat} {ρ₁ : Assignment} {Δ₁ : Nat → TyS}
    (e₁ : ExtOk K ρ st st₁ ρ₁ Δ₁) (hs : Rel { K with Δ := Δ₁ } ρ₁ φ π st₁ s)
    (h : Runs (Ochr.blockEntry fuel u) st₁ b caps st₂) (hD : DecTab K.D st₂) :
    ∃ (ρ₂ : Assignment) (Δ₂ : Nat → TyS) (π₂ : Nat → Nat),
      st₁.absTy.size ≤ st₂.absTy.size ∧ st₁.nextLoan ≤ st₂.nextLoan ∧ (∀ l, l < st₁.nextLoan → π₂ l = π l) ∧
      ExtOk { K with Δ := Δ₁ } ρ₁ st₁ st₂ ρ₂ Δ₂ ∧
      Rel { K with Δ := Δ₂ } ρ₂ φ π₂ st₂ (matchEntry K φ true u s).1 ∧ st₂.tailNext = st₁.tailNext := by
  sorry

/-- **The transported term at the join's grain** (leaf; [Join], D84, the arm of a match on a known
constructor, `evalMatch`'s): the arm by `eval_step` (out of tail position; the checker runs it at no
hint, the reference at `J`'s, `HintIndep`), then the join's drop (`joinDrop_step`) at the entry set the
reference read before the entry (`joinEntry`); typed, the check against `P(a)` is private and `P(b)`
is the result's type (`conv_sound` at the endpoints: they mean the same, so do `P(a)` and `P(b)`). -/
theorem J_arm (fuel : Nat) (ih : StepsIHBelow fuel) (hJ : Assignment → TyS) {st st₂ st' : MState} {typed want : Bool} {J u : Term}
    {Pa Pb : Value} {hint : Option Value} {v : Value} {T? : Option Value} {b : Nat} {s s₁ : SState}
    {π₂ : Nat → Nat} {ρ₂ : Assignment} {Δ₂ : Nat → TyS}
    (hg : Good K.dm ({ K with Δ := Δ₂ } : RunCtx).M K.Γ ρ₂ st₂) (hctx : CtxOk { K with Δ := Δ₂ } ρ₂ st₂)
    (hs : Rel { K with Δ := Δ₂ } ρ₂ φ π₂ st₂ s₁) (htn : st₂.tailNext = false)
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) J s).isSome)
    (h : Runs (jArm fuel typed want J u Pa Pb) st₂ b (v, T?) st') (hD : DecTab K.D st') :
    SimConclT { K with Δ := Δ₂ } ρ₂ φ π₂ st₂ st' s₁
      (fun ρ' s₁' => match runT K ρ' φ false (hJ ρ') u s₁' with
        | some ((r, R), s₂) => some ((r, R), joinDrop K φ (movedPlaces φ s₁') J s₂)
        | none => none) v T? := by
  sorry

/-- **The stuck block is the `J`** (leaf; [T-J-stuck], D63): the block's run (`closeBlock_step`: the run
of `tJ` at `P(b)`) is the reference's `J` at its own hint: the statement positions are discarded
copies either way (`J_stmts_run`), the transported term runs alike at either hint (`HintIndep`), and
`P(b)` is the type of its result (the equation `h` is true under a typed assignment, so the
endpoints mean the same, and `P(a)`, `t`'s type, is `P(b)`). -/
theorem J_stuck_bridge {st st₁ st' : MState} {typed : Bool} {A a b P hh u : Term} {hint : Option Value}
    {A' av bv Pv hT Pb v : Value} {T? : Option Value} {s : SState} {π : Nat → Nat}
    {ρ₁ : Assignment} {Δ₁ : Nat → TyS} (e₁ : ExtOk K ρ st st₁ ρ₁ Δ₁)
    (hok : typed = false → (runT K ρ φ st.curTail (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u]) s).isSome)
    (h : SimConcl { K with Δ := Δ₁ } ρ₁ φ π st₁ st' s
      (fun ρ' => run { K with Δ := Δ₁ } ρ' φ (hintM { K with Δ := Δ₁ } ρ₁ (some Pb))
        (.prim "J" [.val A', .val av, .val bv, .val Pv, .ascribe (.val .proof) (.val hT), u])) v)
    (hT? : T? = some Pb) :
    SimConclT { K with Δ := Δ₁ } ρ₁ φ π st₁ st' s
      (fun ρ' => runT K ρ' φ st.curTail (hintM K ρ hint) (.prim "J" [A, a, b, P, hh, u])) v T? := by
  sorry

/-- The hint the reference's `J` hands its transported term (main's D124; lead27, docs/31 D184): the motive's
meaning called at the first endpoint's, both run on copies of `s`, `err` where a run fails. -/
noncomputable def jHintS (K : RunCtx) (ρ : Assignment) (φ : Future) (a P : Term) (s : SState) : TyS :=
  match runT K ρ φ false (.plain .err) a s, runT K ρ φ false (.plain .err) P s with
  | some (xa, _), some (xP, _) =>
    match callOf K.dm.read xP [xa] s with
    | some (y, _) => .plain y.1.asTy
    | none => .plain .err
  | _, _ => .plain .err

/-- **`J`, assembled** (no `sorry` in the body): the front a private computation (`J_split`), the
relation kept (`Rel.kept`); then at convertible endpoints the entry (`J_entry`) and the transported
term at the join's grain (`J_arm`), which is the reference's clause after its statement positions
(`runT_J_some`, `J_stmts_run`); or the stuck block, by the induction hypothesis (`closeBlock_step`),
which is the reference's `J` (`J_stuck_bridge`); either composed with the front
(`SimConclT.of_prefix`). -/
theorem J_step_asm (fuel : Nat) (ih : StepsIHBelow fuel) : J_step_stmt K ρ φ (fuel + 1) := by
  intro st st' typed A a b P hh u hint v T? hg hctx s π hs hns hok htn hD bh h
  obtain ⟨st₁, Pa, Pb, want, k₁, ht₁, hfront, hbr⟩ := J_split K ρ fuel s hns hctx h
  rcases hbr with ⟨st₂, caps, b₁, b₂, hent, harm⟩ | ⟨htyped, tJ, arm, b₁, hflJ, ⟨A', av, bv, Pv, hT, rfl⟩, hcb, hT?⟩
  · -- convertible endpoints: the entry, then the transported term at the join's grain
    have hD₂ : DecTab K.D st₂ := hD.back (harm.grows (grows_jArm _ _ _ _ _ _ _))
    obtain ⟨ρ₁, Δ₁, e₁⟩ := hfront hg (hD₂.back (hent.grows (grows_blockEntry _ _)))
    have hs₁ := Rel.kept K ρ φ hg hctx hs k₁ e₁
    obtain ⟨ρ₂, Δ₂, π₂, sz₂, nl₂, hπ₂, e₂, hs₂, ht₂⟩ := J_entry K ρ φ fuel e₁ hs₁ hent hD₂
    have harm' := J_arm K ρ φ fuel ih (fun ρ' => jHintS K ρ' φ a P s) e₂.2.2 e₂.2.1 hs₂ (ht₂.trans (ht₁.trans htn)) hok harm hD
    have e₁₂ := ExtOk.trans K ρ k₁ e₁ e₂
    refine SimConclT.of_prefix K ρ φ (Nat.le_trans k₁.2.2.2.2.1 sz₂) (Nat.le_trans k₁.2.2.2.2.2.2 nl₂)
      (fun l hl => hπ₂ l (Nat.lt_of_lt_of_le hl k₁.2.2.2.2.2.2)) e₁₂.1 (fun ρ' hρ' => ?_) harm'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := J_stmts_run K ρ φ hg hctx hok ρ' hρ'
    obtain ⟨xa, ea⟩ := Option.isSome_iff_exists.mp h2
    obtain ⟨xP, eP⟩ := Option.isSome_iff_exists.mp h4
    obtain ⟨yc, ec⟩ := Option.isSome_iff_exists.mp (h6 xa xP ea eP)
    have hjh : jHintS K ρ' φ a P s = .plain yc.1.1.asTy := by
      unfold jHintS; rw [ea, eP]; dsimp only; rw [ec]
    -- SORRY (model lane, 2026-11-21, ruling (A), for (II)): the strict ends of `J`'s entry and join:
    -- every borrow [Entry] and the join's drop end has a member content at every typed future. The
    -- checker's rule (main's D98: no borrow ends over moved-out content) is what discharges it.
    show _ = (match runT K ρ' φ false (jHintS K ρ' φ a P s) u _ with
        | some ((r, R), s₂) => some ((r, R), joinDrop K φ (movedPlaces φ _) _ s₂)
        | none => none)
    rw [hjh]
    exact runT_J_some K ρ' φ st.curTail (hintM K ρ hint) A a b P hh u s (by sorry) xa xP yc ea eP ec
      (fun _ _ _ _ => by sorry) hns h1 h3 h5
  · -- endpoints not convertible (typed): the stuck block
    obtain ⟨ρ₁, Δ₁, e₁⟩ := hfront hg (hD.back (hcb.grows (grows_closeBlock _ _ _ _)))
    have hs₁ := Rel.kept K ρ φ hg hctx hs k₁ e₁
    have hcl := (ih.at { K with Δ := Δ₁ } ρ₁ φ).closeBlock_step st₁ st' _ [arm] (some Pb) v T?
      e₁.2.2 e₁.2.1 rfl s π hs₁ (hflJ ρ₁ Δ₁ e₁) hD b₁ hcb
    exact SimConclT.of_prefix K ρ φ k₁.2.2.2.2.1 k₁.2.2.2.2.2.2 (fun _ _ => rfl) e₁.1 (fun _ _ => rfl)
      (J_stuck_bridge K ρ φ e₁ hok hcl hT?)

end

end Ochr.Meaning.Steps
