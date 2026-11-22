import Ochr.Meaning.Steps.MasterTail
import Ochr.Meaning.Steps.FragLet

/-!
# The master induction's `let` step, typed and unerased, in general (lead22, 2026-11-22; docs/31 D152)

`letIn_core`/`stepLetIn_typed`: the step for `let x = u; w` from the induction hypothesis (`Master.IH`),
for every right-hand side and body, every value and type, every state with a frame meeting `Pre` and every
related good reference state, for a TYPED run of a `let` whose reading the table decides and does not make
a proof (so the table leaves it unerased). Its proof is the fragment's (`FragLet.letF_core`) with every
fragment-specific piece replaced by a general named fact, each stated here at the exact class it is used at:

* `ValsCongrA` (a fact about the model, NEW): the embedded values' condition moves to an extension of the
  assignment and `Δ` that agrees at the term's unknowns (the body is checked at the extension);
* `LetTailDecl` (a fact about the table, NEW): the table reads a `let` as its body in the scope extended by
  the right-hand side's reading, as the checker's `declOf` does (`Decide.lean`'s `.letIn` clause): what makes
  the reading the `let` hands its tail the table's reading of the tail, the hypothesis's entry condition;
* `LetPushG` (the push, NEW; the invariant's part is the checker's, the relation's the model's): moving the
  right-hand side's value from flight into the new binding on the checker's side, `pushBindShaped` of its
  meaning on the reference's, keeps `Pre` and `Rel` (the fragment's `push_frag`, for every value);
* `LetDropG` (the drop, NEW; the inversion of `dropTopBind` is the checker's, the relation across the ends the
  model's): the checker's `dropTopBind` is matched by the reference's drop (`LetDrop`: the binding's held label
  ended, or the borrows lent at it), with `Pre` and `Rel` after (the fragment's `drop_frag`, for every value);
  and, on the checker's side, the drop keeps the mode and the frames and pops the top binding's reading.

What the run keeps (`Kept`: the mode, the frames, the top readings; lead23, D154) is proved from `letInv`'s mode
facts, the sub-runs' induction hypotheses and the drop's; lead22's whole-machine `EvalTop` is gone.

The rest is proved: `letInv` (the machine lane's), (I) at `u` and `w` (`Strict.fund_all`), `SGood` after the
push (`Strict.sgood_pushBindShaped`), the body's reference run moved to the extended assignment
(`runT_congrA`, from the `let`'s unknowns being the start state's).

Not covered, each a separate obligation of `StepLetIn`: an UNTYPED `let` (`LetInv` is typed; the untyped
`evalCore` defers a call's type, `lazyTy`, and hands its tail the hint, where the reference hands none:
`HintIndep` needed, or the model's change of D151 extended); a `let` the table erases or reads as a proof or
`.any` (the erased mode, D150's ruling).
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The facts the general step assumes -/

/-- **The table reads a `let` as its body in the extended scope** (a fact about the table, NEW): as the
checker's `declOf` does. Where the checker's `declOf` of the `let` succeeds this is `DecTab` at its two
sub-runs; the fuel-free table can differ only at a scope where it fails, where no `eval` of the `let`
succeeds either. -/
def LetTailDecl (D : Decisions) : Prop :=
  ∀ (sc : List DeclInfo) (x : Hint) (u w : Term), D.declOf sc (.letIn x u w) = D.declOf (D.declOf sc u :: sc) w

/-- **A value fits a reading at every place under its binding** (lead27, docs/31 D185): the invariant's two shape clauses,
(V) (`ShapeFacts.fits`: a place the table reads as an inductive of `Γ` holds one of its constructors or a stand-in) and
(C⋆) (`ShapeFacts.proofCopy`: a place at the join's grain holding `⋆` is read as a copy), at every place rooted at a
binding read `du` that holds `v`, with the scope `sc` below it. The checker's content of such a place is `v` followed
along the place's path (`ckContent`), so this is what a push of `v` read `du` asks of the two clauses at the new
binding. -/
def FitsAt (D : Decisions) (Γ : List IndDecl) (sc : List DeclInfo) (du : DeclInfo) (v : Value) : Prop :=
  ∀ p : Place, p.steps.1 = 0 →
    (∀ w n args, v.follow p.steps.2 = some w → D.placeDecl (du :: sc) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → w.fitsInd n = true) ∧
    (GrainOk D Γ (du :: sc) p → v.follow p.steps.2 = some .proof → D.copy (D.placeDecl (du :: sc) p) = true)

/-- **The value a typed evaluation returns fits the table's reading of its term** (checker, NEW, lead27, docs/31 D185;
UNREAD): at the class the `let` runs its right-hand side at (typed, no hint, not in tail position, no reading handed
down, any erased depth), from a state meeting the checker's invariant, the value fits the table's reading of the term
in the state's scope (`FitsAt`). What the push needs of the invariant's shape clauses at the new binding. Guarded on
concrete programs in `Steps/FitGuards.lean`. -/
def EvalFitsT : Prop :=
  ∀ (D : Decisions) (Γ : List IndDecl) (n : Nat) (u : Term) (st₀ st₁ : MState) (bh : Nat) (v₀ : Value)
    (T₀ : Option Value),
    Inv D Γ st₀.norm → DecTab D st₁ → ModeR st₀ → st₀.tailNext = false → st₀.tailDecl = none →
    Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ →
    FitsAt D Γ (DecideScope.topReadings st₀) (D.declOf (DecideScope.topReadings st₀) u) v₀

/-- **The value an UNTYPED evaluation returns fits the table's reading of its term, where the reference's run of the
term succeeds** (mixed, NEW, lead27, docs/31 D185; UNREAD): at the class an untyped `let` runs its right-hand side at,
from related states, the reference's run of the term succeeding (the untyped `let`'s entry condition gives it). The
checker's untyped run tests nothing of the value's shape, so the fit comes from the reference: its strict tests make
the result a member of its type (`GoodRes`), the value means the result (`Out`), and two things link that to the
table's reading: the table reads a term as an inductive `n` only where the reference's result type is `n`'s data code,
and as a non-copy only where it is not a proposition (the decisions' soundness against the reference); and a value
whose meaning is a member of `n`'s data code is a constructor of `n` or a stand-in. Neither is stated alone yet; this
fact is the two together at the one class the `let` needs. -/
def EvalFitsU : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (n : Nat) (u : Term) (st₀ st₁ : MState) (bh : Nat)
    (v₀ : Value) (T₀ : Option Value) (s : SState),
    Pre K ρ st₀ → Rel K ρ φ π st₀ s → Strict.SGood K.dm K.Γ φ s → DecTab K.D st₁ → ModeR st₀ →
    st₀.tailNext = false → st₀.tailDecl = none →
    (runT K ρ φ false (.plain TyM.err) u s).isSome →
    Runs (Ochr.eval n false u none) st₀ bh (v₀, T₀) st₁ →
    FitsAt K.D K.Γ (DecideScope.topReadings st₀) (K.D.declOf (DecideScope.topReadings st₀) u) v₀

/-- The fit a sub-run gives, moved to the scope after it (its readings kept) and the reading the `let` names. -/
theorem fitsAt_of_eval {D : Decisions} {Γ : List IndDecl} {st st₀ st₁ : MState} {u : Term} {du : DeclInfo} {v₀ : Value}
    (hk₀ : Kern st st₀) (htop : DecideScope.topReadings st₁ = DecideScope.topReadings st₀)
    (hdu : D.declOf (DecideScope.topReadings st) u = du)
    (h : FitsAt D Γ (DecideScope.topReadings st₀) (D.declOf (DecideScope.topReadings st₀) u) v₀) :
    FitsAt D Γ (DecideScope.topReadings st₁) du v₀ := by
  rw [htop, ← hdu, ColumnC.topReadings_kern hk₀]
  exact h

/-- **The push of a `let`'s binding, on both sides** (NEW; the fragment's `push_frag` for every value): from
the checker's state with the right-hand side's value `v₀` in flight at `T₀`, meeting `Pre` and related to the
reference's state after the right-hand side, whose result `ru` the value means and the type agrees with,
and which (I) makes good: the state with the value moved into a new top binding (read `du`) meets `Pre` and is
related to the reference's state with the result bound (`pushBindShaped`, read `du`). -/
def LetPushG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ stB : MState) (v₀ : Value)
    (T₀ : Option Value) (x : Hint) (p : Bool) (du : DeclInfo) (ru : Res) (s₁ : SState),
    0 < st₁.env.size →
    Pre K ρ (st₁.withTempT v₀ T₀) → Rel K ρ φ π (st₁.withTempT v₀ T₀) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1 → (∀ T, T₀ = some T → StrAgree K ρ T ru.2) →
    ru.2.label = (Value.heldLabel v₀).map π →
    Strict.GoodRes K.dm.read ru → Strict.LabOk K.dm s₁ ru → LoU s₁ ru.2.label →
    FitsAt K.D K.Γ (DecideScope.topReadings st₁) du v₀ →
    Kern { st₁ with env := Env.pushBindE st₁.env x T₀ v₀ p du } stB →
    Pre K ρ stB ∧ Rel K ρ φ π stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })

/-- **`LetPushG` as stated before lead27: FALSE** (machine10's reading; docs/31 D185), kept as the record. Two ways: the
pushed value `v₀` and the reading `du` it is bound at were unrelated (now the hypothesis `FitsAt`; the conclusion's
shape clause fails at a value that does not fit, `letPush_old_breaks_fits`); and at a value with no type (`T₀ = none`)
the checker's binding reads `err` while the reference's has the result's type (D183; ruling asked, D185). -/
def LetPushG_old : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st₁ stB : MState) (v₀ : Value)
    (T₀ : Option Value) (x : Hint) (p : Bool) (du : DeclInfo) (ru : Res) (s₁ : SState),
    0 < st₁.env.size →
    Pre K ρ (st₁.withTempT v₀ T₀) → Rel K ρ φ π (st₁.withTempT v₀ T₀) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    meanV K ρ (fun l => φ (π l)) ru.2 v₀ = ru.1 → (∀ T, T₀ = some T → StrAgree K ρ T ru.2) →
    ru.2.label = (Value.heldLabel v₀).map π →
    Strict.GoodRes K.dm.read ru → Strict.LabOk K.dm s₁ ru → LoU s₁ ru.2.label →
    Kern { st₁ with env := Env.pushBindE st₁.env x T₀ v₀ p du } stB →
    Pre K ρ stB ∧ Rel K ρ φ π stB (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du })

/-- **The first form's shape clause fails where the value does not fit** (kernel-checked, lead27): `Z` bound at a
reading the table reads as an inductive of `Γ` does not fit it. With machine10's reading (the premises of
`LetPushG_old` say nothing relating `v₀` and `du`, and the pushed state's `ShapeFacts.fits` asks exactly this at the new
binding), this is why `LetPushG_old` is false. -/
theorem letPush_old_breaks_fits {D : Decisions} {Γ : List IndDecl} {sc : List DeclInfo} {du : DeclInfo} {n : String}
    {args : List DeclInfo} (hD : D.placeDecl (du :: sc) (.var 0) = .ind n args) (hΓ : (Γ.find? (·.name == n)).isSome) :
    ¬ FitsAt D Γ sc du .zero := by
  intro h
  have := (h (.var 0) rfl).1 .zero n args rfl hD hΓ
  simp [Value.fitsInd] at this

/-- **The drop of a `let`'s binding, on both sides** (NEW; the fragment's `drop_frag` for every value): the
checker's successful `dropTopBind` from a state meeting `Pre`, related to a good reference state, is matched by
the reference's drop of its top binding (`LetDrop`), keeping the temporaries, only growing the tables, with
`Pre` and `Rel` after; on the checker's side it keeps the mode and the frames and pops the top binding's
reading. -/
def LetDropG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (W st₃ : MState) (s₂ : SState) (n bh : Nat),
    0 < W.env.size → Pre K ρ W → Rel K ρ φ π W s₂ → Strict.SGood K.dm K.Γ φ s₂ →
    Runs (Ochr.dropTopBind n) W bh () st₃ →
    ∃ s₃, LetDrop K φ s₂ s₃ ∧ topTemps st₃.env = topTemps W.env ∧
      (W.absTy.size ≤ st₃.absTy.size ∧ W.nextLoan ≤ st₃.nextLoan) ∧ Pre K ρ st₃ ∧ Rel K ρ φ π st₃ s₃ ∧
      ModeEq W st₃ ∧ st₃.env.size = W.env.size ∧
      DecideScope.topReadings st₃ = (DecideScope.topReadings W).tail

/-- **The embedded values' condition moves to an extension that agrees at the term's unknowns** (a fact about
the model, NEW; at each embedded value by `runT_congrA`, whose run reads only the unknowns it holds). The
fragment had it for free (its terms embed no value); a `let`'s body is checked at the extension its
right-hand side handed on. -/
def ValsCongrA : Prop :=
  ∀ (K : RunCtx) (Δ' : Nat → TyS) (ρ ρ' : Assignment) (φ : Future) (t : Term),
    (∀ σ, t.anyAtom (· == .abs σ) = true → AgreeA K Δ' ρ ρ' σ) →
    t.valsOk (Strict.ValsP K ρ φ) → t.valsOk (Strict.ValsP (KA K Δ') ρ' φ)

namespace LetGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- `let x = S(Z); let y = (); x`: a body whose run pushes and drops two bindings. -/
def bodyLL : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ .tt (.place (.var 1)))

/-- A state with one frame holding one binding read `.unit`. -/
def stLL : MState := { env := #[{ binds := #[{ hint := ⟨"z"⟩, ty := some .tUnit, val := .unit, decl := .unit }] }] }

-- `Kept` at a concrete run: the run succeeds, in the plain mode, with the frames and the top readings kept
#guard isOk (Ochr.eval 100 true bodyLL none) stLL 100000
#guard (outSt (Ochr.eval 100 true bodyLL none) stLL 100000).env.size == stLL.env.size
#guard DecideScope.topReadings (outSt (Ochr.eval 100 true bodyLL none) stLL 100000) == DecideScope.topReadings stLL
#guard let st' := outSt (Ochr.eval 100 true bodyLL none) stLL 100000
  !st'.copying && !st'.inPlace && !st'.headEval && st'.erasedDepth == 0

-- `LetTailDecl` at the checker's `declOf`: `let y = (); #1` read in the scope `[.other]` is `#1` read in
-- `[.unit, .other]` (`.other`), and `let y = (); #0` is `.unit`
#guard outVal (withLive true (Ochr.declOf 100 false [] [] (.letIn ⟨"y"⟩ .tt (.place (.var 1)))))
    (scopeState stLL [.other]) 100000 ==
  outVal (withLive true (Ochr.declOf 100 false [] [] (.place (.var 1)))) (scopeState stLL [.unit, .other]) 100000
#guard outVal (withLive true (Ochr.declOf 100 false [] [] (.letIn ⟨"y"⟩ .tt (.place (.var 0)))))
    (scopeState stLL [.other]) 100000 == .unit

/-- One frame holding `z` read `.unit` and, on top, `x ↦ 1` read `.other` at `Nat`. -/
def stLL2 : MState := { env := #[{ binds := #[{ hint := ⟨"z"⟩, ty := some .tUnit, val := .unit, decl := .unit },
  { hint := ⟨"x"⟩, ty := some .tNat, val := .succ .zero, decl := .other }] }] }

-- `LetDropG`'s checker part at a concrete drop: `dropTopBind` keeps the frames and the mode and pops the top
-- binding's reading
#guard isOk (Ochr.dropTopBind 100) stLL2 100000
#guard (outSt (Ochr.dropTopBind 100) stLL2 100000).env.size == stLL2.env.size
#guard DecideScope.topReadings (outSt (Ochr.dropTopBind 100) stLL2 100000) == (DecideScope.topReadings stLL2).tail
#guard let st' := outSt (Ochr.dropTopBind 100) stLL2 100000
  !st'.copying && !st'.inPlace && !st'.headEval && st'.erasedDepth == 0

end LetGuards

/-! ## Small lemmas -/

theorem size_pushBindE (E : Env) (h : Hint) (ty : Option Value) (v : Value) (p : Bool) (d : DeclInfo) :
    (Env.pushBindE E h ty v p d).size = E.size := by
  simp [Env.pushBindE]

theorem absBelow_mono {t : Term} {a b : Nat} (h : t.absBelow a) (hab : a ≤ b) : t.absBelow b :=
  fun σ hσ => Nat.lt_of_lt_of_le (h σ hσ) hab

theorem absBelow_letIn {x : Hint} {u w : Term} {n : Nat} (h : (Term.letIn x u w).absBelow n) :
    u.absBelow n ∧ w.absBelow n :=
  ⟨fun σ hσ => h σ (by simp [Term.anyAtom, hσ]), fun σ hσ => h σ (by simp [Term.anyAtom, hσ])⟩

/-! ## The step -/

section
variable {K : RunCtx} {φ : Future}

/-- **A typed, unerased `let`, at `evalCore`, in general.** From the induction hypothesis at the fuel of the
`let`'s `eval` and the facts above. -/
theorem letIn_core (hLT : LetTailDecl K.D) (hPu : LetPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFT : EvalFitsT) (hc : Strict.FundCtx K) {ρ : Assignment} {m : Nat} {x : Hint} {u w : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.letIn x u w) (fun st => 0 < st.env.size) (· = true) := by
  intro st st' typed hint v T? s π hne hty hm hctl htn htd hcd hp hr hS hv hab hhb hnh hfl _ hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, hme₃', hD₁, hD₂⟩ := Machine.letInvD m x u w hint st st' bh v T? K.D htn htd hD h
  obtain ⟨habu, habw⟩ := absBelow_letIn hab
  have hnhu : u.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.1
  have hnhw : w.hasHolePrim = false := by simp [Term.hasHolePrim] at hnh; exact hnh.2
  have hsz₀ : st₀.env.size = st.env.size := (ColumnC.size_of_erase hk₀.env).symm
  -- the step for `u`
  have hOu := (ih m (by omega) K.Δ ρ).1 u st₀ st₁ true none v₀ T₀ s π (hm.of_modeEq hm₀) (fun _ => htn₀) (by omega) (.inl htd₀)
    (hp.of_kern hk₀) (hr.of_kern hk₀) hS hv.1 (by rw [← hk₀.absTy]; exact habu) (hintBelow_none _) hnhu (fun e => by cases e) hD₁ bh₁ hru
  replace hOu := outK_of_outLK hOu
  rw [htn₀] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩, hK₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hv.1 false (.plain TyM.err) s s₁ ru hS hxu'
  have hm₁ : ModeR st₁ := (hm.of_modeEq hm₀).of_modeEq hK₁.mode
  have hsz₁ := hK₁.size
  have htop₁ := hK₁.top
  have hne₁ : 0 < st₁.env.size := by omega
  -- the value fits its reading at the new binding (the checker's fact, at the typed run of `u`)
  have hfit := fitsAt_of_eval hk₀ htop₁ hdu
    (hFT K.D K.Γ m u st₀ st₁ bh₁ v₀ T₀ (hp.of_kern hk₀).inv hD₁ (hm.of_modeEq hm₀) htn₀ htd₀ hru)
  -- the push, on both sides
  obtain ⟨hpB, hrB⟩ := hPu { K with Δ := Δ₁ } ρ₁ φ π₁ st₁ stB v₀ T₀ x p du ru s₁ hne₁ hp₁ hr₁ hS₁ hmu hau hlu
    hgu hlabu hlouu hfit hkB
  have hSB : Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) := by
    by_cases hs₁ : s₁.env = []
    · rw [Strict.pushBindShaped_nil _ _ hs₁]; exact hS₁
    · exact Strict.sgood_pushBindShaped hS₁ _ rfl hgu hlabu hlouu hs₁
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du } := by
    rw [scopeOf_rel hr, hdu]
  -- the step for `w`, at the extended context
  have hszB : stB.env.size = st₁.env.size := by
    rw [← ColumnC.size_of_erase hkB.env]; exact size_pushBindE _ _ _ _ _ _
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st₁.env.size - 1 < st₁.env.size)⟩
  have htopB : DecideScope.topReadings stB = du :: DecideScope.topReadings st := by
    rw [← ColumnC.topReadings_kern hkB, ColumnC.topReadings_pushBindE hfr₁, htop₁, ColumnC.topReadings_kern hk₀.symm]
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) :=
    .inr (by rw [htdB, hcd, htopB, hLT, hdu])
  have habB : st.absTy.size ≤ stB.absTy.size := by
    have := he₁.abs; rw [← hkB.absTy]; rw [← hk₀.absTy] at this; exact this
  have hagree : ∀ σ, w.anyAtom (· == .abs σ) = true → AgreeA K Δ₁ ρ ρ₁ σ := fun σ hσ => by
    have hσ' : σ < st₀.absTy.size := by rw [← hk₀.absTy]; exact habw σ hσ
    obtain ⟨a, d⟩ := he₁.agree σ hσ'
    exact ⟨a.symm, d.symm⟩
  have hOw := (ih m (by omega) Δ₁ ρ₁).1 w stB st₂ true none r T? _ π₁ (hm₁.of_modeEq hmeB)
    (fun _ => htnB.trans (hctl rfl)) (by omega) htdB'
    hpB hrB hSB (hVC K Δ₁ ρ ρ₁ φ w hagree hv.2) (absBelow_mono habw habB) (hintBelow_none _) hnhw (fun e => by cases e) hD₂ bh₂ hrw
  replace hOw := outK_of_outLK hOw
  rw [htnB] at hOw
  obtain ⟨⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩, hK₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w
      (pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := du }) = some (rw', s₂) := by
    rw [runT_congrA K Δ₁ ρ ρ₁ φ _ w _ _ hagree]; exact hxw
  obtain ⟨-, -, -, hS₂⟩ := Strict.fund_all hc w hv.2 st.curTail (.plain TyM.err) _ s₂ rw' hSB hxw'
  have hsz₂ := hK₂.size
  have hne₂ : 0 < st₂.env.size := by omega
  -- the drop
  obtain ⟨s₃, hLD, htt, ⟨hga, hgl⟩, hP₃, hR₃, hme₃, hsz₃, htop₃⟩ := hDr { K with Δ := Δ₂ } ρ₂ φ π₂ (st₂.withTempT r T?) st₃ s₂ m bh₃
    (by rw [size_withTempT]; exact hne₂) hp₂ hr₂ hS₂ hrd
  obtain rfl : v = r := popped_of_topTemps hne₂ htt hk₃
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans
      ((he₂.grow hga hgl).congr rfl rfl (by rw [hk₃.absTy]; rfl) (by rw [hk₃.nextLoan]; rfl))
  have hW : ModeEq st₂ (st₂.withTempT v T?) := ⟨rfl, rfl, rfl, rfl⟩
  have hkept : Kept st st' := by
    refine ⟨hm₀.trans (hK₁.mode.trans (hmeB.trans (hK₂.mode.trans
      (hW.trans (hme₃.trans hme₃'))))), ?_, ?_⟩
    · have e1 := ColumnC.size_of_erase hk₃.env
      rw [size_withTempT] at e1 hsz₃
      omega
    · rw [← topReadings_withTempT st' v T?, ← ColumnC.topReadings_kern hk₃, htop₃, topReadings_withTempT,
        hK₂.top, htopB]
      rfl
  refine ⟨⟨ρ₂, Δ₂, π₂, rw', s₃, hext, ?_, hmw, haw, hlw, hP₃.of_kern hk₃, hR₃.of_kern hk₃⟩, hkept⟩
  -- the reference's `let`
  -- a typed `let` is not in tail position (`hctl`): its tail runs with no hint on both sides (D156)
  have hth : tailHint st.curTail (hintM K ρ hint) = .plain TyM.err := by rw [hctl rfl]; rfl
  rw [runT_letIn _ _ x u w s hfl, hxu']
  simp only [bind, Option.bind]
  rw [hpb, hth, hxw']
  exact letDrop_eval hLD rw'

/-- **The step for a typed `let` the table reads as decided data, in general**: from the induction
hypothesis, at every fuel, `Δ` and assignment, for every right-hand side and body, `EvalSim` (`EvalAt` for typed
runs from a state with a frame where the table reads the `let` as neither `.any` nor a proof, so it leaves it
unerased), with what the run keeps (`EvalSimK`). ASSUMES 4 facts: `LetTailDecl` (table), `ValsCongrA` (model),
`LetPushG` and `LetDropG` (each part checker, part model); and `Strict.FundCtx K` of the context. -/
theorem stepLetIn_typed (hLT : LetTailDecl K.D) (hPu : LetPushG) (hDr : LetDropG)
    (hVC : ValsCongrA) (hFT : EvalFitsT) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (x : Hint) (u w : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.letIn x u w)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) (· = true) := by
  intro n ih Δ ρ x u w
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.letIn x u w)
      (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.letIn x u w) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.letIn x u w)).isProof = false) (· = true) :=
    fun st st' typed hint v T? s π hP => letIn_core (K := { K with Δ := Δ }) hLT hPu hDr hVC hFT ⟨hc.globals, hc.sorts⟩ ih
      st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

end

end Ochr.Meaning.Steps.Form.Master
