import Ochr.Meaning.Steps.MasterLet

/-!
# The master induction's `S(u)` step, in general (lead24, 2026-11-22; docs/31 D173)

`stepSucc`: `EvalAt` for `S(u)`, typed or untyped, at every erased depth, for every argument `u`, every state with a
frame where the table reads the term as neither `.any` nor a proof, from the induction hypothesis at `u`. Since D171
the reference runs `u` with no hint, as the typed checker does, so the hypothesis at `u` is exactly the run the
`.succ` clause makes. Proved here: the checker's inversion at any depth (`Machine.succInvD`), (I) at `u`
(`Strict.fund_all`, for the strict test of an untyped run's result is the clause's own), what the run keeps.

ASSUMES 5 facts (and `Strict.FundCtx K`), each at the exact class it is used at (lead27 restated `SuccFlightG` and added
the last two, docs/31 D185):
* `SuccStrictG` (mixed): in a TYPED run, the strict test at `S`'s result passes: the argument's reference result `r`
  has `r.1.succ` a number. Its checker half: a typed `eval` returns a type (`T₀` is `some`), and `expectTy T₀ Nat`
  passed; its model half: conversion to `Nat` is sound (`T₀` means `Nat`, so `r.2.m = Nat`, D101) and a value the
  checker reads is not `⊥` (so `r.1` is not `moved`, and `GoodRes` makes it a number). An untyped run needs none of
  this: its entry condition (`hok`, the reference's run of `S(u)` succeeds) IS the strict test.
* `SuccMeanG` (model): the meaning of the argument's value at `Nat` (`meanV`'s `.succ` clause reads `v₀` at `Nat`) has
  the successor the meaning at the reference's result type has, wherever that successor is a number. True for a
  number and an unknown at `Nat`; a sealed program's meaning runs it at the hint (`meanV`'s `.sealed`).
* `SuccFlightG` (mixed): the value in flight changes from `v₀` (at `T₀`) to `S(v₀)` (at `Nat`) across the quiet stretch
  and `expectTy` after `u`: `Pre` (its invariant the checker's) and `Rel` (the model's) survive. For a number, the
  column's `popInert`/`pushInert` and `rel_withTempT_num`; for every value at `Nat` (unknowns, sealed programs) it is
  stated here. RESTATED (lead27): the argument's value `v₀` is not a borrow. As first stated (`SuccFlightG_old`) it was
  FALSE in an untyped run, where nothing stops `v₀` being a borrow (`S(&x)`).
* `SuccArgNoBorrowT` (checker, typed only): a typed argument whose type passes `expectTy _ Nat` is not a borrow.
* `SuccRefNoLabel` (model, untyped only): where the reference's `S(u)` succeeds, `u`'s result carries no label. FALSE as
  the model stands (a borrow means its content, so `S(&x)` passes the reference's test); ruling asked.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- **The strict test at a typed `S(u)` passes** (mixed; see the header). -/
def SuccStrictG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (n : Nat) (u : Term) (st₀ st₁ st₂ : MState) (bh₁ bh₂ : Nat)
    (v₀ : Value) (T₀ : Option Value) (r : Res),
    Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ →
    Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ →
    Pre K ρ (st₁.withTempT v₀ T₀) → (∀ T, T₀ = some T → StrAgree K ρ T r.2) →
    meanV K ρ φ r.2 v₀ = r.1 → Strict.GoodRes K.dm.read r →
    r.1.succ ∈ₛ[K.dm.read] TyM.nat

/-- **The argument's meaning at `Nat` has the same successor** (model; see the header). -/
def SuccMeanG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (ψ : Future) (R : TyS) (v : Value),
    (meanV K ρ ψ R v).succ ∈ₛ[K.dm.read] TyM.nat →
    (meanV K ρ ψ (.plain TyM.nat) v).succ = (meanV K ρ ψ R v).succ

/-- **The value in flight becomes `S(v₀)`, as first stated: FALSE** (machine10's reading, lead27's record, docs/31 D185):
nothing stops `v₀` being a borrow in an untyped run (the checker's untyped run of `S(&x)` returns `S(borrow_l v)`,
`SuccGuards` below), and then the conclusion's state holds a borrow inside data in a temporary, which breaks the
invariant's first clause (`succFlight_old_breaks_wf1`, kernel-checked at every state with a frame). Kept as the record. -/
def SuccFlightG_old : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (n : Nat) (typed : Bool) (st₁ st' : MState)
    (v₀ : Value) (T₀ : Option Value) (s₁ : SState),
    Pre K ρ (st₁.withTempT v₀ T₀) → Rel K ρ φ π (st₁.withTempT v₀ T₀) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    Quiet st₁ st' →
    (typed = true → ∃ (st₂ : MState) (bh₂ : Nat),
      Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st') →
    Pre K ρ (st'.withTempT (.succ v₀) (some .tNat)) ∧ Rel K ρ φ π (st'.withTempT (.succ v₀) (some .tNat)) s₁

/-- **The value in flight becomes `S(v₀)`** (mixed; see the header; RESTATED by lead27, docs/31 D185: `v₀` is not a
borrow, the hypothesis the first form lacked; WF1 at the premise already excludes a borrow below the root). -/
def SuccFlightG : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (n : Nat) (typed : Bool) (st₁ st' : MState)
    (v₀ : Value) (T₀ : Option Value) (s₁ : SState),
    (∀ l w, v₀ ≠ .borrow l w) →
    Pre K ρ (st₁.withTempT v₀ T₀) → Rel K ρ φ π (st₁.withTempT v₀ T₀) s₁ → Strict.SGood K.dm K.Γ φ s₁ →
    Quiet st₁ st' →
    (typed = true → ∃ (st₂ : MState) (bh₂ : Nat),
      Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st') →
    Pre K ρ (st'.withTempT (.succ v₀) (some .tNat)) ∧ Rel K ρ φ π (st'.withTempT (.succ v₀) (some .tNat)) s₁

/-- **A typed `S`'s argument is not a borrow** (checker, NEW, lead27, docs/31 D185; UNREAD): a typed run of the
argument from a state meeting the checker's invariant, whose type passes `expectTy _ Nat`, returns no borrow. Read off
the code: a typed run returns a borrow only at a borrow type (`&p` returns `T.map .tRef`; a read returns the place's
stored type, and every binder stores a borrow at the type of what it bound: a `let` at its right-hand side's, a
parameter at its declared `&A`), and `conv (&A) Nat` fails. Its truth at every state `Pre` allows needs that the
invariant ties a binding holding a borrow to a borrow type, which is not one of its clauses (to be read). Guarded:
`S(&x)` and `S(y)` with `y : &Nat` are rejected typed (`SuccGuards`). -/
def SuccArgNoBorrowT : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (n : Nat) (u : Term) (st₀ st₁ st₂ : MState) (bh₁ bh₂ : Nat) (v₀ : Value)
    (T₀ : Option Value),
    Pre K ρ st₀ → Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ →
    Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ → ∀ l w, v₀ ≠ .borrow l w

/-- **The reference's `S` takes no borrow** (model, NEW, lead27, docs/31 D185): where the reference's `S(u)` succeeds
(the untyped step's entry condition, `hok`), `u`'s result carries no label. FALSE as the model stands: the reference
means a borrow by its content (`meanV`'s `.borrow` clause) and its `&x` returns the content's meaning with the label on
the type (`borrowPlace`), so `S(&x)` at `x : Nat` passes the strict test at `S`. A ruling is asked (D185): (A) the
reference's `S` fails when its argument's result carries a label, which makes this a lemma of the clause; or (B) the
checker's untyped `S` rejects a borrow argument. -/
def SuccRefNoLabel : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (u : Term) (s : SState),
    K.D.flags (scopeOf s) (.succ u) = (false, false) → (runT K ρ φ tl hint (.succ u) s).isSome →
    ∀ r s₁, runT K ρ φ false (.plain TyM.err) u s = some (r, s₁) → r.2.label = none

/-- **The first form's conclusion fails at a borrow in flight** (kernel-checked, lead27): at every state with a frame,
`S(borrow_l w)` in a temporary breaks the invariant's first clause, so `Pre` fails there. With the guard below (the
checker's untyped run of `S(&x)` returns `S(borrow_0 (S(Z)))`) and machine10's reading that the premises hold there,
this is why `SuccFlightG_old` is false. -/
theorem succFlight_old_breaks_wf1 (st : MState) (hne : 0 < st.env.size) (l : Nat) (w : Value) (T? : Option Value) :
    ¬ WF1 (st.withTempT (.succ (.borrow l w)) T?).norm.env := by
  intro h
  obtain ⟨p, hp, hv⟩ := Machine.mem_values_iff.mp (mem_values_withTempT st _ T? hne)
  have h1 := h.1 p hp
  rw [hv] at h1
  exact h1 (by simp [Value.hasBorrow, Value.anyAtom])

namespace SuccGuards

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

/-- One frame, `x ↦ σ0` at `Nat` (an unknown), read `.other`. -/
def bS : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := .abs 0, decl := .other }
def stS : MState := { env := #[{ binds := #[bS] }], nextAbs := 1, absTy := #[.tNat], absDecl := #[.other] }

-- `SuccStrictG`'s checker half at a concrete argument over an unknown: the typed run of the argument returns a type
-- (`Nat`), and `S(x)`'s typed run returns `S(σ0)` at `Nat`, `x` moved (the value in flight `SuccFlightG` changes)
#guard (outVal (Ochr.eval 100 true (.place (.var 0)) none) stS 100000).2 == some .tNat
#guard (outVal (Ochr.eval 100 true (.succ (.place (.var 0))) none) stS 100000) == (.succ (.abs 0), some .tNat)
#guard (outSt (Ochr.eval 100 true (.succ (.place (.var 0))) none) stS 100000).env[0]!.binds[0]!.val == .bot
-- untyped: the same value, no type checked
#guard (outVal (Ochr.eval 100 false (.succ (.place (.var 0))) none) stS 100000).1 == .succ (.abs 0)

/-- One frame, `x ↦ S(Z)` at `Nat`. -/
def bN : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := .succ .zero, decl := .other }
def stN : MState := { env := #[{ binds := #[bN] }] }
/-- One frame, `x ↦ S(Z)` at `Nat` lent to `y ↦ &x` at `&Nat`. -/
def stB : MState := { env := #[{ binds := #[{ bN with val := .loan 0 },
  { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := .borrow 0 (.succ .zero), decl := .ref .other }] }], nextLoan := 1 }

-- `SuccFlightG_old`'s counterexample: the UNTYPED run of `S(&x)` succeeds with a borrow inside data, at `Nat`
-- (`Value.exact` compares constructors; a wrong expectation, `S(S(Z))`, fails)
#guard Value.exact (outVal (Ochr.eval 100 false (.succ (.borrow (.var 0))) none) stN 100000).1 (.succ (.borrow 0 (.succ .zero)))
#guard !Value.exact (outVal (Ochr.eval 100 false (.succ (.borrow (.var 0))) none) stN 100000).1 (.succ (.succ .zero))
#guard (outVal (Ochr.eval 100 false (.succ (.borrow (.var 0))) none) stN 100000).2 == some .tNat
-- `SuccArgNoBorrowT`: the TYPED runs of `S(&x)` and of `S(y)` at `y : &Nat` are rejected (and `S(x)` is accepted, so the
-- guard distinguishes)
#guard !isOk (Ochr.eval 100 true (.succ (.borrow (.var 0))) none) stN 100000
#guard !isOk (Ochr.eval 100 true (.succ (.place (.var 0))) none) stB 100000
#guard isOk (Ochr.eval 100 true (.succ (.place (.var 0))) none) stN 100000

end SuccGuards

section
variable {K : RunCtx} {φ : Future}

/-- `S`'s value holds no borrow. -/
theorem heldLabel_succ (v : Value) : Value.heldLabel (.succ v) = none := rfl

/-- **`S(u)`, at `evalCore`, in general.** -/
theorem succ_coreG (hST : SuccStrictG) (hSM : SuccMeanG) (hSF : SuccFlightG) (hNT : SuccArgNoBorrowT)
    (hNU : SuccRefNoLabel) (hc : Strict.FundCtx K)
    {ρ : Assignment} {m : Nat} {u : Term} (ih : IH K φ (m + 3)) :
    CoreSimK K ρ φ (m + 1) (.succ u) (fun st => 0 < st.env.size) := by
  intro st st' typed hint v T? s π hne _ hm hctl htn htd hcd hp hr hS hv hab hhb hnh hfl hok hD bh h
  obtain ⟨st₀, st₁, v₀, T₀, bh₁, hk₀, hm₀, htn₀, htd₀, hu₀, rfl, rfl, hq, hme, hDb, hty⟩ :=
    Machine.succInvD m typed u hint st st' bh v T? htn htd h
  have hsz₀ : st₀.env.size = st.env.size := (ColumnC.size_of_erase hk₀.env).symm
  have hnh' : u.hasHolePrim = false := by simpa [Term.hasHolePrim] using hnh
  have hab' : u.absBelow st₀.absTy.size := fun σ hσ => by
    rw [← hk₀.absTy]; exact hab σ (by simpa [Term.anyAtom] using hσ)
  have hrs : ∀ s', runT K ρ φ st.curTail (hintM K ρ hint) (.succ u) s' =
      SM.erasedIf (K.D.flags (scopeOf s') (.succ u)) (SM.strictS K.dm.read (do
        let (v, _) ← runT K ρ φ false (.plain TyM.err) u; pure (v.succ, .plain TyM.nat))) s' := fun s' => by
    rw [runT]
  -- the untyped entry condition, at `u`
  have hokU : typed = false → (runT K ρ φ st₀.tailNext (hintM K ρ none) u s).isSome := fun ht => by
    have hs := hok ht
    rw [hrs, hfl] at hs
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false] at hs
    rw [htn₀]
    show (runT K ρ φ false (.plain TyM.err) u s).isSome
    unfold SM.strictS at hs
    simp only [Bind.bind] at hs
    cases e : runT K ρ φ false (.plain TyM.err) u s with
    | none => rw [e] at hs; simp at hs
    | some _ => rfl
  have hOu := (ih m (by omega) K.Δ ρ).1 u st₀ st₁ typed none v₀ T₀ s π (hm.of_modeEq hm₀) (fun _ => htn₀)
    (by omega) (.inl htd₀) (hp.of_kern hk₀) (hr.of_kern hk₀) hS (by simpa [Term.valsOk] using hv) hab' (hintBelow_none _) hnh' hokU
    (hDb K.D hD) bh₁ hu₀
  replace hOu := outK_of_outLK hOu
  rw [htn₀] at hOu
  obtain ⟨⟨ρ₁, Δ₁, π₁, r, s₁, he₁, hx, hmean, hagr, hlab, hp₁, hr₁⟩, hK₁⟩ := hOu
  have hx' : runT K ρ φ false (.plain TyM.err) u s = some (r, s₁) := hx
  obtain ⟨hgu, -, -, hS₁⟩ := Strict.fund_all hc u (by simpa [Term.valsOk] using hv) false (.plain TyM.err) s s₁ r hS hx'
  -- the reference's `S(u)`, where its strict test passes
  have hcl : ∀ (hmem : r.1.succ ∈ₛ[K.dm.read] TyM.nat),
      runT K ρ φ st.curTail (hintM K ρ hint) (.succ u) s = some ((r.1.succ, .plain TyM.nat), s₁) := fun hmem => by
    rw [hrs, hfl]
    simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
    unfold SM.strictS
    simp only [Bind.bind, hx']
    exact if_pos hmem
  -- the strict test
  have hmem : r.1.succ ∈ₛ[K.dm.read] TyM.nat := by
    cases typed with
    | false =>
      have hs := hok rfl
      rw [hrs, hfl] at hs
      simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false] at hs
      unfold SM.strictS at hs
      simp only [Bind.bind, hx'] at hs
      rcases Classical.em (r.1.succ ∈ₛ[K.dm.read] TyM.nat) with hn | hn
      · exact hn
      · exfalso
        simp only [pure, TyS.plain] at hs
        rw [if_neg hn] at hs; cases hs
    | true =>
      obtain ⟨st₂, bh₂, hx₂, -⟩ := hty rfl
      exact hST { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) m u st₀ st₁ st₂ bh₁ bh₂ v₀ T₀ r hu₀ hx₂ hp₁ hagr hmean hgu
  have hrun := hcl hmem
  have hmv : meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) (.plain TyM.nat) (.succ v₀) = r.1.succ := by
    show (meanV { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) (.plain TyM.nat) v₀).succ = _
    rw [hSM { K with Δ := Δ₁ } ρ₁ (fun l => φ (π₁ l)) r.2 v₀ (by rw [hmean]; exact hmem), hmean]
  -- the argument is not a borrow: typed, by the checker's fact; untyped, by the reference's success (`hok`) and the
  -- label the result carries (`Out`'s label clause)
  have hnb : ∀ l w, v₀ ≠ .borrow l w := by
    cases typed with
    | true =>
      obtain ⟨st₂, bh₂, hx₂, -⟩ := hty rfl
      exact hNT K ρ m u st₀ st₁ st₂ bh₁ bh₂ v₀ T₀ (hp.of_kern hk₀) hu₀ hx₂
    | false =>
      intro l w e
      have h0 := hNU K ρ φ st.curTail (hintM K ρ hint) u s hfl (hok rfl) r s₁ hx'
      rw [hlab, e] at h0
      cases h0
  obtain ⟨hpF, hrF⟩ := hSF { K with Δ := Δ₁ } ρ₁ φ π₁ m typed st₁ st' v₀ T₀ s₁ hnb hp₁ hr₁ hS₁ hq hty
  have hkept : Kept st st' := by
    refine ⟨hm₀.trans (hK₁.mode.trans hme), ?_, ?_⟩
    · rw [← ColumnC.size_of_erase hq.env, hK₁.size, hsz₀]
    · rw [← ColumnC.topReadings_of_erase hq.env, hK₁.top, ColumnC.topReadings_kern hk₀.symm]
  refine ⟨⟨ρ₁, Δ₁, π₁, (r.1.succ, .plain TyM.nat), s₁, ⟨?_, ?_, ?_, ?_⟩, hrun, hmv, fun T hT => ?_,
    by rw [heldLabel_succ]; rfl, hpF, hrF⟩, hkept⟩
  · rw [hk₀.absTy]; exact Nat.le_trans he₁.abs hq.absSize
  · rw [hk₀.nextLoan]; exact Nat.le_trans he₁.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he₁.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he₁.ren l hl
  · cases hT; exact strAgree_tNat

/-- **The step for `S(u)`, in general**: from the induction hypothesis, at every fuel, `Δ` and assignment, for every
argument, typed or untyped, `EvalSimK` from a state with a frame where the table reads `S(u)` as neither `.any` nor a
proof (so it leaves it unerased). ASSUMES 5 facts: `SuccStrictG` (mixed, typed), `SuccMeanG` (model), `SuccFlightG`
(mixed, restated by lead27: the argument is not a borrow), `SuccArgNoBorrowT` (checker, typed; unread),
`SuccRefNoLabel` (model, untyped; FALSE as the model stands, ruling asked, docs/31 D185); and `Strict.FundCtx K`. -/
theorem stepSucc (hST : SuccStrictG) (hSM : SuccMeanG) (hSF : SuccFlightG) (hNT : SuccArgNoBorrowT)
    (hNU : SuccRefNoLabel) (hc : Strict.FundCtx K) :
    ∀ n, IH K φ n → ∀ (Δ : Nat → TyS) (ρ : Assignment) (u : Term),
      EvalSimK { K with Δ := Δ } ρ φ n (.succ u)
        (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.succ u) ≠ .any ∧
          (K.D.declOf (DecideScope.topReadings st) (.succ u)).isProof = false) := by
  intro n ih Δ ρ u
  by_cases hn : n < 3
  · intro st st' typed hint v T? s π _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bh h
    exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hc' : CoreSimK { K with Δ := Δ } ρ φ (m + 1) (.succ u)
      (fun st => 0 < st.env.size ∧ K.D.declOf (DecideScope.topReadings st) (.succ u) ≠ .any ∧
        (K.D.declOf (DecideScope.topReadings st) (.succ u)).isProof = false) :=
    fun st st' typed hint v T? s π hP => succ_coreG (K := { K with Δ := Δ }) hST hSM hSF hNT hNU ⟨hc.globals, hc.sorts⟩ ih
      st st' typed hint v T? s π hP.1
  exact eval_of_coreK (K := { K with Δ := Δ }) Machine.evalInvD
    (fun a b hk ha => ⟨by rw [← ColumnC.size_of_erase hk.env]; exact ha.1,
      by rw [← ColumnC.topReadings_kern hk]; exact ha.2⟩)
    (fun w e => by cases e) (fun f as h e => by cases e) (fun st hst => hst.2) hc'

end

end Ochr.Meaning.Steps.Form.Master
