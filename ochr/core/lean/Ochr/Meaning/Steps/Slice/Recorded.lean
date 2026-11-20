import Ochr.Meaning.Steps.JoinNoop
import Ochr.Meaning.Steps.EqJAsm
import Ochr.Meaning.Steps.Slice.UpdAt

/-!
# A generalisation record read back (the slice, `recordedNeutral_ok`)

`Machine.recordedNeutral n` returns, for a sealed program `n` this world generalised (`n := σ` in
`neutrals`), the unknown `σ` with the [Split] refinements made since substituted (`expandRefs`).
Its meaning is `n`'s: the expansion replaces an unknown `τ` by a refinement `τ := r'` that means
`ρ τ` (`TypedAssignment.refs`), and the record makes `ρ σ` mean `n` (`TypedAssignment.neutral`).
Both path conditions are stated at the constant future and the unknown's type; loan-freeness and
top-hint-freeness of the records carry them to every future and hint.
-/

namespace Ochr.Meaning.Steps

open Ochr

/-- Two lists related pointwise (no Mathlib here, so no `List.Forall₂`). -/
inductive Pw {α β : Type} (P : α → β → Prop) : List α → List β → Prop
  | nil : Pw P [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : P a b → Pw P as bs → Pw P (a :: as) (b :: bs)

theorem Pw.imp {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {as : List α} {bs : List β}, Pw P as bs → Pw Q as bs
  | _, _, .nil => .nil
  | _, _, .cons hab hr => .cons (h _ _ hab) (Pw.imp h hr)

section
variable (K : RunCtx) (ρ : Assignment)

/-- A run of `mapM` relates its inputs and outputs pointwise by what each run guarantees. -/
theorem runs_mapM_forall₂ {α β : Type} (f : α → M β) (P : α → β → Prop)
    (hf : ∀ x st b y st', Runs (f x) st b y st' → P x y) :
    ∀ (xs : List α) {st st' : MState} {b : Nat} {ys : List β}, Runs (xs.mapM f) st b ys st' →
      Pw P xs ys
  | [], st, st', b, ys, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, -⟩ := runs_pure_inv h
    exact .nil
  | x :: xs, st, st', b, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    obtain ⟨ys', st₂, b₂, h3, h4⟩ := Runs.bind_inv h2
    obtain ⟨rfl, -⟩ := runs_pure_inv h4
    exact .cons (hf x st b y st₁ h1) (runs_mapM_forall₂ f P hf xs h3)

/-- Fields meaning the same at every hint give the same field meanings. -/
theorem meanFields_forall₂ (ψ : Future) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (fs ys : List Value), Pw (fun f y => ∀ H, meanV K ρ ψ H y = meanV K ρ ψ H f) fs ys →
      ∀ (i : Nat) (earlier : List Sem), meanFields K ρ ψ d r c i earlier ys = meanFields K ρ ψ d r c i earlier fs
  | [], [], .nil, _, _ => rfl
  | f :: fs, y :: ys, .cons hfy hrest, i, earlier => by
    simp only [meanFields, hfy, meanFields_forall₂ ψ d r c fs ys hrest]

/-- **The refined expansion means the value** (`expandRefsF`): where every refinement record means
its unknown at every future and hint, replacing unknowns by their records, recursively, keeps the
meaning at every future and hint. -/
theorem expandRefsF_mean (refs : List (Nat × Value))
    (hrefs : ∀ τ r', (τ, r') ∈ refs → ∀ ψ H, ρ τ = meanV K ρ ψ H r') :
    ∀ (fuel : Nat) (v : Value) {st st' : MState} {b : Nat} {w : Value},
      Runs (Ochr.expandRefsF refs fuel v) st b w st' → ∀ ψ H, meanV K ρ ψ H w = meanV K ρ ψ H v
  | 0, v, st, st', b, w, h => by
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.expandRefsF, runMachineL_exhausted] at h
  | fuel + 1, v, st, st', b, w, h => by
    rw [Ochr.expandRefsF.eq_def] at h
    intro ψ H
    cases v with
    | abs σ =>
      dsimp only at h
      split at h
      · rename_i r' hr'
        rw [expandRefsF_mean refs hrefs fuel r' h ψ H, ← hrefs σ r' (mem_of_lookup hr') ψ H]
        simp only [meanV]
      · obtain ⟨rfl, -⟩ := runs_pure_inv h
        rfl
    | succ v =>
      dsimp only at h
      obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      obtain ⟨rfl, -⟩ := runs_pure_inv h2
      simp only [meanV, expandRefsF_mean refs hrefs fuel v h1 ψ]
    | ind t c hh ps fs =>
      dsimp only at h
      obtain ⟨ys, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      obtain ⟨rfl, -⟩ := runs_pure_inv h2
      have h2 := runs_mapM_forall₂ _ (fun f y => ∀ ψ H, meanV K ρ ψ H y = meanV K ρ ψ H f)
        (fun x _ _ _ _ hx => expandRefsF_mean refs hrefs fuel x hx) fs h1
      have h3 : Pw (fun f y => ∀ H, meanV K ρ ψ H y = meanV K ρ ψ H f) fs ys :=
        Pw.imp (fun _ _ hfy => hfy ψ) h2
      simp only [meanV, meanFields_forall₂ K ρ ψ _ _ c fs ys h3]
    | _ => obtain ⟨rfl, -⟩ := runs_pure_inv h; rfl

/-- What the expansion holds anywhere (for an atom test false at the nodes it rebuilds, `succ` and
a constructor value) was in the value or in a refinement record. -/
theorem expandRefsF_anyAtom (refs : List (Nat × Value)) (P : Value → Bool)
    (hs : ∀ x, P (.succ x) = false) (hi : ∀ t c h ps fs, P (.ind t c h ps fs) = false) :
    ∀ (fuel : Nat) (v : Value) {st st' : MState} {b : Nat} {w : Value},
      Runs (Ochr.expandRefsF refs fuel v) st b w st' → w.anyAtom P = true →
        v.anyAtom P = true ∨ ∃ σ r', (σ, r') ∈ refs ∧ r'.anyAtom P = true
  | 0, v, st, st', b, w, h, _ => by
    obtain ⟨L, left, log, h⟩ := h
    simp [Ochr.expandRefsF, runMachineL_exhausted] at h
  | fuel + 1, v, st, st', b, w, h, hw => by
    rw [Ochr.expandRefsF.eq_def] at h
    cases v with
    | abs σ =>
      dsimp only at h
      split at h
      · rename_i r' hr'
        refine .inr ?_
        rcases expandRefsF_anyAtom refs P hs hi fuel r' h hw with h1 | ⟨σ', r'', hm, h2⟩
        · exact ⟨σ, r', mem_of_lookup hr', h1⟩
        · exact ⟨σ', r'', hm, h2⟩
      · obtain ⟨rfl, -⟩ := runs_pure_inv h
        exact .inl hw
    | succ v =>
      dsimp only at h
      obtain ⟨y, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      obtain ⟨rfl, -⟩ := runs_pure_inv h2
      simp only [Value.anyAtom, hs, Bool.false_or] at hw ⊢
      exact expandRefsF_anyAtom refs P hs hi fuel v h1 hw
    | ind t c hh ps fs =>
      dsimp only at h
      obtain ⟨ys, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
      obtain ⟨rfl, -⟩ := runs_pure_inv h2
      have h2 := runs_mapM_forall₂ _ (fun f y => y.anyAtom P = true →
          f.anyAtom P = true ∨ ∃ σ r', (σ, r') ∈ refs ∧ r'.anyAtom P = true)
        (fun x _ _ _ _ hx => expandRefsF_anyAtom refs P hs hi fuel x hx) fs h1
      simp only [Value.anyAtom, hi, Bool.false_or, Bool.or_eq_true] at hw ⊢
      rcases hw with hw | hw
      · exact .inl (.inl hw)
      · have key : ∀ {fs ys : List Value}, Pw (fun f y => y.anyAtom P = true →
            f.anyAtom P = true ∨ ∃ σ r', (σ, r') ∈ refs ∧ r'.anyAtom P = true) fs ys →
            Value.anyAtomList P ys = true →
              Value.anyAtomList P fs = true ∨ ∃ σ r', (σ, r') ∈ refs ∧ r'.anyAtom P = true := by
          intro fs ys hp
          induction hp with
          | nil => intro h; simp [Value.anyAtomList] at h
          | cons hab _ ih =>
            intro h
            simp only [Value.anyAtomList, Bool.or_eq_true] at h ⊢
            rcases h with h | h
            · rcases hab h with h' | h'
              · exact .inl (.inl h')
              · exact .inr h'
            · rcases ih h with h' | h'
              · exact .inl (.inr h')
              · exact .inr h'
        rcases key h2 hw with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'
    | _ => obtain ⟨rfl, -⟩ := runs_pure_inv h; exact .inl hw

/-- A lookup by `==` finds a record whose key is `==` to the one asked. -/
theorem lookup_beq {β : Type} : ∀ {l : List (Value × β)} {a : Value} {b : β}, l.lookup a = some b →
    ∃ k, (k, b) ∈ l ∧ (a == k) = true
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: rest, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨k, List.mem_cons_self, hk⟩
    · obtain ⟨k', hm, hk'⟩ := lookup_beq h
      exact ⟨k', List.mem_cons_of_mem _ hm, hk'⟩

/-- `recordedNeutral n` returning a value: `n` is a sealed program, a record `n' := σ` with
`n == n'` is the first `==`-match in `neutrals`, and the value is `σ` expanded by the refinements. -/
theorem runs_recordedNeutral_some {n r : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.recordedNeutral n) st b (some r) st') :
    ∃ σ fuel b₁, st.neutrals.lookup n = some σ ∧ Runs (Ochr.expandRefsF st.refs fuel (.abs σ)) st b₁ r st' := by
  unfold Ochr.recordedNeutral at h
  split at h
  · obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
    obtain ⟨hx, hst₁⟩ := runs_get_inv hg
    subst x; subst st₁
    split at h2
    · rename_i σ hσ
      obtain ⟨y, st₂, b₂, hg', h3⟩ := Runs.bind_inv h2
      obtain ⟨hy, hst₂⟩ := runs_get_inv hg'
      subst y; subst st₂
      obtain ⟨w, st₃, b₃, hex, h4⟩ := Runs.bind_inv h3
      obtain ⟨hw, rfl⟩ := runs_pure_inv h4
      cases hw
      unfold Ochr.expandRefs at hex
      obtain ⟨fl, st₄, b₄, hfl, h5⟩ := Runs.bind_inv hex
      have e : st₄ = st ∧ fl = b₂ := by
        obtain ⟨L, left, log, hfl⟩ := hfl
        have e0 : runMachineL Ochr.fuelLeft st b₂ L = (.ok b₂ st, b₂, L) := rfl
        rw [e0] at hfl
        simp only [Prod.mk.injEq, Outcome.ok.injEq] at hfl
        exact ⟨hfl.1.2.symm, hfl.1.1.symm⟩
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨σ, _, _, hσ, h5⟩
    · obtain ⟨h0, -⟩ := runs_pure_inv h2
      cases h0
  · obtain ⟨h0, -⟩ := runs_pure_inv h
    cases h0

/-- **`recordedNeutral_ok` from what it needs of the records**: every refinement record means its
unknown at every future and hint and holds no loan, and a generalisation record `n' := σ` with
`n == n'` makes `σ` mean `n` at every future and hint. The bounds are (WF6)'s. -/
theorem recordedNeutral_ok_of (st : MState) (n r : Value) (b' : Nat)
    (hg : Good K.dm K.M K.Γ ρ st)
    (hrefs : ∀ τ r', (τ, r') ∈ st.refs → (∀ ψ H, ρ τ = meanV K ρ ψ H r') ∧ ∀ l, r'.hasLoan l = false)
    (hneut : ∀ n' σ, (n', σ) ∈ st.neutrals → (n == n') = true → ∀ ψ H, ρ σ = meanV K ρ ψ H n)
    (hr : Runs (Ochr.recordedNeutral n) st b' (some r) st) : NeutralOk K ρ st n r := by
  obtain ⟨σ, fuel, b₁, hl, he⟩ := runs_recordedNeutral_some hr
  obtain ⟨n', hm, hk⟩ := lookup_beq hl
  have w6 : WF6 st := hg.2.2.2.2.2.2.1
  refine ⟨fun ψ H => ?_, fun τ hτ => ?_, fun l => ?_⟩
  · rw [expandRefsF_mean K ρ st.refs (fun τ r' h => (hrefs τ r' h).1) fuel _ he ψ H]
    simp only [meanV]
    exact hneut n' σ hm hk ψ H
  · rcases expandRefsF_anyAtom st.refs (· == .abs τ) (fun _ => rfl) (fun _ _ _ _ _ => rfl) fuel _ he hτ
      with h | ⟨σ', r', hm', h'⟩
    · have e : σ = τ := by simpa [Value.anyAtom, BEq.beq, Value.beq] using h
      subst e
      exact w6.1 σ (.neutral n' σ hm (.inl rfl))
    · exact (w6.2.2.1 σ' r' hm').2 τ h'
  · cases hL : r.hasLoan l
    · rfl
    · rcases expandRefsF_anyAtom st.refs (fun | .loan m | .gloan m _ => m == l | _ => false)
        (fun _ => rfl) (fun _ _ _ _ _ => rfl) fuel _ he hL with h | ⟨σ', r', hm', h'⟩
      · simp [Value.anyAtom] at h
      · have := (hrefs σ' r' hm').2 l
        exact Bool.noConfusion (this.symm.trans h')


/-- **A record held loan-free and top-hint-free means its unknown at every future and hint**, from
its path condition (at the constant future and the unknown's type): a loan-free value means the same
at every future (`meanV_congr`), a top-hint-free one at every hint (`meanV_hintIndep`). The shape of
`etaRecorded_sim`, for any path condition of `TypedAssignment`. -/
theorem pathCond_everywhere (st : MState) (hctx : CtxOk K ρ st) {τ : Nat} {v : Value}
    (hpc : ρ τ = Value.mean K.dm K.M K.Γ ρ (fun _ => .err) (.plain (MState.absTyM K.dm K.M K.Γ ρ st τ)) v)
    (hlf : ∀ l, v.hasLoan l = false) (hhf : v.topHintFree K.Γ = true) : ∀ ψ H, ρ τ = meanV K ρ ψ H v := by
  intro ψ H
  rw [hpc, meanV_eq_mean_aux K ρ (fun _ => .err) _ v]
  rw [meanV_congr K ρ (fun _ => .err) ψ _ v hctx.noLabel fun l hl => by
    have := hlf l
    rw [Value.hasLoan_of_hasLoanM hl] at this; cases this]
  exact meanV_hintIndep K ρ ψ v hhf _ H

/-- A refinement record held loan-free and top-hint-free means its unknown everywhere. -/
theorem refs_everywhere (st : MState) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) {τ : Nat} {v : Value}
    (hm : (τ, v) ∈ st.refs) (hlf : ∀ l, v.hasLoan l = false) (hhf : v.topHintFree K.Γ = true) :
    ∀ ψ H, ρ τ = meanV K ρ ψ H v :=
  pathCond_everywhere K ρ st hctx (hg.1.refs τ v hm) hlf hhf

/-- A generalisation record's program, top-hint-free, means its unknown everywhere ((WF11): it holds
no loan). -/
theorem neutral_everywhere (st : MState) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) {n : Value} {σ : Nat}
    (hm : (n, σ) ∈ st.neutrals) (hhf : n.topHintFree K.Γ = true) : ∀ ψ H, ρ σ = meanV K ρ ψ H n :=
  have h11 : WF11 st := hg.2.2.2.2.2.2.2.2.2.2.2.1
  pathCond_everywhere K ρ st hctx (hg.1.neutral n σ hm) (h11.2.2.2.1 n σ hm) hhf

end

/-- **What `recordedNeutral_ok` needs of the records that `Good` and `CtxOk` do not state** (the
slice, 2026-11-20; proposed to main as clauses: the first beside (WF11)'s for the other two kinds of
record, the other two beside (Hη) in `ShapeFacts`). A refinement record holds no loan and is
top-hint-free, and so is a generalisation record's program: with the path conditions
(`TypedAssignment.refs`, `.neutral`, read at the constant future and the unknown's type) they make
each record mean its unknown at every future and hint (`pathCond_everywhere`). Swept (`lake exe
sweep`, clauses (WF11r), (Hr), (Hn)): 72,076 suite states, 25,553 holding a refinement record (13,390
of a declaration with parameters) and 8,623 a generalisation record; 739 probe states (177, 22): no
violation. -/
structure RecordFacts (Γ : List IndDecl) (st : MState) : Prop where
  refsLoanFree : ∀ σ v, (σ, v) ∈ st.refs → ∀ l, v.hasLoan l = false
  refsHint : ∀ σ v, (σ, v) ∈ st.refs → v.topHintFree Γ = true
  neutralHint : ∀ n σ, (n, σ) ∈ st.neutrals → n.topHintFree Γ = true

section
variable (K : RunCtx) (ρ : Assignment)

/-- **`recordedNeutral_ok` from the record facts**: the refinement records mean their unknowns
everywhere (`refs_everywhere`); the record the lookup finds, `n' := σ` with `n == n'`, makes `σ` mean
`n'` everywhere (`neutral_everywhere`); `hkey` carries that to `n`. -/
theorem recordedNeutral_ok_of_facts (st : MState) (n r : Value) (b' : Nat)
    (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st) (hf : RecordFacts K.Γ st)
    (hkey : ∀ n' σ, (n', σ) ∈ st.neutrals → (n == n') = true → ∀ ψ H, meanV K ρ ψ H n' = meanV K ρ ψ H n)
    (hr : Runs (Ochr.recordedNeutral n) st b' (some r) st) : NeutralOk K ρ st n r :=
  recordedNeutral_ok_of K ρ st n r b' hg
    (fun τ r' hm => ⟨refs_everywhere K ρ st hg hctx hm (hf.refsLoanFree τ r' hm) (hf.refsHint τ r' hm),
      hf.refsLoanFree τ r' hm⟩)
    (fun n' σ hm hk ψ H => by
      rw [neutral_everywhere K ρ st hg hctx hm (hf.neutralHint n' σ hm) ψ H]
      exact hkey n' σ hm hk ψ H)
    hr

end

end Ochr.Meaning.Steps
