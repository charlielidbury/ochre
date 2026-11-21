import Ochr.Meaning.Steps.FormMachine

/-!
# `Inv` across a change of Ω that adds no structure (machine lane; for `InvSteps`)

The state-level lemmas of `FormMachine.lean` (`InvSteps`) each change Ω in one small way: a number,
`()` or `⊥` pushed, popped or written; a borrow of a number moved or rewritten; a fresh loan made. Every
clause of `Inv` but four reads Ω only through its VALUES (an atom test on each value, the loans of
each value, the unknowns of each value), so it survives any change after which every value is an old
one or a SIMPLE one (`Simple`: a number, `()`, `⊥`, a loan, a borrow of a number), given what the
simple ones say of labels (`hocc`). `inv_step` is that lemma: the four clauses that read positions
(WF1's uniqueness of holders, WF2, WF12, WF14), the live-loan clause (L) and the two that read the
declared readings (`fits`, `proofCopy`) are its hypotheses, provided per change by `InvPos.lean`
(changes that keep the positions up to simple values) and by the lemma itself.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

/-- A number, `()` or `⊥`: a value holding no label, no unknown, no structure. -/
def _root_.Ochr.Value.Bland (v : Value) : Prop := v.Num ∨ v = .unit ∨ v = .bot

/-- A borrow of a number. -/
def _root_.Ochr.Value.NumBorrow (v : Value) : Prop := ∃ l w, v = .borrow l w ∧ w.Num

/-- What the columns' changes write: a bland value, a borrow of a number, a loan. -/
def _root_.Ochr.Value.Simple (v : Value) : Prop := v.Bland ∨ v.NumBorrow ∨ ∃ l, v = .loan l

theorem _root_.Ochr.Value.Bland.simple {v : Value} (h : v.Bland) : v.Simple := .inl h
theorem _root_.Ochr.Value.NumBorrow.simple {v : Value} (h : v.NumBorrow) : v.Simple := .inr (.inl h)

/-- An atom test false at every simple atom is false of every simple value. -/
theorem _root_.Ochr.Value.Simple.anyAtom {v : Value} (h : v.Simple) {P : Value → Bool} (h0 : P .zero = false)
    (hs : ∀ w, P (.succ w) = false) (hu : P .unit = false) (hb : P .bot = false)
    (hbr : ∀ l w, P (.borrow l w) = false) (hl : ∀ l, P (.loan l) = false) : v.anyAtom P = false := by
  rcases h with (hn | rfl | rfl) | ⟨l, w, rfl, hw⟩ | ⟨l, rfl⟩
  · exact hn.anyAtom h0 hs
  · simp [Value.anyAtom, hu]
  · simp [Value.anyAtom, hb]
  · simp [Value.anyAtom, hbr, hw.anyAtom h0 hs]
  · simp [Value.anyAtom, hl]

theorem _root_.Ochr.Value.Bland.anyAtom {v : Value} (h : v.Bland) {P : Value → Bool} (h0 : P .zero = false)
    (hs : ∀ w, P (.succ w) = false) (hu : P .unit = false) (hb : P .bot = false) : v.anyAtom P = false := by
  rcases h with hn | rfl | rfl
  · exact hn.anyAtom h0 hs
  · simp [Value.anyAtom, hu]
  · simp [Value.anyAtom, hb]

theorem _root_.Ochr.Value.Num.loans {v : Value} (h : v.Num) : v.loans = [] := by
  induction h with
  | zero => simp [Value.loans]
  | succ _ ih => simp [Value.loans, ih]

theorem _root_.Ochr.Value.Num.outerLoans {v : Value} (h : v.Num) : v.outerLoans = [] := by
  induction h with
  | zero => simp [Value.outerLoans]
  | succ _ ih => simp [Value.outerLoans, ih]

theorem _root_.Ochr.Value.Bland.loans {v : Value} (h : v.Bland) : v.loans = [] := by
  rcases h with hn | rfl | rfl
  · exact hn.loans
  · simp [Value.loans]
  · simp [Value.loans]

theorem _root_.Ochr.Value.Bland.outerLoans {v : Value} (h : v.Bland) : v.outerLoans = [] := by
  rcases h with hn | rfl | rfl
  · exact hn.outerLoans
  · simp [Value.outerLoans]
  · simp [Value.outerLoans]

theorem _root_.Ochr.Value.NumBorrow.loans {v : Value} (h : v.NumBorrow) : v.loans = [] := by
  obtain ⟨l, w, rfl, hw⟩ := h; simp [Value.loans, hw.loans]

theorem _root_.Ochr.Value.NumBorrow.outerLoans {v : Value} (h : v.NumBorrow) : v.outerLoans = [] := by
  obtain ⟨l, w, rfl, hw⟩ := h; simp [Value.outerLoans, hw.outerLoans]

theorem _root_.Ochr.Value.Bland.holdsBorrow {v : Value} (h : v.Bland) (l : Nat) : v.holdsBorrow l = false := by
  rcases h with hn | rfl | rfl
  · exact hn.holdsBorrow l
  · simp [Value.holdsBorrow]
  · simp [Value.holdsBorrow]

theorem _root_.Ochr.Value.Bland.sitesOf {v : Value} (h : v.Bland) (l : Nat) (pos : Pos) (path : List Step) :
    v.sitesOf l pos path = [] := by
  rcases h with hn | rfl | rfl
  · exact hn.sitesOf l pos path
  · simp [Value.sitesOf]
  · simp [Value.sitesOf]

theorem _root_.Ochr.Value.NumBorrow.sitesOf {v : Value} (h : v.NumBorrow) (l : Nat) (pos : Pos) (path : List Step) :
    v.sitesOf l pos path = [] := by
  obtain ⟨m, w, rfl, hw⟩ := h; simp [Value.sitesOf, hw.sitesOf]

theorem _root_.Ochr.Value.Bland.shapeOf {v : Value} (h : v.Bland) : shapeOf v = none := by
  rcases h with hn | rfl | rfl
  · cases hn <;> rfl
  · rfl
  · rfl

theorem _root_.Ochr.Value.Num.follow_bot {v : Value} (h : v.Num) (path : List Step) : v.follow path ≠ some .bot := by
  induction h generalizing path with
  | zero => cases path with
    | nil => simp [Value.follow]
    | cons s ss => cases s <;> simp [Value.follow, stepV]
  | succ hw ih => cases path with
    | nil => simp [Value.follow]
    | cons s ss =>
      cases s with
      | proj i => cases i with
        | zero => simpa [Value.follow, stepV] using ih ss
        | succ k => simp [Value.follow, stepV]
      | _ => simp [Value.follow, stepV]

/-- A bland value reaches `⊥` only at the empty path. -/
theorem _root_.Ochr.Value.Bland.follow_bot {v : Value} (h : v.Bland) {path : List Step}
    (hf : v.follow path = some .bot) : path = [] := by
  rcases h with hn | rfl | rfl
  · exact absurd hf (hn.follow_bot path)
  · cases path with
    | nil => rfl
    | cons s ss => cases s <;> simp [Value.follow, stepV] at hf
  · cases path with
    | nil => rfl
    | cons s ss => cases s <;> simp [Value.follow, stepV] at hf

/-- What every change of `InvSteps` keeps besides Ω: the tables `Inv` reads (the label counter may
grow). -/
structure TabSame (a b : MState) : Prop where
  nextLoan : a.nextLoan ≤ b.nextLoan
  nextAbs : a.nextAbs = b.nextAbs
  absTy : a.absTy = b.absTy
  absDecl : a.absDecl = b.absDecl
  refs : a.refs = b.refs
  etaRefs : a.etaRefs = b.etaRefs
  goal : a.goal = b.goal
  neutrals : a.neutrals = b.neutrals

/-- Every binding of `b` has the stored and deferred types of a binding of `a`, or is new, stored at
`Nat` or `&Nat`, nothing deferred. -/
def BindsFrom (a b : MState) : Prop :=
  ∀ (f i : Nat) (bb : Binding), b.env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some bb →
    (∃ (f' i' : Nat) (ba : Binding), a.env[f']?.bind (fun fr : Frame => fr.binds[i']?) = some ba ∧ ba.ty = bb.ty ∧
      ba.lazyTy = bb.lazyTy) ∨
    (bb.lazyTy = none ∧ (bb.ty = some .tNat ∨ bb.ty = some (.tRef .tNat) ∨ bb.ty = some .tUnit))

theorem mem_values_iff {env : Env} {v : Value} : v ∈ Env.values env ↔ ∃ p ∈ allPos env, valAt env p = v := by
  simp [Env.values, List.mem_map]

/-- (WF1)'s first half at one simple value. -/
theorem wf1At_simple {v : Value} (h : v.Simple) :
    match (generalizing := false) v with
    | .borrow _ w => ¬ w.hasBorrow = true
    | v => ¬ v.hasBorrow = true := by
  rcases h with (hn | rfl | rfl) | ⟨l, w, rfl, hw⟩ | ⟨l, rfl⟩
  · cases hn with
    | zero => simp [Value.hasBorrow, Value.anyAtom]
    | succ hw =>
      show ¬ (Value.succ _).hasBorrow = true
      rw [Value.hasBorrow, (Value.Num.succ hw).anyAtom rfl (fun _ => rfl)]; simp
  · simp [Value.hasBorrow, Value.anyAtom]
  · simp [Value.hasBorrow, Value.anyAtom]
  · show ¬ w.hasBorrow = true
    rw [Value.hasBorrow, hw.anyAtom rfl (fun _ => rfl)]; simp
  · simp [Value.hasBorrow, Value.anyAtom]

/-- A borrow's content in a simple value holds no loan. -/
theorem simple_borrow_loans {v w : Value} {m : Nat} (h : v.Simple) (e : v = .borrow m w) : w.loans = [] := by
  subst e
  rcases h with (hn | h | h) | ⟨l, w', e, hw⟩ | ⟨l, h⟩
  · cases hn
  · cases h
  · cases h
  · cases e; exact hw.loans
  · cases h

theorem simple_loans_sub {v : Value} (h : v.Simple) {l : Nat} (hl : l ∈ v.loans) : v = .loan l := by
  rcases h with hb | hn | ⟨m, rfl⟩
  · rw [hb.loans] at hl; cases hl
  · rw [hn.loans] at hl; cases hl
  · simp [Value.loans] at hl; rw [hl]

theorem tNat_hasAbs (σ : Nat) : Value.tNat.hasAbs σ = false := rfl
theorem tRefNat_hasAbs (σ : Nat) : (Value.tRef .tNat).hasAbs σ = false := rfl

/-- The unknowns `b` names are `a`'s. -/
theorem refd_of_step {a b : MState} (ht : TabSame a b)
    (hv : ∀ v ∈ Env.values b.env, v ∈ Env.values a.env ∨ v.Simple) (hb : BindsFrom a b) :
    ∀ σ, b.Refd σ → a.Refd σ := by
  intro σ h
  induction h with
  | @val τ v hv' h =>
    rcases hv v hv' with ha | hs
    · exact .val v ha h
    · rw [Value.hasAbs, hs.anyAtom (P := (· == .abs τ)) rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)] at h
      cases h
  | ty f i bb T hbb hT h =>
    rcases hb f i bb hbb with ⟨f', i', ba, hba, hty, -⟩ | ⟨-, e | e | e⟩
    · exact .ty f' i' ba T hba (hty.trans hT) h
    · rw [e] at hT; cases hT; rw [tNat_hasAbs] at h; cases h
    · rw [e] at hT; cases hT; rw [tRefNat_hasAbs] at h; cases h
    · rw [e] at hT; cases hT; cases h
  | lazyTy f i bb P ws j hbb hT h =>
    rcases hb f i bb hbb with ⟨f', i', ba, hba, -, hlz⟩ | ⟨e, -⟩
    · exact .lazyTy f' i' ba P ws j hba (hlz.trans hT) h
    · rw [e] at hT; cases hT
  | goal G hG h => exact .goal G (ht.goal.trans hG) h
  | neutral m σ' hm h => exact .neutral m σ' (ht.neutrals ▸ hm) h
  | eta σ' v he h => exact .eta σ' v (ht.etaRefs ▸ he) h
  | dep σ' T _ hT h ih => exact .dep σ' T ih (ht.absTy ▸ hT) h

/-- **`Inv` across a change that writes only simple values** (the generic half of every `InvSteps`
lemma): the clauses that read Ω value by value follow from `a`'s; the position-reading ones, (L), and
the readings' two are hypotheses. -/
theorem inv_step {D : Decisions} {Γ : List IndDecl} {a b : MState} (hi : Inv D Γ a) (ht : TabSame a b)
    (hv : ∀ v ∈ Env.values b.env, v ∈ Env.values a.env ∨ v.Simple)
    (hocc : ∀ l, b.Occurs l → a.Occurs l ∨ l < b.nextLoan) (hb : BindsFrom a b)
    (h1 : ∀ p ∈ allPos b.env, ∀ q ∈ allPos b.env, ∀ l, Env.shape b.env p = some l → Env.shape b.env q = some l → p = q)
    (h2 : WF2 b.env) (h12 : WF12 b.env) (h14 : WF14 b.env)
    (hL : ∀ v ∈ Env.values b.env, ∀ l ∈ v.loans, liveLoan b.env l = true)
    (hfits : ∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true)
    (hpc : ∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) : Inv D Γ b := by
  obtain ⟨⟨w1a, -⟩, -, w3, w4, ⟨w6a, w6b, w6c, w6d, w6e⟩, ⟨w8a, w8b, w8c, w8d⟩, w10, ⟨w11a, w11b, w11c, w11d, w11e⟩,
    -, -, w15, w16, sf, wocc⟩ := hi
  have hlt : ∀ l, b.Occurs l → l < b.nextLoan := fun l hl =>
    (hocc l hl).elim (fun h => Nat.lt_of_lt_of_le (wocc l h) ht.nextLoan) id
  refine ⟨⟨fun p hp => ?_, h1⟩, h2, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, h12, h14,
    ?_, ?_, ⟨hfits, hL, ?_, hpc, ?_, ?_, ?_⟩, hlt⟩
  · -- (WF1), first half
    rcases hv _ (mem_values_iff.mpr ⟨p, hp, rfl⟩) with ha | hs
    · obtain ⟨q, hq, e⟩ := mem_values_iff.mp ha
      have := w1a q hq; rw [e] at this; exact this
    · exact wf1At_simple hs
  · -- (WF3): `b`'s relation is inside `a`'s
    refine Subrelation.wf (fun {l m} h => ?_) w3
    obtain ⟨p, hp, w, e, hl⟩ := h
    rcases hv _ (mem_values_iff.mpr ⟨p, hp, e⟩) with ha | hs
    · obtain ⟨q, hq, e'⟩ := mem_values_iff.mp ha
      exact ⟨q, hq, w, e', hl⟩
    · rw [simple_borrow_loans hs rfl] at hl; cases hl
  · intro v hv'
    rcases hv v hv' with ha | hs
    · exact w4 v ha
    · rw [hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)]; simp
  · intro σ hσ; rw [← ht.absTy]; exact w6a σ (refd_of_step ht hv hb σ hσ)
  · rw [← ht.absTy]; exact w6b
  · rw [← ht.refs, ← ht.absTy]; exact w6c
  · rw [← ht.absTy, ← ht.nextAbs]; exact w6d
  · intro v hv' l hl
    rcases hv v hv' with ha | hs
    · exact Nat.lt_of_lt_of_le (w6e v ha l hl) ht.nextLoan
    · have e := simple_loans_sub hs hl
      subst e
      exact hlt l ⟨_, hv', by simp only [Value.anyAtom, Bool.or_eq_true]; left; left; show (l == l) = true; simp⟩
  · intro v hv'
    rcases hv v hv' with ha | hs
    · exact w8a v ha
    · exact hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  · intro f i bb hbb T hT
    rcases hb f i bb hbb with ⟨f', i', ba, hba, hty, -⟩ | ⟨-, e | e | e⟩
    · exact w8b f' i' ba hba T (hty.trans hT)
    · rw [e] at hT; cases hT; rfl
    · rw [e] at hT; cases hT; rfl
    · rw [e] at hT; cases hT; rfl
  · rw [← ht.absTy]; exact w8c
  · rw [← ht.goal]; exact w8d
  · intro v hv'
    rcases hv v hv' with ha | hs
    · exact w10 v ha
    · exact hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  · intro f i bb hbb
    rcases hb f i bb hbb with ⟨f', i', ba, hba, hty, hlz⟩ | ⟨e, e' | e' | e'⟩
    · rw [← hty, ← hlz]; exact w11a f' i' ba hba
    · refine ⟨fun T hT l => ?_, fun P ws j h => by rw [e] at h; cases h⟩
      rw [e'] at hT; cases hT; rfl
    · refine ⟨fun T hT l => ?_, fun P ws j h => by rw [e] at h; cases h⟩
      rw [e'] at hT; cases hT; rfl
    · refine ⟨fun T hT l => ?_, fun P ws j h => by rw [e] at h; cases h⟩
      rw [e'] at hT; cases hT; rfl
  · rw [← ht.absTy]; exact w11b
  · rw [← ht.goal]; exact w11c
  · rw [← ht.neutrals]; exact w11d
  · rw [← ht.etaRefs]; exact w11e
  · intro v hv' l
    rcases hv v hv' with ha | hs
    · exact w15 v ha l
    · exact hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  · intro v hv'
    rcases hv v hv' with ha | hs
    · exact w16 v ha
    · exact hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  · intro v hv'
    rcases hv v hv' with ha | hs
    · exact sf.ctors v ha
    · exact hs.anyAtom rfl (fun _ => rfl) rfl rfl (fun _ _ => rfl) (fun _ => rfl)
  · rw [← ht.etaRefs]; exact sf.etaHint
  · rw [← ht.etaRefs]; exact sf.etaNoSelf
  · intro σ l h; rw [← ht.absTy]; rw [← ht.absDecl] at h; exact sf.readingsSorted σ l h

end Ochr.Meaning.Steps.Machine
