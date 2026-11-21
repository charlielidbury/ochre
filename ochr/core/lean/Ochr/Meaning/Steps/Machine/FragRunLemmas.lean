import Ochr.Meaning.Steps.Machine.FragDecs
import Ochr.Meaning.Steps.FragSeq
import Ochr.Meaning.Steps.FragSeqB
import Ochr.Meaning.Steps.FragLet

/-!
# The fragment's checker states across the checker's steps (machine lane, machine6; for `FragRun`)

`FSt`/`FStT` carried across the changes a fragment term's run makes: a change of values that keeps
the environment's skeleton and adds no loan or borrow (`FStT.mono`: a write, an end), a number or
`()` pushed in flight (`FSt.pushNum`), a variable lent at the counter (`FSt.lend`), a `let`'s drop.
`Fresh`: the label counter above every label in the environment, which `FSt` does not say and `&x`
needs (machine6's finding: without it `FragRun` is false).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope
open Ochr.Meaning.Steps.Form

/-- The label counter above every label of the environment (a fragment environment's labels are its
positions' loans and borrows). -/
def Fresh (s : MState) : Prop :=
  ∀ q ∈ allPos s.env, ∀ l, (valAt s.env q = .loan l ∨ ∃ w, valAt s.env q = .borrow l w) → l < s.nextLoan

theorem lookup_val {E : Env} {f j : Nat} {b : Binding} (hb : E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b) :
    valAt E (.bind f j) = b.val := by
  rcases hfr : E[f]? with _ | fr
  · rw [hfr] at hb; cases hb
  · rw [hfr] at hb; simp only [Option.bind_some] at hb
    rw [valAt_bind_eq, hfr]; simp [hb]

/-- Two environments with one skeleton: the same positions, variables, bindings' stored types and
readings, frames, and top frame's number of temporaries. -/
structure SameSkel (E E' : Env) : Prop where
  allPos : allPos E' = allPos E
  ck : ∀ i, ckVarPos E' i = ckVarPos E i
  lk : ∀ (f j : Nat) (b' : Binding), E'[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b' →
    ∃ b, E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧ b'.ty = b.ty ∧ b'.decl = b.decl
  lk' : ∀ (f j : Nat) (b : Binding), E[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    ∃ b', E'[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b'
  size : E'.size = E.size
  topT : ∀ fr, E[E.size - 1]? = some fr → ∃ fr', E'[E'.size - 1]? = some fr' ∧ fr'.temps.size = fr.temps.size

theorem SameSkel.refl (E : Env) : SameSkel E E :=
  ⟨rfl, fun _ => rfl, fun _ _ b h => ⟨b, h, rfl, rfl⟩, fun _ _ b h => ⟨b, h⟩, rfl, fun fr h => ⟨fr, h, rfl⟩⟩

theorem SameSkel.trans {E₁ E₂ E₃ : Env} (h₁ : SameSkel E₁ E₂) (h₂ : SameSkel E₂ E₃) : SameSkel E₁ E₃ := by
  refine ⟨h₂.allPos.trans h₁.allPos, fun i => (h₂.ck i).trans (h₁.ck i), fun f j b h => ?_, fun f j b h => ?_,
    h₂.size.trans h₁.size, fun fr h => ?_⟩
  · obtain ⟨b₂, hb₂, e1, e2⟩ := h₂.lk f j b h
    obtain ⟨b₁, hb₁, e3, e4⟩ := h₁.lk f j b₂ hb₂
    exact ⟨b₁, hb₁, e1.trans e3, e2.trans e4⟩
  · obtain ⟨b₂, hb₂⟩ := h₁.lk' f j b h
    exact h₂.lk' f j b₂ hb₂
  · obtain ⟨fr₂, h2, e2⟩ := h₁.topT fr h
    obtain ⟨fr₃, h3, e3⟩ := h₂.topT fr₂ h2
    exact ⟨fr₃, h3, e3.trans e2⟩

theorem topTemps_size_setAtE (E : Env) (p : Pos) (w : Value) (fr : Frame) (hfr : E[E.size - 1]? = some fr) :
    ∃ fr', (Env.setAtE E p w)[(Env.setAtE E p w).size - 1]? = some fr' ∧ fr'.temps.size = fr.temps.size := by
  have hs : (Env.setAtE E p w).size = E.size := size_setAtE_any _ _ _
  rw [hs]
  cases p with
  | bind f j =>
    simp only [Env.setAtE, Array.getElem?_modify, hfr]
    split <;> exact ⟨_, rfl, rfl⟩
  | temp f i =>
    simp only [Env.setAtE, Array.getElem?_modify, hfr]
    split
    · exact ⟨_, rfl, by simp [Array.set!]⟩
    · exact ⟨_, rfl, rfl⟩

theorem SameSkel.setAtE (E : Env) (p : Pos) (w : Value) : SameSkel E (Env.setAtE E p w) :=
  ⟨allPos_setAtE _ _ _, fun i => ckVarPos_setAtE_any (E := E) (w := w) p i,
    fun f j b' h => by obtain ⟨b, hb, e1, e2⟩ := lookup_setAtE_decl h; exact ⟨b, hb, e1.symm, e2.symm⟩,
    fun f j b h => (lookup_setAtE_fwd' (p := p) (v := w) h).imp fun _ h => h.1,
    size_setAtE_any _ _ _, fun fr h => topTemps_size_setAtE E p w fr h⟩

/-- **`FStT` across a change of values with one skeleton that adds no loan or borrow**: the new
environment's values are fragment values; its temporaries hold numbers, `()` or borrows; its loans and
borrows were there (at the same positions), and still meet each other; each variable holds what its
type admits. -/
theorem _root_.Ochr.Meaning.Steps.Form.FStT.mono {Γ : List Form.FT} {s s' : MState} (h : FStT Γ s) (hs : SameSkel s.env s'.env)
    (hloan : ∀ q l, valAt s'.env q = .loan l → valAt s.env q = .loan l)
    (hbor : ∀ q l w, valAt s'.env q = .borrow l w → ∃ w', valAt s.env q = .borrow l w')
    (hvals : ∀ q ∈ allPos s'.env, FVal (valAt s'.env q))
    (htemps : ∀ f i, Pos.temp f i ∈ allPos s'.env → (valAt s'.env (.temp f i)).Num ∨
      valAt s'.env (.temp f i) = .unit ∨ ∃ l c, valAt s'.env (.temp f i) = .borrow l c)
    (hheld : ∀ q l, q ∈ allPos s'.env → valAt s'.env q = .loan l → ∃ q' c, q' ∈ allPos s'.env ∧
      valAt s'.env q' = .borrow l c)
    (hlender : ∀ q l c, q ∈ allPos s'.env → valAt s'.env q = .borrow l c → ∃ q', q' ∈ allPos s'.env ∧
      valAt s'.env q' = .loan l)
    (hholds : ∀ i A f j, Γ[i]? = some A → ckVarPos s.env i = some (.bind f j) → A.holds (valAt s'.env (.bind f j))) :
    FStT Γ s' := by
  have hA : ∀ q, q ∈ allPos s'.env → q ∈ allPos s.env := fun q hq => hs.allPos ▸ hq
  refine ⟨hvals, htemps, fun q q' l hq hq' e e' => h.loan1 q q' l (hA q hq) (hA q' hq') (hloan q l e) (hloan q' l e'),
    fun q q' l w w' hq hq' e e' => ?_, hheld, hlender, fun i A hi => ?_, fun f j f' j' l c hq hq' e e' => ?_,
    fun f j b l hb e => ?_, by rw [hs.size]; exact h.frame, fun f i l c hq e fr hfr => ?_⟩
  · obtain ⟨u, hu⟩ := hbor q l w e
    obtain ⟨u', hu'⟩ := hbor q' l w' e'
    exact h.bor1 q q' l u u' (hA q hq) (hA q' hq') hu hu'
  · obtain ⟨f, j, b, hck, hb, hty, hrd, -⟩ := h.top i A hi
    obtain ⟨b', hb'⟩ := hs.lk' f j b hb
    obtain ⟨b₀, hb₀, e1, e2⟩ := hs.lk f j b' hb'
    rw [hb] at hb₀; cases hb₀
    refine ⟨f, j, b', by rw [hs.ck]; exact hck, hb', by rw [e1, hty], by rw [e2, hrd], ?_⟩
    rw [← lookup_val hb']; exact hholds i A f j hi hck
  · obtain ⟨u, hu⟩ := hbor _ l c e'
    exact h.order f j f' j' l u (hA _ hq) (hA _ hq') (hloan _ l e) hu
  · obtain ⟨b₀, hb₀, e1, e2⟩ := hs.lk f j b hb
    have hv := hloan _ l (by rw [lookup_val hb]; exact e)
    rw [lookup_val hb₀] at hv
    obtain ⟨h1, h2⟩ := h.lent f j b₀ l hb₀ hv
    exact ⟨e1.trans h1, e2.trans h2⟩
  · obtain ⟨u, hu⟩ := hbor _ l c e
    obtain ⟨fr₀, hfr₀⟩ : ∃ fr₀, s.env[s.env.size - 1]? = some fr₀ :=
      ⟨_, Array.getElem?_eq_getElem (by have := h.frame; omega : s.env.size - 1 < s.env.size)⟩
    obtain ⟨fr', hfr', ht⟩ := hs.topT fr₀ hfr₀
    rw [hfr] at hfr'; cases hfr'
    obtain ⟨h1, h2⟩ := h.tempLast f i l u (hA _ hq) hu fr₀ hfr₀
    exact ⟨by rw [h1, hs.size], by rw [h2, ht]⟩

/-- A fragment state with nothing in flight is one with a value in flight. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.toT {Γ : List Form.FT} {s : MState} (h : FSt Γ s) : FStT Γ s := by
  refine ⟨h.vals, fun f i hq => (h.temps f i hq).elim .inl (fun e => .inr (.inl e)), h.loan1, h.bor1,
    fun q l hq e => ?_, h.lender, h.top, h.order, h.lent, h.frame, fun f i l c hq e => ?_⟩
  · obtain ⟨f, j, c, hp, hy⟩ := h.held q l hq e
    exact ⟨_, c, hp, hy⟩
  · rcases h.temps f i hq with hn | hu
    · rw [e] at hn; cases hn
    · rw [e] at hu; cases hu

/-- A state with a value in flight whose temporaries hold no borrow is one with nothing in flight. -/
theorem _root_.Ochr.Meaning.Steps.Form.FStT.toFSt {Γ : List Form.FT} {s : MState} (h : FStT Γ s)
    (ht : ∀ f i, Pos.temp f i ∈ allPos s.env → (valAt s.env (.temp f i)).Num ∨ valAt s.env (.temp f i) = .unit) :
    FSt Γ s := by
  refine ⟨h.vals, ht, h.loan1, h.bor1, fun q l hq e => ?_, h.lender, h.top, h.order, h.lent, h.frame⟩
  obtain ⟨q', c, hq', hy⟩ := h.held q l hq e
  cases q' with
  | bind f j => exact ⟨f, j, c, hq', hy⟩
  | temp f i =>
    rcases ht f i hq' with hn | hu
    · rw [hy] at hn; cases hn
    · rw [hy] at hu; cases hu

theorem _root_.Ochr.Meaning.Steps.Form.FStT.of_erase {Γ : List Form.FT} {a b : MState} (he : a.env.erase = b.env.erase) (h : FStT Γ a) : FStT Γ b := by
  have hv : ∀ q, valAt b.env q = valAt a.env q := fun q => by rw [← valAt_erase, ← he, valAt_erase]
  have ha : allPos b.env = allPos a.env := by rw [← allPos_erase, ← he, allPos_erase]
  have hl : ∀ f j, b.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = a.env[f]?.bind (fun fr : Frame => fr.binds[j]?) :=
    fun f j => by rw [← lookup_erase, ← he, lookup_erase]
  have hc : ∀ i, ckVarPos b.env i = ckVarPos a.env i := fun i => by rw [← ckVarPos_erase, ← he, ckVarPos_erase]
  have hsz : b.env.size = a.env.size := by
    have := congrArg Array.size he; simp only [Env.erase_size] at this; exact this.symm
  have hsk : SameSkel a.env b.env := by
    refine ⟨ha, hc, fun f j b' h => ⟨b', by rw [← hl]; exact h, rfl, rfl⟩, fun f j b' h => ⟨b', by rw [hl]; exact h⟩,
      hsz, fun fr hfr => ?_⟩
    obtain ⟨fr', h1, h2⟩ := top_of_erase_temps he hfr
    exact ⟨fr', h1, by rw [h2]⟩
  exact h.mono hsk (fun q l e => by rw [← hv]; exact e) (fun q l w e => ⟨w, by rw [← hv]; exact e⟩)
    (fun q hq => by rw [hv]; exact h.vals q (ha ▸ hq))
    (fun f i hq => by rw [hv]; exact h.temps f i (ha ▸ hq))
    (fun q l hq e => by
      obtain ⟨q', c, hq', hy⟩ := h.held q l (ha ▸ hq) (by rw [← hv]; exact e)
      exact ⟨q', c, ha ▸ hq', by rw [hv]; exact hy⟩)
    (fun q l c hq e => by
      obtain ⟨q', hq', hx⟩ := h.lender q l c (ha ▸ hq) (by rw [← hv]; exact e)
      exact ⟨q', ha ▸ hq', by rw [hv]; exact hx⟩)
    (fun i A f j hi hck => by
      obtain ⟨f', j', b', hck', hb', -, -, hh⟩ := h.top i A hi
      rw [hck] at hck'; cases hck'
      rw [hv, lookup_val hb']; exact hh)

theorem Fresh.of_erase {a b : MState} (he : a.env.erase = b.env.erase) (hn : a.nextLoan ≤ b.nextLoan) (h : Fresh a) :
    Fresh b := by
  have hv : ∀ q, valAt b.env q = valAt a.env q := fun q => by rw [← valAt_erase, ← he, valAt_erase]
  have ha : allPos b.env = allPos a.env := by rw [← allPos_erase, ← he, allPos_erase]
  intro q hq l e
  rw [hv] at e
  exact Nat.lt_of_lt_of_le (h q (ha ▸ hq) l e) hn

/-! ## A value pushed in flight -/

theorem push_view {s : MState} {fr : Frame} (hfr : s.env[s.env.size - 1]? = some fr) (v : Value) (T : Option Value) :
    allPos (s.withTempT v T).env = allPos s.env ++ [.temp (s.env.size - 1) fr.temps.size] ∧
    valAt (s.withTempT v T).env (.temp (s.env.size - 1) fr.temps.size) = v ∧
    (∀ q ∈ allPos s.env, valAt (s.withTempT v T).env q = valAt s.env q) ∧
    Pos.temp (s.env.size - 1) fr.temps.size ∉ allPos s.env ∧
    (∀ i, ckVarPos (s.withTempT v T).env i = ckVarPos s.env i) ∧
    (∀ (f j : Nat), (s.withTempT v T).env[f]?.bind (fun fr : Frame => fr.binds[j]?) = s.env[f]?.bind (fun fr : Frame => fr.binds[j]?)) ∧
    (s.withTempT v T).env.size = s.env.size ∧
    ∃ fr', (s.withTempT v T).env[(s.withTempT v T).env.size - 1]? = some fr' ∧ fr'.temps.size = fr.temps.size + 1 := by
  have hne : 0 < s.env.size := by
    rcases Nat.eq_zero_or_pos s.env.size with e | e
    · rw [Array.getElem?_eq_none (by omega)] at hfr; cases hfr
    · exact e
  refine ⟨by rw [allPos_withTempT', allPos_pushTempE _ _ fr hfr hne], by rw [valAt_withTempT', valAt_pushTempE_new _ _ fr hfr],
    fun q hq => by rw [valAt_withTempT', valAt_pushTempE_mem (E := s.env) (v := v) (fr := fr) (hfr := hfr) hq],
    fun hm => ?_, fun i => by rw [withTempT_env, ckVarPos_pushTempTyE], fun f j => by rw [withTempT_env, binds_pushTempTyE],
    size_withTempT _ _ _, ?_⟩
  · obtain ⟨fr', hf', hi⟩ := mem_allPos_temp _ _ _ hm
    rw [hfr] at hf'; cases hf'; exact Nat.lt_irrefl _ hi
  · refine ⟨{ fr with temps := fr.temps.push v, tempTys := fr.tempTys.push T }, ?_, by simp⟩
    rw [size_withTempT, withTempT_env]
    simp only [Env.pushTempTyE, Array.getElem?_modify, if_true, hfr, Option.map_some]

/-- **A number or `()` pushed in flight** from a fragment state. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.pushNum {Γ : List Form.FT} {s : MState} (h : FSt Γ s) {v : Value}
    (hv : v.Num ∨ v = .unit) (T : Option Value) : FStT Γ (s.withTempT v T) := by
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by have := h.frame; omega : s.env.size - 1 < s.env.size)⟩
  obtain ⟨hA, hnew, hold, hnm, hck, hlk, hsz, fr', hfr', hts⟩ := push_view hfr v T
  have hcases : ∀ q ∈ allPos (s.withTempT v T).env, q = .temp (s.env.size - 1) fr.temps.size ∨ q ∈ allPos s.env := by
    intro q hq; rw [hA, List.mem_append, List.mem_singleton] at hq; exact hq.symm
  have hmem : ∀ q ∈ allPos s.env, q ∈ allPos (s.withTempT v T).env := fun q hq => by
    rw [hA]; exact List.mem_append_left _ hq
  have hnl : ∀ l, v ≠ .loan l := fun l e => by rcases hv with hn | hu <;> (rw [e] at *; cases ‹_›)
  have hnb : ∀ l w, v ≠ .borrow l w := fun l w e => by rcases hv with hn | hu <;> (rw [e] at *; cases ‹_›)
  -- every position's old value, or `v`
  have hval : ∀ q ∈ allPos (s.withTempT v T).env, (q = .temp (s.env.size - 1) fr.temps.size ∧
      valAt (s.withTempT v T).env q = v) ∨ (q ∈ allPos s.env ∧ valAt (s.withTempT v T).env q = valAt s.env q) := by
    intro q hq
    rcases hcases q hq with rfl | hq'
    · exact .inl ⟨rfl, hnew⟩
    · exact .inr ⟨hq', hold q hq'⟩
  refine ⟨fun q hq => ?_, fun f i hq => ?_, fun q q' l hq hq' e e' => ?_, fun q q' l w w' hq hq' e e' => ?_,
    fun q l hq e => ?_, fun q l c hq e => ?_, fun i A hi => ?_, fun f j f' j' l c hq hq' e e' => ?_,
    fun f j b l hb e => ?_, by rw [hsz]; exact h.frame, fun f i l c hq e fr₀ hfr₀ => ?_⟩
  · rcases hval q hq with ⟨-, e⟩ | ⟨hq', e⟩ <;> rw [e]
    · rcases hv with hn | hu
      · exact .num hn
      · rw [hu]; exact .unit
    · exact h.vals q hq'
  · rcases hval _ hq with ⟨-, e⟩ | ⟨hq', e⟩ <;> rw [e]
    · rcases hv with hn | hu
      · exact .inl hn
      · exact .inr (.inl hu)
    · rcases h.temps f i hq' with hn | hu
      · exact .inl hn
      · exact .inr (.inl hu)
  · rcases hval q hq with ⟨-, e1⟩ | ⟨hq1, e1⟩
    · rw [e1] at e; exact absurd e (hnl l)
    rcases hval q' hq' with ⟨-, e2⟩ | ⟨hq2, e2⟩
    · rw [e2] at e'; exact absurd e' (hnl l)
    rw [e1] at e; rw [e2] at e'
    exact h.loan1 q q' l hq1 hq2 e e'
  · rcases hval q hq with ⟨-, e1⟩ | ⟨hq1, e1⟩
    · rw [e1] at e; exact absurd e (hnb l w)
    rcases hval q' hq' with ⟨-, e2⟩ | ⟨hq2, e2⟩
    · rw [e2] at e'; exact absurd e' (hnb l w')
    rw [e1] at e; rw [e2] at e'
    exact h.bor1 q q' l w w' hq1 hq2 e e'
  · rcases hval q hq with ⟨-, e1⟩ | ⟨hq1, e1⟩
    · rw [e1] at e; exact absurd e (hnl l)
    rw [e1] at e
    obtain ⟨f, j, c, hp, hy⟩ := h.held q l hq1 e
    exact ⟨_, c, hmem _ hp, by rw [hold _ hp]; exact hy⟩
  · rcases hval q hq with ⟨-, e1⟩ | ⟨hq1, e1⟩
    · rw [e1] at e; exact absurd e (hnb l c)
    rw [e1] at e
    obtain ⟨q', hq', hx⟩ := h.lender q l c hq1 e
    exact ⟨q', hmem _ hq', by rw [hold _ hq']; exact hx⟩
  · obtain ⟨f, j, b, hck', hb, h1, h2, h3⟩ := h.top i A hi
    exact ⟨f, j, b, by rw [hck]; exact hck', by rw [hlk]; exact hb, h1, h2, h3⟩
  · rcases hval _ hq with ⟨e0, -⟩ | ⟨hq1, e1⟩
    · cases e0
    rcases hval _ hq' with ⟨e0, -⟩ | ⟨hq2, e2⟩
    · cases e0
    rw [e1] at e; rw [e2] at e'
    exact h.order f j f' j' l c hq1 hq2 e e'
  · rw [hlk] at hb; exact h.lent f j b l hb e
  · rcases hval _ hq with ⟨-, e1⟩ | ⟨hq1, e1⟩
    · rw [e1] at e; exact absurd e (hnb l c)
    rw [e1] at e
    rcases h.temps f i hq1 with hn | hu
    · rw [e] at hn; cases hn
    · rw [e] at hu; cases hu

theorem Fresh.pushNum {s : MState} (h : Fresh s) {v : Value} (hv : v.Num ∨ v = .unit) (T : Option Value)
    (hne : 0 < s.env.size) : Fresh (s.withTempT v T) := by
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : s.env.size - 1 < s.env.size)⟩
  obtain ⟨hA, hnew, hold, -⟩ := push_view hfr v T
  intro q hq l e
  rw [hA, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · rw [hold q hq] at e; exact h q hq l e
  · rw [hnew] at e
    rcases e with e | ⟨w, e⟩ <;> rcases hv with hn | hu
    · rw [e] at hn; cases hn
    · rw [e] at hu; cases hu
    · rw [e] at hn; cases hn
    · rw [e] at hu; cases hu

/-- Dropping the value in flight keeps the counter above every label. -/
theorem Fresh.untemp {s : MState} {v : Value} {T : Option Value} (h : Fresh (s.withTempT v T)) (hne : 0 < s.env.size) :
    Fresh s := by
  obtain ⟨fr, hfr⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : s.env.size - 1 < s.env.size)⟩
  obtain ⟨hA, -, hold, -⟩ := push_view hfr v T
  intro q hq l e
  have := h q (by rw [hA]; exact List.mem_append_left _ hq) l (by rw [hold q hq]; exact e)
  exact this

/-! ## A write, an end -/

theorem valAt_setAt_eq (E : Env) (p : Pos) (w : Value) (hp : p ∈ allPos E) (q : Pos) :
    valAt (Env.setAtE E p w) q = if q = p then w else valAt E q := by
  split
  · next e => subst e; exact Ochr.Meaning.Steps.valAt_setAtE_self _ hp
  · next e => exact valAt_setAtE_other _ _ _ _ e

/-- The variable a fragment state's top typing puts at a position holding a loan is a number variable. -/
theorem _root_.Ochr.Meaning.Steps.Form.FStT.holds_loan {Γ : List Form.FT} {s : MState} (h : FStT Γ s) {i : Nat} {A : Form.FT} {f j l : Nat}
    (hi : Γ[i]? = some A) (hck : ckVarPos s.env i = some (.bind f j)) (hx : valAt s.env (.bind f j) = .loan l) :
    A = .nat := by
  obtain ⟨f', j', b, hck', hb, -, -, hh⟩ := h.top i A hi
  rw [hck] at hck'; cases hck'
  rw [← lookup_val hb, hx] at hh
  cases A with
  | nat => rfl
  | unit => rcases hh with e | e <;> cases e
  | ref => rcases hh with e | ⟨_, _, e, _⟩ <;> cases e

theorem _root_.Ochr.Meaning.Steps.Form.FStT.holds_at {Γ : List Form.FT} {s : MState} (h : FStT Γ s) {i : Nat} {A : Form.FT} {f j : Nat}
    (hi : Γ[i]? = some A) (hck : ckVarPos s.env i = some (.bind f j)) : A.holds (valAt s.env (.bind f j)) := by
  obtain ⟨f', j', b, hck', hb, -, -, hh⟩ := h.top i A hi
  rw [hck] at hck'; cases hck'
  rw [lookup_val hb]; exact hh

theorem holds_bot (A : Form.FT) : A.holds .bot := by
  cases A
  · exact .inr (.inl rfl)
  · exact .inr rfl
  · exact .inl rfl

/-- **A write at a binding that keeps its labels** (a number or `⊥` over a number or `⊥`; a borrow's
content replaced). -/
theorem _root_.Ochr.Meaning.Steps.Form.FStT.setAt {Γ : List Form.FT} {s : MState} (h : FStT Γ s) {f j : Nat}
    {w : Value} (hp : Pos.bind f j ∈ allPos s.env) (hw : FVal w)
    (hl : ∀ l, w = .loan l ↔ valAt s.env (.bind f j) = .loan l)
    (hb : ∀ l, (∃ c, w = .borrow l c) ↔ (∃ c, valAt s.env (.bind f j) = .borrow l c))
    (hholds : ∀ i A, Γ[i]? = some A → ckVarPos s.env i = some (.bind f j) → A.holds w) :
    FStT Γ { s with env := Env.setAtE s.env (.bind f j) w } := by
  have hv := valAt_setAt_eq s.env (.bind f j) w hp
  have hA : allPos (Env.setAtE s.env (.bind f j) w) = allPos s.env := allPos_setAtE _ _ _
  refine h.mono (SameSkel.setAtE s.env (.bind f j) w) (fun q l e => ?_) (fun q l c e => ?_) (fun q hq => ?_) (fun f' i hq => ?_)
    (fun q l hq e => ?_) (fun q l c hq e => ?_) (fun i A f' j' hi hck => ?_)
  · show valAt s.env q = _
    have e' : valAt (Env.setAtE s.env (.bind f j) w) q = .loan l := e
    rw [hv] at e'; split at e'
    · next hq => subst hq; exact (hl l).mp e'
    · exact e'
  · have e' : valAt (Env.setAtE s.env (.bind f j) w) q = .borrow l c := e
    rw [hv] at e'; split at e'
    · next hq => subst hq; exact (hb l).mp ⟨c, e'⟩
    · exact ⟨c, e'⟩
  · show FVal (valAt (Env.setAtE s.env (.bind f j) w) q)
    rw [hv]; split
    · exact hw
    · exact h.vals q (hA ▸ hq)
  · show _ ∨ _
    have hq' : Pos.temp f' i ∈ allPos s.env := hA ▸ hq
    rw [show valAt (Env.setAtE s.env (.bind f j) w) (.temp f' i) = valAt s.env (.temp f' i) by
      rw [hv, if_neg (by intro e; cases e)]]
    exact h.temps f' i hq'
  · have hq' : q ∈ allPos s.env := hA ▸ hq
    have e' : valAt (Env.setAtE s.env (.bind f j) w) q = .loan l := e
    have hold : valAt s.env q = .loan l := by
      rw [hv] at e'; split at e'
      · next hq => subst hq; exact (hl l).mp e'
      · exact e'
    obtain ⟨q', c, hq'', hy⟩ := h.held q l hq' hold
    by_cases e2 : q' = .bind f j
    · subst e2
      obtain ⟨c', hc'⟩ := (hb l).mpr ⟨c, hy⟩
      exact ⟨_, c', by show _ ∈ allPos (Env.setAtE _ _ _); rw [hA]; exact hq'', by
        show valAt (Env.setAtE s.env (.bind f j) w) _ = _; rw [hv, if_pos rfl]; exact hc'⟩
    · exact ⟨q', c, by show _ ∈ allPos (Env.setAtE _ _ _); rw [hA]; exact hq'', by
        show valAt (Env.setAtE s.env (.bind f j) w) _ = _; rw [hv, if_neg e2]; exact hy⟩
  · have hq' : q ∈ allPos s.env := hA ▸ hq
    have e' : valAt (Env.setAtE s.env (.bind f j) w) q = .borrow l c := e
    obtain ⟨c₀, hold⟩ : ∃ c₀, valAt s.env q = .borrow l c₀ := by
      rw [hv] at e'; split at e'
      · next hq => subst hq; exact (hb l).mp ⟨c, e'⟩
      · exact ⟨c, e'⟩
    obtain ⟨q', hq'', hx⟩ := h.lender q l c₀ hq' hold
    refine ⟨q', by show _ ∈ allPos (Env.setAtE _ _ _); rw [hA]; exact hq'', ?_⟩
    show valAt (Env.setAtE s.env (.bind f j) w) _ = _
    rw [hv]; split
    · next e2 => subst e2; exact (hl l).mpr hx
    · exact hx
  · rw [hv]; split
    · next e2 => cases e2; exact hholds i A hi hck
    · exact h.holds_at hi hck

theorem Fresh.setAt {s : MState} (h : Fresh s) {p : Pos} {w : Value} (hp : p ∈ allPos s.env)
    (hw : ∀ l, (w = .loan l ∨ ∃ c, w = .borrow l c) → l < s.nextLoan) :
    Fresh { s with env := Env.setAtE s.env p w } := by
  intro q hq l e
  have hq' : q ∈ allPos s.env := by have := hq; rwa [show allPos (Env.setAtE s.env p w) = allPos s.env from allPos_setAtE _ _ _] at this
  have e' : valAt (Env.setAtE s.env p w) q = .loan l ∨ ∃ c, valAt (Env.setAtE s.env p w) q = .borrow l c := e
  rw [valAt_setAt_eq _ _ _ hp] at e'
  split at e'
  · exact hw l e'
  · exact h q hq' l e'

/-- **The end of one borrow held at a binding** (the lender a binding): a fragment state again. -/
theorem _root_.Ochr.Meaning.Steps.Form.FStT.ofEnd {Γ : List Form.FT} {s : MState} (h : FStT Γ s)
    {fx jx fy jy l : Nat} {c : Value} (hF : EndAt s.env (.bind fx jx) (.bind fy jy) l c) :
    FStT Γ { s with env := endE s.env (.bind fx jx) (.bind fy jy) c } := by
  have hv := hF.valAt_endE
  have hA : allPos (endE s.env (.bind fx jx) (.bind fy jy) c) = allPos s.env := FEnd.allPos_endE
  have hne := hF.ne
  refine h.mono ((SameSkel.setAtE s.env (.bind fy jy) .bot).trans (SameSkel.setAtE _ (.bind fx jx) c)) (fun q m e => ?_) (fun q m c' e => ?_)
    (fun q hq => hF.vals_endE q hq) (fun f' i hq => ?_) (fun q m hq e => ?_) (fun q m c' hq e => ?_)
    (fun i A f' j' hi hck => ?_)
  · have e' : valAt (endE s.env (.bind fx jx) (.bind fy jy) c) q = .loan m := e
    rw [hv] at e'
    split at e'
    · exact absurd e' (FVal.num_ne_loan hF.c m)
    · split at e'
      · cases e'
      · exact e'
  · have e' : valAt (endE s.env (.bind fx jx) (.bind fy jy) c) q = .borrow m c' := e
    rw [hv] at e'
    split at e'
    · exact absurd e' (hF.c.not_borrow m c')
    · split at e'
      · cases e'
      · exact ⟨c', e'⟩
  · show _ ∨ _
    have hq' : Pos.temp f' i ∈ allPos s.env := hA ▸ hq
    rw [show valAt (endE s.env (.bind fx jx) (.bind fy jy) c) (.temp f' i) = valAt s.env (.temp f' i) by
      rw [hv, if_neg (by intro e; cases e), if_neg (by intro e; cases e)]]
    exact h.temps f' i hq'
  · have hq' : q ∈ allPos s.env := hA ▸ hq
    have e' : valAt (endE s.env (.bind fx jx) (.bind fy jy) c) q = .loan m := e
    rw [hv] at e'
    split at e'
    · exact absurd e' (FVal.num_ne_loan hF.c m)
    split at e'
    · cases e'
    next hqx hqy =>
    have hml : m ≠ l := fun e2 => by subst e2; exact hqx (hF.loan1 q hq' e')
    obtain ⟨q', c₁, hq'', hy⟩ := h.held q m hq' e'
    have h1 : q' ≠ .bind fx jx := fun e2 => by subst e2; rw [hF.x] at hy; cases hy
    have h2 : q' ≠ .bind fy jy := fun e2 => by subst e2; rw [hF.y] at hy; cases hy; exact hml rfl
    exact ⟨q', c₁, hA ▸ hq'', by rw [hv, if_neg h1, if_neg h2]; exact hy⟩
  · have hq' : q ∈ allPos s.env := hA ▸ hq
    have e' : valAt (endE s.env (.bind fx jx) (.bind fy jy) c) q = .borrow m c' := e
    rw [hv] at e'
    split at e'
    · exact absurd e' (hF.c.not_borrow m c')
    split at e'
    · cases e'
    next hqx hqy =>
    have hml : m ≠ l := fun e2 => by subst e2; exact hqy (hF.bor1 q hq' c' e')
    obtain ⟨q', hq'', hx⟩ := h.lender q m c' hq' e'
    have h1 : q' ≠ .bind fx jx := fun e2 => by subst e2; rw [hF.x] at hx; cases hx; exact hml rfl
    have h2 : q' ≠ .bind fy jy := fun e2 => by subst e2; rw [hF.y] at hx; cases hx
    exact ⟨q', hA ▸ hq'', by rw [hv, if_neg h1, if_neg h2]; exact hx⟩
  · rw [hv]
    split
    · next e2 =>
      cases e2
      rw [h.holds_loan hi hck hF.x]; exact .inl hF.c
    · split
      · exact holds_bot A
      · exact h.holds_at hi hck

theorem Fresh.ofEnd {s : MState} (h : Fresh s) {px ph : Pos} {l : Nat} {c : Value} (hF : EndAt s.env px ph l c) :
    Fresh { s with env := endE s.env px ph c } := by
  intro q hq l' e
  have hq' : q ∈ allPos s.env := by have := hq; rwa [show allPos (endE s.env px ph c) = allPos s.env from FEnd.allPos_endE] at this
  have e' : valAt (endE s.env px ph c) q = .loan l' ∨ ∃ w, valAt (endE s.env px ph c) q = .borrow l' w := e
  rw [hF.valAt_endE] at e'
  split at e'
  · rcases e' with e' | ⟨w, e'⟩
    · exact absurd e' (FVal.num_ne_loan hF.c l')
    · exact absurd e' (hF.c.not_borrow l' w)
  · split at e'
    · rcases e' with e' | ⟨w, e'⟩ <;> cases e'
    · exact h q hq' l' e'

/-! ## `&x`: a number variable lent at the counter -/

/-- **`&x` of a number variable from a fragment state** whose counter is above every label: `x` lent at
the counter, the borrow in flight. -/
theorem _root_.Ochr.Meaning.Steps.Form.FSt.lend {Γ : List Form.FT} {s : MState} (h : FSt Γ s) (hfr : Fresh s)
    {f j : Nat} {bx : Binding} (hbx : s.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some bx) (hc : bx.val.Num)
    (hty : bx.ty = some .tNat ∧ bx.decl = .other) (T : Option Value) :
    FStT Γ (({ s with env := Env.setAtE s.env (.bind f j) (.loan s.nextLoan), nextLoan := s.nextLoan + 1 } : MState).withTempT
      (.borrow s.nextLoan bx.val) T) ∧
    Fresh (({ s with env := Env.setAtE s.env (.bind f j) (.loan s.nextLoan), nextLoan := s.nextLoan + 1 } : MState).withTempT
      (.borrow s.nextLoan bx.val) T) := by
  have hp : Pos.bind f j ∈ allPos s.env := (lookup_pos hbx).1
  have hx : valAt s.env (.bind f j) = bx.val := lookup_val hbx
  generalize hn : s.nextLoan = n at *
  generalize hs1 : ({ s with env := Env.setAtE s.env (.bind f j) (.loan n), nextLoan := n + 1 } : MState) = s1
  have hs1e : s1.env = Env.setAtE s.env (.bind f j) (.loan n) := by rw [← hs1]
  have hs1n : s1.nextLoan = n + 1 := by rw [← hs1]
  obtain ⟨fr, hfr0⟩ : ∃ fr, s.env[s.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by have := h.frame; omega : s.env.size - 1 < s.env.size)⟩
  have hsz1 : s1.env.size = s.env.size := by rw [hs1e]; exact size_setAtE_any _ _ _
  obtain ⟨fr1, hfr1, hts1⟩ := topTemps_size_setAtE s.env (.bind f j) (.loan n) fr hfr0
  rw [← hs1e] at hfr1
  rw [hsz1] at hfr1
  have hfr1' : s1.env[s1.env.size - 1]? = some fr1 := by rw [hsz1]; exact hfr1
  obtain ⟨hA, hnew, hold, hnm, hck, hlk, hsz, fr', hfr', hts⟩ := push_view hfr1' (.borrow n bx.val) T
  rw [hsz1] at hA hnew hnm
  have hA1 : allPos s1.env = allPos s.env := by rw [hs1e]; exact allPos_setAtE _ _ _
  have hv1 : ∀ q, valAt s1.env q = if q = .bind f j then .loan n else valAt s.env q := by
    intro q; rw [hs1e]; exact valAt_setAt_eq _ _ _ hp q
  rw [hts1] at hA hnew hnm
  generalize hpt : Pos.temp (s.env.size - 1) fr.temps.size = pt at hA hnew hnm
  -- the positions of the end state and what they hold
  have hcase : ∀ q ∈ allPos (s1.withTempT (.borrow n bx.val) T).env,
      (q = pt ∧ valAt (s1.withTempT (.borrow n bx.val) T).env q = .borrow n bx.val) ∨
      (q = .bind f j ∧ valAt (s1.withTempT (.borrow n bx.val) T).env q = .loan n) ∨
      (q ∈ allPos s.env ∧ q ≠ .bind f j ∧ valAt (s1.withTempT (.borrow n bx.val) T).env q = valAt s.env q) := by
    intro q hq
    rw [hA, List.mem_append, List.mem_singleton, hA1] at hq
    rcases hq with hq | rfl
    · rw [hold q (hA1 ▸ hq), hv1]
      by_cases e : q = .bind f j
      · exact .inr (.inl ⟨e, by rw [if_pos e]⟩)
      · exact .inr (.inr ⟨hq, e, by rw [if_neg e]⟩)
    · exact .inl ⟨rfl, hnew⟩
  have hmem : ∀ q ∈ allPos s.env, q ∈ allPos (s1.withTempT (.borrow n bx.val) T).env := fun q hq => by
    rw [hA, hA1]; exact List.mem_append_left _ hq
  have hptm : pt ∈ allPos (s1.withTempT (.borrow n bx.val) T).env := by rw [hA]; simp
  have hnmpt : pt ∉ allPos s.env := hA1 ▸ hnm
  have hlt : ∀ q ∈ allPos s.env, ∀ l, (valAt s.env q = .loan l ∨ ∃ w, valAt s.env q = .borrow l w) → l < n :=
    fun q hq l e => hn ▸ hfr q hq l e
  have hnx : ∀ l, bx.val ≠ .loan l := fun l e => by rw [e] at hc; cases hc
  have hnbx : ∀ l w, bx.val ≠ .borrow l w := fun l w e => hc.not_borrow l w e
  refine ⟨⟨fun q hq => ?_, fun f' i hq => ?_, fun q q' l hq hq' e e' => ?_, fun q q' l w w' hq hq' e e' => ?_,
    fun q l hq e => ?_, fun q l c hq e => ?_, fun i A hi => ?_, fun f₁ j₁ f₂ j₂ l c hq hq' e e' => ?_,
    fun f₁ j₁ b l hb e => ?_, by rw [hsz, hsz1]; exact h.frame, fun f' i l c hq e fr₀ hfr₀ => ?_⟩, ?_⟩
  · rcases hcase q hq with ⟨-, e⟩ | ⟨-, e⟩ | ⟨hq', -, e⟩ <;> rw [e]
    · exact .bor n (hx ▸ hc)
    · exact .loan n
    · exact h.vals q hq'
  · rcases hcase _ hq with ⟨-, e⟩ | ⟨e0, -⟩ | ⟨hq', -, e⟩
    · rw [e]; exact .inr (.inr ⟨n, bx.val, rfl⟩)
    · cases e0
    · rw [e]; rcases h.temps f' i hq' with h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
  · -- loan1
    rcases hcase q hq with ⟨-, e1⟩ | ⟨rfl, e1⟩ | ⟨hq1, hx1, e1⟩
    · rw [e1] at e; cases e
    · rw [e1] at e; cases e
      rcases hcase q' hq' with ⟨-, e2⟩ | ⟨rfl, e2⟩ | ⟨hq2, -, e2⟩
      · rw [e2] at e'; cases e'
      · rfl
      · rw [e2] at e'; exact absurd (hlt q' hq2 _ (.inl e')) (Nat.lt_irrefl _)
    · rw [e1] at e
      rcases hcase q' hq' with ⟨-, e2⟩ | ⟨rfl, e2⟩ | ⟨hq2, -, e2⟩
      · rw [e2] at e'; cases e'
      · rw [e2] at e'; cases e'; exact absurd (hlt q hq1 _ (.inl e)) (Nat.lt_irrefl _)
      · rw [e2] at e'; exact h.loan1 q q' l hq1 hq2 e e'
  · -- bor1
    rcases hcase q hq with ⟨rfl, e1⟩ | ⟨-, e1⟩ | ⟨hq1, hx1, e1⟩
    · rw [e1] at e; cases e
      rcases hcase q' hq' with ⟨rfl, e2⟩ | ⟨-, e2⟩ | ⟨hq2, -, e2⟩
      · rfl
      · rw [e2] at e'; cases e'
      · rw [e2] at e'; exact absurd (hlt q' hq2 _ (.inr ⟨w', e'⟩)) (Nat.lt_irrefl _)
    · rw [e1] at e; cases e
    · rw [e1] at e
      rcases hcase q' hq' with ⟨rfl, e2⟩ | ⟨-, e2⟩ | ⟨hq2, -, e2⟩
      · rw [e2] at e'; cases e'; exact absurd (hlt q hq1 _ (.inr ⟨w, e⟩)) (Nat.lt_irrefl _)
      · rw [e2] at e'; cases e'
      · rw [e2] at e'; exact h.bor1 q q' l w w' hq1 hq2 e e'
  · -- held
    rcases hcase q hq with ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨hq1, hx1, e1⟩
    · rw [e1] at e; cases e
    · rw [e1] at e; cases e; exact ⟨pt, bx.val, hptm, hnew⟩
    · rw [e1] at e
      obtain ⟨f₁, j₁, c, hp1, hy⟩ := h.held q l hq1 e
      have hne1 : Pos.bind f₁ j₁ ≠ .bind f j := fun e2 => by rw [e2, hx] at hy; exact hnbx _ _ hy
      refine ⟨_, c, hmem _ hp1, ?_⟩
      rcases hcase _ (hmem _ hp1) with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨-, -, e2⟩
      · rw [← e0] at hnmpt; exact absurd hp1 hnmpt
      · exact absurd e0 hne1
      · rw [e2]; exact hy
  · -- lender
    rcases hcase q hq with ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨hq1, hx1, e1⟩
    · rw [e1] at e; cases e
      refine ⟨.bind f j, hmem _ hp, ?_⟩
      rcases hcase _ (hmem _ hp) with ⟨e0, -⟩ | ⟨-, e2⟩ | ⟨-, hne, -⟩
      · rw [← e0] at hnmpt; exact absurd hp hnmpt
      · exact e2
      · exact absurd rfl hne
    · rw [e1] at e; cases e
    · rw [e1] at e
      obtain ⟨q', hq', hx'⟩ := h.lender q l c hq1 e
      have hne1 : q' ≠ .bind f j := fun e2 => by rw [e2, hx] at hx'; exact hnx _ hx'
      refine ⟨q', hmem _ hq', ?_⟩
      rcases hcase _ (hmem _ hq') with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨-, -, e2⟩
      · rw [← e0] at hnmpt; exact absurd hq' hnmpt
      · exact absurd e0 hne1
      · rw [e2]; exact hx'
  · -- top
    obtain ⟨f₁, j₁, b, hck', hb, h1, h2, h3⟩ := h.top i A hi
    obtain ⟨b', hb', e1, e2⟩ := lookup_setAtE_fwd' (p := .bind f j) (v := .loan n) hb
    refine ⟨f₁, j₁, b', by rw [hck, hs1e, ckVarPos_setAtE_any]; exact hck', by rw [hlk, hs1e]; exact hb',
      by rw [e1, h1], by rw [e2, h2], ?_⟩
    have hv' : b'.val = valAt s1.env (.bind f₁ j₁) := by rw [hs1e]; exact (lookup_val hb').symm
    rw [hv', hv1]
    split
    · next e =>
      cases e
      have hbb : b = bx := by rw [hbx] at hb; exact (Option.some.inj hb).symm
      subst hbb
      cases A with
      | nat => exact .inr (.inr ⟨n, rfl⟩)
      | unit => rcases h3 with e | e <;> rw [e] at hc <;> cases hc
      | ref => rcases h3 with e | ⟨_, _, e, _⟩ <;> rw [e] at hc <;> cases hc
    · rw [lookup_val hb]; exact h3
  · -- order
    have hq1 : Pos.bind f₁ j₁ ∈ allPos s.env := by
      rcases hcase _ hq with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨hq1, -, -⟩
      · rw [← hpt] at e0; cases e0
      · cases e0; exact hp
      · exact hq1
    have hq2 : Pos.bind f₂ j₂ ∈ allPos s.env := by
      rcases hcase _ hq' with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨hq2, -, -⟩
      · rw [← hpt] at e0; cases e0
      · cases e0; exact hp
      · exact hq2
    rcases hcase _ hq' with ⟨e0, -⟩ | ⟨-, e2⟩ | ⟨-, -, e2⟩
    · rw [← hpt] at e0; cases e0
    · rw [e2] at e'; cases e'
    rw [e2] at e'
    rcases hcase _ hq with ⟨e0, -⟩ | ⟨-, e1⟩ | ⟨-, -, e1⟩
    · rw [← hpt] at e0; cases e0
    · rw [e1] at e; cases e; exact absurd (hlt _ hq2 _ (.inr ⟨c, e'⟩)) (Nat.lt_irrefl _)
    · rw [e1] at e; exact h.order f₁ j₁ f₂ j₂ l c hq1 hq2 e e'
  · -- lent
    rw [hlk, hs1e] at hb
    obtain ⟨b₀, hb₀, e1, e2⟩ := lookup_setAtE_decl hb
    have hv' : b.val = valAt (Env.setAtE s.env (.bind f j) (.loan n)) (.bind f₁ j₁) := (lookup_val hb).symm
    rw [valAt_setAt_eq _ _ _ hp] at hv'
    split at hv'
    · next e0 =>
      cases e0
      have hbb : b₀ = bx := by rw [hbx] at hb₀; exact (Option.some.inj hb₀).symm
      subst hbb
      exact ⟨e1 ▸ hty.1, e2 ▸ hty.2⟩
    · rw [hv', lookup_val hb₀] at e
      obtain ⟨h1, h2⟩ := h.lent f₁ j₁ b₀ l hb₀ e
      exact ⟨e1 ▸ h1, e2 ▸ h2⟩
  · -- tempLast
    rcases hcase _ hq with ⟨e0, -⟩ | ⟨e0, -⟩ | ⟨hq1, -, e1⟩
    · rw [← hpt] at e0; cases e0
      rw [hsz, hsz1] at hfr₀
      have : fr₀ = fr' := by rw [hsz, hsz1] at hfr'; rw [hfr'] at hfr₀; exact (Option.some.inj hfr₀).symm
      subst this
      exact ⟨by rw [hsz, hsz1], by rw [hts, hts1]; omega⟩
    · cases e0
    · rw [e1] at e
      rcases h.temps f' i hq1 with h1 | h1
      · rw [e] at h1; cases h1
      · rw [e] at h1; cases h1
  · -- the counter
    intro q hq l e
    show l < s1.nextLoan
    rw [hs1n]
    rcases hcase q hq with ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨hq1, -, e1⟩ <;> rw [e1] at e
    · rcases e with e | ⟨w, e⟩ <;> cases e; omega
    · rcases e with e | ⟨w, e⟩ <;> cases e; omega
    · exact Nat.lt_succ_of_lt (hlt q hq1 l e)

end Ochr.Meaning.Steps.Machine
