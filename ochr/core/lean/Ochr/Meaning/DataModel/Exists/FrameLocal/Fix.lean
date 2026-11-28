import Ochr.Meaning.DataModel.Exists.FrameLocal.Agree

/-!
# Frame locality, part 5b: a closure's body frame across the transform (exists4)

The `.fix` clause runs the body in `s.under` (a fresh bottom frame) with `self` and the parameters
pushed on the top frame and the borrow parameters' cells on frame 0 (`fixBodyAt`). Across
`qset Q β'` the varied positions move up a frame (`qset_under`: `Qup Q`, `βup β'`), the pushes
commute, the body's variables avoid the moved `Q` exactly when the closure's did, and the body's
output, read at full argument lists, is the same.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning SState
open Classical

/-! ## The top frame grows by `k` bindings -/

/-- `t`'s top frame is `s`'s with `k` more bindings (`varPos` reads only this). -/
def TopGrow (s t : SState) (k : Nat) : Prop :=
  t.env.length = s.env.length ∧ t.env.getLast?.map (·.binds.length) = s.env.getLast?.map (·.binds.length + k)

theorem TopGrow.refl (s : SState) : TopGrow s s 0 := ⟨rfl, by cases s.env.getLast? <;> rfl⟩

theorem TopGrow.of_env {s t : SState} (h : t.env = s.env) : TopGrow s t 0 := by
  refine ⟨by rw [h], ?_⟩; rw [h]; cases s.env.getLast? <;> rfl

theorem TopGrow.trans {s t u : SState} {k m : Nat} (h₁ : TopGrow s t k) (h₂ : TopGrow t u m) : TopGrow s u (k + m) := by
  refine ⟨h₂.1.trans h₁.1, ?_⟩
  rw [h₂.2]
  have e := h₁.2
  cases hs : s.env.getLast? with
  | none => rw [hs] at e; cases ht : t.env.getLast? <;> simp_all
  | some fr =>
    rw [hs] at e
    cases ht : t.env.getLast? with
    | none => rw [ht] at e; cases e
    | some fr' => rw [ht] at e; simp only [Option.map_some, Option.some.injEq] at e ⊢; omega

theorem topGrow_pushBind (s : SState) (b : SBinding) : TopGrow s (s.pushBind b) 1 := by
  refine ⟨by simp [SState.pushBind], ?_⟩
  rw [pushBind_getLast]; cases s.env.getLast? <;> simp

theorem topGrow_pushBindShaped (s : SState) (b : SBinding) : TopGrow s (pushBindShaped s b) 1 := by
  have hp := envPush_pushBindShaped s b
  refine ⟨hp.1, ?_⟩
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?]
  cases hs : s.env[s.env.length - 1]? with
  | none =>
    have : (pushBindShaped s b).env[(pushBindShaped s b).env.length - 1]? = none := by
      have := hp.1; rw [List.getElem?_eq_none_iff] at hs ⊢; omega
    rw [this]; rfl
  | some fr =>
    obtain ⟨fr', h', hb, -⟩ := hp.2 _ fr hs
    rw [show (pushBindShaped s b).env.length - 1 = s.env.length - 1 by rw [hp.1], h']
    simp only [SState.topIdx, if_true] at hb
    simp [hb]

theorem topGrow_pushCell {s : SState} (ht : 0 < s.topIdx) (b : SBinding) : TopGrow s (s.pushCell b) 0 := by
  refine ⟨by simp [SState.pushCell], ?_⟩
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?]
  simp only [SState.pushCell, List.length_modify, List.getElem?_modify]
  have : (0 : Nat) ≠ s.env.length - 1 := by unfold SState.topIdx at ht; omega
  simp only [this, if_false]
  cases s.env[s.env.length - 1]? <;> rfl

theorem varPos_grow {s t : SState} {k : Nat} (h : TopGrow s t k) (i : Nat) : t.varPos (i + k) = s.varPos i := by
  have ht : t.topIdx = s.topIdx := by simp only [SState.topIdx, h.1]
  unfold SState.varPos
  have e := h.2
  cases hs : s.env.getLast? with
  | none =>
    rw [hs] at e
    cases hg : t.env.getLast? with
    | none => rfl
    | some _ => rw [hg] at e; cases e
  | some fr =>
    rw [hs] at e
    cases hg : t.env.getLast? with
    | none => rw [hg] at e; cases e
    | some fr' =>
      rw [hg] at e
      simp only [Option.map_some, Option.some.injEq] at e
      dsimp only
      rw [ht, e]
      by_cases hi : i < fr.binds.length
      · rw [if_pos (by omega), if_pos hi]; congr 2; omega
      · rw [if_neg (by omega), if_neg hi]

theorem varPos_grow_new {s t : SState} {k : Nat} (h : TopGrow s t k) {i : Nat} (hi : i < k) {pos : Pos}
    (hp : t.varPos i = some pos) : pos ∉ s.positions := by
  have ht : t.topIdx = s.topIdx := by simp only [SState.topIdx, h.1]
  unfold SState.varPos at hp
  have e := h.2
  cases hg : t.env.getLast? with
  | none => rw [hg] at hp; cases hp
  | some fr' =>
    rw [hg] at hp e
    dsimp only at hp
    split at hp
    · cases hp
      rw [ht]
      intro hm
      rw [mem_positions] at hm
      simp only [SState.lookup] at hm
      cases hs : s.env.getLast? with
      | none => rw [hs] at e; cases e
      | some fr =>
        rw [hs] at e
        simp only [Option.map_some, Option.some.injEq] at e
        have hl : s.env[s.topIdx]? = some fr := by
          rw [List.getLast?_eq_getElem?] at hs; exact hs
        rw [hl] at hm
        simp only [Option.bind_some] at hm
        rw [List.getElem?_eq_none_iff.mpr (by omega)] at hm
        cases hm
    · cases hp

/-! ## A binding pushed -/

theorem varPos_push {s t : SState} (h : EnvPush s t) (i : Nat) : t.varPos (i + 1) = s.varPos i := by
  have ht : t.topIdx = s.topIdx := by simp only [SState.topIdx, h.1]
  unfold SState.varPos
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?]
  cases hs : s.env[s.env.length - 1]? with
  | none =>
    have : t.env[t.env.length - 1]? = none := by
      have := h.1; rw [List.getElem?_eq_none_iff] at hs ⊢; omega
    rw [this]
  | some fr =>
    obtain ⟨fr', h', hb, -⟩ := h.2 _ fr hs
    have e : t.env.length - 1 = s.env.length - 1 := by rw [h.1]
    rw [e, h']
    dsimp only
    simp only [SState.topIdx, if_true] at hb
    rw [hb, ht]
    by_cases hi : i < fr.binds.length
    · rw [if_pos (by omega), if_pos hi]
      congr 2; omega
    · rw [if_neg (by omega), if_neg hi]

theorem varPos_zero_push {Q : Pos → Prop} {s t : SState} (h : EnvPush s t) (hQ : ∀ p, Q p → p ∈ s.positions) :
    ∀ pos, t.varPos 0 = some pos → ¬ Q pos := by
  intro pos hp
  unfold SState.varPos at hp
  rw [List.getLast?_eq_getElem?] at hp
  cases hs : s.env[s.env.length - 1]? with
  | none =>
    have : t.env[t.env.length - 1]? = none := by
      have := h.1; rw [List.getElem?_eq_none_iff] at hs ⊢; omega
    rw [this] at hp; cases hp
  | some fr =>
    obtain ⟨fr', h', hb, -⟩ := h.2 _ fr hs
    have e : t.env.length - 1 = s.env.length - 1 := by rw [h.1]
    rw [e, h'] at hp
    simp only [SState.topIdx, if_true] at hb
    dsimp only at hp
    rw [if_pos (by omega)] at hp
    cases hp
    have ht : t.topIdx = s.topIdx := by simp only [SState.topIdx, h.1]
    rw [ht, hb, Nat.add_sub_cancel]
    exact not_q_new hQ hs

/-- The variables of a term under one more binder, at the state with that binding pushed. -/
theorem VarsAvoid.push {Q : Pos → Prop} {s t : SState} {T u : Term} (hV : VarsAvoid Q s T)
    (hsub : ∀ x ∈ u.placeOccs 1, x ∈ T.placeOccs 0) (h : EnvPush s t) (hQ : ∀ p, Q p → p ∈ s.positions) :
    VarsAvoid Q t u := by
  intro v hv pos hp
  by_cases hv0 : v = 0
  · subst hv0
    exact varPos_zero_push h hQ pos hp
  · rcases freeVars_sub hsub v hv with h0 | h0
    · omega
    · have e : v = (v - 1) + 1 := by omega
      rw [e, varPos_push h] at hp
      exact hV _ h0 pos hp

theorem Adm.push {K : RunCtx} {Q : Pos → Prop} {β β' : Pos → SBinding} {s : SState} (h : Adm K Q β β' s)
    (b : SBinding) : Adm K Q β β' (pushBindShaped s b) := by
  have hfix : qset Q β (pushBindShaped s b) = pushBindShaped s b := by
    rw [← qset_pushBindShaped s h.twin.pre.pos h.twin.pre.shape b, h.twin.fix]
  have hsh : ∀ p, Q p → (pushBindShaped s b).shape p = none := fun p hp => by rw [← hfix]; simp [hp]
  have hpos : ∀ p, Q p → p ∈ (pushBindShaped s b).positions := fun p hp =>
    mem_positions_pushBindShaped b (h.twin.pre.pos p hp)
  exact ⟨⟨⟨h.twin.pre.temp, hpos, hsh, h.twin.pre.const⟩, ⟨h.twin.pre.temp, hpos, hsh, h.twin.pre'.const⟩, hfix,
    EnvLe.refl _⟩, h.decl, h.good, h.good'⟩

/-! ## Bindings pushed by `extendBy` -/

theorem Adm.pushBind {K : RunCtx} {Q : Pos → Prop} {β β' : Pos → SBinding} {s : SState} (h : Adm K Q β β' s)
    (b : SBinding) : Adm K Q β β' (s.pushBind b) := by
  have hfix : qset Q β (s.pushBind b) = s.pushBind b := by
    rw [← qset_pushBind s h.twin.pre.pos b, h.twin.fix]
  have hsh : ∀ p, Q p → (s.pushBind b).shape p = none := fun p hp => by rw [← hfix]; simp [hp]
  have hpos : ∀ p, Q p → p ∈ (s.pushBind b).positions := fun p hp =>
    mem_positions_pushBind s b (h.twin.pre.pos p hp)
  exact ⟨⟨⟨h.twin.pre.temp, hpos, hsh, h.twin.pre.const⟩, ⟨h.twin.pre.temp, hpos, hsh, h.twin.pre'.const⟩, hfix,
    EnvLe.refl _⟩, h.decl, h.good, h.good'⟩

theorem Adm.pushes {K : RunCtx} {Q : Pos → Prop} {β β' : Pos → SBinding} :
    ∀ (l : List SBinding) {s : SState}, Adm K Q β β' s → Adm K Q β β' (l.foldl (fun s b => s.pushBind b) s)
  | [], _, h => h
  | b :: l, _, h => Adm.pushes l (h.pushBind b)

theorem qset_pushes {Q : Pos → Prop} {β : Pos → SBinding} :
    ∀ (l : List SBinding) (s : SState), (∀ p, Q p → p ∈ s.positions) →
      l.foldl (fun s b => s.pushBind b) (qset Q β s) = qset Q β (l.foldl (fun s b => s.pushBind b) s)
  | [], _, _ => rfl
  | b :: l, s, hQ => by
    simp only [List.foldl_cons]
    rw [qset_pushBind s hQ b]
    exact qset_pushes l _ fun p hp => mem_positions_pushBind s b (hQ p hp)

theorem varPos_pushes : ∀ (l : List SBinding) (s : SState) (i : Nat),
    (l.foldl (fun s b => s.pushBind b) s).varPos (i + l.length) = s.varPos i
  | [], s, i => rfl
  | b :: l, s, i => by
    simp only [List.foldl_cons, List.length_cons]
    rw [show i + (l.length + 1) = (i + 1) + l.length by omega, varPos_pushes l _ (i + 1), varPos_push (envPush_pushBind s b)]

theorem varPos_pushes_new {Q : Pos → Prop} : ∀ (l : List SBinding) (s : SState), (∀ p, Q p → p ∈ s.positions) →
    ∀ i, i < l.length → ∀ pos, (l.foldl (fun s b => s.pushBind b) s).varPos i = some pos → ¬ Q pos
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | b :: l, s, hQ, i, hi, pos, hp => by
    simp only [List.foldl_cons] at hp
    have hQ' : ∀ p, Q p → p ∈ (s.pushBind b).positions := fun p hq => mem_positions_pushBind s b (hQ p hq)
    by_cases hil : i < l.length
    · exact varPos_pushes_new l _ hQ' i hil pos hp
    · have e : i = 0 + l.length := by simp at hi; omega
      rw [e, varPos_pushes] at hp
      exact varPos_zero_push (envPush_pushBind s b) hQ pos hp

/-! ## Under a fresh bottom frame -/

theorem down_up (p : Pos) : p.up.down? = some p := by cases p <;> rfl

theorem eq_up_of_down {p q : Pos} (h : p.down? = some q) : p = q.up := by
  rcases p with ⟨_ | f, i⟩ | ⟨_ | f, i⟩ <;> simp [Pos.down?] at h <;> subst h <;> rfl

theorem qup_up {Q : Pos → Prop} (p : Pos) : Qup Q p.up ↔ Q p := by
  simp only [Qup, down_up]

theorem varPos_under (s : SState) (i : Nat) : s.under.varPos i = (s.varPos i).map Pos.up := by
  by_cases he : s.env = []
  · have : s.varPos i = none := by unfold SState.varPos; rw [he]; rfl
    rw [this]
    unfold SState.varPos
    simp only [under_env, he, List.isEmpty_nil, if_true]
    simp
  · unfold SState.varPos
    have ht : s.under.topIdx = s.topIdx + 1 := by
      simp only [SState.topIdx, under_env_ne _ he, List.length_cons]
      have : s.env.length ≠ 0 := fun h => he (List.eq_nil_of_length_eq_zero h)
      omega
    have hg : s.under.env.getLast? = s.env.getLast? := by
      rw [under_env_ne _ he]
      cases e : s.env with
      | nil => exact absurd e he
      | cons a l => rw [List.getLast?_cons_cons]
    rw [hg, ht]
    cases s.env.getLast? with
    | none => rfl
    | some fr => dsimp only; split <;> rfl

/-- What frame locality asks of a state, one frame up. -/
theorem Adm.under {K : RunCtx} {Q : Pos → Prop} {β β' : Pos → SBinding} {s : SState} (h : Adm K Q β β' s) :
    Adm K (Qup Q) (βup β) (βup β') s.under := by
  have hfix : qset (Qup Q) (βup β) s.under = s.under := by rw [← qset_under, h.twin.fix]
  have hdown : ∀ p, Qup Q p → ∃ q, p = q.up ∧ Q q := fun p hp => by
    unfold Qup at hp
    cases hd : p.down? with
    | none => rw [hd] at hp; exact absurd hp id
    | some q => rw [hd] at hp; exact ⟨q, eq_up_of_down hd, hp⟩
  have htemp : ∀ f i, ¬ Qup Q (.temp f i) := fun f i hq => by
    obtain ⟨q, e, hq⟩ := hdown _ hq
    cases q with
    | bind => cases e
    | temp f' i' => exact h.twin.pre.temp f' i' hq
  have hpos : ∀ p, Qup Q p → p ∈ s.under.positions := fun p hp => by
    obtain ⟨q, rfl, hq⟩ := hdown p hp
    exact (mem_positions_under_up s q).mpr (h.twin.pre.pos q hq)
  have hsh : ∀ p, Qup Q p → s.under.shape p = none := fun p hp => by rw [← hfix]; simp [hp]
  have hbu : ∀ (γ : Pos → SBinding) p, Qup Q p → ∃ q, βup γ p = γ q ∧ Q q := fun γ p hp => by
    obtain ⟨q, rfl, hq⟩ := hdown p hp
    exact ⟨q, by simp only [βup, down_up], hq⟩
  refine ⟨⟨⟨htemp, hpos, hsh, fun p hp => ?_⟩, ⟨htemp, hpos, hsh, fun p hp => ?_⟩, hfix, EnvLe.refl _⟩,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨q, e, hq⟩ := hbu β p hp; rw [e]; exact h.twin.pre.const q hq
  · obtain ⟨q, e, hq⟩ := hbu β' p hp; rw [e]; exact h.twin.pre'.const q hq
  · obtain ⟨q, e, hq⟩ := hbu β p hp; obtain ⟨q', e', hq'⟩ := hbu β' p hp
    obtain ⟨q₀, rfl, -⟩ := hdown p hp
    simp only [βup, down_up] at e e' ⊢
    exact h.decl _ (by simpa [qup_up] using hp)
  · obtain ⟨q, e, hq⟩ := hbu β p hp; rw [e]; exact h.good q hq
  · obtain ⟨q, e, hq⟩ := hbu β' p hp; rw [e]; exact h.good' q hq

/-! ## One parameter pushed (`fixStep`) -/

section
variable {Q : Pos → Prop} {β : Pos → SBinding}

theorem qset_env0 (X : SState) : ((qset Q β X).env[0]?).map (·.binds.length) = (X.env[0]?).map (·.binds.length) := by
  rw [qset_env_get]; cases X.env[0]? <;> simp

theorem fixStep_qset {fb fb' : List PBind × PBind} (hB : BAgree 0 fb.1 fb'.1) {X : SState} (hP : Pre Q β X)
    (acc : List Sem) (cells : List Pos) {x x' : Sem × PiDom} (h1 : x.1 = x'.1) (hr : x.2.isRef = x'.2.isRef)
    (hd : ∀ a : List Sem, a.length = acc.length → x.2.dom a = x'.2.dom a) :
    fixStep fb' (qset Q β X, acc, cells) x' =
      (qset Q β (fixStep fb (X, acc, cells) x).1, (fixStep fb (X, acc, cells) x).2) := by
  obtain ⟨v, pd⟩ := x
  obtain ⟨v', pd'⟩ := x'
  dsimp only at h1 hr hd
  subst h1
  unfold fixStep
  dsimp only
  rw [← hr]
  have tail : ∀ (T : TyS) (d : DeclInfo),
      (if pd.isRef = true then
        (pushBindShaped (((((qset Q β X).freshLoan.2.pushCell { ty := .plain T.m, val := fun ψ => ψ (qset Q β X).freshLoan.1, decl := .other }).setLent (qset Q β X).freshLoan.1 [⟨Pos.bind 0 ((((qset Q β X).freshLoan.2.env[0]?).map (·.binds.length)).getD 0), [], false⟩]).setHeldMem (qset Q β X).freshLoan.1 v).setHeldTy (qset Q β X).freshLoan.1 T.m)
          { ty := { T with label := some (qset Q β X).freshLoan.1 }, val := fun _ => v, decl := d },
          acc ++ [v], cells ++ [Pos.bind 0 ((((qset Q β X).freshLoan.2.env[0]?).map (·.binds.length)).getD 0)])
      else ((qset Q β X).pushBind { ty := { T with label := none }, val := fun _ => v, decl := d }, acc ++ [v], cells)) =
      (qset Q β (if pd.isRef = true then
        (pushBindShaped ((((X.freshLoan.2.pushCell { ty := .plain T.m, val := fun ψ => ψ X.freshLoan.1, decl := .other }).setLent X.freshLoan.1 [⟨Pos.bind 0 (((X.freshLoan.2.env[0]?).map (·.binds.length)).getD 0), [], false⟩]).setHeldMem X.freshLoan.1 v).setHeldTy X.freshLoan.1 T.m)
          { ty := { T with label := some X.freshLoan.1 }, val := fun _ => v, decl := d },
          acc ++ [v], cells ++ [Pos.bind 0 (((X.freshLoan.2.env[0]?).map (·.binds.length)).getD 0)])
      else (X.pushBind { ty := { T with label := none }, val := fun _ => v, decl := d }, acc ++ [v], cells)).1,
       (if pd.isRef = true then
        (pushBindShaped ((((X.freshLoan.2.pushCell { ty := .plain T.m, val := fun ψ => ψ X.freshLoan.1, decl := .other }).setLent X.freshLoan.1 [⟨Pos.bind 0 (((X.freshLoan.2.env[0]?).map (·.binds.length)).getD 0), [], false⟩]).setHeldMem X.freshLoan.1 v).setHeldTy X.freshLoan.1 T.m)
          { ty := { T with label := some X.freshLoan.1 }, val := fun _ => v, decl := d },
          acc ++ [v], cells ++ [Pos.bind 0 (((X.freshLoan.2.env[0]?).map (·.binds.length)).getD 0)])
      else (X.pushBind { ty := { T with label := none }, val := fun _ => v, decl := d }, acc ++ [v], cells)).2) := by
    intro T d
    cases pd.isRef
    · simp only [Bool.false_eq_true, if_false]
      rw [qset_pushBind X hP.pos]
    · simp only [if_true]
      rw [qset_freshLoan]
      dsimp only
      rw [qset_pushCell X.freshLoan.2 (fun p hp => hP.pos p hp), qset_setLent, qset_setHeldMem, qset_setHeldTy,
        qset_pushBindShaped _ (by intro p hp; exact mem_positions_pushCell _ _ (hP.pos p hp))
          (by intro p hp; exact hP.shape p hp), qset_env0]
  cases hb : fb.1[acc.length]? with
  | none =>
    have hb' : fb'.1[acc.length]? = none := by
      rw [List.getElem?_eq_none_iff] at hb ⊢; rw [← hB.1]; exact hb
    rw [hb']
    dsimp only
    rw [← hd acc rfl]
    exact tail _ _
  | some b =>
    obtain ⟨b', hb'⟩ : ∃ b', fb'.1[acc.length]? = some b' := by
      have : acc.length < fb'.1.length := by rw [← hB.1]; exact (List.getElem?_eq_some_iff.1 hb).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    rw [hb']
    obtain ⟨e2, e1⟩ := hB.2 _ b b' hb hb'
    dsimp only
    rw [← e1 acc (by simp), ← e2]
    exact tail _ _

end

/-! ## The parameters pushed (the fold of `fixStep`) -/

theorem fixStep_positions (fb : List PBind × PBind) (X : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom)
    {p : Pos} (hp : p ∈ X.positions) : p ∈ (fixStep fb (X, acc, cells) x).1.positions := by
  unfold fixStep
  dsimp only
  split
  · exact mem_positions_pushBindShaped _ (mem_positions_pushCell _ _ hp)
  · exact mem_positions_pushBind _ _ hp

theorem topGrow_refStep {X : SState} (ht : 0 < X.topIdx) (c b : SBinding) (l : Nat) (xs : List Site) (v : Sem) (T : TyM) :
    TopGrow X (pushBindShaped ((((X.freshLoan.2.pushCell c).setLent l xs).setHeldMem l v).setHeldTy l T) b) 1 := by
  have h1 : TopGrow X X.freshLoan.2 0 := TopGrow.of_env rfl
  have h2 := topGrow_pushCell (s := X.freshLoan.2) ht c
  have h3 := topGrow_pushBindShaped ((((X.freshLoan.2.pushCell c).setLent l xs).setHeldMem l v).setHeldTy l T) b
  have := (h1.trans h2).trans ((TopGrow.of_env (s := X.freshLoan.2.pushCell c) rfl).trans h3)
  simpa using this

theorem fixStep_topGrow (fb : List PBind × PBind) {X : SState} (ht : 0 < X.topIdx) (acc : List Sem)
    (cells : List Pos) (x : Sem × PiDom) : TopGrow X (fixStep fb (X, acc, cells) x).1 1 := by
  unfold fixStep
  dsimp only
  split
  · exact topGrow_refStep ht _ _ _ _ _ _
  · exact topGrow_pushBind _ _

theorem fixStep_cells (fb : List PBind × PBind) (X : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom) :
    ∀ c ∈ (fixStep fb (X, acc, cells) x).2.2, c ∈ cells ∨ ∃ j, c = .bind 0 j := by
  unfold fixStep
  dsimp only
  split
  · intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact .inl hc
    · exact .inr ⟨_, rfl⟩
  · exact fun c hc => .inl hc

/-- The fold's invariant: what `Twin` asks, at the frame's own layout. -/
def FInv (Q : Pos → Prop) (β β' : Pos → SBinding) (X : SState) : Prop :=
  Pre Q β X ∧ Pre Q β' X ∧ qset Q β X = X

/-- Argument lists paired with agreeing descriptions, `n` arguments in. -/
def ZipAgree (n : Nat) (xs xs' : List (Sem × PiDom)) : Prop :=
  xs.length = xs'.length ∧ ∀ (i : Nat) (x x' : Sem × PiDom), xs[i]? = some x → xs'[i]? = some x' →
    x.1 = x'.1 ∧ x.2.isRef = x'.2.isRef ∧ ∀ a : List Sem, a.length = n + i → x.2.dom a = x'.2.dom a

theorem zipAgree_zip : ∀ (args : List Sem) {n : Nat} {ps ps' : List PiDom}, DomAgree n ps ps' →
    ZipAgree n (args.zip ps) (args.zip ps')
  | [], _, _, _, _ => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | a :: as, n, [], [], _ => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | a :: as, n, [], _ :: _, h => absurd h.1 (by simp)
  | a :: as, n, _ :: _, [], h => absurd h.1 (by simp)
  | a :: as, n, p :: ps, p' :: ps', h => by
    have ih := zipAgree_zip as h.tail
    obtain ⟨hr, hd⟩ := h.head
    refine ⟨by simp [ih.1], fun i x x' hx hx' => ?_⟩
    cases i with
    | zero =>
      simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at hx hx'
      subst hx hx'
      exact ⟨rfl, hr, fun acc ha => hd acc (by omega)⟩
    | succ i =>
      simp only [List.zip_cons_cons, List.getElem?_cons_succ] at hx hx'
      obtain ⟨e1, e2, e3⟩ := ih.2 i x x' hx hx'
      exact ⟨e1, e2, fun acc ha => e3 acc (by omega)⟩

theorem fixStep_acc (fb : List PBind × PBind) (X : SState) (acc : List Sem) (cells : List Pos) (x : Sem × PiDom) :
    (fixStep fb (X, acc, cells) x).2.1 = acc ++ [x.1] := by
  unfold fixStep; dsimp only; split <;> rfl

theorem foldl_fixStep_qset {Q : Pos → Prop} {β β' : Pos → SBinding} {fb fb' : List PBind × PBind}
    (hB : BAgree 0 fb.1 fb'.1) : ∀ (xs xs' : List (Sem × PiDom)) (X : SState) (acc : List Sem) (cells : List Pos),
    ZipAgree acc.length xs xs' → FInv Q β β' X →
    xs'.foldl (fixStep fb') (qset Q β' X, acc, cells) =
      (qset Q β' (xs.foldl (fixStep fb) (X, acc, cells)).1, (xs.foldl (fixStep fb) (X, acc, cells)).2) ∧
    FInv Q β β' (xs.foldl (fixStep fb) (X, acc, cells)).1
  | [], [], X, acc, cells, _, hI => ⟨rfl, hI⟩
  | [], _ :: _, _, _, _, h, _ => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, h, _ => absurd h.1 (by simp)
  | x :: xs, x' :: xs', X, acc, cells, hz, hI => by
    obtain ⟨e1, e2, e3⟩ := hz.2 0 x x' rfl rfl
    have hs' := fixStep_qset hB hI.2.1 acc cells e1 e2 fun a ha => e3 a (by omega)
    have hs0 := fixStep_qset (fb' := fb) (x := x) (x' := x) (BAgree.refl 0 fb.1) hI.1 acc cells rfl rfl fun a _ => rfl
    rw [hI.2.2] at hs0
    have hfix : qset Q β (fixStep fb (X, acc, cells) x).1 = (fixStep fb (X, acc, cells) x).1 := by
      have := congrArg Prod.fst hs0; exact this.symm
    have hpos : ∀ p, Q p → p ∈ (fixStep fb (X, acc, cells) x).1.positions := fun p hp =>
      fixStep_positions fb X acc cells x (hI.1.pos p hp)
    have hsh : ∀ p, Q p → (fixStep fb (X, acc, cells) x).1.shape p = none := fun p hp => by
      rw [← hfix]; simp [hp]
    have hI' : FInv Q β β' (fixStep fb (X, acc, cells) x).1 :=
      ⟨⟨hI.1.temp, hpos, hsh, hI.1.const⟩, ⟨hI.1.temp, hpos, hsh, hI.2.1.const⟩, hfix⟩
    simp only [List.foldl_cons]
    rw [hs']
    have hz' : ZipAgree (fixStep fb (X, acc, cells) x).2.1.length xs xs' := by
      rw [fixStep_acc]
      refine ⟨by simpa using hz.1, fun i y y' hy hy' => ?_⟩
      obtain ⟨f1, f2, f3⟩ := hz.2 (i + 1) y y' (by simpa using hy) (by simpa using hy')
      exact ⟨f1, f2, fun a ha => f3 a (by simp at ha; omega)⟩
    exact foldl_fixStep_qset hB xs xs' _ _ _ hz' hI'

theorem foldl_fixStep_topGrow (fb : List PBind × PBind) : ∀ (xs : List (Sem × PiDom)) (X : SState) (acc : List Sem)
    (cells : List Pos), 0 < X.topIdx → TopGrow X (xs.foldl (fixStep fb) (X, acc, cells)).1 xs.length
  | [], X, _, _, _ => TopGrow.refl X
  | x :: xs, X, acc, cells, ht => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := fixStep_topGrow fb ht acc cells x
    have ht' : 0 < (fixStep fb (X, acc, cells) x).1.topIdx := by
      simp only [SState.topIdx, h1.1]; exact ht
    rw [Nat.add_comm]
    exact h1.trans (foldl_fixStep_topGrow fb xs _ _ _ ht')

theorem foldl_fixStep_cells (fb : List PBind × PBind) : ∀ (xs : List (Sem × PiDom)) (X : SState) (acc : List Sem)
    (cells : List Pos), ∀ c ∈ (xs.foldl (fixStep fb) (X, acc, cells)).2.2, c ∈ cells ∨ ∃ j, c = .bind 0 j
  | [], _, _, _ => fun c hc => .inl hc
  | x :: xs, X, acc, cells => by
    simp only [List.foldl_cons]
    intro c hc
    rcases foldl_fixStep_cells fb xs _ _ _ c hc with h | h
    · exact fixStep_cells fb X acc cells x c h
    · exact .inr h

/-! ## The body's run in its frame -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The body's variables avoid the moved `Q` in its frame: the pushed `self` and parameters are new
positions, and the rest are the closure's free variables, one frame up. -/
theorem VarsAvoid.body {Q : Pos → Prop} {s X : SState} {T body : Term} {k : Nat} (hV : VarsAvoid Q s T)
    (hsub : ∀ x ∈ body.placeOccs k, x ∈ T.placeOccs 0) (hQ : ∀ p, Q p → p ∈ s.positions)
    (hg : TopGrow s.under X k) : VarsAvoid (Qup Q) X body := by
  intro v hv pos hp hq
  have hdown : ∃ q, pos = q.up ∧ Q q := by
    unfold Qup at hq
    cases hd : pos.down? with
    | none => rw [hd] at hq; exact absurd hq id
    | some q => rw [hd] at hq; exact ⟨q, eq_up_of_down hd, hq⟩
  obtain ⟨q, rfl, hq'⟩ := hdown
  by_cases hvk : v < k
  · exact varPos_grow_new hg hvk hp ((mem_positions_under_up s q).mpr (hQ q hq'))
  · rcases freeVars_sub hsub v hv with h0 | h0
    · omega
    · rw [show v = (v - k) + k by omega, varPos_grow hg, varPos_under] at hp
      cases hs : s.varPos (v - k) with
      | none => rw [hs] at hp; cases hp
      | some q' =>
        rw [hs] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        have : q' = q := by
          have := congrArg Pos.down? hp; rw [down_up, down_up] at this; exact Option.some.inj this
        subst this
        exact hV _ h0 q' hs hq'

/-- **The closure's body output across the transform**, at a full argument list: its frame is the
transform's (one frame up), its run commutes by the body's induction hypothesis `hb`, and its
finals are read at cells of frame 0, which the transform does not touch. -/
theorem fixBodyAt_qset (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s : SState} (hA : Adm K Q β β' s) (hR : RInv (fun _ => True) s) {T body : Term} (hV : VarsAvoid Q s T)
    (n : Nat) (hsub : ∀ x ∈ body.placeOccs (n + 1), x ∈ T.placeOccs 0)
    (hb : ∀ (hint : TyS) (X : SState) (Q₁ : Pos → Prop) (β₁ β₁' : Pos → SBinding), Adm K Q₁ β₁ β₁' X →
      VarsAvoid Q₁ X body → RInv (fun _ => True) X → Comm Q₁ β₁' (runT K ρ φ true hint body) X)
    {fb fb' : List PBind × PBind} (hB : BAgree 0 fb.1 fb'.1) (hd2 : fb.2.2 = fb'.2.2)
    {ps ps' : List PiDom} (hps : DomAgree 0 ps ps') (hpl : ps.length = n) {out out' : PiCod}
    (hco : out.isRef = out'.isRef) (piT : TyM) (selfM : Sem) (args : List Sem) (ha : args.length = n)
    (hcod : fb.2.1 args = fb'.2.1 args) :
    fixBodyAt K ρ φ fb' (qset Q β' s) ps' out' piT (qset Q β' s).nextLoan body selfM args =
      fixBodyAt K ρ φ fb s ps out piT s.nextLoan body selfM args := by
  unfold fixBodyAt
  dsimp only
  have hA₀ := hA.under
  rw [qset_under, ← hd2, qset_pushBind s.under hA₀.twin.pre.pos]
  generalize hself : ({ ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } : SBinding) = b
  have hA₁ := hA₀.pushBind b
  have hI : FInv (Qup Q) (βup β) (βup β') (s.under.pushBind b) := ⟨hA₁.twin.pre, hA₁.twin.pre', hA₁.twin.fix⟩
  have hz : ZipAgree ([] : List Sem).length (args.zip ps) (args.zip ps') := by
    simpa using zipAgree_zip args hps
  obtain ⟨hfold, hI₂⟩ := foldl_fixStep_qset hB (args.zip ps) (args.zip ps') _ [] [] hz hI
  rw [hfold]
  have hRF := (foldl_fixStep_inv (fb := fb) (args.zip ps) _
    (formInv_init (L := fun _ => True) (rinv_under hR) (under_topIdx_pos s) b selfM (by rw [← hself]))).1
  have hG : TopGrow s.under ((args.zip ps).foldl (fixStep fb) (s.under.pushBind b, [], [])).1 (n + 1) := by
    have h1 := topGrow_pushBind s.under b
    have h2 := foldl_fixStep_topGrow fb (args.zip ps) (s.under.pushBind b) [] []
      (by rw [show (s.under.pushBind b).topIdx = s.under.topIdx from topIdx_pushBind' _ _]; exact under_topIdx_pos s)
    have := h1.trans h2
    rw [List.length_zip, ha, hpl, Nat.min_self, Nat.add_comm] at this
    exact this
  have hcells := foldl_fixStep_cells fb (args.zip ps) (s.under.pushBind b) [] []
  generalize hF : (args.zip ps).foldl (fixStep fb) (s.under.pushBind b, [], []) = F at hI₂ hRF hG hcells
  obtain ⟨X₂, acc₂, cells₂⟩ := F
  dsimp only at hI₂ hRF hG hcells ⊢
  rw [← hcod]
  have hA₂ : Adm K (Qup Q) (βup β) (βup β') X₂ :=
    ⟨⟨hI₂.1, hI₂.2.1, hI₂.2.2, EnvLe.refl _⟩, hA₀.decl, hA₀.good, hA₀.good'⟩
  have hVb : VarsAvoid (Qup Q) X₂ body := VarsAvoid.body hV hsub hA.twin.pre.pos hG
  have cb := hb (fb.2.1 args) X₂ (Qup Q) (βup β) (βup β') hA₂ hVb hRF
  have cb0 := hb (fb.2.1 args) X₂ (Qup Q) (βup β) (βup β) hA₂.self hVb hRF
  unfold Comm qmap at cb
  have hfin : ∀ (S : SState), cells₂.map (fun c => (qset (Qup Q) (βup β') S).valAt c) = cells₂.map (fun c => S.valAt c) := by
    intro S
    refine List.map_congr_left fun c hc => ?_
    rcases hcells c hc with h | ⟨j, rfl⟩
    · cases h
    · exact qset_valAt_not S (by simp [Qup, Pos.down?])
  -- main's D142: an erased function's body runs on a copy, its pop at the start state
  cases hEr : fnErasedD fb.2.2
  · simp only [SM.bodyRun]
    rw [cb]
    cases h3 : runT K ρ φ true (fb.2.1 args) body X₂ with
    | none => rfl
    | some r =>
      obtain ⟨⟨r, R⟩, X₃⟩ := r
      obtain ⟨-, -, e₃, -⟩ := runT_rinv K ρ φ _ hK true body _ X₂ X₃ (r, R) hRF h3
      have hA₃ := hA₂.next e₃ (fix_of_comm cb0 hA₂.twin.fix h3)
      have hP := hA₃.twin.pre'
      simp only [Option.map_some, qset_nextLoan, hco, qset_liveLabels hP.shape, fun ls => endsOk_qset K φ ls hP,
        qset_foldl_endLabel hP.temp hP.const _ _ hP.shape, hfin]
      split <;> rename_i hE <;> simp only [hE, if_true, if_false, not_false_eq_true]
  · simp only [SM.bodyRun, SM.stmtIf, ↓reduceIte]
    rw [cb]
    cases h3 : runT K ρ φ true (fb.2.1 args) body X₂ with
    | none => rfl
    | some r =>
      obtain ⟨⟨r, R⟩, X₃⟩ := r
      have hP := hA₂.twin.pre'
      simp only [Option.map_some, qset_nextLoan, hco, qset_liveLabels hP.shape, fun ls => endsOk_qset K φ ls hP,
        qset_foldl_endLabel hP.temp hP.const _ _ hP.shape, hfin]
      try (split <;> rename_i hE <;> simp only [hE, if_true, if_false, not_false_eq_true])

/-- **The frame a later domain or the codomain is read in, across the transform** (docs/31 D210): `extendBy` is the
forming state under a fresh bottom frame with the parameters bound as [Def] binds them (`paramPush`, a borrow
parameter at a fresh label with a cell of frame 0), so the transform acts on it ONE FRAME UP, as on a closure's body
frame (`fixBodyAt_qset`); the extended state meets what the induction hypothesis asks there. -/
theorem extendBy_qset {Q : Pos → Prop} {β β' : Pos → SBinding} {s : SState} (hA : Adm K Q β β' s)
    (hR : RInv (fun _ => True) s) {T u : Term} (hV : VarsAvoid Q s T) {k : Nat}
    (hsub : ∀ x ∈ u.placeOccs k, x ∈ T.placeOccs 0) {bs bs' : List PBind} (hB : BAgree 0 bs bs')
    (rs : List Bool) (acc : List Sem) (ha : acc.length = k) (hrs : rs.length = k) :
    extendBy (qset Q β' s) bs' rs acc = qset (Qup Q) (βup β') (extendBy s bs rs acc) ∧
    Adm K (Qup Q) (βup β) (βup β') (extendBy s bs rs acc) ∧ VarsAvoid (Qup Q) (extendBy s bs rs acc) u ∧
    RInv (fun _ => True) (extendBy s bs rs acc) := by
  have hA₀ := hA.under
  have hI : FInv (Qup Q) (βup β) (βup β') s.under := ⟨hA₀.twin.pre, hA₀.twin.pre', hA₀.twin.fix⟩
  have hdom : DomAgree 0 (refDoms rs) (refDoms rs) := DomAgree.refl 0 _
  have hz : ZipAgree ([] : List Sem).length (acc.zip (refDoms rs)) (acc.zip (refDoms rs)) := by
    simpa using zipAgree_zip acc hdom
  let fb : List PBind × PBind := (bs, ((fun _ => .plain TyM.err), DeclInfo.other))
  let fb' : List PBind × PBind := (bs', ((fun _ => .plain TyM.err), DeclInfo.other))
  obtain ⟨hfold, hI₂⟩ := foldl_fixStep_qset (fb := fb) (fb' := fb') hB (acc.zip (refDoms rs)) (acc.zip (refDoms rs)) _ [] [] hz hI
  have hRF : RInv (fun _ => True) (extendBy s bs rs acc) := rinv_extendBy hR bs rs acc
  have hG : TopGrow s.under ((acc.zip (refDoms rs)).foldl (fixStep fb) (s.under, [], [])).1 k := by
    have := foldl_fixStep_topGrow fb (acc.zip (refDoms rs)) s.under [] [] (under_topIdx_pos s)
    rwa [List.length_zip, ha, refDoms, List.length_map, hrs, Nat.min_self] at this
  have e1 : extendBy s bs rs acc = ((acc.zip (refDoms rs)).foldl (fixStep fb) (s.under, [], [])).1 := rfl
  have e2 : extendBy (qset Q β' s) bs' rs acc =
      ((acc.zip (refDoms rs)).foldl (fixStep fb') (qset (Qup Q) (βup β') s.under, [], [])).1 := by
    show ((acc.zip (refDoms rs)).foldl (fixStep fb') ((qset Q β' s).under, [], [])).1 = _
    rw [qset_under]
  rw [e2, hfold, e1]
  rw [e1] at hRF
  exact ⟨rfl, ⟨⟨hI₂.1, hI₂.2.1, hI₂.2.2, EnvLe.refl _⟩, hA₀.decl, hA₀.good, hA₀.good'⟩,
    VarsAvoid.body hV hsub hA.twin.pre.pos hG, hRF⟩

end

/-! ## The stages of a closure -/

theorem weakCod_agree {n l k : Nat} {rk : List Sem → Nat} {out out' : PiCod} (h : CodAgree n out out') :
    CodAgree n (weakCod l rk k out) (weakCod l rk k out') :=
  ⟨h.1, fun acc ha => by simp only [weakCod]; rw [h.2 acc ha]⟩

theorem refFinals_agree : ∀ {n : Nat} {ps ps' : List PiDom}, DomAgree n ps ps' → ∀ args : List Sem,
    refFinals ps args = refFinals ps' args
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => absurd h.1 (by simp)
  | _, _ :: _, [], h, _ => absurd h.1 (by simp)
  | _, p :: ps, p' :: ps', h, [] => by cases p; cases p'; rfl
  | _, p :: ps, p' :: ps', h, a :: as => by
    simp only [refFinals]
    rw [h.head.1, refFinals_agree h.tail as]

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem fixStage_succ (fb : List PBind × PBind) (l : Nat) (s : SState) (ps : List PiDom) (out : PiCod)
    (dec : Option Nat) (start : Nat) (body : Term) (k : Nat) :
    fixStage K ρ φ fb l s ps out dec start body (k + 1) =
      fixBodyAt K ρ φ fb s ps out (piTyAt K.dm.read l ps (weakCod l (fixRank dec) k out)) start body
        (closureAt K.dm.read l φ ps (weakCod l (fixRank dec) k out)
          (stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec start body k))) := rfl

/-- **The stages agree at full argument lists**, by induction on the stage: stage `k + 1`'s `self` is
stage `k`'s closure, the same on both sides (`closureAt_congr'`), and its body output is
`fixBodyAt_qset`'s. -/
theorem fixStage_qset (hK : ∀ n, (K.C.global n).2.label = none) {Q : Pos → Prop} {β β' : Pos → SBinding}
    {s : SState} (hA : Adm K Q β β' s) (hR : RInv (fun _ => True) s) {T body : Term} (hV : VarsAvoid Q s T)
    (n : Nat) (hsub : ∀ x ∈ body.placeOccs (n + 1), x ∈ T.placeOccs 0)
    (hb : ∀ (hint : TyS) (X : SState) (Q₁ : Pos → Prop) (β₁ β₁' : Pos → SBinding), Adm K Q₁ β₁ β₁' X →
      VarsAvoid Q₁ X body → RInv (fun _ => True) X → Comm Q₁ β₁' (runT K ρ φ true hint body) X)
    {fb fb' : List PBind × PBind} (hB : BAgree 0 fb.1 fb'.1) (hd2 : fb.2.2 = fb'.2.2)
    {ps ps' : List PiDom} (hps : DomAgree 0 ps ps') (hpl : ps.length = n) {out out' : PiCod}
    (hco : CodAgree n out out') (hcod : ∀ args : List Sem, args.length = n → fb.2.1 args = fb'.2.1 args)
    (l : Nat) (dec : Option Nat) : ∀ (k : Nat) (args : List Sem), args.length = n →
      fixStage K ρ φ fb' l (qset Q β' s) ps' out' dec (qset Q β' s).nextLoan body k args =
        fixStage K ρ φ fb l s ps out dec s.nextLoan body k args
  | 0, _, _ => rfl
  | k + 1, args, ha => by
    rw [fixStage_succ, fixStage_succ]
    have hw : CodAgree ps.length (weakCod l (fixRank dec) k out) (weakCod l (fixRank dec) k out') := by
      rw [hpl]; exact weakCod_agree hco
    have hg : ∀ a : List Sem, a.length = ps.length →
        stageFn l ps (fixRank dec) k (fixStage K ρ φ fb l s ps out dec s.nextLoan body k) a =
          stageFn l ps' (fixRank dec) k (fixStage K ρ φ fb' l (qset Q β' s) ps' out' dec (qset Q β' s).nextLoan body k) a := by
      intro a ha'
      simp only [stageFn]
      rw [fixStage_qset hK hA hR hV n hsub hb hB hd2 hps hpl hco hcod l dec k a (by rw [ha', hpl]),
        refFinals_agree hps a]
    rw [← piTyAt_congr K.dm.read l ps ps' _ _ hps hw,
      ← closureAt_congr' K.dm.read l φ ps ps' _ _ _ _ hps hw hg]
    exact fixBodyAt_qset K ρ φ hK hA hR hV n hsub hb hB hd2 hps hpl hco.1 _ _ args ha (hcod args ha)

end

