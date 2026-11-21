import Ochr.Meaning.Steps.FragMachine
import Ochr.Meaning.Steps.Machine.FormFacts

/-!
# The fragment's state-level facts (machine lane; `Steps/FragMachine.lean`'s statements)

Each is "`Inv` before, the exact change, `Inv` after", reading no run, proved as the columns' were
(`InvSteps.lean`): `InvPopBot`, `InvSetBotNum`, `InvPopUnit`, `InvBindUnit` (with `PlaceLocal.unit`),
`InvEnd`, `InvLendG`.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem invPopBot : InvPopBot := by
  intro D Γ st T? hi
  rw [norm_withTempT] at hi
  exact (inv_pushTemp (.inr (.inr rfl))).mpr hi

theorem invSetBotNum : InvSetBotNum := by
  intro D Γ st f j v₀ hL hd hb hv₀ hi
  rw [norm_withEnv, erase_setAtE]
  have hva : valAt st.norm.env (.bind f j) = valAt st.env (.bind f j) := valAt_erase _ _
  refine inv_setAt (s := st.norm) hi (.inr (.inl ⟨.inr (.inr (hva.trans hb)), .inl hv₀⟩)) fun p x hp hx =>
    ⟨fun e => (by have := hv₀.follow hx; rw [e] at this; cases this),
      fun n args e => absurd e (hL.noInd (.inl rfl) (fun b h => (hd b (by rw [← binds_norm]; exact h)).1) hp n args)⟩

/-- `invPopBind'` for any bland top binding. -/
theorem invPopBland (D : Decisions) (Γ : List IndDecl) (st : MState) (fr : Frame) (b : Binding) (hL : PlaceLocal D)
    (hfr : st.env[st.env.size - 1]? = some fr) (hb : fr.binds.back? = some b) (hv : b.val.Bland)
    (hi : Inv D Γ st.norm) : Inv D Γ { st with env := Env.popBindE st.env }.norm := by
  rw [norm_withEnv, erase_popBindE]
  have hfr' : st.norm.env[st.norm.env.size - 1]? = some fr.erase := by
    show (Env.erase st.env)[(Env.erase st.env).size - 1]? = _
    rw [Env.erase_size, Env.erase_get?, hfr]; rfl
  have hn : 0 < fr.erase.binds.size := by
    show 0 < fr.binds.size
    rcases Nat.eq_zero_or_pos fr.binds.size with e | e
    · simp [Array.back?, e] at hb
    · exact e
  refine inv_popBind st.norm.env fr.erase hfr' hn rfl hL ?_ hi
  have hb' : fr.binds[fr.binds.size - 1]? = some b := hb
  rw [valAt_bind_lookup, hfr', Option.bind_some]
  show (((fr.binds[fr.binds.size - 1]?).getD default).val).Bland
  rw [hb']
  exact hv

theorem invPopUnit : InvPopUnit := by
  intro D Γ st fr b hL hfr hb hv hi
  exact invPopBland D Γ st fr b hL hfr hb (.inr (.inl hv)) hi

theorem invBindUnit : InvBindUnit := by
  intro D Γ st h T? p hL hne hi
  rw [norm_withTempT] at hi
  rw [norm_withEnv, erase_pushBindE]
  exact inv_pushBind (s := st.norm) hL (by show 0 < (Env.erase st.env).size; rw [Env.erase_size]; exact hne)
    (.inr (.inr rfl)) (.inr (.inr rfl)) (.inr (.inr rfl)) hi

/-! ## `Inv` at an environment of fragment values -/

theorem _root_.Ochr.Meaning.Steps.Form.FVal.simple {v : Value} (h : FVal v) : v.Simple := by
  cases h with
  | num h => exact .inl (.inl h)
  | unit => exact .inl (.inr (.inl rfl))
  | bot => exact .inl (.inr (.inr rfl))
  | loan m => exact .inr (.inr ⟨m, rfl⟩)
  | bor m h => exact .inr (.inl ⟨m, _, rfl, h⟩)

theorem _root_.Ochr.Meaning.Steps.Form.FVal.outerLoans' {v : Value} (h : FVal v) :
    v.outerLoans = [] ∨ ∃ m, v = .loan m ∧ v.outerLoans = [m] := by
  cases h with
  | num h => exact .inl h.outerLoans
  | unit => exact .inl rfl
  | bot => exact .inl rfl
  | loan m => exact .inr ⟨m, rfl, rfl⟩
  | bor m h => exact .inl (show _ = [] from h.outerLoans)

theorem count_flatMap_le_one {α β : Type} [BEq β] [LawfulBEq β] (f : α → List β) (x : β) :
    ∀ (L : List α), L.Nodup → (∀ a ∈ L, (f a).count x ≤ 1) → (∀ a ∈ L, ∀ b ∈ L, x ∈ f a → x ∈ f b → a = b) →
    (L.flatMap f).count x ≤ 1
  | [], _, _, _ => by simp
  | a :: L, hnd, h1, hu => by
    rw [List.flatMap_cons, List.count_append]
    by_cases hx : x ∈ f a
    · have h0 : (L.flatMap f).count x = 0 := by
        rw [List.count_eq_zero]; intro hm
        obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hm
        have := hu a (.head _) b (.tail _ hb) hx hxb
        subst this; exact (List.nodup_cons.mp hnd).1 hb
      have := h1 a (.head _); omega
    · rw [List.count_eq_zero.mpr hx]
      have := count_flatMap_le_one f x L (List.nodup_cons.mp hnd).2 (fun a h => h1 a (.tail _ h))
        (fun a ha b hb => hu a (.tail _ ha) b (.tail _ hb))
      omega

theorem two_le_count_flatMap {α β : Type} [BEq β] [LawfulBEq β] (f : α → List β) (x : β) {L : List α} {p q : α}
    (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p) (hxp : x ∈ f p) (hxq : x ∈ f q) : 2 ≤ (L.flatMap f).count x := by
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hp
  rw [List.flatMap_append, List.flatMap_cons, List.count_append, List.count_append]
  have hp1 : 1 ≤ (f p).count x := List.count_pos_iff.mpr hxp
  rcases List.mem_append.mp hq with h | h
  · have : 1 ≤ (L1.flatMap f).count x := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨q, h, hxq⟩)
    omega
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h hne
    · have : 1 ≤ (L2.flatMap f).count x := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨q, h, hxq⟩)
      omega

/-- (WF2) makes every loan occur once. -/
theorem inv_loan1 {D : Decisions} {Γ : List IndDecl} {a : MState} (hi : Inv D Γ a) {p q : Pos} {l : Nat}
    (hp : p ∈ allPos a.env) (hq : q ∈ allPos a.env) (ep : valAt a.env p = .loan l) (eq : valAt a.env q = .loan l) :
    p = q := by
  refine Classical.byContradiction fun hne => ?_
  have h2 := hi.2.1.2 l
  simp only [Env.values, List.flatMap_map] at h2
  have := two_le_count_flatMap (fun p => (valAt a.env p).outerLoans) l hp hq (Ne.symm hne)
    (by show l ∈ (valAt a.env p).outerLoans; rw [ep]; simp [Value.outerLoans])
    (by show l ∈ (valAt a.env q).outerLoans; rw [eq]; simp [Value.outerLoans])
  exact absurd (Nat.le_trans this h2) (by decide)

theorem shapeOf_some {v : Value} {l : Nat} (h : shapeOf v = some l) : ∃ w, v = .borrow l w := by
  unfold shapeOf at h; split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- (WF1) makes every borrow held once. -/
theorem inv_bor1 {D : Decisions} {Γ : List IndDecl} {a : MState} (hi : Inv D Γ a) {p q : Pos} {l : Nat} {w w' : Value}
    (hp : p ∈ allPos a.env) (hq : q ∈ allPos a.env) (ep : valAt a.env p = .borrow l w)
    (eq : valAt a.env q = .borrow l w') : p = q :=
  hi.1.2 p hp q hq l (by rw [shape_eq_shapeOf, ep]; rfl) (by rw [shape_eq_shapeOf, eq]; rfl)

/-- **`Inv` across a change to an environment of fragment values** (`FVal` everywhere): the
position-reading clauses from the loans' and borrows' uniqueness and the loans' liveness. -/
theorem inv_of_fval {D : Decisions} {Γ : List IndDecl} {a b : MState} (hi : Inv D Γ a) (ht : TabSame a b)
    (hb : BindsFrom a b) (hs : ∀ p ∈ allPos b.env, FVal (valAt b.env p))
    (hocc : ∀ l, b.Occurs l → a.Occurs l ∨ l < b.nextLoan)
    (hloan1 : ∀ p ∈ allPos b.env, ∀ q ∈ allPos b.env, ∀ l, valAt b.env p = .loan l → valAt b.env q = .loan l → p = q)
    (hbor1 : ∀ p ∈ allPos b.env, ∀ q ∈ allPos b.env, ∀ l w w', valAt b.env p = .borrow l w →
      valAt b.env q = .borrow l w' → p = q)
    (hheld : ∀ p ∈ allPos b.env, ∀ l, valAt b.env p = .loan l → liveLoan b.env l = true)
    (hfits : ∀ p v n args, ckContent b.env p = some v → D.placeDecl (topReadings b) p = .ind n args →
      (Γ.find? (·.name == n)).isSome → v.fitsInd n = true)
    (hpc : ∀ p, GrainOk D Γ (topReadings b) p → ckContent b.env p = some .proof →
      D.copy (D.placeDecl (topReadings b) p) = true) : Inv D Γ b := by
  have hsites : ∀ l x, x ∈ Env.sitesOf b.env l → ∃ p ∈ allPos b.env, valAt b.env p = .loan l ∧ x = ⟨p, [], false⟩ := by
    intro l x hx
    obtain ⟨p, hp, hx'⟩ := List.mem_flatMap.mp hx
    rw [(hs p hp).sitesOf] at hx'
    split at hx'
    · rename_i e; exact ⟨p, hp, e, List.mem_singleton.mp hx'⟩
    · cases hx'
  refine inv_step hi ht (fun v hv => .inr (by obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv; exact (hs p hp).simple))
    hocc hb ?_ ⟨fun v hv l hl => ?_, fun l => ?_⟩ ?_ ?_ (fun v hv l hl => ?_) hfits hpc
  · intro p hp q hq l h h'
    rw [shape_eq_shapeOf] at h h'
    obtain ⟨w, e⟩ := shapeOf_some h
    obtain ⟨w', e'⟩ := shapeOf_some h'
    exact hbor1 p hp q hq l w w' e e'
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    rcases (hs p hp).outerLoans' with e | ⟨m, e, e'⟩
    · rw [e] at hl; cases hl
    · rw [e'] at hl; cases List.mem_singleton.mp hl; exact hheld p hp _ e
  · simp only [Env.values, List.flatMap_map]
    refine count_flatMap_le_one _ l _ (allPos_nodup _) (fun p hp => ?_) (fun p hp q hq h h' => ?_)
    · rcases (hs p hp).outerLoans' with e | ⟨m, -, e'⟩
      · simp [e]
      · simp only [e', List.count_cons, List.count_nil]; split <;> omega
    · rcases (hs p hp).outerLoans' with e | ⟨m, e, e'⟩
      · rw [e] at h; cases h
      rcases (hs q hq).outerLoans' with f | ⟨m', f, f'⟩
      · rw [f] at h'; cases h'
      rw [e'] at h; rw [f'] at h'
      cases List.mem_singleton.mp h; cases List.mem_singleton.mp h'
      exact hloan1 p hp q hq l e f
  · intro k l hk hl x hx hf
    obtain ⟨p, -, -, rfl⟩ := hsites k x hx
    cases hf
  · intro pos path hf l hl x hx hpos
    obtain ⟨p, -, e, rfl⟩ := hsites l x hx
    cases hpos
    rw [e] at hf
    cases path with
    | nil => cases hf
    | cons s ss => cases s <;> simp [Value.follow, stepV] at hf
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv
    have := simple_loans_sub (hs p hp).simple hl
    exact hheld p hp l this

/-! ## A position written, a binding or a temporary -/

section SetAny
variable (E : Env) (w : Value)

theorem size_setAtE_any (p : Pos) : (Env.setAtE E p w).size = E.size := by
  cases p <;> simp [Env.setAtE]

theorem frameBinds_setAtE_temp (f i k : Nat) :
    (Env.setAtE E (.temp f i) w)[k]?.map (·.binds) = E[k]?.map (·.binds) := by
  simp only [Env.setAtE, Array.getElem?_modify]
  split <;> cases E[k]? <;> simp_all

theorem bindsAt_setAtE_temp (f i k j : Nat) :
    (Env.setAtE E (.temp f i) w)[k]?.bind (fun fr : Frame => fr.binds[j]?) =
      E[k]?.bind (fun fr : Frame => fr.binds[j]?) := by
  simp only [Env.setAtE, Array.getElem?_modify]
  split <;> cases E[k]? <;> simp_all

theorem back_setAtE_any (p : Pos) :
    (Env.setAtE E p w).back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) =
      E.back?.map (fun fr : Frame => fr.binds.toList.map (·.decl)) := by
  cases p with
  | bind f j => exact back_setAtE E f j w
  | temp f i =>
    have h := frameBinds_setAtE_temp E w f i (E.size - 1)
    simp only [Array.back?, size_setAtE_any]
    revert h
    cases (Env.setAtE E (.temp f i) w)[E.size - 1]? <;> cases E[E.size - 1]? <;> simp_all

theorem ckVarPos_setAtE_any (p : Pos) (i : Nat) : ckVarPos (Env.setAtE E p w) i = ckVarPos E i := by
  cases p with
  | bind f j => exact ckVarPos_setAtE E f j w i
  | temp f k =>
    have h := frameBinds_setAtE_temp E w f k (E.size - 1)
    have hb : (Env.setAtE E (.temp f k) w)[E.size - 1]!.binds = E[E.size - 1]!.binds := by
      rw [getElem!_def, getElem!_def]
      revert h
      cases (Env.setAtE E (.temp f k) w)[E.size - 1]? <;> cases E[E.size - 1]? <;> simp_all <;> rfl
    unfold ckVarPos; rw [size_setAtE_any, hb]

theorem binds_setAtE_any (p : Pos) {k i : Nat} {bb : Binding}
    (h : (Env.setAtE E p w)[k]?.bind (fun fr : Frame => fr.binds[i]?) = some bb) :
    ∃ ba, E[k]?.bind (fun fr : Frame => fr.binds[i]?) = some ba ∧ ba.ty = bb.ty ∧ ba.lazyTy = bb.lazyTy := by
  cases p with
  | bind f j => exact binds_setAtE_from E f j w h
  | temp f j => rw [bindsAt_setAtE_temp] at h; exact ⟨bb, h, rfl, rfl⟩

theorem ckContent_setAtE_any (p : Pos) (q : Place) : ckContent (Env.setAtE E p w) q =
    if ckVarPos E q.steps.1 = some p then w.follow q.steps.2 else ckContent E q := by
  unfold ckContent; rw [ckVarPos_setAtE_any]
  cases h : ckVarPos E q.steps.1 with
  | none => rfl
  | some pos =>
    simp only [Option.bind_some]
    by_cases e : pos = p
    · subst e; rw [if_pos rfl, Ochr.Meaning.Steps.valAt_setAtE_self _ (ckVarPos_mem E h)]
    · rw [if_neg (fun h' => e (Option.some.inj h')), valAt_setAtE_other E _ _ w e]

end SetAny

theorem _root_.Ochr.Meaning.Steps.Form.FEnd.erase' {E : Env} {px ph : Pos} {l : Nat} {c : Value}
    (h : FEnd E px ph l c) : FEnd E.erase px ph l c := by
  have hv : ∀ q, valAt E.erase q = valAt E q := valAt_erase E
  have ha : allPos E.erase = allPos E := allPos_erase E
  refine ⟨fun q hq => ?_, fun f i m hq => ?_, by rw [ha]; exact h.hpx, by rw [ha]; exact h.hph, by rw [hv]; exact h.x,
    by rw [hv]; exact h.y, h.c, fun q hq e => h.loan1 q (by rw [← ha]; exact hq) (by rw [← hv]; exact e),
    fun q hq w e => h.bor1 q (by rw [← ha]; exact hq) w (by rw [← hv]; exact e)⟩
  · rw [hv]; exact h.vals q (by rw [← ha]; exact hq)
  · rw [hv]; exact h.tempNoLoan f i m (by rw [← ha]; exact hq)

/-! ## `InvEnd`: one borrow ended in a fragment environment -/

theorem ckVarPos_bind {E : Env} {i : Nat} {pos : Pos} (h : ckVarPos E i = some pos) : ∃ f j, pos = .bind f j := by
  unfold ckVarPos at h; split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

theorem inv_endE {D : Decisions} {Γ : List IndDecl} {a : MState} {px ph : Pos} {l : Nat} {c : Value}
    (hL : PlaceLocal D) (hF : FEnd a.env px ph l c)
    (hd : ∀ f j, px = .bind f j → ∀ b, a.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .other)
    (hi : Inv D Γ a) : Inv D Γ { a with env := endE a.env px ph c } := by
  have hcN : c.Num := hF.c
  have ha : allPos (endE a.env px ph c) = allPos a.env := FEnd.allPos_endE
  have hvx : valAt (endE a.env px ph c) px = c := by rw [hF.valAt_endE, if_pos rfl]
  have hvh : valAt (endE a.env px ph c) ph = .bot := by rw [hF.valAt_endE, if_neg hF.ne, if_pos rfl]
  have hval : ∀ q, q ≠ px → q ≠ ph → valAt (endE a.env px ph c) q = valAt a.env q := fun q e1 e2 => by
    rw [hF.valAt_endE, if_neg e1, if_neg e2]
  have hR : topReadings { a with env := endE a.env px ph c } = topReadings a := by
    unfold topReadings endE; rw [back_setAtE_any, back_setAtE_any]
  have hck : ∀ i, ckVarPos (endE a.env px ph c) i = ckVarPos a.env i := fun i => by
    unfold endE; rw [ckVarPos_setAtE_any, ckVarPos_setAtE_any]
  obtain ⟨hf, hp⟩ := readClauses_of (b := { a with env := endE a.env px ph c }) hi hR (fun p x h => by
    show _ ∨ _
    unfold ckContent at h ⊢
    rw [hck] at h
    cases hpos : ckVarPos a.env p.steps.1 with
    | none => rw [hpos] at h; cases h
    | some pos =>
      simp only [hpos, Option.bind_some] at h ⊢
      by_cases e1 : pos = px
      · subst e1
        rw [hvx] at h
        right
        refine ⟨fun e => (by have := hcN.follow h; rw [e] at this; cases this), fun n args e => absurd e ?_⟩
        obtain ⟨f, j, e⟩ := ckVarPos_bind hpos
        subst e
        exact hL.noInd (.inl rfl) (fun b hb => hd f j rfl b hb) hpos n args
      · by_cases e2 : pos = ph
        · subst e2; rw [hvh] at h; right; rw [bot_follow h]; exact ⟨fun e => (by cases e), fun _ _ _ _ => rfl⟩
        · rw [hval pos e1 e2] at h; exact .inl h)
  have hpm : ∀ p ∈ allPos (endE a.env px ph c), p ∈ allPos a.env := fun p hp => by rw [← ha]; exact hp
  have hnb : ∀ m, valAt (endE a.env px ph c) px ≠ .loan m ∧ valAt (endE a.env px ph c) ph ≠ .loan m :=
    fun m => ⟨(by rw [hvx]; exact FVal.num_ne_loan hcN m), (by rw [hvh]; exact fun e => by cases e)⟩
  have hnb' : ∀ m w, valAt (endE a.env px ph c) px ≠ .borrow m w ∧ valAt (endE a.env px ph c) ph ≠ .borrow m w :=
    fun m w => ⟨(by rw [hvx]; exact fun e => by rw [e] at hcN; cases hcN), (by rw [hvh]; exact fun e => by cases e)⟩
  -- a position holding a loan or a borrow after the end is not `px` or `ph`, and held it before
  have hold : ∀ p v, valAt (endE a.env px ph c) p = v → (∀ m, v ≠ .loan m) ∨ p ≠ px ∧ p ≠ ph ∧ valAt a.env p = v := by
    intro p v e
    by_cases e1 : p = px
    · subst e1; rw [hvx] at e; subst e; exact .inl (FVal.num_ne_loan hcN)
    by_cases e2 : p = ph
    · subst e2; rw [hvh] at e; subst e; exact .inl fun m e => by cases e
    exact .inr ⟨e1, e2, by rw [← hval p e1 e2]; exact e⟩
  refine inv_of_fval hi (tabSame_env _ _) (fun k i bb h => ?_) (fun p hp => ?_) (fun l' ⟨v, hv', h⟩ => ?_)
    (fun p hp q hq m ep eq => ?_) (fun p hp q hq m w w' ep eq => ?_) (fun p hp m ep => ?_) hf hp
  · unfold endE at h
    obtain ⟨b1, h1, h2, h3⟩ := binds_setAtE_any _ _ _ h
    obtain ⟨b0, h0, h2', h3'⟩ := binds_setAtE_any _ _ _ h1
    exact .inl ⟨k, i, b0, h0, h2'.trans h2, h3'.trans h3⟩
  · by_cases e1 : p = px
    · subst e1; rw [hvx]; exact .num hcN
    by_cases e2 : p = ph
    · subst e2; rw [hvh]; exact .bot
    rw [hval p e1 e2]; exact hF.vals p (hpm p hp)
  · obtain ⟨p, hp, rfl⟩ := mem_values_iff.mp hv'
    refine .inl ⟨valAt a.env p, mem_values_iff.mpr ⟨p, hpm p hp, rfl⟩, ?_⟩
    by_cases e1 : p = px
    · subst e1; rw [hvx, Ochr.Value.Bland.anyAtom (v := c) (Or.inl hcN) rfl (fun _ => rfl) rfl rfl] at h; cases h
    by_cases e2 : p = ph
    · subst e2; rw [hvh, Ochr.Value.Bland.anyAtom (v := .bot) (Or.inr (Or.inr rfl)) rfl (fun _ => rfl) rfl rfl] at h; cases h
    rw [hval p e1 e2] at h; exact h
  · by_cases e1 : p = px
    · subst e1; exact absurd ep ((hnb m).1)
    by_cases e1' : q = px
    · subst e1'; exact absurd eq ((hnb m).1)
    by_cases e2 : p = ph
    · subst e2; exact absurd ep ((hnb m).2)
    by_cases e2' : q = ph
    · subst e2'; exact absurd eq ((hnb m).2)
    rw [hval p e1 e2] at ep; rw [hval q e1' e2'] at eq
    exact inv_loan1 hi (hpm p hp) (hpm q hq) ep eq
  · by_cases e1 : p = px
    · subst e1; exact absurd ep ((hnb' m w).1)
    by_cases e1' : q = px
    · subst e1'; exact absurd eq ((hnb' m w').1)
    by_cases e2 : p = ph
    · subst e2; exact absurd ep ((hnb' m w).2)
    by_cases e2' : q = ph
    · subst e2'; exact absurd eq ((hnb' m w').2)
    rw [hval p e1 e2] at ep; rw [hval q e1' e2'] at eq
    exact inv_bor1 hi (hpm p hp) (hpm q hq) ep eq
  · by_cases e1 : p = px
    · subst e1; exact absurd ep ((hnb m).1)
    by_cases e2 : p = ph
    · subst e2; exact absurd ep ((hnb m).2)
    rw [hval p e1 e2] at ep
    have hml : m ≠ l := fun e => by subst e; exact e1 (hF.loan1 p (hpm p hp) ep)
    have hlive : liveLoan a.env m = true :=
      hi.2.1.1 _ (mem_values_iff.mpr ⟨p, hpm p hp, rfl⟩) m (by rw [ep]; simp [Value.outerLoans])
    obtain ⟨q, hq, hhb⟩ := liveLoan_iff.mp hlive
    have hqx : q ≠ px := fun e => by subst e; rw [hF.x] at hhb; cases hhb
    have hqh : q ≠ ph := fun e => by
      subst e; rw [hF.y] at hhb
      simp only [Value.holdsBorrow, Ochr.Value.Bland.holdsBorrow (v := c) (Or.inl hcN) m, Bool.or_false] at hhb
      exact hml (beq_iff_eq.mp hhb).symm
    exact liveLoan_iff.mpr ⟨q, by rw [ha]; exact hq, by rw [hval q hqx hqh]; exact hhb⟩

theorem invEnd : InvEnd := by
  intro D Γ st px ph l c hL hF hd hi
  rw [norm_withEnv]
  have hE : (endE st.env px ph c).erase = endE st.norm.env px ph c := by
    unfold endE; rw [erase_setAtE, erase_setAtE]; rfl
  rw [hE]
  exact inv_endE (a := st.norm) hL hF.erase' (fun f j e b hb => hd f j e b (by rw [← binds_norm]; exact hb)) hi

/-! ## `InvLendG`: a number binding lent at the counter, other borrows live -/

theorem occurs_of_pos {a : MState} {q : Pos} {m : Nat} (hq : q ∈ allPos a.env)
    (h : (valAt a.env q).anyAtom (fun x => x == .loan m || (match x with | .borrow l' _ => l' == m | _ => false)) = true) :
    a.Occurs m := ⟨_, mem_values_iff.mpr ⟨q, hq, rfl⟩, h⟩

theorem inv_lendG {D : Decisions} {Γ : List IndDecl} {a : MState} {f j : Nat} (hL : PlaceLocal D)
    (hp : Pos.bind f j ∈ allPos a.env) (hn : (valAt a.env (.bind f j)).Num)
    (hd : ∀ b, a.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .other)
    (hs : ∀ q ∈ allPos a.env, FVal (valAt a.env q)) (hi : Inv D Γ a) :
    Inv D Γ { a with env := Env.pushTempE (Env.setAtE a.env (.bind f j) (.loan a.nextLoan)) (.borrow a.nextLoan (valAt a.env (.bind f j))), nextLoan := a.nextLoan + 1 } := by
  have wocc : ∀ l, a.Occurs l → l < a.nextLoan := hi.2.2.2.2.2.2.2.2.2.2.2.2.2
  generalize hE' : Env.setAtE a.env (.bind f j) (.loan a.nextLoan) = E'
  generalize hw : valAt a.env (.bind f j) = w at hn
  have hsz : E'.size = a.env.size := by rw [← hE']; exact size_setAtE _ _ _ _
  have hne : 0 < a.env.size := by
    obtain ⟨fr, b, hf, -⟩ := mem_allPos_bind _ _ _ hp
    rcases Nat.eq_zero_or_pos a.env.size with e | e
    · have : f < a.env.size := (Array.getElem?_eq_some_iff.mp hf).1
      omega
    · exact e
  obtain ⟨fr, hfr⟩ : ∃ fr, E'[E'.size - 1]? = some fr := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have haE : allPos E' = allPos a.env := by rw [← hE', allPos_setAtE]
  have hpos : allPos (Env.pushTempE E' (.borrow a.nextLoan w)) = allPos a.env ++ [.temp (E'.size - 1) fr.temps.size] := by
    rw [allPos_pushTempE _ _ fr hfr (by omega), haE]
  have hnt : ∀ q ∈ allPos a.env, q ≠ .temp (E'.size - 1) fr.temps.size := fun q hq e => by
    rw [← haE, e] at hq
    obtain ⟨fr', hf', hi'⟩ := mem_allPos_temp _ _ _ hq
    rw [hfr] at hf'; cases hf'; exact absurd hi' (Nat.lt_irrefl _)
  have vnew : valAt (Env.pushTempE E' (.borrow a.nextLoan w)) (.temp (E'.size - 1) fr.temps.size) = .borrow a.nextLoan w :=
    valAt_pushTempE_new _ _ fr hfr
  have vx : valAt (Env.pushTempE E' (.borrow a.nextLoan w)) (.bind f j) = .loan a.nextLoan := by
    rw [valAt_pushTempE_bind, ← hE', valAt_setAtE_self hp]
  have vold : ∀ q ∈ allPos a.env, q ≠ .bind f j → valAt (Env.pushTempE E' (.borrow a.nextLoan w)) q = valAt a.env q :=
    fun q hq e => by rw [valAt_pushTempE_mem E' _ fr hfr (by rw [haE]; exact hq), ← hE', valAt_setAtE_other _ _ _ _ e]
  -- every position of the new environment: the new temporary, `x`, or an old one
  have hcase : ∀ q ∈ allPos (Env.pushTempE E' (.borrow a.nextLoan w)),
      q = .temp (E'.size - 1) fr.temps.size ∨ q = .bind f j ∨ (q ∈ allPos a.env ∧ q ≠ .bind f j) := by
    intro q hq
    rw [hpos, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · by_cases e : q = .bind f j
      · exact .inr (.inl e)
      · exact .inr (.inr ⟨hq, e⟩)
    · exact .inl hq
  have hmem : ∀ q ∈ allPos a.env, q ∈ allPos (Env.pushTempE E' (.borrow a.nextLoan w)) := fun q hq => by
    rw [hpos]; exact List.mem_append_left _ hq
  -- a label of an old value is below the counter
  have hlt : ∀ q ∈ allPos a.env, ∀ m, (∃ w', valAt a.env q = .loan m ∨ valAt a.env q = .borrow m w') → m < a.nextLoan := by
    intro q hq m ⟨w', e⟩
    refine wocc m ⟨_, mem_values_iff.mpr ⟨q, hq, rfl⟩, ?_⟩
    rcases e with e | e
    · rw [e]; exact (occ_loan m m).trans (beq_self_eq_true m)
    · have hw' : w'.Num := by
        have := hs q hq; rw [e] at this
        cases this with
        | num h => cases h
        | bor _ h => exact h
      rw [e]; exact (occ_numBorrow hw').trans (beq_self_eq_true m)
  have hR : topReadings { a with env := Env.pushTempE E' (.borrow a.nextLoan w), nextLoan := a.nextLoan + 1 } =
      topReadings a := by
    unfold topReadings; dsimp only; rw [back_pushTempE, ← hE', back_setAtE]
  obtain ⟨hf, hpc⟩ := readClauses_of (b := { a with env := Env.pushTempE E' (.borrow a.nextLoan w), nextLoan := a.nextLoan + 1 })
    hi hR (fun p x h => by
      show _ ∨ _
      have h' : ckContent E' p = some x := by rw [← ckContent_pushTempE E' (.borrow a.nextLoan w)]; exact h
      rw [← hE', ckContent_setAtE] at h'
      split at h'
      · rename_i hp0
        right
        refine ⟨fun e => ?_, fun n args e => absurd e (hL.noInd (.inl rfl) hd hp0 n args)⟩
        subst e
        revert h'; generalize p.steps.2 = ss; intro h'
        cases ss with
        | nil => cases h'
        | cons s ss => cases s <;> simp [Value.follow, stepV] at h'
      · exact .inl h')
  refine inv_of_fval hi ⟨Nat.le_succ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun k i bb h => ?_) (fun q hq => ?_)
    (fun l ⟨v, hv', h⟩ => ?_) (fun p hp q hq m ep eq => ?_) (fun p hp q hq m w₁ w₂ ep eq => ?_) (fun p hp m ep => ?_) hf hpc
  · rw [binds_pushTempE, ← hE'] at h
    obtain ⟨ba, h1, h2, h3⟩ := binds_setAtE_from _ _ _ _ h
    exact .inl ⟨k, i, ba, h1, h2, h3⟩
  · rcases hcase q hq with rfl | rfl | ⟨hq', e⟩
    · rw [vnew]; exact .bor _ hn
    · rw [vx]; exact .loan _
    · rw [vold q hq' e]; exact hs q hq'
  · obtain ⟨q, hq, rfl⟩ := mem_values_iff.mp hv'
    rcases hcase q hq with rfl | rfl | ⟨hq', e⟩
    · rw [vnew] at h; have h2 := (occ_numBorrow hn).symm.trans h
      exact .inr (by rw [← beq_iff_eq.mp h2]; exact Nat.lt_succ_self _)
    · rw [vx] at h; have h2 := (occ_loan _ _).symm.trans h
      exact .inr (by rw [← beq_iff_eq.mp h2]; exact Nat.lt_succ_self _)
    · rw [vold q hq' e] at h; exact .inl ⟨_, mem_values_iff.mpr ⟨q, hq', rfl⟩, h⟩
  · rcases hcase p hp with rfl | rfl | ⟨hp', e⟩
    · rw [vnew] at ep; cases ep
    · rcases hcase q hq with rfl | rfl | ⟨hq', e'⟩
      · rw [vnew] at eq; cases eq
      · rfl
      · rw [vx] at ep; cases ep; rw [vold q hq' e'] at eq
        exact absurd (hlt q hq' _ ⟨w, .inl eq⟩) (Nat.lt_irrefl _)
    · rcases hcase q hq with rfl | rfl | ⟨hq', e'⟩
      · rw [vnew] at eq; cases eq
      · rw [vx] at eq; cases eq; rw [vold p hp' e] at ep
        exact absurd (hlt p hp' _ ⟨w, .inl ep⟩) (Nat.lt_irrefl _)
      · rw [vold p hp' e] at ep; rw [vold q hq' e'] at eq; exact inv_loan1 hi hp' hq' ep eq
  · rcases hcase p hp with rfl | rfl | ⟨hp', e⟩
    · rcases hcase q hq with rfl | rfl | ⟨hq', e'⟩
      · rfl
      · rw [vx] at eq; cases eq
      · rw [vnew] at ep; cases ep; rw [vold q hq' e'] at eq
        exact absurd (hlt q hq' _ ⟨w₂, .inr eq⟩) (Nat.lt_irrefl _)
    · rw [vx] at ep; cases ep
    · rcases hcase q hq with rfl | rfl | ⟨hq', e'⟩
      · rw [vnew] at eq; cases eq; rw [vold p hp' e] at ep
        exact absurd (hlt p hp' _ ⟨w₁, .inr ep⟩) (Nat.lt_irrefl _)
      · rw [vx] at eq; cases eq
      · rw [vold p hp' e] at ep; rw [vold q hq' e'] at eq; exact inv_bor1 hi hp' hq' ep eq
  · rcases hcase p hp with rfl | rfl | ⟨hp', e⟩
    · rw [vnew] at ep; cases ep
    · rw [vx] at ep; cases ep
      exact liveLoan_iff.mpr ⟨.temp (E'.size - 1) fr.temps.size,
        by rw [hpos]; exact List.mem_append_right _ (List.mem_singleton_self _), by rw [vnew]; simp [Value.holdsBorrow]⟩
    · rw [vold p hp' e] at ep
      have hlive : liveLoan a.env m = true :=
        hi.2.1.1 _ (mem_values_iff.mpr ⟨p, hp', rfl⟩) m (by rw [ep]; simp [Value.outerLoans])
      obtain ⟨q, hq, hhb⟩ := liveLoan_iff.mp hlive
      have hqx : q ≠ .bind f j := fun e' => by
        subst e'; rw [hw] at hhb; rw [Ochr.Value.Bland.holdsBorrow (Or.inl hn)] at hhb; cases hhb
      exact liveLoan_iff.mpr ⟨q, hmem q hq, by rw [vold q hq hqx]; exact hhb⟩

theorem invLendG : InvLendG := by
  intro D Γ st f j T? hL hp hn hb hs _ hi
  rw [norm_withTempT]
  have hva : valAt st.norm.env (.bind f j) = valAt st.env (.bind f j) := valAt_erase _ _
  have hp' : Pos.bind f j ∈ allPos st.norm.env := by
    show _ ∈ allPos (Env.erase st.env); rw [allPos_erase]; exact hp
  have key := inv_lendG (a := st.norm) hL hp' (by rw [hva]; exact hn)
    (fun b h => (hb b (by rw [← binds_norm]; exact h)).2)
    (fun q hq => by
      show FVal (valAt (Env.erase st.env) q); rw [valAt_erase]
      exact hs q (by rw [← allPos_erase]; exact hq)) hi
  rw [hva] at key
  show Inv D Γ { st.norm with env := Env.pushTempE (Env.setAtE st.env (.bind f j) (.loan st.nextLoan)).erase (.borrow st.nextLoan (valAt st.env (.bind f j))), nextLoan := st.nextLoan + 1 }
  rw [erase_setAtE]
  exact key

end Ochr.Meaning.Steps.Machine
