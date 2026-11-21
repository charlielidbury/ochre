import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.UpdBot
import Ochr.Meaning.RunEnv
import Ochr.Meaning.KeyBridge

/-!
# L3: the write of `⊥` keeps the relation (the relation's half of `botWrite_step`)
-/

namespace Ochr.Meaning.Steps

open Ochr.Meaning

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The skeleton of the checker's state read as a reference state is unchanged by a write at a
binding (its type's code is read off the stored type, not the value). -/
theorem skel_setAtE (st : MState) (f i : Nat) (v' : Value) :
    (SM' K ρ { st with env := Env.setAtE st.env (.bind f i) v' }).env.map (fun fr => fr.binds.map bindSkel) =
      (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) := by
  apply List.ext_getElem?
  intro f'
  simp only [SM', MState.sstate, Binding.refTy, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Array.getElem?_toList, hintAt_setAtE]
  simp only [Env.setAtE, Array.getElem?_modify]
  by_cases hf : f = f'
  · subst hf
    rcases hfr : st.env[f]? with _ | fr
    · simp
    · simp only [if_true, Option.map_some, Function.comp_apply, Option.some.injEq]
      apply List.ext_getElem?
      intro i'
      simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Array.getElem?_toList,
        Array.getElem?_modify]
      by_cases hi : i = i'
      · subst hi
        rcases hb : fr.binds[i]? with _ | b
        · simp
        · simp only [if_true, Option.map_some, Function.comp_apply, bindSkel]; rfl
      · simp only [hi, if_false]
        rcases fr.binds[i']? with _ | b' <;> rfl
  · simp only [hf, if_false]
    rcases st.env[f']? with _ | fr'
    · rfl
    · simp only [Option.map_some, Function.comp_apply, List.map_map, Option.some.injEq]
      rfl

/-- A write in the reference state keeps its skeleton (only a meaning changes). -/
theorem skel_setAt (s : SState) (p : Pos) (g : SVal) :
    (s.setAt p g).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
  cases p with
  | bind f i =>
    simp only [SState.setAt]
    apply map_modify_eq
    intro fr
    show (fr.binds.modify i _).map _ = _
    apply map_modify_eq
    intro _; rfl
  | temp f i =>
    simp only [SState.setAt]
    apply map_modify_eq
    intro _; rfl

/-- The values of Ω after a write are the written one and the old ones. -/
theorem mem_values_setAtE {env : Env} {p : Pos} {v' w : Value} (h : w ∈ Env.values (Env.setAtE env p v')) :
    w = v' ∨ w ∈ Env.values env := by
  simp only [Env.values, List.mem_map, allPos_setAtE] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  by_cases hqp : q = p
  · subst hqp
    rcases q with ⟨f, i⟩ | ⟨f, i⟩
    · obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind env f i hq
      exact .inl (valAt_setAtE_bind env f i v' fr b hf hb)
    · obtain ⟨fr, hf, hi⟩ := mem_allPos_temp env f i hq
      exact .inl (valAt_setAtE_temp env f i v' fr hf hi)
  · exact .inr ⟨q, hq, (valAt_setAtE_other env p q v' hqp).symm⟩

/-- The test the relation's `fresh` clause makes of an atom: a loan or a borrow of `l`. -/
theorem shallow_occurs (l : Nat) :
    ShallowAtom (fun a => a == .loan l || (match a with | .borrow l' _ => l' == l | _ => false)) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

/-- The write of `⊥` makes no label occur that did not. -/
theorem occurs_setAtE_bot {st : MState} {pos : Pos} {steps : List Step} {v' : Value}
    (hp : pos ∈ allPos st.env) (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v') (l : Nat)
    (h : ({ st with env := Env.setAtE st.env pos v' } : MState).Occurs l) : st.Occurs l := by
  obtain ⟨w, hw, ha⟩ := h
  rcases mem_values_setAtE hw with rfl | hw
  · exact ⟨valAt st.env pos, List.mem_map.mpr ⟨pos, hp, rfl⟩,
      anyAtom_of_updAt_bot (shallow_occurs l) steps _ _ hv ha⟩
  · exact ⟨w, hw, ha⟩

/-- The test `hasBorrow` makes of an atom is shallow. -/
theorem shallow_borrow : ShallowAtom (fun | .borrow _ _ => true | _ => false) where
  bot := rfl
  ind _ _ _ _ _ _ := rfl
  borrow _ _ _ := rfl
  gloan _ _ _ := rfl
  succ _ _ := rfl

/-- **The write of `⊥` holds the same borrows**, where a borrow is the whole value of its position
((WF1)) and a whole root written holds no borrow. -/
theorem holdsBorrow_updAt_bot {steps : List Step} {v v' : Value}
    (hwf : match v with | .borrow _ w => ¬ w.hasBorrow | v => ¬ v.hasBorrow)
    (hroot : steps = [] → topLabel v = none) (h : Value.updAt (fun _ => .bot) steps v = some v') (l : Nat) :
    v'.holdsBorrow l = v.holdsBorrow l := by
  have hnb : ∀ x : Value, ¬ x.hasBorrow → x.holdsBorrow l = false := fun x hx => by
    cases e : x.holdsBorrow l
    · rfl
    · exact absurd (hasBorrow_of_holdsBorrow l x e) hx
  rcases steps with _ | ⟨st, ss⟩
  · simp only [Value.updAt, Option.some.injEq] at h
    subst h
    have hv : ¬ v.hasBorrow := by
      cases v <;> first | exact hwf | (simp [topLabel] at hroot)
    rw [hnb v hv]; rfl
  · cases v with
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        have hw : ¬ w.hasBorrow := hwf
        have hw2 : ¬ w'.hasBorrow := fun hb => hw (anyAtom_of_updAt_bot shallow_borrow ss w w' hw' hb)
        simp only [Value.holdsBorrow, hnb w hw, hnb w' hw2]
      | proj _ | field _ => simp [Value.updAt] at h
    | _ =>
      have hv : ¬ Value.hasBorrow _ := hwf
      have hv2 : ¬ v'.hasBorrow := fun hb => hv (anyAtom_of_updAt_bot shallow_borrow _ _ v' h hb)
      rw [hnb _ hv, hnb _ hv2]

theorem valAt_setAtE_self {env : Env} {pos : Pos} (v : Value) (hp : pos ∈ allPos env) :
    valAt (Env.setAtE env pos v) pos = v := by
  rcases pos with ⟨f, i⟩ | ⟨f, i⟩
  · obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind env f i hp
    exact valAt_setAtE_bind env f i v fr b hf hb
  · obtain ⟨fr, hf, hi⟩ := mem_allPos_temp env f i hp
    exact valAt_setAtE_temp env f i v fr hf hi

theorem find?_congr' {α : Type _} {P Q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, P x = Q x) → l.find? P = l.find? Q
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.find?_cons, h a (List.mem_cons_self ..)]
    split
    · rfl
    · exact find?_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A write that keeps the borrows the position holds keeps every borrow's liveness. -/
theorem liveLoan_setAtE {env : Env} {pos : Pos} {v' : Value} (hp : pos ∈ allPos env)
    (h : ∀ l, v'.holdsBorrow l = (valAt env pos).holdsBorrow l) (l : Nat) :
    liveLoan (Env.setAtE env pos v') l = liveLoan env l := by
  unfold liveLoan findBorrow
  rw [allPos_setAtE, find?_congr' (Q := fun p => (valAt env p).holdsBorrow l)]
  intro x _
  by_cases hx : x = pos
  · subst hx; rw [valAt_setAtE_self v' hp, h]
  · rw [valAt_setAtE_other env pos x v' hx]

/-- **After the access, the write of `⊥` keeps every borrow's sites**: none is at, over or under
the place (`hclear`), and the write removes only those (`sitesOf_updAt_bot`). -/
theorem sitesOf_setAtE_bot {env : Env} {pos : Pos} {steps : List Step} {v' : Value} (hp : pos ∈ allPos env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt env pos) = some v') (l : Nat)
    (hclear : ∀ x ∈ Env.sitesOf env l, x.pos = pos → dataHit steps x.path = false) (x : Site) :
    x ∈ Env.sitesOf (Env.setAtE env pos v') l ↔ x ∈ Env.sitesOf env l := by
  unfold Env.sitesOf
  rw [allPos_setAtE]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp', hx⟩
    by_cases hpp : p = pos
    · subst hpp
      rw [valAt_setAtE_self v' hp, sitesOf_updAt_bot l p steps [] _ v' hv x] at hx
      exact ⟨p, hp', hx.1⟩
    · rw [valAt_setAtE_other env pos p v' hpp] at hx
      exact ⟨p, hp', hx⟩
  · rintro ⟨p, hp', hx⟩
    by_cases hpp : p = pos
    · subst hpp
      refine ⟨p, hp', ?_⟩
      rw [valAt_setAtE_self v' hp, sitesOf_updAt_bot l p steps [] _ v' hv x]
      refine ⟨hx, ?_⟩
      have hxp := (sitesOf_prefix l p [] _ x hx).1
      have hd := hclear x (by simp only [Env.sitesOf, List.mem_flatMap]; exact ⟨p, hp', hx⟩) hxp
      simp only [dataHit, Bool.or_eq_false_iff] at hd
      simp only [List.nil_append]
      -- the checker's positional prefix is an erased one (`KeyBridge`, the free direction)
      intro h
      have h' := pathKey_prefix_of_walkKey (List.isPrefixOf_iff_prefix.mp h)
      rw [← List.isPrefixOf_iff_prefix, hd.2] at h'
      cases h'
    · rw [← valAt_setAtE_other env pos p v' hpp] at hx
      exact ⟨p, hp', hx⟩

theorem shapeOf_eq_topLabel (v : Value) : shapeOf v = topLabel v := by cases v <;> rfl

theorem SState.lent_setAt (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).lent = s.lent := by
  cases p <;> rfl

theorem SState.nextLoan_setAt' (s : SState) (p : Pos) (g : SVal) : (s.setAt p g).nextLoan = s.nextLoan := by
  cases p <;> rfl

theorem SState.live_setAt (s : SState) (p : Pos) (g : SVal) (l : Nat) : (s.setAt p g).Live l ↔ s.Live l := by
  simp only [SState.Live, SState.liveLabels, SState.positions_setAt, SState.shape_setAt]

/-- **L3, the relation's half: the write of `⊥` keeps the relation.** After the access (no live
borrow lent at, over or under the place), the checker's write of `⊥` at a binding's path and the
reference's write of `moved` there give related states: the meanings by L2 (with sealed siblings
whose tails read no hint, `mean_updAt_botS`, docs/31 D45; first stated for a value holding no
sealed program at all), the skeleton, the holders, liveness and every borrow's sites unchanged. -/
theorem botWrite_rel (st : MState) (s : SState) (π : Nat → Nat) (f i : Nat) (steps : List Step) (v' : Value)
    (hs : Rel K ρ φ π st s) (hwf1 : WF1 st.env)
    (hp : Pos.bind f i ∈ allPos st.env) (hsp : Pos.bind f i ∈ s.positions)
    (hv : Value.updAt (fun _ => .bot) steps (valAt st.env (.bind f i)) = some v')
    (hroot : steps = [] → Env.shape st.env (.bind f i) = none)
    (hclear : ∀ l, liveLoan st.env l = true → ∀ x ∈ Env.sitesOf st.env l, x.pos = .bind f i →
      dataHit steps x.path = false)
    (hplain : (valAt st.env (.bind f i)).anyAtom (Value.bareCtor K.Γ) = false ∧
      (valAt st.env (.bind f i)).anyAtom (fun a => a.isSealed && !a.topHintFree K.Γ) = false)
    (hnat : ∀ ψ, NatAlong K.dm K.M K.Γ ρ ψ steps (valAt st.env (.bind f i))) :
    Rel K ρ φ π { st with env := Env.setAtE st.env (.bind f i) v' }
      (s.setAt (.bind f i) fun φ' =>
        (Sem.updAt K.dm K.Γ (s.tyAt (.bind f i)) (fun _ => .moved) steps (s.valAt (.bind f i) φ')).getD .err) := by
  -- the borrows held are the same, so liveness is
  have hwf := hwf1.1 (Pos.bind f i) hp
  have hhold : ∀ l, v'.holdsBorrow l = (valAt st.env (Pos.bind f i)).holdsBorrow l := holdsBorrow_updAt_bot hwf
    (fun he => by rw [← shapeOf_eq_topLabel, ← shape_eq_shapeOf]; exact hroot he) hv
  have hlive : ∀ l, liveLoan (Env.setAtE st.env (Pos.bind f i) v') l = liveLoan st.env l := liveLoan_setAtE hp hhold
  -- the holders are the same
  have hshape : ∀ q, Env.shape (Env.setAtE st.env (Pos.bind f i) v') q = Env.shape st.env q := by
    intro q
    by_cases hq : q = (Pos.bind f i)
    · rw [hq]
      rw [shape_eq_shapeOf, shape_eq_shapeOf, valAt_setAtE_self v' hp, shapeOf_eq_topLabel, shapeOf_eq_topLabel]
      rcases steps with _ | ⟨st0, ss⟩
      · simp only [Value.updAt, Option.some.injEq] at hv
        subst hv
        have := hroot rfl
        rw [shape_eq_shapeOf, shapeOf_eq_topLabel] at this
        rw [this]; rfl
      · exact updAt_bot_top hv
    · exact shape_setAtE_other st.env (Pos.bind f i) q v' hq
  -- the reference's live labels are the same
  have hF : ∀ ψ, (RelF φ (s.setAt (Pos.bind f i) fun φ' =>
      (Sem.updAt K.dm K.Γ (s.tyAt (Pos.bind f i)) (fun _ => .moved) steps (s.valAt (Pos.bind f i) φ')).getD .err) ψ ∧
      TypedLive K (s.setAt (Pos.bind f i) fun φ' =>
      (Sem.updAt K.dm K.Γ (s.tyAt (Pos.bind f i)) (fun _ => .moved) steps (s.valAt (Pos.bind f i) φ')).getD .err) ψ) →
      RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l hl => hψ.1 l (fun h => hl ((SState.live_setAt _ _ _ l).mp h)),
      fun l hl => by
        have := hψ.2 l ((SState.live_setAt _ _ _ l).mpr hl)
        rwa [holderTy_setAt] at this⟩
  have hp' : Pos.bind f i ∈ allPos (Env.setAtE st.env (Pos.bind f i) v') := by rw [allPos_setAtE]; exact hp
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    rw [skel_setAtE K ρ st f i v', hs.skel]
    exact (skel_setAt s _ _).symm
  · -- fresh
    intro l hl ho
    rw [SState.nextLoan_setAt']
    exact hs.fresh l hl (occurs_setAtE_bot hp hv l ho)
  · -- readings at bindings
    intro ψ hψ p hpt
    have hψ0 := hF ψ hψ
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) v') p = _
    by_cases hpp : p = Pos.bind f i
    · rw [hpp, valAt_setAt_self _ _ _ hsp]
      show _ = (Sem.updAt K.dm K.Γ (s.tyAt (Pos.bind f i)) (fun _ => .moved) steps (s.valAt (Pos.bind f i) ψ)).getD .err
      rw [← hs.sim.1 ψ hψ0 (Pos.bind f i) (by simp [IsTemp])]
      show _ = (Sem.updAt K.dm K.Γ (s.tyAt (Pos.bind f i)) (fun _ => .moved) steps
        (Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) st.env (Pos.bind f i))).getD .err
      rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp', hintAt_setAtE, valAt_setAtE_self v' hp,
        mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp,
        mean_updAt_botS K ρ _ steps _ _ _ v' hv hplain.1 hplain.2 (hnat _)]
      rfl
    · rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) p v' _ hpp, SState.valAt_setAt_ne _ _ _ _ (Ne.symm hpp)]
      exact hs.sim.1 ψ hψ0 p hpt
  · -- holders at bindings, checker to reference
    intro p l hpt hsh
    have hsh' : Env.shape st.env p = some l := by rw [← hshape p]; exact hsh
    rw [SState.shape_setAt]
    exact hs.sim.2.1 p l hpt hsh'
  · -- holders at bindings, reference to checker
    intro p l' hpt hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨l, h1, h2⟩ := hs.sim.2.2.1 p l' hpt hsh
    exact ⟨l, by show Env.shape _ p = _; rw [hshape p]; exact h1, h2⟩
  · -- borrows in flight, checker to reference
    intro f' i' l hsh
    have hsh' : Env.shape st.env (.temp f' i') = some l := by rw [← hshape]; exact hsh
    obtain ⟨j, hj, hval⟩ := hs.sim.2.2.2.1 f' i' l hsh'
    refine ⟨j, by rw [SState.shape_setAt]; exact hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) v') (.temp f' i') = _
    rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) _ v' _ (by simp), SState.valAt_setAt_ne _ _ _ _ (by simp)]
    exact hval ψ (hF ψ hψ)
  · -- borrows in flight, reference to checker
    intro f' j l' hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨i', l, h1, h2⟩ := hs.sim.2.2.2.2 f' j l' hsh
    exact ⟨i', l, by show Env.shape _ _ = _; rw [hshape]; exact h1, h2⟩
  · -- inj
    intro l l' hl hl' he
    rw [hlive] at hl hl'
    exact hs.inj l l' hl hl' he
  · -- sites
    intro l hl x
    rw [hlive] at hl
    rw [SState.lent_setAt, hs.sites l hl x]
    exact (sitesOf_setAtE_bot hp hv l (hclear l hl) x).symm
  · -- holders: the write changes no position and no holder
    intro p l h
    rw [SState.shape_setAt'] at h
    rw [SState.positions_setAt]
    exact hs.holders p l h
  · -- records: the write changes no record, no holder and no stored type
    intro l hl
    rw [holderTy_setAt]
    have hrec := hs.records l ((SState.live_setAt _ _ _ l).mp hl)
    rcases f with _ | f <;> exact hrec

end

end Ochr.Meaning.Steps
