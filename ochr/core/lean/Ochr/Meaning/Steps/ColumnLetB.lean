import Ochr.Meaning.Steps.ColumnBorrow
import Ochr.Meaning.Steps.ColumnLet

/-!
# The borrow column: `let y = &x; w` (lead8)

The `let` of a borrow-valued right-hand side. On the checker's side the borrow leaves the monad and
is bound (`LetInv`); on the reference's, `pushBindShaped` moves the label from the temporary that
parks it to the new binding (`takeLabel`, by `holderOf`), which needs the reference to hold the label
at one position (`Strict.SGood.uniq`, docs/31 D114, D117).

* `PBS.eq`: the reference's push of a binding holding a label, unfolded at a temporary holder.
* `rel_pushBind_borrow`: the relation after the push, where the borrow is the only live one.
* `letB_core`: the step.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

namespace PBS

theorem getLast_setAt_temp (s : SState) (f k : Nat) (g : SVal) {fr : SFrame} (hfr : s.env.getLast? = some fr) :
    ∃ fr', (s.setAt (.temp f k) g).env.getLast? = some fr' ∧ fr'.binds = fr.binds := by
  simp only [SState.setAt]
  rw [List.getLast?_eq_getElem?, List.length_modify, List.getElem?_modify]
  rw [List.getLast?_eq_getElem?] at hfr
  rw [hfr]
  split <;> exact ⟨_, rfl, rfl⟩

/-- **The reference's push of a binding holding the label `l`**, where `l`'s holder is the
temporary `r`: the holder is taken (`moved`, its shape cleared), the binding pushed, and the binding
made the holder. -/
theorem eq {s : SState} {b : SBinding} {l : Nat} {f k : Nat} {frs : SFrame} (hl : b.ty.label = some l)
    (hr : s.holderOf l = some (.temp f k)) (hlast : s.env.getLast? = some frs) :
    pushBindShaped s b = { ((({ s.setAt (.temp f k) (fun _ => .moved) with
        shape := fun p => if p = .temp f k then none else s.shape p } : SState)).pushBind b) with
      shape := fun q => if q = .bind s.topIdx frs.binds.length then some l else
        if q = .temp f k then none else s.shape q } := by
  unfold pushBindShaped; rw [hl]; dsimp only
  unfold SState.takeLabel; rw [hr]; dsimp only
  rw [SState.pushBind_getLast]
  obtain ⟨fr', h1, h2⟩ := getLast_setAt_temp s f k (fun _ => .moved) hlast
  have h1' : ({ s.setAt (.temp f k) (fun _ => .moved) with
      shape := fun p => if p = .temp f k then none else s.shape p } : SState).env.getLast? = some fr' := h1
  rw [h1']
  simp only [Option.map_some, SState.pushBind_topIdx, List.length_append, List.length_singleton,
    Nat.add_sub_cancel, h2]
  have ht : ({ s.setAt (.temp f k) (fun _ => .moved) with
      shape := fun p => if p = .temp f k then none else s.shape p } : SState).topIdx = s.topIdx := by
    show (s.setAt (.temp f k) (fun _ => .moved)).topIdx = s.topIdx
    exact SStateB.topIdx_setAt _ _ _
  rw [ht]
  rfl

end PBS

theorem sitesOf_pushTempE' (env : Env) (v : Value) (fr : Frame) (hfr : env[env.size - 1]? = some fr)
    (hne : 0 < env.size) (l : Nat) (hv : ∀ pos path, v.sitesOf l pos path = []) :
    Env.sitesOf (Env.pushTempE env v) l = Env.sitesOf env l := by
  simp only [Env.sitesOf]
  rw [allPos_pushTempE env v fr hfr hne, List.flatMap_append, List.flatMap_singleton,
    valAt_pushTempE_new env v fr hfr, hv, List.append_nil]
  apply flatMap_congr_mem
  intro q hq
  cases q with
  | bind f i => rw [valAt_pushTempE_bind]
  | temp f i =>
    rw [valAt_pushTempE_old env v fr hfr f i]
    intro e; cases e
    obtain ⟨fr', hf', hi⟩ := mem_allPos_temp env _ _ hq
    rw [hfr] at hf'; cases hf'
    exact absurd hi (Nat.lt_irrefl _)

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The relation after the `let` of a borrow** (the borrow in flight the only live one): the
checker binds it; the reference moves its label from the temporary that parked it to the binding. -/
theorem rel_pushBind_borrow {π : Nat → Nat} {st : MState} {s : SState} {T? : Option Value} {l : Nat} {w : Value}
    (hr : Rel K ρ φ π (st.withTempT (.borrow l w) T?) s) (huniq : s.Uniq) (hne : 0 < st.env.size)
    (hnb : ∀ q l', q ∈ allPos st.env → (valAt st.env q).holdsBorrow l' = false) (hw : w.Num)
    (h : Hint) (T : Value) (p : Bool) (d : DeclInfo) (R : TyS) (hR : (Value.tyS K.dm K.M K.Γ ρ T).m = R.m)
    (hRl : R.label = some (π l)) (hheld : s.heldTy (π l) = R.m) (c : Sem)
    (hc : ∀ (φ' : Future) (hint : TyS), Value.mean K.dm K.M K.Γ ρ φ' hint w = c) :
    Rel K ρ φ π { st with env := Env.pushBindE st.env h (some T) (.borrow l w) p d }
      (pushBindShaped s { ty := R, val := fun _ => c, decl := d }) := by
  have hr' : Rel K ρ φ π (st.withTemp (.borrow l w)) s := Rel.of_kern (kern_withTemp st _ T?).symm hr
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  have hsk : (SM' K ρ st).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) :=
    (skel_pushTempE K ρ st (.borrow l w)).symm.trans hr'.skel
  obtain ⟨frs, hfrs, htop, hlen⟩ := skel_align K ρ st s hsk fr hfr
  have hlast : s.env.getLast? = some frs := by
    rw [List.getLast?_eq_getElem?]; simpa [SState.topIdx] using hfrs
  -- the checker's side before: no borrow but the one in flight
  have hEc : (st.withTemp (.borrow l w)).env = Env.pushTempE st.env (.borrow l w) := rfl
  have hntC : Env.shape (Env.pushTempE st.env (.borrow l w)) (.temp (st.env.size - 1) fr.temps.size) = some l := by
    simp only [Env.shape, valAt_pushTempE_new st.env _ fr hfr]
  have hshE : ∀ q, Env.shape st.env q = none := fun q => by
    rcases e : Env.shape st.env q with _ | l'
    · rfl
    · have hq : q ∈ allPos st.env := mem_allPos_of_shape e
      have : (valAt st.env q).holdsBorrow l' = true := by
        rw [shape_eq_shapeOf] at e
        generalize valAt st.env q = v at e
        cases v <;> simp [shapeOf] at e
        subst e; simp [Value.holdsBorrow]
      rw [hnb q l' hq] at this; cases this
  have hliveC : ∀ l', liveLoan (Env.pushTempE st.env (.borrow l w)) l' = true → l' = l := fun l' hl' => by
    unfold liveLoan findBorrow at hl'
    obtain ⟨q, hq, hb⟩ := List.find?_isSome.mp hl'
    rw [allPos_pushTempE _ _ fr hfr hne, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · have hq' : q ≠ .temp (st.env.size - 1) fr.temps.size := fun e => by
        subst e; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hq; rw [hfr] at hf'; cases hf'
        exact absurd hi (Nat.lt_irrefl _)
      have : valAt (Env.pushTempE st.env (.borrow l w)) q = valAt st.env q := by
        cases q with
        | bind f i => exact valAt_pushTempE_bind _ _ f i
        | temp f i => exact valAt_pushTempE_old _ _ fr hfr f i hq'
      rw [this, hnb q l' hq] at hb; cases hb
    · rw [valAt_pushTempE_new _ _ fr hfr] at hb
      simp only [Value.holdsBorrow, Bool.or_eq_true, beq_iff_eq, hw.holdsBorrow] at hb
      rcases hb with hb | hb
      · exact hb.symm
      · cases hb
  -- the reference's holder of `π l`: a temporary, the only position holding a label
  obtain ⟨j₀, hj₀, -⟩ := hr'.sim.2.2.2.1 (st.env.size - 1) fr.temps.size l hntC
  have hshS : ∀ q l', s.shape q = some l' → q = .temp (st.env.size - 1) j₀ ∧ l' = π l := fun q l' hq => by
    have hlv : s.Live l' := (SState.live_iff s l').mpr ⟨q, hr'.holders q l' hq, hq⟩
    obtain ⟨l₀, h₀, he⟩ := rel_live_ref K ρ φ _ s π hr' hlv
    obtain rfl := hliveC l₀ h₀
    subst he
    exact ⟨huniq q _ _ hq hj₀, rfl⟩
  have hhold : s.holderOf (π l) = some (.temp (st.env.size - 1) j₀) := by
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((SState.live_iff s _).mpr ⟨_, hr'.holders _ _ hj₀, hj₀⟩)
    rw [hr₀, (hshS r _ (SState.holderOf_spec hr₀).2).1]
  -- the reference's push, unfolded
  have hbl : ({ ty := R, val := fun _ => c, decl := d } : SBinding).ty.label = some (π l) := hRl
  rw [PBS.eq hbl hhold hlast]
  generalize hb : ({ ty := R, val := fun _ => c, decl := d } : SBinding) = b
  obtain ⟨t₃, ht₃⟩ : ∃ t : SState, t = { s.setAt (.temp (st.env.size - 1) j₀) (fun _ => .moved) with
      shape := fun p => if p = .temp (st.env.size - 1) j₀ then none else s.shape p } := ⟨_, rfl⟩
  rw [← ht₃]
  have ht3top : t₃.topIdx = s.topIdx := by rw [ht₃]; exact SStateB.topIdx_setAt _ _ _
  obtain ⟨frs₃, hfrs₃, hb₃⟩ : ∃ fr', t₃.env[t₃.topIdx]? = some fr' ∧ fr'.binds = frs.binds := by
    obtain ⟨fr', h1, h2⟩ := PBS.getLast_setAt_temp s (st.env.size - 1) j₀ (fun _ => .moved) hlast
    refine ⟨fr', ?_, h2⟩
    rw [ht₃]; rw [List.getLast?_eq_getElem?] at h1; simpa [SState.topIdx] using h1
  have hy : Pos.bind t₃.topIdx frs₃.binds.length = .bind (st.env.size - 1) fr.binds.size := by
    rw [ht3top, hb₃, htop, hlen]
  have hy' : Pos.bind s.topIdx frs.binds.length = .bind (st.env.size - 1) fr.binds.size := by rw [htop, hlen]
  have ht3pos : t₃.positions = s.positions := by rw [ht₃]; exact SState.positions_setAt _ _ _
  have ht3val : ∀ f i, t₃.valAt (.bind f i) = s.valAt (.bind f i) := fun f i => by
    rw [ht₃]
    exact SState.valAt_setAt_ne s (.temp (st.env.size - 1) j₀) (fun _ => .moved) (.bind f i) (fun e => by cases e)
  have ht3ty : ∀ q, t₃.tyAt q = s.tyAt q := fun q => by rw [ht₃]; exact tyAt_setAt _ _ _ q
  have ht3lent : t₃.lent = s.lent := by rw [ht₃]; rfl
  have ht3held : t₃.heldTy = s.heldTy := by rw [ht₃]; rfl
  have ht3mem : t₃.heldMem = s.heldMem := by rw [ht₃]; rfl
  have ht3nl : t₃.nextLoan = s.nextLoan := by rw [ht₃]; exact SState.nextLoan_setAt' _ _ _
  have hyC := hy'
  -- the reference's state after: its shape, positions, values, types
  have hX5 : ∀ q, (if q = .bind s.topIdx frs.binds.length then some (π l) else
      if q = .temp (st.env.size - 1) j₀ then none else s.shape q) =
      if q = .bind (st.env.size - 1) fr.binds.size then some (π l) else none := fun q => by
    rw [hy']
    split
    · rfl
    · split
      · rfl
      · rcases e : s.shape q with _ | l'
        · rfl
        · next h2 => exact absurd (hshS q l' e).1 h2
  have hXpos : ∀ q, q ∈ (t₃.pushBind b).positions ↔ q = .bind (st.env.size - 1) fr.binds.size ∨ q ∈ s.positions :=
    fun q => by
      obtain ⟨A, B, h1, h2⟩ := positions_pushBind' t₃ b frs₃ hfrs₃
      rw [h2, ← ht3pos, h1, hy]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
  have hXval : ∀ f i, (t₃.pushBind b).valAt (.bind f i) =
      if Pos.bind f i = .bind (st.env.size - 1) fr.binds.size then (fun _ => c) else s.valAt (.bind f i) := fun f i => by
    split
    · next he => rw [he, ← hy, valAt_pushBind_new t₃ b frs₃ hfrs₃, ← hb]
    · next he => rw [valAt_pushBind_ne t₃ b frs₃ hfrs₃ _ (by rw [hy]; exact he), ht3val]
  have hXty : (t₃.pushBind b).tyAt (.bind (st.env.size - 1) fr.binds.size) = R := by
    rw [← hy]; simp only [SState.tyAt, sbind_pushBind_new t₃ b frs₃ hfrs₃]; rw [← hb]
  -- the checker's state after
  have hshB : ∀ q, Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q =
      if q = .bind (st.env.size - 1) fr.binds.size then some l else none := fun q => by
    split
    · next he => rw [he, shape_eq_shapeOf, valAt_pushBindE_new st.env h _ _ p d fr hfr]; rfl
    · next he => rw [shape_pushBindE_ne st.env h _ _ p d fr hfr q he, hshE]
  have hBnew : Pos.bind (st.env.size - 1) fr.binds.size ∈ allPos (Env.pushBindE st.env h (some T) (.borrow l w) p d) := by
    obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE st.env h (some T) (.borrow l w) p d fr hfr hne
    rw [h2]; simp
  have hliveB : ∀ l', liveLoan (Env.pushBindE st.env h (some T) (.borrow l w) p d) l' = true → l' = l := fun l' hl' => by
    unfold liveLoan findBorrow at hl'
    obtain ⟨q, hq, hb'⟩ := List.find?_isSome.mp hl'
    by_cases he : q = .bind (st.env.size - 1) fr.binds.size
    · subst he
      rw [valAt_pushBindE_new st.env h _ _ p d fr hfr] at hb'
      simp only [Value.holdsBorrow, Bool.or_eq_true, beq_iff_eq, hw.holdsBorrow] at hb'
      rcases hb' with hb' | hb'
      · exact hb'.symm
      · cases hb'
    · have hq' : q ∈ allPos st.env := by
        obtain ⟨A, B, h1, h2⟩ := allPos_pushBindE st.env h (some T) (.borrow l w) p d fr hfr hne
        rw [h2, List.mem_append, List.mem_cons] at hq
        rw [h1, List.mem_append]
        rcases hq with hq | hq | hq
        · exact .inl hq
        · exact absurd hq he
        · exact .inr hq
      rw [valAt_pushBindE_ne st.env h _ _ p d fr hfr q he, hnb q l' hq'] at hb'; cases hb'
  have hliveCl : liveLoan (Env.pushTempE st.env (.borrow l w)) l = true := by
    unfold liveLoan findBorrow
    refine List.find?_isSome.mpr ⟨.temp (st.env.size - 1) fr.temps.size, ?_, ?_⟩
    · rw [allPos_pushTempE _ _ fr hfr hne]; simp
    · rw [valAt_pushTempE_new _ _ fr hfr]; simp [Value.holdsBorrow]
  have hsv : ∀ pos path, (Value.borrow l w).sitesOf l pos path = [] := fun pos path => hw.sitesOf l pos _
  -- liveness and the holders' types, on both sides
  have hliveS : ∀ l', s.Live l' ↔ l' = π l := fun l' => by
    rw [SState.live_iff]
    constructor
    · rintro ⟨q, -, hq⟩; exact (hshS q l' hq).2
    · rintro rfl; exact ⟨_, hr'.holders _ _ hj₀, hj₀⟩
  obtain ⟨S5, hS5⟩ : ∃ S5 : Pos → Option Nat, S5 = fun q => if q = .bind s.topIdx frs.binds.length then some (π l) else if q = .temp (st.env.size - 1) j₀ then none else s.shape q := ⟨_, rfl⟩
  rw [← hS5]
  have hshX : ∀ q, ({ t₃.pushBind b with shape := S5 } : SState).shape q =
      if q = .bind (st.env.size - 1) fr.binds.size then some (π l) else none := fun q => by
    show S5 q = _; rw [hS5]; exact hX5 q
  have hliveX : ∀ l', ({ t₃.pushBind b with shape := S5 } : SState).Live l' ↔ l' = π l := fun l' => by
    rw [SState.live_iff]
    constructor
    · rintro ⟨q, -, hq⟩; rw [hshX] at hq; split at hq <;> cases hq; rfl
    · rintro rfl; exact ⟨_, (hXpos _).mpr (.inl rfl), by rw [hshX]; simp⟩
  have hhtX : holderTy ({ t₃.pushBind b with shape := S5 } : SState) (π l) = R.m := by
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((hliveX (π l)).mpr rfl)
    have hrs := (SState.holderOf_spec hr₀).2
    rw [hshX] at hrs
    have hry : r = .bind (st.env.size - 1) fr.binds.size := by split at hrs; assumption; cases hrs
    unfold holderTy; rw [hr₀, hry]
    show (({ t₃.pushBind b with shape := S5 } : SState).tyAt (Pos.bind (st.env.size - 1) fr.binds.size)).m = R.m
    exact congrArg TyS.m hXty
  have hhtS : holderTy s (π l) = R.m := by unfold holderTy; rw [hhold]; exact hheld
  have hF : ∀ ψ, (RelF φ ({ t₃.pushBind b with shape := S5 } : SState) ψ ∧ TypedLive K ({ t₃.pushBind b with shape := S5 } : SState) ψ) → RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l' hl' => hψ.1 l' (fun h' => hl' ((hliveS l').mpr ((hliveX l').mp h'))),
      fun l' hl' => by
        have := hψ.2 l' ((hliveX l').mpr ((hliveS l').mp hl'))
        obtain rfl := (hliveS l').mp hl'
        rw [hhtX] at this; rw [hhtS]; exact this⟩
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    have ht3sk : t₃.env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
      rw [ht₃]; exact skel_setAt _ _ _
    have hbs : bindSkel b = (R.m, d) := by rw [← hb]; rfl
    show _ = (t₃.pushBind b).env.map (fun fr => fr.binds.map bindSkel)
    rw [skel_pushBindE K ρ st h T _ p d fr hfr, sskel_pushBind, ht3sk, ← hsk, ht3top, htop, hbs, hR]
  · -- fresh
    intro l' hl' ho
    show π l' < t₃.nextLoan
    rw [ht3nl]
    obtain ⟨v', hv', ha⟩ := ho
    have hmem : v' ∈ Env.values (st.withTemp (.borrow l w)).env := by
      rw [hEc, values_pushTempE st.env _ fr hfr hne]
      rcases mem_values_pushBindE st.env h (some T) _ p d fr hfr hne hv' with rfl | hv''
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ hv''
    exact hr'.fresh l' hl' ⟨v', hmem, ha⟩
  · -- the bindings mean the same
    intro ψ hψ q hq
    cases q with
    | temp => exact absurd trivial hq
    | bind f i =>
      show Env.mean K.dm K.M K.Γ ρ _ (Env.pushBindE st.env h (some T) (.borrow l w) p d) (.bind f i) =
        (t₃.pushBind b).valAt (.bind f i) ψ
      rw [hXval]
      split
      · next he => rw [he, mean_pushBindE_new K.dm K.M K.Γ ρ st.env h _ p d fr hfr _ T]; exact hc _ _
      · next he =>
        rw [mean_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) _ p d fr hfr _ _ he]
        have := hr'.sim.1 ψ (hF ψ hψ) (.bind f i) hq
        rw [← this]
        exact (mean_pushTempE_other K.dm K.M K.Γ ρ st.env _ fr hfr _ _ (by intro e; cases e)).symm
  · intro q l' hq hsh
    have hsh' : Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = some l' := hsh
    rw [hshB] at hsh'
    split at hsh'
    · next he => cases hsh'; rw [hshX, if_pos he]
    · cases hsh'
  · intro q l' hq hsh
    rw [hshX] at hsh
    split at hsh
    · next he =>
      cases hsh
      refine ⟨l, ?_, rfl⟩
      show Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = some l
      rw [hshB, if_pos he]
    · cases hsh
  · intro f i l' hsh
    have hsh' : Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) (.temp f i) = some l' := hsh
    rw [hshB, if_neg (fun e => by cases e)] at hsh'; cases hsh'
  · intro f j l' hsh
    rw [hshX, if_neg (fun e => by cases e)] at hsh; cases hsh
  · intro l₁ l₂ h₁ h₂ _
    rw [hliveB l₁ h₁, hliveB l₂ h₂]
  · intro l' hl' x
    rw [hliveB l' hl']
    show x ∈ t₃.lent (π l) ↔ _
    rw [ht3lent, hr'.sites l hliveCl x, hEc, sitesOf_pushTempE' st.env _ fr hfr hne l hsv,
      sitesOf_pushBindE st.env h (some T) _ p d fr hfr hne l hsv]
  · intro q l' hsh
    rw [hshX] at hsh
    split at hsh
    · next he => exact (hXpos q).mpr (.inl he)
    · cases hsh
  · intro l' hl'
    obtain rfl := (hliveX l').mp hl'
    rw [hhtX]
    have := hr'.records (π l) ((hliveS _).mpr rfl)
    rw [hhtS] at this
    show (t₃.heldMem (π l)).whole ∧ t₃.heldMem (π l) ∈ₛ[K.dm.read] R.m
    rw [ht3mem]; exact this

end

theorem topReadings_withTempT (st : MState) (v : Value) (T? : Option Value) :
    DecideScope.topReadings (st.withTempT v T?) = DecideScope.topReadings st := by
  simp only [DecideScope.topReadings, MState.withTempT, Array.back?_eq_getElem?, Array.size_modify,
    Array.getElem?_modify]
  split <;> rcases st.env[st.env.size - 1]? <;> rfl

theorem asg_pushBind_borrow {K : RunCtx} {ρ : Assignment} {st : MState} {l : Nat} {w : Value} (hw : w.Num)
    (ha : Asg K ρ (st.withTempT (.borrow l w) (some (.tRef .tNat))).norm) (hne : 0 < st.env.size) (x : Hint) (p : Bool)
    (d : DeclInfo) : Asg K ρ ({ st with env := Env.pushBindE st.env x (some (.tRef .tNat)) (.borrow l w) p d } : MState).norm := by
  rcases hfr : st.env[st.env.size - 1]? with _ | fr
  · rw [Array.getElem?_eq_none_iff] at hfr; omega
  refine ha.of_refd rfl rfl rfl rfl rfl fun σ hσ => refd_mono_withTempT (.borrow l w) (some (.tRef .tNat)) σ ?_
  refine refd_sub (st := st) (st' := { st with env := Env.pushBindE st.env x (some (.tRef .tNat)) (.borrow l w) p d })
    rfl rfl rfl rfl ?_ ?_ ?_ σ hσ
  · intro w' hw' σ' hσ'
    rcases mem_values_pushBindE st.env x (some (.tRef .tNat)) (.borrow l w) p d fr hfr hne hw' with rfl | hw''
    · have hb : (Value.borrow l w).hasAbs σ' = w.hasAbs σ' := rfl
      rw [hb, hw.hasAbs] at hσ'; cases hσ'
    · exact ⟨w', hw'', hσ'⟩
  · intro f i b T σ' hb hT hσ'
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) fr.binds.size
    · cases e
      rw [bind_pushBindE_new st.env x (some (.tRef .tNat)) (.borrow l w) p d fr hfr] at hb
      cases hb; cases hT; cases hσ'
    · rw [bind_pushBindE_ne st.env x (some (.tRef .tNat)) (.borrow l w) p d fr hfr f i e] at hb
      exact .ty f i b T (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb) hT hσ'
  · intro f i b P ws j σ' hb hl hσ'
    by_cases e : Pos.bind f i = .bind (st.env.size - 1) fr.binds.size
    · cases e
      rw [bind_pushBindE_new st.env x (some (.tRef .tNat)) (.borrow l w) p d fr hfr] at hb
      cases hb; cases hl
    · rw [bind_pushBindE_ne st.env x (some (.tRef .tNat)) (.borrow l w) p d fr hfr f i e] at hb
      exact .lazyTy f i b P ws j (by show st.env.erase[f]?.bind _ = _; rw [lookup_erase]; exact hb) hl hσ'


section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **A typed `let h = u; w` at `evalCore`, for a right-hand side whose value is a borrow** of a
number at `&Nat`, the only borrow live after `u` (`hbor`), and a binding that holds no borrow and
has no site when it is dropped (the borrow ended in `w`). As `let_core`, with the push of a borrow
(`rel_pushBind_borrow`): the reference moves the label from the temporary that parks it to the
binding. -/
theorem letB_core (hL : LetInv) (hDN : DropNoopInv) (hI : InvSteps) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K)
    {n : Nat} {x : Hint} {u w : Term} {Plet Pu Pw : MState → Prop}
    (htail : ∀ st stB, Plet st → Pw stB →
      K.D.declOf (DecideScope.topReadings st) (.letIn x u w) = K.D.declOf (DecideScope.topReadings stB) w)
    (hu : EvalSim K ρ φ n u Pu (· = true)) (hPu : ∀ a b, Kern a b → Plet a → Pu b)
    (hw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ n w Pw (· = true))
    (hflu : ∀ st, Plet st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hflw : ∀ st, Pw st → K.D.flags (DecideScope.topReadings st) w = (false, false))
    (hdo : ∀ st, Plet st → K.D.declOf (DecideScope.topReadings st) u = .ref .other)
    (hbor : ∀ st st₀ st₁ bh v₀ T₀, Plet st → Kern st st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ →
      ∃ l w₀, v₀ = .borrow l w₀ ∧ w₀.Num ∧ T₀ = some (.tRef .tNat) ∧
        (∀ q l', q ∈ allPos st₁.env → (valAt st₁.env q).holdsBorrow l' = false) ∧ 0 < st₁.env.size ∧
        DecideScope.topReadings st₁ = DecideScope.topReadings st ∧ Mode st₁)
    (hPw : ∀ (st st₀ st₁ : MState) (bh : Nat) (v₀ : Value) (p : Bool), Plet st → Kern st st₀ → Mode st₀ →
      st₀.tailDecl = none → DecTab K.D st₁ → Runs (Ochr.eval n true u none) st₀ bh (v₀, some (.tRef .tNat)) st₁ →
      Pw { st₁ with env := Env.pushBindE st₁.env x (some (.tRef .tNat)) v₀ p (K.D.declOf (DecideScope.topReadings st₁) u) })
    (hPwk : ∀ a b, Kern a b → Pw a → Pw b)
    (hwv : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), w.valsOk (Strict.ValsP { K with Δ := Δ' } ρ' φ))
    (hwa : ∀ m, w.absBelow m) (hwn : w.hasHolePrim = false)
    (hdrop : ∀ stB st₂ bh r T?, Pw stB → Mode stB →
      (stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w)) → DecTab K.D st₂ →
      Runs (Ochr.eval n true w none) stB bh (r, T?) st₂ →
      ∃ fr b, st₂.env[st₂.env.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ (b.val = .bot ∨ b.val.Num))
    (hwh : NoHint K ρ φ w) :
    CoreSim K ρ φ (n + 1) (.letIn x u w) Plet (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  obtain ⟨du, st₀, st₁, stB, st₂, st₃, v₀, r, T₀, p, bh₁, bh₂, bh₃, hk₀, hm₀, htn₀, htd₀, htdB, hru, hdu,
    hkB, hmeB, htnB, hrw, hrd, hk₃, -, hD₁, hD₂⟩ := hL n x u w hint st st' bh v T? K.D hm htn htd hD h
  obtain ⟨lb, wb, rfl, hwb, rfl, hnb₁, hne₁, hrd₁, hm₁⟩ := hbor st st₀ st₁ bh₁ v₀ T₀ hPst hk₀ hm₀ htd₀ hD₁ hru
  have hmB : Mode stB := hm₁.of_modeEq hmeB
  have hduo : du = .ref .other := hdu.symm.trans (hdo st hPst)
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hv.1
  have hvw : w.valsOk (Strict.ValsP K ρ φ) := hv.2
  -- the step for `u`
  have hOu := hu st₀ st₁ true none (.borrow lb wb) (some (.tRef .tNat)) s π (hPu st st₀ hk₀ hPst) rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hvu
    (fun σ hσ => by rw [← hk₀.absTy]; exact hab σ (by simp [Term.anyAtom, hσ])) (by simp [Term.hasHolePrim] at hnh; exact hnh.1)
    (by rw [scopeOf_rel hr]; exact hflu st hPst) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, hau, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  -- (I) at `u`: the reference state after it is good
  obtain ⟨hgu, hlabu, hlouu, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  -- the right-hand side's value: a borrow of a number, at `&Nat`, with the checker's label renamed
  obtain ⟨m, hmv⟩ := hwb.vmean
  have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hru2 : (Value.tyS ({ K with Δ := Δ₁ } : RunCtx).dm ({ K with Δ := Δ₁ } : RunCtx).M ({ K with Δ := Δ₁ } : RunCtx).Γ
      ρ₁ (.tRef .tNat)).m = ru.2.m := hau _ rfl
  have hrul : ru.2.label = some (π₁ lb) := by rw [hlu]; rfl
  obtain ⟨fr₁, hfr₁⟩ : ∃ fr₁, st₁.env[st₁.env.size - 1]? = some fr₁ :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  -- the push, on both sides
  have hsc₁ : scopeOf s₁ = DecideScope.topReadings st₁ := by rw [scopeOf_rel hr₁, topReadings_withTempT]
  let bB : SBinding := { ty := ru.2, val := fun _ => ru.1, decl := du }
  have hpb : pushBindShaped s₁ { ty := ru.2, val := fun _ => ru.1, decl := K.D.declOf (scopeOf s) u } =
      pushBindShaped s₁ bB := by
    rw [scopeOf_rel hr, hdu]
  have hrB : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stB (pushBindShaped s₁ bB) :=
    (rel_pushBind_borrow hr₁ hS₁.uniq hne₁ hnb₁ hwb x (.tRef .tNat) p du ru.2 hru2 hrul (hlabu (π₁ lb) hrul).1 ru.1
      (fun φ' hint' => by rw [hru1]; exact hmv _ _ _ _ _ _)).of_kern hkB
  have hpB : Pre { K with Δ := Δ₁ } ρ₁ stB :=
    ⟨hp₁.ctx.of_eq (by show stB.inds = st₁.inds; rw [← hkB.inds])
      (by show stB.globals = st₁.globals; rw [← hkB.globals]),
     by rw [← hkB.norm, hduo]; exact hI.bindBorrow K.D K.Γ st₁ x lb wb _ p hPL hwb hne₁ hp₁.inv,
     by rw [← hkB.norm]; exact asg_pushBind_borrow hwb hp₁.asg hne₁ x p du⟩
  have hs₁ne : s₁.env ≠ [] := by
    have hfr₁' : (st₁.withTempT (.borrow lb wb) (some (.tRef .tNat))).env[
        (st₁.withTempT (.borrow lb wb) (some (.tRef .tNat))).env.size - 1]? = some { fr₁ with
          temps := fr₁.temps.push (.borrow lb wb), tempTys := fr₁.tempTys.push (some (.tRef .tNat)) } := by
      simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr₁]; rfl
    obtain ⟨frs, hfrs, -, -⟩ := skel_align { K with Δ := Δ₁ } ρ₁ _ s₁ hr₁.skel _ hfr₁'
    intro e; rw [e] at hfrs; simp at hfrs
  have hSB : Strict.SGood K.dm K.Γ φ (pushBindShaped s₁ bB) :=
    Strict.sgood_pushBindShaped hS₁ bB rfl hgu hlabu hlouu hs₁ne
  -- the step for `w`, at the extended context
  have hPB : Pw stB := by
    have := hPw st st₀ st₁ bh₁ (.borrow lb wb) p hPst hk₀ hm₀ htd₀ hD₁ hru
    rw [hrd₁, hdu] at this; exact hPwk _ _ hkB this
  have htdB' : stB.tailDecl = none ∨ stB.tailDecl = some (K.D.declOf (DecideScope.topReadings stB) w) := by
    exact .inr (by rw [htdB, hcd, htail st stB hPst hPB])
  have hOw := hw Δ₁ ρ₁ stB st₂ true none r T? (pushBindShaped s₁ bB) π₁ hPB rfl hmB htdB' hpB hrB hSB (hwv Δ₁ ρ₁)
    (fun σ hσ => hwa _ σ hσ) hwn (by rw [scopeOf_rel hrB]; exact hflw stB hPB) (fun e => by cases e) hD₂ bh₂ hrw
  rw [htnB] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩ := hOw
  -- the drop: the binding `let` pushed is now `⊥` or a number, with no loan, borrow or site
  obtain ⟨fr₂, bx, hfr₂, hbx, hbxv⟩ := hdrop stB st₂ bh₂ r T? hPB hmB htdB' hD₂ hrw
  have hnl : bx.val.loans = [] := by
    rcases hbxv with e | e
    · rw [e]; simp [Value.loans]
    · exact e.loans
  have hnb : ∀ l, bx.val.holdsBorrow l = false := fun l => by
    rcases hbxv with e | e
    · rw [e]; rfl
    · exact e.holdsBorrow l
  have hnbor : ∀ l w, bx.val ≠ .borrow l w := fun l w => by
    rcases hbxv with e | e
    · rw [e]; intro e'; cases e'
    · exact e.not_borrow l w
  have hns : ∀ l pos, bx.val.sitesOf l pos [] = [] := fun l pos => by
    rcases hbxv with e | e
    · rw [e]; simp [Value.sitesOf]
    · exact e.sitesOf l pos []
  let frW : Frame := { fr₂ with temps := fr₂.temps.push r, tempTys := fr₂.tempTys.push T? }
  have hfrW : (st₂.withTempT r T?).env[(st₂.withTempT r T?).env.size - 1]? = some frW := by
    simp only [MState.withTempT, Array.size_modify, Array.getElem?_modify, if_true, hfr₂]; rfl
  have hbW : frW.binds.back? = some bx := hbx
  have hn₂ : 0 < frW.binds.size := by
    have := hbW; rw [Array.back?_eq_getElem?] at this
    rcases Nat.eq_zero_or_pos frW.binds.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at this; cases this
    · exact h0
  have hne₂ : 0 < st₂.env.size := by
    rcases Nat.eq_zero_or_pos st₂.env.size with h0 | h0
    · rw [Array.getElem?_eq_none (by omega)] at hfr₂; cases hfr₂
    · exact h0
  have h₃ := hDN n (st₂.withTempT r T?) st₃ bh₃ frW bx hfrW hbW hnl hnbor hnb hrd
  obtain rfl : v = r := popped_eq hne₂ h₃ hk₃
  have hk' := h₃.trans hk₃
  -- the reference's drop ends nothing: it holds nothing there and nothing is lent there
  obtain ⟨frs, hlast, hsh, hpos, hbv⟩ := rel_top_shape_none hr₂ frW bx hfrW hbW hnb
  have hll : letLenders s₂ = s₂ := letLenders_noop frs hlast (by
    rw [hpos]; exact rel_noSites_at hr₂ (fun l => by rw [hbv]; exact hns l _))
  -- the reference's `let`
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w (pushBindShaped s₁ bB) = some (rw', s₂) := by
    rw [← wcong hwa Δ₁ ρ₁]; exact hxw
  have hxl : runT K ρ φ st.curTail (hintM K ρ hint) (.letIn x u w) s = some (rw', s₂.dropLast) := by
    rw [runT_letIn _ _ x u w s hfl, hxu']
    have hllok : LetLendersOk K φ s₂ := by
      unfold LetLendersOk; rw [hlast]
      exact accessOk_noSites (by rw [hpos]; exact rel_noSites_at hr₂ (fun l => by rw [hbv]; exact hns l _))
    simp only [bind, Option.bind]
    rw [hpb, hwh.tail, hxw']
    simp only [hlast, hsh, hll, if_pos hllok]
  -- the conclusion
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkB.absTy hkB.nextLoan).trans (he₂.congr rfl rfl hk'.absTy hk'.nextLoan)
  refine ⟨ρ₂, Δ₂, π₂, rw', s₂.dropLast, hext, hxl, hmw, haw, hlw, ?_, ?_⟩
  · refine Pre.of_kern hk' ⟨hp₂.ctx.of_eq rfl rfl, ?_, asg_popBind hp₂.asg frW hfrW hn₂⟩
    exact hI.popBind K.D K.Γ (st₂.withTempT v T?) frW bx hPL hfrW hbW hbxv hp₂.inv
  · exact (rel_popBind_noSites hr₂ frW bx hfrW hbW (fun l => hns l _) hnb).of_kern hk'

end

/-! ## `*y := u`: a write through a borrow variable -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem sitesOf_setAtE_noSites {env : Env} {pos : Pos} {v' : Value} (hp : pos ∈ allPos env)
    (hw : ∀ l pos' path, (valAt env pos).sitesOf l pos' path = []) (hv' : ∀ l pos' path, v'.sitesOf l pos' path = [])
    (l : Nat) : Env.sitesOf (Env.setAtE env pos v') l = Env.sitesOf env l := by
  unfold Env.sitesOf
  rw [allPos_setAtE]
  congr 1; funext q
  by_cases hq : q = pos
  · subst hq; rw [valAt_setAtE_self v' hp, hv', hw]
  · rw [valAt_setAtE_other env pos q v' hq]

/-- **The write of a number through a borrow variable keeps the relation** (`*y := v'`, `y` holding
`borrow_l w`, `w` and `v'` numbers): the holder keeps its label, its content changes; the checker's
new value and the reference's new meaning agree at every future the relation compares at. -/
theorem rel_setBorrowNum {π : Nat → Nat} {st : MState} {s : SState} {f i : Nat} {lb : Nat} {w v' : Value} {g : SVal}
    {k : Nat} (hs : Rel K ρ φ π st s) (hp : Pos.bind f i ∈ allPos st.env) (hsp : Pos.bind f i ∈ s.positions)
    (hw0 : valAt st.env (.bind f i) = .borrow lb w) (hw : w.Num) (hv' : v'.Num)
    (hk : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint v' = .el0 Nat k)
    (hg : ∀ ψ, RelF φ s ψ ∧ TypedLive K s ψ → g ψ = .el0 Nat k) :
    Rel K ρ φ π { st with env := Env.setAtE st.env (.bind f i) (.borrow lb v') } (s.setAt (.bind f i) g) := by
  have hhold : ∀ l', (Value.borrow lb v').holdsBorrow l' = (valAt st.env (Pos.bind f i)).holdsBorrow l' := fun l' => by
    rw [hw0]; simp [Value.holdsBorrow, hv'.holdsBorrow, hw.holdsBorrow]
  have hlive : ∀ l', liveLoan (Env.setAtE st.env (Pos.bind f i) (.borrow lb v')) l' = liveLoan st.env l' :=
    liveLoan_setAtE hp hhold
  have hshape : ∀ q, Env.shape (Env.setAtE st.env (Pos.bind f i) (.borrow lb v')) q = Env.shape st.env q := by
    intro q
    by_cases hq : q = Pos.bind f i
    · rw [hq, shape_eq_shapeOf, shape_eq_shapeOf, valAt_setAtE_self _ hp, hw0]; rfl
    · exact shape_setAtE_other st.env (Pos.bind f i) q _ hq
  have hF : ∀ ψ, (RelF φ (s.setAt (Pos.bind f i) g) ψ ∧ TypedLive K (s.setAt (Pos.bind f i) g) ψ) →
      RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l hl => hψ.1 l (fun h => hl ((SState.live_setAt _ _ _ l).mp h)),
      fun l hl => by
        have := hψ.2 l ((SState.live_setAt _ _ _ l).mpr hl)
        rwa [holderTy_setAt] at this⟩
  have hp' : Pos.bind f i ∈ allPos (Env.setAtE st.env (Pos.bind f i) (.borrow lb v')) := by rw [allPos_setAtE]; exact hp
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [skel_setAtE K ρ st f i (.borrow lb v'), hs.skel]
    exact (skel_setAt s _ _).symm
  · intro l' hl ho
    rw [SState.nextLoan_setAt']
    refine hs.fresh l' hl ?_
    obtain ⟨w', hw', ha⟩ := ho
    rcases mem_values_setAtE hw' with rfl | hw''
    · -- the new value's atoms: the borrow `l`, which the old value at `y` held, and a number's
      have hal : lb = l' := by
        simp only [Value.anyAtom, Bool.or_eq_true, borrow_beq_loan, Bool.false_or] at ha
        rcases ha with ha | ha
        · exact beq_iff_eq.mp ha
        · rw [hv'.inert.anyAtom _ (by rfl) (by rfl) (by rfl) (fun _ => by rfl)] at ha; cases ha
      subst hal
      refine ⟨_, List.mem_map_of_mem hp, ?_⟩
      rw [hw0]; simp [Value.anyAtom]
    · exact ⟨w', hw'', ha⟩
  · intro ψ hψ p hpt
    have hψ0 := hF ψ hψ
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) (.borrow lb v')) p = _
    by_cases hpp : p = Pos.bind f i
    · rw [hpp, valAt_setAt_self _ _ _ hsp, hg ψ hψ0, mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ hp',
        valAt_setAtE_self _ hp]
      exact hk _ _ _ _ _ _
    · rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) p (.borrow lb v') _ hpp, SState.valAt_setAt_ne _ _ _ _ (Ne.symm hpp)]
      exact hs.sim.1 ψ hψ0 p hpt
  · intro p l hpt hsh
    have hsh' : Env.shape st.env p = some l := by rw [← hshape p]; exact hsh
    rw [SState.shape_setAt]
    exact hs.sim.2.1 p l hpt hsh'
  · intro p l' hpt hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨l, h1, h2⟩ := hs.sim.2.2.1 p l' hpt hsh
    exact ⟨l, by show Env.shape _ p = _; rw [hshape p]; exact h1, h2⟩
  · intro f' i' l hsh
    have hsh' : Env.shape st.env (.temp f' i') = some l := by rw [← hshape]; exact hsh
    obtain ⟨j, hj, hval⟩ := hs.sim.2.2.2.1 f' i' l hsh'
    refine ⟨j, by rw [SState.shape_setAt]; exact hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ (fun l => ψ (π l)) (Env.setAtE st.env (Pos.bind f i) (.borrow lb v')) (.temp f' i') = _
    rw [mean_setAtE_other K.dm K.M K.Γ ρ st.env (Pos.bind f i) _ (.borrow lb v') _ (by simp), SState.valAt_setAt_ne _ _ _ _ (by simp)]
    exact hval ψ (hF ψ hψ)
  · intro f' j l' hsh
    rw [SState.shape_setAt] at hsh
    obtain ⟨i', l, h1, h2⟩ := hs.sim.2.2.2.2 f' j l' hsh
    exact ⟨i', l, by show Env.shape _ _ = _; rw [hshape]; exact h1, h2⟩
  · intro l l' hl hl' he
    rw [hlive] at hl hl'
    exact hs.inj l l' hl hl' he
  · intro l hl x
    rw [hlive] at hl
    rw [SState.lent_setAt, hs.sites l hl x, sitesOf_setAtE_noSites (v' := .borrow lb v') hp
      (by rw [hw0]; exact fun l' pos path => hw.sitesOf l' pos _) (fun l' pos path => hv'.sitesOf l' pos _) l]
  · intro p l h
    rw [SState.shape_setAt'] at h
    rw [SState.positions_setAt]
    exact hs.holders p l h
  · intro l hl
    rw [holderTy_setAt]
    have hrec := hs.records l ((SState.live_setAt _ _ _ l).mp hl)
    rcases f with _ | f <;> exact hrec


end

/-- `y` a top-frame variable stored at `&Nat` holding a borrow of a number. -/
def DerefVar (i : Nat) (st : MState) : Prop :=
  ∃ f j b l w, ckVarPos st.env i = some (.bind f j) ∧ st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b ∧
    b.val = .borrow l w ∧ w.Num ∧ b.ty = some (.tRef .tNat)

theorem DerefVar.of_erase {i : Nat} {st st' : MState} (he : st.env.erase = st'.env.erase) (h : DerefVar i st) :
    DerefVar i st' := by
  obtain ⟨f, j, b, l, w, h1, h2, h3, h4, h5⟩ := h
  refine ⟨f, j, b, l, w, ?_, ?_, h3, h4, h5⟩
  · rw [← ckVarPos_erase, ← he, ckVarPos_erase]; exact h1
  · rw [← lookup_erase, ← he, lookup_erase]; exact h2

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **A typed write through a borrow variable, at `evalCore`** (`*y := u`, `y` stored at `&Nat`
holding `borrow_l w`, `w` and `u`'s value numbers). The strict run's tests pass: the access of `y`
at `[*]` ends nothing (nothing is lent inside `y`); the update through `*` is defined at every typed
future (`*` is transparent to `Sem.updAt`); the write is at `[*]` (`lentOk`); the holder keeps its
label (`rel_setBorrowNum`). -/
theorem assignDeref_core (hA : AssignDerefInv) (hI : InvSteps) (hPL : PlaceLocal K.D) (hc : Strict.FundCtx K)
    {n i : Nat} {u : Term}
    {P Pu : MState → Prop} (hu : EvalSim K ρ φ n u Pu) (hPu : ∀ a b, Kern a b → P a → Pu b)
    (hP : ∀ st, P st → DerefVar i st)
    (hdy : ∀ st, P st → ∀ f j b, ckVarPos st.env i = some (.bind f j) →
      st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.decl = .ref .other)
    (hflu : ∀ st, P st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hhint : ∀ (T : TyS) (s : SState), runT K ρ φ false T u s = runT K ρ φ false (.plain TyM.err) u s)
    (hnum : ∀ st₀ st₁ bh hint v₀ T₀, Pu st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u hint) st₀ bh (v₀, T₀) st₁ → v₀.Num ∧ Env.erase st₀.env = Env.erase st₁.env ∧
        ∀ T, T₀ = some T → (T == .tNat) = true)
    (hinv : ∀ sc, K.D.invalidated sc (.deref (.var i)) = []) :
    CoreSim K ρ φ (n + 1) (.assign (.deref (.var i)) u) P (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd _ hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  have htyped : ∀ f j b, ckVarPos st.env i = some (.bind f j) →
      st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b → b.ty = some (.tRef .tNat) := by
    obtain ⟨f0, j0, b0, -, -, hpos0, hb0, -, -, ht0⟩ := hP st hPst
    intro f j b hpos hb
    rw [hpos0, Option.some.injEq, Pos.bind.injEq] at hpos
    obtain ⟨rfl, rfl⟩ := hpos
    rw [hb0, Option.some.injEq] at hb
    subst hb; exact ht0
  obtain ⟨st₀, st₁, hu', v₀, T₀, bh₁, hk₀, hm₀, htn₀, htd₀, hru, hD₁, rfl, rfl, hpost⟩ :=
    hA n i u hint st st' bh v T? K.D hm htn htd htyped hD h
  have hPu₀ := hPu st st₀ hk₀ hPst
  obtain ⟨hv₀, he₀₁, hT₀⟩ := hnum st₀ st₁ bh₁ hu' v₀ T₀ hPu₀ hm₀ htd₀ hD₁ hru
  -- `y` at `u`'s end is as it was: `borrow_l w`, `w` a number, at `&Nat`
  obtain ⟨f, j, b, lb, w, hpos₁, hlk₁, hbw, hwn, htb'⟩ := (hP st hPst).of_erase (hk₀.env.trans he₀₁)
  obtain ⟨st₂, hq, hki, -, hpos₂, hlk₂, hk'⟩ := hpost f j b lb w hpos₁ hlk₁ hbw hwn
  replace hki := hki hT₀
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hv
  -- the step for `u`
  have hOu := hu st₀ st₁ true hu' v₀ T₀ s π hPu₀ trivial hm₀ (.inl htd₀) (hp.of_kern hk₀) (hr.of_kern hk₀) hS hvu
    (fun σ hσ => by rw [← hk₀.absTy]; exact hab σ (by simp [Term.anyAtom, hσ]))
    (by simpa [Term.hasHolePrim] using hnh)
    (by rw [scopeOf_rel hr]; exact hflu st hPst) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, hmu, -, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := by rw [← hhint]; exact hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  -- `u`'s value: a number, with no label
  obtain ⟨m, hmv⟩ := hv₀.vmean
  have hru1 : ru.1 = .el0 Nat m := by rw [← hmu, ← meanV_eq_mean]; exact hmv _ _ _ _ _ _
  have hrul : ru.2.label = none := by rw [hlu, num_heldLabel hv₀]; rfl
  -- after `u` and the quiet steps, `y` is as it was: `borrow_l w`, at `&Nat`
  have hr₂ : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ st₂ s₁ :=
    rel_of_withTempT_num hv₀ (hr₁.of_quiet (hq.withTempT v₀ T₀) hp₁.labels)
  obtain ⟨mw, hmw⟩ := hwn.vmean
  have hmx : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint b.val = .el0 Nat mw := by
    intro dm C Γ ρ φ hint; rw [hbw]; exact hmw _ _ _ _ _ _
  -- the reference's `y`: the same position, its content at `Nat`, lent nothing inside, meaning `w`
  have hvb₂ : valAt st₂.env (.bind f j) = b.val := by
    rw [valAt_bind_eq]; rcases hfr : st₂.env[f]? with _ | fr
    · rw [hfr] at hlk₂; cases hlk₂
    · rw [hfr] at hlk₂; simp only [Option.bind_some] at hlk₂; simp [hlk₂]
  have hposA : Pos.bind f j ∈ allPos st₂.env := by
    rcases hfr : st₂.env[f]? with _ | fr
    · rw [hfr] at hlk₂; cases hlk₂
    · rw [hfr] at hlk₂; exact bind_mem_allPos st₂.env f j fr b hfr hlk₂
  obtain ⟨hposS, htyS⟩ := rel_bind_ty hr₂ hlk₂
  have htyN : (s₁.tyAt (.bind f j)).m = TyM.nat := by
    rw [htyS]; simp only [Env.hintAt, hlk₂, htb']; rfl
  have hns : ∀ l, (valAt st₂.env (.bind f j)).sitesOf l (.bind f j) [] = [] := fun l => by
    rw [hvb₂, hbw]; exact hwn.sitesOf l _ _
  have hacc : ∀ hit, s₁.access (.bind f j) hit = s₁ := fun _ => access_noSites (rel_noSites_at hr₂ hns)
  have haok : ∀ hit, AccessOk K φ s₁ (.bind f j) hit := fun _ => accessOk_noSites (rel_noSites_at hr₂ hns)
  have hres : resolve s₁ (.deref (.var i)) = some (.bind f j, [.deref]) :=
    rel_resolve_ck { K with Δ := Δ₁ } ρ₁ φ st₂ s₁ π₁ (.deref (.var i)) _ hr₂ hpos₂
  have hx : ∀ ψ, RelF φ s₁ ψ ∧ TypedLive { K with Δ := Δ₁ } s₁ ψ → s₁.valAt (.bind f j) ψ = .el0 Nat mw := by
    intro ψ hψ; rw [← hr₂.sim.1 ψ hψ (.bind f j) (by simp [IsTemp])]; exact mean_numVar hlk₂ hmx _
  -- the write through `*`: `y`'s content becomes `u`'s value, at every future
  let g : SVal := fun φ' =>
    (Sem.updAt K.dm K.Γ (s₁.tyAt (.bind f j)) (fun _ => ru.1) [.deref] (s₁.valAt (.bind f j) φ')).getD .err
  have hgv : ∀ ψ, g ψ = .el0 Nat m := fun ψ => by
    show (Sem.updAt _ _ _ _ [.deref] _).getD _ = _; rw [← hru1]; rfl
  -- the reference's run of the write: every test passes
  have hco : contentOf K φ (.deref (.var i)) s₁ =
      some ((.el0 Nat mw, { s₁.tyAt (.bind f j) with label := none }, .bind f j, [.deref]), s₁) := by
    have hval : s₁.valAt (.bind f j) (s₁.typedFuture φ) = .el0 Nat mw :=
      hx _ ⟨relF_typedFuture φ s₁, hr₂.typedFuture_typed φ⟩
    unfold contentOf; rw [hres]; simp only; rw [hacc]
    simp [Sem.follow, Sem.step, hval]
  have hpt : placeTy K φ (.deref (.var i)) s₁ = .plain TyM.nat := by
    unfold placeTy; rw [hco]; show TyS.plain (s₁.tyAt (.bind f j)).m = _; rw [htyN]
  have htest : ∀ ψ, TypedFut K φ s₁ ψ →
      (Sem.updAt K.dm K.Γ (s₁.tyAt (.bind f j)) (fun _ => ru.1) [.deref] (s₁.valAt (.bind f j) ψ)).isSome :=
    fun _ _ => rfl
  have hAok : AssignOk K φ (.deref (.var i)) s₁ := by
    unfold AssignOk; rw [hres]; exact ⟨fun _ => haok _, fun h => by cases h⟩
  have hsc : setContent K φ (.bind f j) [.deref] ru.1 s₁ = some (⟨⟩, s₁.setAt (.bind f j) g) := by
    unfold setContent; rw [if_pos htest]
  have hasg : assignAt K φ (.deref (.var i)) ru.1 ru.2.label s₁ =
      some ((.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g) := by
    unfold assignAt; rw [hres]; simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false]
    rw [hacc, hsc, hrul]
  have hinvs : invalidate K φ (.deref (.var i)) (s₁.setAt (.bind f j) g) = s₁.setAt (.bind f j) g := by
    unfold invalidate; rw [hinv]; rfl
  have hinvok : InvalidateOk K φ (.deref (.var i)) (s₁.setAt (.bind f j) g) := by
    unfold InvalidateOk; rw [hinv]; trivial
  have hlent : lentOk K φ (.deref (.var i)) (s₁.setAt (.bind f j) g) := by
    unfold lentOk; rw [resolve_setAt, hres]
    exact .inr (.inl rfl)
  have hxa : runT K ρ φ st.curTail (hintM K ρ hint) (.assign (.deref (.var i)) u) s =
      some ((.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g) := by
    rw [runT_assign _ _ _ _ s hfl]
    simp only [hhint, hxu', bind, Option.bind]
    rw [hpt, if_pos ⟨by rw [hru1]; exact ⟨m, rfl⟩, fun l hl => by rw [hrul] at hl; cases hl⟩]
    unfold SM.guarded; rw [if_pos hAok, hasg]
    simp only [hinvs, if_pos (And.intro hinvok hlent)]
  -- the conclusion: `()` at `Unit`, the checker's state after related to the reference's
  have hX : Asg { K with Δ := Δ₁ } ρ₁ ({ st₂ with env := Env.setAtE st₂.env (.bind f j) (.borrow lb v₀) } : MState).norm := by
    have hA₂ : Asg { K with Δ := Δ₁ } ρ₁ (st₂.withTempT v₀ T₀).norm :=
      Asg.of_quiet (hq.withTempT v₀ T₀) hp₁.asg hp₁.inv.wf6
    refine hA₂.of_refd rfl rfl rfl rfl rfl fun σ hσ => refd_mono_withTempT v₀ T₀ σ ?_
    refine refd_sub (st := st₂) (st' := { st₂ with env := Env.setAtE st₂.env (.bind f j) (.borrow lb v₀) })
      rfl rfl rfl rfl ?_ ?_ ?_ σ hσ
    · intro w' hw' σ' hσ'
      rcases mem_values_setAtE hw' with rfl | hw''
      · have hb : (Value.borrow lb v₀).hasAbs σ' = v₀.hasAbs σ' := rfl
        rw [hb, hv₀.hasAbs] at hσ'; cases hσ'
      · exact ⟨w', hw'', hσ'⟩
    · intro f' i' b' T σ' hb' hT hσ'
      obtain ⟨b'', hb'', hty'', -⟩ := lookup_setAtE hb'
      exact .ty f' i' b'' T (by rw [show st₂.norm.env = st₂.env.erase from rfl, lookup_erase]; exact hb'')
        (by rw [hty'']; exact hT) hσ'
    · intro f' i' b' P ws j' σ' hb' hl hσ'
      obtain ⟨b'', hb'', -, hlz''⟩ := lookup_setAtE hb'
      exact .lazyTy f' i' b'' P ws j' (by rw [show st₂.norm.env = st₂.env.erase from rfl, lookup_erase]; exact hb'')
        (by rw [hlz'']; exact hl) hσ'
  refine ⟨ρ₁, Δ₁, π₁, (.el0 Unit (), .plain TyM.unit), s₁.setAt (.bind f j) g, ⟨?_, ?_, ?_, ?_⟩, hxa, rfl,
    fun T hT => by cases hT; rfl, rfl, ?_, ?_⟩
  · rw [hk₀.absTy, ← hk'.absTy]; exact Nat.le_trans he₁.abs hq.absSize
  · rw [hk₀.nextLoan, ← hk'.nextLoan]; exact Nat.le_trans he₁.lab hq.nextLoan
  · intro σ hσ; rw [hk₀.absTy] at hσ; exact he₁.agree σ hσ
  · intro l hl; rw [hk₀.nextLoan] at hl; exact he₁.ren l hl
  · refine ⟨hp₁.ctx.of_eq ?_ ?_, ?_, ?_⟩
    · show st'.inds = st₁.inds; rw [← hk'.inds, ← hq.inds]
    · show st'.globals = st₁.globals; rw [← hk'.globals, ← hq.globals]
    · have h₁ : Inv K.D K.Γ st₁.norm := hI.popInert K.D K.Γ st₁ v₀ T₀ (.inl hv₀) hp₁.inv
      have h₂ : Inv K.D K.Γ st'.norm := by
        rw [← hk'.norm]
        exact hI.writeDeref K.D K.Γ st₂ f j lb w v₀ hPL
          (fun b' hb' => hdy st hPst f j b'
            (by rw [← ckVarPos_erase, hk₀.env.trans (he₀₁.trans hq.env), ckVarPos_erase]; exact hpos₂)
            (by rw [← lookup_erase, hk₀.env.trans (he₀₁.trans hq.env), lookup_erase]; exact hb'))
          (by rw [hvb₂, hbw]) hwn hv₀ (hki K.D K.Γ h₁)
      exact hI.pushInert K.D K.Γ st' _ _ (.inr rfl) h₂
    · have : Asg { K with Δ := Δ₁ } ρ₁ st'.norm := by rw [← hk'.norm]; exact hX
      exact asg_withTempT_inert this Value.inert_unit _
  · have hR := rel_setBorrowNum hr₂ hposA hposS (by rw [hvb₂, hbw]) hwn hv₀ hmv (fun ψ _ => hgv ψ)
    exact rel_withTempT_inert (hR.of_kern hk') Value.inert_unit _

end

/-! ## `u; w`, for a first part whose value is `()` -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The sequence clause of the strict run, where the aligned table does not erase it. -/
theorem runT_seq (tl : Bool) (hint : TyS) (u w : Term) (s : SState)
    (hfl : K.D.flags (scopeOf s) (.seq u w) = (false, false)) :
    runT K ρ φ tl hint (.seq u w) s = (do
      let r ← runT K ρ φ false (.plain TyM.err) u
      SM.guardMod (DiscardOk K φ r.2) (discardEnd r.2)
      runT K ρ φ tl (tailHint tl hint) w) s := by
  rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl]; rfl

theorem asg_of_withTempT {st : MState} {v : Value} {T? : Option Value} (h : Asg K ρ (st.withTempT v T?).norm) :
    Asg K ρ st.norm :=
  h.of_refd rfl rfl rfl rfl rfl fun σ hσ => refd_mono_withTempT v T? σ hσ

/-- **A typed `u; w` at `evalCore`**, for a first part whose value is `()` (so its drop ends
nothing on either side): the step for `u`, then the step for `w` from the state after it, the
reference's discarded result holding no label. -/
theorem seq_core (hSq : SeqInv) (hI : InvSteps) (hc : Strict.FundCtx K) {n : Nat} {u w : Term}
    {Pseq Pu Pw : MState → Prop}
    (htail : ∀ st stW, Pseq st → Pw stW →
      K.D.declOf (DecideScope.topReadings st) (.seq u w) = K.D.declOf (DecideScope.topReadings stW) w)
    (hu : EvalSim K ρ φ n u Pu (· = true)) (hPu : ∀ a b, Kern a b → Pseq a → Pu b)
    (hw : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), EvalSim { K with Δ := Δ' } ρ' φ n w Pw (· = true))
    (hflu : ∀ st, Pseq st → K.D.flags (DecideScope.topReadings st) u = (false, false))
    (hflw : ∀ st, Pw st → K.D.flags (DecideScope.topReadings st) w = (false, false))
    (hunit : ∀ st₀ st₁ bh v₀ T₀, Pu st₀ → Mode st₀ → st₀.tailDecl = none → DecTab K.D st₁ →
      Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ → v₀ = .unit ∧ Mode st₁)
    (hPw : ∀ (st st₀ st₁ : MState) (bh : Nat) (v₀ : Value) (T₀ : Option Value), Pseq st → Kern st st₀ → Mode st₀ →
      st₀.tailDecl = none → DecTab K.D st₁ → Runs (Ochr.eval n true u none) st₀ bh (v₀, T₀) st₁ → Pw st₁)
    (hPwk : ∀ a b, Kern a b → Pw a → Pw b)
    (hwv : ∀ (Δ' : Nat → TyS) (ρ' : Assignment), w.valsOk (Strict.ValsP { K with Δ := Δ' } ρ' φ))
    (hwa : ∀ m, w.absBelow m) (hwn : w.hasHolePrim = false) (hwh : NoHint K ρ φ w) :
    CoreSim K ρ φ (n + 1) (.seq u w) Pseq (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd hcd hp hr hS hv hab hnh hfl _ hD bh h
  subst hty
  obtain ⟨st₀, st₁, stW, v₀, T₀, bh₁, bh₂, hk₀, hm₀, htn₀, htd₀, htdW, hru, hD₁, hdrop, htnW, hrw⟩ :=
    hSq n u w hint st st' bh v T? K.D hm htn htd hD h
  obtain ⟨rfl, hm₁⟩ := hunit st₀ st₁ bh₁ v₀ T₀ (hPu st st₀ hk₀ hPst) hm₀ htd₀ hD₁ hru
  have hmW : Mode stW := hm₁.of_modeEq (hdrop (fun _ => rfl) rfl).2
  have hvu : u.valsOk (Strict.ValsP K ρ φ) := hv.1
  -- the step for `u`
  have hOu := hu st₀ st₁ true none .unit T₀ s π (hPu st st₀ hk₀ hPst) rfl hm₀ (.inl htd₀) (hp.of_kern hk₀)
    (hr.of_kern hk₀) hS hvu
    (fun σ hσ => by rw [← hk₀.absTy]; exact hab σ (by simp [Term.anyAtom, hσ])) (by simp [Term.hasHolePrim] at hnh; exact hnh.1)
    (by rw [scopeOf_rel hr]; exact hflu st hPst) (fun e => by cases e) hD₁ bh₁ hru
  rw [htn₀] at hOu
  obtain ⟨ρ₁, Δ₁, π₁, ru, s₁, he₁, hxu, -, -, hlu, hp₁, hr₁⟩ := hOu
  have hxu' : runT K ρ φ false (.plain TyM.err) u s = some (ru, s₁) := hxu
  obtain ⟨-, -, -, hS₁⟩ := Strict.fund_all hc u hvu false (.plain TyM.err) s s₁ ru hS hxu'
  have hrul : ru.2.label = none := by rw [hlu]; rfl
  -- the drop of `()`: nothing on either side
  have hkW : Kern st₁ stW := (hdrop (fun _ => rfl) rfl).1
  have hrW : Rel { K with Δ := Δ₁ } ρ₁ φ π₁ stW s₁ := (rel_of_withTempT_inert Value.inert_unit hr₁).of_kern hkW
  have hpW : Pre { K with Δ := Δ₁ } ρ₁ stW :=
    ⟨hp₁.ctx.of_eq (by show stW.inds = st₁.inds; rw [← hkW.inds]) (by show stW.globals = st₁.globals; rw [← hkW.globals]),
     by rw [← hkW.norm]; exact hI.popInert K.D K.Γ st₁ .unit T₀ (.inr rfl) hp₁.inv,
     by rw [← hkW.norm]; exact asg_of_withTempT hp₁.asg⟩
  -- the step for `w`
  have hPW : Pw stW := hPwk _ _ hkW (hPw st st₀ st₁ bh₁ .unit T₀ hPst hk₀ hm₀ htd₀ hD₁ hru)
  have htdW' : stW.tailDecl = none ∨ stW.tailDecl = some (K.D.declOf (DecideScope.topReadings stW) w) := by
    rcases htdW with e | e
    · exact .inl e
    · exact .inr (by rw [e, hcd, htail st stW hPst hPW])
  have hOw := hw Δ₁ ρ₁ stW st' true none v T? s₁ π₁ hPW rfl hmW htdW' hpW hrW hS₁ (hwv Δ₁ ρ₁)
    (fun σ hσ => hwa _ σ hσ) hwn (by rw [scopeOf_rel hrW]; exact hflw stW hPW) (fun e => by cases e) hD bh₂ hrw
  rw [htnW] at hOw
  obtain ⟨ρ₂, Δ₂, π₂, rw', s₂, he₂, hxw, hmw, haw, hlw, hp₂, hr₂⟩ := hOw
  have hxw' : runT K ρ φ st.curTail (.plain TyM.err) w s₁ = some (rw', s₂) := by
    rw [← wcong hwa Δ₁ ρ₁]; exact hxw
  have hxs : runT K ρ φ st.curTail (hintM K ρ hint) (.seq u w) s = some (rw', s₂) := by
    rw [runT_seq _ _ u w s hfl]
    simp only [bind, Option.bind]
    rw [hxu']
    simp only
    rw [SM.guardMod_of (by unfold DiscardOk; rw [hrul]; trivial)]
    simp only
    have hd : discardEnd ru.2 s₁ = s₁ := by unfold discardEnd; rw [hrul]
    rw [hd, hwh.tail]; exact hxw'
  have hext : Ext K ρ π st st' ρ₂ Δ₂ π₂ :=
    (he₁.congr hk₀.absTy hk₀.nextLoan hkW.absTy hkW.nextLoan).trans he₂
  exact ⟨ρ₂, Δ₂, π₂, rw', s₂, hext, hxs, hmw, haw, hlw, hp₂, hr₂⟩

end

end Ochr.Meaning.Steps.Form
