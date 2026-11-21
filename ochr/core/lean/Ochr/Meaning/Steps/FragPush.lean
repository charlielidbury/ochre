import Ochr.Meaning.Steps.Frag

/-!
# The `let` of a borrow with other borrows live (lead11)

`ColumnLetB.rel_pushBind_borrow` moved the borrow in flight into a pushed binding where it was the
only live borrow (`hnb`). Here the same with any other borrows live: the label in flight is held at
one temporary on the reference side (`SState.Uniq`), and every other holder stays where it was.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

theorem liveLoan_pushTempE_bor {env : Env} {fr : Frame} (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size)
    {l : Nat} {w : Value} (hw : w.Num) (l' : Nat) :
    liveLoan (Env.pushTempE env (.borrow l w)) l' = true ↔ l' = l ∨ liveLoan env l' = true := by
  by_cases e : l' = l
  · subst e; simp only [true_or, iff_true]
    unfold liveLoan findBorrow
    refine List.find?_isSome.mpr ⟨.temp (env.size - 1) fr.temps.size, ?_, ?_⟩
    · rw [allPos_pushTempE _ _ fr hfr hne]; simp
    · rw [valAt_pushTempE_new _ _ fr hfr]; simp [Value.holdsBorrow]
  · have hb : (Value.borrow l w).holdsBorrow l' = false := by
      simp only [Value.holdsBorrow, hw.holdsBorrow, Bool.or_false, beq_eq_false_iff_ne]; exact fun h => e h.symm
    unfold liveLoan; rw [findBorrow_pushTempE env _ fr hfr hne l' hb]; simp [e]

theorem liveLoan_pushBindE_bor {env : Env} {fr : Frame} (hfr : env[env.size - 1]? = some fr) (hne : 0 < env.size)
    (h : Hint) (ty : Option Value) (p : Bool) (d : DeclInfo) {l : Nat} {w : Value} (hw : w.Num) (l' : Nat) :
    liveLoan (Env.pushBindE env h ty (.borrow l w) p d) l' = true ↔ l' = l ∨ liveLoan env l' = true := by
  by_cases e : l' = l
  · subst e; simp only [true_or, iff_true]
    unfold liveLoan findBorrow
    obtain ⟨A, B, -, h2⟩ := allPos_pushBindE env h ty (.borrow l' w) p d fr hfr hne
    refine List.find?_isSome.mpr ⟨.bind (env.size - 1) fr.binds.size, by rw [h2]; simp, ?_⟩
    rw [valAt_pushBindE_new env h ty _ p d fr hfr]; simp [Value.holdsBorrow]
  · have hb : (Value.borrow l w).holdsBorrow l' = false := by
      simp only [Value.holdsBorrow, hw.holdsBorrow, Bool.or_false, beq_eq_false_iff_ne]; exact fun h => e h.symm
    rw [liveLoan_pushBindE env h ty _ p d fr hfr hne l' hb]; simp [e]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The value in flight, a borrow, moved into a pushed binding, other borrows live** (the general
form of `ColumnLetB.rel_pushBind_borrow`): no position of the checker's environment holds `l` (`hnl`);
on the reference side `π l` is held at one temporary (`SState.Uniq`), which the push clears, and every
other label keeps its holder. -/
theorem rel_pushBind_borrowG {π : Nat → Nat} {st : MState} {s : SState} {T? : Option Value} {l : Nat} {w : Value}
    (hr : Rel K ρ φ π (st.withTempT (.borrow l w) T?) s) (huniq : s.Uniq) (hne : 0 < st.env.size)
    (hnl : ∀ q, Env.shape st.env q ≠ some l) (hw : w.Num)
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
  have hEc : (st.withTemp (.borrow l w)).env = Env.pushTempE st.env (.borrow l w) := rfl
  have hntC : Env.shape (Env.pushTempE st.env (.borrow l w)) (.temp (st.env.size - 1) fr.temps.size) = some l := by
    simp only [Env.shape, valAt_pushTempE_new st.env _ fr hfr]
  have hliveCl : liveLoan (Env.pushTempE st.env (.borrow l w)) l = true :=
    (liveLoan_pushTempE_bor hfr hne hw l).mpr (.inl rfl)
  -- the checker's positions other than the new temporary keep their values
  have hvalC : ∀ q, q ∈ allPos st.env → valAt (Env.pushTempE st.env (.borrow l w)) q = valAt st.env q := by
    intro q hq
    cases q with
    | bind f i => exact valAt_pushTempE_bind _ _ f i
    | temp f i =>
      refine valAt_pushTempE_old _ _ fr hfr f i (fun e => ?_)
      obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ (e ▸ hq)
      rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
  -- the reference's holder of `π l`: a temporary, its only holder
  obtain ⟨j₀, hj₀, -⟩ := hr'.sim.2.2.2.1 (st.env.size - 1) fr.temps.size l hntC
  have hshS : ∀ q, s.shape q = some (π l) → q = .temp (st.env.size - 1) j₀ := fun q hq => huniq q _ _ hq hj₀
  have hhold : s.holderOf (π l) = some (.temp (st.env.size - 1) j₀) := by
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((SState.live_iff s _).mpr ⟨_, hr'.holders _ _ hj₀, hj₀⟩)
    rw [hr₀, hshS r (SState.holderOf_spec hr₀).2]
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
  have ht3val : ∀ q, q ≠ .temp (st.env.size - 1) j₀ → t₃.valAt q = s.valAt q := fun q hq => by
    rw [ht₃]
    exact SState.valAt_setAt_ne s (.temp (st.env.size - 1) j₀) (fun _ => .moved) q (fun e => hq e.symm)
  have ht3ty : ∀ q, t₃.tyAt q = s.tyAt q := fun q => by rw [ht₃]; exact tyAt_setAt _ _ _ q
  have ht3lent : t₃.lent = s.lent := by rw [ht₃]; rfl
  have ht3held : t₃.heldTy = s.heldTy := by rw [ht₃]; rfl
  have ht3mem : t₃.heldMem = s.heldMem := by rw [ht₃]; rfl
  have ht3nl : t₃.nextLoan = s.nextLoan := by rw [ht₃]; exact SState.nextLoan_setAt' _ _ _
  have hnewS : Pos.bind (st.env.size - 1) fr.binds.size ∉ s.positions := by
    rw [← hy', SState.mem_positions]; simp [SState.lookup, hfrs]
  obtain ⟨S5, hS5⟩ : ∃ S5 : Pos → Option Nat, S5 = fun q => if q = .bind s.topIdx frs.binds.length then some (π l)
      else if q = .temp (st.env.size - 1) j₀ then none else s.shape q := ⟨_, rfl⟩
  rw [← hS5]
  have hshX : ∀ q, ({ t₃.pushBind b with shape := S5 } : SState).shape q =
      if q = .bind (st.env.size - 1) fr.binds.size then some (π l)
      else if q = .temp (st.env.size - 1) j₀ then none else s.shape q := fun q => by
    show S5 q = _; rw [hS5, hy']
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
  have hXvalB : ∀ f i, (t₃.pushBind b).valAt (.bind f i) =
      if Pos.bind f i = .bind (st.env.size - 1) fr.binds.size then (fun _ => c) else s.valAt (.bind f i) := fun f i => by
    split
    · next he => rw [he, ← hy, valAt_pushBind_new t₃ b frs₃ hfrs₃, ← hb]
    · next he => rw [valAt_pushBind_ne t₃ b frs₃ hfrs₃ _ (by rw [hy]; exact he), ht3val _ (fun e => by cases e)]
  have hXvalT : ∀ f i, Pos.temp f i ≠ .temp (st.env.size - 1) j₀ →
      (t₃.pushBind b).valAt (.temp f i) = s.valAt (.temp f i) := fun f i hne' => by
    rw [valAt_pushBind_ne t₃ b frs₃ hfrs₃ _ (fun e => by cases e), ht3val _ hne']
  have hXty : (t₃.pushBind b).tyAt (.bind (st.env.size - 1) fr.binds.size) = R := by
    rw [← hy]; simp only [SState.tyAt, sbind_pushBind_new t₃ b frs₃ hfrs₃]; rw [← hb]
  have hXtyO : ∀ q, q ≠ .bind (st.env.size - 1) fr.binds.size → (t₃.pushBind b).tyAt q = s.tyAt q := fun q hq => by
    rw [tyAt_pushBind_ne t₃ b frs₃ hfrs₃ q (by rw [hy]; exact hq), ht3ty]
  -- liveness and the holders' types, on both sides
  have hliveX : ∀ L, ({ t₃.pushBind b with shape := S5 } : SState).Live L ↔ s.Live L := fun L => by
    rw [SState.live_iff, SState.live_iff]
    constructor
    · rintro ⟨q, -, hsq⟩
      rw [hshX] at hsq
      split at hsq
      · cases hsq; exact ⟨_, hr'.holders _ _ hj₀, hj₀⟩
      · split at hsq
        · cases hsq
        · exact ⟨q, hr'.holders q L hsq, hsq⟩
    · rintro ⟨q, hq, hsq⟩
      by_cases hL : L = π l
      · subst hL; exact ⟨_, (hXpos _).mpr (.inl rfl), by rw [hshX]; simp⟩
      · have hq1 : q ≠ .bind (st.env.size - 1) fr.binds.size := fun e => hnewS (e ▸ hq)
        have hq2 : q ≠ .temp (st.env.size - 1) j₀ := fun e => by
          rw [e, hj₀] at hsq; exact hL (Option.some.inj hsq).symm
        exact ⟨q, (hXpos q).mpr (.inr hq), by rw [hshX, if_neg hq1, if_neg hq2]; exact hsq⟩
  have hholdX : ∀ L, s.Live L → holderTy ({ t₃.pushBind b with shape := S5 } : SState) L = holderTy s L := by
    intro L hL
    obtain ⟨r, hr₀⟩ := SState.holderOf_of_live ((hliveX L).mpr hL)
    have hrs := (SState.holderOf_spec hr₀).2
    rw [hshX] at hrs
    by_cases e : L = π l
    · subst e
      have hry : r = .bind (st.env.size - 1) fr.binds.size := by
        split at hrs
        · assumption
        · split at hrs
          · cases hrs
          · next h2 => exact absurd (hshS r hrs) h2
      unfold holderTy; rw [hr₀, hry, hhold]
      show (({ t₃.pushBind b with shape := S5 } : SState).tyAt (Pos.bind (st.env.size - 1) fr.binds.size)).m = s.heldTy (π l)
      rw [hheld]; exact congrArg TyS.m hXty
    · obtain ⟨r', hr₀'⟩ := SState.holderOf_of_live hL
      have hrs' := (SState.holderOf_spec hr₀').2
      have hr1 : r ≠ .bind (st.env.size - 1) fr.binds.size := fun e' => by
        rw [if_pos e'] at hrs; exact e (Option.some.inj hrs).symm
      rw [if_neg hr1] at hrs
      have hr2 : r ≠ .temp (st.env.size - 1) j₀ := fun e' => by rw [if_pos e'] at hrs; cases hrs
      rw [if_neg hr2] at hrs
      obtain rfl := huniq r r' L hrs hrs'
      unfold holderTy; rw [hr₀, hr₀']
      cases r with
      | bind f i => exact congrArg TyS.m (hXtyO _ hr1)
      | temp f i => show t₃.heldTy L = s.heldTy L; rw [ht3held]
  have hF : ∀ ψ, (RelF φ ({ t₃.pushBind b with shape := S5 } : SState) ψ ∧
      TypedLive K ({ t₃.pushBind b with shape := S5 } : SState) ψ) → RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun L hL => hψ.1 L (fun h' => hL ((hliveX L).mp h')),
      fun L hL => by have := hψ.2 L ((hliveX L).mpr hL); rwa [hholdX L hL] at this⟩
  have hshE' : ∀ q, q ≠ .bind (st.env.size - 1) fr.binds.size →
      Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = Env.shape st.env q :=
    fun q hq => shape_pushBindE_ne st.env h _ _ p d fr hfr q hq
  have hshNew : Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d)
      (.bind (st.env.size - 1) fr.binds.size) = some l := by
    rw [shape_eq_shapeOf, valAt_pushBindE_new st.env h _ _ p d fr hfr]; rfl
  have hsv : ∀ L pos path, (Value.borrow l w).sitesOf L pos path = [] := fun L pos path => hw.sitesOf L pos _
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
      rw [hXvalB]
      split
      · next he => rw [he, mean_pushBindE_new K.dm K.M K.Γ ρ st.env h _ p d fr hfr _ T]; exact hc _ _
      · next he =>
        rw [mean_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) _ p d fr hfr _ _ he]
        have := hr'.sim.1 ψ (hF ψ hψ) (.bind f i) hq
        rw [← this]
        exact (mean_pushTempE_other K.dm K.M K.Γ ρ st.env _ fr hfr _ _ (by intro e; cases e)).symm
  · -- the checker's holders at bindings are the reference's
    intro q l' hq hsh
    have hsh' : Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = some l' := hsh
    rw [hshX]
    by_cases he : q = .bind (st.env.size - 1) fr.binds.size
    · rw [he, hshNew] at hsh'; cases hsh'; rw [if_pos he]
    · rw [hshE' q he] at hsh'
      rw [if_neg he, if_neg (fun e => by subst e; exact hq trivial)]
      cases q with
      | temp => exact absurd trivial hq
      | bind f i =>
        exact hr'.sim.2.1 (.bind f i) l' hq
          (by show Env.shape (Env.pushTempE st.env (.borrow l w)) _ = _; rw [shape_pushTempE_bind]; exact hsh')
  · -- the reference's holders at bindings are the checker's
    intro q L hq hsh
    rw [hshX] at hsh
    by_cases he : q = .bind (st.env.size - 1) fr.binds.size
    · rw [if_pos he] at hsh; cases hsh
      refine ⟨l, ?_, rfl⟩
      show Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = some l
      rw [he, hshNew]
    · rw [if_neg he, if_neg (fun e => by subst e; exact hq trivial)] at hsh
      obtain ⟨l', h1, h2⟩ := hr'.sim.2.2.1 q L hq hsh
      refine ⟨l', ?_, h2⟩
      show Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) q = some l'
      cases q with
      | temp => exact absurd trivial hq
      | bind f i =>
        rw [hshE' _ he]
        have : Env.shape (Env.pushTempE st.env (.borrow l w)) (.bind f i) = some l' := h1
        rwa [shape_pushTempE_bind] at this
  · -- the checker's temporaries holding a borrow
    intro f i l' hsh
    have hsh' : Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) (.temp f i) = some l' := hsh
    rw [hshE' _ (fun e => by cases e)] at hsh'
    have hmem := mem_allPos_of_shape hsh'
    have hntq : Pos.temp f i ≠ .temp (st.env.size - 1) fr.temps.size := fun e => by
      rw [e] at hmem; obtain ⟨fr', hf', hi⟩ := mem_allPos_temp st.env _ _ hmem
      rw [hfr] at hf'; cases hf'; exact absurd hi (Nat.lt_irrefl _)
    have hshC : Env.shape (Env.pushTempE st.env (.borrow l w)) (.temp f i) = some l' := by
      rw [shape_eq_shapeOf, hvalC _ hmem, ← shape_eq_shapeOf]; exact hsh'
    obtain ⟨j, hj, hjv⟩ := hr'.sim.2.2.2.1 f i l' hshC
    have hl' : l' ≠ l := fun e => hnl _ (e ▸ hsh')
    have hπ : π l' ≠ π l := fun e => hl' (hr'.inj l' l (FEnd.liveLoan_of_shape hshC) hliveCl e)
    have hjne : Pos.temp f j ≠ .temp (st.env.size - 1) j₀ := fun e => by
      rw [e, hj₀] at hj; exact hπ (Option.some.inj hj).symm
    refine ⟨j, by rw [hshX, if_neg (fun e => by cases e), if_neg hjne]; exact hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ _ (Env.pushBindE st.env h (some T) (.borrow l w) p d) (.temp f i) =
      (t₃.pushBind b).valAt (.temp f j) ψ
    rw [mean_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) _ p d fr hfr _ _ (fun e => by cases e), hXvalT f j hjne,
      ← hjv ψ (hF ψ hψ)]
    exact (mean_pushTempE_other K.dm K.M K.Γ ρ st.env _ fr hfr _ _ hntq).symm
  · -- the reference's temporaries holding a borrow
    intro f j L hsh
    rw [hshX, if_neg (fun e => by cases e)] at hsh
    split at hsh
    · cases hsh
    · next hjne =>
      obtain ⟨i, l', h1, h2⟩ := hr'.sim.2.2.2.2 f j L hsh
      have hntq : Pos.temp f i ≠ .temp (st.env.size - 1) fr.temps.size := fun e => by
        have h1' : Env.shape (Env.pushTempE st.env (.borrow l w)) (.temp f i) = some l' := h1
        rw [e, hntC] at h1'; cases h1'
        exact hjne (hshS _ (by rw [h2]; exact hsh))
      refine ⟨i, l', ?_, h2⟩
      show Env.shape (Env.pushBindE st.env h (some T) (.borrow l w) p d) (.temp f i) = some l'
      rw [hshE' _ (fun e => by cases e)]
      have : Env.shape (Env.pushTempE st.env (.borrow l w)) (.temp f i) = some l' := h1
      rwa [shape_eq_shapeOf, valAt_pushTempE_old _ _ fr hfr f i hntq, ← shape_eq_shapeOf] at this
  · -- the renaming is one to one
    intro l₁ l₂ h₁ h₂ e
    exact hr'.inj l₁ l₂ ((liveLoan_pushTempE_bor hfr hne hw l₁).mpr ((liveLoan_pushBindE_bor hfr hne h _ p d hw l₁).mp h₁))
      ((liveLoan_pushTempE_bor hfr hne hw l₂).mpr ((liveLoan_pushBindE_bor hfr hne h _ p d hw l₂).mp h₂)) e
  · -- the sites
    intro L hL x
    have hLC := (liveLoan_pushTempE_bor hfr hne hw L).mpr ((liveLoan_pushBindE_bor hfr hne h _ p d hw L).mp hL)
    show x ∈ t₃.lent (π L) ↔ _
    rw [ht3lent, hr'.sites L hLC x, hEc, sitesOf_pushTempE' st.env _ fr hfr hne L (hsv L),
      sitesOf_pushBindE st.env h (some T) _ p d fr hfr hne L (hsv L)]
  · -- the holders are positions
    intro q L hsh
    rw [hshX] at hsh
    split at hsh
    · next he => exact (hXpos q).mpr (.inl he)
    · split at hsh
      · cases hsh
      · exact (hXpos q).mpr (.inr (hr'.holders q L hsh))
  · -- the records
    intro L hL
    have hLs := (hliveX L).mp hL
    rw [hholdX L hLs]
    have := hr'.records L hLs
    show (t₃.heldMem L).whole ∧ t₃.heldMem L ∈ₛ[K.dm.read] holderTy s L
    rw [ht3mem]; exact this

end

end Ochr.Meaning.Steps.Form
