import Ochr.Meaning.Steps.ColumnLetB
import Ochr.Meaning.Steps.ColumnB

/-!
# The borrow column: the read of `x` that ends `y`'s borrow (lead8)

At `B`'s read (`x ↦ loan_l : Nat`, `y ↦ borrow_l w : &Nat`, `w` a number), the checker's [Access]
of `x` ends `l` (`VarEndInv`), and so does the reference's (`ColumnB.atRead_access`), under ruling
(A)'s STRICT END: the end passes because the holder's content is a whole member of the label's type at
every typed future, which the relation gives (`typedFut_rel`: a typed future of a good state is one it
compares at). The lender is then read through the future at the holder's content, which the relation
also fixes: the holder reads no label of its own (`SGood.holderIndep`), so it means `w` at the future
the run reads at, and `x` at the future that gives the label `w` means `w`.
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

section
variable {K : RunCtx} {φ : Future}

/-- **The strict end of an [Access] that ends exactly one label** passes where that end does. -/
theorem accessOk_single {s : SState} {p : Pos} {hit : List Step → Bool} {l : Nat}
    (hlive : ∀ z, s.Live z ↔ z = l) (hnone : ∀ z, ¬ (s.endLabel l).Live z) (hend : EndOk K φ s l) :
    AccessOk K φ s p hit := by
  have hfix : ∀ (L : List Nat), (∀ z ∈ L, z = l) → L.foldl SState.endLabel (s.endLabel l) = s.endLabel l := by
    intro L hL
    exact foldl_fix _ _ L fun z hz => by rw [hL z hz]; exact endLabel_of_not_live (hnone l)
  have hends : ∀ (L : List Nat), (∀ z ∈ L, z = l) → EndsOk K φ L s := by
    intro L hL
    cases L with
    | nil => trivial
    | cons a L =>
      obtain rfl := hL a (List.mem_cons_self ..)
      refine ⟨hend, ?_⟩
      have : ∀ (M : List Nat) (t : SState), (∀ z, ¬ t.Live z) → EndsOk K φ M t := by
        intro M
        induction M with
        | nil => intro _ _; trivial
        | cons b M ih =>
          intro t ht
          refine ⟨fun r hr => absurd (SState.holderOf_spec hr) (fun h => ht b ((SState.live_iff t b).mpr ⟨r, h⟩)), ?_⟩
          rw [endLabel_of_not_live (ht b)]
          exact ih t ht
      exact this L _ hnone
  have hall : ∀ z ∈ s.liveLabels, z = l := fun z hz => (hlive z).mp hz
  have hstep : accRound p hit s = s.endLabel l ∨ accRound p hit s = s := by
    unfold accRound
    cases e : s.liveLabels.filter (s.reached p hit) with
    | nil => exact .inr rfl
    | cons a L =>
      have ha : a = l := hall a ((List.mem_filter.mp (by rw [e]; exact List.mem_cons_self ..)).1)
      subst ha
      left
      rw [List.foldl_cons]
      exact hfix L fun z hz => hall z ((List.mem_filter.mp (by rw [e]; exact List.mem_cons_of_mem _ hz)).1)
  have hround : ∀ t, (∀ z, ¬ t.Live z) → accRound p hit t = t := fun t ht => by
    unfold accRound
    rw [List.filter_eq_nil_iff.mpr fun z hz => absurd hz (ht z)]; rfl
  intro k _
  cases k with
  | zero =>
    exact hends _ fun z hz => hall z ((List.mem_filter.mp hz).1)
  | succ k =>
    have hk : (List.range (k + 1)).foldl (fun t _ => accRound p hit t) s = s.endLabel l ∨
        (List.range (k + 1)).foldl (fun t _ => accRound p hit t) s = s := by
      rw [List.range_succ_eq_map, List.foldl_cons]
      rcases hstep with e | e
      · rw [e]; left; exact foldl_fix _ _ _ fun _ _ => hround _ hnone
      · rw [e]; right; exact foldl_fix _ _ _ fun _ _ => e
    rcases hk with e | e
    · rw [e, List.filter_eq_nil_iff.mpr fun z hz => absurd hz (hnone z)]; trivial
    · rw [e]; exact hends _ fun z hz => hall z ((List.mem_filter.mp hz).1)

end

theorem skel_mapVals (s : SState) (g : Pos → SVal → SVal) :
    (s.mapVals g).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
  simp only [SState.mapVals, List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst 0 s.env, List.map_map]
  congr 1; funext x
  simp only [Function.comp_apply, List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst 0 x.1.binds, List.map_map]
  rfl

theorem skel_endAt (s : SState) (l : Nat) (r : Pos) :
    (s.endAt l r).env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel) := by
  unfold SState.endAt; exact skel_mapVals _ _

/-! ## The checker's state at the read -/

/-- **`B`'s state at the read of `x`**, the checker's side alone: one frame, `x ↦ loan_l` stored at
`Nat`, `y ↦ borrow_l w` stored at `&Nat`, `w` a number, nothing else. -/
structure ReadPre (st : MState) (l : Nat) (w : Value) : Prop where
  pos : allPos st.env = [.bind 0 0, .bind 0 1]
  ckx : ckVarPos st.env 1 = some (.bind 0 0)
  x : valAt st.env (.bind 0 0) = .loan l
  y : valAt st.env (.bind 0 1) = .borrow l w
  num : w.Num
  tyx : ∀ bx, st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some bx → bx.ty = some .tNat
  tyy : ∀ by', st.env[0]?.bind (fun fr : Frame => fr.binds[1]?) = some by' → by'.ty = some (.tRef .tNat)

theorem ReadPre.of_erase {st st' : MState} {l : Nat} {w : Value} (he : st.env.erase = st'.env.erase)
    (h : ReadPre st l w) : ReadPre st' l w where
  pos := by rw [← allPos_erase, ← he, allPos_erase]; exact h.pos
  ckx := by rw [← ckVarPos_erase, ← he, ckVarPos_erase]; exact h.ckx
  x := by rw [← valAt_erase, ← he, valAt_erase]; exact h.x
  y := by rw [← valAt_erase, ← he, valAt_erase]; exact h.y
  num := h.num
  tyx := fun bx hb => h.tyx bx (by rw [← lookup_erase, he, lookup_erase]; exact hb)
  tyy := fun by' hb => h.tyy by' (by rw [← lookup_erase, he, lookup_erase]; exact hb)

theorem ReadPre.lookup {st : MState} {l : Nat} {w : Value} (h : ReadPre st l w) (i : Nat) (hi : i < 2) :
    ∃ b, st.env[0]?.bind (fun fr : Frame => fr.binds[i]?) = some b ∧ valAt st.env (.bind 0 i) = b.val := by
  have hm : Pos.bind 0 i ∈ allPos st.env := by
    rw [h.pos]; rcases i with _ | _ | i
    · simp
    · simp
    · omega
  obtain ⟨fr, b, hf, hb⟩ := mem_allPos_bind st.env 0 i hm
  refine ⟨b, by rw [hf]; exact hb, ?_⟩
  rw [valAt_bind_eq, hf, Option.getD_some, hb, Option.getD_some]

theorem ReadPre.atRead {K : RunCtx} {ρ : Assignment} {st : MState} {l : Nat} {w : Value} (h : ReadPre st l w) :
    AtRead K ρ st l w where
  pos := h.pos
  ckx := h.ckx
  x := h.x
  y := h.y
  num := h.num
  tx := by
    obtain ⟨b, hb, -⟩ := h.lookup 0 (by omega)
    simp only [Env.hintAt, hb, h.tyx b hb]; rfl
  ty := by
    obtain ⟨b, hb, -⟩ := h.lookup 1 (by omega)
    simp only [Env.hintAt, hb, h.tyy b hb]; rfl

/-! ## The relation after the read -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem mean_bind_not_mem {env : Env} {f i : Nat} {χ : Future} (hp : Pos.bind f i ∉ allPos env) :
    Env.mean K.dm K.M K.Γ ρ χ env (.bind f i) = .err := by
  have e : env[f]?.bind (fun fr : Frame => fr.binds[i]?) = none := by
    rcases e1 : env[f]? with _ | fr
    · rfl
    · simp only [Option.bind_some]
      rcases e2 : fr.binds[i]? with _ | b
      · rfl
      · exact absurd (bind_mem_allPos env f i fr b e1 e2) hp
  simp only [Env.mean, e]

/-- **The relation after the read that ended `y`**: on the checker's side `y ↦ ⊥` and `x ↦ xv` (`w`
copied back, or `⊥` moved), on the reference's any state `t` with the same skeleton and positions, no
label held, `y` moved, `x` the constant `xv` means, and every other binding `err`. -/
theorem rel_afterEnd {π : Nat → Nat} {st : MState} {s t : SState} {l : Nat} {w xv : Value} {cx : Sem}
    (hr : Rel K ρ φ π st s) (hpre : ReadPre st l w) (hxv : xv = w ∨ xv = .bot)
    (hcx : ∀ (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (φ : Future) (hint : TyS),
      Value.mean dm C Γ ρ φ hint xv = cx)
    (ht_skel : t.env.map (fun fr => fr.binds.map bindSkel) = s.env.map (fun fr => fr.binds.map bindSkel))
    (ht_shape : ∀ p, t.shape p = none) (ht_nl : t.nextLoan = s.nextLoan)
    (ht_y : t.valAt (.bind 0 1) φ = .moved) (ht_x : t.valAt (.bind 0 0) φ = cx)
    (ht_o : ∀ f i, Pos.bind f i ≠ .bind 0 0 → Pos.bind f i ≠ .bind 0 1 → t.valAt (.bind f i) φ = .err) :
    Rel K ρ φ π { st with env := Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv } t := by
  have hpos' : allPos (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) = [.bind 0 0, .bind 0 1] := by
    rw [allPos_setAtE, allPos_setAtE, hpre.pos]
  have hxm : Pos.bind 0 0 ∈ allPos st.env := by rw [hpre.pos]; simp
  have hym : Pos.bind 0 1 ∈ allPos st.env := by rw [hpre.pos]; simp
  have hval' : ∀ q, valAt (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) q =
      if q = .bind 0 0 then xv else if q = .bind 0 1 then .bot else valAt st.env q := fun q => by
    split
    · next h => rw [h]; exact valAt_setAtE_self _ (by rw [allPos_setAtE]; exact hxm)
    · next h =>
      rw [valAt_setAtE_other _ _ _ _ h]
      split
      · next h' => rw [h']; exact valAt_setAtE_self _ hym
      · next h' => exact valAt_setAtE_other _ _ _ _ h'
  have hxvn : ∀ l', xv.holdsBorrow l' = false ∧ shapeOf xv = none ∧ ∀ P : Value → Bool, P .zero = false →
      P .unit = false → (∀ w, P (.succ w) = false) → P .bot = false → xv.anyAtom P = false := by
    intro l'
    rcases hxv with rfl | rfl
    · exact ⟨hpre.num.holdsBorrow l', hpre.num.inert.shape, fun P h0 h1 h2 _ => hpre.num.inert.anyAtom P h0 h1 h2⟩
    · exact ⟨rfl, rfl, fun P _ _ _ hb => by simp [Value.anyAtom, hb]⟩
  have hnoshape : ∀ q, Env.shape (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) q = none := by
    intro q
    rcases e : Env.shape (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) q with _ | l'
    · rfl
    · have hq := mem_allPos_of_shape e
      rw [hpos'] at hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rw [shape_eq_shapeOf, hval'] at e
      rcases hq with rfl | rfl
      · rw [if_pos rfl, (hxvn l').2.1] at e; cases e
      · rw [if_neg (by simp), if_pos rfl] at e; cases e
  have hnolive : ∀ l', liveLoan (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) l' = false := by
    intro l'
    cases e : liveLoan (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) l' with
    | false => rfl
    | true =>
      exfalso
      unfold liveLoan findBorrow at e
      obtain ⟨q, hq, hb⟩ := List.find?_isSome.mp e
      rw [hpos'] at hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rw [hval'] at hb
      rcases hq with rfl | rfl
      · rw [if_pos rfl, (hxvn l').1] at hb; cases hb
      · rw [if_neg (by simp), if_pos rfl] at hb; cases hb
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := skel_setAtE K ρ ({ st with env := Env.setAtE st.env (.bind 0 1) .bot } : MState) 0 0 xv
    exact h1.trans ((skel_setAtE K ρ st 0 1 .bot).trans (hr.skel.trans ht_skel.symm))
  · intro l' _ ho
    exfalso
    obtain ⟨v', hv', ha⟩ := ho
    simp only [Env.values, hpos', List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl
    · rw [hval', if_pos rfl, (hxvn l').2.2 _ (by rfl) (by rfl) (fun _ => by rfl) (by rfl)] at ha; cases ha
    · rw [hval', if_neg (by simp), if_pos rfl] at ha
      simp only [Value.anyAtom, Bool.or_false, show (Value.bot == Value.loan l') = false from rfl,
        Bool.false_or] at ha
      cases ha
  · intro ψ hψ p hp
    have hψφ : ψ = φ := funext fun z => hψ.1 z (fun h => by
      obtain ⟨q, -, hq⟩ := (SState.live_iff t z).mp h; rw [ht_shape] at hq; cases hq)
    subst hψφ
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      show Env.mean K.dm K.M K.Γ ρ _ (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) (.bind f i) = _
      by_cases hx0 : Pos.bind f i = .bind 0 0
      · rw [hx0, mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [hpos']; simp), hval', if_pos rfl, ht_x]
        exact hcx _ _ _ _ _ _
      · by_cases hy0 : Pos.bind f i = .bind 0 1
        · rw [hy0, mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [hpos']; simp), hval', if_neg (by simp), if_pos rfl, ht_y]
          rfl
        · rw [ht_o f i hx0 hy0, mean_bind_not_mem (by rw [hpos']; simp_all)]
  · intro p l' _ hsh
    have : Env.shape (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) p = some l' := hsh
    rw [hnoshape] at this; cases this
  · intro p l' _ hsh; rw [ht_shape] at hsh; cases hsh
  · intro f i l' hsh
    have : Env.shape (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) (.temp f i) = some l' := hsh
    rw [hnoshape] at this; cases this
  · intro f j l' hsh; rw [ht_shape] at hsh; cases hsh
  · intro l₁ _ h₁; rw [hnolive] at h₁; cases h₁
  · intro l₁ h₁; rw [hnolive] at h₁; cases h₁
  · intro p l' hsh; rw [ht_shape] at hsh; cases hsh
  · intro l' hl'
    obtain ⟨p, -, hp⟩ := (SState.live_iff t l').mp hl'
    rw [ht_shape] at hp; cases hp
  · intro p q l' hp; rw [ht_shape] at hp; cases hp

end

/-! ## The step -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem asg_afterEnd {st : MState} {xv : Value} (ha : Asg K ρ st.norm) (hxv : ∀ σ, xv.hasAbs σ = false) :
    Asg K ρ ({ st with env := Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv } : MState).norm := by
  refine ha.of_refd rfl rfl rfl rfl rfl (refd_sub rfl rfl rfl rfl ?_ ?_ ?_)
  · intro w hw σ hσ
    rcases mem_values_setAtE hw with rfl | hw'
    · rw [hxv] at hσ; cases hσ
    · rcases mem_values_setAtE hw' with rfl | hw₂
      · cases hσ
      · exact ⟨w, hw₂, hσ⟩
  · intro f' i' b' T σ hb' hT hσ
    obtain ⟨b₂, hb₂, hty₂, -⟩ := lookup_setAtE hb'
    obtain ⟨b₃, hb₃, hty₃, -⟩ := lookup_setAtE hb₂
    exact .ty f' i' b₃ T (by rw [show st.norm.env = st.env.erase from rfl, lookup_erase]; exact hb₃)
      (by rw [hty₃, hty₂]; exact hT) hσ
  · intro f' i' b' P ws j' σ hb' hl hσ
    obtain ⟨b₂, hb₂, -, hlz₂⟩ := lookup_setAtE hb'
    obtain ⟨b₃, hb₃, -, hlz₃⟩ := lookup_setAtE hb₂
    exact .lazyTy f' i' b₃ P ws j' (by rw [show st.norm.env = st.env.erase from rfl, lookup_erase]; exact hb₃)
      (by rw [hlz₃, hlz₂]; exact hl) hσ

/-- **The read of `x` that ends `y`'s borrow, at `evalCore`** (`B`'s read: `ReadPre`). The strict
run's end passes (`EndOk`: `y`'s content is a whole member of `Nat` at every typed future, through
the relation); the value read is `w`, read through the future at `y`'s content. -/
theorem readEnd_core (hVE : VarEndInv) (hI : InvSteps) (hPL : PlaceLocal K.D) {n : Nat} {P : MState → Prop}
    (hP : ∀ st, P st → ∃ l w, ReadPre st l w)
    (hdx : ∀ st, P st → ∀ b, st.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some b → b.decl = .other) :
    CoreSim K ρ φ (n + 1) (.place (.var 1)) P (· = true) := by
  intro st st' typed hint v T? s π hPst hty hm htn htd _ hp hr hS hv hab hnh hfl hok hD bh h
  subst hty
  obtain ⟨l, w, hpre⟩ := hP st hPst
  have hAR : AtRead K ρ st l w := hpre.atRead
  obtain ⟨rfl, hT, -, st₁, hq, hki, hcopy, hmove⟩ :=
    hVE n true hint st st' bh v T? l w K.D hm hpre.pos hpre.x hpre.y hpre.num hpre.tyx hD h
  obtain ⟨mw, hmw⟩ := hpre.num.vmean
  obtain ⟨bx, hlkx, -⟩ := hpre.lookup 0 (by omega)
  obtain ⟨byy, hlky, -⟩ := hpre.lookup 1 (by omega)
  obtain ⟨hxs, htyX⟩ := rel_bind_ty hr hlkx
  obtain ⟨hys, htyY⟩ := rel_bind_ty hr hlky
  have htyXn : (s.tyAt (.bind 0 0)).m = TyM.nat := by rw [htyX]; exact hAR.tx
  have htyYn : (s.tyAt (.bind 0 1)).m = TyM.nat := by rw [htyY]; exact hAR.ty
  obtain ⟨hy, honly⟩ := atRead_shape hr hAR
  have hlive := atRead_live hr hAR
  have hhold := atRead_holder hr hAR
  have hnone := atRead_none hr hAR
  have hacc := atRead_access hr hAR
  have hres : resolve s (.var 1) = some (.bind 0 0, []) := rel_resolve_ck K ρ φ st s π (.var 1) _ hr hpre.ckx
  -- `y` means `w`, `x` the label's final content, wherever the relation compares
  have hyv : ∀ ψ, RelF φ s ψ ∧ TypedLive K s ψ → s.valAt (.bind 0 1) ψ = .el0 Nat mw := fun ψ hψ => by
    rw [← hr.sim.1 ψ hψ (.bind 0 1) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind 0 1) = _
    rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [hpre.pos]; simp), hpre.y]; exact hmw _ _ _ _ _ _
  have hxv : ∀ ψ, RelF φ s ψ ∧ TypedLive K s ψ → s.valAt (.bind 0 0) ψ = ψ (π l) := fun ψ hψ => by
    rw [← hr.sim.1 ψ hψ (.bind 0 0) (by simp [IsTemp])]
    show Env.mean K.dm K.M K.Γ ρ _ st.env (.bind 0 0) = _
    rw [mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [hpre.pos]; simp), hpre.x]; rfl
  have hhty : holderTy s (π l) = TyM.nat := by
    unfold holderTy; rw [hhold]; exact htyYn
  have hheld : s.heldTy (π l) = TyM.nat := by rw [heldTy_eq_holderTy hS ((hlive _).mpr rfl), hhty]
  -- the strict end passes
  have hend : EndOk K φ s (π l) := by
    intro r hr' ψ hψ
    rw [hhold] at hr'; cases hr'
    rw [hyv ψ (typedFut_rel hS hψ), hheld]; exact ⟨mw, rfl⟩
  have hcok : ContentOk K φ (.var 1) s := by
    unfold ContentOk; rw [hres]; exact accessOk_single hlive hnone hend
  -- the lender read through the future at the holder's content
  have hrel : ∀ X : Sem, X.whole → X ∈ₛ[K.dm.read] TyM.nat →
      RelF φ s (φ.upd (π l) X) ∧ TypedLive K s (φ.upd (π l) X) := fun X hw hm' =>
    ⟨fun z hz => by
        have : z ≠ π l := fun e => hz ((hlive z).mpr e)
        simp [Future.upd, this],
     fun z hz => by
        obtain rfl := (hlive z).mp hz
        simp only [Future.upd, if_true]; rw [hhty]; exact ⟨hw, hm'⟩⟩
  have hyφ : s.valAt (.bind 0 1) φ = .el0 Nat mw := by
    rw [← hS.holderIndep hy φ (s.heldMem (π l))]
    apply hyv
    have hrec := hr.records (π l) ((hlive _).mpr rfl)
    rw [hhty] at hrec
    exact hrel _ hrec.1 hrec.2
  have hxφ : s.valAt (.bind 0 0) (φ.upd (π l) (.el0 Nat mw)) = .el0 Nat mw := by
    rw [hxv (φ.upd (π l) (.el0 Nat mw)) (hrel (.el0 Nat mw) (by simp [Sem.whole]) ⟨mw, rfl⟩)]; simp [Future.upd]
  have hnone' : ∀ z, ¬ (s.endAt (π l) (.bind 0 1)).Live z := by rw [← SState.endLabel_eq hhold]; exact hnone
  have htf : (s.endAt (π l) (.bind 0 1)).typedFuture φ = φ := funext fun z => by
    have : z ∉ (s.endAt (π l) (.bind 0 1)).liveLabels := hnone' z
    simp [SState.typedFuture, this]
  have hx' : (s.endAt (π l) (.bind 0 1)).valAt (.bind 0 0) φ = .el0 Nat mw := by
    rw [SState.endAt_valAt _ _ _ _ hxs]; simp only [if_neg (show Pos.bind 0 0 ≠ .bind 0 1 by simp)]; rw [hyφ, hxφ]
  have hy' : (s.endAt (π l) (.bind 0 1)).valAt (.bind 0 1) φ = .moved := by
    rw [SState.endAt_valAt _ _ _ _ hys]; simp
  have htyE : ∀ q, (s.endAt (π l) (.bind 0 1)).tyAt q = s.tyAt q := fun q => by
    unfold SState.endAt; rw [Strict.tyAt_mapVals]; rfl
  have hshE : ∀ q, (s.endAt (π l) (.bind 0 1)).shape q = none := fun q => by
    rw [SState.endAt_shape]
    show (if q = .bind 0 1 then none else s.shape q) = none
    split
    · rfl
    · next h =>
      rcases e : s.shape q with _ | z
      · rfl
      · exact absurd (honly q z e).1 h
  have hpos_s : ∀ f i, Pos.bind f i ∈ s.positions → Pos.bind f i = .bind 0 0 ∨ Pos.bind f i = .bind 0 1 := by
    intro f i h
    obtain ⟨-, hfrm⟩ := rel_frames K ρ φ hr
    rw [SState.mem_positions] at h
    simp only [SState.lookup] at h
    rcases e : s.env[f]? with _ | fr
    · rw [e] at h; cases h
    · rw [e] at h
      have hi : i < fr.binds.length := by
        rcases e2 : fr.binds[i]? with _ | b
        · simp [e2] at h
        · exact (List.getElem?_eq_some_iff.mp e2).1
      have h2 := hfrm f
      rw [e] at h2
      rcases e' : st.env[f]? with _ | fr'
      · rw [e'] at h2; cases h2
      · rw [e'] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        have hi' : i < fr'.binds.size := by rw [← h2]; exact hi
        have hm := bind_mem_allPos st.env f i fr' _ e' (Array.getElem?_eq_getElem hi')
        rw [hpre.pos] at hm
        simpa using hm
  have ho_s : ∀ f i, Pos.bind f i ≠ .bind 0 0 → Pos.bind f i ≠ .bind 0 1 →
      (s.endAt (π l) (.bind 0 1)).valAt (.bind f i) φ = .err := fun f i h0 h1 => by
    have hn : Pos.bind f i ∉ s.positions := fun hm => by
      rcases hpos_s f i hm with e | e
      · exact h0 e
      · exact h1 e
    rw [SState.endAt_valAt_not_mem _ _ _ _ hn, SState.valAt_of_not_mem _ _ hn]
  have hco : contentOf K φ (.var 1) s =
      some ((.el0 Nat mw, (s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0), .bind 0 0, []), s.endAt (π l) (.bind 0 1)) := by
    unfold contentOf; rw [hres]; simp only; rw [hacc, htf]; simp [Sem.follow, hx']
  have hrg : ReadGood K.dm.read ((s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0)).m (.el0 Nat mw) :=
    .inl (by rw [htyE, htyXn]; exact ⟨mw, rfl⟩)
  have hwhole : (Sem.el0 Nat mw).whole := by simp [Sem.whole]
  have hsc : scopeOf s = DecideScope.topReadings st := scopeOf_rel hr
  have hrun : runT K ρ φ st.curTail (hintM K ρ hint) (.place (.var 1)) s =
      readPlace K φ (.var 1) (K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var 1))) s := by
    rw [runT]; show SM.erasedIf (K.D.flags (scopeOf s) _) _ s = _; rw [hfl, hsc]
    show SM.guarded _ _ s = _; unfold SM.guarded; rw [if_pos hcok]
  -- the checker's side after the quiet step
  have hpre₁ : ReadPre st₁ l v := hpre.of_erase hq.env
  have hr₁ : Rel K ρ φ π st₁ s := hr.of_quiet hq hp.labels
  have ha₁ : Asg K ρ st₁.norm := Asg.of_quiet hq hp.asg hp.inv.wf6
  have hdx₁ : ∀ b, st₁.env[0]?.bind (fun fr : Frame => fr.binds[0]?) = some b → b.decl = .other := fun b hb =>
    hdx st hPst b (by rw [← lookup_erase, hq.env, lookup_erase]; exact hb)
  have hinv : Inv K.D K.Γ (st'.withTempT v T?).norm := by
    have h₁ : Inv K.D K.Γ st₁.norm := hki K.D K.Γ hp.inv
    refine hI.pushInert K.D K.Γ st' _ _ (.inl hpre₁.num) ?_
    cases hc : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var 1))
    · rw [← (hmove hc).norm]
      exact hI.endRead K.D K.Γ st₁ l v .bot hPL hdx₁ hpre₁.pos hpre₁.x hpre₁.y hpre₁.num (.inr rfl) h₁
    · rw [← (hcopy hc).norm]
      exact hI.endRead K.D K.Γ st₁ l v v hPL hdx₁ hpre₁.pos hpre₁.x hpre₁.y hpre₁.num (.inl rfl) h₁
  have hmeanV : ∀ ψ hint', meanV K ρ ψ hint' v = .el0 Nat mw := fun ψ hint' => by
    rw [← meanV_eq_mean]; exact hmw _ _ _ _ _ _
  have hagree : ∀ T, T? = some T →
      StrAgree K ρ T { (s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0) with label := none } := by
    intro T e
    have := hT rfl; rw [this] at e; cases e
    show _ = ((s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0)).m; rw [htyE, htyXn]; rfl
  have hskel := skel_endAt s (π l) (.bind 0 1)
  have hnl : (s.endAt (π l) (.bind 0 1)).nextLoan = s.nextLoan := rfl
  cases hc : K.D.copy (K.D.placeDecl (DecideScope.topReadings st) (.var 1))
  · -- a move: `⊥` at `x`
    have hk := hmove hc
    have hset : setContent K φ (.bind 0 0) [] .moved (s.endAt (π l) (.bind 0 1)) =
        some (⟨⟩, (s.endAt (π l) (.bind 0 1)).setAt (.bind 0 0) fun φ' =>
        (Sem.updAt K.dm K.Γ ((s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0)) (fun _ => .moved) []
          ((s.endAt (π l) (.bind 0 1)).valAt (.bind 0 0) φ')).getD .err) := by
      unfold setContent; rw [if_pos (by intro ψ _; rfl)]
    have hst : readPlace K φ (.var 1) false s = some ((.el0 Nat mw,
        { (s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0) with label := none }),
        (s.endAt (π l) (.bind 0 1)).setAt (.bind 0 0) fun φ' =>
          (Sem.updAt K.dm K.Γ ((s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0)) (fun _ => .moved) []
            ((s.endAt (π l) (.bind 0 1)).valAt (.bind 0 0) φ')).getD .err) := by
      unfold readPlace
      rw [hco]
      simp only [Option.bind_some, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
        hshE, hset, bind, Option.bind]
      rfl
    have hxE : Pos.bind 0 0 ∈ (s.endAt (π l) (.bind 0 1)).positions := by rw [SState.endAt_positions]; exact hxs
    have hR := rel_afterEnd (cx := .moved) hr₁ hpre₁ (.inr rfl) (fun _ _ _ _ _ _ => rfl)
      (t := (s.endAt (π l) (.bind 0 1)).setAt (.bind 0 0) fun φ' =>
          (Sem.updAt K.dm K.Γ ((s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0)) (fun _ => .moved) []
            ((s.endAt (π l) (.bind 0 1)).valAt (.bind 0 0) φ')).getD .err)
      ((skel_setAt _ _ _).trans hskel) (fun q => by rw [SState.shape_setAt]; exact hshE q)
      (by rw [SState.nextLoan_setAt']; rfl)
      (by rw [SState.valAt_setAt_ne _ _ _ _ (by simp)]; exact hy')
      (by rw [valAt_setAt_self _ _ _ hxE]; rfl)
      (fun f i h0 h1 => by rw [SState.valAt_setAt_ne _ _ _ _ (Ne.symm h0)]; exact ho_s f i h0 h1)
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel hpre.num], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact asg_afterEnd ha₁ (fun _ => rfl)
        exact asg_withTempT_num this hpre.num T?
    · exact rel_withTempT_num (hR.of_kern hk) hpre.num T?
  · -- a copy: `w` back at `x`
    have hk := hcopy hc
    have hst : readPlace K φ (.var 1) true s = some ((.el0 Nat mw,
        { (s.endAt (π l) (.bind 0 1)).tyAt (.bind 0 0) with label := none }), s.endAt (π l) (.bind 0 1)) := by
      unfold readPlace
      rw [hco]
      simp only [hwhole, hrg, not_true_eq_false, if_false, if_true, bind, Option.bind]
    have hR := rel_afterEnd (cx := .el0 Nat mw) hr₁ hpre₁ (.inl rfl) hmw (t := s.endAt (π l) (.bind 0 1))
      hskel hshE hnl hy' hx' ho_s
    refine ⟨ρ, K.Δ, π, _, _, ⟨by rw [← hk.absTy]; exact hq.absSize, by rw [← hk.nextLoan]; exact hq.nextLoan,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, by rw [hrun, hc]; exact hst, hmeanV _ _, hagree,
      by simp [num_heldLabel hpre.num], ?_, ?_⟩
    · refine ⟨hp.ctx.of_eq ?_ ?_, hinv, ?_⟩
      · show st'.inds = st.inds; rw [← hk.inds, ← hq.inds]
      · show st'.globals = st.globals; rw [← hk.globals, ← hq.globals]
      · have : Asg K ρ st'.norm := by rw [← hk.norm]; exact asg_afterEnd ha₁ hpre.num.hasAbs
        exact asg_withTempT_num this hpre.num T?
    · exact rel_withTempT_num (hR.of_kern hk) hpre.num T?

end

end Ochr.Meaning.Steps.Form
