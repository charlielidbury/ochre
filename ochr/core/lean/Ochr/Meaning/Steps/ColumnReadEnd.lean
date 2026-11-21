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
    (ht_y : ∀ ψ, t.valAt (.bind 0 1) ψ = .moved) (ht_x : ∀ ψ, t.valAt (.bind 0 0) ψ = cx)
    (ht_o : ∀ f i, Pos.bind f i ≠ .bind 0 0 → Pos.bind f i ≠ .bind 0 1 → ∀ ψ, t.valAt (.bind f i) ψ = .err) :
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
  · intro ψ _ p hp
    cases p with
    | temp => exact absurd trivial hp
    | bind f i =>
      show Env.mean K.dm K.M K.Γ ρ _ (Env.setAtE (Env.setAtE st.env (.bind 0 1) .bot) (.bind 0 0) xv) (.bind f i) = _
      by_cases hx0 : Pos.bind f i = .bind 0 0
      · rw [hx0, mean_eq_valAt K.dm K.M K.Γ ρ _ _ _ (by rw [hpos']; simp), hval', if_pos rfl, ht_x]; exact hcx _ _ _ _ _ _
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

end Ochr.Meaning.Steps.Form
