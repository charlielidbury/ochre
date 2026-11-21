import Ochr.Meaning.Steps.ColumnPlumbAux

/-!
# Bindings pushed and popped, on both sides (lead7, the column; statements by the lead, proofs open)

A `let` pushes a binding for the value of its right-hand side and drops it after its tail. These are
the relation's and the assignment's facts about those two moves where the value is a number and
nothing is lent at the binding (what the column's program does). The statements are the lead's;
their proofs are to be supplied without changing them (if one is false, a counterexample is the
answer).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The environment with the top frame's last binding popped (what the checker's `dropTopBind` does
when it ends nothing). -/
def _root_.Ochr.Env.popBindE (env : Env) : Env :=
  env.modify (env.size - 1) fun fr => { fr with binds := fr.binds.pop }

/-- **(P1) A binding pushed for a number keeps the relation**: the checker pushes `v` at the stored
type `T`, the reference pushes the number's meaning `c` at a type of the same code, both with the
same declared reading `d`. -/
theorem rel_pushBind_inert {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState}
    {s : SState} (hr : Rel K ρ φ π st s) (hne : 0 < st.env.size) (h : Hint) (T : Value) {v : Value}
    (hv : v.Inert) (p : Bool) (d : DeclInfo) (R : TyS) (hR : (Value.tyS K.dm K.M K.Γ ρ T).m = R.m) (c : Sem)
    (hc : ∀ (φ' : Future) (hint : TyS), Value.mean K.dm K.M K.Γ ρ φ' hint v = c) :
    Rel K ρ φ π { st with env := Env.pushBindE st.env h (some T) v p d }
      (s.pushBind { ty := R, val := fun _ => c, decl := d }) := by
  generalize hb : ({ ty := R, val := fun _ => c, decl := d } : SBinding) = b
  have hbv : b.val = fun _ => c := by rw [← hb]
  have hbs : bindSkel b = (R.m, d) := by rw [← hb]; rfl
  -- the two top frames, aligned by the skeleton
  obtain ⟨fr, hfr⟩ : ∃ fr, st.env[st.env.size - 1]? = some fr :=
    ⟨_, Array.getElem?_eq_getElem (by omega : st.env.size - 1 < st.env.size)⟩
  obtain ⟨frs, hfrs, htop, hlen⟩ := skel_align K ρ st s hr.skel fr hfr
  have hnew : Pos.bind s.topIdx frs.binds.length = Pos.bind (st.env.size - 1) fr.binds.size := by rw [htop, hlen]
  -- the reference's new position holds nothing, so liveness, holders and their types are kept
  have hsh : s.shape (Pos.bind s.topIdx frs.binds.length) = none := by
    cases e : s.shape (Pos.bind s.topIdx frs.binds.length) with
    | none => rfl
    | some l => exact absurd (hr.holders _ l e) (newS_not_mem s frs hfrs)
  have hlive : ∀ l, (s.pushBind b).Live l ↔ s.Live l := live_pushBind' s b frs hfrs hsh
  have hhty : ∀ l, holderTy (s.pushBind b) l = holderTy s l := holderTy_pushBind s b frs hfrs hsh
  have hF : ∀ ψ, (RelF φ (s.pushBind b) ψ ∧ TypedLive K (s.pushBind b) ψ) → RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l hl => hψ.1 l (fun h' => hl ((hlive l).mp h')),
      fun l hl => by have := hψ.2 l ((hlive l).mpr hl); rwa [hhty] at this⟩
  -- the checker's new position holds a number: no borrow, no site
  have hlv : ∀ l, liveLoan (Env.pushBindE st.env h (some T) v p d) l = liveLoan st.env l :=
    fun l => liveLoan_pushBindE st.env h (some T) v p d fr hfr hne l (hv.holdsBorrow l)
  have hvshape : Env.shape (Env.pushBindE st.env h (some T) v p d) (.bind (st.env.size - 1) fr.binds.size) = none := by
    simp only [Env.shape, valAt_pushBindE_new st.env h (some T) v p d fr hfr]; exact hv.shape
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    rw [skel_pushBindE K ρ st h T v p d fr hfr, sskel_pushBind, hr.skel, htop, hbs, hR]
  · -- fresh
    intro l hl ho
    obtain ⟨w, hw, ha⟩ := ho
    rcases mem_values_pushBindE st.env h (some T) v p d fr hfr hne hw with rfl | hw
    · rw [hv.anyAtom _ rfl rfl (fun _ => rfl)] at ha; cases ha
    · exact hr.fresh l hl ⟨w, hw, ha⟩
  · -- the bindings' meanings
    intro ψ hψ q hq
    show Env.mean K.dm K.M K.Γ ρ _ (Env.pushBindE st.env h (some T) v p d) q = (s.pushBind b).valAt q ψ
    by_cases hqn : q = .bind (st.env.size - 1) fr.binds.size
    · subst hqn
      rw [mean_pushBindE_new K.dm K.M K.Γ ρ st.env h v p d fr hfr _ T, hc, ← hnew,
        valAt_pushBind_new s b frs hfrs, hbv]
    · rw [mean_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) v p d fr hfr _ q hqn,
        valAt_pushBind_ne s b frs hfrs q (by rw [hnew]; exact hqn)]
      exact hr.sim.1 ψ (hF ψ hψ) q hq
  · -- holders at bindings, checker to reference
    intro q l hq hs
    change Env.shape (Env.pushBindE st.env h (some T) v p d) q = some l at hs
    by_cases hqn : q = .bind (st.env.size - 1) fr.binds.size
    · subst hqn; rw [hvshape] at hs; cases hs
    · rw [shape_pushBindE_ne st.env h (some T) v p d fr hfr q hqn] at hs
      exact hr.sim.2.1 q l hq hs
  · -- holders at bindings, reference to checker
    intro q l' hq hs
    obtain ⟨l, h1, h2⟩ := hr.sim.2.2.1 q l' hq hs
    have hqn : q ≠ .bind (st.env.size - 1) fr.binds.size := by
      rintro rfl
      have hs' : s.shape (Pos.bind s.topIdx frs.binds.length) = some l' := by rw [hnew]; exact hs
      rw [hsh] at hs'; cases hs'
    refine ⟨l, ?_, h2⟩
    show Env.shape (Env.pushBindE st.env h (some T) v p d) q = some l
    rw [shape_pushBindE_ne st.env h (some T) v p d fr hfr q hqn]; exact h1
  · -- borrows in flight, checker to reference
    intro f i l hs
    have hqn : Pos.temp f i ≠ .bind (st.env.size - 1) fr.binds.size := by intro e; cases e
    change Env.shape (Env.pushBindE st.env h (some T) v p d) (.temp f i) = some l at hs
    rw [shape_pushBindE_ne st.env h (some T) v p d fr hfr _ hqn] at hs
    obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f i l hs
    refine ⟨j, hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ _ (Env.pushBindE st.env h (some T) v p d) (.temp f i) =
      (s.pushBind b).valAt (.temp f j) ψ
    rw [mean_pushBindE_ne K.dm K.M K.Γ ρ st.env h (some T) v p d fr hfr _ _ hqn,
      valAt_pushBind_ne s b frs hfrs _ (by intro e; cases e)]
    exact hjv ψ (hF ψ hψ)
  · -- borrows in flight, reference to checker
    intro f j l' hs
    obtain ⟨i, l, h1, h2⟩ := hr.sim.2.2.2.2 f j l' hs
    refine ⟨i, l, ?_, h2⟩
    show Env.shape (Env.pushBindE st.env h (some T) v p d) (.temp f i) = some l
    rw [shape_pushBindE_ne st.env h (some T) v p d fr hfr _ (by intro e; cases e)]; exact h1
  · -- inj
    intro l l' hl hl' hπ
    have hl1 : liveLoan (Env.pushBindE st.env h (some T) v p d) l = true := hl
    have hl2 : liveLoan (Env.pushBindE st.env h (some T) v p d) l' = true := hl'
    rw [hlv] at hl1 hl2
    exact hr.inj l l' hl1 hl2 hπ
  · -- sites
    intro l hl x
    have hl1 : liveLoan (Env.pushBindE st.env h (some T) v p d) l = true := hl
    rw [hlv] at hl1
    show x ∈ s.lent (π l) ↔ x ∈ Env.sitesOf (Env.pushBindE st.env h (some T) v p d) l
    rw [sitesOf_pushBindE st.env h (some T) v p d fr hfr hne l (fun pos path => hv.sitesOf l pos path)]
    exact hr.sites l hl1 x
  · -- holders
    intro q l hs
    obtain ⟨A, B, h1, h2⟩ := positions_pushBind' s b frs hfrs
    have hq := hr.holders q l hs
    rw [h1] at hq; rw [h2]
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
  · -- records
    intro l hl
    rw [hhty]
    exact hr.records l ((hlive l).mp hl)

/-- `rel_pushBind_inert` at a number. -/
theorem rel_pushBind_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState}
    {s : SState} (hr : Rel K ρ φ π st s) (hne : 0 < st.env.size) (h : Hint) (T : Value) {v : Value}
    (hv : v.Num) (p : Bool) (d : DeclInfo) (R : TyS) (hR : (Value.tyS K.dm K.M K.Γ ρ T).m = R.m) (c : Sem)
    (hc : ∀ (φ' : Future) (hint : TyS), Value.mean K.dm K.M K.Γ ρ φ' hint v = c) :
    Rel K ρ φ π { st with env := Env.pushBindE st.env h (some T) v p d }
      (s.pushBind { ty := R, val := fun _ => c, decl := d }) :=
  rel_pushBind_inert hr hne h T hv.inert p d R hR c hc

/-! ### (P2) as stated is false: `loans` does not walk a closure's recorded readings

`Value.loans` skips the declared types a closure records for its captures (`.clo cs t rd`'s `rd`,
D82), while `Value.hasLoan`, hence `Value.sitesOf` of a sealed program, walks them
(`SitesFollow.mem_loans_of_hasLoan` needs `rdHasLoan` false for the converse). A binding holding
`⌈clo [] Z [(_, loan 0)]⌉` has `loans = []` and no borrow, yet is a FILL site of the live label `0`
(held by a temporary). Popping it removes that site from the checker's `sitesOf`, and the
reference's `lent` keeps it, so `Rel.sites` fails after the pop. (WF15 excludes such values; `Rel`
and P2's hypotheses do not.) -/

namespace PopBindCE

/-- A sealed program whose closure records a declared type holding the loan `0`. -/
def wv : Value := .sealed (.val (.clo [] (.val .zero) [(.other, .loan 0)]))

def bv : Binding := { hint := default, ty := some .tNat, val := wv }

/-- One frame: the binding, and a temporary holding the borrow `0`. -/
def frv : Frame := { binds := #[bv], temps := #[.borrow 0 .zero] }

def stv : MState := { env := #[frv], nextLoan := 1 }

/-- The checker's state read as a reference state, with the live label's record a number. -/
noncomputable def s0 (K : RunCtx) (ρ : Assignment) : SState :=
  { SM' K ρ stv with heldTy := fun _ => TyM.nat, heldMem := fun _ => .el0 Nat 0 }

theorem allPos_stv : allPos stv.env = [.bind 0 0, .temp 0 0] := by rw [allPos_eq]; rfl

theorem sitesOf_stv : Env.sitesOf stv.env 0 = [⟨.bind 0 0, [], true⟩] := by
  rw [Env.sitesOf, allPos_stv]; rfl

theorem allPos_pop : allPos (Env.popBindE stv.env) = [.temp 0 0] := by rw [allPos_eq]; rfl

theorem sitesOf_pop : Env.sitesOf (Env.popBindE stv.env) 0 = [] := by
  rw [Env.sitesOf, allPos_pop]; rfl

theorem rel_s0 (K : RunCtx) (ρ : Assignment) (φ : Future) : Rel K ρ φ id stv (s0 K ρ) where
  skel := rfl
  fresh := fun _ h _ => h
  sim := ⟨fun ψ _ p _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ stv).valAt p ψ
      rw [sstate_valAt]; rfl,
    fun _ _ _ h => h,
    fun _ l' _ h => ⟨l', h, rfl⟩,
    fun f i l h => ⟨i, h, fun ψ _ => by
      show _ = (MState.sstate K.dm K.M K.Γ ρ stv).valAt (.temp f i) ψ
      rw [sstate_valAt]; rfl⟩,
    fun f j l' h => ⟨j, l', h, rfl⟩⟩
  inj := fun _ _ _ _ h => h
  sites := fun _ _ _ => Iff.rfl
  holders := fun p l h => by
    show p ∈ (MState.sstate K.dm K.M K.Γ ρ stv).positions
    rw [sstate_positions]
    exact mem_allPos_of_shape (l := l) h
  records := fun l hl => by
    refine ⟨show Sem.whole (.el0 Nat 0) by simp [Sem.whole], ?_⟩
    obtain ⟨r, hr⟩ := SState.holderOf_of_live hl
    obtain ⟨hrp, hrs⟩ := SState.holderOf_spec hr
    have hpos : (s0 K ρ).positions = [.bind 0 0, .temp 0 0] := by
      show (MState.sstate K.dm K.M K.Γ ρ stv).positions = _
      rw [sstate_positions, allPos_stv]
    rw [hpos] at hrp
    unfold holderTy
    rw [hr]
    rcases List.mem_cons.mp hrp with rfl | hrp
    · exact absurd hrs (by show Env.shape stv.env (.bind 0 0) ≠ some l; simp [Env.shape, valAt, stv, frv, bv, wv])
    · rcases List.mem_singleton.mp hrp with rfl
      exact (⟨0, rfl⟩ : Sem.el0 Nat 0 ∈ₛ[K.dm.read] TyM.nat)

/-- **P2's hypotheses hold and its conclusion fails**, at every run context, assignment and future. -/
theorem rel_popBind_false (K : RunCtx) (ρ : Assignment) (φ : Future) :
    ∃ (st : MState) (s : SState) (fr : Frame) (b : Binding), Rel K ρ φ id st s ∧
      st.env[st.env.size - 1]? = some fr ∧ fr.binds.back? = some b ∧ b.val.loans = [] ∧
      (∀ l, b.val.holdsBorrow l = false) ∧
      ¬ Rel K ρ φ id { st with env := Env.popBindE st.env } s.dropLast := by
  refine ⟨stv, s0 K ρ, frv, bv, rel_s0 K ρ φ, rfl, rfl, rfl, fun _ => rfl, fun h => ?_⟩
  have hl : liveLoan (Env.popBindE stv.env) 0 = true := by
    simp [liveLoan, findBorrow, allPos_pop]; rfl
  have hx := (h.sites 0 hl ⟨.bind 0 0, [], true⟩).mp (by
    show _ ∈ Env.sitesOf stv.env 0
    rw [sitesOf_stv]; exact List.mem_singleton.mpr rfl)
  rw [sitesOf_pop] at hx
  cases hx

end PopBindCE

/-- **(P2, corrected) The top binding popped, where it has no site and holds no borrow, keeps the
relation.** P2 with `loans = []` replaced by the absence of sites at it, which is what the relation
reads (`Value.Num.sitesOf` gives it for a number; `rel_popBind_rd` derives it from `loans = []`
and WF15's clause for the value). -/
theorem rel_popBind_noSites {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState}
    {s : SState} (hr : Rel K ρ φ π st s) (fr : Frame) (b : Binding) (hfr : st.env[st.env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b)
    (hns : ∀ l, b.val.sitesOf l (.bind (st.env.size - 1) (fr.binds.size - 1)) [] = [])
    (hnb : ∀ l, b.val.holdsBorrow l = false) :
    Rel K ρ φ π { st with env := Env.popBindE st.env } s.dropLast := by
  have hne : 0 < st.env.size := by
    rcases Nat.eq_zero_or_pos st.env.size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at hfr; cases hfr
    · exact h
  rw [Array.back?_eq_getElem?] at hb
  have hn : 0 < fr.binds.size := by
    rcases Nat.eq_zero_or_pos fr.binds.size with h | h
    · rw [Array.getElem?_eq_none (by omega)] at hb; cases hb
    · exact h
  have hbv : valAt st.env (.bind (st.env.size - 1) (fr.binds.size - 1)) = b.val := by
    rw [valAt_bind_lookup, hfr]; simp only [Option.bind_some, hb]; rfl
  have he : Env.popBindE st.env = st.env.modify (st.env.size - 1) popTop := rfl
  obtain ⟨frs, hfrs, htop, hlen⟩ := skel_align K ρ st s hr.skel fr hfr
  have hn' : 0 < frs.binds.length := by omega
  have hold : Pos.bind s.topIdx (frs.binds.length - 1) = Pos.bind (st.env.size - 1) (fr.binds.size - 1) := by
    rw [htop, hlen]
  -- the popped binding holds no borrow, so the reference's holds none either
  have hvsh : Env.shape st.env (.bind (st.env.size - 1) (fr.binds.size - 1)) = none := by
    rw [shape_eq_shapeOf, hbv]
    cases e : b.val with
    | borrow l w => have := hnb l; rw [e] at this; simp [Value.holdsBorrow] at this
    | _ => rfl
  have hsh : s.shape (Pos.bind s.topIdx (frs.binds.length - 1)) = none := by
    cases e : s.shape (Pos.bind s.topIdx (frs.binds.length - 1)) with
    | none => rfl
    | some l' =>
      obtain ⟨l, h1, _⟩ := hr.sim.2.2.1 _ l' (by simp [IsTemp]) e
      rw [hold] at h1
      change Env.shape st.env _ = _ at h1
      rw [hvsh] at h1; cases h1
  have hshe : ∀ q, s.dropLast.shape q = s.shape q := shape_dropLast_eq s frs hfrs hsh
  have hlive : ∀ l, s.dropLast.Live l ↔ s.Live l := live_dropLast' s frs hfrs hn' hsh
  have hhty : ∀ l, holderTy s.dropLast l = holderTy s l := holderTy_dropLast s frs hfrs hn' hsh
  have hF : ∀ ψ, (RelF φ s.dropLast ψ ∧ TypedLive K s.dropLast ψ) → RelF φ s ψ ∧ TypedLive K s ψ :=
    fun ψ hψ => ⟨fun l hl => hψ.1 l (fun h' => hl ((hlive l).mp h')),
      fun l hl => by have := hψ.2 l ((hlive l).mpr hl); rwa [hhty] at this⟩
  have hlv : ∀ l, liveLoan (Env.popBindE st.env) l = liveLoan st.env l := fun l => by
    rw [he]; exact liveLoan_popTop st.env fr hfr hn hne l (by rw [hbv]; exact hnb l)
  have hst : ∀ l, Env.sitesOf (Env.popBindE st.env) l = Env.sitesOf st.env l := fun l => by
    rw [he]; exact sitesOf_popTop st.env fr hfr hn hne l (by rw [hbv]; exact hns l)
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- skel
    show (SM' K ρ { st with env := st.env.modify (st.env.size - 1) popTop }).env.map _ = _
    rw [skel_popTop K ρ st fr hfr, sskel_dropLast, hr.skel, htop]
  · -- fresh
    intro l hl ho
    obtain ⟨w, hw, ha⟩ := ho
    exact hr.fresh l hl ⟨w, mem_values_popTop st.env fr hfr hn hne hw, ha⟩
  · -- the bindings' meanings
    intro ψ hψ q hq
    show Env.mean K.dm K.M K.Γ ρ _ (st.env.modify (st.env.size - 1) popTop) q = s.dropLast.valAt q ψ
    by_cases hqo : q = .bind (st.env.size - 1) (fr.binds.size - 1)
    · subst hqo
      rw [mean_popTop_old K.dm K.M K.Γ ρ st.env fr hfr, ← hold, valAt_dropLast_old s frs hfrs]
    · rw [mean_popTop_ne K.dm K.M K.Γ ρ st.env fr hfr _ q hqo,
        valAt_dropLast_ne s frs hfrs q (by rw [hold]; exact hqo)]
      exact hr.sim.1 ψ (hF ψ hψ) q hq
  · -- holders at bindings, checker to reference
    intro q l hq hs
    change Env.shape (st.env.modify (st.env.size - 1) popTop) q = some l at hs
    obtain ⟨_, hqo⟩ := mem_allPos_popTop st.env fr hfr hn hne (mem_allPos_of_shape hs)
    rw [shape_popTop_ne st.env fr hfr q hqo] at hs
    rw [hshe]
    exact hr.sim.2.1 q l hq hs
  · -- holders at bindings, reference to checker
    intro q l' hq hs
    rw [hshe] at hs
    obtain ⟨l, h1, h2⟩ := hr.sim.2.2.1 q l' hq hs
    have hqo : q ≠ .bind (st.env.size - 1) (fr.binds.size - 1) := by
      rintro rfl; change Env.shape st.env _ = _ at h1; rw [hvsh] at h1; cases h1
    refine ⟨l, ?_, h2⟩
    show Env.shape (st.env.modify (st.env.size - 1) popTop) q = some l
    rw [shape_popTop_ne st.env fr hfr q hqo]; exact h1
  · -- borrows in flight, checker to reference
    intro f i l hs
    have hqo : Pos.temp f i ≠ .bind (st.env.size - 1) (fr.binds.size - 1) := by intro e; cases e
    change Env.shape (st.env.modify (st.env.size - 1) popTop) (.temp f i) = some l at hs
    rw [shape_popTop_ne st.env fr hfr _ hqo] at hs
    obtain ⟨j, hj, hjv⟩ := hr.sim.2.2.2.1 f i l hs
    refine ⟨j, by rw [hshe]; exact hj, fun ψ hψ => ?_⟩
    show Env.mean K.dm K.M K.Γ ρ _ (st.env.modify (st.env.size - 1) popTop) (.temp f i) =
      s.dropLast.valAt (.temp f j) ψ
    rw [mean_popTop_ne K.dm K.M K.Γ ρ st.env fr hfr _ _ hqo, valAt_dropLast_ne s frs hfrs _ (by intro e; cases e)]
    exact hjv ψ (hF ψ hψ)
  · -- borrows in flight, reference to checker
    intro f j l' hs
    rw [hshe] at hs
    obtain ⟨i, l, h1, h2⟩ := hr.sim.2.2.2.2 f j l' hs
    refine ⟨i, l, ?_, h2⟩
    show Env.shape (st.env.modify (st.env.size - 1) popTop) (.temp f i) = some l
    rw [shape_popTop_ne st.env fr hfr _ (by intro e; cases e)]; exact h1
  · -- inj
    intro l l' hl hl' hπ
    have hl1 : liveLoan (Env.popBindE st.env) l = true := hl
    have hl2 : liveLoan (Env.popBindE st.env) l' = true := hl'
    rw [hlv] at hl1 hl2
    exact hr.inj l l' hl1 hl2 hπ
  · -- sites
    intro l hl x
    have hl1 : liveLoan (Env.popBindE st.env) l = true := hl
    rw [hlv] at hl1
    show x ∈ s.lent (π l) ↔ x ∈ Env.sitesOf (Env.popBindE st.env) l
    rw [hst]
    exact hr.sites l hl1 x
  · -- holders
    intro q l hs
    rw [hshe] at hs
    obtain ⟨A, B, h1, h2⟩ := positions_dropLast' s frs hfrs hn'
    have hq := hr.holders q l hs
    rw [h1, List.mem_append, List.mem_cons] at hq
    rw [h2]
    rcases hq with hq | rfl | hq
    · exact List.mem_append_left _ hq
    · rw [hsh] at hs; cases hs
    · exact List.mem_append_right _ hq
  · -- records
    intro l hl
    rw [hhty]
    exact hr.records l ((hlive l).mp hl)

/-- **(P2, with WF15's clause) The top binding popped, where it holds no borrow and no loan, keeps
the relation**, when no closure in its value records a declared type holding a loan or a mark (the
clause of (WF15) for this value, `WF15 st.env` at it): P2's hypotheses plus that one. -/
theorem rel_popBind_rd {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (fr : Frame) (b : Binding) (hfr : st.env[st.env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) (hnl : b.val.loans = []) (hnb : ∀ l, b.val.holdsBorrow l = false)
    (hrd : ∀ l, b.val.anyAtom (Value.rdLoan l) = false) :
    Rel K ρ φ π { st with env := Env.popBindE st.env } s.dropLast :=
  rel_popBind_noSites hr fr b hfr hb
    (fun l => sitesOf_nil_of_hasLoan l _ [] b.val (hasLoan_false_of_loans_nil hnl l (hrd l))) hnb

/-- **(P3) A `let`'s lenders, where nothing is lent at its binding**: the reference's end of the
borrows lent at the top binding does nothing when no live label is lent there. -/
theorem letLenders_noop {s : SState} (fr : SFrame) (hfr : s.env.getLast? = some fr)
    (h : ∀ l ∈ s.liveLabels, ∀ x ∈ s.lent l, x.pos ≠ .bind s.topIdx (fr.binds.length - 1)) :
    letLenders s = s := by
  unfold letLenders
  rw [hfr]
  dsimp only
  have hstep : (s.liveLabels.filter (s.reached (.bind s.topIdx (fr.binds.length - 1)) (dataHit []))).foldl
      SState.endLabel s = s := by
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    intro l hl
    simp only [SState.reached, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro x hx hpos
    exact absurd hpos (h l hl x hx)
  unfold SState.access
  dsimp only
  generalize List.range s.liveLabels.length = L
  induction L with
  | nil => rfl
  | cons _ L ih => rw [List.foldl_cons, hstep, ih]

/-- **(P4) The unknowns a state names, against another's**: a state with the same records, goal and Δ
whose values name only unknowns some value of the other names, and whose bindings' stored and
deferred types name only unknowns the other names, names only what the other names (read off the
kernel). -/
theorem refd_sub {st st' : MState} (hg : st'.goal = st.goal) (hn : st'.neutrals = st.neutrals)
    (he : st'.etaRefs = st.etaRefs) (ha : st'.absTy = st.absTy)
    (hv : ∀ w ∈ Env.values st'.env, ∀ σ, w.hasAbs σ = true → ∃ w' ∈ Env.values st.env, w'.hasAbs σ = true)
    (hty : ∀ (f i : Nat) (b : Binding) (T : Value) (σ : Nat), st'.env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b → b.ty = some T →
      T.hasAbs σ = true → st.norm.Refd σ)
    (hlz : ∀ (f i : Nat) (b : Binding) (P : Value) (ws : List Value) (j σ : Nat), st'.env[f]?.bind (fun fr : Frame => fr.binds[i]?) = some b →
      b.lazyTy = some (P, ws, j) → (P.hasAbs σ = true ∨ ∃ w ∈ ws, w.hasAbs σ = true) → st.norm.Refd σ) :
    ∀ σ, st'.norm.Refd σ → st.norm.Refd σ := by
  have hb : ∀ (m : MState) (f i : Nat), m.norm.env[f]?.bind (fun fr : Frame => fr.binds[i]?) =
      m.env[f]?.bind (fun fr : Frame => fr.binds[i]?) := fun m f i => by
    show m.env.erase[f]?.bind _ = _
    rw [Env.erase_get?]; cases m.env[f]? <;> rfl
  intro σ h
  induction h with
  | val w hw hab =>
    have hw' : w ∈ Env.values st'.env := by rw [← values_erase]; exact hw
    obtain ⟨w', hw'', hab'⟩ := hv w hw' _ hab
    exact .val w' (show w' ∈ Env.values st.env.erase by rw [values_erase]; exact hw'') hab'
  | ty f i b T hb' hT hab => exact hty f i b T _ (by rw [← hb]; exact hb') hT hab
  | lazyTy f i b P ws j hb' hT hab => exact hlz f i b P ws j _ (by rw [← hb]; exact hb') hT hab
  | goal G hG hab => exact .goal G (show st.goal = some G by rw [← hg]; exact hG) hab
  | neutral n σ' hm hab => exact .neutral n σ' (show (n, σ') ∈ st.neutrals by rw [← hn]; exact hm) hab
  | eta σ' w hm hab => exact .eta σ' w (show (σ', w) ∈ st.etaRefs by rw [← he]; exact hm) hab
  | dep σ' T _ hT hab ih => exact .dep σ' T ih (show st.absTy[σ']? = some T by rw [← ha]; exact hT) hab

end Ochr.Meaning.Steps.Form
