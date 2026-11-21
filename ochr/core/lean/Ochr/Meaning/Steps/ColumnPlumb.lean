import Ochr.Meaning.Steps.ColumnTemp

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
theorem rel_pushBind_num {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState}
    {s : SState} (hr : Rel K ρ φ π st s) (hne : 0 < st.env.size) (h : Hint) (T : Value) {v : Value}
    (hv : v.Num) (p : Bool) (d : DeclInfo) (R : TyS) (hR : (Value.tyS K.dm K.M K.Γ ρ T).m = R.m) (c : Sem)
    (hc : ∀ (φ' : Future) (hint : TyS), Value.mean K.dm K.M K.Γ ρ φ' hint v = c) :
    Rel K ρ φ π { st with env := Env.pushBindE st.env h (some T) v p d }
      (s.pushBind { ty := R, val := fun _ => c, decl := d }) := by
  sorry

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

/-- **(P2) The top binding popped, where it holds no borrow and no loan, keeps the relation**: the
checker pops it, the reference drops its last binding (`SState.dropLast`). -/
theorem rel_popBind {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    (hr : Rel K ρ φ π st s) (fr : Frame) (b : Binding) (hfr : st.env[st.env.size - 1]? = some fr)
    (hb : fr.binds.back? = some b) (hnl : b.val.loans = []) (hnb : ∀ l, b.val.holdsBorrow l = false) :
    Rel K ρ φ π { st with env := Env.popBindE st.env } s.dropLast := by
  sorry

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
