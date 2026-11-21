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
