import Ochr.Meaning.Steps.Machine.EvalInv

/-!
# `evalCore`'s steps of the column, inverted (the machine lane)

Each fact here inverts one case of `Machine.evalCore` (unfolded with `unfold`, the prefix `tick`,
`curTail`, `wanted` peeled, then the case's own code stated by `change`: the definitional unfolding
of the `match` on a known term) into its sub-runs, with what lies between them: the kernel kept
(`Kern`), the mode kept (`ModeEq`), or a private computation's quiet exit (`Quiet`: a comparison,
D103, `quiet_conv`).

Statements in the proposed form (`…R`) differ from the lead's `FormMachine` where the lead's is not
provable from the checker's code alone (reported): see each docstring.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem runs_wanted_inv {st st' : MState} {b : Nat} {w : Bool} (h : Runs wanted st b w st') :
    w = st.wantHere ∧ st' = st := by
  unfold wanted at h
  peel h
  exact runs_pure_inv h

theorem Quiet.refl (st : MState) : Quiet st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_conv (n : Nat) (v w : Value) : GrowsM (Ochr.conv n v w) :=
  growsM_of_growsIn fun _ => (machineGrows n).conv v w

/-- **A comparison is quiet** (D103): `conv` puts back the state it started from, keeping only the
names made inside (`restoreNames`). -/
theorem quiet_conv {n : Nat} {v w : Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (Ochr.conv n v w) st b r st') : Quiet st st' := by
  have hg := Runs.grows (grows_conv _ _ _) h
  cases n with
  | zero => unfold Ochr.conv at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.conv.eq_1] at h
    obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
    clear h
    unfold restoreNames at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨-, rfl⟩ := runs_pure_inv h₂
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.nextLoan, ?_, ?_⟩
    · simp
    · intro σ hσ
      simp only [Array.getElem?_append_left hσ]

theorem quiet_expectTy {n : Nat} {w : String} {T : Option Value} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w T A) st b () st') : Quiet st st' := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.expectTy at h
    peel h
    split at h
    · obtain ⟨c, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
      have hq := quiet_conv hc
      split at h₂ <;> first
        | exact (runs_err_false h₂).elim
        | (obtain ⟨-, rfl⟩ := runs_pure_inv h₂; exact hq)
    · obtain ⟨-, rfl⟩ := runs_pure_inv h; exact Quiet.refl _

theorem quiet_modeEq_conv {n : Nat} {v w : Value} {st st' : MState} {b : Nat} {r : Bool}
    (h : Runs (Ochr.conv n v w) st b r st') : ModeEq st st' := by
  cases n with
  | zero => unfold Ochr.conv at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    rw [Ochr.conv.eq_1] at h
    obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
    clear h
    unfold restoreNames at h₂
    rw [runs_modify_bind] at h₂
    obtain ⟨-, rfl⟩ := runs_pure_inv h₂
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem expectTy_inv {n : Nat} {w : String} {T : Option Value} {A : Value} {st st' : MState} {b : Nat}
    (h : Runs (Ochr.expectTy n w T A) st b () st') : Quiet st st' ∧ ModeEq st st' := by
  cases n with
  | zero => unfold Ochr.expectTy at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.expectTy at h
    peel h
    split at h
    · obtain ⟨c, s₁, b₁, hc, h₂⟩ := Runs.bind_inv h
      have hq := quiet_conv hc
      have hm := quiet_modeEq_conv hc
      split at h₂ <;> first
        | exact (runs_err_false h₂).elim
        | (obtain ⟨-, rfl⟩ := runs_pure_inv h₂; exact ⟨hq, hm⟩)
    · obtain ⟨-, rfl⟩ := runs_pure_inv h; exact ⟨Quiet.refl _, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **`SuccInv` in the proposed form**: as the lead's, the typed clause stating the check of `u`'s
type as the checker runs it (`expectTy … T₀ …`, `T₀` the type `u`'s run returned) rather than
asserting `T₀ = some T` (a typed `eval` returns `some` for every term only by a whole-checker fact). -/
def SuccInvR : Prop :=
  ∀ (n : Nat) (typed : Bool) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    Mode st → st.tailNext = false → st.tailDecl = none →
    Runs (Ochr.evalCore (n + 1) typed (.succ u) hint) st bh (v, T?) st' →
    ∃ (st₀ st₁ : MState) (v₀ : Value) (T₀ : Option Value) (bh₁ : Nat), Kern st st₀ ∧ Mode st₀ ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ Runs (Ochr.eval n typed u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      v = .succ v₀ ∧ T? = some .tNat ∧ Quiet st₁ st' ∧ ModeEq st₁ st' ∧ (∀ D, DecTab D st' → DecTab D st₁) ∧
      (typed = true → ∃ (st₂ : MState) (bh₂ : Nat),
        Runs (Ochr.expectTy n "the argument of S" T₀ .tNat) st₁ bh₂ () st₂ ∧ Kern st₂ st')

set_option maxHeartbeats 4000000 in
theorem succInvR : SuccInvR := by
  intro n typed u hint st st' bh v T? hm htn htd h
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨w, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨-, rfl⟩ := runs_wanted_inv hw
  change Runs (do
    let (v, T) ← Ochr.eval n typed u
    if typed then Ochr.expectTy n "the argument of S" T .tNat
    pure (Value.succ v, some Value.tNat)) _ _ _ _ at h
  obtain ⟨⟨v₀, T₀⟩, s₂, b₃, he, h₂⟩ := Runs.bind_inv h
  clear h
  cases typed with
  | false =>
    simp only [if_false, Bool.false_eq_true] at h₂
    peel h₂
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₂
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    exact ⟨_, _, v₀, T₀, _, Kern.rfl' _, hm, htn, htd, he, rfl, rfl, Quiet.refl _, ⟨rfl, rfl, rfl, rfl⟩,
      fun _ hd => hd, fun e => by cases e⟩
  | true =>
    simp only [if_true] at h₂
    obtain ⟨_, s₃, b₄, hx, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨hvt, rfl⟩ := runs_pure_inv h₃
    simp only [Prod.mk.injEq] at hvt
    obtain ⟨rfl, rfl⟩ := hvt
    obtain ⟨hq, hme⟩ := expectTy_inv hx
    exact ⟨_, _, v₀, T₀, _, Kern.rfl' _, hm, htn, htd, he, rfl, rfl, hq, hme,
      fun _ hd => DecTab.back hd (Runs.grows (grows_expectTy _ _ _ _) hx), fun _ => ⟨_, _, hx, Kern.rfl' _⟩⟩

/-! ## `let` -/

mutual
theorem DeclInfo.beq_refl : ∀ d : DeclInfo, d.beq d = true
  | .sort l => by simp [DeclInfo.beq]
  | .prop | .unit | .other | .any | .conflict => by simp [DeclInfo.beq]
  | .pi a | .ref a => by simp [DeclInfo.beq, DeclInfo.beq_refl a]
  | .ind n as => by simp [DeclInfo.beq, DeclInfo.beqList_refl as]
  | .alt as => by simp [DeclInfo.beq, DeclInfo.beqList_refl as]
theorem DeclInfo.beqList_refl : ∀ as : List DeclInfo, DeclInfo.beqList as as = true
  | [] => by simp [DeclInfo.beqList]
  | a :: as => by simp [DeclInfo.beqList, DeclInfo.beq_refl a, DeclInfo.beqList_refl as]
end

theorem runs_refineDecl_inv {d d' : DeclInfo} {st st' : MState} {b : Nat}
    (h : Runs (refineDecl d) st b d' st') : d' = d ∧ st' = st := by
  unfold refineDecl at h
  peel h
  split at h
  · simp only [runs_err_bind] at h
  · exact runs_pure_inv h

theorem runs_getFlags_inv {st st' : MState} {b : Nat} {f : Bool × Bool}
    (h : Runs getFlags st b f st') : f = (st.lastErased, st.lastProof) ∧ st' = st := by
  unfold getFlags at h
  peel h
  exact runs_pure_inv h

theorem runs_pushBind_inv {x : Hint} {T : Option Value} {v : Value} {p : Bool} {d : DeclInfo} {st st' : MState}
    {b : Nat} (h : Runs (pushBind x T v p d) st b () st') :
    st' = { st with env := Env.pushBindE st.env x T v p d } := by
  obtain ⟨L, l, log, h⟩ := h
  have e : runMachineL (pushBind x T v p d) st b L = (.ok () { st with env := Env.pushBindE st.env x T v p d }, b, L) :=
    rfl
  rw [e] at h
  simp only [Prod.mk.injEq, Outcome.ok.injEq] at h
  exact h.1.2.symm

theorem runs_pushTemp_inv {v : Value} {T : Option Value} {site : String} {st st' : MState} {b : Nat}
    (h : Runs (pushTemp v T site) st b () st') : st' = st.withTempT v T := by
  unfold pushTemp notePush at h
  peel h
  split at h <;> peel h <;> (unfold modifyFrame topIdx at h; peel h; exact (runs_pure_inv h).2)

/-- The top frame's temporaries popped (`popTemp`'s environment). -/
def _root_.Ochr.Env.popTempE (env : Env) : Env :=
  env.modify (env.size - 1) fun fr => { fr with temps := fr.temps.pop, tempTys := fr.tempTys.pop }

theorem runs_popTemp_inv {st st' : MState} {b : Nat} {v : Value} (h : Runs popTemp st b v st') :
    (st.env[st.env.size - 1]!).temps.back? = some v ∧ st' = { st with env := Env.popTempE st.env } := by
  unfold popTemp topIdx at h
  peel h
  split at h
  · rename_i v' hv
    unfold modifyFrame at h
    peel h
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hv, rfl⟩
  · simp only [runs_err_iff] at h

/-- Popping the top temporary and pushing it back changes only the stored types, which the kernel
does not read. -/
theorem kern_popTemp_withTempT (st : MState) (v : Value) (T? : Option Value)
    (hb : (st.env[st.env.size - 1]!).temps.back? = some v) :
    Kern st ({ st with env := Env.popTempE st.env }.withTempT v T?) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [MState.withTempT, Env.popTempE, Env.erase, Array.size_modify]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_modify]
    split
    · rename_i hj
      subst hj
      have hlt : st.env.size - 1 < st.env.size := by simpa using h2
      rw [getElem!_pos st.env _ hlt] at hb
      obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
      simp only [Frame.erase, hys, Array.pop_push]
    · rfl

theorem grows_evalCore (n : Nat) (typed : Bool) (t : Term) (hint : Option Value) :
    GrowsM (Ochr.evalCore n typed t hint) := growsM_of_growsIn fun _ => (machineGrows n).evalCore typed t hint

theorem grows_dropTopBind (n : Nat) : GrowsM (Ochr.dropTopBind n) :=
  growsM_of_growsIn fun _ => (machineGrows n).dropTopBind

theorem TablesGrow.of_kern {a b : MState} (h : Kern a b) : TablesGrow a b :=
  ⟨h.globals.symm, h.inds.symm, by rw [h.absDecl]; exact Nat.le_refl _, fun _ _ => by rw [h.absDecl],
    by rw [h.nextAbs]; exact Nat.le_refl _, by rw [h.nextLoan]; exact Nat.le_refl _⟩

theorem TablesGrow.of_fields {a b : MState} (h1 : b.globals = a.globals) (h2 : b.inds = a.inds)
    (h3 : b.absDecl = a.absDecl) (h4 : b.nextAbs = a.nextAbs) (h5 : b.nextLoan = a.nextLoan) : TablesGrow a b :=
  ⟨h1, h2, by rw [h3]; exact Nat.le_refl _, fun _ _ => by rw [h3], by rw [h4]; exact Nat.le_refl _,
    by rw [h5]; exact Nat.le_refl _⟩

theorem TablesGrow.withTempT (st : MState) (v : Value) (T? : Option Value) : TablesGrow st (st.withTempT v T?) :=
  ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- **`LetInv` in the proposed form**: as the lead's, with `u`'s type `T₀` as its run returned it (an
`Option`; that a typed `eval` returns `some` is a whole-checker fact), the binding's reading `du`
read where the checker reads it, at the ENTRY (`evalCore` reads it before evaluating `u`), the mode
after `u` carried to the body's entry and from the drop to the end (`ModeEq`), and the invariant's
clause and `0 < st₁.env.size` left to the caller (the column has both from its own sub-steps). -/
def LetInvR : Prop :=
  ∀ (n : Nat) (h : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (D : Decisions),
    Mode st → st.tailNext = false → st.tailDecl = none → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) true (.letIn h u w) hint) st bh (v, T?) st' →
    ∃ (du : DeclInfo) (st₀ st₁ stB st₂ st₃ : MState) (v₀ r : Value) (T₀ : Option Value) (p : Bool)
      (bh₁ bh₂ bh₃ : Nat),
      Kern st st₀ ∧ Mode st₀ ∧ st₀.tailNext = false ∧ st₀.tailDecl = none ∧ stB.tailDecl = st.curDecl ∧
      Runs (Ochr.eval n true u none) st₀ bh₁ (v₀, T₀) st₁ ∧
      D.declOf (DecideScope.topReadings st) u = du ∧
      Kern { st₁ with env := Env.pushBindE st₁.env h T₀ v₀ p du } stB ∧ ModeEq st₁ stB ∧
      stB.tailNext = st.curTail ∧
      Runs (Ochr.eval n true w none) stB bh₂ (r, T?) st₂ ∧
      Runs (Ochr.dropTopBind n) (st₂.withTempT r T?) bh₃ () st₃ ∧
      Kern st₃ (st'.withTempT v T?) ∧ ModeEq st₃ st' ∧
      DecTab D st₁ ∧ DecTab D st₂

set_option maxHeartbeats 4000000 in
theorem letInvR : LetInvR := by
  intro n x u w hint st st' bh v T? D hm htn htd hD h
  have hDst : DecTab D st := DecTab.back hD (Runs.grows (grows_evalCore _ _ _ _) h)
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨hw1, hw2⟩ := runs_wanted_inv hw
  subst hw1 hw2
  simp only [Term.placeOperand?] at h
  rw [runs_get_bind] at h
  obtain ⟨du, s₂, b₃, hdu, h₁⟩ := Runs.bind_inv h
  clear h
  have hs2 := runs_keep (keep_withLive _ ((decideKeep n).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdu
  subst hs2
  unfold demand at h₁
  rw [runs_modify_bind] at h₁
  rw [if_neg (by simp)] at h₁
  peel h₁
  obtain ⟨⟨v₀, T₀⟩, s₃, b₄, hu, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  peel h₂
  obtain ⟨du', s₄, b₅, hrd, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  obtain ⟨rfl, rfl⟩ := runs_refineDecl_inv hrd
  obtain ⟨fl, s₅, b₆, hgf, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
  obtain ⟨_, s₆, b₇, hpb, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  have hs6 := runs_pushBind_inv hpb
  subst hs6
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false] at h₅
  rw [if_pos (by simp [BEq.beq, DeclInfo.beq_refl])] at h₅
  peel h₅
  simp only [Bool.true_or, if_true, ite_true] at h₅
  obtain ⟨⟨r, R⟩, s₇, b₈, hw', h₆⟩ := Runs.bind_inv h₅
  clear h₅
  obtain ⟨fl, s₈, b₉, hgf, h₇⟩ := Runs.bind_inv h₆
  clear h₆
  obtain ⟨rfl, rfl⟩ := runs_getFlags_inv hgf
  obtain ⟨_, s₉, b₁₀, hpt, h₈⟩ := Runs.bind_inv h₇
  clear h₇
  have hs9 := runs_pushTemp_inv hpt
  subst hs9
  obtain ⟨⟨⟩, s₁₀, b₁₁, hdr, h₉⟩ := Runs.bind_inv h₈
  clear h₈
  unfold setFlags at h₉
  rw [runs_modify_bind] at h₉
  obtain ⟨pv, s₁₁, b₁₂, hpop, h₁₀⟩ := Runs.bind_inv h₉
  clear h₉
  obtain ⟨hvt, rfl⟩ := runs_pure_inv h₁₀
  simp only [Prod.mk.injEq] at hvt
  obtain ⟨rfl, rfl⟩ := hvt
  obtain ⟨hback, rfl⟩ := runs_popTemp_inv hpop
  have hg₂ := (TablesGrow.withTempT _ _ _).trans (Runs.grows (grows_dropTopBind _) hdr)
  have hk3 := kern_popTemp_withTempT _ _ T? hback
  refine ⟨du', { s₂ with wantTy := true }, s₃,
    { s₃ with env := Env.pushBindE s₃.env x T₀ v₀ (s₃.lastProof || du'.isProof) du', deferCallTy := false, callTyLater := none, tailDecl := s₂.curDecl, wantTy := s₂.wantHere, tailNext := s₂.curTail },
    s₈, s₁₀, v₀, r, T₀, s₃.lastProof || du'.isProof, b₃, b₇, b₁₀, ?_, ?_, htn, htd, rfl, hu, ?_, ?_, ?_, rfl, hw',
    hdr, ?_, ?_, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨hm.headEval, hm.copying, hm.inPlace, hm.erased⟩
  · exact decTab_declOf_at hDst hdu
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact Kern.trans (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hk3
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact DecTab.back hD (TablesGrow.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl))
      ((Runs.grows (grows_eval _ _ _ _) hw').trans (hg₂.trans
        (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))))
  · exact DecTab.back hD (hg₂.trans (TablesGrow.of_fields (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)))

end Ochr.Meaning.Steps.Machine
