import Ochr.Meaning.Steps.ColumnQRun

/-!
# The column `Q`: the match run directly, and the closed-off block's meaning (lead18, 2026-11-21; docs/31 D137)

`runMatchQ`: the reference's run of the match NOT in tail position ([Entry], one arm, the join) from every state
reading like `Q`'s start (`ColumnP.RefP`). `mean_vQ`: the meaning of the checker's sealed block `⌈anonQ(σ0)⌉` is the
result of calling the closure `anonQ` means at `ρ σ0`, and that call runs `matchQ` in tail position in the closure's
frame (`FrameJ2.closureJ2`), which `ColumnP.runP` computes. Both give `ρ σ0 - 1`.
-/

namespace Ochr.Meaning.Steps.Form.ColumnQ

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (piNat nB psI outI selfTy selfSem)
open Ochr.Meaning.Steps.Form.ColumnP (RI pn0 ParDecP RefJ RefP dropN setN0 nBot)

/-! ## The match, run directly -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {g : Sem} {s : SState}

/-- The join's drop of `n` after the arm's move of `n.0` leaves what the drop alone leaves: `n` moved. -/
theorem dropN_setN0 (K : RunCtx) (s : SState) : dropN K (setN0 K s) = dropN K s := by
  unfold dropN setN0
  have hv : ∀ (s' : SState), (fun φ' => (Sem.updAt K.dm K.Γ (s'.tyAt (.bind 1 1)) (fun _ => Sem.moved) []
      (s'.valAt (.bind 1 1) φ')).getD .err) = fun _ => Sem.moved := fun s' => by
    funext φ'; rw [Sem.updAt.eq_def]; rfl
  rw [hv, hv]
  simp only [SState.setAt, List.modify_modify_eq]
  congr 2
  funext fr
  simp only [Function.comp_apply, List.modify_modify_eq]
  rfl

/-- **[Entry] at `Q`'s match** (not in tail position): the captures are `n` by move (the decision `ParDecQ.caps`); its
access changes nothing on a state with no live label, its ends are strict-OK, and the lending after the arm does
nothing to a result with no label. -/
theorem entryQ (hd : ParDecQ K.D) (h : RefP ρ φ g s) (hmv : movedPlaces φ s = []) :
    optCheck (MatchEntryOk K φ true matchQ s) = some ⟨⟩ ∧ (matchEntry K φ true matchQ s).1 = s ∧
      ∀ s₂, (matchEntry K φ true matchQ s).2 none s₂ = s₂ := by
  have hbc : K.D.blockCaps (scopeOf s) (movedPlaces φ s) matchQ = ([.var 0], [(.var 0, 2)]) := by
    rw [h.scope, hmv]; exact hd.caps
  have hre : entryReroot s (.var 0) = s := by
    unfold entryReroot; rw [h.resolve0]; exact ColumnP.accessLentPrefix_nil s _
  refine ⟨?_, ?_, ?_⟩
  · unfold optCheck; rw [if_pos]; intro _
    unfold EntryAccessOk; rw [hbc]
    refine ⟨⟨?_, trivial⟩, ⟨⟨?_, ?_⟩, trivial⟩⟩
    · unfold EntryRerootOk; rw [h.resolve0]; dsimp only; unfold LentPrefixOk; rw [ColumnP.lentPrefix_nil]; trivial
    · simp only [List.foldl_cons, List.foldl_nil, hre]; rw [h.resolve0]; exact h.accessOk K φ _ _
    · intro e; cases e
  · unfold matchEntry; simp only [if_true]; unfold entryAccess; rw [hbc]
    simp only [List.foldl_cons, List.foldl_nil, hre]
    unfold entryCap; rw [h.resolve0]; dsimp only; rw [h.access]; rfl
  · intro s₂; unfold matchEntry; simp only [if_true]; split <;> rfl

/-- **The match, not in tail position, at both tags** (as `ColumnP.runP`, with [Entry] first): on `0` the arm `Z`, on
`a + 1` the arm's read of `n.0`; then the join's drop of `n`. The state after is `n` moved in both. -/
theorem runMatchQ (hd : ParDecQ K.D) (h : RefP ρ φ g s) (hg : ∀ q, Sem.movedIn g q = []) (hint : TyS) :
    (ρ 0 = .el0 Nat 0 → runT K ρ φ false hint matchQ s = some ((.el0 Nat 0, .plain TyM.nat), dropN K s)) ∧
    (∀ a, ρ 0 = .el0 Nat (a + 1) →
      runT K ρ φ false hint matchQ s = some ((.el0 Nat a, .plain TyM.nat), dropN K s)) := by
  have hfl : K.D.flags (scopeOf s) (.matchNat (.var 0) .zero (.place pn0)) = (false, false) := by
    rw [h.scope]; exact hd.p.1
  have htag : TagOk K φ (.var 0) s := by unfold TagOk; rw [h.resolve0]; exact h.accessOk K φ _ _
  have htg : ∀ k, ρ 0 = .el0 Nat k →
      SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) natTag) s = some (natTag (.el0 Nat k) (s.tyAt (.bind 1 1)), s) := by
    intro k hk
    rw [SM.guarded_of htag]; unfold tagOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, hk]; rfl
  have hj : ∀ s', RefJ s' → optCheck (JoinDropOk K φ [] (.matchNat (.var 0) .zero (.place pn0)) s') = some ⟨⟩ ∧
      joinDrop K φ [] (.matchNat (.var 0) .zero (.place pn0)) s' = dropN K s' := fun s' h' => by
    obtain ⟨hjok, hjd⟩ := ColumnP.joinP (φ := φ) hd.p h'
    exact ⟨by unfold optCheck; exact if_pos hjok, hjd⟩
  refine ⟨fun h0 => ?_, fun a h0 => ?_⟩
  · have hz : runT K ρ φ false (.plain TyM.err) .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
      rw [runT]; rfl
    have hmv := h.movedPlaces h0 hg
    obtain ⟨hme, hent1, hent2⟩ := entryQ hd h hmv
    change optCheck (MatchEntryOk K φ true (.matchNat (.var 0) .zero (.place pn0)) s) = some ⟨⟩ at hme
    change (matchEntry K φ true (.matchNat (.var 0) .zero (.place pn0)) s).1 = s at hent1
    change ∀ s₂, (matchEntry K φ true (.matchNat (.var 0) .zero (.place pn0)) s).2 none s₂ = s₂ at hent2
    have hnt : natTag (.el0 Nat 0) (s.tyAt (.bind 1 1)) = .el0 Nat 0 := by simp [natTag, Sem.asNat_el0]
    show runT K ρ φ false hint (.matchNat (.var 0) .zero (.place pn0)) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg 0 h0, hnt]
    simp only [bind, Option.bind, Bool.not_false, hme, hent1, Sem.asNat_el0, hz, hmv]
    rw [(hj s h.toRefJ).1, (hj s h.toRefJ).2]
    simp only [TyS.plain, hent2]
    rw [hme]
  · have hmv := h.movedPlaces h0 hg
    obtain ⟨hme, hent1, hent2⟩ := entryQ hd h hmv
    change optCheck (MatchEntryOk K φ true (.matchNat (.var 0) .zero (.place pn0)) s) = some ⟨⟩ at hme
    change (matchEntry K φ true (.matchNat (.var 0) .zero (.place pn0)) s).1 = s at hent1
    change ∀ s₂, (matchEntry K φ true (.matchNat (.var 0) .zero (.place pn0)) s).2 none s₂ = s₂ at hent2
    have hnt : natTag (.el0 Nat (a + 1)) (s.tyAt (.bind 1 1)) = .el0 Nat 1 := by simp [natTag, Sem.asNat_el0]
    have harm := ColumnP.runArmS (K := K) hd.p h h0 false (.plain TyM.err)
    have hj₁ : RefJ (setN0 K s) := h.toRefJ.setAt _ _
    show runT K ρ φ false hint (.matchNat (.var 0) .zero (.place pn0)) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg (a + 1) h0, hnt]
    simp only [bind, Option.bind, Bool.not_false, hme, hent1, Sem.asNat_el0, harm, hmv]
    rw [(hj _ hj₁).1, (hj _ hj₁).2, dropN_setN0]
    simp only [TyS.plain, hent2]
    rw [hme]

/-- **`Q`'s body, run directly**: `S(ρ σ0 - 1)` at `Nat`, `n` moved. -/
theorem runBodyQ (hd : ParDecQ K.D) (h : RefP ρ φ g s) (hg : ∀ q, Sem.movedIn g q = []) (tl : Bool) (hint : TyS)
    {m : Nat} (h0 : ρ 0 = .el0 Nat m) :
    runT K ρ φ tl hint bodyQ s = some ((.el0 Nat (m - 1 + 1), .plain TyM.nat), dropN K s) := by
  have hfl : K.D.flags (scopeOf s) (.succ matchQ) = (false, false) := by rw [h.scope]; exact hd.flBody
  have hm : runT K ρ φ false (.plain TyM.nat) matchQ s = some ((.el0 Nat (m - 1), .plain TyM.nat), dropN K s) := by
    obtain ⟨hZ, hS⟩ := runMatchQ (K := K) hd h hg (.plain TyM.nat)
    cases m with
    | zero => exact hZ h0
    | succ a => exact hS a h0
  show runT K ρ φ tl hint (.succ matchQ) s = _
  rw [runT_succ _ _ _ s hfl]
  unfold SM.strictS
  have hb : (runT K ρ φ false (.plain TyM.nat) matchQ >>= fun x : Res => match x with
      | (v, _) => (pure (v.succ, TyS.plain TyM.nat) : SM Res)) s = some (((Sem.el0 Nat (m - 1)).succ, .plain TyM.nat), dropN K s) := by
    simp only [Bind.bind]; rw [hm]; rfl
  rw [hb]
  have hsu : (Sem.el0 Nat (m - 1)).succ = .el0 Nat (m - 1 + 1) := by rw [Sem.succ, Sem.asNat_el0]
  have hc : (Sem.el0 Nat (m - 1)).succ ∈ₛ[K.dm.read] (TyS.plain TyM.nat).m := by rw [hsu]; exact ⟨m - 1 + 1, rfl⟩
  dsimp only; rw [if_pos hc, hsu]

end

/-! ## What the closed-off block means -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem runT_valNat (tl : Bool) (h : TyS) (s : SState) :
    runT K ρ φ tl h (.val .tNat) s = some ((.ty TyM.nat, { h with label := none }), s) := by
  unfold runT; rfl

theorem bindsOf_valNat (s : SState) (hd : K.D.paramDecls (scopeOf s) [.val .tNat] = [.other]) :
    bindsOf K ρ φ s [.val .tNat] = [(fun _ => .plain TyM.nat, .other)] := by
  unfold bindsOf; rw [hd]
  simp only [runBinds, mkBind, runT_valNat]
  rfl

theorem codOf_valNat (s : SState) (bs : List PBind) : codOf K ρ φ s bs (.val .tNat) = outI := by
  unfold codOf; simp only [run, runT_valNat]; rfl

theorem runDoms_valNat (s : SState) (hd : K.D.paramDecls (scopeOf s) [.val .tNat] = [.other]) :
    runDoms K ρ φ s [.val .tNat] = psI := by
  unfold runDoms; rw [bindsOf_valNat s hd]; rfl

/-- The binders and codomain the `.fix` clause reads the block's signature at, from the empty state. -/
noncomputable def fbA (K : RunCtx) (ρ : Assignment) (φ : Future) : List PBind × PBind :=
  (bindsOf K ρ φ (emptyState 0) [.val .tNat],
    fixCod K ρ φ (emptyState 0) (bindsOf K ρ φ (emptyState 0) [.val .tNat]) (.val .tNat),
    K.D.typeDecl (K.D.teleDecls (scopeOf (emptyState 0)) [.val .tNat]) (.val .tNat))

/-- **The block's function** (stage 1 at rank 0: the block does not recurse). -/
noncomputable def gA (K : RunCtx) (ρ : Assignment) (φ : Future) : List Sem → Option BodyOut :=
  fixG K ρ φ (fbA K ρ φ) 1 (emptyState 0) psI outI (piTyAt K.dm.read 1 psI outI) 0 none matchQ

theorem paramDecls_A (hd : ParDecQ K.D) : K.D.paramDecls (scopeOf (emptyState 0)) [.val .tNat] = [.other] := by
  show K.D.paramDecls [] [.val .tNat] = [.other]
  simp [Decisions.paramDecls, Decisions.teleDecls, hd.td0]

/-- **The block's body in its closure's frame, at every number**: `fixBodyAt` starts from `FrameJ2.closureJ2 a` (the
frame `[{}, {_ ↦ stage 0, n ↦ a}]`) and the body `matchQ` runs there in tail position (`ColumnP.runP`): `a - 1`, no
final. -/
theorem gA_run (hd : ParDecQ K.D) (a : Nat) : gA K ρ φ [.el0 Nat a] = some ⟨.el0 Nat (a - 1), [], none⟩ := by
  have h1 : (fbA K ρ φ).1 = [(fun _ => .plain TyM.nat, .other)] := bindsOf_valNat _ (paramDecls_A hd)
  have h2 : (fbA K ρ φ).2.2 = .other := by
    show K.D.typeDecl (K.D.teleDecls [] [.val .tNat]) (.val .tNat) = .other
    simp [Decisions.teleDecls, hd.td0, hd.td1]
  have hst : ([Sem.el0 Nat a].zip psI).foldl (fixStep (fbA K ρ φ))
      ((emptyState 0).under.pushBind { ty := .plain (selfTy K.dm.read), val := fun _ => selfSem K.dm.read φ, decl := .pi (fbA K ρ φ).2.2 }, [], []) = (FrameJ2.closureJ2 K.dm.read φ a, [.el0 Nat a], []) := by
    simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
      Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append]
    rfl
  have hP := CallJ2.refP_closureJ2 K.dm.read φ a
  obtain ⟨hZ, hS⟩ := ColumnP.runP (K := K) hd.p hP (ColumnP.movedIn_selfSem K.dm.read φ) ((fbA K ρ φ).2.1 [.el0 Nat a])
  have hl : ∀ s', (s' = dropN K (FrameJ2.closureJ2 K.dm.read φ a) ∨ s' = dropN K (setN0 K (FrameJ2.closureJ2 K.dm.read φ a))) →
      s'.liveLabels = [] := by
    intro s' hs'
    have hc : (FrameJ2.closureJ2 K.dm.read φ a).liveLabels = [] := hP.live
    rcases hs' with rfl | rfl
    · unfold dropN; rw [Strict.liveLabels_setAt]; exact hc
    · unfold dropN; rw [Strict.liveLabels_setAt]; unfold setN0; rw [Strict.liveLabels_setAt]; exact hc
  show fixBodyAt K ρ φ (fbA K ρ φ) (emptyState 0) psI outI (selfTy K.dm.read) 0 matchQ (selfSem K.dm.read φ) [.el0 Nat a] = _
  unfold fixBodyAt
  dsimp only
  rw [hst]
  dsimp only
  rw [ColumnP.runT_bodyP K ρ (fun _ => .el0 Nat a) ((fbA K ρ φ).2.1 [.el0 Nat a]) ((fbA K ρ φ).2.1 [.el0 Nat a])]
  cases a with
  | zero =>
    rw [hZ rfl]; dsimp only; rw [hl _ (.inl rfl)]
    simp [ColumnI.endsOk_nil]
    rfl
  | succ a =>
    rw [hS a rfl]; dsimp only; rw [hl _ (.inr rfl)]
    simp [ColumnI.endsOk_nil]
    rfl

theorem gA_tot (hd : ParDecQ K.D) :
    ∀ args, DomMembers K.dm.read psI args →
      ∃ o, gA K ρ φ args = some o ∧ OutGood K.dm.read psI outI args o ∧ o.finals.length = (psI.filter (·.isRef)).length := by
  intro args ha
  obtain ⟨m, rfl⟩ := ColumnR.domMembers_one ha
  refine ⟨_, gA_run hd m, ⟨⟨m - 1, rfl⟩, fun i d hi hd' => ?_⟩, rfl⟩
  rcases i with _ | i
  · simp [psI] at hi; subst hi; cases hd'
  · simp [psI] at hi

/-- The block's closure is a member of `Π(n : Nat). Nat`. -/
theorem gA_mem (hd : ParDecQ K.D) : closureAt K.dm.read 1 φ psI outI (gA K ρ φ) ∈ₛ[K.dm.read] piTyAt K.dm.read 1 psI outI :=
  closure_mem_of_total' K.dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1) (gA_tot hd)

theorem gA_ne_err (hd : ParDecQ K.D) : closureAt K.dm.read 1 φ psI outI (gA K ρ φ) ≠ .err := by
  have hm := gA_mem (ρ := ρ) (φ := φ) hd
  revert hm
  show closureL (lvl0 K.dm.read) φ (telL (lvl0 K.dm.read) psI [] PUnit outI).2 _ ∈ₛ[K.dm.read] _ →
    closureL (lvl0 K.dm.read) φ (telL (lvl0 K.dm.read) psI [] PUnit outI).2 _ ≠ .err
  unfold closureL
  split
  · intro _ e; simp [lvl0] at e
  · intro h; exact absurd h (ClosureCE.err_not_mem_pi K.dm.read _ _)

/-- **The block's code means its closure**: `anonQ`'s `.fix`, run from the empty state, forms the closure of `gA`, a
member of `Π(n : Nat). Nat`, and leaves the state as it was. -/
theorem runT_anonFix (hd : ParDecQ K.D) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint anonFix (emptyState 0) =
      some ((closureAt K.dm.read 1 φ psI outI (gA K ρ φ), .plain (piTyAt K.dm.read 1 psI outI)), emptyState 0) := by
  have hpd := paramDecls_A (K := K) hd
  have hsort : fixSort K (emptyState 0) [⟨"n"⟩] [.val .tNat] (.val .tNat) = 1 := hd.srt
  have hty : fixTy K ρ φ (emptyState 0) [⟨"n"⟩] [.val .tNat] (.val .tNat) = piTyAt K.dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, runDoms_valNat _ hpd, codOf_valNat]
  have hclo : fixClo K ρ φ (emptyState 0) [⟨"n"⟩] [.val .tNat] (.val .tNat) none matchQ =
      closureAt K.dm.read 1 φ psI outI (gA K ρ φ) := by
    unfold fixClo
    rw [hty, hsort, runDoms_valNat _ hpd, codOf_valNat]
    rfl
  have hrun := run_fix_of_mem (K := K) (ρ := ρ) (φ := φ) tl hint ⟨"_"⟩ [⟨"n"⟩] [.val .tNat] (.val .tNat) none matchQ
    (emptyState 0) hd.flFix (by rw [show capOrder (.fix ⟨"_"⟩ [⟨"n"⟩] [.val .tNat] (.val .tNat) none matchQ) = [] from rfl]; trivial)
    (by rw [hty, hclo]; exact gA_mem hd)
  show runT K ρ φ tl hint (.fix ⟨"_"⟩ [⟨"n"⟩] [.val .tNat] (.val .tNat) none matchQ) (emptyState 0) = _
  rw [hrun, hclo, hty]
  rfl

/-- **The call `anonQ(a)`**, at any number `a` (of any recorded type): `a - 1` at `Nat`, the state as it was. -/
theorem callOf_A (hd : ParDecQ K.D) (a : Nat) (T : TyS) (hT : T.label = none) (s : SState) :
    callOf K.dm.read (closureAt K.dm.read 1 φ psI outI (gA K ρ φ), .plain (piTyAt K.dm.read 1 psI outI)) [(.el0 Nat a, T)] s =
      some ((.el0 Nat (a - 1), .plain TyM.nat), s) := by
  obtain ⟨s', hs'⟩ := closure_apply' K.dm.read 1 φ psI outI (gA K ρ φ) ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) (gA_tot hd) [(.el0 Nat a, T)] s ⟨.el0 Nat (a - 1), [], none⟩
    (ColumnR.domMembers_nat K.dm.read a)
    (fun i d hd' => by rcases i with _ | i <;> simp [psI] at hd'; subst hd'; exact Nat.le_refl 1)
    trivial (gA_run hd a)
  have hss : s' = s := ColumnJ.callOf_unlabelled_state _ _ _ _ _ _ hs' (fun a ha => by simp at ha; subst ha; exact hT) rfl
  subst hss
  exact hs'

/-- **What the block's closure value means** (docs/31 D137, after ruling (A): `CapsOk` reads the captures against the
first `caps.length` readings only; the block's parameter reading in `rd` is not a capture's): the closure of `gA`. Before
the ruling this was `err` (`CapsOk [] [_]` was `False`): every closed-off block that took a place meant `err`. -/
theorem meanV_anonQ (hd : ParDecQ K.D) (hint : TyS) :
    meanV K ρ φ hint anonQ = closureAt K.dm.read 1 φ psI outI (gA K ρ φ) := by
  show meanV K ρ φ hint (.clo [] anonFix [(.other, .tNat)]) = _
  rw [meanV, if_pos (by exact trivial)]
  have hs0 : stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ [(.other, .tNat)])) = emptyState 0 := rfl
  rw [hs0, runT_anonFix hd]

/-- **The sealed block's run**: the call of the closure `anonQ` means, at `ρ σ0`. -/
theorem runT_sealQ (hd : ParDecQ K.D) (h : TyS) {m : Nat} (h0 : ρ 0 = .el0 Nat m) :
    runT K ρ φ false h sealQ (emptyState 0) = some ((.el0 Nat (m - 1), .plain TyM.nat), emptyState 0) := by
  have h1 : runT K ρ φ false (TyS.plain TyM.err) (Term.val anonQ) (emptyState 0) =
      some ((closureAt K.dm.read 1 φ psI outI (gA K ρ φ), .plain (piTyAt K.dm.read 1 psI outI)), emptyState 0) := by
    show runT K ρ φ false (TyS.plain TyM.err) (Term.val (.clo [] anonFix [(.other, .tNat)])) (emptyState 0) = _
    unfold runT
    show strictVal K.dm.read (.clo [] anonFix [(.other, .tNat)]) (meanV K ρ φ (.plain TyM.err) anonQ, _) (emptyState 0) = _
    rw [meanV_anonQ hd]
    have hs0 : stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ [(.other, .tNat)])) = emptyState 0 := rfl
    simp only [strictVal, gA_ne_err hd, if_false, hs0, runT_anonFix hd]
    rfl
  have h2 : ∀ T, runArgs K ρ φ false T [] [Term.val (.abs 0)] (emptyState 0) =
      some ([(ρ 0, { K.Δ 0 with label := none })], emptyState 0) := by
    intro T
    rw [runArgs]
    simp only [Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false, Bind.bind]
    rw [runT]; rfl
  unfold sealQ
  rw [runT]
  simp only [show K.D.flags (scopeOf (emptyState 0)) (.call (.val anonQ) [.val (.abs 0)] true) = (false, false)
    from hd.flSeal]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [SM.headOf, Bind.bind, h1]
  rw [h2]
  dsimp only
  rw [if_pos (ColumnJ.borrowArgsTyped_unlabelled _ _ _ _ (fun a ha => by simp at ha; subst ha; rfl)), h0]
  exact callOf_A hd m _ rfl _

/-- **What the checker's closed-off block means**: `⌈anonQ(σ0)⌉` means `ρ σ0 - 1` wherever `ρ σ0` is a number, at every
hint: the reference's direct run of the match (`runMatchQ`) gives the same, at every assignment. -/
theorem mean_vQ (hd : ParDecQ K.D) (hint : TyS) {m : Nat} (h0 : ρ 0 = .el0 Nat m) :
    meanV K ρ φ hint vQ = .el0 Nat (m - 1) := by
  show (match runT K ρ φ false hint sealQ (emptyState 0) with
    | some ((v, _), _) => v
    | none => .err) = _
  rw [runT_sealQ hd hint h0]

end

end Ochr.Meaning.Steps.Form.ColumnQ
