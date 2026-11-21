import Ochr.Meaning.Lemmas
import Ochr.Meaning.Mono
import Ochr.Meaning.Locality

/-!
# CE5, flipped: a positive check for the proposed let drop (built)

`CE5_5dc7710b.lean` (unbuilt) records the leak: a root assignment `x := &y` makes `x` the holder,
the `let`'s drop ended only the label `x`'s type had carried, and `y` then read the future at the
run's own label. With the proposed drop (it ends the label the binding's position holds now),
`let y = Z; (let x = Z; x := &y); y` reads `Z` at every future (`tA_reads_zero`): the drop ends
`x`'s borrow with `x`'s content, `Z`, and nothing is left live. Axioms: propext,
Classical.choice, Quot.sound.
-/

namespace Ochr.Meaning.Regress.CE5flip
open Ochr.Meaning
open Classical

theorem filterMap_none {α β} (l : List α) : List.filterMap (fun _ => (none : Option β)) l = [] := by
  induction l <;> simp_all [List.filterMap]

theorem liveLabels_noshape (s : SState) (h : s.shape = fun _ => none) : s.liveLabels = [] := by
  simp only [SState.liveLabels, h, filterMap_none, List.mergeSort_nil]

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) (hit : List Step → Bool := fun _ => true) :
    s.access p hit = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl


section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The decisions classify no term as a statement or as erased, so `SM.erasedIf` is the run itself
(D19: every clause that can change the state runs under `Decisions.flags`). -/
def NoStmt (K : RunCtx) : Prop := ∀ sc t, K.D.flags sc t = (false, false)

/-- The decisions invalidate no place at a write or a borrow (D112; the default), so `invalidate`
is the identity. -/
def NoInv (K : RunCtx) : Prop := ∀ sc p, K.D.invalidated sc p = []

theorem invalidate_noInv (hinv : NoInv K) (p : Place) (s : SState) : invalidate K φ p s = s := by
  simp [invalidate, hinv _ _]

/-- A place that resolves to a root satisfies D112's `lentOk`. -/
theorem lentOk_root {p : Place} {s : SState} {pos : Pos} (h : resolve s p = some (pos, [])) : lentOk K φ p s := by
  simp [lentOk, h]

theorem stmtIf_noStmt (hfl : NoStmt K) (t : Term) (x : SM Res) (s : SState) :
    SM.erasedIf (K.D.flags (scopeOf s) t) x s = x s := by
  rw [hfl]; rfl

theorem run_letIn (hfl : NoStmt K) (h : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.letIn h u w) s = (run K ρ φ (.plain .err) u s).bind (fun x =>
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => y.2.endLabel l | none => letLenders y.2).dropLast)) := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

/-- The [Drop] of a discarded value that holds no borrow does nothing. -/
theorem seq_discard_plain (T : TyM) (k : SM Res) (s : SState) :
    (SM.modify (discardEnd (TyS.plain T)) >>= fun _ => k) s = k s := rfl

theorem run_seq (hfl : NoStmt K) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s =
      (run K ρ φ (.plain .err) u >>= fun r => SM.modify (discardEnd r.2) >>= fun _ => run K ρ φ hint w) s := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem run_place (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem run_borrow (hfl : NoStmt K) (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.borrow p) s = (match SM.strictS K.dm.read (borrowPlace K φ p) s with
      | some (r, s₁) =>
        let s₂ := invalidate K φ p s₁
        if lentOk K φ p s₂ then some (r, s₂) else none
      | none => none) := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = ((if ¬ v.whole then none else
      if ¬ ReadGood K.dm.read T.m v then none else
      if b then some ((v, { T with label := none }), s') else do
        let lab := if st.isEmpty then s'.shape pos else none
        let (⟨⟩, s) ← setContent K φ pos st .moved s'
        let s := match lab with
          | some l => (s.takeLabel l).pushTempShaped (fun _ => v) l
          | none => s
        some ((v, { T with label := lab }), s)) : Option (Res × SState)) := by
  show (contentOf K φ p s >>= _) = _
  rw [h]
  rfl

/-- `let y = Z; (let x = Z; x := &y); y`: `x` becomes the holder of `y`'s borrow by the
assignment, and its `let` drops it without ending it (the drop ends only the label `x`'s *type*
carried when it was bound). -/
def tA : Term :=
  .letIn ⟨"y"⟩ .zero (.seq (.letIn ⟨"x"⟩ .zero (.assign (.var 0) (.borrow (.var 1)))) (.place (.var 0)))

def yB (K : RunCtx) (n : Nat) : SBinding :=
  { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

noncomputable def xB (K : RunCtx) (n : Nat) : SBinding :=
  { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0,
    decl := K.D.declOf (scopeOf ((emptyState n).pushBind (yB K n))) .zero }

/-- `y` and `x` bound. -/
noncomputable def b1 (n : Nat) : SState := ((emptyState n).pushBind (yB K n)).pushBind (xB K n)

theorem content_b1_y (n : Nat) : contentOf K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 0, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 1) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _) _]
  rfl

theorem content_b1_x (n : Nat) : contentOf K φ (.var 0) (b1 K n) = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 1, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 0) = some (.bind 0 1, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _) _]
  rfl

theorem run_assign (hfl : NoStmt K) (p : Place) (u : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.assign p u) s = (do
      -- the right-hand side first, at the place's type read on a discarded copy; then the access
      let ((v, R), s) ← run K ρ φ (match contentOf K φ p s with
        | some ((_, T, _, _), _) => T
        | none => .plain .err) u s
      -- STRICT: the value written is a member of the place's type, its label holds that type
      if v ∈ₛ[K.dm.read] (placeTy K φ p s).m ∧ labTyOk s R.label (placeTy K φ p s).m then
      match assignAt K φ p v R.label s with
      | some (r, s₁) =>
        let s₂ := invalidate K φ p s₁
        if lentOk K φ p s₂ then some (r, s₂) else none
      | none => none
      else none) := by
  rw [run, runT]; exact stmtIf_noStmt K hfl _ _ s

/-- After `&y`: `y` reads label `n`, the borrow parked in temporary `0`. -/
noncomputable def b2 (n : Nat) : SState :=
  { env := [{ binds := [{ yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.plain TyM.nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err },
                        xB K n],
              temps := [fun _ => .el0 Nat 0] }],
    shape := fun p => if p = .temp 0 0 then some n else none,
    nextLoan := n + 1,
    lent := fun m => if m = n then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = n then TyM.nat else TyM.err,
    heldMem := fun m => if m = n then .el0 Nat 0 else .err }

theorem borrow_b1 (n : Nat) : borrowPlace K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, { TyS.plain TyM.nat with label := some n }), b2 K n) := by
  show (match contentOf K φ (.var 1) (b1 K n) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := s.tyAt pos
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        let s := s.pushTempShaped (fun _ => v) l
        some ((v, { T with label := some l }), ((s.setLent l [⟨pos, steps, false⟩]).setHeldTy l T.m).setHeldMem l v)
      | none => none) = _
  rw [content_b1_y]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  rfl

theorem positions_b2 (n : Nat) : (b2 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SState.positions, b2]
  rfl

theorem holder_b2 (n : Nat) : (b2 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_b2]
  simp [b2]

noncomputable def b3 (n : Nat) : SState :=
  (b2 K n).setAt (.bind 0 1) fun φ' =>
    (Sem.updAt K.dm K.Γ ((b2 K n).tyAt (.bind 0 1)) (fun _ => .el0 Nat 0) [] ((b2 K n).valAt (.bind 0 1) φ')).getD .err

theorem setContent_b2 (n : Nat) : setContent K φ (.bind 0 1) [] (.el0 Nat 0) (b2 K n) = some (⟨⟩, b3 K n) := by
  rw [setContent_root K φ _ _ _ (Or.inl rfl)]; rfl

/-- After the assignment: `x` holds `y`'s borrow. -/
noncomputable def b5 (n : Nat) : SState :=
  let b4 := (b3 K n).takeLabel n
  { b4 with shape := fun q => if q = .bind 0 1 then some n else b4.shape q }

/-- After `&y`, the access of `x` ends nothing: `x` reads no label. -/
theorem content_b2_x (n : Nat) : contentOf K φ (.var 0) (b2 K n) = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 1, []), b2 K n) := by
  have hr : resolve (b2 K n) (.var 0) = some (.bind 0 1, []) := rfl
  have ha : ∀ hit, (b2 K n).access (.bind 0 1) hit = b2 K n := fun hit =>
    SState.access_of_unreached _ _ _ fun y _ => by simp [SState.reached, b2]
  simp only [contentOf, hr, ha]
  rfl

theorem positions_b3 (n : Nat) : (b3 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  simp [SState.positions, b3, b2, SState.setAt]
  rfl

theorem holder_b3 (n : Nat) : (b3 K n).holderOf n = some (.temp 0 0) := by
  unfold SState.holderOf
  rw [positions_b3]
  simp [b3, b2, SState.setAt]

/-- After the `let x` is dropped. -/
noncomputable def b6 (n : Nat) : SState := (b5 K n).dropLast

noncomputable def yB' (n : Nat) : SBinding :=
  { yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.plain TyM.nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err }

theorem take_b3 (n : Nat) : (b3 K n).takeLabel n =
    { ((b3 K n).setAt (.temp 0 0) fun _ => .moved) with
      shape := fun p => if p = .temp 0 0 then none else (b3 K n).shape p } := by
  unfold SState.takeLabel; rw [holder_b3]

theorem resolve_b5 (n : Nat) : resolve (b5 K n) (.var 0) = some (.bind 0 1, []) := by
  unfold b5; simp only [take_b3]; rfl

theorem assign_b1 (hfl : NoStmt K) (hinv : NoInv K) (n : Nat) (hint : TyS) :
    run K ρ φ hint (.assign (.var 0) (.borrow (.var 1))) (b1 K n) = some ((.el0 Unit (), .plain TyM.unit), b5 K n) := by
  rw [run_assign K ρ φ hfl, content_b1_x]
  show (run K ρ φ (.plain TyM.nat) (.borrow (.var 1)) (b1 K n) >>= _) = _
  rw [run_borrow K ρ φ hfl]
  simp only [SM.strictS]
  rw [borrow_b1]
  dsimp only
  rw [if_pos ⟨(0 : Nat), rfl⟩]
  have hr1 : resolve (b2 K n) (.var 1) = some (.bind 0 0, []) := rfl
  have hl1 := lentOk_root K φ hr1
  simp only [invalidate_noInv K φ hinv, hl1, if_true]
  dsimp only [Bind.bind, Option.bind]
  -- the strict write: `Z` is a `Nat`, and the borrow's label holds `Nat`
  have hpT : placeTy K φ (.var 0) (b2 K n) = .plain TyM.nat := by
    unfold placeTy; rw [content_b2_x]; rfl
  rw [hpT, if_pos ⟨⟨(0 : Nat), rfl⟩, fun l hl => by cases hl; simp [b2, TyS.plain]⟩]
  have hr : resolve (b2 K n) (.var 0) = some (.bind 0 1, []) := rfl
  have ha : ∀ hit, (b2 K n).access (.bind 0 1) hit = b2 K n := fun hit =>
    SState.access_of_unreached _ _ _ fun y _ => by simp [SState.reached, b2]
  have hr5 := resolve_b5 K n
  unfold assignAt
  rw [hr]
  dsimp only
  rw [show (b2 K n).shape (.bind 0 1) = none from rfl]
  simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, ha]
  rw [setContent_root K φ _ _ _ (Or.inl rfl)]
  simp only [List.isEmpty_nil, if_true]
  have hl5 := lentOk_root K φ hr5
  have hs : (b2 K n).shape (.bind 0 1) = none := rfl
  simp only [hs]
  show (if lentOk K φ (.var 0) (b5 K n) then some ((Sem.el0 Unit (), TyS.plain TyM.unit), b5 K n) else none) = _
  rw [if_pos hl5]

theorem env_b6 (n : Nat) : (b6 K n).env = [{ binds := [yB' K n], temps := [fun _ => .moved] }] := by
  unfold b6 b5
  simp only [take_b3]
  rfl

theorem shape_b6 (n : Nat) (p : Pos) (hp : p ≠ .bind 0 1) : (b6 K n).shape p = none := by
  -- `dropLast` clears the removed position's entry (spine ae3a1e1c); elsewhere it is `b5`'s
  unfold b6
  simp only [SState.dropLast]
  split <;> split
  all_goals first
    | rfl
    | (unfold b5; simp only [take_b3]
       show (if p = .bind 0 1 then some n else if p = .temp 0 0 then none else if p = .temp 0 0 then some n else none) = none
       simp [hp])

theorem positions_b6 (n : Nat) : (b6 K n).positions = [.bind 0 0, .temp 0 0] := by
  rw [SState.positions_eq, env_b6]
  simp [framePos]

theorem liveLabels_b6 (n : Nat) : (b6 K n).liveLabels = [] := by
  unfold SState.liveLabels
  rw [positions_b6]
  simp [shape_b6 K n (.bind 0 0) (by simp), shape_b6 K n (.temp 0 0) (by simp)]

theorem content_b6 (n : Nat) : contentOf K φ (.var 0) (b6 K n) = some ((φ n, (yB K n).ty, .bind 0 0, []), b6 K n) := by
  have hr : resolve (b6 K n) (.var 0) = some (.bind 0 0, []) := by
    simp [resolve, Place.steps, SState.varPos, env_b6, SState.topIdx]
  have ha : ∀ hit, (b6 K n).access (.bind 0 0) hit = b6 K n := by
    intro hit; simp [SState.access, liveLabels_b6]
  simp only [contentOf, hr, ha]
  have hv : (b6 K n).valAt (.bind 0 0) = (yB' K n).val := by simp [SState.valAt, env_b6]
  have ht : (b6 K n).tyAt (.bind 0 0) = (yB K n).ty := by simp [SState.tyAt, env_b6, yB']
  have hcf : (b6 K n).typedFuture φ = φ := by funext l; simp [SState.typedFuture, liveLabels_b6]
  rw [hv, ht, hcf]
  rfl


theorem positions_b5 (n : Nat) : (b5 K n).positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  rw [SState.positions_eq]
  unfold b5; simp only [take_b3]
  simp [b3, b2, SState.setAt, framePos]
  rfl

theorem shape_b5 (n : Nat) (p : Pos) : (b5 K n).shape p = if p = .bind 0 1 then some n else none := by
  unfold b5; simp only [take_b3]
  show (if p = .bind 0 1 then some n else if p = .temp 0 0 then none else if p = .temp 0 0 then some n else none) = _
  by_cases h : p = .bind 0 1 <;> simp [h]

theorem holder_b5 (n : Nat) : (b5 K n).holderOf n = some (.bind 0 1) := by
  unfold SState.holderOf
  rw [positions_b5]
  simp [shape_b5]

/-- After the fixed drop: `x`'s borrow is ended (y reads x's content) and x is forgotten. -/
noncomputable def b7 (n : Nat) : SState := ((b5 K n).endAt n (.bind 0 1)).dropLast

theorem b5_val_x (n : Nat) (ψ : Future) : (b5 K n).valAt (.bind 0 1) ψ = .el0 Nat 0 := by
  unfold b5; simp only [take_b3]; rfl

theorem b5_val_y (n : Nat) (ψ : Future) : (b5 K n).valAt (.bind 0 0) ψ = ψ n := by
  unfold b5; simp only [take_b3]; rfl

theorem b7_val_y (n : Nat) (ψ : Future) : (b7 K n).valAt (.bind 0 0) ψ = .el0 Nat 0 := by
  have h1 : (b7 K n).valAt (.bind 0 0) = ((b5 K n).endAt n (.bind 0 1)).valAt (.bind 0 0) := by
    unfold b7 b5
    simp only [take_b3]
    rfl
  rw [h1, SState.endAt_valAt _ _ _ _ (by rw [positions_b5]; simp)]
  simp only [show (Pos.bind 0 0 = Pos.bind 0 1) = False from by simp, if_false]
  rw [b5_val_x, b5_val_y]
  simp [Future.upd]

theorem b7_shape (n : Nat) : (b7 K n).shape = fun _ => none := by
  funext p
  unfold b7
  simp only [SState.dropLast]
  split <;> split
  all_goals first
    | rfl
    | (show (if p = .bind 0 1 then none else (b5 K n).shape p) = none
       rw [shape_b5]; split <;> simp_all)

theorem tyAt_b7 (n : Nat) : (b7 K n).tyAt (.bind 0 0) = .plain TyM.nat := by
  unfold b7 b5; simp only [take_b3]; rfl

theorem content_b7 (n : Nat) : contentOf K φ (.var 0) (b7 K n) = some ((.el0 Nat 0, .plain TyM.nat, .bind 0 0, []), b7 K n) := by
  have hr : resolve (b7 K n) (.var 0) = some (.bind 0 0, []) := by
    unfold b7 b5; simp only [take_b3]; rfl
  simp only [contentOf, hr, access_noshape _ _ (b7_shape K n) _]
  rw [b7_val_y, tyAt_b7]
  rfl

theorem drop_b5 (n : Nat) :
    (match (match (b5 K n).env.getLast? with
        | some fr => (b5 K n).shape (.bind (b5 K n).topIdx (fr.binds.length - 1))
        | none => none) with
      | some l => (b5 K n).endLabel l | none => letLenders (b5 K n)).dropLast = b7 K n := by
  have : (match (b5 K n).env.getLast? with
        | some fr => (b5 K n).shape (.bind (b5 K n).topIdx (fr.binds.length - 1))
        | none => none) = some n := by
    unfold b5; simp only [take_b3]; rfl
  rw [this]
  show ((b5 K n).endLabel n).dropLast = _
  rw [SState.endLabel_eq (holder_b5 K n)]
  rfl

/-- With the proposed drop, `let y = Z; (let x = Z; x := &y); y` reads `Z` at every future: the
drop ends `x`'s borrow, so `y` gets `x`'s content back (CE5, flipped). -/
theorem tA_reads_zero (hfl : NoStmt K) (hinv : NoInv K) (n : Nat) (hint : TyS) :
    ∃ T s', run K ρ φ hint tA (emptyState n) = some ((.el0 Nat 0, T), s') := by
  rw [tA, run_letIn K ρ φ hfl]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain TyM.nat), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = (emptyState n).pushBind (yB K n) from rfl, run_seq K ρ φ hfl, SM.bind_apply,
    run_letIn K ρ φ hfl]
  have h1 : run K ρ φ (.plain .err) .zero ((emptyState n).pushBind (yB K n))
      = some ((.el0 Nat 0, .plain TyM.nat), (emptyState n).pushBind (yB K n)) := rfl
  rw [h1]
  simp only [Option.bind]
  rw [show pushBindShaped ((emptyState n).pushBind (yB K n)) _ = b1 K n from rfl, assign_b1 K ρ φ hfl hinv]
  simp only
  rw [drop_b5, seq_discard_plain, run_place K ρ φ hfl]
  have hc := content_b7 K φ n
  rw [readPlace_of K φ _ _ _ _ _ _ _ _ hc]
  have hm : ReadGood K.dm.read (TyS.plain TyM.nat).m (Sem.el0 Nat 0) := Or.inl ⟨(0 : Nat), rfl⟩
  simp only [Sem.whole, not_true_eq_false, ite_false, hm]
  generalize K.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, b7_shape]
    rw [setContent_root K φ _ _ _ (Or.inl rfl)]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
end

end Ochr.Meaning.Regress.CE5flip
