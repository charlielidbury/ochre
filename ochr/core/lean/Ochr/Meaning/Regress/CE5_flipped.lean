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

theorem access_noshape (s : SState) (p : Pos) (h : s.shape = fun _ => none) : s.access p = s := by
  simp [SState.access, liveLabels_noshape s h]

theorem SM.bind_apply {α β : Type 3} (x : SM α) (f : α → SM β) (s : SState) :
    (x >>= f) s = match x s with | some (a, s') => f a s' | none => none := rfl


section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem run_letIn (h : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.letIn h u w) s = (run K ρ φ (.plain .err) u s).bind (fun x =>
      (run K ρ φ hint w (pushBindShaped x.2 { ty := x.1.2, val := fun _ => x.1.1, decl := K.D.declOf (scopeOf x.2) u })).bind
        fun y => some (y.1, (match (match y.2.env.getLast? with
            | some fr => y.2.shape (.bind y.2.topIdx (fr.binds.length - 1))
            | none => none) with
          | some l => y.2.endLabel l | none => y.2).dropLast)) := rfl

theorem run_seq (u w : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.seq u w) s = (run K ρ φ (.plain .err) u >>= fun _ => run K ρ φ hint w) s := rfl

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run K ρ φ hint (.place p) s = readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s := rfl

theorem run_borrow (p : Place) (hint : TyS) (s : SState) : run K ρ φ hint (.borrow p) s = borrowPlace K φ p s := rfl

theorem readPlace_of (p : Place) (b : Bool) (s : SState) (v : Sem) (T : TyS) (pos : Pos) (st : List Step)
    (s' : SState) (h : contentOf K φ p s = some ((v, T, pos, st), s')) :
    readPlace K φ p b s = ((if ¬ v.whole then none else
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
  { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0, decl := K.D.declOf (scopeOf (emptyState n)) .zero }

noncomputable def xB (K : RunCtx) (n : Nat) : SBinding :=
  { ty := .plain (.ty0 Nat), val := fun _ => .el0 Nat 0,
    decl := K.D.declOf (scopeOf ((emptyState n).pushBind (yB K n))) .zero }

/-- `y` and `x` bound. -/
noncomputable def b1 (n : Nat) : SState := ((emptyState n).pushBind (yB K n)).pushBind (xB K n)

theorem content_b1_y (n : Nat) : contentOf K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 0, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 1) = some (.bind 0 0, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _)]
  rfl

theorem content_b1_x (n : Nat) : contentOf K φ (.var 0) (b1 K n) = some ((.el0 Nat 0, .plain (.ty0 Nat), .bind 0 1, []), b1 K n) := by
  have hr : resolve (b1 K n) (.var 0) = some (.bind 0 1, []) := rfl
  simp only [contentOf, hr, access_noshape _ _ (rfl : (b1 K n).shape = _)]
  rfl

theorem run_assign (p : Place) (u : Term) (hint : TyS) (s : SState) :
    run K ρ φ hint (.assign p u) s = (do
      let ((_, T, pos, steps), s) ← contentOf K φ p s
      let ((v, R), s) ← run K ρ φ T u s
      let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
      let (⟨⟩, s) ← setContent K φ pos steps v s
      let s := match R.label, steps with
        | some l, [] => let s := s.takeLabel l; { s with shape := fun q => if q = pos then some l else s.shape q }
        | _, _ => s
      some ((.el0 Unit (), .plain (.ty0 Unit)), s)) := rfl

/-- After `&y`: `y` reads label `n`, the borrow parked in temporary `0`. -/
noncomputable def b2 (n : Nat) : SState :=
  { env := [{ binds := [{ yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err },
                        xB K n],
              temps := [fun _ => .el0 Nat 0] }],
    shape := fun p => if p = .temp 0 0 then some n else none,
    nextLoan := n + 1 }

theorem borrow_b1 (n : Nat) : borrowPlace K φ (.var 1) (b1 K n) = some ((.el0 Nat 0, { TyS.plain (.ty0 Nat) with label := some n }), b2 K n) := by
  show (match contentOf K φ (.var 1) (b1 K n) with
      | some ((v, T, pos, steps), s) =>
        if ¬ v.whole then none else
        let (l, s) := s.freshLoan
        let T0 := (s.tyAt pos).m
        let old := s.valAt pos
        let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
        let s := s.pushTempShaped (fun _ => v) l
        some ((v, { T with label := some l }), s)
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
    (Sem.updAt K.dm K.Γ ((b2 K n).tyAt (.bind 0 1)).m (fun _ => .el0 Nat 0) [] ((b2 K n).valAt (.bind 0 1) φ')).getD .err

theorem setContent_b2 (n : Nat) : setContent K φ (.bind 0 1) [] (.el0 Nat 0) (b2 K n) = some (⟨⟩, b3 K n) := rfl

/-- After the assignment: `x` holds `y`'s borrow. -/
noncomputable def b5 (n : Nat) : SState :=
  let b4 := (b3 K n).takeLabel n
  { b4 with shape := fun q => if q = .bind 0 1 then some n else b4.shape q }

theorem assign_b1 (n : Nat) (hint : TyS) :
    run K ρ φ hint (.assign (.var 0) (.borrow (.var 1))) (b1 K n) = some ((.el0 Unit (), .plain (.ty0 Unit)), b5 K n) := by
  rw [run_assign]
  show (contentOf K φ (.var 0) (b1 K n) >>= _) = _
  rw [content_b1_x]
  show (run K ρ φ (.plain (.ty0 Nat)) (.borrow (.var 1)) (b1 K n) >>= _) = _
  rw [run_borrow, borrow_b1]
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
  { yB K n with val := fun φ' => (Sem.updAt K.dm K.Γ (.ty0 Nat) (fun _ => φ' n) [] (Sem.el0 Nat 0)).getD .err }

theorem take_b3 (n : Nat) : (b3 K n).takeLabel n =
    { ((b3 K n).setAt (.temp 0 0) fun _ => .moved) with
      shape := fun p => if p = .temp 0 0 then none else (b3 K n).shape p } := by
  unfold SState.takeLabel; rw [holder_b3]

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
  have ha : (b6 K n).access (.bind 0 0) = b6 K n := by
    simp [SState.access, liveLabels_b6]
  simp only [contentOf, hr, ha]
  have hv : (b6 K n).valAt (.bind 0 0) = (yB' K n).val := by simp [SState.valAt, env_b6]
  have ht : (b6 K n).tyAt (.bind 0 0) = (yB K n).ty := by simp [SState.tyAt, env_b6, yB']
  rw [hv, ht]
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

theorem content_b7 (n : Nat) : ∃ T, contentOf K φ (.var 0) (b7 K n) = some ((.el0 Nat 0, T, .bind 0 0, []), b7 K n) := by
  have hr : resolve (b7 K n) (.var 0) = some (.bind 0 0, []) := by
    unfold b7 b5; simp only [take_b3]; rfl
  simp only [contentOf, hr, access_noshape _ _ (b7_shape K n)]
  rw [b7_val_y]
  exact ⟨_, rfl⟩

theorem drop_b5 (n : Nat) :
    (match (match (b5 K n).env.getLast? with
        | some fr => (b5 K n).shape (.bind (b5 K n).topIdx (fr.binds.length - 1))
        | none => none) with
      | some l => (b5 K n).endLabel l | none => b5 K n).dropLast = b7 K n := by
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
theorem tA_reads_zero (n : Nat) (hint : TyS) : ∃ T s', run K ρ φ hint tA (emptyState n) = some ((.el0 Nat 0, T), s') := by
  rw [tA, run_letIn]
  have h0 : run K ρ φ (.plain .err) .zero (emptyState n) = some ((.el0 Nat 0, .plain (.ty0 Nat)), emptyState n) := rfl
  rw [h0]
  simp only [Option.bind]
  rw [show pushBindShaped (emptyState n) _ = (emptyState n).pushBind (yB K n) from rfl, run_seq, SM.bind_apply,
    run_letIn]
  have h1 : run K ρ φ (.plain .err) .zero ((emptyState n).pushBind (yB K n))
      = some ((.el0 Nat 0, .plain (.ty0 Nat)), (emptyState n).pushBind (yB K n)) := rfl
  rw [h1]
  simp only [Option.bind]
  rw [show pushBindShaped ((emptyState n).pushBind (yB K n)) _ = b1 K n from rfl, assign_b1]
  simp only
  rw [drop_b5, run_place]
  obtain ⟨T, hc⟩ := content_b7 K φ n
  rw [readPlace_of K φ _ _ _ _ _ _ _ _ hc]
  simp only [Sem.whole, not_true_eq_false, ite_false]
  generalize K.D.copy _ = b
  cases b
  · simp only [Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true, b7_shape]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
end

end Ochr.Meaning.Regress.CE5flip
