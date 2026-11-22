import Ochr.Meaning.Strict.Witness

/-!
# A label moved from a temporary into a binding (the witness of `SGood.uniq`)

`let y = &x; c` from `x : Nat = 1` (`sA`): the borrow parks the fresh label `0` in a temporary
(`sG1`), the `let` moves it into the binding `y` (`pushBindShaped`: `takeLabel` forgets the temporary
as its holder, `sG2`), the tail `c` runs, and the drop ends the borrow (`EndOk`: `y` holds `1`).
The run succeeds (`run_letBorrow`); the state where `y` holds the label is good, the label at ONE
position (`sG2_good`, via `sgood_pushBindShaped`), and `fund_all` gives the final state good
(`w_letBorrow`). The uniqueness clause is what makes the `let`'s move sound: `takeLabel` forgets only
the first holder `find?` meets, so a second holder would survive it.
-/

namespace Ochr.Meaning.Strict.Witness

open Ochr Ochr.Meaning Ochr.Meaning.Strict
open Ochr.Meaning.Strict.FieldWriteCE (nat_mem)
open Classical

section LetBorrow
variable (dm : DataModel)

/-- The state after `&x`: `x` reads label `0`'s final content, a temporary holds the borrow of `1`. -/
noncomputable def sG1 : SState :=
  ((((sA.freshLoan.2.setAt (.bind 0 0) fun φ' => φ' 0).pushTempShaped (fun _ => .el0 Nat 1) 0).setLent 0
    [⟨.bind 0 0, [], false⟩]).setHeldTy 0 TyM.nat).setHeldMem 0 (.el0 Nat 1)

theorem contentOf_sA_x : contentOf (Kw dm []) φw (.var 0) sA =
    some ((.el0 Nat 1, .plain TyM.nat, .bind 0 0, []), sA) := by
  unfold contentOf
  rw [show resolve sA (.var 0) = some (.bind 0 0, []) from rfl]
  dsimp only
  rw [access_noLive live_sA]
  rfl

theorem borrowPlace_sA : borrowPlace (Kw dm []) φw (.var 0) sA =
    some ((.el0 Nat 1, { (TyS.plain TyM.nat) with label := some 0 }), sG1) := by
  unfold borrowPlace
  rw [contentOf_sA_x]
  simp only [Bind.bind, Option.bind_some]
  rw [if_neg (by simp [Sem.whole])]
  unfold sG1
  have hG : (fun φ' => (Sem.updAt (Kw dm []).dm (Kw dm []).Γ (sA.freshLoan.2.tyAt (.bind 0 0))
      (fun _ => φ' sA.freshLoan.1) [] (sA.freshLoan.2.valAt (.bind 0 0) φ')).getD .err) = fun φ' => φ' 0 := by
    funext φ'
    rw [Sem.updAt_nil']; rfl
  simp only [hG]
  rfl

/-- **`&x` runs**: the content `1` is a member of `Nat`; nothing is invalidated (`Kw dm []`). -/
theorem run_borrowX (ρ : Assignment) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint (.borrow (.var 0)) sA =
      some ((.el0 Nat 1, { (TyS.plain TyM.nat) with label := some 0 }), sG1) := by
  rw [runT]
  show SM.erasedIf (false, false) _ sA = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  unfold SM.strictS
  rw [SM.guarded_of (contentOk_noLive live_sA _), borrowPlace_sA]
  dsimp only
  rw [if_pos (show Sem.el0 Nat 1 ∈ₛ[(Kw dm []).dm.read] (TyS.plain TyM.nat).m from nat_mem dm 1)]
  dsimp only
  rw [show invalidate (Kw dm []) φw (.var 0) sG1 = sG1 from rfl, if_pos]
  refine ⟨trivial, ?_⟩
  unfold lentOk
  rw [show resolve sG1 (.var 0) = some (.bind 0 0, []) from rfl]
  exact .inl rfl

/-- `y`, the binding the `let` makes: it holds the borrow `0` of the content `1`. -/
def bY : SBinding := { ty := { (TyS.plain TyM.nat) with label := some 0 }, val := fun _ => .el0 Nat 1, decl := .other }

theorem positions_sG1 : sG1.positions = [.bind 0 0, .temp 0 0] := by
  simp [sG1, sA, st, natB, SState.positions, SState.setHeldMem, SState.setHeldTy, SState.setLent,
    SState.pushTempShaped, SState.pushTemp, SState.setAt, SState.freshLoan, SState.topIdx, List.range']

theorem holderOf_sG1 : sG1.holderOf 0 = some (.temp 0 0) := by
  unfold SState.holderOf; rw [positions_sG1]; rfl

/-- The state after the `let` binds `y`: the temporary is forgotten as the holder (it reads `⊥`),
`y` holds label `0`. -/
noncomputable def sG2 : SState := pushBindShaped sG1 bY

theorem sG2_eq : sG2 = { (sG1.takeLabel 0).pushBind bY with
    shape := fun p => if p = .bind 0 1 then some 0 else (sG1.takeLabel 0).shape p } := by
  unfold sG2 pushBindShaped
  rw [show bY.ty.label = some 0 from rfl]
  dsimp only
  unfold SState.takeLabel
  rw [holderOf_sG1]
  rfl

theorem positions_sG2 : sG2.positions = [.bind 0 0, .bind 0 1, .temp 0 0] := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]
  simp [sG1, sA, st, natB, bY, SState.positions, SState.setHeldMem, SState.setHeldTy, SState.setLent,
    SState.pushTempShaped, SState.pushTemp, SState.pushBind, SState.setAt, SState.freshLoan, SState.topIdx, List.range']

theorem shape_sG2 (p : Pos) : sG2.shape p = if p = .bind 0 1 then some 0 else none := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]
  show (if p = .bind 0 1 then some 0 else if p = .temp 0 0 then none else sG1.shape p) = _
  by_cases h1 : p = .bind 0 1
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : p = .temp 0 0
    · rw [if_pos h2]
    · rw [if_neg h2]
      show (if p = .temp 0 0 then some 0 else none) = none
      rw [if_neg h2]

theorem holderOf_sG2 : sG2.holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_sG2]; simp [shape_sG2]

theorem valAt_sG2_y : sG2.valAt (.bind 0 1) = fun _ => .el0 Nat 1 := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]; rfl

theorem heldTy_sG2 : sG2.heldTy 0 = TyM.nat := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]; rfl

/-- The frame after the `let`: `x`, then `y`; the temporary the borrow was parked in reads `⊥`. -/
def frG2 : SFrame := { binds := [{ ty := .plain TyM.nat, val := fun φ' => φ' 0 }, bY], temps := [fun _ => .moved] }

theorem getLast_sG2 : sG2.env.getLast? = some frG2 := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]; rfl

theorem topIdx_sG2 : sG2.topIdx = 0 := by
  rw [sG2_eq]; unfold SState.takeLabel; rw [holderOf_sG1]; rfl

/-- The drop's end is strict-OK: `y` holds `1`, a member of `Nat`. -/
theorem endOk_sG2 : EndOk (Kw dm []) φw sG2 0 := by
  intro r hr ψ _
  rw [holderOf_sG2] at hr; cases hr
  rw [valAt_sG2_y, heldTy_sG2]; exact nat_mem dm 1

theorem pushBind_sG1 :
    pushBindShaped sG1 ⟨{ (TyS.plain TyM.nat) with label := some 0 }, fun _ => Sem.el0 Nat 1, (Kw dm []).D.declOf (scopeOf sA) (.borrow (.var 0)), none⟩ = sG2 := rfl

/-- **`let y = &x; c` runs**: the borrow is made, moved into `y`, and ended by the drop over `1`. -/
theorem run_letBorrow (ρ : Assignment) (x : Hint) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint (.letIn x (.borrow (.var 0)) (.const "c")) sA =
      some ((.el0 Nat 0, .plain TyM.nat), (sG2.endLabel 0).dropLast) := by
  rw [runT]
  show SM.erasedIf (false, false) _ sA = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [run_borrowX]
  simp only [Bind.bind, Option.bind_some]
  rw [pushBind_sG1, show runT (Kw dm []) ρ φw tl (tailHint tl hint) (.const "c") sG2 = some ((.el0 Nat 0, .plain TyM.nat), sG2) from rfl]
  simp only [Option.bind_some]
  simp only [getLast_sG2, topIdx_sG2, shape_sG2, frG2, List.length_cons, List.length_nil, if_true]
  rw [if_pos (endOk_sG2 dm)]

/-- **The state where `y` holds the borrow is good**, the label at one position (`shape_sG2`): from the
lemma at the borrow's run (`sG1` good, the result good, its label recorded and live) and the `let`'s
binding (`sgood_pushBindShaped`, whose `uniq` clause rests on `takeLabel` leaving no holder). -/
theorem sG2_good (ρ : Assignment) : SGood dm [] φw sG2 := by
  obtain ⟨hv, hlab, hlou, hs⟩ := fund_all (K := Kw dm []) (ρ := ρ) (φ := φw) (fundCtx_Kw dm [])
    (.borrow (.var 0)) trivial false (.plain TyM.err) sA sG1 _ (sA_good dm) (run_borrowX dm ρ false _)
  exact sgood_pushBindShaped (K := Kw dm []) (φ := φw) hs bY rfl hv hlab hlou
    (env_ne_of_mem (p := .bind 0 0) (by rw [positions_sG1]; simp))

/-- **The fundamental lemma applied to a `let` of a borrow**: the run succeeds and leaves a good state. -/
theorem w_letBorrow (ρ : Assignment) (x : Hint) (tl : Bool) (hint : TyS) :
    runT (Kw dm []) ρ φw tl hint (.letIn x (.borrow (.var 0)) (.const "c")) sA =
      some ((.el0 Nat 0, .plain TyM.nat), (sG2.endLabel 0).dropLast) ∧
      SGood dm [] φw ((sG2.endLabel 0).dropLast) :=
  ⟨run_letBorrow dm ρ x tl hint, (fund_all (fundCtx_Kw dm []) (.letIn x (.borrow (.var 0)) (.const "c"))
    ⟨trivial, trivial⟩ tl hint sA _ _ (sA_good dm) (run_letBorrow dm ρ x tl hint)).2.2.2⟩

end LetBorrow

end Ochr.Meaning.Strict.Witness
