import Ochr.Meaning.Steps.BorrowParStart
import Ochr.Meaning.Strict.WitnessFix
import Ochr.Meaning.ClosureRef

/-!
# `W`'s and `K`'s bodies, run by the reference from `fixBodyAt`'s state (lead19, 2026-11-21; docs/31 D141)

The body state is `SBW` (`BorrowParStart.startS_eq`): frame 0 the cell `ψ 0`, frame 1 `self` and `r ↦ a` holding label
`0`, lent at the cell, recorded `a`. At the decisions the checker makes there (`DecW`, `DecK`: the reads are neither a
statement nor a proof; `r`, read `.ref .other`, is not copied):

* `W`'s `clone(*r)` reads the content in place: `a` at `Nat`, the state unchanged (`runT_bodyW`). The pop ends label
  `0` (`W` returns no borrow) after its strict test (the holder `r` holds `a`, a `Nat`), and the cell then reads `a`:
  `fixBodyAt` gives `⟨a, [a], none⟩` (`fixBodyAt_W`), and the closure is a member of `Π(r : &Nat). Nat`.
* `K`'s `r` moves the borrow out of `r` into a temporary holding label `0`: `a` at `Nat` labelled `0`
  (`runT_bodyK`). The pop ends nothing (the returned label `0` is kept), so the cell's final is `ψ 0`, the content the
  caller leaves in the returned borrow: `fixBodyAt` gives `⟨a, [ψ ↦ ψ 0], some 0⟩` (`fixBodyAt_K`).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

section
variable (sb : SBinding) (d : DeclInfo) (a : Sem)

theorem resolve_SBW_deref : resolve (SBW sb d a) (.deref (.var 0)) = some (.bind 1 1, [.deref]) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SBW]

theorem resolve_SBW_var : resolve (SBW sb d a) (.var 0) = some (.bind 1 1, []) := by
  simp [resolve, SState.varPos, SState.topIdx, Place.steps, SBW]

theorem reached_SBW (hit : List Step → Bool) (l : Nat) : (SBW sb d a).reached (.bind 1 1) hit l = false := by
  simp [SState.reached, SBW]

theorem access_SBW (hit : List Step → Bool) : (SBW sb d a).access (.bind 1 1) hit = SBW sb d a := by
  unfold SState.access
  have h : ∀ n : Nat, (List.range n).foldl (fun s _ => (s.liveLabels.filter (s.reached (.bind 1 1) hit)).foldl SState.endLabel s)
      (SBW sb d a) = SBW sb d a := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [liveLabels_SBW, reached_SBW]
  exact h _

theorem typedFuture_SBW (ψ : Future) : (SBW sb d a).typedFuture ψ = ψ.upd 0 a := by
  funext l; unfold SState.typedFuture; rw [liveLabels_SBW]
  by_cases hl : l = 0 <;> simp [hl, SBW, Future.upd]

theorem holderOf_SBW : (SBW sb d a).holderOf 0 = some (.bind 1 1) := by
  unfold SState.holderOf; rw [positions_SBW]; simp [SBW]

end

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future) (sb : SBinding) (d : DeclInfo)

theorem contentOk_SBW (a : Sem) (p : Place) {steps : List Step} (hp : resolve (SBW sb d a) p = some (.bind 1 1, steps)) :
    ContentOk K φ p (SBW sb d a) := by
  unfold ContentOk; rw [hp]
  exact Attack.accessOk_unreached _ φ fun l => reached_SBW sb d a _ l

/-- `*r`: the content `a`, at `Nat`, the state unchanged. -/
theorem contentOf_SBW_deref (a : Sem) :
    contentOf K φ (.deref (.var 0)) (SBW sb d a) = some ((a, .plain TyM.nat, .bind 1 1, [.deref]), SBW sb d a) := by
  unfold contentOf
  rw [resolve_SBW_deref]
  dsimp only
  rw [access_SBW, typedFuture_SBW]
  simp [Sem.follow, Sem.step, SState.valAt, SState.tyAt, SBW, parS, TyS.plain]

/-- `r`: the content `a`, at `Nat` labelled `0` (the binding's stored type), the state unchanged. -/
theorem contentOf_SBW_var (a : Sem) :
    contentOf K φ (.var 0) (SBW sb d a) = some ((a, { (TyS.plain TyM.nat) with label := some 0 }, .bind 1 1, []), SBW sb d a) := by
  unfold contentOf
  rw [resolve_SBW_var]
  dsimp only
  rw [access_SBW, typedFuture_SBW]
  simp [Sem.follow, SState.valAt, SState.tyAt, SBW, parS]

/-- **`W`'s body**, `clone(*r)`, from `SBW` at a number: the number at `Nat`, the state unchanged. -/
theorem runT_bodyW (hfl : K.D.flags [d, sb.decl] bodyW = (false, false)) (m : Nat) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyW (SBW sb d (.el0 Nat m)) = some ((.el0 Nat m, .plain TyM.nat), SBW sb d (.el0 Nat m)) := by
  have hsc : scopeOf (SBW sb d (.el0 Nat m)) = [d, sb.decl] := by simp [scopeOf, SBW, parS]
  have hg : ReadGood K.dm.read TyM.nat (.el0 Nat m) := Or.inl ⟨m, rfl⟩
  have hfl' : K.D.flags [d, sb.decl] (.prim "clone" [.place (.deref (.var 0))]) = (false, false) := hfl
  simp only [bodyW, runT, SM.erasedIf, hsc, hfl', Bool.false_eq_true, if_false, SM.stmtIf, SM.headOf,
    SM.guarded_of (contentOk_SBW K φ sb d _ (.deref (.var 0)) (resolve_SBW_deref sb d _))]
  simp [readPlace, contentOf_SBW_deref, bind, Option.bind, Sem.whole, hg, TyS.plain]

/-- **The state after `K`'s body**: `r` moved, the borrow parked in a temporary of frame 1, which holds label `0`; the
cell and its site, the record and the held type unchanged. -/
noncomputable def SBK (sb : SBinding) (d : DeclInfo) (a : Sem) : SState :=
  { env := [{ binds := [cellS] }, { binds := [sb, { parS a d with val := fun _ => .moved }], temps := [fun _ => a] }],
    shape := fun p => if p = .temp 1 0 then some 0 else none, nextLoan := 1,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩] else [],
    heldTy := fun m => if m = 0 then TyM.nat else TyM.err,
    heldMem := fun m => if m = 0 then a else .err }

/-- **`K`'s body**, `r` (read `.ref .other`, not copied: moved), from `SBW` at a number: the number at `Nat` labelled
`0`, `r ↦ moved`, the borrow parked in a temporary. -/
theorem runT_bodyK (hfl : K.D.flags [d, sb.decl] bodyK = (false, false)) (hcp : K.D.copy (K.D.placeDecl [d, sb.decl] (.var 0)) = false)
    (m : Nat) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyK (SBW sb d (.el0 Nat m))
      = some ((.el0 Nat m, { (TyS.plain TyM.nat) with label := some 0 }), SBK sb d (.el0 Nat m)) := by
  have hsc : scopeOf (SBW sb d (.el0 Nat m)) = [d, sb.decl] := by simp [scopeOf, SBW, parS]
  have hg : ReadGood K.dm.read TyM.nat (.el0 Nat m) := Or.inl ⟨m, rfl⟩
  have hfl' : K.D.flags [d, sb.decl] (.place (.var 0)) = (false, false) := hfl
  simp only [bodyK, runT, SM.erasedIf, hsc, hfl', hcp, Bool.false_eq_true, if_false, SM.stmtIf,
    SM.guarded_of (contentOk_SBW K φ sb d _ (.var 0) (resolve_SBW_var sb d _))]
  simp only [readPlace, contentOf_SBW_var, bind, Option.bind]
  simp only [Sem.whole, TyS.plain, hg, not_true_eq_false, if_false, List.isEmpty_nil, if_true, Bool.false_eq_true]
  have hsh : (SBW sb d (.el0 Nat m)).shape (.bind 1 1) = some 0 := by simp [SBW]
  have hset : setContent K φ (.bind 1 1) [] .moved (SBW sb d (.el0 Nat m))
      = some (⟨⟩, (SBW sb d (.el0 Nat m)).setAt (.bind 1 1) fun _ => .moved) := by
    simp [setContent, Attack.updAt_nil]
  rw [hset, hsh]
  have hh : ((SBW sb d (.el0 Nat m)).setAt (.bind 1 1) fun _ => .moved).holderOf 0 = some (.bind 1 1) := by
    unfold SState.holderOf; rw [SState.positions_setAt, positions_SBW, SState.shape_setAt]; simp [SBW]
  simp only [SState.takeLabel, hh, Option.some.injEq, Prod.mk.injEq, true_and]
  simp only [SState.pushTempShaped, SState.pushTemp, SState.topIdx, SState.setAt, SBW, SBK, parS]
  simp
  funext p
  by_cases h1 : p = .temp 1 0
  · subst h1; simp
  · simp only [h1, if_false]; split <;> simp_all

end

/-! ## The closures' bodies inside `fixBodyAt` -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The state after `W`'s pop: label `0` ended, the cell reads the content `a`. -/
theorem endLabel_SBW_cell (sb : SBinding) (d : DeclInfo) (a : Sem) (ψ : Future) :
    ((SBW sb d a).endLabel 0).valAt (.bind 0 0) ψ = a := by
  unfold SState.endLabel
  rw [positions_SBW]
  simp [SBW, SState.mapVals, SState.valAt, Mean.semEnd, SState.toMean, Future.upd, cellS, parS]

theorem liveLabels_SBK (sb : SBinding) (d : DeclInfo) (a : Sem) : (SBK sb d a).liveLabels = [0] := by
  unfold SState.liveLabels
  have : (SBK sb d a).positions = [.bind 0 0, .bind 1 0, .bind 1 1, .temp 1 0] := by
    simp [SBK, SState.positions, List.range']
  rw [this]; simp [SBK]

/-- **`W`'s body inside the `.fix` clause** (stage 1, rank 0), at a number `m`: the result `m`, the cell's final `m` (the
pop ends label `0`, whose strict test reads `r ↦ m`, a `Nat`), no returned label. Formed in the empty state. -/
theorem fixBodyAt_W (fb : List PBind × PBind) {d : DeclInfo} (h1 : fb.1 = [(fun _ => .plain TyM.nat, d)])
    (piT : TyM) (selfM : Sem) (hfl : K.D.flags [d, .pi fb.2.2] bodyW = (false, false)) (m : Nat) :
    fixBodyAt K ρ φ fb (emptyState 0) psW outW piT 0 bodyW selfM [.el0 Nat m]
      = some ⟨.el0 Nat m, [fun _ => .el0 Nat m], none⟩ := by
  have hS := startS_eq fb h1 { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } (.el0 Nat m)
  unfold startS at hS
  unfold fixBodyAt
  dsimp only
  have hF : ([Sem.el0 Nat m].zip psW).foldl (fixStep fb)
      ((emptyState 0).under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], [])
      = (SBW { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } d (.el0 Nat m), [.el0 Nat m], [.bind 0 0]) := by
    simp only [psW, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at hS ⊢
    refine Prod.ext hS ?_
    simp [fixStep, h1, SState.freshLoan, SState.under, emptyState, SState.pushBind, SState.topIdx]
  rw [hF]
  dsimp only
  rw [runT_bodyW K ρ φ _ d hfl m true _]
  dsimp only
  have hk : ((SBW { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } d (.el0 Nat m)).liveLabels.filter
      fun l => decide (l ≥ 0 ∧ some l ≠ (if outW.isRef = true then (TyS.plain TyM.nat).label else none))) = [0] := by
    rw [liveLabels_SBW]; rfl
  rw [hk]
  have hends : EndsOk K φ [0] (SBW { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } d (.el0 Nat m)) := by
    refine ⟨?_, trivial⟩
    intro q hq ψ _
    rw [holderOf_SBW] at hq
    cases hq
    exact ⟨m, rfl⟩
  rw [if_pos hends]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, Option.some.injEq, BodyOut.mk.injEq,
    List.cons.injEq, and_true, true_and]
  refine ⟨funext fun ψ => endLabel_SBW_cell _ _ _ ψ, rfl⟩

/-- **`K`'s body inside the `.fix` clause** (stage 1, rank 0), at a number `m`: the result `m`, the returned label `0`
(kept: the codomain is a borrow), and the cell's final the future at `0`, the content the caller leaves in the returned
borrow when it ends it. -/
theorem fixBodyAt_K (fb : List PBind × PBind) {d : DeclInfo} (h1 : fb.1 = [(fun _ => .plain TyM.nat, d)])
    (piT : TyM) (selfM : Sem) (hfl : K.D.flags [d, .pi fb.2.2] bodyK = (false, false))
    (hcp : K.D.copy (K.D.placeDecl [d, .pi fb.2.2] (.var 0)) = false) (m : Nat) :
    fixBodyAt K ρ φ fb (emptyState 0) psW outK piT 0 bodyK selfM [.el0 Nat m]
      = some ⟨.el0 Nat m, [fun ψ => ψ 0], some 0⟩ := by
  have hS := startS_eq fb h1 { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } (.el0 Nat m)
  unfold startS at hS
  unfold fixBodyAt
  dsimp only
  have hF : ([Sem.el0 Nat m].zip psW).foldl (fixStep fb)
      ((emptyState 0).under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 }, [], [])
      = (SBW { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } d (.el0 Nat m), [.el0 Nat m], [.bind 0 0]) := by
    simp only [psW, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at hS ⊢
    refine Prod.ext hS ?_
    simp [fixStep, h1, SState.freshLoan, SState.under, emptyState, SState.pushBind, SState.topIdx]
  rw [hF]
  dsimp only
  rw [runT_bodyK K ρ φ _ d hfl hcp m true _]
  dsimp only
  have hk : ((SBK { ty := .plain piT, val := fun _ => selfM, decl := .pi fb.2.2 } d (.el0 Nat m)).liveLabels.filter
      fun l => decide (l ≥ 0 ∧ some l ≠ (if outK.isRef = true then some 0 else none))) = [] := by
    rw [liveLabels_SBK]; rfl
  rw [hk, if_pos (show EndsOk K φ [] _ from trivial)]
  simp only [List.foldl_nil, List.map_cons, List.map_nil]
  rfl

end

/-! ## Membership: `W`'s and `K`'s closures are members (`K`'s after docs/31 D141's restatement of `OutGood`) -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **`W`'s closure is a member of `Π(r : &Nat). Nat`** (`Witness.fixClo_mem_nonrec`), at every `fb` reading the
parameter at `Nat` and decisions that classify `clone(*r)` as neither a statement nor a proof: at each number the body
returns it, and the cell's one final is that number at every future (`OutGood`). No assumed fact. -/
theorem closure_mem_W (fb : List PBind × PBind) {d : DeclInfo} (h1 : fb.1 = [(fun _ => .plain TyM.nat, d)]) (piT : TyM)
    (hfl : K.D.flags [d, .pi fb.2.2] bodyW = (false, false)) :
    closureAt K.dm.read 1 φ psW outW (fixG K ρ φ fb 1 (emptyState 0) psW outW piT 0 none bodyW)
      ∈ₛ[K.dm.read] piTyAt K.dm.read 1 psW outW := by
  refine Strict.Witness.fixClo_mem_nonrec fb 1 (emptyState 0) psW outW piT 0 bodyW ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) fun args ha => ?_
  obtain ⟨hlen, hargs⟩ := ha
  match args, hlen with
  | [x], _ =>
    obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
    subst hx
    refine ⟨_, fixBodyAt_W K ρ φ fb h1 _ _ hfl m, ⟨⟨m, rfl⟩, fun i d' hi hd => ?_⟩, rfl⟩
    rcases i with _ | i
    · simp [psW] at hi; subst hi
      exact ⟨fun _ => .el0 Nat m, rfl, fun _ _ => ⟨m, rfl⟩⟩
    · simp [psW] at hi

/-- `K`'s body's output, at a number `m`: the result `m`, the cell's final the future at the returned label `0`. -/
noncomputable def oK (m : Nat) : BodyOut := ⟨.el0 Nat m, [fun ψ => ψ 0], some 0⟩

/-- `OutGood`'s final clause AS FIRST STATED (before docs/31 D141): each borrow parameter's final a member of its
content type at EVERY future. Kept here only as the statement `not_outGood_K` refutes. -/
def OutGoodEvery (R : DataRead) (ds : List PiDom) (out : PiCod) (args : List Sem) (o : BodyOut) : Prop :=
  o.result ∈ₛ[R] out.cod args ∧
    ∀ (i : Nat) (d : PiDom), ds[i]? = some d → d.isRef = true →
      ∃ f, o.finals[((ds.take i).filter (·.isRef)).length]? = some f ∧ ∀ ψ, f ψ ∈ₛ[R] d.dom (args.take i)

/-- **FINDING (docs/31 D141), the refutation of the old clause**: `K`'s output is not good in the sense first stated
(`OutGoodEvery`): it asked each borrow parameter's final to be a member of its content type at EVERY future, and `K`'s
cell's final is `ψ 0`, the content the caller leaves in the returned borrow, a member only at the futures that give
label `0` one. So the old clause failed for every function returning its borrow parameter; `OutGood` is restated at
the futures typed for the result. -/
theorem not_outGood_K (R : DataRead) (m : Nat) : ¬ OutGoodEvery R psW outK [.el0 Nat m] (oK m) := by
  rintro ⟨-, h⟩
  obtain ⟨f, hf, hmem⟩ := h 0 _ rfl rfl
  simp only [oK, psW, List.take_zero, List.filter_nil, List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hf
  subst hf
  obtain ⟨n, hn⟩ := hmem (fun _ => .err)
  cases hn

/-- **`K`'s output is good** (`OutGood`, restated by docs/31 D141): the result `m` a member of `Nat`, and the cell's
final `ψ 0` a member of `Nat` at every future typed for the result, i.e. one that gives the returned label `0` a member
of the codomain's content type `Nat`. -/
theorem outGood_K (R : DataRead) (m : Nat) : OutGood R psW outK [.el0 Nat m] (oK m) := by
  refine ⟨⟨m, rfl⟩, fun i d hi hd => ?_⟩
  rcases i with _ | i
  · simp only [psW, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    refine ⟨fun ψ => ψ 0, rfl, fun ψ hψ => hψ 0 _ ?_⟩
    simp [BodyOut.held, outK, oK]
  · simp [psW] at hi

/-- `K`'s backward function is injective and its label is `0` (`RetGood`): the cell's final at the future that leaves
`v` in the returned borrow is `v`. -/
theorem retGood_K (R : DataRead) (m : Nat) : RetGood R outK [.el0 Nat m] (oK m) :=
  ⟨0, rfl, fun ψ v w _ _ h => by simpa [oK, Future.upd] using h⟩

/-- `K`'s output is good in the sense the definition being checked is asked of (`OutGood'`, inside `MemBelow` and the
per-stage obligations): `OutGood`, `RetGood`, one final for the one borrow parameter. -/
theorem outGood'_K (R : DataRead) (m : Nat) : OutGood' R psW outK [.el0 Nat m] (oK m) :=
  ⟨outGood_K R m, fun _ => retGood_K R m, rfl⟩

/-- **`K`'s closure is a member of `Π(r : &Nat). &Nat`** (`ClosureRef.closure_mem_of_total_ref'`), at every `fb`
reading the parameter at `Nat`, decisions that classify `r` as neither a statement nor a proof, and `r` read as not
copied: at each number the body returns it under label `0`, and the cell's final is what the caller leaves in the
returned borrow (`outGood_K`, `retGood_K`). No assumed fact. It replaces `closure_ref_hyp_false_K`, which showed the
closure lemma's hypothesis false under the old clause. -/
theorem closure_mem_K (fb : List PBind × PBind) {d : DeclInfo} (h1 : fb.1 = [(fun _ => .plain TyM.nat, d)])
    (piT : TyM) (hfl : K.D.flags [d, .pi fb.2.2] bodyK = (false, false))
    (hcp : K.D.copy (K.D.placeDecl [d, .pi fb.2.2] (.var 0)) = false) :
    closureAt K.dm.read 1 φ psW outK (fixG K ρ φ fb 1 (emptyState 0) psW outK piT 0 none bodyK)
      ∈ₛ[K.dm.read] piTyAt K.dm.read 1 psW outK := by
  refine closure_mem_of_total_ref' K.dm.read 1 φ psW outK _ ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ => Nat.le_refl 1) fun args ha => ?_
  obtain ⟨hlen, hargs⟩ := ha
  match args, hlen with
  | [x], _ =>
    obtain ⟨m, hx⟩ := hargs 0 x _ rfl rfl
    subst hx
    exact ⟨oK m, fixBodyAt_K K ρ φ fb h1 _ _ hfl hcp m, outGood_K _ m, retGood_K _ m, rfl⟩

end

end Ochr.Meaning.Steps.Form.ColumnW
