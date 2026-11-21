import Ochr.Meaning.Steps.ColumnWrite

/-!
# The borrow column: `def B : Nat := let x = S(Z); let y = &x; *y := Z; x` (lead7)

The first column with a LIVE label: `&x` makes one, `*y := Z` writes through it, and the read of
`x` ends it ([Access]), passing `y`'s content back to `x` through the future, under ruling (A)'s
strict end test. This file starts with the step the design turns on, the read whose access ends a
borrow (`readEnd`): the reference's [Access] of `x` is exactly one [End] (`access_single`), whose
test passes because the holder's content is a whole member of the borrow's type at every typed
future (by the relation, at the futures `typedFut_rel` gives); the lender is read through the
future at the holder's content, which the relation fixes at a related future (`SGood.holderIndep`:
the holder does not read its own label).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

/-! ## [Access] that ends exactly one label -/

theorem foldl_fix {α β : Type _} (f : α → β → α) (x : α) :
    ∀ L : List β, (∀ b ∈ L, f x b = x) → L.foldl f x = x
  | [], _ => rfl
  | b :: L, h => by
    rw [List.foldl_cons, h b (List.mem_cons_self ..)]
    exact foldl_fix f x L fun b' hb' => h b' (List.mem_cons_of_mem _ hb')

theorem endLabel_of_not_live {t : SState} {z : Nat} (h : ¬ t.Live z) : t.endLabel z = t := by
  unfold SState.endLabel
  rw [List.find?_eq_none.mpr fun q hq => by
    simp only [decide_eq_true_eq]
    intro hsh
    exact h ((SState.live_iff _ _).mpr ⟨q, hq, hsh⟩)]

/-- **An access whose only live label it reaches ends that label and nothing else**: where `l` is
the one live label, the access reaches it, and none is live after its end. -/
theorem access_single {s : SState} {p : Pos} {hit : List Step → Bool} {l : Nat}
    (hlive : ∀ z, s.Live z ↔ z = l) (hreach : s.reached p hit l = true)
    (hnone : ∀ z, ¬ (s.endLabel l).Live z) : s.access p hit = s.endLabel l := by
  have hall : ∀ z ∈ s.liveLabels, z = l := fun z hz => (hlive z).mp hz
  have hmem : l ∈ s.liveLabels := (hlive l).mpr rfl
  have hfilt : s.liveLabels.filter (s.reached p hit) = s.liveLabels :=
    List.filter_eq_self.mpr fun z hz => by rw [hall z hz]; exact hreach
  have hfix : ∀ z ∈ s.liveLabels, (s.endLabel l).endLabel z = s.endLabel l := by
    intro z hz
    rw [hall z hz]
    exact endLabel_of_not_live (hnone l)
  have hstep : SState.accStep p hit s = s.endLabel l := by
    unfold SState.accStep
    rw [hfilt]
    obtain ⟨L, hL⟩ : ∃ L, s.liveLabels = l :: L := by
      cases e : s.liveLabels with
      | nil => rw [e] at hmem; cases hmem
      | cons a L => exact ⟨L, by rw [hall a (by rw [e]; exact List.mem_cons_self ..)]⟩
    rw [hL, List.foldl_cons]
    exact foldl_fix _ _ L fun z hz => hfix z (by rw [hL]; exact List.mem_cons_of_mem _ hz)
  have hstep' : SState.accStep p hit (s.endLabel l) = s.endLabel l := by
    unfold SState.accStep
    rw [List.filter_eq_nil_iff.mpr fun z hz => absurd hz (hnone z)]
    rfl
  rw [SState.access_eq]
  obtain ⟨k, hk⟩ : ∃ k, s.liveLabels.length = k + 1 := by
    cases e : s.liveLabels with
    | nil => rw [e] at hmem; cases hmem
    | cons a L => exact ⟨L.length, by simp⟩
  rw [hk, List.range_succ_eq_map, List.foldl_cons, hstep]
  exact foldl_fix _ _ _ fun _ _ => hstep'

/-! ## The state at `B`'s read: `x ↦ loan_l : Nat`, `y ↦ borrow_l w : &Nat`, nothing else -/

/-- The checker's state at the read of `x` in `B`. -/
structure AtRead (K : RunCtx) (ρ : Assignment) (st : MState) (l : Nat) (w : Value) : Prop where
  pos : allPos st.env = [.bind 0 0, .bind 0 1]
  ckx : ckVarPos st.env 1 = some (.bind 0 0)
  x : valAt st.env (.bind 0 0) = .loan l
  y : valAt st.env (.bind 0 1) = .borrow l w
  num : w.Num
  tx : (Env.hintAt K.dm K.M K.Γ ρ st.env (.bind 0 0)).m = TyM.nat
  ty : (Env.hintAt K.dm K.M K.Γ ρ st.env (.bind 0 1)).m = TyM.nat

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem AtRead.shapeY {st : MState} {l : Nat} {w : Value} (h : AtRead K ρ st l w) :
    Env.shape st.env (.bind 0 1) = some l := by
  rw [shape_eq_shapeOf, h.y]; rfl

theorem AtRead.ckShape {st : MState} {l : Nat} {w : Value} (h : AtRead K ρ st l w) {q : Pos} {m : Nat}
    (hq : Env.shape st.env q = some m) : q = .bind 0 1 ∧ m = l := by
  have hmem := mem_allPos_of_shape hq
  rw [h.pos] at hmem
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · rw [shape_eq_shapeOf, h.x] at hq; cases hq
  · rw [h.shapeY] at hq; cases hq; exact ⟨rfl, rfl⟩

/-- At a related state the reference's only holder is `y`, of `π l`. -/
theorem atRead_shape {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) :
    s.shape (.bind 0 1) = some (π l) ∧ ∀ p z, s.shape p = some z → p = .bind 0 1 ∧ z = π l := by
  refine ⟨hr.sim.2.1 _ l (by simp [IsTemp]) h.shapeY, fun p z hp => ?_⟩
  cases p with
  | bind f i =>
    obtain ⟨m, h1, h2⟩ := hr.sim.2.2.1 _ z (by simp [IsTemp]) hp
    obtain ⟨e, rfl⟩ := h.ckShape h1
    exact ⟨e, h2.symm⟩
  | temp f j =>
    obtain ⟨i, m, h1, -⟩ := hr.sim.2.2.2.2 f j z hp
    cases (h.ckShape h1).1

theorem atRead_live {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) (z : Nat) : s.Live z ↔ z = π l := by
  obtain ⟨hy, honly⟩ := atRead_shape hr h
  rw [SState.live_iff]
  constructor
  · rintro ⟨p, -, hp⟩; exact (honly p z hp).2
  · rintro rfl; exact ⟨_, hr.holders _ _ hy, hy⟩

theorem atRead_holder {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) : s.holderOf (π l) = some (.bind 0 1) := by
  obtain ⟨r, hr'⟩ := SState.holderOf_of_live ((atRead_live hr h (π l)).mpr rfl)
  rw [hr', ((atRead_shape hr h).2 r _ (SState.holderOf_spec hr').2).1]

theorem atRead_reached {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) : s.reached (.bind 0 0) (dataHit []) (π l) = true := by
  have hlv : liveLoan st.env l = true := by
    unfold liveLoan findBorrow
    rw [h.pos]
    simp [h.x, h.y, Value.holdsBorrow]
  have hsite : (⟨.bind 0 0, [], false⟩ : Site) ∈ s.lent (π l) := by
    rw [hr.sites l hlv]
    unfold Env.sitesOf
    rw [h.pos]
    simp [h.x, Value.sitesOf]
  unfold SState.reached
  rw [List.any_eq_true]
  exact ⟨_, hsite, by simp [dataHit]⟩

theorem atRead_none {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) (z : Nat) : ¬ (s.endLabel (π l)).Live z := by
  rw [SState.endLabel_eq (atRead_holder hr h), SState.live_iff, SState.endAt_positions]
  rintro ⟨p, -, hp⟩
  rw [SState.endAt_shape] at hp
  simp only at hp
  by_cases e : p = .bind 0 1
  · rw [if_pos e] at hp; cases hp
  · rw [if_neg e] at hp; exact e ((atRead_shape hr h).2 p z hp).1

/-- **The reference's access of `x` is the end of `y`'s borrow.** -/
theorem atRead_access {π : Nat → Nat} {st : MState} {s : SState} {l : Nat} {w : Value} (hr : Rel K ρ φ π st s)
    (h : AtRead K ρ st l w) :
    s.access (.bind 0 0) (dataHit []) = s.endAt (π l) (.bind 0 1) := by
  rw [access_single (atRead_live hr h) (atRead_reached hr h) (atRead_none hr h), SState.endLabel_eq (atRead_holder hr h)]

end

/-! ## Sanity runs of the borrow column's assumed facts (the checker's own runs, compiled, not kernel-checked)

`B`'s body as the checker reads it, accepted, its run giving `0` at `Nat`; then each assumed `Prop` of
`FormMachine.lean` for the column (`BorrowNumInv`, `AssignDerefInv`, `SeqInv`, `VarEndInv`) run at
the entry conditions it must survive (the term in tail position and not, a handed-down reading, an
untyped run), and at the three states that refuted their first statements (a lazily typed binding,
a reborrowed content, a lender stored at another type). Mode excludes a private copy (`erasedDepth`). -/

namespace ColumnB

open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open ColumnC (stC stX)

/-- `def B : Nat := (let x = S(Z); let y = &x; *y := Z; x)`. -/
def bodyB : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.borrow (.var 0))
  (.seq (.assign (.deref (.var 0)) .zero) (.place (.var 1))))

def defB : Def := { name := "B", hs := [], doms := [], cod := .nat, body := bodyB }

def acceptedB : Bool :=
  match checkDefs {} [.defn defB] with
  | [(_, .accepted, _)] => true
  | _ => false

#guard acceptedB
#guard outVal (Ochr.eval 100 true bodyB (some .tNat)) stC 1000 == (.zero, some .tNat)
#guard (outSt (Ochr.eval 100 true bodyB (some .tNat)) stC 1000).env[0]!.binds.size == 0

def vals (st : MState) : List Value := (st.env[0]!.binds.toList).map (·.val)

/-- One frame, `x ↦ loan_0 : Nat`, `y ↦ borrow_0 c : &Nat`: `B`'s state after `let y = &x`. -/
def stXY (c : Value) : MState :=
  { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .loan 0, decl := .other },
     { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := .borrow 0 c, decl := .other }] }], nextLoan := 1 }

-- `BorrowNumInv`: `&x` from `x ↦ S(Z)`: `borrow_0 S(Z)` at `&Nat`, `x ↦ loan_0`, the counter one up;
-- in tail position and under a handed-down reading the same
#guard outVal (Ochr.evalCore 100 true (.borrow (.var 0)) none) (stX (.succ .zero)) 1000 ==
  (.borrow 0 (.succ .zero), some (.tRef .tNat))
#guard vals (outSt (Ochr.evalCore 100 true (.borrow (.var 0)) none) (stX (.succ .zero)) 1000) == [.loan 0]
#guard (outSt (Ochr.evalCore 100 true (.borrow (.var 0)) none) (stX (.succ .zero)) 1000).nextLoan == 1
#guard outVal (Ochr.evalCore 100 true (.borrow (.var 0)) none) { stX (.succ .zero) with curTail := true } 1000 ==
  (.borrow 0 (.succ .zero), some (.tRef .tNat))
#guard outVal (Ochr.eval 100 true (.borrow (.var 0)) none) { stX (.succ .zero) with tailDecl := some .other } 1000 ==
  (.borrow 0 (.succ .zero), some (.tRef .tNat))
-- the first statement's refutation: `x` typed lazily (`ty := none`, a deferred codomain `Nat`): the
-- typed run returns `&Nat`, not `b.ty.map .tRef = none`
def stLazy : MState :=
  let b : Binding := { hint := ⟨"x"⟩, ty := none, val := .succ .zero, decl := .other }
  { env := #[{ binds := #[{ b with lazyTy := some (.tPi [] (.pi [] [] .nat) [], [], 0) }] }] }
#guard outVal (Ochr.evalCore 100 true (.borrow (.var 0)) none) stLazy 1000 == (.borrow 0 (.succ .zero), some (.tRef .tNat))

-- `AssignDerefInv`: `*y := Z`: `y ↦ borrow_0 Z`, `()` at `Unit`; in tail position the same
#guard outVal (Ochr.evalCore 100 true (.assign (.deref (.var 0)) .zero) none) (stXY (.succ .zero)) 1000 ==
  (.unit, some .tUnit)
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.deref (.var 0)) .zero) none) (stXY (.succ .zero)) 1000) ==
  [.loan 0, .borrow 0 .zero]
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.deref (.var 0)) .zero) none)
  { stXY (.succ .zero) with curTail := true } 1000) == [.loan 0, .borrow 0 .zero]
-- the first statement's refutation: `y`'s content reborrowed by `r`; the write ends `r`
def stReb : MState :=
  { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .loan 0, decl := .other },
     { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := .borrow 0 (.loan 1), decl := .other },
     { hint := ⟨"r"⟩, ty := some (.tRef .tNat), val := .borrow 1 (.succ .zero), decl := .other }] }], nextLoan := 2 }
#guard vals (outSt (Ochr.evalCore 100 true (.assign (.deref (.var 1)) .zero) none) stReb 1000) ==
  [.loan 0, .borrow 0 .zero, .bot]

-- `SeqInv`: `(*y := Z); x` from `B`'s state: `0` at `Nat`, both `⊥`; the tail under a handed-down reading
#guard outVal (Ochr.evalCore 100 true (.seq (.assign (.deref (.var 0)) .zero) (.place (.var 1))) none)
  (stXY (.succ .zero)) 1000 == (.zero, some .tNat)
#guard vals (outSt (Ochr.evalCore 100 true (.seq (.assign (.deref (.var 0)) .zero) (.place (.var 1))) none)
  (stXY (.succ .zero)) 1000) == [.bot, .bot]
#guard isOk (Ochr.eval 100 true (.seq (.assign (.deref (.var 0)) .zero) (.place (.var 1))) none)
  { stXY (.succ .zero) with tailDecl := some .other } 1000

-- `VarEndInv`: the read of `x` ends `y`: `0` at `Nat`; the move leaves both `⊥`; in tail position the
-- same; untyped, the value with no type
#guard outVal (Ochr.evalCore 100 true (.place (.var 1)) none) (stXY .zero) 1000 == (.zero, some .tNat)
#guard vals (outSt (Ochr.evalCore 100 true (.place (.var 1)) none) (stXY .zero) 1000) == [.bot, .bot]
#guard outVal (Ochr.evalCore 100 true (.place (.var 1)) none) { stXY .zero with curTail := true } 1000 ==
  (.zero, some .tNat)
#guard outVal (Ochr.evalCore 100 false (.place (.var 1)) none) (stXY .zero) 1000 == (.zero, none)
-- the first statement's refutation: `x` stored at `Unit`: `0` at `Unit`
def stUnitX : MState :=
  { stXY .zero with env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tUnit, val := .loan 0, decl := .other },
     { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := .borrow 0 .zero, decl := .other }] }] }
#guard outVal (Ochr.evalCore 100 true (.place (.var 1)) none) stUnitX 1000 == (.zero, some .tUnit)

end ColumnB

end Ochr.Meaning.Steps.Form
