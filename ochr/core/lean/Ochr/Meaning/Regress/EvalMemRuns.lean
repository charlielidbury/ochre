import Ochr.Meaning.Regress.EvalMemGap
import Ochr.Meaning.Steps.EvalMem
import Ochr.Meaning.Regress.DataCodes

/-!
# Typed temporaries on concrete runs (sixth lead, docs/31 D81; kernel-checked)

1. **A borrow argument in flight, under the new form** (`goodT_SB`). `f(&x)` with `x : Nat`: the
   checker's [Borrow] from `x : Nat ↦ 0` returns `borrow_0 0` and leaves `x ↦ loan_0`, counter `1`
   (`bp_val`, `bp_bind`, evaluated by the kernel), and `evalCall` pushes the argument as a
   temporary. Untyped (today's `Good`) that state is good at no assignment
   (`EvalMemGap.borrowArg_not_good`). With the temporary typed `&Nat`, the type the evaluation of
   `&x` returned, it is good at every assignment: the temporary types the label `0` at `Nat`, so the
   lender `x` means a member of `Nat` at every typed future.
2. **The value an evaluation returns is a member of the type it returns**, on four typed runs: a
   `let`, a match on a known number, a call of a known closure (its body run), and a constructor
   (`Cons(3, Cons(4, Nil))` at `List(Nat)`, at the probes' data model).
3. **An untyped run binds a value at a type it never checked**: the untyped `let x = (0 : Unit); x`
   runs and binds `x : Unit ↦ 0`; the typed one is rejected.
-/

namespace Ochr.Meaning.Regress.EvalMemRuns
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Regress.EvalMemGap
open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk natB)

/-! ## 1. A borrow argument in flight -/

/-- The checker's [Borrow] of `x` from `x : Nat ↦ 0`. -/
abbrev bp : M Value := Ochr.borrowPlace 10 (.var 0)

def isB00 : Value → Bool
  | .borrow 0 .zero => true
  | _ => false

def bindLoan0 (st : MState) : Bool :=
  match st.env.toList with
  | [fr] => match fr.binds.toList, fr.temps.toList with
    | [b], [] => (match b.val with | .loan 0 => true | _ => false) && (match b.ty with | some .tNat => true | _ => false)
    | _, _ => false
  | _ => false

/- [Borrow] returns `borrow_0 0`, and leaves one frame with the binding `x : Nat ↦ loan_0` and the
counter `1` (evaluated by `#guard`: the access's walk is well-founded recursion, which the kernel does
not reduce, as in `Regress/StaticLend`). -/
#guard isB00 (outVal bp GenNeutralContent.S 10)
#guard bindLoan0 (outSt bp GenNeutralContent.S 10)
#guard (outSt bp GenNeutralContent.S 10).nextLoan == 1

/-- The state with the argument in flight (`SB` with the counter the checker leaves). -/
def SB1 : MState := { SB with nextLoan := 1 }

/-- The temporary typed `&Nat`, as `evalCore`'s `.borrow` returns it (`T.map .tRef`). -/
def ttB : TempTys := TempTys.none.set 0 0 (some (.tRef .tNat))

theorem allPos_SB1 : allPos SB1.env = [.bind 0 0, .temp 0 0] := by decide +kernel

theorem values_SB1 : Env.values SB1.env = [.loan 0, .borrow 0 .zero] := by
  rw [Env.values, allPos_SB1]; rfl

theorem posTyMT_SB1 (K : RunCtx) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyMT K.dm K.M K.Γ ρ SB1 ttB p = some T) : (p = .bind 0 0 ∨ p = .temp 0 0) ∧ T = TyM.nat := by
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | i
      · simp [MState.posTyMT, MState.posTyM, SB1, SB, Value.tyM, Value.mean, Sem.asTy] at h
        exact ⟨.inl rfl, h.symm⟩
      · simp [MState.posTyMT, MState.posTyM, SB1, SB] at h
    · simp [MState.posTyMT, MState.posTyM, SB1, SB] at h
  | temp f i =>
    rcases f with _ | f
    · rcases i with _ | i
      · simp [MState.posTyMT, SB1, SB, ttB, TempTys.set, Value.tyM, Value.mean, Sem.asTy] at h
        exact ⟨.inr rfl, h.symm⟩
      · simp [MState.posTyMT, SB1, SB] at h
    · simp [MState.posTyMT, SB1, SB] at h

theorem noLabel_bind (p : Pos) (l : Nat) (h : Env.shape SB1.env p = some l) : p = .temp 0 0 ∧ l = 0 := by
  have hm := mem_allPos_of_shape h
  rw [allPos_SB1] at hm
  simp at hm
  rcases hm with rfl | rfl
  · simp [Env.shape, valAt, SB1, SB] at h
  · simp [Env.shape, valAt, SB1, SB] at h; exact ⟨rfl, h.symm⟩

/-- **With the argument's temporary typed `&Nat`, the state is good at every assignment**: a typed
future gives the label `0` a member of `Nat` (its holder, the temporary, is typed), so `x`, which
means the label's final content, is a member of `Nat`; the temporary means `0`. -/
theorem goodT_SB (K : RunCtx) (ρ : Assignment) : GoodT K.dm K.M K.Γ ρ SB1 ttB := by
  have hV := values_SB1
  have hA := allPos_SB1
  have hx : valAt SB1.env (.bind 0 0) = .loan 0 := rfl
  have ht : valAt SB1.env (.temp 0 0) = .borrow 0 .zero := rfl
  -- every site in the state is a loan's, never a fill; none is at a path below anything
  have hsites : ∀ l x, x ∈ Env.sitesOf SB1.env l → x = ⟨.bind 0 0, [], false⟩ := by
    intro l x h
    simp only [Env.sitesOf, hA, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, hx, ht] at h
    rcases h with h | h
    · simp only [Value.sitesOf] at h; split at h <;> simp at h; exact h
    · simp [Value.sitesOf] at h
  refine ⟨⟨fun σ _ h => by simp [SB1, SB] at h, fun n σ h => by simp [SB1, SB] at h,
      fun σ v h => by simp [SB1, SB] at h, fun σ r h => by simp [SB1, SB] at h⟩,
    ⟨?_, fun σ _ h => by simp [SB1, SB] at h, fun G h => by simp [MState.goalM, SB1, SB] at h, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ hφ p T hp
    obtain ⟨hp', rfl⟩ := posTyMT_SB1 K ρ p T hp
    have h0 : φ 0 ∈ₛ[K.dm.read] TyM.nat := hφ (.temp 0 0) 0 rfl TyM.nat
      (by simp [MState.posTyMT, SB1, SB, ttB, TempTys.set, Value.tyM, Value.mean, Sem.asTy])
    rcases hp' with rfl | rfl
    · have e : Env.meanT K.dm K.M K.Γ ρ φ SB1.env ttB (.bind 0 0) = φ 0 := rfl
      rw [e]
      obtain ⟨n, hn⟩ := h0
      exact DataModel.pmem_of_mem K.dm.read K.Γ (by rw [← hn]; simp [Code0.enc, Sem.whole]) ⟨n, hn⟩
    · have e : Env.meanT K.dm K.M K.Γ ρ φ SB1.env ttB (.temp 0 0) = .el0 Nat 0 := rfl
      rw [e]
      exact DataModel.pmem_of_mem K.dm.read K.Γ (by simp [Sem.whole]) ⟨0, rfl⟩
  · intro p T hp
    obtain ⟨-, rfl⟩ := posTyMT_SB1 K ρ p T hp
    rfl
  · rw [hA]; intro p hp; simp at hp
    rcases hp with rfl | rfl
    · rw [hx]; decide
    · rw [ht]; decide
  · intro p _ q _ l hp hq
    rw [(noLabel_bind p l hp).1, (noLabel_bind q l hq).1]
  · rw [hV]; intro v hv l hl; simp at hv
    rcases hv with rfl | rfl
    · simp [Value.outerLoans] at hl; subst hl; decide +kernel
    · simp [Value.outerLoans] at hl
  · intro l; rw [hV]; simp [Value.outerLoans, List.count_cons]; split <;> simp
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, hl⟩ => by
      rw [hA] at hp; simp at hp
      rcases hp with rfl | rfl
      · rw [hx] at hw; cases hw
      · rw [ht] at hw; cases hw; simp [Value.loans] at hl⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide
  · exact MState.refd_lt _ _
      (by rw [hV]; intro v hv σ h; simp at hv
          rcases hv with rfl | rfl <;> simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb hT σ h => by
        rcases f with _ | f
        · rcases i with _ | i
          · simp [SB1, SB] at hb; subst hb; simp at hT; subst hT
            simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h
          · simp [SB1, SB] at hb
        · simp [SB1, SB] at hb)
      (fun f i b P ws j hb hT => by
        rcases f with _ | f
        · rcases i with _ | i
          · simp [SB1, SB] at hb; subst hb; simp at hT
          · simp [SB1, SB] at hb
        · simp [SB1, SB] at hb)
      (fun G hG => by simp [SB1, SB] at hG) (fun m σ' h => by simp [SB1, SB] at h)
      (fun σ' v h => by simp [SB1, SB] at h) (fun σ' T h => by simp [SB1, SB] at h)
  · intro T hT; simp [SB1, SB] at hT
  · intro σ r h; simp [SB1, SB] at h
  · simp [SB1, SB]
  · rw [hV]; intro v hv l hl; simp at hv
    rcases hv with rfl | rfl <;> simp [Value.loans] at hl <;> simp [hl, SB1]
  · intro p T _ f i b _ hb A hA'
    rcases f with _ | f
    · rcases i with _ | i
      · simp [SB1, SB] at hb; subst hb; simp at hA'
      · simp [SB1, SB] at hb
    · simp [SB1, SB] at hb
  · rw [hV]; intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide
  · intro f i b hb T hT
    rcases f with _ | f
    · rcases i with _ | i
      · simp [SB1, SB] at hb; subst hb; simp at hT; subst hT; decide
      · simp [SB1, SB] at hb
    · simp [SB1, SB] at hb
  · intro T hT; simp [SB1, SB] at hT
  · intro G hG; simp [SB1, SB] at hG
  · intro p hp hl; rw [hA] at hp; simp at hp
    rcases hp with rfl | rfl
    · exact ⟨_, rfl⟩
    · rw [ht] at hl; simp [Value.outerLoans] at hl
  · intro v hv; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl <;> rfl
  · intro f i b hb
    rcases f with _ | f
    · rcases i with _ | i
      · simp [SB1, SB] at hb; subst hb
        exact ⟨fun T hT l => by simp at hT; subst hT; rfl, fun P ws j h => by simp at h⟩
      · simp [SB1, SB] at hb
    · simp [SB1, SB] at hb
  · intro T hT; simp [SB1, SB] at hT
  · intro G hG; simp [SB1, SB] at hG
  · intro n σ h; simp [SB1, SB] at h
  · intro σ v h; simp [SB1, SB] at h
  · refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hxs hfill
      rw [hsites k x hxs] at hfill; cases hfill
    · intro pos path hf l _ x hxs hpos
      have e := hsites l x hxs; subst e
      subst hpos
      rw [hx] at hf
      cases path with
      | nil => cases hf
      | cons st ss => cases st <;> simp [Value.follow, stepV] at hf
    · refine ⟨?_, ?_⟩
      · intro v hv l; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl <;> rfl
      · intro v hv; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl <;> rfl

/-! ## 2. The value an evaluation returns, on four typed runs

Each run is the checker's typed `evalCore` from a state good at every assignment; its result (value
and type) is evaluated and fingerprinted (`#guard` where the run reads a place, whose access is
well-founded recursion; `decide +kernel` otherwise), and the value is shown a member of the type the
checker returned, at every future (none of these values holds a loan, so the future is irrelevant),
for every data model where the type is `Nat` and at the probes' data model for `List(Nat)`. -/

def nT (k : Nat) : Term := match k with | 0 => .zero | k + 1 => .succ (nT k)
def nV (k : Nat) : Value := match k with | 0 => .zero | k + 1 => .succ (nV k)

/-- `let x = 1; S(x)` (a `let`). -/
def letT : Term := .letIn ⟨"x"⟩ (nT 1) (.succ (.place (.var 0)))
/-- `let n = 2; match n { Z => Z, S m => m }` (a match on a known number). -/
def matchT : Term := .letIn ⟨"n"⟩ (nT 2) (.matchNat (.var 0) .zero (.place (.proj 0 (.var 0))))
/-- `let f = fix f (n : Nat) : Nat := S(n); f(1)` (a call of a known closure: its body runs). -/
def fnT : Term := .fix ⟨"f"⟩ [⟨"n"⟩] [.nat] .nat none (.succ (.place (.var 0)))
def callT : Term := .letIn ⟨"f"⟩ fnT (.call (.place (.var 0)) [nT 1] false)

/-- The result is the number `k` at `Nat`. -/
def isNatAt (k : Nat) : Value × Option Value → Bool
  | (v, some .tNat) => v == nV k
  | _ => false

#guard isNatAt 2 (outVal (Ochr.evalCore 40 true letT none) S0 40)
#guard isNatAt 1 (outVal (Ochr.evalCore 40 true matchT none) S0 40)
#guard isNatAt 2 (outVal (Ochr.evalCore 60 true callT none) S0 60)

theorem mean_nV (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (ψ : Future) (h : TyS) :
    ∀ k, Value.mean dm C Γ ρ ψ h (nV k) = .el0 Nat k
  | 0 => rfl
  | k + 1 => by
    show (Value.mean dm C Γ ρ ψ (.plain TyM.nat) (nV k)).succ = _
    rw [mean_nV dm C Γ ρ ψ _ k]; exact Sem.succ_el0 k

/-- **A number returned at `Nat` is a member of it**, at every data model, assignment and future. -/
theorem nV_member (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (ψ : Future) (k : Nat) :
    DataModel.pmem dm Γ (Value.mean dm C Γ ρ ψ (Value.tyS dm C Γ ρ .tNat) (nV k))
      (Value.tyM dm C Γ ρ (fun _ => .err) .tNat) := by
  rw [mean_nV]
  exact DataModel.pmem_of_mem dm.read Γ (by simp [Sem.whole]) ⟨k, rfl⟩

/-- `Cons(3, Cons(4, Nil))` at `List(Nat)` (a constructor), with `List` declared. -/
def SL0 : MState := { env := #[{}], inds := [DataModel.Program.listD] }
def nilT : Term := .ctor "List" 0 ⟨"Nil"⟩ [.nat] []
def consT (h t : Term) : Term := .ctor "List" 1 ⟨"Cons"⟩ [.nat] [h, t]
def l34 : Term := consT (nT 3) (consT (nT 4) nilT)

/-- The list `[3, 4]` as the checker builds it, any hints. -/
def vL (h₁ h₂ h₃ : Hint) : Value :=
  .ind "List" 1 h₁ [.tNat] [nV 3, .ind "List" 1 h₂ [.tNat] [nV 4, .ind "List" 0 h₃ [.tNat] []]]

def isL34 : Value × Option Value → Bool
  | (.ind "List" 1 _ [.tNat] [a, .ind "List" 1 _ [.tNat] [b, .ind "List" 0 _ [.tNat] []]], some (.tInd "List" [.tNat])) =>
      a == nV 3 && b == nV 4
  | _ => false

#guard isL34 (outVal (Ochr.evalCore 60 true l34 none) SL0 60)

open Ochr.Meaning.DataModel.Program (dmP listD) in
open Ochr.Meaning.Regress.DataCodes (semL psN rN semL_memTy) in
/-- **The list the checker builds is a member of the type it returns**, at the probes' data model
(`dmP`), any assignment, future and hints: it means the tree `[3, 4]`, a member of `List(Nat)`'s code
(the data layer's `semL_memTy`). -/
theorem vL_member (C : CodeMeaning) (ρ : Assignment) (ψ : Future) (h₁ h₂ h₃ : Hint) :
    DataModel.pmem dmP [listD]
      (Value.mean dmP C [listD] ρ ψ (Value.tyS dmP C [listD] ρ (.tInd "List" [.tNat])) (vL h₁ h₂ h₃))
      (Value.tyM dmP C [listD] ρ (fun _ => .err) (.tInd "List" [.tNat])) := by
  have e : Value.mean dmP C [listD] ρ ψ (Value.tyS dmP C [listD] ρ (.tInd "List" [.tNat])) (vL h₁ h₂ h₃) = semL [3, 4] := by
    simp [vL, Value.mean, Value.meanParams, Value.meanFields, DataModel.ctorR, mean_nV, semL]; rfl
  -- the strict type former: `Nat` is a member of `List`'s parameter type
  have hpo : paramsOk dmP listD [.ty TyM.nat] := by
    intro i v h
    cases i with
    | zero => simp at h; subst h; exact ⟨⟨Nat, .nat, rfl⟩, rfl⟩
    | succ i => simp at h
  have eT : Value.tyM dmP C [listD] ρ (fun _ => .err) (.tInd "List" [.tNat]) = dmP.tyM listD psN := by
    simp [Value.tyM, Value.mean, Value.meanParams, psN, show listD.name = "List" from rfl, hpo, Sem.asTy]
  rw [e, eT]
  exact DataModel.pmem_of_mem dmP.read [listD] (by simp [semL, Sem.whole]) (semL_memTy [3, 4])

/-! ## 3. An untyped run binds at a type it never checked

`(0 : Unit)` run untyped with its type demanded (as a `let` demands its right-hand side's, D82)
returns `0` at `Unit`: the annotation is not re-checked in an untyped run (`evalCore`'s `.ascribe`).
So the untyped `let x = (0 : Unit); x` runs and binds `x : Unit ↦ 0`, a state good at no assignment
(`EvalMemGap.not_good_push`, whose binding differs from this one only in fields `Good` does not read);
the typed run rejects it. -/

def u0 : Term := .ascribe (.val .zero) (.val .tUnit)
def letU : Term := .letIn ⟨"x"⟩ u0 (.place (.var 0))
abbrev u0Demanded : M (Value × Option Value) := do Ochr.demand true; Ochr.eval 10 false u0 none

def isZeroAtUnit : Value × Option Value → Bool
  | (.zero, some .tUnit) => true
  | _ => false

#guard isZeroAtUnit (outVal u0Demanded S0 10)
#guard isOk (Ochr.evalCore 20 false letU none) S0 20
#guard !isOk (Ochr.evalCore 20 true letU none) S0 20

end Ochr.Meaning.Regress.EvalMemRuns
