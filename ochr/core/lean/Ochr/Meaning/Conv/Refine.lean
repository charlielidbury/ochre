import Ochr.Meaning.Conv.Statement
import Ochr.Meaning.Steps.DropOne
import Ochr.Meaning.Steps.Machine.StepInv

/-!
# N3's machine half (part B): a successful comparison is a derivation (conv1, 2026-11-28)

The old attempt's `Rules/RefineConv.lean`, re-proved against today's checker, whose `conv`, `convPi`
and `convFn` put back the state they started from but for names (main's D103, `Env.restoreNames`).
By induction on fuel over `conv`, `convList`, `convT`, `convTList` and `convFn` together: from a state
that differs from the comparison's start only in names (`NamesKept`), a run leaves such a state, and
a `true` answer is a derivation of the machine's instance of conversion (`Conv/Rules.lean`), whose
generic premises are the machine's runs of `convPi` and `convFnRun` from such states.

**Nothing is assumed.** The old attempt's one assumption, `GenericKept` (the generic sub-computations
keep the state as a private computation does), is gone: under D103 each wrapped comparison's final
state is its start state but for names, whatever its inner runs did, which is proved here from the
checker's code and the machine lane's `machineGrows` (the tables only grow).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Machine

/-! ## Comparisons change only names -/

/-- The state `restoreNames saved` leaves when run from `cur` (`Env.restoreNames`). -/
def restoreNamesOf (saved cur : MState) : MState :=
  { saved with nextAbs := cur.nextAbs, nextLoan := cur.nextLoan, nextRecUid := cur.nextRecUid,
               absTy := saved.absTy ++ cur.absTy.extract saved.absTy.size cur.absTy.size,
               absDecl := cur.absDecl }

theorem NamesKept.refl (st : MState) : NamesKept st st :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem NamesKept.trans {a b c : MState} (h₁ : NamesKept a b) (h₂ : NamesKept b c) : NamesKept a c := by
  obtain ⟨e1, n1, l1, s1, t1, ds1, dt1⟩ := h₁
  obtain ⟨e2, n2, l2, s2, t2, ds2, dt2⟩ := h₂
  refine ⟨?_, Nat.le_trans n1 n2, Nat.le_trans l1 l2, Nat.le_trans s1 s2, fun σ hσ => ?_,
    Nat.le_trans ds1 ds2, fun σ hσ => ?_⟩
  · rw [e2, e1]
  · rw [t2 σ (Nat.lt_of_lt_of_le hσ s1), t1 σ hσ]
  · rw [dt2 σ (Nat.lt_of_lt_of_le hσ ds1), dt1 σ hσ]

theorem NamesKept.globals {a b : MState} (h : NamesKept a b) : b.globals = a.globals := by
  rw [h.1]

/-- A wrapped comparison's exit: the start state but for names, given that the tables only grew. -/
theorem namesKept_restoreNamesOf {st s₁ : MState} (hg : TablesGrow st (restoreNamesOf st s₁)) :
    NamesKept st (restoreNamesOf st s₁) := by
  refine ⟨rfl, hg.nextAbs, hg.nextLoan, ?_, fun σ hσ => ?_, hg.size, hg.old⟩
  · simp [restoreNamesOf]
  · simp only [restoreNamesOf]
    rw [Array.getElem?_append_left hσ]

/-- The exit of `conv`, `convPi`, `convFn` (D103): `restoreNames saved; pure r`. -/
theorem runs_restoreNames_pure {saved s₁ st' : MState} {b₁ : Nat} {r r' : Bool}
    (h : Runs (Ochr.restoreNames saved >>= fun _ => (pure r : M Bool)) s₁ b₁ r' st') :
    r' = r ∧ st' = restoreNamesOf saved s₁ := by
  unfold Ochr.restoreNames at h
  rw [runs_modify_bind] at h
  obtain ⟨h1, h2⟩ := runs_pure_inv h
  exact ⟨h1, h2⟩

/-- A relation between the state a comparison starts from and the states it passes through:
reflexive, transitive, keeping Σ. `Reach` (the checker as it is) and equality (a checker whose
comparisons restore their start state: the target form). -/
structure StateRel where
  rel : MState → MState → Prop
  refl : ∀ a, rel a a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  globals : ∀ {a b}, rel a b → b.globals = a.globals
  ofNames : ∀ {a b}, NamesKept a b → rel a b



/-- `NamesKept`, as a relation of the induction. -/
def StateRel.names : StateRel := ⟨NamesKept, NamesKept.refl, NamesKept.trans, NamesKept.globals, id⟩

theorem runs_exhausted_false {α : Type} {m : String} {a : α} {st st' : MState} {b : Nat}
    (h : Runs (exhausted m : M α) st b a st') : False := by
  obtain ⟨L, left, log, h⟩ := h
  simp [runMachineL_exhausted] at h

/-- `(r == r') = true` on recorded readings is the machine's `RdEq`. -/
theorem rdEq_of_beq : ∀ (r r' : List (DeclInfo × Value)), (r == r') = true → RdEq Syn.machine r r'
  | [], [], _ => trivial
  | (d, a) :: as, (e, b) :: bs, h => by
    simp only [List.cons_beq_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (d == e && a == b) = true := h1
    simp only [Bool.and_eq_true] at h1'
    exact ⟨h1'.1, h1'.2, rdEq_of_beq as bs h2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem runs_lookupGlobal_inv {n : String} {st st' : MState} {b : Nat} {g : GDef}
    (h : Runs (Ochr.lookupGlobal n) st b g st') : st' = st ∧ st.globals.find? (·.name == n) = some g := by
  unfold Ochr.lookupGlobal at h
  obtain ⟨x, st₁, b₁, hg, h2⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv hg
  split at h2
  · rename_i d' hd
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
    exact ⟨rfl, hd⟩
  · exact (runs_err_false h2).elim

/-- A function value's Π-type, read off the declarations or its code; the state unchanged. -/
theorem runs_funType_inv {fuel : Nat} {f pf : Value} {st st' : MState} {b : Nat} (hf : isFnV f = true)
    (h : Runs (Ochr.funType fuel f none) st b pf st') : st' = st ∧ fnTyOf st.globals f = some pf := by
  match fuel with
  | 0 => unfold Ochr.funType at h; exact (runs_exhausted_false h).elim
  | n + 1 =>
    unfold Ochr.funType at h
    obtain ⟨o, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    match n with
    | 0 => unfold Ochr.funType? at h1; exact (runs_exhausted_false h1).elim
    | m + 1 =>
      unfold Ochr.funType? at h1
      simp only at h1
      have fin : ∀ T, o = some T → Runs (pure T : M Value) st₁ b₁ pf st' → st' = st₁ ∧ pf = T :=
        fun T _ hr => by obtain ⟨rfl, rfl⟩ := runs_pure_inv hr; exact ⟨rfl, rfl⟩
      match f, hf with
      | .gfn nm, _ =>
        obtain ⟨g, st₂, b₂, hl, hp⟩ := Runs.bind_inv h1
        obtain ⟨rfl, hfind⟩ := runs_lookupGlobal_inv hl
        obtain ⟨rfl, rfl⟩ := runs_pure_inv hp
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
        exact ⟨rfl, by simp [fnTyOf, hfind]⟩
      | .clo cs t rd, _ =>
        match t with
        | .fix _ hs ds c _ _ =>
          obtain ⟨rfl, rfl⟩ := runs_pure_inv h1
          obtain ⟨rfl, rfl⟩ := runs_pure_inv h2
          exact ⟨rfl, rfl⟩
        | .val _ | .place _ | .borrow _ | .assign _ _ | .letIn _ _ _ | .seq _ _ | .matchNat _ _ _
        | .const _ | .sort _ | .pi _ _ _ | .call _ _ _ | .nat | .zero | .succ _ | .unit | .tt
        | .eq _ _ _ | .cong _ _ | .ref _ | .id _ _ _ | .ascribe _ _ | .prim _ _ | .tind _ _
        | .ctor _ _ _ _ _ | .matchInd _ _ _ =>
          obtain ⟨rfl, rfl⟩ := runs_pure_inv h1
          exact (runs_err_false h2).elim

/-! ## The induction -/

section
variable (R : StateRel)

/-- `conv` at `fuel`: from any state the comparison reached, the state after is reached too, and a
`true` answer is a derivation. -/
def ConvOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (v w : Value) (bh : Nat) (b : Bool), R.rel st₀ st →
    Runs (Ochr.conv fuel v w) st bh b st' →
    R.rel st₀ st' ∧ (b = true → ConvV Syn.machine (machPremisesR R.rel st₀) st₀.globals v w)

def ConvListOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (vs ws : List Value) (bh : Nat) (b : Bool), R.rel st₀ st →
    Runs (Ochr.convList fuel vs ws) st bh b st' →
    R.rel st₀ st' ∧ (b = true → ConvL Syn.machine (machPremisesR R.rel st₀) st₀.globals vs ws)

def ConvTOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (t u : Term) (bh : Nat) (b : Bool), R.rel st₀ st →
    Runs (Ochr.convT fuel t u) st bh b st' →
    R.rel st₀ st' ∧ (b = true → ConvT Syn.machine (machPremisesR R.rel st₀) st₀.globals t u)

def ConvTListOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (ts us : List Term) (bh : Nat) (b : Bool), R.rel st₀ st →
    Runs (Ochr.convTList fuel ts us) st bh b st' →
    R.rel st₀ st' ∧ (b = true → ConvTL Syn.machine (machPremisesR R.rel st₀) st₀.globals ts us)

def ConvFnOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (f g : Value) (bh : Nat) (b : Bool), R.rel st₀ st → isFnV f = true →
    isFnV g = true → Runs (Ochr.convFn fuel f g) st bh b st' →
    R.rel st₀ st' ∧ (b = true → ConvH Syn.machine (machPremisesR R.rel st₀) st₀.globals f g)

/-- The five at one fuel. -/
def AllOK (fuel : Nat) : Prop := ConvOK R fuel ∧ ConvListOK R fuel ∧ ConvTOK R fuel ∧ ConvTListOK R fuel ∧ ConvFnOK R fuel

theorem allOK_zero : AllOK R 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ h; unfold Ochr.conv at h; exact (runs_exhausted_false h).elim
  · intro _ _ _ vs ws _ _ _ h
    unfold Ochr.convList at h
    split at h
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      exact ⟨by assumption, fun _ => .nil⟩
    · exact (runs_exhausted_false h).elim
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨by assumption, fun h => by cases h⟩
  · intro _ _ _ _ _ _ _ _ h; unfold Ochr.convT at h; exact (runs_exhausted_false h).elim
  · intro _ _ _ ts us _ _ _ h
    unfold Ochr.convTList at h
    split at h
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      exact ⟨by assumption, fun _ => .nil⟩
    · exact (runs_exhausted_false h).elim
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨by assumption, fun h => by cases h⟩
  · intro _ _ _ _ _ _ _ _ _ _ h; unfold Ochr.convFn at h; exact (runs_exhausted_false h).elim

theorem convList_step {n : Nat} (ih : AllOK R n) : ConvListOK R (n + 1) := by
  intro st₀ st st' vs ws bh b hr h
  unfold Ochr.convList at h
  split at h
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hr, fun _ => .nil⟩
  · obtain ⟨x, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    obtain ⟨y, st₂, b₂, h3, h4⟩ := Runs.bind_inv h2
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
    obtain ⟨r1, d1⟩ := ih.1 st₀ st st₁ _ _ _ _ hr h1
    obtain ⟨r2, d2⟩ := ih.2.1 st₀ st₁ _ _ _ _ _ r1 h3
    refine ⟨r2, fun hb => ?_⟩
    simp only [Bool.and_eq_true] at hb
    exact .cons (d1 hb.1) (d2 hb.2)
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨hr, fun h => by cases h⟩

theorem convTList_step {n : Nat} (ih : AllOK R n) : ConvTListOK R (n + 1) := by
  intro st₀ st st' ts us bh b hr h
  unfold Ochr.convTList at h
  split at h
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hr, fun _ => .nil⟩
  · obtain ⟨x, st₁, b₁, h1, h2⟩ := Runs.bind_inv h
    obtain ⟨y, st₂, b₂, h3, h4⟩ := Runs.bind_inv h2
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h4
    obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ st st₁ _ _ _ _ hr h1
    obtain ⟨r2, d2⟩ := ih.2.2.2.1 st₀ st₁ _ _ _ _ _ r1 h3
    refine ⟨r2, fun hb => ?_⟩
    simp only [Bool.and_eq_true] at hb
    exact .cons (d1 hb.1) (d2 hb.2)
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨hr, fun h => by cases h⟩


theorem convT_step {n : Nat} (ih : AllOK R n) : ConvTOK R (n + 1) := by
  intro st₀ st st' t u bh b hr h
  unfold Ochr.convT at h
  split at h
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hr, fun _ => .refl (by assumption)⟩
  · split at h
    · obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h
      exact ⟨r1, fun hb => .val (d1 hb)⟩
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .letIn (d1 hb.1) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .seq (d1 hb.1) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .cong (d1 hb.1) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .ascribe (d1 hb.1) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      refine ⟨r1, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .assign hb.1 (d1 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .matchNat hb.1.1 (d1 hb.1.2) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨rfl, e1⟩, e2⟩ := hb; exact .call (d1 e1) (d2 e2)
    · obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h
      exact ⟨r1, fun hb => .succ (d1 hb)⟩
    · obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h
      exact ⟨r1, fun hb => .ref (d1 hb)⟩
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨x3, s3, _, h3, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      obtain ⟨r3, d3⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r2 h3
      refine ⟨r3, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .eq (d1 hb.1.1) (d2 hb.1.2) (d3 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨x3, s3, _, h3, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      obtain ⟨r3, d3⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r2 h3
      refine ⟨r3, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .id (d1 hb.1.1) (d2 hb.1.2) (d3 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact .pi (d1 hb.1) (d2 hb.2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨x3, s3, _, h3, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      obtain ⟨r3, d3⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r2 h3
      refine ⟨r3, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨⟨rfl, e1⟩, e2⟩, e3⟩ := hb; exact .fix (d1 e1) (d2 e2) (d3 e3)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      refine ⟨r1, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨rfl, e1⟩ := hb; exact .prim (d1 e1)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      obtain ⟨r2, d2⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ r1 h2
      refine ⟨r2, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨⟨rfl, rfl⟩, e1⟩, e2⟩ := hb; exact .ctor (d1 e1) (d2 e2)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      refine ⟨r1, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨rfl, e1⟩ := hb; exact .tind (d1 e1)
    · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
      obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      obtain ⟨r1, d1⟩ := ih.2.2.2.1 st₀ _ _ _ _ _ _ hr h1
      refine ⟨r1, fun hb => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨e0, rfl⟩, e1⟩ := hb; exact .matchInd e0 (d1 e1)
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨hr, fun h => by cases h⟩


theorem isFn_match (x : Value) :
    (match x with | Value.gfn _ => true | Value.clo _ _ _ => true | _ => false) = isFnV x := by
  cases x <;> rfl

/-- `conv`'s inner block (inside D103's wrapper): a `true` answer is a derivation. Its final state is
not asked: the wrapper restores the start state but for names whatever the block did. -/
theorem conv_inner {n : Nat} (ih : AllOK R n) {st₀ st s₁ : MState} {v w : Value} {bh : Nat} {b : Bool}
    (hr : R.rel st₀ st)
    (h : Runs (do
      if v == w then return true
      let v := unitTop v
      let w := unitTop w
      if v == w then return true
      match v, w with
      | .succ a, .succ b | .tRef a, .tRef b => Ochr.conv n a b
      | .tInd n' as, .tInd m bs => pure (n' == m && (← Ochr.convList n as bs))
      | .tEq A a b, .tEq B c d => pure ((← Ochr.conv n A B) && (← Ochr.conv n a c) && (← Ochr.conv n b d))
      | .borrow l a, .borrow m b => pure (l == m && (← Ochr.conv n a b))
      | .ind t c _ _ fs, .ind u d _ _ gs => pure (t == u && c == d && (← Ochr.convList n fs gs))
      | .sealed t, .sealed u => Ochr.convT n t u
      | .tPi cs t r, .tPi ds u r' =>
        if r == r' && (← Ochr.convList n cs ds) && (← Ochr.convT n t u) then return true
        Ochr.convPi n v w
      | f, g =>
        let isFn : Value → Bool := fun | .gfn _ | .clo _ _ _ => true | _ => false
        if isFn f && isFn g then Ochr.convFn n f g else pure false : M Bool) st bh b s₁) :
    b = true → ConvV Syn.machine (machPremisesR R.rel st₀) st₀.globals v w := by
  split at h
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact fun _ => .refl (by assumption)
  · simp only at h
    have unitD : ConvH Syn.machine (machPremisesR R.rel st₀) st₀.globals (unitTop v) (unitTop w) →
        ConvV Syn.machine (machPremisesR R.rel st₀) st₀.globals v w := fun d => .unit trivial trivial d
    generalize unitTop v = v' at h unitD
    generalize unitTop w = w' at h unitD
    split at h
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      exact fun _ => unitD (.refl (by assumption))
    · split at h
      · obtain ⟨_, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h
        exact fun hb => unitD (.succ (d1 hb))
      · obtain ⟨_, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h
        exact fun hb => unitD (.tRef (d1 hb))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨_, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        intro hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨rfl, e1⟩ := hb
        exact unitD (.tInd (d1 e1))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
        obtain ⟨x3, s3, _, h3, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h1
        obtain ⟨r2, d2⟩ := ih.1 st₀ _ _ _ _ _ _ r1 h2
        obtain ⟨_, d3⟩ := ih.1 st₀ _ _ _ _ _ _ r2 h3
        intro hb
        simp only [Bool.and_eq_true] at hb
        exact unitD (.tEq (d1 hb.1.1) (d2 hb.1.2) (d3 hb.2))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨_, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h1
        intro hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨rfl, e1⟩ := hb
        exact unitD (.borrow (d1 e1))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨_, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        intro hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨⟨rfl, rfl⟩, e1⟩ := hb
        exact unitD (.ind (fun h => by cases h) (d1 e1))
      · obtain ⟨_, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h
        exact fun hb => unitD (.sealed (d1 hb))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
        obtain ⟨r1, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := runs_pure_inv h
          simp only [Bool.and_eq_true] at hc
          exact fun _ => unitD (.piCong (rdEq_of_beq _ _ hc.1.1) (d1 hc.1.2) (d2 hc.2))
        · exact fun hb => by subst hb; exact unitD (.pi ⟨_, _, _, _, r2, h⟩)
      · split at h <;> split at h <;>
          simp only [Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, reduceIte,
            Bool.false_eq_true] at h <;>
          first
          | (obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact fun h => by cases h)
          | (exact fun hb => unitD ((ih.2.2.2.2 st₀ _ _ _ _ _ _ hr rfl rfl h).2 hb))

theorem grows_restoreNamesOf_conv {n : Nat} {v w : Value} {st s₁ : MState} {bh : Nat} {b : Bool}
    (h : Runs (Ochr.conv n v w) st bh b (restoreNamesOf st s₁)) : TablesGrow st (restoreNamesOf st s₁) :=
  Runs.grows (grows_conv _ _ _) h

theorem conv_step {n : Nat} (ih : AllOK R n) : ConvOK R (n + 1) := by
  intro st₀ st st' v w bh b hr h
  have hg := Runs.grows (grows_conv _ _ _) h
  rw [Ochr.conv.eq_1] at h
  obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
  replace h₁ := Runs.onFail_inv h₁
  obtain ⟨rfl, rfl⟩ := runs_restoreNames_pure h₂
  exact ⟨R.trans hr (R.ofNames (namesKept_restoreNamesOf hg)), conv_inner R ih hr h₁⟩

theorem grows_convFn' (n : Nat) (f g : Value) : GrowsM (Ochr.convFn n f g) :=
  growsM_of_growsIn fun _ => (machineGrows n).convFn f g

theorem convFn_step {n : Nat} (ih : AllOK R n) : ConvFnOK R (n + 1) := by
  intro st₀ st st' f g bh b hr hf hg h
  have hgr := Runs.grows (grows_convFn' _ _ _) h
  rw [Ochr.convFn.eq_1] at h
  obtain ⟨r', s₁, b₁, h₁, h₂⟩ := Runs.bind_inv (runs_get_bind.mp h)
  replace h₁ := Runs.onFail_inv h₁
  obtain ⟨rfl, rfl⟩ := runs_restoreNames_pure h₂
  refine ⟨R.trans hr (R.ofNames (namesKept_restoreNamesOf hgr)), ?_⟩
  clear h₂ hgr h
  obtain ⟨s0, s1, _, h0, h1⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := runs_get_inv h0
  split at h1
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h1; exact fun h => by cases h
  · obtain ⟨pf, s2, _, h2, h3⟩ := Runs.bind_inv h1
    obtain ⟨rfl, hpf⟩ := runs_funType_inv hf h2
    obtain ⟨pg, s3, _, h4, h5⟩ := Runs.bind_inv h3
    obtain ⟨rfl, hpg⟩ := runs_funType_inv hg h4
    obtain ⟨x, s4, _, h6, h7⟩ := Runs.bind_inv h5
    obtain ⟨r4, d4⟩ := ih.1 st₀ _ _ _ _ _ _ hr h6
    split at h7
    · rename_i hx
      simp only at h7
      obtain ⟨y, s5, _, h8, h9⟩ := Runs.bind_inv h7
      obtain ⟨r5, d5⟩ := ih.2.1 st₀ _ _ _ _ _ _ r4 h8
      split at h9
      · rename_i hy
        split at h9
        · rename_i _ cs hs ds c rd
          intro hb
          subst hb
          have gl := R.globals hr
          rw [gl] at hpf hpg
          exact .fn hf hg hpf hpg (d4 hx) (d5 hy) ⟨_, _, _, _, _, cs, hs, ds, c, rd, r5, hpf, rfl, h9⟩
        · obtain ⟨rfl, rfl⟩ := runs_pure_inv h9; exact fun h => by cases h
      · obtain ⟨rfl, rfl⟩ := runs_pure_inv h9; exact fun h => by cases h
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h7; exact fun h => by cases h

theorem allOK : ∀ n, AllOK R n
  | 0 => allOK_zero R
  | n + 1 =>
    have ih := allOK n
    ⟨conv_step R ih, convList_step R ih, convT_step R ih, convTList_step R ih, convFn_step R ih⟩

end

/-- **N3's machine half, for `conv`, PROVED, assuming nothing**: a successful comparison answering
`true` is a derivation of the machine's instance of conversion (`Conv/Rules.lean`), whose generic
premises are the machine's own runs of `convPi` and `convFnRun` from states differing from the start
only in names; and the state after differs from the state before only in names (D103). -/
theorem conv_refine (fuel : Nat) (st st' : MState) (v w : Value) (bh : Nat)
    (h : Runs (Ochr.conv fuel v w) st bh true st') :
    ConvV Syn.machine (machPremises st) st.globals v w ∧ NamesKept st st' := by
  obtain ⟨r, d⟩ := (allOK StateRel.names fuel).1 st st st' v w bh true (NamesKept.refl st) h
  exact ⟨d rfl, r⟩

/-- Every comparison, whatever its answer, changes only names. -/
theorem conv_namesKept {fuel : Nat} {st st' : MState} {v w : Value} {bh : Nat} {b : Bool}
    (h : Runs (Ochr.conv fuel v w) st bh b st') : NamesKept st st' :=
  ((allOK StateRel.names fuel).1 st st st' v w bh b (NamesKept.refl st) h).1

end Ochr.Meaning.Conv
