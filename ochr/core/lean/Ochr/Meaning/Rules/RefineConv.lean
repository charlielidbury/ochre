import Ochr.Meaning.Rules.Refine
import Ochr.Meaning.Steps.DropOne

/-!
# The rules trial, part B proved: a successful comparison is a derivation

By induction on fuel, over `conv`, `convList`, `convT`, `convTList` and `convFn` together. The
generic sub-computations (`convPi` as a whole, `convFnRun`) are the premises of [Conv-pi] and
[Conv-fun]; what B takes as given about them is only that they keep the state as a private
computation does (`GenericKept`, machine-side, model-free). Everything else is proved.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem Reach.refl (st : MState) : Reach st st :=
  ⟨⟨rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _⟩, rfl, rfl⟩

theorem Reach.trans {a b c : MState} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  obtain ⟨⟨e1, g1, r1, i1, s1, t1, n1⟩, gl1, cs1⟩ := h₁
  obtain ⟨⟨e2, g2, r2, i2, s2, t2, n2⟩, gl2, cs2⟩ := h₂
  refine ⟨⟨e2.trans e1, g2.trans g1, r2.trans r1, i2.trans i1, Nat.le_trans s1 s2, fun σ hσ => ?_,
    Nat.le_trans n1 n2⟩, gl2.trans gl1, cs2.trans cs1⟩
  rw [t2 σ (Nat.lt_of_lt_of_le hσ s1), t1 σ hσ]

theorem Reach.of_eq {a b : MState} (h : b = a) : Reach a b := h ▸ Reach.refl a

/-- What B takes as given about the generic sub-computations: they keep the state as a private
computation does (true by construction if a comparison restores its start state). -/
structure GenericKept : Prop where
  pi : ∀ fuel P Q st st' bh (b : Bool), Runs (Ochr.convPi fuel P Q) st bh b st' → Reach st st'
  fnRun : ∀ fuel f g pf cs hs ds c st st' bh (b : Bool),
    Runs (Ochr.convFnRun fuel f g pf cs hs ds c) st bh b st' → Reach st st'

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

/-- `conv` at `fuel`: from any state the comparison reached, the state after is reached too, and a
`true` answer is a derivation. -/
def ConvOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (v w : Value) (bh : Nat) (b : Bool), Reach st₀ st →
    Runs (Ochr.conv fuel v w) st bh b st' →
    Reach st₀ st' ∧ (b = true → ConvV Syn.machine (machPremises st₀) st₀.globals v w)

def ConvListOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (vs ws : List Value) (bh : Nat) (b : Bool), Reach st₀ st →
    Runs (Ochr.convList fuel vs ws) st bh b st' →
    Reach st₀ st' ∧ (b = true → ConvL Syn.machine (machPremises st₀) st₀.globals vs ws)

def ConvTOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (t u : Term) (bh : Nat) (b : Bool), Reach st₀ st →
    Runs (Ochr.convT fuel t u) st bh b st' →
    Reach st₀ st' ∧ (b = true → ConvT Syn.machine (machPremises st₀) st₀.globals t u)

def ConvTListOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (ts us : List Term) (bh : Nat) (b : Bool), Reach st₀ st →
    Runs (Ochr.convTList fuel ts us) st bh b st' →
    Reach st₀ st' ∧ (b = true → ConvTL Syn.machine (machPremises st₀) st₀.globals ts us)

def ConvFnOK (fuel : Nat) : Prop :=
  ∀ (st₀ st st' : MState) (f g : Value) (bh : Nat) (b : Bool), Reach st₀ st → isFnV f = true →
    isFnV g = true → Runs (Ochr.convFn fuel f g) st bh b st' →
    Reach st₀ st' ∧ (b = true → ConvH Syn.machine (machPremises st₀) st₀.globals f g)

/-- The five at one fuel. -/
def AllOK (fuel : Nat) : Prop := ConvOK fuel ∧ ConvListOK fuel ∧ ConvTOK fuel ∧ ConvTListOK fuel ∧ ConvFnOK fuel

theorem allOK_zero : AllOK 0 := by
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

theorem convList_step {n : Nat} (ih : AllOK n) : ConvListOK (n + 1) := by
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

theorem convTList_step {n : Nat} (ih : AllOK n) : ConvTListOK (n + 1) := by
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

end Ochr.Meaning.Rules

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem convT_step {n : Nat} (ih : AllOK n) : ConvTOK (n + 1) := by
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

end Ochr.Meaning.Rules

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem isFn_match (x : Value) :
    (match x with | Value.gfn _ => true | Value.clo _ _ _ => true | _ => false) = isFnV x := by
  cases x <;> rfl

theorem conv_step (hk : GenericKept) {n : Nat} (ih : AllOK n) : ConvOK (n + 1) := by
  intro st₀ st st' v w bh b hr h
  unfold Ochr.conv at h
  split at h
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨hr, fun _ => .refl (by assumption)⟩
  · simp only at h
    have unitD : ConvH Syn.machine (machPremises st₀) st₀.globals (unitTop v) (unitTop w) →
        ConvV Syn.machine (machPremises st₀) st₀.globals v w := fun d => .unit trivial trivial d
    generalize unitTop v = v' at h unitD
    generalize unitTop w = w' at h unitD
    split at h
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h
      exact ⟨hr, fun _ => unitD (.refl (by assumption))⟩
    · split at h
      · obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h
        exact ⟨r1, fun hb => unitD (.succ (d1 hb))⟩
      · obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h
        exact ⟨r1, fun hb => unitD (.tRef (d1 hb))⟩
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨r1, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        refine ⟨r1, fun hb => ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨rfl, e1⟩ := hb
        exact unitD (.tInd (d1 e1))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
        obtain ⟨x3, s3, _, h3, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h1
        obtain ⟨r2, d2⟩ := ih.1 st₀ _ _ _ _ _ _ r1 h2
        obtain ⟨r3, d3⟩ := ih.1 st₀ _ _ _ _ _ _ r2 h3
        refine ⟨r3, fun hb => ?_⟩
        simp only [Bool.and_eq_true] at hb
        exact unitD (.tEq (d1 hb.1.1) (d2 hb.1.2) (d3 hb.2))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨r1, d1⟩ := ih.1 st₀ _ _ _ _ _ _ hr h1
        refine ⟨r1, fun hb => ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨rfl, e1⟩ := hb
        exact unitD (.borrow (d1 e1))
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨rfl, rfl⟩ := runs_pure_inv h
        obtain ⟨r1, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        refine ⟨r1, fun hb => ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        obtain ⟨⟨rfl, rfl⟩, e1⟩ := hb
        exact unitD (.ind (fun h => by cases h) (d1 e1))
      · obtain ⟨r1, d1⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ hr h
        exact ⟨r1, fun hb => unitD (.sealed (d1 hb))⟩
      · obtain ⟨x1, s1, _, h1, h⟩ := Runs.bind_inv h
        obtain ⟨x2, s2, _, h2, h⟩ := Runs.bind_inv h
        obtain ⟨r1, d1⟩ := ih.2.1 st₀ _ _ _ _ _ _ hr h1
        obtain ⟨r2, d2⟩ := ih.2.2.1 st₀ _ _ _ _ _ _ r1 h2
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := runs_pure_inv h
          simp only [Bool.and_eq_true] at hc
          exact ⟨r2, fun _ => unitD (.piCong (rdEq_of_beq _ _ hc.1.1) (d1 hc.1.2) (d2 hc.2))⟩
        · exact ⟨r2.trans (hk.pi _ _ _ _ _ _ _ h),
            fun hb => by subst hb; exact unitD (.pi ⟨_, _, _, _, r2, h⟩)⟩
      · split at h <;> split at h <;>
          simp only [Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, reduceIte,
            Bool.false_eq_true] at h <;>
          first
          | (obtain ⟨rfl, rfl⟩ := runs_pure_inv h; exact ⟨hr, fun h => by cases h⟩)
          | (exact ih.2.2.2.2 st₀ _ _ _ _ _ _ hr rfl rfl h |>.imp id (fun d hb => unitD (d hb)))

end Ochr.Meaning.Rules

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem convFn_step (hk : GenericKept) {n : Nat} (ih : AllOK n) : ConvFnOK (n + 1) := by
  intro st₀ st st' f g bh b hr hf hg h
  unfold Ochr.convFn at h
  obtain ⟨s0, s1, _, h0, h1⟩ := Runs.bind_inv h
  obtain ⟨rfl, rfl⟩ := runs_get_inv h0
  split at h1
  · obtain ⟨rfl, rfl⟩ := runs_pure_inv h1; exact ⟨hr, fun h => by cases h⟩
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
          refine ⟨r5.trans (hk.fnRun _ _ _ _ _ _ _ _ _ _ _ _ h9), fun hb => ?_⟩
          subst hb
          have gl := hr.2.1
          rw [gl] at hpf hpg
          exact .fn hf hg hpf hpg (d4 hx) (d5 hy) ⟨_, _, _, _, _, cs, hs, ds, c, rd, r5, hpf, rfl, h9⟩
        · obtain ⟨rfl, rfl⟩ := runs_pure_inv h9; exact ⟨r5, fun h => by cases h⟩
      · obtain ⟨rfl, rfl⟩ := runs_pure_inv h9; exact ⟨r5, fun h => by cases h⟩
    · obtain ⟨rfl, rfl⟩ := runs_pure_inv h7; exact ⟨r4, fun h => by cases h⟩

end Ochr.Meaning.Rules

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem allOK (hk : GenericKept) : ∀ n, AllOK n
  | 0 => allOK_zero
  | n + 1 =>
    have ih := allOK hk n
    ⟨conv_step hk ih, convList_step ih, convT_step ih, convTList_step ih, convFn_step hk ih⟩

/-- **(B) `conv`, proved**: a successful comparison is a derivation of the machine's instance of
conversion, whose generic premises are the machine's runs of `convPi` and `convFnRun` from states
the comparison reached; and the state after is reached from the one before (`KeptAfter`, Σ and the
comparison stack kept). Assumes only that those two generic sub-computations keep the state as
a private computation does (`GenericKept`). -/
theorem conv_refine' (hk : GenericKept) (fuel : Nat) (st st' : MState) (v w : Value) (bh : Nat)
    (h : Runs (Ochr.conv fuel v w) st bh true st') :
    ConvV Syn.machine (machPremises st) st.globals v w ∧ KeptAfter st st' := by
  obtain ⟨r, d⟩ := (allOK hk fuel).1 st st st' v w bh true (Reach.refl st) h
  exact ⟨d rfl, r.1⟩

end Ochr.Meaning.Rules

#print axioms Ochr.Meaning.Rules.conv_refine'
