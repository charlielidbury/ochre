import Ochr.Meaning.DataModel.Examples
import Ochr.Meaning.Run
import Ochr.Examples.Nat
import Ochr.Examples.Bool

/-!
# Opened dependent values: what the model does not mirror (kernel-checked; checker verdicts asserted)

The dependent-values lane's records (`Dep/HANDOFF.md`). The checker's side is the block below,
checked when this file is elaborated, and its states at holes (`#guard`, native: the kernel
cannot run the checker). The model's side is kernel-checked at the probe programs' data model
(`DataModel.Program.dmP`, whose `BW`, `V`, `Fin1` are the hand models of these declarations).
-/

open Ochr Ochr.Test

ochr DepRec uses Nats, Bools {
  def BF (b : Bool) : Type := (match b { false => Nat, true => Unit })
  inductive BW := MkBW(b : Bool, x : BF(b))
  -- (a) the index rewritten, the leaf read at what it holds
  def LeafRead : Nat := (let c = MkBW(false, 5); match c { MkBW(b, x) => (b := true; let y = x; y), })
  reject def LeafReadCtl : Unit := (let c = MkBW(false, 5); match c { MkBW(b, x) => (b := true; let y = x; (y : Unit)), })
  def LeafHonest : Unit := (let c = MkBW(true, ()); match c { MkBW(b, x) => (let y = x; y), })
  def LeafReadAt : Nat := (let c = MkBW(false, 5); match c { MkBW(b, x) => (b := true; let u : Unit = ?; let y = x; y), })
  def LeafHonestAt : Unit := (let c = MkBW(true, ()); match c { MkBW(b, x) => (let u : Unit = ?; let y = x; y), })
  -- (b) a proof field invalidated by a write to its index
  inductive PZ := MkPZ(n : Nat, h : Eq(Nat, n, 1))
  def InvalAt (p : &PZ) : Unit := match *p { MkPZ(n, h) => (n := 0; let u : Unit = ?; n := 1; h := refl), }
  -- (c) a value below no whole member of its type
  inductive Fin1 (n : Nat) := Only(h : Eq(Nat, n, 1))
  inductive V := MkV(n : Nat, x : Fin1(n))
  def BelowAt : Unit := (let c = MkV(1, Only(refl)); match c { MkV(n, x) => (let y = x; n := 0; let u : Unit = ?; ()), })
  -- the same with the dependent field moved out (a non-copy payload)
  inductive FinM (n : Nat) := OnlyM(k : Nat, h : Eq(Nat, n, 1))
  inductive VM := MkVM(n : Nat, x : FinM(n))
  def BelowMovedAt : Unit := (let c = MkVM(1, OnlyM(7, refl)); match c { MkVM(n, x) => (let y = x; n := 0; let u : Unit = ?; ()), })
}

#guard (run "DepRec" DepRec).rejectedWith [
  ("LeafReadCtl", "the ascribed term has type Nat, expected Unit")]

namespace Ochr.Meaning.Dep.Records

def holeΩ (name : String) : List (String × String × String) :=
  let r := Ochr.Test.runWith (some Prelude) "DepRec" DepRec (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map fun (x, T, v) => (x, (T.map Value.pp).getD "?", v.pp))
      | _ => none).headD []
  | none => []

-- (a) After `b := true` the leaf `5` sits under the index `true` (the checker reads it at `Nat`,
-- `LeafReadCtl`); the honest value holds `()` under the same index (read at `Unit`).
#guard holeΩ "LeafReadAt" == [("c", "BW", "MkBW(true, 5)")]
#guard holeΩ "LeafHonestAt" == [("c", "BW", "MkBW(true, ())")]
-- (b) After `n := 0` the checker's proof field is `⊥` (`openWrite`).
#guard holeΩ "InvalAt" == [("p°", "PZ", "loan_0"), ("p", "&PZ", "borrow_0 MkPZ(0, ⊥)")]
-- (c) After `n := 0` the value is open, whole (`Fin1` is a copy type), its field of type
-- `Fin1(1)`; and, with a non-copy payload, open and partly moved.
#guard holeΩ "BelowAt" == [("c", "V", "MkV(0, Only(⋆))"), ("y", "Fin1(1)", "Only(⋆)")]
#guard holeΩ "BelowMovedAt" == [("c", "VM", "MkVM(0, ⊥)"), ("y", "FinM(1)", "OnlyM(7, ⋆)")]


open Ochr.Meaning Ochr.Meaning.DataModel Ochr.Meaning.DataModel.Program Ochr.Meaning.DataLib

theorem unit_ne_nat : Unit ≠ Nat := by
  intro h
  have hs : Subsingleton Nat := h ▸ (inferInstance : Subsingleton Unit)
  exact absurd (hs.elim 0 1) (by decide)

theorem tyM_nat_ne_unit : TyM.nat ≠ TyM.unit := by
  intro h
  simp only [TyM.nat, TyM.unit, TyM.t0.injEq] at h
  exact unit_ne_nat h.1.symm

/-! ## (a) A leaf field's read type -/

/-- `BW`'s field `x`, as a step names it. -/
def gx : FieldRef := ⟨"BW", 0, 1, "x"⟩

/-- **(a) The model's read of a leaf field does not look at the leaf**, at EVERY data model and
declaration list: reading `x` off `MkBW(e, a)` gives `a` at the same type whether `a` is the
number `5` or the unit value (`contentTyS`: a leaf is read at its declaration's field type at the
current earlier fields). The checker reads `5` at `Nat` under the index `true` (`LeafRead`,
`LeafReadCtl`'s message) and `()` at `Unit` under the same index (`LeafHonest`): the meanings of
`Nat` and `Unit` differ (`tyM_nat_ne_unit`), so no data model gives both reads the checker's type,
and `eval_step_stmt`'s `StrAgree` conjunct fails at one of the two accepted reads in every model. -/
theorem leaf_read_type_blind (dm : DataModel) (Γ : List IndDecl) (T : TyS) (r : Rec) (e : Sem) :
    (Sem.follow dm Γ T (.dat "BW" r 0 [e, .el0 Nat 5]) [.field gx]).map (·.2) =
      (Sem.follow dm Γ T (.dat "BW" r 0 [e, .el0 Unit ()]) [.field gx]).map (·.2) := rfl

/-- At the probe programs' model (`BW`'s hand model `bwR`, faithful): the read of `x` off
`MkBW(true, 5)` is at `Unit`, of which `5` is no member. -/
theorem leaf_read_dmP (T : TyS) :
    Sem.follow dmP progDecls T (.dat "BW" bwR 0 [trueV, .el0 Nat 5]) [.field gx] =
      some (.el0 Nat 5, .plain TyM.unit) := by
  rfl

theorem five_not_unit : ¬ (Sem.el0 Nat 5 ∈ₛ[dmP.read] TyM.unit) := by
  rintro ⟨a, ha⟩
  simp only [Code0.enc, Sem.el0.injEq] at ha
  exact unit_ne_nat ha.1

/-! ## (b) No invalidation -/

/-- `PZ`'s field `n`. -/
def gn : FieldRef := ⟨"PZ", 0, 0, "n"⟩

/-- **(b) The model's write to an index field keeps the proof field**, at every data model: `n := 0`
on `MkPZ(1, ⋆)` leaves `MkPZ(0, ⋆)`, where the checker's write leaves `MkPZ(0, ⊥)` (`InvalAt`,
`openWrite`), whose field means `moved` (`bot_means_moved`). The meanings differ at every future,
so `Rel.sim` fails after the step, and `eval_step_stmt` at the assignment is false at `InvalAt`. -/
theorem write_keeps_proof (dm : DataModel) (Γ : List IndDecl) (T : TyS) (r : Rec) :
    Sem.updAt dm Γ T (fun _ => .el0 Nat 0) [.field gn] (.dat "PZ" r 0 [.el0 Nat 1, .proof]) =
      some (.dat "PZ" r 0 [.el0 Nat 0, .proof]) := by
  rw [Sem.updAt_dat' dm Γ T _ (.field gn) [] (by simp) (by decide) rfl]
  rfl

theorem bot_means_moved (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) :
    meanV K ρ φ hint .bot = .moved := by
  rw [meanV]


/-! ## (c) Below no whole member -/

/-- **No member of `V` has the index `0`** (the hand model `vR`, faithful): field `x`'s type at `0`
is `Fin1(0)`, whose one constructor needs `0 = 1`. -/
theorem v_index_zero_empty (f : Sem) : ¬ dmP.Mem vD vR (.dat "V" vR 0 [.el0 Nat 0, f]) := by
  intro hv
  obtain ⟨⟨c, hc⟩, fs, heq, hf⟩ := (mem_iff S vD _ _).1 hv
  simp only [Sem.dat.injEq] at heq
  obtain ⟨-, -, rfl, rfl⟩ := heq
  obtain ⟨_, _, h0, _, f1, _, -, hf1, _⟩ := hf
  simp only [List.cons.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  have hm : dmP.Mem fin1D (fin1Rec (.el Nat 0)) f1 := hf1
  obtain ⟨⟨c', hc'⟩, gs, rfl, hg⟩ := (mem_iff S fin1D _ _).1 hm
  match c', hc' with
  | 0, _ =>
    obtain ⟨g, _, -, hg1, -⟩ := hg
    have hg1' : ∃ p : PLift (Small.el Nat 0 = Small.el Nat 1), encLeaf (.prop _) p = g := hg1
    obtain ⟨⟨hp⟩, -⟩ := hg1'
    simp at hp
  | _ + 1, hc' => exact absurd hc' (by simp [fin1D])

/-- `Fin1(1)`'s one value, the field `BelowAt` leaves under the index `0`. -/
def onlyOne : Sem := .dat "Fin1" (fin1Rec (.el Nat 1)) 0 [.proof]

/-- **(c) The values `BelowAt` and `BelowMovedAt` leave lie below no whole member of `V`**: whatever
the value is a partly moved copy of keeps the index `0`, and no member has it. Partial membership's
member disjunct is false at both, at the faithful model; `pmem` admits them only through `OpenIn`. -/
theorem movedOf_dat_inv {Γ : List IndDecl} {s t : Sem} (h : MovedOf Γ s t) :
    ∀ n r c fs, s = .dat n r c fs → n ≠ "Nat" → t = s ∨ ∃ gs, t = .dat n r c gs ∧ MovedOfList Γ fs gs := by
  cases h with
  | moved => intro _ _ _ _ h; cases h
  | refl => intro _ _ _ _ _ _; exact .inl rfl
  | dat hl =>
    intro _ _ _ _ h _
    simp only [Sem.dat.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inr ⟨_, rfl, hl⟩
  | succ _ => intro _ _ _ _ h hn; simp only [Sem.dat.injEq] at h; exact absurd h.1 (Ne.symm hn)

theorem movedOf_el0_inv {Γ : List IndDecl} {s t : Sem} (h : MovedOf Γ s t) :
    ∀ (A : Type) (a : A), s = .el0 A a → t = s := by
  cases h with
  | moved => intro _ _ h; cases h
  | refl => intro _ _ _; rfl
  | dat _ => intro _ _ h; cases h
  | succ _ => intro _ _ h; cases h

/-- **(c) The values `BelowAt` and `BelowMovedAt` leave lie below no whole member of `V`**: whatever
the value is a partly moved copy of keeps the index `0`, and no member has it. Partial membership's
member disjunct is false at both, at the faithful model; `pmem` admits them only through `OpenIn`. -/
theorem below_no_member (Γ : List IndDecl) (f : Sem) (t : Sem)
    (hm : MovedOf Γ (.dat "V" vR 0 [.el0 Nat 0, f]) t) : ¬ (t ∈ₛ[dmP.read] dmP.tyR vD vR) := by
  intro ht
  have ht' : dmP.Mem vD vR t := (DataModel.mem_tyR dmP vD vR rfl t).1 ht
  rcases movedOf_dat_inv hm _ _ _ _ rfl (by decide) with rfl | ⟨gs, rfl, hl⟩
  · exact v_index_zero_empty f ht'
  · cases hl with
    | cons h0 hl' =>
      cases hl' with
      | cons _ hnil =>
        cases hnil
        rw [movedOf_el0_inv h0 _ _ rfl] at ht'
        exact v_index_zero_empty _ ht'

/-- At `BelowAt`'s value (whole and open) partial membership holds only by `OpenIn`, which admits
ANY whole fields under the type's name and record: the unit value in `x`, too. -/
theorem open_admits_any (Γ : List IndDecl) :
    DataModel.pmem dmP.read Γ (.dat "V" vR 0 [.el0 Nat 0, onlyOne]) (dmP.tyR vD vR) ∧
    DataModel.pmem dmP.read Γ (.dat "V" vR 0 [.el0 Nat 0, .el0 Unit ()]) (dmP.tyR vD vR) := by
  refine ⟨.inr ⟨_, ?_, .refl _, .inr ⟨rfl, rfl, ?_⟩⟩, .inr ⟨_, ?_, .refl _, .inr ⟨rfl, rfl, ?_⟩⟩⟩ <;>
    simp [Sem.whole, onlyOne]

end Ochr.Meaning.Dep.Records
