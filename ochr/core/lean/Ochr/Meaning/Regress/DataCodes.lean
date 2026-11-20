import Ochr.Meaning.Apply1

/-!
# Recursive and nested data types have codes (docs/31 D61; built, kernel-checked)

The concrete check asked for before the re-proof: a data type's code names its declaration, its
parameters and its carrier, and an element is read through the data model (`DataModel.read`).
Here, for a recursive declaration (`List(Nat)`) and a nested one (`Rose(Nat)`, whose field `kids`
is a `List(Rose(Nat))`):
- each value, as the run builds it (`ctorM` packs its fields), is a member of its type's code;
- a value is matched by reading its constructor and fields off it (`Sem.parts`);
- a recursive function over a list (`Len`), built along its type's code by filled stages as the
  `.fix` clause builds it (D60), is a member of that code and gives `2` at `[3, 4]`.
The data models here speak for no declaration (`covers` is empty), so their laws hold vacuously;
their carriers, tags, fields and packing are real, and their reading is their own (`readOf`). As
D59 designed it (the code read an element through a function it held), `Rose(Nat)`'s code would
have held itself (docs/31 D61).

The checker's side (`Regress/ShapeProbes.lean`, each verdict asserted): `Len` over `List(Nat)` is
accepted and `Len(Cons(3, Cons(4, Nil)))` is `2` by `refl` (`LenTwo`; `3` is rejected); `Rose`,
the tree `Node(1, Cons(Node(2, Nil), Nil))` and the match `Root` are accepted, and the root is `1`
by `refl` (`RootOfTree`; `2` is rejected).
-/

namespace Ochr.Meaning.Regress.DataCodes
open Ochr Ochr.Meaning

/-! ## `List(Nat)`: a recursive declaration -/

/-- `inductive List (A : Type) := Nil | Cons(h : A, t : List(A))`. -/
def listD : IndDecl :=
  { name := "List", params := [(⟨"A"⟩, .sort 1)],
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 1)])])] }

/-- `List(Nat)`'s parameters' meanings. -/
def psN : List Sem := [.ty TyM.nat]

/-- The meaning of a list of numbers, as the run gives a constructor value: it names its
declaration and parameters, its constructor and its fields, and packs the list. -/
def semL : List Nat → Sem
  | [] => .dat "List" psN 0 [] (some ⟨List Nat, []⟩)
  | h :: t => .dat "List" psN 1 [.el0 Nat h, semL t] (some ⟨List Nat, h :: t⟩)

def tagL : List Nat → Nat
  | [] => 0
  | _ :: _ => 1

def fieldsL : List Nat → List Sem
  | [] => []
  | h :: t => [.el0 Nat h, semL t]

theorem semL_inj : ∀ {l l' : List Nat}, semL l = semL l' → l = l'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [semL, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2
  | [], _ :: _, h => by simp [semL] at h
  | _ :: _, [], h => by simp [semL] at h

open Classical in
/-- Packing a list's fields: a number and a list's meaning. -/
noncomputable def packL : Nat → List Sem → Option (List Nat)
  | 0, [] => some []
  | 1, [f, s] => (f.as Nat).bind fun h => if hs : ∃ t, semL t = s then some (h :: hs.choose) else none
  | _, _ => none

/-- A data model of `List(Nat)` (every declaration's carrier is `List Nat`; it speaks for no
declaration). -/
noncomputable def dmL : DataModel where
  covers _ := False
  car _ _ := List Nat
  fieldTy _ _ _ _ _ := TyM.err
  paramTy _ _ _ := TyM.univ 1
  pack _ _ c fs := packL c fs
  tag x := tagL x
  fields x := fieldsL x
  rank x := x.length
  tag_pack _ h := h.elim
  fields_pack _ h := h.elim
  pack_fields _ h := h.elim
  pack_isSome h := h.elim
  rank_lt _ _ h := h.elim

theorem enc_list (l : List Nat) :
    Code0.enc dmL.read (.data listD [.ty Nat .nat] (List Nat)) l = semL l := by
  cases l <;> simp [Code0.enc, Par0.sems, Par0.sem, dmL, readOf, tagL, fieldsL, semL, psN, TyM.nat, listD]

/-- `List(Nat)`'s type is the code naming `List`, `Nat`, and the carrier. -/
theorem tyM_list : dmL.tyM listD psN = .t0 (List Nat) (.data listD [.ty Nat .nat] (List Nat)) := by
  simp [DataModel.tyM, listD, dmL, DataModel.parsOf, parOf, psN, TyM.nat]

/-- **Every list's meaning is a member of `List(Nat)`'s code.** -/
theorem semL_mem (l : List Nat) : semL l ∈ₛ[dmL.read] dmL.tyM listD psN := by
  rw [tyM_list]; exact ⟨l, enc_list l⟩

/-- **Built**: the run's constructor value `Cons(3, Cons(4, Nil))` (`ctorM` packing its fields) is
the list's meaning. -/
theorem build_list :
    dmL.ctorM listD psN 1 [.el0 Nat 3, dmL.ctorM listD psN 1 [.el0 Nat 4, dmL.ctorM listD psN 0 []]] = semL [3, 4] := by
  have hpack : ∀ h (t : List Nat), packL 1 [.el0 Nat h, semL t] = some (h :: t) := by
    intro h t
    have he : ∃ t', semL t' = semL t := ⟨t, rfl⟩
    have hs : he.choose = t := semL_inj he.choose_spec
    simp [packL, Sem.as, he, hs]
  have hw : ∀ l, (semL l).whole := by
    intro l; induction l with
    | nil => simp [semL, Sem.whole]
    | cons h t ih => simp [semL, Sem.whole, ih]
  have h0 : dmL.ctorM listD psN 0 [] = semL [] := by simp [DataModel.ctorM, dmL, packL, semL, listD]
  have hc : ∀ h t, dmL.ctorM listD psN 1 [.el0 Nat h, semL t] = semL (h :: t) := by
    intro h t
    simp only [DataModel.ctorM]
    rw [if_pos (by simp [Sem.whole, hw t])]
    have hp : dmL.pack listD psN 1 [.el0 Nat h, semL t] = some (h :: t) := hpack h t
    simp only [hp]
    rfl
  rw [h0, hc, hc]

/-- **Matched**: a list's constructor and fields are read off its meaning. -/
theorem match_list (h : Nat) (t : List Nat) : (semL (h :: t)).parts = some (1, [.el0 Nat h, semL t]) := rfl

/-! ## Recursing over a list: `Len (l : List(Nat)) : Nat by l`

The `.fix` clause's construction along the code `Π(l : List(Nat)). Nat`, the body written as the
function on meanings it computes: a match on the list's constructor, the recursive call through
`self` along the same code. -/

section
variable (R : DataRead) {A : Type} (c : Code0 A)

/-- `Π(a : A). Nat` at a domain code `c`. -/
def tOne : Tel (lvl0 R).Code PUnit ((a : A) → Nat × PUnit) :=
  .param PUnit false A c (fun _ => Nat × PUnit) fun _ => .dat PUnit Nat .nat

theorem dec_nat (n : Nat) : Code0.dec R .nat (.el0 Nat n) = some n := Code0.dec_enc R .nat n

/-- The element a recursion stage's closure is built from along `tOne`: filled where the stage is
undefined, the body's number where it is defined. -/
theorem fill_some (φ : Future) (g : List Sem → Option BodyOut) :
    ∃ F, mkTelFillL (lvl0 R) φ (tOne R c) [] (fun fs => some (PUnit.unit, fs)) g = some F ∧
      ∀ a k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩ → F a = (k, PUnit.unit) := by
  have hleaf : ∀ a, ∃ r, mkTelFillL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
      (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g = some r ∧
      ∀ k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩ → r = (k, PUnit.unit) := by
    intro a
    rw [mkTelFillL.eq_1]
    cases hga : g [c.enc R a] with
    | none =>
      have : (g ([] ++ [(lvl0 R).enc c a])) = none := hga
      simp only [this, Option.bind_none]
      exact ⟨_, dif_pos ⟨(0, PUnit.unit)⟩, fun k h => by cases h⟩
    | some o =>
      have : (g ([] ++ [(lvl0 R).enc c a])) = some o := hga
      simp only [this, Option.bind_some]
      cases hl : mkLeafDataL (lvl0 R) φ (extFin false PUnit A)
          (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) Code0.nat o with
      | some r =>
        refine ⟨r, rfl, fun k hk => ?_⟩
        cases hk
        simp [mkLeafDataL, extMkL, dec_nat, Code0.dec_enc] at hl
        exact hl.symm
      | none =>
        refine ⟨_, dif_pos ⟨(0, PUnit.unit)⟩, fun k hk => ?_⟩
        cases hk
        simp [mkLeafDataL, extMkL, dec_nat, Code0.dec_enc] at hl
  have hall : ∀ a, (mkTelFillL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
      (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g).isSome := by
    intro a
    obtain ⟨r, hr, -⟩ := hleaf a
    rw [hr]; rfl
  refine ⟨fun a => (mkTelFillL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
      (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g).get (hall a), ?_, ?_⟩
  · unfold tOne
    rw [mkTelFillL.eq_3, dif_pos hall]
  · intro a k hk
    obtain ⟨r, hr, hrk⟩ := hleaf a
    simp only [hr, Option.get_some, hrk k hk]

/-- A stage's closure along `tOne`, applied at an element where the stage gives `k`, gives `k`. -/
theorem apply_fill (φ : Future) (g : List Sem → Option BodyOut) (a : A) (k : Nat)
    (ha : g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩) :
    applyFnL (lvl0 R) (tOne R c) (closureFillL (lvl0 R) φ (tOne R c) g) [c.enc R a]
      = some (.data (.el0 Nat k) TyM.nat []) := by
  obtain ⟨F, hF, hFa⟩ := fill_some R c φ g
  unfold closureFillL
  rw [hF]
  show (Sem.as _ (.el0 _ F)).bind (fun F => applyTelL (lvl0 R) (tOne R c) (fun _ => []) F [c.enc R a]) = _
  rw [show Sem.as ((a : A) → Nat × PUnit) (.el0 _ F) = some F from (lvl0_lawful R).unpack_pack _ F, Option.bind_some]
  simp only [tOne, applyTelL, lvl0, Code0.dec_enc, hFa a k ha]
  rfl

/-- The element built strictly along `tOne`, where the body gives a number at every element. -/
theorem mk_some (φ : Future) (g : List Sem → Option BodyOut)
    (hg : ∀ a, ∃ k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩) :
    ∃ F, mkTelL (lvl0 R) φ (tOne R c) [] (fun fs => some (PUnit.unit, fs)) g = some F ∧
      ∀ a k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩ → F a = (k, PUnit.unit) := by
  have hleaf : ∀ a k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩ →
      mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
        (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g = some (k, PUnit.unit) := by
    intro a k h
    rw [mkTelL.eq_1]
    show (g [c.enc R a]).bind _ = _
    rw [h]
    simp [mkLeafDataL, extMkL, dec_nat, Code0.dec_enc]
  have hall : ∀ a, (mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
      (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g).isSome := by
    intro a
    obtain ⟨k, hk⟩ := hg a
    rw [hleaf a k hk]; rfl
  refine ⟨fun a => (mkTelL (lvl0 R) φ (Tel.dat PUnit Nat .nat) ([] ++ [(lvl0 R).enc c a])
      (extMkL false PUnit A (fun fs => some (PUnit.unit, fs)) ((lvl0 R).dec c)) g).get (hall a), ?_, ?_⟩
  · unfold tOne
    rw [mkTelL.eq_3, dif_pos hall]
  · intro a k hk
    simp only [hleaf a k hk, Option.get_some]

/-- A closure built strictly along `tOne`, applied at an element where its body gives `k`. -/
theorem apply_strict (φ : Future) (g : List Sem → Option BodyOut)
    (hg : ∀ a, ∃ k, g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩) (a : A) (k : Nat)
    (ha : g [c.enc R a] = some ⟨.el0 Nat k, [], none⟩) :
    applyFnL (lvl0 R) (tOne R c) (closureL (lvl0 R) φ (tOne R c) g) [c.enc R a]
      = some (.data (.el0 Nat k) TyM.nat []) := by
  obtain ⟨F, hF, hFa⟩ := mk_some R c φ g hg
  unfold closureL
  rw [hF]
  show (Sem.as _ (.el0 _ F)).bind (fun F => applyTelL (lvl0 R) (tOne R c) (fun _ => []) F [c.enc R a]) = _
  rw [show Sem.as ((a : A) → Nat × PUnit) (.el0 _ F) = some F from (lvl0_lawful R).unpack_pack _ F, Option.bind_some]
  simp only [tOne, applyTelL, lvl0, Code0.dec_enc, hFa a k ha]
  rfl

end

/-- `List(Nat)`'s code. -/
def cL : Code0 (List Nat) := .data listD [.ty Nat .nat] (List Nat)

/-- `Len`'s body, as the `.fix` clause runs `match l { Nil => Z, Cons(h, t) => S(self(t)) }`: the
match reads the constructor and fields off the value; the recursive call goes through `self` along
the code. -/
noncomputable def lenBody (self : Sem) : List Sem → Option BodyOut
  | [x] => match x.parts with
    | some (0, []) => some ⟨.el0 Nat 0, [], none⟩
    | some (1, [_, t]) => match applyFnL (lvl0 dmL.read) (tOne dmL.read cL) self [t] with
      | some (.data r _ _) => (Code0.dec dmL.read .nat r).map fun k => ⟨.el0 Nat (k + 1), [], none⟩
      | _ => none
    | _ => none
  | _ => none

/-- The stages, each binding `self` to the closure `mk` builds of the stage below. -/
noncomputable def stage (mk : (List Sem → Option BodyOut) → Sem) (k : Nat) : List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none) (fun _ gk => lenBody (mk gk)) k

/-- The decreasing argument's rank: the packed list's length (the model's `rank`). -/
noncomputable def rankOf : List Sem → Nat
  | [x] => match x.elt with
    | some ⟨B, b⟩ => open Classical in if h : B = List Nat then (cast h b).length else 0
    | none => 0
  | _ => 0

noncomputable def gOf (mk : (List Sem → Option BodyOut) → Sem) : List Sem → Option BodyOut :=
  fun args => stage mk (rankOf args + 1) args

theorem rankOf_list (l : List Nat) : rankOf [semL l] = l.length := by
  cases l <;> simp [rankOf, semL, Sem.elt]

/-- With the stages' closures filled (D60), stage `|l| + 1` gives `l`'s length. -/
theorem stage_val (φ : Future) : ∀ l : List Nat,
    stage (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)) (l.length + 1) [semL l]
      = some ⟨.el0 Nat l.length, [], none⟩
  | [] => by simp [stage, lenBody, semL, Sem.parts]
  | h :: t => by
    show lenBody (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)
      (stage (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)) (t.length + 1))) [semL (h :: t)] = _
    have ha := apply_fill dmL.read cL φ _ t t.length (by rw [show cL.enc dmL.read t = semL t from enc_list t]; exact stage_val φ t)
    rw [show cL.enc dmL.read t = semL t from enc_list t] at ha
    simp only [lenBody, semL, Sem.parts, ha, Option.map, dec_nat]
    rfl

/-- **`Len` is a member of its type's code, and `Len([3, 4])` is `2`.** -/
theorem len_member (φ : Future) :
    (closureL (lvl0 dmL.read) φ (tOne dmL.read cL) (gOf (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)))
        ∈ₛ[dmL.read] piTyL (lvl0 dmL.read) (tOne dmL.read cL)) ∧
      applyFnL (lvl0 dmL.read) (tOne dmL.read cL)
        (closureL (lvl0 dmL.read) φ (tOne dmL.read cL) (gOf (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL))))
        [semL [3, 4]] = some (.data (.el0 Nat 2) TyM.nat []) := by
  have hg : ∀ l : List Nat, gOf (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)) [cL.enc dmL.read l]
      = some ⟨.el0 Nat l.length, [], none⟩ := by
    intro l
    rw [show cL.enc dmL.read l = semL l from enc_list l]
    show stage _ (rankOf [semL l] + 1) [semL l] = _
    rw [rankOf_list]; exact stage_val φ l
  obtain ⟨F, hF, -⟩ := mk_some dmL.read cL φ _ fun l => ⟨_, hg l⟩
  have hc : closureL (lvl0 dmL.read) φ (tOne dmL.read cL) (gOf (closureFillL (lvl0 dmL.read) φ (tOne dmL.read cL)))
      = .el0 _ F := by
    unfold closureL; rw [hF]
  refine ⟨by rw [hc]; exact ⟨F, rfl⟩, ?_⟩
  have := apply_strict dmL.read cL φ _ (fun l => ⟨_, hg l⟩) [3, 4] 2 (hg [3, 4])
  rwa [show cL.enc dmL.read [3, 4] = semL [3, 4] from enc_list [3, 4]] at this

/-! ## `Rose(Nat)`: a nested declaration -/

/-- `inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))`. -/
def roseD : IndDecl :=
  { name := "Rose", params := [(⟨"A"⟩, .sort 1)],
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 1)]])])] }

/-- Rose trees of numbers. -/
inductive RoseN
  | node : Nat → List RoseN → RoseN

/-- `Rose(Nat)`'s code: its declaration, its parameter `Nat`, its carrier. It holds no code of
`List(Rose(Nat))`, so it is a term like any other (as D59 designed it, it would have held one, and
through it itself). -/
def cR : Code0 RoseN := .data roseD [.ty Nat .nat] RoseN

/-- The parameters `List` is given in the field `kids`: `Rose(Nat)`'s code. -/
def psR : List Sem := [.ty (.t0 RoseN cR)]

/-- `List(Rose(Nat))`'s code, `kids`'s type: it holds `Rose(Nat)`'s code as a parameter. -/
def cLR : Code0 (List RoseN) := .data listD [.ty RoseN cR] (List RoseN)

mutual
/-- The meaning of a rose tree, as the run gives a constructor value. -/
def semR : RoseN → Sem
  | .node a ks => .dat "Rose" psN 0 [.el0 Nat a, semLR ks] (some ⟨RoseN, .node a ks⟩)
/-- The meaning of a list of rose trees. -/
def semLR : List RoseN → Sem
  | [] => .dat "List" psR 0 [] (some ⟨List RoseN, []⟩)
  | r :: rs => .dat "List" psR 1 [semR r, semLR rs] (some ⟨List RoseN, r :: rs⟩)
end

/-- The second model's declarations: `Rose`, and `List` at rose trees. -/
def isRose (d : IndDecl) : Bool := d.name == "Rose"

def carB : Bool → Type
  | true => RoseN
  | false => List RoseN

def tagB : (b : Bool) → carB b → Nat
  | true, _ => 0
  | false, [] => 0
  | false, _ :: _ => 1

def fieldsB : (b : Bool) → carB b → List Sem
  | true, .node a ks => [.el0 Nat a, semLR ks]
  | false, [] => []
  | false, r :: rs => [semR r, semLR rs]

open Classical in
/-- Packing: a rose from a number and a list of roses' meaning; a list from a rose's meaning and
a list's. -/
noncomputable def packB : (b : Bool) → Nat → List Sem → Option (carB b)
  | true, 0, [f, s] => (f.as Nat).bind fun a =>
      if hs : ∃ ks, semLR ks = s then some (RoseN.node a hs.choose) else none
  | false, 0, [] => some ([] : List RoseN)
  | false, 1, [s₁, s₂] =>
      if h : (∃ r, semR r = s₁) ∧ ∃ rs, semLR rs = s₂ then some (h.1.choose :: h.2.choose) else none
  | _, _, _ => none

/-- A data model of `Rose(Nat)` and `List(Rose(Nat))` (it speaks for no declaration). -/
noncomputable def dmR : DataModel where
  covers _ := False
  car d _ := carB (isRose d)
  fieldTy _ _ _ _ _ := TyM.err
  paramTy _ _ _ := TyM.univ 1
  pack d _ c fs := packB (isRose d) c fs
  tag {d _} x := tagB (isRose d) x
  fields {d _} x := fieldsB (isRose d) x
  rank _ := 0
  tag_pack _ h := h.elim
  fields_pack _ h := h.elim
  pack_fields _ h := h.elim
  pack_isSome h := h.elim
  rank_lt _ _ h := h.elim

theorem isRose_rose : isRose roseD = true := rfl
theorem isRose_list : isRose listD = false := rfl

/-- `Rose(Nat)`'s type is its code. -/
theorem tyM_rose : dmR.tyM roseD psN = .t0 RoseN cR := by
  simp [DataModel.tyM, roseD, dmR, DataModel.parsOf, parOf, psN, TyM.nat, isRose, carB, cR]

/-- `List(Rose(Nat))`'s type, at `Rose(Nat)`'s type, is the code that holds `Rose(Nat)`'s. -/
theorem tyM_listRose : dmR.tyM listD [.ty (dmR.tyM roseD psN)] = .t0 (List RoseN) cLR := by
  rw [tyM_rose]
  simp [DataModel.tyM, listD, dmR, DataModel.parsOf, parOf, isRose, carB, cLR]

theorem enc_rose (r : RoseN) : Code0.enc dmR.read cR r = semR r := by
  cases r
  simp [Code0.enc, Par0.sems, Par0.sem, dmR, readOf, tagB, fieldsB, semR, psN, TyM.nat, cR, roseD, isRose, carB]

theorem enc_listRose (l : List RoseN) : Code0.enc dmR.read cLR l = semLR l := by
  cases l <;> simp [Code0.enc, Par0.sems, Par0.sem, dmR, readOf, tagB, fieldsB, semLR, psR, cLR, listD, isRose, carB]

/-- **Every rose tree's meaning is a member of `Rose(Nat)`'s code.** -/
theorem semR_mem (r : RoseN) : semR r ∈ₛ[dmR.read] dmR.tyM roseD psN := by
  rw [tyM_rose]; exact ⟨r, enc_rose r⟩

/-- **Every list of rose trees (a `kids` field) is a member of `List(Rose(Nat))`'s code.** -/
theorem semLR_mem (l : List RoseN) : semLR l ∈ₛ[dmR.read] dmR.tyM listD [.ty (dmR.tyM roseD psN)] := by
  rw [tyM_listRose]; exact ⟨l, enc_listRose l⟩

theorem semR_inj : ∀ {r r' : RoseN}, semR r = semR r' → r = r'
  | .node .., .node .., h => by
    simp only [semR, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2

theorem semLR_inj : ∀ {l l' : List RoseN}, semLR l = semLR l' → l = l'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [semLR, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2
  | [], _ :: _, h => by simp [semLR] at h
  | _ :: _, [], h => by simp [semLR] at h

mutual
theorem semR_whole : ∀ r : RoseN, (semR r).whole
  | .node a ks => by simp [semR, Sem.whole, semLR_whole ks]
theorem semLR_whole : ∀ l : List RoseN, (semLR l).whole
  | [] => by simp [semLR, Sem.whole]
  | r :: rs => by simp [semLR, Sem.whole, semR_whole r, semLR_whole rs]
end

/-- **Built**: the run's constructor values `Node(1, Cons(Node(2, Nil), Nil))` are the tree's meaning. -/
theorem build_rose :
    dmR.ctorM roseD psN 0 [.el0 Nat 1,
      dmR.ctorM listD psR 1 [dmR.ctorM roseD psN 0 [.el0 Nat 2, dmR.ctorM listD psR 0 []], dmR.ctorM listD psR 0 []]]
      = semR (.node 1 [.node 2 []]) := by
  have hnil : dmR.ctorM listD psR 0 [] = semLR [] := by
    simp [DataModel.ctorM, dmR, packB, isRose, listD, semLR, carB]
  have hnode : ∀ a ks, dmR.ctorM roseD psN 0 [.el0 Nat a, semLR ks] = semR (.node a ks) := by
    intro a ks
    have he : ∃ ks', semLR ks' = semLR ks := ⟨ks, rfl⟩
    have hp : dmR.pack roseD psN 0 [.el0 Nat a, semLR ks] = some (RoseN.node a ks) := by
      show packB true 0 [.el0 Nat a, semLR ks] = _
      simp [packB, Sem.as, he, semLR_inj he.choose_spec]
      rfl
    simp only [DataModel.ctorM]
    rw [if_pos (by simp [Sem.whole, semLR_whole ks])]
    simp only [hp]
    rfl
  have hcons : ∀ r rs, dmR.ctorM listD psR 1 [semR r, semLR rs] = semLR (r :: rs) := by
    intro r rs
    have h1 : ∃ r', semR r' = semR r := ⟨r, rfl⟩
    have h2 : ∃ rs', semLR rs' = semLR rs := ⟨rs, rfl⟩
    have hp : dmR.pack listD psR 1 [semR r, semLR rs] = some (r :: rs) := by
      show packB false 1 [semR r, semLR rs] = _
      simp [packB, h1, h2, semR_inj h1.choose_spec, semLR_inj h2.choose_spec]
      rfl
    simp only [DataModel.ctorM]
    rw [if_pos (by simp [Sem.whole, semR_whole r, semLR_whole rs])]
    simp only [hp]
    rfl
  rw [hnil, hnode, hcons, hnode]

/-- **Matched**: a rose's constructor and fields, and its `kids` list's, are read off the value. -/
theorem match_rose (a : Nat) (r : RoseN) (rs : List RoseN) :
    (semR (.node a (r :: rs))).parts = some (0, [.el0 Nat a, semLR (r :: rs)]) ∧
      (semLR (r :: rs)).parts = some (1, [semR r, semLR rs]) := ⟨rfl, rfl⟩

end Ochr.Meaning.Regress.DataCodes
