import Ochr.Meaning.Apply1
import Ochr.Meaning.Places
import Ochr.Meaning.DataModel.Program
import Ochr.Meaning.ClosureStage

/-!
# Recursive and nested data types have codes; recursion is guarded by height (docs/31 D61, docs/34 §14; kernel-checked)

The concrete check of the data layer, at the probe programs' data model (`DataModel.Program.dmP`,
its signature and records written by hand): a data type's code names its declaration, its record
and its carrier, and an element is read as its meaning, a tree (`DataModel.read`, the bijection
between a carrier and its members). Here, for a recursive declaration (`List(Nat)`) and a nested
one (`Rose(Nat)`, whose field `kids` is a `List(Rose(Nat))`):
- each value, as the run builds it (`ctorM`: the tree of its declaration, record, constructor and
  fields), is a member of its type's code;
- a value is matched by reading its constructor and fields off it (`Sem.parts`);
- a recursive function over a list (`Len`), built along its type's code by stages as the `.fix`
  clause builds them (each stage's `self` the stage below at the weakened function type, docs/34),
  the stage chosen by the height of the argument's meaning
  (`semRank`), is a member of that code and gives `2` at `[3, 4]`;
- **`CountF`** over `List(Rose(Nat))`, whose recursive call is at the head tree's forest (two field
  steps down, through the nested field), built the same way, gives `3` at `F3`'s forest. Under the
  layer before the port, the rank of the decreasing argument was its own declaration's rank of the
  element it packed, which does not decrease along that call (`DataModel/RankCounterexample.lean`,
  against the frozen copy): the stages ran out one call early. The height of the meaning
  decreases along every field step (`semHeight_field_lt`).

The checker's side (`Regress/ShapeProbes.lean`, `DataModel/Probes.lean`, each verdict asserted):
`Len` over `List(Nat)` is accepted and `Len(Cons(3, Cons(4, Nil)))` is `2` by `refl` (`LenTwo`;
`3` is rejected); `Rose`, the tree `Node(1, Cons(Node(2, Nil), Nil))` and the match `Root` are
accepted; `CountF` is accepted and `F3 : Eq(Nat, CountF(…), 3)` by `refl` (`F2`, at `2`, rejected).
The model's own run of the constructor terms is in `Regress/CodeRuns.lean` (`run_list34`,
`run_tree`).
-/

namespace Ochr.Meaning.Regress.DataCodes
open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.DataModel.Program

/-! ## Members of `List` and `Rose`, taken apart -/

/-- A member of `List` at a record is `Nil`, or `Cons(x, t)` with `x` fitting the parameter's
shape and `t` a member. -/
theorem list_mem_cases (r : Rec) (v : Sem) (hv : dmP.Mem listD r v) :
    v = .dat "List" r 0 [] ∨ ∃ x t, v = .dat "List" r 1 [x, t] ∧
      FitsOneM S (shapeOf (r (paramKey 0))) x ∧ dmP.Mem listD r t := by
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (mem_iff S listD r v).1 hv
  match c, hc with
  | 0, _ =>
    left
    have : fs = [] := hf
    subst this; rfl
  | 1, _ =>
    right
    obtain ⟨x, fs', rfl, hx, t, fs'', rfl, ht, hnil⟩ := hf
    have : fs'' = [] := hnil
    subst this
    exact ⟨x, t, rfl, hx, ht⟩
  | n + 2, hc => exact absurd hc (by simp [listD])

/-- A member of `Rose` at a record is `Node(a, k)`, `k` a member of `List(Rose(…))`. -/
theorem rose_mem_cases (r : Rec) (v : Sem) (hv : dmP.Mem roseD r v) :
    ∃ a k, v = .dat "Rose" r 0 [a, k] ∧ FitsOneM S (shapeOf (r (paramKey 0))) a ∧
      dmP.Mem listD (constRec (.data roseD r)) k := by
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (mem_iff S roseD r v).1 hv
  match c, hc with
  | 0, _ =>
    obtain ⟨a, fs', rfl, ha, k, fs'', rfl, hk, hnil⟩ := hf
    have : fs'' = [] := hnil
    subst this
    exact ⟨a, k, rfl, ha, hk⟩
  | n + 1, hc => exact absurd hc (by simp [roseD])

/-! ## `List(Nat)`: a recursive declaration -/

def natE : Entry := .leaf Nat .nat

/-- `List(Nat)`'s parameters' meanings, and its record: `Nat`'s entry. -/
def psN : List Sem := [.ty TyM.nat]
def rN : Rec := constRec natE

theorem recOf_listNat : dmP.recOf listD psN = rN := rfl

/-- The meaning of a list of numbers: the tree the run's constructor clause gives. -/
def semL : List Nat → Sem
  | [] => .dat "List" rN 0 []
  | h :: t => .dat "List" rN 1 [.el0 Nat h, semL t]

theorem semL_mem : ∀ l : List Nat, dmP.Mem listD rN (semL l)
  | [] => mem_intro listD rN ⟨0, by decide⟩ [] rfl
  | h :: t => by
    refine mem_intro listD rN ⟨1, by decide⟩ _ ?_
    exact ⟨_, _, rfl, ⟨h, rfl⟩, _, [], rfl, semL_mem t, rfl⟩

/-- `List(Nat)`'s type is the code naming `List`, its record, and the carrier. -/
theorem tyM_list : dmP.tyM listD psN = .t0 (dmP.car listD rN) (.data listD rN (dmP.car listD rN)) := rfl

/-- **Every list's meaning is a member of `List(Nat)`'s code.** -/
theorem semL_memTy (l : List Nat) : semL l ∈ₛ[dmP.read] dmP.tyM listD psN :=
  (DataModel.mem_tyR dmP listD rN rfl _).2 (semL_mem l)

/-- **Built**: the run's constructor values `Cons(3, Cons(4, Nil))` are the list's meaning. -/
theorem build_list :
    dmP.ctorM listD psN 1 [.el0 Nat 3, dmP.ctorM listD psN 1 [.el0 Nat 4, dmP.ctorM listD psN 0 []]] = semL [3, 4] := rfl

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

/-- `Π(a : A). Nat`'s description, as the `.fix` clause reads it. -/
def dsOne : List PiDom := [⟨false, fun _ => TyM.t0 A c⟩]

def outOne : PiCod := ⟨false, fun _ => TyM.nat⟩

theorem tOne_telL : telL (lvl0 R) (dsOne c) [] PUnit outOne = ⟨(a : A) → Nat × PUnit, tOne R c⟩ := rfl

/-- Stage `k`'s closure, the `self` of stage `k + 1`, at the weakened function type (docs/34). -/
noncomputable def selfOne (φ : Future) (rk : List Sem → Nat) (k : Nat) (gk : List Sem → Option BodyOut) : Res :=
  (closureAt R 1 φ (dsOne c) (weakCod 1 rk k outOne) (stageFn 1 (dsOne c) rk k gk),
    .plain (piTyAt R 1 (dsOne c) (weakCod 1 rk k outOne)))

/-- **A call through a stage's `self` below its bound** gives the stage below's number, when that
stage gives a number at every element below the bound (`ClosureStage.stage_apply`). -/
theorem selfOne_call (φ : Future) (rk : List Sem → Nat) (k : Nat) (gk : List Sem → Option BodyOut)
    (hgood : ∀ a : A, rk [c.enc R a] < k → ∃ n, gk [c.enc R a] = some ⟨.el0 Nat n, [], none⟩)
    (a : A) (n : Nat) (hlt : rk [c.enc R a] < k) (hn : gk [c.enc R a] = some ⟨.el0 Nat n, [], none⟩) :
    ∃ s', callOf R (selfOne R c φ rk k gk) [(c.enc R a, .plain (TyM.t0 A c))] (emptyState 0)
      = some ((.el0 Nat n, .plain TyM.nat), s') := by
  have hmem1 : ∀ args, Steps.DomMembers R (dsOne c) args → ∃ a : A, args = [c.enc R a] := by
    intro args ⟨hl, hm⟩
    match args, hl with
    | [x], _ =>
      obtain ⟨a, ha⟩ := hm 0 x _ rfl rfl
      exact ⟨a, by rw [← ha]⟩
  exact stage_apply R 1 φ (dsOne c) outOne rk k gk ⟨Nat.le_refl 1, by omega⟩ rfl
    (fun _ _ _ => by simp [LevelFit, outOne, TyM.nat])
    (fun args ha hr => by
      obtain ⟨a', rfl⟩ := hmem1 args ha
      obtain ⟨n', hn'⟩ := hgood a' hr
      refine ⟨_, hn', ⟨⟨n', rfl⟩, fun i d hd hr' => ?_⟩, rfl⟩
      rcases i with _ | i
      · simp only [dsOne, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd; cases hr'
      · simp [dsOne] at hd)
    [(c.enc R a, .plain (TyM.t0 A c))] (emptyState 0) ⟨.el0 Nat n, [], none⟩
    ⟨rfl, fun i x d hx hd => by
      rcases i with _ | i
      · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hx
        simp only [dsOne, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hx; subst hd; exact ⟨a, rfl⟩
      · simp at hx⟩
    (fun i d hd => by
      rcases i with _ | i
      · simp only [dsOne, List.getElem?_cons_zero, Option.some.injEq] at hd
        subst hd; simp [LevelFit]
      · simp [dsOne] at hd)
    hlt trivial hn

end

/-- `List(Nat)`'s code. -/
def cL : Code0 (dmP.car listD rN) := .data listD rN (dmP.car listD rN)

/-- An element of the carrier is read as its meaning. -/
theorem enc_cL (x : dmP.car listD rN) : cL.enc dmP.read x = dmP.meanC x := DataModel.read_car dmP x

/-- `Len`'s body, as the `.fix` clause runs `match l { Nil => Z, Cons(h, t) => S(self(t)) }`: the
match reads the constructor and fields off the value; the recursive call goes through `self` at
its type (`callOf`). -/
noncomputable def lenBody (self : Res) : List Sem → Option BodyOut
  | [x] => match x.parts with
    | some (0, []) => some ⟨.el0 Nat 0, [], none⟩
    | some (1, [_, t]) => match callOf dmP.read self [(t, .plain (TyM.t0 _ cL))] (emptyState 0) with
      | some ((r, _), _) => (Code0.dec dmP.read .nat r).map fun k => ⟨.el0 Nat (k + 1), [], none⟩
      | none => none
    | _ => none
  | _ => none

/-- The stages, each binding `self` to `mk k`'s closure of the stage below (`selfOne`). -/
noncomputable def stage (body : Res → List Sem → Option BodyOut) (mk : Nat → (List Sem → Option BodyOut) → Res)
    (k : Nat) : List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none) (fun k gk => body (mk k gk)) k

/-- The decreasing argument's rank, as the `.fix` clause reads it (`RunCongr.fixRank`): the height
of its meaning. -/
noncomputable def rankOf : List Sem → Nat
  | [x] => semRank x
  | _ => 0

noncomputable def gOf (body : Res → List Sem → Option BodyOut) (mk : Nat → (List Sem → Option BodyOut) → Res) :
    List Sem → Option BodyOut :=
  fun args => stage body mk (rankOf args + 1) args

/-- The length of a list's spine, on meanings. -/
def lenV : Sem → Nat
  | .dat _ _ 1 [_, t] => lenV t + 1
  | _ => 0

/-- A stage above a member's height gives its length (the call at the tail reads the stage below's
`self` below its bound). -/
theorem stage_len (φ : Future) : ∀ (n : Nat) (v : Sem), dmP.Mem listD rN v → semHeight v < n →
    stage lenBody (selfOne dmP.read cL φ rankOf) n [v] = some ⟨.el0 Nat (lenV v), [], none⟩
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, v, hv, hn => by
    show lenBody (selfOne dmP.read cL φ rankOf n (stage lenBody (selfOne dmP.read cL φ rankOf) n)) [v] = _
    rcases list_mem_cases rN v hv with rfl | ⟨x, t, rfl, -, ht⟩
    · rfl
    · have hlt : semHeight t < n := by
        have := semHeight_field_lt "List" rN 1 [x, t] t (by simp)
        omega
      obtain ⟨a, ha⟩ := (DataModel.mem_iff_meanC dmP listD rN t).1 ht
      have ih := stage_len φ n t ht hlt
      have hgood : ∀ b : dmP.car listD rN, rankOf [cL.enc dmP.read b] < n →
          ∃ m, stage lenBody (selfOne dmP.read cL φ rankOf) n [cL.enc dmP.read b] = some ⟨.el0 Nat m, [], none⟩ := by
        intro b hb
        rw [enc_cL] at hb ⊢
        exact ⟨_, stage_len φ n _ ((DataModel.mem_iff_meanC dmP listD rN _).2 ⟨b, rfl⟩) hb⟩
      obtain ⟨s', hs⟩ := selfOne_call dmP.read cL φ rankOf n _ hgood a (lenV t)
        (by rw [enc_cL, ha]; exact hlt) (by rw [enc_cL, ha]; exact ih)
      rw [enc_cL, ha] at hs
      simp only [lenBody, Sem.parts, hs, Option.map, dec_nat]
      rfl

/-- **`Len` is a member of its type's code, and `Len([3, 4])` is `2`.** -/
theorem len_member (φ : Future) :
    (closureL (lvl0 dmP.read) φ (tOne dmP.read cL) (gOf lenBody (selfOne dmP.read cL φ rankOf))
        ∈ₛ[dmP.read] piTyL (lvl0 dmP.read) (tOne dmP.read cL)) ∧
      applyFnL (lvl0 dmP.read) (tOne dmP.read cL)
        (closureL (lvl0 dmP.read) φ (tOne dmP.read cL) (gOf lenBody (selfOne dmP.read cL φ rankOf)))
        [semL [3, 4]] = some (.data (.el0 Nat 2) TyM.nat []) := by
  have hg : ∀ a : dmP.car listD rN, gOf lenBody (selfOne dmP.read cL φ rankOf) [cL.enc dmP.read a]
      = some ⟨.el0 Nat (lenV (dmP.meanC a)), [], none⟩ := by
    intro a
    rw [enc_cL]
    exact stage_len φ _ _ ((DataModel.mem_iff_meanC dmP listD rN _).2 ⟨a, rfl⟩) (Nat.lt_succ_self _)
  obtain ⟨F, hF, -⟩ := mk_some dmP.read cL φ _ fun a => ⟨_, hg a⟩
  have hc : closureL (lvl0 dmP.read) φ (tOne dmP.read cL) (gOf lenBody (selfOne dmP.read cL φ rankOf))
      = .el0 _ F := by
    unfold closureL; rw [hF]
  refine ⟨by rw [hc]; exact ⟨F, rfl⟩, ?_⟩
  obtain ⟨a, ha⟩ := (DataModel.mem_iff_meanC dmP listD rN _).1 (semL_mem [3, 4])
  have := apply_strict dmP.read cL φ _ (fun a => ⟨_, hg a⟩) a _ (hg a)
  rw [enc_cL, ha] at this
  exact this

/-! ## `Rose(Nat)`: a nested declaration -/

/-- `Rose(Nat)`'s record (`Nat`'s entry), and `List(Rose(Nat))`'s: `List`'s record whose entry is
`Rose(Nat)`, the record `Rose`'s field `kids` gives. -/
def rRN : Rec := constRec natE
def rF : Rec := constRec (.data roseD rRN)

theorem recOf_roseNat : dmP.recOf roseD psN = rRN := rfl

/-- `List(Rose(Nat))`'s parameter: `Rose(Nat)`'s type. -/
def psR : List Sem := [.ty (dmP.tyM roseD psN)]

theorem recOf_listRose : dmP.recOf listD psR = rF := rfl

def nilV : Sem := .dat "List" rF 0 []
def consV (x xs : Sem) : Sem := .dat "List" rF 1 [x, xs]
def nodeV (a : Nat) (kids : Sem) : Sem := .dat "Rose" rRN 0 [.el0 Nat a, kids]

theorem nil_mem : dmP.Mem listD rF nilV := mem_intro listD rF ⟨0, by decide⟩ [] rfl

theorem cons_mem (x xs : Sem) (hx : dmP.Mem roseD rRN x) (hxs : dmP.Mem listD rF xs) : dmP.Mem listD rF (consV x xs) := by
  refine mem_intro listD rF ⟨1, by decide⟩ _ ?_
  exact ⟨x, [xs], rfl, hx, xs, [], rfl, hxs, rfl⟩

theorem node_mem (a : Nat) (kids : Sem) (hk : dmP.Mem listD rF kids) : dmP.Mem roseD rRN (nodeV a kids) := by
  refine mem_intro roseD rRN ⟨0, by decide⟩ _ ?_
  exact ⟨_, _, rfl, ⟨a, rfl⟩, kids, [], rfl, hk, rfl⟩

/-- **Built**: the run's constructor values `Node(1, Cons(Node(2, Nil), Nil))` are the tree. -/
theorem build_rose :
    dmP.ctorM roseD psN 0 [.el0 Nat 1,
      dmP.ctorM listD psR 1 [dmP.ctorM roseD psN 0 [.el0 Nat 2, dmP.ctorM listD psR 0 []], dmP.ctorM listD psR 0 []]]
      = nodeV 1 (consV (nodeV 2 nilV) nilV) := rfl

/-- **Every such tree is a member of `Rose(Nat)`'s code, its `kids` of `List(Rose(Nat))`'s.** -/
theorem tree_memTy : nodeV 1 (consV (nodeV 2 nilV) nilV) ∈ₛ[dmP.read] dmP.tyM roseD psN ∧
    consV (nodeV 2 nilV) nilV ∈ₛ[dmP.read] dmP.tyM listD psR :=
  ⟨(DataModel.mem_tyR dmP roseD rRN rfl _).2 (node_mem 1 _ (cons_mem _ _ (node_mem 2 _ nil_mem) nil_mem)),
   (DataModel.mem_tyR dmP listD rF rfl _).2 (cons_mem _ _ (node_mem 2 _ nil_mem) nil_mem)⟩

/-- **Matched**: a rose's constructor and fields, and its `kids` list's, are read off the value. -/
theorem match_rose (a : Nat) (r rs : Sem) :
    (nodeV a (consV r rs)).parts = some (0, [.el0 Nat a, consV r rs]) ∧
      (consV r rs).parts = some (1, [r, rs]) := ⟨rfl, rfl⟩

/-! ## `CountF (f : List(Rose(Nat))) : Nat by f`, recursing through the nested field

`match f { Nil => 0, Cons(t, rest) => match t { Node(a, k) => S(CountF(k)) } }` (`DataModel/Probes.lean`):
the recursive call is at `k`, the head tree's forest, two field steps below `f`. -/

/-- `List(Rose(Nat))`'s code. -/
def cF : Code0 (dmP.car listD rF) := .data listD rF (dmP.car listD rF)

theorem enc_cF (x : dmP.car listD rF) : cF.enc dmP.read x = dmP.meanC x := DataModel.read_car dmP x

/-- `CountF`'s body, as the `.fix` clause runs it: two matches read off the value, the recursive
call through `self` along the code. -/
noncomputable def countBody (self : Res) : List Sem → Option BodyOut
  | [x] => match x.parts with
    | some (0, []) => some ⟨.el0 Nat 0, [], none⟩
    | some (1, [t, _]) => match t.parts with
      | some (0, [_, k]) => match callOf dmP.read self [(k, .plain (TyM.t0 _ cF))] (emptyState 0) with
        | some ((r, _), _) => (Code0.dec dmP.read .nat r).map fun n => ⟨.el0 Nat (n + 1), [], none⟩
        | none => none
      | _ => none
    | _ => none
  | _ => none

/-- What `CountF` computes, on meanings: the depth of the leftmost branch. -/
def countV : Sem → Nat
  | .dat _ _ 1 (.dat _ _ 0 [_, k] :: _) => countV k + 1
  | _ => 0

/-- A stage above a member's height gives its count: the recursive call's forest is two field
steps down, so two stages lower in height, below the stage's bound. -/
theorem stage_count (φ : Future) : ∀ (n : Nat) (v : Sem), dmP.Mem listD rF v → semHeight v < n →
    stage countBody (selfOne dmP.read cF φ rankOf) n [v] = some ⟨.el0 Nat (countV v), [], none⟩
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, v, hv, hn => by
    show countBody (selfOne dmP.read cF φ rankOf n (stage countBody (selfOne dmP.read cF φ rankOf) n)) [v] = _
    rcases list_mem_cases rF v hv with rfl | ⟨x, t, rfl, hx, -⟩
    · rfl
    · have hx' : dmP.Mem roseD rRN x := hx
      obtain ⟨a, k, rfl, -, hk⟩ := rose_mem_cases rRN x hx'
      have hlt : semHeight k < n := by
        have h1 := semHeight_field_lt "Rose" rRN 0 [a, k] k (by simp)
        have h2 := semHeight_field_lt "List" rF 1 [.dat "Rose" rRN 0 [a, k], t] (.dat "Rose" rRN 0 [a, k]) (by simp)
        omega
      obtain ⟨y, hy⟩ := (DataModel.mem_iff_meanC dmP listD rF k).1 hk
      have ih := stage_count φ n k hk hlt
      have hgood : ∀ b : dmP.car listD rF, rankOf [cF.enc dmP.read b] < n →
          ∃ m, stage countBody (selfOne dmP.read cF φ rankOf) n [cF.enc dmP.read b] = some ⟨.el0 Nat m, [], none⟩ := by
        intro b hb
        rw [enc_cF] at hb ⊢
        exact ⟨_, stage_count φ n _ ((DataModel.mem_iff_meanC dmP listD rF _).2 ⟨b, rfl⟩) hb⟩
      obtain ⟨s', hs⟩ := selfOne_call dmP.read cF φ rankOf n _ hgood y (countV k)
        (by rw [enc_cF, hy]; exact hlt) (by rw [enc_cF, hy]; exact ih)
      rw [enc_cF, hy] at hs
      simp only [countBody, Sem.parts, hs, Option.map, dec_nat]
      rfl

/-- `F3`'s forest: `Cons(Node(1, Cons(Node(2, Cons(Node(3, Nil), Nil)), Nil)), Nil)`. -/
def f3 : Sem := consV (nodeV 1 (consV (nodeV 2 (consV (nodeV 3 nilV) nilV)) nilV)) nilV

theorem f3_mem : dmP.Mem listD rF f3 :=
  cons_mem _ _ (node_mem 1 _ (cons_mem _ _ (node_mem 2 _ (cons_mem _ _ (node_mem 3 _ nil_mem) nil_mem)) nil_mem)) nil_mem

/-- **`CountF` is a member of its type's code, and `CountF(F3's forest)` is `3`**, as the checker
computes (`F3` accepted, `F2` rejected). -/
theorem countF_three (φ : Future) :
    (closureL (lvl0 dmP.read) φ (tOne dmP.read cF) (gOf countBody (selfOne dmP.read cF φ rankOf))
        ∈ₛ[dmP.read] piTyL (lvl0 dmP.read) (tOne dmP.read cF)) ∧
      applyFnL (lvl0 dmP.read) (tOne dmP.read cF)
        (closureL (lvl0 dmP.read) φ (tOne dmP.read cF) (gOf countBody (selfOne dmP.read cF φ rankOf)))
        [f3] = some (.data (.el0 Nat 3) TyM.nat []) := by
  have hg : ∀ a : dmP.car listD rF, gOf countBody (selfOne dmP.read cF φ rankOf) [cF.enc dmP.read a]
      = some ⟨.el0 Nat (countV (dmP.meanC a)), [], none⟩ := by
    intro a
    rw [enc_cF]
    exact stage_count φ _ _ ((DataModel.mem_iff_meanC dmP listD rF _).2 ⟨a, rfl⟩) (Nat.lt_succ_self _)
  obtain ⟨F, hF, -⟩ := mk_some dmP.read cF φ _ fun a => ⟨_, hg a⟩
  have hc : closureL (lvl0 dmP.read) φ (tOne dmP.read cF) (gOf countBody (selfOne dmP.read cF φ rankOf))
      = .el0 _ F := by
    unfold closureL; rw [hF]
  refine ⟨by rw [hc]; exact ⟨F, rfl⟩, ?_⟩
  obtain ⟨a, ha⟩ := (DataModel.mem_iff_meanC dmP listD rF _).1 f3_mem
  have := apply_strict dmP.read cF φ _ (fun a => ⟨_, hg a⟩) a _ (hg a)
  rw [enc_cF, ha] at this
  exact this

end Ochr.Meaning.Regress.DataCodes
