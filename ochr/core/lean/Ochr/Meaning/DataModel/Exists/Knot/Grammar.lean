import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Exists.Knot.HintFree
import Ochr.Check

/-!
# The knot, part 2: what an accepted data-sorted declaration's field types are (exists5)

The restated `knot_exists` (docs/34 §18.6) takes the shape of `d`'s field types as a hypothesis,
in plain predicates on terms. These are the checker's first-order grammar (`Check.firstOrderTerm`,
`d` only at nestable parameters, K4/D107), with two further rules taken from Lean's kernel, for which
a ruling has been requested:
* **(B)** a variable mentions what its declared type mentions. So no equation, call or value
  argument in a field type (a *steady* node) reads a binding that varies between the knot's
  comparisons: a field whose type mentions `d` or a varying variable, a nestable parameter, a
  parameter whose type mentions a varying one (`varVaries`).
* **(A)** `d` does not occur inside an argument at a `Prop` parameter. Stated as what the knot uses:
  a varying type argument that is an applied declaration is data-sorted (`SemAgree` compares data
  codes only). (exists5 also asked the parameter to be declared `Type`; the knot never used it, and
  exists7 dropped it: a varying `Prop` parameter of `d` passed on, `Q(P)`, is compared by equality.)
And one condition on value arguments: **(B2)** a value argument either stands at a parameter whose
declared type mentions no earlier parameter whose argument varies (its hint, the parameter's type, is
then the same between the knot's comparisons), or does not read its hint (`hintFreeB`: its head is not
a constructor with its parameters left to the hint, an embedded value, or `clone`/`peek`/`inplace`;
`HintFree.runT_hintFree`). The second disjunct is exists7's (docs/34 §18.10): it admits `NF(DF, 0, ())`
with `NF (A : Type) (n : Nat) (f : NegF(A, n))`, which the checker and Lean accept. What it still
excludes, a constructor with an unwritten parameter at a hint computed from `d`'s code, is
`HintShapes.lean`'s `DK`.

`Spine Γ d c t`: `t` is `Nat`, `Unit`, a parameter, an applied declaration `M(ā)` whose type
arguments are again spines (varying ones only at `M`'s nestable parameters, and at `Type`
parameters when they mention `d`) and whose value arguments are steady (and (B2) at each), or a
steady call or equation.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning

/-- Parameter `j`'s declared type term (in the scope of the earlier parameters, `var 0` the one
just before). -/
def paramTerm (d : IndDecl) (j : Nat) : Term := ((d.params[j]?).map (·.2)).getD .unit

/-- **Parameter `j` varies** between the knot's comparisons: it is nestable (compared only below a
depth, `ParAgree`), or its declared type mentions an earlier parameter that varies. -/
def paramVaries (d : IndDecl) (j : Nat) : Bool :=
  d.nestable.getD j false ||
    (paramTerm d j).freeVars.any fun u => if _h : u < j then paramVaries d (j - 1 - u) else false
termination_by j
decreasing_by omega

/-- **Field `j` of constructor `c` varies**: its declared type mentions `d`, a varying parameter, or
an earlier field that varies (a reference to a field that is not earlier counts as varying). Variable
`v` of a field type is parameter `np - 1 - v` below `np`, field `np + k - 1 - v` below `np + k`. -/
def fieldVaries (d : IndDecl) (c j : Nat) : Bool :=
  match fieldTerm d c j with
  | none => false
  | some FT => FT.mentionsType d.name || FT.freeVars.any fun v =>
      if v < d.params.length then paramVaries d (d.params.length - 1 - v)
      else if v < d.params.length + DataLib.arity d c then
        (if _h : d.params.length + DataLib.arity d c - 1 - v < j then
          fieldVaries d c (d.params.length + DataLib.arity d c - 1 - v) else true)
      else false
termination_by j
decreasing_by omega

/-- Variable `v` of constructor `c`'s field scope varies. -/
def varVaries (d : IndDecl) (c v : Nat) : Bool :=
  if v < d.params.length then paramVaries d (d.params.length - 1 - v)
  else if v < d.params.length + DataLib.arity d c then fieldVaries d c (d.params.length + DataLib.arity d c - 1 - v)
  else false

/-- A term avoids the declaration named `n`: no `n(…)`, constructor or match names it, and it holds
no embedded value (the model's records for `n` are then never read by its run: `Congr.runT_congrR`).

The second clause first read "no embedded value names `n`" (an atom `n(…)` or a constructor value of
`n`). That was not enough: an embedded sealed program or closure `.val (.sealed (.tind n []))` names `n`
only in its term, which `Term.anyAtom` does not look at, and its meaning runs `n(…)` under the model
(`Congr.avoidsOld_gap`). The checker's declared field types hold no embedded value at all (they are
resolved surface syntax), so the clause is now that, decidable and as strong as needed. -/
def Avoids (n : String) (t : Term) : Prop :=
  t.mentionsType n = false ∧ t.anyAtom (fun _ => true) = false

/-- **A steady term** (B): it avoids `d` and reads no varying variable. -/
def Steady (d : IndDecl) (c : Nat) (t : Term) : Prop :=
  Avoids d.name t ∧ ∀ v ∈ t.freeVars, varVaries d c v = false

/-- Whether `M`'s parameter `j` is nestable (as stored; `d`'s own read from `d`, which its name finds). -/
def nestOf (M : IndDecl) (j : Nat) : Bool := M.nestable.getD j false

/-- (B2)'s first disjunct at a value argument: no earlier argument that `M`'s parameter `j`'s type
mentions varies. -/
def HintSteady (d : IndDecl) (c : Nat) (M : IndDecl) (j : Nat) (pre : List Term) : Prop :=
  ∀ u ∈ (paramTerm M j).freeVars, u < j → ∀ a, pre[j - 1 - u]? = some a → Steady d c a

mutual
/-- **The first-order field types of an accepted data-sorted declaration**, under (A), (B), (B2). -/
inductive Spine (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Prop
  | nat : Spine Γ d c .nat
  | unit : Spine Γ d c .unit
  | param (v : Nat) (hv : v < d.params.length) : Spine Γ d c (.place (.var v))
  | tind (n : String) (as : List Term) (M : IndDecl) (hM : Γ.find? (·.name == n) = some M)
      (hargs : SpineArgs Γ d c M 0 [] as) : Spine Γ d c (.tind n as)
  | call (f : String) (as : List Term) (hd : Bool) (h : Steady d c (.call (.const f) as hd)) :
      Spine Γ d c (.call (.const f) as hd)
  | eq (A a b : Term) (h : Steady d c (.eq A a b)) : Spine Γ d c (.eq A a b)

/-- The arguments of `M(…)` from parameter `j`, after the arguments `pre`. -/
inductive SpineArgs (Γ : List IndDecl) (d : IndDecl) (c : Nat) : IndDecl → Nat → List Term → List Term → Prop
  | nil (M : IndDecl) (j : Nat) (pre : List Term) : SpineArgs Γ d c M j pre []
  | type (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = true)
      (ha : Spine Γ d c a) (hn : ¬ Steady d c a → nestOf M j = true)
      (hA : ¬ Steady d c a → ∀ n' as' M', a = .tind n' as' → Γ.find? (·.name == n') = some M' → M'.sort ≠ 0)
      (hrest : SpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : SpineArgs Γ d c M j pre (a :: as)
  | value (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = false)
      (ha : Steady d c a) (hh : HintSteady d c M j pre ∨ hintFreeB Γ a = true)
      (hrest : SpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : SpineArgs Γ d c M j pre (a :: as)
end

/-- **Parameter types are local**: the model's type of `M`'s parameter `j` at the earlier
parameters reads only those its declared type term mentions (what the reference run of the term
reads, by frame locality; the construction's parameter types are that run's). -/
def ParamTyLocal (dm : DataModel) (Γ : List IndDecl) : Prop :=
  ∀ M ∈ Γ, ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j →
    (∀ u ∈ (paramTerm M j).freeVars, u < j → ps[j - 1 - u]? = ps'[j - 1 - u]?) →
      dm.paramTy M j ps = dm.paramTy M j ps'

/-! ## The grammar as a decidable check (what the checker is to enforce)

`spineB` decides `Spine` from syntax, the declarations `Γ` and the declared parameter type terms
(`spineB_sound`). `GrammarOk Γ d`, the check at every field of every constructor of `d`, is the ONE
fact about the checker that the knot assumes ((A), (B), (B2) and the first-order grammar), until the
checker enforces it (docs/34 §18.6). -/

/-- `Steady`, decided. -/
def steadyB (d : IndDecl) (c : Nat) (t : Term) : Bool :=
  !t.mentionsType d.name && !t.anyAtom (fun _ => true) && t.freeVars.all fun v => !varVaries d c v

/-- `HintSteady`, decided. -/
def hintSteadyB (d : IndDecl) (c : Nat) (M : IndDecl) (j : Nat) (pre : List Term) : Bool :=
  (paramTerm M j).freeVars.all fun u => if u < j then (match pre[j - 1 - u]? with
    | some a => steadyB d c a
    | none => true) else true

/-- An applied declaration found in `Γ` is not `Prop`-sorted (anything else passes). -/
def notPropDecl (Γ : List IndDecl) : Term → Bool
  | .tind n _ => match Γ.find? (·.name == n) with
    | some M => M.sort != 0
    | none => true
  | _ => true

mutual
/-- `Spine`, decided. -/
def spineB (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Bool
  | .nat => true
  | .unit => true
  | .place (.var v) => decide (v < d.params.length)
  | .tind n as => match Γ.find? (·.name == n) with
    | some M => spineArgsB Γ d c M 0 [] as
    | none => false
  | .call (.const f) as hd => steadyB d c (.call (.const f) as hd)
  | .eq A a b => steadyB d c (.eq A a b)
  | _ => false
termination_by structural t => t

/-- `SpineArgs`, decided. -/
def spineArgsB (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) : Nat → List Term → List Term → Bool
  | _, _, [] => true
  | j, pre, a :: as =>
    (if M.paramIsType j then
      spineB Γ d c a && (steadyB d c a || (nestOf M j && notPropDecl Γ a))
    else steadyB d c a && (hintSteadyB d c M j pre || hintFreeB Γ a)) && spineArgsB Γ d c M (j + 1) (pre ++ [a]) as
termination_by structural _ _ as => as
end

/-- **The checker fact the knot assumes**: every field type of every constructor of `d` passes the
grammar check (decidable: finitely many fields, each a `Bool`). -/
def GrammarOk (Γ : List IndDecl) (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → spineB Γ d c FT = true

instance (Γ : List IndDecl) (d : IndDecl) : Decidable (GrammarOk Γ d) :=
  decidable_of_iff (d.ctors.zipIdx.all fun (cs, c) => cs.2.all fun (_, FT) => spineB Γ d c FT) (by
    unfold GrammarOk fieldTerm
    constructor
    · intro h c i FT hFT
      cases hc : d.ctors[c]? with
      | none => simp [hc] at hFT
      | some cs =>
        simp only [hc, Option.bind_some, Option.map_eq_some_iff] at hFT
        obtain ⟨⟨nm, FT'⟩, h1, rfl⟩ := hFT
        simp only [List.all_eq_true] at h
        have hcs : (cs, c) ∈ d.ctors.zipIdx := by
          rw [List.mem_iff_getElem?]; exact ⟨c, by simp [List.getElem?_zipIdx, hc]⟩
        exact h _ hcs _ (List.mem_of_getElem? h1)
    · intro h
      simp only [List.all_eq_true]
      rintro ⟨cs, c⟩ hm ⟨nm, FT⟩ hf
      have hc : d.ctors[c]? = some cs := by
        rw [List.mem_iff_getElem?] at hm
        obtain ⟨k, hk⟩ := hm
        rw [List.getElem?_zipIdx] at hk
        cases hk' : d.ctors[k]? with
        | none => simp [hk'] at hk
        | some x =>
          simp only [hk', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk; simpa using hk'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
      exact h c i FT (by simp [hc, hi]))

theorem steadyB_sound {d : IndDecl} {c : Nat} {t : Term} (h : steadyB d c t = true) : Steady d c t := by
  simp only [steadyB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  exact ⟨⟨h.1.1, h.1.2⟩, fun v hv => by simpa using h.2 v hv⟩

theorem hintSteadyB_sound {d : IndDecl} {c : Nat} {M : IndDecl} {j : Nat} {pre : List Term}
    (h : hintSteadyB d c M j pre = true) : HintSteady d c M j pre := by
  intro u hu hlt a ha
  simp only [hintSteadyB, List.all_eq_true] at h
  have := h u hu
  rw [if_pos hlt, ha] at this
  exact steadyB_sound this

mutual
/-- **The check decides the grammar** (soundness, the direction the knot uses). -/
theorem spineB_sound {Γ : List IndDecl} {d : IndDecl} {c : Nat} : ∀ {t : Term}, spineB Γ d c t = true → Spine Γ d c t
  | .nat, _ => .nat
  | .unit, _ => .unit
  | .place p, h => by
    cases p with
    | var v => exact .param v (by simpa [spineB] using h)
    | _ => simp [spineB] at h
  | .tind n as, h => by
    simp only [spineB] at h
    split at h
    · rename_i M hM; exact .tind n as M hM (spineArgsB_sound h)
    · cases h
  | .call f as hd, h => by
    cases f with
    | const g => exact .call g as hd (steadyB_sound (by simpa [spineB] using h))
    | _ => simp [spineB] at h
  | .eq A a b, h => .eq A a b (steadyB_sound (by simpa [spineB] using h))
  | .borrow _, h | .assign _ _, h | .letIn _ _ _, h | .seq _ _, h | .matchNat _ _ _, h | .const _, h
  | .val _, h | .sort _, h | .pi _ _ _, h | .fix _ _ _ _ _ _, h | .zero, h | .succ _, h | .tt, h
  | .cong _ _, h | .ref _, h | .id _ _ _, h | .ascribe _ _, h | .prim _ _, h | .ctor _ _ _ _ _, h
  | .matchInd _ _ _, h => by simp [spineB] at h

theorem spineArgsB_sound {Γ : List IndDecl} {d : IndDecl} {c : Nat} {M : IndDecl} :
    ∀ {j : Nat} {pre as : List Term}, spineArgsB Γ d c M j pre as = true → SpineArgs Γ d c M j pre as
  | j, pre, [], _ => .nil M j pre
  | j, pre, a :: as, h => by
    simp only [spineArgsB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hty : M.paramIsType j = true
    · rw [if_pos hty] at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      obtain ⟨ha, hs⟩ := h1
      refine .type M j pre a as hty (spineB_sound ha) ?_ ?_ (spineArgsB_sound h2)
      · intro hn
        rcases hs with hs | ⟨hn', -⟩
        · exact absurd (steadyB_sound hs) hn
        · exact hn'
      · intro hn
        rcases hs with hs | ⟨-, hnp⟩
        · exact absurd (steadyB_sound hs) hn
        · rintro n' as' M' rfl hM'
          simp [notPropDecl, hM'] at hnp
          exact hnp
    · rw [if_neg hty] at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      exact .value M j pre a as (by simpa using hty) (steadyB_sound h1.1) (h1.2.imp hintSteadyB_sound id)
        (spineArgsB_sound h2)
end

/-! ## Rule (A*), Lean's: a nested occurrence passes only through declarations of its own sort

ADOPTED by the lead (2026-11-22), subject to measurement, with (A) and (B). Two parts, each a `Bool`
on syntax, the declarations and their stored nestable sets; the checker enforces both at every
declaration `d` (with `Γ` the declarations up to and including `d`): `AStarOk Γ d`.
* (i) `occSortB`: every applied declaration in a field type of `d` one of whose arguments mentions `d`
  has `d`'s sort (for a data-sorted `d` this is part of what `Spine`'s (A) asks of the argument).
* (ii) `NestSortB`: each parameter `d` stores as nestable is passed, in every field type of `d`, only to
  declarations of `d`'s sort (D107's nestable computation, with that condition added).
The knot (`knot_exists`) does not need (A*): its records keep a declaration of the other sort as a
sub-record, and stay parametric (`CrossSortCE.hpar_E`). The truth-first construction of `Prop`-sorted
declarations needs it: with it, every shape a nestable `Prop` parameter reaches is a proposition leaf
(`mono_prop`'s hypothesis). -/

/-- The sort of the declaration named `n` in `Γ`. -/
def sortIn (Γ : List IndDecl) (n : String) : Option Nat := (Γ.find? (·.name == n)).map (·.sort)

mutual
/-- (A*)(i) in `t`: an applied declaration one of whose arguments mentions `d` has `d`'s sort. -/
def occSortB (Γ : List IndDecl) (d : IndDecl) : Term → Bool
  | .tind n as => (!(Term.mentionsTypeList d.name as) || sortIn Γ n == some d.sort) && occSortListB Γ d as
  | _ => true
termination_by structural t => t

def occSortListB (Γ : List IndDecl) (d : IndDecl) : List Term → Bool
  | [] => true
  | a :: as => occSortB Γ d a && occSortListB Γ d as
termination_by structural as => as
end

mutual
/-- (A*)(ii) in `t`, at variable `v`: an applied declaration one of whose arguments mentions `v` has
sort `s`. -/
def passSortB (Γ : List IndDecl) (s v : Nat) : Term → Bool
  | .tind n as => (!(as.any fun a => a.freeVars.contains v) || sortIn Γ n == some s) && passSortListB Γ s v as
  | _ => true
termination_by structural t => t

def passSortListB (Γ : List IndDecl) (s v : Nat) : List Term → Bool
  | [] => true
  | a :: as => passSortB Γ s v a && passSortListB Γ s v as
termination_by structural as => as
end

/-- (A*)(ii) at `M`: each stored nestable parameter (variable `np - 1 - j` in a field type) is passed
only to declarations of `M`'s sort. -/
def NestSortB (Γ : List IndDecl) (M : IndDecl) : Bool :=
  (List.range M.params.length).all fun j => !(M.nestable.getD j false) ||
    M.ctors.all fun cs => cs.2.all fun f => passSortB Γ M.sort (M.params.length - 1 - j) f.2

/-- **Rule (A*) at a declaration** (`Γ`: the declarations up to and including `d`). -/
def AStarOk (Γ : List IndDecl) (d : IndDecl) : Bool :=
  (d.ctors.all fun cs => cs.2.all fun f => occSortB Γ d f.2) && NestSortB Γ d

/-- Rule (A*) at `Prop`-sorted declarations only: the lead's fallback variant (rule (A) for data-sorted
declarations, the same-sort rule for `Prop`-sorted ones). It is all the truth-first construction
assumes (`General.truth_exists`'s `hstar`); the uniform rule (`AStarOk` everywhere) implies it. The knot
(`knot_exists`) assumes neither. -/
def AStarPropOk (Γ : List IndDecl) (d : IndDecl) : Bool := d.sort != 0 || AStarOk Γ d

/-! ## The grammar for a `Prop`-sorted declaration (truth first)

`PSpine` is `Spine` with (A) read for `Prop`: a varying type argument (one that mentions `d` or a
varying variable) stands at a `Prop` parameter of a `Prop`-sorted declaration (rule (A*)(i) and the
universe: a proposition is no `Type` argument). (B) and (B2) as for `Spine`. `PGrammarOk` is its
decidable check at every field, the grammar fact `General.truth_exists` is to assume. -/

/-- A parameter type term that is `Prop` (`.sort 0`). -/
def isType0 : Term → Bool
  | .sort 0 => true
  | _ => false

mutual
/-- The first-order field types of an accepted `Prop`-sorted declaration. -/
inductive PSpine (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Prop
  | nat : PSpine Γ d c .nat
  | unit : PSpine Γ d c .unit
  | param (v : Nat) (hv : v < d.params.length) : PSpine Γ d c (.place (.var v))
  | tind (n : String) (as : List Term) (M : IndDecl) (hM : Γ.find? (·.name == n) = some M)
      (hargs : PSpineArgs Γ d c M 0 [] as) : PSpine Γ d c (.tind n as)
  | call (f : String) (as : List Term) (hd : Bool) (h : Steady d c (.call (.const f) as hd)) :
      PSpine Γ d c (.call (.const f) as hd)
  | eq (A a b : Term) (h : Steady d c (.eq A a b)) : PSpine Γ d c (.eq A a b)

inductive PSpineArgs (Γ : List IndDecl) (d : IndDecl) (c : Nat) : IndDecl → Nat → List Term → List Term → Prop
  | nil (M : IndDecl) (j : Nat) (pre : List Term) : PSpineArgs Γ d c M j pre []
  | type (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = true)
      (ha : PSpine Γ d c a) (hn : ¬ Steady d c a → nestOf M j = true)
      (hA : ¬ Steady d c a → paramTerm M j = .sort 0 ∧ M.sort = 0)
      (hrest : PSpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : PSpineArgs Γ d c M j pre (a :: as)
  | value (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = false)
      (ha : Steady d c a) (hh : HintSteady d c M j pre ∨ hintFreeB Γ a = true)
      (hrest : PSpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : PSpineArgs Γ d c M j pre (a :: as)
end

mutual
/-- `PSpine`, decided. -/
def pspineB (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Bool
  | .nat => true
  | .unit => true
  | .place (.var v) => decide (v < d.params.length)
  | .tind n as => match Γ.find? (·.name == n) with
    | some M => pspineArgsB Γ d c M 0 [] as
    | none => false
  | .call (.const f) as hd => steadyB d c (.call (.const f) as hd)
  | .eq A a b => steadyB d c (.eq A a b)
  | _ => false
termination_by structural t => t

/-- `PSpineArgs`, decided. -/
def pspineArgsB (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) : Nat → List Term → List Term → Bool
  | _, _, [] => true
  | j, pre, a :: as =>
    (if M.paramIsType j then
      pspineB Γ d c a && (steadyB d c a || (nestOf M j && isType0 (paramTerm M j) && M.sort == 0))
    else steadyB d c a && (hintSteadyB d c M j pre || hintFreeB Γ a)) && pspineArgsB Γ d c M (j + 1) (pre ++ [a]) as
termination_by structural _ _ as => as
end

/-- **The grammar fact for a `Prop`-sorted declaration**: every field type passes `pspineB`. -/
def PGrammarOk (Γ : List IndDecl) (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → pspineB Γ d c FT = true

mutual
theorem pspineB_sound {Γ : List IndDecl} {d : IndDecl} {c : Nat} : ∀ {t : Term}, pspineB Γ d c t = true → PSpine Γ d c t
  | .nat, _ => .nat
  | .unit, _ => .unit
  | .place p, h => by
    cases p with
    | var v => exact .param v (by simpa [pspineB] using h)
    | _ => simp [pspineB] at h
  | .tind n as, h => by
    simp only [pspineB] at h
    split at h
    · rename_i M hM; exact .tind n as M hM (pspineArgsB_sound h)
    · cases h
  | .call f as hd, h => by
    cases f with
    | const g => exact .call g as hd (steadyB_sound (by simpa [pspineB] using h))
    | _ => simp [pspineB] at h
  | .eq A a b, h => .eq A a b (steadyB_sound (by simpa [pspineB] using h))
  | .borrow _, h | .assign _ _, h | .letIn _ _ _, h | .seq _ _, h | .matchNat _ _ _, h | .const _, h
  | .val _, h | .sort _, h | .pi _ _ _, h | .fix _ _ _ _ _ _, h | .zero, h | .succ _, h | .tt, h
  | .cong _ _, h | .ref _, h | .id _ _ _, h | .ascribe _ _, h | .prim _ _, h | .ctor _ _ _ _ _, h
  | .matchInd _ _ _, h => by simp [pspineB] at h

theorem pspineArgsB_sound {Γ : List IndDecl} {d : IndDecl} {c : Nat} {M : IndDecl} :
    ∀ {j : Nat} {pre as : List Term}, pspineArgsB Γ d c M j pre as = true → PSpineArgs Γ d c M j pre as
  | j, pre, [], _ => .nil M j pre
  | j, pre, a :: as, h => by
    simp only [pspineArgsB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hty : M.paramIsType j = true
    · rw [if_pos hty] at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      obtain ⟨ha, hs⟩ := h1
      refine .type M j pre a as hty (pspineB_sound ha) ?_ ?_ (pspineArgsB_sound h2)
      · intro hn
        rcases hs with hs | ⟨⟨hn', -⟩, -⟩
        · exact absurd (steadyB_sound hs) hn
        · exact hn'
      · intro hn
        rcases hs with hs | ⟨⟨-, h0⟩, hsort⟩
        · exact absurd (steadyB_sound hs) hn
        · refine ⟨?_, by simpa using hsort⟩
          unfold isType0 at h0; split at h0 <;> simp_all
    · rw [if_neg hty] at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h1
      exact .value M j pre a as (by simpa using hty) (steadyB_sound h1.1) (h1.2.imp hintSteadyB_sound id)
        (pspineArgsB_sound h2)
end


/-! ## The grammar in two parts: enforced by the checker today, enforced after main's D123

The lead's ruling (2026-11-22) on (B2): the checker is to store, in a declaration's field and parameter
types, the parameters it solves for a constructor (main's D123, as Lean's elaborator writes every
implicit argument). Until then (B2) is false at an accepted declaration (`HintShapes.DK`). So the grammar
is two named facts: `GrammarCoreOk` (everything but (B2): the first-order grammar, (A), (B); to be
derived from the checker's checks, step 2) and `GrammarHintOk` ((B2) at every value argument along the
spine: ENFORCED AFTER MAIN'S D123). Their conjunction is `GrammarOk` (`grammarOk_of_parts`), and likewise
for `Prop`-sorted declarations (`PGrammarCoreOk`, the same `GrammarHintOk`). -/

/-- The decided check at every field of every constructor, as a `Prop`. -/
theorem allFields_iff (d : IndDecl) (P : Nat → Term → Bool) :
    (d.ctors.zipIdx.all fun (cs, c) => cs.2.all fun (_, FT) => P c FT) = true ↔
      ∀ c i FT, fieldTerm d c i = some FT → P c FT = true := by
  unfold fieldTerm
  constructor
  · intro h c i FT hFT
    cases hc : d.ctors[c]? with
    | none => simp [hc] at hFT
    | some cs =>
      simp only [hc, Option.bind_some, Option.map_eq_some_iff] at hFT
      obtain ⟨⟨nm, FT'⟩, h1, rfl⟩ := hFT
      simp only [List.all_eq_true] at h
      have hcs : (cs, c) ∈ d.ctors.zipIdx := by
        rw [List.mem_iff_getElem?]; exact ⟨c, by simp [List.getElem?_zipIdx, hc]⟩
      exact h _ hcs _ (List.mem_of_getElem? h1)
  · intro h
    simp only [List.all_eq_true]
    rintro ⟨cs, c⟩ hm ⟨nm, FT⟩ hf
    have hc : d.ctors[c]? = some cs := by
      rw [List.mem_iff_getElem?] at hm
      obtain ⟨k, hk⟩ := hm
      rw [List.getElem?_zipIdx] at hk
      cases hk' : d.ctors[k]? with
      | none => simp [hk'] at hk
      | some x =>
        simp only [hk', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk; simpa using hk'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
    exact h c i FT (by simp [hc, hi])

mutual
/-- **(B2) along a field type's spine**: at each value argument of an applied declaration (inside the
field type and, recursively, inside its arguments at type parameters), the hint is steady or the
argument does not read it (`hintFreeB`). -/
def valHintB (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Bool
  | .tind n as => match Γ.find? (·.name == n) with
    | some M => valHintArgsB Γ d c M 0 [] as
    | none => true
  | _ => true
termination_by structural t => t

def valHintArgsB (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) : Nat → List Term → List Term → Bool
  | _, _, [] => true
  | j, pre, a :: as =>
    (if M.paramIsType j then valHintB Γ d c a else (hintSteadyB d c M j pre || hintFreeB Γ a)) &&
      valHintArgsB Γ d c M (j + 1) (pre ++ [a]) as
termination_by structural _ _ as => as
end

/-- **(B2) at every field: a fact about the checker ENFORCED AFTER MAIN'S D123** (false today at
`HintShapes.DK`). -/
def GrammarHintOk (Γ : List IndDecl) (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → valHintB Γ d c FT = true

instance (Γ : List IndDecl) (d : IndDecl) : Decidable (GrammarHintOk Γ d) :=
  decidable_of_iff _ (allFields_iff d (valHintB Γ d))

mutual
/-- `spineB` without (B2): the part of the grammar the checker enforces today. -/
def spineCoreB (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Bool
  | .nat => true
  | .unit => true
  | .place (.var v) => decide (v < d.params.length)
  | .tind n as => match Γ.find? (·.name == n) with
    | some M => spineCoreArgsB Γ d c M 0 [] as
    | none => false
  | .call (.const f) as hd => steadyB d c (.call (.const f) as hd)
  | .eq A a b => steadyB d c (.eq A a b)
  | _ => false
termination_by structural t => t

def spineCoreArgsB (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) : Nat → List Term → List Term → Bool
  | _, _, [] => true
  | j, pre, a :: as =>
    (if M.paramIsType j then
      spineCoreB Γ d c a && (steadyB d c a || (nestOf M j && notPropDecl Γ a))
    else steadyB d c a) && spineCoreArgsB Γ d c M (j + 1) (pre ++ [a]) as
termination_by structural _ _ as => as
end

mutual
theorem spineB_of_parts {Γ : List IndDecl} {d : IndDecl} {c : Nat} :
    ∀ {t : Term}, spineCoreB Γ d c t = true → valHintB Γ d c t = true → spineB Γ d c t = true
  | .nat, _, _ => by simp [spineB]
  | .unit, _, _ => by simp [spineB]
  | .place p, h1, _ => by cases p <;> simp_all [spineCoreB, spineB]
  | .call f as hd, h1, _ => by cases f <;> simp_all [spineCoreB, spineB]
  | .eq A a b, h1, _ => by simp_all [spineCoreB, spineB]
  | .tind n as, h1, h2 => by
    simp only [spineCoreB] at h1
    simp only [valHintB] at h2
    simp only [spineB]
    split at h1
    · rename_i M hM
      rw [hM] at h2
      exact spineArgsB_of_parts h1 h2
    · cases h1
  | .borrow _, h1, _ | .assign _ _, h1, _ | .letIn _ _ _, h1, _ | .seq _ _, h1, _ | .matchNat _ _ _, h1, _ | .const _, h1, _
  | .val _, h1, _ | .sort _, h1, _ | .pi _ _ _, h1, _ | .fix _ _ _ _ _ _, h1, _ | .zero, h1, _ | .succ _, h1, _ | .tt, h1, _
  | .cong _ _, h1, _ | .ref _, h1, _ | .id _ _ _, h1, _ | .ascribe _ _, h1, _ | .prim _ _, h1, _ | .ctor _ _ _ _ _, h1, _
  | .matchInd _ _ _, h1, _ => by simp [spineCoreB] at h1

theorem spineArgsB_of_parts {Γ : List IndDecl} {d : IndDecl} {c : Nat} {M : IndDecl} :
    ∀ {j : Nat} {pre as : List Term}, spineCoreArgsB Γ d c M j pre as = true → valHintArgsB Γ d c M j pre as = true →
      spineArgsB Γ d c M j pre as = true
  | _, _, [], _, _ => by simp [spineArgsB]
  | j, pre, a :: as, h1, h2 => by
    simp only [spineCoreArgsB, valHintArgsB, spineArgsB, Bool.and_eq_true] at h1 h2 ⊢
    refine ⟨?_, spineArgsB_of_parts h1.2 h2.2⟩
    by_cases hty : M.paramIsType j = true
    · simp only [hty, if_true, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨spineB_of_parts h1.1.1 h2.1, h1.1.2⟩
    · simp only [hty, Bool.false_eq_true, if_false, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1.1, h2.1⟩
end

/-- **The rest of the grammar at every field (data-sorted): a fact about the checker, to be derived
from its checks today** (step 2). -/
def GrammarCoreOk (Γ : List IndDecl) (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → spineCoreB Γ d c FT = true

instance (Γ : List IndDecl) (d : IndDecl) : Decidable (GrammarCoreOk Γ d) :=
  decidable_of_iff _ (allFields_iff d (spineCoreB Γ d))

theorem grammarOk_of_parts {Γ : List IndDecl} {d : IndDecl} (h1 : GrammarCoreOk Γ d) (h2 : GrammarHintOk Γ d) :
    GrammarOk Γ d :=
  fun c i FT hFT => spineB_of_parts (h1 c i FT hFT) (h2 c i FT hFT)

mutual
/-- `pspineB` without (B2): the part of the grammar the checker enforces today. -/
def pspineCoreB (Γ : List IndDecl) (d : IndDecl) (c : Nat) : Term → Bool
  | .nat => true
  | .unit => true
  | .place (.var v) => decide (v < d.params.length)
  | .tind n as => match Γ.find? (·.name == n) with
    | some M => pspineCoreArgsB Γ d c M 0 [] as
    | none => false
  | .call (.const f) as hd => steadyB d c (.call (.const f) as hd)
  | .eq A a b => steadyB d c (.eq A a b)
  | _ => false
termination_by structural t => t

def pspineCoreArgsB (Γ : List IndDecl) (d : IndDecl) (c : Nat) (M : IndDecl) : Nat → List Term → List Term → Bool
  | _, _, [] => true
  | j, pre, a :: as =>
    (if M.paramIsType j then
      pspineCoreB Γ d c a && (steadyB d c a || (nestOf M j && isType0 (paramTerm M j) && M.sort == 0))
    else steadyB d c a) && pspineCoreArgsB Γ d c M (j + 1) (pre ++ [a]) as
termination_by structural _ _ as => as
end

mutual
theorem pspineB_of_parts {Γ : List IndDecl} {d : IndDecl} {c : Nat} :
    ∀ {t : Term}, pspineCoreB Γ d c t = true → valHintB Γ d c t = true → pspineB Γ d c t = true
  | .nat, _, _ => by simp [pspineB]
  | .unit, _, _ => by simp [pspineB]
  | .place p, h1, _ => by cases p <;> simp_all [pspineCoreB, pspineB]
  | .call f as hd, h1, _ => by cases f <;> simp_all [pspineCoreB, pspineB]
  | .eq A a b, h1, _ => by simp_all [pspineCoreB, pspineB]
  | .tind n as, h1, h2 => by
    simp only [pspineCoreB] at h1
    simp only [valHintB] at h2
    simp only [pspineB]
    split at h1
    · rename_i M hM
      rw [hM] at h2
      exact pspineArgsB_of_parts h1 h2
    · cases h1
  | .borrow _, h1, _ | .assign _ _, h1, _ | .letIn _ _ _, h1, _ | .seq _ _, h1, _ | .matchNat _ _ _, h1, _ | .const _, h1, _
  | .val _, h1, _ | .sort _, h1, _ | .pi _ _ _, h1, _ | .fix _ _ _ _ _ _, h1, _ | .zero, h1, _ | .succ _, h1, _ | .tt, h1, _
  | .cong _ _, h1, _ | .ref _, h1, _ | .id _ _ _, h1, _ | .ascribe _ _, h1, _ | .prim _ _, h1, _ | .ctor _ _ _ _ _, h1, _
  | .matchInd _ _ _, h1, _ => by simp [pspineCoreB] at h1

theorem pspineArgsB_of_parts {Γ : List IndDecl} {d : IndDecl} {c : Nat} {M : IndDecl} :
    ∀ {j : Nat} {pre as : List Term}, pspineCoreArgsB Γ d c M j pre as = true → valHintArgsB Γ d c M j pre as = true →
      pspineArgsB Γ d c M j pre as = true
  | _, _, [], _, _ => by simp [pspineArgsB]
  | j, pre, a :: as, h1, h2 => by
    simp only [pspineCoreArgsB, valHintArgsB, pspineArgsB, Bool.and_eq_true] at h1 h2 ⊢
    refine ⟨?_, pspineArgsB_of_parts h1.2 h2.2⟩
    by_cases hty : M.paramIsType j = true
    · simp only [hty, if_true, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨pspineB_of_parts h1.1.1 h2.1, h1.1.2⟩
    · simp only [hty, Bool.false_eq_true, if_false, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨h1.1, h2.1⟩
end

/-- **The rest of the grammar at every field (`Prop`-sorted): a fact about the checker, to be derived
from its checks today** (step 2). -/
def PGrammarCoreOk (Γ : List IndDecl) (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → pspineCoreB Γ d c FT = true

instance (Γ : List IndDecl) (d : IndDecl) : Decidable (PGrammarCoreOk Γ d) :=
  decidable_of_iff _ (allFields_iff d (pspineCoreB Γ d))

theorem pgrammarOk_of_parts {Γ : List IndDecl} {d : IndDecl} (h1 : PGrammarCoreOk Γ d) (h2 : GrammarHintOk Γ d) :
    PGrammarOk Γ d :=
  fun c i FT hFT => pspineB_of_parts (h1 c i FT hFT) (h2 c i FT hFT)

end Ochr.Meaning.DataModel.Exists.Knot
