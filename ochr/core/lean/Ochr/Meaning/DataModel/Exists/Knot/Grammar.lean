import Ochr.Meaning.DataModel.Exists.Defs
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
There is no condition on a value argument's hint. There was one, (B2) (exists5, weakened by exists7):
the reference ran a parameter's argument at the parameter's type, which for a value argument of a
nested occurrence can vary with the knot's records, and (B2) asked that it not vary or not be read.
Since docs/31 D172 the reference runs every parameter with no hint, as the typed checker does, so a
value argument's run is the same between the knot's comparisons outright and (B2) is gone
(`HintShapes.lean`: `DK` and `DT3`, once outside the grammar, are in it; docs/34 §18.10).

`Spine Γ d c t`: `t` is `Nat`, `Unit`, a parameter, an applied declaration `M(ā)` whose type
arguments are again spines (varying ones only at `M`'s nestable parameters, and at `Type`
parameters when they mention `d`) and whose value arguments are steady, or a steady call or equation.
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

mutual
/-- **The first-order field types of an accepted data-sorted declaration**, under (A) and (B). -/
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
      (ha : Steady d c a)
      (hrest : SpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : SpineArgs Γ d c M j pre (a :: as)
end

/-- **Parameter types are local**: the model's type of `M`'s parameter `j` at the earlier
parameters reads only those its declared type term mentions (what the reference run of the term
reads, by frame locality; the construction's parameter types are that run's). -/
def ParamTyLocal (dm : DataModel) (Γ : List IndDecl) : Prop :=
  ∀ M ∈ Γ, ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j →
    (∀ u ∈ (paramTerm M j).freeVars, u < j → ps[j - 1 - u]? = ps'[j - 1 - u]?) →
      dm.paramTy M j ps = dm.paramTy M j ps'

/-- **The declaration's own parameter types are local in its varying parameters** (exists9; what the
knot reads, `canFrame_eq`): a parameter that does not vary has the same type at two lists of earlier
parameters that agree at every parameter that does not vary. Weaker than `ParamTyLocal` at `d`, which
asks agreement only at the parameters the type term mentions and which faithful parameter types need
not meet: a mentioned parameter's binding type may read an unmentioned one (`(n : Nat) (v : Fin(n))
(h : P(v))`), and the run reads a parameter strictly at its binding type. The run-defined parameter
types meet this one by frame locality: a parameter that does not vary mentions only parameters that do
not vary, whose bindings are then the same. -/
def ParamTyLocalD (dm : DataModel) (d : IndDecl) : Prop :=
  ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j → paramVaries d j = false →
    (∀ u, u < j → paramVaries d u = false → ps[u]? = ps'[u]?) → dm.paramTy d j ps = dm.paramTy d j ps'

/-! ## The grammar as a decidable check (what the checker is to enforce)

`spineB` decides `Spine` from syntax, the declarations `Γ` and the declared parameter type terms
(`spineB_sound`). `GrammarOk Γ d`, the check at every field of every constructor of `d`, is the ONE
fact about the checker that the knot assumes ((A), (B) and the first-order grammar; enforced by the
checker since main's D120/D121, its derivation from the checker's checks is `FromChecker.lean`). -/

/-- `Steady`, decided. -/
def steadyB (d : IndDecl) (c : Nat) (t : Term) : Bool :=
  !t.mentionsType d.name && !t.anyAtom (fun _ => true) && t.freeVars.all fun v => !varVaries d c v

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
    else steadyB d c a) && spineArgsB Γ d c M (j + 1) (pre ++ [a]) as
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
      exact .value M j pre a as (by simpa using hty) (steadyB_sound h1) (spineArgsB_sound h2)
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
varying variable) stands at a nestable parameter of a `Prop`-sorted declaration (rule (A*)(i)). (B)
as for `Spine`. `PGrammarOk` is its decidable check at every field, the grammar fact `truth_exists`
assumes. (exists6 also asked the parameter to be declared `Prop`; `truth_exists` never used it, and
exists8 dropped it, as exists7 dropped the `Type` half of (A) for `Spine`.) -/

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
      (hA : ¬ Steady d c a → M.sort = 0)
      (hrest : PSpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : PSpineArgs Γ d c M j pre (a :: as)
  | value (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = false)
      (ha : Steady d c a)
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
      pspineB Γ d c a && (steadyB d c a || (nestOf M j && M.sort == 0))
    else steadyB d c a) && pspineArgsB Γ d c M (j + 1) (pre ++ [a]) as
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
        rcases hs with hs | ⟨hn', -⟩
        · exact absurd (steadyB_sound hs) hn
        · exact hn'
      · intro hn
        rcases hs with hs | ⟨-, hsort⟩
        · exact absurd (steadyB_sound hs) hn
        · simpa using hsort
    · rw [if_neg hty] at h1
      exact .value M j pre a as (by simpa using hty) (steadyB_sound h1) (pspineArgsB_sound h2)
end


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

instance (Γ : List IndDecl) (d : IndDecl) : Decidable (PGrammarOk Γ d) :=
  decidable_of_iff _ (allFields_iff d (pspineB Γ d))

end Ochr.Meaning.DataModel.Exists.Knot
