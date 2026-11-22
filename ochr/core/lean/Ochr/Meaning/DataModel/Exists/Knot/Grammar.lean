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
* **(A)** `d` does not occur inside an argument at a `Prop` parameter. Stated with what typing
  gives: a varying type argument stands at a `Type` parameter and, when it is an applied
  declaration, that declaration is data-sorted (`SemAgree` compares data codes only).
And one consequence of typing that the syntax must state: **(B2)** a value argument does not stand
at a parameter whose declared type mentions an earlier parameter whose argument varies (its hint,
the parameter's type, would vary).

`Spine Γ d c t`: `t` is `Nat`, `Unit`, a parameter, an applied declaration `M(ā)` whose type
arguments are again spines (varying ones only at `M`'s nestable parameters, and at `Type`
parameters when they mention `d`) and whose value arguments are steady (B2 at each), or a steady
call or equation.
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

/-- (B2) at a value argument: no earlier argument that `M`'s parameter `j`'s type mentions varies. -/
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
      (hA : ¬ Steady d c a → paramTerm M j = .sort 1 ∧
        ∀ n' as' M', a = .tind n' as' → Γ.find? (·.name == n') = some M' → M'.sort ≠ 0)
      (hrest : SpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : SpineArgs Γ d c M j pre (a :: as)
  | value (M : IndDecl) (j : Nat) (pre : List Term) (a : Term) (as : List Term) (hty : M.paramIsType j = false)
      (ha : Steady d c a) (hh : HintSteady d c M j pre)
      (hrest : SpineArgs Γ d c M (j + 1) (pre ++ [a]) as) : SpineArgs Γ d c M j pre (a :: as)
end

/-- **Parameter types are local**: the model's type of `M`'s parameter `j` at the earlier
parameters reads only those its declared type term mentions (what the reference run of the term
reads, by frame locality; the construction's parameter types are that run's). -/
def ParamTyLocal (dm : DataModel) (Γ : List IndDecl) : Prop :=
  ∀ M ∈ Γ, ∀ (j : Nat) (ps ps' : List Sem), ps.length = j → ps'.length = j →
    (∀ u ∈ (paramTerm M j).freeVars, u < j → ps[j - 1 - u]? = ps'[j - 1 - u]?) →
      dm.paramTy M j ps = dm.paramTy M j ps'

end Ochr.Meaning.DataModel.Exists.Knot
