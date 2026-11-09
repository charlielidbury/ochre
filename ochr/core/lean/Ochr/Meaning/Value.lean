import Ochr.Meaning.Data
import Ochr.Meaning.Future
import Ochr.Meaning.Pi

/-!
# The meaning of a value, `⟦v⟧_{ρ,φ}` (docs/18 Def. "meaning of a state", docs/27 Def. 2)

Under an assignment `ρ` of the abstract values and a future `φ` of the live borrows:
* `σ` means `ρ σ`; `⋆` means `•`; `⊥` means `moved`; `Z`, `S v`, `()` mean the numbers and the
  unit as elements of `Nat` and `Unit`;
* a constructor value means `el0` of its data carrier at its parameters, or an untyped tuple
  when a field holds `moved` (`DataModel.ctorM`);
* a type value means `ty T`: `Nat`, `Unit`, `sort l`, `D(ā)` by the data model, `Eq(A, a, b)` the
  proposition `⟦a⟧ = ⟦b⟧` (so `Eq` reads no type: docs/24 C10), `&A` the content type `⟦A⟧`
  (a borrow is read as what it holds, so a borrow-typed place means its content);
* `borrow_ℓ w` means `⟦w⟧`, its *current* content; `loan_ℓ` means `φ ℓ`, the *final* content
  of the borrow that took it (docs/27 §3);
* a global, a closure, a Π-closure and a sealed program mean what running code means, through
  `CodeMeaning`, which the reference run supplies (milestone 2).

## The type hint (docs/31 D8, revised)

A constructor value of a parameterised type may record no parameters (`ps = []`): an untyped
run (a sealed program's re-normalisation, a callee's body) records only the parameters written
in the source, and the checker reads such a value's type from its position (D49 (4),
`Machine.indValType?`). The typed model needs the parameters' meanings, so the meaning of a
value is read *at a type*, the `hint : TyS`, whose `data` component names the declaration and
the parameters' meanings: the position's stored type, a field's type at the earlier fields
(`DataModel.fieldTy`), a parameter's type, an equation's type. Only a constructor value with
`ps = []` reads the hint, taking the parameters straight off `hint.data` (no choice: a carrier
does not determine them, data-generic's counterexample); everything else ignores it. So
docs/18's V2 holds in this sense: what a constructor value means is determined by its type,
whether or not it records its parameters. `TyS.plain .err` is "no hint".

The definition is total; an ill-formed value means `err`.
-/

namespace Ochr.Meaning

/-- What the meaning of a value needs from the meaning of code. The reference run (`Run.lean`)
defines these together with `Value.mean` in one recursion; here they are a parameter, so that
the first-order meaning is fixed and checkable on its own. -/
structure CodeMeaning where
  /-- The meaning of the global `gfn n` (a function) or of a constant, from the program so far,
  with its type as the run knows it (a function's Π-shape). -/
  global : String → Sem × TyS
  /-- The meaning of the sealed program `⌈t⌉` read at the type `hint`: `t` run from the empty
  state, its abstract values read from `ρ` and its loans (holes, inert loans) from `φ`. -/
  sealed : Assignment → Future → TyS → Term → Sem
  /-- The meaning of the closure `clo caps t rd`: a function on its annotated domain, read off the
  reference run of its body with the captures bound at their recorded types; a recursive closure
  by guarded recursion on the rank of its decreasing argument (docs/24 §4). -/
  clo : Assignment → Future → List Value → Term → List (DeclInfo × Value) → Sem
  /-- The meaning of the Π-closure `tPi caps t rd`: the dependent product of its parameter types
  and codomain, evaluated at every argument (`Pi.lean`). -/
  pi : Assignment → Future → List Value → Term → List (DeclInfo × Value) → TyM
  /-- The meaning of a deferred type (D82 `Binding.lazyTy`): parameter `i` of the Π-type `P` at
  the arguments `ws` as passed, or `P`'s codomain there for `i` the number of parameters. -/
  paramTy : Assignment → Value → List Value → Nat → TyS

/-- Read a meaning as an element of the Lean type `A` (classically, by the tag). -/
noncomputable def Sem.as (A : Type) : Sem → Option A
  | .el0 B b => open Classical in if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Read a meaning as a number. -/
noncomputable def Sem.asNat (s : Sem) : Option Nat := s.as Nat

/-- `S` on meanings: the successor of a number, the partly moved tuple `S(⊥…)` of a
non-whole argument (D84), `err` otherwise. -/
noncomputable def Sem.succ (s : Sem) : Sem :=
  match s.asNat with
  | some n => .el0 Nat (n + 1)
  | none => open Classical in if s.whole then .err else .ctor "Nat" 1 [s]

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

mutual
/-- The meaning of a value under `ρ` and `φ`, read at the type `hint`, with the declarations
`Γ` (`MState.inds`). -/
noncomputable def Value.mean (ρ : Assignment) (φ : Future) (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (Value.mean ρ φ (.plain (.ty0 Nat)) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (C.global n).1
  | .clo caps t rd => C.clo ρ φ caps t rd
  | .borrow _ w => Value.mean ρ φ hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  | .sealed t => C.sealed ρ φ hint t
  | .proof => .proof
  | .tNat => .ty (.ty0 Nat)
  | .tUnit => .ty (.ty0 Unit)
  | .tEq A a b =>
    let T := TyS.plain (Value.mean ρ φ (.plain .err) A).asTy
    .ty (.prop (Value.mean ρ φ T a = Value.mean ρ φ T b))
  | .tRef A => Value.mean ρ φ (.plain .err) A
  | .tPi caps t rd => .ty (C.pi ρ φ caps t rd)
  | .sort l => .ty (.univ l)
  | .ind ty c _ ps fs =>
    match Γ.find? (·.name == ty) with
    | some d =>
      let ps? := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some (Value.meanParams ρ φ d 0 [] ps)
      match ps? with
      | some ps' => if d.sort == 0 then .proof else dm.ctorM d ps' c (Value.meanFields ρ φ d ps' c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match Γ.find? (·.name == n) with
    | some d => .ty (dm.tyM d (Value.meanParams ρ φ d 0 [] args))
    | none => .ty .err
termination_by structural v => v

/-- The meanings of a constructor's fields, each read at its field type at the earlier ones. -/
noncomputable def Value.meanFields (ρ : Assignment) (φ : Future) (d : IndDecl) (ps : List Sem) (c i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := Value.mean ρ φ (.plain (dm.fieldTy d ps c i earlier)) v
    s :: Value.meanFields ρ φ d ps c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- The meanings of an inductive's parameters, each read at its parameter type. -/
noncomputable def Value.meanParams (ρ : Assignment) (φ : Future) (d : IndDecl) (i : Nat)
    (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := Value.mean ρ φ (.plain (dm.paramTy d i earlier)) v
    s :: Value.meanParams ρ φ d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs
end

/-- The meaning of a type value, as a type. -/
noncomputable def Value.tyM (ρ : Assignment) (φ : Future) (T : Value) : TyM :=
  (Value.mean dm C Γ ρ φ (.plain .err) T).asTy

end

end Ochr.Meaning
