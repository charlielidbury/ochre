import Ochr.Meaning.Data
import Ochr.Meaning.Future

/-!
# The meaning of a value, `⟦v⟧_{ρ,φ}` (docs/18 Def. "meaning of a state", docs/27 Def. 2)

Under an assignment `ρ` of the abstract values and a future `φ` of the live borrows:
* `σ` means `ρ σ`; `⋆` means `•`; `⊥` means `moved`; `Z`, `S v`, `()` mean the numbers and the
  unit as elements of `Nat` and `Unit`;
* a constructor value means `el0` of its data carrier at the parameters it records, or an
  untyped tuple when a field holds `moved` (`DataModel.ctorM`);
* a type value means `ty T`: `Nat`, `Unit`, `sort l`, `D(ā)` by the data model, `Eq(A, a, b)` the
  proposition `⟦a⟧ = ⟦b⟧` (so `Eq` reads no type: docs/24 C10), `&A` the content type `⟦A⟧`
  (a borrow is read as what it holds, so a borrow-typed place means its content: see the note on
  `tRef`);
* `borrow_ℓ w` means `⟦w⟧`, its *current* content; `loan_ℓ` means `φ ℓ`, the *final* content
  of the borrow that took it (docs/27 §3);
* a global, a closure, a Π-closure and a sealed program mean what running code means, through
  `CodeMeaning`, which the reference run supplies (milestone 2, Q3): a closure is a function on
  its annotated domain, a Π-closure the dependent product of its components, a sealed program its
  program run from the empty state with every loan read from `φ`.

The definition is total; an ill-formed value means `err`.
-/

namespace Ochr.Meaning

/-- What the meaning of a value needs from the meaning of code (Q3). The reference run
(`Run.lean`) defines these together with `Value.mean` in one recursion; here they are a
parameter, so that the first-order meaning is fixed and checkable on its own. -/
structure CodeMeaning where
  /-- The meaning of the global `gfn n` (a function) or of a constant, from the program so far. -/
  global : String → Sem
  /-- The meaning of the sealed program `⌈t⌉`: `t` run from the empty state, its abstract values
  read from `ρ` and its loans (holes, inert loans) from `φ`. -/
  sealed : Assignment → Future → Term → Sem
  /-- The meaning of the closure `clo caps t rd`: a function on its annotated domain, read off the
  reference run of its body with the captures bound at their recorded types; a recursive closure
  by guarded recursion on the rank of its decreasing argument (docs/24 §4). -/
  clo : Assignment → Future → List Value → Term → List (DeclInfo × Value) → Sem
  /-- The meaning of the Π-closure `tPi caps t rd`: the dependent product of its parameter types
  and codomain, evaluated at every argument (impredicatively a proposition when its codomain is
  one; with the final contents of borrowed parameters, and an injective backward function when it
  returns a borrow: `Slice.lean` §1). -/
  pi : Assignment → Future → List Value → Term → List (DeclInfo × Value) → TyM
  /-- The meaning of a deferred type (D82 `Binding.lazyTy`): parameter `i` of the Π-type `P` at
  the arguments `ws` as passed, or `P`'s codomain there for `i` the number of parameters. -/
  paramTy : Assignment → Value → List Value → Nat → TyM

/-- Read a meaning as an element of the Lean type `A` (classically, by the tag). -/
noncomputable def Sem.as (A : Type) : Sem → Option A
  | .el0 B b => open Classical in if h : B = A then some (h ▸ b) else none
  | _ => none

/-- Read a meaning as a number. -/
noncomputable def Sem.asNat (s : Sem) : Option Nat := s.as Nat

/-- Read a meaning as a type. -/
def Sem.asTy : Sem → TyM
  | .ty T => T
  | _ => .err

/-- `S` on meanings: the successor of a number, the partly moved tuple `S(⊥…)` of a
non-whole argument (D84), `err` otherwise. -/
noncomputable def Sem.succ (s : Sem) : Sem :=
  match s.asNat with
  | some n => .el0 Nat (n + 1)
  | none => open Classical in if s.whole then .err else .ctor "Nat" 1 [s]

section
variable (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl)

mutual
/-- The meaning of a value under `ρ` and `φ`, with the declarations `Γ` (`MState.inds`). -/
noncomputable def Value.mean (ρ : Assignment) (φ : Future) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (Value.mean ρ φ v).succ
  | .unit => .el0 Unit ()
  | .gfn n => C.global n
  | .clo caps t rd => C.clo ρ φ caps t rd
  | .borrow _ w => Value.mean ρ φ w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  | .sealed t => C.sealed ρ φ t
  | .proof => .proof
  | .tNat => .ty (.ty0 Nat)
  | .tUnit => .ty (.ty0 Unit)
  | .tEq _ a b => .ty (.prop (Value.mean ρ φ a = Value.mean ρ φ b))
  | .tRef A => Value.mean ρ φ A
  | .tPi caps t rd => .ty (C.pi ρ φ caps t rd)
  | .sort l => .ty (.univ l)
  | .ind ty c _ ps fs =>
    match Γ.find? (·.name == ty) with
    | some d => dm.ctorM d (Value.meanList ρ φ ps) c (Value.meanList ρ φ fs)
    | none => .err
  | .tInd n args =>
    match Γ.find? (·.name == n) with
    | some d => .ty (dm.tyM d (Value.meanList ρ φ args))
    | none => .ty .err
termination_by structural v => v

noncomputable def Value.meanList (ρ : Assignment) (φ : Future) : List Value → List Sem
  | [] => []
  | v :: vs => Value.mean ρ φ v :: Value.meanList ρ φ vs
termination_by structural vs => vs
end

/-- The meaning of a type value, as a type. -/
noncomputable def Value.tyM (ρ : Assignment) (φ : Future) (T : Value) : TyM :=
  (Value.mean dm C Γ ρ φ T).asTy

end

end Ochr.Meaning
