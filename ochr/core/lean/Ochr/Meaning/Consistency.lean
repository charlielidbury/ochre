import Ochr.Meaning.Program
import Ochr.Meaning.Bounded
import Ochr.Meaning.Steps.Tail

/-!
# Milestone 4: the assembly of `consistencyBounded` (docs/18 Corollaries 15 and 16)

The chain, each link a statement here (all `sorry`; the step lemmas are `Steps/*.lean`):
1. **Acceptance resolves.** `Accepted (Prelude.decls ++ q) fuel` means every declaration resolves
   to an item (`Run.checkProgram`'s first loop) and `checkDefs` gives each item `accepted`; so
   the items are checked in order from the Σ of the earlier ones, exactly as `progMeaning`
   steps through them (`Program.progMeaning_sig`).
2. **Every accepted definition means an element of its type** (`defn_member`): by induction on
   the items, an accepted function's closure is a member of its Π-type (`Steps/Tail.checkFix_sound`)
   and an accepted constant's value a member of its goal (`checkConst_sound`), under the globals'
   meanings so far; the data model covers every accepted declaration (`checkInd_sound`).
3. **`False` means the empty proposition**: the library's `False` has no constructors, so its
   carrier is empty and `tyM` gives `prop False` (`false_means_empty`, a law of the data model
   for the library's declaration, which `libModel` and the generic model satisfy).
4. **Consistency**: a parameterless definition of type `False` would mean a member of `prop
   False`, that is, a proof of `False` (`Sem.mem proof (prop P) = P`); so there is none.
A data model exists for every accepted program (`exists_dataModel`, data-generic's generic
construction), which turns the relative statement into `consistencyBounded`.

What the assembly covers as the run stands (docs/31 D12): definitions whose Π-type is in `Type₀`
or `Prop`; polymorphic definitions wait on the level-1 construction.
-/

namespace Ochr.Meaning.Assembly

open Ochr.Meaning Ochr.Surface Ochr.Consistency

section
variable (dm : DataModel) (D : MState → Decisions)

/-- The items of a surface program, when every declaration resolves (`Run.checkProgram`'s first
loop, `runResolve`), in order. -/
def ResolvesTo (p : Program) (fuel : Nat) (items : List Item) : Prop :=
  items.length = p.length ∧
  ∀ (i : Nat) (d : SDecl) (it : Item), p[i]? = some d → items[i]? = some it →
    ∃ st, (runResolve p d fuel false).1 = .ok (.ok it) ∧ (runResolve p d fuel false).2 = st

/-- (1) An accepted program resolves to items each of which `checkDefs` accepts; and the state
each item is checked from is the Σ of the items before it. -/
theorem accepted_resolves (p : Program) (fuel : Nat) (acc : Accepted p fuel) :
    ∃ items, ResolvesTo p fuel items ∧
      ∀ (i : Nat) (it : Item), items[i]? = some it →
        let P := progMeaning dm D (fun _ => .err) {} fuel (items.take i)
        (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _ := by
  sorry

/-- (2) Every accepted definition's meaning is a member of its type, at the empty assignment and
every future: the induction over the items, with `Steps/Tail.checkFix_sound` for a function
and `checkConst_sound` for a constant, each under `Good` at the generic state
(`Steps/Tail.generic_good`), and `checkInd_sound` keeping the data model covering Σ. -/
theorem defn_member (items : List Item) (fuel : Nat)
    (hacc : ∀ (i : Nat) (it : Item), items[i]? = some it →
      let P := progMeaning dm D (fun _ => .err) {} fuel (items.take i)
      (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _)
    (hcov : (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm) :
    let P := progMeaning dm D (fun _ => .err) {} fuel items
    ∀ n s T, (n, s, T) ∈ P.means → s ∈ₛ T.m := by
  sorry

/-- (3) The library's `False` means the empty proposition: `tyM` of a declaration with no
constructors is `prop (Nonempty car)`, and a carrier with no constructor is empty
(`DataModel.pack_fields`: every element is a constructor applied to fields). -/
theorem false_means_empty (d : IndDecl) (hd : d.name = "False" ∧ d.ctors = [] ∧ d.sort = 0)
    (hcov : dm.covers d) : dm.tyM d [] = .prop False := by
  sorry

/-- The stored type of a parameterless definition declared `: False` is the library's `False`
applied to nothing, once the library is in front (names are distinct: `Check.declared`). -/
theorem falseConst_ty (q : Program) (fuel : Nat) (items : List Item) (d : SDecl)
    (hres : ResolvesTo (Prelude.decls ++ q) fuel items) (hd : d ∈ q) (hf : d.IsFalseConst) :
    let P := progMeaning dm D (fun _ => .err) {} fuel items
    ∃ s T, (d.name, s, T) ∈ P.means ∧ T.m = .prop False := by
  sorry

/-- (4) Consistency, relative to a data model covering the program and the decisions read from
the checker: no accepted, hole-free, level-bounded program has a parameterless definition of
type `False`. A member of `prop False` is a proof of `False` (`Sem.mem`). -/
theorem consistency_rel (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel)
    (hcov : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  sorry

end

/-- A data model covering every accepted program exists (the generic construction by stages,
`DataGeneric.lean`, data-generic), with the checker's decisions (`DecisionsInst.checkerDecisions`). -/
theorem exists_dataModel (items : List Item) (fuel : Nat) :
    ∃ (dm : DataModel) (D : MState → Decisions),
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm := by
  sorry

/-- `consistencyBounded` from the relative statement and the existence of a data model. -/
theorem consistencyBounded_assembled (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  sorry

end Ochr.Meaning.Assembly
