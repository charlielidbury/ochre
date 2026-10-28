import Ochr.Syntax
import Std.Data.HashMap

/-!
# Source locations of core terms (the editor, docs/07)

The `ochr` command records where each surface term is written (`Surface.STerm.loc`). A core
`Term` has no location of its own: resolving the declaration being checked records a side
table from each resolved node's *address* (its identity: terms are values, and `==` ignores
binder names) to its source range. The machine looks a term up when it evaluates it
(`Located.located`), so an error is reported at the innermost located term being evaluated. The
table is empty except when the `ochr` command checks a block, so no other run changes.
-/

namespace Ochr

/-- A source range: byte offsets in the file of the `ochr` block. -/
structure Loc where
  start : Nat
  stop : Nat
deriving Inhabited, BEq, Repr

private unsafe def termAddrImpl (t : Term) : USize := ptrAddrUnsafe t

/-- The address of a term node: its identity, stable while the node is alive. Lean frees a node
when its last reference goes and may reuse the address, so a table keyed by addresses holds a
reference to every node it records (`Locs.keep`): an address in the table is always its node's. -/
@[implemented_by termAddrImpl]
opaque termAddr (t : Term) : USize

/-- A scalar term (`Nat`, `Z`, `Unit`, `()`) is not a heap object: its "address" is its
boxed tag, shared by all its occurrences, so it is never recorded. -/
def isNodeAddr (a : USize) : Bool := a % 2 == 0

/-- Where the declaration being checked is in the source (empty outside the editor). -/
structure Locs where
  /-- a node's address ↦ its range -/
  table : Std.HashMap USize Loc := {}
  /-- every node recorded in `table`, kept alive so that its address is not reused -/
  keep : Array Term := #[]
  /-- a call node's address ↦ its arguments' ranges -/
  args : Std.HashMap USize (Array (Option Loc)) := {}
  /-- a match node's address ↦ its scrutinee's range -/
  scruts : Std.HashMap USize Loc := {}
  /-- the scrutinee (place, range) of the match being split, whose content the next tail
  term (an arm) notes on its path -/
  arm : Option (Place × Loc) := none
  /-- the innermost located term being evaluated (set by `located`; `Rules.fire` notes there) -/
  here : Option Loc := none
  /-- the arguments' ranges of the call being evaluated (set by `located`, read by `callType`) -/
  callArgs : Array (Option Loc) := #[]
  /-- off while evaluating what is not the declaration's own code at this point (a callee's
  parameter types at a call) -/
  on : Bool := true
deriving Inhabited

/-- The immediate subterms of a term, in order (to walk a term and a rebuilt copy of it in
parallel, `Located.relocate`). A constructor missing here only loses locations below it. -/
def Term.children : Term → List Term
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => [t]
  | .letIn _ t u | .seq t u | .cong t u | .ascribe t u => [t, u]
  | .matchNat _ z s => [z, s]
  | .pi _ ds c => ds ++ [c]
  | .fix _ _ ds c _ b => ds ++ [c, b]
  | .call f as _ => f :: as
  | .eq a b c | .id a b c => [a, b, c]
  | .ctor _ _ _ ps as => ps ++ as
  | .prim _ as | .tind _ as => as
  | .matchInd _ _ arms => arms.map (·.2)
  | _ => []

/-- A child of a term is smaller (`Locs.relocate`'s measure). -/
theorem Term.sizeOf_lt_of_mem_children {t o : Term} (h : o ∈ t.children) : sizeOf o < sizeOf t := by
  cases t <;> simp only [Term.children, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    List.mem_map] at h <;> simp only [Term.assign.sizeOf_spec,
    Term.letIn.sizeOf_spec, Term.seq.sizeOf_spec, Term.matchNat.sizeOf_spec, Term.pi.sizeOf_spec,
    Term.fix.sizeOf_spec, Term.call.sizeOf_spec, Term.succ.sizeOf_spec, Term.fst.sizeOf_spec,
    Term.snd.sizeOf_spec, Term.eq.sizeOf_spec, Term.cong.sizeOf_spec, Term.ref.sizeOf_spec,
    Term.id.sizeOf_spec, Term.ascribe.sizeOf_spec, Term.prim.sizeOf_spec, Term.tind.sizeOf_spec,
    Term.ctor.sizeOf_spec, Term.matchInd.sizeOf_spec]
  all_goals first
    | (subst h; omega)
    | (have := List.sizeOf_lt_of_mem h; omega)
    | (rcases h with h | h | h <;> first | (subst h; omega) | (have := List.sizeOf_lt_of_mem h; omega))
    | (rcases h with h | h <;> first | (subst h; omega) | (have := List.sizeOf_lt_of_mem h; omega))
    | (obtain ⟨⟨_, a⟩, ha, rfl⟩ := h
       have := List.sizeOf_lt_of_mem ha
       simp only [Prod.mk.sizeOf_spec] at this ⊢; omega)

/-- The ranges of `old`'s nodes, recorded again for the corresponding nodes of `new`, a copy
of `old` rebuilt with the same shape (`capture` renames a closure's free variables). Stops
where the shapes differ. -/
def Locs.relocate (ls : Locs) (old new : Term) : Locs :=
  let a := termAddr old
  let b := termAddr new
  if a == b then ls else     -- the same node: its subtree is recorded already
  let ls := if !isNodeAddr b || !(ls.table.contains a || ls.args.contains a) then ls else
    let ls := { ls with keep := ls.keep.push new }
    let ls := match ls.table.get? a with
      | some l => { ls with table := ls.table.insert b l }
      | none => ls
    match ls.args.get? a with
    | some as => { ls with args := ls.args.insert b as }
    | none => ls
  if old.children.length != new.children.length then ls
  else (old.children.zip new.children).attach.foldl (fun ls ⟨(o, n), _⟩ => ls.relocate o n) ls
termination_by sizeOf old
decreasing_by exact Term.sizeOf_lt_of_mem_children (List.of_mem_zip ‹_›).1

end Ochr
