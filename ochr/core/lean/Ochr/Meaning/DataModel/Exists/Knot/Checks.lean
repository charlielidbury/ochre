import Ochr.Meaning.DataModel.Exists.Knot.FromChecker

/-!
# The checker's checks on an inductive declaration, as pure functions (exists8, step 2)

`checkInd` (`Check.lean`) checks each field type of a declaration `d` with three monadic functions
that read the declarations through `lookupInd`: `firstOrderTerm` (D36, K4, D71), `readViolation`
(D120) and the pure `sortNestViolation` (D121); and it stores `d` with the nestable set
`nestableSet` computed from the fields (D107). Here: pure mirrors of the two monadic ones
(`foB`, `rvB`), with the lookups made in the declarations the checker sees while it checks the fields
(`declEnv`: the earlier ones, then `d`'s entry with no constructors), and the bundle `IndChecks Γ0 d`
of everything `checkInd` establishes about the stored `d` that the grammar needs.

The mirrors are WEAKER than the checker where the grammar does not need a test (a called global's
codomain, the arguments of a call beyond not mentioning `d`, an equation's type being first-order),
so that the bridge from the checker's run to them is the easy direction. The bridge itself is a named
fact for the machine lane, `CheckIndGivesChecks` (read from `checkInd`'s code). The one fact the
bundle does not hold is that a declared field type contains no embedded value (`FieldsNoVal`): it
holds of resolved surface syntax, and no check of the checker's establishes it.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr

/-- The declarations `checkInd` looks names up in while it checks `d`'s fields: the earlier ones,
then `d`'s entry with no constructors and no nestable parameter (`checkInd`'s `modify`). -/
def declEnv (Γ0 : List IndDecl) (d : IndDecl) : List IndDecl :=
  Γ0 ++ [{ d with ctors := [], nestable := [], declaring := true }]

/-- The nesting table `checkInd` checks `d`'s fields against (its `nest`): `d`'s own set as stored,
the earlier declarations' as stored. -/
def ownNest (Γ0 : List IndDecl) (d : IndDecl) : NestTable := fun m j =>
  if m == d.name then d.nestable.getD j false else nestTableOf Γ0 m j

/-- `checkInd`'s `reads` at constructor `c`: a variable the term reads (`deepVars`) whose declared
type mentions `d`. -/
def readsOf (d : IndDecl) (c : Nat) (t : Term) : Option Nat :=
  (d.deepVars c t).find? fun u => ((d.varType c u).map (·.mentionsType d.name)).getD false

mutual
/-- `firstOrderTerm`, pure and weakened: a call's arguments only do not mention `n`, and an
equation's parts only do not mention `n`. -/
def foB (Γd : List IndDecl) (nest : NestTable) (n : String) (np : Nat) : Term → Bool
  | .nat => true
  | .unit => true
  | .place (.var j) => decide (j < np)
  | .tind m as => match Γd.find? (·.name == m) with
    | some dm => foArgsB Γd nest n np m dm 0 as
    | none => false
  | .call (.const _) as _ => !Term.mentionsTypeList n as
  | .eq A a b => !A.mentionsType n && !a.mentionsType n && !b.mentionsType n
  | _ => false
termination_by structural t => t

/-- `firstOrderArgs`, pure. -/
def foArgsB (Γd : List IndDecl) (nest : NestTable) (n : String) (np : Nat) (m : String) (dm : IndDecl) :
    Nat → List Term → Bool
  | _, [] => true
  | i, a :: as =>
    (if dm.paramIsType i then foB Γd nest n np a && (!a.mentionsType n || nest m i) else !a.mentionsType n) &&
      foArgsB Γd nest n np m dm (i + 1) as
termination_by structural _ as => as
end

mutual
/-- `readViolation`, pure: is there a violation (`true`)? -/
def rvB (Γd : List IndDecl) (reads : Term → Option Nat) : Term → Bool
  | .tind m as => match Γd.find? (·.name == m) with
    | some dm => rvArgsB Γd reads dm 0 as
    | none => false
  | .call f as hd => (reads (.call f as hd)).isSome
  | .eq A a b => (reads (.eq A a b)).isSome
  | _ => false
termination_by structural t => t

/-- `readViolationArgs`, pure. -/
def rvArgsB (Γd : List IndDecl) (reads : Term → Option Nat) (dm : IndDecl) : Nat → List Term → Bool
  | _, [] => false
  | i, a :: as => (if dm.paramIsType i then rvB Γd reads a else (reads a).isSome) || rvArgsB Γd reads dm (i + 1) as
termination_by structural _ as => as
end

/-- **What `checkInd` establishes about the declaration it stores**, at the declarations `Γ0` before
it: its name is fresh ([Ind-decl]); its stored nestable set is `nestableSet`'s (D107, D120, D121);
its fields are a telescope ([Ind], D64); and at every field type the three checks pass. -/
structure IndChecks (Γ0 : List IndDecl) (d : IndDecl) : Prop where
  fresh : Γ0.find? (·.name == d.name) = none
  nest : d.nestable = nestableSet (nestTableOf Γ0) (sortTableOf Γ0 d) d
  tele : TeleOk d
  fo : ∀ c i FT, fieldTerm d c i = some FT → foB (declEnv Γ0 d) (ownNest Γ0 d) d.name d.params.length FT = true
  rv : ∀ c i FT, fieldTerm d c i = some FT → rvB (declEnv Γ0 d) (readsOf d c) FT = false
  sv : ∀ c i FT, fieldTerm d c i = some FT → sortNestViolation (sortTableOf Γ0 d) d.name d.sort FT = none

/-- **A declared field type holds no embedded value**: a fact about resolution (resolved surface
syntax has none), which no check of the checker's establishes. -/
def FieldsNoVal (d : IndDecl) : Prop :=
  ∀ c i FT, fieldTerm d c i = some FT → FT.anyAtom (fun _ => true) = false

/-- **The bridge** (PROVED: `Steps.Machine.checkIndGivesChecks`, exists12): when `checkInd` accepts `d` at a state, the
declarations after it are the ones before it and one more, the entry it stores, and that entry
passes `IndChecks` at the declarations before it. Read from `checkInd`'s code: the freshness test,
the stored `nestable := ownSet`, the [Ind] loop, and at each field `firstOrderTerm` returning `true`,
`readViolation` returning `none` and `sortNestViolation` returning `none` at a state whose
declarations are `declEnv`'s (the mirrors are weaker than those functions). -/
def CheckIndGivesChecks : Prop :=
  ∀ (d : IndDecl) (st st' : MState) (fuel : Nat), (runMachine (checkInd d) st fuel).1 = .ok () st' →
    ∃ d', st'.inds = st.inds ++ [d'] ∧ IndChecks st.inds d'

end Ochr.Meaning.DataModel.Exists.Knot
