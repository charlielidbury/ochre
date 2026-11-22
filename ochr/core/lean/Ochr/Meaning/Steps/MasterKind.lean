import Ochr.Meaning.Steps.MasterPlace
import Ochr.Meaning.Steps.MasterSucc
import Ochr.Meaning.Steps.Machine.StoredTypeCE
import Ochr.Examples.Nat

/-!
# (K), a binding's stored type has its value's kind: guards, the two counterexamples excluded, and what is left
(lead28, 2026-11-22; docs/31 D188)

The invariant's clause `Form.KindTyped` (the lead's ruling on machine11's reading): where its type is stored, a
binding holding a borrow stores a borrow type and one holding a function value (a global function, a closure) a
function type written as one; a global whose value is a function value has a type written as one. A deferred type
and a binding with no type are asked nothing.

* Checked on the checker's own states: at the holes of three real programs below (a borrow parameter, a closure in a
  binding, the lazily typed bindings of a higher-order function's instance run), each guard paired with a broken copy
  of the state that the mirror rejects; and by `lake exe sweep` (its clause (K)) over every example and case study at
  call depth 0 (115,064 states) and, with `--deep-private`, at every call depth inside private copies too (every block,
  the adversarial `SweepProbes.KindAttacks` included): no violation. 58,028 states hold a function value at a deferred
  type and each such type evaluates (`bindTy?`) to a Π written as one; 70,742 states carry a deferred call's record,
  each a Π written as one.
* The two counterexamples machine11 pinned now fail the invariant: `StoredTypeCE.stB` (`x ↦ borrow_0(Z) : Nat`) is
  refuted in the kernel (`not_kindTyped_stB`); `StoredTypeCE.stF` (`f ↦ g : Nat`, a global function at `Nat`) by guard.
* What is still missing for the two facts, stated as named run facts (checker, UNREAD): `EvalKindT` (a typed run returns
  a type, a borrow at a borrow type and a function value at a Π written as one), `ExpectRefNat` (`expectTy` of a borrow type
  against `Nat` fails), from which `SuccArgNoBorrowT` follows (`succArgNoBorrowT_of`, PROVED); and `LaterPiG` (an
  untyped deferred call records a Π written as one), the gap under `LetCallInvU`.
-/

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## The counterexamples excluded -/

/-- machine11's state for `SuccArgNoBorrowT` (`x ↦ borrow_0(Z)` stored at `Nat`) fails (K). -/
theorem not_kindTyped_stB : ¬ KindTyped Machine.StoredTypeCE.stB := fun h => by
  obtain ⟨A, hA⟩ := (h.1 0 1 _ rfl).1 0 .zero rfl .tNat rfl
  cases hA

/-- A Bool mirror of (K), for guards: every binding of every frame, and every global. -/
def kindAtB (b : Binding) : Bool :=
  (match b.val, b.ty with
    | .borrow .., some (.tRef _) => true
    | .borrow .., some _ => false
    | _, _ => true) &&
  (if b.val.isFnVal then (match b.ty with | some T => T.piWritten | none => true) else true)

def kindTypedB (st : MState) : Bool :=
  st.env.toList.all (fun fr => fr.binds.toList.all kindAtB) &&
    st.globals.all fun g => !g.val.isFnVal || g.ty.piWritten

-- machine11's state for the gap under `LetCallInvU` (`f ↦ g`, a global function stored at `Nat`) fails (K)
#guard !kindTypedB Machine.StoredTypeCE.stF
#guard !kindTypedB Machine.StoredTypeCE.stB

end Ochr.Meaning.Steps.Form.Master

#guard_msgs (drop warning) in
ochr KindAt uses Nats {
  def AtBorrow (r : &Nat) : Unit := ?
  def AtClosure (n : Nat) : Unit := (let f = (λ(m : Nat) : Nat => S(m)); ?)
  def Idn (n : Nat) : Nat := n
  def HO (f : Π(m : Nat). Nat) (x : Nat) : Nat := (let y = f(x); y)
  def UseHO : Nat := HO(Idn, Z)
}

namespace Ochr.Meaning.Steps.Form.Master.KindGuards

open Ochr Ochr.Meaning Ochr.Test

def rows (deep : Bool) : List Ochr.Test.Row :=
  (Ochr.Test.runWith (some Prelude) "KindAt" KindAt { recordStates := true, recordDeep := deep } (located := true)).rows

/-- The checker's state at the hole of `decl`. -/
def holeSt (decl : String) : MState :=
  match (rows false).find? (·.name == decl) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- Every state recorded at call depth above 0 in `decl`'s check (a callee's body run in place). -/
def deepSts (decl : String) : List MState :=
  match (rows true).find? (·.name == decl) with
  | some row => row.trace.toList.filterMap fun | .deep _ _ st => some st | _ => none
  | none => []

/-- The state with the top frame's binding `i` (from the bottom) given the stored type `T`. -/
def retype (st : MState) (i : Nat) (T : Option Value) : MState :=
  { st with env := st.env.modify (st.env.size - 1) fun fr => { fr with binds := fr.binds.modify i ({ · with ty := T }) } }

-- a borrow parameter: `r ↦ borrow_ℓ σ` at `&Nat` (the cell its loan); stored at `Nat` instead, (K) fails
#guard (holeSt "AtBorrow").env.toList.any (·.binds.toList.any fun b => b.val.isBorrow && (b.ty matches some (.tRef _)))
#guard kindTypedB (holeSt "AtBorrow")
#guard !kindTypedB (retype (holeSt "AtBorrow") ((holeSt "AtBorrow").env.back!.binds.size - 1) (some .tNat))

-- a closure in a binding: `f ↦ clo …` at `Π(m : Nat). Nat`; stored at `Nat` instead, (K) fails
#guard (holeSt "AtClosure").env.back!.binds.toList.any fun b => (b.val matches .clo ..) && (b.ty.map Value.piWritten == some true)
#guard kindTypedB (holeSt "AtClosure")
#guard !kindTypedB (retype (holeSt "AtClosure") ((holeSt "AtClosure").env.back!.binds.size - 1) (some .tNat))

-- the lazily typed bindings of `HO`'s instance run (`UseHO`): `f ↦ Idn` and `x` at deferred parameter types, every
-- recorded state meets (K); `f`'s deferred type evaluates (`bindTy?`) to a Π written as one; `f` stored at `Nat`
-- instead, (K) fails
#guard (deepSts "UseHO").length > 0
#guard (deepSts "UseHO").any fun st => st.env.toList.any (·.binds.toList.any fun b => (b.val matches .gfn "Idn") && b.ty.isNone && b.lazyTy.isSome)
#guard (deepSts "UseHO").all kindTypedB
#guard (deepSts "UseHO").all fun st => (List.range st.env.size).all fun f => (List.range st.env[f]!.binds.size).all fun i =>
  let b := st.env[f]!.binds[i]!
  !(b.val.isFnVal && b.ty.isNone && b.lazyTy.isSome) ||
    match (runMachine (Ochr.bindTy? 1000 (.bind f i)) { st with tailDecl := none, headEval := false } 200000).1 with
    | .ok (some T) _ => T.piWritten
    | _ => false
#guard (deepSts "UseHO").any fun st => !kindTypedB
  { st with env := st.env.map fun fr => { fr with binds := fr.binds.map fun b => if b.val matches .gfn "Idn" then { b with ty := some .tNat } else b } }

-- `DeferClearG` (the placeholder until main's D130): from the hole of `AtClosure` (`f` a closure), the untyped `let` of a
-- call, its type wanted, ends with the deferral flag clear; and the leak it guards against: `Z` run from a state with
-- the flag SET ends with it still set (no evaluation consumes it today but a call's, D187)
def runFlag (st : MState) (t : Term) : Option Bool :=
  match (runMachine (do
      modify fun s => { s with wantTy := true }
      discard (Ochr.eval 1000 false t none)
      pure (← get).deferCallTy) st 1000000).1 with
  | .ok b _ => some b
  | _ => none

#guard runFlag (holeSt "AtClosure") (.letIn ⟨"y"⟩ (.call (.place (.var 0)) [.zero] false) (.place (.var 0))) == some false
#guard runFlag { holeSt "AtClosure" with deferCallTy := true } .zero == some true

end Ochr.Meaning.Steps.Form.Master.KindGuards

namespace Ochr.Meaning.Steps.Form.Master

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-! ## What is still missing (named, checker, UNREAD) -/

/-- **A typed run's value has its type's kind** (checker, NEW, lead28, docs/31 D188; UNREAD): from a state meeting the
checker's invariant, a typed run of any term returns a type (read TRUE as `SuccStrictG`'s checker half), and a borrow
only at a borrow type and a function value only at a function type written as one. The induction over `eval` whose base at a read is (K): a read of a variable returns its
stored type (`placeType`), so (K) gives it; where the type is deferred, the read evaluates it (`bindTy?`), which is
this fact's own obligation (the sweep: every such type evaluates to the right kind); `&p` returns `T.map .tRef`; a
`let`/`;`/match returns its tail's; a call its codomain at the arguments (`callType`; a borrow result exactly at a
borrow codomain, D48); an ascription its annotation (conversion keeps the kind). The generalisation of
`SuccArgNoBorrowT` that `LetPushG` needs too: the binding a `let` pushes meets (K) exactly by it. -/
def EvalKindT : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (n : Nat) (u : Term) (hint : Option Value) (st₀ st₁ : MState) (bh : Nat) (v : Value)
    (T? : Option Value),
    Pre K ρ st₀ → Runs (Ochr.eval n true u hint) st₀ bh (v, T?) st₁ →
    ∃ T, T? = some T ∧ (∀ l c, v = .borrow l c → ∃ A, T = .tRef A) ∧ (v.isFnVal = true → T.piWritten = true)

/-- **A borrow type does not convert to `Nat`** (checker, NEW, lead28; UNREAD): `expectTy` of `&A` against `Nat` fails. -/
def ExpectRefNat : Prop :=
  ∀ (n : Nat) (w : String) (A : Value) (st st' : MState) (bh : Nat),
    ¬ Runs (Ochr.expectTy n w (some (.tRef A)) .tNat) st bh () st'

/-- **`SuccArgNoBorrowT` from the two** (PROVED, standard axioms): the typed argument returns a type; were its value a
borrow, the type would be `&A`, and `expectTy` of `&A` against `Nat` would fail. -/
theorem succArgNoBorrowT_of (hK : EvalKindT) (hR : ExpectRefNat) : SuccArgNoBorrowT := by
  intro K ρ n u st₀ st₁ st₂ bh₁ bh₂ v₀ T₀ hp hu hx l w e
  obtain ⟨T, rfl, hb, -⟩ := hK K ρ n u none st₀ st₁ bh₁ v₀ T₀ hp hu
  obtain ⟨A, rfl⟩ := hb l w e
  exact hR n _ A st₁ st₂ bh₂ hx

-- `LaterPiG` (an untyped deferred call that returns no type records a Π written as one, the gap under `LetCallInvU`)
-- is stated beside `LetCallInvU` in `Steps/MasterUntyped.lean`, where the untyped `let` of a call consumes it (D190).

end Ochr.Meaning.Steps.Form.Master
