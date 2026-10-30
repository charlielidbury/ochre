import Ochr.Machine

/-!
# Stability (the paper's Conjecture 2), stated (the proof is open)

A statement is evaluated along two paths: at a definition's generic call, where calls and
matches on abstract values close off, and directly at each instance, where they run.
[Call-type] and [Split] identify the results, so a proof checked on the first path is used on
the second. The paper's Conjecture 2 says the two paths take the same decisions: refining and
then running makes the same choices as running and then refining. This file states it against
the checker; `notes/stability.md` decomposes it site by site, and `StabilitySig.lean` proves the
fields of `DecisionsCommute` that need neither `RunsCorrespond` nor typing (`stability`).

## What a refinement is

A refinement `α` (`Refinement`) is a list of values for abstract values, `σ ↦ v`. The paper's
three kinds are all of this form in the checker:
* a value for an abstract value, as a case split makes (`σ := S(σ')`) or a call site does
  (a parameter's generic `σ` instantiated with the argument);
* a definable closure for an abstract function: an abstract function is an abstract value of
  a Π-type, refined to a closure or a top-level function;
* a value for a hole: a hole is a fresh abstract value of its type (`hole-fix`), so refining
  it is the same operation.

It is applied as the checker applies a refinement (`refine`): substituted into every value of
Ω, every stored type, the type of every abstract value and the goal, with every sealed program
it reaches re-normalised (`Refinement.onState`), and into terms and values the same way
(`Refinement.onTerm`, `Refinement.onValue`). It must respect Ω (`Respects`): each `σ` it
refines is an unknown of Ω, and the value it gets has a type convertible with `σ`'s, which is
the paper's "of a type convertible with the one it replaces".

## What "the same decisions" means

The paper's statement is about subterms both runs reach. The checker is a big-step machine that
builds no derivation tree, and the two runs do not even visit the same subterms: the generic
run closes off a call the instance runs, and checks every arm of a match the instance takes
one arm of. So the statement is split into its two halves, each a precise statement about the
checker's functions:

* **The decisions commute with refinement** (`DecisionsCommute`). A decision is a call of one
  of the checker's decision functions (the erasure pre-pass, a function type's class, [Close]'s
  row, whether a match is on a proof, a stuck block's captures, an observed place's type, the
  footprint). Each must give, on refined inputs, the refinement of what it gave on the
  originals: the same flags, class, row, captures and modes; the refined type; and, for the
  footprint, containment (the paper's item 6). These are the paper's items (1), (2), (4), (5)
  and (6), one field each.
* **The runs stay related** (`RunsCorrespond`). Running `tα` at `Ωα` does not go wrong where
  running `t` at `Ω` did not, and when it finishes it agrees, up to resolution, with the
  generic run's result and final state refined by `α`. This is what makes the two runs present
  related inputs to the decision functions at the subterms they both reach, and it gives the
  paper's item (3) (an arm is well typed on both runs or on neither) and the second half of
  item (6) (the extra equations compute to `⊤`). It is naturality (Conjecture 3) for a
  symbolic refinement, not only a ground one.

`Conjecture2` is their conjunction.

## Up to resolution

Two runs can place their borrows differently and name their fresh unknowns differently, so
results and states are compared after *resolution* (the paper's `ρ`): every borrow ended
(`endAll`), which leaves no loan to rename, and then the unknowns either run created
(at or above Ω's `nextAbs`) renamed injectively onto the other's (`FreshRenaming`, itself a
refinement by unknowns). `AgreeUpToρ` compares the values and every position's content.

## What is proved here

Only `byTypeMatch_arms`: whether a match is on a proof reads the arms' constructors, never
their bodies, so it commutes with any refinement of the bodies (site 11, by construction).
The census sites that read only syntax and declared types are stable for the same reason,
since a refinement changes no term's syntax and no binding's declared reading; that general
fact is stated in `notes/stability.md` and not proved here.
-/

namespace Ochr.Stability
open Ochr

/-- Run a machine computation from a state: its value and final state, if it succeeds. -/
def run? {α : Type} (x : M α) (Ω : MState) (fuel : Nat) : Option (α × MState) :=
  match (runMachine x Ω fuel).1 with
  | .ok a Ω' => some (a, Ω')
  | _ => none

/-- A computation fails: a type error, as opposed to success or exhaustion. -/
def Fails {α : Type} (x : M α) (Ω : MState) (fuel : Nat) : Prop :=
  match (runMachine x Ω fuel).1 with
  | .fail _ => True
  | _ => False

/-- A refinement: values for abstract values, `σ ↦ v`. Abstract functions and holes are
abstract values too, so this covers the paper's three kinds. -/
abbrev Refinement := List (Nat × Value)

namespace Refinement

/-- Apply `α` to the state, as [Split] does: substitute into Ω, the stored types, the types of
unknowns and the goal, re-normalising every sealed program it reaches (`refine`). -/
def onState (α : Refinement) (fuel : Nat) : M Unit :=
  α.forM fun p => refine fuel p.1 p.2

/-- Apply `α` to a value (sealed programs re-normalised, `substV`). -/
def onValue (α : Refinement) (fuel : Nat) (v : Value) : M Value :=
  α.foldlM (fun v p => substV fuel (.abs p.1) p.2 v) v

/-- Apply `α` to a term (its embedded values, `substT`). -/
def onTerm (α : Refinement) (fuel : Nat) (t : Term) : M Term :=
  α.foldlM (fun t p => substT fuel (.abs p.1) p.2 t) t

end Refinement

/-- A value is borrow-free: no borrow type, borrow or loan anywhere inside it. -/
def borrowFree (v : Value) : Bool :=
  !(v.anyAtom fun | .tRef _ | .borrow _ _ | .loan _ => true | _ => false)

/-- `α` respects `Ω`: each `σ` it refines is an unknown of `Ω`, and the value it gets is
borrow-free and checks at `Ω` with a type convertible with `σ`'s.

Borrow-free is the paper's refinements, not a weakening. They substitute constructor values,
closures and ground values, never borrows: a borrow parameter's generic value is `borrow_ℓ σ`
with `σ` itself borrow-free, and closures capture no borrows (RULES §1). Nor is any unknown type
ever given a borrow type: `&` is only the whole declared type of a parameter, result or
annotated term, never an argument (D48 (2), tests `UseBlkRef` and `UseBlkBox`, block `BlockRow`
in `Examples/BorrowTypes.lean`). Without it, refining `σ0 : Type` to `&Nat` would make a
binding of type `σ0` a borrow-typed one, and its footprint grow (`probe_footprint_*` in
`StabilityFootprint.lean`). -/
def Respects (α : Refinement) (Ω : MState) (fuel : Nat) : Prop :=
  ∀ p ∈ α, p.1 < Ω.absTy.size ∧ borrowFree p.2 = true ∧
    ∃ v T Ω₁ Ω₂, run? (eval fuel true (.val p.2)) Ω fuel = some ((v, some T), Ω₁) ∧
      run? (conv fuel T Ω.absTy[p.1]!) Ω₁ fuel = some (true, Ω₂)

/-- What an observation can see of a state: every binding's and temporary's value, frame by
frame. -/
def contents (Ω : MState) : List (List Value) :=
  Ω.env.toList.map fun fr => fr.binds.toList.map (·.val) ++ fr.temps.toList

/-- Resolution `ρ`: end every borrow, with `v` held as a temporary so that a loan inside it is
resolved too. -/
def resolve? (v : Value) (Ω : MState) (fuel : Nat) : Option (Value × MState) :=
  run? (do pushTemp v; endAll fuel; popTemp) Ω fuel

/-- A renaming of the unknowns a run created (those at or above `fresh`): injective, onto
unknowns at or above `fresh`. -/
def FreshRenaming (β : Refinement) (fresh : Nat) : Prop :=
  (∀ p ∈ β, fresh ≤ p.1 ∧ ∃ σ', p.2 = .abs σ' ∧ fresh ≤ σ') ∧
    (β.map (·.1)).Nodup ∧ (β.map (·.2)).Nodup

/-- Agreement up to resolution: after `ρ`, and after renaming the fresh unknowns of the first
to the second's, the values are equal and every position holds the same value. -/
def AgreeUpToρ (v₁ : Value) (Ω₁ : MState) (v₂ : Value) (Ω₂ : MState) (fresh fuel : Nat) : Prop :=
  ∃ r₁ R₁ r₂ R₂ β w R₁',
    resolve? v₁ Ω₁ fuel = some (r₁, R₁) ∧ resolve? v₂ Ω₂ fuel = some (r₂, R₂) ∧
    FreshRenaming β fresh ∧
    run? (do let w ← β.onValue fuel r₁; β.onState fuel; pure w) R₁ fuel = some (w, R₁') ∧
    w = r₂ ∧ contents R₁' = contents R₂

/-- The erasure pre-pass's decision for a term at a state: its flags (erased, proof), read from
its declared type in the live scope (`evalAt`). -/
def erasureOf (fuel : Nat) (t : Term) : M (Option (Bool × Bool)) := do
  preFlags t (← withLive true (declOf fuel false [] [] t))

/-- **The decisions commute with refinement.** Each field is one of the paper's items, for the
decision function the checker uses: on refined inputs it gives the refinement of what it gave on
the originals (`Ωα` the refined state, `tα`, `Pα` the refined term or value). Each says that what
the generic run decided, the instance decides too; where the generic run fails there is nothing
to commute (the definition is rejected).

A function type's class and [Close] row are stated for Π-type values only. For anything else
they are not decisions of any run that goes on: `fnClass` reads `0` and `declKind` fails on an
unknown `A : Type`, and a refinement of `A` to a Π-type would read a class and a row the generic
run never decided. Every call reads them through `callFn`, which rejects a callee whose type is
not a Π-type (`callType`, `declKind`) before reading the class; `stmtCallee`'s earlier read is
followed by that `callFn`. The order is pinned by comments at both sites and by the test
`CallSort` (`Examples/Functions.lean`, block `CallUnknown`). -/
structure DecisionsCommute : Prop where
  /-- (1) Erasure: the pre-pass gives a term and its refinement the same flags. -/
  erasure : ∀ (Ω : MState) (α : Refinement) (t : Term) (fuel : Nat), Respects α Ω fuel →
    ∀ Ωα tα fl Ω₁, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
      (run? (α.onTerm fuel t) Ω fuel).map (·.1) = some tα →
      run? (erasureOf fuel t) Ω fuel = some (fl, Ω₁) →
      (run? (erasureOf fuel tα) Ωα fuel).map (·.1) = some fl
  /-- (1) A match is on a proof by its arms' constructors and the scrutinee's declaration. -/
  byType : ∀ (Ω : MState) (ty : String) (arms : List (Hint × Term)) (g : Term → Term) (fuel : Nat),
    (run? (byTypeMatch ty (arms.map fun a => (a.1, g a.2))) Ω fuel).map (·.1) =
      (run? (byTypeMatch ty arms) Ω fuel).map (·.1)
  /-- (4) A function type's class (D54) survives refinement. -/
  fnClass : ∀ (Ω : MState) (α : Refinement) (cs : List Value) (t : Term) (Pα : Value) (fuel : Nat),
    Respects α Ω fuel →
    (run? (α.onValue fuel (.tPi cs t)) Ω fuel).map (·.1) = some Pα →
    ∀ Ωα, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
    ∀ k, (run? (fnClass fuel (.tPi cs t)) Ω fuel).map (·.1) = some k →
      (run? (fnClass fuel Pα) Ωα fuel).map (·.1) = some k
  /-- (4) So does [Close]'s row, read from the declared codomain, for a function. A stuck block's
  function is excluded: its codomain is an embedded value (the match's type), and its row is
  value-dependent by design, like `Eq`. An unknown match type refined to `Unit` turns the row
  from data to `Unit` (η at `Unit`, D59), checked against the real `declKind` by
  `probe_blockRow_generic`/`probe_blockRow_instance` in `StabilitySig.lean`. The re-normalisation
  of the closed-off block at the refined type reads the refined row, which is `RunsCorrespond`'s
  closing off (C). The other flip, data to `&`, would be unsound (Figure 16's row); it cannot
  happen because `&` is never an argument, so no unknown type becomes a borrow type (D48 (2),
  tests `UseBlkRef` and `UseBlkBox` in `Examples/BorrowTypes.lean`). -/
  closeRow : ∀ (Ω : MState) (α : Refinement) (cs : List Value) (t : Term) (Pα : Value) (fuel : Nat),
    (∀ hs ds B, t ≠ .pi hs ds (.val B)) → Respects α Ω fuel →
    (run? (α.onValue fuel (.tPi cs t)) Ω fuel).map (·.1) = some Pα →
    ∀ Ωα, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
    ∀ k, (run? (declKind fuel (.tPi cs t)) Ω fuel).map (·.1) = some k →
      (run? (declKind fuel Pα) Ωα fuel).map (·.1) = some k
  /-- (2) A stuck block closed off at both states captures the same places in the same modes:
  the block (its anonymous function and arguments) at `Ωα` is the refinement of the one at `Ω`.
  Since D76 a block is formed only by `closeBlock`, which runs its arms itself; the arms are
  computations that read the state they run in, so the same arms are run at both states. -/
  captures : ∀ (Ω : MState) (α : Refinement) (mt mtα : Term) (arms : List BlockArm) (B : Value)
      (fuel : Nat), Respects α Ω fuel →
    (run? (α.onTerm fuel mt) Ω fuel).map (·.1) = some mtα →
    ∀ Ωα b Bα, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
      (run? (α.onValue fuel B) Ω fuel).map (·.1) = some Bα →
      (run? (closeBlock fuel mt arms (some B)) Ω fuel).map (·.1) = some b →
      ∀ bα, (run? (closeBlock fuel mtα arms (some Bα)) Ωα fuel).map (·.1) = some bα →
        (run? (α.onValue fuel b.1) Ω fuel).map (·.1) = some bα.1
  /-- (5) An observed place is compared at the refined type. -/
  observedType : ∀ (Ω : MState) (α : Refinement) (p : Place) (fuel : Nat), Respects α Ω fuel →
    ∀ Ωα A, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
      (run? (placeType fuel p) Ω fuel).map (·.1) = some A →
      ∀ Aα, (run? (placeType fuel p) Ωα fuel).map (·.1) = some Aα →
        ∃ Aα' Ω₁, run? (α.onValue fuel A) Ω fuel = some (Aα', Ω₁) ∧
          (run? (conv fuel Aα' Aα) Ωα fuel).map (·.1) = some true
  /-- (6) The footprint at the refined state is contained in the one before: a refinement only
  removes owners (a hole's fill that loses the hole). -/
  footprint : ∀ (Ω : MState) (α : Refinement) (ts tsα : List Term) (fuel : Nat), Respects α Ω fuel →
    ∀ Ωα, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
      (run? (ts.mapM (α.onTerm fuel)) Ω fuel).map (·.1) = some tsα →
      ∀ π ∈ footprint Ωα.env tsα, π ∈ footprint Ω.env ts

/-- **D55 preservation for embedded values**: an embedded value's declared reading
(`valueDecl`) survives refinement. The erasure pre-pass (`declOf` reads `.val v` by `valueDecl`)
and a function type's class (its captured values' readings scope its codomain) rest on it.

It is not provable from the checker's code alone. Its two cases are statements about evaluation:
- a sealed program is re-run by the refinement (`nfSealed`), and the reading of its normal form
  must be the reading of the program (`declOf`): evaluation preserves declared readings, subject
  reduction for the declared-type reader. It is false at a state whose globals were not checked
  (a function declared into `Nat` whose body returns a type), so it is an invariant of checked
  programs, an induction over the evaluator;
- an unknown `σ` refined to `r` reads `r`'s own reading where it read `σ`'s type's. `Respects`
  gives only that `r`'s type converts with `σ`'s, and conversion of Π-types compares generic
  calls, not syntax. So this needs conversion to respect declared readings, which reduces to the
  first case (a type term's reading is its value's reading).
So both are typing facts (M in `notes/stability.md` §5), not consequences of syntax and the
signature. -/
def ValueDeclCommutes : Prop :=
  ∀ (Ω : MState) (α : Refinement) (v vα : Value) (fuel : Nat) (d : DeclInfo) (Ω₁ Ωα : MState),
    Respects α Ω fuel →
    run? (α.onState fuel) Ω fuel = some ((), Ωα) →
    (run? (α.onValue fuel v) Ω fuel).map (·.1) = some vα →
    run? (valueDecl fuel v) Ω fuel = some (d, Ω₁) →
    (run? (valueDecl fuel vα) Ωα fuel).map (·.1) = some d

/-- **The runs stay related** (symbolic naturality). Running `tα` at `Ωα` does not fail where
running `t` at `Ω` succeeded, and when it finishes it agrees up to resolution with the generic
run's result and final state refined by `α`. A sealed program in the generic result is
re-normalised by the refinement, which is how a call the generic run closed off meets the
instance's run of it. -/
def RunsCorrespond : Prop :=
  ∀ (Ω : MState) (α : Refinement) (t : Term) (fuel : Nat), Respects α Ω fuel →
  ∀ v T Ω', run? (eval fuel true t) Ω fuel = some ((v, T), Ω') →
  ∀ Ωα tα, run? (α.onState fuel) Ω fuel = some ((), Ωα) →
    (run? (α.onTerm fuel t) Ω fuel).map (·.1) = some tα →
    ¬ Fails (eval fuel true tα) Ωα fuel ∧
    ∀ v'' T'' Ω''', run? (eval fuel true tα) Ωα fuel = some ((v'', T''), Ω''') →
      ∃ vα Ω'α, run? (do let w ← α.onValue fuel v; α.onState fuel; pure w) Ω' fuel = some (vα, Ω'α) ∧
        AgreeUpToρ vα Ω'α v'' Ω''' Ω.nextAbs fuel

/-- **Conjecture 2 (stability), against the checker**: the decisions commute with refinement,
and the runs stay related, so at every subterm both runs reach they decide alike. -/
def Conjecture2 : Prop := DecisionsCommute ∧ RunsCorrespond

-- The conjecture's proof, with the fields proved so far, is `stability` in `StabilitySig.lean`.

/-- Site 11, by construction: whether a match is on a proof reads the arms' constructors (the
hints) and the scrutinee's declaration, never the arms' bodies, so refining the bodies cannot
change it. -/
theorem byTypeMatch_arms (ty : String) (arms : List (Hint × Term)) (g : Term → Term) :
    byTypeMatch ty (arms.map fun a => (a.1, g a.2)) = byTypeMatch ty arms := by
  simp [byTypeMatch]

end Ochr.Stability
