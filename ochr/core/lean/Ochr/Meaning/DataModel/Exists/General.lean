import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup
import Ochr.Meaning.DataModel.Exists.Step2
import Ochr.Meaning.DataModel.Exists.PropMono

/-!
# The general proof's riskiest statements (stated, `sorry`; outside the default build)

Written by `exists2` for its successor (2026-11-21), after the two instances (`PreludeModel`,
`Step2`) and the small-reading half of piece 3 (`Piece3`). Each statement carries what it rests on
and how it was attacked. Read `HANDOFF.md` first.

* `runT_frameLocal`: FRAME LOCALITY, the core lemma of piece 3.
* `GlobalsTyped`, `globals_typed`: finding 2's obligation (a global a field type calls returns a
  member of its codomain sort, `Prop` or `Type₀`, or does not run).
* `knot_exists`: moved to the default build, proved (`Knot.knot_exists`).
* `truth_exists`: piece 5 (truth first); FALSE as written (`TruthCE`). `PropLe`, `mono_prop`: proved,
  `PropMono.lean`.
-/

namespace Ochr.Meaning.DataModel.Exists.General

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists

/-! ## Frame locality -/

/-- `s'` is `s` with the values of the bottom frame's bindings at the positions `X` replaced, each
binding there holding, in both, a whole member of its stored type (at every future): the canonical
frame a record key rebuilds and the actual frame differ exactly so (`Piece3.index_fields_eq`: they
agree at every index field). -/
def DiffAt (dm : DataModel) (X : Nat → Prop) (s s' : SState) : Prop :=
  s'.shape = s.shape ∧ s'.nextLoan = s.nextLoan ∧ s'.env.length = s.env.length ∧
    (∀ f, f ≠ 0 → s'.env[f]? = s.env[f]?) ∧
    ∃ fr fr' : SFrame, s.env[0]? = some fr ∧ s'.env[0]? = some fr' ∧ fr'.temps = fr.temps ∧
      fr'.binds.length = fr.binds.length ∧
      ∀ p (b b' : SBinding), fr.binds[p]? = some b → fr'.binds[p]? = some b' →
        b'.ty = b.ty ∧ b'.decl = b.decl ∧
        (b'.val = b.val ∨ (X p ∧ ∀ ψ, (b.val ψ).whole ∧ (b'.val ψ).whole ∧
          b.val ψ ∈ₛ[dm.read] b.ty.m ∧ b'.val ψ ∈ₛ[dm.read] b.ty.m))

/-- **Frame locality, as first written: FALSE** (exists3, 2026-11-21; docs/34 §18.5). Kept for the
record; the restatement is `FrameLocal.runT_qset` (an equation over the transform `qset`).
Attacked: (1) `DiffAt` does not compare `lent`, `heldTy`, `heldMem`, and a live label's recorded member
is what a place reading that label reads (kernel-checked: `FrameLocalCE.frameLocal_false`, `X` empty);
(2) a value at `X` may read the future, and `Id`'s observation reads every position after ending every
borrow, so two sides that end a borrow differently see an `X` binding differently (argued); (3) the
decisions (`joinMoves`, `blockCaps`, `invalidated`, `rePointed`) may name a place at `X`, and a drop
at a field of an `X` binding is defined at one value and not the other (argued). The restatement asks
constant values at `X` (the canonical frame's are), compares every record, and assumes `DecLocal`.

Earlier attack (exists2): the whole-state scans `movedPlaces`, `lentOk`/`StateOk`, `SM.guarded`,
`JoinDropOk`, `typedFuture`, `Id`'s observation read no value at `X` that the term does not reach;
that reading missed counts 1 to 3. -/
theorem runT_frameLocal (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (t : Term)
    (X : Nat → Prop) (s s' : SState) (hd : DiffAt K.dm X s s') (hone : s.env.length = 1)
    (hX : ∀ v ∈ t.freeVars, ∀ p, s.varPos v = some (.bind 0 p) → ¬ X p)
    {r : Res} {s₁ : SState} (hr : runT K ρ φ tl h t s = some (r, s₁)) :
    ∃ s₁', runT K ρ φ tl h t s' = some (r, s₁') ∧ DiffAt K.dm X s₁ s₁' := by
  sorry

/-! ## Finding 2: the globals a field type calls -/

/-- **Finding 2's obligation** (BELIEVED TRUE; asked at every argument, which costs nothing for a
closure: `callOf` decodes each argument at its domain's code, so at a non-member it does not run).
Only at globals whose stored codomain is `Prop` or `Type₀`: first stated at every global it was FALSE
(a `def f (n : Nat) : Nat` returns a number; `def G (b : Bool) : Type₁` returns `Type`), and the
checker's field types call only sort-valued globals (`Check.firstOrderTerm`) of codomain `Prop` or
`Type₀` (`Probes.DMXBoundary`). It also needs the meaning recorded for `n` to be the first global of
that name's, which `ProgState.step` keeps (names are distinct). From the strict run: a function's
meaning is its `.fix` run, whose closure formation tests that the closure is a member of the function
type it builds (`SM.strictS`, `Run.lean`'s `.fix`); a member applied at members of its domains returns
a member of its codomain (`app_mem'`); and the stored type the call reads (`globalTyS` of the checker's
stored `tPi`) is that function type's code (`Consistency.fix_split`'s first claim, open, the lead's).
A meaning whose run failed is `err`, at which no call runs. -/
theorem globals_typed (dm : DataModel) (D : MState → Decisions) (fuel : Nat) (items : List Item) :
    GlobalsTyped dm (progMeaning dm D (fun _ => .err) {} fuel items) := by
  sorry

/-! ## Pieces 3 and 4: a data-sorted declaration's knot -/

/- `knot_exists` is PROVED (exists6, 2026-11-22) in the default build: `Knot.knot_exists`
(`Knot/Exists.lean`, standard axioms), assuming six named facts (`GrammarCoreOk`, `GrammarHintOk`, `hpar`,
`ParamTyLocal`, `DecLocal`, label-free globals). The statement that stood here (exists5's
restatement) asked the earlier fields to fit the knot's shapes and assumed `GlobalsTyped`; the proved
one asks them to be members of their field types (what `FieldsFaithful` hands its consumer), so
`GlobalsTyped` is not needed for it. -/

/-! ## Piece 5: `Prop`-sorted declarations, truth first -/

/- `PropLe` and `mono_prop` are PROVED (exists6) in the default build: `Exists/PropMono.lean`. The
step is direct (the same constructor and fields; a proof fits any weaker proposition leaf); its
content is the hypothesis `hcanon`, which the induction over declarations must establish, and which can
hold only under rule (A*) (`CrossSortCE.lean`). -/

/- `truth_exists` (exists6's restatement, believed true) is PROVED by exists7, in the default build:
`Knot/TruthExists.lean` (`Knot.truth_exists`), in a form parallel to `Knot.knot_exists` (rule (A*) at the
earlier declarations not assumed; monotonicity at the genuine keys; the third conclusion `(S.fty …).mean`). -/

end Ochr.Meaning.DataModel.Exists.General
