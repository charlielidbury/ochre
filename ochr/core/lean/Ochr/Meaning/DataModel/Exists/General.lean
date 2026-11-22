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
(`Knot/Exists.lean`, standard axioms), assuming five named facts (`GrammarOk`, `hpar`,
`ParamTyLocal`, `DecLocal`, label-free globals). The statement that stood here (exists5's
restatement) asked the earlier fields to fit the knot's shapes and assumed `GlobalsTyped`; the proved
one asks them to be members of their field types (what `FieldsFaithful` hands its consumer), so
`GlobalsTyped` is not needed for it. -/

/-! ## Piece 5: `Prop`-sorted declarations, truth first -/

/- `PropLe` and `mono_prop` are PROVED (exists6) in the default build: `Exists/PropMono.lean`. The
step is direct (the same constructor and fields; a proof fits any weaker proposition leaf); its
content is the hypothesis `hcanon`, which the induction over declarations must establish, and which can
hold only under rule (A*) (`CrossSortCE.lean`). -/

/-- **A `Prop`-sorted declaration, truth first** (RESTATED by exists6, 2026-11-22; BELIEVED TRUE).

As first written it was FALSE (`TruthCE.truthOld_false`, kernel-checked): it assumed nothing of the
earlier records, and an anti-monotone earlier record makes `Q : Prop := MkQ(h : N(Q))` inhabited exactly
when it is not. Restated: the earlier records are monotone in their nestable `Prop` parameters
(`hmono`, `ShapeLe` at every key, which `mono_prop` turns into monotone inhabitation, and which the
construction must return for `d` too, the second conclusion, so the induction over declarations goes
on); rule (A*) at every declaration (`hstar`; the lead's ruling); frame locality's two facts and local
parameter types (as for the knot); the earlier fields members of their field types (as `knot_exists`).
The grammar fact for a `Prop`-sorted `d` is `hgram` (`Knot.PGrammarOk`: `PSpine`, which is `Spine`
with (A) read for `Prop`, decidable).

Plan (HANDOFF): `T := lfpP Φ` (`Truth.lean`), `Φ T ps` = some constructor has fields fitting the shapes
of the record `R_T ps`, which is the knot's record built from an interpreter that reads `d`'s own
occurrences `d(ā)` as the proposition leaf `T ā` and everything else as `ftyK` does (no knot: `R_T`
does not read itself, so it is defined outright by the interpreter at each key). `Φ` is monotone by
`mono_prop` (`hmono`, (A*): every shape `T` reaches is a proposition leaf or a `Prop`-sorted
sub-record); then `T = Φ T` (`lfpP_fixed`) is `uTyR d (R_T ps) = TyM.prop (T ps)`; faithfulness is
`knotK_agree`'s argument with a self-occurrence's run `tyM d ā = prop (Nonempty (car d (R_T ā)))` =
`prop (T ā)` by the fixed point, and `steadyAt_knotK`'s at the steady nodes. -/
theorem truth_exists (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hd : d ∈ K.Γ) (hs : d.sort = 0)
    (hgram : Knot.PGrammarOk K.Γ d) (hstar : ∀ M ∈ K.Γ, Knot.AStarOk K.Γ M = true)
    (hmono : ∀ M ∈ K.Γ, M ≠ d → ∀ ps ps', PropLe M ps ps' → ∀ c i es,
      ShapeLe (uShape M (K.dm.recOf M ps) c i es) (uShape M (K.dm.recOf M ps') c i es))
    (hpty : Knot.ParamTyLocal K.dm K.Γ) (hD : FrameLocal.DecLocal K.D)
    (hK : ∀ g, (K.C.global g).2.label = none) :
    ∃ (T : List Sem → Prop) (R : List Sem → Rec),
      (∀ ps, uTyR d (R ps) = TyM.prop (T ps)) ∧
      (∀ ps ps', PropLe d ps ps' → ∀ c i es, ShapeLe (uShape d (R ps) c i es) (uShape d (R ps') c i es)) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read] (setRec K.dm d R).fieldTy d ps c j (e.take j)) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d R } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d R) K.D d ps c e) = some (r, s') →
          r.1.asTy = shapeTyP (uShape d (R ps) c i (e.map Sem.small)) := by
  sorry

end Ochr.Meaning.DataModel.Exists.General
