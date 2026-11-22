import Ochr.Meaning.DataModel.Exists.Knot.TruthAgree

/-!
# Truth first: a `Prop`-sorted declaration's records exist (exists7)

Pieces 3 and 4 for a `Prop`-sorted declaration (`General.truth_exists` as restated by exists6, proved
here in a form parallel to `knot_exists`): a spec whose records' field types are the reference run's
readings of the declared field types, at the records themselves; `d`'s code at those records is the
truth predicate's proposition; and the records are monotone in `d`'s nestable `Prop` parameters, which
the next declarations' `hmono` reads.

The construction (`Knot/TruthInterp.lean` … `Knot/TruthAgree.lean`): read `d`'s own occurrences as a
truth predicate `T` (`ftyP`); its records `truthRec T` read no record of `d`, so no knot is needed;
`T` is the least fixed point, among predicates monotone in their arguments, of "`d` is inhabited at
`truthRec T`" (`truthP`, `Truth.lfpM_fixed`); monotone because every shape a weaker `T` or a weaker
parameter reaches is a weaker proposition leaf or a `Prop`-sorted sub-record inhabited when the first is
(`ftyP_le`, from `PSpine` and the earlier records' `hmono`). Then the run's code of `d(ā)` is
`TyM.prop (T ā)` (`uTyR_truthRec`) and the run agrees with the interpreter (`truth_agree`), the steady
nodes by the knot's argument (`steadyAt_spec`).

Against exists6's restatement: rule (A*) at the earlier `Prop`-sorted declarations (`hstar`) is not
assumed (for `d` itself `PSpine` carries what (A*) says, and the earlier ones enter only through
`hmono`, which the assembly discharges with this theorem's second conclusion); the monotonicity is
asked and returned at the genuine keys only (`es.length = i`, all that fitting reads); and the third
conclusion reads `(S.fty …).mean`, as `knot_exists`'s does.
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- **A `Prop`-sorted declaration's records exist, truth first.** Assumes: the grammar fact
`PGrammarOk` (about the checker); `DecLocal` (an obligation on the decisions); the earlier
`Prop`-sorted records monotone (`hmono`), `ParamTyLocal` and label-free globals (for the assembly). -/
theorem truth_exists (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hd : d ∈ K.Γ) (hs : d.sort = 0)
    (hgram : PGrammarOk K.Γ d)
    (hmono : ∀ M ∈ K.Γ, M ≠ d → M.sort = 0 → ∀ ps ps', PropLe M ps ps' → ∀ c i es, es.length = i →
      ShapeLe (uShape M (K.dm.recOf M ps) c i es) (uShape M (K.dm.recOf M ps') c i es))
    (hpty : ParamTyLocal K.dm K.Γ) (hD : FrameLocal.DecLocal K.D)
    (hK : ∀ g, (K.C.global g).2.label = none) :
    ∃ (S : KnotSpec) (T : List Sem → Prop), S.d = d ∧
      (∀ ps, uTyR d (recK S ps) = TyM.prop (T ps)) ∧
      (∀ ps ps', PropLe d ps ps' → ∀ c i es, es.length = i →
        ShapeLe (uShape d (recK S ps) c i es) (uShape d (recK S ps') c i es)) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read] (setRec K.dm d (recK S)).fieldTy d ps c j (e.take j)) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d (recK S) } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d (recK S)) K.D d ps c e) = some (r, s') →
          r.1.asTy = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean := by
  have G : TruthHyp K d := ⟨hs, hd, fun c i FT h => pspineB_sound (hgram c i FT h), hmono, hpty⟩
  exact ⟨truthSpec K ρ d (truthP K ρ d), truthP K ρ d, rfl, uTyR_truthRec G, fun _ _ hp => truthRec_mono G hp,
    truth_agree K ρ d G (steadyAt_spec K ρ d _ hD hK)⟩

end Ochr.Meaning.DataModel.Exists.Knot
