import Ochr.Meaning.DataModel.Exists.Knot.Steady

/-!
# The knot, part 7: `knot_exists` (exists6)

Pieces 3 and 4 of the existence proof for a data-sorted declaration (docs/34 §18.6), in the form the
assembly uses: a guarded knot (`KnotSpec`) whose field types are the reference run's readings of the
declared field types in the frame the checker types a field in (`teleFrame`), at the knot's own
records. Restated from `General.knot_exists` (exists5's restatement, outside the build, `sorry`):
* the grammar is the one checker fact `GrammarOk` (decidable, `Grammar.lean`), not `Spine` directly;
* the earlier fields are asked to be members of their field types at the knot's model (what
  `FieldsFaithful` hands its consumer), not to fit the knot's shapes; with that, `GlobalsTyped` and
  the lookup hypothesis `hfind` are not needed (they served only to turn fitting into membership).
-/

namespace Ochr.Meaning.DataModel.Exists.Knot

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- **A data-sorted declaration's canonical knot exists.** Assumes five named facts, of three kinds:
* about the checker, NOT YET ENFORCED by it: `hgram` (`GrammarOk`: the first-order grammar with (A),
  (B), (B2); rule (A*) is not needed here and is not part of it);
* an obligation on the checker's decisions, for the machine lane: `hD` (`DecLocal`, frame locality's);
* for the assembly to discharge: `hpar` (the earlier declarations' records are parametric in their
  nestable parameters; canonical records are, e.g. `CrossSortCE.hpar_E`), `hpty` (the earlier
  parameter types are local, `ParamTyLocal`), `hK` (the globals carry no label). The witness is `knotK`; guardedness is `ftyK_agree`, the agreement with the run is
`knotK_agree` along the spine and `steadyAt_knotK` at the steady nodes. -/
theorem knot_exists (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hd : d ∈ K.Γ) (hs : d.sort ≠ 0)
    (hgram : GrammarOk K.Γ d)
    (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
    (hpty : ParamTyLocal K.dm K.Γ) (hD : FrameLocal.DecLocal K.D)
    (hK : ∀ g, (K.C.global g).2.label = none) :
    ∃ S : KnotSpec, S.d = d ∧ (∀ j, S.N j = d.nestable.getD j false) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), e[j] ∈ₛ[K.dm.read] (setRec K.dm d (recK S)).fieldTy d ps c j (e.take j)) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d (recK S) } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d (recK S)) K.D d ps c e) = some (r, s') →
          r.1.asTy = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean := by
  have hspine : ∀ c i FT, fieldTerm d c i = some FT → Spine K.Γ d c FT :=
    fun c i FT h => spineB_sound (hgram c i FT h)
  exact ⟨knotK K ρ d hs hd hspine hpar hpty, rfl, fun _ => rfl,
    knotK_agree K ρ d hs hd hspine hpar hpty (steadyAt_knotK K ρ d hs hd hspine hpar hpty hD hK)⟩

end Ochr.Meaning.DataModel.Exists.Knot
