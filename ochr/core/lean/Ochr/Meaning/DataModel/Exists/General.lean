import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Exists.Knot.Grammar
import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup
import Ochr.Meaning.DataModel.Exists.Step2

/-!
# The general proof's riskiest statements (stated, `sorry`; outside the default build)

Written by `exists2` for its successor (2026-11-21), after the two instances (`PreludeModel`,
`Step2`) and the small-reading half of piece 3 (`Piece3`). Each statement carries what it rests on
and how it was attacked. Read `HANDOFF.md` first.

* `runT_frameLocal`: FRAME LOCALITY, the core lemma of piece 3.
* `GlobalsTyped`, `globals_typed`: finding 2's obligation (a global a field type calls returns a
  member of its codomain sort, `Prop` or `Type₀`, or does not run).
* `knot_exists`: pieces 3 and 4 for a data-sorted declaration, in the form the assembly uses (a
  guarded knot whose field types are the run's).
* `PropLe`, `mono_prop`, `truth_exists`: piece 5 (truth first, with the monotonicity induction).
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

/-- **A data-sorted declaration's canonical knot** (restated by exists5, 2026-11-22; BELIEVED TRUE
under the two checker rules the lead adopted, subject to measurement, docs/34 §18.6).

As first written it was FALSE (`KnotCE.knotOld_false`, kernel-checked): it had no hypothesis that
`d` is accepted, and `hpar` compares value parameters by equality, while a value argument may carry
the knot's own record (`Pt(D2, x)` with `x : D2`). The restatement takes `d`'s field types in the
first-order grammar with Lean's two rules (`Knot.Spine`: (B) the non-spine nodes, equations, calls and
value arguments, read nothing that varies between the knot's comparisons; (A) a varying type argument
stands at a `Type` parameter and is data-sorted; (B2) a value argument's parameter type does not
mention a varying argument), the parameter types local (`Knot.ParamTyLocal`), the decisions local
(`DecLocal`, frame locality's hypothesis), the globals label-free, and `GlobalsTyped`: frame
locality swaps only bindings holding members of their types (`Good`), and an earlier field typed by a
call's result is a member of it only when that result is no junk code (`LeafOk`: a call returns a code
of level 0 or 1, never a `Prop`-sorted declaration's data code over its own carrier).

How: the interpreter reads the field type along its spine (`D(ā)` as `D`'s record at the arguments,
`d`'s own through the knot's record function, a parameter as itself) and the non-spine nodes as their
runs under `K.dm` at a CANONICAL frame rebuilt from the key (non-varying index fields rebuilt as the
members of their canonical types with the key's small readings; everything that varies, and the
fields that are no index, a fixed dummy). Guardedness by induction on the spine (`hpar`, `recK`'s own
parametricity, `SemAgree`); the non-spine nodes are record-free by construction. Agreement with the
actual run by induction on the term: along the spine `RunLemmas.runT_tind`/`runT_teleFrame_param`;
at a non-spine node `Knot.runT_stateOf_swap` (the actual frame and the canonical one differ only at
bindings it does not read; rebuilt index fields equal the actual ones, `Piece3.memTy_small_inj`) and a
model congruence (a term avoiding `d` runs the same under `K.dm` and under the knot's model). The
obstacle that `teleFrame` typed the field being typed by its own type is repaired (docs/31 D160: the
fields not yet bound are typed `err`, as the checker's `fieldTele` binds them). -/
theorem knot_exists (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hd : d ∈ K.Γ) (hs : d.sort ≠ 0)
    (hfind : K.Γ.find? (·.name == d.name) = some d)
    (hspine : ∀ c i FT, fieldTerm d c i = some FT → Knot.Spine K.Γ d c FT)
    (hpar : ∀ M ∈ K.Γ, M ≠ d → ∀ n, RAgree (fun j => M.nestable.getD j false) n (K.dm.recOf M) (K.dm.recOf M))
    (hpty : Knot.ParamTyLocal K.dm K.Γ) (hD : FrameLocal.DecLocal K.D)
    (hK : ∀ g, (K.C.global g).2.label = none)
    (hglob : ∀ P : ProgState, P.baseC = K.C → GlobalsTyped K.dm P) :
    ∃ S : KnotSpec, S.d = d ∧ (∀ j, S.N j = d.nestable.getD j false) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), FitsOneM uSig (uShape d (recK S ps) c j ((e.take j).map Sem.small)) e[j]) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d (recK S) } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d (recK S)) K.D d ps c e) = some (r, s') →
          r.1.asTy = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean := by
  sorry

/-! ## Piece 5: `Prop`-sorted declarations, truth first -/

/-- Parameter lists that differ only at nestable `Prop` parameters, each weakened. -/
def PropLe (d : IndDecl) (ps ps' : List Sem) : Prop :=
  ps'.length = ps.length ∧ ∀ j v v', ps[j]? = some v → ps'[j]? = some v' →
    v' = v ∨ (d.nestable.getD j false = true ∧
      ∃ P P' : Prop, v = .ty (TyM.prop P) ∧ v' = .ty (TyM.prop P') ∧ (P → P'))

/-- **Membership is monotone in the nestable `Prop` parameters** (BELIEVED TRUE for the canonical
records, by induction over the declarations; FALSE for an arbitrary faithful model, which may put
anything where the run of a field type is undefined, so it is stated of a model whose records are the
canonical ones: `hcanon`, to be replaced by the construction's own predicate once `knot_exists` and
`truth_exists` define it). Why it holds for the canonical records: a nestable `Prop` parameter occurs in
a field type only whole (a leaf `prop P`, fitted by `•` exactly when `P`, monotone) or at a nestable
`Prop` parameter of an earlier declaration (by induction); a field type that does not mention it is the
run's result at a frame that differs only at the parameter's binding (`runT_frameLocal`), so the same.
What the truth-first construction needs it for: the one-step operator of a `Prop`-sorted declaration
nested at a `Prop` parameter of an earlier one (`Q := MkQ(h : And(Q, True))`) is monotone, so its
least predicate is a fixed point. -/
theorem mono_prop (dm : DataModel) (d : IndDecl) (ps ps' : List Sem)
    (hcanon : ∀ c i es, (uShape d (dm.recOf d ps') c i es = uShape d (dm.recOf d ps) c i es) ∨
      ∃ P P' : Prop, (P → P') ∧ uShape d (dm.recOf d ps) c i es = .leaf (PLift P) (.prop P) ∧
        uShape d (dm.recOf d ps') c i es = .leaf (PLift P') (.prop P'))
    (hle : PropLe d ps ps') :
    (∃ v, dm.Mem d (dm.recOf d ps) v) → ∃ v, dm.Mem d (dm.recOf d ps') v := by
  sorry

/-- **A `Prop`-sorted declaration, truth first** (BELIEVED TRUE). The least predicate closed under the
constructors, with the declaration's own occurrences (and its occurrences inside earlier declarations
at nestable `Prop` parameters) read as the predicate; records whose such occurrences are leaves holding
it (no self-reference, no knot); the record means the predicate; and its field types are the run's
(under the model whose records for `d` are these). `Step2.ev_tyR`, `Step2.q_tyR` are two instances,
each computed outright; the general fixed point needs `mono_prop`. First stated without the last
clause it was vacuous (any record and its own inhabitation meet it). -/
theorem truth_exists (K : RunCtx) (ρ : Assignment) (d : IndDecl) (hd : d ∈ K.Γ) (hs : d.sort = 0)
    (hglob : ∀ P : ProgState, P.baseC = K.C → GlobalsTyped K.dm P) :
    ∃ (T : List Sem → Prop) (R : List Sem → Rec),
      (∀ ps, uTyR d (R ps) = TyM.prop (T ps)) ∧
      ∀ (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (r : Res) (s' : SState),
        ps.length = d.params.length → (∀ j (hj : j < ps.length), ps[j] ∈ₛ[K.dm.read] K.dm.paramTy d j (ps.take j)) →
        (∀ j (hj : j < e.length), FitsOneM uSig (uShape d (R ps) c j ((e.take j).map Sem.small)) e[j]) →
        e.length = i → fieldTerm d c i = some FT →
        run { K with dm := setRec K.dm d R } ρ noFuture (.plain (TyM.univ 1)) FT
          (teleFrame (setRec K.dm d R) K.D d ps c e) = some (r, s') →
          r.1.asTy = shapeTyP (uShape d (R ps) c i (e.map Sem.small)) := by
  sorry

end Ochr.Meaning.DataModel.Exists.General
