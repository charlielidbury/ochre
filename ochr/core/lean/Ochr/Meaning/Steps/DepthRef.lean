import Ochr.Meaning.Steps.ColumnQMean
import Ochr.Meaning.Steps.DataBoxRun
import Ochr.Meaning.Steps.MasterGuards

/-!
# The erased depth, tested on the reference's side (lead24, 2026-11-22; docs/31 D170)

`EvalAt` and `TailAt` hold at every erased depth (D155). Above depth 0 the checker skips two kinds of check (the
capture-move checks of [D53]; the runtime-only checks K2/K3) and so accepts more (`MasterGuards.DepthProbe`). This
file asks whether the reference's STRICT run succeeds on the programs accepted only there, and whether its result
is what the checker's value means, by kernel-checked runs, as `TailHintRegress` does for the tail hint.

**The capture-move check: `CapE`** (`def CapE (n : Nat) : Type := ((λ(m : Nat) : Nat => n); Nat)`; its twin `Cap0`,
returning `Z : Nat`, is rejected: "[D53] a closure's body moves a captured value out"). Its body, in the core:
`(fix _ (m : Nat) : Nat := #2); Nat`, `#2` being `n` under `m` and the closure's own name (`bodyCapE`, guarded against
the checker's own resolution). From the body state the reference's `.fix` clause builds for `CapE` at any argument `a`
(`sC`: `[{}, {self, n ↦ a}]`, at any binding of `self`, which nothing reads):
- the inner closure's function returns `a` at EVERY argument (`gCap_run`): its body's read of `n` moves `n` in the run
  of that call only, which starts from the forming state each time; so a second use sees `n` as the first did. The
  reference reads a closure as a function of its arguments, called on its forming state afresh: moving a capture out
  is invisible to it, at every depth;
- the closure is a member of `Π(m : Nat). Nat` (`gCap_mem`), the `.fix` run succeeds and moves `n` out of the forming
  frame (the capture by move: `run_fixCap`);
- the whole body runs to `Nat` at `Type₀` (`.ty TyM.nat` at `univ 1`, the meaning of the checker's value `Nat` at
  `.sort 1`), the discarded closure holding no borrow (`run_bodyCapE`).

**A runtime-only check (K3): `CtorE`** (`abstract inductive A := MkA(k : Nat)`, `def CtorE (n : Nat) : Type :=
(MkA(n); Nat)`; its twin `Ctor0` rejected by K3). The reference reads neither `abstract` nor the depth: `MkA(n)` runs
as `ColumnBox.runWrap`'s `MkBox(n)` does and passes its strict test (`datA_mem`, from the data model's faithfulness to
`[A]`), then the discard and `Nat` (`run_bodyCtorE`).

**Whole programs** (`column_CapE`, `column_CtorE`): at every table aligned with the checker (the decisions read are got
by kernel evaluation of the checker's procedures, `parDecCap`, `parDecCtor`, `parDecDef`), the reference's `.fix`
clause forms each function's closure from the empty state, a MEMBER of `Π(n : Nat). Type₀` (`fix_typeFn`): the strict
run of the accepted program succeeds. Assumes nothing (`CtorE`: the context's faithfulness to `[A]`, part of `Pre`).
So the master's statements may stand at every erased depth (docs/31 D155's (b)): the reference's strict run succeeds
on one program of each kind the checker accepts only above depth 0. `NestE`, `MatchE` and `ReadE` are not run here;
they rest on the same two facts (a closure's body is run afresh from the forming state at every call; the reference
reads no `abstract`, `unsized` or depth).
-/

namespace Ochr.Meaning.Steps.Form.DepthRef

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Strict.Witness
open Ochr.Meaning.Steps.Form.ColumnI (psI outI selfTy selfSem)

/-! ## A read of a number, at any position -/

/-- A state shaping nothing lends nothing. -/
theorem liveLabels_noShape {s : SState} (h : ∀ p, s.shape p = none) : s.liveLabels = [] := by
  have e : s.shape = fun _ => none := funext h
  unfold SState.liveLabels
  rw [e]
  have : ∀ (L : List Pos), L.filterMap (fun _ => (none : Option Nat)) = [] := fun L => by
    induction L with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  rw [this]; exact List.mergeSort_nil

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The read of a variable holding a number, which moves it**, from a state shaping nothing (so no label is live,
the access ends nothing and the typed future is the run's), at a table reading the place unerased and not copy. -/
theorem runRead_num {s : SState} {j : Nat} {pos : Pos} {a : Nat} (hsh : ∀ p, s.shape p = none)
    (hpos : s.varPos j = some pos) (hval : s.valAt pos φ = .el0 Nat a) (hty : (s.tyAt pos).m = TyM.nat)
    (hfl : K.D.flags (scopeOf s) (.place (.var j)) = (false, false))
    (hcp : K.D.copy (K.D.placeDecl (scopeOf s) (.var j)) = false) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place (.var j)) s =
      some ((.el0 Nat a, { s.tyAt pos with label := none }), s.setAt pos fun _ => .moved) := by
  have hlive := liveLabels_noShape hsh
  have hacc : ∀ hit, s.access pos hit = s := fun hit => access_noSites (fun l hl => by rw [hlive] at hl; cases hl)
  have htf : s.typedFuture φ = φ := by funext l; unfold SState.typedFuture; rw [hlive]; simp
  have hres : resolve s (.var j) = some (pos, []) := by unfold resolve; simp [Place.steps, hpos]
  have hco : contentOf K φ (.var j) s = some ((.el0 Nat a, s.tyAt pos, pos, []), s) := by
    unfold contentOf; rw [hres]; dsimp only
    rw [hacc, htf, hval]; rfl
  have hset : setContent K φ pos [] .moved s = some (⟨⟩, s.setAt pos fun _ => .moved) := by
    unfold setContent
    rw [if_pos]
    · congr 2
    · intro ψ _; rw [Sem.updAt.eq_def]; rfl
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.place (.var j)))
    (SM.guarded (ContentOk K φ (.var j)) (readPlace K φ (.var j) (K.D.copy (K.D.placeDecl (scopeOf s) (.var j))))) s = _
  rw [hfl, hcp]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold ContentOk; rw [hres]; exact accessOk_noSites (fun l hl => by rw [hlive] at hl; cases hl))]
  unfold readPlace
  rw [hco]
  have hwhole : (Sem.el0 Nat a).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (s.tyAt pos).m (.el0 Nat a) := by rw [hty]; exact .inl ⟨a, rfl⟩
  simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_nil,
    if_true, hsh, hset]

end

/-! ## `CapE`: a closure whose body moves its capture out, in an erased position -/

/-- The closure in `CapE`'s body: `λ(m : Nat) : Nat => n`, `n` being `#2` under `m` and the closure's own name. -/
def fixCap : Term := .fix ⟨"_"⟩ [⟨"m"⟩] [.nat] .nat none (.place (.var 2))

/-- `CapE`'s body in the core: the closure, discarded, then `Nat`. -/
def bodyCapE : Term := .seq fixCap .nat

/-- The binding of `CapE`'s parameter at the number `a`, as the `.fix` clause's `fixStep` pushes it. -/
def nBnd (a : Nat) : SBinding := { ty := .plain TyM.nat, val := fun _ => .el0 Nat a, decl := .other }

/-- **The decisions the reference's run of `CapE`'s body reads**, in the body's scope `sc` (the readings of `n`, then
`self`): the body and the closure neither statements nor proofs (the checker's `preFlags`: only a proof or a call is
erased); the parameter `m` and the codomain read `.other`; the closure's sort `1`; the capture of `n` not a copy (so
by move); and, in the closure body's scope (`m`, the closure's `self`, then `sc`), the read of `n` unerased and not a
copy. -/
structure ParDecCap (D : Decisions) (sc : List DeclInfo) : Prop where
  flBody : D.flags sc bodyCapE = (false, false)
  flFix : D.flags sc fixCap = (false, false)
  td0 : D.typeDecl sc .nat = .other
  td1 : D.typeDecl (.other :: sc) .nat = .other
  srt : D.piSort sc (.pi [⟨"m"⟩] [.nat] .nat) = 1
  cpN : D.copy (D.placeDecl sc (.var 0)) = false
  flRd : D.flags (.other :: .pi .other :: sc) (.place (.var 2)) = (false, false)
  cpRd : D.copy (D.placeDecl (.other :: .pi .other :: sc) (.var 2)) = false

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- The binders and codomain the `.fix` clause reads the closure's signature at, in the forming state `s`. -/
noncomputable def fbC (K : RunCtx) (ρ : Assignment) (φ : Future) (s : SState) : List PBind × PBind :=
  (bindsOf K ρ φ s [.nat], fixCod K ρ φ s (bindsOf K ρ φ s [.nat]) ([.nat].map Term.isRefTy) .nat, K.D.typeDecl (K.D.teleDecls (scopeOf s) [.nat]) .nat)

/-- **The closure's function** (stage 1 at rank 0: it does not recurse), formed in `s`. -/
noncomputable def gCap (K : RunCtx) (ρ : Assignment) (φ : Future) (s : SState) : List Sem → Option BodyOut :=
  fixG K ρ φ (fbC K ρ φ s) 1 s psI outI (piTyAt K.dm.read 1 psI outI) s.nextLoan none (.place (.var 2))

/-- The closure's `self` in its body: the stage-0 closure at the weakened type (`ColumnI.selfSem`), read `.pi .other`. -/
noncomputable def selfIn (R : DataRead) (φ : Future) : SBinding :=
  { ty := .plain (selfTy R), val := fun _ => selfSem R φ, decl := .pi .other }

/-- The closure body's state at the argument `m`: the forming state under a fresh bottom frame, with the closure's
`self` (the stage-0 closure at the weakened type, read `.pi .other`) and `m` pushed on its top frame. -/
noncomputable def sIn (R : DataRead) (φ : Future) (s : SState) (m : Nat) : SState :=
  (s.under.pushBind (selfIn R φ)).pushBind (nBnd m)

/-- What the runs read of the forming state: nothing shaped, and two bindings on one frame above an empty one,
`self` (any binding: nothing reads it) and `n ↦ a`. The reference's body state for `CapE` at the argument `a` is one
(the `.fix` clause forms `CapE` in the empty state: `[{}, {self, n}]`, D126). -/
structure RefCap (b : SBinding) (a : Nat) (s : SState) : Prop where
  shape : ∀ p, s.shape p = none
  env : s.env = [{}, { binds := [b, nBnd a] }]

variable {b : SBinding} {a : Nat} {s : SState}

theorem RefCap.scope (h : RefCap b a s) : scopeOf s = [.other, b.decl] := by
  unfold scopeOf; rw [h.env]; rfl

theorem RefCap.varPos0 (h : RefCap b a s) : s.varPos 0 = some (.bind 1 1) := by
  unfold SState.varPos SState.topIdx; rw [h.env]; rfl

theorem RefCap.in_env (h : RefCap b a s) (R : DataRead) (m : Nat) :
    (sIn R φ s m).env = [{}, {}, { binds := [b, nBnd a, selfIn R φ, nBnd m] }] := by
  unfold sIn SState.pushBind SState.under SState.topIdx; simp [h.env]

theorem RefCap.in_shape (h : RefCap b a s) (R : DataRead) (m : Nat) (p : Pos) : (sIn R φ s m).shape p = none := by
  show p.down?.bind s.shape = none
  cases p.down? <;> simp [h.shape]

theorem RefCap.in_scope (h : RefCap b a s) (R : DataRead) (m : Nat) :
    scopeOf (sIn R φ s m) = .other :: .pi .other :: scopeOf s := by
  unfold scopeOf; rw [h.in_env R m, h.env]; rfl

theorem RefCap.in_varPos2 (h : RefCap b a s) (R : DataRead) (m : Nat) : (sIn R φ s m).varPos 2 = some (.bind 2 1) := by
  unfold SState.varPos SState.topIdx; rw [h.in_env R m]; rfl

theorem paramDecls_cap (hd : ParDecCap K.D (scopeOf s)) :
    K.D.paramDecls (scopeOf s) [.nat] = [.other] := by
  simp [Decisions.paramDecls, Decisions.teleDecls, hd.td0]

theorem fbC_1 (hd : ParDecCap K.D (scopeOf s)) :
    (fbC K ρ φ s).1 = [(fun _ => .plain TyM.nat, .other)] :=
  ColumnI.bindsOf_nat K ρ φ s (paramDecls_cap hd)

theorem fbC_22 (hd : ParDecCap K.D (scopeOf s)) : (fbC K ρ φ s).2.2 = .other := by
  show K.D.typeDecl (K.D.teleDecls (scopeOf s) [.nat]) .nat = .other
  simp [Decisions.teleDecls, hd.td0, hd.td1]

/-- **The closure returns `n`'s value `a` at every argument** (its body, in the body state at `m`, reads `n`, which
moves it IN THAT RUN: the run starts from the forming state at every call, so no call sees another's move). -/
theorem gCap_run (h : RefCap b a s) (hd : ParDecCap K.D (scopeOf s)) (m : Nat) :
    gCap K ρ φ s [.el0 Nat m] = some ⟨.el0 Nat a, [], none⟩ := by
  have h1 := fbC_1 (ρ := ρ) (φ := φ) (s := s) hd
  have h2 := fbC_22 (ρ := ρ) (φ := φ) (s := s) hd
  have hst : ([Sem.el0 Nat m].zip psI).foldl (fixStep (fbC K ρ φ s))
      (s.under.pushBind { ty := .plain (selfTy K.dm.read), val := fun _ => selfSem K.dm.read φ, decl := .pi (fbC K ρ φ s).2.2 },
        [], []) = (sIn K.dm.read φ s m, [.el0 Nat m], []) := by
    simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep, h1, h2,
      Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append]
    rfl
  have hsc : scopeOf (sIn K.dm.read φ s m) = .other :: .pi .other :: scopeOf s := h.in_scope K.dm.read m
  have hrd := runRead_num (K := K) (ρ := ρ) (φ := φ) (s := sIn K.dm.read φ s m) (j := 2) (pos := .bind 2 1) (a := a)
    (h.in_shape K.dm.read m) (h.in_varPos2 K.dm.read m) (by unfold SState.valAt; rw [h.in_env]; rfl)
    (by unfold SState.tyAt; rw [h.in_env]; rfl) (by rw [hsc]; exact hd.flRd) (by rw [hsc]; exact hd.cpRd)
  have hl : ((sIn K.dm.read φ s m).setAt (.bind 2 1) fun _ => .moved).liveLabels = [] := by
    rw [Strict.liveLabels_setAt]; exact liveLabels_noShape (h.in_shape K.dm.read m)
  show fixBodyAt K ρ φ (fbC K ρ φ s) s psI outI (selfTy K.dm.read) s.nextLoan (.place (.var 2)) (selfSem K.dm.read φ)
    [.el0 Nat m] = _
  unfold fixBodyAt
  dsimp only
  rw [hst]
  dsimp only
  rw [h2, fnErasedD_other, SM.bodyRun_false]     -- main's D142: the closure returns data
  rw [hrd]
  dsimp only
  rw [hl]
  simp [ColumnI.endsOk_nil]

/-- The closure's function is total on `Nat`, returning a member of `Nat`. -/
theorem gCap_tot (h : RefCap b a s) (hd : ParDecCap K.D (scopeOf s)) :
    ∀ args, DomMembers K.dm.read psI args →
      ∃ o, gCap K ρ φ s args = some o ∧ OutGood K.dm.read psI outI args o ∧
        o.finals.length = (psI.filter (·.isRef)).length := by
  intro args ha
  obtain ⟨m, rfl⟩ := ColumnR.domMembers_one ha
  refine ⟨_, gCap_run h hd m, ⟨⟨a, rfl⟩, fun i d hi hd' => ?_⟩, rfl⟩
  rcases i with _ | i
  · simp [psI] at hi; subst hi; cases hd'
  · simp [psI] at hi

/-- **The closure is a member of `Π(m : Nat). Nat`**: the strict test at forming it passes. -/
theorem gCap_mem (h : RefCap b a s) (hd : ParDecCap K.D (scopeOf s)) :
    closureAt K.dm.read 1 φ psI outI (gCap K ρ φ s) ∈ₛ[K.dm.read] piTyAt K.dm.read 1 psI outI :=
  closure_mem_of_total' K.dm.read 1 φ psI outI _ ⟨Nat.le_refl 1, by omega⟩ rfl (fun _ _ => Nat.le_refl 1)
    (gCap_tot h hd)

/-- **The `.fix` run forms the closure**: the capture's access ends nothing, the closure passes its strict test, and
`n` is moved out of the forming frame (captured by move: `n`'s reading is not copy). -/
theorem run_fixCap (h : RefCap b a s) (hd : ParDecCap K.D (scopeOf s)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint fixCap s =
      some ((closureAt K.dm.read 1 φ psI outI (gCap K ρ φ s), .plain (piTyAt K.dm.read 1 psI outI)),
        s.setAt (.bind 1 1) fun _ => .moved) := by
  have hpd := paramDecls_cap hd
  have hsort : fixSort K s [⟨"m"⟩] [.nat] .nat = 1 := hd.srt
  have hty : fixTy K ρ φ s [⟨"m"⟩] [.nat] .nat = piTyAt K.dm.read 1 psI outI := by
    unfold fixTy; rw [hsort, ColumnI.runDoms_nat K ρ φ s hpd, ColumnI.codOf_nat]
  have hclo : fixClo K ρ φ s [⟨"m"⟩] [.nat] .nat none (.place (.var 2)) =
      closureAt K.dm.read 1 φ psI outI (gCap K ρ φ s) := by
    unfold fixClo
    rw [hty, hsort, ColumnI.runDoms_nat K ρ φ s hpd, ColumnI.codOf_nat]
    rfl
  have hlive := liveLabels_noShape h.shape
  have hacc : ∀ pos hit, s.access pos hit = s := fun _ _ => access_noSites (fun l hl => by rw [hlive] at hl; cases hl)
  have hcap : capOrder fixCap = [0] := rfl
  have hmv : fixMoves K fixCap s = s.setAt (.bind 1 1) fun _ => .moved := by
    unfold fixMoves; rw [hcap]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold capStep; rw [h.varPos0]; dsimp only
    rw [hacc, hd.cpN]; rfl
  have hfo : FoldOk (capStep K) (CapOk K φ) (capOrder fixCap) s := by
    rw [hcap]
    exact ⟨by unfold CapOk; rw [h.varPos0]; exact accessOk_noSites (fun l hl => by rw [hlive] at hl; cases hl), trivial⟩
  have hrun := run_fix_of_mem (K := K) (ρ := ρ) (φ := φ) tl hint ⟨"_"⟩ [⟨"m"⟩] [.nat] .nat none (.place (.var 2)) s
    hd.flFix hfo (by rw [hty, hclo]; exact gCap_mem h hd)
  show runT K ρ φ tl hint (.fix ⟨"_"⟩ [⟨"m"⟩] [.nat] .nat none (.place (.var 2))) s = _
  rw [hrun, hclo, hty, ← hmv]
  rfl

/-- **`CapE`'s body runs to `Nat` at `Type₀`**, the meaning of the checker's value `Nat` at `.sort 1`: the closure is
formed (`run_fixCap`), discarded (it holds no borrow: `DiscardOk` asks nothing), and `Nat` runs; `n` is left moved
by the capture, as the checker's capture moves it. At every tail flag and hint. -/
theorem run_bodyCapE (h : RefCap b a s) (hd : ParDecCap K.D (scopeOf s)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyCapE s =
      some ((.ty TyM.nat, .plain (TyM.univ 1)), s.setAt (.bind 1 1) fun _ => .moved) := by
  rw [show bodyCapE = .seq fixCap .nat from rfl, runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.seq fixCap .nat)) _ s = _
  rw [show K.D.flags (scopeOf s) (.seq fixCap .nat) = (false, false) from hd.flBody]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [Bind.bind, run_fixCap h hd, SM.guardMod, DiscardOk, discardEnd, ColumnI.runT_nat]
  simp [TyS.plain]

end

/-- **The reference's body state for `CapE` is one `RefCap` reads**: the `.fix` clause forms `CapE` in the empty state
and pushes, on its fresh bottom frame, `self` and then the parameter at `a` (`fixStep` at a plain `Nat` parameter read
`.other`: `nBnd a`, as `ColumnI.start_I` computes for `I`). -/
theorem refCap_start (b : SBinding) (a : Nat) : RefCap b a (((emptyState 0).under.pushBind b).pushBind (nBnd a)) :=
  ⟨fun p => by show p.down?.bind (fun _ => none) = none; cases p.down? <;> rfl, rfl⟩

/-! ## The checker's side: the core term, and the decisions the reference reads -/

/-- The checker's own resolution of a definition of `DepthProbe` to the core: its body. -/
def coreBody (nm : String) : Option Term :=
  match DepthProbe.decls.find? (·.name == nm) with
  | some d => match (Ochr.Surface.runResolve DepthProbe.decls d 100000).1 with
    | .ok (.ok (.defn df)) => some df.body
    | _ => none
  | none => none

-- `CapE`'s body is `bodyCapE` (the checker accepts `CapE`: `MasterGuards.DepthProbe`)
#guard coreBody "CapE" == some bodyCapE

/-- `CapE`'s body scope: `n`, then `self`, read `.pi (.sort 1)` (the codomain `Type` read as a type, `typeDecl`). -/
abbrev scCap : List DeclInfo := [.other, .pi (.sort 1)]

/-- A state at erased depth 1 (where the checker checks `CapE`'s body: it returns a type, `withErasedIf`), with no
global and no declaration; the decisions below read neither (no constant, no inductive in the terms). -/
def stCapE : MState := { erasedDepth := 1 }

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther isOther_eq)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)
open Ochr.Meaning.Steps.Form.ColumnP.Aux (pdRun cpRun)

abbrev scIn : List DeclInfo := .other :: .pi .other :: scCap

theorem ok_fl_body : isOk (flagsRun bodyCapE) (scopeState stCapE scCap) 1000 = true := by decide +kernel
theorem val_fl_body : outVal (flagsRun bodyCapE) (scopeState stCapE scCap) 1000 = (false, false) := by decide +kernel
theorem ok_fl_fix : isOk (flagsRun fixCap) (scopeState stCapE scCap) 1000 = true := by decide +kernel
theorem val_fl_fix : outVal (flagsRun fixCap) (scopeState stCapE scCap) 1000 = (false, false) := by decide +kernel
theorem ok_td0 : isOk (typeDeclRun .nat) (scopeState stCapE scCap) 1000 = true := by decide +kernel
theorem val_td0 : isOther (outVal (typeDeclRun .nat) (scopeState stCapE scCap) 1000) = true := by decide +kernel
theorem ok_td1 : isOk (typeDeclRun .nat) (scopeState stCapE (.other :: scCap)) 1000 = true := by decide +kernel
theorem val_td1 : isOther (outVal (typeDeclRun .nat) (scopeState stCapE (.other :: scCap)) 1000) = true := by
  decide +kernel
theorem ok_srt : isOk (piSortRun (.pi [⟨"m"⟩] [.nat] .nat)) (scopeState stCapE scCap) 1000 = true := by decide +kernel
theorem val_srt : outVal (piSortRun (.pi [⟨"m"⟩] [.nat] .nat)) (scopeState stCapE scCap) 1000 = 1 := by decide +kernel
theorem ok_pdN : isOk (pdRun (.var 0)) (scopeState stCapE scCap) 1000 = true := by decide +kernel
theorem val_pdN : isOther (outVal (pdRun (.var 0)) (scopeState stCapE scCap) 1000) = true := by decide +kernel
theorem ok_fl_rd : isOk (flagsRun (.place (.var 2))) (scopeState stCapE scIn) 1000 = true := by decide +kernel
theorem val_fl_rd : outVal (flagsRun (.place (.var 2))) (scopeState stCapE scIn) 1000 = (false, false) := by
  decide +kernel
theorem ok_pdRd : isOk (pdRun (.var 2)) (scopeState stCapE scIn) 1000 = true := by decide +kernel
theorem val_pdRd : isOther (outVal (pdRun (.var 2)) (scopeState stCapE scIn) 1000) = true := by decide +kernel
theorem ok_cp : isOk cpRun stCapE 1000 = true := by decide +kernel
theorem val_cp : outVal cpRun stCapE 1000 = false := by decide +kernel

end Aux

/-- **`ParDecCap` at every table aligned with the checker at `stCapE`** (kernel evaluation of the checker's decision
procedures, as `ColumnQ.parDecQ`). -/
theorem parDecCap {D : Decisions} (hd : DecTab D stCapE) : ParDecCap D scCap := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hcp : D.copy .other = false := by
    rw [hd.copy 100 .other _ 1000 _ (runs_out ColumnP.Aux.cpRun _ 1000 Aux.ok_cp), Aux.val_cp]
  have hfl : ∀ sc t, isOk (ColumnC.Aux.flagsRun t) (scopeState stCapE sc) 1000 = true →
      D.flags sc t = outVal (ColumnC.Aux.flagsRun t) (scopeState stCapE sc) 1000 := fun sc t hok =>
    hd.flags 100 sc t _ 1000 _ (runs_out (ColumnC.Aux.flagsRun t) _ 1000 hok)
  have hpd : ∀ sc p, isOk (ColumnP.Aux.pdRun p) (scopeState stCapE sc) 1000 = true →
      D.placeDecl sc p = outVal (ColumnP.Aux.pdRun p) (scopeState stCapE sc) 1000 := fun sc p hok =>
    hd.placeDecl 100 sc p _ 1000 _ (runs_out (ColumnP.Aux.pdRun p) _ 1000 hok)
  have htd : ∀ sc, isOk (ColumnI.Aux.typeDeclRun .nat) (scopeState stCapE sc) 1000 = true →
      D.typeDecl sc .nat = outVal (ColumnI.Aux.typeDeclRun .nat) (scopeState stCapE sc) 1000 := fun sc hok =>
    hd.typeDecl 100 sc _ _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun _) _ 1000 hok)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfl _ _ Aux.ok_fl_body, Aux.val_fl_body]
  · rw [hfl _ _ Aux.ok_fl_fix, Aux.val_fl_fix]
  · rw [htd _ Aux.ok_td0]; exact ColumnC.Aux.isOther_eq Aux.val_td0
  · rw [htd _ Aux.ok_td1]; exact ColumnC.Aux.isOther_eq Aux.val_td1
  · rw [hd.piSort 100 _ _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 Aux.ok_srt), Aux.val_srt]
  · rw [hpd _ _ Aux.ok_pdN, ColumnC.Aux.isOther_eq Aux.val_pdN]; exact hcp
  · rw [hfl _ _ Aux.ok_fl_rd, Aux.val_fl_rd]
  · rw [hpd _ _ Aux.ok_pdRd, ColumnC.Aux.isOther_eq Aux.val_pdRd]; exact hcp

/-! ## `CtorE`: a constructor of an abstract type, in an erased position (K3)

`abstract inductive A := MkA(k : Nat)`, `def CtorE (n : Nat) : Type := (MkA(n); Nat)`; its twin `Ctor0`, returning `Z`,
is rejected: "[K3] the constructor MkA of the abstract type A at runtime". The reference reads neither `abstract` nor
the depth: its run of `MkA(n)` is `ColumnBox.runWrap`'s run of `MkBox(n)` with `A` for `Box` (a one-constructor
declaration with one `Nat` field), then the discard and `Nat`. -/

/-- `abstract inductive A := MkA(k : Nat)`, as the checker stores it. -/
def declA : IndDecl := { name := "A", ctors := [("MkA", [("k", .nat)])], «abstract» := true }

/-- `MkA(n)` in `CtorE`'s body. -/
def ctorA : Term := .ctor "A" 0 ⟨"MkA"⟩ [] [.place (.var 0)]

/-- `CtorE`'s body in the core. -/
def bodyCtorE : Term := .seq ctorA .nat

-- `CtorE`'s body is `bodyCtorE`
#guard coreBody "CtorE" == some bodyCtorE

/-- The record of `A` (no parameter) and the meaning of `MkA(f)`. -/
def recA (dm : DataModel) : Rec := dm.recOf declA []
def tyAM (dm : DataModel) : TyM := dm.tyR declA (recA dm)
def datA (dm : DataModel) (f : Sem) : Sem := .dat "A" (recA dm) 0 [f]

/-- **The field type is the reference's reading of `Nat`** (`FieldsFaithful` at the one field), as `ColumnBox.fieldTy_box`. -/
theorem fieldTy_A {K : RunCtx} (hΓ : K.Γ = [declA]) (hf : CtxFaithful K) :
    K.dm.fieldTyR declA (recA K.dm) 0 0 [] = TyM.nat := by
  have h := (hf K.Δ (fun _ => .el0 Nat 0)).1 declA (by rw [hΓ]; simp) [] 0 0 [] .nat rfl
    (fun j h => absurd h (Nat.not_lt_zero _)) (fun j h => absurd h (Nat.not_lt_zero _)) rfl rfl
  have hrun := h (.ty TyM.nat, .plain (TyM.univ 1)) (teleFrame K.dm K.D declA [] 0 []) (by
    show runT { K with Δ := K.Δ } (fun _ => .el0 Nat 0) noFuture false _ .nat _ = _
    rw [runT]; rfl)
  exact hrun.symm

theorem shape_A {K : RunCtx} (hΓ : K.Γ = [declA]) (hf : CtxFaithful K) :
    K.dm.sig.shape declA (recA K.dm) 0 0 [] = .leaf Nat .nat :=
  ColumnBox.shape_of_nat K.dm _ (by have h := fieldTy_A hΓ hf; unfold DataModel.fieldTyR at h; simpa using h)

theorem recLeafOk_A {K : RunCtx} (hΓ : K.Γ = [declA]) (hf : CtxFaithful K) : K.dm.RecLeafOk declA (recA K.dm) :=
  (hf K.Δ (fun _ => .el0 Nat 0)).2.2.leafOk declA (by rw [hΓ]; simp) [] rfl (fun j h => absurd h (Nat.not_lt_zero _))

/-- **Each `MkA(m)` is a member of `A`** (as `ColumnBox.datBox_mem`). -/
theorem datA_mem (dm : DataModel) (hsh : dm.sig.shape declA (recA dm) 0 0 [] = .leaf Nat .nat)
    (hok : dm.RecLeafOk declA (recA dm)) (m : Nat) : datA dm (.el0 Nat m) ∈ₛ[dm.read] tyAM dm := by
  refine dm.ctorR_mem declA (recA dm) 0 [.el0 Nat m] rfl (by decide) rfl (fun i f hi => ?_) hok
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    unfold DataModel.fieldTyR
    simp only [List.take_zero, List.map_nil]
    rw [hsh]; exact ⟨m, rfl⟩
  · simp at hi

/-- **The decisions the reference's run of `CtorE`'s body reads**, in its scope `sc`: the body, the constructor and
the read of `n` neither statements nor proofs; `n`'s reading not copy. -/
structure ParDecCtor (D : Decisions) (sc : List DeclInfo) : Prop where
  flBody : D.flags sc bodyCtorE = (false, false)
  flCtor : D.flags sc ctorA = (false, false)
  flRd : D.flags sc (.place (.var 0)) = (false, false)
  cpRd : D.copy (D.placeDecl sc (.var 0)) = false

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {sc : List DeclInfo} {s : SState} {a : Nat}

/-- The read of `n` (at `(1, 1)`, holding `a`) from a state `RefBox` reads, which moves it. -/
theorem runRead_box (h : ColumnBox.RefBox sc φ (.el0 Nat a) TyM.nat s)
    (hfl : K.D.flags sc (.place (.var 0)) = (false, false)) (hcp : K.D.copy (K.D.placeDecl sc (.var 0)) = false)
    (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place (.var 0)) s =
      some ((.el0 Nat a, { s.tyAt (.bind 1 1) with label := none }), s.setAt (.bind 1 1) fun _ => .moved) :=
  runRead_num h.shape h.varPos0 h.val h.ty (by rw [h.scope]; exact hfl) (by rw [h.scope]; exact hcp) tl hint

/-- **`MkA(n)`**: from `n ↦ a`, the tree `MkA(a)` at `A`'s record and type, `n` moved (`ColumnBox.runWrap` with `A`
for `Box`; the strict test at the constructor is `datA_mem`). -/
theorem runCtorA (hd : ParDecCtor K.D sc) (hΓ : K.Γ = [declA]) (hf : CtxFaithful K)
    (h : ColumnBox.RefBox sc φ (.el0 Nat a) TyM.nat s) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint ctorA s = some ((datA K.dm (.el0 Nat a), .plain (tyAM K.dm)), s.setAt (.bind 1 1) fun _ => .moved) := by
  have hfl : K.D.flags (scopeOf s) ctorA = (false, false) := by rw [h.scope]; exact hd.flCtor
  have hmem := datA_mem K.dm (shape_A hΓ hf) (recLeafOk_A hΓ hf) a
  show runT K ρ φ tl hint (.ctor "A" 0 ⟨"MkA"⟩ [] [.place (.var 0)]) s = _
  rw [runT]
  simp only [SM.erasedIf, SM.stmtIf, ← show ctorA = .ctor "A" 0 ⟨"MkA"⟩ [] [.place (.var 0)] from rfl, hfl,
    Bool.false_eq_true, if_false]
  rw [show K.Γ.find? (·.name == "A") = some declA by rw [hΓ]; rfl]
  have hrf : ∀ (rh : Option Rec), runFields K ρ φ false declA 0 0 rh [] [] [.place (.var 0)] s =
      some (([.el0 Nat a], []), s.setAt (.bind 1 1) fun _ => .moved) := by
    intro rh
    simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, bind]
    rw [runRead_box (K := K) (ρ := ρ) h hd.flRd hd.cpRd false]
    rfl
  have e1 : (declA.sort == 0) = false := rfl
  have e2 : declA.params.isEmpty = true := rfl
  have e3 : declA.params.length = 0 := rfl
  simp only [runParams, pure, bind, List.isEmpty_nil, Bool.not_true, Bool.false_or, e1, e2, e3,
    List.replicate_zero, if_true]
  rw [show (if false = true then List.map some ([] : List Sem) else []) = ([] : List (Option Sem)) from rfl, hrf]
  simp only [true_or, if_true, Option.orElse, HOrElse.hOrElse, OrElse.orElse]
  unfold SM.strictS
  simp only [ctorOut, e1, Bool.false_eq_true, if_false, pure]
  exact if_pos hmem

/-- **`CtorE`'s body runs to `Nat` at `Type₀`** (the meaning of the checker's `Nat` at `.sort 1`): `MkA(n)` runs and
passes its strict test, the discarded tree holds no borrow, `Nat` runs; `n` is left moved, as the checker's read of
`n` (a field taken by move) leaves it. At every tail flag and hint. -/
theorem run_bodyCtorE (hd : ParDecCtor K.D sc) (hΓ : K.Γ = [declA]) (hf : CtxFaithful K)
    (h : ColumnBox.RefBox sc φ (.el0 Nat a) TyM.nat s) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint bodyCtorE s =
      some ((.ty TyM.nat, .plain (TyM.univ 1)), s.setAt (.bind 1 1) fun _ => .moved) := by
  rw [show bodyCtorE = .seq ctorA .nat from rfl, runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.seq ctorA .nat)) _ s = _
  rw [show K.D.flags (scopeOf s) (.seq ctorA .nat) = (false, false) by rw [h.scope]; exact hd.flBody]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [Bind.bind, runCtorA hd hΓ hf h, SM.guardMod, DiscardOk, discardEnd, ColumnI.runT_nat]
  simp [TyS.plain]

end

/-- **The reference's body state for `CtorE` is one `RefBox` reads** (formed in the empty state: `[{}, {self, n ↦ a}]`),
at the scope `[.other, b.decl]`. -/
theorem refBox_start (b : SBinding) (φ : Future) (a : Nat) :
    ColumnBox.RefBox [.other, b.decl] φ (.el0 Nat a) TyM.nat (((emptyState 0).under.pushBind b).pushBind (nBnd a)) := by
  have hsh : ∀ p, (((emptyState 0).under.pushBind b).pushBind (nBnd a)).shape p = none := (refCap_start b a).shape
  exact ⟨liveLabels_noShape hsh, hsh, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- A state at erased depth 1 with `A` declared (the constructor's reading reads its declaration). -/
def stCtorE : MState := { erasedDepth := 1, inds := [declA] }

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther isOther_eq)
open Ochr.Meaning.Steps.Form.ColumnP.Aux (pdRun cpRun)

theorem ok_fl_bodyC : isOk (flagsRun bodyCtorE) (scopeState stCtorE scCap) 1000 = true := by decide +kernel
theorem val_fl_bodyC : outVal (flagsRun bodyCtorE) (scopeState stCtorE scCap) 1000 = (false, false) := by decide +kernel
theorem ok_fl_ctor : isOk (flagsRun ctorA) (scopeState stCtorE scCap) 1000 = true := by decide +kernel
theorem val_fl_ctor : outVal (flagsRun ctorA) (scopeState stCtorE scCap) 1000 = (false, false) := by decide +kernel
theorem ok_fl_rd0 : isOk (flagsRun (.place (.var 0))) (scopeState stCtorE scCap) 1000 = true := by decide +kernel
theorem val_fl_rd0 : outVal (flagsRun (.place (.var 0))) (scopeState stCtorE scCap) 1000 = (false, false) := by
  decide +kernel
theorem ok_pd0 : isOk (pdRun (.var 0)) (scopeState stCtorE scCap) 1000 = true := by decide +kernel
theorem val_pd0 : isOther (outVal (pdRun (.var 0)) (scopeState stCtorE scCap) 1000) = true := by decide +kernel
theorem ok_cpC : isOk cpRun stCtorE 1000 = true := by decide +kernel
theorem val_cpC : outVal cpRun stCtorE 1000 = false := by decide +kernel

end Aux

/-- **`ParDecCtor` at every table aligned with the checker at `stCtorE`** (kernel evaluation). -/
theorem parDecCtor {D : Decisions} (hd : DecTab D stCtorE) : ParDecCtor D scCap := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hfl : ∀ sc t, isOk (ColumnC.Aux.flagsRun t) (scopeState stCtorE sc) 1000 = true →
      D.flags sc t = outVal (ColumnC.Aux.flagsRun t) (scopeState stCtorE sc) 1000 := fun sc t hok =>
    hd.flags 100 sc t _ 1000 _ (runs_out (ColumnC.Aux.flagsRun t) _ 1000 hok)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfl _ _ Aux.ok_fl_bodyC, Aux.val_fl_bodyC]
  · rw [hfl _ _ Aux.ok_fl_ctor, Aux.val_fl_ctor]
  · rw [hfl _ _ Aux.ok_fl_rd0, Aux.val_fl_rd0]
  · rw [hd.placeDecl 100 _ _ _ 1000 _ (runs_out (ColumnP.Aux.pdRun _) _ 1000 Aux.ok_pd0),
      ColumnC.Aux.isOther_eq Aux.val_pd0]
    exact (hd.copy 100 .other _ 1000 _ (runs_out ColumnP.Aux.cpRun _ 1000 Aux.ok_cpC)).trans Aux.val_cpC

/-! ## The whole program: a function returning a type, formed by the reference's `.fix` clause

`CapE` and `CtorE` are both `def X (n : Nat) : Type := t`. Where the body runs, from the state the `.fix` clause builds
at every argument, to `Nat` at `Type₀` leaving no label live (`run_bodyCapE`, `run_bodyCtorE`), the clause forms `X`'s
closure from the empty state (where a global is formed) and it is a MEMBER of `Π(n : Nat). Type₀`: the reference's
strict run of the accepted program succeeds (`fix_typeFn`). -/

/-- The codomain `Type₀`, as the `.fix` clause reads it. -/
def outT : PiCod := ⟨false, fun _ => TyM.univ 1⟩

/-- **The decisions the `.fix` clause reads at `X`'s signature**, in the empty scope: `n` read `.other`, the codomain
read `.sort 1` (so `self` reads `.pi (.sort 1)`), the sort of `Π(n : Nat). Type` is `2`, the `fix` unerased. -/
structure ParDecDef (D : Decisions) (fx : Term) : Prop where
  td0 : D.typeDecl [] .nat = .other
  tdT : D.typeDecl [.other] (.sort 1) = .sort 1
  srt : D.piSort [] (.pi [⟨"n"⟩] [.nat] (.sort 1)) = 2
  flFix : D.flags [] fx = (false, false)

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem runT_sort (tl : Bool) (h : TyS) (l : Nat) (s : SState) :
    runT K ρ φ tl h (.sort l) s = some ((.ty (TyM.univ l), .plain (TyM.univ (sortSucc l))), s) := by
  rw [runT]; rfl

theorem codOf_type (s : SState) (bs : List PBind) (rs : List Bool) : codOf K ρ φ s bs rs (.sort 1) = outT := by
  unfold codOf; simp only [runT_sort]; rfl

/-- The body state the `.fix` clause builds for `X` at the argument `a`, `self` bound by `b`. -/
noncomputable def sX (b : SBinding) (a : Nat) : SState := ((emptyState 0).under.pushBind b).pushBind (nBnd a)

/-- **A function `X (n : Nat) : Type := t` whose body runs to `Nat` is a member of `Π(n : Nat). Type₀`**, and the
`.fix` clause forms it from the empty state, leaving the state as it was. `hbody`: from the body state at every
argument, for every binding of `self` read `.pi (.sort 1)` (the codomain's reading), the body runs to `Nat` at `Type₀`
and leaves `n` moved. -/
theorem fix_typeFn (hX : Hint) (t : Term) (hd : ParDecDef K.D (.fix hX [⟨"n"⟩] [.nat] (.sort 1) none t))
    (hcap : capOrder (.fix hX [⟨"n"⟩] [.nat] (.sort 1) none t) = [])
    (hbody : ∀ (b : SBinding) (a : Nat) (tl : Bool) (hint : TyS), b.decl = .pi (.sort 1) →
      runT K ρ φ tl hint t (sX b a) = some ((.ty TyM.nat, .plain (TyM.univ 1)), (sX b a).setAt (.bind 1 1) fun _ => .moved))
    (tl : Bool) (hint : TyS) :
    ∃ f, runT K ρ φ tl hint (.fix hX [⟨"n"⟩] [.nat] (.sort 1) none t) (emptyState 0) =
        some ((f, .plain (piTyAt K.dm.read 2 psI outT)), emptyState 0) ∧ f ∈ₛ[K.dm.read] piTyAt K.dm.read 2 psI outT := by
  have hpd : K.D.paramDecls (scopeOf (emptyState 0)) [.nat] = [.other] := by
    show K.D.paramDecls [] [.nat] = [.other]
    simp [Decisions.paramDecls, Decisions.teleDecls, hd.td0]
  have hsort : fixSort K (emptyState 0) [⟨"n"⟩] [.nat] (.sort 1) = 2 := hd.srt
  have h1 : bindsOf K ρ φ (emptyState 0) [.nat] = [(fun _ => .plain TyM.nat, .other)] := ColumnI.bindsOf_nat _ ρ φ _ hpd
  have h2 : K.D.typeDecl (K.D.teleDecls (scopeOf (emptyState 0)) [.nat]) (.sort 1) = .sort 1 := by
    show K.D.typeDecl (K.D.teleDecls [] [.nat]) (.sort 1) = .sort 1
    simp [Decisions.teleDecls, hd.td0, hd.tdT]
  have hty : fixTy K ρ φ (emptyState 0) [⟨"n"⟩] [.nat] (.sort 1) = piTyAt K.dm.read 2 psI outT := by
    unfold fixTy; rw [hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, codOf_type]
  have hmem : fixClo K ρ φ (emptyState 0) [⟨"n"⟩] [.nat] (.sort 1) none t ∈ₛ[K.dm.read] piTyAt K.dm.read 2 psI outT := by
    unfold fixClo
    rw [hty, hsort, ColumnI.runDoms_nat _ ρ φ _ hpd, codOf_type]
    refine fixClo_mem_nonrec _ 2 (emptyState 0) psI outT _ 0 t ⟨by omega, by omega⟩ rfl
      (fun _ _ => Nat.le_refl 2) fun args ha => ?_
    obtain ⟨a, rfl⟩ := ColumnR.domMembers_one ha
    let fb : List PBind × PBind := (bindsOf K ρ φ (emptyState 0) [.nat],
      fixCod K ρ φ (emptyState 0) (bindsOf K ρ φ (emptyState 0) [.nat]) ([.nat].map Term.isRefTy) (.sort 1),
      K.D.typeDecl (K.D.teleDecls (scopeOf (emptyState 0)) [.nat]) (.sort 1))
    let selfM : Sem := closureAt K.dm.read 2 φ psI (weakCod 2 (fixRank none) 0 outT)
      (stageFn 2 psI (fixRank none) 0 (fun _ => none))
    let selfT : TyM := piTyAt K.dm.read 2 psI (weakCod 2 (fixRank none) 0 outT)
    let b : SBinding := { ty := .plain selfT, val := fun _ => selfM, decl := .pi fb.2.2 }
    have hb : b.decl = .pi (.sort 1) := by show DeclInfo.pi fb.2.2 = _; rw [show fb.2.2 = .sort 1 from h2]
    have hst : ([Sem.el0 Nat a].zip psI).foldl (fixStep fb) ((emptyState 0).under.pushBind b, [], []) =
        (sX b a, [.el0 Nat a], []) := by
      simp only [psI, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, fixStep,
        show fb.1 = _ from h1, Bool.false_eq_true, if_false, List.length_nil, List.getElem?_cons_zero, List.nil_append]
      rfl
    have hl : ((sX b a).setAt (.bind 1 1) fun _ => .moved).liveLabels = [] := by
      rw [Strict.liveLabels_setAt]; exact liveLabels_noShape (refCap_start b a).shape
    refine ⟨⟨.ty TyM.nat, [], none⟩, ?_, ⟨Strict.ty_univ1_mem Code0.nat rfl, fun i d hi hd' => ?_⟩, rfl⟩
    · show fixBodyAt K ρ φ fb (emptyState 0) psI outT _ 0 t _ [.el0 Nat a] = _
      unfold fixBodyAt
      dsimp only
      rw [hst]
      dsimp only
      -- main's D142: `t` returns types, so its body runs as a statement and the pop sees the start's state
      rw [show fb.2.2 = .sort 1 from h2, fnErasedD_sort]
      simp only [SM.bodyRun, SM.stmtIf, ↓reduceIte]
      rw [hbody b a true _ hb]
      simp only [Option.map_some]
      rw [show (sX b a).liveLabels = [] from liveLabels_noShape (refCap_start b a).shape]
      simp [ColumnI.endsOk_nil]
    · rcases i with _ | i
      · simp [psI] at hi; subst hi; cases hd'
      · simp [psI] at hi
  refine ⟨_, ?_, hmem⟩
  rw [run_fix_of_mem tl hint hX [⟨"n"⟩] [.nat] (.sort 1) none t (emptyState 0) hd.flFix (by rw [hcap]; trivial)
    (by rw [hty]; exact hmem), hty]
  unfold fixMoves; rw [hcap]; rfl

end

/-! ## The two programs, whole -/

/-- `CapE` and `CtorE` as the reference's `.fix` terms (the checker's `Def`: one parameter `n : Nat`, codomain `Type`). -/
def fixCapE : Term := .fix ⟨"CapE"⟩ [⟨"n"⟩] [.nat] (.sort 1) none bodyCapE
def fixCtorE : Term := .fix ⟨"CtorE"⟩ [⟨"n"⟩] [.nat] (.sort 1) none bodyCtorE

/-- The checker's own resolution of a definition of `DepthProbe`: its parameters' domains and its codomain. -/
def coreSig (nm : String) : Option (List Term × Term) :=
  match DepthProbe.decls.find? (·.name == nm) with
  | some d => match (Ochr.Surface.runResolve DepthProbe.decls d 100000).1 with
    | .ok (.ok (.defn df)) => some (df.doms, df.cod)
    | _ => none
  | none => none

#guard coreSig "CapE" == some ([.nat], .sort 1)
#guard coreSig "CtorE" == some ([.nat], .sort 1)

namespace Aux

open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal runs_out)
open Ochr.Meaning.Steps.Form.ColumnC.Aux (flagsRun isOther isOther_eq)
open Ochr.Meaning.Steps.Form.ColumnI.Aux (typeDeclRun piSortRun)

def isSort1 : DeclInfo → Bool
  | .sort 1 => true
  | _ => false

theorem isSort1_eq {d : DeclInfo} (h : isSort1 d = true) : d = .sort 1 := by
  unfold isSort1 at h; split at h <;> first | rfl | cases h

section
variable (st : MState) (hst : st = stCapE ∨ st = stCtorE)
include hst

theorem ok_tdN : isOk (typeDeclRun .nat) (scopeState st []) 1000 = true := by
  rcases hst with rfl | rfl <;> decide +kernel
theorem val_tdN : isOther (outVal (typeDeclRun .nat) (scopeState st []) 1000) = true := by
  rcases hst with rfl | rfl <;> decide +kernel
theorem ok_tdT : isOk (typeDeclRun (.sort 1)) (scopeState st [.other]) 1000 = true := by
  rcases hst with rfl | rfl <;> decide +kernel
theorem val_tdT : isSort1 (outVal (typeDeclRun (.sort 1)) (scopeState st [.other]) 1000) = true := by
  rcases hst with rfl | rfl <;> decide +kernel
theorem ok_srtT : isOk (piSortRun (.pi [⟨"n"⟩] [.nat] (.sort 1))) (scopeState st []) 1000 = true := by
  rcases hst with rfl | rfl <;> decide +kernel
theorem val_srtT : outVal (piSortRun (.pi [⟨"n"⟩] [.nat] (.sort 1))) (scopeState st []) 1000 = 2 := by
  rcases hst with rfl | rfl <;> decide +kernel

end

theorem ok_fl_fixCapE : isOk (flagsRun fixCapE) (scopeState stCapE []) 1000 = true := by decide +kernel
theorem val_fl_fixCapE : outVal (flagsRun fixCapE) (scopeState stCapE []) 1000 = (false, false) := by decide +kernel
theorem ok_fl_fixCtorE : isOk (flagsRun fixCtorE) (scopeState stCtorE []) 1000 = true := by decide +kernel
theorem val_fl_fixCtorE : outVal (flagsRun fixCtorE) (scopeState stCtorE []) 1000 = (false, false) := by
  decide +kernel

end Aux

/-- `ParDecDef` at a table aligned with the checker at `stCapE` or `stCtorE`, given the `fix` unerased there. -/
theorem parDecDef {D : Decisions} {st : MState} (hst : st = stCapE ∨ st = stCtorE) (hd : DecTab D st) (fx : Term)
    (hfx : D.flags [] fx = (false, false)) : ParDecDef D fx := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  refine ⟨?_, ?_, ?_, hfx⟩
  · rw [hd.typeDecl 100 [] .nat _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun .nat) _ 1000 (Aux.ok_tdN st hst))]
    exact ColumnC.Aux.isOther_eq (Aux.val_tdN st hst)
  · rw [hd.typeDecl 100 [.other] (.sort 1) _ 1000 _ (runs_out (ColumnI.Aux.typeDeclRun _) _ 1000 (Aux.ok_tdT st hst))]
    exact Aux.isSort1_eq (Aux.val_tdT st hst)
  · rw [hd.piSort 100 [] _ _ 1000 _ (runs_out (ColumnI.Aux.piSortRun _) _ 1000 (Aux.ok_srtT st hst)), Aux.val_srtT st hst]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem scopeOf_sX (b : SBinding) (a : Nat) : scopeOf (sX b a) = [.other, b.decl] := (refCap_start b a).scope

/-- **`CapE`, whole** (the capture-move check, accepted only above depth 0): at every table aligned with the checker
(at `stCapE`), the reference's `.fix` clause forms `CapE`'s closure from the empty state, a member of
`Π(n : Nat). Type₀`; at every argument the body forms the inner closure (a member of `Π(m : Nat). Nat`, returning `n`'s
value at every argument), moves `n` into it, discards it, and returns `Nat`. Assumes nothing. -/
theorem column_CapE (hD : DecTab K.D stCapE) (tl : Bool) (hint : TyS) :
    ∃ f, runT K ρ φ tl hint fixCapE (emptyState 0) =
        some ((f, .plain (piTyAt K.dm.read 2 psI outT)), emptyState 0) ∧ f ∈ₛ[K.dm.read] piTyAt K.dm.read 2 psI outT := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hfx : K.D.flags [] fixCapE = (false, false) := by
    rw [hD.flags 100 [] _ _ 1000 _ (runs_out (ColumnC.Aux.flagsRun _) _ 1000 Aux.ok_fl_fixCapE), Aux.val_fl_fixCapE]
  refine fix_typeFn ⟨"CapE"⟩ bodyCapE (parDecDef (.inl rfl) hD _ hfx) rfl (fun b a tl' hint' hb => ?_) tl hint
  have hsc : scopeOf (sX b a) = scCap := by rw [scopeOf_sX, hb]
  exact run_bodyCapE (refCap_start b a) (by show ParDecCap K.D (scopeOf (sX b a)); rw [hsc]; exact parDecCap hD) tl' hint'

/-- **`CtorE`, whole** (K3, accepted only above depth 0): at every table aligned with the checker (at `stCtorE`), in a
context whose declarations are `[A]` with a data model faithful to it, the reference's `.fix` clause forms `CtorE`'s
closure from the empty state, a member of `Π(n : Nat). Type₀`; at every argument the body builds `MkA(n)` (a member
of `A`), discards it, and returns `Nat`. Assumes nothing beyond the context's own faithfulness (`CtxFaithful`, which
every step's `Pre` carries). -/
theorem column_CtorE (hD : DecTab K.D stCtorE) (hΓ : K.Γ = [declA]) (hf : CtxFaithful K) (tl : Bool) (hint : TyS) :
    ∃ f, runT K ρ φ tl hint fixCtorE (emptyState 0) =
        some ((f, .plain (piTyAt K.dm.read 2 psI outT)), emptyState 0) ∧ f ∈ₛ[K.dm.read] piTyAt K.dm.read 2 psI outT := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  have hfx : K.D.flags [] fixCtorE = (false, false) := by
    rw [hD.flags 100 [] _ _ 1000 _ (runs_out (ColumnC.Aux.flagsRun _) _ 1000 Aux.ok_fl_fixCtorE), Aux.val_fl_fixCtorE]
  refine fix_typeFn ⟨"CtorE"⟩ bodyCtorE (parDecDef (.inr rfl) hD _ hfx) rfl (fun b a tl' hint' hb => ?_) tl hint
  have hR := refBox_start b φ a
  rw [hb] at hR
  exact run_bodyCtorE (parDecCtor hD) hΓ hf hR tl' hint'

end

end Ochr.Meaning.Steps.Form.DepthRef
