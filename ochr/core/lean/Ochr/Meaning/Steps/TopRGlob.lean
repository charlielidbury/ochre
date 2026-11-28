import Ochr.Meaning.Steps.TopRLinks

/-!
# The acceptance test at `R`: what later checks read of `R` (`GlobGrowG`; lead46, docs/31 D259 on)

After `R`'s check, its entry must meet `GlobalsOk`'s clauses at the context of every later check. Tools here: `R`'s
closure at `Π(n : Nat). Nat` is determined by its function at the numbers (the closure applies it only at encoded
carrier elements, and a data codomain with no borrow parameter reads no future), and `R`'s function is `0` at every
number at every context whose table decides `R`'s code as the checker does.
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.ColumnR Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Steps.Form.ColumnI (psI outI)
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly

/-- **A closure at `Π(n : Nat). Nat` is determined by its function at the numbers** (whose outputs have no finals): at
any two futures. -/
theorem closureAt_nat_congr (R : DataRead) (φ φ' : Future) (g g' : List Sem → Option BodyOut)
    (hg : ∀ m, g [.el0 Nat m] = g' [.el0 Nat m]) (hf : ∀ m o, g [.el0 Nat m] = some o → o.finals = []) :
    closureAt R 1 φ psI outI g = closureAt R 1 φ' psI outI g' := by
  unfold closureAt closureL
  have key : mkTelL (lvl0 R) φ (telL (lvl0 R) psI [] PUnit outI).2 [] (fun fs => some (PUnit.unit, fs)) g =
      mkTelL (lvl0 R) φ' (telL (lvl0 R) psI [] PUnit outI).2 [] (fun fs => some (PUnit.unit, fs)) g' := by
    simp only [psI, outI, telL, mkTelL, List.nil_append]
    refine dite_isSome_congr _ _ (funext fun x => ?_)
    have hx : Code0.enc R TyM.nat.code0.snd x = Sem.el0 Nat x := rfl
    rw [hx, ← hg x]
    rcases e : g [Sem.el0 Nat x] with _ | o
    · rfl
    · simp only [Option.bind_some]
      unfold mkLeafDataL
      rw [hf x o e]
      rfl
  rw [key]
  rfl


/-- **`R`'s function is `0` at every number** (PROVED at every context whose table decides `R`'s code as the checker
does: the fixpoint equation, `fixEqAt_R`, and the body's run, `fixBodyAt_R_anyK`, by induction on the number). -/
theorem GG_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) (φ : Future) (m : Nat) :
    GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR [.el0 Nat m] = some ⟨.el0 Nat 0, [], none⟩ := by
  have hfg := fnGoodAt_R (φ := φ) K ρ hd
  unfold FnGoodAt at hfg
  rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd] at hfg
  have hX : SelfR K.dm outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) := ⟨rfl, fun a ha => hfg.1.2 a ha trivial, hfg.2⟩
  have hsel : selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR =
      closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) := by
    unfold selfG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]
  have hpiT : piTG K ρ φ [⟨"n"⟩] [.nat] .nat = piTyAt K.dm.read 1 psI outI := by
    unfold piTG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]
  have hT := fixBodyAt_R_anyK (φ := φ) K hd.1 ρ (fbG K ρ φ [.nat] .nat) (fbG_R1 K ρ hd) (fbG_R2 K ρ hd)
    (closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR), .plain (piTyAt K.dm.read 1 psI outI))
    rfl hX.whole (SelfR.movedIn outI _) hX.mem
  have heq : ∀ k, GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR [.el0 Nat k] =
      fixBodyAt K ρ φ (fbG K ρ φ [.nat] .nat) (emptyState 0) psI outI (piTyAt K.dm.read 1 psI outI) 0 bodyR
        (closureAt K.dm.read 1 φ psI outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR)) [.el0 Nat k] := by
    intro k
    have h := fixEqAt_R (φ := φ) K ρ hd [.el0 Nat k] (by rw [psG_R K ρ hd]; exact domMembers_nat _ k)
    rw [h, psG_R K ρ hd, outG_R K ρ, hpiT, hsel]
    rfl
  induction m with
  | zero => rw [heq]; exact hT.1
  | succ m ih =>
    rw [heq]
    exact hT.2 m (.el0 Nat 0) _ rfl (fun s => SelfR.apply (φ := φ) hX m ih s)


/-- `R`'s closure at its forming state is a member of its type (under `DecR`). -/
theorem selfG_mem_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) (φ : Future) :
    selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR ∈ₛ[K.dm.read] piTG K ρ φ [⟨"n"⟩] [.nat] .nat := by
  have hfg := fnGoodAt_R (φ := φ) K ρ hd
  unfold FnGoodAt at hfg
  rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd] at hfg
  have hX : SelfR K.dm outI (GG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) := ⟨rfl, fun a ha => hfg.1.2 a ha trivial, hfg.2⟩
  unfold selfG piTG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]
  exact hX.mem

/-- **The run of `R`'s `fix` term at its forming state** (under `DecR`): `R`'s closure `selfG` at its type `piTG`. -/
theorem runT_fixR (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) (φ : Future) (tl : Bool) :
    runT K ρ φ tl (.plain .err) fixR (stateOf 0 []) =
      some ((selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR, .plain (piTG K ρ φ [⟨"n"⟩] [.nat] .nat)), stateOf 0 []) := by
  show runT K ρ φ tl (.plain .err) (.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) (stateOf 0 []) = _
  rw [run_fix_def]
  have hfl : K.D.flags (scopeOf (stateOf 0 [])) (.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) = (false, false) :=
    hd.2.2.2.2
  have hfm : fixMoves K (.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) (stateOf 0 []) = stateOf 0 [] := by
    unfold fixMoves; rw [show capOrder (.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) = [] from capOrder_fixR]; rfl
  rw [hfl, hfm, show capOrder (.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) = [] from capOrder_fixR]
  simp only [SM.erasedIf, SM.stmtIf, FoldOk, Bool.false_eq_true, if_false, if_true, ↓reduceIte]
  exact strictS_some K.dm.read (selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR, .plain (piTG K ρ φ [⟨"n"⟩] [.nat] .nat)) _
    (selfG_mem_R K hd ρ φ)

/-- `R`'s stored meaning at its stage: its closure at the program's assignment and the constant future, at its stored
type's meaning. -/
theorem defMeaning_R (K : RunCtx) (hd : DecR K.D) :
    defMeaning (fun _ => .err) K defR (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) []) =
      some (selfG K (fun _ => .err) noFuture [⟨"n"⟩] [.nat] .nat (some 0) bodyR,
        globalTyS (fun _ => .err) K (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])) := by
  unfold defMeaning
  simp only [defR, List.isEmpty_cons, Bool.false_eq_true, if_false]
  rw [show (emptyState 0 : SState) = stateOf 0 [] from rfl, run]
  rw [show (Term.fix ⟨"R"⟩ [⟨"n"⟩] [.nat] .nat (some 0) bodyR) = fixR from rfl, runT_fixR K hd]

/-- **`R`'s closure is the same at every context with `DecR`, assignment and future** (`closureAt_nat_congr`, `GG_R`). -/
theorem selfG_R_eq (K K' : RunCtx) (hd : DecR K.D) (hd' : DecR K'.D) (hdm : K'.dm = K.dm) (ρ ρ' : Assignment)
    (φ φ' : Future) :
    selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR = selfG K' ρ' φ' [⟨"n"⟩] [.nat] .nat (some 0) bodyR := by
  unfold selfG
  rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd, psG_R K' ρ' hd', outG_R K' ρ', lG_R K' hd', hdm]
  exact closureAt_nat_congr _ φ φ' _ _ (fun m => by rw [GG_R K hd, GG_R K' hd'])
    (fun m o h => by rw [GG_R K hd] at h; cases h; rfl)


/-- **`R`'s stored type means `Π(n : Nat). Nat` at every assignment** (`globalTyS_tPi` at any assignment, under `DecR`). -/
theorem meanV_tPi_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) :
    (meanV K ρ noFuture (.plain .err) (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])).asTy = piTyAt K.dm.read 1 psI outI := by
  have h1 : meanV K ρ noFuture (.plain .err) (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) []) =
      (match run K ρ noFuture (.plain .err) (.pi [⟨"n"⟩] [.nat] .nat) (stateOf 0 []) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err) := by
    classical
    show (if CapsOk K.dm.read (capsVals K ρ noFuture []) (capsTys K ρ noFuture []) then
        match run K ρ noFuture (.plain .err) (.pi [⟨"n"⟩] [.nat] .nat)
          (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture []))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err) = _
    rw [capsVals, capsTys, if_pos (show CapsOk K.dm.read [] [] from trivial)]
    rfl
  have hok' : PiOk K.dm.read (runDoms K ρ noFuture (stateOf 0 []) [.nat]) []
      (codOf K ρ noFuture (stateOf 0 []) (bindsOf K ρ noFuture (stateOf 0 []) [.nat]) ([Term.nat].map Term.isRefTy) .nat) := by
    show PiOk K.dm.read (psG K ρ noFuture [.nat]) [] (outG K ρ noFuture [.nat] .nat)
    rw [psG_R K ρ hd, outG_R K ρ]; exact ⟨rfl, fun _ _ => rfl⟩
  rw [h1, run, run_pi_def, if_pos hok']
  show piTyAt K.dm.read (lG K [⟨"n"⟩] [.nat] .nat) (psG K ρ noFuture [.nat]) (outG K ρ noFuture [.nat] .nat) = _
  rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]

/-- **`retKind` at `R`** (MODEL; read true, unproved: `R`'s function formed at ANY state returns an unlabelled result,
its codomain being `Nat`; the column's run of the body, `ColumnRRun.runR`, is for the two-frame start state and must be
generalised to the top frame of any state). `Master.RetKindG`'s clause at `R`'s code, at every context with `DecR`. -/
def RetKindR : Prop :=
  ∀ (K : RunCtx), DecR K.D → ∀ (ρ : Assignment) (φ : Future) (s : SState) (piT : TyM) (args : List Sem) (o : BodyOut),
    DomMembers K.dm.read (runDoms K ρ φ s [.nat]) args →
    fixG K ρ φ (bindsOf K ρ φ s [.nat], fixCod K ρ φ s (bindsOf K ρ φ s [.nat]) ([Term.nat].map Term.isRefTy) .nat,
        K.D.typeDecl (K.D.teleDecls (scopeOf s) [.nat]) .nat)
      (K.D.piSort (scopeOf s) (.pi [⟨"n"⟩] [.nat] .nat)) s (runDoms K ρ φ s [.nat])
      (codOf K ρ φ s (bindsOf K ρ φ s [.nat]) ([Term.nat].map Term.isRefTy) .nat) piT s.nextLoan (some 0) bodyR args = some o →
    o.retLabel.isSome = (codOf K ρ φ s (bindsOf K ρ φ s [.nat]) ([Term.nat].map Term.isRefTy) .nat).isRef


/-- `R`'s stored type's meaning at any context with `DecR`. -/
theorem globalTyS_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) :
    (globalTyS ρ K (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])).m = piTyAt K.dm.read 1 psI outI := by
  unfold globalTyS Value.tyS
  rw [meanV_eq_mean]
  exact meanV_tPi_R K hd ρ

theorem piTG_R (K : RunCtx) (hd : DecR K.D) (ρ : Assignment) (φ : Future) :
    piTG K ρ φ [⟨"n"⟩] [.nat] .nat = piTyAt K.dm.read 1 psI outI := by
  unfold piTG; rw [psG_R K ρ hd, outG_R K ρ, lG_R K hd]

/-- A closed closure means its code's run from the empty state. -/
theorem meanV_clo_nil (K : RunCtx) (ρ : Assignment) (φ : Future) (t : Term) :
    meanV K ρ φ (.plain .err) (.clo [] t []) =
      (match runT K ρ φ false (.plain TyM.err) t (stateOf 0 []) with
        | some ((v, _), _) => v
        | none => .err) := by
  classical
  show (if CapsOk K.dm.read (capsVals K ρ φ []) (capsTys K ρ φ []) then
      (match runT K ρ φ false (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ []) (capsTys K ρ φ []))) with
        | some ((v, _), _) => v
        | none => .err)
    else .err) = _
  rw [capsVals, capsTys, if_pos (show CapsOk K.dm.read [] [] from trivial)]
  rfl

/-- The stage after `R`: Σ `R`'s entry, `R`'s meaning its closure at its stored type's meaning. -/
noncomputable def stageR (dm : DataModel) (Γ : List IndDecl) (P : ProgState) (st' : MState) : ProgState :=
  { globals := [gR], inds := st'.inds,
    means := [("R", (selfG (KS dm Γ P st') (fun _ => .err) noFuture [⟨"n"⟩] [.nat] .nat (some 0) bodyR,
      globalTyS (fun _ => .err) (KS dm Γ P st') (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])))] }

section
variable {dm : DataModel} {items : List Item}

/-- **`GlobGrowG` at `R`'s program** (PROVED but for `RetKindR`): after `R`'s check, at the context of every later check
(its decisions a later state's, whose Σ starts with `R`'s entry, so `DecR` holds there), `R`'s entry meets every clause
of `GlobalsOk`: its stored type means `Π(n : Nat). Nat` (`ty`); its stored meaning, its closure formed at the stage's
context, the program assignment and the constant future, is every later context's closure of `R` at every assignment,
future and `Δ` (`fn`, `accepted`: `selfG_R_eq`); it is a member (`mem`, the step's `MeansMember`); its fixpoint equation
(`fixEq`, `fixEqAt_R`, computed: no widened `MemBelow`); `memBelow` and `const` vacuous; `codeValFree`; `retKind` the
assumed `RetKindR`. -/
theorem globGrow_R (hret : RetKindR) (dm : DataModel) (hr : ResolvesTo pq F items) :
    GlobGrowG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin hrun _ _ _ _ hMM _ Dd cu hlater hcu
  obtain ⟨rfl, hPg, hPm⟩ := atStage_R hr hin
  have hrun' := hrun
  rw [hPg] at hrun'
  obtain ⟨-, -, -, -, -, -, hg', -⟩ := R_check_inv hrun'
  have hd0 : DecR (KS dm (indsOf {} F items) P st').D := decR_KS (m := false) (rest := []) P st' hg'
  have hstep : ProgState.step dm (chainDecisions F) (indsOf {} F items) (fun _ => .err) {} F P (.defn defR) =
      (stageR dm (indsOf {} F items) P st') := by
    unfold ProgState.step
    dsimp only
    rw [show ({ globals := P.globals, inds := P.inds, cfg := {} } : MState) = { globals := P.globals, inds := P.inds } from rfl,
      hrun]
    dsimp only
    have hT : ((st'.globals.find? (·.name == defR.name)).map (·.ty)).getD .bot = .tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [] := by
      rw [hg']; rfl
    rw [hT, defMeaning_R _ hd0, hg', hPm]
    rfl
  rw [hstep] at hMM hlater hcu ⊢
  obtain ⟨st'', rfl, ⟨rest, hrest⟩, -⟩ := hlater
  have hdK : DecR (chainDecisions F st'') := decR_chain st'' (m := false) (rest := rest) (by rw [← hrest]; rfl)
  have hRnot : ∀ x ∈ cu, x.1 ≠ "R" := fun x hx h => by
    have := hcu x hx
    rw [h] at this
    simp [ProgState.isGlobal, stageR] at this
  have hglob : (ctxAt dm (indsOf {} F items) (stageR dm (indsOf {} F items) P st')
        (chainDecisions F st'') cu).C.global "R" =
      (selfG (KS dm (indsOf {} F items) P st') (fun _ => .err) noFuture [⟨"n"⟩] [.nat] .nat (some 0) bodyR,
        globalTyS (fun _ => .err) (KS dm (indsOf {} F items) P st') (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])) := by
    rcases cu with _ | ⟨f, b, G⟩
    · rfl
    · have hf : f ≠ "R" := hRnot (f, b, G) rfl
      show (if "R" = f then G else _) = _
      rw [if_neg (Ne.symm hf)]
      rfl
  have hfind : ∀ n g, ([gR] : List GDef).find? (·.name == n) = some g → n = "R" ∧ g = gR := fun n g h => find_gR h
  have hcur : ∀ n, n = "R" → (ctxAt dm (indsOf {} F items) (stageR dm (indsOf {} F items) P st')
        (chainDecisions F st'') cu).cur.map (·.1) ≠ some n := by
    intro n hn e
    subst hn
    rcases cu with _ | ⟨f, b, G⟩
    · cases e
    · simp only [ctxAt, Option.map_some, Option.some.injEq] at e
      exact hRnot (f, b, G) rfl e
  have hselfeq : ∀ (K : RunCtx), DecR K.D → K.dm = dm → ∀ ρ φ,
      selfG (KS dm (indsOf {} F items) P st') (fun _ => .err) noFuture [⟨"n"⟩] [.nat] .nat (some 0) bodyR =
        selfG K ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR :=
    fun K hK hKdm ρ φ => selfG_R_eq _ K hd0 hK hKdm _ ρ _ φ
  have hty : (globalTyS (fun _ => .err) (KS dm (indsOf {} F items) P st') (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])).m =
      piTyAt dm.read 1 psI outI := globalTyS_R _ hd0 _
  refine ⟨fun n g hf _ ρ => ?_, fun n g hf hn => ?_, fun n g t hf ht _ ρ φ => ?_, fun n g hf _ => ?_,
    fun n g b hf hc => ?_, fun n gd self hs ds c dec body hf hc hfn ρ φ args ha => ?_,
    fun n gd self hs ds c dec body hf hc hfn Δ ρ φ => ?_, fun n gd self hs ds c dec body hf hc hfn => ?_,
    fun n g t hf ht => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    rw [hglob]
    show _ = (meanV _ ρ noFuture (.plain .err) (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat) [])).asTy
    rw [meanV_tPi_R _ hdK ρ, hty]
    rfl
  · obtain ⟨rfl, rfl⟩ := hfind n g hf; cases hn
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    simp only [gR, Option.some.injEq] at ht; subst ht
    rw [hglob]
    refine ⟨?_, fun r s' hrun => ?_⟩
    · rw [meanV_clo_nil, runT_fixR _ hdK ρ φ false]
      exact hselfeq _ hdK rfl ρ φ
    · rw [run, runT_fixR _ hdK ρ φ false] at hrun
      injection hrun with hrun
      rw [← (Prod.mk.inj hrun).1]
      show piTG _ ρ φ [⟨"n"⟩] [.nat] .nat = _
      rw [piTG_R _ hdK ρ φ, hty]
      rfl
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    rw [hglob]
    exact hMM "R" _ _ (List.mem_singleton.2 rfl)
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    exact absurd (by rw [hc]; rfl) (hcur "R" rfl)
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf
    simp only [gR, fixR, Option.some.injEq, Term.fix.injEq] at hfn
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfn
    exact fixEqAt_R _ ρ hdK args ha
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf
    simp only [gR, fixR, Option.some.injEq, Term.fix.injEq] at hfn
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfn
    rw [hglob]
    refine ⟨hselfeq _ hdK rfl ρ φ, ?_, ?_⟩
    · rw [piTG_R _ hdK ρ φ, hty]; rfl
    · exact hMM "R" _ _ (List.mem_singleton.2 rfl)
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf
    simp only [gR, fixR, Option.some.injEq, Term.fix.injEq] at hfn
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hfn
    exact hret _ hdK
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    simp only [gR, Option.some.injEq] at ht; subst ht; rfl

/-- **`ConstG` at `R`'s program** (PROVED, vacuous: its only definition has a parameter). -/
theorem constG_R (dm : DataModel) (hr : ResolvesTo pq F items) :
    ConstG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin hd
  obtain ⟨rfl, -, -⟩ := atStage_R hr hin
  cases hd

/-- **The links of the top at `R`'s program** (`hlinks` exactly as `consistency_of_master` takes it, at `R`'s program):
PROVED but for TWO facts, `KeepsTabFixR` (whole-machine, the machine lane's) and `RetKindR` (`R`'s function at an
arbitrary forming state returns an unlabelled result; model, read true). -/
theorem hlinks_R (hkt : KeepsTabFixR) (hret : RetKindR) : ∀ items, ResolvesTo pq F items →
    ∀ dm, (∀ d' ∈ indsOf {} F items, dm.covers d') →
      (∀ k, k ≤ items.length → DataFaithful dm (chainDecisions F) (indsOf {} F items)
        (progMeaning dm (chainDecisions F) (indsOf {} F items) (fun _ => .err) {} F (items.take k))) →
      TopLinks dm (chainDecisions F) (indsOf {} F items) F items :=
  fun _ hr dm _ _ => ⟨constG_R dm hr, fixG_R hkt dm hr, globGrow_R hret dm hr⟩

end

end Ochr.Meaning.Steps.Form.Top.RT
