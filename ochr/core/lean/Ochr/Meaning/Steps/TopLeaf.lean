import Ochr.Meaning.Steps.TopRGlob

/-!
# The knot's leaf from the simulation's conclusion, with the goal's meaning kept (lead47; docs/31 D286, D287)

The orchestrator's ruling on D286 (2026-11-28): `TailAt`'s leaf (both forms) and `EvalAt`'s end are to conclude that the
goal's meaning is kept, `hintM { K with Δ := Δ' } ρ' st'.goal = hintM K ρ st.goal`, inside the existential where the
leaf's assignment and `Δ'` live. BEFORE that is built into the general statement, this file tests that the clause, in
exactly that form, is what the knot's leaf consumes: `FixLeafAt` (`Top.FixLeafAt`) with `TailAt`'s conclusion strengthened
by the clause (`TailConclG`) and the start's goal tied to the codomain (`FixStartAt`'s last conjunct, which `knot_step`
holds), from named facts: [Return] (`LeafReturnG`), the leaf's type against the goal read after the pop with N3
(`LeafConvG`), the pop's ends (`LeafPopG`). PROVED for every function with no borrow parameter and a data codomain
(`fixLeafG_of`), so at `D (n : Nat) : Nat by n := match n { Z => Z, S m => S (D m) }` (`fixLeafG_D`).
-/

namespace Ochr.Meaning.Steps.Form.Top.Leaf

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.FixEqDesc Ochr.Meaning.Assembly Ochr.Surface

/-! ## The conclusion with the goal's meaning kept -/

/-- `Out` with the goal's meaning kept (the ruling on docs/31 D286): at the extended context and assignment, the end
state's goal means what the start's goal meant. -/
def OutG (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st st' : MState) (s : SState)
    (x : SM Res) (v : Value) (T? : Option Value) : Prop :=
  ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
    Ext K ρ π st st' ρ' Δ' π' ∧ x s = some (r, s') ∧
    meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧
    (∀ T, T? = some T → StrAgree { K with Δ := Δ' } ρ' T r.2) ∧
    r.2.label = (Value.heldLabel v).map π' ∧
    Pre { K with Δ := Δ' } ρ' (st'.withTempT v T?) ∧
    Rel { K with Δ := Δ' } ρ' φ π' (st'.withTempT v T?) s' ∧
    hintM { K with Δ := Δ' } ρ' st'.goal = hintM K ρ st.goal

/-- `TailOutK` with the goal's meaning kept at the leaf. -/
def TailOutKG (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState) (x : SM Res)
    (k : Value → Value → M Unit) : Prop :=
  ∃ (stl : MState) (v T : Value), (∃ bk stk, Runs (k v T) stl bk () stk) ∧ OutG K ρ φ π st stl s x v (some T) ∧
    Kept st stl

/-- `TailOutE` with the goal's meaning kept at the leaf (at a lemma, the whole of soundness: D286). -/
def TailOutEG (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState) (x : SM Res)
    (k : Value → Value → M Unit) : Prop :=
  ∃ (stl : MState) (v T : Value), (∃ bk stk, Runs (k v T) stl bk () stk) ∧
    (∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      Ext K ρ π st stl ρ' Δ' π' ∧ x s = some (r, s') ∧
      meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) r.2 v = r.1 ∧ StrAgree { K with Δ := Δ' } ρ' T r.2 ∧
      Pre { K with Δ := Δ' } ρ' (stl.withTempT v (some T)) ∧
      hintM { K with Δ := Δ' } ρ' stl.goal = hintM K ρ st.goal) ∧
    Kept st stl

/-- `TailConcl` with the goal's meaning kept at the leaf, in both forms. -/
def TailConclG (K : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (st : MState) (s : SState) (t : Term)
    (x : SM Res) (k : Value → Value → M Unit) : Prop :=
  ((K.D.flags (scopeOf s) t).2 = false → TailOutKG K ρ φ π st s x k) ∧ TailOutEG K ρ φ π st s x k

/-- The strengthened conclusion gives the present one. -/
theorem TailConclG.concl {K : RunCtx} {ρ : Assignment} {φ : Future} {π : Nat → Nat} {st : MState} {s : SState}
    {t : Term} {x : SM Res} {k : Value → Value → M Unit} (h : TailConclG K ρ φ π st s t x k) :
    TailConcl K ρ φ π st s t x k := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨stl, v, T, hk, ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr, -⟩, hK⟩ := h.1 hf
    exact ⟨stl, v, T, hk, ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hl, hp, hr⟩, hK⟩
  · obtain ⟨stl, v, T, hk, ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hp, -⟩, hK⟩ := h.2
    exact ⟨stl, v, T, hk, ⟨ρ', Δ', π', r, s', he, hx, hm, ha, hp⟩, hK⟩

/-! ## The named facts the leaf uses -/

/-- **[Return] at the leaf** (MIXED; READ TRUE, unproved): `fixCont`'s first action, `wholeReturned v`, succeeds only at a
value holding no `⊥` (checker, `Machine.wholeReturned`), and a value holding no `⊥` never means `⊥` (model: `meanV` gives
`.moved` only at `.bot`). -/
def LeafReturnG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS), meanV K ρ φ h v ≠ .moved

/-- **The leaf's type against the goal** (MIXED; READ TRUE, unproved): `fixCont` compares the leaf's type `T` with the
goal it reads after `bodyReturns`, the pop and `popTemp`, which is the leaf's (checker: none of them writes `goal`), and
`conv` answers "equal"; N3 (`Conv.ConvTypeStmt`, the conversion lane's: a type checked against a type means the same at
every assignment meeting the state) makes the two types' meanings equal at the leaf's assignment. -/
def LeafConvG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment), Pre K ρ (stl.withTempT v (some T)) →
      (Value.tyS K.dm K.M K.Γ ρ T).m = (hintM K ρ stl.goal).m

/-- **The pop at the leaf, at a data codomain with no borrow parameter** (MIXED; READ TRUE, unproved; the paper's [Def]
"`pop(Ω', v)` succeeds"): `fixCont`'s `popFrame` succeeded at the leaf, where the checker's state with the result in
flight is related to the reference's; so the reference's ends after the body (`fixBodyAt`'s `EndsOk` over every label
live at the run's end, the result holding none) pass, at any context with the leaf's data model and declarations. -/
def LeafPopG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name v T) stl bk () stk →
    ∀ (K K₁ : RunCtx) (ρ : Assignment) (φ : Future) (π : Nat → Nat) (s' : SState),
      K₁.dm = K.dm → K₁.Γ = K.Γ →
      Pre K ρ (stl.withTempT v (some T)) → Rel K ρ φ π (stl.withTempT v (some T)) s' →
      Strict.SGood K.dm K.Γ φ s' →
      EndsOk K₁ φ (s'.liveLabels.filter fun l => l ≥ 0 ∧ some l ≠ (none : Option Nat)) s'

/-! ## The leaf -/

/-- The closure's frame pushes no cell for a parameter that is not a borrow. -/
theorem foldl_fixStep_cells (fb : List PBind × PBind) :
    ∀ (l : List (Sem × PiDom)) (s : SState) (acc : List Sem) (cells : List Pos), (∀ p ∈ l, p.2.isRef = false) →
      (l.foldl (fixStep fb) (s, acc, cells)).2.2 = cells
  | [], _, _, _, _ => rfl
  | p :: l, s, acc, cells, h => by
    simp only [List.foldl_cons]
    have hp : p.2.isRef = false := h p (List.mem_cons_self ..)
    unfold fixStep
    simp only [hp, Bool.false_eq_true, if_false]
    exact foldl_fixStep_cells fb l _ _ cells fun q hq => h q (List.mem_cons_of_mem _ hq)

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl}

/-- **`FixLeafAt` with the goal's meaning kept, at every function with no borrow parameter and a data codomain**
(PROVED from the clause and three named facts). Its parts, each used: the leaf (`TailConclG`'s full form, the body read
as data); the reference's result is the stage's run's (`heq`), whose result is good (the fundamental lemma, `hfund`);
[Return] (`LeafReturnG`) excludes `⊥`; the result's type is the leaf type's meaning (`StrAgree`), which is the leaf goal's
(`LeafConvG`: `fixCont`'s `conv`, N3), which is the start's goal's (the CLAUSE), which is the codomain at `a`
(`FixStartAt`'s hint, `hhint`; the hint `fixCod` is `outG`'s codomain, by definition); the pop's ends (`LeafPopG`); no
cell, so no final. -/
theorem fixLeafG_of (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (d : Def) (st' : MState) (w : FixWit)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (hnoref : ∀ p ∈ psG (P.ctx dm D Γ st') ρ φ d.doms, p.isRef = false)
    (hdata : (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = false)
    (hpre : Pre (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀)
    (hfl : ((ctxBΔ dm D Γ P d st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)) d.body).2 = false)
    (hT : TailConclG (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) d.body
      (runT (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀.goal) d.body)
      (fixCont w.n d.name))
    (hhint : hintM (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀.goal = (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a)
    (heq : runT (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀.goal) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) =
      runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a))
    (hfund : ∀ r s', runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod).2.1 a) d.body
        (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) = some (r, s') →
      Strict.GoodRes dm.read r ∧ Strict.SGood dm Γ φ s')
    (hcod : (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a ≠ TyM.err) :
    ∃ o, stG (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body (b + 1) a = some o ∧
      OutGood' dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod) a o := by
  obtain ⟨stl, v, T, ⟨bk, stk, hk⟩, ⟨ρ', Δ', π', r, s', -, hx, hmv, hstr, -, hpl, hrl, hgoal⟩, -⟩ := hT.1 hfl
  rw [heq] at hx
  obtain ⟨hgood, hsg⟩ := hfund r s' hx
  -- the result's type is the codomain at `a`
  have hty : r.2.m = (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a := by
    rw [← hstr T rfl, hConv _ _ v T stl stk bk hk _ ρ' hpl, hgoal, hhint]
    rfl
  have hmem : r.1 ∈ₛ[dm.read] (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a := by
    rcases hgood with h | h | ⟨he, -⟩
    · rw [← hty]; exact h
    · exact absurd (hmv.trans h) (hRet _ _ v T stl stk bk hk _ ρ' _ r.2)
    · exact absurd (hty ▸ he) hcod
  have hcells : ∀ s₀ : SState, ((a.zip (psG (P.ctx dm D Γ st') ρ φ d.doms)).foldl
      (fixStep (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod)) (s₀, [], [])).2.2 = [] := fun s₀ =>
    foldl_fixStep_cells (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod)
      (a.zip (psG (P.ctx dm D Γ st') ρ φ d.doms)) s₀ [] [] (fun p hp => hnoref p.2 (List.of_mem_zip hp).2)
  rw [stG_succ]
  unfold fixBodyAt
  dsimp only
  generalize hF : List.foldl (fixStep (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod)) _
    (a.zip (psG (P.ctx dm D Γ st') ρ φ d.doms)) = F
  have hs₂ : startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a = F.1 := by rw [← hF]; rfl
  have hc₂ : F.2.2 = [] := by rw [← hF]; exact hcells _
  obtain ⟨s₂, acc, cells⟩ := F
  simp only at hs₂ hc₂
  subst hc₂
  rw [← hs₂, hx]
  simp only [hdata, Bool.false_eq_true, if_false]
  have hends := (hPop w.n d.name v T stl stk bk hk { ctxBΔ dm D Γ P d st' ρ φ b Δa with Δ := Δ' } (P.ctx dm D Γ st') ρ' φ π'
    s' rfl rfl hpl hrl hsg)
  have hkeep : (if (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = true then r.2.label else none) = none := by
    rw [hdata]; rfl
  rw [hkeep, if_pos hends]
  refine ⟨_, rfl, ⟨hmem, fun i p hi hr => ?_⟩, fun h => ?_, ?_⟩
  · rw [hnoref p (List.mem_of_getElem? hi)] at hr; cases hr
  · rw [hdata] at h; cases h
  · simp only [List.map_nil, List.length_nil]
    rw [eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro p hp; simp [hnoref p hp]


/-! ## At `D` -/

/-- `D`'s body: `match n { Z => Z, S m => S (D m) }`, the recursive call through its own binding (`#1`), its argument the
predecessor field of the parameter, under the core successor (the juxtaposition `S (D m)` resolves to it; the call form
`S(a)` resolves to a closure call of the surface's `succFn`, docs/31 D258). Its `S` leaf is `S(⌈D(σ1)⌉)`. -/
def bodyD : Term := .matchNat (.var 0) .zero (.succ (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false))

/-- `D` as a core definition. -/
def defD : Def := { name := "D", hs := [⟨"n"⟩], doms := [.nat], cod := .nat, dec := some 0, body := bodyD }

-- The program of the test: `D` after the library. The concrete syntax has no juxtaposition for `S` (`S(a)` is a call of
-- the surface's `succFn`, a closure call, docs/31 D258), so the declaration is written as surface syntax directly, its
-- successor the juxtaposition form `.app "S" [_]`, which the surface resolves to the core `S` (`Surface.resolveF`).
/-- `D`, as a surface declaration. -/
def sdD : SDecl :=
  { name := "D", params := [("n", .ident "Nat")], ret := .ident "Nat", dec := some "n", expectAccept := true,
    body := .matchGen (.ident "n") [("Z", [], .ident "Z"), ("S", ["m"], .app "S" [.call (.ident "D") [.ident "m"]])] }

/-- The program: the library, then `D`. -/
def pqD : Program := Prelude.decls ++ [sdD]

/-- The resolution of `D` is `defD`. -/
def isDItem : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.defn ⟨n, [h], [.nat], .nat, some 0,
      .matchNat (.var 0) .zero (.succ (.call (.place (.var 1)) [.place (.proj 0 (.var 0))] false)), none⟩)) =>
    n == "D" && h.name == "n"
  | _ => false

#guard isDItem (runResolve pqD sdD 100000 false).1
-- the checker accepts the program (every verdict as expected)
#guard Ochr.Consistency.accepts {} 2000000 pqD

/-- **The knot's leaf at `D`, from the simulation's conclusion with the goal's meaning kept** (PROVED from the clause and
named facts; docs/31 D287): stage `b + 1` good at `a`. ASSUMES: the clause (in `TailConclG`, the hypothesis the ruling
makes a conclusion of `TailAt`); `LeafReturnG`, `LeafConvG`, `LeafPopG` (MIXED, read true, unproved); two TABLE facts
at `D`'s code (the aligned table reads the type `Nat` as data, and `D`'s body at its start as data: read true); and
what `knot_step` holds there (`FixStartAt`'s hint, the run being the stage's, the fundamental lemma at it). -/
theorem fixLeafG_D (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (st' : MState) (w : FixWit) (hT0 : (D st').typeDecl [] .nat = .other)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (hpre : Pre (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀)
    (hfl : ((ctxBΔ dm D Γ P defD st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a)) defD.body).2 = false)
    (hT : TailConclG (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a) defD.body
      (runT (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀.goal)
        defD.body)
      (fixCont w.n defD.name))
    (hhint : hintM (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀.goal =
      (fbG (P.ctx dm D Γ st') ρ φ defD.doms defD.cod).2.1 a)
    (heq : runT (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀.goal)
        defD.body (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a) =
      runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ defD.doms defD.cod).2.1 a) defD.body
        (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a))
    (hfund : ∀ r s', runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ defD.doms defD.cod).2.1 a) defD.body
        (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a) = some (r, s') →
      Strict.GoodRes dm.read r ∧ Strict.SGood dm Γ φ s') :
    ∃ o, stG (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body (b + 1) a = some o ∧
      OutGood' dm.read (psG (P.ctx dm D Γ st') ρ φ defD.doms) (outG (P.ctx dm D Γ st') ρ φ defD.doms defD.cod) a o := by
  have hps : psG (P.ctx dm D Γ st') ρ φ defD.doms = ColumnI.psI :=
    ColumnI.runDoms_nat _ ρ φ formG (by
      show (D st').paramDecls [] [.nat] = [.other]
      simp [Decisions.paramDecls, Decisions.teleDecls, hT0])
  have hout : outG (P.ctx dm D Γ st') ρ φ defD.doms defD.cod = ColumnI.outI := ColumnI.codOf_nat _ ρ φ formG _ _
  refine fixLeafG_of hRet hConv hPop P defD st' w ρ ρa Δa φ π b a (by rw [hps]; intro p hp; simp [ColumnI.psI] at hp; subst hp; rfl)
    (by rw [hout]; rfl) hpre hfl hT hhint heq hfund (by
      rw [hout]; intro h; injection h with h1; exact PEmpty.elim (cast h1 (0 : Nat)))

end

end Ochr.Meaning.Steps.Form.Top.Leaf
