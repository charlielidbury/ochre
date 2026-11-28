import Ochr.Meaning.Steps.TopRGlob

/-!
# The knot's leaf from the simulation's conclusion, with the goal's meaning kept (lead47, lead48; docs/31 D286, D287, D290)

The orchestrator's ruling on D286 (2026-11-28): `TailAt`'s leaf (both forms) and `EvalAt`'s end conclude that the goal's
meaning is kept, `hintM { K with Δ := Δ' } ρ' st'.goal = hintM K ρ st.goal`, inside the existential where the leaf's
assignment and `Δ'` live. lead47 tested the clause here as a hypothesis (D287); lead48 built it into the general
statement (D290), so this file now takes `TailAt`'s own conclusion (`TailConcl`): `FixLeafAt` (`Top.FixLeafAt`, which since
D290 also takes `FixStartAt`'s hint, the start's goal tied to the codomain, which `knot_step` holds) from named facts:
[Return] (`LeafReturnG`), the leaf's type against the goal read after the pop with N3 (`LeafConvG`), the pop's ends
(`LeafPopG`). PROVED for every function with no borrow parameter and a data codomain whose body the table reads as data
(`fixLeafG_of`), so at `D (n : Nat) : Nat by n := match n { Z => Z, S m => S (D m) }` (`fixLeafG_D`).
-/

namespace Ochr.Meaning.Steps.Form.Top.Leaf

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Meaning.Steps.Form.FixEqDesc Ochr.Meaning.Assembly Ochr.Surface

/-! ## The conclusion with the goal's meaning kept

Built into the general statement by lead48 (docs/31 D290): `TailAt`'s conclusion `TailConcl` carries the clause in both
forms (`TailOutK` through `Master.OutG`, `TailOutE` directly), so the leaf below takes `TailAt`'s own conclusion and no
longer assumes the clause. (Before, this file stated the strengthened forms `OutG`, `TailOutKG`, `TailOutEG` and
`TailConclG` here, as a hypothesis of the leaf, D287.) -/

/-! ## The named facts the leaf uses -/

/-- **[Return] at the leaf, as first stated** (lead47): FALSE (lead48, docs/31 D291). It asked the leaf's value not to mean
`⊥` at EVERY assignment; at a leaf returning an unknown (`def Id1 (n : Nat) : Nat := n`: the leaf is `σ0`, `fixCont`
succeeds there, `LeafAttack`'s guard) an assignment sending `σ0` to `.moved` makes it mean `⊥` (`leafReturnG_old_false`).
Its one consumer reads it at the leaf's own assignment, which meets `Pre`; restated so (`LeafReturnG`). -/
def LeafReturnG_old : Prop :=
  ∀ (n : Nat) (name : String) (start : Option Env) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name start v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS), meanV K ρ φ h v ≠ .moved

/-- The first form is false wherever `fixCont` succeeds at a leaf whose value is an unknown. -/
theorem leafReturnG_old_false {n : Nat} {name : String} {start : Option Env} {σ : Nat} {T : Value} {stl stk : MState} {bk : Nat}
    (hk : Runs (fixCont n name start (.abs σ) T) stl bk () stk) (K : RunCtx) (φ : Future) (h : TyS) :
    ¬ LeafReturnG_old := fun hR =>
  hR n name start (.abs σ) T stl stk bk hk K (fun _ => .moved) φ h (by rw [Ochr.Meaning.Attack.meanV_abs])

/-- **[Return] at the leaf** (MIXED; READ TRUE, unproved; RESTATED by lead48, docs/31 D291: at an assignment meeting the
leaf's state, as `LeafConvG` is): the leaf's value means no `⊥`. Its parts: the value is whole (checker: `wholeReturned`
tests a returned borrow's content; a data value in flight is whole, every read of a place requiring its content whole,
[Read], and a constructor's or a call's result being built from whole parts); a whole value means no `⊥` at an assignment
that meets the state (model: `meanV` gives `.moved` at `.bot`, and at an unknown its assignment's value, a member of its
type by `TypedAssignment`). -/
def LeafReturnG : Prop :=
  ∀ (n : Nat) (name : String) (start : Option Env) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name start v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS), Pre K ρ (stl.withTempT v (some T)) →
      meanV K ρ φ h v ≠ .moved

/-- **The leaf's type against the goal** (MIXED; READ TRUE, unproved): `fixCont` compares the leaf's type `T` with the
goal it reads after `bodyReturns`, the pop and `popTemp`, which is the leaf's (checker: none of them writes `goal`), and
`conv` answers "equal"; N3 (`Conv.ConvTypeStmt`, the conversion lane's: a type checked against a type means the same at
every assignment meeting the state) makes the two types' meanings equal at the leaf's assignment. DERIVED (lead48, docs/31
D291, `Steps/TopLeafConv.leafConvG_of`) from the checker's part (`LeafGoalPopG`, read true, attacked), N3's hypotheses
(`N3Hyps`, the conversion lane's) and N3's side conditions (`LeafSideG`). -/
def LeafConvG : Prop :=
  ∀ (n : Nat) (name : String) (start : Option Env) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name start v T) stl bk () stk →
    ∀ (K : RunCtx) (ρ : Assignment), Pre K ρ (stl.withTempT v (some T)) →
      (Value.tyS K.dm K.M K.Γ ρ T).m = (hintM K ρ stl.goal).m

/-- **The pop at the leaf, at a data codomain with no borrow parameter** (MIXED; READ TRUE, unproved; the paper's [Def]
"`pop(Ω', v)` succeeds"): `fixCont`'s `popFrame` succeeded at the leaf, where the checker's state with the result in
flight is related to the reference's; so the reference's ends after the body (`fixBodyAt`'s `EndsOk` over every label
live at the run's end, the result holding none) pass, at any context with the leaf's data model and declarations. -/
def LeafPopG : Prop :=
  ∀ (n : Nat) (name : String) (v T : Value) (stl stk : MState) (bk : Nat),
    Runs (fixCont n name none v T) stl bk () stk →
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

/-- One step of the closure's frame pushes a cell exactly at a borrow parameter. -/
theorem fixStep_cells_length (fb : List PBind × PBind) (sa : SState × List Sem × List Pos) (p : Sem × PiDom) :
    (fixStep fb sa p).2.2.length = sa.2.2.length + (if p.2.isRef then 1 else 0) := by
  obtain ⟨s, acc, cells⟩ := sa
  unfold fixStep
  cases p.2.isRef <;> simp

/-- The closure's frame pushes one cell per borrow parameter. -/
theorem foldl_fixStep_cells_length (fb : List PBind × PBind) :
    ∀ (l : List (Sem × PiDom)) (sa : SState × List Sem × List Pos),
      (l.foldl (fixStep fb) sa).2.2.length = sa.2.2.length + (l.filter (·.2.isRef)).length
  | [], _ => rfl
  | p :: l, sa => by
    rw [List.foldl_cons, foldl_fixStep_cells_length fb l, fixStep_cells_length]
    cases hp : p.2.isRef <;> simp [List.filter_cons, hp] <;> omega

/-- Zipping arguments with as many domains keeps the count of borrow domains. -/
theorem zip_filter_isRef_length : ∀ (a : List Sem) (ps : List PiDom), a.length = ps.length →
    ((a.zip ps).filter (·.2.isRef)).length = (ps.filter (·.isRef)).length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, p :: ps, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := zip_filter_isRef_length a ps h
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp_all

section
variable {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl}

/-- **`FixLeafAt` with the goal's meaning kept, at every function with no borrow parameter and a data codomain**
(PROVED from `TailAt`'s conclusion and three named facts). Its parts, each used: the leaf (`TailConcl`'s full form, the body read
as data); the reference's result is the stage's run's (`heq`), whose result is good (the fundamental lemma, `hfund`);
[Return] (`LeafReturnG`) excludes `⊥`; the result's type is the leaf type's meaning (`StrAgree`), which is the leaf goal's
(`LeafConvG`: `fixCont`'s `conv`, N3), which is the start's goal's (the CLAUSE), which is the codomain at `a`
(`FixStartAt`'s hint, `hhint`; the hint `fixCod` is `outG`'s codomain, by definition); the pop's ends (`LeafPopG`); no
cell, so no final. -/
theorem fixLeafG_of (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (d : Def) (st' : MState) (w : FixWit) (hst : w.start = none)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (hnoref : ∀ p ∈ psG (P.ctx dm D Γ st') ρ φ d.doms, p.isRef = false)
    (hdata : (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = false)
    (hpre : Pre (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀)
    (hfl : ((ctxBΔ dm D Γ P d st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)) d.body).2 = false)
    (hT : TailConcl (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) d.body
      (runT (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀.goal) d.body)
      (fixCont w.n d.name w.start))
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
    rw [← hstr T rfl, hConv _ _ _ v T stl stk bk hk _ ρ' hpl, hgoal, hhint]
    rfl
  have hmem : r.1 ∈ₛ[dm.read] (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a := by
    rcases hgood with h | h | ⟨he, -⟩
    · rw [← hty]; exact h
    · exact absurd (hmv.trans h) (hRet _ _ _ v T stl stk bk hk _ ρ' _ r.2 hpl)
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
  have hends := (hPop w.n d.name v T stl stk bk (hst ▸ hk) { ctxBΔ dm D Γ P d st' ρ φ b Δa with Δ := Δ' } (P.ctx dm D Γ st') ρ' φ π'
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

/-- **The knot's leaf at `D`, from the simulation's conclusion with the goal's meaning kept** (PROVED from `TailAt`'s
conclusion and named facts; docs/31 D287, D290): stage `b + 1` good at `a`. ASSUMES: `LeafReturnG`, `LeafConvG`, `LeafPopG` (MIXED, read
true, unproved); the clause is no longer assumed (it is `TailAt`'s conclusion since D290); two TABLE facts
at `D`'s code (the aligned table reads the type `Nat` as data, and `D`'s body at its start as data: read true); and
what `knot_step` holds there (`FixStartAt`'s hint, the run being the stage's, the fundamental lemma at it). -/
theorem fixLeafG_D (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (st' : MState) (w : FixWit) (hst : w.start = none) (hT0 : (D st').typeDecl [] .nat = .other)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (hpre : Pre (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀)
    (hfl : ((ctxBΔ dm D Γ P defD st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a)) defD.body).2 = false)
    (hT : TailConcl (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a) defD.body
      (runT (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P defD st' ρ φ b Δa) ρa w.st₀.goal)
        defD.body)
      (fixCont w.n defD.name w.start))
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
  refine fixLeafG_of hRet hConv hPop P defD st' w hst ρ ρa Δa φ π b a (by rw [hps]; intro p hp; simp [ColumnI.psI] at hp; subst hp; rfl)
    (by rw [hout]; rfl) hpre hfl hT hhint heq hfund (by
      rw [hout]; intro h; injection h with h1; exact PEmpty.elim (cast h1 (0 : Nat)))

/-- **The link `FixLeafAt` itself, at a function with no borrow parameter and a data codomain** (PROVED from the three
named facts and three facts about the definition; docs/31 D290): `fixLeafG_of` at every quantified argument, the
link's own hypotheses supplying the start's `Pre`, the hint, `TailAt`'s conclusion, the run's congruence and the
fundamental lemma. The facts about the definition: its domains are not borrows and its codomain is data (MODEL, by
computing `psG`, `outG`), the table reads its body as data at every start (TABLE), and the codomain at member arguments
is not `err` (MODEL). -/
theorem fixLeafAt_of (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (d : Def) (st' : MState) (w : FixWit) (hst : w.start = none)
    (hnoref : ∀ ρ φ, ∀ p ∈ psG (P.ctx dm D Γ st') ρ φ d.doms, p.isRef = false)
    (hdata : ∀ ρ φ, (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = false)
    (hfl : ∀ ρ φ b Δa a, ((ctxBΔ dm D Γ P d st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)) d.body).2 = false)
    (hcod : ∀ ρ φ a, DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a →
      (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a ≠ TyM.err) :
    FixLeafAt dm D Γ P d st' w := by
  intro ρ ρa Δa φ π b a ha _ hpre _ hhint hT heq hfund
  exact fixLeafG_of hRet hConv hPop P d st' w hst ρ ρa Δa φ π b a (hnoref ρ φ) (hdata ρ φ) hpre (hfl ρ φ b Δa a) hT hhint
    heq hfund (hcod ρ φ a ha)

/-- **The link `FixLeafAt` at `D`** (PROVED from `LeafReturnG`, `LeafConvG`, `LeafPopG` and two TABLE facts at `D`'s
code, each read true: the type `Nat` read as data, `D`'s body read as data at every start; docs/31 D290). -/
theorem fixLeafAt_D (hRet : LeafReturnG) (hConv : LeafConvG) (hPop : LeafPopG)
    (P : ProgState) (st' : MState) (w : FixWit) (hst : w.start = none) (hT0 : (D st').typeDecl [] .nat = .other)
    (hfl : ∀ ρ φ b Δa a, ((ctxBΔ dm D Γ P defD st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ defD.hs defD.doms defD.cod defD.dec defD.body b a)) defD.body).2 = false) :
    FixLeafAt dm D Γ P defD st' w := by
  intro ρ ρa Δa φ π b a _ _ hpre _ hhint hT heq hfund
  exact fixLeafG_D hRet hConv hPop P st' w hst hT0 ρ ρa Δa φ π b a hpre (hfl ρ φ b Δa a) hT hhint heq hfund


/-! ## A function with borrow parameters: the pop leaves members in the cells (`Z0`) -/

/-- The closure's frame at the arguments with its cells: `startAt`'s fold, kept whole (its first component is `startAt`). -/
noncomputable def startFold (K : RunCtx) (ρ : Assignment) (φ : Future) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (b : Nat) (a : List Sem) : SState × List Sem × List Pos :=
  let G := stageClo K ρ φ hs ds c dec body b
  let sb : SBinding := ⟨.plain G.2.m, fun _ => G.1, .pi (fbG K ρ φ ds c).2.2, none⟩
  (a.zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c)) (formG.under.pushBind sb, [], [])

theorem startAt_fold (K : RunCtx) (ρ : Assignment) (φ : Future) (hs : List Hint) (ds : List Term) (c : Term)
    (dec : Option Nat) (body : Term) (b : Nat) (a : List Sem) :
    startAt K ρ φ hs ds c dec body b a = (startFold K ρ φ hs ds c dec body b a).1 := rfl

/-- **The pop at the leaf, with the cells' finals** (MIXED; READ TRUE, unproved; per definition, as `FixLeafAt` is; the paper's
[Def] "`pop(Ω', v)` succeeds" and [Return] at the borrow parameters): at the leaf, `fixCont`'s pop succeeded and the
checker's state with the result in flight is related to the reference's `s'`; so the reference's ends after the body pass,
and after them each borrow parameter's cell holds, at every future, a member of the parameter's content type (the
checker's pop ends each parameter's borrow and its cell receives the final content, whole by [Return] at the borrow; the
relation carries that to the reference's cell). At a data codomain: the result holds no label (`keep` is `none`). -/
def LeafPopAt (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (P : ProgState) (d : Def) (st' : MState)
    (w : FixWit) : Prop :=
  ∀ (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (b : Nat) (a : List Sem) (v T : Value) (stl stk : MState) (bk : Nat)
    (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (s' : SState),
    DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a →
    Runs (fixCont w.n d.name w.start v T) stl bk () stk →
    Pre { ctxBΔ dm D Γ P d st' ρ φ b Δa with Δ := Δ' } ρ' (stl.withTempT v (some T)) →
    Rel { ctxBΔ dm D Γ P d st' ρ φ b Δa with Δ := Δ' } ρ' φ π' (stl.withTempT v (some T)) s' →
    Strict.SGood dm Γ φ s' →
    EndsOk (P.ctx dm D Γ st') φ (s'.liveLabels.filter fun l => l ≥ 0 ∧ some l ≠ (none : Option Nat)) s' ∧
    ∀ (i : Nat) (dd : PiDom), (psG (P.ctx dm D Γ st') ρ φ d.doms)[i]? = some dd → dd.isRef = true →
      ∃ f, ((startFold (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a).2.2.map fun c =>
          ((s'.liveLabels.filter fun l => l ≥ 0 ∧ some l ≠ (none : Option Nat)).foldl SState.endLabel s').valAt c)[
            (((psG (P.ctx dm D Γ st') ρ φ d.doms).take i).filter (·.isRef)).length]? = some f ∧
        ∀ ψ, f ψ ∈ₛ[dm.read] dd.dom (a.take i)

/-- **`FixLeafAt` with the goal's meaning kept, at every function with a data codomain** (borrow parameters allowed;
PROVED from `TailAt`'s conclusion and named facts): `fixLeafG_of` with the pop's finals (`LeafPopAt`) for the cells. -/
theorem fixLeafG_ofRef (hRet : LeafReturnG) (hConv : LeafConvG)
    (P : ProgState) (d : Def) (st' : MState) (w : FixWit) (hPop : LeafPopAt dm D Γ P d st' w)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (ha : DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ d.doms) a)
    (hdata : (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = false)
    (hfl : ((ctxBΔ dm D Γ P d st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a)) d.body).2 = false)
    (hT : TailConcl (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a) d.body
      (runT (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P d st' ρ φ b Δa) ρa w.st₀.goal) d.body)
      (fixCont w.n d.name w.start))
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
  have hty : r.2.m = (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a := by
    rw [← hstr T rfl, hConv _ _ _ v T stl stk bk hk _ ρ' hpl, hgoal, hhint]
    rfl
  have hmem : r.1 ∈ₛ[dm.read] (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).cod a := by
    rcases hgood with h | h | ⟨he, -⟩
    · rw [← hty]; exact h
    · exact absurd (hmv.trans h) (hRet _ _ _ v T stl stk bk hk _ ρ' _ r.2 hpl)
    · exact absurd (hty ▸ he) hcod
  obtain ⟨hends, hfin⟩ := hPop ρ ρa Δa φ b a v T stl stk bk ρ' Δ' π' s' ha hk hpl hrl hsg
  rw [stG_succ]
  unfold fixBodyAt
  dsimp only
  generalize hF : List.foldl (fixStep (fbG (P.ctx dm D Γ st') ρ φ d.doms d.cod)) _
    (a.zip (psG (P.ctx dm D Γ st') ρ φ d.doms)) = F
  have hSF : startFold (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a = F := by rw [← hF]; rfl
  obtain ⟨s₂, acc, cells⟩ := F
  have hs₂ : startAt (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a = s₂ := by
    rw [startAt_fold, hSF]
  have hlen : cells.length = ((psG (P.ctx dm D Γ st') ρ φ d.doms).filter (·.isRef)).length := by
    have e : cells = (startFold (P.ctx dm D Γ st') ρ φ d.hs d.doms d.cod d.dec d.body b a).2.2 := by rw [hSF]
    rw [e]; unfold startFold; dsimp only
    rw [foldl_fixStep_cells_length]
    simp only [List.length_nil, Nat.zero_add]
    exact zip_filter_isRef_length a _ ha.1
  rw [hSF] at hfin
  simp only at hfin
  rw [← hs₂, hx]
  simp only [hdata, Bool.false_eq_true, if_false]
  have hkeep : (if (outG (P.ctx dm D Γ st') ρ φ d.doms d.cod).isRef = true then r.2.label else none) = none := by
    rw [hdata]; rfl
  rw [hkeep, if_pos hends]
  refine ⟨_, rfl, ⟨hmem, fun i dd hi hr => ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨f, hf, hm⟩ := hfin i dd hi hr
    exact ⟨f, hf, fun ψ _ => hm ψ⟩
  · rw [hdata] at h; cases h
  · simp only [List.length_map]; exact hlen


/-! ## At `Z0` -/

-- The program of the test: `Z0` after the library, accepted (the `ochr` block asserts it), resolved to `defZ0`.
open Ochr.Test in
ochr TopZ0P {
  def Z0 (x : &Nat) : Unit by x := match *x { Z => (), S p => Z0(&p) }
}

/-- `Z0`'s body: `match *x { Z => (), S p => Z0(&p) }`, the recursive call through its own binding, its argument a
borrow of the predecessor field behind the parameter. -/
def bodyZ0 : Term := .matchNat (.deref (.var 0)) .tt (.call (.place (.var 1)) [.borrow (.proj 0 (.deref (.var 0)))] false)

/-- `Z0` as a core definition. -/
def defZ0 : Def := { name := "Z0", hs := [⟨"x"⟩], doms := [.ref .nat], cod := .unit, dec := some 0, body := bodyZ0 }

/-- The resolution of `Z0` is `defZ0`. -/
def isZ0Item : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.defn ⟨n, [h], [.ref .nat], .unit, some 0, b, none⟩)) => n == "Z0" && h.name == "x" && b == bodyZ0
  | _ => false

#guard isZ0Item (runResolve (Prelude.decls ++ TopZ0P.decls) ((Prelude.decls ++ TopZ0P.decls).getD 4 default) 100000 false).1

/-- **The knot's leaf at `Z0`, from the simulation's conclusion with the goal's meaning kept** (PROVED from `TailAt`'s
conclusion and named facts; docs/31 D289, D290): stage `b + 1` good at `a`, its final content in the cell a member of `Nat` at every future.
ASSUMES: `LeafReturnG`, `LeafConvG` (MIXED, read true; the clause is `TailAt`'s conclusion since D290); `LeafPopAt` at `Z0` (MIXED, read
true: the pop's ends pass and the cell holds a member of `Nat`, from the checker's pop through the relation at the leaf);
the TABLE fact that `Z0`'s body at its start is read as data; and what `knot_step` holds there. -/
theorem fixLeafG_Z0 (hRet : LeafReturnG) (hConv : LeafConvG) (P : ProgState) (st' : MState) (w : FixWit)
    (hPop : LeafPopAt dm D Γ P defZ0 st' w)
    (ρ ρa : Assignment) (Δa : Nat → TyS) (φ : Future) (π : Nat → Nat) (b : Nat) (a : List Sem)
    (ha : DomMembers dm.read (psG (P.ctx dm D Γ st') ρ φ defZ0.doms) a)
    (hfl : ((ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a)) defZ0.body).2 = false)
    (hT : TailConcl (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa φ π w.st₀
      (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a) defZ0.body
      (runT (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa w.st₀.goal)
        defZ0.body)
      (fixCont w.n defZ0.name w.start))
    (hhint : hintM (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa w.st₀.goal =
      (fbG (P.ctx dm D Γ st') ρ φ defZ0.doms defZ0.cod).2.1 a)
    (heq : runT (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa φ true (hintM (ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa) ρa w.st₀.goal)
        defZ0.body (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a) =
      runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ defZ0.doms defZ0.cod).2.1 a) defZ0.body
        (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a))
    (hfund : ∀ r s', runT (P.ctx dm D Γ st') ρ φ true ((fbG (P.ctx dm D Γ st') ρ φ defZ0.doms defZ0.cod).2.1 a) defZ0.body
        (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a) = some (r, s') →
      Strict.GoodRes dm.read r ∧ Strict.SGood dm Γ φ s') :
    ∃ o, stG (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body (b + 1) a = some o ∧
      OutGood' dm.read (psG (P.ctx dm D Γ st') ρ φ defZ0.doms) (outG (P.ctx dm D Γ st') ρ φ defZ0.doms defZ0.cod) a o := by
  have hcod : (outG (P.ctx dm D Γ st') ρ φ defZ0.doms defZ0.cod).cod a = TyM.unit := by
    unfold outG
    simp only [defZ0, codOf]
    rw [run, runT]; rfl
  refine fixLeafG_ofRef hRet hConv P defZ0 st' w hPop ρ ρa Δa φ π b a ha rfl hfl hT hhint heq hfund ?_
  rw [hcod]; intro h; injection h with h1; exact PEmpty.elim (cast h1 ())

/-- **The link `FixLeafAt` at `Z0`** (a borrow parameter; PROVED from `LeafReturnG`, `LeafConvG`, `LeafPopAt` at `Z0`, and
the TABLE fact that `Z0`'s body is read as data at every start; docs/31 D290). -/
theorem fixLeafAt_Z0 (hRet : LeafReturnG) (hConv : LeafConvG) (P : ProgState) (st' : MState) (w : FixWit)
    (hPop : LeafPopAt dm D Γ P defZ0 st' w)
    (hfl : ∀ ρ φ b Δa a, ((ctxBΔ dm D Γ P defZ0 st' ρ φ b Δa).D.flags
      (scopeOf (startAt (P.ctx dm D Γ st') ρ φ defZ0.hs defZ0.doms defZ0.cod defZ0.dec defZ0.body b a)) defZ0.body).2 =
        false) :
    FixLeafAt dm D Γ P defZ0 st' w := by
  intro ρ ρa Δa φ π b a ha _ _ _ hhint hT heq hfund
  exact fixLeafG_Z0 hRet hConv P st' w hPop ρ ρa Δa φ π b a ha (hfl ρ φ b Δa a) hT hhint heq hfund

end

end Ochr.Meaning.Steps.Form.Top.Leaf
