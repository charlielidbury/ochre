import Ochr.Meaning.Steps.TopAttack
import Ochr.Meaning.Steps.Machine.ConstRunJ

/-!
# The acceptance test of the top at one program (lead45, 2026-11-28; docs/31 D258 on)

`consistency_of_master`'s hypotheses other than the 32 steps, at ONE real program: the library (`Pair`, `False`,
`True`, `And`) and one constant. Everything here is kernel-checked; what could not be proved is named in docs/31 D258.

**The program.** The brief's `def one : Nat := S(Z)` is NOT the constant `S(Z)` in the core: the surface reads `S(…)`,
written as a call, as a call of the closure `succFn = fix _ (n : Nat) : Nat := S(n)` (`Surface.resolve`, D124), so its
body is `succFn(Z)`, a λ formed and called in place (guarded below). Its route through the top needs the step for a
call whose head is a closure (not stated: `AllSteps.call`'s non-global heads are open, D247) and the step for a `fix`
formed in a body (`StepFix` at a λ, FALSE until main's D148 and the model's clause of R-dec, D255). The literal `1`
resolves to the core's `S(Z)` (`Term.ofNat`), which is `ProgSanity.oneDef`; the test is carried out at that program,
`def one : Nat := 1`, whose body needs only the steps for `S` and `Z`.

**Why not by computation alone.** The kernel cannot evaluate the library's check: `checkInd` of `Pair` (and `And`)
reads its parameters' places, and every place access goes through `Machine.firstLiveLoanOnPath`, defined by
well-founded recursion (`termination_by v ss => (ss, v)`), on which the kernel's reduction is stuck (bisected: guarded
by `decide +kernel` failures, scratch). Resolution, `checkInd` of `False` and `True`, and the decisions at small states
are kernel-evaluable. So the facts about the library's items are carried symbolically (the checker's verdicts threaded
through `checkDefs`), and the facts about `one`'s check are inversions of `checkDef` (as `Machine.constRunJ`).
-/

namespace Ochr.Meaning.Steps.Form.Top.One

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly
open Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice

-- The program of the acceptance test: one constant after the library.
open Ochr.Test in
ochr TopOneP {
  def one : Nat := 1
}

-- The brief's program: `S(Z)`, a call of the surface's successor function.
open Ochr.Test in
ochr TopOneS {
  def one : Nat := S(Z)
}

/-- The program `q`. -/
def q : Program := TopOneP.decls

/-- The whole program the checker checks: the library, then `q`. -/
def pq : Program := Prelude.decls ++ q

/-- The fuel of the test. -/
def F : Nat := 100000

/-- The resolution of the `i`-th declaration. -/
def resAt (i : Nat) : Except Exhausted (Except String Item) := (runResolve pq (pq.getD i default) F false).1

/-- An item that is an inductive declaration. -/
def isIndItem : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.ind _)) => true
  | _ => false

/-- The item `def one : Nat := 1` as resolved: `ProgSanity.oneDef`. -/
def isOneItem : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.defn ⟨n, [], [], .nat, none, .succ .zero, none⟩)) => n == "one"
  | _ => false

theorem pq_length : pq.length = 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem res_ind : isIndItem (resAt 0) = true ∧ isIndItem (resAt 1) = true ∧ isIndItem (resAt 2) = true ∧
    isIndItem (resAt 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem res_one : isOneItem (resAt 4) = true := by decide +kernel

/-- The brief's `S(Z)` resolves to a call of the closure `succFn` at `Z` (the finding of the module docstring). -/
def isSuccFnCall : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.defn d)) => match d.body with
    | .call (.fix _ [_] [.nat] .nat none (.succ (.place (.var 0)))) [.zero] _ => true
    | _ => false
  | _ => false

set_option maxRecDepth 100000 in
theorem resS_call :
    isSuccFnCall (runResolve (Prelude.decls ++ TopOneS.decls) ((Prelude.decls ++ TopOneS.decls).getD 4 default) F false).1
      = true := by decide +kernel

/-! ## The items, pinned by resolution -/

theorem ind_of {x : Except Exhausted (Except String Item)} (h : isIndItem x = true) : ∃ d, x = .ok (.ok (.ind d)) := by
  unfold isIndItem at h; split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem oneDef_of {x : Except Exhausted (Except String Item)} (h : isOneItem x = true) :
    x = .ok (.ok (.defn ProgSanity.oneDef)) := by
  unfold isOneItem at h; split at h
  · simp only [beq_iff_eq] at h; subst h; rfl
  · cases h

/-- Every item of a resolution of `pq` is the resolution of its declaration. -/
theorem items_at {items : List Item} (hr : ResolvesTo pq F items) (i : Nat) (it : Item) (hi : items[i]? = some it) :
    resAt i = .ok (.ok it) := by
  have hlt : i < pq.length := by rw [← hr.1]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨_, h, -⟩ := hr.2 i (pq.getD i default) it (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl) hi
  exact h

/-- **The resolved items**: four inductive declarations, then `one`. -/
theorem items_shape {items : List Item} (hr : ResolvesTo pq F items) :
    items.length = 5 ∧ (∀ i, i < 4 → ∀ it, items[i]? = some it → ∃ d, it = .ind d) ∧
      items[4]? = some (.defn ProgSanity.oneDef) := by
  have hl : items.length = 5 := by rw [hr.1, pq_length]
  obtain ⟨h0, h1, h2, h3⟩ := res_ind
  refine ⟨hl, fun i hi it hit => ?_, ?_⟩
  · have e := items_at hr i it hit
    have hind : isIndItem (resAt i) = true := by
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | 2, _ => exact h2
      | 3, _ => exact h3
    rw [e] at hind
    obtain ⟨d, hd⟩ := ind_of hind
    exact ⟨d, by cases hd; rfl⟩
  · have h4 : items[4]? = some items[4] := List.getElem?_eq_getElem (by omega)
    have e := items_at hr 4 _ h4
    have h1 := oneDef_of res_one
    rw [e] at h1
    rw [h4]
    injection h1 with h1
    injection h1 with h1
    rw [h1]

/-- Along inductive declarations only, the checker's globals do not change. -/
theorem sigAfterFrom_globals_ind (cfg : Config) (fuel : Nat) :
    ∀ (its : List Item) (s : List GDef × List IndDecl), (∀ it ∈ its, ∃ d, it = .ind d) →
      (sigAfterFrom cfg fuel s its).1 = s.1
  | [], _, _ => rfl
  | it :: its, s, h => by
    unfold sigAfterFrom
    rw [List.foldl_cons]
    have ih := sigAfterFrom_globals_ind cfg fuel its
    unfold sigAfterFrom at ih
    obtain ⟨d, rfl⟩ := h it List.mem_cons_self
    split
    · rename_i st' hst
      rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      exact ((Steps.Machine.checkItem_tables (.ind d) _ st' fuel hst).1 d rfl).2
    · exact ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## `one`'s body, `S(Z)`, as the checker evaluates it -/

/-- **The table at `S(Z)`** (PROVED, by the checker's decision procedures): read `.other`, not erased. -/
theorem decTab_one {D : Decisions} {st : MState} (hD : DecTab D st) :
    (∀ sc, D.declOf sc (.succ .zero) = .other) ∧ (∀ sc, D.flags sc (.succ .zero) = (false, false)) :=
  decTab_fixed hD (.succ .zero) .other (fun k S f l => by rw [Ochr.declOf]; rfl) (fun S f l => rfl)

/-- A table aligned with the checker at any state: the chain's. -/
theorem decTab_chain (fuel : Nat) (st : MState) : DecTab (chainDecisions fuel st) st :=
  decTab_ff st _ (fun _ => Machine.decide_fuel_agree' _) (Machine.decide_fuel_agree' st)

/-- **The checker's value of `S(Z)`** (PROVED): every successful run of `eval` on `S(Z)`, at any erased depth, out of
tail position with no reading handed down, returns the value `S(Z)` at `Nat`. -/
theorem eval_one_inv {n : Nat} {typed : Bool} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value}
    {T? : Option Value} (hm : ModeR st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n typed (.succ .zero) hint) st bh (v, T?) st') : v = .succ .zero ∧ T? = some .tNat := by
  by_cases hn : n < 3
  · exact absurd h (Machine.evalLow n typed _ hint st st' bh _ hn (fun w e => by cases e))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  have hD := decTab_chain F st'
  obtain ⟨hd1, -⟩ := decTab_one hD
  obtain ⟨st₀, st₁, bh', -, hme, -, htn₀, htd₀, -, hcore, -, -⟩ := Machine.evalInvD (m + 1) typed (.succ .zero) hint st st' bh v T?
    _ hm hD (fun w e => by cases e) (fun f as h e => by cases e) (by rw [hd1]; exact fun e => by cases e)
    (by rw [hd1]; rfl) (Or.inl htd) h
  obtain ⟨s₀, s₁, v₀, T₀, bh₁, -, hme₀, -, htd₁, hev, rfl, hT, -, -, -, -⟩ :=
    Machine.succInvD m typed .zero hint st₀ st₁ bh' v T? htn₀ htd₀ hcore
  refine ⟨?_, hT⟩
  have hm₀ : ModeR s₀ := (hm.of_modeEq hme).of_modeEq hme₀
  by_cases hk : m < 3
  · exact absurd hev (Machine.evalLow m typed _ none s₀ s₁ bh₁ _ hk (fun w e => by cases e))
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 + 2 := ⟨m - 3, by omega⟩
  have hD₁ := decTab_chain F s₁
  obtain ⟨hz1, -⟩ := decTab_zero hD₁
  obtain ⟨r₀, r₁, bh'', -, -, -, -, -, -, h₀, -, -⟩ := Machine.evalInvD (k + 1) typed .zero none s₀ s₁ bh₁ v₀ T₀ _ hm₀ hD₁
    (fun w e => by cases e) (fun f as h e => by cases e) (by rw [hz1]; exact fun e => by cases e) (by rw [hz1]; rfl)
    (Or.inl htd₁) hev
  obtain ⟨rfl, -, -⟩ := zeroInvE k typed none r₀ r₁ bh'' v₀ T₀ h₀
  rfl

/-! ## `one`'s check, inverted (the witness of `ConstCheckAt`) -/

/-- `isPropV` at `Nat` is `false` and keeps the state. -/
theorem runs_isPropV_nat {f : Nat} {st st' : MState} {b : Nat} {p : Bool} (h : Runs (isPropV f .tNat) st b p st') :
    p = false ∧ st' = st := by
  cases f with
  | zero => unfold isPropV at h; simp only [Machine.runs_exhausted_iff] at h
  | succ f => unfold isPropV at h; exact runs_pure_inv h

/-- The state `one`'s body is evaluated from: one empty frame, Σ the library's (no global), the [Rec] records as the
goal's evaluation left them. -/
def stB (I : List IndDecl) (s : MState) : MState :=
  { ({ globals := [], inds := I } : MState) with env := #[{}], recStack := s.recStack, nextRecUid := s.nextRecUid }

set_option maxHeartbeats 8000000 in
/-- **`one`'s check, inverted** (PROVED): from any declarations `I` and the empty Σ, an accepted `def one : Nat := 1`
evaluated its body `S(Z)` from `stB I _` to the value `S(Z)` at `Nat`, converted `Nat` to the goal `Nat`, passed
[Return], and stored the global `one` at `Nat` with the value `S(Z)`. -/
theorem one_check_inv {I : List IndDecl} {fuel : Nat} {st' : MState}
    (hr : (runMachine (checkItem (.defn ProgSanity.oneDef)) { globals := [], inds := I } fuel).1 = .ok () st') :
    ∃ (r s₂ s₀ s₃ s₃' s₄ : MState) (n bh : Nat) (at' : List (Nat × Value)) (ad : List (Nat × DeclInfo)),
      Runs (Ochr.eval n true (.succ .zero) (some .tNat)) (stB I r) bh (.succ .zero, some .tNat) s₂ ∧
      s₂.globals = [] ∧ s₂.inds = I ∧ Machine.LocsEq s₂ s₀ ∧ (∃ f b, Runs (Ochr.conv f .tNat .tNat) s₀ b true s₃) ∧ Machine.LocsEq s₃ s₃' ∧
      (∃ f b, Runs (Ochr.bodyReturns f s!"{ProgSanity.oneDef.name} is defined as it" (.succ .zero) .tNat [] "") s₃' b () s₄) ∧
      st'.globals = [{ name := "one", ty := .tNat, fn? := none, val := .succ .zero, absTys := at', absDecls := ad }] := by
  have h := Machine.runs_of_runMachine_fst hr
  unfold checkItem at h
  obtain ⟨_, s₀₀, b₀₀, hsh, h⟩ := Runs.bind_inv h
  have hs0 : s₀₀ = { globals := [], inds := I } := by
    unfold seedHoles at hsh
    rw [Machine.runs_get_bind] at hsh
    exact (runs_pure_inv hsh).2
  subst hs0
  unfold checkDef at h
  obtain ⟨dcl, s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
  clear h
  have := runs_keep (Machine.keep_declared _) hd; subst this
  dsimp only at h₁
  have e1 : ((ProgSanity.oneDef.cod :: ProgSanity.oneDef.doms).any (Term.mentionsConst ProgSanity.oneDef.name)) = false := rfl
  have e2 : (!((ProgSanity.oneDef.cod :: ProgSanity.oneDef.doms).all Term.refTopOk && ProgSanity.oneDef.body.refsOk)) = false :=
    rfl
  by_cases hd1 : dcl = true
  · simp only [hd1, if_true] at h₁
    exact absurd h₁ (fun h => by obtain ⟨_, _, _, he, _⟩ := Runs.bind_inv h; exact runs_err_false he)
  simp only [hd1, e1, e2, Bool.false_eq_true, if_false] at h₁
  obtain ⟨fl, s₂, b₂, hfl, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  have := runs_keep Machine.keep_fuelLeft hfl; subst this
  obtain ⟨_, s₃, b₃, hdo, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  have := runs_keep (keep_discard ((decideKeep _).2.2.2.2.2.2.2.2.1 _ _ _ _)) hdo; subst this
  obtain ⟨_, s₄, b₄, hu, h₄⟩ := Runs.bind_inv h₃
  clear h₃
  have := runs_keep (Machine.keep_undeclaredCheck _ _) hu; subst this
  simp only [ProgSanity.oneDef, List.isEmpty_nil, if_true] at h₄
  peel h₄
  obtain ⟨fl2, s₅, b₅, hfl2, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  have := runs_keep Machine.keep_fuelLeft hfl2; subst this
  obtain ⟨g, s₆, b₆, hg, h₆⟩ := Runs.bind_inv h₅
  clear h₅
  obtain ⟨rfl, rs, nr, rfl⟩ := Machine.runs_evalType_nat hg rfl rfl
  obtain ⟨fl3, s₇, b₇, hfl3, h₇⟩ := Runs.bind_inv h₆
  clear h₆
  have := runs_keep Machine.keep_fuelLeft hfl3; subst this
  obtain ⟨⟨v, T⟩, s₈, b₈, hev, h₈⟩ := Runs.bind_inv h₇
  clear h₇
  obtain ⟨rfl, rfl⟩ := eval_one_inv ⟨rfl, rfl, rfl⟩ rfl hev
  have hg8 : TablesGrow _ s₈ := Runs.grows (grows_eval _ _ _ _) hev
  obtain ⟨_, s₉, b₉, hloc, h₉⟩ := Runs.bind_inv h₈
  clear h₈
  obtain ⟨s₀, b₀, s₉', hle₀, hx, hle₁⟩ := Machine.Runs.located_inv hloc
  clear hloc
  simp only at hx
  obtain ⟨fc, s₁₀, b₁₀, hfc, hx⟩ := Runs.bind_inv hx
  have e10 : s₁₀ = s₀ := runs_keep Machine.keep_fuelLeft hfc
  obtain ⟨c, s₁₁, b₁₁, hcv, hx⟩ := Runs.bind_inv hx
  have hg11 : TablesGrow s₁₀ s₁₁ :=
    Runs.grows (Machine.growsM_of_growsIn fun G => (Machine.machineGrows _).conv _ _) hcv
  cases c
  · simp only [Bool.false_eq_true, if_false] at hx; exact absurd hx runs_err_false
  simp only [if_true] at hx
  have e9 : s₉' = s₁₁ := (runs_pure_inv hx).2
  obtain ⟨fb, s₁₂, b₁₂, hfb, h₉⟩ := Runs.bind_inv h₉
  have e12 : s₁₂ = s₉ := runs_keep Machine.keep_fuelLeft hfb
  rw [e12] at h₉
  obtain ⟨_, s₁₃, b₁₃, hbr, h₉⟩ := Runs.bind_inv h₉
  have hg13 : TablesGrow s₉ s₁₃ :=
    Runs.grows (Machine.growsM_of_growsIn fun G => (Machine.machineGrows _).bodyReturns _ _ _ _ _) hbr
  obtain ⟨fp, s₁₄, b₁₄, hfp, h₉⟩ := Runs.bind_inv h₉
  have e14 : s₁₄ = s₁₃ := runs_keep Machine.keep_fuelLeft hfp
  rw [e14] at h₉
  obtain ⟨p, s₁₅, b₁₅, hp, h₉⟩ := Runs.bind_inv h₉
  obtain ⟨rfl, e15⟩ := runs_isPropV_nat hp
  rw [e15] at h₉
  simp only [Bool.false_eq_true, if_false] at h₉
  rw [Machine.runs_get_bind] at h₉
  obtain ⟨ad, s₁₆, b₁₆, hmap, h₉⟩ := Runs.bind_inv h₉
  have hg16 : TablesGrow s₁₃ s₁₆ := Runs.grows (Machine.growsM_of_growsIn fun G => by
    have hEv : ∀ (G : Machine.Tab) (f : Nat) (typed : Bool) (t : Term) (hint : Option Value),
      Machine.GrowsIn G (Ochr.eval f typed t hint) := fun G f => (Machine.machineGrows f).eval
    grows_goI) hmap
  have hst := Machine.runs_modify_inv h₉
  subst hst
  have hle0 : s₁₀.globals = s₈.globals := by rw [e10, ← hle₀]
  have hle1 : s₉.globals = s₁₁.globals := by rw [← hle₁, e9]
  refine ⟨{ inds := I, recStack := rs, nextRecUid := nr }, s₈, s₁₀, s₁₁, s₉, s₁₃, fl3, b₇,
    holeAbs s₁₃.absTy [Value.tNat, Value.zero.succ], ad, hev, hg8.globals, hg8.inds, by rw [e10]; exact hle₀, ⟨fc, b₁₀, hcv⟩,
    by rw [← e9]; exact hle₁, ⟨fb, b₁₂, hbr⟩, ?_⟩
  show s₁₆.globals ++ _ = _
  rw [hg16.globals, hg13.globals, hle1, hg11.globals, hle0, hg8.globals]
  rfl

/-! ## The stage after the library -/

/-- Along inductive declarations only, the program meaning records no meaning. -/
theorem progMeaningFrom_means_ind (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (ρ : Assignment)
    (cfg : Config) (fuel : Nat) :
    ∀ (its : List Item) (P : ProgState), (∀ it ∈ its, ∃ d, it = .ind d) →
      (progMeaningFrom dm D Γ ρ cfg fuel P its).means = P.means
  | [], _, _ => rfl
  | it :: its, P, h => by
    simp only [progMeaningFrom, List.foldl_cons]
    have ih := progMeaningFrom_means_ind dm D Γ ρ cfg fuel its
    simp only [progMeaningFrom] at ih
    obtain ⟨d, rfl⟩ := h it List.mem_cons_self
    rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    unfold ProgState.step
    dsimp only
    split <;> rfl

/-- **A stage of `one`'s program at an item that is a definition**: the item is `one`, at the stage after the
library, whose Σ has no global and whose meanings are none. -/
theorem atStage_one {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {items : List Item}
    (hr : ResolvesTo pq F items) {P : ProgState} {d : Def} (hin : AtStage dm D Γ F items P (.defn d)) :
    d = ProgSanity.oneDef ∧ P.globals = [] ∧ P.means = [] := by
  obtain ⟨hl, hind, h4⟩ := items_shape hr
  obtain ⟨k, hk, rfl⟩ := hin
  have hk5 : k < 5 := hl ▸ (List.getElem?_eq_some_iff.1 hk).1
  have hk4 : k = 4 := by
    rcases Nat.lt_or_ge k 4 with h | h
    · obtain ⟨d', hd'⟩ := hind k h _ hk
      cases hd'
    · omega
  subst hk4
  rw [h4] at hk
  injection hk with hk
  injection hk with hk
  subst hk
  have htake : ∀ it ∈ items.take 4, ∃ d, it = .ind d := by
    intro it hit
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hit
    rw [List.getElem_take] at e
    simp only [List.length_take] at hi
    exact hind i (by omega) it (by rw [← e]; exact List.getElem?_eq_getElem _)
  refine ⟨rfl, ?_, ?_⟩
  · have h := progMeaningFrom_sigAfter dm D Γ (fun _ => .err) {} F {} (items.take 4)
    simp only at h
    unfold progMeaning
    have h1 := congrArg Prod.fst h
    simp only at h1
    rw [h1]
    exact sigAfterFrom_globals_ind {} F _ _ htake
  · unfold progMeaning
    exact progMeaningFrom_means_ind dm D Γ _ {} F _ {} htake

/-! ## The start of `one`'s body: every hypothesis of the general step, at the state with the library's declarations

As `ColumnC`'s `stC` (one empty frame, nothing else), with the declarations `I` of the stage: no clause of the
checker's invariant reads them at a state holding no value. -/

/-- The kernel of `one`'s start: one empty frame, the declarations `I`. -/
def stN (I : List IndDecl) : MState := { inds := I }

theorem norm_stB (I : List IndDecl) (r : MState) : (stB I r).norm = stN I := by
  simp [stB, stN, MState.norm, Env.erase, Frame.erase]

theorem ckContent_stN (I : List IndDecl) (p : Place) : ckContent (stN I).env p = none := ColumnC.Aux.ckContent_stC p

theorem bind_stN (I : List IndDecl) (f i : Nat) : (stN I).env[f]?.bind (fun fr => fr.binds[i]?) = none :=
  ColumnC.Aux.bind_stC f i

theorem liveLoan_stN (I : List IndDecl) (l : Nat) : liveLoan (stN I).env l = false := ColumnC.Aux.liveLoan_stC l

theorem allPos_stN (I : List IndDecl) : allPos (stN I).env = [] := ColumnC.Aux.allPos_stC

theorem values_stN (I : List IndDecl) : Env.values (stN I).env = [] := ColumnC.Aux.values_stC

theorem not_refd_stN (I : List IndDecl) (σ : Nat) : ¬ (stN I).Refd σ := by
  intro h
  have := MState.refd_lt (stN I) 0 (by simp [values_stN])
    (fun f i b T hb => by simp [stN] at hb; rcases f with _ | f <;> simp at hb)
    (fun f i b P ws j hb => by simp [stN] at hb; rcases f with _ | f <;> simp at hb)
    (fun G hG => by simp [stN] at hG) (fun m σ' h => by simp [stN] at h) (fun σ' v h => by simp [stN] at h)
    (fun σ' T h => by simp [stN] at h) σ h
  omega

theorem occurs_stN (I : List IndDecl) (l : Nat) : ¬ (stN I).Occurs l := by
  rintro ⟨v, hv, -⟩; simp [values_stN] at hv

/-- The checker's invariant at `stN I`, at every table and declaration list. -/
theorem inv_stN (I : List IndDecl) (D : Decisions) (Γ : List IndDecl) : Inv D Γ (stN I) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; simp [allPos_stN] at hp
  · intro p hp; simp [allPos_stN] at hp
  · intro v hv; simp [values_stN] at hv
  · intro l; simp [values_stN]
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, _⟩ => by simp [allPos_stN] at hp⟩⟩
  · intro v hv; simp [values_stN] at hv
  · intro σ h; exact absurd h (not_refd_stN I σ)
  · intro T hT; simp [stN] at hT
  · intro σ r h; simp [stN] at h
  · rfl
  · intro v hv; simp [values_stN] at hv
  · intro v hv; simp [values_stN] at hv
  · intro f i b hb; simp [bind_stN] at hb
  · intro T hT; simp [stN] at hT
  · intro G hG; simp [stN] at hG
  · intro v hv; simp [values_stN] at hv
  · intro f i b hb; simp [bind_stN] at hb
  · intro T hT; simp [stN] at hT
  · intro G hG; simp [stN] at hG
  · intro n σ h; simp [stN] at h
  · intro σ v h; simp [stN] at h
  · intro k l hk; simp [liveLoan_stN] at hk
  · intro pos path _ l hl; simp [liveLoan_stN] at hl
  · intro v hv; simp [values_stN] at hv
  · intro v hv; simp [values_stN] at hv
  · intro p v n args h; simp [ckContent_stN] at h
  · intro v hv; simp [values_stN] at hv
  · intro v hv; simp [values_stN] at hv
  · intro p _ h; simp [ckContent_stN] at h
  · intro σ r h; simp [stN] at h
  · intro σ r h; simp [stN] at h
  · intro σ l h; simp [stN] at h
  · intro l h; exact absurd h (occurs_stN I l)
  · exact fun f i b hb => by simp [bind_stN] at hb

theorem asg_stN (I : List IndDecl) (K : RunCtx) (ρ : Assignment) : Asg K ρ (stN I) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ _ h; simp [stN] at h
  · intro n σ h; simp [stN] at h
  · intro σ v h; simp [stN] at h
  · intro σ r h; simp [stN] at h
  · intro σ _ h; simp [stN] at h
  · intro G h; simp [MState.goalM, stN] at h
  · intro σ _ h; simp [stN] at h

/-- **`Pre` at `one`'s start**, at the program's context at the stage after the library (any decisions): its
declarations a prefix of the program's, covered and faithful, the stage's meanings none. -/
theorem pre_stB {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {P : ProgState} {st : MState}
    (I : List IndDecl) (r : MState) (ρ : Assignment) (hI : I <+: Γ) (hcov : ∀ d ∈ Γ, dm.covers d)
    (hf : DeclsFaithful (P.ctx dm D Γ st) I) (hm : P.means = []) :
    Pre (P.ctx dm D Γ st) ρ (stB I r) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stB]
  · refine ⟨hI, hcov, hf, fun n => ?_, GlobalsOk.of_globals (globalsOk_nil _) rfl⟩
    show (P.globalTy n).label = none
    unfold ProgState.globalTy
    rw [hm]
    rfl
  · exact inv_stN I _ _
  · exact asg_stN I _ ρ

theorem positions_SM_stB (K : RunCtx) (ρ : Assignment) (I : List IndDecl) (r : MState) :
    (SM' K ρ (stB I r)).positions = [] := by
  unfold SM'; rw [sstate_positions]; exact ColumnC.Aux.allPos_stC

theorem shape_SM_stB (K : RunCtx) (ρ : Assignment) (I : List IndDecl) (r : MState) (p : Pos) :
    (SM' K ρ (stB I r)).shape p = none := by
  cases h : (SM' K ρ (stB I r)).shape p with
  | none => rfl
  | some l =>
    have := mem_allPos_of_shape (l := l) h
    rw [show allPos (stB I r).env = [] from ColumnC.Aux.allPos_stC] at this; cases this

theorem liveLabels_SM_stB (K : RunCtx) (ρ : Assignment) (I : List IndDecl) (r : MState) :
    (SM' K ρ (stB I r)).liveLabels = [] := by
  simp [SState.liveLabels, positions_SM_stB]

theorem valAt_SM_stB (K : RunCtx) (ρ : Assignment) (I : List IndDecl) (r : MState) (p : Pos) :
    (SM' K ρ (stB I r)).valAt p = fun _ => .err :=
  SState.valAt_of_not_mem _ _ (by rw [positions_SM_stB]; exact List.not_mem_nil)

theorem rel_stB (K : RunCtx) (ρ : Assignment) (φ : Future) (I : List IndDecl) (r : MState) :
    Rel K ρ φ id (stB I r) (SM' K ρ (stB I r)) :=
  Rel.start_noLive _ _ _ _ fun l h => by simp [SState.Live, liveLabels_SM_stB] at h

theorem sgood_stB (K : RunCtx) (ρ : Assignment) (φ : Future) (I : List IndDecl) (r : MState) :
    Strict.SGood K.dm K.Γ φ (SM' K ρ (stB I r)) where
  bind := fun ψ _ f i hp => by rw [positions_SM_stB] at hp; cases hp
  holder := fun ψ _ p l hl => by rw [shape_SM_stB] at hl; cases hl
  held := fun l hl => by rw [liveLabels_SM_stB] at hl; cases hl
  holderTy := fun f i l hl => by rw [shape_SM_stB] at hl; cases hl
  acyc := ⟨fun p ψ ψ' _ => by rw [valAt_SM_stB], fun r x hr => (by rw [positions_SM_stB] at hr; cases hr),
    fun p x hp => (by rw [shape_SM_stB] at hp; cases hp)⟩
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    exact absurd (by show (SM' K ρ (stB I r)).valAt p ψ = (SM' K ρ (stB I r)).valAt p (ψ.upd l x); rw [valAt_SM_stB]) hne
  uniq := fun p _ l hp _ => by rw [shape_SM_stB] at hp; cases hp

/-! ## The constant's links at `one`, PROVED -/

theorem meanV_one (K : RunCtx) (ρ : Assignment) (ψ : Future) (R : TyS) :
    meanV K ρ ψ R (.succ .zero) = (Sem.el0 Nat 0).succ := rfl

theorem one_mem (R : DataRead) : (Sem.el0 Nat 0).succ ∈ₛ[R] TyM.nat :=
  ⟨1, by simp [Sem.succ, Sem.asNat, Sem.as, Code0.enc]⟩

/-- **`ConstG` at `one`'s program** (PROVED, no hypothesis beyond the program's resolution): `one`'s check inverted
(`ConstCheckAt`), its start (`ConstStartAt`: `Pre`, the start relation, goodness, the body's syntax, the chain's table
at the run's end), its leaf (`ConstLeafAt`: the checker's value `S(Z)` means `1`, a number) and its meaning
(`ConstMeanAt`: the program meaning records `1` at `Nat`, the chain's table not erasing `S(Z)`). -/
theorem constG_one (dm : DataModel) {items : List Item} (hr : ResolvesTo pq F items) :
    ConstG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin _ hrun _ hfaith hcov hΓP
  obtain ⟨rfl, hPg, hPm⟩ := atStage_one hr hin
  rw [hPg] at hrun
  obtain ⟨r, s₂, s₀, s₃, s₃', s₄, n, bh, at', ad, hev, hg2, hi2, hl0, ⟨fc, bc, hcv⟩, hl3, ⟨fb, bb, hbr⟩, hst'⟩ :=
    one_check_inv hrun
  refine ⟨⟨n, stB P.inds r, s₂, s₃, s₄, bh, .tNat, .succ .zero, .tNat⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨rfl, rfl, rfl⟩, rfl, by show 0 < 1; omega, rfl, hPg.symm, hev, ⟨s₀, fc, bc, hl0, hcv⟩,
      ⟨s₃', fb, bb, hl3, hbr⟩, ⟨_, by rw [hst', hPg]; rfl, rfl, rfl⟩, by rw [hst']; rfl⟩
  · intro ρ φ
    have hf : DeclsFaithful (P.ctx dm (chainDecisions F) (indsOf {} F items) s₂) P.inds :=
      hfaith s₂ hi2 (by rw [hPg]; exact List.nil_prefix)
    refine ⟨pre_stB P.inds r ρ hΓP hcov hf hPm, rel_stB _ ρ φ P.inds r,
      sgood_stB (P.ctx dm (chainDecisions F) (indsOf {} F items) s₂) ρ φ P.inds r, ?_, ?_, ?_, rfl,
      decTab_chain F s₂⟩
    · simp [ProgSanity.oneDef, Term.valsOk]
    · intro σ h; simp [ProgSanity.oneDef, Term.anyAtom] at h
    · intro T hT σ hσ; cases hT; cases hσ
  · intro ρ' Δ' π' r' _ hmv _ _
    rw [← hmv, meanV_one]
    exact one_mem _
  · intro ρ φ r' s' _ _
    have hne : ∀ sc, ((P.ctx dm (chainDecisions F) (indsOf {} F items) st').D.flags sc (.succ .zero)).2 = false :=
      fun sc => by
        show ((chainDecisions F st').flags sc (.succ .zero)).2 = false
        rw [(decTab_one (decTab_chain F st')).2 sc]
    refine ⟨_, ProgSanity.defMeaning_one _ _ hne, ?_⟩
    exact ⟨1, rfl⟩

/-- **`FixG` at `one`'s program** (PROVED, vacuous: its only definition has no parameter). -/
theorem fixG_one (dm : DataModel) {items : List Item} (hr : ResolvesTo pq F items) :
    FixG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin hd
  obtain ⟨rfl, -, -⟩ := atStage_one hr hin
  exact absurd rfl hd

theorem succ_el0 : (Sem.el0 Nat 0).succ = Sem.el0 Nat 1 := by simp [Sem.succ, Sem.asNat, Sem.as]

/-- The stage after `one`. -/
def P1 (at' : List (Nat × Value)) (ad : List (Nat × DeclInfo)) (I : List IndDecl) : ProgState :=
  { globals := [{ name := "one", ty := .tNat, fn? := none, val := .succ .zero, absTys := at', absDecls := ad }],
    inds := I, means := [("one", .el0 Nat 1, .plain TyM.nat)] }

/-- The stage after `one`: Σ holds `one`'s entry, and the meanings `one`'s, `1` at `Nat`. -/
theorem step_one {dm : DataModel} {Γ : List IndDecl} {P : ProgState} {st' : MState} (hPg : P.globals = [])
    (hPm : P.means = [])
    (hrun : (runMachine (checkItem (.defn ProgSanity.oneDef)) { globals := P.globals, inds := P.inds } F).1 = .ok () st') :
    ∃ at' ad, (ProgState.step dm (chainDecisions F) Γ (fun _ => .err) {} F P (.defn ProgSanity.oneDef)) =
      P1 at' ad st'.inds := by
  have hrun' := hrun
  rw [hPg] at hrun'
  obtain ⟨-, -, -, -, -, -, -, -, at', ad, -, -, -, -, -, -, -, hst'⟩ := one_check_inv hrun'
  refine ⟨at', ad, ?_⟩
  unfold ProgState.step
  dsimp only
  rw [show ({ globals := P.globals, inds := P.inds, cfg := {} } : MState) = { globals := P.globals, inds := P.inds } from rfl,
    hrun]
  dsimp only
  have hT : ((st'.globals.find? (·.name == ProgSanity.oneDef.name)).map (·.ty)).getD .bot = .tNat := by rw [hst']; rfl
  have hne : ∀ sc, ((P.ctx dm (chainDecisions F) Γ st').D.flags sc (.succ .zero)).2 = false := fun sc => by
    show ((chainDecisions F st').flags sc (.succ .zero)).2 = false
    rw [(decTab_one (decTab_chain F st')).2 sc]
  rw [hT, ProgSanity.defMeaning_one _ _ hne, hst', hPm]
  rfl

/-- **`GlobGrowG` at `one`'s program** (PROVED): after `one`, its entry meets `GlobalsOk` at the context of every later
check: its type's meaning is `Nat`, its meaning `1` is its stored value's, a member; every clause about a function's
code is vacuous (it has none); the function under check of a later context is no global of the stage. -/
theorem globGrow_one (dm : DataModel) {items : List Item} (hr : ResolvesTo pq F items) :
    GlobGrowG dm (chainDecisions F) (indsOf {} F items) F items := by
  intro P d st' hin hrun _ _ _ _ _ _ Dd cu _ hcu
  obtain ⟨rfl, hPg, hPm⟩ := atStage_one hr hin
  obtain ⟨at', ad, hstep⟩ := step_one (dm := dm) (Γ := indsOf {} F items) hPg hPm hrun
  rw [hstep] at hcu ⊢
  -- the context reads `one` as the stage does, and names no function under check called `one`
  have hglob : ∀ n, n = "one" →
      (ctxAt dm (indsOf {} F items) (P1 at' ad st'.inds) Dd cu).C.global n = (Sem.el0 Nat 1, .plain TyM.nat) := by
    intro n hn; subst hn
    have hb : (P1 at' ad st'.inds).baseC.global "one" = (Sem.el0 Nat 1, .plain TyM.nat) := rfl
    rcases cu with _ | ⟨f, b, G⟩
    · exact hb
    · have hf : (P1 at' ad st'.inds).isGlobal f = false := hcu _ rfl
      have hne : "one" ≠ f := fun e => by
        subst e
        have h1 : (P1 at' ad st'.inds).isGlobal "one" = true := rfl
        rw [h1] at hf; cases hf
      show (if "one" = f then G else (P1 at' ad st'.inds).baseC.global "one") = _
      rw [if_neg hne]; exact hb
  have hcur : ∀ n, n = "one" → (ctxAt dm (indsOf {} F items) (P1 at' ad st'.inds) Dd cu).cur.map (·.1) ≠ some n := by
    intro n hn; subst hn
    rcases cu with _ | ⟨f, b, G⟩
    · exact fun e => by cases e
    · intro e
      have hf : (P1 at' ad st'.inds).isGlobal f = false := hcu _ rfl
      simp only [ctxAt, Option.map_some] at e
      injection e with e
      subst e
      have h1 : (P1 at' ad st'.inds).isGlobal "one" = true := rfl
      rw [h1] at hf; cases hf
  have hfind : ∀ n g, ({ globals := (P1 at' ad st'.inds).globals } : MState).globals.find? (·.name == n) = some g →
      n = "one" ∧ g = { name := "one", ty := .tNat, fn? := none, val := .succ .zero, absTys := at', absDecls := ad } := by
    intro n g h
    simp only [P1, List.find?_cons, List.find?_nil] at h
    split at h
    · rename_i hn
      simp only [beq_iff_eq] at hn
      injection h with h
      exact ⟨hn.symm, h.symm⟩
    · cases h
  refine ⟨fun n g hf _ ρ => ?_, fun n g hf _ ρ φ => ?_, fun n g t hf ht => ?_, fun n g hf _ => ?_,
    fun n g b hf hc => ?_, fun n gd _ _ _ _ _ _ hf _ ht => ?_, fun n gd _ _ _ _ _ _ hf _ ht => ?_,
    fun n gd _ _ _ _ _ _ hf _ ht => ?_, fun n g t hf ht => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    rw [hglob _ rfl]; rfl
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    rw [hglob _ rfl]
    show Sem.el0 Nat 1 = (Sem.el0 Nat 0).succ
    exact succ_el0.symm
  · obtain ⟨rfl, rfl⟩ := hfind n g hf; cases ht
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    rw [hglob _ rfl]
    exact ⟨1, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hfind n g hf
    exact absurd (by rw [hc]; rfl) (hcur _ rfl)
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf; cases ht
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf; cases ht
  · obtain ⟨rfl, rfl⟩ := hfind n gd hf; cases ht
  · obtain ⟨rfl, rfl⟩ := hfind n g hf; cases ht

/-! ## The top's non-step hypotheses at `one`'s program -/

/-- **The links of the top at `one`'s program** (PROVED, kernel-checked; standard axioms): `hlinks` exactly as
`consistency_of_master` takes it, at the program `def one : Nat := 1` and fuel `F`. -/
theorem hlinks_one : ∀ items, ResolvesTo pq F items →
    ∀ dm, (∀ d' ∈ indsOf {} F items, dm.covers d') →
      (∀ k, k ≤ items.length → DataFaithful dm (chainDecisions F) (indsOf {} F items)
        (progMeaning dm (chainDecisions F) (indsOf {} F items) (fun _ => .err) {} F (items.take k))) →
      TopLinks dm (chainDecisions F) (indsOf {} F items) F items :=
  fun _ hr dm _ _ => ⟨constG_one dm hr, fixG_one dm hr, globGrow_one dm hr⟩

/-- The declared type of `one`, unlocated, is not `False`. -/
def retIsFalse (d : SDecl) : Bool :=
  match d.ret.unloc with
  | .ident "False" => true
  | _ => false

set_option maxRecDepth 100000 in
theorem one_ret_not_false : retIsFalse (q.getD 0 default) = false := by decide +kernel

theorem q_length : q.length = 1 := by decide +kernel

/-- **`FalseConstG` at `one`'s program** (PROVED; vacuous: `one` is not a closed definition of `False`). -/
theorem falseConst_one : FalseConstG q F := by
  intro _ _ _ _ _ d hd hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hi0 : i = 0 := by rw [q_length] at hi; omega
  subst hi0
  have h := one_ret_not_false
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h
  unfold retIsFalse at h
  rw [hf.2.2] at h
  cases h

/-! ## `ResolveG` at `one`'s program: the resolution half -/

/-- The item the `i`-th declaration resolves to. -/
def itOf (i : Nat) : Item := match resAt i with
  | .ok (.ok it) => it
  | _ => default

/-- The resolved items. -/
def itemsQ : List Item := [itOf 0, itOf 1, itOf 2, itOf 3, itOf 4]

theorem resAt_itOf (i : Nat) (h : ∃ it, resAt i = .ok (.ok it)) : resAt i = .ok (.ok (itOf i)) := by
  obtain ⟨it, e⟩ := h
  unfold itOf; rw [e]

/-- **The program resolves** (PROVED, by the kernel's run of resolution): the half of `ResolveG` that is about
resolution. -/
theorem resolves_one : ResolvesTo pq F itemsQ := by
  refine ⟨by rw [pq_length]; rfl, fun i d it hd hit => ⟨_, ?_, rfl⟩⟩
  have hi : i < 5 := by rw [← pq_length]; exact (List.getElem?_eq_some_iff.1 hd).1
  have hdd : d = pq.getD i default := by rw [List.getD_eq_getElem?_getD, hd]; rfl
  subst hdd
  obtain ⟨h0, h1, h2, h3⟩ := res_ind
  have hex : ∃ it', resAt i = .ok (.ok it') := by
    match i, hi with
    | 0, _ => obtain ⟨d, e⟩ := ind_of h0; exact ⟨_, e⟩
    | 1, _ => obtain ⟨d, e⟩ := ind_of h1; exact ⟨_, e⟩
    | 2, _ => obtain ⟨d, e⟩ := ind_of h2; exact ⟨_, e⟩
    | 3, _ => obtain ⟨d, e⟩ := ind_of h3; exact ⟨_, e⟩
    | 4, _ => exact ⟨_, oneDef_of res_one⟩
  have e := resAt_itOf i hex
  have hit' : it = itOf i := by
    match i, hi, hit with
    | 0, _, h => injection h with h; exact h.symm
    | 1, _, h => injection h with h; exact h.symm
    | 2, _, h => injection h with h; exact h.symm
    | 3, _, h => injection h with h; exact h.symm
    | 4, _, h => injection h with h; exact h.symm
  rw [hit']
  exact e

end Ochr.Meaning.Steps.Form.Top.One
