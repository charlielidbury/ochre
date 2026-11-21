import Ochr.Meaning.Strict.FieldWriteCE
import Ochr.Meaning.Steps.Statements
import Ochr.Meaning.SitesFollow
import Ochr.Test

/-!
# The field write that no simulation statement over `Rel` and `SGood` can prove (lead7, 2026-11-21)

REGRESS RECORD (the reference side kernel-checked; the checker side evaluated, `#guard`, since its
[Access] runs through well-founded recursion the kernel does not unfold).

The fundamental lemma's strict run (`Run.lean`, the write rule) tests a write at a field path at
every TYPED future of the reference state (`TypedFut`), which gives each live label an OPEN member of
its recorded type (`moved` included). The simulation relation `Rel` compares the reference state with
the checker's only at futures giving each live label a WHOLE member of its holder's type
(`TypedLive`), and must (docs/31 D66: elsewhere the reference reads a returned borrow's lent place
through the backward function and the checker reads it raw). At the futures `Rel` does not compare,
nothing ties the reference state to the checker's. So a step statement of the form "from every
reference state related to the checker's (`Rel`) and good (`SGood`), the strict run succeeds" is
false at a write to a field, whatever else it assumes of the checker's state.

The checker's state is the one it reaches in the accepted `CW` below at the write `x.0 := Z`: one
frame, `z ↦ loan₀ : Nat`, `y ↦ borrow₀ 0 : &Nat`, `x ↦ S(Z) : Nat` (`#guard`: the hole's values;
the checker's step from it succeeds). Nothing is lent at `x`. The reference state `S₁` has the same
skeleton, holders and lending, and `x` means `1` wherever label `0` holds a number and `0`
elsewhere. It is related to the checker's (`rel_S₁`: at every future `Rel` compares, label `0` holds
a number and `x` means `1`, as the checker's `x` does) and good (`sgood_S₁`: `0` and `1` are both
members of `Nat`). At the typed future giving label `0` the value `moved` (an open member of `Nat`),
`x` means `0`, which has no predecessor: the strict run's write is undefined there, and the run
fails (`runT_S₁`).
-/

open Ochr.Test

ochr FieldWriteGap {
  def CW : Unit := (let z = Z; let y = &z; let x = S(Z); x.0 := Z; ())
}

#guard_msgs (drop warning) in
ochr FieldWriteGapAt {
  def CWAt : Unit := (let z = Z; let y = &z; let x = S(Z); (? : Unit))
}

namespace Ochr.Meaning.Regress.FieldWriteGap
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## The checker's side (evaluated) -/

/-- The values of the bindings the checker holds at the hole of `CWAt` (the editor's Ω, from the
real run). -/
def atHole : List Value :=
  let r := Ochr.Test.runWith none "FieldWriteGapAt" FieldWriteGapAt (located := true)
  match r.rows.find? (·.name == "CWAt") with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

#guard atHole == [.loan 0, .borrow 0 .zero, .succ .zero]

def bz : Binding := { hint := ⟨"z"⟩, ty := some .tNat, val := .loan 0 }
def by' : Binding := { hint := ⟨"y"⟩, ty := some (.tRef .tNat), val := .borrow 0 .zero }
def bx : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := .succ .zero }

/-- The checker's state at the write: `x` is variable `0`, `y` variable `1`, `z` variable `2`. -/
def St : MState := { env := #[{ binds := #[bz, by', bx] }], nextLoan := 1 }

/-- The write `x.0 := Z`. -/
def tW : Term := .assign (.proj 0 (.var 0)) .zero

def isOk {α : Type} (f : M α) (st : MState) (fuel : Nat) : Bool :=
  match runMachine f st fuel with
  | (.ok _ _, _, _) => true
  | _ => false

-- the checker's typed step from `St` succeeds
#guard isOk (Ochr.eval 100000 true tW none) St 1000000
-- (and the guard can fail: a write below the predecessor, where `x.0 = Z` has no field, is rejected)
#guard !isOk (Ochr.eval 100000 true (.assign (.proj 0 (.proj 0 (.var 0))) .zero) none) St 1000000

/-! ## The reference's side (kernel-checked) -/

open Ochr.Meaning.Strict Ochr.Meaning.Strict.FieldWriteCE

/-- `x`'s meaning in the reference state: `1` wherever label `0` holds a number, `0` elsewhere. -/
noncomputable def xval : SVal := fun ψ => match (ψ 0).asNat with
  | some _ => .el0 Nat 1
  | none => .el0 Nat 0

/-- Where label `0` is lent: `z`, by its loan (the checker's site, `Env.sitesOf`). -/
def lent₁ : Nat → List Site := fun l => if l = 0 then [⟨.bind 0 0, [], false⟩] else []

def sh₁ : Pos → Option Nat := fun p => if p = .bind 0 1 then some 0 else none

/-- The reference state: `St`'s skeleton, holders and lending; `x` means `xval`. -/
noncomputable def S₁ : SState where
  env := [{ binds := [{ ty := .plain TyM.nat, val := fun ψ => ψ 0 }, { ty := .plain TyM.nat, val := fun _ => .el0 Nat 0 },
    { ty := .plain TyM.nat, val := xval }] }]
  shape := sh₁
  nextLoan := 1
  lent := lent₁
  heldTy := fun _ => TyM.nat
  heldMem := fun _ => .el0 Nat 0

theorem positions_S₁ : S₁.positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  simp [S₁, SState.positions, List.range']

theorem live_S₁ : S₁.liveLabels = [0] := by
  unfold SState.liveLabels; rw [positions_S₁]; simp [S₁, sh₁]

theorem sh₁_some {p : Pos} {l : Nat} (h : sh₁ p = some l) : p = .bind 0 1 ∧ l = 0 := by
  unfold sh₁ at h
  split at h
  · cases h; rename_i hp; exact ⟨hp, rfl⟩
  · cases h

theorem holderOf_S₁ : S₁.holderOf 0 = some (.bind 0 1) := by
  unfold SState.holderOf; rw [positions_S₁]; simp [S₁, sh₁]

/-- A member of `Nat` is a number. -/
theorem nat_of_mem (dm : DataModel) {v : Sem} (h : v ∈ₛ[dm.read] TyM.nat) : ∃ n, v = .el0 Nat n := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

theorem xval_num {ψ : Future} {n : Nat} (h : ψ 0 = .el0 Nat n) : xval ψ = .el0 Nat 1 := by
  unfold xval; rw [h, Sem.asNat_el0]

theorem xval_cases (ψ : Future) : xval ψ = .el0 Nat 1 ∨ xval ψ = .el0 Nat 0 := by
  unfold xval; split <;> simp

/-- Off label `0`, nothing in `S₁` reads the future. -/
theorem valAt_S₁_indep (p : Pos) (ψ : Future) {l : Nat} (hl : l ≠ 0) (x : Sem) :
    S₁.valAt p (ψ.upd l x) = S₁.valAt p ψ := by
  have h0 : (ψ.upd l x) 0 = ψ 0 := Future.upd_other _ _ (Ne.symm hl)
  cases p with
  | bind f i =>
    rcases f with _ | f
    · rcases i with _ | _ | _ | i
      · exact h0
      · rfl
      · show xval _ = xval _
        unfold xval; rw [h0]
      · rfl
    · rfl
  | temp f i =>
    rcases f with _ | f
    · rfl
    · rfl

/-- **`S₁` is good**, at every data model. -/
theorem sgood_S₁ (dm : DataModel) : SGood dm [] φ₀ S₁ := by
  refine ⟨fun ψ hψ f i hp => ?_, fun ψ hψ p l hl => ?_, fun l _ => nat_mem dm 0, fun f i l hl => ?_,
    ⟨fun p ψ ψ' h => ?_, fun r x _ hs ψ ψ' _ => ?_, fun p x hp => ?_⟩, fun p l ⟨ψ, x, hne⟩ => ?_⟩
  · rw [positions_S₁] at hp
    simp only [List.mem_cons, Pos.bind.injEq, List.mem_nil_iff, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inl (hψ.2 0 (by rw [live_S₁]; simp))
    · exact .inl (.mem (nat_mem dm 0))
    · show GoodVal dm [] (xval ψ) TyM.nat
      rcases xval_cases ψ with h | h <;> rw [h]
      · exact .inl (.mem (nat_mem dm 1))
      · exact .inl (.mem (nat_mem dm 0))
  · obtain ⟨rfl, rfl⟩ := sh₁_some hl
    exact .mem (nat_mem dm 0)
  · obtain ⟨he, rfl⟩ := sh₁_some hl
    cases he; rfl
  · have : ψ = ψ' := funext fun y => h y (.inl trivial)
    rw [this]
  · obtain ⟨rfl, rfl⟩ := sh₁_some hs
    rfl
  · obtain ⟨rfl, rfl⟩ := sh₁_some hp
    exact ⟨by rw [positions_S₁]; simp, by decide⟩
  · show l < 1
    by_cases hl : l = 0
    · omega
    · exact absurd (valAt_S₁_indep p ψ hl x).symm hne

/-! ### The relation -/

theorem allPos_St : allPos St.env = [.bind 0 0, .bind 0 1, .bind 0 2] := by decide +kernel

theorem shape_St (p : Pos) : Env.shape St.env p = sh₁ p := by
  by_cases hp : p ∈ allPos St.env
  · rw [allPos_St] at hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rfl
  · have h1 : Env.shape St.env p = none := by
      cases e : Env.shape St.env p with
      | none => rfl
      | some l => exact absurd (mem_allPos_of_shape e) hp
    rw [h1]
    unfold sh₁
    rw [if_neg]
    intro e; subst e; exact hp (by rw [allPos_St]; simp)

theorem sitesOf_St : Env.sitesOf St.env 0 = [⟨.bind 0 0, [], false⟩] := by
  unfold Env.sitesOf; rw [allPos_St]; rfl

theorem liveLoan_St {l : Nat} (h : liveLoan St.env l = true) : l = 0 := by
  unfold liveLoan findBorrow at h
  rw [allPos_St] at h
  rcases l with _ | l
  · rfl
  · exfalso
    revert h
    simp [List.find?, valAt, St, bz, by', bx, Value.holdsBorrow]

section
variable (dm : DataModel) (ρ : Assignment)

/-- The checker's meanings at its bindings: `z` the future at `0`, `y` the number `0`, `x` the
number `1`; `err` off the state. -/
theorem mean_St (ψ : Future) (f i : Nat) :
    Env.mean (Kc dm).dm (Kc dm).M (Kc dm).Γ ρ ψ St.env (.bind f i) =
      if f = 0 ∧ i = 0 then ψ 0 else if f = 0 ∧ i = 1 then .el0 Nat 0
      else if f = 0 ∧ i = 2 then .el0 Nat 1 else .err := by
  rcases f with _ | f
  · rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · simp [Env.mean, St, bx, Value.mean, Sem.succ, Sem.asNat_el0]
    · simp [Env.mean, St]
  · simp [Env.mean, St]

theorem valAt_S₁ (ψ : Future) (f i : Nat) :
    S₁.valAt (.bind f i) ψ =
      if f = 0 ∧ i = 0 then ψ 0 else if f = 0 ∧ i = 1 then .el0 Nat 0
      else if f = 0 ∧ i = 2 then xval ψ else .err := by
  rcases f with _ | f
  · rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · simp [SState.valAt, S₁]
  · simp [SState.valAt, S₁]

theorem holderTy_S₁ : holderTy S₁ 0 = TyM.nat := by
  unfold holderTy; rw [holderOf_S₁]; rfl

theorem skel_St : (SM' (Kc dm) ρ St).env.map (fun fr => fr.binds.map bindSkel) =
    S₁.env.map (fun fr => fr.binds.map bindSkel) := by
  rfl

theorem sh₁_temp (f i : Nat) : sh₁ (.temp f i) = none := by
  unfold sh₁; rw [if_neg]; intro h; cases h

/-- **`S₁` simulates the checker's state**, with no renaming: the same skeleton, holders and lending,
and at every future the relation compares (label `0` a number) the same meanings. -/
theorem rel_S₁ : Rel (Kc dm) ρ φ₀ id St S₁ where
  skel := skel_St dm ρ
  fresh := fun _ hl _ => hl
  sim := by
    refine ⟨fun ψ hψ p hp => ?_, fun p l _ h => ?_, fun p l' _ h => ?_, fun f i l h => ?_, fun f j l' h => ?_⟩
    · cases p with
      | temp => exact absurd trivial hp
      | bind f i =>
        show Env.mean (Kc dm).dm (Kc dm).M (Kc dm).Γ ρ (fun l => ψ (id l)) St.env (.bind f i) = _
        rw [mean_St, valAt_S₁]
        by_cases h2 : f = 0 ∧ i = 2
        · obtain ⟨rfl, rfl⟩ := h2
          have hm := (hψ.2 0 (by show 0 ∈ S₁.liveLabels; rw [live_S₁]; simp)).2
          rw [holderTy_S₁] at hm
          obtain ⟨n, hn⟩ := nat_of_mem dm hm
          simp [xval_num hn]
        · simp only [h2, if_false]
          rfl
    · show sh₁ p = some l
      rw [← shape_St]; exact h
    · exact ⟨l', by show Env.shape St.env p = some l'; rw [shape_St]; exact h, rfl⟩
    · exfalso
      have : Env.shape St.env (.temp f i) = some l := h
      rw [shape_St, sh₁_temp] at this; cases this
    · exfalso
      have : sh₁ (.temp f j) = some l' := h
      rw [sh₁_temp] at this; cases this
  inj := fun _ _ _ _ h => h
  sites := fun l hl x => by
    rw [liveLoan_St hl]
    show x ∈ lent₁ 0 ↔ x ∈ Env.sitesOf St.env 0
    rw [sitesOf_St]; simp [lent₁]
  holders := fun p l h => by
    obtain ⟨rfl, rfl⟩ := sh₁_some h
    rw [positions_S₁]; simp
  records := fun l hl => by
    have : l ∈ S₁.liveLabels := hl
    rw [live_S₁] at this
    have hl0 : l = 0 := by simpa using this
    subst hl0
    rw [holderTy_S₁]
    exact ⟨by simp [S₁, Sem.whole], nat_mem dm 0⟩

/-! ### The strict run fails -/

/-- [Access] of `x` at `.0` reaches no label: label `0` is lent at `z` only. -/
theorem access_S₁ : S₁.access (.bind 0 2) (dataHit [.proj 0]) = S₁ := by
  have hr : S₁.reached (.bind 0 2) (dataHit [.proj 0]) = fun _ => false := by
    funext l
    unfold SState.reached
    show (lent₁ l).any _ = false
    unfold lent₁
    split <;> simp
  have hstep : (S₁.liveLabels.filter (S₁.reached (.bind 0 2) (dataHit [.proj 0]))).foldl SState.endLabel S₁ = S₁ := by
    rw [hr, live_S₁]; rfl
  unfold SState.access
  rw [live_S₁]
  simp only [List.length_singleton]
  exact hstep

/-- The typed future at which label `0` holds `moved` (an open member of `Nat`). -/
def ψ₀ : Future := φ₀.upd 0 .moved

theorem typedFut_ψ₀ : TypedFut (Kc dm) φ₀ S₁ ψ₀ := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · have hl0 : l ≠ 0 := by intro e; subst e; exact hl (by rw [live_S₁]; simp)
    exact Future.upd_other _ _ hl0
  · rw [live_S₁] at hl
    have hl0 : l = 0 := by simpa using hl
    subst hl0
    show DataModel.OMem dm [] TyM.nat (ψ₀ 0)
    rw [show ψ₀ 0 = .moved from Future.upd_same _ _ _]
    exact .moved _

/-- **The write at `x.0` is undefined at a typed future**, so the strict write fails: at `ψ₀`, `x`
means `0`, which has no predecessor. -/
theorem setContent_S₁ (v : Sem) : setContent (Kc dm) φ₀ (.bind 0 2) [.proj 0] v S₁ = none := by
  unfold setContent
  rw [if_neg]
  intro hall
  have h := hall ψ₀ (typedFut_ψ₀ dm)
  have hx : S₁.valAt (.bind 0 2) ψ₀ = .el0 Nat 0 := by
    show xval ψ₀ = _
    unfold xval
    rw [show ψ₀ 0 = .moved from Future.upd_same _ _ _]
    rfl
  have hu : Sem.updAt dm [] (.plain TyM.nat) (fun _ => v) [.proj 0] (Sem.el0 Nat 0) = none := by
    rw [Sem.updAt.eq_def]
    simp [Sem.asNat_el0]
  rw [hx] at h
  change (Sem.updAt dm [] (.plain TyM.nat) (fun _ => v) [.proj 0] (Sem.el0 Nat 0)).isSome = true at h
  rw [hu] at h
  cases h

theorem resolve_S₁ : resolve S₁ (.proj 0 (.var 0)) = some (.bind 0 2, [.proj 0]) := rfl

theorem assignAt_S₁ (v : Sem) (lab : Option Nat) : assignAt (Kc dm) φ₀ (.proj 0 (.var 0)) v lab S₁ = none := by
  unfold assignAt
  rw [resolve_S₁]
  simp only [List.isEmpty_cons, Bool.false_and, Bool.false_eq_true, if_false, access_S₁, setContent_S₁]

/-- **The strict run of `x.0 := Z` fails from `S₁`**, in or out of tail position, at any hint:
whatever the outcome of its test of the value written, its write is undefined at `ψ₀`. -/
theorem runT_S₁ (tl : Bool) (hint : TyS) : runT (Kc dm) ρ φ₀ tl hint tW S₁ = none := by
  have hz : ∀ (T : TyS) (s : SState), runT (Kc dm) ρ φ₀ false T .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) :=
    fun _ _ => by rw [runT]; rfl
  unfold tW
  rw [runT]
  show SM.erasedIf (false, false) _ S₁ = none
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [bind, Option.bind, hz, assignAt_S₁]
  split <;> rfl

/-- **The gap.** At every data model and assignment: the reference state `S₁` simulates the checker's
state `St` (`Rel`, no renaming), is good (`SGood`), the context meets the fundamental lemma's
obligations (`FundCtx`), and the strict run of `x.0 := Z` fails from `S₁`, in or out of tail position,
at any hint; while the checker's typed step from `St` succeeds (`#guard` above). The checker-side
hypotheses of a step (`Pre`: the assignment typed, `WF`, `CtxOk`) are about `St` and the context, and
constrain the reference state only through `Rel`; they are not proved here. -/
theorem fieldWrite_gap (dm : DataModel) (ρ : Assignment) :
    Rel (Kc dm) ρ φ₀ id St S₁ ∧ SGood (Kc dm).dm (Kc dm).Γ φ₀ S₁ ∧ FundCtx (Kc dm) ∧
      ∀ tl hint, runT (Kc dm) ρ φ₀ tl hint tW S₁ = none :=
  ⟨rel_S₁ dm ρ, sgood_S₁ dm, fundCtx_Kc dm, runT_S₁ dm ρ⟩

end

end Ochr.Meaning.Regress.FieldWriteGap
