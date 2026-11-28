import Ochr.Meaning.Steps.TopR

/-!
# The acceptance test at `R`: the start of the check at a bound (`FixStartAt`; lead46, docs/31 D259 on)

`FixStartAt` at `R`'s program, at the witness the checker's inversion gives (`w.st₀ = st0R P.inds u`: the column's
`stRm` with the stage's declarations). The parts: `Pre` at the check's context with the start's `Δa` (the declarations
faithful there, by a transfer from the stage's context: the library's declarations name no global, so their runs read
neither the function under check nor `R`'s meaning; `GlobalsOk` with `R`'s own `memBelow` from the knot's induction
hypothesis; the invariant and the assignment as the column's), the start relation (the checker's start state read as a
reference state IS `fixBodyAt`'s), the frame good, the table aligned, the hint the codomain.
-/

namespace Ochr.Meaning.Steps.Form.Top.RT

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master
open Ochr.Consistency Ochr.Surface Ochr.Meaning.Assembly
open Ochr.Meaning.Steps.Form.ColumnR Ochr.Meaning.Steps.Form.FixEqDesc
open Ochr.Meaning.Steps.Form.ColumnI (psI outI ρAt nB piNat)
open Ochr.Meaning.DataModel.Exists.Knot (NameOk Term.nok KN AgreeN)

/-! ## The stage's declarations are the library's -/

/-- Along inductive declarations only, every declaration of the stage is one of the start's or has the parameters and
constructors of one of the items (the checker stores it with its nestable set computed). -/
theorem inds_ind_items (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (ρ : Assignment) (cfg : Config)
    (fuel : Nat) : ∀ (its : List Item) (P : ProgState), (∀ it ∈ its, ∃ d, it = .ind d) →
      ∀ d' ∈ (progMeaningFrom dm D Γ ρ cfg fuel P its).inds,
        d' ∈ P.inds ∨ ∃ d, Item.ind d ∈ its ∧ d'.params = d.params ∧ d'.ctors = d.ctors
  | [], _, _, d', h => .inl h
  | it :: its, P, h, d', hd' => by
    simp only [progMeaningFrom, List.foldl_cons] at hd'
    obtain ⟨d, rfl⟩ := h it List.mem_cons_self
    rcases inds_ind_items dm D Γ ρ cfg fuel its _ (fun x hx => h x (List.mem_cons_of_mem _ hx)) d' hd' with h1 | ⟨d₁, hm, hp, hc⟩
    · unfold ProgState.step at h1
      dsimp only at h1
      split at h1
      · rename_i st' hst
        rw [((Steps.Machine.checkItem_tables (.ind d) _ st' fuel hst).1 d rfl).1] at h1
        rcases List.mem_append.1 h1 with h2 | h2
        · exact .inl h2
        · simp only [List.mem_singleton] at h2
          subst h2
          exact .inr ⟨d, List.mem_cons_self, rfl, rfl⟩
      · exact .inl h1
    · exact .inr ⟨d₁, List.mem_cons_of_mem _ hm, hp, hc⟩

/-- The name test that admits no global at all. -/
def NG : NameOk := ⟨fun _ => true, fun _ => true, fun _ => false⟩

/-- A declaration's parameter and field types name no global. -/
def declNok (d : IndDecl) : Bool :=
  d.params.all (fun p => Term.nok NG p.2) && d.ctors.all (fun c => c.2.all (fun f => Term.nok NG f.2))

/-- The resolved item names no global in its declaration's types (`true` off an inductive declaration). -/
def itemNok : Except Exhausted (Except String Item) → Bool
  | .ok (.ok (.ind d)) => declNok d
  | _ => true

set_option maxRecDepth 100000 in
theorem res_nok : itemNok (resAt 0) = true ∧ itemNok (resAt 1) = true ∧ itemNok (resAt 2) = true ∧
    itemNok (resAt 3) = true := by decide +kernel

/-- **Every declaration of `R`'s stage names no global in its types** (PROVED: the stage's declarations are the
library's, as the checker stores them; the library's types, by the kernel's run of resolution). -/
theorem stage_declNok {dm : DataModel} {D : MState → Decisions} {Γ : List IndDecl} {items : List Item}
    (hr : ResolvesTo pq F items) {P : ProgState} (hin : AtStage dm D Γ F items P (.defn defR)) :
    ∀ d ∈ P.inds, declNok d = true := by
  obtain ⟨hl, hind, h4⟩ := items_shape hr
  obtain ⟨k, hk, rfl⟩ := hin
  have hk4 : k = 4 := by
    have hk5 : k < 5 := hl ▸ (List.getElem?_eq_some_iff.1 hk).1
    rcases Nat.lt_or_ge k 4 with h | h
    · obtain ⟨d', hd'⟩ := hind k h _ hk
      cases hd'
    · omega
  subst hk4
  have htake : ∀ it ∈ items.take 4, ∃ d, it = .ind d := by
    intro it hit
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hit
    rw [List.getElem_take] at e
    simp only [List.length_take] at hi
    exact hind i (by omega) it (by rw [← e]; exact List.getElem?_eq_getElem _)
  intro d' hd'
  rcases inds_ind_items dm D Γ (fun _ => .err) {} F (items.take 4) {} htake d' hd' with h | ⟨d, hm, hp, hc⟩
  · simp at h
  · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
    simp only [List.length_take] at hi
    rw [List.getElem_take] at e
    have hi4 : i < 4 := by omega
    have hres := items_at hr i (.ind d) (by rw [← e]; exact List.getElem?_eq_getElem (by omega))
    obtain ⟨h0, h1, h2, h3⟩ := res_nok
    have hn : itemNok (resAt i) = true := by
      match i, hi4 with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | 2, _ => exact h2
      | 3, _ => exact h3
    rw [hres] at hn
    have hn' : declNok d = true := hn
    unfold declNok at hn' ⊢
    rw [hp, hc]
    exact hn'

theorem nok_field {d : IndDecl} (h : declNok d = true) {c i : Nat} {FT : Term} (hf : fieldTerm d c i = some FT) :
    Term.nok NG FT = true := by
  unfold declNok at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  unfold fieldTerm at hf
  simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at hf
  obtain ⟨f, ⟨ct, hct, hfi⟩, rfl⟩ := hf
  exact h.2 ct (List.mem_of_getElem? hct) f (List.mem_of_getElem? hfi)

theorem nok_param {d : IndDecl} (h : declNok d = true) {j : Nat} {hn : Hint} {PT : Term}
    (hp : d.params[j]? = some (hn, PT)) : Term.nok NG PT = true := by
  unfold declNok at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 _ (List.mem_of_getElem? hp)

/-- **Faithfulness carries to a context with other globals and another function under check** where the declarations'
types name no global (their runs read neither, `Knot.runT_congrN`). -/
theorem declFaithful_C {K : RunCtx} {d : IndDecl} (hd : declNok d = true) (C' : CodeMeaning) (c : Option (String × Nat))
    (Δ' : Nat → TyS) (h : DeclFaithful K d) : DeclFaithful { K with C := C', cur := c, Δ := Δ' } d := by
  intro Δ ρ
  obtain ⟨hf, hp, hrec⟩ := h Δ ρ
  have hA : AgreeN { K with Δ := Δ } K.dm C' NG :=
    ⟨fun _ _ _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ hn => by cases hn⟩
  refine ⟨fun ps ci i e FT hl hpt hft he hFT r s' hrun => ?_, fun ps j hn PT hpt hj hPT r s' hrun => ?_,
    ⟨hrec.types, hrec.values, hrec.smallOnly, hrec.leafOk⟩⟩
  · refine hf ps ci i e FT hl hpt hft he hFT r s' ?_
    rw [DataModel.Exists.Knot.run_congrN { K with Δ := Δ } K.dm C' NG ρ noFuture (cur' := c) hA FT _ _ (nok_field hd hFT)]
    exact hrun
  · refine hp ps j hn PT hpt hj hPT r s' ?_
    rw [DataModel.Exists.Knot.run_congrN { K with Δ := Δ } K.dm C' NG ρ noFuture (cur' := c) hA PT _ _ (nok_param hd hPT)]
    exact hrun


/-! ## The generic state of `R`'s check, and `Pre` there -/

/-- `R`'s binding of itself, marked with the check's uid `u` (the checker takes the next fresh mark; nothing reads its value,
only that it is set). -/
def selfRu (u : Nat) : Binding := { selfR with recUid := some u }

/-- The frames at `R`'s generic state, its own binding marked `u`. -/
def envU (u : Nat) : Env := #[{}, { binds := #[selfRu u, nB] }]

/-- **The state `checkFix` checks `R`'s body from**, at the stage's declarations `I` and the fresh mark `u`: the column's
`stRm` (frame 1 holds `R`'s marked binding of itself and `n ↦ σ0`, the [Rec] context with the entry `σ0`, the goal
`Nat`), the mark `u` for the column's `0`. -/
def st0R (I : List IndDecl) (u : Nat) : MState :=
  { stR with inds := I, env := envU u, typing := true, recStack := [{ rcR with uid := u }], nextRecUid := u + 1 }

/-- Its kernel. -/
def stRI (I : List IndDecl) (u : Nat) : MState := { stR with inds := I, env := envU u }

theorem norm_st0R (I : List IndDecl) (u : Nat) : (st0R I u).norm = stRI I u := by
  simp [st0R, stRI, stR, envU, MState.norm, Env.erase, Frame.erase]

theorem stRI_env (I : List IndDecl) (u : Nat) : (stRI I u).env = envU u := rfl

theorem allPos_envU (u : Nat) : allPos (envU u) = [.bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [envU, frameAllPos, List.range_succ]

theorem values_envU (u : Nat) : Env.values (envU u) = [.gfn "R", .abs 0] := by
  rw [Env.values, allPos_envU]; rfl

theorem bind_envU {u f i : Nat} {b : Binding} (h : (envU u)[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 1 ∧ i = 0 ∧ b = selfRu u) ∨ (f = 1 ∧ i = 1 ∧ b = nB) := by
  rcases f with _ | _ | f
  · simp [envU] at h
  · rcases i with _ | _ | i
    · simp [envU] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [envU] at h; exact .inr ⟨rfl, rfl, h.symm⟩
    · simp [envU] at h
  · simp [envU] at h

theorem shape_envU (u : Nat) (p : Pos) : Env.shape (envU u) p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem liveLoan_envU (u l : Nat) : liveLoan (envU u) l = false := by
  rw [liveLoan, findBorrow, allPos_envU]; rfl

theorem sitesOf_envU (u l : Nat) : Env.sitesOf (envU u) l = [] := by
  unfold Env.sitesOf; rw [allPos_envU]; simp [valAt, envU, selfRu, selfR, nB, Value.sitesOf]

theorem occurs_envU (u : Nat) (st : MState) (he : st.env = envU u) (l : Nat) : ¬ st.Occurs l := by
  rintro ⟨w, hw, h⟩
  rw [he, values_envU] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact Bool.false_ne_true h

theorem refd_stRI {I : List IndDecl} {u σ : Nat} (h : (stRI I u).Refd σ) : σ < 1 := by
  refine MState.refd_lt (stRI I u) 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ; rw [stRI_env, values_envU] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (Bool.false_ne_true hσ).elim
    · have := abs_hasAbs_eq hσ; omega
  · intro f i b T hb hT σ hσ; rw [stRI_env] at hb
    rcases bind_envU hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfRu, selfR, nB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT; rw [stRI_env] at hb
    rcases bind_envU hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfRu, selfR, nB] at hT
  · intro G hG σ hσ; simp [stRI, stR] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stRI, stR] at h
  · intro σ' v h; simp [stRI, stR] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stRI, stR] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stRI, stR] at h

theorem ckContent_stRI {I : List IndDecl} {u : Nat} {p : Place} {v : Value} (h : ckContent (stRI I u).env p = some v) :
    v = .gfn "R" ∨ v = .abs 0 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < (stRI I u).env[(stRI I u).env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "R" ∨ w = .abs 0) → w.follow path = some v → v = .gfn "R" ∨ v = .abs 0 := by
      rintro w hw hf
      cases path with
      | nil => simp [Value.follow] at hf; exact hf ▸ hw
      | cons s ss => rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < (stRI I u).env[(stRI I u).env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem steps_nil {p : Place} {i : Nat} (h : p.steps = (i, [])) : p = .var i := by
  cases p with
  | var j => simp [Place.steps] at h; rw [h]
  | deref q => simp only [Place.steps] at h; injection h with _ h; simp at h
  | proj j q => simp only [Place.steps] at h; injection h with _ h; simp at h
  | field g q => simp only [Place.steps] at h; injection h with _ h; simp at h

/-- Only `R`'s own binding holds the function. -/
theorem ckContent_stRI_gfn {I : List IndDecl} {u : Nat} {p : Place} (h : ckContent (stRI I u).env p = some (.gfn "R")) :
    p = .var 1 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < (stRI I u).env[(stRI I u).env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    rcases i with _ | _ | i
    · have h0 : (Value.abs 0).follow path = some (.gfn "R") := h
      cases path with
      | nil => simp [Value.follow] at h0
      | cons s ss => cases s <;> simp [Value.follow, stepV] at h0
    · have h1 : (Value.gfn "R").follow path = some (.gfn "R") := h
      cases path with
      | nil => exact steps_nil hp
      | cons s ss => cases s <;> simp [Value.follow, stepV] at h1
    · omega
  · have hi' : ¬ i < (stRI I u).env[(stRI I u).env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem topReadings_stRI (I : List IndDecl) (u : Nat) : DecideScope.topReadings (stRI I u) = ColumnP.RI := rfl

/-- **The checker's invariant at `R`'s generic state** (any declaration list; a table reading `R`'s own binding as a
function, as every aligned one does): the column's `inv_stR` with the stage's declarations. -/
theorem inv_stRI (D : Decisions) (Γ : List IndDecl) (I : List IndDecl) (u : Nat)
    (hpd1 : D.placeDecl ColumnP.RI (.var 1) = .pi .other) : Inv D Γ (stRI I u) := by
  have hvals : ∀ v ∈ Env.values (stRI I u).env, v = .gfn "R" ∨ v = .abs 0 := fun v hv => by
    rw [stRI_env, values_envU] at hv; simpa using hv
  have hpos : ∀ p ∈ allPos (stRI I u).env, p = .bind 1 0 ∨ p = .bind 1 1 := fun p hp => by
    rw [stRI_env, allPos_envU] at hp; simpa using hp
  have hbind : ∀ {f i b}, (stRI I u).env[f]?.bind (fun fr => fr.binds[i]?) = some b →
      (f = 1 ∧ i = 0 ∧ b = selfRu u) ∨ (f = 1 ∧ i = 1 ∧ b = nB) := fun hb => bind_envU hb
  have hsh : ∀ p, Env.shape (stRI I u).env p = none := fun p => shape_envU u p
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp; rcases hpos p hp with rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [hsh] at h; cases h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro l; rw [stRI_env, values_envU]; exact Nat.zero_le _
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases hpos p hp with rfl | rfl <;> cases hw⟩⟩
  · intro v hv; rcases hvals v hv with rfl | rfl <;> exact Bool.false_ne_true
  · intro σ h; exact refd_stRI h
  · intro T hT σ hσ; simp [stRI, stR] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stRI, stR] at h
  · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [selfRu, selfR, nB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stRI, stR] at hT; subst hT; rfl
  · intro G hG; simp [stRI, stR] at hG; subst hG; rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro f i b hb; rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [selfRu, selfR] at hT; subst hT; rfl, fun P ws j h => by simp [selfRu, selfR] at h⟩
    · exact ⟨fun T hT l => by simp [nB] at hT; subst hT; rfl, fun P ws j h => by simp [nB] at h⟩
  · intro T hT l; simp [stRI, stR] at hT; subst hT; rfl
  · intro G hG l; simp [stRI, stR] at hG; subst hG; rfl
  · intro n σ h; simp [stRI, stR] at h
  · intro σ v h; simp [stRI, stR] at h
  · intro k l hk; rw [stRI_env, liveLoan_envU] at hk; cases hk
  · intro pos path _ l hl; rw [stRI_env, liveLoan_envU] at hl; cases hl
  · intro v hv l; rcases hvals v hv with rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p v n args hc hpd _
    rcases ckContent_stRI hc with rfl | rfl
    · rw [ckContent_stRI_gfn hc, topReadings_stRI, hpd1] at hpd; cases hpd
    · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stRI h with h | h <;> cases h
  · intro σ r h; simp [stRI, stR] at h
  · intro σ r h; simp [stRI, stR] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stRI, stR] at h
  · intro l h; exact absurd h (occurs_envU u (stRI I u) (stRI_env I u) l)
  · refine (fun f i b hb => ?_)
    · rcases hbind hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
      · exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩


/-! ## `R`'s own clause: `memBelow` from the knot's induction hypothesis -/

/-- **The stage closure under `MemBelow`** at any context reading the model `R`, where `fn` is good below `b`
(`ColumnRSplit.memBelow_GR` at every context). -/
theorem memBelow_GRK (K : RunCtx) {φ : Future} {b : Nat} {fn : List Sem → Option BodyOut}
    (hgb : GoodBelow K.dm.read b fn) : MemBelow K (GR K.dm.read φ b fn) gR b := by
  refine ⟨1, φ, psI, outI, fn, ⟨Nat.le_succ_of_le (Nat.le_succ 1), fun _ _ _ => Nat.le_refl 1⟩,
    fun _ args _ _ => ⟨trivial, fun i d hi => ?_⟩, ?_, ?_, fun args ha hlt => ?_⟩
  · rcases i with _ | i
    · simp [psI] at hi; subst hi; exact Nat.le_refl 1
    · simp [psI] at hi
  · rw [decRank_gR]; rfl
  · rw [decRank_gR]; rfl
  · obtain ⟨m, rfl⟩ := domMembers_one ha
    rw [decRank_gR, rkR_nat] at hlt
    obtain ⟨o, ho, hg, hf⟩ := hgb m hlt
    exact ⟨o, ho, hg, fun h => by simp [outI] at h, by rw [hf]; rfl⟩

section
variable {dm : DataModel} {Γ : List IndDecl}

/-- The stage's function at bound `b` (what the knot's induction hypothesis is about). -/
noncomputable abbrev fnB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) :
    List Sem → Option BodyOut :=
  stG (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b

/-- **The stage closure `R` means at bound `b` is the column's `GR`** (under `DecR`). -/
theorem stageClo_GR (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D) (ρ : Assignment) (φ : Future) (b : Nat) :
    stageClo (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b = GR dm.read φ b (fnB (dm := dm) (Γ := Γ) P st ρ φ b) := by
  unfold stageClo fnB
  generalize stG (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b = f
  rw [psG_R _ ρ hd, outG_R _ ρ, lG_R _ hd]
  rfl

/-- **The knot's induction hypothesis, in the column's form** (under `DecR`). -/
theorem goodBelow_of_B (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D) (ρ : Assignment) (φ : Future) (b : Nat)
    (hIH : GoodBelowB (KS dm Γ P st) ρ φ defR b) : GoodBelow dm.read b (fnB (dm := dm) (Γ := Γ) P st ρ φ b) := by
  intro m hm
  have ha : DomMembers dm.read (psG (KS dm Γ P st) ρ φ defR.doms) [.el0 Nat m] := by
    show DomMembers dm.read (psG (KS dm Γ P st) ρ φ [.nat]) [.el0 Nat m]
    rw [psG_R _ ρ hd]; exact domMembers_nat _ m
  obtain ⟨o, ho, hg⟩ := hIH [.el0 Nat m] ha (by show rkR [.el0 Nat m] < b; rw [rkR_nat]; exact hm)
  change OutGood' dm.read (psG (KS dm Γ P st) ρ φ [.nat]) (outG (KS dm Γ P st) ρ φ [.nat] .nat) [.el0 Nat m] o at hg
  rw [psG_R _ ρ hd, outG_R _ ρ] at hg
  refine ⟨o, ho, hg.1, ?_⟩
  have := hg.2.2
  simp [psI] at this
  exact this

/-- The check's context at bound `b` for `R`, with `Δa`. -/
noncomputable abbrev KB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) : RunCtx :=
  ctxBΔ dm (chainDecisions F) Γ P defR st ρ φ b Δa

theorem KB_R (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) :
    (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).C.global "R" = stageClo (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b := by
  rfl

/-- **`GlobalsOk` at `R`'s generic state in the check's context** (Σ holds `R` alone; every clause but `codeValFree`
and `memBelow` is about globals other than the one under check). -/
theorem globalsOk_B (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D) (ρ : Assignment) (φ : Future) (b : Nat)
    (Δa : Nat → TyS) (hgb : GoodBelow dm.read b (fnB (dm := dm) (Γ := Γ) P st ρ φ b)) {st₀ : MState}
    (hg : st₀.globals = [gR]) : GlobalsOk (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) st₀ where
  ty := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  const := fun n g hf hn => by rw [hg] at hf; rw [(find_gR hf).2] at hn; cases hn
  fn := fun n g t hf _ hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  mem := fun n g hf hc => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  fixEq := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  accepted := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  retKind := fun n _ _ _ _ _ _ _ hf hc _ => by rw [hg] at hf; exact absurd (by rw [(find_gR hf).1]; rfl) hc
  codeValFree := fun n g t hf ht => by
    rw [hg] at hf; obtain ⟨-, rfl⟩ := find_gR hf
    simp only [gR, Option.some.injEq] at ht; subst ht; rfl
  memBelow := fun n g b' hf hcur => by
    rw [hg] at hf
    obtain ⟨rfl, rfl⟩ := find_gR hf
    have hb : b' = b := by
      have : (some ("R", b) : Option (String × Nat)) = some ("R", b') := hcur
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at this; exact this.symm
    subst hb
    rw [KB_R, stageClo_GR P st hd ρ φ b']
    exact memBelow_GRK _ hgb

/-- **The assignment at `R`'s generic state** in the check's context with `Δa = ΔP` (`σ0 : Nat` read at its number). -/
theorem asg_B (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (I : List IndDecl) (u : Nat) (ρa : Assignment)
    (hρ : ∃ m, ρa 0 = .el0 Nat m) : Asg (KB (dm := dm) (Γ := Γ) P st ρ φ b ColumnP.ΔP) ρa (stRI I u) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stRI h; omega
    rw [ColumnP.absTyM_nat _ _ (st := stRI I u) rfl]; obtain ⟨m, hm⟩ := hρ; exact ⟨m, hm.symm⟩
  · intro n σ h; simp [stRI, stR] at h
  · intro σ v h; simp [stRI, stR] at h
  · intro σ r h; simp [stRI, stR] at h
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stRI h; omega
    rw [ColumnP.absTyM_nat _ _ (st := stRI I u) rfl]; rfl
  · intro G h; simp only [MState.goalM, stRI, stR, Option.map_some, Option.some.injEq] at h; subst h; rfl
  · intro σ h _
    obtain rfl : σ = 0 := by have := refd_stRI h; omega
    rfl

/-- **`Pre` at `R`'s generic state in the check's context at bound `b`** (`Δa = ΔP`, the assignment giving `σ0` a
number): the declarations faithful there (from the stage's faithfulness, the library's types naming no global), every
global with no label, `GlobalsOk`, the invariant, the assignment. -/
theorem pre_B (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D)
    (hpd1 : (KS dm Γ P st).D.placeDecl ColumnP.RI (.var 1) = .pi .other) (ρ : Assignment) (φ : Future) (b : Nat)
    (hgb : GoodBelow dm.read b (fnB (dm := dm) (Γ := Γ) P st ρ φ b)) (hPm : P.means = [])
    (hΓP : P.inds <+: Γ) (hcov : ∀ d ∈ Γ, dm.covers d) (hfaith : DeclsFaithful (KS dm Γ P st) P.inds)
    (hnok : ∀ d ∈ P.inds, declNok d = true) (u : Nat) (ρa : Assignment) (hρ : ∃ m, ρa 0 = .el0 Nat m) :
    Pre (KB (dm := dm) (Γ := Γ) P st ρ φ b ColumnP.ΔP) ρa (st0R P.inds u) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_st0R]
  · refine ⟨hΓP, hcov, fun d hdm => declFaithful_C (K := KS dm Γ P st) (hnok d hdm) (ctxB dm (chainDecisions F) Γ P defR st ρ φ b).C (some ("R", b)) ColumnP.ΔP (hfaith d hdm), fun n => ?_,
      globalsOk_B P st hd ρ φ b _ hgb rfl⟩
    show (if n = "R" then _ else P.baseC.global n).2.label = none
    split
    · rfl
    · show (P.globalTy n).label = none
      unfold ProgState.globalTy
      rw [hPm]
      rfl
  · exact inv_stRI _ _ _ u hpd1
  · exact asg_B P st ρ φ b P.inds u ρa hρ

/-- The stage closure, abbreviated. -/
noncomputable abbrev GS (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) : Sem × TyS :=
  stageClo (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b

/-- **The checker's generic state, read as a reference state in the check's context**: `[{}, frR G a]` (`env_SMR` in
the check's context). -/
theorem env_SMB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) (I : List IndDecl) (u : Nat)
    (ρ' : Assignment) (a : Nat) :
    (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) (ρAt ρ' a) (st0R I u)).env = [{}, frR (GS (dm := dm) (Γ := Γ) P st ρ φ b) a] := by
  have h0 : Binding.refTy (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).dm (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).M
      (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).Γ (ρAt ρ' a) (st0R I u).env 1 0 (selfRu u) =
      .plain (GS (dm := dm) (Γ := Γ) P st ρ φ b).2.m := by
    rw [Binding.refTy_marked _ _ _ _ _ _ _ _ u rfl rfl]
    show TyS.plain (((KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).C.global "R").2.m) = _
    rw [KB_R]
  have h1 : Binding.refTy (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).dm (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).M
      (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).Γ (ρAt ρ' a) (st0R I u).env 1 1 nB = .plain TyM.nat := by
    rw [Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]; rfl
  have hv0 : ∀ ψ, Env.mean (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).dm (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).M
      (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).Γ (ρAt ρ' a) ψ (st0R I u).env (.bind 1 0) = (GS (dm := dm) (Γ := Γ) P st ρ φ b).1 := by
    intro ψ
    show ((KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).C.global "R").1 = _
    rw [KB_R]
  have hv1 : ∀ ψ, Env.mean (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).dm (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).M
      (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).Γ (ρAt ρ' a) ψ (st0R I u).env (.bind 1 1) = .el0 Nat a := fun _ => rfl
  unfold SM' MState.sstate
  simp only [st0R, envU, List.zipIdx, List.map, frR, Nat.zero_add]
  rw [show (#[{}, { binds := #[selfRu u, nB] }] : Env) = (st0R I u).env from rfl, h0, h1]
  simp only [List.cons.injEq, SFrame.mk.injEq, SBinding.mk.injEq, and_true, true_and]
  exact ⟨⟨funext hv0, rfl⟩, funext hv1, rfl⟩

/-- **`startAt` at `R` is the checker's generic state read as a reference state** in the check's context (`start_R`,
and the two readings of the same frames agree). -/
theorem startAt_B (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D) (ρ : Assignment) (φ : Future) (b : Nat)
    (Δa : Nat → TyS) (I : List IndDecl) (u : Nat) (m : Nat) :
    startAt (KS dm Γ P st) ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b [.el0 Nat m] =
      SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) (ρAt ρ m) (st0R I u) := by
  have hst := start_R (dm := dm) (D := (KS dm Γ P st).D) (b := b) (G := GS (dm := dm) (Γ := Γ) P st ρ φ b) rfl ρ
    (fbG (KS dm Γ P st) ρ φ [.nat] .nat) (fbG_R1 _ ρ hd) (fbG_R2 _ ρ hd) m
  unfold startAt
  dsimp only
  rw [psG_R _ ρ hd, show formG = emptyState 0 from rfl, hst]
  apply ColumnI.sstate_ext
  · rw [env_SMR rfl, env_SMB]
  · funext p; unfold SM'; rw [sstate_shape, sstate_shape, shape_stR]; exact (shape_envU u p).symm
  · rfl
  · funext l; show Env.sitesOf stR.env l = Env.sitesOf (envU u) l; rw [sitesOf_stR, sitesOf_envU]
  · rfl
  · rfl

theorem shape_SMB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) (I : List IndDecl) (u : Nat)
    (ρ' : Assignment) (p : Pos) : (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).shape p = none := by
  unfold SM'; rw [sstate_shape]; exact shape_envU u p

theorem liveLabels_SMB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS)
    (I : List IndDecl) (u : Nat) (ρ' : Assignment) : (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).liveLabels = [] := by
  unfold SState.liveLabels
  rw [List.filterMap_eq_nil_iff.mpr (fun p _ => shape_SMB P st ρ φ b Δa I u ρ' p), List.mergeSort_nil]

/-- **The start relation at `R`** (no live label: `Rel.start`). -/
theorem rel_B (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) (I : List IndDecl) (u : Nat)
    (ρ' : Assignment) : Rel (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' φ id (st0R I u) (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)) :=
  Rel.start_noLive _ _ _ _ fun l h => by simp [SState.Live, liveLabels_SMB] at h

theorem positions_SMB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS)
    (I : List IndDecl) (u : Nat) (ρ' : Assignment) :
    (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).positions = [.bind 1 0, .bind 1 1] := by
  unfold SM'; rw [sstate_positions]; exact allPos_envU u

theorem valAt_SMB (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS) (I : List IndDecl) (u : Nat)
    (ρ' : Assignment) (p : Pos) (ψ : Future) :
    (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).valAt p ψ =
      match p with
      | .bind 1 0 => (GS (dm := dm) (Γ := Γ) P st ρ φ b).1
      | .bind 1 1 => ρ' 0
      | _ => .err := by
  unfold SM'; rw [sstate_valAt]
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rfl
    · rcases i with _ | _ | i
      · show ((KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).C.global "R").1 = _
        rw [KB_R]; rfl
      · rfl
      · rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem tyAt_SMB_self (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS)
    (I : List IndDecl) (u : Nat) (ρ' : Assignment) :
    ((SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).tyAt (.bind 1 0)).m = (GS (dm := dm) (Γ := Γ) P st ρ φ b).2.m := by
  unfold SM'
  rw [sstate_tyAt_bind _ _ _ _ _ 1 0 { binds := #[selfRu u, nB] } (selfRu u) rfl rfl,
    Binding.refTy_marked _ _ _ _ _ _ _ _ u rfl rfl]
  show (((KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).C.global "R").2.m) = _
  rw [KB_R]

theorem tyAt_SMB_n (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future) (b : Nat) (Δa : Nat → TyS)
    (I : List IndDecl) (u : Nat) (ρ' : Assignment) :
    ((SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).tyAt (.bind 1 1)).m = TyM.nat := by
  unfold SM'
  rw [sstate_tyAt_bind _ _ _ _ _ 1 1 { binds := #[selfRu u, nB] } nB rfl rfl, Binding.refTy_unmarked _ _ _ _ _ _ _ _ rfl]
  rfl

/-- **The start's frame is good** (the stage closure a member of its weakened type, the parameter a number). -/
theorem sgood_B (P : ProgState) (st : MState) (hd : DecR (KS dm Γ P st).D) (ρ : Assignment) (φ : Future) (b : Nat)
    (Δa : Nat → TyS) (I : List IndDecl) (u : Nat) (hgb : GoodBelow dm.read b (fnB (dm := dm) (Γ := Γ) P st ρ φ b))
    (ρ' : Assignment) (hρ : ∃ m, ρ' 0 = .el0 Nat m) (φ' : Future) :
    Strict.SGood dm Γ φ' (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)) where
  bind := fun ψ _ f i hp => by
    rw [positions_SMB] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false, Pos.bind.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [valAt_SMB, tyAt_SMB_self]
      have hm : (GS (dm := dm) (Γ := Γ) P st ρ φ b).1 ∈ₛ[dm.read] (GS (dm := dm) (Γ := Γ) P st ρ φ b).2.m := by
        rw [GS, stageClo_GR P st hd ρ φ b]; exact GR_mem hgb
      exact Strict.goodVal_of_mem dm.read_wholeFields Γ hm
    · rw [valAt_SMB, tyAt_SMB_n]
      obtain ⟨m, hm⟩ := hρ
      exact Strict.goodVal_of_mem dm.read_wholeFields Γ (show ρ' 0 ∈ₛ[dm.read] TyM.nat from ⟨m, hm.symm⟩)
  holder := fun ψ _ p l hl => by rw [shape_SMB] at hl; cases hl
  held := fun l hl => by rw [liveLabels_SMB] at hl; cases hl
  holderTy := fun f i l hl => by rw [shape_SMB] at hl; cases hl
  acyc := ⟨fun p ψ ψ' _ => by rw [valAt_SMB, valAt_SMB], fun r x _ hr => (by rw [shape_SMB] at hr; cases hr),
    fun p x hp => (by rw [shape_SMB] at hp; cases hp)⟩
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    exact absurd (show (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).valAt p ψ =
      (SM' (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) ρ' (st0R I u)).valAt p (ψ.upd l x) by rw [valAt_SMB, valAt_SMB]) hne
  uniq := fun p _ l hp _ => by rw [shape_SMB] at hp; cases hp

end

namespace Aux
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)
open Ochr.Meaning.Steps.Form.ColumnR.Aux (pdRun)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem ok_pd_1 (st : MState) : isOk (pdRun (.var 1)) (scopeState st ColumnP.RI) 1000 = true := by rfl
theorem val_pd_1 (st : MState) : outVal (pdRun (.var 1)) (scopeState st ColumnP.RI) 1000 = .pi .other := by rfl
end Aux

/-- An aligned table reads `R`'s own binding as a function (`.pi .other`), at every state. -/
theorem pd_self {D : Decisions} {st : MState} (hd : DecTab D st) : D.placeDecl ColumnP.RI (.var 1) = .pi .other := by
  open Ochr.Meaning.Regress.GenNeutralContent in
  rw [hd.placeDecl 100 ColumnP.RI (.var 1) _ 1000 _ (runs_out (ColumnR.Aux.pdRun (.var 1)) _ 1000 (Aux.ok_pd_1 st)),
    Aux.val_pd_1]

/-- **The tie at `R`'s generic state** (R1, lead47, docs/31 D284): the [Rec] stack is `R`'s entry alone (`checkFix`'s push
at an empty stack), `K.cur = ("R", b)`, and the entry's unknown `σ0` is sent to `m ≤ b`. -/
theorem recTie_B {dm : DataModel} {Γ : List IndDecl} (P : ProgState) (st : MState) (ρ : Assignment) (φ : Future)
    (b : Nat) (Δa : Nat → TyS)
    (I : List IndDecl) (u m : Nat) (hm : m < b + 1) :
    RecTie (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa) (ρAt ρ m) (st0R I u) where
  glob := by
    intro ctx hctx
    simp only [st0R, List.mem_singleton] at hctx
    subst hctx
    exact ⟨"R", rfl⟩
  cur := by
    intro h hh
    simp [st0R, rcR, BEq.beq, Value.beq] at hh
    subst hh
    rfl
  on := by
    intro g hg
    have hg' : g = "R" := by
      have e : (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).cur.map (·.1) = some "R" := rfl
      rw [e] at hg; exact (Option.some.inj hg).symm
    subst hg'
    simp [st0R, rcR, BEq.beq, Value.beq]
  rank := by
    intro n b' hc ctx hctx _ j σ hj he
    have e : (KB (dm := dm) (Γ := Γ) P st ρ φ b Δa).cur = some ("R", b) := rfl
    rw [e] at hc
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    simp only [st0R, List.mem_singleton] at hctx
    subst hctx
    simp only [rcR, List.mem_singleton] at hj
    subst hj
    simp [rcR] at he
    subst he
    show semHeight (ρAt ρ m 0) ≤ b
    simp [ρAt, semHeight, Sem.asNat_el0]
    omega
  below := by
    intro ctx hctx j σ he
    simp only [st0R, List.mem_singleton] at hctx
    subst hctx
    rcases j with _ | j
    · simp [rcR] at he
      subst he
      show 0 < (st0R I u).absTy.size
      simp [st0R, stR]
    · simp [rcR] at he

/-- **`FixStartAt` at `R`** (PROVED at every witness whose generic state is `st0R` of the stage's declarations and whose
end state's tables grow to the item's end state; the inversion of `R`'s check gives such a witness, `TopRCheck`). At each
bound `b` and number `m < b + 1`: the assignment `σ0 ↦ m`, `Δa = ΔP`; `Pre` (`pre_B`), the start relation (`rel_B`),
the frame good (`sgood_B`), the body closed, the table aligned (`DecTab.back`), the hint the codomain `Nat`. -/
theorem fixStart_R {dm : DataModel} {Γ : List IndDecl} {items : List Item} (hr : ResolvesTo pq F items) {P : ProgState}
    {st' : MState} (hin : AtStage dm (chainDecisions F) Γ F items P (.defn defR)) (hPg : P.globals = []) (hPm : P.means = [])
    (hg' : st'.globals = [gR]) (hi' : st'.inds = P.inds) (hfaith : DataFaithful dm (chainDecisions F) Γ P)
    (hcov : ∀ d ∈ Γ, dm.covers d) (hΓP : P.inds <+: Γ) (w : FixWit) (u : Nat) (hw0 : w.st₀ = st0R P.inds u)
    (hw1 : TablesGrow w.st₁ st') : FixStartAt dm (chainDecisions F) Γ P defR st' w := by
  intro ρ φ b a hIH ha hlt
  have hd : DecR (KS dm Γ P st').D := decR_KS (m := false) (rest := []) P st' hg'
  have hpd1 := pd_self (One.decTab_chain F st')
  change DomMembers dm.read (psG (KS dm Γ P st') ρ φ [.nat]) a at ha
  rw [psG_R _ ρ hd] at ha
  obtain ⟨m, rfl⟩ := domMembers_one ha
  have hgb := goodBelow_of_B P st' hd ρ φ b hIH
  have hρ : ∃ k, ρAt ρ m 0 = .el0 Nat k := ⟨m, by simp [ρAt]⟩
  refine ⟨ρAt ρ m, ColumnP.ΔP, id, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · rw [hw0]
    exact pre_B P st' hd hpd1 ρ φ b hgb hPm hΓP hcov (hfaith st' hi' (by rw [hPg]; exact List.nil_prefix))
      (stage_declNok hr hin) u (ρAt ρ m) hρ
  · rw [hw0]
    exact recTie_B P st' ρ φ b ColumnP.ΔP P.inds u m
      (by simpa [fixRank, defR, semRank, semHeight, Sem.asNat_el0] using hlt)
  · show Rel (KB (dm := dm) (Γ := Γ) P st' ρ φ b ColumnP.ΔP) (ρAt ρ m) φ id w.st₀
      (startAt (KS dm Γ P st') ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b [.el0 Nat m])
    rw [hw0, startAt_B P st' hd ρ φ b ColumnP.ΔP P.inds u m]
    exact rel_B P st' ρ φ b ColumnP.ΔP P.inds u (ρAt ρ m)
  · show Strict.SGood dm Γ φ (startAt (KS dm Γ P st') ρ φ [⟨"n"⟩] [.nat] .nat (some 0) bodyR b [.el0 Nat m])
    rw [startAt_B P st' hd ρ φ b ColumnP.ΔP P.inds u m]
    exact sgood_B P st' hd ρ φ b ColumnP.ΔP P.inds u hgb (ρAt ρ m) hρ φ
  · simp [defR, bodyR, Term.valsOk, Term.valsOkList]
  · intro σ h; simp [defR, bodyR, Term.anyAtom, Term.anyAtomList] at h
  · exact (One.decTab_chain F st').back hw1
  · rw [hw0]
    show hintM (KB (dm := dm) (Γ := Γ) P st' ρ φ b ColumnP.ΔP) (ρAt ρ m) (some .tNat) =
      fixCod (KS dm Γ P st') ρ φ formG (bindsOf (KS dm Γ P st') ρ φ formG [.nat]) [false] .nat [.el0 Nat m]
    unfold fixCod
    rw [ColumnI.codOf_nat]
    rfl

end Ochr.Meaning.Steps.Form.Top.RT
