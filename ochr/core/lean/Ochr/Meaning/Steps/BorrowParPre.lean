import Ochr.Meaning.Steps.ColumnW

/-!
# `W`'s body start: `Pre` and `SGood` (lead19, 2026-11-21; docs/31 D144)

The bundles `body_simW` takes at the body's start, instantiated: `Pre` at `stW` in the context `KB "W" outW` (`CtxS`, the
checker's invariant `Inv` of a state with a cell `loan₀` and the live borrow `borrow₀ σ0`, `Asg` for an assignment giving
`σ0` a number), and `SGood` at the reference's body state `SBW`. With `rel_startW` (D140), `body_simW` applies at the
start: `body_runW` (the step, applied at the column's own start).
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Start

namespace Pre'

theorem norm_stW : stW.norm = stW := by
  simp [stW, MState.norm, Env.erase, Frame.erase]

theorem allPos_stW : allPos stW.env = [.bind 0 0, .bind 1 0, .bind 1 1] := allPos_envB

theorem values_stW : Env.values stW.env = [.loan 0, .gfn "W", .borrow 0 (.abs 0)] := by
  rw [Env.values, allPos_stW]; rfl

theorem mem_values {v : Value} (hv : v ∈ Env.values stW.env) : v = .loan 0 ∨ v = .gfn "W" ∨ v = .borrow 0 (.abs 0) := by
  rw [values_stW] at hv; simpa using hv

theorem mem_allPos {p : Pos} (hp : p ∈ allPos stW.env) : p = .bind 0 0 ∨ p = .bind 1 0 ∨ p = .bind 1 1 := by
  rw [allPos_stW] at hp; simpa using hp

theorem live0 : liveLoan stW.env 0 = true := by rw [liveLoan, findBorrow, allPos_stW]; rfl

theorem live_eq {l : Nat} (h : liveLoan stW.env l = true) : l = 0 := liveLoan_envB h

theorem bind_stW {f i : Nat} {b : Binding} (h : stW.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 0 ∧ i = 0 ∧ b = cellR) ∨ (f = 1 ∧ i = 0 ∧ b = selfW) ∨ (f = 1 ∧ i = 1 ∧ b = rB (.borrow 0 (.abs 0))) := by
  rcases f with _ | _ | f
  · rcases i with _ | i
    · simp [stW] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [stW] at h
  · rcases i with _ | _ | i
    · simp [stW] at h; exact .inr (.inl ⟨rfl, rfl, h.symm⟩)
    · simp [stW] at h; exact .inr (.inr ⟨rfl, rfl, h.symm⟩)
    · simp [stW] at h
  · simp [stW] at h

theorem shape_stW (p : Pos) : Env.shape stW.env p = if p = .bind 1 1 then some 0 else none := shape_envB p

theorem sites_stW (l : Nat) : Env.sitesOf stW.env l = if l = 0 then [⟨.bind 0 0, [], false⟩] else [] := sitesOf_envB l

/-- What a read of a place of `stW` can give: the function, the borrow, or its content. -/
theorem ckContent_stW {p : Place} {v : Value} (h : ckContent stW.env p = some v) :
    v = .gfn "W" ∨ v = .borrow 0 (.abs 0) ∨ v = .abs 0 := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stW.env[stW.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    rcases i with _ | _ | i
    · -- `r`
      change (Value.borrow 0 (.abs 0)).follow path = some v at h
      rcases path with _ | ⟨s, ss⟩
      · simp [Value.follow] at h; exact .inr (.inl h.symm)
      · cases s <;> simp [Value.follow, stepV] at h
        rcases ss with _ | ⟨s', ss'⟩
        · simp [Value.follow] at h; exact .inr (.inr h.symm)
        · cases s' <;> simp [Value.follow, stepV] at h
    · change (Value.gfn "W").follow path = some v at h
      rcases path with _ | ⟨s, ss⟩
      · simp [Value.follow] at h; exact .inl h.symm
      · cases s <;> simp [Value.follow, stepV] at h
    · omega
  · have hi' : ¬ i < stW.env[stW.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem occurs_stW {l : Nat} (h : stW.Occurs l) : l = 0 := by
  obtain ⟨v, hv, h⟩ := h
  rcases l with _ | l
  · rfl
  exfalso
  have e1 : (Value.loan 0 == Value.loan (l + 1)) = false := by
    show Value.beq _ _ = false; simp [Value.beq]
  have e2 : (Value.gfn "W" == Value.loan (l + 1)) = false := rfl
  have e3 : (Value.borrow 0 (.abs 0) == Value.loan (l + 1)) = false := rfl
  have e4 : (Value.abs 0 == Value.loan (l + 1)) = false := rfl
  rcases mem_values hv with rfl | rfl | rfl <;> simp [Value.anyAtom, e1, e2, e3, e4] at h

theorem not_refd_ge {σ : Nat} (h : stW.Refd σ) : σ < 1 := by
  refine MState.refd_lt stW 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · intro v hv σ hσ
    rcases mem_values hv with rfl | rfl | rfl
    · cases hσ
    · cases hσ
    · simp only [Value.hasAbs, Value.anyAtom, Bool.or_eq_true] at hσ
      rcases hσ with h | h
      · simp [BEq.beq, Value.beq] at h
      · have := abs_hasAbs_eq (σ := 0) (σ' := σ) (by simpa [Value.hasAbs, Value.anyAtom] using h); omega
  · intro f i b T hb hT σ hσ
    rcases bind_stW hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [cellR, selfW, rB] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT
    rcases bind_stW hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [cellR, selfW, rB] at hT
  · intro G hG σ hσ; simp [stW] at hG; subst hG; exact (Bool.false_ne_true hσ).elim
  · intro m σ' h; simp [stW] at h
  · intro σ' v h; simp [stW] at h
  · intro σ' T h σ hσ
    rcases σ' with _ | σ'
    · simp [stW] at h; subst h; exact (Bool.false_ne_true hσ).elim
    · simp [stW] at h

theorem inv_stW (D : Decisions) : Inv D [] stW := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  -- (WF1)
  · intro p hp; rcases mem_allPos hp with rfl | rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h1 h2; rw [shape_stW] at h1 h2
    split at h1 <;> split at h2 <;> simp_all
  -- (WF2)
  · intro v hv l hl
    rcases mem_values hv with rfl | rfl | rfl <;> simp [Value.outerLoans] at hl
    subst hl; exact live0
  · intro l; rw [values_stW]; simp only [List.flatMap_cons, List.flatMap_nil]
    simp [Value.outerLoans]
    exact List.count_le_length
  -- (WF3)
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, hl⟩ => by
      rcases mem_allPos hp with rfl | rfl | rfl <;> simp [valAt, stW, cellR, selfW, rB] at hw
      obtain ⟨rfl, rfl⟩ := hw; simp [Value.loans] at hl⟩⟩
  -- (WF4)
  · intro v hv; rcases mem_values hv with rfl | rfl | rfl <;> exact Bool.false_ne_true
  -- (WF6)
  · intro σ h; exact not_refd_ge h
  · intro T hT σ hσ; simp [stW] at hT; subst hT; exact (Bool.false_ne_true hσ).elim
  · intro σ r h; simp [stW] at h
  · rfl
  · intro v hv l hl; rcases mem_values hv with rfl | rfl | rfl <;> simp [Value.loans] at hl <;> simp [stW, hl]
  -- (WF8)
  · intro v hv; rcases mem_values hv with rfl | rfl | rfl <;> rfl
  · intro f i b hb T hT; rcases bind_stW hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;>
      simp [cellR, selfW, rB] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stW] at hT; subst hT; rfl
  · intro G hG; simp [stW] at hG; subst hG; rfl
  -- (WF10)
  · intro v hv; rcases mem_values hv with rfl | rfl | rfl <;> rfl
  -- (WF11)
  · intro f i b hb; rcases bind_stW hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [cellR] at hT; subst hT; rfl, fun P ws j h => by simp [cellR] at h⟩
    · exact ⟨fun T hT l => by simp [selfW] at hT; subst hT; rfl, fun P ws j h => by simp [selfW] at h⟩
    · exact ⟨fun T hT l => by simp [rB] at hT; subst hT; rfl, fun P ws j h => by simp [rB] at h⟩
  · intro T hT l; simp [stW] at hT; subst hT; rfl
  · intro G hG l; simp [stW] at hG; subst hG; rfl
  · intro n σ h; simp [stW] at h
  · intro σ v h; simp [stW] at h
  -- (WF12): label `0`'s one site is a loan, not a fill
  · intro k l hk _ x hx hf
    rw [sites_stW, if_pos (live_eq hk)] at hx
    simp at hx; subst hx; cases hf
  -- (WF14): nothing in Ω is `⊥`
  · intro pos path h l hl x hx hxp
    rw [sites_stW, if_pos (live_eq hl)] at hx
    simp only [List.mem_singleton] at hx; subst hx
    simp only at hxp; subst hxp
    change (Value.loan 0).follow path = some .bot at h
    rcases path with _ | ⟨st, ss⟩
    · simp [Value.follow] at h
    · cases st <;> simp [Value.follow, stepV] at h
  -- (WF15), (WF16)
  · intro v hv l; rcases mem_values hv with rfl | rfl | rfl <;> rfl
  · intro v hv; rcases mem_values hv with rfl | rfl | rfl <;> rfl
  -- `ShapeFacts`
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl
    rcases mem_values hv with rfl | rfl | rfl <;> simp [Value.loans] at hl
    subst hl; exact live0
  · intro v hv; rcases mem_values hv with rfl | rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stW h with h | h | h <;> cases h
  · intro σ r h; simp [stW] at h
  · intro σ r h; simp [stW] at h
  · intro σ l h; rcases σ with _ | σ <;> simp [stW] at h
  -- the label counter
  · intro l h; rw [occurs_stW h]; decide
  -- (K): the cell a loan, `W`'s own binding at its Π-type, the borrow parameter at `&Nat`
  · refine (fun f i b hb => ?_)
    · rcases f with _ | _ | f
      · rcases i with _ | i
        · simp only [stW] at hb; cases hb; exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
        · simp [stW] at hb
      · rcases i with _ | _ | i
        · simp only [stW] at hb; cases hb
          exact ⟨fun l c e => (nomatch e), fun l c e => (nomatch e)⟩
        · simp only [stW] at hb; cases hb
          exact ⟨fun l c e T hT => ⟨.tNat, by cases hT; rfl⟩, fun l c e hn => (by cases hn)⟩
        · simp [stW] at hb
      · simp [stW] at hb

end Pre'

open Pre'

section
variable (dm : DataModel) (D : Decisions) (ρ : Assignment) (φ φ' : Future)

theorem find_gW {n : String} {g : GDef} (h : stW.globals.find? (·.name == n) = some g) : n = "W" ∧ g = gW := by
  simp only [stW, List.find?_cons, List.find?_nil] at h
  split at h
  · rename_i hn; cases h; exact ⟨(beq_iff_eq.mp hn).symm, rfl⟩
  · cases h

theorem decRank_gW (K : RunCtx) : decRank K gW = fixRank none := rfl

theorem ctxS_stW : CtxS (KB "W" outW dm D φ) stW where
  inds := List.prefix_refl _
  covers := fun _ h => absurd h List.not_mem_nil
  faithful := fun _ h => absurd h List.not_mem_nil
  noLabel := fun n => by simp only [KB, CB]; split <;> rfl
  globals := {
    ty := fun n g hf hc => absurd (by rw [(find_gW hf).1]; rfl) hc
    const := fun n g hf hn => by rw [(find_gW hf).2] at hn; cases hn
    fn := fun n g t hf _ hc => absurd (by rw [(find_gW hf).1]; rfl) hc
    mem := fun n g hf hc => absurd (by rw [(find_gW hf).1]; rfl) hc
    memBelow := fun n g b hf hcur => by
      obtain ⟨rfl, rfl⟩ := find_gW hf
      simp only [KB, Option.some.injEq, Prod.mk.injEq, true_and] at hcur
      subst hcur
      refine ⟨1, φ, psW, outW, fun _ => none, ⟨Nat.le_succ_of_le (Nat.le_succ 1), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩,
        fun _ _ _ h => absurd h (Nat.not_lt_zero _), ?_, ?_, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
      · simp only [KB, CB, decRank_gW]; rfl
      · simp only [KB, CB, decRank_gW]; rfl }

theorem asg_stW (hρ : ∃ m, ρ 0 = .el0 Nat m) : Asg (KB "W" outW dm D φ) ρ stW := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro σ _ h
    have : σ = 0 := by simp [stW] at h; omega
    subst this; obtain ⟨m, hm⟩ := hρ
    show ρ 0 ∈ₛ[dm.read] MState.absTyM _ _ _ ρ stW 0
    unfold MState.absTyM; exact ⟨m, hm.symm⟩
  · intro n σ h; simp [stW] at h
  · intro σ v h; simp [stW] at h
  · intro σ r h; simp [stW] at h
  · intro σ _ h
    have : σ = 0 := by simp [stW] at h; omega
    subst this; unfold MState.absTyM; rfl
  · intro G h; simp only [MState.goalM, stW, Option.map_some, Option.some.injEq] at h; subst h; rfl
  · intro σ _ h
    have : σ = 0 := by simp [stW] at h; omega
    subst this; rfl

/-- **`Pre` at `W`'s body start**, for an assignment giving `σ0` a number. No assumed fact. -/
theorem pre_stW (hρ : ∃ m, ρ 0 = .el0 Nat m) : Pre (KB "W" outW dm D φ) ρ stW := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stW]
  · exact ctxS_stW dm D φ
  · exact inv_stW D
  · exact asg_stW dm D ρ φ hρ

/-- The stage-0 closure is a member of the weakened type. -/
theorem selfSemB_mem (R : DataRead) (φ : Future) (out : PiCod) (hout : out.isRef = false) :
    selfSemB R φ out ∈ₛ[R] selfTyB R out :=
  stage_mem R 1 φ psW out (fixRank none) 0 (fun _ => none) ⟨Nat.le_refl 1, by omega⟩ hout
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-- **`SGood` at `W`'s reference body state.** No assumed fact. -/
theorem sgood_SBW (m : Nat) : Strict.SGood dm [] φ' (SBW (selfS dm.read φ outW .other) (.ref .other) (.el0 Nat m)) where
  bind := fun ψ hψ f i hp => by
    rw [positions_SBW] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false, Pos.bind.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have h0 := hψ.2 0 (by rw [liveLabels_SBW]; simp)
      exact Strict.goodVal_of_mem dm.read_wholeFields [] (show ψ 0 ∈ₛ[dm.read] TyM.nat from h0)
    · exact Strict.goodVal_of_mem dm.read_wholeFields [] (selfSemB_mem dm.read φ outW rfl)
    · exact Strict.goodVal_of_mem dm.read_wholeFields [] (show Sem.el0 Nat m ∈ₛ[dm.read] TyM.nat from ⟨m, rfl⟩)
  holder := fun ψ _ p l hl => by
    change (if p = .bind 1 1 then some 0 else none) = some l at hl
    split at hl
    · rename_i hp; subst hp; cases hl
      exact dm.pmem_of_mem (s := .el0 Nat m) (T := TyM.nat) [] (by simp [Sem.whole]) ⟨m, rfl⟩
    · cases hl
  held := fun l hl => by
    rw [liveLabels_SBW] at hl; simp at hl; subst hl; exact ⟨m, rfl⟩
  holderTy := fun f i l hl => by
    change (if Pos.bind f i = .bind 1 1 then some 0 else none) = some l at hl
    split at hl
    · rename_i hp; cases hp; cases hl; rfl
    · cases hl
  acyc := by
    refine ⟨fun p ψ ψ' h => ?_, fun r x _ hr => ?_, fun p x hp => ?_⟩
    · have : ψ = ψ' := funext fun y => h y (.inl trivial)
      rw [this]
    · change (if r = .bind 1 1 then some 0 else none) = some x at hr
      split at hr
      · rename_i hp; subst hp; intro ψ ψ' _; rfl
      · cases hr
    · change (if p = .bind 1 1 then some 0 else none) = some x at hp
      split at hp
      · rename_i hp'; subst hp'; cases hp; exact ⟨by rw [positions_SBW]; simp, by show 0 < 1; omega⟩
      · cases hp
  fresh := fun p l h => by
    obtain ⟨ψ, x, hne⟩ := h
    show l < 1
    by_cases hl : l = 0
    · omega
    · exfalso; apply hne
      change SState.valAt _ p ψ = SState.valAt _ p (ψ.upd l x)
      rcases p with ⟨f, i⟩ | ⟨f, i⟩
      · rcases f with _ | _ | f
        · rcases i with _ | i
          · show ψ 0 = (ψ.upd l x) 0
            simp [Future.upd, Ne.symm hl]
          · rfl
        · rcases i with _ | _ | i <;> rfl
        · rfl
      · rcases f with _ | _ | f <;> rfl
  uniq := fun p q l hp hq => by
    change (if p = .bind 1 1 then some 0 else none) = some l at hp
    change (if q = .bind 1 1 then some 0 else none) = some l at hq
    split at hp <;> split at hq <;> simp_all

end

/-- **`W`'s body step, applied at the column's own start**: from the checker's run of `clone(*r)` from `stW`'s kernel, at a
table aligned with the checker at `stW`, the reference's body state `fixBodyAt` builds at the number `m` (which every
`fb` reading the parameter at `Nat`, `.ref .other`, the codomain `.other` gives) meets `Pre`, `Rel` and `SGood`, and
`body_simW`'s conclusion holds there. ASSUMES 2 facts about the checker, `BodyWInv` and `InvNumA`; no model fact. -/
theorem body_outW (hB : BodyWInv) (hN : InvNumA) (dm : DataModel) {D : Decisions} (ρ : Assignment) (φ : Future) (m : Nat)
    (hDW : DecTab D stW) {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {v : Value} {T? : Option Value}
    (hk : Kern stW st) (hm : Mode st) (htd : st.tailDecl = none)
    (h : Runs (Ochr.eval n true bodyW hint) st bh (v, T?) st')
    (fb : List PBind × PBind) (h1 : fb.1 = [(fun _ => .plain TyM.nat, .ref .other)]) (h2 : fb.2.2 = .other) :
    Out (KB "W" outW dm D φ) (ColumnI.ρAt ρ m) φ id st st'
      (startS fb (selfS dm.read φ outW fb.2.2) ⟨true, fun _ => TyM.nat⟩ (.el0 Nat m))
      (runT (KB "W" outW dm D φ) (ColumnI.ρAt ρ m) φ st.tailNext (hintM (KB "W" outW dm D φ) (ColumnI.ρAt ρ m) hint) bodyW)
      v T? := by
  have hR : DecideScope.topReadings st = Aux.RW := by rw [← ColumnC.topReadings_kern hk]; rfl
  have hfl : (KB "W" outW dm D φ).D.flags (DecideScope.topReadings st) bodyW = (false, false) := by
    rw [hR]; exact (fixDecW hDW).2.2.2.2
  have hS : Strict.SGood dm [] φ (startS fb (selfS dm.read φ outW fb.2.2) ⟨true, fun _ => TyM.nat⟩ (.el0 Nat m)) := by
    rw [startS_eq fb h1, h2]; exact sgood_SBW dm φ φ m
  exact body_simW hB hN hk hm htd hfl h _ id ((pre_stW dm D (ColumnI.ρAt ρ m) φ ⟨m, rfl⟩).of_kern hk)
    ((rel_startW dm D ρ φ φ fb h1 h2 m).of_kern hk) hS

end Ochr.Meaning.Steps.Form.ColumnW
