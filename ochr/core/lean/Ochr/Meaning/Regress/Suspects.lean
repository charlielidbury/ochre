import Ochr.Meaning.Regress.OpenFalse

/-!
# The inventory's reading-only suspects, checked (sixth lead, `Meaning/OPEN.md`; kernel-checked)

1. **`owners_sound_stmt` is false at an ordinary reborrow** (`owners_sound_false`). After
   `let r = &x; let s = &*r`, the state is `x ↦ loan₀`, `r ↦ borrow₀(loan₁)`, `s ↦ borrow₁ 0`: good
   at every assignment (`good_SRb`). `r` means its content, the final content of the reborrow `1`, so
   its meaning depends on the label `1`; but `owners 1` follows the holder `r`'s own borrow `0` to its
   lender and lists only `x` (`owners_SRb`, evaluated by the kernel). The statement's "conversely
   every position whose meaning depends on `l` is among them" misses a reborrow's holder.
-/

namespace Ochr.Meaning.Regress.Suspects
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-! ## 1. `owners_sound` -/

def bx : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := .loan 0 }
def br : Binding := { hint := ⟨"r"⟩, ty := some (.tRef .tNat), val := .borrow 0 (.loan 1) }
def bs : Binding := { hint := ⟨"s"⟩, ty := some (.tRef .tNat), val := .borrow 1 .zero }

/-- `let r = &x; let s = &*r`: `x` lent to `0`, `r`'s content lent to `1`. -/
def SRb : MState := { env := #[{ binds := #[bx, br, bs] }], nextLoan := 2 }

theorem owners_SRb : owners SRb.env 1 = [.bind 0 0] := by decide +kernel

theorem allPos_SRb : allPos SRb.env = [.bind 0 0, .bind 0 1, .bind 0 2] := by decide +kernel

theorem values_SRb : Env.values SRb.env = [.loan 0, .borrow 0 (.loan 1), .borrow 1 .zero] := by
  rw [Env.values, allPos_SRb]; rfl

theorem bind_SRb (f i : Nat) (b : Binding) (h : SRb.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    f = 0 ∧ ((i = 0 ∧ b = bx) ∨ (i = 1 ∧ b = br) ∨ (i = 2 ∧ b = bs)) := by
  rcases f with _ | f
  · rcases i with _ | _ | _ | i
    · simp [SRb] at h; exact ⟨rfl, .inl ⟨rfl, h.symm⟩⟩
    · simp [SRb] at h; exact ⟨rfl, .inr (.inl ⟨rfl, h.symm⟩)⟩
    · simp [SRb] at h; exact ⟨rfl, .inr (.inr ⟨rfl, h.symm⟩)⟩
    · simp [SRb] at h
  · simp [SRb] at h

theorem posTyM_SRb (dm : DataModel) (C : CodeMeaning) (Γ : List IndDecl) (ρ : Assignment) (p : Pos) (T : TyM)
    (h : MState.posTyM dm C Γ ρ SRb p = some T) :
    T = TyM.nat ∧ (p = .bind 0 0 ∨ p = .bind 0 1 ∨ p = .bind 0 2) := by
  cases p with
  | temp => simp [MState.posTyM] at h
  | bind f i =>
    simp only [MState.posTyM] at h
    split at h
    · rename_i b hb
      obtain ⟨rfl, hi⟩ := bind_SRb f i b hb
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [bx, br, bs, Value.tyM, Value.mean, Sem.asTy] at h <;> exact ⟨h.symm, by simp⟩
    · cases h

theorem shape_SRb (p : Pos) (l : Nat) (h : Env.shape SRb.env p = some l) :
    (p = .bind 0 1 ∧ l = 0) ∨ (p = .bind 0 2 ∧ l = 1) := by
  have hm := mem_allPos_of_shape h
  rw [allPos_SRb] at hm
  simp at hm
  rcases hm with rfl | rfl | rfl
  · simp [Env.shape, valAt, SRb, bx] at h
  · simp [Env.shape, valAt, SRb, br] at h; exact .inl ⟨rfl, h.symm⟩
  · simp [Env.shape, valAt, SRb, bs] at h; exact .inr ⟨rfl, h.symm⟩

theorem nat_whole (s : Sem) (dm : DataModel) (h : s ∈ₛ[dm.read] TyM.nat) : s.whole := by
  obtain ⟨n, rfl⟩ := h; simp [Code0.enc, Sem.whole]

/-- **The reborrow state is good at every assignment.** -/
theorem good_SRb (K : RunCtx) (ρ : Assignment) : Good K.dm K.M K.Γ ρ SRb := by
  have hV := values_SRb
  have hA := allPos_SRb
  have hsites : ∀ l x, x ∈ Env.sitesOf SRb.env l →
      (x = ⟨.bind 0 0, [], false⟩ ∧ l = 0) ∨ (x = ⟨.bind 0 1, [.deref], false⟩ ∧ l = 1) := by
    intro l x h
    simp only [Env.sitesOf, hA, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at h
    have e0 : valAt SRb.env (.bind 0 0) = .loan 0 := rfl
    have e1 : valAt SRb.env (.bind 0 1) = .borrow 0 (.loan 1) := rfl
    have e2 : valAt SRb.env (.bind 0 2) = .borrow 1 .zero := rfl
    rw [e0, e1, e2] at h
    rcases h with h | h | h
    · simp only [Value.sitesOf] at h; split at h <;> simp at h; exact .inl ⟨h, by omega⟩
    · simp only [Value.sitesOf] at h; split at h <;> simp at h; exact .inr ⟨h, by omega⟩
    · simp [Value.sitesOf] at h
  refine ⟨⟨fun σ _ h => by simp [SRb] at h, fun n σ h => by simp [SRb] at h,
      fun σ v h => by simp [SRb] at h, fun σ r h => by simp [SRb] at h⟩,
    ⟨?_, fun σ _ h => by simp [SRb] at h, fun G h => by simp [MState.goalM, SRb] at h⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ hφ p T hp
    obtain ⟨rfl, hp'⟩ := posTyM_SRb K.dm K.M K.Γ ρ p T hp
    have h0 : φ 0 ∈ₛ[K.dm.read] TyM.nat := hφ (.bind 0 1) 0 rfl TyM.nat
      (by simp [MState.posTyM, SRb, br, Value.tyM, Value.mean, Sem.asTy])
    have h1 : φ 1 ∈ₛ[K.dm.read] TyM.nat := hφ (.bind 0 2) 1 rfl TyM.nat
      (by simp [MState.posTyM, SRb, bs, Value.tyM, Value.mean, Sem.asTy])
    rcases hp' with rfl | rfl | rfl
    · exact DataModel.pmem_of_mem _ _ (nat_whole _ K.dm h0) h0
    · exact DataModel.pmem_of_mem _ _ (nat_whole _ K.dm h1) h1
    · exact DataModel.pmem_of_mem K.dm K.Γ (by simp [Env.mean, SRb, bs, Value.mean, Sem.whole]) ⟨0, rfl⟩
  · rw [hA]; intro p hp; simp at hp
    rcases hp with rfl | rfl | rfl
    · show ¬ (Value.loan 0).hasBorrow = true; decide
    · show ¬ (Value.loan 1).hasBorrow = true; decide
    · show ¬ (Value.zero).hasBorrow = true; decide
  · intro p _ q _ l hp hq
    rcases shape_SRb p l hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases shape_SRb q _ hq with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | rfl | omega
  · rw [hV]; intro v hv l hl; simp at hv
    rcases hv with rfl | rfl | rfl <;> simp [Value.outerLoans] at hl <;> subst hl <;> decide +kernel
  · intro l; rw [hV]
    simp only [List.flatMap_cons, List.flatMap_nil, Value.outerLoans, List.append_nil]
    by_cases h0 : l = 0
    · subst h0; decide
    · by_cases h1 : l = 1
      · subst h1; decide
      · simp [List.count_cons]; split <;> split <;> omega
  · have hlu : ∀ l m, loanUnder SRb.env l m → l = 1 ∧ m = 0 := by
      rintro l m ⟨p, hp, w, hw, hl⟩
      rw [hA] at hp; simp at hp
      rcases hp with rfl | rfl | rfl
      · simp [valAt, SRb, bx] at hw
      · simp [valAt, SRb, br] at hw; obtain ⟨rfl, rfl⟩ := hw; simp [Value.loans] at hl; exact ⟨hl, rfl⟩
      · simp [valAt, SRb, bs] at hw; obtain ⟨rfl, rfl⟩ := hw; simp [Value.loans] at hl
    have acc1 : Acc (loanUnder SRb.env) 1 := ⟨_, fun c hc => absurd (hlu c 1 hc).2 (by decide)⟩
    exact ⟨fun a => ⟨a, fun b hb => by obtain ⟨rfl, rfl⟩ := hlu b a hb; exact acc1⟩⟩
  · unfold WF4; rw [hV]; intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> decide
  · exact MState.refd_lt _ _
      (by rw [hV]; intro v hv σ h; simp at hv
          rcases hv with rfl | rfl | rfl <;> simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b T hb hT σ h => by
        obtain ⟨_, hi⟩ := bind_SRb f i b hb
        rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [bx, br, bs] at hT <;> subst hT <;>
          simp [Value.hasAbs, Value.anyAtom, BEq.beq, Value.beq] at h)
      (fun f i b P ws j hb hT => by
        obtain ⟨_, hi⟩ := bind_SRb f i b hb
        rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [bx, br, bs] at hT)
      (fun G hG => by simp [SRb] at hG) (fun m σ' h => by simp [SRb] at h)
      (fun σ' v h => by simp [SRb] at h) (fun σ' T h => by simp [SRb] at h)
  · intro T hT; simp [SRb] at hT
  · intro σ r h; simp [SRb] at h
  · simp [SRb]
  · rw [hV]; intro v hv l hl; simp at hv
    rcases hv with rfl | rfl | rfl <;> simp [Value.loans] at hl <;> subst hl <;> simp [SRb]
  · intro p T _ f i b _ hb A hA'
    obtain ⟨_, hi⟩ := bind_SRb f i b hb
    rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [bx, br, bs] at hA' <;> subst hA' <;> rfl
  · rw [hV]; intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> decide
  · intro f i b hb T hT
    obtain ⟨_, hi⟩ := bind_SRb f i b hb
    rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [bx, br, bs] at hT <;> subst hT <;> decide
  · intro T hT; simp [SRb] at hT
  · intro G hG; simp [SRb] at hG
  · intro p hp hl; rw [hA] at hp; simp at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · simp [valAt, SRb, bs, Value.outerLoans] at hl
  · intro v hv; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl | rfl <;> rfl
  · intro f i b hb
    obtain ⟨_, hi⟩ := bind_SRb f i b hb
    rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      exact ⟨fun T hT l => by simp [bx, br, bs] at hT; subst hT; rfl, fun P ws j h => by simp [bx, br, bs] at h⟩
  · intro T hT; simp [SRb] at hT
  · intro G hG; simp [SRb] at hG
  · intro n σ h; simp [SRb] at h
  · intro σ v h; simp [SRb] at h
  · refine ⟨?_, ?_, ?_⟩
    · intro k l _ _ x hxs hfill
      rcases hsites k x hxs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases hfill
    · intro pos path hf l _ x hxs hpos
      rcases hsites l x hxs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> subst hpos
      · have e0 : valAt SRb.env (.bind 0 0) = .loan 0 := rfl
        rw [e0] at hf
        cases path with
        | nil => cases hf
        | cons st ss => cases st <;> simp [Value.follow, stepV] at hf
      · have e1 : valAt SRb.env (.bind 0 1) = .borrow 0 (.loan 1) := rfl
        rw [e1] at hf
        cases path with
        | nil => cases hf
        | cons st ss =>
          cases st with
          | deref =>
            cases ss with
            | nil => simp [Value.follow, stepV] at hf
            | cons st' ss' => cases st' <;> simp [Value.follow, stepV] at hf
          | _ => simp [Value.follow, stepV] at hf
    · refine ⟨?_, ?_⟩
      · intro v hv l; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl | rfl <;> rfl
      · intro v hv; rw [hV] at hv; simp at hv; rcases hv with rfl | rfl | rfl <;> rfl

/-- **`owners_sound_stmt` is false** (any fuel, any context admitting the reborrow state): `r`'s
meaning depends on the reborrow's label `1`, and `owners 1` is `[x]`. -/
theorem owners_sound_false (K : RunCtx) (ρ : Assignment) (φ : Future) (fuel : Nat) (hctx : CtxOk K ρ SRb) :
    ¬ owners_sound_stmt K ρ φ fuel := by
  intro hs
  have hl : liveLoan SRb.env 1 = true := by decide +kernel
  have hdep : (MState.mean K.dm K.M K.Γ ρ SRb).dependsOn (.bind 0 1) 1 := by
    refine ⟨fun _ => .err, .moved, ?_⟩
    simp [MState.mean, Env.mean, SRb, br, Value.mean, Future.upd]
  have h := hs SRb 1 (.bind 0 1) (good_SRb K ρ) hctx hl hdep
  rw [owners_SRb] at h
  simp at h

/-! ## 2. `proof_step`: an inlined captured proof is trusted at its type

`capture` inlines a captured proof as `(⋆ : T)`, and `evalCore`'s `.ascribe (.val .proof) A` returns
`⋆` at `A` with no check. So `(⋆ : Eq(Nat, 0, 1))` runs, typed, to `⋆` at `False` (the equation
computes to `False`); `proof_step_stmt` then concludes `⋆` a member of `False`. True of the states
`capture` produces (a captured proof was a member where it was captured); the statement needs that as
a hypothesis, or (C1) with the inlined form strict at its type (docs/31 D83). -/

def pf : Term := .ascribe (.val .proof) (.eq .nat .zero (.succ .zero))
abbrev ep : M (Value × Option Value) := Ochr.eval 60 true pf none

def isPF : Value × Option Value → Bool
  | (.proof, some (.tInd "False" [])) => true
  | _ => false

theorem isPF_eq {p : Value × Option Value} (h : isPF p = true) : p = (.proof, some (.tInd "False" [])) := by
  unfold isPF at h; split at h
  · rfl
  · cases h

open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out) in
theorem okP : isOk ep (Regress.EvalMemGap.S0.withTemp .zero) 60 = true := by decide +kernel
open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out) in
theorem pfP : isPF (outVal ep (Regress.EvalMemGap.S0.withTemp .zero) 60) = true := by decide +kernel

open Ochr.Meaning.Regress.GenNeutralContent (outSt outVal isOk runs_out) in
/-- **`proof_step_stmt` is false** (fuel 60, any context admitting the empty frame with `0` in flight,
reading `(⋆ : Eq(Nat, 0, 1))` as a proof, its decisions aligned after): the checker returns `⋆` at
`False`, which has no member (in this context no declaration is named `False`, so its meaning is the
error type; with the library's `False` it is the empty proposition). -/
theorem proof_step_false (K : RunCtx) (ρ : Assignment) (φ : Future)
    (hctx : CtxOk K ρ (Regress.EvalMemGap.S0.withTemp .zero))
    (hfl : (K.D.flags (scopeOf (SM' K ρ (Regress.EvalMemGap.S0.withTemp .zero))) pf).2 = true)
    (hD : DecTab K.D (outSt ep (Regress.EvalMemGap.S0.withTemp .zero) 60)) :
    ¬ proof_step_stmt K ρ φ 60 := by
  intro hs
  have hrel : Rel K ρ φ id (Regress.EvalMemGap.S0.withTemp .zero) (SM' K ρ (Regress.EvalMemGap.S0.withTemp .zero)) :=
    Rel.start_noLive K ρ φ _ (fun l hl => by
      exfalso
      simp [SState.Live, SState.liveLabels, SM', MState.sstate, Env.shape, Regress.EvalMemGap.S0,
        MState.withTemp, valAt, SState.positions] at hl)
  have hr : Runs ep (Regress.EvalMemGap.S0.withTemp .zero) 60 (.proof, some (.tInd "False" []))
      (outSt ep (Regress.EvalMemGap.S0.withTemp .zero) 60) := by
    have := runs_out ep _ 60 okP
    rwa [isPF_eq pfP] at this
  obtain ⟨-, ρ', Δ', -, -, hmem⟩ :=
    hs _ _ true pf none (.tInd "False" []) (Regress.EvalMemGap.good_S0T K ρ) hctx _ id hrel hfl hD 60 hr
  have hΓ : K.Γ = [] := hctx.inds
  have e : (meanV { K with Δ := Δ' } ρ' φ (.plain .err) (.tInd "False" [])).asTy = TyM.err := by
    simp [meanV, hΓ, Sem.asTy]
  rw [e] at hmem
  obtain ⟨a, -⟩ := hmem
  exact nomatch a

end Ochr.Meaning.Regress.Suspects
