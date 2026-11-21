import Ochr.Meaning.Steps.FrameFrag
import Ochr.Meaning.Steps.ColumnJ

/-!
# `J2`'s call: the relation at the callee's state (lead16, 2026-11-21; docs/31 D132)

`def J2 : Nat := (let x = S(Z); I(x))`. Glue (c) of docs/31 D128's plan, its relation part: the checker's callee
state at the call (`stCJ2`: the caller's frame `{x ↦ ⊥ : Nat}`, the callee's frame `{I ↦ .gfn I : Π(n : Nat). Nat`
unmarked, `n ↦ S(Z)` LAZILY typed`}`, as `runBodyCore` pushes it; pinned below against the checker's recorded
state) is related to the in-place reference state `inPlaceJ2 s₂ f 1` (the caller's reference state with the
callee's frame pushed, `CallRef.callFrame`), from every reference state `s₂` related to the caller after the
argument's read, at every context whose global `I` means `f` at `Π(n : Nat). Nat` and which reads `I`'s
declared type and the deferred parameter type as the reference's frame stores them.
-/

namespace Ochr.Meaning.Steps.Form.CallJ2

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnI (piNat gI psI outI NoBorrow liveLabels_of_rel)
open Ochr.Meaning.Steps.Form.FrameJ2 (inPlaceJ2 nBind inPlaceJ2_env)

/-- `x`, holding `v`, at `Nat`. -/
def xB (v : Value) : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := v, decl := .other }

/-- The callee's binding of itself at a call: `I`'s global at its declared type, NOT marked. -/
def selfU : Binding := { hint := ⟨"I"⟩, ty := some piNat, val := .gfn "I", decl := .pi .other }

/-- The callee's parameter at a call: the argument, its type DEFERRED to `I`'s Π-type at the argument. -/
def nLazy (w : Value) : Binding :=
  { hint := ⟨"n"⟩, ty := none, val := w, decl := .other, lazyTy := some (piNat, [w], 0) }

/-- The caller's state after the argument's read: `x` moved. -/
def stX : MState := { env := #[{ binds := #[xB .bot] }], globals := [gI] }

/-- **The callee's state at `J2`'s call** (its kernel). -/
def stCJ2 : MState := { env := #[{ binds := #[xB .bot] }, { binds := #[selfU, nLazy (.succ .zero)] }], globals := [gI] }

namespace Guards

open Ochr.Meaning.Steps.Form.ParGuards (bindOk)

/-- The recorded callee state agrees with `stCJ2` on its kernel. -/
def calleeKernOk (st : MState) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.size == 1 && bindOk st.env[0]!.binds[0]! "x" .bot .tNat .other none &&
  st.env[0]!.temps.isEmpty && st.env[1]!.temps.isEmpty && st.env[1]!.binds.size == 2 &&
  bindOk st.env[1]!.binds[0]! "I" (.gfn "I") piNat (.pi .other) none &&
  (let b := st.env[1]!.binds[1]!
   b.hint.name == "n" && b.val == .succ .zero && b.ty.isNone && ParGuards.declIs b.decl .other && !b.proof &&
     b.recUid.isNone && !b.cap && b.lazyTy.any fun (P, ws, i) => P == piNat && ws == [.succ .zero] && i == 0) &&
  (match st.globals with | [g] => ParGuards.globalOk g "I" bodyI | _ => false) && st.inds.isEmpty &&
  st.absTy.isEmpty && st.nextAbs == 0 && st.nextLoan == 0 && st.goal.isNone && st.refs.isEmpty &&
  st.etaRefs.isEmpty && st.neutrals.isEmpty && !st.liveScope && st.absDecl.isEmpty

-- the body's entry, as the checker records it in `J2`'s check, has `stCJ2`'s kernel
#guard match FrameJ2.Guards.deep with
  | (false, _, st) :: _ => calleeKernOk st
  | _ => false

end Guards

/-! ## The relation at the callee's state -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem shape_stX (p : Pos) : Env.shape stX.env p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f
    · rcases i with _ | i <;> rfl
    · rfl
  · rcases f with _ | f <;> rfl

theorem shape_stCJ2 (p : Pos) : Env.shape stCJ2.env p = none := by
  unfold Env.shape
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rcases i with _ | i <;> rfl
    · rcases i with _ | _ | i <;> rfl
    · rfl
  · rcases f with _ | _ | f <;> rfl

theorem liveLoan_stCJ2 (l : Nat) : liveLoan stCJ2.env l = false := by
  rw [liveLoan, findBorrow]
  have : allPos stCJ2.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
    rw [allPos_eq]; simp [stCJ2, frameAllPos, List.range_succ]
  rw [this]; rfl

theorem sitesOf_stCJ2 (l : Nat) : Env.sitesOf stCJ2.env l = [] := by
  have : allPos stCJ2.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
    rw [allPos_eq]; simp [stCJ2, frameAllPos, List.range_succ]
  unfold Env.sitesOf; rw [this]
  simp [valAt, stCJ2, xB, selfU, nLazy, Value.sitesOf]

theorem occurs_stCJ2 (l : Nat) : ¬ stCJ2.Occurs l := by
  have : allPos stCJ2.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
    rw [allPos_eq]; simp [stCJ2, frameAllPos, List.range_succ]
  rintro ⟨v, hv, h⟩
  rw [Env.values, this] at hv
  simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> exact Bool.false_ne_true h

/-- **The relation at `J2`'s callee state.** From every reference state `s₂` related to the caller after the
argument's read (`x` moved), the checker's callee state is related to `s₂` with the callee's frame pushed
(`inPlaceJ2`, as `CallRef.callFrame` makes it), at the same renaming, at every context whose global `I` means `f` at
`Π(n : Nat). Nat` (`hgl`), which reads `I`'s declared type as that type (`hpi`: `GlobalsOk.ty`'s content) and the
deferred parameter type as `Nat` (`hn`: `codeMeaning.paramTy` at `I`'s Π-type, `bindsOf_nat`). -/
theorem rel_calleeJ2 {π : Nat → Nat} {s₂ : SState} {f : Sem} (hr : Rel K ρ φ π stX s₂)
    (hgl : K.C.global "I" = (f, .plain (piTyAt K.dm.read 1 psI outI)))
    (hpi : (Value.tyS K.dm K.M K.Γ ρ piNat).m = piTyAt K.dm.read 1 psI outI)
    (hn : (Env.hintAt K.dm K.M K.Γ ρ stCJ2.env (.bind 1 1)).m = TyM.nat) :
    Rel K ρ φ π stCJ2 (inPlaceJ2 K.dm.read s₂ f 1) := by
  have hlive₂ : s₂.liveLabels = [] := liveLabels_of_rel hr shape_stX
  have hsh₂ : ∀ p, s₂.shape p = none := by
    intro p
    rcases e : s₂.shape p with _ | l
    · rfl
    · have : l ∈ s₂.liveLabels := by
        unfold SState.liveLabels; rw [List.mem_mergeSort]
        exact List.mem_filterMap.mpr ⟨p, hr.holders p l e, e⟩
      rw [hlive₂] at this; cases this
  have hshI : ∀ p, (inPlaceJ2 K.dm.read s₂ f 1).shape p = none := fun p => hsh₂ p
  have hliveI : (inPlaceJ2 K.dm.read s₂ f 1).liveLabels = [] := by
    unfold SState.liveLabels
    rw [List.filterMap_eq_nil_iff.mpr (fun p _ => hshI p), List.mergeSort_nil]
  -- the caller's reference frames: one frame of one binding
  have hsk := congrArg (fun L => L.map List.length) hr.skel
  have hlen : s₂.env.map (fun fr => fr.binds.length) = [1] := by
    have : (SM' K ρ stX).env.map (fun fr => (fr.binds.map bindSkel).length) = [1] := by
      simp [SM', MState.sstate, stX]
    simpa [List.map_map, Function.comp_def, ← this] using hsk.symm
  obtain ⟨fr0, hen⟩ : ∃ fr0, s₂.env = [fr0] := by
    rcases he : s₂.env with _ | ⟨fr0, _ | ⟨fr1, rest⟩⟩ <;> rw [he] at hlen <;> simp at hlen
    exact ⟨fr0, rfl⟩
  have henv : (inPlaceJ2 K.dm.read s₂ f 1).env =
      [fr0, { binds := [{ ty := .plain (piTyAt K.dm.read 1 psI outI), val := fun _ => f, decl := .pi .other }, nBind 1] }] := by
    rw [inPlaceJ2_env, hen]; rfl
  have hval0 : ∀ i, (inPlaceJ2 K.dm.read s₂ f 1).valAt (.bind 0 i) = s₂.valAt (.bind 0 i) := fun i => by
    unfold SState.valAt; rw [henv, hen]; rfl
  have hF : ∀ ψ, RelF φ (inPlaceJ2 K.dm.read s₂ f 1) ψ ∧ TypedLive K (inPlaceJ2 K.dm.read s₂ f 1) ψ →
      RelF φ s₂ ψ ∧ TypedLive K s₂ ψ := fun ψ ⟨h1, _⟩ =>
    ⟨fun l _ => h1 l (by show l ∉ _; rw [hliveI]; simp),
     fun l hl => absurd hl (by show l ∉ s₂.liveLabels; rw [hlive₂]; simp)⟩
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  -- the skeleton: the caller's frame, then `I` at its Π-type and `n` at `Nat`
  · have hlhs : (SM' K ρ stCJ2).env.map (fun fr => fr.binds.map bindSkel) =
        [[(TyM.nat, .other)], [(piTyAt K.dm.read 1 psI outI, .pi .other), (TyM.nat, .other)]] := by
      unfold SM' MState.sstate
      simp only [stCJ2, List.zipIdx, List.map, Nat.zero_add]
      simp only [bindSkel, List.cons.injEq, Prod.mk.injEq, and_true, List.map_nil]
      exact ⟨⟨rfl, rfl⟩, ⟨hpi, rfl⟩, ⟨hn, rfl⟩⟩
    have hcaller : s₂.env.map (fun fr => fr.binds.map bindSkel) = [[(TyM.nat, .other)]] := by
      rw [← hr.skel]
      unfold SM' MState.sstate
      simp only [stX, List.zipIdx, List.map, Nat.zero_add]
      simp only [bindSkel, List.cons.injEq, Prod.mk.injEq, and_true]
      exact ⟨rfl, rfl⟩
    rw [hlhs, henv]
    rw [hen] at hcaller
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcaller ⊢
    exact ⟨hcaller.symm, rfl, rfl⟩
  -- no label occurs in the callee's state
  · intro l _ ho; exact absurd ho (occurs_stCJ2 l)
  -- the meanings
  · intro ψ hψ p hp
    rcases p with ⟨fi, i⟩ | ⟨fi, i⟩
    · rcases fi with _ | _ | fi
      · rw [hval0, ← hr.sim.1 ψ (hF ψ hψ) (.bind 0 i) (by simp [IsTemp])]
        rcases i with _ | i <;> rfl
      · rcases i with _ | _ | i
        · show (K.C.global "I").1 = (inPlaceJ2 K.dm.read s₂ f 1).valAt (.bind 1 0) ψ
          rw [hgl]; unfold SState.valAt; rw [henv]; rfl
        · show (Value.mean K.dm K.M K.Γ ρ _ (.plain TyM.nat) Value.zero).succ =
            (inPlaceJ2 K.dm.read s₂ f 1).valAt (.bind 1 1) ψ
          unfold SState.valAt; rw [henv]
          show (Sem.el0 Nat 0).succ = Sem.el0 Nat 1
          rw [Sem.succ_el0]
        · unfold SState.valAt; rw [henv]; rfl
      · unfold SState.valAt; rw [henv]; rfl
    · exact absurd trivial hp
  · intro p l _ h
    have h' : Env.shape stCJ2.env p = some l := h
    rw [shape_stCJ2] at h'; cases h'
  · intro p l _ h; rw [hshI] at h; cases h
  · intro f' i l h
    have h' : Env.shape stCJ2.env (.temp f' i) = some l := h
    rw [shape_stCJ2] at h'; cases h'
  · intro f' j l h; rw [hshI] at h; cases h
  · intro l l' h; rw [liveLoan_stCJ2] at h; cases h
  · intro l h; rw [liveLoan_stCJ2] at h; cases h
  · intro p l h; rw [hshI] at h; cases h
  · intro l hl; exact absurd hl (by show l ∉ _; rw [hliveI]; simp)

end

/-! ## The context's two readings `rel_calleeJ2` asks for, discharged -/

section
variable {K : RunCtx} {ρ : Assignment}

/-- **The deferred parameter type reads `Nat`** (`codeMeaning.paramTy` at `I`'s Π-type: the binder the `.fix`
clause reads at `.nat`, `ColumnI.bindsOf_nat`), at every table reading `Nat` as a parameter `.other` at the empty
scope (`fixDecJ`/`fixDecI` give it). -/
theorem hint_nLazy (hpd : K.D.paramDecls [] [.nat] = [.other]) :
    (Env.hintAt K.dm K.M K.Γ ρ stCJ2.env (.bind 1 1)).m = TyM.nat := by
  show (K.M.paramTy ρ piNat [.succ .zero] 0).m = TyM.nat
  show ((match (bindsOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture [])))
    [.nat])[0]? with
    | some b => b.1 ([Value.succ .zero].map (meanV K ρ noFuture (.plain TyM.err)) |>.take 0)
    | none => fixCod K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture [])))
        (bindsOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture []))) [.nat]) .nat
        ([Value.succ .zero].map (meanV K ρ noFuture (.plain TyM.err)))) : TyS).m = TyM.nat
  rw [ColumnI.bindsOf_nat K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture [])))
    (by rw [show scopeOf (stateOf 0 (capsState (capsVals K ρ noFuture []) (capsTys K ρ noFuture []))) = [] by
          simp [scopeOf, stateOf, capsState, capsVals, capsTys]]; exact hpd)]
  rfl

/-- **`I`'s declared type reads as its global's type** (`GlobalsOk.ty`'s content: the stored type `Π(n : Nat). Nat`
read under the constant future), at every context whose `GlobalsOk` holds at a state with `I`'s global, `I` not being
checked. -/
theorem hpi_of_globals {st : MState} (hg : GlobalsOk K st) (hst : st.globals = [gI]) (hcur : K.cur.map (·.1) ≠ some "I") :
    (Value.tyS K.dm K.M K.Γ ρ piNat).m = (K.C.global "I").2.m := by
  rw [hg.ty "I" gI (by rw [hst]; rfl) hcur ρ]
  rfl

end

/-! ## Steps (3) and (4) of `J2`'s plan, with only what they use -/

open CallBody FrameFrag FrameJ2 in
/-- **The closure's run of `I`'s body is what the checker's untyped run in place computed** (`FrameFrag`'s
`closureRun_of_checker_free` without `FundCtx`, the in-place state's `SGood` and `FrameStart`, which the frame
property's proof on the label-free fragment does not use, docs/31 D129): from the checker's callee state related to
the in-place reference state, the closure's run of `I`'s body from `closureJ2 a` succeeds with the meaning of the
checker's untyped value. Assumes 2 facts about the checker, `BodyLazyInv`, `InvNumA`; no model fact. -/
theorem closureRun_J2 (hB : BodyLazyInv) (hN : InvNumA)
    {K : RunCtx} {ρ : Assignment} {φ : Future} {R : List DeclInfo} (hd : ParDecI K.D R)
    {s₂ : SState} {f : Sem} {a : Nat} {st st' : MState} {n : Nat} {hint : Option Value} {bh : Nat} {v : Value}
    {T? : Option Value} {π : Nat → Nat}
    (hP : LazyNum K ρ R st) (hm : Mode st) (hp : Pre K ρ st) (hr : Rel K ρ φ π st (inPlaceJ2 K.dm.read s₂ f a))
    (hrel : FrameRelS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (inPlaceJ2 K.dm.read s₂ f a) (closureJ2 K.dm.read φ a))
    (hfl : K.D.flags (scopeOf (inPlaceJ2 K.dm.read s₂ f a)) bodyI = (false, false)) (hD : DecTab K.D st')
    (h : Runs (Ochr.eval n false bodyI hint) st bh (v, T?) st') (tl : Bool) (h' : TyS) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a) = some (r, s') ∧
      ∃ T : TyS, meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) T v = r.1 := by
  obtain ⟨ρ', Δ', π', r, s₁, -, hx, hmean, -, -, -, -⟩ :=
    bodyLazy_out (K := K) (ρ := ρ) (φ := φ) hB hN hd n st st' hint v T? _ π hP hm hp hr hfl hD bh h
  have hag : FrameAgreeS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (runT K ρ φ st.tailNext (hintM K ρ hint) bodyI (inPlaceJ2 K.dm.read s₂ f a))
      (runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a)) := by
    refine run_frameS_lf K ρ φ (a := false) (fun e => absurd e (by decide)) hrel (closureJ2_env K.dm.read φ a)
      (closureJ2_shape K.dm.read φ a) (closureJ2_lent K.dm.read φ a) (fun j b hj hb => ?_) (fun v hv => by simp at hv)
      (n := 1) rfl lfree_bodyI _ _ _ _
    rcases j with _ | _ | j
    · exact absurd rfl hj
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb; exact ⟨rfl, fun _ _ => rfl⟩
    · simp at hb
  rw [hx] at hag
  cases hcl : runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a) with
  | none => rw [hcl] at hag; exact hag.elim
  | some rs =>
    rw [hcl] at hag
    exact ⟨ρ', Δ', π', rs.1, rs.2, rfl, _, hmean.trans hag.1⟩

/-! ## `Pre` and `LazyNum` at the callee state -/

theorem allPos_stCJ2 : allPos stCJ2.env = [.bind 0 0, .bind 1 0, .bind 1 1] := by
  rw [allPos_eq]; simp [stCJ2, frameAllPos, List.range_succ]

theorem values_stCJ2 : Env.values stCJ2.env = [.bot, .gfn "I", .succ .zero] := by
  rw [Env.values, allPos_stCJ2]; rfl

theorem bind_stCJ2 {f i : Nat} {b : Binding} (h : stCJ2.env[f]?.bind (fun fr => fr.binds[i]?) = some b) :
    (f = 0 ∧ i = 0 ∧ b = xB .bot) ∨ (f = 1 ∧ i = 0 ∧ b = selfU) ∨ (f = 1 ∧ i = 1 ∧ b = nLazy (.succ .zero)) := by
  rcases f with _ | _ | f
  · rcases i with _ | i
    · simp [stCJ2] at h; exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [stCJ2] at h
  · rcases i with _ | _ | i
    · simp [stCJ2] at h; exact .inr (.inl ⟨rfl, rfl, h.symm⟩)
    · simp [stCJ2] at h; exact .inr (.inr ⟨rfl, rfl, h.symm⟩)
    · simp [stCJ2] at h
  · simp [stCJ2] at h

theorem ckContent_stCJ2 {p : Place} {v : Value} (h : ckContent stCJ2.env p = some v) :
    v = .gfn "I" ∨ v = .succ .zero ∨ v = .zero := by
  rcases hp : p.steps with ⟨i, path⟩
  simp only [ckContent, hp] at h
  unfold ckVarPos at h
  by_cases hi : i < 2
  · have hi' : i < stCJ2.env[stCJ2.env.size - 1]!.binds.size := hi
    rw [if_pos hi'] at h
    simp only [Option.bind_some] at h
    have hv : ∀ w : Value, (w = .gfn "I" ∨ w = .succ .zero) → w.follow path = some v →
        v = .gfn "I" ∨ v = .succ .zero ∨ v = .zero := by
      rintro w hw hf
      rcases path with _ | ⟨s, _ | ⟨s', ss⟩⟩
      · simp [Value.follow] at hf; rcases hw with rfl | rfl
        · exact .inl hf.symm
        · exact .inr (.inl hf.symm)
      · rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
        rename_i k
        rcases k with _ | k <;> simp [stepV] at hf
        exact .inr (.inr hf.symm)
      · rcases hw with rfl | rfl <;> cases s <;> simp [Value.follow, stepV] at hf
        rename_i k
        rcases k with _ | k <;> simp [stepV] at hf
    rcases i with _ | _ | i
    · exact hv _ (.inr rfl) h
    · exact hv _ (.inl rfl) h
    · omega
  · have hi' : ¬ i < stCJ2.env[stCJ2.env.size - 1]!.binds.size := hi
    rw [if_neg hi'] at h; cases h

theorem not_refd_stCJ2 (σ : Nat) : ¬ stCJ2.Refd σ := fun h => by
  have := MState.refd_lt stCJ2 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ h
  · omega
  · intro v hv σ hσ; rw [values_stCJ2] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> exact (Bool.false_ne_true hσ).elim
  · intro f i b T hb hT σ hσ
    rcases bind_stCJ2 hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [xB, selfU, nLazy] at hT <;> subst hT <;>
      exact (Bool.false_ne_true hσ).elim
  · intro f i b P ws j hb hT σ hσ
    rcases bind_stCJ2 hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [xB, selfU, nLazy] at hT
    obtain ⟨rfl, rfl, rfl⟩ := hT
    rcases hσ with h | ⟨w, hw, h⟩
    · exact (Bool.false_ne_true h).elim
    · simp at hw; subst hw; exact (Bool.false_ne_true h).elim
  · intro G hG; simp [stCJ2] at hG
  · intro m σ' h; simp [stCJ2] at h
  · intro σ' v h; simp [stCJ2] at h
  · intro σ' T h; simp [stCJ2] at h

theorem norm_stCJ2 : stCJ2.norm = stCJ2 := by simp [stCJ2, MState.norm, Env.erase, Frame.erase]

/-- **`Inv` at the callee state.** -/
theorem inv_stCJ2 (D : Decisions) : Inv D [] stCJ2 := by
  have hvals : ∀ v ∈ Env.values stCJ2.env, v = .bot ∨ v = .gfn "I" ∨ v = .succ .zero := fun v hv => by
    rw [values_stCJ2] at hv; simpa using hv
  have hpos : ∀ p ∈ allPos stCJ2.env, p = .bind 0 0 ∨ p = .bind 1 0 ∨ p = .bind 1 1 := fun p hp => by
    rw [allPos_stCJ2] at hp; simpa using hp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp; rcases hpos p hp with rfl | rfl | rfl <;> exact Bool.false_ne_true
  · intro p _ q _ l h; rw [shape_stCJ2] at h; cases h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl <;> cases hl
  · intro l; rw [values_stCJ2]; exact Nat.zero_le _
  · exact ⟨fun a => ⟨a, fun b ⟨p, hp, w, hw, _⟩ => by rcases hpos p hp with rfl | rfl | rfl <;> cases hw⟩⟩
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl <;> exact Bool.false_ne_true
  · intro σ h; exact absurd h (not_refd_stCJ2 σ)
  · intro T hT; simp [stCJ2] at hT
  · intro σ r h; simp [stCJ2] at h
  · rfl
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl <;> rfl
  · intro f i b hb T hT
    rcases bind_stCJ2 hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [xB, selfU, nLazy] at hT <;> subst hT <;> rfl
  · intro T hT; simp [stCJ2] at hT
  · intro G hG; simp [stCJ2] at hG
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl <;> rfl
  · intro f i b hb; rcases bind_stCJ2 hb with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨fun T hT l => by simp [xB] at hT; subst hT; rfl, fun P ws j h => by simp [xB] at h⟩
    · exact ⟨fun T hT l => by simp [selfU] at hT; subst hT; rfl, fun P ws j h => by simp [selfU] at h⟩
    · refine ⟨fun T hT l => by simp [nLazy] at hT, fun P ws j h l => ?_⟩
      simp [nLazy] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun w hw => by simp at hw; subst hw; rfl⟩
  · intro T hT; simp [stCJ2] at hT
  · intro G hG; simp [stCJ2] at hG
  · intro n σ h; simp [stCJ2] at h
  · intro σ v h; simp [stCJ2] at h
  · intro k l hk; rw [liveLoan_stCJ2] at hk; cases hk
  · intro pos path _ l hl; rw [liveLoan_stCJ2] at hl; cases hl
  · intro v hv l; rcases hvals v hv with rfl | rfl | rfl <;> rfl
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl <;> rfl
  · intro p v n args _ _ h; simp at h
  · intro v hv l hl; rcases hvals v hv with rfl | rfl | rfl <;> cases hl
  · intro v hv; rcases hvals v hv with rfl | rfl | rfl <;> rfl
  · intro p _ h; rcases ckContent_stCJ2 h with h | h | h <;> cases h
  · intro σ r h; simp [stCJ2] at h
  · intro σ r h; simp [stCJ2] at h
  · intro σ l h; simp [stCJ2] at h
  · intro l h; exact absurd h (occurs_stCJ2 l)

section
variable {K : RunCtx} {ρ : Assignment}

/-- **`Pre` at the callee state**, at every context whose part a check does not change holds of the caller
(`CtxS` reads only the globals and the declarations) and which has no declarations. -/
theorem pre_stCJ2 (hc : CtxS K stX.norm) (hΓ : K.Γ = []) : Pre K ρ stCJ2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [norm_stCJ2]
  · exact hc.of_eq rfl rfl
  · rw [hΓ]; exact inv_stCJ2 K.D
  · refine ⟨⟨fun σ h => absurd h (not_refd_stCJ2 σ), ?_, ?_, ?_⟩, fun σ h => absurd h (not_refd_stCJ2 σ), ?_,
      fun σ h => absurd h (not_refd_stCJ2 σ)⟩
    · intro n σ h; simp [stCJ2] at h
    · intro σ v h; simp [stCJ2] at h
    · intro σ r h; simp [stCJ2] at h
    · intro G h; simp [MState.goalM, stCJ2] at h

/-- **`LazyNum` at the callee state** (what the untyped body step asks), at every table reading `Nat` as a
parameter `.other` at the empty scope. -/
theorem lazyNum_stCJ2 (hpd : K.D.paramDecls [] [.nat] = [.other]) {st : MState} (hk : Kern stCJ2 st)
    (htd : st.tailDecl = none) : CallBody.LazyNum K ρ [.other, .pi .other] st := by
  have hck : ckVarPos st.env 0 = some (.bind 1 1) := by rw [← ckVarPos_erase, ← hk.env, ckVarPos_erase]; rfl
  have hb : st.env[1]?.bind (fun fr : Frame => fr.binds[1]?) = some (nLazy (.succ .zero)) := by
    rw [← lookup_erase, ← hk.env, lookup_erase]; rfl
  have hh : Env.hintAt K.dm K.M K.Γ ρ st.env (.bind 1 1) = Env.hintAt K.dm K.M K.Γ ρ stCJ2.env (.bind 1 1) := by
    simp only [Env.hintAt, hb]; rfl
  refine ⟨⟨1, 1, _, hck, hb, .succ .zero, rfl, by rw [hh]; exact hint_nLazy hpd⟩, ?_, htd⟩
  rw [← ColumnC.topReadings_kern hk]; rfl

end

end Ochr.Meaning.Steps.Form.CallJ2
