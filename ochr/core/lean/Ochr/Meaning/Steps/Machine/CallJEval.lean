import Ochr.Meaning.Steps.Machine.CallJLeaves
import Ochr.Meaning.Steps.Machine.EvalInv
import Ochr.Meaning.Steps.Machine.HintKeep

/-!
# `eval` around `evalCore` at a call whose pre-pass reads data (machine8; for `CallJInv`)

`EvalInvR` excludes calls: a call's after-the-fact classification is the flags `callFn` sets. Where
the call's reading is `.other` the pre-pass says "neither erased nor a proof", so `evalCore` runs on
the state itself, and the run succeeds only if the flags it leaves agree (else `[pre-pass]`'s
INTERNAL error); nothing is restored.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

set_option maxHeartbeats 4000000 in
theorem evalAt_inv_call {n : Nat} {typed : Bool} {f : Term} {as : List Term} {hd : Bool} {hint : Option Value}
    {st st' : MState} {bh : Nat} {r : Value × Option Value}
    (hh : st.headEval = false) (htd : st.tailDecl = none)
    (hdd : ∀ s b d s', Kern st s → Runs (withLive true (Ochr.declOf n false [] [] (.call f as hd))) s b d s' → d = .other)
    (h : Runs (Ochr.evalAt (n + 1) typed (.call f as hd) hint) st bh r st') :
    ∃ st₀ st₁ bh', Kern st st₀ ∧ ModeEq st₀ { st with headEval := false } ∧ st₀.curTail = st.tailNext ∧
      st₀.tailNext = false ∧ st₀.tailDecl = none ∧ st₀.wantHere = (typed || st.wantTy) ∧ st₀.wantTy = false ∧
      Runs (Ochr.evalCore n typed (.call f as hd) hint) st₀ bh' r st₁ ∧ Kern st₁ st' ∧ ModeEq st₁ st' := by
  unfold Ochr.evalAt at h
  peel h
  rw [if_pos (by rw [hh]; rfl)] at h
  rw [htd] at h
  obtain ⟨d?, s₁, b₁, hd', h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨d, hd'', rfl⟩ := Runs.map_inv hd'
  clear hd'
  have hs := runs_keep (keep_withLive _ ((decideKeep n).2.2.2.2.2.2.2.2.1 _ _ _ _)) hd''
  subst hs
  obtain rfl := hdd _ _ _ _ (by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hd''
  clear hd''
  peel h₁
  obtain ⟨pre, s₂, b₂, hp, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  have hs := runs_keep (keep_preFlags _ _) hp
  subst hs
  have hpre : pre = some (false, false) := by
    unfold preFlags at hp; peel hp; have := (runs_pure_inv hp).1; simpa [DeclInfo.isProof] using this
  subst hpre
  peel h₂
  obtain ⟨r', s₃, b₃, hcore, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  replace hcore := Runs.onFail_inv hcore
  rw [if_neg (by decide)] at hcore
  peel h₃
  obtain ⟨fl, s₄, b₄, hfl, h₄⟩ := Runs.bind_inv h₃
  have hs := runs_keep keep_getFlags hfl
  subst hs
  clear h₃
  peel h₄
  split at h₄
  · simp only [runs_err_bind] at h₄
  · rename_i hne
    obtain ⟨e, p⟩ := fl
    have hep : e = false := by
      cases e <;> cases p <;> simp_all
    subst hep
    simp only [Bool.false_eq_true, if_false, setFlags] at h₄
    peel h₄
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₄
    refine ⟨_, _, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcore, ?_, ?_⟩
    all_goals first | rfl | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | exact ⟨rfl, rfl, rfl, rfl⟩


theorem evalCore_call_inv {n : Nat} {typed : Bool} {f : Term} {as : List Term} {hd : Bool} {hint : Option Value}
    {st st' : MState} {bh : Nat} {r : Value × Option Value}
    (h : Runs (Ochr.evalCore (n + 1) typed (.call f as hd) hint) st bh r st') :
    ∃ b', Runs (Ochr.evalCall n typed f as hd) st b' r st' := by
  unfold Ochr.evalCore at h
  obtain ⟨b₁, h⟩ := Runs.tick_bind h
  obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
  obtain ⟨rfl, rfl⟩ := runs_wanted_inv hw
  simp only [Term.placeOperand?] at h
  exact ⟨_, h⟩

theorem Runs.withLive_inv {α : Type} {lv : Bool} {x : M α} {st st' : MState} {b : Nat} {a : α}
    (h : Runs (withLive lv x) st b a st') : ∃ b₁ s₁, Runs x { st with liveScope := lv } b₁ a s₁ := by
  unfold withLive at h
  peel h
  obtain ⟨r, s₁, b₁, hx, h2⟩ := Runs.bind_inv h
  replace hx := Runs.onFail_inv hx
  peel h2
  obtain ⟨rfl, -⟩ := runs_pure_inv h2
  exact ⟨_, _, hx⟩

theorem runs_declOf_zero {k : Nat} {chk : Bool} {sc : List DeclInfo} {ns : List String} {st st' : MState} {b : Nat}
    {d : DeclInfo} (h : Runs (Ochr.declOf k chk sc ns .zero) st b d st') : d = .other ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.declOf at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.declOf at h; exact runs_pure_inv h

theorem runs_needsCtx_zero {k : Nat} {st st' : MState} {b : Nat} {c : Bool}
    (h : Runs (Ochr.needsCtx k .zero) st b c st') : c = false ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.needsCtx at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.needsCtx at h; exact runs_pure_inv h

theorem runs_needsCtx_bodyI {k : Nat} {st st' : MState} {b : Nat} {c : Bool}
    (h : Runs (Ochr.needsCtx k Form.bodyI) st b c st') : c = false ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.needsCtx at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.needsCtx Form.bodyI at h; exact runs_pure_inv h

theorem evalCore_zero_eq {n : Nat} {typed : Bool} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} (h : Runs (Ochr.evalCore n typed .zero hint) st bh r st') :
    r = (.zero, some .tNat) ∧ st' = st := by
  cases n with
  | zero => unfold Ochr.evalCore at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.evalCore at h
    obtain ⟨b₁, h⟩ := Runs.tick_bind h
    obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
    obtain ⟨rfl, rfl⟩ := runs_wanted_inv hw
    simp only [Term.placeOperand?] at h
    exact runs_pure_inv h

/-- **A typed `Z`, through `eval`**: `Z` at `Nat`, the kernel kept, the mode kept. -/
theorem eval_zero_inv {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {r : Value × Option Value}
    (h : Runs (Ochr.eval n true .zero hint) st bh r st') (hm : Mode st) (htd : st.tailDecl = none) :
    r = (.zero, some .tNat) ∧ Kern st st' ∧ Mode st' ∧ st'.tailDecl = none := by
  match n, h with
  | 0, h => exact absurd h (noRun_eval_low 0 (by omega) _ _ _ _ _ _ _)
  | 1, h => exact absurd h (noRun_eval_low 1 (by omega) _ _ _ _ _ _ _)
  | n + 2, h =>
    rw [Ochr.eval.eq_1] at h
    obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
    obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
    obtain ⟨hhe, htde, -⟩ := hla.tail
    obtain ⟨st₀, st₁, bh', hk₀, hme₀, -, -, htd₀, -, hcore, hk₁, hme₁, htd₁⟩ :=
      evalAt_inv' (dd := .other) (hhe ▸ hm.headEval) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
        (.inl (htde ▸ htd)) (fun _ _ _ _ _ hr => by
          obtain ⟨_, _, hr'⟩ := Runs.withLive_inv hr; exact (runs_declOf_zero hr').1)
        (fun e => by cases e) rfl hat
    obtain ⟨rfl, rfl⟩ := evalCore_zero_eq hcore
    have hm₀ : Mode st₁ := Mode.of_modeEq ⟨rfl, hla.modeEq.copying ▸ hm.copying, hla.modeEq.inPlace ▸ hm.inPlace,
      hla.modeEq.erased ▸ hm.erased⟩ hme₀.symm
    exact ⟨rfl, hla.kern.trans (hk₀.trans (hk₁.trans hlb.kern)), Mode.of_modeEq (Mode.of_modeEq hm₀ hme₁) hlb.modeEq,
      by rw [← hlb.tail.2.1, htd₁]; exact htd₀⟩

theorem evalCore_const_I_inv {n : Nat} {typed : Bool} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} (hg : st.globals = [ColumnI.gI])
    (h : Runs (Ochr.evalCore n typed (.const "I") hint) st bh r st') :
    r = (.gfn "I", some ColumnI.piNat) ∧ st' = st := by
  cases n with
  | zero => unfold Ochr.evalCore at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.evalCore at h
    obtain ⟨b₁, h⟩ := Runs.tick_bind h
    obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
    obtain ⟨rfl, rfl⟩ := runs_wanted_inv hw
    simp only [Term.placeOperand?] at h
    obtain ⟨g, s₂, b₃, hgl, h₁⟩ := Runs.bind_inv h
    have hs := runs_keep (keep_lookupGlobal _) hgl; subst hs
    have hgI : g = ColumnI.gI := by
      unfold lookupGlobal at hgl; peel hgl; rw [hg] at hgl
      have e : ColumnI.gI.name = "I" := rfl
      simp only [List.find?, e, beq_self_eq_true] at hgl
      exact (runs_pure_inv hgl).1
    subst hgI
    obtain ⟨p, s₃, b₄, hp, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨rfl, rfl⟩ := runs_isPropV_piNat hp
    simp only [Bool.false_eq_true, if_false, pure_bind] at h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
    exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **A call's head `I`, through `eval`** (`headEval` set, so no pre-pass): `I`'s global at its type; the
kernel kept, the head flag cleared, the rest of the mode kept, no reading handed on. -/
theorem eval_const_I_inv {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {r : Value × Option Value}
    (hh : st.headEval = true) (hg : st.globals = [ColumnI.gI]) (h : Runs (Ochr.eval n true (.const "I") hint) st bh r st') :
    r = (.gfn "I", some ColumnI.piNat) ∧ Kern st st' ∧ st'.headEval = false ∧ st'.copying = st.copying ∧
      st'.inPlace = st.inPlace ∧ st'.erasedDepth = st.erasedDepth ∧ st'.tailDecl = none := by
  cases n with
  | zero => unfold Ochr.eval at h; simp only [runs_exhausted_iff] at h
  | succ n =>
  rw [Ochr.eval.eq_1] at h
  obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
  obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
  obtain ⟨hhe, -, -⟩ := hla.tail
  have hka := hla.kern
  cases n with
  | zero => unfold Ochr.evalAt at hat; simp only [runs_exhausted_iff] at hat
  | succ n =>
  unfold Ochr.evalAt at hat
  peel hat
  rw [← hhe, hh] at hat
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false] at hat
  peel hat
  obtain ⟨r', s₃, b₃, hcore, h₂⟩ := Runs.bind_inv hat
  clear hat
  replace hcore := Runs.onFail_inv hcore
  obtain ⟨rfl, rfl⟩ := evalCore_const_I_inv (by rw [← hka.globals, hg]) hcore
  peel h₂
  obtain ⟨x, s₄, b₄, hcl, h₃⟩ := Runs.bind_inv h₂
  have hs := runs_keep (keep_leafProof _ _ _) hcl; subst hs
  clear h₂
  peel h₃
  have hl : LocsEq sb st' := hlb
  split at h₃ <;> (simp only [setFlags] at h₃; peel h₃; obtain ⟨rfl, rfl⟩ := runs_pure_inv h₃) <;>
    (refine ⟨rfl, ?_, ?_⟩
     · refine hka.trans (Kern.trans ?_ hl.kern); exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
     · unfold LocsEq at hl hla; rw [← hl, ← hla]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem runs_argDecls_zero {k : Nat} {st st' : MState} {b : Nat} {ads : Array DeclInfo}
    (h : Runs (Array.mapM (fun a => withLive true (Ochr.declOf k false [] [] a)) #[Term.zero]) st b ads st') :
    ads = #[.other] ∧ st' = st := by
  have hs := runs_keep (by
    rw [Array.mapM_eq_mapM_toList]
    exact keep_map _ (keep_mapM _ fun _ => keep_withLive _ ((decideKeep k).2.2.2.2.2.2.2.2.1 _ _ _ _))) h
  subst hs
  refine ⟨?_, rfl⟩
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨l, hl, rfl⟩ := Runs.map_inv h
  simp only [List.mapM_cons, List.mapM_nil, Array.toList] at hl
  obtain ⟨d, s₁, b₁, hd, h₁⟩ := Runs.bind_inv hl
  have hs := runs_keep (keep_withLive _ ((decideKeep k).2.2.2.2.2.2.2.2.1 _ _ _ _)) hd; subst hs
  obtain ⟨_, _, hd'⟩ := Runs.withLive_inv hd
  obtain ⟨rfl, -⟩ := runs_declOf_zero hd'
  simp only [pure_bind, bind_pure_comp, map_pure] at h₁
  obtain ⟨rfl, -⟩ := runs_pure_inv h₁
  rfl

theorem keep_noteEnders (e : Array (Option Nat)) (ws : Array Value) : Keep (noteEnders e ws) := by
  unfold noteEnders; keep_go
  all_goals (rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact keep_forIn _ _ fun _ _ => by keep_go)

theorem keep_enderLoc (e : Array (Option Nat)) (ws : Array Value) : Keep (enderLoc e ws) := by
  unfold enderLoc; keep_go

theorem runs_stmtCallee_I {k : Nat} {st st' : MState} {b : Nat} {c : Bool}
    (h : Runs (Ochr.stmtCallee k (.gfn "I") (some ColumnI.piNat) none) st b c st') : c = false ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.stmtCallee at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.stmtCallee at h
    simp only at h
    obtain ⟨T, s₁, b₁, hT, h₁⟩ := Runs.bind_inv h
    have hT' : T = some ColumnI.piNat ∧ s₁ = st := by
      cases k with
      | zero => unfold Ochr.funType? at hT; simp only [runs_exhausted_iff] at hT
      | succ k => unfold Ochr.funType? at hT; exact runs_pure_inv hT
    obtain ⟨rfl, rfl⟩ := hT'
    simp only at h₁
    obtain ⟨c', s₂, b₂, hc, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨rfl, rfl⟩ := runs_fnClass_piNat hc
    exact runs_pure_inv h₂

theorem runs_callTemps_inv {f n : Nat} {st st' : MState} {b : Nat} {r : Value × Array Value}
    (h : Runs (callTemps f n) st b r st') :
    st' = st ∧ n + 1 ≤ (st.env[f]!).temps.size ∧
      r = ((st.env[f]!).temps[(st.env[f]!).temps.size - (n + 1)]!,
        (st.env[f]!).temps.extract ((st.env[f]!).temps.size - (n + 1) + 1) (st.env[f]!).temps.size) := by
  unfold callTemps at h
  peel h
  split at h
  · simp only [runs_err_bind] at h
  · rename_i hlt
    peel h
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h
    exact ⟨rfl, by omega, rfl⟩

theorem _root_.Ochr.Meaning.Steps.Form.Kern.size {a b : MState} (h : Kern a b) : a.env.size = b.env.size := by
  have := congrArg Array.size h.env; simpa [Env.erase] using this

theorem _root_.Ochr.Meaning.Steps.Form.Kern.temps {a b : MState} (h : Kern a b) (f : Nat) : (a.env[f]!).temps = (b.env[f]!).temps := by
  have := congrArg (fun e : Env => (e[f]!).temps) h.env; simpa only [temps_erase] using this

theorem _root_.Ochr.Meaning.Steps.Form.Kern.binds {a b : MState} (h : Kern a b) (f : Nat) : (a.env[f]!).binds = (b.env[f]!).binds := by
  have := congrArg (fun e : Env => (e[f]!).binds) h.env; simpa only [binds_erase] using this

/-- Two states with one kernel, each with the same value pushed: one kernel, whatever the stored types. -/
theorem _root_.Ochr.Meaning.Steps.Form.Kern.withTempT' {a b : MState} (h : Kern a b) {v : Value} {T T' : Option Value} :
    Kern (a.withTempT v T) (b.withTempT v T') :=
  ⟨by rw [erase_withTempT, erase_withTempT, h.env], h.globals, h.inds, h.nextLoan, h.nextAbs, h.absTy, h.absDecl,
    h.refs, h.etaRefs, h.goal, h.neutrals, h.liveScope⟩

/-- `J`'s state with the call's head and argument held (main's D115). -/
def stJ2 : MState := (CallGuards.stJ.withTempT (.gfn "I") (some ColumnI.piNat)).withTempT .zero (some .tNat)

theorem callTemps_J {st st' : MState} {b : Nat} {r : Value × Array Value}
    (h : Runs (callTemps (st.env.size - 1) 1) st b r st') (hk : Kern stJ2 st) :
    r = (.gfn "I", #[.zero]) ∧ st' = st := by
  obtain ⟨rfl, -, rfl⟩ := runs_callTemps_inv h
  rw [← hk.size, ← hk.temps]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`J`'s call down to `callFn`**: the call's reading, the arguments' readings (`Z`: data), the head `I`
(its global at its type) and the argument `Z` (at `Nat`) evaluated typed and held as the frame's last two
temporaries; then `callFn` from a state with the kernel `stJ2`, in the plain mode, no reading handed down. -/
theorem evalCall_J_inv {k : Nat} {s s' : MState} {bh : Nat} {r : Value × Option Value}
    (hk : Kern CallGuards.stJ s) (hm : Mode s) (htd : s.tailDecl = none)
    (h : Runs (Ochr.evalCall (k + 1) true (.const "I") [.zero] false) s bh r s') :
    ∃ res sF bF, Kern stJ2 sF ∧ Mode sF ∧ sF.tailDecl = none ∧
      Runs (withLive true (Ochr.declOf k false [] [] CallGuards.bodyJ)) s bh res s ∧
      Runs (Ochr.callFn k true (some ColumnI.piNat) 1 #[some .tNat] false none none res #[false] s.wantHere
        s.deferCallTy none) sF bF r s' := by
  unfold Ochr.evalCall at h
  peel h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨res, s₁, b₁, hres, h1⟩ := Runs.bind_inv h
  clear h
  have := runs_keep (keep_withLive _ ((decideKeep k).2.2.2.2.2.2.2.2.1 _ _ _ _)) hres; subst this
  obtain ⟨ads, s₂, b₂, hads, h2⟩ := Runs.bind_inv h1
  clear h1
  obtain ⟨rfl, rfl⟩ := runs_argDecls_zero hads
  peel h2
  unfold callRecUid at h2
  peel h2
  unfold wanted at h2
  peel h2
  unfold demand at h2
  peel h2
  obtain ⟨hv, s₃, b₃, hev, h3⟩ := Runs.bind_inv h2
  clear h2
  obtain ⟨rfl, hk3, hh3, hc3, hi3, he3, htd3⟩ := eval_const_I_inv rfl (by rw [← hk.globals]; rfl) hev
  peel h3
  obtain ⟨_, s₄, b₄, hpt, h4⟩ := Runs.bind_inv h3
  clear h3
  have := runs_pushTemp_inv hpt; subst this
  obtain ⟨stmt, s₅, b₅, hst, h5⟩ := Runs.bind_inv h4
  clear h4
  obtain ⟨rfl, rfl⟩ := runs_stmtCallee_I hst
  simp only [List.zip, List.zipWith, List.zipIdx, List.forIn_cons, List.forIn_nil] at h5
  obtain ⟨acc, s₆, b₆, hloop, h6⟩ := Runs.bind_inv h5
  clear h5
  obtain ⟨step, s₇, b₇, hstep, hm7⟩ := Runs.bind_inv hloop
  clear hloop
  obtain ⟨nc, s₈, b₈, hnc, h8⟩ := Runs.bind_inv hstep
  clear hstep
  -- D124: the argument's hint is guarded by `readsHint`, computed first (it reads only); `Z` is no hinted form
  have := runs_keep (keep_readsHint _ _ _ _) hnc; subst s₈
  simp only [Bool.and_false, Bool.not_true, Bool.false_and, Bool.or_false, Bool.false_eq_true, if_false] at h8
  peel h8
  obtain ⟨wT, s₉, b₉, hw, h9⟩ := Runs.bind_inv h8
  clear h8
  unfold stmtArgIf at hw
  simp only [Bool.not_false, if_true] at hw
  obtain ⟨rfl, hk10, hm10, htd10⟩ := eval_zero_inv hw ⟨hh3, hc3.trans hm.copying, rfl, he3.trans hm.erased⟩ htd3
  peel h9
  obtain ⟨_, s₁₁, b₁₁, hpt2, h11⟩ := Runs.bind_inv h9
  clear h9
  have := runs_pushTemp_inv hpt2; subst this
  obtain ⟨en, s₁₂, b₁₂, hen, h12⟩ := Runs.bind_inv h11
  clear h11
  have := runs_keep (keep_noteEnders _ _) hen; subst this
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h12
  simp only at hm7
  obtain ⟨rfl, rfl⟩ := runs_pure_inv hm7
  obtain ⟨f0, s₁₃, b₁₃, htop, h13⟩ := Runs.bind_inv h6
  clear h6
  obtain ⟨rfl, rfl⟩ := runs_topIdx_inv htop
  obtain ⟨ct, s₁₄, b₁₄, hct, h14⟩ := Runs.bind_inv h13
  clear h13
  have hk3' : Kern CallGuards.stJ s₃ := by
    refine hk.trans (Kern.trans ?_ hk3); exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := callTemps_J hct (Kern.withTempT' (Kern.trans (Kern.trans (Kern.withTempT' hk3') (by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) hk10))
  obtain ⟨loc, s₁₅, b₁₅, hloc, h15⟩ := Runs.bind_inv h14
  clear h14
  have := runs_keep (keep_enderLoc _ _) hloc; subst this
  replace h15 := Runs.atLoc_inv h15
  have hfills : Array.map (fun x => x == DeclInfo.unit.ref) #[DeclInfo.other] = #[false] := by simp; rfl
  rw [hfills] at h15
  change Runs (Ochr.callFn k true (some ColumnI.piNat) 1 #[some .tNat] false none none res #[false] _ _ none) _ _ _ _ at h15
  refine ⟨res, _, _, Kern.withTempT' (Kern.trans (Kern.trans (Kern.withTempT' hk3') (by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)) hk10), ⟨hm10.headEval, hm10.copying,
    hm10.inPlace, hm10.erased⟩, htd10, hres, h15⟩

/-! ## Private runs that change nothing the kernel holds -/

theorem runs_restoreKeep_same {saved cur st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (restoreKeep saved) cur b u st') (ha : cur.nextAbs = saved.nextAbs) (hl : cur.nextLoan = saved.nextLoan)
    (hn : cur.neutrals = saved.neutrals) (he : cur.etaRefs = saved.etaRefs) (ht : cur.absTy = saved.absTy)
    (hd : cur.absDecl = saved.absDecl) : ∃ rs nr, st' = { saved with recStack := rs, nextRecUid := nr } := by
  refine ⟨st'.recStack, st'.nextRecUid, ?_⟩
  unfold restoreKeep at h
  have := runs_modify_inv h
  subst this
  simp only [ha, hl, hn, he, ht, hd, Array.extract_size, Array.extract_eq_empty_of_le (Nat.le_refl _),
    Array.append_empty]
  congr 1
  simp

theorem Runs.privately_inv {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α}
    (h : Runs (Ochr.privately x) st b a st') :
    ∃ b' cur b'', Runs x { st with privateDepth := st.privateDepth + 1 } b' a cur ∧ Runs (restoreKeep st) cur b'' () st' := by
  have e : Ochr.privately x = (do
      let saved ← get
      modify fun s => { s with privateDepth := s.privateDepth + 1 }
      let r ← Ochr.onFail x (restoreKeep saved)
      restoreKeep saved
      pure r) := rfl
  rw [e] at h
  peel h
  obtain ⟨r, s₁, b₁, hx, h₁⟩ := Runs.bind_inv h
  replace hx := Runs.onFail_inv hx
  obtain ⟨_, s₂, b₂, hr, h₂⟩ := Runs.bind_inv h₁
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
  exact ⟨_, _, _, hx, hr⟩

theorem inStatement_eq {α : Type} (x : M α) : Ochr.inStatement x = Ochr.privately (Ochr.withErased x) := rfl

theorem Runs.withErased_inv {α : Type} {x : M α} {st st' : MState} {b : Nat} {a : α}
    (h : Runs (Ochr.withErased x) st b a st') :
    ∃ b' cur, Runs x { st with erasedDepth := st.erasedDepth + 1 } b' a cur ∧
      st' = { cur with erasedDepth := cur.erasedDepth - 1 } := by
  unfold Ochr.withErased at h
  peel h
  obtain ⟨r, s₁, b₁, hx, h₁⟩ := Runs.bind_inv h
  replace hx := Runs.onFail_inv hx
  peel h₁
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
  exact ⟨_, _, hx, rfl⟩

theorem evalCore_nat_eq {n : Nat} {typed : Bool} {hint : Option Value} {st st' : MState} {bh : Nat}
    {r : Value × Option Value} (h : Runs (Ochr.evalCore n typed .nat hint) st bh r st') :
    r = (.tNat, some (.sort 1)) ∧ st' = st := by
  cases n with
  | zero => unfold Ochr.evalCore at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.evalCore at h
    obtain ⟨b₁, h⟩ := Runs.tick_bind h
    obtain ⟨want, s₁, b₂, hw, h⟩ := Runs.bind_inv (runs_get_bind.mp h)
    obtain ⟨rfl, rfl⟩ := runs_wanted_inv hw
    simp only [Term.placeOperand?] at h
    exact runs_pure_inv h

/-- **`Nat` evaluated as a term** (typed): the type `Nat` in `Type₀`; the kernel kept, the reading
handed down kept. -/
theorem eval_nat_inv {n : Nat} {hint : Option Value} {st st' : MState} {bh : Nat} {r : Value × Option Value}
    (h : Runs (Ochr.eval n true .nat hint) st bh r st') (hh : st.headEval = false) (htd : st.tailDecl = none) :
    r = (.tNat, some (.sort 1)) ∧ Kern st st' ∧ ModeEq st { st' with headEval := false } ∧ st'.tailDecl = none := by
  cases n with
  | zero => unfold Ochr.eval at h; simp only [runs_exhausted_iff] at h
  | succ n =>
  cases n with
  | zero => rw [Ochr.eval.eq_1] at h; obtain ⟨_, _, _, -, hna, -⟩ := Runs.located_inv h
            obtain ⟨_, hat⟩ := Runs.noteValue_inv hna; unfold Ochr.evalAt at hat; simp only [runs_exhausted_iff] at hat
  | succ n =>
  rw [Ochr.eval.eq_1] at h
  obtain ⟨sa, ba, sb, hla, hna, hlb⟩ := Runs.located_inv h
  obtain ⟨ba', hat⟩ := Runs.noteValue_inv hna
  obtain ⟨hhe, htde, -⟩ := hla.tail
  obtain ⟨st₀, st₁, bh', hk₀, hme₀, -, -, htd₀, -, hcore, hk₁, hme₁, htd₁⟩ :=
    evalAt_inv' (dd := .sort 1) (hhe ▸ hh) (fun _ e => by cases e) (fun _ _ _ e => by cases e)
      (.inl (htde ▸ htd)) (fun _ _ _ _ _ hr => by
        obtain ⟨_, _, hr'⟩ := Runs.withLive_inv hr; exact (runs_declOf_nat hr').1)
      (fun e => by cases e) rfl hat
  obtain ⟨rfl, rfl⟩ := evalCore_nat_eq hcore
  refine ⟨rfl, hla.kern.trans (hk₀.trans (hk₁.trans hlb.kern)), ?_, by rw [← hlb.tail.2.1, htd₁]; exact htd₀⟩
  have m1 := hla.modeEq
  have m2 := hme₀
  have m3 := hme₁
  have m4 := hlb.modeEq
  exact ⟨hh, m1.copying.trans (m2.copying.symm.trans (m3.copying.trans m4.copying)),
    m1.inPlace.trans (m2.inPlace.symm.trans (m3.inPlace.trans m4.inPlace)),
    m1.erased.trans (m2.erased.symm.trans (m3.erased.trans m4.erased))⟩

set_option maxHeartbeats 4000000 in
/-- **`Nat` as a type** (`evalType`: a statement, on a private copy): `Nat`; the state as it was but for
the [Rec] records a private copy may narrow. -/
theorem runs_evalType_nat {n : Nat} {st st' : MState} {bh : Nat} {v : Value}
    (h : Runs (Ochr.evalType n .nat) st bh v st') (hh : st.headEval = false) (htd : st.tailDecl = none) :
    v = .tNat ∧ ∃ rs nr, st' = { st with recStack := rs, nextRecUid := nr } := by
  cases n with
  | zero =>
    have e : Ochr.evalType 0 Term.nat = inStatement (exhausted "out of fuel") := rfl
    rw [e, inStatement_eq] at h
    obtain ⟨b₁, cur, b₂, hx, hr⟩ := Runs.privately_inv h
    obtain ⟨b₃, cur', hx', rfl⟩ := Runs.withErased_inv hx
    simp only [runs_exhausted_iff] at hx'
  | succ k =>
    rw [evalType_succ, inStatement_eq] at h
    obtain ⟨b₁, cur, b₂, hx, hr⟩ := Runs.privately_inv h
    obtain ⟨b₃, cur', hx', rfl⟩ := Runs.withErased_inv hx
    obtain ⟨vT, s₁, b₄, hev, h₁⟩ := Runs.bind_inv hx'
    obtain ⟨rfl, hk, -, -⟩ := eval_nat_inv hev hh htd
    simp only at h₁
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁
    exact ⟨rfl, runs_restoreKeep_same hr hk.nextAbs.symm hk.nextLoan.symm hk.neutrals.symm hk.etaRefs.symm
      hk.absTy.symm hk.absDecl.symm⟩


/-- What a private computation must leave as it found to be undone whole by `restoreKeep` (the counters,
the generalisation and η records, Δ), and the two fields `evalType` reads on entry. -/
structure Ctr (a b : MState) : Prop where
  nextAbs : b.nextAbs = a.nextAbs
  nextLoan : b.nextLoan = a.nextLoan
  neutrals : b.neutrals = a.neutrals
  etaRefs : b.etaRefs = a.etaRefs
  absTy : b.absTy = a.absTy
  absDecl : b.absDecl = a.absDecl
  headEval : b.headEval = a.headEval
  tailDecl : b.tailDecl = a.tailDecl

theorem Ctr.trans {a b c : MState} (h₁ : Ctr a b) (h₂ : Ctr b c) : Ctr a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5, h₂.6.trans h₁.6,
    h₂.7.trans h₁.7, h₂.8.trans h₁.8⟩

theorem runs_evalType_nat_ctr {n : Nat} {st st' : MState} {bh : Nat} {v : Value}
    (h : Runs (Ochr.evalType n .nat) st bh v st') (hh : st.headEval = false) (htd : st.tailDecl = none) :
    v = .tNat ∧ Ctr st st' := by
  obtain ⟨rfl, rs, nr, rfl⟩ := runs_evalType_nat h hh htd
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runs_pushCaps_nil {k : Nat} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (pushCaps k []) st b u st') : st' = st := by
  cases k with
  | zero => unfold pushCaps at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold pushCaps at h; simp only [List.zipIdx_nil, List.forIn_nil] at h; exact (runs_pure_inv h).2

theorem runs_takeArgBorrow_nb {w : Value} {st st' : MState} {b : Nat} {u : PUnit}
    (h : Runs (takeArgBorrow w) st b u st') (hw : ∀ l c, w ≠ .borrow l c) : st' = st := by
  unfold takeArgBorrow at h
  split at h
  · exact absurd rfl (hw _ _)
  · exact (runs_pure_inv h).2

theorem Runs.noteLoc_bind {β : Type} {l : Option Loc} {n : Note} {k : PUnit → M β} {st st' : MState} {b : Nat}
    {y : β} (h : Runs (noteLoc l n >>= k) st b y st') : Runs (k ()) st b y st' := by
  unfold noteLoc at h
  simp only [bind_assoc, runs_get_bind] at h
  split at h
  · simpa only [runs_pure_bind'] using h
  · split at h
    · exact Runs.log_bind h
    · simpa only [runs_pure_bind'] using h

set_option maxHeartbeats 4000000 in
/-- **[Call-type] of `I` at `Z`** (typed): `Nat`; a private computation that binds the parameter at its
declared type and evaluates the codomain, undone whole but for the [Rec] records. -/
theorem runs_callType_J {k : Nat} {st st' : MState} {b : Nat} {T : Value}
    (h : Runs (Ochr.callType k ColumnI.piNat #[.zero] #[some .tNat]) st b T st') (hh : st.headEval = false)
    (htd : st.tailDecl = none) : T = .tNat ∧ ∃ rs nr, st' = { st with recStack := rs, nextRecUid := nr } := by
  cases k with
  | zero => unfold Ochr.callType at h; simp only [runs_exhausted_iff] at h
  | succ k =>
  unfold Ochr.callType ColumnI.piNat at h
  simp only [List.length_cons, List.length_nil, Array.size, bne_self_eq_false, Bool.false_eq_true, if_false] at h
  obtain ⟨pf, s₁, b₁, hpf, h₁⟩ := Runs.bind_inv h
  clear h
  obtain ⟨rfl, rfl⟩ := runs_paramFlags_nat hpf
  peel h₁
  obtain ⟨saved, s₂, b₂, hg, h₂⟩ := Runs.bind_inv h₁
  clear h₁
  obtain ⟨rfl, rfl⟩ := runs_get_inv hg
  peel h₂
  obtain ⟨T', cur, b₃, hx, h₃⟩ := Runs.bind_inv h₂
  clear h₂
  replace hx := Runs.onFail_inv hx
  obtain ⟨_, s₉, b₄, hr, h₄⟩ := Runs.bind_inv h₃
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₄
  unfold unlocated pushFrame at hx
  peel hx
  obtain ⟨_, s₄, b₆, hcaps, h₄⟩ := Runs.bind_inv hx
  clear hx
  have := runs_pushCaps_nil hcaps
  subst this
  obtain ⟨pd, s₅, b₇, hpd, h₅⟩ := Runs.bind_inv h₄
  clear h₄
  obtain ⟨rfl, rfl⟩ := runs_paramDecls_nat hpd
  simp only [List.zip, List.zipWith, List.zipIdx, List.forIn_cons, List.forIn_nil] at h₅
  obtain ⟨_, s₆, b₈, hloop, h₆⟩ := Runs.bind_inv h₅
  clear h₅
  obtain ⟨step, s₇, b₉, hstep, hm7⟩ := Runs.bind_inv hloop
  clear hloop
  obtain ⟨A, s₈, b₁₀, hA, h₈⟩ := Runs.bind_inv hstep
  clear hstep
  obtain ⟨rfl, hc8⟩ := runs_evalType_nat_ctr hA hh htd
  replace h₈ := Runs.noteLoc_bind h₈
  obtain ⟨_, s₉, b₁₁, hex, h₉⟩ := Runs.bind_inv h₈
  replace hex := Runs.atLoc_inv hex
  have := runs_expectTy_of_beq (by decide) hex
  subst this
  obtain ⟨_, s₁₀, b₁₂, hta, h₁₀⟩ := Runs.bind_inv h₉
  have := runs_takeArgBorrow_nb hta (by intro l c e; simp at e)
  subst this
  obtain ⟨d, s₁₁, b₁₃, hrd, h₁₁⟩ := Runs.bind_inv h₁₀
  obtain ⟨rfl, rfl⟩ := runs_refineDecl_inv hrd
  obtain ⟨_, s₁₂, b₁₄, hpb, h₁₂⟩ := Runs.bind_inv h₁₁
  have := runs_pushBind_inv hpb
  subst this
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁₂
  simp only at hm7
  obtain ⟨rfl, rfl⟩ := runs_pure_inv hm7
  obtain ⟨T₂, s₁₃, b₁₅, hT₂, h₁₃⟩ := Runs.bind_inv h₆
  obtain ⟨rfl, hc13⟩ := runs_evalType_nat_ctr hT₂ (hc8.headEval.trans hh) (hc8.tailDecl.trans htd)
  peel h₁₃
  obtain ⟨rfl, rfl⟩ := runs_pure_inv h₁₃
  refine ⟨rfl, runs_restoreKeep_same hr ?_ ?_ ?_ ?_ ?_ ?_⟩
  · exact hc13.nextAbs.trans hc8.nextAbs
  · exact hc13.nextLoan.trans hc8.nextLoan
  · exact hc13.neutrals.trans hc8.neutrals
  · exact hc13.etaRefs.trans hc8.etaRefs
  · exact hc13.absTy.trans hc8.absTy
  · exact hc13.absDecl.trans hc8.absDecl

end Ochr.Meaning.Steps.Machine
