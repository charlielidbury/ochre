import Ochr.Meaning.Steps.CallBody
import Ochr.Meaning.FrameProp

/-!
# The frame property at the smallest call from a non-empty caller: `J2` (lead15, 2026-11-21; docs/31 D128)

`def J2 : Nat := (let x = S(Z); I(x))` (core; the surface `let x = 1; I(x)`, asserted). At the call
the caller's frame holds `x`, moved by the argument's read; the callee's frame is pushed on it.

**The ruling (docs/31 D127, (S1) refined).** The frame relation relates the function's binding of
itself by a clause of its own, `SelfRel` (each side a member of its own stored type), keyed on where
the construction puts it (after the captures: index `#caps`, `0` for a global), and asks equality at
every other binding. As stated now, for bodies in which the function's own name does not occur.

**What this file gives.**
- The checker at `J2`'s call, by `#guard`: the callee's state is `[{x ↦ ⊥ : Nat}, {I ↦ .gfn I, n ↦ S(Z)
  lazily typed}]` at counter 0; the body runs untyped; the call returns `S(S(Z))` at `Nat`.
- `SelfRel`, `FrameRelS`, `FrameAgreeS`: `FrameProp.FrameRel`/`FrameAgree` with the function's own
  binding exempt from equality and related by `SelfRel`.
- `inPlaceJ2`, `closureJ2`: the two states the frame property compares at `J2`'s call, explicit.
- **`FrameJ2`**: EXACTLY the instance of the frame property `J2`'s step needs, one named model fact
  (the model lane's to prove; this statement is its specification).
-/

open Ochr.Test

ochr CallProbeJ2 {
  def Ip (n : Nat) : Nat := S(n)
  def J2p : Nat := (let x = 1; Ip(x))
}

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

namespace FrameJ2

/-! ## The checker at `J2`'s call -/

namespace Guards

open Ochr.Surface
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)
open ParGuards (bodyOf bindOk declIs)
open ColumnI (piNat gI)

/-- `J2`'s body. -/
def bodyJ2 : Term := .letIn ⟨"x"⟩ (.succ .zero) (.call (.const "I") [.place (.var 0)] false)
def defJ2 : Def := { name := "J2", hs := [], doms := [], cod := .nat, body := bodyJ2 }
def stJ2 : MState := { env := #[{}], globals := [gI] }

-- the surface `let x = 1; Ip(x)` is this term
#guard bodyOf CallProbeJ2 "J2p" == .letIn ⟨"x"⟩ (.succ .zero) (.call (.const "Ip") [.place (.var 0)] false)
#guard isOk (checkDef defJ2) stJ2 100000
-- the body is `S(S(Z))` at `Nat`, the state `stJ2`'s again (the `let` drops `x`)
#guard outVal (Ochr.eval 100 true bodyJ2 (some .tNat)) stJ2 100000 == (.succ (.succ .zero), some .tNat)
#guard CallGuards.startOk "I" (outSt (Ochr.eval 100 true bodyJ2 (some .tNat)) stJ2 100000)

def deep : List (Bool × Option (Value × Option Value) × MState) :=
  match runMachine (Ochr.eval 100 true bodyJ2 (some .tNat)) { stJ2 with cfg := { recordDeep := true } } 100000 with
  | (_, _, log) => log.toList.filterMap fun
      | LogEntry.deep ex fl st => some (ex, fl, st) | _ => none

/-- The callee's state at `J2`'s call: the caller's frame `{x ↦ w : Nat}` (moved by the argument's read),
the callee's frame on it, counter 0. -/
def calleeOk (st : MState) (w : Value) : Bool :=
  st.env.size == 2 && st.env[0]!.binds.size == 1 && bindOk st.env[0]!.binds[0]! "x" .bot .tNat .other none &&
  st.env[0]!.temps.isEmpty && CallGuards.calleeFrameOk st.env[1]! w && st.nextLoan == 0 && st.absTy.isEmpty &&
  st.depth == 1

#guard deep.length == 4
-- the body's entry: the callee's state, `n ↦ S(Z)` lazily typed, in tail position
#guard match deep with
  | (false, _, st) :: _ =>
    -- `calleeFrameOk` asks the deferred type at `[Z]`; here the argument is `S(Z)`
    st.env.size == 2 && bindOk st.env[0]!.binds[0]! "x" .bot .tNat .other none &&
    bindOk st.env[1]!.binds[0]! "I" (.gfn "I") piNat (.pi .other) none &&
    st.env[1]!.binds[1]!.val == .succ .zero && st.env[1]!.binds[1]!.ty.isNone &&
    st.env[1]!.binds[1]!.lazyTy.any (fun (P, ws, i) => P == piNat && ws == [.succ .zero] && i == 0) &&
    st.nextLoan == 0 && st.tailNext && st.depth == 1
  | _ => false
-- the read returns `S(Z)` with no type; the body `S(S(Z))` at `Nat`
#guard match deep with
  | [_, _, (true, some (v, T), _), (true, some (v', T'), _)] =>
    v == .succ .zero && T.isNone && v' == .succ (.succ .zero) && T' == some .tNat
  | _ => false

end Guards

/-! ## The frame relation with the function's own binding related by its own clause (the ruling) -/

/-- The binding at index `i` of the top frame. -/
def topBind? (s : SState) (i : Nat) : Option SBinding := s.env.getLast?.bind (·.binds[i]?)

/-- The state with the top frame's binding `i` replaced. -/
def setTopBind (s : SState) (i : Nat) (b : SBinding) : SState :=
  { s with env := s.env.modify s.topIdx fun fr => { fr with binds := fr.binds.set i b } }

/-- **`SelfRel`** (the ruling, docs/31 D127): at the function's binding of itself, each side's value is
a member of its own stored type at every future, the type carrying no label; the readings and the
recursion records agree. Nothing relates the two values (in place the callee's meaning at its
declared type, in the closure the stage below at the weakened type). Planned, not built: for a
recursive function, "the two agree when applied to arguments below the current one". -/
def SelfRel (R : DataRead) (b b' : SBinding) : Prop :=
  (∀ ψ, b.val ψ ∈ₛ[R] b.ty.m) ∧ (∀ ψ, b'.val ψ ∈ₛ[R] b'.ty.m) ∧ b.ty.label = none ∧ b'.ty.label = none ∧
    b.decl = b'.decl ∧ b.recBound = b'.recBound

/-- **The frame relation, the function's own binding (top frame, index `i`: after the captures)
related by `SelfRel`**: `FrameRel` between the in-place state and the closure's state with that one
binding replaced by the in-place one. -/
def FrameRelS (R : DataRead) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (i : Nat) (s s' : SState) : Prop :=
  ∃ b b', topBind? s i = some b ∧ topBind? s' i = some b' ∧ SelfRel R b b' ∧ FrameRel σ s₀ ks s (setTopBind s' i b)

/-- The two runs agree, the end states related by `FrameRelS`. -/
def FrameAgreeS (R : DataRead) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (i : Nat) :
    Option (Res × SState) → Option (Res × SState) → Prop
  | some (r, s₁), some (r', s₁') => r.1 = r'.1 ∧ r.2 = { r'.2 with label := r'.2.label.map σ } ∧ FrameRelS R σ s₀ ks i s₁ s₁'
  | none, none => True
  | _, _ => False

/-! ## The two states at `J2`'s call -/

open ColumnI

/-- The parameter's binding on both sides: the number `a` at `Nat`, read `.other`. -/
noncomputable def nBind (a : Nat) : SBinding := { ty := .plain TyM.nat, val := fun _ => .el0 Nat a, decl := .other }

/-- **In place** (`CallRef.callFrame` at `J2`'s call, as the checker's `runBodyCore`): the caller's
reference state `s₂`, the callee's frame pushed on it holding `I ↦ f` at `I`'s declared Π-type
`Π(n : Nat). Nat` (the context's global), then `n ↦ a`. -/
noncomputable def inPlaceJ2 (R : DataRead) (s₂ : SState) (f : Sem) (a : Nat) : SState :=
  (s₂.pushFrame.pushBind { ty := .plain (piTyAt R 1 psI outI), val := fun _ => f, decl := .pi .other }).pushBind (nBind a)

/-- **The closure's state** (the `.fix` clause's `fixBodyAt` for `I` at `a`, column `I`'s `start_I`): a fresh
bottom frame, then `I ↦` stage 0 at the weakened type `Π(n : Nat). Unit`, then `n ↦ a`, counter 0. -/
noncomputable def closureJ2 (R : DataRead) (φ : Future) (a : Nat) : SState :=
  ((emptyState 0).under.pushBind { ty := .plain (selfTy R), val := fun _ => selfSem R φ, decl := .pi .other }).pushBind (nBind a)

/-- **The instance of the frame property `J2`'s step needs** (a model fact, assumed; the model lane's to
prove; docs/31 D128). At every context with `FundCtx` and every caller state `s₂` (here `J2`'s frame
`{x ↦ moved : Nat}`, but any): the run of `I`'s body `S(#0)` in place, from `s₂` with the callee's frame
pushed, and the run in the closure's own state, at any tail flags and hints, agree. Its hypotheses,
spelled out:
- *below*: the caller's frames read no label at or above the counter `c = s₂.nextLoan`, hold none of
  the frame's labels and lend nothing into the callee's frame (`FrameStart` at no parameter); the
  in-place state is good (`SGood`, as the restated `run_frame` asks);
- *the argument*: a number `a`, at `Nat`, carrying no label;
- *cells*: none (`ks = []`: no borrow parameter);
- *labels and counters*: the renaming `σ l = c + l` takes the closure's labels (counter 0) to the
  in-place ones (counter `c`); no label is live at the call on either side;
- *the function's own binding* (index 0: no capture): related by `SelfRel` (in place the global's
  meaning `f`, a member of `Π(n : Nat). Nat`; in the closure stage 0, a member of `Π(n : Nat). Unit`),
  every other binding equal (`FrameRelS`);
- *the body*: `I`'s, in which `I`'s own name does not occur.
Conclusion: the same result (its label renamed), and the end states related (`FrameAgreeS`). -/
def FrameJ2 : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (s₂ : SState) (f : Sem) (a : Nat) (tl tl' : Bool) (h h' : TyS),
    Strict.FundCtx K →
    FrameStart (inPlaceJ2 K.dm.read s₂ f a) [] →
    Strict.SGood K.dm K.Γ φ (inPlaceJ2 K.dm.read s₂ f a) →
    FrameRelS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (inPlaceJ2 K.dm.read s₂ f a) (closureJ2 K.dm.read φ a) →
    FrameAgreeS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (runT K ρ φ tl h bodyI (inPlaceJ2 K.dm.read s₂ f a)) (runT K ρ φ tl' h' bodyI (closureJ2 K.dm.read φ a))


/-! ## Steps (3) and (4) of `J2`'s plan compose (docs/31 D128) -/

/-- **The closure's run of `I`'s body is what the checker's untyped run in place computed**: from the
checker's callee state related to the in-place reference state (`Pre`, `Rel`, `SGood` there: the glue
of step (4), hypotheses here), the untyped body step (`bodyLazy_sim`) gives the in-place run's
success and that its result is the meaning of the checker's value; `FrameJ2` carries both to the
closure's own state, the run `callOf` applies. Assumes `BodyLazyInv`, `InvNumA` (checker) and `FrameJ2`
(model). -/
theorem closureRun_of_checker (hB : CallBody.BodyLazyInv) (hN : InvNumA) (hFJ : FrameJ2)
    {K : RunCtx} {ρ : Assignment} {φ : Future} {R : List DeclInfo} (hd : ParDecI K.D R) (hc : Strict.FundCtx K)
    {s₂ : SState} {f : Sem} {a : Nat} {st st' : MState} {n : Nat} {hint : Option Value} {bh : Nat} {v : Value}
    {T? : Option Value} {π : Nat → Nat}
    (hP : CallBody.LazyNum K ρ R st) (hm : Mode st) (hp : Pre K ρ st)
    (hr : Rel K ρ φ π st (inPlaceJ2 K.dm.read s₂ f a)) (hS : Strict.SGood K.dm K.Γ φ (inPlaceJ2 K.dm.read s₂ f a))
    (hfs : FrameStart (inPlaceJ2 K.dm.read s₂ f a) [])
    (hrel : FrameRelS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (inPlaceJ2 K.dm.read s₂ f a) (closureJ2 K.dm.read φ a))
    (hfl : K.D.flags (scopeOf (inPlaceJ2 K.dm.read s₂ f a)) bodyI = (false, false)) (hD : DecTab K.D st')
    (h : Runs (Ochr.eval n false bodyI hint) st bh (v, T?) st') (tl : Bool) (h' : TyS) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a) = some (r, s') ∧
      ∃ T : TyS, meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) T v = r.1 := by
  obtain ⟨ρ', Δ', π', r, s₁, -, hx, hmean, -, -, -, -⟩ :=
    CallBody.bodyLazy_out (K := K) (ρ := ρ) (φ := φ) hB hN hd n st st' hint v T? _ π hP hm hp hr hfl hD bh h
  have hag := hFJ K ρ φ s₂ f a st.tailNext tl (hintM K ρ hint) h' hc hfs hS hrel
  rw [hx] at hag
  cases hcl : runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a) with
  | none => rw [hcl] at hag; exact hag.elim
  | some rs =>
    rw [hcl] at hag
    exact ⟨ρ', Δ', π', rs.1, rs.2, rfl, _, hmean.trans hag.1⟩

/-! ## The check on the model's side: the relation holds at `J2`'s call -/


theorem modify_append_len {α : Type _} (l : List α) (x : α) (g : α → α) : (l ++ [x]).modify l.length g = l ++ [g x] := by
  induction l with
  | nil => simp [List.modify]
  | cons a l ih => simp [List.modify_succ_cons, ih]

theorem closureJ2_shape (R : DataRead) (φ : Future) (a : Nat) (p : Pos) : (closureJ2 R φ a).shape p = none := by
  simp only [closureJ2, SState.pushBind, SState.under, emptyState]
  cases p.down? <;> rfl

theorem closureJ2_lent (R : DataRead) (φ : Future) (a : Nat) (l : Nat) : (closureJ2 R φ a).lent l = [] := by
  simp [closureJ2, SState.pushBind, SState.under, emptyState]

theorem closureJ2_env (R : DataRead) (φ : Future) (a : Nat) : (closureJ2 R φ a).env =
    [{}, { binds := [{ ty := .plain (selfTy R), val := fun _ => selfSem R φ, decl := .pi .other }, nBind a] }] := by
  simp [closureJ2, SState.pushBind, SState.under, emptyState, SState.topIdx]

theorem inPlaceJ2_env (R : DataRead) (s₂ : SState) (f : Sem) (a : Nat) : (inPlaceJ2 R s₂ f a).env =
    s₂.env ++ [{ binds := [{ ty := .plain (piTyAt R 1 psI outI), val := fun _ => f, decl := .pi .other }, nBind a] }] := by
  simp [inPlaceJ2, SState.pushBind, SState.pushFrame, SState.topIdx, modify_append_len]


/-- **`FrameJ2`'s relation holds at `J2`'s call** (the check that its hypothesis is met where `J2`
uses it, kernel-checked): the in-place state and the closure's state are related by `FrameRelS` at
the renaming `l ↦ c + l`, when the global's meaning is a member of `I`'s declared type and the
caller's holders and lent sites are its own positions. -/
theorem frameRelS_start (R : DataRead) (φ : Future) (s₂ : SState) (f : Sem) (a : Nat)
    (hf : f ∈ₛ[R] piTyAt R 1 psI outI)
    (hsh : ∀ p : Pos, p.frameOf = s₂.env.length → s₂.shape p = none)
    (hlent : ∀ l (x : Site), x ∈ s₂.lent l → x.pos.frameOf < s₂.env.length) :
    FrameRelS R (fun l => s₂.nextLoan + l) (inPlaceJ2 R s₂ f a) [] 0 (inPlaceJ2 R s₂ f a) (closureJ2 R φ a) := by
  let bIn : SBinding := { ty := .plain (piTyAt R 1 psI outI), val := fun _ => f, decl := .pi .other }
  let bCl : SBinding := { ty := .plain (selfTy R), val := fun _ => selfSem R φ, decl := .pi .other }
  have hti : topBind? (inPlaceJ2 R s₂ f a) 0 = some bIn := by simp [topBind?, inPlaceJ2_env, bIn]
  have htc : topBind? (closureJ2 R φ a) 0 = some bCl := by simp [topBind?, closureJ2_env, bCl]
  refine ⟨bIn, bCl, hti, htc, ⟨fun _ => hf, fun _ => selfSem_mem R φ, rfl, rfl, rfl, rfl⟩, ?_⟩
  have hcl : (setTopBind (closureJ2 R φ a) 0 bIn).env = [{}, { binds := [bIn, nBind a] }] := by
    simp [setTopBind, closureJ2_env, SState.topIdx]
  have hclsh : ∀ p, (setTopBind (closureJ2 R φ a) 0 bIn).shape p = none := fun p => closureJ2_shape R φ a p
  have hcll : ∀ l, (setTopBind (closureJ2 R φ a) 0 bIn).lent l = [] := fun l => closureJ2_lent R φ a l
  have hlive : ∀ l, ¬ (setTopBind (closureJ2 R φ a) 0 bIn).Live l := by
    intro l hl; unfold SState.Live SState.liveLabels at hl; simp [hclsh] at hl
  have htop : (inPlaceJ2 R s₂ f a).topIdx = s₂.env.length := by simp [SState.topIdx, inPlaceJ2_env]
  have hsh' : ∀ p, (inPlaceJ2 R s₂ f a).shape p = s₂.shape p := fun _ => rfl
  have hlt' : ∀ l, (inPlaceJ2 R s₂ f a).lent l = s₂.lent l := fun _ => rfl
  have hren : ∀ b : SBinding, b.ty.label = none → (∀ ψ ψ', b.val ψ = b.val ψ') →
      BindRen (fun l => s₂.nextLoan + l) b b := fun b hl hv => by
    refine ⟨?_, rfl, rfl, fun ψ => hv _ _⟩
    cases b with | mk ty val decl recBound => cases ty with | mk m lab => simp at hl; subst hl; rfl
  refine ⟨fun l l' h => by simp at h; omega, fun j => by show s₂.nextLoan + (0 + j) = s₂.nextLoan + j; omega,
    ⟨rfl, by rw [hcl]; rfl⟩, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ _ _ _ => rfl, fun l hl => absurd hl (hlive l)⟩
  · refine ⟨{ binds := [bIn, nBind a] }, { binds := [bIn, nBind a] }, by rw [inPlaceJ2_env]; simp; rfl, by rw [hcl]; simp,
      rfl, fun i b b' hb hb' => ?_, rfl, fun j v hv => by simp at hv⟩
    all_goals try rfl
    rw [hb] at hb'; cases hb'
    rcases i with _ | _ | i
    · simp at hb; subst hb; exact hren _ rfl (fun _ _ => rfl)
    · simp at hb; subst hb; exact hren _ rfl (fun _ _ => rfl)
    · simp at hb
  · intro p hp; rw [hclsh, hsh']; exact hsh p (by rw [hp, htop])
  · intro q l hq; rw [hclsh] at hq; cases hq
  · intro l hl; exact absurd hl (hlive l)
  · intro l x hx
    rw [hcll, hlt']
    simp only [List.not_mem_nil, iff_false]
    intro hm; have := hlent _ x hm; rw [hx, htop] at this; omega
  · intro m x hx hm; rw [hlt'] at hm; have := hlent _ x hm; rw [hx, htop] at this; omega
  · intro l x hx; rw [hcll] at hx; cases hx


end FrameJ2

end Ochr.Meaning.Steps.Form
