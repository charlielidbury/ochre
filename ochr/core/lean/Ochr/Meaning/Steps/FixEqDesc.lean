import Ochr.Meaning.Steps.UnderCheck
import Ochr.Meaning.Steps.FixKnot

/-!
# The fixpoint equation of an accepted global, from the descent clause and the knot's goodness (lead37; docs/31 D232, D234)

`FixEqG` (`Steps/FrameRec`: an accepted global's function, at member arguments, is one run of its body with its own
closure bound) is a THEOREM from two clauses of the context, both established at the global's acceptance, in this order
(D213 corrected by D232): the knot's `FnGoodG` (the function is good at every member argument, its type fits its sort:
what `step_member_fix` assembles membership from), then `RecDescG` (the body's output depends on its own binding only
through that binding's function below the arguments' rank, `Steps/UnderCheck`).

The proof is the induction on the bound the paper's recursion case describes. The stage `k + 1` at `c` is the body run
with its own binding the stage-`k` closure at the WEAKENED type; by `RecDescG` it is the body run with the stage-`rank c`
closure, since below `rank c` the two stages agree with the function (the induction); that is the stage `rank c + 1`,
the function at `c`. So every stage agrees with the function below its bound (`stage_agree`), and one more use of
`RecDescG`, at the stage-`rank a` closure and the global's own closure, is the equation.

Not restricted to the frame-free fragment: the derivation reads nothing of the body. The fragment matters where the
equation is used (`CallInPlaceFrame.callInPlace_of`).
-/

namespace Ochr.Meaning.Steps.Form.FixEqDesc

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.Master

/-- A function type that fits its sort fits it at every weakened codomain (the true one below the bound, `Unit`/`True`
above). -/
theorem piFits_weakCod {R : DataRead} {l : Nat} {ps : List PiDom} {out : PiCod} (h : PiFits R l ps out (fun _ => True))
    (rk : List Sem → Nat) (b : Nat) : PiFits R l ps (weakCod l rk b out) (fun _ => True) := by
  cases l with
  | zero =>
    refine ⟨h.1, fun args hm _ => ?_⟩
    show ∃ Q, (if rk args < b then out.cod args else fillTy 0) = TyM.prop Q
    split
    · exact h.2 args hm trivial
    · exact ⟨True, rfl⟩
  | succ n =>
    refine ⟨h.1, fun args hm _ => ?_⟩
    show LevelFit (n + 1) (if rk args < b then out.cod args else fillTy (n + 1))
    split
    · exact h.2 args hm trivial
    · simp only [fillTy, Nat.succ_ne_zero, if_false, TyM.unit, LevelFit]; omega

/-- The stage function at a bound is good everywhere at the weakened codomain (`OutGood'`), given the stage good below
the bound and a type that fits. -/
theorem stageFn_good' {R : DataRead} {l : Nat} {ps : List PiDom} {out : PiCod} {rk : List Sem → Nat} {b : Nat}
    {stage : List Sem → Option BodyOut} (hfit : PiFits R l ps out (fun _ => True))
    (hg : ∀ a, DomMembers R ps a → rk a < b → ∃ o, stage a = some o ∧ OutGood' R ps out a o) :
    ∀ a, DomMembers R ps a → ∃ o, stageFn l ps rk b stage a = some o ∧ OutGood' R ps (weakCod l rk b out) a o := by
  intro a hm
  cases hr : out.isRef with
  | false =>
    obtain ⟨o, h1, h2, h3⟩ := stageFn_good R l ps rk b out stage
      (fun a hm hlt => (hg a hm hlt).imp fun o ⟨e, g, _, len⟩ => ⟨e, g, len⟩) a hm
    exact ⟨o, h1, h2, fun h => by simp [weakCod, hr] at h, h3⟩
  | true =>
    have hl : l ≠ 0 := by
      rintro rfl
      have := h_isRef_zero hfit
      rw [hr] at this; cases this
    obtain ⟨o, h1, h2, h3, h4⟩ := stageFn_good_ref R l hl ps rk b out stage
      (fun a hm hlt => (hg a hm hlt).imp fun o ⟨e, g, ret, len⟩ => ⟨e, g, ret hr, len⟩) a hm
    exact ⟨o, h1, h2, fun _ => h3, h4⟩
where
  h_isRef_zero {R : DataRead} {ps : List PiDom} {out : PiCod} (h : PiFits R 0 ps out (fun _ => True)) :
      out.isRef = false := h.1

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The global's stages (`fixStage` at its forming state, from the counter `0`). -/
noncomputable abbrev stG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) :
    Nat → List Sem → Option BodyOut :=
  fixStage K ρ φ (fbG K ρ φ ds c) (lG K hs ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) dec 0 body

/-- Stage `k + 1` is the body run with its own binding the stage-`k` closure at the weakened type. -/
theorem stG_succ (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) (k : Nat) (a : List Sem) :
    stG K ρ φ hs ds c dec body (k + 1) a =
      fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
        (piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) (weakCod (lG K hs ds c) (fixRank dec) k (outG K ρ φ ds c))) 0 body
        (closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) (weakCod (lG K hs ds c) (fixRank dec) k (outG K ρ φ ds c))
          (stageFn (lG K hs ds c) (psG K ρ φ ds) (fixRank dec) k (stG K ρ φ hs ds c dec body k))) a := rfl

/-- The global's function is the stage `rank + 1`. -/
theorem GG_eq (hs : List Hint) (ds : List Term) (c : Term) (j : Nat) (body : Term) (a : List Sem) :
    GG K ρ φ hs ds c (some j) body a = stG K ρ φ hs ds c (some j) body (fixRank (some j) a + 1) a := rfl

/-- Without `by` (R-dec, docs/31 D296), the global's function is one run of its body with `()` in the slot. -/
theorem GG_none (hs : List Hint) (ds : List Term) (c : Term) (body : Term) :
    GG K ρ φ hs ds c none body =
      fixBodyU K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) 0 body := rfl

/-- **Every stage agrees with the global's function below its bound** (the stabilisation, from `RecDescG` and the
function's goodness, by strong induction on the bound). -/
theorem stage_agree {st : MState} (hd : RecDescG K st) (hg : FnGoodG K st) {n : String} {gd : GDef} {self : Hint}
    {hs : List Hint} {ds : List Term} {c : Term} {j : Nat} {body : Term}
    (hfind : st.globals.find? (·.name == n) = some gd) (hcur : K.cur.map (·.1) ≠ some n)
    (hfn : gd.fn? = some (.fix self hs ds c (some j) body)) :
    ∀ m a, DomMembers K.dm.read (psG K ρ φ ds) a → fixRank (some j) a < m →
      stG K ρ φ hs ds c (some j) body m a = GG K ρ φ hs ds c (some j) body a := by
  obtain ⟨hfit, hgood⟩ := hg n gd self hs ds c (some j) body hfind hcur hfn ρ φ
  have hdesc := hd n gd self hs ds c j body hfind hcur hfn ρ φ
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro a ha hlt
    cases m with
    | zero => exact absurd hlt (Nat.not_lt_zero _)
    | succ k =>
      have hk := ih k (Nat.lt_succ_self k)
      have hr := ih (fixRank (some j) a) hlt
      have gk : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < k →
          ∃ o, stG K ρ φ hs ds c (some j) body k b = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
        fun b hb hl => by rw [hk b hb hl]; exact hgood b hb
      have gr : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < fixRank (some j) a →
          ∃ o, stG K ρ φ hs ds c (some j) body (fixRank (some j) a) b = some o ∧
            OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
        fun b hb hl => by rw [hr b hb hl]; exact hgood b hb
      rw [stG_succ, GG_eq, stG_succ]
      refine hdesc a ha _ _ _ _ rfl rfl (piFits_weakCod hfit _ _) (piFits_weakCod hfit _ _)
        (stageFn_good' hfit gk) (stageFn_good' hfit gr) (fun b hb hlt' => ⟨?_, ?_⟩)
      · have h1 : fixRank (some j) b < k := by omega
        simp only [stageFn, if_pos h1, if_pos hlt']
        rw [hk b hb h1, hr b hb hlt']
      · have h1 : fixRank (some j) b < k := by omega
        simp only [weakCod, if_pos h1, if_pos hlt']

/-- **THE FIXPOINT EQUATION of every accepted global** (docs/31 D232, D234): from the descent clause and the knot's
goodness. Assumes the two clauses of the context (`RecDescG`: read true, its establishment the knot's simulation, D232;
`FnGoodG`: the knot's output, `fix_split` and `stages_below`). -/
theorem fixEqG_of {st : MState} (hd : RecDescG K st) (hg : FnGoodG K st) : FixEqG K st := by
  intro n gd self hs ds c dec body hfind hcur hfn ρ φ args hargs
  -- R-dec (docs/31 D296): without `by` the equation is the definition (`fixBodyU` on both sides)
  cases dec with
  | none => rfl
  | some j =>
  obtain ⟨hfit, hgood⟩ := hg n gd self hs ds c (some j) body hfind hcur hfn ρ φ
  have hagree := stage_agree K ρ φ hd hg hfind hcur hfn
  have gr : ∀ b, DomMembers K.dm.read (psG K ρ φ ds) b → fixRank (some j) b < fixRank (some j) args →
      ∃ o, stG K ρ φ hs ds c (some j) body (fixRank (some j) args) b = some o ∧
        OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) b o :=
    fun b hb hl => by rw [hagree _ b hb hl]; exact hgood b hb
  rw [GG_eq, stG_succ]
  refine hd n gd self hs ds c j body hfind hcur hfn ρ φ args hargs _ _ _ _ rfl rfl (piFits_weakCod hfit _ _) hfit
    (stageFn_good' hfit gr) hgood (fun b hb hlt => ⟨?_, ?_⟩)
  · simp only [stageFn, if_pos hlt]
    exact hagree _ b hb hlt
  · simp only [weakCod, if_pos hlt]

end

end Ochr.Meaning.Steps.Form.FixEqDesc
