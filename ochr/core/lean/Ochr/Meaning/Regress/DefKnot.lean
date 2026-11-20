import Ochr.Meaning.Steps.FixKnot
import Ochr.Meaning.Regress.CodeClosures
import Ochr.Examples.Nat

/-!
# The knot of [Def]: `checkFix_sound`'s hypothesis holds its conclusion (docs/31 D72; kernel-checked)

`Check.checkDef` pushes a function's global (`fn? := some fixT`, `ty := tPi [] (pi x̄ Ā B) []`) BEFORE
it runs `checkFix (.gfn f) [] fixT`, so that recursive calls find it. `checkFix_sound_stmt` asks
`CtxOk K ρ st` at that state, and `CtxOk`'s `GlobalsOk` asks every global of the state to mean the
closure of its code (`fn`), at its stored type (`ty`), and to be a member of it (`mem`). For the
global being defined that is already `checkFix_sound`'s conclusion (`ctxOk_contains_fix_member`):
at a definition the statement is vacuous, and nothing else in the chain proves an accepted function
a member of its type. Assembling `defn_member` cannot close as the statements stand: the definition's
own membership has to come from the guarded recursion on its decreasing argument, with `CtxOk`
asking of the definition being checked only what that recursion gives (membership at arguments of
smaller rank), not the whole of it.
-/

open Ochr.Test

-- A recursive definition through the knot (docs/31 D79): `Double` accepted, a self call at the same
-- argument rejected by [Rec].
ochr DefKnotProbe uses Nats {
  def Double (n : Nat) : Nat by n := match n { Z => Z, S m => S(S(Double(m))) }
  reject def Same (n : Nat) : Nat by n := Same(n)
}

namespace Ochr.Meaning.Regress.DefKnot
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **`CtxOk` at a state holding a function's global already makes it a member of its type.** -/
theorem ctxOk_contains_fix_member (K : RunCtx) (ρ : Assignment) (φ : Future) (st : MState) (hctx : CtxOk K ρ st)
    (n : String) (g : GDef) (t : Term) (hg : st.globals.find? (·.name == n) = some g) (hfn : g.fn? = some t)
    (hcur : K.cur = none) :
    meanV K ρ φ (.plain .err) (.clo [] t []) ∈ₛ[K.dm.read] (meanV K ρ noFuture (.plain .err) g.ty).asTy := by
  have hne : (K.cur.map (·.1)) ≠ some n := by rw [hcur]; exact fun h => by cases h
  have h1 := (hctx.globals.fn n g t hg hfn hne ρ φ).1
  have h2 := hctx.globals.mem n g hg hne
  have h3 := hctx.globals.ty n g hg hne ρ
  rw [h1, h3] at h2
  exact h2

/-- **The knot cut** (docs/31 D73, D79): with the definition being checked named in the context at the
bound `0`, `CtxOk` asks of its global only `MemBelow 0`: that it be the stage-`0` closure at the
weakened function type (`Unit`/`True`-valued everywhere), of a function asked nothing (no argument
has a rank below `0`). Nothing of the conclusion is assumed (`Steps.memBelow_zero`). -/
theorem memBelow_zero' (K : RunCtx) (g : GDef) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (fn : List Sem → Option BodyOut) (hl : l ≤ 3) (h0 : l = 0 → out.isRef = false) :
    MemBelow K (closureAt K.dm.read l φ ds (weakCod l (decRank K g) 0 out) (stageFn l ds (decRank K g) 0 fn),
      .plain (piTyAt K.dm.read l ds (weakCod l (decRank K g) 0 out))) g 0 :=
  memBelow_zero K g l φ ds out fn hl h0

/-! ## `Double` through the knot's induction (kernel-checked)

`Double`'s closure as the `.fix` clause builds it (`CodeClosures`: its body as the function on
meanings it computes, `dblBody`; each stage's `self` the stage below at the weakened function type,
docs/34; at arguments of rank `r` the stage `r + 1`, `gOf`). The step of the induction on the bound holds at every bound (`double_step`), so the knot's induction (`stages_below`) makes the fixpoint good at
every member argument (`double_total`), and its closure is a member of its type (`double_member`, the
closure lemma's membership half on this instance). The step is in the run's shape: stage `b + 1` is
good below `b + 1` (`stage_val`: stage `n` doubles every `x < n`). The checker accepts `Double` and rejects `Same`. -/

open Ochr.Meaning.Regress.CodeClosures in
/-- The domain and codomain of `Π(n : Nat). Nat` as the `.fix` clause reads them. -/
def dsNat : List PiDom := [⟨false, fun _ => TyM.nat⟩]

def outNat : PiCod := ⟨false, fun _ => TyM.nat⟩

theorem nat_of_mem {R : DataRead} {x : Sem} (h : x ∈ₛ[R] TyM.nat) : ∃ n, x = .el0 Nat n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.symm⟩

theorem args_of_members {R : DataRead} {a : List Sem} (h : DomMembers R dsNat a) : ∃ n, a = [.el0 Nat n] := by
  obtain ⟨hl, hm⟩ := h
  match a, hl with
  | [x], _ =>
    obtain ⟨n, rfl⟩ := nat_of_mem (hm 0 x _ rfl rfl)
    exact ⟨n, rfl⟩

open Ochr.Meaning.Regress.CodeClosures in
/-- **The step of the induction on the bound, for `Double`**, in the run's shape: at member arguments
of rank below `b + 1` the stage `b + 1` is good (`OutGood'`; whatever stage `b` is below `b`: here the
stages compute outright). -/
theorem double_step (R : DataRead) (φ : Future) (b : Nat)
    (_ : ∀ a, DomMembers R dsNat a → rankOf R a < b →
      ∃ o, stage R φ b a = some o ∧ OutGood' R dsNat outNat a o) :
    ∀ a, DomMembers R dsNat a → rankOf R a < b + 1 →
      ∃ o, stage R φ (b + 1) a = some o ∧ OutGood' R dsNat outNat a o := by
  intro a ha hr
  obtain ⟨n, rfl⟩ := args_of_members ha
  rw [rankOf_nat] at hr
  refine ⟨_, stage_val φ (b + 1) n hr, ⟨⟨⟨2 * n, rfl⟩, ?_⟩, fun h => by simp [outNat] at h, rfl⟩⟩
  intro i d hd hr
  rcases i with _ | i
  · simp only [dsNat, List.getElem?_cons_zero, Option.some.injEq] at hd
    subst hd; cases hr
  · simp [dsNat] at hd

open Ochr.Meaning.Regress.CodeClosures in
/-- **`Double`'s fixpoint is good at every member argument**, by the knot's induction. -/
theorem double_total (R : DataRead) (φ : Future) :
    ∀ a, DomMembers R dsNat a → ∃ o, gOf R φ a = some o ∧ OutGood' R dsNat outNat a o :=
  stages_below (stage R φ) (rankOf R) (DomMembers R dsNat) (OutGood' R dsNat outNat)
    (double_step R φ)

open Ochr.Meaning.Regress.CodeClosures in
/-- **`Double`'s closure is a member of its type**: the closure lemma's membership half on this
instance (`closure_mem_of_total` at the level `1`, whose code is `tNN`), from `double_member`. -/
theorem double_closure_member (R : DataRead) (φ : Future) :
    closureAt R 1 φ dsNat outNat (gOf R φ) ∈ₛ[R] piTyAt R 1 dsNat outNat :=
  (double_member φ).1

end Ochr.Meaning.Regress.DefKnot
