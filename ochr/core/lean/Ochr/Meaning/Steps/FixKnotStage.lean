import Ochr.Meaning.Steps.FixKnot
import Ochr.Meaning.ClosureStage

/-!
# The knot restated on the weakened stage closure (for the proof's lead to adopt)

`Steps/FixKnot.lean`'s two closure statements are false as stated (`ClosureCE`), and `MemBelow`
types the definition's global at its true function type, where the stage-`b` closure (good only
below the bound) is not an element unless every result type is already known to be inhabited. Here
the statements in the forms that hold, on the weakened stage closure (`ClosureStage.lean`):

* `OutGood'`: a body's output is good: `OutGood`, plus, at a returned borrow, a returned label with
  an injective backward function (`RetGood`), plus one final content per borrow parameter (what the
  strict construction decodes; the run's frame pop gives exactly one per borrow cell).
* `PiFits`: the function type fits its sort: at sort `0` a borrow-free codomain that is a
  proposition at every member argument tuple; at a data sort `1 ≤ l ≤ 3` the codomain and every
  domain fit the level and the codomain is canonical (the checker's sorts, `Levels.lean`).
* `MemBelow'`: membership below the bound, the global being the stage closure typed at the
  weakened function type (true codomain below `b`, `Unit`/`True` above).
* Proved from the data layer: the stage closure is a member of the type the global carries
  (`memBelow'_mem`); applied below the bound it is the function's result at the true codomain
  (`memBelow'_apply`); `MemBelow'` at bound `0` holds of any function (`memBelow'_zero`); and the
  knot's final step, a closure whose function is total and good is a member of its true type
  (`closure_mem_of_total_stmt`).

The run's `.fix` clause builds its stages on the weakened closure (`RunCongr.fixStage`): stage
`b + 1` binds `self` to `MemBelow'`'s global at bound `b` with `fn` the stage `b`. What adopting
this changes on the lead's side (not done here): `GlobalsOk.ty` asks the definition being checked
(`K.cur`) to be typed at the weakened Π, not at its stored type; `fix_split`'s step carries
`OutGood'` and the result `PiFits`.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- **A body's output is good** at arguments: `OutGood`, a returned borrow's label and injective
backward function, and one final content per borrow parameter. -/
def OutGood' (R : DataRead) (ds : List PiDom) (out : PiCod) (args : List Sem) (o : BodyOut) : Prop :=
  OutGood R ds out args o ∧ (out.isRef = true → RetGood R out args o) ∧
    o.finals.length = (ds.filter (·.isRef)).length

/-- **A function type fits its sort**: at sort `0`, a borrow-free codomain that is a proposition at
every member argument tuple; at a data sort `1 ≤ l ≤ 3`, at every member argument tuple, the
codomain fits the level and is canonical, and every domain fits the level. -/
def PiFits (R : DataRead) : Nat → List PiDom → PiCod → Prop
  | 0, ds, out => out.isRef = false ∧ ∀ args, DomMembers R ds args → ∃ P, out.cod args = TyM.prop P
  | n + 1, ds, out => n + 1 ≤ 3 ∧ ∀ args, DomMembers R ds args →
      LevelFit (n + 1) (out.cod args) ∧ (out.cod args).Canon ∧
        ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit (n + 1) (d.dom (args.take i))

/-- **Membership below a bound, on the weakened stage closure**: the global is the stage closure of
a function good (`OutGood'`) at member arguments whose decreasing component has rank below `b`,
typed at the weakened function type, along a function type that fits its sort. -/
def MemBelow' (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) : Prop :=
  ∃ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (fn : List Sem → Option BodyOut),
    PiFits K.dm.read l ds out ∧
    G.1 = closureAt K.dm.read l φ ds (weakCod l (decRank K g) b out) (stageFn l ds (decRank K g) b fn) ∧
    G.2.m = piTyAt K.dm.read l ds (weakCod l (decRank K g) b out) ∧
    ∀ args, DomMembers K.dm.read ds args → decRank K g args < b →
      ∃ o, fn args = some o ∧ OutGood' K.dm.read ds out args o

/-- **The stage closure is a member of the type the global carries** (the weakened function type):
an honest element, so `MemBelow'` is consistent with membership. -/
theorem memBelow'_mem (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow' K G g b) :
    G.1 ∈ₛ[K.dm.read] G.2.m := by
  obtain ⟨l, φ, ds, out, fn, hfit, h1, h2, hgood⟩ := h
  rw [h1, h2]
  cases l with
  | zero =>
    obtain ⟨hdata, hprop⟩ := hfit
    exact stage_mem_prop _ φ ds out _ b fn hdata (fun args hm _ => hprop args hm)
      (fun args hm hlt => by
        obtain ⟨o, hg, ⟨⟨hres, -⟩, -⟩⟩ := hgood args hm hlt
        exact ⟨o, hg, hres⟩)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    cases hr : out.isRef with
    | false =>
      exact stage_mem _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr (fun args hm _ => (hall args hm).1)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hlen⟩)
    | true =>
      exact stage_mem_ref _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr (fun args hm _ => (hall args hm).1)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hret hr, hlen⟩)

/-- **`MemBelow'` at bound `0` holds of any function** along a fitting type (the induction's base:
the stage-`0` closure is `()`/`True`-valued everywhere). -/
theorem memBelow'_zero (K : RunCtx) (g : GDef) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (fn : List Sem → Option BodyOut) (hfit : PiFits K.dm.read l ds out) :
    MemBelow' K (closureAt K.dm.read l φ ds (weakCod l (decRank K g) 0 out) (stageFn l ds (decRank K g) 0 fn),
      .plain (piTyAt K.dm.read l ds (weakCod l (decRank K g) 0 out))) g 0 :=
  ⟨l, φ, ds, out, fn, hfit, rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **The closure lemma's application half, read through `MemBelow'`** (the form of
`closure_apply` that holds): at a data sort, the global called at member arguments whose decreasing
component has rank below the bound gives the function's result there, typed at the TRUE codomain
(under a fresh label at a returned borrow), and that result is good. -/
theorem memBelow'_apply (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow' K G g b) :
    ∃ (l : Nat) (ds : List PiDom) (out : PiCod) (fn : List Sem → Option BodyOut),
      PiFits K.dm.read l ds out ∧
      (∀ args, DomMembers K.dm.read ds args → decRank K g args < b →
        ∃ o, fn args = some o ∧ OutGood' K.dm.read ds out args o) ∧
      (1 ≤ l → ∀ (args : List Res) (s : SState), DomMembers K.dm.read ds (args.map (·.1)) →
        decRank K g (args.map (·.1)) < b →
        ∃ o, fn (args.map (·.1)) = some o ∧ OutGood' K.dm.read ds out (args.map (·.1)) o ∧
          ∃ (lab : Option Nat) (s' : SState),
            callOf K.dm.read G args s = some ((o.result, ⟨out.cod (args.map (·.1)), lab⟩), s') ∧
            (out.isRef = false → lab = none)) := by
  obtain ⟨l, φ, ds, out, fn, hfit, h1, h2, hgood⟩ := h
  refine ⟨l, ds, out, fn, hfit, hgood, fun hl1 args s hm hlt => ?_⟩
  have hc : callOf K.dm.read G args s = callOf K.dm.read (G.1, .plain G.2.m) args s := rfl
  rw [hc, h1, h2]
  obtain ⟨o, hg, hgd⟩ := hgood _ hm hlt
  refine ⟨o, hg, hgd, ?_⟩
  cases l with
  | zero => exact absurd hl1 (by omega)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    obtain ⟨-, hcanon, hdom⟩ := hall _ hm
    cases hr : out.isRef with
    | false =>
      obtain ⟨s', hs'⟩ := stage_apply _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr
        (fun args hm _ => (hall args hm).1)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hlen⟩) args s o hm hdom hlt hcanon hg
      exact ⟨none, s', hs', fun _ => rfl⟩
    | true =>
      obtain ⟨k, s', hs'⟩ := stage_apply_ref _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr
        (fun args hm _ => (hall args hm).1)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hret hr, hlen⟩) args s o hm hdom hlt hcanon hg
      exact ⟨some k, s', hs', fun h => by cases h⟩

/-- **The closure lemma's membership half, in the form that holds** (the knot's last step,
`Assembly.step_member_fix`): a closure whose function is defined and good (`OutGood'`) at every
member argument is a member of its TRUE function type, along a type that fits its sort. -/
theorem closure_mem_of_total_stmt (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hfit : PiFits R l ds out)
    (htot : ∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood' R ds out args o) :
    closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out := by
  cases l with
  | zero =>
    obtain ⟨hdata, hprop⟩ := hfit
    exact closure_mem_prop' R φ ds out g hdata hprop (fun args hm => by
      obtain ⟨o, hg, ⟨⟨hres, -⟩, -⟩⟩ := htot args hm
      exact ⟨o, hg, hres⟩)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    cases hr : out.isRef with
    | false =>
      exact closure_mem_of_total' R (n + 1) φ ds out g ⟨by omega, hle⟩ hr (fun args hm => (hall args hm).1)
        (fun args hm => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := htot args hm
          exact ⟨o, hg, hgd, hlen⟩)
    | true =>
      exact closure_mem_of_total_ref' R (n + 1) φ ds out g ⟨by omega, hle⟩ hr (fun args hm => (hall args hm).1)
        (fun args hm => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := htot args hm
          exact ⟨o, hg, hgd, hret hr, hlen⟩)

/-- **The knot's conclusion, restated** (what `Assembly.step_member_fix` becomes on `fix_split`
restated to `OutGood'` and `PiFits`): from the induction step at `OutGood'`, the guarded fixpoint's
closure is a member of its true function type. -/
theorem knot_member (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (stage : Nat → List Sem → Option BodyOut) (rank : List Sem → Nat) (hfit : PiFits R l ds out)
    (hstep : ∀ b, (∀ a, DomMembers R ds a → rank a < b → ∃ o, stage (rank a + 1) a = some o ∧ OutGood' R ds out a o) →
      ∀ a, DomMembers R ds a → rank a = b → ∃ o, stage (b + 1) a = some o ∧ OutGood' R ds out a o) :
    closureAt R l φ ds out (fun args => stage (rank args + 1) args) ∈ₛ[R] piTyAt R l ds out :=
  closure_mem_of_total_stmt R l φ ds out _ hfit
    (fun args ha => stages_total stage rank (DomMembers R ds) (OutGood' R ds out) hstep args ha)

end Ochr.Meaning.Steps
