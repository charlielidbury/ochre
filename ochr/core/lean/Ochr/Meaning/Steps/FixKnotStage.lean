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
* `PiFits`, `PiCallable`: what the closure lemmas consume of the function type beyond goodness,
  at the argument tuples a guard admits: for membership, at sort `0` a borrow-free codomain that is
  a proposition, at a data sort `1 ≤ l ≤ 3` a codomain that fits the level (`PiFits`); for a call,
  a canonical codomain and domains that fit the level (`PiCallable`). The checker's sorts give them
  (`Levels.lean`).
* `MemBelow'`: membership below the bound, the global being the stage closure typed at the
  weakened function type (true codomain below `b`, `Unit`/`True` above); it asks exactly what
  `memBelow'_mem` and `memBelow'_apply` consume, all of it below the bound only.
* Proved from the data layer: the stage closure is a member of the type the global carries
  (`memBelow'_mem`); applied below the bound it is the function's result at the true codomain
  (`memBelow'_apply`); `MemBelow'` at bound `0` holds of any function (`memBelow'_zero`); and the
  knot's final step, a closure whose function is total and good is a member of its true type
  (`closure_mem_of_total_stmt`); the induction in the run's shape, "stage `b` is good below `b`"
  (`stages_below`), and its conclusion (`knot_member`).

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

/-- **What membership consumes of a function type**, at the argument tuples `P` admits: at sort `0`
a borrow-free codomain that is a proposition; at a data sort `1 ≤ l ≤ 3`, a codomain that fits the
level. -/
def PiFits (R : DataRead) : Nat → List PiDom → PiCod → (List Sem → Prop) → Prop
  | 0, ds, out, P => out.isRef = false ∧ ∀ args, DomMembers R ds args → P args → ∃ Q, out.cod args = TyM.prop Q
  | n + 1, ds, out, P => n + 1 ≤ 3 ∧ ∀ args, DomMembers R ds args → P args → LevelFit (n + 1) (out.cod args)

/-- **What a call consumes of a function type** beyond membership, at the argument tuples `P`
admits: a canonical codomain, and domains that fit the level. -/
def PiCallable (R : DataRead) (l : Nat) (ds : List PiDom) (out : PiCod) (P : List Sem → Prop) : Prop :=
  ∀ args, DomMembers R ds args → P args →
    (out.cod args).Canon ∧ ∀ (i : Nat) (d : PiDom), ds[i]? = some d → LevelFit l (d.dom (args.take i))

/-- **Membership below a bound, on the weakened stage closure**: the global is the stage closure of
a function good (`OutGood'`) at member arguments whose decreasing component has rank below `b`,
typed at the weakened function type; below the bound, the function type meets what membership and
(at a data sort) a call consume. -/
def MemBelow' (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) : Prop :=
  ∃ (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod) (fn : List Sem → Option BodyOut),
    PiFits K.dm.read l ds out (decRank K g · < b) ∧
    (1 ≤ l → PiCallable K.dm.read l ds out (decRank K g · < b)) ∧
    G.1 = closureAt K.dm.read l φ ds (weakCod l (decRank K g) b out) (stageFn l ds (decRank K g) b fn) ∧
    G.2.m = piTyAt K.dm.read l ds (weakCod l (decRank K g) b out) ∧
    ∀ args, DomMembers K.dm.read ds args → decRank K g args < b →
      ∃ o, fn args = some o ∧ OutGood' K.dm.read ds out args o

/-- **The stage closure is a member of the type the global carries** (the weakened function type):
an honest element, so `MemBelow'` is consistent with membership. -/
theorem memBelow'_mem (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow' K G g b) :
    G.1 ∈ₛ[K.dm.read] G.2.m := by
  obtain ⟨l, φ, ds, out, fn, hfit, -, h1, h2, hgood⟩ := h
  rw [h1, h2]
  cases l with
  | zero =>
    obtain ⟨hdata, hprop⟩ := hfit
    exact stage_mem_prop _ φ ds out _ b fn hdata (fun args hm hlt => hprop args hm hlt)
      (fun args hm hlt => by
        obtain ⟨o, hg, ⟨⟨hres, -⟩, -⟩⟩ := hgood args hm hlt
        exact ⟨o, hg, hres⟩)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    cases hr : out.isRef with
    | false =>
      exact stage_mem _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr (fun args hm hlt => hall args hm hlt)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hlen⟩)
    | true =>
      exact stage_mem_ref _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr (fun args hm hlt => hall args hm hlt)
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hret hr, hlen⟩)

/-- **`MemBelow'` at bound `0` holds of any function** at a sort `l ≤ 3` (borrow-free at sort `0`):
nothing is asked below `0` (the induction's base; the stage-`0` closure is `()`/`True`-valued
everywhere). -/
theorem memBelow'_zero (K : RunCtx) (g : GDef) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (fn : List Sem → Option BodyOut) (hl : l ≤ 3) (h0 : l = 0 → out.isRef = false) :
    MemBelow' K (closureAt K.dm.read l φ ds (weakCod l (decRank K g) 0 out) (stageFn l ds (decRank K g) 0 fn),
      .plain (piTyAt K.dm.read l ds (weakCod l (decRank K g) 0 out))) g 0 := by
  refine ⟨l, φ, ds, out, fn, ?_, fun _ _ _ h => absurd h (Nat.not_lt_zero _), rfl, rfl,
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  cases l with
  | zero => exact ⟨h0 rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n => exact ⟨hl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **The closure lemma's application half, read through `MemBelow'`** (the form of
`closure_apply` that holds): at a data sort, the global called at member arguments whose decreasing
component has rank below the bound gives the function's result there, typed at the TRUE codomain
(under a fresh label at a returned borrow), and that result is good. -/
theorem memBelow'_apply (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow' K G g b) :
    ∃ (l : Nat) (ds : List PiDom) (out : PiCod) (fn : List Sem → Option BodyOut),
      (∀ args, DomMembers K.dm.read ds args → decRank K g args < b →
        ∃ o, fn args = some o ∧ OutGood' K.dm.read ds out args o) ∧
      (1 ≤ l → ∀ (args : List Res) (s : SState), DomMembers K.dm.read ds (args.map (·.1)) →
        decRank K g (args.map (·.1)) < b →
        ∃ o, fn (args.map (·.1)) = some o ∧ OutGood' K.dm.read ds out (args.map (·.1)) o ∧
          ∃ (lab : Option Nat) (s' : SState),
            callOf K.dm.read G args s = some ((o.result, ⟨out.cod (args.map (·.1)), lab⟩), s') ∧
            (out.isRef = false → lab = none)) := by
  obtain ⟨l, φ, ds, out, fn, hfit, hcall, h1, h2, hgood⟩ := h
  refine ⟨l, ds, out, fn, hgood, fun hl1 args s hm hlt => ?_⟩
  have hc : callOf K.dm.read G args s = callOf K.dm.read (G.1, .plain G.2.m) args s := rfl
  rw [hc, h1, h2]
  obtain ⟨o, hg, hgd⟩ := hgood _ hm hlt
  refine ⟨o, hg, hgd, ?_⟩
  obtain ⟨hcanon, hdom⟩ := hcall hl1 _ hm hlt
  cases l with
  | zero => exact absurd hl1 (by omega)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    cases hr : out.isRef with
    | false =>
      obtain ⟨s', hs'⟩ := stage_apply _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr hall
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hlen⟩) args s o hm hdom hlt hcanon hg
      exact ⟨none, s', hs', fun _ => rfl⟩
    | true =>
      obtain ⟨k, s', hs'⟩ := stage_apply_ref _ (n + 1) φ ds out _ b fn ⟨by omega, hle⟩ hr hall
        (fun args hm hlt => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := hgood args hm hlt
          exact ⟨o, hg, hgd, hret hr, hlen⟩) args s o hm hdom hlt hcanon hg
      exact ⟨some k, s', hs', fun h => by cases h⟩

/-- **The closure lemma's membership half, in the form that holds** (the knot's last step,
`Assembly.step_member_fix`): a closure whose function is defined and good (`OutGood'`) at every
member argument is a member of its TRUE function type, when the type meets what membership
consumes. -/
theorem closure_mem_of_total_stmt (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) (hfit : PiFits R l ds out (fun _ => True))
    (htot : ∀ args, DomMembers R ds args → ∃ o, g args = some o ∧ OutGood' R ds out args o) :
    closureAt R l φ ds out g ∈ₛ[R] piTyAt R l ds out := by
  cases l with
  | zero =>
    obtain ⟨hdata, hprop⟩ := hfit
    exact closure_mem_prop' R φ ds out g hdata (fun args hm => hprop args hm trivial) (fun args hm => by
      obtain ⟨o, hg, ⟨⟨hres, -⟩, -⟩⟩ := htot args hm
      exact ⟨o, hg, hres⟩)
  | succ n =>
    obtain ⟨hle, hall⟩ := hfit
    cases hr : out.isRef with
    | false =>
      exact closure_mem_of_total' R (n + 1) φ ds out g ⟨by omega, hle⟩ hr (fun args hm => hall args hm trivial)
        (fun args hm => by
          obtain ⟨o, hg, hgd, -, hlen⟩ := htot args hm
          exact ⟨o, hg, hgd, hlen⟩)
    | true =>
      exact closure_mem_of_total_ref' R (n + 1) φ ds out g ⟨by omega, hle⟩ hr (fun args hm => hall args hm trivial)
        (fun args hm => by
          obtain ⟨o, hg, hgd, hret, hlen⟩ := htot args hm
          exact ⟨o, hg, hgd, hret hr, hlen⟩)

/-- **The induction on the bound, in the run's shape**: if, from stage `b` good at member arguments
of rank below `b`, stage `b + 1` is good at member arguments of rank below `b + 1`, then the guarded
fixpoint (`stage (rank a + 1) a`) is good at every member argument. With the run's stages built on
the weakened closure, the step's hypothesis is `MemBelow'` at `b` for `fn := stage b`: no
stage-stability lemma is needed. -/
theorem stages_below {A O : Type _} (stage : Nat → A → Option O) (rank : A → Nat) (mem : A → Prop)
    (good : A → O → Prop)
    (hstep : ∀ b, (∀ a, mem a → rank a < b → ∃ o, stage b a = some o ∧ good a o) →
      ∀ a, mem a → rank a < b + 1 → ∃ o, stage (b + 1) a = some o ∧ good a o) :
    ∀ a, mem a → ∃ o, stage (rank a + 1) a = some o ∧ good a o := by
  have key : ∀ b a, mem a → rank a < b → ∃ o, stage b a = some o ∧ good a o := by
    intro b
    induction b with
    | zero => intro a _ h; exact absurd h (Nat.not_lt_zero _)
    | succ b ih => exact hstep b ih
  intro a ha
  exact key (rank a + 1) a ha (Nat.lt_succ_self _)

/-- **The knot's conclusion, restated** (what `Assembly.step_member_fix` becomes on `fix_split`
restated to `OutGood'`, `PiFits` and the run's shape of the step): the guarded fixpoint's closure is
a member of its true function type. -/
theorem knot_member (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (stage : Nat → List Sem → Option BodyOut) (rank : List Sem → Nat) (hfit : PiFits R l ds out (fun _ => True))
    (hstep : ∀ b, (∀ a, DomMembers R ds a → rank a < b → ∃ o, stage b a = some o ∧ OutGood' R ds out a o) →
      ∀ a, DomMembers R ds a → rank a < b + 1 → ∃ o, stage (b + 1) a = some o ∧ OutGood' R ds out a o) :
    closureAt R l φ ds out (fun args => stage (rank args + 1) args) ∈ₛ[R] piTyAt R l ds out :=
  closure_mem_of_total_stmt R l φ ds out _ hfit
    (fun args ha => stages_below stage rank (DomMembers R ds) (OutGood' R ds out) hstep args ha)

end Ochr.Meaning.Steps
