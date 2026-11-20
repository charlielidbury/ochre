import Ochr.Meaning.Steps.Knot
import Ochr.Meaning.ClosureStage

/-!
# The knot of [Def]: the induction on the bound (docs/31 D73, D79; docs/34, the weakened stage closure)

`checkDef` pushes a function's global before it checks the body, so that recursive calls find it;
`CtxOk` then asks of that global only membership below a bound (`RunCtx.cur`, `MemBelow`): it is
the stage closure, typed at the weakened function type (the true codomain at arguments whose
decreasing component has rank below `b`, `Unit` above), of a function good below `b`. The run's
own stages are these closures (`RunCongr.fixStage`: stage `b + 1` binds `self` to stage `b`'s), so
in the induction's step the global is the run's `self`, `MemBelow b` holds with the function the
stage `b`, and no stage-stability lemma is needed: from stage `b` good below `b`, the body's generic
run (the checker accepted it) makes stage `b + 1` good below `b + 1`; so the guarded fixpoint (at
arguments of rank `r`, the stage `r + 1`) is good at every member argument (`stages_below`), and a
closure whose function is total and good is a member of its type (`closure_mem_of_total`).

Here, all proved from the data layer (`Closure.lean`, `ClosureRef.lean`, `ClosureStage.lean`):
* `memBelow_mem`: the global under `MemBelow` is a member of the type it carries;
* `memBelow_zero`: `MemBelow` at bound `0` holds of any function (the induction's base);
* `memBelow_apply`: a call of the global below the bound gives the function's result at the TRUE
  codomain (a fresh label at a returned borrow), and that result is good (`OutGood'`);
* `closure_mem_of_total`, `knot_member`: the knot's conclusion at the true type.
The first-stated `closure_mem_of_total` and `closure_apply` were false (`ClosureCE`) and are
replaced by these. Also here: the rank's strict decrease (`semRank_part`, R2) and [Rec]'s link
(`recDecreases`, a leaf). The spine's leaves and the assembly of `step_member_fix` are in
`Consistency.lean`.
-/

namespace Ochr.Meaning.Steps

open Ochr Ochr.Meaning

/-- **The stage closure is a member of the type the global carries** (the weakened function type):
an honest element, so `MemBelow` is consistent with membership. -/
theorem memBelow_mem (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow K G g b) :
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

/-- **`MemBelow` at bound `0` holds of any function** at a sort `l ≤ 3` (borrow-free at sort `0`):
nothing is asked below `0` (the induction's base; the stage-`0` closure is `()`/`True`-valued
everywhere). -/
theorem memBelow_zero (K : RunCtx) (g : GDef) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (fn : List Sem → Option BodyOut) (hl : l ≤ 3) (h0 : l = 0 → out.isRef = false) :
    MemBelow K (closureAt K.dm.read l φ ds (weakCod l (decRank K g) 0 out) (stageFn l ds (decRank K g) 0 fn),
      .plain (piTyAt K.dm.read l ds (weakCod l (decRank K g) 0 out))) g 0 := by
  refine ⟨l, φ, ds, out, fn, ?_, fun _ _ _ h => absurd h (Nat.not_lt_zero _), rfl, rfl,
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  cases l with
  | zero => exact ⟨h0 rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n => exact ⟨hl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

/-- **The closure lemma's application half, read through `MemBelow`** (the form of
the first-stated `closure_apply` that holds, `ClosureCE`): at a data sort, the global called at member arguments whose decreasing
component has rank below the bound gives the function's result there, typed at the TRUE codomain
(under a fresh label at a returned borrow), and that result is good. -/
theorem memBelow_apply (K : RunCtx) (G : Sem × TyS) (g : GDef) (b : Nat) (h : MemBelow K G g b) :
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
theorem closure_mem_of_total (R : DataRead) (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
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
the weakened closure, the step's hypothesis is `MemBelow` at `b` for `fn := stage b`: no
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
  closure_mem_of_total R l φ ds out _ hfit
    (fun args ha => stages_below stage rank (DomMembers R ds) (OutGood' R ds out) hstep args ha)

/-- A part of a meaning: a field of a constructor value, a number's predecessor, and so on down.
Only a constructor value has fields here: a proof (`⋆`) has none, although the run reads `⋆` off a
field of `⋆` (`Sem.stepField`), so `⋆` would otherwise be a part of itself and (R2) false. [Rec]
never needs one: `strictSubterms` does not descend into `⋆`, and the only constructor values of a
`Prop`-sorted declaration it descends into (refinements of a subsingleton, (I7)) have only proof
fields, none of the decreasing parameter's data type. -/
inductive SemPart (dm : DataModel) (Γ : List IndDecl) : Sem → Sem → Prop
  | field {n : String} {r : Rec} {c i : Nat} {fs : List Sem} {f : Sem} (h : fs[i]? = some f) :
      SemPart dm Γ f (.dat n r c fs)
  | pred (n : Nat) : SemPart dm Γ (.el0 Nat n) (.el0 Nat (n + 1))
  | trans {a b c : Sem} : SemPart dm Γ a b → SemPart dm Γ b c → SemPart dm Γ a c

/-- **(R2) A part has a strictly smaller rank** (from the data layer: `semHeight_field_lt`, through
every declaration and nesting, as a function of the meaning alone; `semRank` is the height). What
`recDecreases_stmt` turns [Rec]'s syntactic check into. -/
theorem semRank_part (dm : DataModel) (Γ : List IndDecl) {a b : Sem} (h : SemPart dm Γ a b) :
    semRank a < semRank b := by
  induction h with
  | field h => exact semHeight_field_lt _ _ _ _ _ (List.mem_of_getElem? h)
  | pred n =>
    show semHeight (.el0 Nat n) < semHeight (.el0 Nat (n + 1))
    simp only [semHeight, Sem.asNat_el0, Option.getD_some]
    omega
  | trans _ _ ih₁ ih₂ => exact Nat.lt_trans ih₁ ih₂

/-! ### The [Rec] link (the spine's; docs/31 D73 item 3) -/

/-- **[Rec], semantically** (leaf): [Rec] (`Machine.recCheck`) accepts a recursive call when the
decreasing argument `u` is a strict subterm of the parameter's entry unknown `σ` as the path
conditions expand it (`expandRefs`). At a good state, under an assignment that meets the path
conditions (`TypedAssignment.refs`) and is typed (so the entry unknown's value is a constructor value
of its type, whose fields its expansion's fields mean), `u`'s meaning is a part of `ρ σ`; with
`semRank_part` its rank is smaller, which is what the induction on the bound needs at a recursive
call. (The lane's answer: this holds only under typed assignments satisfying the records, which
`Good` gives.) -/
theorem recDecreases (K : RunCtx) (ρ : Assignment) (ψ : Future) (st st' : MState) (σ : Nat) (e u : Value) (b : Nat)
    (hT : TyS) (hg : Good K.dm K.M K.Γ ρ st) (hctx : CtxOk K ρ st)
    (he : Runs (Ochr.expandRefs st.refs (.abs σ)) st b e st')
    (hu : u ∈ Ochr.strictSubterms e) :
    SemPart K.dm K.Γ (meanV K ρ ψ hT u) (ρ σ) := by
  sorry

end Ochr.Meaning.Steps
