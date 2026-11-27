import Ochr.Meaning.Steps.MasterCall

/-!
# The frame property for a body that reads its own binding, and the fixpoint clause it needs (lead30; docs/31 D202)

The lead's Task 1, group 2: a callee's body that calls itself (`R(m)` is `.call (.place self) …`). `RunFrameS`
(`FrameFrag`) compares the run in place, where `self` means the callee's whole function `G` (the context's global,
`GlobalsOk.fn`: the closure of `fixG`, at its declared type), with the run in the closure `callOf` applies, where `self`
is the stage below (`fixStage`, at the WEAKENED type); it relates the two `self`s by `SelfRel` (each a member of its own
type), which is why it excludes bodies that read `self`. lead29's plan was to strengthen `SelfRel` with agreement below
the closure's stage and to add a hypothesis that every recursive call decreases.

**The route taken here instead**: compare the run in place with the closure's body run whose `self` IS `G`, at its
TRUE type (`fixBodyAt` at `piT` and `closureAt … out G`). Then the two `self` bindings are EQUAL (the same meaning, the
same stored type `.plain piT`, the same reading `.pi cd`: `CallRef.callFrame` binds `fres = K.C.global g` exactly so),
the relation is `FrameRel` itself, with no exemption and no "self not free" hypothesis (`RunFrame`), and a recursive
call in the body is an ordinary `.call` on related states (the head read in place, the same `G` on both sides). What
links that run to what `callOf` applies (`G` at the arguments, i.e. the stage `rank + 1`) is a fact about the global's
meaning alone, the fixpoint equation of its guarded recursion (`FixEqG`): one unfolding with itself as `self` is itself.
It is a clause of the context, like `RetKindG`, for every global but the one being checked (under ruling (C), D200, a
call of the function being checked never runs its body).

**Where `FixEqG` is established** (not built): when the global `g` is accepted, at the knot (`step_member_fix`), by
induction on the rank of the decreasing argument. `G(a)` is stage `rank a + 1` at `a`: the body run with `self` the
stage-`rank a` closure at the weakened type; `fixBodyAt piT G a` is the body run with `self = G`. The two runs differ
only at `self`, whose callOf-results agree at every argument of rank `< rank a` (the induction hypothesis: `G(c)` is
stage `rank c + 1` at `c`, and stage `k` at `c` is stage `rank c + 1` there for every `k > rank c`, the stabilisation,
by the same induction). So they agree if every recursive call the body makes at `a` is at rank `< rank a`: that is
[Rec] at each typed call site of `g`'s generic check, carried to the reference's run of the body by the simulation of
that check (the master induction at `K.cur = (g, b)`, `RecRankG` at typed sites; under (C) each such call is closed off,
and the sealed call means the context's stage-`b` closure applied, D134). A non-recursive `g` (`dec = none`, rank `0`,
stage 1, `self` the stage-0 closure, never read: D31) satisfies it by `RunFrameS` between the two closure states (the
same frames, `self` exempt, both members of their types).

**Attacked, by reading** (docs/31 D202): `R (n : Nat) : Nat by n := match n { Z => Z, S m => R(m) }`: at `a + 1` both
sides run the arm `S` and apply `self` at `a` (`ColumnR.runR`, parametric in `self`): `callOf G [a] = G(a)`, stage
`a + 1` at `a`; and `callOf` of the stage-`a+1` closure at the weakened type at `a`, `a < a + 1`, so stage `a + 1` at
`a` (`stageFn`): the same, with no stabilisation needed. `A (m : Nat) (n : Nat) : Nat by n := match n { Z => m, S k =>
A(S(m), k) }`: the rank reads `n` only (`fixRank (some 1)`); at `(m, k + 1)` both apply `self` at `(S(m), k)`, rank `k`,
the same way. A call two below (`match n { Z => Z, S k => match k { Z => Z, S j => F(j) } }`) needs the stabilisation
(stage `j + 2` at `j` is stage `j + 1` there), which the induction gives. A call at rank `≥ rank a` would make the two
sides differ (the weakened stage gives the fill, `G` the real value, or fails where `G` fails); [Rec] rejects every
such call at a typed site, the erased ones included (types are typed, so [Rec] runs there; a proof call is `⋆` in the
reference and never applied).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

section GlobalFix
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A global's forming state: `meanV` reads `.clo [] t []` by the `.fix` clause from it (`GlobalsOk.fn`). -/
def formG : SState := stateOf 0 []

/-- The closure's binders, body hint and codomain reading at a global's code (`run_fix_def`'s `fb`, at `formG`). -/
noncomputable def fbG (ds : List Term) (c : Term) : List PBind × (List Sem → TyS) × DeclInfo :=
  (bindsOf K ρ φ formG ds, fixCod K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c,
    K.D.typeDecl (K.D.teleDecls (scopeOf formG) ds) c)

/-- Its domains and codomain. -/
noncomputable def psG (ds : List Term) : List PiDom := runDoms K ρ φ formG ds
noncomputable def outG (ds : List Term) (c : Term) : PiCod :=
  codOf K ρ φ formG (bindsOf K ρ φ formG ds) (ds.map Term.isRefTy) c

/-- The declared sort, the function type, the closure's function (`fixG`, from the counter `0`) and the global's meaning
(its closure), all at `formG`. -/
noncomputable def lG (hs : List Hint) (ds : List Term) (c : Term) : Nat := K.D.piSort (scopeOf formG) (.pi hs ds c)
noncomputable def piTG (hs : List Hint) (ds : List Term) (c : Term) : TyM :=
  piTyAt K.dm.read (lG K hs ds c) (psG K ρ φ ds) (outG K ρ φ ds c)
noncomputable def GG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : List Sem → Option BodyOut :=
  fixG K ρ φ (fbG K ρ φ ds c) (lG K hs ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 dec body
noncomputable def selfG (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term) : Sem :=
  closureAt K.dm.read (lG K hs ds c) φ (psG K ρ φ ds) (outG K ρ φ ds c) (GG K ρ φ hs ds c dec body)

end GlobalFix

/-- **The frame property at EQUAL selves** (docs/31 D202): `RunFrameS` over `FrameRel` itself (the function's own
binding the same on both sides, as everywhere else in the frame), so with no "the body does not read `self`"
hypothesis: a recursive call in the body is a `.call` on related states. Both states good (D201), the locality clauses
(D129), a cell for every parameter label (D203). OPEN. The run in place is the checker's (`CallRef.callFrame`, `self` the global `G` at its declared type); the
closure's is `fixBodyAt` with `self = G` at the true type, linked to `callOf` by `FixEqG`. -/
def RunFrame : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat)
    (tl : Bool) (hint : TyS) (t : Term) (s s' : SState),
    Strict.FundCtx K → FrameStart s₀ ks → t.valsOk (Strict.ValsP K ρ φ) → (t.idFree = true ∨ ks = []) →
    FrameRel σ s₀ ks s s' →
    (∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) →
    (∀ p, p.frameOf = 1 → Ochr.Meaning.FT (fun l => s'.Live l ∧ σ l ∉ ks) (s'.valAt p)) →
    Strict.SGood K.dm K.Γ φ s → Strict.SGood K.dm K.Γ φ s' →
    ks.length ≤ (s'.env.headD {}).binds.length →
    FrameAgree σ s₀ ks (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s')

/-- **The fixpoint equation of an accepted global** (MODEL; docs/31 D202, restated by D232). For every global `n` of the
checker's state other than the one being checked, with a `fix` code, at every assignment and future, at member arguments:
the global's function (`GG`, the `.fix` clause's `fixG` at the global's forming state `formG`: stage `rank + 1`) equals one
run of the body with `self` the global's own closure at its true function type. Stated at `formG` only (D232: a global is
formed there and nowhere else; at another state the body's variables are not its own, and the right side's closure is `err`
wherever the function is not good everywhere). Since D232 a THEOREM, not an assumed clause: `FixEqDesc.fixEqG_of`, from
the descent clause `RecDescG` and the knot's goodness `FnGoodG`. -/
def FixEqG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future) (args : List Sem), DomMembers K.dm.read (psG K ρ φ ds) args →
      GG K ρ φ hs ds c dec body args =
        fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c) (piTG K ρ φ hs ds c) 0 body
          (selfG K ρ φ hs ds c dec body) args

/-- **An accepted global's function is good, its type fits its sort** (MODEL; a clause of the context, docs/31 D232): at
every assignment and future, the function type of the global's code at its forming state fits its declared sort
(`PiFits`), and the global's function is defined and good (`OutGood'`) at every member argument. Established at the
global's acceptance by the knot (`Consistency.fix_split`'s three parts and `FixKnot.stages_below`, exactly what
`step_member_fix` assembles membership from: membership is `closure_mem_of_total` of this), BEFORE the fixpoint equation,
which uses it (D232: the equation's right side binds the global's closure, `err` unless its function is good everywhere). -/
def FnGoodG (K : RunCtx) (st : MState) : Prop :=
  ∀ (n : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat) (body : Term),
    st.globals.find? (·.name == n) = some gd → K.cur.map (·.1) ≠ some n →
    gd.fn? = some (.fix self hs ds c dec body) →
    ∀ (ρ : Assignment) (φ : Future),
      PiFits K.dm.read (lG K hs ds c) (psG K ρ φ ds) (outG K ρ φ ds c) (fun _ => True) ∧
      ∀ a, DomMembers K.dm.read (psG K ρ φ ds) a →
        ∃ o, GG K ρ φ hs ds c dec body a = some o ∧ OutGood' K.dm.read (psG K ρ φ ds) (outG K ρ φ ds c) a o

end Ochr.Meaning.Steps.Form
