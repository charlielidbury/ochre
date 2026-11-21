import Ochr.Meaning.Steps.FragTop
import Ochr.Meaning.Strict.WitnessFix

/-!
# The first columns with a parameter: the facts they assume (lead13)

`def I (n : Nat) : Nat := S(n)`. The checker checks a function's body once (`Machine.checkFix`), typed,
in tail position (`checkTail`), from a state with two frames: frame `0` empty (it holds the cells of
borrow parameters, here none), frame `1` holding `I ↦ .gfn "I"` at its Π-type (read `.pi .other`) and
the parameter `n ↦ σ₀`, an UNKNOWN of type `Nat` (`absAt`), read `.other`; `Δ = [Nat]`, the goal `Nat`.
`S(n)` is no form `checkTail` handles, so it runs `eval true (S n) (some Nat)` and hands the result
to the return check. The run reads `n` by MOVING it (`n ↦ ⊥` after; the copy decision at `.other` is
false), and returns `S(σ₀)` at `Nat` (`Steps/ParGuards.lean`).

New relative to the fragment: values holding an unknown. `Value.NumA` is a numeral over an unknown or
over `Z`; the facts below are the fragment's `Num` facts with `NumA` (and the unknown's type `Nat`).

The reference: the `.fix` clause makes a closure whose body runs, at each argument, in ONE frame
(`RunCongr.fixBodyAt`: `self`, then the parameters, pushed on the closure's creation state), where the
checker's body state has two. `FrameDrop0` relates the two (the model's frame property,
`FrameProp.run_frame`, at no parameter label and an empty caller frame).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- A numeral over `Z` or over an unknown: `Sᵏ(Z)`, `Sᵏ(σ)`. -/
inductive _root_.Ochr.Value.NumA : Value → Prop
  | zero : Value.NumA .zero
  | abs (σ : Nat) : Value.NumA (.abs σ)
  | succ {v : Value} : Value.NumA v → Value.NumA (.succ v)

theorem _root_.Ochr.Value.Num.numA {v : Value} (h : v.Num) : v.NumA := by
  induction h with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

/-- The unknowns a numeral holds are of type `Nat` in `st`'s Δ. -/
def NumAt (st : MState) (v : Value) : Prop :=
  v.NumA ∧ ∀ σ, v.hasAbs σ = true → st.absTy[σ]? = some .tNat

/-! ## Facts about the checker -/

/-- **`evalCore` of a variable holding a numeral over an unknown** (`VarNumInv` with `NumA` for `Num`;
the parameter's read in `I`'s body): the value is the binding's, at its stored type; quiet; copied or
moved as the aligned copy decision says. -/
def VarNumAInv : Prop :=
  ∀ (n : Nat) (typed : Bool) (i : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value)
    (T? : Option Value) (f j : Nat) (b : Binding) (D : Decisions),
    Mode st → ckVarPos st.env i = some (.bind f j) → st.env[f]?.bind (fun fr : Frame => fr.binds[j]?) = some b →
    b.val.NumA → b.ty.isSome → DecTab D st' →
    Runs (Ochr.evalCore (n + 1) typed (.place (.var i)) hint) st bh (v, T?) st' →
    v = b.val ∧ (∀ T, T? = some T → b.ty = some T) ∧ (typed = true → T?.isSome) ∧ Mode st' ∧
    ∃ st₁, Quiet st st₁ ∧ KeepsInv st st₁ ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = true → Kern st₁ st') ∧
      (D.copy (D.placeDecl (DecideScope.topReadings st) (.var i)) = false →
        Kern { st₁ with env := Env.setAtE st₁.env (.bind f j) .bot } st')

/-- **The state-level lemmas for numerals over unknowns** (`InvPushInert`, `InvPopInert`, `InvSetBot`
with `NumA`; read no run): a numeral whose unknowns are of type `Nat` pushed or popped as the top
temporary; a binding holding one set to `⊥`. -/
structure InvNumA : Prop where
  push : ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (v : Value) (T? : Option Value),
    NumAt st v → Inv D Γ st.norm → Inv D Γ (st.withTempT v T?).norm
  pop : ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (v : Value) (T? : Option Value),
    v.NumA → Inv D Γ (st.withTempT v T?).norm → Inv D Γ st.norm
  setBot : ∀ (D : Decisions) (Γ : List IndDecl) (st : MState) (f j : Nat),
    (valAt st.env (.bind f j)).NumA → Inv D Γ st.norm →
    Inv D Γ { st with env := Env.setAtE st.env (.bind f j) .bot }.norm

/-! ## A fact about the reference run (the model lane's) -/

/-- **The reference run does not see an empty bottom frame** (`FrameProp.run_frame` at no parameter
label, the caller's frames one empty frame; the model lane's): a run from a state whose frames are an
empty frame under `fr`, with no borrow anywhere, succeeds where the run from `fr` alone does, with the
same result, and leaves no live label where the other leaves none. -/
def FrameDrop0 (K : RunCtx) (ρ : Assignment) (φ : Future) : Prop :=
  ∀ (tl : Bool) (hint : TyS) (t : Term) (s : SState) (fr : SFrame) (r : Res) (s' : SState),
    t.valsOk (Strict.ValsP K ρ φ) → Strict.SGood K.dm K.Γ φ s →
    s.env = [{}, fr] → (∀ p, s.shape p = none) →
    runT K ρ φ tl hint t s = some (r, s') → s'.liveLabels = [] →
    ∃ s'', runT K ρ φ tl hint t { env := [fr], shape := fun _ => none, nextLoan := s.nextLoan } = some (r, s'') ∧
      s''.liveLabels = []

end Ochr.Meaning.Steps.Form
