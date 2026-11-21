import Ochr.Meaning.Steps.ColumnP

/-!
# The first functions with a borrow parameter, columns `W` and `K`: their states and the checker facts they assume (lead18, 2026-11-21; docs/31 D138)

`def W (r : &Nat) : Nat := clone(*r)` reads through its borrow parameter; `def K (r : &Nat) : &Nat := r` returns it.
In core terms `W`'s body is `clone(*#0)` (`bodyW`) and `K`'s is `#0` (`bodyK`), each with the domain `&Nat`. The
smaller `W (r : &Nat) : Nat := *r` is REJECTED by the checker ("[D53] a borrow ends while its content is partly moved
out": the read of `*r` moves the content out, and the parameter's borrow ends at the return over it), so `clone` is
the smallest read through the parameter the checker accepts.

The body's start state (pinned in `Steps/BorrowParGuards.lean`, against the state the checker records on entry to the
body, docs/31 D126 and `Steps/FrameGuards.lean`): frame 0 holds the parameter's CELL `r° ↦ loan₀` at the content type
`Nat`; frame 1 holds the function's binding of itself (marked) and the parameter `r ↦ borrow₀ σ0` at `&Nat`, read
`.ref .other`; the label counter is at 1, the unknowns `[σ0 : Nat]`.

What each body does (pinned): `W`'s `clone(*r)` reads the content `σ0` in place: the value `σ0 : Nat`, the state as it
was (the borrow still held by `r`); `K`'s `r` moves the borrow out of `r`: the value `borrow₀ σ0 : &Nat` (labelled `0`),
`r ↦ ⊥`, the cell untouched.
-/

namespace Ochr.Meaning.Steps.Form.ColumnW

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form

/-- `W`'s body: `clone(*#0)`. -/
def bodyW : Term := .prim "clone" [.place (.deref (.var 0))]

/-- `K`'s body: `#0`. -/
def bodyK : Term := .place (.var 0)

def fixW : Term := .fix ⟨"W"⟩ [⟨"r"⟩] [.ref .nat] .nat none bodyW
def fixK : Term := .fix ⟨"K"⟩ [⟨"r"⟩] [.ref .nat] (.ref .nat) none bodyK

def defW : Def := { name := "W", hs := [⟨"r"⟩], doms := [.ref .nat], cod := .nat, body := bodyW }
def defK : Def := { name := "K", hs := [⟨"r"⟩], doms := [.ref .nat], cod := .ref .nat, body := bodyK }

/-- `Π(r : &Nat). Nat` and `Π(r : &Nat). &Nat`, as the checker's values. -/
def piW : Value := .tPi [] (.pi [⟨"r"⟩] [.ref .nat] .nat) []
def piK : Value := .tPi [] (.pi [⟨"r"⟩] [.ref .nat] (.ref .nat)) []

def gW : GDef := { name := "W", ty := piW, fn? := some fixW, val := .gfn "W" }
def gK : GDef := { name := "K", ty := piK, fn? := some fixK, val := .gfn "K" }

/-- The parameter's cell in frame 0: `r° ↦ loan₀` at the content type. -/
def cellR : Binding := { hint := ⟨"r°"⟩, ty := some .tNat, val := .loan 0, decl := .other }

/-- The functions' bindings of themselves, marked; `K`'s codomain is read `.ref .other`. -/
def selfW : Binding := { hint := ⟨"W"⟩, ty := some piW, val := .gfn "W", decl := .pi .other, recUid := some 0 }
def selfK : Binding := { hint := ⟨"K"⟩, ty := some piK, val := .gfn "K", decl := .pi (.ref .other), recUid := some 0 }

/-- The parameter holding `v`, at `&Nat`, read `.ref .other`. -/
def rB (v : Value) : Binding := { hint := ⟨"r"⟩, ty := some (.tRef .tNat), val := v, decl := .ref .other }

/-- The kernel of `W`'s body's start state (and of its end: `clone` reads in place). -/
def stW : MState :=
  { env := #[{ binds := #[cellR] }, { binds := #[selfW, rB (.borrow 0 (.abs 0))] }], globals := [gW], nextLoan := 1,
    nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some .tNat }

/-- The kernel of `K`'s body's start state. -/
def stK : MState :=
  { env := #[{ binds := #[cellR] }, { binds := #[selfK, rB (.borrow 0 (.abs 0))] }], globals := [gK], nextLoan := 1,
    nextAbs := 1, absTy := #[.tNat], absDecl := #[.other], goal := some (.tRef .tNat) }

/-- The kernel after `K`'s body: the borrow moved out of `r` (into the value in flight). -/
def endK : MState := { stK with env := #[{ binds := #[cellR] }, { binds := #[selfK, rB .bot] }] }

/-- `W`'s value: the content `σ0`. -/
def vW : Value := .abs 0

/-- `K`'s value: the parameter's borrow, `borrow₀ σ0`. -/
def vK : Value := .borrow 0 (.abs 0)

/-! ## The facts about the checker -/

/-- **`W`'s body** (a fact about the checker alone; the machine lane's to prove): every successful typed `eval` of
`clone(*r)` from a state with `stW`'s kernel, in the plain mode, with no handed-down reading, returns the content `σ0`
at `Nat` and ends with `stW`'s kernel (the read is in place: the borrow stays held by `r`). Guarded in
`Steps/BorrowParGuards.lean`. -/
def BodyWInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Kern stW st → Mode st → st.tailDecl = none →
    Runs (Ochr.eval n true bodyW hint) st bh (v, T?) st' →
    v = vW ∧ T? = some .tNat ∧ Kern stW st'

/-- **`K`'s body** (a fact about the checker alone): every successful typed `eval` of `r` from a state with `stK`'s
kernel, in the plain mode, with no handed-down reading, returns the borrow `borrow₀ σ0` at `&Nat` and ends with
`endK`'s kernel (`r ↦ ⊥`: the read of a borrow variable moves it). Guarded in `Steps/BorrowParGuards.lean`. -/
def BodyKInv : Prop :=
  ∀ (n : Nat) (hint : Option Value) (st st' : MState) (bh : Nat) (v : Value) (T? : Option Value),
    Kern stK st → Mode st → st.tailDecl = none →
    Runs (Ochr.eval n true bodyK hint) st bh (v, T?) st' →
    v = vK ∧ T? = some (.tRef .tNat) ∧ Kern endK st'

end Ochr.Meaning.Steps.Form.ColumnW
