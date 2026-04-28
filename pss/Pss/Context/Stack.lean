import Pss.Syntax.LocallyNameless
import Pss.Context.Logical

/-! # `Pss.Context.Stack` — continuation stacks and extended contexts

Stacks of operands as in MPSS Fig. 1: `s ::= nil | α :: s`. Extended contexts
`Γ ; s` pair a logical context with a stack. The PSS-side of the formalization
uses an implicit empty stack throughout.
-/

namespace Pss

/-- A continuation stack. **List head = top of stack** (the operand that would
be consumed next by an `Me-FOp` or `Ms-FOp` rule). -/
abbrev Stack := List Term

/-- Extended context `Γ ; s` (MPSS). -/
abbrev ExtCtx := Ctx × Stack

/-- The logical-context component of an extended context. -/
def ExtCtx.ctx (E : ExtCtx) : Ctx := E.fst

/-- The stack component of an extended context. -/
def ExtCtx.stack (E : ExtCtx) : Stack := E.snd

@[simp] lemma ExtCtx.ctx_mk (Γ : Ctx) (s : Stack) :
    ExtCtx.ctx (Γ, s) = Γ := rfl

@[simp] lemma ExtCtx.stack_mk (Γ : Ctx) (s : Stack) :
    ExtCtx.stack (Γ, s) = s := rfl

/-- Push an operand onto the stack of an extended context. -/
def ExtCtx.extend (E : ExtCtx) (α : Term) : ExtCtx := (E.ctx, α :: E.stack)

@[simp] lemma ExtCtx.extend_mk (Γ : Ctx) (s : Stack) (α : Term) :
    ExtCtx.extend (Γ, s) α = (Γ, α :: s) := rfl

end Pss
