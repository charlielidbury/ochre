import Ochr.Meaning.Steps.Statements

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

namespace Ochr.Meaning.Regress.DefKnot
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **`CtxOk` at a state holding a function's global already makes it a member of its type.** -/
theorem ctxOk_contains_fix_member (K : RunCtx) (ρ : Assignment) (φ : Future) (st : MState) (hctx : CtxOk K ρ st)
    (n : String) (g : GDef) (t : Term) (hg : st.globals.find? (·.name == n) = some g) (hfn : g.fn? = some t) :
    meanV K ρ φ (.plain .err) (.clo [] t []) ∈ₛ[K.dm.read] (meanV K ρ noFuture (.plain .err) g.ty).asTy := by
  have h1 := (hctx.globals.fn n g t hg hfn ρ φ).1
  have h2 := hctx.globals.mem n g hg
  have h3 := hctx.globals.ty n g hg ρ
  rw [h1, h3] at h2
  exact h2

end Ochr.Meaning.Regress.DefKnot
