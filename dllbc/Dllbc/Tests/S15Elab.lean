import Dllbc.Boundary
import Dllbc.Macro
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.Migrate

/-!
# §15 test suite — the pure surface authoring layer, and `le_trans`

The M11 wall was mis-indexed de Bruijn failing silently. This milestone's claim:
names + explicit motives collapse it without a unifier. The evidence is here —
`le_trans`, the lemma I abandoned as a raw term, authored in `pure{ }` and
checked; plus the J warm-ups and the round-trip that a hand-built term and its
surface elaboration are convertible.

Two `hasType` additions served it (both ordinary type theory, not a unifier):
application-spine synthesis for a bound function variable (`ih b c hab hbc`), and
over-application of an eliminator (`natRec … n` returning a function, then given
its argument).
-/

open Dllbc

namespace Dllbc.Tests.S15Elab

/-- Check a pure `Term` against a pure type `Term` (deep fuel — lemmas nest). -/
def chk (tm ty : Term) : Bool :=
  match (do let v ← readC 2000 tm; let t ← readC 2000 ty; hasType 2000 v t).run (seedPure [] []) with
  | .ok r _ => r
  | .error _ _ => false

/-! ## Elaboration round-trip: surface `le_refl` = the hand-built kernel term -/

-- The surface `le_refl` (StdLemmas) elaborates to a `Term` convertible with the
-- M11 hand-built `Std.le_reflT`.
example : expectConv [] [] Dllbc.StdLemmas.le_refl Std.le_reflT = true := by native_decide

/-! ## The lemmas check at their stated types -/

example : chk Dllbc.StdLemmas.le_refl Dllbc.StdLemmas.le_refl_ty = true := by native_decide
-- THE ACCEPTANCE TEST — `le_trans` authored in the surface, checked.
example : chk Dllbc.StdLemmas.le_trans Dllbc.StdLemmas.le_trans_ty = true := by native_decide
example : chk Dllbc.StdLemmas.id_trans Dllbc.StdLemmas.id_trans_ty = true := by native_decide
example : chk Dllbc.StdLemmas.id_congr Dllbc.StdLemmas.id_congr_ty = true := by native_decide

/-! ## `le_trans` APPLIED in a checked function — closing the loop with §12

    A body that ⇒-lifts `le_trans Nat a b c p q` (the pure lift, §11) and returns
    it at the dependent type `Le a c` (instantiated at the actuals, §12). -/

def natT : Term := .const "Nat"
def leT (a b : Term) : Term := Std.LeT a b
def av : Var := ⟨0, "a"⟩
def bv : Var := ⟨1, "b"⟩
def cv : Var := ⟨2, "c"⟩
-- body: `le_trans a b c p q` (Le is monomorphic at Nat — no type argument)
def useTransBody : Term :=
  .app (.app (.app (.app (.app Dllbc.StdLemmas.le_trans (.var av)) (.var bv)) (.var cv))
    (.var ⟨3, "p"⟩)) (.var ⟨4, "q"⟩)
def useTrans : FnDef :=
  { name := "useTrans", retType := leT (.var av) (.var cv),
    telescope := [("a", natT), ("b", natT), ("c", natT),
                  ("p", leT (.var av) (.var bv)), ("q", leT (.var bv) (.var cv))],
    body := useTransBody }
example : Migrate.progOkOf useTrans = true := by native_decide

/-! ## Negative tests -/

-- Wrong motive: `elim n return (λ m. Le Z m) { … }` gives a proof of `Le Z n`,
-- but the function claims `Le n n`. Elaboration SUCCEEDS (the term is
-- well-formed); the audit rejects it — the motive is written on the `return`
-- clause and thus visible, so the failure is comprehensible. The surfaced error
-- is: "audit: result (…) does not have return type (…)".
def LeFn : Term := Std.LeFnT
def badReflClosed : Term := pure{
  λ (n : Nat). elim n return (λ (m : Nat). LeFn Z m) { Z => unit, S (k) ih => ih } }
-- SUBJECT: a deliberately-lying FnDef — retType claims `Le n n` while the (surface)
-- body proves `Le Z n`. Hand-built raw so the lie is explicit; converting it to
-- decl{} would obscure exactly what the negative test demonstrates.
def badRefl : FnDef :=
  { name := "badRefl", retType := Std.LeT (.var ⟨0, "n"⟩) (.var ⟨0, "n"⟩),
    telescope := [("n", natT)], body := (.app badReflClosed (.var ⟨0, "n"⟩)) }
example : Migrate.progRejectsOf badRefl "does not have return type" = true := by native_decide

-- Unresolved name: `pure{ Le nope nope }` where `nope` is unbound is a Lean
-- elaboration error at macro time (the resolve-or-error discipline), not a
-- silent `pvar`. Demonstrated by `#guard_msgs` would require the exact message;
-- here we simply note it cannot be written — an unbound lowercase name in a
-- `pure{ }` block fails to compile, exactly as in `dllbc{ }`.

/-! ## The measure (§15's report card)

    `le_trans` in the surface: 14 lines (`StdLemmas.le_trans`), every binder named,
    every motive written once and visible on its `return` clause. The M11 raw-term
    attempt was ABANDONED at the wall: a three-level nested dependent induction
    over ~15 distinct de Bruijn binder contexts, each mis-index failing silently
    with only a `false` from `native_decide` and no locus. The surface term
    type-checked on the SECOND attempt (the first surfaced two real bugs in
    `hasType` — sym-application and eliminator over-application — not de Bruijn
    slips, because there are no indices to slip). Names + explicit motives
    collapsed the wall; no unifier, no motive inference, no case trees. -/

end Dllbc.Tests.S15Elab
