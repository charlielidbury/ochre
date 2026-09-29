import Ochr.Test
open Ochr Ochr.Test

/-! A closed proof of `False` accepted by the default rules (ochr-core 0127f58b).
Found by the fuzzer (seed 1, case 1424, truth oracle), minimised by hand.

`sealedType` (Machine.lean) sets `recCands := []` inside `onCopy`; `restoreKeep` then keeps
`cur.recCands.drop (cur.recCands.length - saved.recCands.length)` = `[].drop 0` = `[]`,
while `recStack` is restored. `recCheck` zips `recStack` with `recCands`, so from then on
no recursive call is checked. `sealedType` runs when `valType` meets a sealed program:
here `fieldTypes` of `And` at the parameter `⌈Le(σ, 1)⌉` (the match on `h`). -/
ochr RecWipe {
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S a' => match b { Z => False, S b' => Le(a', b') } }
  def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }
  def Boom : False := Lie(0, ⟨refl, refl⟩)
  -- controls: without the sealed conjunct, or without the match, [Rec] rejects
  reject def Lie2 (n : Nat) (h : ⊤ ∧ ⊤) : False by n := match h { Intro(a, b) => Lie2(n, h) }
  reject def Lie3 (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := Lie3(n, h)
}
#eval IO.println (run "RecWipe" RecWipe).show

-- the mechanism in isolation: recStack survives sealedType, recCands does not
#eval show IO Unit from do
  let st : MState := { recStack := [⟨.gfn "f", #[some 0]⟩], recCands := [[0]], nextAbs := 1, absTy := #[.tNat] }
  let act : M (Nat × Nat) := do
    discard (tryCatch (discard (sealedType (.val (.abs 0)))) (fun _ => pure ()))
    let s ← get
    pure (s.recStack.length, s.recCands.length)
  IO.println s!"(recStack, recCands) lengths after sealedType: {repr (runM act st |>.toOption)}"
