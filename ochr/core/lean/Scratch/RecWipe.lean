import Ochr.Test
open Ochr Ochr.Test

/-! Fuzzer finding F-v2-1 (notes/fuzzer.md §v2.5): a closed proof of `False` accepted by the
default rules on ochr-core 0127f58b and 96d788a1 (D52). Found by the fuzzer (seed 1, case
1424, truth oracle), minimised by hand.

The mechanism, on those commits: `sealedType` (Machine.lean) set `recCands := []` inside
`onCopy`, and `restoreKeep` kept `cur.recCands.drop (cur.recCands.length - saved.recCands.length)`,
which is `[].drop 0 = []`, while `recStack` was restored; `recCheck` zipped the two, so from
then on no recursive call was checked. `sealedType` ran when `valType` met a sealed program:
here `fieldTypes` of `And` at the parameter `⌈Le(σ, 1)⌉` (the match on `h`).

Fixed by 3ff0e1e2 ([Rec] frames carry their candidates; restores merge by identity): the
checker now rejects `Lie`, so every declaration below is a `reject def`. -/
ochr RecWipe {
  def Le (a : Nat) (b : Nat) : Prop by a := match a { Z => ⊤, S a' => match b { Z => False, S b' => Le(a', b') } }
  reject def Lie (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := match h { Intro(a, b) => Lie(n, h) }
  reject def Boom : False := Lie(0, ⟨refl, refl⟩)
  -- controls, rejected on every commit: without the sealed conjunct, or without the match
  reject def Lie2 (n : Nat) (h : ⊤ ∧ ⊤) : False by n := match h { Intro(a, b) => Lie2(n, h) }
  reject def Lie3 (n : Nat) (h : Le(n, 1) ∧ ⊤) : False by n := Lie3(n, h)
}
#eval IO.println (run "RecWipe" RecWipe).show
