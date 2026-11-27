import Ochr.Meaning.Steps.CallGAttack
import Ochr.Meaning.Steps.UnderCheck

/-!
# The function under check, the closed-off call and the re-run, attacked on the checker (lead31; docs/31 D205, D206)

Main's D135 at the holes of real programs (`Steps/UnderCheck.lean` has the statements). Each hole reports its
environment; the guards read the variable bound to the call's result:
- `RH(m)`, `AH(S(m), k)` (two arguments, recursing on the second while the first grows) and `TH(TT, m)` (whose body,
  matching on its known first argument, would run to `Z` in place) are each closed off at once: a sealed call of the
  global itself;
- `CB`: a closed-off call with a borrow argument fills the lender with `⌈let c = σ; AddM(&c, y); c⌉`; `CT`: a
  closed-off call returning a borrow, written through and ended, leaves `⌈…; *r := 0; c⌉` (the hole filled);
- `CS`: the fill re-runs after a later split (`0` in arm `Z`, `S(⌈…σ'…⌉)` in arm `S`);
- `RB`: a stuck block's sealed program, re-run after a later split, reaches a recursive call of the function under
  check, which closes off (`⌈RB(σ, 0)⌉`), where before D135 it would have run the body untyped;
- `GoH`: a LOCAL recursive function `go` capturing `n`; the split on `n` refines the capture; a closure `h` capturing `go`
  is called in place and calls `go`, which closes off: the sealed head is the closure VALUE with its capture refined to
  `0` (recognised by code), `go`'s own binding is moved into `h`, and `h` holds `go`'s refined closure. The model has no
  counterpart (docs/31 D205). ACCEPTED UNTIL main's D136 (ruled by the lead, 2026-11-27: a local function is not
  recursive, as in Lean's kernel); then `GoH` becomes a `reject def` and its two guards go.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr UnderCheckAtk {
  inductive BB := TT | FF
  def RH (n : Nat) : Nat by n := match n { Z => Z, S m => (let r = RH(m); ?) }
  def AH (m : Nat) (n : Nat) : Nat by n := match n { Z => m, S k => (let r = AH(S(m), k); ?) }
  def TH (p : BB) (n : Nat) : Nat by n := match p { TT => Z, FF => match n { Z => Z, S m => (let r = TH(TT, m); ?) } }
  def AddM (x : &Nat) (y : Nat) : Unit by x := match *x { Z => *x := y, S p => AddM(&p, y) }
  def TailM (x : &Nat) : &Nat by x := match *x { Z => x, S p => TailM(&p) }
  def CB (a : Nat) (y : Nat) : Nat := (let c = a; AddM(&c, y); let r = c; ?)
  def CT (a : Nat) : Nat := (let c = a; let t = TailM(&c); *t := Z; let r = c; ?)
  def CS (a : Nat) : Nat := (let c = clone(a); AddM(&c, Z); match a { Z => (let r = c; ?), S q => (let r = c; ?) })
  def RB (n : Nat) (k : Nat) : Nat by n := match n { Z => Z, S m => (let r = (match k { Z => RB(m, Z), S j => Z }); match k { Z => (let u = r; ?), S j => (let u = r; ?) }) }
  def GoH (n : Nat) (x : Nat) : Nat := (fix go (y : Nat) : Nat by y := match n { Z => match y { Z => Z, S p => (let h = (λ(u : Unit) : Nat => go(clone(p))); let r = h(()); ?) }, S q => Z })(x)
}

namespace Ochr.Meaning.Steps.Form.UnderCheckAtk

open Ochr Ochr.Meaning

/-- Every environment a hole of definition `nm` reports. -/
def holes (nm : String) : List (List (String × Option Value × Value)) :=
  let r := Ochr.Test.runWith (some Prelude) "UnderCheckAtk" UnderCheckAtk {} (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some Ω | _ => none
  | none => []

/-- The innermost binding named `x` at a hole. -/
def valOf (Ω : List (String × Option Value × Value)) (x : String) : String :=
  match Ω.reverse.find? (·.1 == x) with
  | some (_, _, v) => toString v
  | none => "?"

#guard (holes "RH").map (valOf · "r") == ["⌈RH(σ1)⌉"]
#guard (holes "AH").map (valOf · "r") == ["⌈AH(S(σ0), σ2)⌉"]
#guard (holes "TH").map (valOf · "r") == ["⌈TH(TT, σ2)⌉"]
#guard (holes "CB").map (valOf · "r") == ["⌈let c1 = σ0; AddM(&c1, σ1); c1⌉"]
#guard (holes "CT").map (valOf · "r") == ["⌈let c1 = σ0; let r = TailM(&c1); *r := 0; c1⌉"]
#guard (holes "CS").map (valOf · "r") == ["0", "S(⌈let c1 = σ2; AddM(&c1, 0); c1⌉)"]
#guard (holes "RB").map (valOf · "u") == ["⌈RB(σ2, 0)⌉", "0"]
-- `go`'s recursive call through `h`: the sealed head is `go`'s closure with its capture `n` refined to `0`
#guard (holes "GoH").map (valOf · "r") ==
  ["⌈(fix go (y : Nat) : Nat by y := match κ1 { Z => match y { Z => 0, S _ => let h = fix _ (u : Unit) : Nat := go(clone(y.0)); let r = h(()); hole }, S _ => 0 } where κ1 = 0)(σ3)⌉"]
#guard (holes "GoH").map (valOf · "go") == ["⊥"]
-- the decreasing parameter's predecessor was MOVED into each recursive call (`n ↦ S(⊥)`; in `RB` the block took `n`
-- whole): the entry value survives only in the [Rec] stack's record, so the rank of a sealed call's argument is read
-- against the record (`RecRankG`), never against the environment (docs/31 D207)
#guard ["RH","AH","TH","RB"].map (fun n => (holes n).map (valOf · "n")) == [["S(⊥)"], ["S(⊥)"], ["S(⊥)"], ["⊥", "⊥"]]
-- `go` is not a global: the context constrains nothing at its name (`GlobalsOk` reads the globals only), while the
-- relation reads `go`'s marked binding at `C.global "go"` (`Binding.refTy`)
#guard ((Ochr.Test.runWith (some Prelude) "UnderCheckAtk" UnderCheckAtk {} (located := false)).allAsExpected)

end Ochr.Meaning.Steps.Form.UnderCheckAtk
