import Ochr.Meaning.Steps.UnderCheckAttack

/-!
# A borrow parameter in a later parameter's type, and a parameter label lent at a match's entry (lead32; docs/31 D210, D211)

Two findings of the theory lane's second referee, pinned on the checker.

**`G1`, `G2` (docs/31 D210).** The checker reads a later parameter's type and the codomain at [Def]'s generic call, where a
borrow parameter `x` holds `borrow_ℓ σ` and its lender is a fresh owned place (the cell `c ↦ loan_ℓ`): an `Id` whose sides
write through `x` and then move or re-point it observes the cell. So `e`'s type in `G1` is `False` (the cell ends holding
`0` on one side, `1` on the other), and `G1 := e` is accepted. At a call site the same type is read with `x` bound to the
caller's borrow, and the observation sees the caller's place (`CallG1` is rejected: "argument 2 (e) has type ⊤,
expected False", the caller's `a` ending `0` on one side and `1` on the other). The model, before D210, read the same type with `x` a plain binding holding its
content, no label and no cell (`Run.extendBinds`): after `*x := 0; let z = x; ()` nothing remains that remembers the
write, so `e`'s type meant `True`, `G1`'s type meant `Π(x)(e : True). False`, which is empty, and `G1` was not a member
of its type. D210 makes the model read later domains and the codomain as [Def] does (`Run.extendBy` through `paramPush`).

**`P2`, `UseP2c` (docs/31 D211; the orchestrator's message of 2026-11-27).** The paper proof's invariant (P) of the frame
property ("a parameter label is lent only at its cell and in the caller's frames, never in the top frame, and never ended
by an access") is false: at `n = Z` the match's result is `x`, whose label is the PARAMETER label, and [Entry]'s [Lend]
lends the match's result at every place the block would take by `&`, here the captured `q`, a place of the callee's top
frame; `clone(q)` then accesses `q` and ends that parameter label. The checker accepts both, and `UseP2c` shows the
caller's `c` holding `1` after the call (the write through `r` reached it).

**`P3`, `UseP3` (docs/31 D211).** Two parameter labels lent at disjoint fields of one top-frame place by two entries, and
ended together by one access (`let w = q`), in label order. The caller makes `y`'s borrow (`rb`) before `x`'s, so in
place `x`'s label is the larger and in the function's own frame (where `x`'s cell comes first) the smaller: the
renaming is not monotone on parameter labels, and the access ends the two in opposite orders on the two sides. Both are
accepted and the caller sees both writes, so the frame relation's lemma for [Access] cannot rest on the order of ends
being the same: it needs the ends to commute (their holders read neither label).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr ParamCellAtk {
  def G1 (x : &Nat) (e : Id(Unit, (*x := Z; let z = x; ()), (*x := S(Z); let z = x; ()))) : False := e
  def G2 (x : &Nat) (y : &Nat) (e : Id(Unit, (*x := Z; x := y; ()), (*x := S(Z); x := y; ()))) : False := e
  def G5 (x : &Nat) (e : Id(Unit, *x := Z, *x := S(Z))) : False := e
  reject def CallG1 : False := (let a = S(Z); G1(&a, refl))
  def G1h (x : &Nat) (e : Id(Unit, (*x := Z; let z = x; ()), (*x := S(Z); let z = x; ()))) : Unit := ?
  def G2h (x : &Nat) (y : &Nat) (e : Id(Unit, (*x := Z; x := y; ()), (*x := S(Z); x := y; ()))) : Unit := ?
  def P2 (n : Nat) (x : &Nat) : Nat := (let q = S(S(S(S(S(Z))))); let r : &Nat = match n { Z => x, S(j) => &q, }; *r := S(Z); clone(q))
  def UseP2c : Eq(Nat, (let c = S(S(S(Z))); P2(Z, &c); c), S(Z)) := refl
  def UseP2s : Eq(Nat, (let c = S(S(S(Z))); P2(S(Z), &c); c), S(S(S(Z)))) := refl
  inductive PP := MkP(a : Nat, b : Nat)
  def P3 (n : Nat) (x : &Nat) (y : &Nat) : Nat := (let q = MkP(S(Z), S(S(Z)));
    let r1 : &Nat = match n { Z => x, S(j) => &q.0, };
    let r2 : &Nat = match n { Z => y, S(j) => &q.1, };
    *r1 := Z; *r2 := S(Z); let w = q; Z)
  def UseP3 : Eq(PP, (let a = S(S(S(Z))); let b = S(S(S(S(Z)))); let rb = &b; P3(Z, &a, rb); MkP(a, b)), MkP(Z, S(Z))) := refl
}

namespace Ochr.Meaning.Steps.Form.ParamCellAtk

open Ochr Ochr.Meaning

/-- Every environment a hole of definition `nm` reports. -/
def holes (nm : String) : List (List (String × Option Value × Value)) :=
  let r := Ochr.Test.runWith (some Prelude) "ParamCellAtk" ParamCellAtk {} (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some Ω | _ => none
  | none => []

/-- The stored type of the innermost binding named `x` at a hole. -/
def tyOf (Ω : List (String × Option Value × Value)) (x : String) : String :=
  match Ω.reverse.find? (·.1 == x) with
  | some (_, some T, _) => toString T
  | some (_, none, _) => "none"
  | none => "?"

-- at [Def]'s generic call `e`'s type is `False`: the observation sees the cell (`x`'s lender), which ends holding `0`
-- on one side and `1` on the other; the model's plain reading (no label, no cell) gave `⊤`
#guard (holes "G1h").map (tyOf · "e") == ["False"]
#guard (holes "G2h").map (tyOf · "e") == ["False"]
-- every verdict as expected: `G1`, `G2`, `G5` accepted, `CallG1` rejected (at the call site the observation sees the
-- caller's `a`), `P2`, `UseP2c` (the write through the parameter label lent at `q` reaches the caller's `c`), `UseP2s`
#guard ((Ochr.Test.runWith (some Prelude) "ParamCellAtk" ParamCellAtk {} (located := false)).allAsExpected)

end Ochr.Meaning.Steps.Form.ParamCellAtk
