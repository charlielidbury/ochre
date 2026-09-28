import Ochr.Examples.More

/-! # Unit tests of individual rules, run directly on the machine functions -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Units

def globalsOf (p : Program) : List GDef := (globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)).1

def st (p : Program) (nAbs : Nat) : MState :=
  { globals := globalsOf p, nextAbs := nAbs, absTy := (List.replicate nAbs Value.tNat).toArray }

def ok? {α : Type} : Except String α → Option α
  | .ok a => some a
  | .error _ => none

/-- `N(v, w) := ⌈let c1 = v; AddM(&c1, w); c1⌉`, what [Close] leaves in `AddM`'s borrowed place. -/
def N (v w : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.val v) (.seq (.call (.val (.gfn "AddM")) [.borrow (.var 0), .val w] true) (.place (.var 0))))

/-- `B(v)[h] := ⌈let c1 = v; let r = TailM(&c1); *r := h; c1⌉`, `TailM`'s effect with its hole. -/
def B (v h : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.val v) (.letIn ⟨"r"⟩ (.call (.val (.gfn "TailM")) [.borrow (.var 0)] true)
    (.seq (.assign (.deref (.var 0)) (.val h)) (.place (.var 1)))))

-- [Seal] (D9): refining σ0 := S σ1 re-runs N(σ0, 0); the inner call closes off, the
-- head call does not, so the S surfaces (deriver-e1 lemma S2)
#guard ok? (runM (substV (.abs 0) (.succ (.abs 1)) (N (.abs 0) .zero)) (st E2 2)) == some (.succ (N (.abs 1) .zero))
-- deriver-e1 S1: N(0, 0) ≡ 0
#guard ok? (runM (substV (.abs 0) .zero (N (.abs 0) .zero)) (st E2 1)) == some .zero
-- deriver-e1 S0: N(σ, 0) is normal (its own head call is not closed off again: no loop)
#guard ok? (runM (substV (.abs 5) .zero (N (.abs 0) .zero)) (st E2 6)) == some (N (.abs 0) .zero)
-- deriver-e2 §3.4: B(S σ1)[τ] ≡ S B(σ1)[τ]
#guard ok? (runM (substV (.abs 0) (.succ (.abs 1)) (B (.abs 0) (.abs 2))) (st E2 3)) == some (.succ (B (.abs 1) (.abs 2)))
-- deriver-e2 F3 / D11: a loan whose borrow is outside the [Seal] run is inert: B(0)[loan_9] ≡ loan_9
#guard ok? (runM (substV (.abs 0) .zero (B (.abs 0) (.loan 9))) (st E2 1)) == some (.loan 9)
-- ending the borrow fills the hole by substitution and re-normalises (D11)
#guard ok? (runM (substV (.loan 9) (.abs 2) (B .zero (.loan 9))) (st E2 3)) == some (.abs 2)

-- D18: owners(ℓ) is a set. Ω = [a ↦ S loan_5, b ↦ ⌈… loan_5 …⌉, r ↦ borrow_5 0]
def envD18 : Env := #[{ binds := #[⟨⟨"a"⟩, some .tNat, .succ (.loan 5), false⟩,
                                  ⟨⟨"b"⟩, some .tNat, .sealed (.val (.loan 5)), false⟩,
                                  ⟨⟨"r"⟩, some (.tRef .tNat), .borrow 5 .zero, false⟩] }]
#guard owners envD18 5 == [.bind 0 0, .bind 0 1]
-- W(*r := 0, *r := 1) observes both owners; the single-owner reading keeps one
#guard footprint envD18 [.assign (.deref (.var 0)) .zero, .assign (.deref (.var 0)) (.succ .zero)] == [.bind 0 0, .bind 0 1]
#guard footprint envD18 [.assign (.deref (.var 0)) .zero] false == [.bind 0 0]
-- an occurrence inside another borrow's content contributes that borrow's owners
def envChain : Env := #[{ binds := #[⟨⟨"c"⟩, some .tNat, .loan 0, false⟩] },
                        { binds := #[⟨⟨"x"⟩, some (.tRef .tNat), .borrow 0 (.succ (.loan 1)), false⟩,
                                     ⟨⟨"x'"⟩, some (.tRef .tNat), .borrow 1 (.abs 0), false⟩] }]
#guard owners envChain 1 == [.bind 0 0]

-- D18 end to end: after Pick the returned borrow's hole is in both a and b, so the
-- parameter type of Probe at the call point has one conjunct per owner
ochr D18 {
  def Pick (n : Nat) (x : &Nat) (y : &Nat) : &Nat := match n { Z => x | S _ => y }
  def Probe (z : &Nat) (e : Id Unit (*z := 0) (*z := 1)) : Unit := ()
  reject def Use (n : Nat) (a : Nat) (b : Nat) : Unit := let r = Pick(n, &a, &b); Probe(r, refl)

  -- meta-model C2 without currying (lean-checker, v1.4): the annotated block forms its
  -- type while the hole is in both a and b, and checks each arm against it refined. With
  -- owner sets the S arm must prove the b-conjunct Eq Nat 0 1 and fails; observing only
  -- the first owner accepts BadD18, and ClosedD18 is a closed proof of Eq Nat 0 1.
  def Pick3 (x : &Nat) (y : &Nat) (s : Nat) : &Nat := match s { Z => x | S _ => y }
  def K (z : &Nat) (e : Id Unit (*z := 0) (*z := 1)) : Eq Nat 0 1 := e
  reject def BadD18 (s : Nat) (hs : Eq Nat s 1) (a : Nat) (b : Nat) : Eq Nat 0 1 :=
    let r = Pick3(&a, &b, s);
    let e : Id Unit (*r := 0) (*r := 1) = match s { Z => hs | S _ => refl };
    K(r, e)
  reject def ClosedD18 : Eq Nat 0 1 := BadD18(1, refl, 0, 0)

  -- reviewer-1 C1: the same without an annotated block, expressible already in v1. The
  -- hypothesis h recomputes, with local copies, exactly the sealed program that a1 holds
  -- after Pick; single-owner observation makes Neq's parameter type that one equation.
  def Neq (y : &Nat) (h : Id Unit (*y := Z) (*y := S Z)) : Eq Nat Z (S Z) := h
  reject def GR (a1 : Nat) (a2 : Nat) (b : Nat)
      (h : Eq Nat (let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := Z; c1)
                  (let c1 = a1; let c2 = a2; let r = Pick(b, &c1, &c2); *r := S Z; c1)) : Eq Nat Z (S Z) :=
    let r = Pick(b, &a1, &a2); Neq(r, h)
  reject def BadR : Eq Nat Z (S Z) := GR(0, 0, 1, refl)
}

def useMessage (cfg : Config) : String :=
  match ((run "D18" D18 cfg).rows.find? (·.name == "Use")).map (·.verdict) with
  | some (Verdict.rejected m) => m
  | _ => ""

-- all owners: the expected parameter type is a conjunction over a and b
#guard ((useMessage {}).splitOn "∧").length == 2
-- single owner (counterfactual): one equation only
#guard ((useMessage { multiOwner := false }).splitOn "∧").length == 1

end Ochr.Units

#eval IO.println (Ochr.Units.useMessage {})
