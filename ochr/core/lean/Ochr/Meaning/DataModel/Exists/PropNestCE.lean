import Ochr.Meaning.DataModel.Canonical.Knot
import Ochr.Examples.Nat

/-!
# The knot is not guarded at a `Prop`-sorted declaration nested at a `Prop` parameter (piece 4)

`inductive Q : Prop := MkQ(h : And(Q, True))` is accepted (asserted below): `Q` occurs at `And`'s
parameter `P`, which `And` uses only as a whole field type, so it is nestable (D107). The reference
run reads the field's type as `And(Q, True)`: `And`'s code at the record of its parameters, the
first being `Q`'s own type, `uTyR Q (R [])`, which for a `Prop`-sorted declaration is the
proposition `Nonempty (car Q (R []))`. That proposition reads `Q`'s record at EVERY depth.

So no record function for `And` faithful at its first field makes `Q`'s field type guarded
(`not_guarded`): faithfulness makes `And`'s records at `prop True` and `prop False` differ at some
path `p`, and two records of `Q` that agree on every path shorter than `p.length + 1` (`chain`: a
proof of `Q` nested `k` times, then a leaf `prop b`) can still have `Q` inhabited at one and empty at
the other (`chain_inhabited`). Piece 4's guardedness therefore holds only for data-sorted
declarations; a `Prop`-sorted one is built from its truth predicate first (piece 5, as
`Proto/PropSorted.lean` does for `Ev`, whose docstring names this case), and that needs every
earlier declaration's membership to be monotone in its nestable `Prop` parameters.
-/

open Ochr.Test

namespace Ochr.Meaning.DataModel.Exists.PropNestCE

ochr DMXPropNest uses Nats {
  inductive Q : Prop := MkQ(h : And(Q, True))
  inductive BoxP (A : Prop) := MkBP(x : A)
  inductive P : Prop := MkP(b : BoxP(P))
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, S(S(m))))
  inductive EvB (n : Nat) : Prop := MkEvB(h : And(EvB(n), Ev(n))) | StopB(h : Ev(n))
  def evb : EvB(0) := StopB[0](EvZ[0](refl))
}

-- every declaration of the block is accepted
#guard (run "DMXPropNest" DMXPropNest).rejectedWith []

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- `Q`, as a `Prop`-sorted declaration with one constructor of one field. -/
def qD : IndDecl :=
  { name := "Q", sort := 0, ctors := [("MkQ", [("h", .tind "And" [.tind "Q" [], .tind "True" []])])] }

/-- `And`. -/
def andD : IndDecl :=
  { name := "And", params := [(⟨"P"⟩, .sort 0), (⟨"Q"⟩, .sort 0)], sort := 0,
    ctors := [("Intro", [("l", .place (.var 1)), ("r", .place (.var 1))])] }

/-- A record of `Q`: its field a proof of `Q` again, `k` times, then a leaf `prop b`. -/
def chain (b : Prop) : Nat → List RStep → Entry
  | 0, [(0, 0, [])] => .leaf (PLift b) (.prop b)
  | _ + 1, [(0, 0, [])] => .data qD
  | k + 1, (0, 0, [.proof]) :: q => chain b k q
  | _, _ => .none

theorem chain_agree (b b' : Prop) : ∀ (k : Nat) (q : List RStep), q.length ≤ k → chain b k q = chain b' k q
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => rfl
  | k + 1, (c, i, es) :: q, h => by
    have hq : q.length ≤ k := by simpa using h
    rcases c with _ | c <;> rcases i with _ | i <;> rcases es with _ | ⟨e, es⟩
    all_goals first
      | rfl
      | (rcases q with _ | ⟨s, q⟩ <;> first | rfl | (rcases e with _ | _ | _ | _ <;> first | rfl | (rcases es with _ | _ <;> first | rfl | exact chain_agree b b' k _ hq)))
      | (rcases e with _ | _ | _ | _ <;> first | rfl | (rcases es with _ | _ <;> first | rfl | exact chain_agree b b' k _ hq))

/-- `Q`'s field at a `chain` record. -/
theorem chain_shape0 (b : Prop) : uShape qD (chain b 0) 0 0 [] = .leaf (PLift b) (.prop b) := rfl

theorem chain_cont (b : Prop) (k : Nat) : contRec (chain b (k + 1)) (contStep 0 0 []) = chain b k := by
  funext q
  rcases q with _ | ⟨s, q⟩ <;> rfl

theorem chain_shapeS (b : Prop) (k : Nat) : uShape qD (chain b (k + 1)) 0 0 [] = .prf qD (chain b k) := by
  have h := uShape_data qD (chain b (k + 1)) 0 0 [] qD rfl
  rw [h, projIdx_nil, chain_cont]
  rfl

theorem chain_inhabited (b : Prop) : ∀ k, (∃ v, DataLib.Mem uSig qD (chain b k) v) ↔ b := by
  intro k
  induction k with
  | zero =>
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨⟨c, hc⟩, fs, -, hfs⟩ := (DataLib.mem_iff uSig qD _ v).1 hv
      have hc0 : c = 0 := by simp [qD] at hc; omega
      subst hc0
      obtain ⟨f, fs', -, hf, -⟩ := hfs
      change FitsOneM uSig (uShape qD (chain b 0) 0 0 []) f at hf
      rw [chain_shape0] at hf
      obtain ⟨⟨hb⟩, -⟩ := hf
      exact hb
    · intro hb
      refine ⟨_, (DataLib.mem_iff uSig qD _ _).2 ⟨⟨0, by decide⟩, [.proof], rfl, .proof, [], rfl, ?_, rfl⟩⟩
      change FitsOneM uSig (uShape qD (chain b 0) 0 0 []) _
      rw [chain_shape0]
      exact ⟨⟨hb⟩, rfl⟩
  | succ k ih =>
    refine Iff.trans ?_ ih
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨⟨c, hc⟩, fs, -, hfs⟩ := (DataLib.mem_iff uSig qD _ v).1 hv
      have hc0 : c = 0 := by simp [qD] at hc; omega
      subst hc0
      obtain ⟨f, fs', -, hf, -⟩ := hfs
      change FitsOneM uSig (uShape qD (chain b (k + 1)) 0 0 []) f at hf
      rw [chain_shapeS] at hf
      exact hf.2
    · intro hv
      refine ⟨_, (DataLib.mem_iff uSig qD _ _).2 ⟨⟨0, by decide⟩, [.proof], rfl, .proof, [], rfl, ?_, rfl⟩⟩
      change FitsOneM uSig (uShape qD (chain b (k + 1)) 0 0 []) _
      rw [chain_shapeS]
      exact ⟨rfl, hv⟩

/-- `Q`'s type at a `chain` record is the proposition at its bottom. -/
theorem uTyR_chain (b : Prop) (k : Nat) : uTyR qD (chain b k) = TyM.prop b := by
  have hs : (qD.sort == 0) = true := rfl
  simp only [uTyR, hs, if_true]
  congr 1
  apply propext
  refine Iff.trans ?_ (chain_inhabited b k)
  constructor
  · rintro ⟨x⟩; exact ⟨_, (DataLib.mem_iff_meanC uSig qD _ _).2 ⟨x, rfl⟩⟩
  · rintro ⟨v, hv⟩; obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig qD _ v).1 hv; exact ⟨x⟩

theorem prop_true_ne_false : TyM.prop True ≠ TyM.prop False := by
  intro h
  obtain ⟨hA, -⟩ := TyM.t0_inj h
  exact (cast hA (PLift.up trivial)).down

/-- `Q`'s field type as the run reads it, given a record function `RA` for `And` and `True`'s type
`T`: `And` at `Q`'s own proposition (through `Q`'s record function `R`) and `T`. -/
noncomputable def qFty (RA : List Sem → Rec) (T : TyM) (R : List Sem → Rec) : FTy :=
  .data andD (RA [.ty (uTyR qD (R [])), .ty T])

/-- **Not guarded**: for every record function of `And` faithful at its first field (a field typed by
the parameter `P` means `P`), `Q`'s field type is not guarded at any set of nestable parameters. -/
theorem not_guarded (RA : List Sem → Rec) (T : TyM)
    (hA : ∀ P : Prop, shapeTyP (uShape andD (RA [.ty (TyM.prop P), .ty T]) 0 0 []) = TyM.prop P)
    (N : Nat → Bool) :
    ¬ ∀ n R R', RAgree N n R R' → FTyAgree n (qFty RA T R) (qFty RA T R') := by
  intro hg
  have hne : RA [.ty (TyM.prop True), .ty T] ≠ RA [.ty (TyM.prop False), .ty T] := by
    intro h
    have h1 := hA True
    rw [h, hA False] at h1
    exact prop_true_ne_false h1.symm
  have hp : ∃ p, RA [.ty (TyM.prop True), .ty T] p ≠ RA [.ty (TyM.prop False), .ty T] p :=
    Classical.byContradiction fun hc => hne (funext fun p => Classical.byContradiction fun hp => hc ⟨p, hp⟩)
  obtain ⟨p, hp⟩ := hp
  have hag : RAgree N (p.length + 1) (fun _ => chain True (p.length + 1)) (fun _ => chain False (p.length + 1)) :=
    fun _ _ _ q hq => chain_agree True False _ q (by omega)
  have h := (hg (p.length + 1) _ _ hag).2 p (Nat.lt_succ_self _)
  simp only [qFty, FTy.cont, uTyR_chain] at h
  exact hp h

end Ochr.Meaning.DataModel.Exists.PropNestCE
