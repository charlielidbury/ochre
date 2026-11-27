import Ochr.Meaning.Steps.FrameEnd

/-!
# [End] against the frame relation: the holders and the shape (lead31; docs/31 D209)

The second part of the end's bookkeeping (lead30's `FrameEnd` proved the values: `bindRen_end`, `lowerVal_end`). When
the body ends a borrow, the reference's `endLabel` finds the label's holder (`holderOf`, the first position holding it)
and forgets it (`endAt`). Here: the two sides find CORRESPONDING holders (in place `p`, a position of the callee's top
frame, in the closure `upPos p`), and the three shape clauses of `FrameRel` (`topShape`, `lowerShape`, `clShape`)
survive the two ends. Principle 12 (access is exclusive: a live borrow has one holder) and principle 6 (effects stay
local: the callee's labels are held in its own frame).

Hypotheses, by class: `FrameRel` (the relation); `Uniq` of the in-place state (one holder per label: `Strict.SGood.uniq`);
`ShapeAt` of the in-place state (a shape entry is at a position). `ShapeAt` is NOT a clause of `SGood` or of
`FrameRel`: a holder recorded at a position the state does not have would make `holderOf` miss it in place while the
closure finds its counterpart; every run keeps it (a position is dropped with its shape entry, `dropLast_shape`), so the
internal relation of the frame property is to carry it (docs/31 D209).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-- Every shape entry is at a position of the state. -/
def ShapeAt (s : SState) : Prop := ∀ p l, s.shape p = some l → p ∈ s.positions

/-- `upPos` is one to one within a frame. -/
theorem upPos_inj {c : Nat} {p q : Pos} (hf : p.frameOf = q.frameOf) (h : upPos c p = upPos c q) : p = q := by
  cases p <;> cases q <;> simp_all [upPos, Pos.frameOf]

/-- **The two ends find corresponding holders.** If the closure's `holderOf l` is `q`, then `q` is `upPos p` for a
position `p` of the callee's top frame, and in place `holderOf (σ l)` is `p`. -/
theorem holder_frame {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (hu : s.Uniq) (hsa : ShapeAt s) {l : Nat} {q : Pos} (hq : s'.holderOf l = some q) :
    ∃ p, p.frameOf = s₀.topIdx ∧ q = upPos ks.length p ∧ s.holderOf (σ l) = some p := by
  obtain ⟨-, hql⟩ := SState.holderOf_spec hq
  obtain ⟨p, hpf, rfl⟩ := hr.clShape q l hql
  have hp : s.shape p = some (σ l) := by rw [hr.topShape p hpf, hql]; rfl
  obtain ⟨p', hp'⟩ := SState.holderOf_of_live ((SState.live_iff s _).2 ⟨p, hsa p _ hp, hp⟩)
  have h' := (SState.holderOf_spec hp').2
  exact ⟨p, hpf, rfl, by rw [hp', hu p' p _ h' hp]⟩

/-- **`topShape` after the two ends**, at corresponding holders. -/
theorem topShape_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    {l : Nat} {p : Pos} (hpf : p.frameOf = s₀.topIdx) :
    ∀ p₁, p₁.frameOf = s₀.topIdx →
      (s.endAt (σ l) p).shape p₁ = ((s'.endAt l (upPos ks.length p)).shape (upPos ks.length p₁)).map σ := by
  intro p₁ h₁
  rw [SState.endAt_shape, SState.endAt_shape]
  by_cases e : p₁ = p
  · subst e; simp
  · have e' : upPos ks.length p₁ ≠ upPos ks.length p := fun h => e (upPos_inj (by rw [h₁, hpf]) h)
    simp only [if_neg e, if_neg e']
    exact hr.topShape p₁ h₁

/-- **`lowerShape` after the end in place**: the holder is in the top frame, so the caller's holders stay. -/
theorem lowerShape_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    {l : Nat} {p : Pos} (hpf : p.frameOf = s₀.topIdx) :
    ∀ p₁, p₁.frameOf < s₀.topIdx → (s.endAt l p).shape p₁ = s₀.shape p₁ := by
  intro p₁ h₁
  rw [SState.endAt_shape]
  have hne : p₁ ≠ p := fun e => by subst e; omega
  simp only [if_neg hne]
  exact hr.lowerShape p₁ h₁

/-- **`clShape` after the end in the closure**: the closure holds nothing new. -/
theorem clShape_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (l : Nat) (q₀ : Pos) :
    ∀ q m, (s'.endAt l q₀).shape q = some m → ∃ p, p.frameOf = s₀.topIdx ∧ q = upPos ks.length p := by
  intro q m h
  rw [SState.endAt_shape] at h
  by_cases e : q = q₀
  · simp [e] at h
  · simp only [if_neg e] at h
    exact hr.clShape q m h

/-- **The ends are `endAt` at corresponding holders**: what the value lemmas (`bindRen_end`, `lowerVal_end`) and the shape
lemmas above are about. -/
theorem endLabel_frame {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (hu : s.Uniq) (hsa : ShapeAt s) {l : Nat} (hl : s'.Live l) :
    ∃ p, p.frameOf = s₀.topIdx ∧ s'.endLabel l = s'.endAt l (upPos ks.length p) ∧
      s.endLabel (σ l) = s.endAt (σ l) p := by
  obtain ⟨q, hq⟩ := SState.holderOf_of_live hl
  obtain ⟨p, hpf, rfl, hp⟩ := holder_frame hr hu hsa hq
  exact ⟨p, hpf, SState.endLabel_eq hq, SState.endLabel_eq hp⟩

/-- **`topLabels` after the end in the closure**: ending only shrinks the live labels. -/
theorem topLabels_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (l : Nat) (q₀ : Pos) : ∀ m, (s'.endAt l q₀).Live m → σ m ∈ ks ∨ s₀.nextLoan ≤ σ m :=
  fun m h => hr.topLabels m (SState.endAt_live h)

/-- **`held` after the two ends**: the records do not change, and the closure's live labels only shrink. -/
theorem held_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (l l' : Nat) (p q₀ : Pos) : ∀ m, (s'.endAt l' q₀).Live m →
      (σ m ∉ ks → (s.endAt l p).heldMem (σ m) = (s'.endAt l' q₀).heldMem m) ∧
        (s.endAt l p).heldTy (σ m) = (s'.endAt l' q₀).heldTy m :=
  fun m h => hr.held m (SState.endAt_live h)

/-- **`inj`, `fresh` and `frames` after the two ends**: no label is issued and no frame pushed or dropped. -/
theorem counters_endAt {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState} (hr : FrameRel σ s₀ ks s s')
    (l l' : Nat) (p q₀ : Pos) :
    (∀ j, σ ((s'.endAt l' q₀).nextLoan + j) = (s.endAt l p).nextLoan + j) ∧
      (s.endAt l p).env.length = s₀.env.length ∧ (s'.endAt l' q₀).env.length = 2 := by
  refine ⟨fun j => hr.fresh j, ?_, ?_⟩
  · simp only [SState.endAt, SState.mapVals, List.length_map, List.length_zipIdx]; exact hr.frames.1
  · simp only [SState.endAt, SState.mapVals, List.length_map, List.length_zipIdx]; exact hr.frames.2

end Ochr.Meaning.Steps.Form.FrameEnd
