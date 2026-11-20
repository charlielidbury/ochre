import Ochr.Meaning.DataModel.Proto.Examples

/-!
# The residual (docs/34 §3, §12): a field type applying a function to parameter-typed data

`RE (A : Type) := MkRE(xs : List(A), v : Eq(Word, LenL(A, xs), Succ(Zero)))`, used at itself:
`re1 : RE(RE(Nat))` (accepted; `reBad`, with an empty list, rejected; `Probes.lean`). The
reference run computes `v`'s type by applying `LenL`'s meaning, a Lean function on CARRIERS
(D59's closures), to `xs`'s meaning decoded into `List`'s carrier at `A`'s record; at
`A := RE(Nat)` that carrier is built from `RE`'s own signature. Read naively, the signature
`RE`'s carrier is built from is defined through a carrier built from that signature.

It is not. A closure is built from its body's run on the ENCODING of its argument
(`closureAt`: `f a := dec (run body (enc a))`, here `lenC := lenV ∘ meanC`), so applied to the
decoding of a member it is the body's run on the member itself: decoding then encoding is the
identity on members (the bijection, `mem_iff_meanC`). The signature is therefore defined on
meanings alone (`reRec`: the equation keyed by `xs` read small, `lenS`), with no carrier, and the
run's carrier-based reading agrees with it at every well-typed `xs` (`re_faithful`), at every
parameter, `RE(Nat)` included (`re_faithful_nested`). No recursion on records is needed. What
the port needs in its place is the run-level form of the same fact: a global closure applied to
a member argument is its body's run on the argument's meaning (docs/34 §12).
-/

namespace Ochr.Meaning.DataModel.Proto

/-! ## Locality: membership reads the signature only where it reaches

Two signatures that agree on a set of declarations and records closed under the data fields they
give have the same members there. So the members of `List` at `RE(Nat)`'s record are fixed by
`RE`'s signature at `RE(Nat)`'s record (and `List`'s), whatever it says at `RE(RE(Nat))`'s: the
order a definition of the signature by recursion on records would follow (docs/34 §12). -/

/-- A set of declarations and records closed under the data fields `S` gives there. -/
def Closed (S : Sig) (P : IndDecl → Rec → Prop) : Prop :=
  ∀ d r c i e d' r', P d r → S.shape d r c i e = .sub d' r' → P d' r'

theorem fits_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e)
    (L L' : Lvl) (hL : ∀ d r f, P d r → FitsOne L (.sub d r) f → FitsOne L' (.sub d r) f)
    (d : IndDecl) (r : Rec) (hd : P d r) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Val), Fits S L d r c i n e fs → Fits S' L' d r c i n e fs
  | _, 0, _, _, hf => hf
  | i, n + 1, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fits_congr S S' P hP hag L L' hL d r hd c (i + 1) n _ fs' h2⟩
    rw [← hag d r c i e hd]
    have hcl := hP d r c i e
    revert h1 hcl
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact fun h _ => h
    | sub d' r' => exact fun h hcl => hL d' r' f (hcl d' r' hd rfl) h

theorem rz_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e) :
    ∀ (k : Nat) (d : IndDecl) (r : Rec) (v : Val), P d r → Rz S k d r v → Rz S' k d r v
  | 0, _, _, _, _, ⟨x, _⟩ => x.elim
  | k + 1, d, r, v, hd, h => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 h
    exact (rz_succ_iff S' k d r _).2 ⟨c, fs, rfl, fits_congr S S' P hP hag (lvl S k) (lvl S' k)
      (fun d' r' f hd' h' => rz_congr S S' P hP hag k d' r' f hd' h') d r hd c 0 _ [] fs hf⟩

/-- **Locality of membership.** -/
theorem mem_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e)
    (d : IndDecl) (r : Rec) (hd : P d r) (v : Val) (h : Mem S d r v) : Mem S' d r v :=
  let ⟨k, hk⟩ := h; ⟨k, rz_congr S S' P hP hag k d r v hd hk⟩

/-- `LenL`'s body on meanings: the length of a list's spine. -/
def lenV : Val → Nat
  | .dat _ _ 1 [_, t] => lenV t + 1
  | _ => 0

theorem lenV_small : ∀ v : Val, lenV v = lenS v.small
  | .dat _ _ 1 [_, t] => by
    show lenV t + 1 = lenS (.node 1 [_, t.small])
    rw [lenV_small t]; rfl
  | .dat n r 0 fs => by cases fs <;> rfl
  | .dat n r (c + 2) fs => by cases fs <;> rfl
  | .dat n r 1 [] => rfl
  | .dat n r 1 [_] => rfl
  | .dat n r 1 (_ :: _ :: _ :: _) => rfl
  | .el0 _ _ | .el1 _ _ | .ty _ | .proof | .moved | .err => rfl

/-- `LenL`'s closure at `A`: a Lean function on `List`'s carrier at `A`'s record, its body run on
the encoding of its argument (`closureAt`'s form). -/
def lenC (eA : Entry) (x : car S listD (constRec eA)) : Nat := lenV (meanC S x)

open Classical in
/-- Decoding a meaning into `List`'s carrier at `A`'s record (`Code0.dec`'s form). -/
noncomputable def decL (eA : Entry) (v : Val) : Option (car S listD (constRec eA)) :=
  if h : ∃ x : car S listD (constRec eA), meanC S x = v then some h.choose else none

/-- **The run's reading of `v`'s type**: decode `xs`, apply `LenL`'s closure, compare with `1`
(`Succ(Zero)`); `err` where the decoding fails. -/
noncomputable def runRE (eA : Entry) (xs : Val) : Shape :=
  match decL eA xs with
  | some x => shapeOf (propEntry (lenC eA x = 1))
  | none => .leaf PEmpty .err

/-- **The signature, defined on meanings alone, is the run's carrier-based reading at every
well-typed `xs`.** -/
theorem re_faithful (eA : Entry) (xs : Val) (hxs : Mem S listD (constRec eA) xs) :
    runRE eA xs = S.shape reD (reRec eA) 0 1 [xs.small] := by
  have hex : ∃ x : car S listD (constRec eA), meanC S x = xs := (mem_iff_meanC S _ _ _).1 hxs
  have hdec : decL eA xs = some hex.choose := by simp only [decL, dif_pos hex]
  simp only [runRE, hdec]
  show shapeOf (propEntry (lenV (meanC S hex.choose) = 1)) = shapeOf (reRec eA [(0, 1, [xs.small])])
  rw [hex.choose_spec, lenV_small]
  rfl

/-- At the parameter `RE(Nat)`: `List`'s carrier there is built from `RE`'s own signature. -/
theorem re_faithful_nested (xs : Val) (hxs : Mem S listD (constRec (.data reD (reRec natE))) xs) :
    runRE (.data reD (reRec natE)) xs = S.shape reD (reRec (.data reD (reRec natE))) 0 1 [xs.small] :=
  re_faithful _ xs hxs

/-! ## The probe's values -/

def re0 : Val := .dat "RE" (reRec natE) 0 [consV (constRec natE) (.el0 Nat 0) (nilV (constRec natE)), .proof]
def reR1 : Rec := reRec (.data reD (reRec natE))
def re1 : Val := .dat "RE" reR1 0
  [consV (constRec (.data reD (reRec natE))) re0 (nilV (constRec (.data reD (reRec natE)))), .proof]

theorem re0_mem : Mem S reD (reRec natE) re0 := by
  refine mem_intro reD _ ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ?_, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩
  exact cons_mem _ _ _ ⟨0, rfl⟩ (nil_mem _)

/-- **`re1 : RE(RE(Nat))` is a member.** -/
theorem re1_mem : Mem S reD reR1 re1 := by
  refine mem_intro reD _ ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ?_, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩
  exact cons_mem _ _ _ re0_mem (nil_mem _)

/-- `reBad`'s type at the empty list is empty (the checker rejects `reBad`). -/
theorem reBad_empty (fs : List Val) :
    ¬ Mem S reD (reRec natE) (.dat "RE" (reRec natE) 0 (nilV (constRec natE) :: fs)) := by
  rw [mem_iff]
  rintro ⟨⟨c, hc⟩, gs, he, hf⟩
  simp only [Val.dat.injEq, true_and] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨f, fs', hfs, -, f2, fs2, hfs2, h2, -⟩ := hf
  simp only [List.cons.injEq] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have h2' : ∃ p : PLift (lenS (nilV (constRec natE)).small = 1), encLeaf (.prop _) p = f2 := h2
  obtain ⟨⟨hp⟩, -⟩ := h2'
  cases hp

/-- `Rose`'s nested field: the run's reading of `List(Rose(A))` (the code `List` at the type
`Rose(A)`, whose code names `Rose` and its record) is the signature's shape: no carrier read. -/
theorem rose_faithful (r : Rec) (e : List Small) :
    shapeOf (entryOf (tyOf S listD (constRec (entryOf (tyOf S roseD r))))) = S.shape roseD r 0 1 e := rfl

end Ochr.Meaning.DataModel.Proto
