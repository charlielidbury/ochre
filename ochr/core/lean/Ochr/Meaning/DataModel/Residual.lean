import Ochr.Meaning.DataModel.Examples

/-!
# The residual (docs/34 §3, §12): a field type applying a function to parameter-typed data (kernel-checked)

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

namespace Ochr.Meaning.DataModel.Program

open Ochr Ochr.Meaning Ochr.Meaning.DataLib

/-! ## Locality: membership reads the signature only where it reaches

Two signatures that agree on a set of declarations and records closed under the data fields they
give have the same members there. So the members of `List` at `RE(Nat)`'s record are fixed by
`RE`'s signature at `RE(Nat)`'s record (and `List`'s), whatever it says at `RE(RE(Nat))`'s: the
order a definition of the signature by recursion on records would follow (docs/34 §12). -/

/-- A set of declarations and records closed under the data and proof fields `S` gives there. -/
def Closed (S : Sig) (P : IndDecl → Rec → Prop) : Prop :=
  ∀ d r c i e d' r', P d r → (S.shape d r c i e = .sub d' r' ∨ S.shape d r c i e = .prf d' r') → P d' r'

theorem fits_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e)
    (L L' : Lvl) (hL : ∀ d r f, P d r → FitsOne L (.sub d r) f → FitsOne L' (.sub d r) f)
    (d : IndDecl) (r : Rec) (hd : P d r) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Sem), Fits S L d r c i n e fs → Fits S' L' d r c i n e fs
  | _, 0, _, _, hf => hf
  | i, n + 1, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fits_congr S S' P hP hag L L' hL d r hd c (i + 1) n _ fs' h2⟩
    rw [← hag d r c i e hd]
    have hcl := hP d r c i e
    revert h1 hcl
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact fun h _ => h
    | sub d' r' => exact fun h hcl => hL d' r' f (hcl d' r' hd (.inl rfl)) h
    | prf d' r' =>
      rintro ⟨hf, ⟨y⟩⟩ hcl
      obtain ⟨y', _⟩ := hL d' r' (L.mean y) (hcl d' r' hd (.inr rfl)) ⟨y, rfl⟩
      exact ⟨hf, ⟨y'⟩⟩

theorem rz_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e) :
    ∀ (k : Nat) (d : IndDecl) (r : Rec) (v : Sem), P d r → Rz S k d r v → Rz S' k d r v
  | 0, _, _, _, _, ⟨x, _⟩ => x.elim
  | k + 1, d, r, v, hd, h => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 h
    exact (rz_succ_iff S' k d r _).2 ⟨c, fs, rfl, fits_congr S S' P hP hag (lvl S k) (lvl S' k)
      (fun d' r' f hd' h' => rz_congr S S' P hP hag k d' r' f hd' h') d r hd c 0 _ [] fs hf⟩

/-- **Locality of membership.** -/
theorem mem_congr (S S' : Sig) (P : IndDecl → Rec → Prop) (hP : Closed S P)
    (hag : ∀ d r c i e, P d r → S.shape d r c i e = S'.shape d r c i e)
    (d : IndDecl) (r : Rec) (hd : P d r) (v : Sem) (h : DataLib.Mem S d r v) : DataLib.Mem S' d r v :=
  let ⟨k, hk⟩ := h; ⟨k, rz_congr S S' P hP hag k d r v hd hk⟩

/-- `LenL`'s body on meanings: the length of a list's spine. -/
def lenV : Sem → Nat
  | .dat _ _ 1 [_, t] => lenV t + 1
  | _ => 0

theorem lenV_small : ∀ v : Sem, lenV v = lenS v.small
  | .dat _ _ 1 [_, t] => by
    show lenV t + 1 = lenS (.node 1 [_, t.small])
    rw [lenV_small t]; rfl
  | .dat n r 0 fs => by cases fs <;> rfl
  | .dat n r (c + 2) fs => by cases fs <;> rfl
  | .dat n r 1 [] => rfl
  | .dat n r 1 [_] => rfl
  | .dat n r 1 (_ :: _ :: _ :: _) => rfl
  | .el0 _ _ | .el1 _ _ | .el2 _ _ | .ty _ | .proof | .moved | .err => rfl

/-- `LenL`'s closure at `A`: a Lean function on `List`'s carrier at `A`'s record, its body run on
the encoding of its argument (`closureAt`'s form). -/
def lenC (eA : Entry) (rA : Rec) (x : DataLib.car S listD (listR eA rA)) : Nat := lenV (DataLib.meanC S x)

open Classical in
/-- Decoding a meaning into `List`'s carrier at `A`'s record (`Code0.dec`'s form). -/
noncomputable def decL (eA : Entry) (rA : Rec) (v : Sem) : Option (DataLib.car S listD (listR eA rA)) :=
  if h : ∃ x : DataLib.car S listD (listR eA rA), DataLib.meanC S x = v then some h.choose else none

/-- **The run's reading of `v`'s type**: decode `xs`, apply `LenL`'s closure, compare with `1`
(`Succ(Zero)`); `err` where the decoding fails. -/
noncomputable def runRE (eA : Entry) (rA : Rec) (xs : Sem) : Shape :=
  match decL eA rA xs with
  | some x => shapeOf (propEntry (lenC eA rA x = 1)) natRec
  | none => .leaf PEmpty .err

/-- **The signature, defined on meanings alone, is the run's carrier-based reading at every
well-typed `xs`.** -/
theorem re_faithful (eA : Entry) (rA : Rec) (xs : Sem) (hxs : DataLib.Mem S listD (listR eA rA) xs) :
    runRE eA rA xs = S.shape reD (reRec eA rA) 0 1 [xs.small] := by
  have hex : ∃ x : DataLib.car S listD (listR eA rA), DataLib.meanC S x = xs := (DataLib.mem_iff_meanC S _ _ _).1 hxs
  have hdec : decL eA rA xs = some hex.choose := by simp only [decL, dif_pos hex]
  simp only [runRE, hdec]
  show shapeOf (propEntry (lenV (DataLib.meanC S hex.choose) = 1)) natRec
    = shapeOf (reRec eA rA [(0, 1, [xs.small])]) natRec
  rw [hex.choose_spec, lenV_small]
  rfl

/-- At the parameter `RE(Nat)`: `List`'s carrier there is built from `RE`'s own signature. -/
theorem re_faithful_nested (xs : Sem) (hxs : DataLib.Mem S listD (listR (.data reD) (reRec natE natRec)) xs) :
    runRE (.data reD) (reRec natE natRec) xs = S.shape reD (reRec (.data reD) (reRec natE natRec)) 0 1 [xs.small] :=
  re_faithful _ _ xs hxs

/-! ## The probe's values -/

/-- `List`'s values at a record. -/
def nilV (r : Rec) : Sem := .dat "List" r 0 []
def consV (r : Rec) (x xs : Sem) : Sem := .dat "List" r 1 [x, xs]

theorem nil_mem (r : Rec) : DataLib.Mem S listD r (nilV r) := mem_intro listD r ⟨0, by decide⟩ [] rfl

/-- `Cons(x, xs)` at `List(A)`'s record (`listR`: the signature is universal, so the tail's shape is
what the record holds past `t`, `List(A)`'s own record), `x` fitting the parameter's shape. -/
theorem cons_mem (eA : Entry) (rA : Rec) (x xs : Sem) (hx : FitsOneM S (shapeOf eA rA) x)
    (hxs : DataLib.Mem S listD (listR eA rA) xs) :
    DataLib.Mem S listD (listR eA rA) (consV (listR eA rA) x xs) := by
  refine mem_intro listD _ ⟨1, by decide⟩ [x, xs] ?_
  refine ⟨x, [xs], rfl, ?_, xs, [], rfl, hxs, rfl⟩
  show FitsOneM S (uShape listD (listR eA rA) 1 0 []) x
  rw [uShape_shapeOf]
  exact hx

def re0 : Sem := .dat "RE" (reRec natE natRec) 0
  [consV (listR natE natRec) (.el0 Nat 0) (nilV (listR natE natRec)), .proof]
def reR1 : Rec := reRec (.data reD) (reRec natE natRec)
def re1 : Sem := .dat "RE" reR1 0
  [consV (listR (.data reD) (reRec natE natRec)) re0 (nilV (listR (.data reD) (reRec natE natRec))), .proof]

theorem re0_mem : DataLib.Mem S reD (reRec natE natRec) re0 := by
  refine mem_intro reD _ ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ?_, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩
  exact cons_mem natE natRec _ _ ⟨0, rfl⟩ (nil_mem _)

/-- **`re1 : RE(RE(Nat))` is a member.** -/
theorem re1_mem : DataLib.Mem S reD reR1 re1 := by
  refine mem_intro reD _ ⟨0, by decide⟩ _ ?_
  refine ⟨_, _, rfl, ?_, _, [], rfl, ⟨⟨rfl⟩, rfl⟩, rfl⟩
  exact cons_mem (.data reD) (reRec natE natRec) _ _ re0_mem (nil_mem _)

/-- `reBad`'s type at the empty list is empty (the checker rejects `reBad`). -/
theorem reBad_empty (fs : List Sem) :
    ¬ DataLib.Mem S reD (reRec natE natRec) (.dat "RE" (reRec natE natRec) 0 (nilV (listR natE natRec) :: fs)) := by
  rw [DataLib.mem_iff]
  rintro ⟨⟨c, hc⟩, gs, he, hf⟩
  simp only [Sem.dat.injEq, true_and] at he
  obtain ⟨-, rfl, rfl⟩ := he
  obtain ⟨f, fs', hfs, -, f2, fs2, hfs2, h2, -⟩ := hf
  simp only [List.cons.injEq] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have h2' : ∃ p : PLift (lenS (nilV (listR natE natRec)).small = 1), encLeaf (.prop _) p = f2 := h2
  obtain ⟨⟨hp⟩, -⟩ := h2'
  cases hp

/-- `Rose`'s nested field: the run's reading of `List(Rose(A))` (`List`'s record at the type
`Rose(A)`, whose code names `Rose` and its record) is the signature's shape: no carrier read. At
`Rose`'s records (`roseR`; the signature is universal, so the shape is what the record holds past
`kids`, `forestR`, which is `List`'s record at `Rose(A)`, `forestR_eq`), and at earlier fields read
small of `kids`'s length (one, `a`: the key of field `1`). -/
theorem rose_faithful (eA : Entry) (rA : Rec) (e : List Small) (he : e.length = 1) :
    S.shape roseD (roseR eA rA) 0 1 e = .sub listD (dmP.recOf listD [.ty (dmP.tyR roseD (roseR eA rA))]) := by
  obtain ⟨s, rfl⟩ : ∃ s, e = [s] := by
    match e, he with
    | [s], _ => exact ⟨s, rfl⟩
  show uShape roseD (roseR eA rA) 0 1 [s] = .sub listD (listR (.data roseD) (roseR eA rA))
  rw [← forestR_eq]
  rfl

end Ochr.Meaning.DataModel.Program
