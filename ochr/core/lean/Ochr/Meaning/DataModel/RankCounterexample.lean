import Ochr.Meaning.DataModel.Old

/-!
# The rank law did not give guarded recursion through nesting (docs/34 §2.2; kernel-checked)

A record against the data layer before docs/34's port (its frozen copy, `DataModel/Old.lean`,
with the old `semRank` and the old `Regress/DataCodes.lean` rose trees copied below). The port's
rank is the height of the meaning, under which `CountF` computes `3` (`Regress/DataCodes.lean`).

`DataModel.rank_lt` says that a field whose declared type is a direct occurrence of the
declaration packs an element of smaller rank. The reference run's guarded fixpoint reads
`semRank` of the decreasing argument, the rank its own declaration gives the element it packs
(`Places.lean`), and the checker's [Rec] accepts a recursive call at any strict subterm of the
entry value, through any field (`DataModel/Probes.lean`: `CountF` over `List(Rose(Nat))`,
recursing on the head tree's forest, accepted, and `Eq(…, 3)` by `refl`).

Here is a data model `dmK` that covers `List` and `Rose`, satisfies every law of `DataModel`
(its reading is its own, `List`'s direct recursive field is announced by `recArgs` and ranked
by length), reads `List(Rose(Nat))` and `Rose(Nat)` at the run's codes, and under which the
forest `k` reached from `f` by two field steps (`f.0.1`, the head tree's `kids`) has the same
`semRank` as `f` (`semRank_eq`). The generic model's rank of that time (the first stage, length
plus one for a list) was the same. So `rank_lt` does not give what `CountF` needs, and the
model's guarded fixpoint cuts `CountF`'s recursion where the checker computes.

The model is honest at the parameters the program uses (`List` at `Rose(Nat)`, `Rose` at `Nat`)
and degenerate elsewhere (only fieldless constructors), which the laws allow.
-/

namespace Ochr.Meaning.DataModel.RankCounterexample

open Ochr Ochr.Meaning.Old Ochr.Meaning.Old.DataModel

/-! ## The old layer's rank and rose trees (copied from `Places.lean` and `Regress/DataCodes.lean`
at 34ecffdd) -/

/-- The old rank: the rank its own declaration gives the element a constructor value packs (a
number's, its value, is not needed here). -/
noncomputable def semRank (dm : DataModel) (Γ : List IndDecl) : Sem → Nat
  | .dat n ps _ _ (some ⟨A, x⟩) =>
    match Γ.find? (·.name == n) with
    | some d => open Classical in if h : A = dm.car d ps then dm.rank (h ▸ x) else 0
    | none => 0
  | _ => 0

def listD : IndDecl :=
  { name := "List", params := [(⟨"A"⟩, .sort 1)],
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 1)])])] }

def roseD : IndDecl :=
  { name := "Rose", params := [(⟨"A"⟩, .sort 1)],
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 1)]])])] }

def psN : List Sem := [.ty TyM.nat]

inductive RoseN
  | node : Nat → List RoseN → RoseN

def cR : Code0 RoseN := .data roseD [.ty Nat .nat] RoseN
def psR : List Sem := [.ty (.t0 RoseN cR)]
def cLR : Code0 (List RoseN) := .data listD [.ty RoseN cR] (List RoseN)

mutual
def semR : RoseN → Sem
  | .node a ks => .dat "Rose" psN 0 [.el0 Nat a, semLR ks] (some ⟨RoseN, .node a ks⟩)
def semLR : List RoseN → Sem
  | [] => .dat "List" psR 0 [] (some ⟨List RoseN, []⟩)
  | r :: rs => .dat "List" psR 1 [semR r, semLR rs] (some ⟨List RoseN, r :: rs⟩)
end

theorem semR_inj : ∀ {r r' : RoseN}, semR r = semR r' → r = r'
  | .node .., .node .., h => by
    simp only [semR, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2

theorem semLR_inj : ∀ {l l' : List RoseN}, semLR l = semLR l' → l = l'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [semLR, Sem.dat.injEq, Option.some.injEq] at h
    exact eq_of_heq (Sigma.mk.inj h.2.2.2.2).2
  | [], _ :: _, h => by simp [semLR] at h
  | _ :: _, [], h => by simp [semLR] at h

/-! ## The model -/

/-- Constructor `c` of `d` exists and has no fields. -/
def Fieldless (d : IndDecl) (c : Nat) : Prop := ∃ ctor, d.ctors[c]? = some ctor ∧ ctor.2.length = 0

/-- A type that is `Nat`. -/
def natTy : TyM → Bool
  | .t0 _ .nat => true
  | _ => false

/-- A type that is a data code of a declaration named `Rose` at the parameter `Nat`. -/
def roseNatTy : TyM → Bool
  | .t0 _ (.data e [.ty _ .nat] _) => e.name == "Rose"
  | _ => false

/-- What the model makes of a declaration at parameters. -/
inductive K
  | rose | list | other
deriving DecidableEq

def kind (d : IndDecl) (ps : List Sem) : K :=
  match ps with
  | [.ty T] =>
    if d.name == "Rose" && natTy T then .rose
    else if d.name == "List" && roseNatTy T then .list
    else .other
  | _ => .other

def K.car (d : IndDecl) : K → Type
  | .rose => RoseN
  | .list => List RoseN
  | .other => {c : Nat // Fieldless d c}

def K.tag (d : IndDecl) : (k : K) → k.car d → Nat
  | .rose, _ => 0
  | .list, [] => 0
  | .list, _ :: _ => 1
  | .other, x => x.1

def K.fields (d : IndDecl) : (k : K) → k.car d → List Sem
  | .rose, .node a ks => [.el0 Nat a, semLR ks]
  | .list, [] => []
  | .list, r :: rs => [semR r, semLR rs]
  | .other, _ => []

def K.fieldTy : K → Nat → TyM
  | .rose, i => if i = 0 then TyM.nat else .t0 (List RoseN) cLR
  | .list, i => if i = 0 then .t0 RoseN cR else .t0 (List RoseN) cLR
  | .other, _ => TyM.err

def K.rank (d : IndDecl) : (k : K) → k.car d → Nat
  | .list, l => l.length
  | _, _ => 0

theorem K.inj (d : IndDecl) : ∀ (k : K) (x y : k.car d), k.tag d x = k.tag d y → k.fields d x = k.fields d y → x = y
  | .rose, .node a ks, .node b ls, _, h => by
    simp only [K.fields, List.cons.injEq, Sem.el0.injEq, heq_eq_eq, true_and, and_true] at h
    obtain ⟨rfl, h⟩ := h
    have := semLR_inj h
    rw [this]
  | .list, [], [], _, _ => rfl
  | .list, [], _ :: _, h, _ => by cases h
  | .list, _ :: _, [], h, _ => by cases h
  | .list, r :: rs, s :: ss, _, h => by
    simp only [K.fields, List.cons.injEq, and_true] at h
    rw [semR_inj h.1, semLR_inj h.2]
  | .other, x, y, h, _ => Subtype.ext h


/-! ## The model -/

def car (d : IndDecl) (ps : List Sem) : Type := (kind d ps).car d
def tag {d : IndDecl} {ps : List Sem} (x : car d ps) : Nat := (kind d ps).tag d x
def fields {d : IndDecl} {ps : List Sem} (x : car d ps) : List Sem := (kind d ps).fields d x

/-- The model's reading: its own tags and fields. -/
noncomputable def R : DataRead := readOf car tag fields

theorem kind_roseN : kind roseD psN = .rose := rfl
theorem kind_listR : kind listD psR = .list := rfl

theorem R_rose (r : RoseN) : R roseD psN RoseN r = (0, K.fields roseD .rose r) :=
  readOf_car car tag fields (d := roseD) (ps := psN) r

theorem R_list (l : List RoseN) : R listD psR (List RoseN) l = (K.tag listD .list l, K.fields listD .list l) :=
  readOf_car car tag fields (d := listD) (ps := psR) l

/-- The run's codes of `Rose(Nat)` and `List(Rose(Nat))` encode, at the model's reading, as the
meanings `Regress/DataCodes.lean` gives (`semR`, `semLR`). -/
theorem enc_cR (r : RoseN) : Code0.enc R cR r = semR r := by
  show Sem.dat "Rose" psN (R roseD psN RoseN r).1 (R roseD psN RoseN r).2 (some ⟨RoseN, r⟩) = semR r
  rw [R_rose]; cases r; rfl

theorem enc_cLR (l : List RoseN) : Code0.enc R cLR l = semLR l := by
  show Sem.dat "List" psR (R listD psR (List RoseN) l).1 (R listD psR (List RoseN) l).2
    (some ⟨List RoseN, l⟩) = semLR l
  rw [R_list]; cases l <;> rfl

theorem mem_nat (s : Sem) : s ∈ₛ[R] TyM.nat ↔ ∃ a, s = .el0 Nat a :=
  ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

theorem mem_cR (s : Sem) : s ∈ₛ[R] .t0 RoseN cR ↔ ∃ r, s = semR r :=
  ⟨fun ⟨r, h⟩ => ⟨r, by rw [← h, enc_cR]⟩, fun ⟨r, h⟩ => ⟨r, by rw [h, enc_cR]⟩⟩

theorem mem_cLR (s : Sem) : s ∈ₛ[R] .t0 (List RoseN) cLR ↔ ∃ l, s = semLR l :=
  ⟨fun ⟨l, h⟩ => ⟨l, by rw [← h, enc_cLR]⟩, fun ⟨l, h⟩ => ⟨l, by rw [h, enc_cLR]⟩⟩

theorem mem_err (s : Sem) : ¬ (s ∈ₛ[R] TyM.err) := fun ⟨a, _⟩ => a.elim


/-! ## Packing, kind by kind -/

theorem kind_roseD (ps : List Sem) : kind roseD ps ≠ .list := by
  unfold kind
  split
  · split
    · simp
    · split
      · simp [roseD] at *
      · simp
  · simp

theorem kind_listD (ps : List Sem) : kind listD ps ≠ .rose := by
  unfold kind
  split
  · split
    · simp [listD] at *
    · split <;> simp
  · simp

theorem ex_other (d : IndDecl) (c : Nat) (fs : List Sem) :
    (∃ x : K.car d .other, K.tag d .other x = c ∧ K.fields d .other x = fs) ↔
      ∃ ctor, d.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[R] K.fieldTy .other i := by
  constructor
  · rintro ⟨⟨c', ctor, hc, hl⟩, rfl, rfl⟩
    exact ⟨ctor, hc, by simp [hl, K.fields], fun i hi => absurd hi (by simp [K.fields])⟩
  · rintro ⟨ctor, hc, hl, hm⟩
    cases fs with
    | nil => exact ⟨⟨c, ctor, hc, by simpa using hl.symm⟩, rfl, rfl⟩
    | cons f fs => exact absurd (hm 0 (by simp)) (mem_err _)

theorem ex_rose (c : Nat) (fs : List Sem) :
    (∃ x : K.car roseD .rose, K.tag roseD .rose x = c ∧ K.fields roseD .rose x = fs) ↔
      ∃ ctor, roseD.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[R] K.fieldTy .rose i := by
  constructor
  · rintro ⟨⟨a, ks⟩, rfl, rfl⟩
    refine ⟨_, rfl, rfl, fun i hi => ?_⟩
    match i, hi with
    | 0, _ => exact (mem_nat _).2 ⟨a, rfl⟩
    | 1, _ => exact (mem_cLR _).2 ⟨ks, rfl⟩
  · rintro ⟨ctor, hc, hl, hm⟩
    match c, hc with
    | 0, hc =>
      simp only [roseD, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, fs⟩⟩⟩ <;> simp at hl
      obtain ⟨a, rfl⟩ := (mem_nat _).1 (by simpa [K.fieldTy] using hm 0 (by simp))
      obtain ⟨l, rfl⟩ := (mem_cLR _).1 (by simpa [K.fieldTy] using hm 1 (by simp))
      exact ⟨.node a l, rfl, rfl⟩
    | n + 1, hc => simp [roseD] at hc

theorem ex_list (c : Nat) (fs : List Sem) :
    (∃ x : K.car listD .list, K.tag listD .list x = c ∧ K.fields listD .list x = fs) ↔
      ∃ ctor, listD.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[R] K.fieldTy .list i := by
  constructor
  · rintro ⟨x, rfl, rfl⟩
    cases x with
    | nil => exact ⟨_, rfl, rfl, fun i hi => absurd hi (by simp [K.fields])⟩
    | cons r rs =>
      refine ⟨_, rfl, rfl, fun i hi => ?_⟩
      match i, hi with
      | 0, _ => exact (mem_cR _).2 ⟨r, rfl⟩
      | 1, _ => exact (mem_cLR _).2 ⟨rs, rfl⟩
  · rintro ⟨ctor, hc, hl, hm⟩
    match c, hc with
    | 0, hc =>
      simp only [listD, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      cases fs with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons _ _ => simp at hl
    | 1, hc =>
      simp only [listD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, fs⟩⟩⟩ <;> simp at hl
      obtain ⟨r, rfl⟩ := (mem_cR _).1 (by simpa [K.fieldTy] using hm 0 (by simp))
      obtain ⟨l, rfl⟩ := (mem_cLR _).1 (by simpa [K.fieldTy] using hm 1 (by simp))
      exact ⟨r :: l, rfl, rfl⟩
    | n + 2, hc => simp [listD] at hc

theorem elt_semLR (l : List RoseN) : (semLR l).elt = some ⟨List RoseN, l⟩ := by cases l <;> rfl


theorem ex_iff (d : IndDecl) (hd : d = listD ∨ d = roseD) (ps : List Sem) (c : Nat) (fs : List Sem) :
    (∃ x : car d ps, tag x = c ∧ fields x = fs) ↔
      ∃ ctor, d.ctors[c]? = some ctor ∧ fs.length = ctor.2.length ∧
        ∀ i (h : i < fs.length), fs[i] ∈ₛ[R] (kind d ps).fieldTy i := by
  unfold car tag fields
  have hne : kind d ps = .rose → d = roseD := fun h => by
    rcases hd with rfl | rfl
    · exact absurd h (kind_listD ps)
    · rfl
  have hnl : kind d ps = .list → d = listD := fun h => by
    rcases hd with rfl | rfl
    · rfl
    · exact absurd h (kind_roseD ps)
  generalize kind d ps = k at hne hnl ⊢
  cases k with
  | rose => obtain rfl := hne rfl; exact ex_rose c fs
  | list => obtain rfl := hnl rfl; exact ex_list c fs
  | other => exact ex_other d c fs

theorem rank_list (ps : List Sem) (x : car listD ps) (y : car listD psR) (hk : kind listD ps = .list)
    (ht : tag x = 1) (hy : ((fields x)[1]?).bind Sem.elt = some ⟨car listD psR, y⟩) :
    (kind listD psR).rank listD y < (kind listD ps).rank listD x := by
  change List RoseN at y
  change K.car listD (kind listD ps) at x
  change ((kind listD ps).fields listD x)[1]?.bind Sem.elt = some ⟨List RoseN, y⟩ at hy
  change (kind listD ps).tag listD x = 1 at ht
  show y.length < (kind listD ps).rank listD x
  revert x
  rw [hk]
  intro x hy ht
  cases x with
  | nil => cases ht
  | cons r rs =>
    have hy2 : (semLR rs).elt = some ⟨List RoseN, y⟩ := hy
    rw [elt_semLR, Option.some.injEq] at hy2
    have h := eq_of_heq (Sigma.mk.inj hy2).2
    subst h
    show rs.length < (r :: rs).length
    simp

/-- **A lawful data model of `List` and `Rose`** whose rank of a list is its length. -/
noncomputable def dmK : DataModel where
  covers d := d = listD ∨ d = roseD
  car := car
  fieldTy d ps _ i _ := (kind d ps).fieldTy i
  paramTy _ _ _ := TyM.univ 1
  recArgs d ps c i _ := if kind d ps = .list ∧ c = 1 ∧ i = 1 then some psR else none
  pack d ps c fs := open Classical in
    if h : ∃ x : car d ps, tag x = c ∧ fields x = fs then some h.choose else none
  tag := tag
  fields := fields
  rank {d ps} x := (kind d ps).rank d x
  tag_pack {d ps c fs} x _ h := by
    split at h
    · rename_i hh; cases h; exact hh.choose_spec.1
    · cases h
  fields_pack {d ps c fs} x _ h := by
    split at h
    · rename_i hh; cases h; exact hh.choose_spec.2
    · cases h
  pack_fields {d ps} x _ := by
    show (open Classical in
      if h : ∃ y : car d ps, tag y = tag x ∧ fields y = fields x then some h.choose else none) = some x
    rw [dif_pos ⟨x, rfl, rfl⟩]
    congr 1
    have hs := (⟨x, rfl, rfl⟩ : ∃ y : car d ps, tag y = tag x ∧ fields y = fields x).choose_spec
    exact K.inj d (kind d ps) _ _ hs.1 hs.2
  pack_isSome {d ps c fs} hd := by
    refine Iff.trans ?_ (ex_iff d hd ps c fs)
    show (open Classical in
      if h : ∃ x : car d ps, tag x = c ∧ fields x = fs then some h.choose else none).isSome ↔ _
    split
    · rename_i h; exact ⟨fun _ => h, fun _ => rfl⟩
    · rename_i h; exact ⟨fun hh => absurd hh (by simp), fun hh => absurd hh h⟩
  rank_lt {d ps ps'} x y hd i hr hy := by
    split at hr
    · rename_i hk
      obtain ⟨hk, ht, rfl⟩ := hk
      cases hr
      have hd' : d = listD := by
        rcases hd with rfl | rfl
        · rfl
        · exact absurd hk (kind_roseD ps)
      subst hd'
      exact rank_list ps x y hk ht hy
    · cases hr


/-! ## The model reads the program's types at the run's codes -/

/-- `Rose(Nat)` means its code `cR`, and `List(Rose(Nat))` the code `cLR` holding it: the run's
readings of `D(ā)` (`.tind`: `dm.tyM d ps`). -/
theorem tyM_rose : dmK.tyM roseD psN = .t0 RoseN cR := rfl
theorem tyM_listRose : dmK.tyM listD [.ty (dmK.tyM roseD psN)] = .t0 (List RoseN) cLR := rfl

/-- The field types at those parameters are the run's readings of the declared field types:
`Rose`'s `kids : List(Rose(A))` at `A := Nat`, `List`'s `h : A` and `t : List(A)` at
`A := Rose(Nat)`. -/
theorem fieldTy_honest (e : List Sem) :
    dmK.fieldTy roseD psN 0 1 e = dmK.tyM listD [.ty (dmK.tyM roseD psN)] ∧
    dmK.fieldTy listD psR 1 0 e = dmK.tyM roseD psN ∧
    dmK.fieldTy listD psR 1 1 e = dmK.tyM listD psR :=
  ⟨rfl, rfl, rfl⟩

/-- `List`'s recursive field is announced at its declared occurrence's parameters. -/
theorem recArgs_honest (e : List Sem) : dmK.recArgs listD psR 1 1 e = some psR := rfl

/-! ## `CountF`'s recursive call does not decrease the rank -/

/-- The forest `CountF` is called at in `F3` (`DataModel/Probes.lean`), and the forest its
recursive call is at: the head tree's `kids`. -/
def f : List RoseN := [.node 1 [.node 2 [.node 3 []]]]
def k : List RoseN := [.node 2 [.node 3 []]]

/-- `k`'s meaning is reached from `f`'s by two field steps (`Sem.parts`, what the run's match reads):
field `0` of `f` (the head tree), then field `1` of that (its `kids`). -/
theorem k_in_f : (semLR f).parts = some (1, [semR (.node 1 k), semLR []]) ∧
    (semR (.node 1 k)).parts = some (0, [.el0 Nat 1, semLR k]) := ⟨rfl, rfl⟩

/-- Both are members of `List(Rose(Nat))` at the model's reading. -/
theorem f_mem : semLR f ∈ₛ[dmK.read] dmK.tyM listD psR := ⟨f, enc_cLR f⟩
theorem k_mem : semLR k ∈ₛ[dmK.read] dmK.tyM listD psR := ⟨k, enc_cLR k⟩

/-- The program's inductive declarations, as the run reads them. -/
def Γ : List IndDecl := [listD, roseD]

theorem semRank_semLR (l : List RoseN) : semRank dmK Γ (semLR l) = l.length := by
  have he : semLR l = .dat "List" psR (K.tag listD .list l) (K.fields listD .list l) (some ⟨List RoseN, l⟩) := by
    cases l <;> rfl
  rw [he]
  show (match Γ.find? (·.name == "List") with
    | some d => open Classical in if h : List RoseN = dmK.car d psR then dmK.rank (h ▸ l) else 0
    | none => 0) = l.length
  have hf : Γ.find? (·.name == "List") = some listD := rfl
  rw [hf]
  exact (dif_pos (rfl : List RoseN = dmK.car listD psR)).trans rfl

/-- **`CountF`'s recursive argument has the rank of its entry value**: `semRank` of `k` equals
`semRank` of `f`, though `k` is a strict subterm of `f` (`k_in_f`), the checker accepts the call,
and the model is lawful (`dmK`, `rank_lt` included). The reference run's guarded fixpoint
evaluates `CountF` at `f` with stages up to `semRank f + 1` and reaches `k` with one stage fewer
than its own rank needs, so the model's `CountF(f)` reads the filler of D60 one call early. -/
theorem semRank_eq : semRank dmK Γ (semLR k) = semRank dmK Γ (semLR f) := by
  rw [semRank_semLR, semRank_semLR]; rfl

end Ochr.Meaning.DataModel.RankCounterexample
