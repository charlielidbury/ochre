import Ochr.Meaning.Steps.FrameEndShape

/-!
# [End] against the frame relation, assembled (lead32; docs/31 D212)

The third and last part of the end's bookkeeping. lead30 proved the values (`FrameEnd`: `bindRen_end`, `lowerVal_end`),
lead31 the holders and the shape (`FrameEndShape`). Here: the sites a re-lend moves (`relend`: `lentTop`, `lentImg`,
`lentCl`, `lentCaller`), the caller's frames' skeleton (`lowerSkel`), the caller's values at the cells after the end
(`lowerVal`), the top frames (`top`), and the assembly: from `FrameRel` at a live closure label `l`, the two ends are
`FrameRel`-related again.

The sites need no invariant (P) (docs/31 D211: it is false, a match's entry lends a parameter label in the callee's top
frame): an end replaces each site AT THE HOLDER by the ended label's sites, adjusted, and keeps every other site. The
ended label's top-frame sites correspond through `upPos` (`lentTop`, before the end), its other sites are the caller's
(in place) or the cells (in the closure), which no top-frame clause compares. Principle 12 (one holder; an end moves
the loans its content holds to where the ended borrow was lent) and principle 6 (the callee's places are its frame's).
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning

/-- A site re-rooted by an end at a holder site `x` (`relend`'s map): its position is kept. -/
def relendSite (x y : Site) : Site := if y.fill then y else { y with path := y.path ++ inContent x.path, fill := x.fill }

theorem relendSite_pos (x y : Site) : (relendSite x y).pos = y.pos := by
  unfold relendSite; split <;> rfl

theorem relendSite_up (c : Nat) (x y : Site) :
    relendSite { x with pos := upPos c x.pos } { y with pos := upPos c y.pos } =
      { relendSite x y with pos := upPos c (relendSite x y).pos } := by
  unfold relendSite; split <;> rfl

theorem relend_eq (s : SState) (l : Nat) (r : Pos) (m : Nat) :
    s.relend l r m = if m = l then [] else (s.lent m).flatMap fun x =>
      if x.pos = r then (s.lent l).map (relendSite x) else [x] := rfl

theorem endAt_lent (s : SState) (l : Nat) (r : Pos) : (s.endAt l r).lent = s.relend l r := rfl

theorem flatMap_ite_self {α : Type _} (xs : List α) (P : α → Prop) [DecidablePred P] (f : α → List α)
    (h : ∀ x ∈ xs, ¬ P x) : xs.flatMap (fun x => if P x then f x else [x]) = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, if_neg (h a (by simp)), ih (fun x hx => h x (by simp [hx]))]
    rfl

/-- A site of `m` after an end at `r`: an old site of `m` away from `r`, or an old site of the ended label re-rooted at
an old site of `m` at `r`. -/
theorem mem_relend {s : SState} {l : Nat} {r : Pos} {m : Nat} {x : Site} (hm : m ≠ l) :
    x ∈ s.relend l r m ↔ (x ∈ s.lent m ∧ x.pos ≠ r) ∨
      ∃ x₀ ∈ s.lent m, x₀.pos = r ∧ ∃ y ∈ s.lent l, x = relendSite x₀ y := by
  rw [relend_eq, if_neg hm, List.mem_flatMap]
  constructor
  · rintro ⟨x₀, hx₀, hx⟩
    split at hx
    · rename_i e
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact .inr ⟨x₀, hx₀, e, y, hy, rfl⟩
    · rename_i e
      rw [List.mem_singleton] at hx; subst hx
      exact .inl ⟨hx₀, e⟩
  · rintro (⟨hx, e⟩ | ⟨x₀, hx₀, e, y, hy, rfl⟩)
    · exact ⟨x, hx, by rw [if_neg e]; exact List.mem_singleton_self _⟩
    · exact ⟨x₀, hx₀, by rw [if_pos e]; exact List.mem_map_of_mem hy⟩

variable {σ : Nat → Nat} {s₀ : SState} {ks : List Nat} {s s' : SState}

/-- **`lentCaller` after the end in place**: a caller's borrow is not the ended label (one holder), and its sites are
in the caller's frames (`FrameStart.callerLent`), never at the callee's holder. -/
theorem lentCaller_endAt (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hu : s.Uniq) {k : Nat} {p : Pos}
    (hpf : p.frameOf = s₀.topIdx) (hps : s.shape p = some k) :
    ∀ m q, q.frameOf < s₀.topIdx → s₀.shape q = some m → (s.endAt k p).lent m = s₀.lent m := by
  intro m q hq hm
  have hsm : s.shape q = some m := by rw [hr.lowerShape q hq]; exact hm
  have hmk : m ≠ k := fun e => by
    subst e
    have := hu q p _ hsm hps
    subst this; omega
  rw [endAt_lent, relend_eq, if_neg hmk, hr.lentCaller m q hq hm]
  exact flatMap_ite_self _ _ _ fun x hx e => by
    have := hs₀.callerLent q m x hq hm hx
    rw [e] at this; omega

/-- **`lentCl` after the end in the closure**: the re-rooted sites keep their positions (the cells or the top frame). -/
theorem lentCl_endAt (hr : FrameRel σ s₀ ks s s') (l : Nat) (q₀ : Pos) :
    ∀ m (x : Site), x ∈ (s'.endAt l q₀).lent m →
      (∃ p, p.frameOf = s₀.topIdx ∧ x.pos = upPos ks.length p) ∨ ∃ i, i < ks.length ∧ x.pos = .bind 0 i := by
  intro m x hx
  rw [endAt_lent] at hx
  by_cases hml : m = l
  · rw [relend_eq, if_pos hml] at hx; cases hx
  · rcases (mem_relend hml).mp hx with ⟨hx, -⟩ | ⟨x₀, -, -, y, hy, rfl⟩
    · exact hr.lentCl m x hx
    · have := hr.lentCl l y hy
      rwa [relendSite_pos]

theorem site_up_inj {c : Nat} {a b : Site} (hf : a.pos.frameOf = b.pos.frameOf)
    (h : { a with pos := upPos c a.pos } = { b with pos := upPos c b.pos }) : a = b := by
  obtain ⟨ap, aπ, af⟩ := a
  obtain ⟨bp, bπ, bf⟩ := b
  simp only [Site.mk.injEq] at h ⊢
  exact ⟨upPos_inj hf h.1, h.2.1, h.2.2⟩

/-- **`lentImg` after the end in place**: a top-frame site of a held label after the end was a top-frame site of the
same label before it (a re-rooted site sits where the ended label's did, an old site of the label at the holder). -/
theorem lentImg_endAt (hr : FrameRel σ s₀ ks s s') {k : Nat} {p : Pos} (hpf : p.frameOf = s₀.topIdx) :
    ∀ m (x : Site), x.pos.frameOf = s₀.topIdx → (∃ q, (s.endAt k p).shape q = some m) → x ∈ (s.endAt k p).lent m →
      ∃ l, m = σ l := by
  intro m x hxf ⟨q, hq⟩ hx
  rw [SState.endAt_shape] at hq
  dsimp only at hq
  split at hq
  · cases hq
  · have hheld : ∃ q, s.shape q = some m := ⟨q, hq⟩
    rw [endAt_lent] at hx
    by_cases hmk : m = k
    · rw [relend_eq, if_pos hmk] at hx; cases hx
    · rcases (mem_relend hmk).mp hx with ⟨hx, -⟩ | ⟨x₀, hx₀, e, -, -, -⟩
      · exact hr.lentImg m x hxf hheld hx
      · exact hr.lentImg m x₀ (by rw [e]; exact hpf) hheld hx₀

/-- **`lentTop` after the two ends**, at corresponding holders: a kept site corresponds as before; a re-rooted site
corresponds because the holder site and the ended label's top-frame site did, and `relendSite` commutes with `upPos`.
The ended label's sites outside the top frame (in place the caller's, in the closure the cells, D211's entry fills
included where they are in the top frame) are re-rooted on each side without being compared. -/
theorem lentTop_endAt (hr : FrameRel σ s₀ ks s s') (hu : s.Uniq) {l : Nat} {p : Pos} (hpf : p.frameOf = s₀.topIdx)
    (hps : s.shape p = some (σ l)) :
    ∀ m (x : Site), x.pos.frameOf = s₀.topIdx → (∃ q, (s.endAt (σ l) p).shape q = some (σ m)) →
      (x ∈ (s.endAt (σ l) p).lent (σ m) ↔
        { x with pos := upPos ks.length x.pos } ∈ (s'.endAt l (upPos ks.length p)).lent m) := by
  intro m x hxf ⟨q, hq⟩
  rw [SState.endAt_shape] at hq
  dsimp only at hq
  split at hq
  · cases hq
  rename_i hqp
  have hheld : ∃ q, s.shape q = some (σ m) := ⟨q, hq⟩
  have hml : m ≠ l := fun e => by subst e; exact hqp (hu q p _ hq hps)
  have hσ : σ m ≠ σ l := fun e => hml (hr.inj _ _ e)
  have hheldl : ∃ q, s.shape q = some (σ l) := ⟨p, hps⟩
  rw [endAt_lent, endAt_lent, mem_relend hσ, mem_relend hml]
  constructor
  · rintro (⟨hx, e⟩ | ⟨x₀, hx₀, e, y, hy, rfl⟩)
    · exact .inl ⟨(hr.lentTop m x hxf hheld).mp hx, fun e' => e (upPos_inj (by rw [hxf, hpf]) e')⟩
    · have hyf : y.pos.frameOf = s₀.topIdx := by rw [← relendSite_pos x₀ y]; exact hxf
      have hx₀f : x₀.pos.frameOf = s₀.topIdx := by rw [e]; exact hpf
      refine .inr ⟨{ x₀ with pos := upPos ks.length x₀.pos }, (hr.lentTop m x₀ hx₀f hheld).mp hx₀, by simp [e],
        { y with pos := upPos ks.length y.pos }, (hr.lentTop l y hyf hheldl).mp hy, ?_⟩
      rw [relendSite_up]
  · rintro (⟨hx, e⟩ | ⟨x₀', hx₀', e, y', hy', hxe⟩)
    · exact .inl ⟨(hr.lentTop m x hxf hheld).mpr hx, fun e' => e (by simp [e'])⟩
    · let x₀ : Site := { x₀' with pos := p }
      have hx₀up : { x₀ with pos := upPos ks.length x₀.pos } = x₀' := by
        obtain ⟨xp, xπ, xf⟩ := x₀'
        simp only at e
        simp [x₀, e]
      have hx₀ : x₀ ∈ s.lent (σ m) := (hr.lentTop m x₀ hpf hheld).mpr (by rw [hx₀up]; exact hx₀')
      have hy'pos : y'.pos = upPos ks.length x.pos := by
        rw [← relendSite_pos x₀' y', ← hxe]
      let y : Site := { y' with pos := x.pos }
      have hyup : { y with pos := upPos ks.length y.pos } = y' := by
        obtain ⟨yp, yπ, yf⟩ := y'
        simp only at hy'pos
        simp [y, hy'pos]
      have hy : y ∈ s.lent (σ l) := (hr.lentTop l y hxf hheldl).mpr (by rw [hyup]; exact hy')
      refine .inr ⟨x₀, hx₀, rfl, y, hy, ?_⟩
      refine site_up_inj (c := ks.length) (by rw [relendSite_pos]) ?_
      rw [← relendSite_up, hx₀up, hyup]
      exact hxe

/-! ## The values and the skeleton -/

theorem endAt_valAt_away {t : SState} {L : Nat} {r q : Pos} (hqr : q ≠ r) (ψ : Future) :
    (t.endAt L r).valAt q ψ = t.valAt q (ψ.upd L (t.valAt r ψ)) := by
  by_cases hq : q ∈ t.positions
  · rw [SState.endAt_valAt t L r q hq]; simp only [if_neg hqr]
  · rw [SState.endAt_valAt_not_mem t L r q hq, SState.valAt_of_not_mem t q hq]

theorem headD_binds_getElem? (t : SState) (i : Nat) : (t.env.headD {}).binds[i]? = t.bindAt? 0 i := by
  unfold SState.bindAt?; cases t.env <;> simp

theorem cellsOf_getElem? (c : Nat) (t : SState) (i : Nat) :
    (cellsOf c t)[i]? = if i < c then (t.bindAt? 0 i).map (·.val) else none := by
  unfold cellsOf
  rw [List.getElem?_take]
  split
  · rw [List.getElem?_map, headD_binds_getElem?]
  · rfl

theorem valAt_bind_of (t : SState) {f i : Nat} {b : SBinding} (h : t.bindAt? f i = some b) : t.valAt (.bind f i) = b.val := by
  show (match t.env[f]?.bind (·.binds[i]?) with | some b => b.val | none => fun _ => .err) = b.val
  rw [show t.env[f]?.bind (·.binds[i]?) = t.bindAt? f i from rfl, h]

/-- **The cells after the closure's end** (the holder is in the closure's frame, not frame 0): each cell reads the ended
label at the holder's value, the form `lowerVal_end` asks. -/
theorem cellsOf_endAt (t : SState) (c l : Nat) (q₀ : Pos) (hq : q₀.frameOf ≠ 0) :
    cellsOf c (t.endAt l q₀) = (cellsOf c t).map fun v ψ => v (ψ.upd l (t.valAt q₀ ψ)) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, cellsOf_getElem?, cellsOf_getElem?]
  split
  · unfold SState.endAt
    rw [SState.bindAt?_mapVals]
    change Option.map _ (Option.map _ (t.bindAt? 0 i)) = _
    cases hb : t.bindAt? 0 i with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      congr 1
      funext ψ
      have hne : (Pos.bind 0 i) ≠ q₀ := fun e => hq (by rw [← e]; rfl)
      simp only [if_neg hne]
      rw [valAt_bind_of t hb]
  · rfl

/-- The caller's frames' skeleton is kept by an end (an end rewrites values only). -/
theorem envSkel_endAt (t : SState) (k : Nat) (r : Pos) (f : Nat) :
    ((t.endAt k r).env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) =
      (t.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) := by
  unfold SState.endAt SState.mapVals
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  cases t.env[f]? with
  | none => rfl
  | some fr =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.map_map, List.length_map, List.length_zipIdx,
      and_true]
    conv => rhs; rw [← List.zipIdx_map_fst 0 fr.binds, List.map_map]
    rfl

/-- **`lowerSkel` after the end in place.** -/
theorem lowerSkel_endAt (hr : FrameRel σ s₀ ks s s') (k : Nat) (r : Pos) :
    ∀ f, f < s₀.topIdx →
      ((s.endAt k r).env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) =
      (s₀.env[f]?).map (fun fr => (fr.binds.map fun b => (b.ty, b.decl), fr.temps.length)) := fun f hf => by
  rw [envSkel_endAt]; exact hr.lowerSkel f hf

/-- **`lowerVal` after the two ends**: lead30's `lowerVal_end` at the cells after the closure's end. -/
theorem lowerVal_endAt (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks)
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length) {l : Nat} (hl : σ l ∈ ks ∨ s₀.nextLoan ≤ σ l) {p : Pos}
    (hpf : p.frameOf = s₀.topIdx) (hx : ∀ ψ, s.valAt p ψ = s'.valAt (upPos ks.length p) (renF σ ψ)) :
    ∀ q, q.frameOf < s₀.topIdx → ∀ ψ,
      (s.endAt (σ l) p).valAt q ψ = s₀.valAt q (cellFuture σ ks (cellsOf ks.length (s'.endAt l (upPos ks.length p))) ψ) := by
  intro q hq ψ
  have hqp : q ≠ p := fun e => by subst e; omega
  have hup : (upPos ks.length p).frameOf ≠ 0 := by cases p <;> simp [upPos, Pos.frameOf]
  have hlen : ks.length ≤ (cellsOf ks.length s').length := by
    simp only [cellsOf, List.length_take, List.length_map]; exact Nat.le_min.mpr ⟨Nat.le_refl _, hcells⟩
  rw [endAt_valAt_away hqp, cellsOf_endAt s' _ l _ hup]
  exact lowerVal_end hr.inj hs₀ (cellsOf ks.length s') hlen hl hx hq (hr.lowerVal q hq) ψ

/-! ## The top frames -/

theorem topIdx_eq (hr : FrameRel σ s₀ ks s s') : s.topIdx = s₀.topIdx := by
  unfold SState.topIdx; rw [hr.frames.1]

/-- The top frame is the frame at `topIdx`. -/
theorem env_top (t : SState) {F : SFrame} (h : t.env.getLast? = some F) : t.env[t.topIdx]? = some F := by
  rw [List.getLast?_eq_getElem?] at h; exact h

/-- **The top frames' values correspond** through `upPos` and the renaming, at every position of the frame. -/
theorem top_valAt (hr : FrameRel σ s₀ ks s s') (q : Pos) (hq : q.frameOf = s₀.topIdx) (ψ : Future) :
    s.valAt q ψ = s'.valAt (upPos ks.length q) (renF σ ψ) := by
  obtain ⟨F, F', hF, hF', hlen, hb, htl, ht⟩ := hr.top
  have hs : s.env[s₀.topIdx]? = some F := by rw [← topIdx_eq hr]; exact env_top s hF
  have hs' : s'.env[1]? = some F' := by
    have := env_top s' hF'; unfold SState.topIdx at this; rw [hr.frames.2] at this; exact this
  cases q with
  | bind f i =>
    simp only [Pos.frameOf] at hq; subst hq
    show (match s.env[s₀.topIdx]?.bind (·.binds[i]?) with | some b => b.val | none => fun _ => .err) ψ =
      (match s'.env[1]?.bind (·.binds[i]?) with | some b => b.val | none => fun _ => .err) (renF σ ψ)
    rw [hs, hs']
    simp only [Option.bind_some]
    cases h1 : F.binds[i]? with
    | none =>
      have : F'.binds[i]? = none := by rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      rw [this]
    | some b =>
      have hi : i < F'.binds.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
      rw [List.getElem?_eq_getElem hi]
      exact (hb i b _ h1 (List.getElem?_eq_getElem hi)).2.2.2 ψ
  | temp f j =>
    simp only [Pos.frameOf] at hq; subst hq
    show (match s.env[s₀.topIdx]?.bind (·.temps[j]?) with | some v => v | none => fun _ => .err) ψ =
      (match s'.env[1]?.bind (·.temps[j]?) with | some v => v | none => fun _ => .err) (renF σ ψ)
    rw [hs, hs']
    simp only [Option.bind_some]
    cases h1 : F.temps[j]? with
    | none =>
      have : F'.temps[j]? = none := by rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      rw [this]
    | some v =>
      obtain ⟨v', h2, hv⟩ := ht j v h1
      rw [h2]; exact hv ψ

/-- A frame with each binding's and temporary's value rewritten at its position in frame `fi` (`mapVals` on one frame). -/
def mapFrame (fi : Nat) (g : Pos → SVal → SVal) (F : SFrame) : SFrame :=
  SFrame.mk (F.binds.zipIdx.map fun bi => { bi.1 with val := g (.bind fi bi.2) bi.1.val })
    (F.temps.zipIdx.map fun vi => g (.temp fi vi.2) vi.1)

theorem mapFrame_bind (fi : Nat) (g : Pos → SVal → SVal) (F : SFrame) (i : Nat) :
    (mapFrame fi g F).binds[i]? = F.binds[i]?.map fun b => { b with val := g (.bind fi i) b.val } := by
  simp [mapFrame, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  rfl

theorem mapFrame_temp (fi : Nat) (g : Pos → SVal → SVal) (F : SFrame) (j : Nat) :
    (mapFrame fi g F).temps[j]? = F.temps[j]?.map fun v => g (.temp fi j) v := by
  simp [mapFrame, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  rfl

/-- The last frame after an end at `r`: each value rewritten as `endAt` rewrites it. -/
theorem getLast?_endAt (t : SState) (k : Nat) (r : Pos) {F : SFrame} (h : t.env.getLast? = some F) :
    (t.endAt k r).env.getLast? = some (mapFrame t.topIdx
      (fun p _ ψ => if p = r then Sem.moved else t.valAt p (ψ.upd k (t.valAt r ψ))) F) := by
  rw [List.getLast?_eq_getElem?] at h ⊢
  unfold SState.endAt
  simp only [SState.mapVals, List.length_map, List.length_zipIdx, List.getElem?_map, List.getElem?_zipIdx, h,
    Option.map_some, SState.topIdx, Nat.zero_add]
  rfl

/-- **`top` after the two ends**, at corresponding holders: the holder is `moved` on both sides; every other binding and
temporary reads the ended label at the holder's value, related through the renaming (`bindRen_end`). -/
theorem top_endAt (hr : FrameRel σ s₀ ks s s') {l : Nat} {p : Pos} (hpf : p.frameOf = s₀.topIdx) :
    ∃ F F', (s.endAt (σ l) p).env.getLast? = some F ∧ (s'.endAt l (upPos ks.length p)).env.getLast? = some F' ∧
      F.binds.length = F'.binds.length ∧
      (∀ (i : Nat) b b', F.binds[i]? = some b → F'.binds[i]? = some b' → BindRen σ b b') ∧
      F'.temps.length = F.temps.length ∧
      ∀ (j : Nat) v, F.temps[j]? = some v → ∃ v', F'.temps[j]? = some v' ∧ ∀ ψ, v ψ = v' (renF σ ψ) := by
  obtain ⟨F, F', hF, hF', hlen, hb, htl, ht⟩ := hr.top
  have hti : s.topIdx = s₀.topIdx := topIdx_eq hr
  have hti' : s'.topIdx = 1 := by unfold SState.topIdx; rw [hr.frames.2]
  have hcond : ∀ q, q.frameOf = s₀.topIdx → (q = p ↔ upPos ks.length q = upPos ks.length p) := fun q hq =>
    ⟨fun e => by rw [e], fun e => upPos_inj (by rw [hq, hpf]) e⟩
  have hval : ∀ q, q.frameOf = s₀.topIdx → ∀ ψ,
      (if q = p then Sem.moved else s.valAt q (ψ.upd (σ l) (s.valAt p ψ))) =
      (if upPos ks.length q = upPos ks.length p then Sem.moved else
        s'.valAt (upPos ks.length q) ((renF σ ψ).upd l (s'.valAt (upPos ks.length p) (renF σ ψ)))) := by
    intro q hq ψ
    by_cases e : q = p
    · rw [if_pos e, if_pos ((hcond q hq).mp e)]
    · rw [if_neg e, if_neg (fun e' => e ((hcond q hq).mpr e'))]
      exact bindRen_end hr.inj (top_valAt hr q hq) (top_valAt hr p hpf) ψ
  refine ⟨_, _, getLast?_endAt _ _ _ hF, getLast?_endAt _ _ _ hF', by simp [mapFrame, hlen], ?_,
    by simp [mapFrame, htl], ?_⟩
  · intro i b b' h1 h2
    rw [mapFrame_bind] at h1 h2
    cases e1 : F.binds[i]? with
    | none => rw [e1] at h1; cases h1
    | some b₀ =>
      cases e2 : F'.binds[i]? with
      | none => rw [e2] at h2; cases h2
      | some b₀' =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        obtain ⟨hty, hdecl, hrec, -⟩ := hb i b₀ b₀' e1 e2
        refine ⟨hty, hdecl, hrec, fun ψ => ?_⟩
        rw [hti, hti']
        exact hval (.bind s₀.topIdx i) rfl ψ
  · intro j v h1
    rw [mapFrame_temp] at h1
    cases e1 : F.temps[j]? with
    | none => rw [e1] at h1; cases h1
    | some v₀ =>
      rw [e1] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      obtain ⟨v₀', e2, -⟩ := ht j v₀ e1
      refine ⟨_, by rw [mapFrame_temp, e2]; rfl, fun ψ => ?_⟩
      rw [hti, hti']
      exact hval (.temp s₀.topIdx j) rfl ψ

/-! ## The assembly -/

/-- **[End] against the frame relation** (docs/31 D212): ending a live label `l` of the closure at its holder, and its
image `σ l` in place at the corresponding holder, keeps `FrameRel`. Hypotheses: the relation; `FrameStart` at the call
(the caller's frames read nothing the callee makes; the caller's borrows lend only in the caller's frames); one holder per
label in place (`Strict.SGood.uniq`); a cell for every parameter label (D203). No invariant (P) (D211). -/
theorem frameRel_endAt (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hu : s.Uniq)
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length) {l : Nat} (hl : s'.Live l) {p : Pos}
    (hpf : p.frameOf = s₀.topIdx) (hps : s.shape p = some (σ l)) :
    FrameRel σ s₀ ks (s.endAt (σ l) p) (s'.endAt l (upPos ks.length p)) where
  inj := hr.inj
  fresh := (counters_endAt hr (σ l) l p _).1
  frames := (counters_endAt hr (σ l) l p _).2
  lowerSkel := lowerSkel_endAt hr _ _
  lowerVal := lowerVal_endAt hr hs₀ hcells (hr.topLabels l hl) hpf (top_valAt hr p hpf)
  lowerShape := lowerShape_endAt hr hpf
  top := top_endAt hr hpf
  topShape := topShape_endAt hr hpf
  clShape := clShape_endAt hr l _
  held := held_endAt hr (σ l) l p _
  lentTop := lentTop_endAt hr hu hpf hps
  lentImg := lentImg_endAt hr hpf
  lentCl := lentCl_endAt hr l _
  lentCaller := fun m q hq hm => lentCaller_endAt hr hs₀ hu hpf hps m q hq hm
  topLabels := topLabels_endAt hr l _

/-- **[End] against the frame relation, as the run ends a label** (`endLabel`, which finds the holder): from a live closure
label, the two `endLabel`s are related, and the cells clause is kept (frame 0 keeps its length). -/
theorem frameRel_endLabel (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hu : s.Uniq) (hsa : ShapeAt s)
    (hcells : ks.length ≤ (s'.env.headD {}).binds.length) {l : Nat} (hl : s'.Live l) :
    FrameRel σ s₀ ks (s.endLabel (σ l)) (s'.endLabel l) := by
  obtain ⟨q, hq⟩ := SState.holderOf_of_live hl
  obtain ⟨p, hpf, rfl, hp⟩ := holder_frame hr hu hsa hq
  rw [SState.endLabel_eq hq, SState.endLabel_eq hp]
  exact frameRel_endAt hr hs₀ hu hcells hl hpf (SState.holderOf_spec hp).2

/-! ## Ends along corresponding lists -/

theorem shapeAt_endLabel {t : SState} (h : ShapeAt t) (l : Nat) : ShapeAt (t.endLabel l) := by
  cases hh : t.holderOf l with
  | none => rw [SState.endLabel_of_none hh]; exact h
  | some r =>
    rw [SState.endLabel_eq hh]
    intro p m hp
    rw [SState.endAt_shape] at hp
    dsimp only at hp
    split at hp
    · cases hp
    · rw [SState.endAt_positions]; exact h p m hp

theorem headD_len_endLabel (t : SState) (l : Nat) :
    ((t.endLabel l).env.headD {}).binds.length = (t.env.headD {}).binds.length := by
  cases hh : t.holderOf l with
  | none => rw [SState.endLabel_of_none hh]
  | some r =>
    rw [SState.endLabel_eq hh]
    unfold SState.endAt SState.mapVals
    cases h : t.env with
    | nil => simp [h]
    | cons fr rest => simp [h, List.zipIdx_cons]

/-- **Ends along corresponding lists keep the frame relation**: ending, one by one, the closure labels of a list `L`
and in place their images, IN THE SAME ORDER, keeps `FrameRel` (and what each end needs again). The [Access] lemma's
core: what remains of it is that the two sides' rounds end corresponding labels, in label order on each side, which for
parameter labels are different orders (D211's `P3`), reconciled by commutation of ends. -/
theorem frameRel_foldEnd (hs₀ : FrameStart s₀ ks) : ∀ (L : List Nat) {s s' : SState},
    FrameRel σ s₀ ks s s' → s.Uniq → ShapeAt s → ks.length ≤ (s'.env.headD {}).binds.length →
    (∀ l ∈ L, s'.Live l) → L.Nodup →
    FrameRel σ s₀ ks ((L.map σ).foldl SState.endLabel s) (L.foldl SState.endLabel s')
  | [], _, _, hr, _, _, _, _, _ => hr
  | l :: L, s, s', hr, hu, hsa, hc, hl, hnd => by
    simp only [List.map_cons, List.foldl_cons]
    have hnd' := List.nodup_cons.mp hnd
    refine frameRel_foldEnd hs₀ L (frameRel_endLabel hr hs₀ hu hsa hc (hl l (by simp)))
      (hu.endLabel _) (shapeAt_endLabel hsa _) (by rw [headD_len_endLabel]; exact hc) (fun m hm => ?_) hnd'.2
    exact SState.live_endLabel (hl m (by simp [hm])) (fun e => hnd'.1 (e ▸ hm))

/-! ## The labels an access reaches -/

theorem frameOf_lt_of_mem {t : SState} {p : Pos} (h : p ∈ t.positions) : p.frameOf < t.env.length := by
  rw [SState.mem_positions] at h
  cases p with
  | bind f i =>
    simp only [SState.lookup, Pos.frameOf] at h ⊢
    cases e : t.env[f]? with
    | none => rw [e] at h; simp at h
    | some fr => exact (List.getElem?_eq_some_iff.1 e).1
  | temp f i =>
    simp only [SState.lookup, Pos.frameOf] at h ⊢
    cases e : t.env[f]? with
    | none => rw [e] at h; simp at h
    | some fr => exact (List.getElem?_eq_some_iff.1 e).1

/-- **The labels an access of a top-frame place reaches correspond**: in place they are exactly the images of those the
closure's access of the corresponding place reaches. A caller's label is never reached there (its sites are in the
caller's frames); a reached label is held in the top frame (`lentImg`, `topShape`), and its site corresponds (`lentTop`).
Parameter labels included (D211: an entry may have lent one at a top-frame place). So the two accesses end
corresponding SETS of labels; their ORDERS (label order on each side) differ where `σ` is not monotone (`P3`). -/
theorem reached_corr (hr : FrameRel σ s₀ ks s s') (hs₀ : FrameStart s₀ ks) (hsa : ShapeAt s) (hsa' : ShapeAt s')
    {q : Pos} (hq : q.frameOf = s₀.topIdx) (hit : List Step → Bool) (m : Nat) :
    (s.Live m ∧ s.reached q hit m = true) ↔
      ∃ l, m = σ l ∧ s'.Live l ∧ s'.reached (upPos ks.length q) hit l = true := by
  constructor
  · rintro ⟨hl, hre⟩
    obtain ⟨p, hp, hps⟩ := (SState.live_iff s m).1 hl
    simp only [SState.reached, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hre
    obtain ⟨x, hx, hxq, hxh⟩ := hre
    have hxf : x.pos.frameOf = s₀.topIdx := by rw [hxq]; exact hq
    have hpf : p.frameOf = s₀.topIdx := by
      have h1 := frameOf_lt_of_mem hp
      rw [hr.frames.1] at h1
      have h2 : p.frameOf ≤ s₀.topIdx := by unfold SState.topIdx; omega
      rcases Nat.lt_or_eq_of_le h2 with h3 | h3
      · exfalso
        have h4 : s₀.shape p = some m := by rw [← hr.lowerShape p h3]; exact hps
        rw [hr.lentCaller m p h3 h4] at hx
        have := hs₀.callerLent p m x h3 h4 hx
        omega
      · exact h3
    obtain ⟨l, rfl⟩ := hr.lentImg m x hxf ⟨p, hps⟩ hx
    have hsh : (s'.shape (upPos ks.length p)).map σ = some (σ l) := by rw [← hr.topShape p hpf]; exact hps
    obtain ⟨l', hl'⟩ : ∃ l', s'.shape (upPos ks.length p) = some l' := by
      cases e : s'.shape (upPos ks.length p) with
      | none => rw [e] at hsh; cases hsh
      | some l' => exact ⟨l', rfl⟩
    rw [hl'] at hsh
    have hll : l' = l := hr.inj _ _ (Option.some.inj hsh)
    subst hll
    refine ⟨l', rfl, (SState.live_iff s' l').2 ⟨_, hsa' _ _ hl', hl'⟩, ?_⟩
    simp only [SState.reached, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨_, (hr.lentTop l' x hxf ⟨p, hps⟩).mp hx, by simp [hxq], hxh⟩
  · rintro ⟨l, rfl, hl, hre⟩
    obtain ⟨q', -, hq's⟩ := (SState.live_iff s' l).1 hl
    obtain ⟨p, hpf, rfl⟩ := hr.clShape q' l hq's
    have hps : s.shape p = some (σ l) := by rw [hr.topShape p hpf, hq's]; rfl
    simp only [SState.reached, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hre ⊢
    obtain ⟨y, hy, hyq, hyh⟩ := hre
    refine ⟨(SState.live_iff s _).2 ⟨p, hsa p _ hps, hps⟩, { y with pos := q }, ?_, rfl, hyh⟩
    refine (hr.lentTop l { y with pos := q } hq ⟨p, hps⟩).mpr ?_
    obtain ⟨yp, yπ, yf⟩ := y
    simp only at hyq ⊢
    rw [← hyq]; exact hy

end Ochr.Meaning.Steps.Form.FrameEnd
