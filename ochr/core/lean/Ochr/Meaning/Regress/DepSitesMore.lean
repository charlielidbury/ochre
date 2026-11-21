import Ochr.Meaning.Regress.DepSites
import Ochr.Meaning.Regress.StaticLend
import Ochr.Examples.DependentFields

/-!
# Dependence within sites on two more states (docs/31 D67; kernel-checked)

Under the erased comparison (`pathKey`), beside `Regress/DepSites.lean`'s six:
* **a reborrow of a reborrow** (`let r = &a; let s = &*r; let t = &*s`), and after the middle
  borrow's end, whose re-rooting the checker's `endBorrow` agrees with (`rr_end`): holds
  (`dws_RR`, `dws_RR'`);
* **a field borrowed through a returned borrow of a pair** (`let r = IdP(&x); let s = &(*r).0`),
  the first site BELOW a root by field (`(r, [*, .0])`): holds (`dws_Pair`), the value read off
  field `0` being independent of `s`'s final content whatever the declaration;
* **a dependent pair with its index lent** (D93's `LendIndex`: `V := MkV(n : Word, x : Fin1(n))`,
  `let r = match *v { MkV(n, x) => &n }`): holds (`dws_LendIndex`).
With the reading's TYPE compared too the invariant failed at a dependent pair
(`dws_Pair_dependent_fails`, kept as the record of why the typed form was dropped): the type field
`1` is read at reads field `0`, which is lent; the value read does not.
The checker's states are read at holes of its real runs (`atHole`, the editor's Ω), and the
reference's sites are the checker's (identity renaming), kernel-checked.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr DepSitesAt uses Nats {
  def IdP (p : &(Nat × Nat)) : &(Nat × Nat) := &*p
  def RRAt (a : Nat) : Unit := (let r = &a; let s = &*r; let t = &*s; ?)
  def PairAt (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r = IdP(&x); let s = &(*r).0; ?)
}

#guard_msgs (drop warning) in
ochr DepSitesDepAt uses DepFields {
  def LendIndexAt (v : &V) : Unit := (let r = match *v { MkV(n, x) => &n, }; ?)
}

namespace Ochr.Meaning.Regress.DepSitesMore
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CallInPlace Ochr.Meaning.Regress

def atHoleIn (blk : String) (prog : Ochr.Surface.Block) (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) blk prog (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

def atHole (name : String) : List Value := atHoleIn "DepSitesAt" DepSitesAt name

/-! ## A reborrow of a reborrow

`let r = &a; let s = &*r; let t = &*s`. At the hole the checker holds `a ↦ loan_0`,
`r ↦ borrow_0 loan_1`, `s ↦ borrow_1 loan_2`, `t ↦ borrow_2 σ0` (frame `1`: the function, `a`, `r`,
`s`, `t`). The reference (identity renaming, the checker's sites): `a` reads `0`'s final content,
`r` reads `1`'s, `s` reads `2`'s, `t` holds `σ0`. Then [End 1] at `s` (`s`'s borrow ends while
`t` lives): `r` reads `2`'s final content (`1` fixed to what `s` holds), `s` is forgotten, and
`t`'s site `(s, [*])` is re-rooted through `1`'s site `(r, [*])` to `(r, [*])` (the reborrow's `*`
replaces the ended borrow's, `inContent`), as the checker's `endBorrow` does (`rr_end`). No site
path holds two `*`s. -/

def vRR : List Value := [.loan 0, .borrow 0 (.loan 1), .borrow 1 (.loan 2), .borrow 2 (.abs 0)]
#guard atHole "RRAt" == vRR
def stRR : MState := StaticLend.stateAt "RRAt" vRR 3 1

/-- The checker's sites: `0` at `a`, `1` at `(r, [*])`, `2` at `(s, [*])`; after its [End 1] at `s`,
every label is lent where the reference's `relend` lends it, `2` at `(r, [*])`. -/
theorem rr_sites : StaticLend.sameSites (Env.sitesOf stRR.env 0) [⟨.bind 1 1, [], false⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stRR.env 1) [⟨.bind 1 2, [.deref], false⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stRR.env 2) [⟨.bind 1 3, [.deref], false⟩] = true := by
  decide +kernel
theorem rr_end : StaticLend.endAgrees stRR 1 (.bind 1 3) 50 = true ∧
    StaticLend.sameSites ((StaticLend.refOf stRR.env).relend 1 (.bind 1 3) 2) [⟨.bind 1 2, [.deref], false⟩] = true := by
  decide +kernel

def SRR (S A R T U : SBinding) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => ψ 0 },
      { R with val := fun ψ => ψ 1 }, { T with val := fun ψ => ψ 2 }, { U with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 2 then some 0 else if p = .bind 1 3 then some 1 else if p = .bind 1 4 then some 2 else none,
    nextLoan := 3, lent := Env.sitesOf stRR.env }

def SRR' (S A R T U : SBinding) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => ψ 0 },
      { R with val := fun ψ => ψ 2 }, { T with val := fun _ => .moved }, { U with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 2 then some 0 else if p = .bind 1 4 then some 2 else none,
    nextLoan := 3, lent := (StaticLend.refOf stRR.env).relend 1 (.bind 1 3) }

theorem rs_RR (l i : Nat) (h : (l = 0 ∧ i = 1) ∨ (l = 1 ∧ i = 2) ∨ (l = 2 ∧ i = 3)) :
    (Env.sitesOf stRR.env l).any (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

theorem rs_RR' (l i : Nat) (h : (l = 0 ∧ i = 1) ∨ (l = 2 ∧ i = 2)) :
    ((StaticLend.refOf stRR.env).relend 1 (.bind 1 3) l).any
      (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel

variable (dm : DataModel) (Γ : List IndDecl)

/-- **A reborrow of a reborrow.** -/
theorem dws_RR (S A R T U : SBinding) (vs vt : Sem) : DepWithinSites (SRR S A R T U vs vt) := by
  apply DepSites.dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SRR]
    · rcases i with _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SRR]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 0) (rs_RR 0 1 (.inl ⟨rfl, rfl⟩))]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 1) (rs_RR 1 2 (.inr (.inl ⟨rfl, rfl⟩)))]
      · simp [SState.valAt, SRR, DepSites.agree_of_rootSited h (l := 2) (rs_RR 2 3 (.inr (.inr ⟨rfl, rfl⟩)))]
      all_goals simp [SState.valAt, SRR]
    · simp [SState.valAt, SRR]
  · rcases f with _ | _ | f <;> simp [SState.valAt, SRR]

/-- **The same after the middle borrow's end.** -/
theorem dws_RR' (S A R T U : SBinding) (vs vt : Sem) : DepWithinSites (SRR' S A R T U vs vt) := by
  apply DepSites.dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SRR']
    · rcases i with _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SRR']
      · simp [SState.valAt, SRR', DepSites.agree_of_rootSited h (l := 0) (rs_RR' 0 1 (.inl ⟨rfl, rfl⟩))]
      · simp [SState.valAt, SRR', DepSites.agree_of_rootSited h (l := 2) (rs_RR' 2 2 (.inr ⟨rfl, rfl⟩))]
      all_goals simp [SState.valAt, SRR']
    · simp [SState.valAt, SRR']
  · rcases f with _ | _ | f <;> simp [SState.valAt, SRR']


/-! ## A field borrowed through a returned borrow of a pair

`IdP (p : &(Nat × Nat)) : &(Nat × Nat) := &*p`, then `let x = (a, b); let r = IdP(&x); let s = &(*r).0`.
At the hole the checker holds `a ↦ ⊥`, `b ↦ ⊥`, `x ↦ lent_1 loan_1` (a fill over `1`, the label the
call reserved, main's D99), `r ↦ borrow_1 (loan_3, σ1)`, `s ↦ borrow_3 σ0` (frame `1`: the function, `a`, `b`, `x`,
`r`, `s`). The reference (identity renaming, the checker's sites): `x` reads a function of `1`'s
final content (`callOf`'s `.ref` row), `r` reads the pair whose field `0` is `3`'s final content
and whose field `1` is `σ1`'s meaning (`ctorM`: a constructor value describes itself, its element
whatever the fields give), `s` holds `σ0`. `3` is lent at `(r, [*, .0])`, BELOW the root: a read of
`r` at a path whose first field is `.1` is incomparable with it, and reads field `1` whatever `3`'s
final content is, whatever the declaration (`follow_dat_off`; the type it is read at may read field `0`, which the
invariant does not compare). -/

def vP : List Value := [.bot, .bot, .gloan 1 (.loan 1),
  .borrow 1 (.ind "Pair" 0 ⟨"Mk"⟩ [.tNat, .tNat] [.loan 3, .abs 1]), .borrow 3 (.abs 0)]
#guard atHole "PairAt" == vP
def stP : MState := StaticLend.stateAt "PairAt" vP 4 2

/-- The checker's sites: `1` fills `x`; `3` is lent at `(r, [*, .0])`. -/
theorem pair_sites : StaticLend.sameSites (Env.sitesOf stP.env 1) [⟨.bind 1 3, [], true⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stP.env 3) [⟨.bind 1 4, [.deref, .field ⟨"Pair", 0, 0, ""⟩], false⟩] = true := by
  decide +kernel

noncomputable def SPr (S A B X R T : SBinding) (fx : Sem → Sem) (ps : Rec) (v1 vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun _ => .moved },
      { B with val := fun _ => .moved }, { X with val := fun ψ => fx (ψ 1) },
      { R with val := fun ψ => .dat "Pair" ps 0 [ψ 3, v1] }, { T with val := fun _ => vt }] []],
    shape := fun p => if p = .bind 1 4 then some 1 else if p = .bind 1 5 then some 3 else none,
    nextLoan := 4, lent := Env.sitesOf stP.env }

/-- **Off field `0`, the value read off a two-field constructor value does not read field `0`**,
whatever the declaration (the value read, `readV`, by the value alone; its type at field `1` may). -/
theorem follow_dat_off (n : String) (ps : Rec) (v1 : Sem) (a a' : Sem) :
    ∀ (steps : List Step), (pathKey steps).head? ≠ none → (pathKey steps).head? ≠ some (0, 0) →
      readV (.dat n ps 0 [a, v1]) steps = readV (.dat n ps 0 [a', v1]) steps
  | [], h, _ => absurd rfl h
  | .deref :: ss, h1, h2 => by
    simp only [readV, stepV, Option.bind_some]
    exact follow_dat_off n ps v1 a a' ss h1 h2
  | .proj i :: ss, h1, h2 => by
    cases i with
    | zero => exact absurd rfl h2
    | succ i =>
      cases i with
      | zero => simp [readV, stepV, fieldV]
      | succ i => simp [readV, stepV, fieldV]
  | .field g :: ss, h1, h2 => by
    simp only [readV, stepV]
    by_cases hn : ¬ (n = g.ty ∧ n ≠ "Nat")
    · simp [hn]
    have hn : n = g.ty ∧ n ≠ "Nat" := Classical.byContradiction hn
    rw [if_pos hn, if_pos hn]
    by_cases hc : 0 = g.ctor
    · have hi : g.idx ≠ 0 := fun hi => h2 (by simp [pathKey, Step.key, ← hc, hi])
      rcases g with ⟨gt, gc, gi, gn⟩
      simp only at hc hi
      subst hc
      rcases gi with _ | _ | gi
      · exact absurd rfl hi
      · simp [fieldV]
      · simp [fieldV]
    · simp [fieldV, hc]

/-- A path whose key is not comparable with `[.0]`'s starts with another field. -/
theorem off_key00 {steps π : List Step} (hπ : pathKey π = [(0, 0)]) (hd : dataHit steps π = false) :
    (pathKey steps).head? ≠ none ∧ (pathKey steps).head? ≠ some (0, 0) := by
  simp only [dataHit, hπ, Bool.or_eq_false_iff] at hd
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have : pathKey steps = [] := by
      cases hk : pathKey steps with
      | nil => rfl
      | cons _ _ => rw [hk] at hn; cases hn
    rw [this] at hd; simp at hd
  · cases hk : pathKey steps with
    | nil => rw [hk] at hn; cases hn
    | cons k0 rest =>
      rw [hk] at hn hd
      simp only [List.head?_cons, Option.some.injEq] at hn
      subst hn
      simp [List.isPrefixOf] at hd

theorem rs_P (l i : Nat) (h : l = 1 ∧ i = 3) :
    (Env.sitesOf stP.env l).any (fun x => decide (x.pos = .bind 1 i) && (pathKey x.path).isEmpty) = true := by
  obtain ⟨rfl, rfl⟩ := h; decide +kernel

theorem siteP3 : (Env.sitesOf stP.env 3).any
    (fun x => decide (x.pos = .bind 1 4) && pathKey x.path == [(0, 0)]) = true := by
  decide +kernel

/-- **A field borrowed through a returned borrow of a pair**: the site below the root. -/
theorem dws_Pair (S A B X R T : SBinding) (fx : Sem → Sem) (ps : Rec) (v1 vs vt : Sem) :
    DepWithinSites (SPr S A B X R T fx ps v1 vs vt) := by
  intro p steps ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SPr]
    · rcases i with _ | _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
      · have h2 : ψ 1 = ψ' 1 := Classical.byContradiction fun hne => by
          have := (h 1 hne).2
          rw [DepSites.reached_of_rootSited (s := SPr S A B X R T fx ps v1 vs vt) (p := .bind 1 3) (l := 1)
            (rs_P 1 3 ⟨rfl, rfl⟩) steps] at this; cases this
        simp [SState.valAt, SPr, h2]
      · by_cases h3 : ψ 3 = ψ' 3
        · simp [SState.valAt, SPr, h3]
        · have hr := (h 3 h3).2
          obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp siteP3
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxp
          have hd : dataHit steps x.path = false := by
            simp only [SState.reached, SPr, List.any_eq_false] at hr
            have := hr x hx
            simp only [hxp.1, Bool.and_eq_true, decide_eq_true_eq, true_and, Bool.not_eq_true] at this
            exact this
          obtain ⟨h1, h2⟩ := off_key00 hxp.2 hd
          simp only [SState.valAt, SPr, SState.tyAt]
          exact follow_dat_off "Pair" ps v1 _ _ steps h1 h2
      · simp [SState.valAt, SPr]
      · simp [SState.valAt, SPr]
    · simp [SState.valAt, SPr]
  · rcases f with _ | _ | f <;> simp [SState.valAt, SPr]

theorem sitesP3_all : (Env.sitesOf stP.env 3).all
    (fun x => !decide (x.pos = .bind 1 4) || pathKey x.path == [(0, 0)]) = true := by
  decide +kernel

/-- The invariant with the reading's type compared too (its form before the lead's decision on the
dependent pair, docs/31 D67). -/
def DepWithinSitesT (s : SState) : Prop :=
  ∀ (p : Pos) (steps : List Step) (ψ ψ' : Future),
    (∀ l, ψ l ≠ ψ' l → s.Live l ∧ s.reached p (dataHit steps) l = false) →
    Sem.follow dm Γ (s.tyAt p) (s.valAt p ψ) steps = Sem.follow dm Γ (s.tyAt p) (s.valAt p ψ') steps

/-- **With the type compared, for a dependent pair the reading's TYPE reads the lent field**: where the type field `1` is read
at depends on field `0` (`fieldTy` reading the earlier fields, as a dependent declaration's does),
two typed futures differing only at `3` (lent at `(r, [*, .0])`, incomparable with `[*, .1]`) read
field `1` at different types. The value read is the same (`dws_Pair`). The record of why the
invariant compares values only. -/
theorem dws_Pair_dependent_fails (S A B X R T : SBinding) (fx : Sem → Sem) (ps : Rec) (v1 vs vt : Sem)
    (x y : Sem)
    (hdep : Sem.follow dm Γ ((SPr S A B X R T fx ps v1 vs vt).tyAt (.bind 1 4)) (.dat "Pair" ps 0 [x, v1])
        [.deref, .field ⟨"Pair", 0, 1, ""⟩] ≠
      Sem.follow dm Γ ((SPr S A B X R T fx ps v1 vs vt).tyAt (.bind 1 4)) (.dat "Pair" ps 0 [y, v1])
        [.deref, .field ⟨"Pair", 0, 1, ""⟩]) :
    ¬ DepWithinSitesT dm Γ (SPr S A B X R T fx ps v1 vs vt) := by
  intro h
  have := h (.bind 1 4) [.deref, .field ⟨"Pair", 0, 1, ""⟩] (fun l => if l = 3 then x else .err)
    (fun l => if l = 3 then y else .err) (fun l hl => ?_)
  · have e1 : (SPr S A B X R T fx ps v1 vs vt).valAt (.bind 1 4) (fun l => if l = 3 then x else .err)
        = .dat "Pair" ps 0 [x, v1] := by simp [SState.valAt, SPr]
    have e2 : (SPr S A B X R T fx ps v1 vs vt).valAt (.bind 1 4) (fun l => if l = 3 then y else .err)
        = .dat "Pair" ps 0 [y, v1] := by simp [SState.valAt, SPr]
    rw [e1, e2] at this
    exact hdep this
  · by_cases hl3 : l = 3
    · subst hl3
      refine ⟨?_, ?_⟩
      · rw [SState.live_iff]
        exact ⟨.bind 1 5, by simp [SPr, SState.positions, List.range'], by simp [SPr]⟩
      · simp only [SState.reached, SPr, List.any_eq_false]
        intro z hz hzr
        have hall := List.all_eq_true.mp sitesP3_all z hz
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hzr
        simp only [hzr.1, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hall
        have h2 := hzr.2
        have hk : pathKey [Step.deref, .field ⟨"Pair", 0, 1, ""⟩] = [(0, 1)] := rfl
        rw [dataHit, hall, hk] at h2
        revert h2; decide
    · simp [hl3] at hl

/-! ## A dependent pair with its index lent (D93's `LendIndex`)

`V := MkV(n : Word, x : Fin1(n))`, `x`'s type reading `n`; `let r = match *v { MkV(n, x) => &n }`.
At the hole the checker holds the parameter's cell `loan_0` (frame `0`), `v ↦ borrow_0 MkV(loan_1, σ2)`
and `r ↦ borrow_1 σ1` (frame `1`: the function, `v`, `r`). The reference (identity renaming, the
checker's sites): the cell reads `0`'s final content, `v` reads the constructor value whose field
`0` is `1`'s final content, `r` holds `σ1`. `1` is lent at `(v, [*, .0])`: reading `v` at `x`
reads `σ2`'s meaning whatever the index's final content is, though the type `x` is read at reads it. -/

def vLI : List Value := [.loan 0, .borrow 0 (.ind "V" 0 ⟨"MkV"⟩ [] [.loan 1, .abs 2]), .borrow 1 (.abs 1)]
#guard atHoleIn "DepSitesDepAt" DepSitesDepAt "LendIndexAt" == vLI

/-- The checker's state at the hole: the cell in frame `0`, the function, `v`, `r` in frame `1`. -/
def stLI : MState :=
  { env := #[{ binds := #[({ hint := ⟨"cell"⟩, ty := none, val := .loan 0 } : Binding)] },
      { binds := #[({ hint := ⟨"LendIndexAt"⟩, ty := none, val := .gfn "LendIndexAt" } : Binding),
        { hint := ⟨"v"⟩, ty := none, val := .borrow 0 (.ind "V" 0 ⟨"MkV"⟩ [] [.loan 1, .abs 2]) },
        { hint := ⟨"r"⟩, ty := none, val := .borrow 1 (.abs 1) }] }],
    nextLoan := 2, absTy := Array.replicate 3 .tNat, absDecl := Array.replicate 3 .other, nextAbs := 3 }

theorem li_sites : StaticLend.sameSites (Env.sitesOf stLI.env 0) [⟨.bind 0 0, [], false⟩] = true ∧
    StaticLend.sameSites (Env.sitesOf stLI.env 1) [⟨.bind 1 1, [.deref, .field ⟨"V", 0, 0, ""⟩], false⟩] = true := by
  decide +kernel

theorem rsLI0 : (Env.sitesOf stLI.env 0).any (fun x => decide (x.pos = .bind 0 0) && (pathKey x.path).isEmpty) = true := by
  decide +kernel

theorem siteLI1 : (Env.sitesOf stLI.env 1).any
    (fun x => decide (x.pos = .bind 1 1) && pathKey x.path == [(0, 0)]) = true := by
  decide +kernel

noncomputable def SLI (C S Vb R : SBinding) (ps : Rec) (vx vs vr : Sem) : SState :=
  { env := [SFrame.mk [{ C with val := fun ψ => ψ 0 }] [],
      SFrame.mk [{ S with val := fun _ => vs }, { Vb with val := fun ψ => .dat "V" ps 0 [ψ 1, vx] },
        { R with val := fun _ => vr }] []],
    shape := fun p => if p = .bind 1 1 then some 0 else if p = .bind 1 2 then some 1 else none,
    nextLoan := 2, lent := Env.sitesOf stLI.env }

/-- **A dependent pair with its index lent**: the value read at the dependent field does not read
the lent index. -/
theorem dws_LendIndex (C S Vb R : SBinding) (ps : Rec) (vx vs vr : Sem) :
    DepWithinSites (SLI C S Vb R ps vx vs vr) := by
  intro p steps ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · rcases i with _ | i
      · have h0 : ψ 0 = ψ' 0 := Classical.byContradiction fun hne => by
          have := (h 0 hne).2
          rw [DepSites.reached_of_rootSited (s := SLI C S Vb R ps vx vs vr) (p := .bind 0 0) (l := 0)
            rsLI0 steps] at this; cases this
        simp [SState.valAt, SLI, h0]
      · simp [SState.valAt, SLI]
    · rcases i with _ | _ | _ | i
      · simp [SState.valAt, SLI]
      · by_cases h1 : ψ 1 = ψ' 1
        · simp [SState.valAt, SLI, h1]
        · have hr := (h 1 h1).2
          obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp siteLI1
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxp
          have hd : dataHit steps x.path = false := by
            simp only [SState.reached, SLI, List.any_eq_false] at hr
            have := hr x hx
            simp only [hxp.1, Bool.and_eq_true, decide_eq_true_eq, true_and, Bool.not_eq_true] at this
            exact this
          obtain ⟨hn, hk⟩ := off_key00 hxp.2 hd
          simp only [SState.valAt, SLI, SState.tyAt]
          exact follow_dat_off "V" ps vx _ _ steps hn hk
      · simp [SState.valAt, SLI]
      · simp [SState.valAt, SLI]
    · simp [SState.valAt, SLI]
  · rcases f with _ | _ | f <;> simp [SState.valAt, SLI]

end Ochr.Meaning.Regress.DepSitesMore
