import Ochr.Meaning.Strict.Fund
import Ochr.Meaning.DataModel.ReadMember
import Ochr.Meaning.DataModel.Program

/-!
# "Well typed inside": a value with a meaning is hereditarily well typed (the strict type formers' payoff)

The checker compares values untyped; the model is typed. Conversion's soundness (the rules trial,
`origin/rules-trial`, `Rules/SoundT.lean`) needs the values compared to be HEREDITARILY well typed:
each part a type former reads is typed at the type the former reads it at. Since the type formers
are strict (`Value.lean`: `EqOk`, `paramsOk`; `Run.lean`: `PiOk`, `CapsOk`), this is not carried as
an invariant: it follows from the value having a meaning (`hwt_of_fit`).

`HWT K ρ φ h T v` (the trial's `Rules/Typed.lean`, adapted):
* the meaning is read at an explicit hint `h` (the hint the former reads the part at), and the
  head condition is `Fit`: `moved`, a member of `T`, or, at the error type, a type value with a level
  (the fundamental lemma's error-type escape, for types the bounded model has no universe for);
* an `Eq`'s type is typed by "has a level" (`HWT (.plain err) err A`), not at a universe (the trial's
  advice, accepted by the orchestrator: no universe holds a level-3 type);
* a constructor value's recorded parameters are not asked (no proof uses them); its type is a data
  code at its record (`T.dataCode?`); each field is read at the hint its declaration (found by name,
  as the value's meaning finds it) gives it, and typed at the type the READ gives it
  (`DataModel.readTy`, at the type's declaration and the value's record: no declaration is looked
  up for the type, so no coherence between the two is asked);
* code is excepted: a closure's and a Π-closure's captures are typed, their code is not; a sealed
  program only fits.

The lemma's one side condition (`NoProp`, the trial's exception (b)): no constructor value of a
`Prop` declaration (it means `⋆`; the checker's D42 invariant). The trial's exception (c), a data
code off the program's declarations, is gone with the read typed by the type (`DataModel.readTy`): a field
of a member of ANY data code fits the type the read gives it. What still reads the program's
declarations is the MEANING of a value (a checker value names its declaration by string).
-/

namespace Ochr.Meaning.Strict
open Ochr.Meaning Ochr.Meaning.DataModel

open Classical

/-- A meaning fits a type: `moved`, a member, or (at the error type) a type value with a level. -/
def Fit (R : DataRead) (T : TyM) (s : Sem) : Prop :=
  s = .moved ∨ s ∈ₛ[R] T ∨ (T = TyM.err ∧ ∃ X, s = .ty X ∧ X.level.isSome = true)

/-- A value no type former reads parts of. -/
def _root_.Ochr.Value.formerFree : Value → Bool
  | .succ _ | .tEq .. | .tInd .. | .ind .. | .tRef _ | .borrow .. | .gloan .. | .sealed _
  | .clo .. | .tPi .. => false
  | _ => true

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A recorded type, as `capsTys` reads it. -/
noncomputable def capTy (T : Value) : TyM := (meanV K ρ φ (.plain TyM.err) T).asTy

mutual
/-- **Hereditarily well typed**: `v` read at the hint `h` fits `T`, and each part a type former reads
is hereditarily well typed at the hint and the type the former reads it at. -/
inductive HWT : TyS → TyM → Value → Prop
  | atom {h : TyS} {T : TyM} {v : Value} : v.formerFree = true → Fit K.dm.read T (meanV K ρ φ h v) → HWT h T v
  | succ {h : TyS} {T : TyM} {a : Value} : Fit K.dm.read T (meanV K ρ φ h (.succ a)) →
      HWT (.plain TyM.nat) TyM.nat a → HWT h T (.succ a)
  /-- an `Eq`'s type has a level, its sides are at it -/
  | tEq {h : TyS} {T : TyM} {A a b : Value} : Fit K.dm.read T (meanV K ρ φ h (.tEq A a b)) →
      HWT (.plain TyM.err) TyM.err A →
      HWT (.plain (capTy K ρ φ A)) (capTy K ρ φ A) a → HWT (.plain (capTy K ρ φ A)) (capTy K ρ φ A) b →
      HWT h T (.tEq A a b)
  /-- an inductive type's arguments at its parameter types -/
  | tInd {h : TyS} {T : TyM} {n : String} {args : List Value} {d : IndDecl} :
      Fit K.dm.read T (meanV K ρ φ h (.tInd n args)) → K.Γ.find? (·.name == n) = some d →
      HWTParams d 0 [] args → HWT h T (.tInd n args)
  /-- a constructor value of a data declaration `d` (its meaning's), at a data code of `d'` at its
  record `r`: each field read at `d`'s field type as hint, typed at the type the read gives it -/
  | ind {h : TyS} {T : TyM} {t : String} {c : Nat} {hh : Hint} {ps fs : List Value} {d d' : IndDecl} {r : Rec} :
      Fit K.dm.read T (meanV K ρ φ h (.ind t c hh ps fs)) → K.Γ.find? (·.name == t) = some d →
      (d.sort == 0) = false → T.dataCode? = some (d', r) → HWTFields d d' r c 0 [] fs →
      HWT h T (.ind t c hh ps fs)
  /-- `&A` means `A`'s meaning (read at no hint) -/
  | tRef {h : TyS} {T : TyM} {A : Value} : HWT (.plain TyM.err) T A → HWT h T (.tRef A)
  | borrow {h : TyS} {T : TyM} {l : Nat} {w : Value} : HWT h T w → HWT h T (.borrow l w)
  | gloan {h : TyS} {T : TyM} {l : Nat} {w : Value} : HWT h T w → HWT h T (.gloan l w)
  /-- code: a sealed program only fits -/
  | sealed {h : TyS} {T : TyM} {t : Term} : Fit K.dm.read T (meanV K ρ φ h (.sealed t)) → HWT h T (.sealed t)
  /-- code: a closure's captures are typed, its code is not -/
  | clo {h : TyS} {T : TyM} {cs : List Value} {t : Term} {rd : List (DeclInfo × Value)} :
      Fit K.dm.read T (meanV K ρ φ h (.clo cs t rd)) → HWTCaps cs rd → HWT h T (.clo cs t rd)
  | tPi {h : TyS} {T : TyM} {cs : List Value} {t : Term} {rd : List (DeclInfo × Value)} :
      Fit K.dm.read T (meanV K ρ φ h (.tPi cs t rd)) → HWTCaps cs rd → HWT h T (.tPi cs t rd)

/-- Parameters, each at its parameter type at the earlier ones. -/
inductive HWTParams : IndDecl → Nat → List Sem → List Value → Prop
  | nil {d : IndDecl} {i : Nat} {e : List Sem} : HWTParams d i e []
  | cons {d : IndDecl} {i : Nat} {e : List Sem} {v : Value} {vs : List Value} :
      HWT (.plain (K.dm.paramTy d i e)) (K.dm.paramTy d i e) v →
      HWTParams d (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.paramTy d i e)) v]) vs →
      HWTParams d i e (v :: vs)

/-- Fields, each read at `d`'s field type at the record and the earlier fields, and typed at the
type the read gives it in a value of `d'` (none: nothing asked, a junk leaf). -/
inductive HWTFields : IndDecl → IndDecl → Rec → Nat → Nat → List Sem → List Value → Prop
  | nil {d d' : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} : HWTFields d d' r c i e []
  | cons {d d' : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {v : Value} {vs : List Value} :
      (∀ U, K.dm.readTy K.Γ d' r c i e (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) v) = some U →
        HWT (.plain (K.dm.fieldTyR d r c i e)) U v) →
      HWTFields d d' r c (i + 1) (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) v]) vs →
      HWTFields d d' r c i e (v :: vs)

/-- Captures, each at its recorded type (read at no hint, as `capsVals` reads it). -/
inductive HWTCaps : List Value → List (DeclInfo × Value) → Prop
  -- the readings may run on past the captures (a stuck block's parameters', docs/31 D137): not read
  | nil {rd : List (DeclInfo × Value)} : HWTCaps [] rd
  | cons {v : Value} {vs : List Value} {dI : DeclInfo} {T : Value} {rd : List (DeclInfo × Value)} :
      HWT (.plain TyM.err) (capTy K ρ φ T) v → HWTCaps vs rd → HWTCaps (v :: vs) ((dI, T) :: rd)
end

mutual
/-- **The side condition** (the trial's exception (b)): no constructor value of a `Prop` declaration
(outside code). -/
def NoProp : Value → Prop
  | .succ a => NoProp a
  | .tEq A a b => NoProp A ∧ NoProp a ∧ NoProp b
  | .tInd _ args => NoPropL args
  | .ind t _ _ _ fs => (∀ d, K.Γ.find? (·.name == t) = some d → d.sort ≠ 0) ∧ NoPropL fs
  | .tRef A => NoProp A
  | .borrow _ w => NoProp w
  | .gloan _ w => NoProp w
  | .clo cs _ _ => NoPropL cs
  | .tPi cs _ _ => NoPropL cs
  | _ => True
termination_by structural v => v

def NoPropL : List Value → Prop
  | [] => True
  | v :: vs => NoProp v ∧ NoPropL vs
termination_by structural vs => vs
end

end
/-! ## What fits: the facts about meanings the lemma uses -/

section
variable {dm : DataModel}

/-- A type value that is a member of a type has a level (members of the universes are typed codes;
no data element is a type value). -/
theorem ty_mem_level {X T : TyM} (h : Sem.ty X ∈ₛ[dm.read] T) : X.level.isSome = true := by
  have hd : ∀ (d : IndDecl) (r : Rec) (A : Type) (a : A), dm.read.read d r A a ≠ .ty X := by
    intro d r A a ha
    change dm.readFn d r A a = _ at ha
    unfold DataModel.readFn at ha
    split at ha
    · have hm : dm.Mem d r (.ty X) := (dm.mem_iff_meanC d r _).2 ⟨_, ha⟩
      obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
      cases he
    · cases ha
  have h0 : ∀ {A : Type} (c : Code0 A) (a : A), c.enc dm.read a ≠ .ty X := by
    intro A c a
    cases c <;> first | exact hd _ _ _ a | exact a.elim | simp [Code0.enc]
  have h1 : ∀ {A : Type 1} (c : Code1 A) (a : A), c.enc dm.read a = .ty X → X.level.isSome = true := by
    intro A c a ha
    cases c with
    | lift A c => exact absurd ha (h0 c a.down)
    | univ0 => simp only [Code1.enc, Sem.ty.injEq] at ha; subst ha; rfl
    | univ1 =>
      obtain ⟨B, c, hc⟩ := a
      simp only [Code1.enc, Sem.ty.injEq] at ha; subst ha
      simp [TyM.level, hc]
    | pi C t => simp [Code1.enc] at ha
  cases T with
  | t0 A c => obtain ⟨a, ha⟩ := h; exact absurd ha (h0 c a)
  | t1 A c => obtain ⟨a, ha⟩ := h; exact h1 c a ha
  | t2 A c =>
    obtain ⟨a, ha⟩ := h
    cases c with
    | lift A c => exact h1 c a.down ha
    | univ2 =>
      obtain ⟨B, c, hc⟩ := a
      simp only [Code2.enc, Sem.ty.injEq] at ha; subst ha
      simp [TyM.level, hc]
    | pi C t => simp [Code2.enc] at ha

/-- The error type value fits nothing. -/
theorem ty_err_not_fit {T : TyM} : ¬ Fit dm.read T (.ty TyM.err) := by
  rintro (h | h | ⟨-, X, hX, hl⟩)
  · cases h
  · have := ty_mem_level h; simp [TyM.err, TyM.level, Code0.level] at this
  · cases hX; simp [TyM.err, TyM.level, Code0.level] at hl

/-- The error value fits nothing. -/
theorem err_not_fit {T : TyM} : ¬ Fit dm.read T .err := by
  rintro (h | h | ⟨-, X, hX, -⟩)
  · cases h
  · have := mem_whole dm.read_wholeFields h; simp [Sem.whole] at this
  · cases hX

/-- A meaning read as a type with a level is a type value. -/
theorem ty_of_asTy_level {s : Sem} (h : s.asTy.level.isSome = true) : ∃ X, s = .ty X ∧ X.level.isSome = true := by
  cases s with
  | ty X => exact ⟨X, rfl, h⟩
  | _ => simp [Sem.asTy, TyM.err, TyM.level, Code0.level] at h

/-- A number's reading is the number. -/
theorem eq_of_asNat {x : Sem} {n : Nat} (h : x.asNat = some n) : x = .el0 Nat n := by
  unfold Sem.asNat Sem.as at h
  split at h
  · rename_i B b
    split at h
    · rename_i hB; subst hB; cases h; rfl
    · cases h
  · cases h

/-- `S` of a meaning fits only where the meaning is a number. -/
theorem succ_fit {T : TyM} {x : Sem} (h : Fit dm.read T x.succ) : x ∈ₛ[dm.read] TyM.nat := by
  unfold Sem.succ at h
  cases hx : x.asNat with
  | some n => rw [eq_of_asNat hx]; exact ⟨n, rfl⟩
  | none =>
    rw [hx] at h
    simp only at h
    by_cases hw : x.whole
    · rw [if_pos hw] at h; exact absurd h err_not_fit
    · rw [if_neg hw] at h
      rcases h with h | h | ⟨-, X, hX, -⟩
      · cases h
      · have := mem_whole dm.read_wholeFields h
        simp only [Sem.whole, List.mem_singleton, forall_eq] at this
        exact absurd this hw
      · cases hX

/-- No member of the error type, and no constructor value of it. -/
theorem tyIn_err (P : IndDecl → Rec → Prop) : TyIn dm P TyM.err := by
  intro d r n c gs h; obtain ⟨a, _⟩ := h; exact a.elim

theorem tyIn_nat (P : IndDecl → Rec → Prop) : TyIn dm P TyM.nat := by
  intro d r n c gs _ h; cases h

end
/-! ## Fields and parameters, one by one -/

section
variable {dm : DataModel}

/-- Parameters `ps`, from index `i` after the earlier `e`, are members of their parameter types. -/
def POk (dm : DataModel) (d : IndDecl) (i : Nat) (e ps : List Sem) : Prop :=
  ∀ j v, ps[j]? = some v → v ∈ₛ[dm.read] dm.paramTy d (i + j) (e ++ ps.take j)

theorem pOk_of_paramsOk {d : IndDecl} {ps : List Sem} (h : paramsOk dm d ps) : POk dm d 0 [] ps := by
  intro j v hv; simpa using h j v hv

theorem POk.cons {d : IndDecl} {i : Nat} {e : List Sem} {m : Sem} {ms : List Sem} (h : POk dm d i e (m :: ms)) :
    m ∈ₛ[dm.read] dm.paramTy d i e ∧ POk dm d (i + 1) (e ++ [m]) ms := by
  refine ⟨by simpa using h 0 m rfl, fun j v hv => ?_⟩
  have := h (j + 1) v (by simpa using hv)
  rw [show i + 1 + j = i + (j + 1) by omega, List.append_assoc]
  simpa [List.take_succ_cons] using this

/-- Fields `fs`, from index `i` after the earlier `e`, are members of the types the read gives them
in a value of `d'` at `r`. -/
def FOk (dm : DataModel) (Γ : List IndDecl) (d' : IndDecl) (r : Rec) (c i : Nat) (e fs : List Sem) : Prop :=
  ∀ j f, fs[j]? = some f → ∀ U, dm.readTy Γ d' r c (i + j) (e ++ fs.take j) f = some U → f ∈ₛ[dm.read] U

theorem FOk.cons {Γ : List IndDecl} {d' : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {m : Sem} {ms : List Sem}
    (h : FOk dm Γ d' r c i e (m :: ms)) :
    (∀ U, dm.readTy Γ d' r c i e m = some U → m ∈ₛ[dm.read] U) ∧ FOk dm Γ d' r c (i + 1) (e ++ [m]) ms := by
  refine ⟨fun U hU => h 0 m rfl U (by simpa using hU), fun j v hv U hU => ?_⟩
  refine h (j + 1) v (by simpa using hv) U ?_
  rw [show i + (j + 1) = i + 1 + j by omega]
  simpa [List.take_succ_cons] using hU

/-- **A member's fields fit the types the read gives them** (`DataModel.fits_readTy`), whatever the
data code: no declaration is found by name. -/
theorem fOk_of_mem {Γ : List IndDecl} {d' : IndDecl} {r : Rec} {n : String} {c : Nat} {gs : List Sem}
    (hm : dm.Mem d' r (.dat n r c gs)) : FOk dm Γ d' r c 0 [] gs := by
  intro j f hf U hU
  obtain ⟨⟨c', hc'⟩, fs, he, hfits⟩ := (DataLib.mem_iff dm.sig d' r _).1 hm
  simp only [Sem.dat.injEq] at he
  obtain ⟨-, -, hc, rfl⟩ := he
  subst hc
  have hfit := DataModel.fitsM_get dm.sig d' r c _ 0 [] gs hfits j f hf
  simp only [Nat.zero_add, List.nil_append] at hfit hU
  rw [dm.readTy_fit hfit] at hU
  exact dm.fits_readTy hfit hU

end

/-! ## The strict formers' meanings, taken apart -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem meanV_tEq' (h : TyS) (A a b : Value) : meanV K ρ φ h (.tEq A a b) =
    if EqOk K.dm.read (meanV K ρ φ (.plain .err) A) (meanV K ρ φ (.plain (capTy K ρ φ A)) a)
        (meanV K ρ φ (.plain (capTy K ρ φ A)) b) then
      .ty (TyM.prop (meanV K ρ φ (.plain (capTy K ρ φ A)) a = meanV K ρ φ (.plain (capTy K ρ φ A)) b))
    else .ty TyM.err := rfl

theorem meanV_clo' (h : TyS) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) :
    meanV K ρ φ h (.clo cs t rd) =
      if CapsOk K.dm.read (capsVals K ρ φ cs) (capsTys K ρ φ rd) then
        (match runT K ρ φ false (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd))) with
        | some ((v, _), _) => v
        | none => .err)
      else .err := rfl

theorem meanV_tPi' (h : TyS) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) :
    meanV K ρ φ h (.tPi cs t rd) =
      if CapsOk K.dm.read (capsVals K ρ φ cs) (capsTys K ρ φ rd) then
        (match runT K ρ φ false (.plain TyM.err) t (stateOf 0 (capsState (capsVals K ρ φ cs) (capsTys K ρ φ rd))) with
        | some ((v, _), _) => .ty v.asTy
        | none => .ty TyM.err)
      else .ty TyM.err := rfl

/-- `D(ā)`'s meaning: the error type, or its arguments are typed. -/
theorem meanV_tInd_cases (h : TyS) (n : String) (args : List Value) :
    meanV K ρ φ h (.tInd n args) = .ty TyM.err ∨
      ∃ d, K.Γ.find? (·.name == n) = some d ∧ paramsOk K.dm d (meanParams K ρ φ d 0 [] args) := by
  simp only [meanV]
  split
  · rename_i d hd
    by_cases hp : paramsOk K.dm d (meanParams K ρ φ d 0 [] args)
    · exact .inr ⟨d, hd, hp⟩
    · rw [if_neg hp]; exact .inl rfl
  · exact .inl rfl

/-- A constructor value's meaning: `err`, or its declaration's tree (or `⋆`) at the record it reads. -/
theorem meanV_ind_cases (h : TyS) (t : String) (c : Nat) (hh : Hint) (ps fs : List Value) :
    meanV K ρ φ h (.ind t c hh ps fs) = .err ∨ ∃ d r, K.Γ.find? (·.name == t) = some d ∧
      meanV K ρ φ h (.ind t c hh ps fs) =
        (if d.sort == 0 then .proof else DataModel.ctorR d r c (meanFields K ρ φ d r c 0 [] fs)) := by
  simp only [meanV]
  split
  · rename_i d hd
    split
    · rename_i r _
      exact .inr ⟨d, r, hd, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

end

/-! ## The payoff: a value whose meaning fits is hereditarily well typed -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem fit_of_side {R : DataRead} {T : TyM} {v : Sem} (h : SideOk R T v) : Fit R T v :=
  h.elim .inl fun h => .inr (.inl h)

mutual
/-- **"Well typed inside"**: a value with no `Prop` constructor value inside (`NoProp`) whose meaning,
read at `h`, fits `T` (`moved`, a member, or a type value with a level at the error type) is
hereditarily well typed there. No other hypothesis: the data code `T` may be any, declared by the
program or not. -/
theorem hwt_of_fit : ∀ (v : Value) (h : TyS) (T : TyM), NoProp K v →
    Fit K.dm.read T (meanV K ρ φ h v) → HWT K ρ φ h T v
  | .zero, _, _, _, hf => .atom rfl hf
  | .unit, _, _, _, hf => .atom rfl hf
  | .gfn _, _, _, _, hf => .atom rfl hf
  | .loan _, _, _, _, hf => .atom rfl hf
  | .bot, _, _, _, hf => .atom rfl hf
  | .abs _, _, _, _, hf => .atom rfl hf
  | .proof, _, _, _, hf => .atom rfl hf
  | .tNat, _, _, _, hf => .atom rfl hf
  | .tUnit, _, _, _, hf => .atom rfl hf
  | .sort _, _, _, _, hf => .atom rfl hf
  | .succ a, _, _, hc, hf => .succ hf (hwt_of_fit a _ _ hc (.inr (.inl (succ_fit hf))))
  | .tRef A, _, _, hc, hf => .tRef (hwt_of_fit A _ _ hc hf)
  | .borrow _ w, _, _, hc, hf => .borrow (hwt_of_fit w _ _ hc hf)
  | .gloan _ w, _, _, hc, hf => .gloan (hwt_of_fit w _ _ hc hf)
  | .sealed _, _, _, _, hf => .sealed hf
  | .tEq A a b, h, T, hc, hf => by
    obtain ⟨cA, ca, cb⟩ := hc
    have hf' := hf
    rw [meanV_tEq'] at hf'
    by_cases hok : EqOk K.dm.read (meanV K ρ φ (.plain .err) A) (meanV K ρ φ (.plain (capTy K ρ φ A)) a)
        (meanV K ρ φ (.plain (capTy K ρ φ A)) b)
    · obtain ⟨hl, sa, sb⟩ := hok
      obtain ⟨X, hX, hXl⟩ := ty_of_asTy_level hl
      exact .tEq hf (hwt_of_fit A _ _ cA (.inr (.inr ⟨rfl, X, hX, hXl⟩)))
        (hwt_of_fit a _ _ ca (fit_of_side sa)) (hwt_of_fit b _ _ cb (fit_of_side sb))
    · rw [if_neg hok] at hf'; exact absurd hf' ty_err_not_fit
  | .tInd n args, h, T, hc, hf => by
    rcases meanV_tInd_cases K ρ φ h n args with he | ⟨d, hd, hp⟩
    · rw [he] at hf; exact absurd hf ty_err_not_fit
    · exact .tInd hf hd (hwtParams_of d args 0 [] hc (pOk_of_paramsOk hp))
  | .clo cs t rd, h, T, hc, hf => by
    have hf' := hf
    rw [meanV_clo'] at hf'
    by_cases hok : CapsOk K.dm.read (capsVals K ρ φ cs) (capsTys K ρ φ rd)
    · exact .clo hf (hwtCaps_of cs rd hc hok)
    · rw [if_neg hok] at hf'; exact absurd hf' err_not_fit
  | .tPi cs t rd, h, T, hc, hf => by
    have hf' := hf
    rw [meanV_tPi'] at hf'
    by_cases hok : CapsOk K.dm.read (capsVals K ρ φ cs) (capsTys K ρ φ rd)
    · exact .tPi hf (hwtCaps_of cs rd hc hok)
    · rw [if_neg hok] at hf'; exact absurd hf' ty_err_not_fit
  | .ind t c hh ps fs, h, T, hc, hf => by
    obtain ⟨hns, cfs⟩ := hc
    rcases meanV_ind_cases K ρ φ h t c hh ps fs with he | ⟨d, r, hd, he⟩
    · rw [he] at hf; exact absurd hf err_not_fit
    · have hs : (d.sort == 0) = false := by simpa using hns d hd
      have hf' := hf
      rw [he, hs] at hf'
      simp only [Bool.false_eq_true, if_false, DataModel.ctorR] at hf'
      rcases hf' with hm | hm | ⟨-, X, hX, -⟩
      · cases hm
      · obtain ⟨d', hdc, hMem, -⟩ := mem_dat_inv K.dm hm
        exact .ind hf hd hs hdc (hwtFields_of d d' r c fs 0 [] cfs (fOk_of_mem hMem))
      · cases hX

theorem hwtParams_of (d : IndDecl) : ∀ (args : List Value) (i : Nat) (e : List Sem),
    NoPropL K args → POk K.dm d i e (meanParams K ρ φ d i e args) → HWTParams K ρ φ d i e args
  | [], _, _, _, _ => .nil
  | v :: vs, i, e, hc, hp => by
    obtain ⟨cv, cvs⟩ := hc
    obtain ⟨h1, h2⟩ := POk.cons (m := meanV K ρ φ (.plain (K.dm.paramTy d i e)) v) hp
    exact .cons (hwt_of_fit v _ _ cv (.inr (.inl h1))) (hwtParams_of d vs (i + 1) _ cvs h2)

theorem hwtFields_of (d d' : IndDecl) (r : Rec) (c : Nat) : ∀ (fs : List Value) (i : Nat) (e : List Sem),
    NoPropL K fs → FOk K.dm K.Γ d' r c i e (meanFields K ρ φ d r c i e fs) → HWTFields K ρ φ d d' r c i e fs
  | [], _, _, _, _ => .nil
  | v :: vs, i, e, hc, hp => by
    obtain ⟨cv, cvs⟩ := hc
    obtain ⟨h1, h2⟩ := FOk.cons (m := meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) v) hp
    exact .cons (fun U hU => hwt_of_fit v _ _ cv (.inr (.inl (h1 U hU))))
      (hwtFields_of d d' r c vs (i + 1) _ cvs h2)

theorem hwtCaps_of : ∀ (cs : List Value) (rd : List (DeclInfo × Value)),
    NoPropL K cs → CapsOk K.dm.read (capsVals K ρ φ cs) (capsTys K ρ φ rd) → HWTCaps K ρ φ cs rd
  | [], _, _, _ => .nil
  | _ :: _, [], _, hk => by simp [capsVals, capsTys, CapsOk] at hk
  | v :: vs, (dI, T) :: rd, hc, hk => by
    obtain ⟨cv, cvs⟩ := hc
    obtain ⟨h1, h2⟩ := hk
    exact .cons (hwt_of_fit v _ _ cv (.inr (.inl h1))) (hwtCaps_of vs rd cvs h2)
end

end

/-! ## With the fundamental lemma: a value a successful strict run returns -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The payoff, composed**: where a successful strict run from a good state returns the meaning of
a value `v` (read at `h`) with no `Prop` constructor value inside, `v` is hereditarily well typed at
the run's type, unless the result is the error-type escape. (It inherits `fund_all`'s guesses.
`FundCtx` no longer asks the read hypothesis `MemReads`, whose partly moved form is false,
`ReadProto.not_memReads_dep`: reads are strict, `Run.ReadGood`.) -/
theorem hwt_of_run (hc : FundCtx K) {t : Term} (ht : t.valsOk (ValsP K ρ φ)) {tl : Bool} {hint : TyS}
    {s s' : SState} {r : Res} (hs : SGood K.dm K.Γ φ s) (hr : runT K ρ φ tl hint t s = some (r, s'))
    {v : Value} {h : TyS} (hv : meanV K ρ φ h v = r.1) (hcv : NoProp K v) :
    HWT K ρ φ h r.2.m v ∨ (r.2.m = TyM.err ∧ NoData r.1) := by
  rcases (fund_all hc t ht tl hint s s' r hs hr).1 with hm | hm | he
  · exact .inl (hwt_of_fit v h _ hcv (by rw [hv]; exact .inr (.inl hm)))
  · exact .inl (hwt_of_fit v h _ hcv (by rw [hv]; exact .inl hm))
  · exact .inr he

end

/-- The predicate excludes what the trial's counterexample needs: `Eq(Nat, Nat, Nat)`, an equation
at `Nat` whose sides are types, is hereditarily well typed at no type (its side `Nat` is no number). -/
theorem eq_types_not_hwt (K : RunCtx) (ρ : Assignment) (φ : Future) (h : TyS) (T : TyM) :
    ¬ HWT K ρ φ h T (.tEq .tNat .tNat .tNat) := by
  intro hw
  generalize hv : Value.tEq .tNat .tNat .tNat = v at hw
  cases hw with
  | atom hx _ => subst hv; cases hx
  | tEq _ _ ha _ =>
    rename_i A a b
    simp only [Value.tEq.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    have e : capTy K ρ φ .tNat = TyM.nat := rfl
    rw [e] at ha
    generalize hw : Value.tNat = w at ha
    cases ha with
    | atom _ hf =>
      subst hw
      rcases hf with h1 | ⟨n, hn⟩ | ⟨h1, -⟩
      · cases h1
      · cases hn
      · have := congrArg TyM.level h1; simp [TyM.nat, TyM.err, TyM.level, Code0.level] at this
    | _ => cases hw
  | _ => cases hv


/-- **Non-vacuity witness for `hwt_of_fit`**: applied at a concrete instance (the probes' data model,
no declarations), it gives `Eq(Nat, 0, 0)` hereditarily well typed at `Prop`, and from that its side
`0` at `Nat`. -/
theorem hwt_witness (C : CodeMeaning) (D : Decisions) (ρ : Assignment) (φ : Future) :
    HWT ({ dm := DataModel.Program.dmP, Γ := [], C := C, D := D } : RunCtx) ρ φ (.plain TyM.err) (TyM.univ 0)
      (.tEq .tNat .zero .zero) := by
  let K : RunCtx := { dm := DataModel.Program.dmP, Γ := [], C := C, D := D }
  have hok : EqOk K.dm.read (meanV K ρ φ (.plain .err) .tNat) (meanV K ρ φ (.plain (capTy K ρ φ .tNat)) .zero)
      (meanV K ρ φ (.plain (capTy K ρ φ .tNat)) .zero) := ⟨rfl, .inr ⟨0, rfl⟩, .inr ⟨0, rfl⟩⟩
  refine hwt_of_fit _ _ _ ⟨trivial, trivial, trivial⟩ ?_
  rw [meanV_tEq', if_pos hok]
  exact .inr (.inl (ty_univ0_mem _))

theorem hwt_witness_side (C : CodeMeaning) (D : Decisions) (ρ : Assignment) (φ : Future) :
    HWT ({ dm := DataModel.Program.dmP, Γ := [], C := C, D := D } : RunCtx) ρ φ (.plain TyM.nat) TyM.nat .zero := by
  have h := hwt_witness C D ρ φ
  generalize hv : Value.tEq .tNat .zero .zero = v at h
  cases h with
  | tEq _ _ ha _ =>
    simp only [Value.tEq.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    exact ha
  | atom hx _ => subst hv; cases hx
  | _ => cases hv

end Ochr.Meaning.Strict
