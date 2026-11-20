import Ochr.Meaning.Apply

/-!
# Function meanings at every level: calling a built function runs its body; the level dispatch

`Apply.lean` builds and applies function meanings along telescope codes at any lawful level. This
file proves that calling a built function runs its body (`applyTelL_mkTelL`), at every lawful
level, and gives the meaning of a Π-type and of a closure at the declared sort `l`
(`Decisions.piSort`): a proposition and `⋆` at `Prop` (D12), the level-`l - 1` code and element
otherwise, `err` above the bounded levels. The `.pi` and `.fix` clauses both read the same
telescope code (`telL`), so a closure is a member of its own type (`closureAt_mem`).
-/

namespace Ochr.Meaning

open Classical

universe u

section
variable (L : Lvl.{u})

/-- The arguments fit the telescope code: as many as its parameters, each decoding at its
parameter's code, the rest fitting the rest of the code at that element. -/
def ArgsFitL : {Fin C : Type u} → Tel L.Code Fin C → List Sem → Prop
  | _, _, .dat .., [] => True
  | _, _, .ref .., [] => True
  | _, _, .param _ _ _ c _ k, a :: as => ∃ x, L.dec c a = some x ∧ ArgsFitL (k x) as
  | _, _, _, _ => False

/-- `readFin` inverts `mkFin` on what it consumes (the accumulated final contents). -/
def FinInv {Fin : Type u} (mkFin : List Sem → Option (Fin × List Sem)) (readFin : Fin → List Sem) : Prop :=
  ∀ fs fin rest, mkFin fs = some (fin, rest) → readFin fin ++ rest = fs

/-- The inverse is kept by each parameter's step (`extMkL`/`extReadL`), at a lawful level. -/
theorem finInv_ext (hL : L.Lawful) (b : Bool) (Fin T : Type u) (c : L.Code T)
    (mkFin : List Sem → Option (Fin × List Sem)) (readFin : Fin → List Sem) (h : FinInv mkFin readFin) :
    FinInv (extMkL b Fin T mkFin (L.dec c)) (extReadL b Fin T readFin (L.enc c)) := by
  cases b with
  | false => exact h
  | true =>
    intro fs fin rest hm
    cases hmk : mkFin fs with
    | none => simp [extMkL, hmk] at hm
    | some p =>
      obtain ⟨x, r⟩ := p
      cases r with
      | nil => simp [extMkL, hmk] at hm
      | cons t r' =>
        cases hd : L.dec c t with
        | none => simp [extMkL, hmk, hd] at hm
        | some y =>
          simp [extMkL, hmk, hd] at hm
          obtain ⟨rfl, rfl⟩ := hm
          have := h fs x (t :: r') hmk
          simp only [extReadL, hL.enc_of_dec c hd, List.append_assoc, List.singleton_append]
          exact this

/-- The starting accumulator (`PUnit`, nothing consumed) is inverted by reading nothing. -/
theorem finInv_start : FinInv (fun fs => some (PUnit.unit, fs)) (fun (_ : PUnit.{u + 1}) => ([] : List Sem)) := by
  intro fs fin rest h
  cases h
  rfl

/-- What applying a built function gives, against its body's run `o`: for a data codomain the
body's result and its final contents at the future; for a returned borrow the body's result as
the forward value, and as the backward function the body's finals read at the future that fixes
the returned label to the value left in it. -/
def AppMatches (φ : Future) (o : BodyOut) : AppResultL L → Prop
  | .data r _ fins => r = o.result ∧ fins = o.finals.map (· φ)
  | .ref _ c fwd back => ∃ k, o.retLabel = some k ∧ L.enc c fwd = o.result ∧
      ∀ v, back v = o.finals.map (· (φ.upd k (L.enc c v)))

/-- **Calling a built function runs its body**, at a lawful level: if `mkTelL` built `F` along the
code `t` from the body's run `g`, then applying `F` to arguments that fit the code gives what the
body's run at those arguments gives. -/
theorem applyTelL_mkTelL (hL : L.Lawful) (φ : Future) (g : List Sem → Option BodyOut) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (acc : List Sem) (mkFin : List Sem → Option (Fin × List Sem))
      (readFin : Fin → List Sem) (F : C) (args : List Sem),
      FinInv mkFin readFin → mkTelL L φ t acc mkFin g = some F → ArgsFitL L t args →
      ∃ o r, g (acc ++ args) = some o ∧ applyTelL L t readFin F args = some r ∧ AppMatches L φ o r
  | _, _, .dat Fin B c, acc, mkFin, readFin, F, [], hF, hmk, _ => by
    simp only [mkTelL] at hmk
    cases hg : g acc with
    | none => rw [hg] at hmk; cases hmk
    | some o =>
      rw [hg, Option.bind_some] at hmk
      unfold mkLeafDataL at hmk
      cases hr : L.dec c o.result with
      | none => simp [hr] at hmk
      | some r =>
        cases hm : mkFin (o.finals.map (· φ)) with
        | none => simp [hr, hm] at hmk
        | some q =>
          obtain ⟨fin, rest⟩ := q
          cases rest with
          | cons _ _ => simp [hr, hm] at hmk
          | nil =>
            simp only [hr, hm, Option.some.injEq] at hmk
            subst hmk
            refine ⟨o, _, by simpa using hg, rfl, hL.enc_of_dec c hr, ?_⟩
            simpa using hF _ _ _ hm
  | _, _, .ref Fin U c, acc, mkFin, readFin, F, [], hF, hmk, _ => by
    simp only [mkTelL] at hmk
    cases hg : g acc with
    | none => rw [hg] at hmk; cases hmk
    | some o =>
      rw [hg, Option.bind_some] at hmk
      unfold mkLeafRefL at hmk
      cases hk : o.retLabel with
      | none => simp [hk] at hmk
      | some k =>
        cases hr : L.dec c o.result with
        | none => simp [hk, hr] at hmk
        | some fwd =>
          simp only [hk, hr] at hmk
          split at hmk
          · rename_i htot
            split at hmk
            · cases hmk
              refine ⟨o, _, by simpa using hg, rfl, k, hk, hL.enc_of_dec c hr, fun v => ?_⟩
              obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (htot v)
              have hget : (mkBackAtL L φ Fin mkFin c o k v).get (htot v) = b := by simp [hb]
              show readFin ((mkBackAtL L φ Fin mkFin c o k v).get (htot v)) = _
              rw [hget]
              unfold mkBackAtL at hb
              split at hb
              · rename_i fin heq
                cases hb
                simpa using hF _ _ _ heq
              · cases hb
            · cases hmk
          · cases hmk
  | _, _, .param Fin isRef A c C k, acc, mkFin, readFin, F, a :: as, hF, hmk, ⟨x, hx, hfit⟩ => by
    simp only [mkTelL] at hmk
    split at hmk
    · rename_i hall
      cases hmk
      have hea : L.enc c x = a := hL.enc_of_dec c hx
      obtain ⟨o, r, hg, hap, hm⟩ := applyTelL_mkTelL hL φ g (k x) (acc ++ [L.enc c x]) _ _ _ as
        (finInv_ext L hL isRef Fin A c mkFin readFin hF) (Option.some_get (hall x)).symm hfit
      refine ⟨o, r, by simpa [hea] using hg, ?_, hm⟩
      simp only [applyTelL, hx]
      exact hap
    · cases hmk
  | _, _, .dat .., _, _, _, _, _ :: _, _, _, hfit => hfit.elim
  | _, _, .ref .., _, _, _, _, _ :: _, _, _, hfit => hfit.elim
  | _, _, .param .., _, _, _, _, [], _, _, hfit => hfit.elim

/-- The body's run is defined, and of its type, at the given arguments (walking the code: what
the strict leaf of `mkTelL` asks at them). -/
def LeafDefL (φ : Future) (g : List Sem → Option BodyOut) : {Fin C : Type u} → Tel L.Code Fin C → List Sem →
    (List Sem → Option (Fin × List Sem)) → List Sem → Prop
  | _, _, .dat Fin _ c, acc, mkFin, [] => ((g acc).bind (mkLeafDataL L φ Fin mkFin c)).isSome
  | _, _, .ref Fin _ c, acc, mkFin, [] => ((g acc).bind (mkLeafRefL L φ Fin mkFin c)).isSome
  | _, _, .param Fin isRef A c _ k, acc, mkFin, a :: as =>
    ∀ x, L.dec c a = some x → LeafDefL φ g (k x) (acc ++ [L.enc c x]) (extMkL isRef Fin A mkFin (L.dec c)) as
  | _, _, .dat .., _, _, _ :: _ => False
  | _, _, .ref .., _, _, _ :: _ => False
  | _, _, .param .., _, _, [] => False

/-- **Calling a filled closure where its body is defined runs its body** (a recursion stage read
below its rank, docs/31 D60). -/
theorem applyTelL_mkTelFillL (hL : L.Lawful) (φ : Future) (g : List Sem → Option BodyOut) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C) (acc : List Sem) (mkFin : List Sem → Option (Fin × List Sem))
      (readFin : Fin → List Sem) (F : C) (args : List Sem),
      FinInv mkFin readFin → mkTelFillL L φ t acc mkFin g = some F → ArgsFitL L t args →
      LeafDefL L φ g t acc mkFin args →
      ∃ o r, g (acc ++ args) = some o ∧ applyTelL L t readFin F args = some r ∧ AppMatches L φ o r
  | _, _, .dat Fin B c, acc, mkFin, readFin, F, [], hF, hmk, _, hdef => by
    obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.mp hdef
    have hmk' : mkTelL L φ (.dat Fin B c) acc mkFin g = some F := by
      simp only [mkTelFillL, hF'] at hmk
      simp only [mkTelL, hF', hmk]
    exact applyTelL_mkTelL L hL φ g (.dat Fin B c) acc mkFin readFin F [] hF hmk' trivial
  | _, _, .ref Fin U c, acc, mkFin, readFin, F, [], hF, hmk, _, hdef => by
    obtain ⟨F', hF'⟩ := Option.isSome_iff_exists.mp hdef
    have hmk' : mkTelL L φ (.ref Fin U c) acc mkFin g = some F := by
      simp only [mkTelFillL, hF'] at hmk
      simp only [mkTelL, hF', hmk]
    exact applyTelL_mkTelL L hL φ g (.ref Fin U c) acc mkFin readFin F [] hF hmk' trivial
  | _, _, .param Fin isRef A c C k, acc, mkFin, readFin, F, a :: as, hF, hmk, ⟨x, hx, hfit⟩, hdef => by
    simp only [mkTelFillL] at hmk
    split at hmk
    · rename_i hall
      cases hmk
      have hea : L.enc c x = a := hL.enc_of_dec c hx
      obtain ⟨o, r, hg, hap, hm⟩ := applyTelL_mkTelFillL hL φ g (k x) (acc ++ [L.enc c x]) _ _ _ as
        (finInv_ext L hL isRef Fin A c mkFin readFin hF) (Option.some_get (hall x)).symm hfit (hdef x hx)
      refine ⟨o, r, by simpa [hea] using hg, ?_, hm⟩
      simp only [applyTelL, hx]
      exact hap
    · cases hmk
  | _, _, .dat .., _, _, _, _, _ :: _, _, _, hfit, _ => hfit.elim
  | _, _, .ref .., _, _, _, _, _ :: _, _, _, hfit, _ => hfit.elim
  | _, _, .param .., _, _, _, _, [], _, _, hfit, _ => hfit.elim

/-- **Calling a closure runs its body**, at a lawful level. -/
theorem applyFnL_closureL (hL : L.Lawful) (φ : Future) {C : Type u} (t : Tel L.Code PUnit C)
    (g : List Sem → Option BodyOut) (args : List Sem)
    (hs : (mkTelL L φ t [] (fun fs => some (PUnit.unit, fs)) g).isSome) (hfit : ArgsFitL L t args) :
    ∃ o r, g args = some o ∧ applyFnL L t (closureL L φ t g) args = some r ∧ AppMatches L φ o r := by
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨o, r, hg, hap, hm⟩ := applyTelL_mkTelL L hL φ g t [] _ (fun _ => []) F args (finInv_start) hF hfit
  refine ⟨o, r, by simpa using hg, ?_, hm⟩
  unfold closureL applyFnL
  rw [hF]
  simp only [hL.unpack_pack, Option.bind_some]
  exact hap

end

/-! ## The level dispatch -/

/-- The meaning of a Π-type at its declared sort `l` (D55, `Decisions.piSort`): the proposition
`piProp` at `Prop`, the level-`l - 1` telescope code at `Type_{l-1}` for the bounded levels, `err`
above (D2). The `.pi` and `.fix` clauses both use it, so that a closure lies in its type. -/
noncomputable def piTyAt (l : Nat) (ds : List PiDom) (out : PiCod) : TyM :=
  match l with
  | 0 => TyM.prop (piProp ds [] fun acc => if out.isRef then False else (out.cod acc).true)
  | 1 => piTyL lvl0 (telL lvl0 ds [] PUnit out).2
  | 2 => piTyL lvl1 (telL lvl1 ds [] PUnit out).2
  | 3 => piTyL lvl2 (telL lvl2 ds [] PUnit out).2
  | _ => TyM.err

/-- The meaning of a closure at its declared sort `l`: `⋆` at `Prop` (D12: a proof-valued
function is a proof), the level-`l - 1` element built along the same code otherwise, `err` above
the bounded levels. -/
noncomputable def closureAt (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) : Sem :=
  match l with
  | 0 => .proof
  | 1 => closureL lvl0 φ (telL lvl0 ds [] PUnit out).2 g
  | 2 => closureL lvl1 φ (telL lvl1 ds [] PUnit out).2 g
  | 3 => closureL lvl2 φ (telL lvl2 ds [] PUnit out).2 g
  | _ => .err

/-- The closure of a recursion stage at its declared sort (`mkTelFillL`, docs/31 D60). -/
noncomputable def closureFillAt (l : Nat) (φ : Future) (ds : List PiDom) (out : PiCod)
    (g : List Sem → Option BodyOut) : Sem :=
  match l with
  | 0 => .proof
  | 1 => closureFillL lvl0 φ (telL lvl0 ds [] PUnit out).2 g
  | 2 => closureFillL lvl1 φ (telL lvl1 ds [] PUnit out).2 g
  | 3 => closureFillL lvl2 φ (telL lvl2 ds [] PUnit out).2 g
  | _ => .err

/-- **At a data sort, a closure is a member of its type at that sort, or `err`** (D12's invariant
for `Type₀`, `Type₁`, `Type₂`): it is built in the carrier its type's code is indexed by. -/
theorem closureAt_mem (l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3) (φ : Future) (ds : List PiDom)
    (out : PiCod) (g : List Sem → Option BodyOut) :
    closureAt l φ ds out g ∈ₛ piTyAt l ds out ∨ closureAt l φ ds out g = .err := by
  rcases hl with rfl | rfl | rfl
  · exact closureL_mem lvl0 lvl0_lawful φ _ g
  · exact closureL_mem lvl1 lvl1_lawful φ _ g
  · exact closureL_mem lvl2 lvl2_lawful φ _ g

/-- The next parameter of a function type `T` after the given arguments, read off its telescope
code: whether it is a borrow, and its (content) code; `none` if `T` is not a function type. -/
noncomputable def TyM.paramAt? : TyM → List Sem → Option (Bool × TyM)
  | .t0 _ (.pi _ t), as => telParamL lvl0 t as
  | .t1 _ (.pi _ t), as => telParamL lvl1 t as
  | .t2 _ (.pi _ t), as => telParamL lvl2 t as
  | _, _ => none

/-- The codomain a function type `T` reaches at the arguments, read off its telescope code:
whether it is a returned borrow, and its (content) code (D82 [Call-type]). -/
noncomputable def TyM.codAt? : TyM → List Sem → Option (Bool × TyM)
  | .t0 _ (.pi _ t), as => telCodL lvl0 t as
  | .t1 _ (.pi _ t), as => telCodL lvl1 t as
  | .t2 _ (.pi _ t), as => telCodL lvl2 t as
  | _, _ => none

/-- The type of the next argument of a call through a function of type `T`, after the given
arguments (the hint the argument runs at, D82 [Call-type]); `err` past the end. -/
noncomputable def TyM.domAfter (T : TyM) (as : List Sem) : TyM := ((T.paramAt? as).map (·.2)).getD TyM.err

end Ochr.Meaning
