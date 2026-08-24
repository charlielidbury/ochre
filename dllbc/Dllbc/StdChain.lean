import Dllbc.Program
import Dllbc.FnMacro
import Dllbc.ElabCheck
import Dllbc.ProgMacro
import Dllbc.Std


/-! # The standard lemma chain (docs/20 stage 4)

    Every standard-library lemma as an `fn`, in a chain of module blocks, each
    seeded from the one before (`std0`, `std1 := prog (std0) { … }`, …, `std`):
    the signature is the stated type, the body is the proof, and a block
    elaborating IS the definition-site check of the lemmas in it. 41 are native
    match+recursion rewrites; the rest apply the original proof term (an `XRaw`
    constant of `StdChainRaw` below) to the parameters. The spec functions and
    predicate formers are bound into the state at the END of the chain, in the
    final link `std`, so the file imports no lemma library and consumers seed
    from `std` alone, citing lemmas and formers by name. Only `std` is a
    consumer-facing name; the links are the cuts described below. -/

namespace Dllbc

/-! The raw library — the spec functions, predicate formers, and original proof
    terms — as Lean constants. Two measured facts shape this:

    * They are constants, not literals in the block: inlining the λ bodies makes
      the quoted `Term` so large that compiling the `def` hits the code
      generator's maximum recursion depth. A constant is a compact `Expr`.
    * A proof term is APPLIED in a `fn` body as the constant, never through a
      `let`-bound name: applying a bound value is ⇒-application, where a recursor
      stuck on a symbolic scrutinee is refused ("reachable through a seal, not
      through a call"); a spliced constant is a pure literal lifted under ⇝. The
      bindings exist for consumers' TYPES (a seed binding cited in a type reduces),
      so only the 26 formers are bound and none of the `XRaw` terms are — and they
      are bound LAST, because every σ-refinement rebuilds every Ω binding
      (`refineSym`).

      **The number that justified LAST is stale, and its subject no longer
      exists.** "98 s against 79 s" was measured on the SINGLE 136-statement
      block, which stopped compiling on the detach-tails rebase and was cut into
      the eleven links below (docs/20 §5, "Cut into links"); docs/20 records 17 s
      wall for the cut module against 85 s for the block it replaced, and marks
      the 98/79 pair superseded. On this machine today a full-file
      `lake build Dllbc.StdChain` — dependencies warm, so the figure is Lean
      elaborating this module and compiling `StdChainRaw` — is **13–14 s** across
      five samples. The ORDER argument is unaffected: `refineSym` still rebuilds
      every Ω binding, so binding early is still more work. Its magnitude on the
      link structure has not been re-measured, and the one adjacent datum says it
      is now small — adding ten further bindings to this final link measured 14 s
      against a 14 s baseline. Anyone about to spend the 19 s should re-take it
      first. (Binding the ten `Std` formers early is separately impossible, not
      merely slow: docs/24 §3d.) -/
namespace StdChainRaw
open Dllbc
def LeReflRaw : Term := prog_parse {
  λ (N : Nat). elim N return (λ (M : Nat). Le M M) {
    Z => unit,
    S (K) Ih => Ih } }
def LeTransRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (A0 : Nat). Π (B : Nat) → Π (C : Nat) → Le A0 B → Le B C → Le A0 C) {
      Z => λ (B : Nat). λ (C : Nat). λ (Hab : Le Z B). λ (Hbc : Le B C). unit,
      S (A') Ih => λ (B : Nat). λ (C : Nat). λ (Hab : Le (S A') B). λ (Hbc : Le B C).
        elim B return (λ (B0 : Nat). Le (S A') B0 → Le B0 C → Le (S A') C) {
          Z => λ (Hab0 : Le (S A') Z). λ (Hbc0 : Le Z C). botElim (Le (S A') C) Hab0,
          S (B') Ihb => λ (Hab0 : Le (S A') (S B')). λ (Hbc0 : Le (S B') C).
            elim C return (λ (C0 : Nat). Le (S B') C0 → Le (S A') C0) {
              Z => λ (Hbc1 : Le (S B') Z). botElim (Le (S A') Z) Hbc1,
              S (C') Ihc => λ (Hbc1 : Le (S B') (S C')). Ih B' C' Hab0 Hbc1
            } Hbc0
        } Hab Hbc
    } }
def LeUpRRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le Az (S B)) {
    Z => λ (B : Nat). λ (H : Le Z B). unit,
    S (A') Ih => λ (B : Nat). λ (H : Le (S A') B).
      elim B return (λ (Bz : Nat). Le (S A') Bz → Le (S A') (S Bz)) {
        Z => λ (H0 : Le (S A') Z). botElim (Le (S A') (S Z)) H0,
        S (B') Ihb => λ (H0 : Le (S A') (S B')). Ih B' H0
      } H } }
def LeAddRaw : Term := prog_parse {
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le Iz (Add Iz G)) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeAddLRaw : Term := prog_parse {
  λ (B : Nat). λ (A : Nat).
    elim A return (λ (Az : Nat). Le B (Add Az B)) {
      Z => LeReflRaw B,
      S (A') Ih => LeUpRRaw B (Add A' B) Ih } }
def LeAddSuccRaw : Term := prog_parse {
  λ (I : Nat). elim I return (λ (Iz : Nat). Π (G : Nat) → Le (S Iz) (Add Iz (S G))) {
    Z => λ (G : Nat). unit,
    S (I') Ih => λ (G : Nat). Ih G } }
def LeRwRRaw : Term := prog_parse {
  λ (A : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le A X).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le A Y') P Y H }
def LeRwLRaw : Term := prog_parse {
  λ (B : Nat). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (P : Le X B).
    j Nat X (λ (Y' : Nat). λ (Hh : Id Nat X Y'). Le Y' B) P Y H }
def LeAddMonoLRaw : Term := prog_parse {
  λ (Lo : Nat). λ (A : Nat). λ (B : Nat). λ (H : Le A B).
    elim Lo return (λ (Loz : Nat). Le (Add Loz A) (Add Loz B)) {
      Z => H,
      S (Lo') Ih => Ih } }
def IdTransRaw : Term := prog_parse {
  λ (A : Type). λ (X : A). λ (Y : A). λ (Z0 : A). λ (P : Id A X Y). λ (Q : Id A Y Z0).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' Z0 → Id A X Z0) (λ (H : Id A X Z0). H) Y P Q }
def IdCongrRaw : Term := prog_parse {
  λ (A : Type). λ (B : Type). λ (F : A → B). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id B (F X) (F Y')) Refl Y P }
def IdSymRaw : Term := prog_parse {
  λ (A : Type). λ (X : A). λ (Y : A). λ (P : Id A X Y).
    j A X (λ (Y' : A). λ (H : Id A X Y'). Id A Y' X) Refl Y P }
def AddZeroRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (X : Nat). Id Nat (Add X Z) X) {
    Z => Refl,
    S (A') Ih => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Add A' Z) A' Ih } }
def AddSuccRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). elim A return (λ (X : Nat). Id Nat (Add X (S B)) (S (Add X B))) {
    Z => Refl,
    S (A') Ih => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Add A' (S B)) (S (Add A' B)) Ih } }
def AddCommRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Id Nat (Add X B) (Add B X)) {
    Z => λ (B : Nat). IdSymRaw Nat (Add B Z) B (AddZeroRaw B),
    S (A') Ih => λ (B : Nat).
      IdTransRaw Nat (S (Add A' B)) (S (Add B A')) (Add B (S A'))
        (IdCongrRaw Nat Nat (λ (N : Nat). S N) (Add A' B) (Add B A') (Ih B))
        (IdSymRaw Nat (Add B (S A')) (S (Add B A')) (AddSuccRaw B A')) } }
def AddAssocRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (X : Nat). Π (B : Nat) → Π (C : Nat) → Id Nat (Add (Add X B) C) (Add X (Add B C))) {
    Z => λ (B : Nat). λ (C : Nat). Refl,
    S (A') Ih => λ (B : Nat). λ (C : Nat).
      IdCongrRaw Nat Nat (λ (N : Nat). S N) (Add (Add A' B) C) (Add A' (Add B C)) (Ih B C) } }
def CountAppendRaw : Term := prog_parse {
  λ (M : Nat). λ (A : List Nat). λ (B : List Nat).
    elim A return (λ (X : List Nat). Id Nat (Count M (Append X B)) (Add (Count M X) (Count M B))) {
      Nil => Refl,
      Cons (H) (T) Ih =>
        elim (Eqb M H) return (λ (Bv : Bool).
          Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M (Append T B))) (Count M (Append T B)) Bv)
                 (Add (boolRec (λ (W : Bool). Nat) (S (Count M T)) (Count M T) Bv) (Count M B))) {
          True => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Count M (Append T B)) (Add (Count M T) (Count M B)) Ih,
          False => Ih
        }
    } }
def NthL : Term := prog_parse {
  λ (K : Nat). elim K return (λ (Z0 : Nat). List Nat → Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => H },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). Nat) { Nil => Z, Cons (H) (T) Ihl => Rec T } } }
def Set : Term := prog_parse {
  λ (K : Nat). λ (V : Nat). elim K return (λ (Z0 : Nat). List Nat → List Nat) {
    Z => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons V T },
    S (K') Rec => λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) { Nil => Nil, Cons (H) (T) Ihl => Cons H (Rec T) } } }
def SwapL : Term := prog_parse {
  λ (I : Nat). elim I return (λ (Z0 : Nat). Nat → List Nat → List Nat) {
    Z => λ (J : Nat). λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) {
      Nil => Nil,
      Cons (X) (Xs) Ihl => elim J return (λ (Z0 : Nat). List Nat) {
        Z => Cons X Xs,
        S (J') Jih => Cons (NthL J' Xs) (Set J' X Xs) } },
    S (I') Reci => λ (J : Nat). λ (L : List Nat). elim L return (λ (Z0 : List Nat). List Nat) {
      Nil => Nil,
      Cons (X) (Xs) Ihl => elim J return (λ (Z0 : Nat). List Nat) {
        Z => Cons X Xs,
        S (J') Jih => Cons X (Reci J' Xs) } } } }
def LenSetRaw : Term := prog_parse {
  λ (K : Nat). λ (V : Nat).
    elim K return (λ (Z0 : Nat). Π (L : List Nat) → Id Nat (Len (Set Z0 V L)) (Len L)) {
      Z => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set Z V X)) (Len X)) {
        Nil => Refl, Cons (H) (T) Ihl => Refl },
      S (K') Ih => λ (L : List Nat). elim L return (λ (X : List Nat). Id Nat (Len (Set (S K') V X)) (Len X)) {
        Nil => Refl,
        Cons (H) (T) Ihl => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Len (Set K' V T)) (Len T) (Ih T) } } }
def LenSwapLRaw : Term := prog_parse {
  λ (I : Nat).
    elim I return (λ (Z0 : Nat). Π (J : Nat) → Π (L : List Nat) → Id Nat (Len (SwapL Z0 J L)) (Len L)) {
      Z => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (X : List Nat). Id Nat (Len (SwapL Z J X)) (Len X)) {
          Nil => Refl,
          Cons (Y) (Ys) Ihl => elim J return (λ (W : Nat). Id Nat (Len (SwapL Z W (Cons Y Ys))) (Len (Cons Y Ys))) {
            Z => Refl,
            S (J') Jih => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Len (Set J' Y Ys)) (Len Ys) (LenSetRaw J' Y Ys) } },
      S (I') Ih => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (X : List Nat). Id Nat (Len (SwapL (S I') J X)) (Len X)) {
          Nil => Refl,
          Cons (Y) (Ys) Ihl => elim J return (λ (W : Nat). Id Nat (Len (SwapL (S I') W (Cons Y Ys))) (Len (Cons Y Ys))) {
            Z => Refl,
            S (J') Jih => IdCongrRaw Nat Nat (λ (N : Nat). S N) (Len (SwapL I' J' Ys)) (Len Ys) (Ih J' Ys) } } } }
def CountConsCongrRaw : Term := prog_parse {
  λ (M : Nat). λ (H : Nat). λ (L1 : List Nat). λ (L2 : List Nat). λ (P : Id Nat (Count M L1) (Count M L2)).
    IdCongrRaw Nat Nat (λ (R : Nat). boolRec (λ (W : Bool). Nat) (S R) R (Eqb M H)) (Count M L1) (Count M L2) P }
def CountConsHitRaw : Term := prog_parse {
  λ (M : Nat). λ (A : Nat). λ (L : List Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M L)) (Count M L) Z0) (S (Count M L)))
      Refl (Eqb M A) (IdSymRaw Bool (Eqb M A) True Hq) }
def SwapLSetRaw : Term := prog_parse {
  λ (I : Nat).
    elim I return (λ (Iz : Nat). Π (J : Nat) → Π (L : List Nat) → Le (S Iz) J → Le (S J) (Len L) →
        Id (List Nat) (Set Iz (NthL J L) (Set J (NthL Iz L) L)) (SwapL Iz J L)) {
      Z => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S Z) J → Le (S J) (Len Lz) →
            Id (List Nat) (Set Z (NthL J Lz) (Set J (NthL Z Lz) Lz)) (SwapL Z J Lz)) {
          Nil => λ (Pij : Le (S Z) J). λ (P2 : Le (S J) (Len Nil)).
            botElim (Id (List Nat) (Set Z (NthL J Nil) (Set J (NthL Z Nil) Nil)) (SwapL Z J Nil)) P2,
          Cons (Y) (Ys) Ihl => λ (Pij : Le (S Z) J). λ (P2 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat). Le (S Z) Jz → Le (S Jz) (Len (Cons Y Ys)) →
                Id (List Nat) (Set Z (NthL Jz (Cons Y Ys)) (Set Jz (NthL Z (Cons Y Ys)) (Cons Y Ys))) (SwapL Z Jz (Cons Y Ys))) {
              Z => λ (Pijz : Le (S Z) Z). λ (P2z : Le (S Z) (Len (Cons Y Ys))).
                botElim (Id (List Nat) (Set Z (NthL Z (Cons Y Ys)) (Set Z (NthL Z (Cons Y Ys)) (Cons Y Ys))) (SwapL Z Z (Cons Y Ys))) Pijz,
              S (J') Jih => λ (Pijs : Le (S Z) (S J')). λ (P2s : Le (S (S J')) (Len (Cons Y Ys))). Refl
            } Pij P2 },
      S (I') Ih => λ (J : Nat). λ (L : List Nat).
        elim L return (λ (Lz : List Nat). Le (S (S I')) J → Le (S J) (Len Lz) →
            Id (List Nat) (Set (S I') (NthL J Lz) (Set J (NthL (S I') Lz) Lz)) (SwapL (S I') J Lz)) {
          Nil => λ (Pij : Le (S (S I')) J). λ (P2 : Le (S J) (Len Nil)).
            botElim (Id (List Nat) (Set (S I') (NthL J Nil) (Set J (NthL (S I') Nil) Nil)) (SwapL (S I') J Nil)) P2,
          Cons (Y) (Ys) Ihl => λ (Pij : Le (S (S I')) J). λ (P2 : Le (S J) (Len (Cons Y Ys))).
            elim J return (λ (Jz : Nat). Le (S (S I')) Jz → Le (S Jz) (Len (Cons Y Ys)) →
                Id (List Nat) (Set (S I') (NthL Jz (Cons Y Ys)) (Set Jz (NthL (S I') (Cons Y Ys)) (Cons Y Ys))) (SwapL (S I') Jz (Cons Y Ys))) {
              Z => λ (Pijz : Le (S (S I')) Z). λ (P2z : Le (S Z) (Len (Cons Y Ys))).
                botElim (Id (List Nat) (Set (S I') (NthL Z (Cons Y Ys)) (Set Z (NthL (S I') (Cons Y Ys)) (Cons Y Ys))) (SwapL (S I') Z (Cons Y Ys))) Pijz,
              S (J') Jih => λ (Pijs : Le (S (S I')) (S J')). λ (P2s : Le (S (S J')) (Len (Cons Y Ys))).
                IdCongrRaw (List Nat) (List Nat) (λ (T : List Nat). Cons Y T)
                  (Set I' (NthL J' Ys) (Set J' (NthL I' Ys) Ys)) (SwapL I' J' Ys) (Ih J' Ys Pijs P2s)
            } Pij P2 } } }
def BoolFTRaw : Term := prog_parse {
  λ (H : Id Bool False True).
    j Bool False (λ (Y' : Bool). λ (Hh : Id Bool False Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Bot, False => Unit })
      unit True H }
def BoolTFRaw : Term := prog_parse {
  λ (H : Id Bool True False).
    j Bool True (λ (Y' : Bool). λ (Hh : Id Bool True Y'). elim Y' return (λ (Z0 : Bool). Type) { True => Unit, False => Bot })
      unit False H }
def LebTrueLeRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) True → Le Az B) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) True). unit,
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) True → Le (S A') Bz) {
          Z => λ (H : Id Bool (Leb (S A') Z) True). botElim (Le (S A') Z) (BoolFTRaw H),
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) True). Ih B' H } } }
def LebFalseGtRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Leb Az B) False → Le (S B) Az) {
      Z => λ (B : Nat). λ (H : Id Bool (Leb Z B) False). botElim (Le (S B) Z) (BoolTFRaw H),
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Id Bool (Leb (S A') Bz) False → Le (S Bz) (S A')) {
          Z => λ (H : Id Bool (Leb (S A') Z) False). unit,
          S (B') Ihb => λ (H : Id Bool (Leb (S A') (S B')) False). Ih B' H } } }
def LeAntisymRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Le B Az → Id Nat Az B) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Z Bz → Le Bz Z → Id Nat Z Bz) {
          Z => λ (H1 : Le Z Z). λ (H2 : Le Z Z). Refl,
          S (B') Ihb => λ (H1 : Le Z (S B')). λ (H2 : Le (S B') Z). botElim (Id Nat Z (S B')) H2 },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S A') Bz → Le Bz (S A') → Id Nat (S A') Bz) {
          Z => λ (H1 : Le (S A') Z). λ (H2 : Le Z (S A')). botElim (Id Nat (S A') Z) H1,
          S (B') Ihb => λ (H1 : Le (S A') (S B')). λ (H2 : Le (S B') (S A')).
            IdCongrRaw Nat Nat (λ (N : Nat). S N) A' B' (Ih B' H1 H2) } } }
def ZnotsRaw : Term := prog_parse {
  λ (X : Nat). λ (H : Id Nat Z (S X)).
    j Nat Z (λ (Y : Nat). λ (Hy : Id Nat Z Y). elim Y return (λ (Yy : Nat). Type) { Z => Unit, S (K) Ih => Bot })
      unit (S X) H }
def Pred : Term := prog_parse { λ (N : Nat). elim N return (λ (Z0 : Nat). Nat) { Z => Z, S (K) Ih => K } }
def SInjRaw : Term := prog_parse {
  λ (M : Nat). λ (N : Nat). λ (H : Id Nat (S M) (S N)).
    IdCongrRaw Nat Nat Pred (S M) (S N) H }
def SubRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Nat → Nat) {
      Z => λ (B : Nat). Z,
      S (A') Rec => λ (B : Nat). elim B return (λ (Bz : Nat). Nat) { Z => S A', S (B') Bih => Rec B' } } }
def AddSubCancelRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le B Az → Id Nat (Add B (SubRaw Az B)) Az) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Bz Z → Id Nat (Add Bz (SubRaw Z Bz)) Z) {
          Z => λ (H : Le Z Z). Refl,
          S (B') Bih => λ (H : Le (S B') Z). botElim (Id Nat (Add (S B') (SubRaw Z (S B'))) Z) H },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le Bz (S A') → Id Nat (Add Bz (SubRaw (S A') Bz)) (S A')) {
          Z => λ (H : Le Z (S A')). Refl,
          S (B') Bih => λ (H : Le (S B') (S A')).
            IdCongrRaw Nat Nat (λ (N : Nat). S N) (Add B' (SubRaw A' B')) A' (Ih B' H) } } }
def LePredLRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (H : Le (S A) B).
    LeTransRaw A (S A) B (LeUpRRaw A A (LeReflRaw A)) H }
def EqbGtFalseRaw : Term := prog_parse {
  λ (H : Nat).
    elim H return (λ (Hz : Nat). Π (X : Nat) → Le (S Hz) X → Id Bool (Eqb X Hz) False) {
      Z => λ (X : Nat).
        elim X return (λ (Xz : Nat). Le (S Z) Xz → Id Bool (Eqb Xz Z) False) {
          Z => λ (Hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) Hlt,
          S (X') Xih => λ (Hlt : Le (S Z) (S X')). Refl },
      S (H') Ih => λ (X : Nat).
        elim X return (λ (Xz : Nat). Le (S (S H')) Xz → Id Bool (Eqb Xz (S H')) False) {
          Z => λ (Hlt : Le (S (S H')) Z). botElim (Id Bool (Eqb Z (S H')) False) Hlt,
          S (X') Xih => λ (Hlt : Le (S (S H')) (S X')). Ih X' Hlt } } }
def EqbLtFalseRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Le (S Az) B → Id Bool (Eqb Az B) False) {
      Z => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S Z) Bz → Id Bool (Eqb Z Bz) False) {
          Z => λ (Hlt : Le (S Z) Z). botElim (Id Bool (Eqb Z Z) False) Hlt,
          S (B') Bih => λ (Hlt : Le (S Z) (S B')). Refl },
      S (A') Ih => λ (B : Nat).
        elim B return (λ (Bz : Nat). Le (S (S A')) Bz → Id Bool (Eqb (S A') Bz) False) {
          Z => λ (Hlt : Le (S (S A')) Z). botElim (Id Bool (Eqb (S A') Z) False) Hlt,
          S (B') Bih => λ (Hlt : Le (S (S A')) (S B')). Ih B' Hlt } } }
def CountConsMissRaw : Term := prog_parse {
  λ (M : Nat). λ (H : Nat). λ (T : List Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (Count M T)) (Count M T) Z0) (Count M T))
      Refl (Eqb M H) (IdSymRaw Bool (Eqb M H) False Hq) }
def EqbReflRaw : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Nz : Nat). Id Bool (Eqb Nz Nz) True) {
    Z => Refl,
    S (N') Ih => Ih } }
def Ub : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le H P). Ih } }
def Lb : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Type) {
      Nil => Unit,
      Cons (H) (T) Ih => Σ (Hh : Le P H). Ih } }
def ListRwRaw : Term := prog_parse {
  λ (P : List Nat → Type). λ (X : List Nat). λ (Y : List Nat).
    λ (H : Id (List Nat) X Y). λ (Px : P X).
      j (List Nat) X (λ (Y2 : List Nat). λ (Hh : Id (List Nat) X Y2). P Y2) Px Y H }
def SortedHeadRaw : Term := prog_parse {
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Bound H T) {
      Pair (X) (Y) => X } }
def SortedTailRaw : Term := prog_parse {
  λ (H : Nat). λ (T : List Nat). λ (S0 : Σ (Hb : Bound H T). Sorted T).
    elim S0 return (λ (Q : Σ (Hb : Bound H T). Sorted T). Sorted T) {
      Pair (X) (Y) => Y } }
def UbHeadRaw : Term := prog_parse {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Le H P) {
      Pair (X) (Y) => X } }
def UbTailRaw : Term := prog_parse {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le H P). Ub P T).
    elim U return (λ (Q : Σ (Hu : Le H P). Ub P T). Ub P T) {
      Pair (X) (Y) => Y } }
def LbBoundRaw : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat). Lb P Lz → Bound P Lz) {
      Nil => λ (Hn : Unit). Hn,
      Cons (H) (T) Ih => λ (Hl : Σ (Hh : Le P H). Lb P T).
        elim Hl return (λ (Q : Σ (Hh : Le P H). Lb P T). Le P H) {
          Pair (X) (Y) => X } } }
def BoundAppendRaw : Term := prog_parse {
  λ (H : Nat). λ (P : Nat). λ (T : List Nat). λ (B : List Nat).
    elim T return (λ (Tz : List Nat).
        Bound H Tz → Le H P → Bound H (Append Tz (Cons P B))) {
      Nil => λ (Hb : Unit). λ (Hp : Le H P). Hp,
      Cons (H2) (T2) Ih => λ (Hb : Le H H2). λ (Hp : Le H P). Hb } }
def SortedAppendPivotRaw : Term := prog_parse {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Sa : Sorted A). λ (Ua : Ub P A). λ (Sb : Sorted B). λ (Lb0 : Lb P B).
      elim A return (λ (Az : List Nat).
          Sorted Az → Ub P Az → Sorted (Append Az (Cons P B))) {
        Nil => λ (Sn : Unit). λ (Un : Unit). Pair(LbBoundRaw P B Lb0, Sb),
        Cons (H) (T) Ih => λ (Sc : Sorted (Cons H T)). λ (Uc : Ub P (Cons H T)).
          Pair(BoundAppendRaw H P T B (SortedHeadRaw H T Sc) (UbHeadRaw P H T Uc),
               Ih (SortedTailRaw H T Sc) (UbTailRaw P H T Uc))
      } Sa Ua }
def CountConsLRaw : Term := prog_parse {
  λ (N : Nat). λ (X : Nat). λ (A : List Nat). λ (B : List Nat). λ (C : List Nat).
    λ (H : Id Nat (Add (Count N A) (Count N B)) (Count N C)).
      elim (Eqb N X) return (λ (Bv : Bool).
        Id Nat (Add (boolRec (λ (W : Bool). Nat) (S (Count N A)) (Count N A) Bv) (Count N B))
               (boolRec (λ (W : Bool). Nat) (S (Count N C)) (Count N C) Bv)) {
        True => IdCongrRaw Nat Nat (λ (R : Nat). S R)
                  (Add (Count N A) (Count N B)) (Count N C) H,
        False => H } }
def CountConsRRaw : Term := prog_parse {
  λ (N : Nat). λ (X : Nat). λ (A : List Nat). λ (B : List Nat). λ (C : List Nat).
    λ (H : Id Nat (Add (Count N A) (Count N B)) (Count N C)).
      elim (Eqb N X) return (λ (Bv : Bool).
        Id Nat (Add (Count N A) (boolRec (λ (W : Bool). Nat) (S (Count N B)) (Count N B) Bv))
               (boolRec (λ (W : Bool). Nat) (S (Count N C)) (Count N C) Bv)) {
        True => IdTransRaw Nat (Add (Count N A) (S (Count N B)))
                  (S (Add (Count N A) (Count N B))) (S (Count N C))
                  (AddSuccRaw (Count N A) (Count N B))
                  (IdCongrRaw Nat Nat (λ (R : Nat). S R)
                    (Add (Count N A) (Count N B)) (Count N C) H),
        False => H } }
def LbHeadRaw : Term := prog_parse {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Le P H) {
      Pair (X) (Y) => X } }
def LbTailRaw : Term := prog_parse {
  λ (P : Nat). λ (H : Nat). λ (T : List Nat). λ (U : Σ (Hu : Le P H). Lb P T).
    elim U return (λ (Q : Σ (Hu : Le P H). Lb P T). Lb P T) {
      Pair (X) (Y) => Y } }
def NoAboveOfUbRaw : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Ub P Lz → Π (X : Nat) → Le (S P) X → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S P) X). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le H P). Ub P T). λ (X : Nat). λ (Hx : Le (S P) X).
        IdTransRaw Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMissRaw X H T
            (EqbGtFalseRaw H X (LeTransRaw (S H) (S P) X (UbHeadRaw P H T U) Hx)))
          (Ih (UbTailRaw P H T U) X Hx) } }
def UbOfNoAboveRaw : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        (Π (X : Nat) → Le (S P) X → Id Nat (Count X Lz) Z) → Ub P Lz) {
      Nil => λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (Count X Nil) Z). unit,
      Cons (H) (T) Ih => λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (Count X (Cons H T)) Z).
        Pair(
          elim (Leb H P) return (λ (Bv : Bool). Id Bool (Leb H P) Bv → Le H P) {
            True => λ (E : Id Bool (Leb H P) True). LebTrueLeRaw H P E,
            False => λ (E : Id Bool (Leb H P) False).
              botElim (Le H P)
                (ZnotsRaw (Count H T)
                  (IdTransRaw Nat Z (Count H (Cons H T)) (S (Count H T))
                    (IdSymRaw Nat (Count H (Cons H T)) Z (Hn H (LebFalseGtRaw H P E)))
                    (CountConsHitRaw H H T (EqbReflRaw H))))
          } Refl,
          Ih (λ (X : Nat). λ (Hx : Le (S P) X).
                elim (Eqb X H) return (λ (Bv : Bool). Id Bool (Eqb X H) Bv → Id Nat (Count X T) Z) {
                  True => λ (Eq : Id Bool (Eqb X H) True).
                    botElim (Id Nat (Count X T) Z)
                      (ZnotsRaw (Count X T)
                        (IdTransRaw Nat Z (Count X (Cons H T)) (S (Count X T))
                          (IdSymRaw Nat (Count X (Cons H T)) Z (Hn X Hx))
                          (CountConsHitRaw X H T Eq))),
                  False => λ (Eq : Id Bool (Eqb X H) False).
                    IdTransRaw Nat (Count X T) (Count X (Cons H T)) Z
                      (IdSymRaw Nat (Count X (Cons H T)) (Count X T) (CountConsMissRaw X H T Eq))
                      (Hn X Hx)
                } Refl)) } }
def UbPermRaw : Term := prog_parse {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Ub P B).
      UbOfNoAboveRaw P A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTransRaw Nat (Count X A) (Count X B) Z (Hc X) (NoAboveOfUbRaw P B Hb X Hx)) }
def NoBelowOfLbRaw : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        Lb P Lz → Π (X : Nat) → Le (S X) P → Id Nat (Count X Lz) Z) {
      Nil => λ (U : Unit). λ (X : Nat). λ (Hx : Le (S X) P). Refl,
      Cons (H) (T) Ih => λ (U : Σ (Hh : Le P H). Lb P T). λ (X : Nat). λ (Hx : Le (S X) P).
        IdTransRaw Nat (Count X (Cons H T)) (Count X T) Z
          (CountConsMissRaw X H T
            (EqbLtFalseRaw X H (LeTransRaw (S X) P H Hx (LbHeadRaw P H T U))))
          (Ih (LbTailRaw P H T U) X Hx) } }
def LbOfNoBelowRaw : Term := prog_parse {
  λ (P : Nat). λ (L : List Nat).
    elim L return (λ (Lz : List Nat).
        (Π (X : Nat) → Le (S X) P → Id Nat (Count X Lz) Z) → Lb P Lz) {
      Nil => λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (Count X Nil) Z). unit,
      Cons (H) (T) Ih => λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (Count X (Cons H T)) Z).
        Pair(
          elim (Leb P H) return (λ (Bv : Bool). Id Bool (Leb P H) Bv → Le P H) {
            True => λ (E : Id Bool (Leb P H) True). LebTrueLeRaw P H E,
            False => λ (E : Id Bool (Leb P H) False).
              botElim (Le P H)
                (ZnotsRaw (Count H T)
                  (IdTransRaw Nat Z (Count H (Cons H T)) (S (Count H T))
                    (IdSymRaw Nat (Count H (Cons H T)) Z (Hn H (LebFalseGtRaw P H E)))
                    (CountConsHitRaw H H T (EqbReflRaw H))))
          } Refl,
          Ih (λ (X : Nat). λ (Hx : Le (S X) P).
                elim (Eqb X H) return (λ (Bv : Bool). Id Bool (Eqb X H) Bv → Id Nat (Count X T) Z) {
                  True => λ (Eq : Id Bool (Eqb X H) True).
                    botElim (Id Nat (Count X T) Z)
                      (ZnotsRaw (Count X T)
                        (IdTransRaw Nat Z (Count X (Cons H T)) (S (Count X T))
                          (IdSymRaw Nat (Count X (Cons H T)) Z (Hn X Hx))
                          (CountConsHitRaw X H T Eq))),
                  False => λ (Eq : Id Bool (Eqb X H) False).
                    IdTransRaw Nat (Count X T) (Count X (Cons H T)) Z
                      (IdSymRaw Nat (Count X (Cons H T)) (Count X T) (CountConsMissRaw X H T Eq))
                      (Hn X Hx)
                } Refl)) } }
def LbPermRaw : Term := prog_parse {
  λ (P : Nat). λ (A : List Nat). λ (B : List Nat).
    λ (Hc : Π (N : Nat) → Id Nat (Count N A) (Count N B)). λ (Hb : Lb P B).
      LbOfNoBelowRaw P A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTransRaw Nat (Count X A) (Count X B) Z (Hc X) (NoBelowOfLbRaw P B Hb X Hx)) }
def CountA : Term := prog_parse {
  λ (X : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Nat) Z
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Nat).
        elim (Eqb X H) return (λ (Bz : Bool). Nat) { True => S Ih, False => Ih })
      N A }
def BoundA : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type). Le P H) N A }
def SortedA : Term := prog_parse {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hb : BoundA H K T). Ih) N A }
def UbA : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le H P). Ih) N A }
def LbA : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Type) Unit
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat). λ (Ih : Type).
        Σ (Hh : Le P H). Ih) N A }
def Asingle : Term := prog_parse { λ (X : Nat). acons Z X Arr() }
def SortedHeadARaw : Term := prog_parse {
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). BoundA H K T) {
        Pair (X) (Y) => X } }
def SortedTailARaw : Term := prog_parse {
  λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (S0 : Σ (Hb : BoundA H K T). SortedA K T).
      elim S0 return (λ (Q : Σ (Hb : BoundA H K T). SortedA K T). SortedA K T) {
        Pair (X) (Y) => Y } }
def UbHeadARaw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). Le H P) {
        Pair (X) (Y) => X } }
def UbTailARaw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hu : Le H P). UbA P K T).
      elim U return (λ (Q : Σ (Hu : Le H P). UbA P K T). UbA P K T) {
        Pair (X) (Y) => Y } }
def LbBoundARaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). LbA P M B → BoundA P M B)
      (λ (Hn : Unit). Hn)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : LbA P K T → BoundA P K T).
          λ (Hl : Σ (Hh : Le P H). LbA P K T).
            elim Hl return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) {
              Pair (X) (Y) => X })
      N A }
def BoundArrCatRaw : Term := prog_parse {
  λ (H : Nat). λ (P : Nat). λ (K : Nat). λ (T : Array K Nat).
    λ (Q : Nat). λ (B : Array Q Nat).
      arrRec Nat (λ (M : Nat). λ (Tz : Array M Nat).
          BoundA H M Tz → Le H P →
            BoundA H (Add M (S Q)) (arrCat M (S Q) Tz (arrCat 1 Q (Asingle P) B)))
        (λ (Hb : Unit). λ (Hp : Le H P). Hp)
        (λ (K2 : Nat). λ (H2 : Nat). λ (T2 : Array K2 Nat).
          λ (Ih : BoundA H K2 T2 → Le H P →
              BoundA H (Add K2 (S Q)) (arrCat K2 (S Q) T2 (arrCat 1 Q (Asingle P) B))).
            λ (Hb : Le H H2). λ (Hp : Le H P). Hb)
        K T }
def SortedArrCatRaw : Term := prog_parse {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Sa : SortedA M A). λ (Ua : UbA P M A). λ (Sb : SortedA Q B). λ (Lb0 : LbA P Q B).
      arrRec Nat (λ (Mz : Nat). λ (Az : Array Mz Nat).
          SortedA Mz Az → UbA P Mz Az →
            SortedA (Add Mz (S Q)) (arrCat Mz (S Q) Az (arrCat 1 Q (Asingle P) B)))
        (λ (Sn : Unit). λ (Un : Unit). Pair(LbBoundARaw P Q B Lb0, Sb))
        (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
          λ (Ih : SortedA K T → UbA P K T →
              SortedA (Add K (S Q)) (arrCat K (S Q) T (arrCat 1 Q (Asingle P) B))).
            λ (Sc : Σ (Hb : BoundA H K T). SortedA K T).
              λ (Uc : Σ (Hu : Le H P). UbA P K T).
                Pair(BoundArrCatRaw H P K T Q B (SortedHeadARaw K H T Sc) (UbHeadARaw P K H T Uc),
                     Ih (SortedTailARaw K H T Sc) (UbTailARaw P K H T Uc)))
        M A Sa Ua }
def CountArrCatRaw : Term := prog_parse {
  λ (X : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    arrRec Nat (λ (Mz : Nat). λ (Az : Array Mz Nat).
        Id Nat (CountA X (Add Mz Q) (arrCat Mz Q Az B))
               (Add (CountA X Mz Az) (CountA X Q B)))
      Refl
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : Id Nat (CountA X (Add K Q) (arrCat K Q T B))
                       (Add (CountA X K T) (CountA X Q B))).
          elim (Eqb X H) return (λ (Bv : Bool).
            Id Nat (boolRec (λ (W : Bool). Nat)
                     (S (CountA X (Add K Q) (arrCat K Q T B)))
                     (CountA X (Add K Q) (arrCat K Q T B)) Bv)
                   (Add (boolRec (λ (W : Bool). Nat)
                     (S (CountA X K T)) (CountA X K T) Bv) (CountA X Q B))) {
            True => IdCongrRaw Nat Nat (λ (N : Nat). S N)
                      (CountA X (Add K Q) (arrCat K Q T B))
                      (Add (CountA X K T) (CountA X Q B)) Ih,
            False => Ih })
      M A }
def CountAconsHitRaw : Term := prog_parse {
  λ (M : Nat). λ (A : Nat). λ (K : Nat). λ (L : Array K Nat). λ (Hq : Id Bool (Eqb M A) True).
    j Bool True
      (λ (Z0 : Bool). λ (H : Id Bool True Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K L)) (CountA M K L) Z0)
               (S (CountA M K L)))
      Refl (Eqb M A) (IdSymRaw Bool (Eqb M A) True Hq) }
def CountAconsMissRaw : Term := prog_parse {
  λ (M : Nat). λ (H : Nat). λ (K : Nat). λ (T : Array K Nat). λ (Hq : Id Bool (Eqb M H) False).
    j Bool False
      (λ (Z0 : Bool). λ (Hh : Id Bool False Z0).
        Id Nat (boolRec (λ (W : Bool). Nat) (S (CountA M K T)) (CountA M K T) Z0)
               (CountA M K T))
      Refl (Eqb M H) (IdSymRaw Bool (Eqb M H) False Hq) }
def LbHeadA : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). Le P H) { Pair (X) (Y) => X } }
def LbTailA : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
    λ (U : Σ (Hh : Le P H). LbA P K T).
      elim U return (λ (Q : Σ (Hh : Le P H). LbA P K T). LbA P K T) { Pair (X) (Y) => Y } }
def NoAboveOfUbARaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        UbA P M Az → Π (X : Nat) → Le (S P) X → Id Nat (CountA X M Az) Z)
      (λ (U : Unit). λ (X : Nat). λ (Hx : Le (S P) X). Refl)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : UbA P K T → Π (X : Nat) → Le (S P) X → Id Nat (CountA X K T) Z).
          λ (U : Σ (Hh : Le H P). UbA P K T). λ (X : Nat). λ (Hx : Le (S P) X).
            IdTransRaw Nat (CountA X (S K) (acons K H T)) (CountA X K T) Z
              (CountAconsMissRaw X H K T
                (EqbGtFalseRaw H X (LeTransRaw (S H) (S P) X (UbHeadARaw P K H T U) Hx)))
              (Ih (UbTailARaw P K H T U) X Hx))
      N A }
def UbOfNoAboveARaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        (Π (X : Nat) → Le (S P) X → Id Nat (CountA X M Az) Z) → UbA P M Az)
      (λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (CountA X Z Arr()) Z). unit)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : (Π (X : Nat) → Le (S P) X → Id Nat (CountA X K T) Z) → UbA P K T).
          λ (Hn : Π (X : Nat) → Le (S P) X → Id Nat (CountA X (S K) (acons K H T)) Z).
            Pair(
              elim (Leb H P) return (λ (Bv : Bool). Id Bool (Leb H P) Bv → Le H P) {
                True => λ (E : Id Bool (Leb H P) True). LebTrueLeRaw H P E,
                False => λ (E : Id Bool (Leb H P) False).
                  botElim (Le H P)
                    (ZnotsRaw (CountA H K T)
                      (IdTransRaw Nat Z (CountA H (S K) (acons K H T)) (S (CountA H K T))
                        (IdSymRaw Nat (CountA H (S K) (acons K H T)) Z (Hn H (LebFalseGtRaw H P E)))
                        (CountAconsHitRaw H H K T (EqbReflRaw H))))
              } Refl,
              Ih (λ (X : Nat). λ (Hx : Le (S P) X).
                    elim (Eqb X H) return (λ (Bv : Bool).
                        Id Bool (Eqb X H) Bv → Id Nat (CountA X K T) Z) {
                      True => λ (Eq : Id Bool (Eqb X H) True).
                        botElim (Id Nat (CountA X K T) Z)
                          (ZnotsRaw (CountA X K T)
                            (IdTransRaw Nat Z (CountA X (S K) (acons K H T)) (S (CountA X K T))
                              (IdSymRaw Nat (CountA X (S K) (acons K H T)) Z (Hn X Hx))
                              (CountAconsHitRaw X H K T Eq))),
                      False => λ (Eq : Id Bool (Eqb X H) False).
                        IdTransRaw Nat (CountA X K T) (CountA X (S K) (acons K H T)) Z
                          (IdSymRaw Nat (CountA X (S K) (acons K H T)) (CountA X K T)
                            (CountAconsMissRaw X H K T Eq))
                          (Hn X Hx)
                    } Refl)))
      N A }
def UbPermARaw : Term := prog_parse {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : UbA P Q B).
      UbOfNoAboveARaw P M A (λ (X : Nat). λ (Hx : Le (S P) X).
        IdTransRaw Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoAboveOfUbARaw P Q B Hb X Hx)) }
def NoBelowOfLbARaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        LbA P M Az → Π (X : Nat) → Le (S X) P → Id Nat (CountA X M Az) Z)
      (λ (U : Unit). λ (X : Nat). λ (Hx : Le (S X) P). Refl)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : LbA P K T → Π (X : Nat) → Le (S X) P → Id Nat (CountA X K T) Z).
          λ (U : Σ (Hh : Le P H). LbA P K T). λ (X : Nat). λ (Hx : Le (S X) P).
            IdTransRaw Nat (CountA X (S K) (acons K H T)) (CountA X K T) Z
              (CountAconsMissRaw X H K T
                (EqbLtFalseRaw X H (LeTransRaw (S X) P H Hx (LbHeadA P K H T U))))
              (Ih (LbTailA P K H T U) X Hx))
      N A }
def LbOfNoBelowARaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (Az : Array M Nat).
        (Π (X : Nat) → Le (S X) P → Id Nat (CountA X M Az) Z) → LbA P M Az)
      (λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (CountA X Z Arr()) Z). unit)
      (λ (K : Nat). λ (H : Nat). λ (T : Array K Nat).
        λ (Ih : (Π (X : Nat) → Le (S X) P → Id Nat (CountA X K T) Z) → LbA P K T).
          λ (Hn : Π (X : Nat) → Le (S X) P → Id Nat (CountA X (S K) (acons K H T)) Z).
            Pair(
              elim (Leb P H) return (λ (Bv : Bool). Id Bool (Leb P H) Bv → Le P H) {
                True => λ (E : Id Bool (Leb P H) True). LebTrueLeRaw P H E,
                False => λ (E : Id Bool (Leb P H) False).
                  botElim (Le P H)
                    (ZnotsRaw (CountA H K T)
                      (IdTransRaw Nat Z (CountA H (S K) (acons K H T)) (S (CountA H K T))
                        (IdSymRaw Nat (CountA H (S K) (acons K H T)) Z (Hn H (LebFalseGtRaw P H E)))
                        (CountAconsHitRaw H H K T (EqbReflRaw H))))
              } Refl,
              Ih (λ (X : Nat). λ (Hx : Le (S X) P).
                    elim (Eqb X H) return (λ (Bv : Bool).
                        Id Bool (Eqb X H) Bv → Id Nat (CountA X K T) Z) {
                      True => λ (Eq : Id Bool (Eqb X H) True).
                        botElim (Id Nat (CountA X K T) Z)
                          (ZnotsRaw (CountA X K T)
                            (IdTransRaw Nat Z (CountA X (S K) (acons K H T)) (S (CountA X K T))
                              (IdSymRaw Nat (CountA X (S K) (acons K H T)) Z (Hn X Hx))
                              (CountAconsHitRaw X H K T Eq))),
                      False => λ (Eq : Id Bool (Eqb X H) False).
                        IdTransRaw Nat (CountA X K T) (CountA X (S K) (acons K H T)) Z
                          (IdSymRaw Nat (CountA X (S K) (acons K H T)) (CountA X K T)
                            (CountAconsMissRaw X H K T Eq))
                          (Hn X Hx)
                    } Refl)))
      N A }
def LbPermARaw : Term := prog_parse {
  λ (P : Nat). λ (M : Nat). λ (A : Array M Nat). λ (Q : Nat). λ (B : Array Q Nat).
    λ (Hc : Π (X : Nat) → Id Nat (CountA X M A) (CountA X Q B)). λ (Hb : LbA P Q B).
      LbOfNoBelowARaw P M A (λ (X : Nat). λ (Hx : Le (S X) P).
        IdTransRaw Nat (CountA X M A) (CountA X Q B) Z (Hc X)
          (NoBelowOfLbARaw P Q B Hb X Hx)) }
def CountSwap2Raw : Term := prog_parse {
  λ (M : Nat). λ (A : Nat). λ (B : Nat).
    elim (Eqb M A) generalizing (Id Nat (CountA M 2 Arr(B, A)) (CountA M 2 Arr(A, B))) {
      True => elim (Eqb M B) generalizing
        (Id Nat (boolRec (λ (W : Bool). Nat) (S (S Z)) (S Z) (Eqb M B))
                (S (boolRec (λ (W : Bool). Nat) (S Z) Z (Eqb M B)))) {
        True => Refl, False => Refl },
      False => Refl } }
def NatRwRaw : Term := prog_parse {
  λ (P : Nat → Type). λ (X : Nat). λ (Y : Nat). λ (H : Id Nat X Y). λ (Px : P X).
    j Nat X (λ (Y2 : Nat). λ (Hh : Id Nat X Y2). P Y2) Px Y H }
def LeZeroEqRaw : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Z0 : Nat). Le Z0 Z → Id Nat Z0 Z) {
    Z => λ (H : Le Z Z). Refl,
    S (N2) Ih => λ (H : Bot). botElim (Id Nat (S N2) Z) H } }
def SortedANilRaw : Term := prog_parse {
  λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Id Nat M Z → SortedA M B)
      (λ (H : Id Nat Z Z). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : Id Nat K Z → SortedA K T).
          λ (H : Id Nat (S K) Z).
            botElim (SortedA (S K) (acons K Hh T)) (ZnotsRaw K (IdSymRaw Nat (S K) Z H)))
      N A }
def SplitAL : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Π (Kz : Nat) → Type)
      (λ (Kz : Nat). Unit)
      (λ (M : Nat). λ (H : Nat). λ (T : Array M Nat). λ (Ih : Π (Kz : Nat) → Type).
        λ (Kz : Nat).
          elim Kz return (λ (W : Nat). Type) {
            Z => Σ (Hh : Le P H). Ih Z,
            S (K2) Rec => Σ (Hh : Le H P). Ih K2 })
      N A K }
def PartA : Term := prog_parse {
  λ (Pv : Nat). λ (K : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). Π (Kz : Nat) → Type)
      (λ (Kz : Nat). Unit)
      (λ (M : Nat). λ (H : Nat). λ (T : Array M Nat). λ (Ih : Π (Kz : Nat) → Type).
        λ (Kz : Nat).
          elim Kz return (λ (W : Nat). Type) {
            Z => Σ (He : Id Nat H Pv). LbA Pv M T,
            S (K2) Rec => Σ (Hh : Le H Pv). Ih K2 })
      N A K }
def SplitANilRaw : Term := prog_parse {
  λ (P : Nat). λ (Kz : Nat). λ (N : Nat). λ (A : Array N Nat). λ (Hz : Id Nat N Z).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat).
        Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M B)
      (λ (K2 : Nat). λ (H : Id Nat Z Z). unit)
      (λ (M : Nat). λ (Hh : Nat). λ (T : Array M Nat).
        λ (Ih : Π (K2 : Nat) → Id Nat M Z → SplitAL P K2 M T).
          λ (K2 : Nat). λ (H : Id Nat (S M) Z).
            botElim (SplitAL P K2 (S M) (acons M Hh T)) (ZnotsRaw M (IdSymRaw Nat (S M) Z H)))
      N A Kz Hz }
def SplitA0LbRaw : Term := prog_parse {
  λ (P : Nat). λ (N : Nat). λ (A : Array N Nat).
    arrRec Nat (λ (M : Nat). λ (B : Array M Nat). SplitAL P Z M B → LbA P M B)
      (λ (H : Unit). unit)
      (λ (K : Nat). λ (Hh : Nat). λ (T : Array K Nat).
        λ (Ih : SplitAL P Z K T → LbA P K T).
          λ (S0 : Σ (H2 : Le P Hh). SplitAL P Z K T).
            elim S0 return (λ (Qz : Σ (H2 : Le P Hh). SplitAL P Z K T). LbA P (S K) (acons K Hh T)) {
              Pair (U) (V) => Pair(U, Ih V) })
      N A }
def SplitACatE1Raw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        SplitAL P (S Kz) (Add Kz Mm) (arrCat Kz Mm Lz W) →
          Σ (Hu : UbA P Kz Lz). SplitAL P (S Z) Mm W)
      (λ (H : SplitAL P (S Z) Mm W). Pair(unit, H))
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W) →
                  Σ (Hu : UbA P K2 T). SplitAL P (S Z) Mm W).
          λ (S0 : Σ (H2 : Le Hh P). SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W)).
            elim S0 return (λ (Qz : Σ (H2 : Le Hh P).
                                SplitAL P (S K2) (Add K2 Mm) (arrCat K2 Mm T W)).
                Σ (Hu : UbA P (S K2) (acons K2 Hh T)). SplitAL P (S Z) Mm W) {
              Pair (U) (V) =>
                elim (Ih V) return (λ (Qz2 : Σ (Hu : UbA P K2 T). SplitAL P (S Z) Mm W).
                    Σ (Hu : UbA P (S K2) (acons K2 Hh T)). SplitAL P (S Z) Mm W) {
                  Pair (A1) (B1) => Pair(Pair(U, A1), B1) } })
      K L }
def SplitACatI0Raw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        UbA P Kz Lz → SplitAL P Z Mm W → SplitAL P Kz (Add Kz Mm) (arrCat Kz Mm Lz W))
      (λ (U : Unit). λ (H : SplitAL P Z Mm W). H)
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : UbA P K2 T → SplitAL P Z Mm W →
                  SplitAL P K2 (Add K2 Mm) (arrCat K2 Mm T W)).
          λ (U : Σ (H2 : Le Hh P). UbA P K2 T). λ (H : SplitAL P Z Mm W).
            elim U return (λ (Qz : Σ (H2 : Le Hh P). UbA P K2 T).
                SplitAL P (S K2) (Add (S K2) Mm) (arrCat (S K2) Mm (acons K2 Hh T) W)) {
              Pair (A1) (B1) => Pair(A1, Ih B1 H) })
      K L }
def PartACatI0Raw : Term := prog_parse {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        UbA Pv Kz Lz → PartA Pv Z Mm W → PartA Pv Kz (Add Kz Mm) (arrCat Kz Mm Lz W))
      (λ (U : Unit). λ (H : PartA Pv Z Mm W). H)
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : UbA Pv K2 T → PartA Pv Z Mm W →
                  PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
          λ (U : Σ (H2 : Le Hh Pv). UbA Pv K2 T). λ (H : PartA Pv Z Mm W).
            elim U return (λ (Qz : Σ (H2 : Le Hh Pv). UbA Pv K2 T).
                PartA Pv (S K2) (Add (S K2) Mm) (arrCat (S K2) Mm (acons K2 Hh T) W)) {
              Pair (A1) (B1) => Pair(A1, Ih B1 H) })
      K L }
def PartACatE0Raw : Term := prog_parse {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    arrRec Nat (λ (Kz : Nat). λ (Lz : Array Kz Nat).
        PartA Pv Kz (Add Kz Mm) (arrCat Kz Mm Lz W) →
          Σ (Hu : UbA Pv Kz Lz). PartA Pv Z Mm W)
      (λ (H : PartA Pv Z Mm W). Pair(unit, H))
      (λ (K2 : Nat). λ (Hh : Nat). λ (T : Array K2 Nat).
        λ (Ih : PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W) →
                  Σ (Hu : UbA Pv K2 T). PartA Pv Z Mm W).
          λ (S0 : Σ (H2 : Le Hh Pv). PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
            elim S0 return (λ (Qz : Σ (H2 : Le Hh Pv).
                                PartA Pv K2 (Add K2 Mm) (arrCat K2 Mm T W)).
                Σ (Hu : UbA Pv (S K2) (acons K2 Hh T)). PartA Pv Z Mm W) {
              Pair (U) (V) =>
                elim (Ih V) return (λ (Qz2 : Σ (Hu : UbA Pv K2 T). PartA Pv Z Mm W).
                    Σ (Hu : UbA Pv (S K2) (acons K2 Hh T)). PartA Pv Z Mm W) {
                  Pair (A1) (B1) => Pair(Pair(U, A1), B1) } })
      K L }
def SplitACatUbRaw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1Raw P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). UbA P K L) {
          Pair (U) (V) => U } }
def SplitACatRestRaw : Term := prog_parse {
  λ (P : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)).
      elim (SplitACatE1Raw P K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA P K L). SplitAL P (S Z) Mm W). SplitAL P (S Z) Mm W) {
          Pair (U) (V) => V } }
def SplitA1HeadRaw : Term := prog_parse {
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). Le Yv P) {
        Pair (U) (V) => U } }
def SplitA1TailRaw : Term := prog_parse {
  λ (P : Nat). λ (R : Nat). λ (G : Array R Nat). λ (Yv : Nat).
    λ (S0 : Σ (Hh : Le Yv P). SplitAL P Z R G).
      elim S0 return (λ (Qz : Σ (Hh : Le Yv P). SplitAL P Z R G). SplitAL P Z R G) {
        Pair (U) (V) => V } }
def PartACatUbRaw : Term := prog_parse {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0Raw Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). UbA Pv K L) {
          Pair (U) (V) => U } }
def PartACatRestRaw : Term := prog_parse {
  λ (Pv : Nat). λ (K : Nat). λ (Mm : Nat). λ (L : Array K Nat). λ (W : Array Mm Nat).
    λ (S0 : PartA Pv K (Add K Mm) (arrCat K Mm L W)).
      elim (PartACatE0Raw Pv K Mm L W S0)
        return (λ (Qz : Σ (Hu : UbA Pv K L). PartA Pv Z Mm W). PartA Pv Z Mm W) {
          Pair (U) (V) => V } }
def PartA0EqRaw : Term := prog_parse {
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). Id Nat Ev Pv) {
        Pair (U) (V) => U } }
def PartA0LbRaw : Term := prog_parse {
  λ (Pv : Nat). λ (Jj : Nat). λ (G : Array Jj Nat). λ (Ev : Nat).
    λ (S0 : Σ (He : Id Nat Ev Pv). LbA Pv Jj G).
      elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). LbA Pv Jj G). LbA Pv Jj G) {
        Pair (U) (V) => V } }
def BumpN : Term := prog_parse {
  λ (B : Bool). λ (C : Nat). elim B return (λ (W : Bool). Nat) { True => S C, False => C } }
def CountAconsCongrRaw : Term := prog_parse {
  λ (Q : Nat). λ (H : Nat). λ (K : Nat). λ (T1 : Array K Nat). λ (T2 : Array K Nat).
    λ (Hc : Id Nat (CountA Q K T1) (CountA Q K T2)).
      IdCongrRaw Nat Nat (λ (C : Nat). BumpN (Eqb Q H) C)
        (CountA Q K T1) (CountA Q K T2) Hc }
def BumpCommRaw : Term := prog_parse {
  λ (B1 : Bool). λ (B2 : Bool). λ (Cl : Nat). λ (Cg : Nat).
    elim B1 return (λ (W : Bool).
        Id Nat (BumpN B2 (Add Cl (BumpN W Cg))) (BumpN W (Add Cl (BumpN B2 Cg)))) {
      True =>
        elim B2 return (λ (W2 : Bool).
            Id Nat (BumpN W2 (Add Cl (S Cg))) (S (Add Cl (BumpN W2 Cg)))) {
          True => Refl,
          False => AddSuccRaw Cl Cg },
      False =>
        elim B2 return (λ (W2 : Bool).
            Id Nat (BumpN W2 (Add Cl Cg)) (Add Cl (BumpN W2 Cg))) {
          True => IdSymRaw Nat (Add Cl (S Cg)) (S (Add Cl Cg)) (AddSuccRaw Cl Cg),
          False => Refl } } }
def CountSwapARaw : Term := prog_parse {
  λ (Q : Nat). λ (X : Nat). λ (Y : Nat). λ (K : Nat). λ (L : Array K Nat).
  λ (R : Nat). λ (G : Array R Nat).
    IdTransRaw Nat
      (CountA Q (S (Add K (S R))) (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
      (BumpN (Eqb Q Y) (Add (CountA Q K L) (BumpN (Eqb Q X) (CountA Q R G))))
      (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
      (IdCongrRaw Nat Nat (λ (C : Nat). BumpN (Eqb Q Y) C)
         (CountA Q (Add K (S R)) (arrCat K (S R) L (acons R X G)))
         (Add (CountA Q K L) (CountA Q (S R) (acons R X G)))
         (CountArrCatRaw Q K L (S R) (acons R X G)))
      (IdTransRaw Nat
        (BumpN (Eqb Q Y) (Add (CountA Q K L) (BumpN (Eqb Q X) (CountA Q R G))))
        (BumpN (Eqb Q X) (Add (CountA Q K L) (BumpN (Eqb Q Y) (CountA Q R G))))
        (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
        (BumpCommRaw (Eqb Q X) (Eqb Q Y) (CountA Q K L) (CountA Q R G))
        (IdSymRaw Nat
          (CountA Q (S (Add K (S R))) (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G))))
          (BumpN (Eqb Q X) (Add (CountA Q K L) (BumpN (Eqb Q Y) (CountA Q R G))))
          (IdCongrRaw Nat Nat (λ (C : Nat). BumpN (Eqb Q X) C)
             (CountA Q (Add K (S R)) (arrCat K (S R) L (acons R Y G)))
             (Add (CountA Q K L) (CountA Q (S R) (acons R Y G)))
             (CountArrCatRaw Q K L (S R) (acons R Y G))))) }
def NextR : Term := prog_parse {
  λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => Z, S (C2) Rc => S(R) } }
def NextC : Term := prog_parse {
  λ (B : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => B, S (C2) Rc => C2 } }
def NextQ : Term := prog_parse {
  λ (Q : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Nat) { Z => S(Q), S (C2) Rc => Q } }
def ModC : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat). Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). R,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat).
        Rec B (NextR R C) (NextC B C) } }
def Mod : Term := prog_parse {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => ModC A B2 Z B2 } }
def DivC : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) → Π (Q : Nat) → Nat) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat). Q,
      S (A2) Rec => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (Q : Nat).
        Rec B (NextR R C) (NextC B C) (NextQ Q C) } }
def Div : Term := prog_parse {
  λ (A : Nat). λ (B : Nat).
    elim B return (λ (Bz : Nat). Nat) { Z => Z, S (B2) Rb => DivC A B2 Z B2 Z } }
def StepInvRaw : Term := prog_parse {
  λ (B : Nat). λ (R : Nat). λ (C : Nat).
    elim C return (λ (Cz : Nat). Le (Add R Cz) B → Le (Add (NextR R Cz) (NextC B Cz)) B) {
      Z => λ (H : Le (Add R Z) B). LeReflRaw B,
      S (C2) Rc => λ (H : Le (Add R (S C2)) B).
        LeRwLRaw B (Add R (S C2)) (S (Add R C2)) (AddSuccRaw R C2) H } }
def ModCLtRaw : Term := prog_parse {
  λ (A : Nat).
    elim A return (λ (Az : Nat).
        Π (B : Nat) → Π (R : Nat) → Π (C : Nat) →
          Le (Add R C) B → Le (S (ModC Az B R C)) (S B)) {
      Z => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             LeTransRaw R (Add R C) B (LeAddRaw R C) H,
      S (A2) Ih => λ (B : Nat). λ (R : Nat). λ (C : Nat). λ (H : Le (Add R C) B).
             Ih B (NextR R C) (NextC B C) (StepInvRaw B R C H) } }
def ModLtNRaw : Term := prog_parse {
  λ (A : Nat). λ (N : Nat).
    elim N return (λ (Nz : Nat). Le (S Z) Nz → Le (S (Mod A Nz)) Nz) {
      Z => λ (H : Le (S Z) Z). botElim (Le (S (Mod A Z)) Z) H,
      S (B2) Rb => λ (H : Le (S Z) (S B2)). ModCLtRaw A B2 Z B2 (LeReflRaw B2) } }
def ModDecRaw : Term := prog_parse {
  λ (I : Nat).
    elim I return (λ (Iz : Nat).
        Π (N : Nat) → Le (S Iz) N → Σ (R : Nat). Id Nat N (Add Iz (S R))) {
      Z => λ (N : Nat).
        elim N return (λ (Nz : Nat). Le (S Z) Nz → Σ (R : Nat). Id Nat Nz (Add Z (S R))) {
          Z => λ (H : Le (S Z) Z). botElim (Σ (R : Nat). Id Nat Z (Add Z (S R))) H,
          S (N2) Ihn => λ (H : Le (S Z) (S N2)). Pair(N2, Refl) },
      S (I2) Ih => λ (N : Nat).
        elim N return (λ (Nz : Nat).
            Le (S (S I2)) Nz → Σ (R : Nat). Id Nat Nz (Add (S I2) (S R))) {
          Z => λ (H : Le (S (S I2)) Z). botElim (Σ (R : Nat). Id Nat Z (Add (S I2) (S R))) H,
          S (N2) Ihn => λ (H : Le (S (S I2)) (S N2)).
            elim (Ih N2 H) return (λ (Q : Σ (R : Nat). Id Nat N2 (Add I2 (S R))).
                Σ (R : Nat). Id Nat (S N2) (Add (S I2) (S R))) {
              Pair (X) (Y) =>
                Pair(X, IdCongrRaw Nat Nat (λ (Nn : Nat). S Nn) N2 (Add I2 (S X)) Y) } } } }
def Mul : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). elim A return (λ (Az : Nat). Nat) {
    Z => Z, S (A2) Rec => Add B Rec } }
def AddSwapLRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    elim A return (λ (Az : Nat). Id Nat (Add Az (Add B C)) (Add B (Add Az C))) {
      Z => Refl,
      S (A2) Ih =>
        IdTransRaw Nat (S (Add A2 (Add B C))) (S (Add B (Add A2 C))) (Add B (S (Add A2 C)))
          (IdCongrRaw Nat Nat (λ (X : Nat). S X) (Add A2 (Add B C)) (Add B (Add A2 C)) Ih)
          (IdSymRaw Nat (Add B (S (Add A2 C))) (S (Add B (Add A2 C))) (AddSuccRaw B (Add A2 C))) } }
def AddInterchangeRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (D : Nat).
    IdTransRaw Nat (Add (Add A B) (Add C D)) (Add A (Add B (Add C D))) (Add (Add A C) (Add B D))
      (AddAssocRaw A B (Add C D))
      (IdTransRaw Nat (Add A (Add B (Add C D))) (Add A (Add C (Add B D))) (Add (Add A C) (Add B D))
        (IdCongrRaw Nat Nat (λ (X : Nat). Add A X) (Add B (Add C D)) (Add C (Add B D))
          (AddSwapLRaw B C D))
        (IdSymRaw Nat (Add (Add A C) (Add B D)) (Add A (Add C (Add B D)))
          (AddAssocRaw A C (Add B D)))) }
def MulSuccRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat).
    elim A return (λ (Az : Nat). Id Nat (Mul Az (S B)) (Add Az (Mul Az B))) {
      Z => Refl,
      S (A2) Ih =>
        IdCongrRaw Nat Nat (λ (X : Nat). S X)
          (Add B (Mul A2 (S B))) (Add A2 (Add B (Mul A2 B)))
          (IdTransRaw Nat (Add B (Mul A2 (S B))) (Add B (Add A2 (Mul A2 B)))
            (Add A2 (Add B (Mul A2 B)))
            (IdCongrRaw Nat Nat (λ (X : Nat). Add B X) (Mul A2 (S B)) (Add A2 (Mul A2 B)) Ih)
            (AddSwapLRaw B A2 (Mul A2 B))) } }
def MulAddRRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (C : Nat).
    elim A return (λ (Az : Nat).
        Id Nat (Mul Az (Add B C)) (Add (Mul Az B) (Mul Az C))) {
      Z => Refl,
      S (A2) Ih =>
        IdTransRaw Nat (Add (Add B C) (Mul A2 (Add B C)))
          (Add (Add B C) (Add (Mul A2 B) (Mul A2 C)))
          (Add (Add B (Mul A2 B)) (Add C (Mul A2 C)))
          (IdCongrRaw Nat Nat (λ (X : Nat). Add (Add B C) X)
            (Mul A2 (Add B C)) (Add (Mul A2 B) (Mul A2 C)) Ih)
          (AddInterchangeRaw B C (Mul A2 B) (Mul A2 C)) } }
def MulTwoDoubleRaw : Term := prog_parse {
  λ (A : Nat). λ (C : Nat).
    IdTransRaw Nat (Mul A (Mul 2 C)) (Mul A (Add C C)) (Add (Mul A C) (Mul A C))
      (IdCongrRaw Nat Nat (λ (X : Nat). Mul A (Add C X)) (Add C Z) C (AddZeroRaw C))
      (MulAddRRaw A C C) }
def LeAddMonoRRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (K : Nat). λ (H : Le A B).
    LeRwRRaw (Add A K) (Add K B) (Add B K) (AddCommRaw K B)
      (LeRwLRaw (Add K B) (Add K A) (Add A K) (AddCommRaw K A) (LeAddMonoLRaw K A B H)) }
def LeAddMonoRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (D : Nat). λ (H1 : Le A B). λ (H2 : Le C D).
    LeTransRaw (Add A C) (Add B C) (Add B D) (LeAddMonoRRaw A B C H1) (LeAddMonoLRaw B C D H2) }
def LeMulRRaw : Term := prog_parse {
  λ (A : Nat). λ (B : Nat). λ (C : Nat). λ (H : Le B C).
    elim A return (λ (Az : Nat). Le (Mul Az B) (Mul Az C)) {
      Z => unit,
      S (A2) Ih => LeAddMonoRaw B C (Mul A2 B) (Mul A2 C) H Ih } }
def Le5M4Raw : Term := prog_parse {
  λ (C : Nat). λ (H : Le 2 C).
    LeTransRaw 5 (Mul 4 2) (Mul 4 C) unit (LeMulRRaw 4 2 C H) }
def FiveN4ZeroRaw : Term := prog_parse {
  λ (N : Nat). elim N return (λ (Nz : Nat). Le (Mul 5 Nz) 4 → Id Nat Nz Z) {
    Z => λ (H : Le (Mul 5 Z) 4). Refl,
    S (N2) Ih => λ (H : Le (Mul 5 (S N2)) 4).
      botElim (Id Nat (S N2) Z)
        (LeRwLRaw 4 (Mul 5 (S N2)) (Add 5 (Mul 5 N2)) (MulSuccRaw 5 N2) H) } }
def LeLebTrueRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Le Az B → Id Bool (Leb Az B) True) {
    Z => λ (B : Nat). λ (H : Le Z B). Refl,
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Le (S A2) Bz → Id Bool (Leb (S A2) Bz) True) {
        Z => λ (H : Le (S A2) Z). botElim (Id Bool (Leb (S A2) Z) True) H,
        S (B2) Ihb => λ (H : Le (S A2) (S B2)). Ih B2 H } } }
def EqbTrueEqRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Az : Nat).
      Π (B : Nat) → Id Bool (Eqb Az B) True → Id Nat Az B) {
    Z => λ (B : Nat). elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) True → Id Nat Z Bz) {
      Z => λ (H : Id Bool (Eqb Z Z) True). Refl,
      S (B2) Ihb => λ (H : Id Bool (Eqb Z (S B2)) True).
        botElim (Id Nat Z (S B2)) (BoolFTRaw H) },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Id Bool (Eqb (S A2) Bz) True → Id Nat (S A2) Bz) {
        Z => λ (H : Id Bool (Eqb (S A2) Z) True). botElim (Id Nat (S A2) Z) (BoolFTRaw H),
        S (B2) Ihb => λ (H : Id Bool (Eqb (S A2) (S B2)) True).
          IdCongrRaw Nat Nat (λ (X : Nat). S X) A2 B2 (Ih B2 H) } } }
def EqbSymRaw : Term := prog_parse {
  λ (A : Nat). elim A return (λ (Az : Nat). Π (B : Nat) → Id Bool (Eqb Az B) (Eqb B Az)) {
    Z => λ (B : Nat). elim B return (λ (Bz : Nat). Id Bool (Eqb Z Bz) (Eqb Bz Z)) {
      Z => Refl, S (B2) Ihb => Refl },
    S (A2) Ih => λ (B : Nat).
      elim B return (λ (Bz : Nat). Id Bool (Eqb (S A2) Bz) (Eqb Bz (S A2))) {
        Z => Refl, S (B2) Ihb => Ih B2 } } }
def IfDecRaw : Term := prog_parse {
  λ (B : Bool). λ (T : Type).
    λ (F : Id Bool B True → T). λ (G : Id Bool B False → T).
      boolRec (λ (Bm : Bool). (Id Bool Bm True → T) → ((Id Bool Bm False → T) → T))
        (λ (F2 : Id Bool True True → T). λ (G2 : Id Bool True False → T). F2 Refl)
        (λ (F2 : Id Bool False True → T). λ (G2 : Id Bool False False → T). G2 Refl)
        B F G }
/-- **The load-ledger arithmetic, Div-free.** The hashmap's 4/5 load factor is
    carried without floor division: `n ≤ ⌊4·cap/5⌋` is, for integers, exactly
    `5·n ≤ 4·cap`, and "n exceeds the threshold" is exactly `5·n > 4·cap` — so the
    packed ledger stores `Mul 4 cap` and compares against `Mul 5 n`, and no
    floor-division lemma library is needed. `LedgerGrowRaw` is the one fact resize
    owes: a map at the threshold that takes one more entry fits under the DOUBLED
    capacity's threshold. -/
def LedgerGrowRaw : Term := prog_parse {
  λ (C : Nat). λ (N : Nat). λ (H1 : Le (S Z) C). λ (Hle : Le (Mul 5 N) (Mul 4 C)).
    IfDecRaw (Leb 2 C) (Le (Mul 5 (S N)) (Mul 4 (Mul 2 C)))
      (λ (E : Id Bool (Leb 2 C) True).
        LeRwLRaw (Mul 4 (Mul 2 C)) (Add 5 (Mul 5 N)) (Mul 5 (S N))
          (IdSymRaw Nat (Mul 5 (S N)) (Add 5 (Mul 5 N)) (MulSuccRaw 5 N))
          (LeRwRRaw (Add 5 (Mul 5 N)) (Add (Mul 4 C) (Mul 4 C)) (Mul 4 (Mul 2 C))
            (IdSymRaw Nat (Mul 4 (Mul 2 C)) (Add (Mul 4 C) (Mul 4 C)) (MulTwoDoubleRaw 4 C))
            (LeAddMonoRaw 5 (Mul 4 C) (Mul 5 N) (Mul 4 C)
              (Le5M4Raw C (LebTrueLeRaw 2 C E)) Hle)))
      (λ (E : Id Bool (Leb 2 C) False).
        NatRwRaw (λ (Cz : Nat). Le (Mul 5 N) (Mul 4 Cz) → Le (Mul 5 (S N)) (Mul 4 (Mul 2 Cz)))
          (S Z) C
          (IdSymRaw Nat C (S Z) (LeAntisymRaw C (S Z) (LebFalseGtRaw 2 C E) H1))
          (λ (Hle1 : Le (Mul 5 N) (Mul 4 (S Z))).
            NatRwRaw (λ (Nz : Nat). Le (Mul 5 (S Nz)) (Mul 4 (Mul 2 (S Z)))) Z N
              (IdSymRaw Nat N Z (FiveN4ZeroRaw N Hle1)) unit)
          Hle) }
end StdChainRaw

/-! ## The links

    One block per transcription segment (the `-- ── segment k ──` markers are
    the cuts, and they are arbitrary: docs/20's "cut the block at any statement
    boundary and thread env"), the former `let`s alone in the last. The `fn`
    ORDER is the single block's order, unchanged; a call to a lemma in an
    earlier link resolves by name through the seed (`Checked.seeded` retargets a
    block's calls at the seed's declarations, and a `[k]` hint rides the seed's
    `ledgers.hints`), a call to a sibling in the same link through `bindFn` as
    before. Cutting changes nothing the consumer can observe — `std.env` holds
    every lemma and former either way — and it was forced, twice over, by the
    shape of ONE block rather than by anything semantic:

    * **The code generator's recursion guard.** A block's `Term` is quoted as a
      right-nested `Expr` — the `fn` row expands to `FnMacro.bindFn slot dec
      (rest)`, so 136 statements are 136 nested applications — and compiling
      the `def` recurses into that nesting. At 136 statements it reports
      "maximum recursion depth reached in the code generator" (main's
      detach-tails commits changed the per-statement shape and pushed it over;
      `set_option maxRecDepth` does not reach this guard). Ten links of 11
      `fn`s and one of 26 `let`s compile without comment.
    * **The elaboration cost is superlinear in the block's length.** Each
      `bindFn` retargets the whole REST of the block, so one block walks each
      statement's tail once per `fn` above it. Measured on the same tree, same
      136 statements: one block elaborates in 80 s (and then fails to compile);
      these eleven links elaborate in 5.8 s total, 17 s wall for the module
      including the `StdChainRaw` constants. The seed Ω is the same size in
      both — the links save the tail walks, not the refinements. -/

set_option maxHeartbeats 0 in
def std0 : Checked := prog () {
  -- ── segment 0 ──

  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };

  fn LeTrans [a] (a : Nat, b : Nat, c : Nat, Hab : Le a b, Hbc : Le b c) -> Le a c {
    match a { Z => unit,
      S(a2) => match b { Z => botElim (Le (S a2) c) Hab,
        S(b2) => match c { Z => botElim (Le (S a2) Z) Hbc,
          S(c2) => LeTrans(a2, b2, c2, Hab, Hbc) } } } };

  fn LeUpR [a] (a : Nat, b : Nat, H : Le a b) -> Le a (S b) {
    match a { Z => unit,
      S(a2) => match b { Z => botElim (Le (S a2) (S Z)) H,
        S(b2) => LeUpR(a2, b2, H) } } };

  fn LeAdd [i] (i : Nat, g : Nat) -> Le i (Add i g) {
    match i { Z => unit, S(i2) => LeAdd(i2, g) } };

  fn LeAddL [a] (b : Nat, a : Nat) -> Le b (Add a b) {
    match a { Z => LeRefl(b),
      S(a2) => LeUpR(b, Add a2 b, LeAddL(b, a2)) } };

  fn LeAddSucc [i] (i : Nat, g : Nat) -> Le (S i) (Add i (S g)) {
    match i { Z => unit, S(i2) => LeAddSucc(i2, g) } };

  fn LeRwR (a : Nat, x : Nat, y : Nat, h : Id Nat x y, p : Le a x) -> Le a y {
    match h { Refl => p } };

  fn LeRwL (b : Nat, x : Nat, y : Nat, h : Id Nat x y, p : Le x b) -> Le y b {
    match h { Refl => p } };

  fn LeAddMonoL [lo] (lo : Nat, a : Nat, b : Nat, h : Le a b) -> Le (Add lo a) (Add lo b) {
    match lo { Z => h, S(lo2) => LeAddMonoL(lo2, a, b, h) } };

  fn IdTrans (A : Type, x : A, y : A, z : A, p : Id A x y, q : Id A y z) -> Id A x z {
    match p { Refl => q } };

  fn IdCongr (A : Type, B : Type, F : A → B, x : A, y : A, p : Id A x y) -> Id B (F x) (F y) {
    match p { Refl => Refl } };

  ()
}

set_option maxHeartbeats 0 in
def std1 : Checked := prog (std0) {
  -- ── segment 1 ──


  -- P1: no composition through `j`/IdCongr/IdTrans is needed here — a single
  -- non-recursive `Refl`-match transports the proof directly.
  fn IdSym (A : Type, x : A, y : A, p : Id A x y) -> Id A y x {
    match p { Refl => Refl }
  };

  -- P2 (see report): AddZero/AddSucc/AddComm/AddAssoc/CountAppend/LenSet/
  -- LenSwapL/CountConsCongr/CountConsHit/SwapLSet all compose their recursive
  -- step through IdCongr/IdTrans/j, whose ι-rule needs a literal Refl-shaped
  -- witness — a `fn` self-call desugars to the opaque `Ih`, which `j` cannot
  -- reduce through. So these stay spliced citations of the original proof.

  fn AddZero (a : Nat) -> Id Nat (Add a Z) a { Dllbc.StdChainRaw.AddZeroRaw a };

  fn AddSucc (a : Nat, b : Nat) -> Id Nat (Add a (S b)) (S (Add a b)) {
    Dllbc.StdChainRaw.AddSuccRaw a b
  };

  fn AddComm (a : Nat, b : Nat) -> Id Nat (Add a b) (Add b a) {
    Dllbc.StdChainRaw.AddCommRaw a b
  };

  fn AddAssoc (a : Nat, b : Nat, c : Nat)
      -> Id Nat (Add (Add a b) c) (Add a (Add b c)) {
    Dllbc.StdChainRaw.AddAssocRaw a b c
  };

  fn CountAppend (m : Nat, a : List Nat, b : List Nat)
      -> Id Nat (Count m (Dllbc.Std.Append a b))
           (Add (Count m a) (Count m b)) {
    Dllbc.StdChainRaw.CountAppendRaw m a b
  };

  fn LenSet (k : Nat, v : Nat, l : List Nat) -> Id Nat (Len (Dllbc.StdChainRaw.Set k v l)) (Len l) {
    Dllbc.StdChainRaw.LenSetRaw k v l
  };

  fn LenSwapL (i : Nat, j : Nat, l : List Nat) -> Id Nat (Len (Dllbc.StdChainRaw.SwapL i j l)) (Len l) {
    Dllbc.StdChainRaw.LenSwapLRaw i j l
  };

  fn CountConsCongr (m : Nat, h : Nat, l1 : List Nat, l2 : List Nat,
      P : Id Nat (Count m l1) (Count m l2))
      -> Id Nat (Count m (Cons h l1)) (Count m (Cons h l2)) {
    Dllbc.StdChainRaw.CountConsCongrRaw m h l1 l2 P
  };

  fn CountConsHit (m : Nat, a : Nat, l : List Nat, Hq : Id Bool (Eqb m a) True)
      -> Id Nat (Count m (Cons a l)) (S (Count m l)) {
    Dllbc.StdChainRaw.CountConsHitRaw m a l Hq
  };

  fn SwapLSet (i : Nat, j : Nat, l : List Nat,
      pij : Le (S i) j, p2 : Le (S j) (Len l))
      -> Id (List Nat)
           (Dllbc.StdChainRaw.Set i (Dllbc.StdChainRaw.NthL j l) (Dllbc.StdChainRaw.Set j (Dllbc.StdChainRaw.NthL i l) l))
           (Dllbc.StdChainRaw.SwapL i j l) {
    Dllbc.StdChainRaw.SwapLSetRaw i j l pij p2
  };

  ()
}

set_option maxHeartbeats 0 in
def std2 : Checked := prog (std1) {
  -- ── segment 2 ──

  fn BoolFT (H : Id Bool False True) -> Bot { Dllbc.StdChainRaw.BoolFTRaw H };

  fn BoolTF (H : Id Bool True False) -> Bot { Dllbc.StdChainRaw.BoolTFRaw H };

  fn LebTrueLe [a] (a : Nat, b : Nat, H : Id Bool (Leb a b) True) -> Le a b {
    match a {
      Z => unit,
      S(a') => match b {
        Z => { let bad = BoolFT(H); botElim (Le (S a') Z) bad },
        S(b') => LebTrueLe(a', b', H)
      }
    }
  };

  fn LebFalseGt [a] (a : Nat, b : Nat, H : Id Bool (Leb a b) False) -> Le (S b) a {
    match a {
      Z => { let bad = BoolTF(H); botElim (Le (S b) Z) bad },
      S(a') => match b {
        Z => unit,
        S(b') => LebFalseGt(a', b', H)
      }
    }
  };

  fn LeAntisym [a] (a : Nat, b : Nat, H1 : Le a b, H2 : Le b a) -> Id Nat a b {
    match a {
      Z => match b {
        Z => Refl,
        S(b') => botElim (Id Nat Z (S b')) H2
      },
      S(a') => match b {
        Z => botElim (Id Nat (S a') Z) H1,
        S(b') => { let ih = LeAntisym(a', b', H1, H2); IdCongr Nat Nat (λ (n : Nat). S n) a' b' ih }
      }
    }
  };

  fn Znots (x : Nat, H : Id Nat Z (S x)) -> Bot { Dllbc.StdChainRaw.ZnotsRaw x H };

  fn SInj (m : Nat, n : Nat, H : Id Nat (S m) (S n)) -> Id Nat m n { Dllbc.StdChainRaw.SInjRaw m n H };

  fn Sub [a] (a : Nat, b : Nat) -> Nat {
    match a {
      Z => Z,
      S(a') => match b {
        Z => S(a'),
        S(b') => Sub(a', b')
      }
    }
  };

  fn AddSubCancel (a : Nat, b : Nat, H : Le b a) -> Id Nat (Add b (Dllbc.StdChainRaw.SubRaw a b)) a { Dllbc.StdChainRaw.AddSubCancelRaw a b H };

  fn LePredL (a : Nat, b : Nat, H : Le (S a) b) -> Le a b { Dllbc.StdChainRaw.LePredLRaw a b H };

  fn EqbGtFalse [h] (h : Nat, x : Nat, Hlt : Le (S h) x) -> Id Bool (Eqb x h) False {
    match h {
      Z => match x {
        Z => botElim (Id Bool (Eqb Z Z) False) Hlt,
        S(x') => Refl
      },
      S(h') => match x {
        Z => botElim (Id Bool (Eqb Z (S h')) False) Hlt,
        S(x') => EqbGtFalse(h', x', Hlt)
      }
    }
  };

  ()
}

set_option maxHeartbeats 0 in
def std3 : Checked := prog (std2) {
  -- ── segment 3 ──

  fn EqbLtFalse [a] (a : Nat, b : Nat, Hab : Le (S a) b) -> Id Bool (Eqb a b) False {
    match a {
      Z => match b {
        Z => botElim (Id Bool (Eqb Z Z) False) Hab,
        S(b2) => Refl },
      S(a2) => match b {
        Z => botElim (Id Bool (Eqb (S a2) Z) False) Hab,
        S(b2) => EqbLtFalse(a2, b2, Hab) } } };

  fn CountConsMiss (m : Nat, h : Nat, t : List Nat, Hq : Id Bool (Eqb m h) False) ->
      Id Nat (Count m (Cons h t)) (Count m t) {
    Dllbc.StdChainRaw.CountConsMissRaw m h t Hq };

  fn EqbRefl [n] (n : Nat) -> Id Bool (Eqb n n) True {
    match n { Z => Refl, S(n2) => EqbRefl(n2) } };

  fn ListRw (P : List Nat → Type, x : List Nat, y : List Nat,
      H : Id (List Nat) x y, px : P x) -> P y {
    Dllbc.StdChainRaw.ListRwRaw P x y H px };

  fn SortedHead (h : Nat, t : List Nat, s0 : Sorted (Cons h t)) -> Bound h t {
    match s0 { Pair(x, y) => x } };

  fn SortedTail (h : Nat, t : List Nat, s0 : Sorted (Cons h t)) -> Sorted t {
    match s0 { Pair(x, y) => y } };

  -- P2: `Ub`/`Lb` are old-style hand terms whose Σ binds a COMPTIME first
  -- component (`Σ (Hh : Le H P). Ih`, capital `Hh`), and the fence refuses to
  -- ⇒-move a comptime match-arm binder out as a function's return value — P1
  -- (`match u { Pair(X, y) => X }`) hits "fence: 'X' is a COMPTIME binder ...
  -- cannot be ⇒-moved" no matter which case (X)/(x) is tried for the first
  -- component (lower-case there instead fails the earlier "arm binder is
  -- lowercase but the component is COMPTIME" check). Citing the old term
  -- sidesteps it.
  fn UbHead (p : Nat, h : Nat, t : List Nat, u : Dllbc.StdChainRaw.Ub p (Cons h t)) -> Le h p {
    Dllbc.StdChainRaw.UbHeadRaw p h t u };

  fn UbTail (p : Nat, h : Nat, t : List Nat, u : Dllbc.StdChainRaw.Ub p (Cons h t)) -> Dllbc.StdChainRaw.Ub p t {
    Dllbc.StdChainRaw.UbTailRaw p h t u };

  fn LbBound (p : Nat, l : List Nat, hl : Dllbc.StdChainRaw.Lb p l) -> Bound p l {
    Dllbc.StdChainRaw.LbBoundRaw p l hl };

  fn BoundAppend (h : Nat, p : Nat, t : List Nat, b : List Nat, hb : Bound h t, hp : Le h p) ->
      Bound h (Dllbc.Std.Append t (Cons p b)) {
    match t {
      Nil => hp,
      Cons(h2, t2) => hb } };

  -- P2: the original's recursion feeds `T`/`P`/`B`/`Sa`/`Ua` to SIX different
  -- helper calls in the Cons arm, each more than once; as `fn`+`match`
  -- lowercase (runtime) params those uses are affine moves and collide
  -- ("readR: t#8 holds ⊥ (use-after-move)"). Citing the old term sidesteps the
  -- sharing problem entirely — the original already checks (chkLib,
  -- Dllbc.StdChainRaw.lean:2036).
  fn SortedAppendPivot (p : Nat, a : List Nat, b : List Nat,
      Sa : Sorted a, ua : Dllbc.StdChainRaw.Ub p a, Sb : Sorted b, lb0 : Dllbc.StdChainRaw.Lb p b) ->
      Sorted (Dllbc.Std.Append a (Cons p b)) {
    Dllbc.StdChainRaw.SortedAppendPivotRaw p a b Sa ua Sb lb0 };

  ()
}

set_option maxHeartbeats 0 in
def std4 : Checked := prog (std3) {
  -- ── segment 4 ──

  fn CountConsL (n : Nat, x : Nat, a : List Nat, b : List Nat, c : List Nat,
      H : Id Nat (Add (Count n a) (Count n b)) (Count n c))
      -> Id Nat (Add (Count n (Cons x a)) (Count n b)) (Count n (Cons x c)) {
    Dllbc.StdChainRaw.CountConsLRaw n x a b c H };

  fn CountConsR (n : Nat, x : Nat, a : List Nat, b : List Nat, c : List Nat,
      H : Id Nat (Add (Count n a) (Count n b)) (Count n c))
      -> Id Nat (Add (Count n a) (Count n (Cons x b))) (Count n (Cons x c)) {
    Dllbc.StdChainRaw.CountConsRRaw n x a b c H };

  fn LbHead (p : Nat, h : Nat, t : List Nat, U : Dllbc.StdChainRaw.Lb p (Cons h t)) -> Le p h {
    Dllbc.StdChainRaw.LbHeadRaw p h t U };

  fn LbTail (p : Nat, h : Nat, t : List Nat, U : Dllbc.StdChainRaw.Lb p (Cons h t)) -> Dllbc.StdChainRaw.Lb p t {
    Dllbc.StdChainRaw.LbTailRaw p h t U };

  fn NoAboveOfUb (p : Nat, l : List Nat, Hu : Dllbc.StdChainRaw.Ub p l, x : Nat, Hx : Le (S p) x)
      -> Id Nat (Count x l) Z {
    Dllbc.StdChainRaw.NoAboveOfUbRaw p l Hu x Hx };

  fn UbOfNoAbove (p : Nat, l : List Nat,
      HN : (Π (x : Nat) → Le (S p) x → Id Nat (Count x l) Z)) -> Dllbc.StdChainRaw.Ub p l {
    Dllbc.StdChainRaw.UbOfNoAboveRaw p l HN };

  fn UbPerm (p : Nat, a : List Nat, b : List Nat,
      HC : (Π (n : Nat) → Id Nat (Count n a) (Count n b)), Hb : Dllbc.StdChainRaw.Ub p b) -> Dllbc.StdChainRaw.Ub p a {
    Dllbc.StdChainRaw.UbPermRaw p a b HC Hb };

  fn NoBelowOfLb (p : Nat, l : List Nat, Hl : Dllbc.StdChainRaw.Lb p l, x : Nat, Hx : Le (S x) p)
      -> Id Nat (Count x l) Z {
    Dllbc.StdChainRaw.NoBelowOfLbRaw p l Hl x Hx };

  fn LbOfNoBelow (p : Nat, l : List Nat,
      HN : (Π (x : Nat) → Le (S x) p → Id Nat (Count x l) Z)) -> Dllbc.StdChainRaw.Lb p l {
    Dllbc.StdChainRaw.LbOfNoBelowRaw p l HN };

  fn LbPerm (p : Nat, a : List Nat, b : List Nat,
      HC : (Π (n : Nat) → Id Nat (Count n a) (Count n b)), Hb : Dllbc.StdChainRaw.Lb p b) -> Dllbc.StdChainRaw.Lb p a {
    Dllbc.StdChainRaw.LbPermRaw p a b HC Hb };

  fn SortedHeadA (k : Nat, h : Nat, t : Array k Nat,
      S0 : Dllbc.StdChainRaw.SortedA (S k) (acons k h t)) -> Dllbc.StdChainRaw.BoundA h k t {
    Dllbc.StdChainRaw.SortedHeadARaw k h t S0 };

  ()
}

set_option maxHeartbeats 0 in
def std5 : Checked := prog (std4) {
  -- ── segment 5 ──


  -- P1: non-recursive projection out of a Σ (`fn` with no `[k]` hint is a
  -- plain sealed λ, so `match` here is just the elim sugar, no recursor).
  fn SortedTailA (K : Nat, H : Nat, T : Array K Nat,
      s0 : Σ (hb : Dllbc.StdChainRaw.BoundA H K T). Dllbc.StdChainRaw.SortedA K T)
      -> Dllbc.StdChainRaw.SortedA K T {
    match s0 { Pair(hb, y) => y }
  };

  fn UbHeadA (P : Nat, K : Nat, H : Nat, T : Array K Nat,
      u : Σ (hu : Le H P). Dllbc.StdChainRaw.UbA P K T)
      -> Le H P {
    match u { Pair(hu, y) => hu }
  };

  fn UbTailA (P : Nat, K : Nat, H : Nat, T : Array K Nat,
      u : Σ (hu : Le H P). Dllbc.StdChainRaw.UbA P K T)
      -> Dllbc.StdChainRaw.UbA P K T {
    match u { Pair(hu, y) => y }
  };

  -- P2 from here: all touch `arrRec`/`Array` (or the `j`-eliminator), which the
  -- `fn`+`match` sugar has no recursor for (only `Nat`/`List` recursion). Body
  -- is a splice of the original proof (its `StdChainRaw` constant) applied to the new telescope —
  -- bare qualified identifier with DSL space-application, no `%`.

  fn LbBoundA (P : Nat, N : Nat, A : Array N Nat, Hl : Dllbc.StdChainRaw.LbA P N A)
      -> Dllbc.StdChainRaw.BoundA P N A {
    Dllbc.StdChainRaw.LbBoundARaw P N A Hl
  };

  fn BoundArrCat (H : Nat, P : Nat, K : Nat, T : Array K Nat, Q : Nat, B : Array Q Nat,
      Hbt : Dllbc.StdChainRaw.BoundA H K T, Hhp : Le H P)
      -> Dllbc.StdChainRaw.BoundA H (Add K (S Q))
           (arrCat K (S Q) T (arrCat 1 Q (Dllbc.StdChainRaw.Asingle P) B)) {
    Dllbc.StdChainRaw.BoundArrCatRaw H P K T Q B Hbt Hhp
  };

  fn SortedArrCat (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      Sa : Dllbc.StdChainRaw.SortedA M A, Ua : Dllbc.StdChainRaw.UbA P M A,
      Sb : Dllbc.StdChainRaw.SortedA Q B, Lb0 : Dllbc.StdChainRaw.LbA P Q B)
      -> Dllbc.StdChainRaw.SortedA (Add M (S Q))
           (arrCat M (S Q) A (arrCat 1 Q (Dllbc.StdChainRaw.Asingle P) B)) {
    Dllbc.StdChainRaw.SortedArrCatRaw P M A Q B Sa Ua Sb Lb0
  };

  fn CountArrCat (X : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat)
      -> Id Nat (Dllbc.StdChainRaw.CountA X (Add M Q) (arrCat M Q A B))
           (Add (Dllbc.StdChainRaw.CountA X M A) (Dllbc.StdChainRaw.CountA X Q B)) {
    Dllbc.StdChainRaw.CountArrCatRaw X M A Q B
  };

  fn CountAconsHit (M : Nat, A : Nat, K : Nat, L : Array K Nat, Hq : Id Bool (Eqb M A) True)
      -> Id Nat (Dllbc.StdChainRaw.CountA M (S K) (acons K A L))
           (S (Dllbc.StdChainRaw.CountA M K L)) {
    Dllbc.StdChainRaw.CountAconsHitRaw M A K L Hq
  };

  fn CountAconsMiss (M : Nat, H : Nat, K : Nat, T : Array K Nat, Hq : Id Bool (Eqb M H) False)
      -> Id Nat (Dllbc.StdChainRaw.CountA M (S K) (acons K H T)) (Dllbc.StdChainRaw.CountA M K T) {
    Dllbc.StdChainRaw.CountAconsMissRaw M H K T Hq
  };

  fn NoAboveOfUbA (P : Nat, N : Nat, A : Array N Nat, Hu : Dllbc.StdChainRaw.UbA P N A,
      X : Nat, Hx : Le (S P) X)
      -> Id Nat (Dllbc.StdChainRaw.CountA X N A) Z {
    Dllbc.StdChainRaw.NoAboveOfUbARaw P N A Hu X Hx
  };

  fn UbOfNoAboveA (P : Nat, N : Nat, A : Array N Nat,
      Hn : Π (X : Nat) → Le (S P) X → Id Nat (Dllbc.StdChainRaw.CountA X N A) Z)
      -> Dllbc.StdChainRaw.UbA P N A {
    Dllbc.StdChainRaw.UbOfNoAboveARaw P N A Hn
  };

  ()
}

set_option maxHeartbeats 0 in
def std6 : Checked := prog (std5) {
  -- ── segment 6 ──

  fn UbPermA (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      Hc : Π (X : Nat) → Id Nat (Dllbc.StdChainRaw.CountA X M A) (Dllbc.StdChainRaw.CountA X Q B),
      Hb : Dllbc.StdChainRaw.UbA P Q B) -> Dllbc.StdChainRaw.UbA P M A {
    Dllbc.StdChainRaw.UbPermARaw P M A Q B Hc Hb };

  fn NoBelowOfLbA (P : Nat, N : Nat, A : Array N Nat, Hlb : Dllbc.StdChainRaw.LbA P N A,
      X : Nat, Hx : Le (S X) P) -> Id Nat (Dllbc.StdChainRaw.CountA X N A) Z {
    Dllbc.StdChainRaw.NoBelowOfLbARaw P N A Hlb X Hx };

  fn LbOfNoBelowA (P : Nat, N : Nat, A : Array N Nat,
      Hn : Π (X : Nat) → Le (S X) P → Id Nat (Dllbc.StdChainRaw.CountA X N A) Z) ->
      Dllbc.StdChainRaw.LbA P N A {
    Dllbc.StdChainRaw.LbOfNoBelowARaw P N A Hn };

  fn LbPermA (P : Nat, M : Nat, A : Array M Nat, Q : Nat, B : Array Q Nat,
      Hc : Π (X : Nat) → Id Nat (Dllbc.StdChainRaw.CountA X M A) (Dllbc.StdChainRaw.CountA X Q B),
      Hb : Dllbc.StdChainRaw.LbA P Q B) -> Dllbc.StdChainRaw.LbA P M A {
    Dllbc.StdChainRaw.LbPermARaw P M A Q B Hc Hb };

  fn CountSwap2 (M : Nat, A : Nat, B : Nat) ->
      Id Nat (Dllbc.StdChainRaw.CountA M 2 Arr(B, A)) (Dllbc.StdChainRaw.CountA M 2 Arr(A, B)) {
    Dllbc.StdChainRaw.CountSwap2Raw M A B };

  fn NatRw (P : Nat → Type, X : Nat, Y : Nat, H : Id Nat X Y, Px : P X) -> P Y {
    Dllbc.StdChainRaw.NatRwRaw P X Y H Px };

  fn LeZeroEq [n] (n : Nat, H : Le n Z) -> Id Nat n Z {
    match n { Z => Refl, S(n2) => botElim (Id Nat (S n2) Z) H } };

  fn SortedANil (N : Nat, A : Array N Nat, H : Id Nat N Z) -> Dllbc.StdChainRaw.SortedA N A {
    Dllbc.StdChainRaw.SortedANilRaw N A H };

  fn SplitANil (P : Nat, Kz : Nat, N : Nat, A : Array N Nat, Hz : Id Nat N Z) ->
      Dllbc.StdChainRaw.SplitAL P Kz N A {
    Dllbc.StdChainRaw.SplitANilRaw P Kz N A Hz };

  fn SplitA0Lb (P : Nat, N : Nat, A : Array N Nat, Hs : Dllbc.StdChainRaw.SplitAL P Z N A) ->
      Dllbc.StdChainRaw.LbA P N A {
    Dllbc.StdChainRaw.SplitA0LbRaw P N A Hs };

  fn SplitACatE1 (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      Hs : Dllbc.StdChainRaw.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W)) ->
      Σ (Hu : Dllbc.StdChainRaw.UbA P K L). Dllbc.StdChainRaw.SplitAL P (S Z) Mm W {
    Dllbc.StdChainRaw.SplitACatE1Raw P K Mm L W Hs };

  ()
}

set_option maxHeartbeats 0 in
def std7 : Checked := prog (std6) {
  -- ── segment 7 ──

  fn SplitACatI0 (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      U : Dllbc.StdChainRaw.UbA P K L, H : Dllbc.StdChainRaw.SplitAL P Z Mm W)
      -> Dllbc.StdChainRaw.SplitAL P K (Add K Mm) (arrCat K Mm L W) {
    Dllbc.StdChainRaw.SplitACatI0Raw P K Mm L W U H };

  fn PartACatI0 (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      U : Dllbc.StdChainRaw.UbA Pv K L, H : Dllbc.StdChainRaw.PartA Pv Z Mm W)
      -> Dllbc.StdChainRaw.PartA Pv K (Add K Mm) (arrCat K Mm L W) {
    Dllbc.StdChainRaw.PartACatI0Raw Pv K Mm L W U H };

  fn PartACatE0 (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdChainRaw.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Σ (Hu : Dllbc.StdChainRaw.UbA Pv K L). Dllbc.StdChainRaw.PartA Pv Z Mm W {
    Dllbc.StdChainRaw.PartACatE0Raw Pv K Mm L W S0 };

  fn SplitACatUb (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdChainRaw.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdChainRaw.UbA P K L {
    elim (Dllbc.StdChainRaw.SplitACatE1Raw P K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdChainRaw.UbA P K L). Dllbc.StdChainRaw.SplitAL P (S Z) Mm W).
                Dllbc.StdChainRaw.UbA P K L) {
        Pair (U) (V) => U } };

  fn SplitACatRest (P : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdChainRaw.SplitAL P (S K) (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdChainRaw.SplitAL P (S Z) Mm W {
    elim (Dllbc.StdChainRaw.SplitACatE1Raw P K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdChainRaw.UbA P K L). Dllbc.StdChainRaw.SplitAL P (S Z) Mm W).
                Dllbc.StdChainRaw.SplitAL P (S Z) Mm W) {
        Pair (U) (V) => V } };

  fn SplitA1Head (P : Nat, R : Nat, G : Array R Nat, Yv : Nat,
      S0 : Σ (Hh : Le Yv P). Dllbc.StdChainRaw.SplitAL P Z R G)
      -> Le Yv P {
    elim S0 return (λ (Qz : Σ (Hh : Le Yv P). Dllbc.StdChainRaw.SplitAL P Z R G). Le Yv P) {
      Pair (U) (V) => U } };

  fn SplitA1Tail (P : Nat, R : Nat, G : Array R Nat, Yv : Nat,
      S0 : Σ (Hh : Le Yv P). Dllbc.StdChainRaw.SplitAL P Z R G)
      -> Dllbc.StdChainRaw.SplitAL P Z R G {
    elim S0 return (λ (Qz : Σ (Hh : Le Yv P). Dllbc.StdChainRaw.SplitAL P Z R G).
                      Dllbc.StdChainRaw.SplitAL P Z R G) {
      Pair (U) (V) => V } };

  fn PartACatUb (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdChainRaw.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdChainRaw.UbA Pv K L {
    elim (Dllbc.StdChainRaw.PartACatE0Raw Pv K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdChainRaw.UbA Pv K L). Dllbc.StdChainRaw.PartA Pv Z Mm W).
                Dllbc.StdChainRaw.UbA Pv K L) {
        Pair (U) (V) => U } };

  fn PartACatRest (Pv : Nat, K : Nat, Mm : Nat, L : Array K Nat, W : Array Mm Nat,
      S0 : Dllbc.StdChainRaw.PartA Pv K (Add K Mm) (arrCat K Mm L W))
      -> Dllbc.StdChainRaw.PartA Pv Z Mm W {
    elim (Dllbc.StdChainRaw.PartACatE0Raw Pv K Mm L W S0)
      return (λ (Qz : Σ (Hu : Dllbc.StdChainRaw.UbA Pv K L). Dllbc.StdChainRaw.PartA Pv Z Mm W).
                Dllbc.StdChainRaw.PartA Pv Z Mm W) {
        Pair (U) (V) => V } };

  fn PartA0Eq (Pv : Nat, Jj : Nat, G : Array Jj Nat, Ev : Nat,
      S0 : Σ (He : Id Nat Ev Pv). Dllbc.StdChainRaw.LbA Pv Jj G)
      -> Id Nat Ev Pv {
    elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). Dllbc.StdChainRaw.LbA Pv Jj G). Id Nat Ev Pv) {
      Pair (U) (V) => U } };

  fn PartA0Lb (Pv : Nat, Jj : Nat, G : Array Jj Nat, Ev : Nat,
      S0 : Σ (He : Id Nat Ev Pv). Dllbc.StdChainRaw.LbA Pv Jj G)
      -> Dllbc.StdChainRaw.LbA Pv Jj G {
    elim S0 return (λ (Qz : Σ (He : Id Nat Ev Pv). Dllbc.StdChainRaw.LbA Pv Jj G).
                      Dllbc.StdChainRaw.LbA Pv Jj G) {
      Pair (U) (V) => V } };

  ()
}

set_option maxHeartbeats 0 in
def std8 : Checked := prog (std7) {
  -- ── segment 8 ──


  fn CountAconsCongr (Q : Nat, H : Nat, K : Nat, T1 : Array K Nat, T2 : Array K Nat,
      Hc : Id Nat (Dllbc.StdChainRaw.CountA Q K T1) (Dllbc.StdChainRaw.CountA Q K T2)) ->
      Id Nat (Dllbc.StdChainRaw.CountA Q (S K) (acons K H T1))
             (Dllbc.StdChainRaw.CountA Q (S K) (acons K H T2)) {
    Dllbc.StdChainRaw.CountAconsCongrRaw Q H K T1 T2 Hc };

  fn BumpComm (b1 : Bool, b2 : Bool, cl : Nat, cg : Nat) ->
      Id Nat (Dllbc.StdChainRaw.BumpN b2 (Add cl (Dllbc.StdChainRaw.BumpN b1 cg)))
             (Dllbc.StdChainRaw.BumpN b1 (Add cl (Dllbc.StdChainRaw.BumpN b2 cg))) {
    match b1 {
      True => match b2 { True => Refl, False => Dllbc.StdChainRaw.AddSuccRaw cl cg },
      False => match b2 {
        True => Dllbc.StdChainRaw.IdSymRaw Nat (Add cl (S cg)) (S (Add cl cg))
                   (Dllbc.StdChainRaw.AddSuccRaw cl cg),
        False => Refl } } };

  fn CountSwapA (Q : Nat, X : Nat, Y : Nat, K : Nat, L : Array K Nat, R : Nat, G : Array R Nat) ->
      Id Nat (Dllbc.StdChainRaw.CountA Q (S (Add K (S R)))
                (acons (Add K (S R)) Y (arrCat K (S R) L (acons R X G))))
             (Dllbc.StdChainRaw.CountA Q (S (Add K (S R)))
                (acons (Add K (S R)) X (arrCat K (S R) L (acons R Y G)))) {
    Dllbc.StdChainRaw.CountSwapARaw Q X Y K L R G };

  fn StepInv (b : Nat, r : Nat, c : Nat, H : Le (Add r c) b) ->
      Le (Add (Dllbc.StdChainRaw.NextR r c) (Dllbc.StdChainRaw.NextC b c)) b {
    match c {
      Z => Dllbc.StdChainRaw.LeReflRaw b,
      S(c2) => Dllbc.StdChainRaw.LeRwLRaw b (Add r (S c2)) (S (Add r c2))
                  (Dllbc.StdChainRaw.AddSuccRaw r c2) H } };

  fn ModCLt [a] (a : Nat, b : Nat, r : Nat, c : Nat, h : Le (Add r c) b) ->
      Le (S (Dllbc.StdChainRaw.ModC a b r c)) (S b) {
    match a {
      Z => Dllbc.StdChainRaw.LeTransRaw r (Add r c) b (Dllbc.StdChainRaw.LeAddRaw r c) h,
      S(a2) => ModCLt(a2, b, (Dllbc.StdChainRaw.NextR r c), (Dllbc.StdChainRaw.NextC b c),
                  StepInv(b, r, c, h)) } };

  fn ModLtN (a : Nat, n : Nat, H : Le (S Z) n) -> Le (S (Dllbc.StdChainRaw.Mod a n)) n {
    match n {
      Z => botElim (Le (S (Dllbc.StdChainRaw.Mod a Z)) Z) H,
      S(b2) => ModCLt(a, b2, Z, b2, Dllbc.StdChainRaw.LeReflRaw b2) } };

  fn ModDec (I : Nat, N : Nat, H : Le (S I) N) -> Σ (R : Nat). Id Nat N (Add I (S R)) {
    Dllbc.StdChainRaw.ModDecRaw I N H };

  fn AddSwapL [a] (a : Nat, b : Nat, c : Nat) ->
      Id Nat (Add a (Add b c)) (Add b (Add a c)) {
    match a {
      Z => Refl,
      S(a2) =>
        Dllbc.StdChainRaw.IdTransRaw Nat (S (Add a2 (Add b c))) (S (Add b (Add a2 c))) (Add b (S (Add a2 c)))
          (Dllbc.StdChainRaw.IdCongrRaw Nat Nat (λ (X : Nat). S X) (Add a2 (Add b c)) (Add b (Add a2 c))
             AddSwapL(a2, b, c))
          (Dllbc.StdChainRaw.IdSymRaw Nat (Add b (S (Add a2 c))) (S (Add b (Add a2 c)))
             (Dllbc.StdChainRaw.AddSuccRaw b (Add a2 c))) } };

  fn AddInterchange (A : Nat, B : Nat, C : Nat, D : Nat) ->
      Id Nat (Add (Add A B) (Add C D)) (Add (Add A C) (Add B D)) {
    Dllbc.StdChainRaw.AddInterchangeRaw A B C D };

  fn MulSucc [a] (a : Nat, b : Nat) ->
      Id Nat (Dllbc.StdChainRaw.Mul a (S b)) (Add a (Dllbc.StdChainRaw.Mul a b)) {
    match a {
      Z => Refl,
      S(a2) => {
        let hsw = AddSwapL(b, a2, (Dllbc.StdChainRaw.Mul a2 b));
        Dllbc.StdChainRaw.IdCongrRaw Nat Nat (λ (X : Nat). S X)
          (Add b (Dllbc.StdChainRaw.Mul a2 (S b))) (Add a2 (Add b (Dllbc.StdChainRaw.Mul a2 b)))
          (Dllbc.StdChainRaw.IdTransRaw Nat (Add b (Dllbc.StdChainRaw.Mul a2 (S b)))
            (Add b (Add a2 (Dllbc.StdChainRaw.Mul a2 b)))
            (Add a2 (Add b (Dllbc.StdChainRaw.Mul a2 b)))
            (Dllbc.StdChainRaw.IdCongrRaw Nat Nat (λ (X : Nat). Add b X)
               (Dllbc.StdChainRaw.Mul a2 (S b)) (Add a2 (Dllbc.StdChainRaw.Mul a2 b)) MulSucc(a2, b))
            hsw) } } };

  fn MulAddR [a] (a : Nat, b : Nat, c : Nat) ->
      Id Nat (Dllbc.StdChainRaw.Mul a (Add b c))
             (Add (Dllbc.StdChainRaw.Mul a b) (Dllbc.StdChainRaw.Mul a c)) {
    match a {
      Z => Refl,
      S(a2) => {
        let hi = AddInterchange(b, c, (Dllbc.StdChainRaw.Mul a2 b), (Dllbc.StdChainRaw.Mul a2 c));
        Dllbc.StdChainRaw.IdTransRaw Nat
          (Add (Add b c) (Dllbc.StdChainRaw.Mul a2 (Add b c)))
          (Add (Add b c) (Add (Dllbc.StdChainRaw.Mul a2 b) (Dllbc.StdChainRaw.Mul a2 c)))
          (Add (Add b (Dllbc.StdChainRaw.Mul a2 b)) (Add c (Dllbc.StdChainRaw.Mul a2 c)))
          (Dllbc.StdChainRaw.IdCongrRaw Nat Nat (λ (X : Nat). Add (Add b c) X)
            (Dllbc.StdChainRaw.Mul a2 (Add b c))
            (Add (Dllbc.StdChainRaw.Mul a2 b) (Dllbc.StdChainRaw.Mul a2 c)) MulAddR(a2, b, c))
          hi } } };

  ()
}

set_option maxHeartbeats 0 in
def std9 : Checked := prog (std8) {
  -- ── segment 9 ──


  -- P2: straight-line (IdTrans/IdCongr/MulAddR), no recursion — splice the
  -- existing checked proof, renamed telescope.
  fn MulTwoDouble (a : Nat, c : Nat) ->
      Id Nat (Dllbc.StdChainRaw.Mul a (Dllbc.StdChainRaw.Mul 2 c)) (Add (Dllbc.StdChainRaw.Mul a c) (Dllbc.StdChainRaw.Mul a c)) {
    Dllbc.StdChainRaw.MulTwoDoubleRaw a c };

  -- P2: straight-line (LeRwR/LeRwL/AddComm/LeAddMonoL), no recursion.
  fn LeAddMonoR (a : Nat, b : Nat, k : Nat, H : Le a b) -> Le (Add a k) (Add b k) {
    Dllbc.StdChainRaw.LeAddMonoRRaw a b k H };

  -- P2: straight-line (LeTrans/LeAddMonoR-shaped composition), no recursion.
  fn LeAddMono (a : Nat, b : Nat, c : Nat, d : Nat, H1 : Le a b, H2 : Le c d) ->
      Le (Add a c) (Add b d) {
    Dllbc.StdChainRaw.LeAddMonoRaw a b c d H1 H2 };

  -- P1: elim on A with Ih = LeAddMono at the predecessor — the LeTrans-shaped
  -- match+recursion. Self-call `LeMulR(a2, b, c, H)` becomes `ih` at the
  -- predecessor; the local fn `LeAddMono` above is called by name.
  --
  -- H is CAPITAL (comptime), not lowercase, even though the original proof
  -- never matches on it: the S(a2) arm uses H twice on one path (once as
  -- LeAddMono's own proof argument, once threaded into the recursive
  -- call), and a lowercase H is a linear runtime resource that can only be
  -- read once per path — confirmed empirically: lowercase h fails
  -- elaboration with "h#3 holds ⊥ (use-after-move)", capitalizing it fixes
  -- it clean. LeTrans's own worked example (docs/20) keeps its analogous
  -- premises (Hab, Hbc) capital for the same reason.
  fn LeMulR [a] (a : Nat, b : Nat, c : Nat, H : Le b c) ->
      Le (Dllbc.StdChainRaw.Mul a b) (Dllbc.StdChainRaw.Mul a c) {
    match a {
      Z => unit,
      S(a2) => LeAddMono(b, c, Dllbc.StdChainRaw.Mul a2 b, Dllbc.StdChainRaw.Mul a2 c, H, LeMulR(a2, b, c, H)) } };

  -- P2: straight-line (LeTrans applied at unit / LeMulR), no recursion.
  fn Le5M4 (c : Nat, H : Le 2 c) -> Le 5 (Dllbc.StdChainRaw.Mul 4 c) {
    Dllbc.StdChainRaw.Le5M4Raw c H };

  -- P1: elim on N, no self-call in either arm (the S arm discharges by
  -- botElim on the impossible `H`) — match ⇜-refines `H`'s type per arm
  -- exactly as the LeTrans model does for its premises.
  fn FiveN4Zero (n : Nat, H : Le (Dllbc.StdChainRaw.Mul 5 n) 4) -> Id Nat n Z {
    match n {
      Z => Refl,
      S(n2) => botElim (Id Nat (S n2) Z)
        (Dllbc.StdChainRaw.LeRwLRaw 4 (Dllbc.StdChainRaw.Mul 5 (S n2)) (Add 5 (Dllbc.StdChainRaw.Mul 5 n2)) (Dllbc.StdChainRaw.MulSuccRaw 5 n2) H) } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2 H` — the
  -- LeTrans-shaped nested match, decreasing only on A.
  fn LeLebTrue [a] (a : Nat, b : Nat, H : Le a b) -> Id Bool (Leb a b) True {
    match a {
      Z => Refl,
      S(a2) => match b {
        Z => botElim (Id Bool (Leb (S a2) Z) True) H,
        S(b2) => LeLebTrue(a2, b2, H) } } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2 H` in the S/S
  -- case only.
  fn EqbTrueEq [a] (a : Nat, b : Nat, H : Id Bool (Eqb a b) True) -> Id Nat a b {
    match a {
      Z => match b {
        Z => Refl,
        S(b2) => botElim (Id Nat Z (S b2)) (Dllbc.StdChainRaw.BoolFTRaw H) },
      S(a2) => match b {
        Z => botElim (Id Nat (S a2) Z) (Dllbc.StdChainRaw.BoolFTRaw H),
        S(b2) => Dllbc.StdChainRaw.IdCongrRaw Nat Nat (λ (x : Nat). S x) a2 b2 (EqbTrueEq(a2, b2, H)) } } };

  -- P1: elim on A, inner elim on B per arm, self-call `Ih B2` in the S/S
  -- case only (no premise to carry).
  fn EqbSym [a] (a : Nat, b : Nat) -> Id Bool (Eqb a b) (Eqb b a) {
    match a {
      Z => match b { Z => Refl, S(b2) => Refl },
      S(a2) => match b { Z => Refl, S(b2) => EqbSym(a2, b2) } } };

  -- P2 (per dispatch note): Type-family/Bool-motive shape — B/T/F/G stay
  -- capital (comptime), splice the existing boolRec-based proof.
  fn IfDec (B : Bool, T : Type, F : Id Bool B True → T, G : Id Bool B False → T) -> T {
    Dllbc.StdChainRaw.IfDecRaw B T F G };

  -- P2: the resize-ledger combinator (IfDec/NatRw dispatch on non-decreasing
  -- premises) — splice the existing checked proof.
  fn LedgerGrow (c : Nat, n : Nat, H1 : Le (S Z) c, Hle : Le (Dllbc.StdChainRaw.Mul 5 n) (Dllbc.StdChainRaw.Mul 4 c)) ->
      Le (Dllbc.StdChainRaw.Mul 5 (S n)) (Dllbc.StdChainRaw.Mul 4 (Dllbc.StdChainRaw.Mul 2 c)) {
    Dllbc.StdChainRaw.LedgerGrowRaw c n H1 Hle };

  ()
}

set_option maxHeartbeats 0 in
def std : Checked := prog (std9) {
  -- ── the spec functions and predicate formers, bound LAST so consumers resolve
  -- them by name from the seed while the fn checks above never sweep them (each
  -- σ-refinement rebuilds every Ω binding; the raw proof terms are not bound at
  -- all — bodies cite the `StdChainRaw` constants directly) ──
  let Append = Dllbc.Std.Append;
  let NthL = Dllbc.StdChainRaw.NthL;
  let Set = Dllbc.StdChainRaw.Set;
  let SwapL = Dllbc.StdChainRaw.SwapL;
  let Pred = Dllbc.StdChainRaw.Pred;
  let Ub = Dllbc.StdChainRaw.Ub;
  let Lb = Dllbc.StdChainRaw.Lb;
  let CountA = Dllbc.StdChainRaw.CountA;
  let BoundA = Dllbc.StdChainRaw.BoundA;
  let SortedA = Dllbc.StdChainRaw.SortedA;
  let UbA = Dllbc.StdChainRaw.UbA;
  let LbA = Dllbc.StdChainRaw.LbA;
  let Asingle = Dllbc.StdChainRaw.Asingle;
  let LbHeadA = Dllbc.StdChainRaw.LbHeadA;
  let LbTailA = Dllbc.StdChainRaw.LbTailA;
  let SplitAL = Dllbc.StdChainRaw.SplitAL;
  let PartA = Dllbc.StdChainRaw.PartA;
  let BumpN = Dllbc.StdChainRaw.BumpN;
  let NextR = Dllbc.StdChainRaw.NextR;
  let NextC = Dllbc.StdChainRaw.NextC;
  let NextQ = Dllbc.StdChainRaw.NextQ;
  let ModC = Dllbc.StdChainRaw.ModC;
  let Mod = Dllbc.StdChainRaw.Mod;
  let DivC = Dllbc.StdChainRaw.DivC;
  let Div = Dllbc.StdChainRaw.Div;
  let Mul = Dllbc.StdChainRaw.Mul;

  ()
}


end Dllbc
