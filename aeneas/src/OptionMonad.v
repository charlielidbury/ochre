(** A few tactics and notations for options and co...
*)

(** * Useful general purpose tactics *)

(**r a useful tactic for forward style
     author: X. Leroy in CompCert/Coqlib.v 
*)
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).



(**r apply (possibly existential) 'thm' in forward style (based on Leroy's exploit) *)
Ltac feapply thm :=
  exploit thm; eauto;
  let H := fresh "FWD" in
  intro H;
  match type of H with
  | (@ex _ _ ) => decompose [ex and] H; clear H; eauto
  | (@and _ _) => decompose [ex and] H; clear H; eauto
  | _ => generalize H; clear H
  end.

(* Demo de feapply *)

Goal forall (P: nat -> Prop) (Q: nat -> nat -> Prop) (R: nat -> nat -> nat -> Prop)
     (H1: P 42)
     (H2: Q 2 421)
     (H: forall x y z, P x -> Q y z -> exists q, q=x+y /\ R q x z),
     R 44 42 421.
Proof.
  intros; feapply H.
  subst; assumption.
Qed.

(**r autodestruct = find alone something to destruct in the current goal *)

Ltac deepest_match exp := 
  match exp with
  | context f [match ?expr with | _ => _ end] => ltac: (deepest_match expr)
  | _ => exp
  end.

Ltac autodestruct :=
  let EQ := fresh "EQ" in 
  match goal with
  | |- context f [match ?expr with | _ => _ end] => 
    let t := ltac: (deepest_match expr) in
    destruct t eqn:EQ; generalize EQ; clear EQ; congruence || trivial
  end.

(** * Notations for option_monad *)

Declare Scope option_monad_scope.

Notation "'SOME' X <- A 'IN' B" := (match A with Some X => B | None => None end)
         (at level 60, X ident, A at level 50, B at level 60)
         : option_monad_scope.

Notation "'ASSERT' A 'IN' B" := (if A then B else None)
         (at level 60, A at level 50, B at level 60)
         : option_monad_scope.

Notation "'Is_Some' o" := (exists a, o=Some a)
         (at level 62)
         : option_monad_scope.

Local Open Scope option_monad_scope.

(** Simple tactics for option-monad *)

Ltac simplify_someHyp :=
  match goal with
  | H: None = Some _ |- _  => inversion H
  | H: Some _ = None |- _  => inversion H
  | H: false = true |- _  => inversion H
  | H: true = false |- _  => inversion H
  | H: ?t = ?t |- _ => clear H
  | H: Is_Some _ |- _ => inversion H; clear H; subst
  | H: Some _ = Some _ |- _  => inversion H; clear H; subst
  | H: Some _ <> None |- _ => clear H
  | H: None <> Some _ |- _ => clear H
  | H: true <> false |- _ => clear H
  | H: false <> true |- _ => clear H
  | H: _ = Some _ |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = None |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = true |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = false |- _ => (try rewrite !H in * |- *); generalize H; clear H
  end.

Ltac simplify_someHyps := 
  repeat (simplify_someHyp; simpl in * |- *).

Ltac try_simplify_someHyps := 
  try (intros; simplify_someHyps; eauto).

Ltac simplify_option := repeat (try_simplify_someHyps; autodestruct); try_simplify_someHyps.

