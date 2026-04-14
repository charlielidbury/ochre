(** * Mechanized_LLBC.PathToSubtree : definitions and properties of values and states. *)
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Import ListNotations.

From stdpp Require Import pmap gmap.

Local Open Scope option_monad_scope.

(** As a hint database, "spath" is used to solve common goals, in particular, proving comparisons
    between paths.
    As a rewriting database, "spath" is used to reduce computations on paths, values and states, and
    to put them in normal form. *)
Create HintDb spath.

(** This is a hint database used to reduce weight computations. *)
Create HintDb weight.

Coercion Z.of_nat : nat >-> Z.

(** * Paths, prefixes and disjointness *)

(** A vpath ("value path") is the data structure used to uniquely represent nodes in a tree. The
    integers in the list are the indices of the children we take, going down from the root to the
    node in the tree. It is called "vpath" because it will mostly be used by values in
    intermediate languages between LLBC## and HLPL. The vpaths are used to:
    - Get the child at a node.
    - Set a child at a node.
 *)
(*
    TODO: motivate the comparison between vpaths (prefix, equal, disjoint).
 *)
Definition vpath := list nat.

(** A spath ("state path") is used to uniquely represent nodes in a state. It is a pair [(i, q)]. The
    positive [i] identifies a value in the state, and the vpath [q] identifies the node in this value.
 *)
Definition spath : Type  := positive * vpath.

(** The concatenation of a spath and a vpath. *)
Definition app_spath_vpath (p : spath) (q : vpath) := (fst p, snd p ++ q).
(* TODO: place the notation in a scope? *)
Notation "p +++ q" := (app_spath_vpath p q) (right associativity, at level 60).

Lemma app_spath_vpath_nil_r (p : spath) : p +++ nil = p.
Proof. apply injective_projections; reflexivity || apply app_nil_r. Qed.

Lemma app_spath_vpath_assoc (p : spath) q r : p +++ q ++ r = (p +++ q) +++ r.
Proof. unfold app_spath_vpath. rewrite app_assoc. reflexivity. Qed.

(** The large and strict prefix relations between two paths. *)
Definition vprefix (p q : vpath) := exists r, p ++ r = q.
Definition vstrict_prefix (p q : vpath) := exists i r, p ++ i :: r = q.

(** Two paths [p] and [q] are disjoint if neither is the prefix of the other. The most useful
    characterization, that we are defining here, is that p and q are of the form
    [r ++ [i] ++ p'] and [r ++ [j] ++ q'], where r is the longest common prefix, and where [i <> j] are
    the first indices where [p] and [q] differ.
 *)
Definition vdisj (p q : vpath) :=
  exists (r p' q' : vpath) i j, i <> j /\ p = r ++ (i :: p') /\ q = r ++ (j :: q').

Global Instance vdisj_symmetric : Symmetric vdisj.
Proof. intros ? ? (v & p & q & i & j & ? & ? & ?). exists v, q, p, j, i. auto. Qed.

(** Showing that every two paths are comparable. *)
Variant vComparable (p q : vpath) : Prop :=
| vCompEq (H : p = q)
| vCompStrictPrefixLeft (H : vstrict_prefix p q)
| vCompStrictPrefixRight (H : vstrict_prefix q p)
| vCompDisj (H : vdisj p q).

Lemma comparable_cons p q i (H : vComparable p q) : vComparable (i :: p) (i :: q).
Proof.
  destruct H as [ <- | (j & r & <-) | (j & r & <-) | (r & ? & ? & ? & ? & ? & -> & ->)].
  - apply vCompEq. reflexivity.
  - apply vCompStrictPrefixLeft. exists j, r. reflexivity.
  - apply vCompStrictPrefixRight. exists j, r. reflexivity.
  - apply vCompDisj. exists (i :: r). repeat eexists. assumption.
Qed.

Lemma comparable_vpaths p : forall q, vComparable p q.
Proof.
  induction p as [ | i p' IH]; intro q; destruct q as [ | j q'].
  - apply vCompEq. reflexivity.
  - apply vCompStrictPrefixLeft. exists j, q'. reflexivity.
  - apply vCompStrictPrefixRight. exists i, p'. reflexivity.
  - destruct (Nat.eq_dec i j) as [<- | diff].
    + apply comparable_cons, IH.
    + apply vCompDisj. exists nil. repeat eexists. assumption.
Qed.

(** Prefixness and disjointness for spaths: *)
Definition prefix (p q : spath) := exists r, p +++ r = q.

Definition strict_prefix (p q : spath) := exists i r, p +++ (i :: r) = q.

Lemma vstrict_prefix_is_vprefix p q : vstrict_prefix p q -> vprefix p q.
Proof. intros (? & ? & ?). eexists. eassumption. Qed.

Lemma strict_prefix_is_prefix (p q : spath) : strict_prefix p q -> prefix p q.
Proof. intros (? & ? & ?). eexists. eassumption. Qed.

Definition disj (p q : spath) :=
(fst p <> fst q) \/ (fst p = fst q /\ vdisj (snd p) (snd q)).

Global Instance symmetric_disj : Symmetric disj.
Proof.
intros p q [? | [? ?]].
+ left. auto.
+ right. split; symmetry; assumption.
Qed.

Variant Comparable (p q : spath) : Prop :=
| CompEq (H : p = q)
| CompStrictPrefixLeft (H : strict_prefix p q)
| CompStrictPrefixRight (H : strict_prefix q p)
| CompDisj (H : disj p q)
.

Lemma comparable_spaths p q : Comparable p q.
Proof.
rewrite (surjective_pairing p), (surjective_pairing q).
destruct (decide (fst p = fst q)) as [<- | ].
- destruct (comparable_vpaths (snd p) (snd q)) as [ <- | (i & r & <-) | (i & r & <-) | ].
  + apply CompEq. reflexivity.
  + apply CompStrictPrefixLeft. exists i, r. unfold app_spath_vpath. cbn. reflexivity.
  + apply CompStrictPrefixRight. exists i, r. unfold app_spath_vpath. cbn. reflexivity.
  + apply CompDisj. right. auto.
- apply CompDisj. left. cbn. assumption.
Qed.

Lemma app_same_nil {B : Type} (x y : list B) (H : x ++ y = x) : y = nil.
Proof. eapply app_inv_head. rewrite H, app_nil_r. reflexivity. Qed.

Lemma prefix_antisym p q (H : prefix p q) (G : prefix q p) : p = q.
Proof.
  destruct H as [r <-]. destruct G as [r' G]. unfold app_spath_vpath in G.
  apply (f_equal snd) in G; cbn in G. rewrite <-app_assoc in G.
  apply app_same_nil, app_eq_nil in G. destruct G as [-> _].
  rewrite app_spath_vpath_nil_r. reflexivity.
Qed.

Lemma vstrict_prefix_irrefl p : ~vstrict_prefix p p.
Proof. intros (? & ? & ?).  apply app_same_nil in H. discriminate. Qed.

Lemma vdisj_irrefl p : ~vdisj p p.
Proof.
  intros (? & ? & ? & ? & ? & ? & H & G). rewrite G in H. apply app_inv_head in H.
  congruence.
Qed.

Lemma strict_prefix_irrefl p : ~strict_prefix p p.
Proof.
  intros (? & ? & ?). apply (f_equal snd) in H. unfold app_spath_vpath in H.
  apply app_same_nil in H. discriminate.
Qed.

Corollary not_prefix_left_strict_prefix_right p q : strict_prefix q p -> ~ prefix p q.
Proof.
  intros ? ?. destruct (prefix_antisym p q).
  - assumption.
  - apply strict_prefix_is_prefix. assumption.
  - apply (strict_prefix_irrefl p). assumption.
Qed.

Lemma not_vprefix_left_vstrict_prefix_right p q : vstrict_prefix q p -> ~vprefix p q.
Proof.
  intros (? & ? & H) (q' & G). rewrite <-(app_nil_r p), <-G, <-app_assoc in H.
  apply app_inv_head in H. destruct q'; discriminate.
Qed.

Lemma not_prefix_implies_not_strict_prefix p q : ~prefix p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. auto. Qed.

Global Instance : Reflexive vprefix.
Proof. intro p. exists nil. apply app_nil_r. Qed.

Global Instance vprefix_trans : Transitive vprefix.
Proof. intros ? ? ? (? & <-) (? & <-). rewrite<- app_assoc. eexists. reflexivity. Qed.

Global Instance prefix_trans : Transitive prefix.
Proof.
  intros ? ? ? (? & <-) (? & <-). rewrite<- app_spath_vpath_assoc. eexists. reflexivity.
Qed.

Global Instance strict_prefix_trans : Transitive strict_prefix.
Proof.
  intros ? ? ? (? & ? & <-) (? & ? & <-). rewrite<- app_spath_vpath_assoc.
  eexists _, _. reflexivity.
Qed.

Global Instance reflexive_prefix : Reflexive prefix.
Proof. intro p. exists nil. apply app_spath_vpath_nil_r. Qed.

Local Hint Unfold app_spath_vpath : core.

Lemma not_vprefix_vdisj p q : vdisj p q -> ~vprefix p q.
Proof.
  intros (r' & p' & q' & i & j & diff & H & G) (r & <-). rewrite H, <-app_assoc in G.
  apply app_inv_head_iff in G. injection G. auto.
Qed.

Lemma not_prefix_disj p q : disj p q -> ~prefix p q.
Proof.
  intros [ | (? & ?)] (? & <-).
  - auto.
  - eapply (not_vprefix_vdisj (snd p) (snd _)); [eassumption | ]. eexists. reflexivity.
Qed.

Lemma not_disj_strict_prefix p q : disj p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. eapply not_prefix_disj; eassumption. Qed.

Corollary not_disj_strict_prefix' p q : disj q p -> ~strict_prefix p q.
Proof. intros H. symmetry in H. apply not_disj_strict_prefix. exact H. Qed.

Lemma vdisj_common_prefix p q r : vdisj (p ++ q) (p ++ r) <-> vdisj q r.
Proof.
  split.
  - intro H. induction p as [ | x p IH].
    + assumption.
    + apply IH. cbn in H.
      destruct H as (p' & q' & r' & i & j & diff & Hqq' & Hrr').
      destruct p' as [ | y p'].
      * apply (f_equal (@hd_error _)) in Hqq', Hrr'. inversion Hqq'. inversion Hrr'.
        congruence.
      * inversion Hqq'. subst y. inversion Hrr'.
        exists p', q', r', i, j. auto.
  - intros (p' & q' & r' & i & j & ? & -> & ->).
    exists (p ++ p'), q', r', i, j. rewrite<- !app_assoc. auto.
Qed.

Corollary disj_common_prefix p q r : disj (p +++ q) (p +++ r) <-> vdisj q r.
Proof.
  split.
  - intros [H | (_ & H) ].
    + cbn in H. congruence.
    + eapply vdisj_common_prefix. exact H.
  - intro. right. split.
    + reflexivity.
    + apply vdisj_common_prefix. assumption.
Qed.

Lemma disj_common_index i p q : disj (i, p) (i, q) <-> vdisj p q.
Proof.
  split.
  - intros [H | (_ & ?)].
    + cbn in H. congruence.
    + assumption.
  - intro. right. auto.
Qed.

Lemma disj_diff_fst a p q : fst p <> a -> disj p (a, q).
Proof. left. assumption. Qed.

Lemma disj_diff_fst' a p q : fst p <> a -> disj (a, q) p.
Proof. left. symmetry. assumption. Qed.

Lemma not_vprefix_implies_not_vstrict_prefix p q : ~vprefix p q -> ~vstrict_prefix p q.
Proof. intros ? ?%vstrict_prefix_is_vprefix. auto. Qed.

Lemma neq_implies_not_prefix p q : ~prefix p q -> p <> q.
Proof. intros H <-. apply H. reflexivity. Qed.

Lemma neq_implies_not_prefix' p q : ~prefix p q -> q <> p.
Proof. intro. symmetry. apply neq_implies_not_prefix. assumption. Qed.

Lemma disj_if_left_disj_prefix p q r : disj p q -> disj p (q +++ r).
Proof.
  intros [ | (? & (x & p' & q' & H))].
  - left. assumption.
  - right. split; [assumption | ]. exists x, p', (q' ++ r).
    decompose [ex and] H. repeat eexists; try eassumption. cbn.
    rewrite app_comm_cons, app_assoc. apply<- app_inv_tail_iff. assumption.
Qed.

Lemma prefix_and_strict_prefix_implies_strict_prefix p q r :
  prefix p q -> strict_prefix q r -> strict_prefix p r.
Proof.
  intros (x & <-) (i & y & <-). rewrite<- app_spath_vpath_assoc.
  destruct (x ++ i :: y) eqn:?.
  - exfalso. eapply app_cons_not_nil. symmetry. eassumption.
  - eexists _, _. reflexivity.
Qed.

Lemma prefix_trans' p q r : prefix (p +++ q) r -> prefix p r.
Proof. transitivity (p +++ q); [ | assumption]. exists q. reflexivity. Qed.

Lemma vprefix_and_neq_implies_vstrict_prefix p q : vprefix p q -> p <> q -> vstrict_prefix p q.
Proof.
  intros ([ | ] & <-) H.
  - rewrite app_nil_r in H. easy.
  - eexists _, _. reflexivity.
Qed.

Lemma prefix_and_neq_implies_strict_prefix p q : prefix p q -> p <> q -> strict_prefix p q.
Proof.
  intros ([ | ] & <-) H.
  - rewrite app_spath_vpath_nil_r in H. easy.
  - eexists _, _. reflexivity.
Qed.

Lemma not_prefix_left_strict_prefix_right' p q : prefix p q -> ~strict_prefix q p.
Proof. intros ? ?. eapply not_prefix_left_strict_prefix_right; eassumption. Qed.

Corollary disj_if_right_disj_prefix p q r : disj p q -> disj (p +++ r) q.
Proof. intro. symmetry. apply disj_if_left_disj_prefix. symmetry. assumption. Qed.

Lemma decidable_vpath_eq (p q : vpath) : p = q \/ p <> q.
Proof.
  destruct (comparable_vpaths p q) as [ | | | ].
  - left. assumption.
  - right. intros <-. eapply vstrict_prefix_irrefl. eassumption.
  - right. intros <-. eapply vstrict_prefix_irrefl. eassumption.
  - right. intros <-. eapply vdisj_irrefl. eassumption.
Qed.

Lemma decidable_spath_eq (p q : spath) : p = q \/ p <> q.
Proof.
  destruct p as (i & p'). destruct q as (j & q').
  destruct (decide (i = j)); destruct (decidable_vpath_eq p' q'); intuition congruence.
Qed.

Lemma decidable_vprefix p q : vprefix p q \/ ~vprefix p q.
Proof.
  destruct (comparable_vpaths p q) as [<- | | | ].
  - left. reflexivity.
  - left. apply vstrict_prefix_is_vprefix. assumption.
  - right. apply not_vprefix_left_vstrict_prefix_right. assumption.
  - right. apply not_vprefix_vdisj. assumption.
Qed.

Lemma decidable_prefix p q : prefix p q \/ ~prefix p q.
Proof.
  destruct (comparable_spaths p q) as [<- | | | ].
  - left. reflexivity.
  - left. apply strict_prefix_is_prefix. assumption.
  - right. apply not_prefix_left_strict_prefix_right. assumption.
  - right. apply not_prefix_disj. assumption.
Qed.

Lemma prefix_if_equal_or_strict_prefix (p q : spath) : prefix p q -> p = q \/ strict_prefix p q.
Proof.
  intros ([ | i r] & <-).
  - left. symmetry. apply app_spath_vpath_nil_r.
  - right. exists i, r. reflexivity.
Qed.

Lemma prove_not_prefix (p q : spath) : p <> q -> ~strict_prefix p q -> ~prefix p q.
Proof. intros ? ? [ | ]%prefix_if_equal_or_strict_prefix; auto. Qed.

Lemma prove_disj (p q : spath) : p <> q -> ~strict_prefix p q -> ~strict_prefix q p -> disj p q.
Proof. destruct (comparable_spaths p q); easy. Qed.

Lemma prove_disj' (p q : spath) : ~strict_prefix q p -> ~prefix p q -> disj p q.
Proof.
  intros. apply prove_disj; auto using not_prefix_implies_not_strict_prefix, neq_implies_not_prefix.
Qed.

Lemma vstrict_prefix_app_last p q i : vstrict_prefix p (q ++ i :: nil) -> vprefix p q.
Proof.
  intros (j & r & ?).
  destruct exists_last with (l := j :: r) as (r' & j' & G). { symmetry. apply nil_cons. }
  rewrite G in H. apply f_equal with (f := @removelast _) in H.
  rewrite app_assoc in H. rewrite !removelast_last in H. exists r'. exact H.
Qed.

Corollary strict_prefix_app_last p q i : strict_prefix p (q +++ [i]) <-> prefix p q.
Proof.
  split.
  - intros (j & r & H). inversion H.
    destruct (vstrict_prefix_app_last (snd p) (snd q) i) as (r' & ?).
    + exists j, r. assumption.
    + exists r'. apply injective_projections; assumption.
  - intros (r & <-). rewrite<- app_spath_vpath_assoc. destruct (r ++ [i]) eqn:EQN.
    + symmetry in EQN. apply app_cons_not_nil in EQN. destruct EQN.
    + eexists _, _. reflexivity.
Qed.

Corollary not_strict_prefix_app_last p q i : ~strict_prefix p (q +++ [i]) <-> ~prefix p q.
Proof. split; intros H ?; eapply H, strict_prefix_app_last; eassumption. Qed.

Lemma not_strict_prefix_nil (p : spath) i : ~strict_prefix p (i, []).
Proof.
  intros (? & ? & H). apply (f_equal snd) in H. eapply app_cons_not_nil. symmetry. exact H.
Qed.

Lemma prefix_of_disj_implies_not_prefix p q r : prefix p q -> disj q r -> ~prefix r p.
Proof.
  intros ? ? ?. assert (prefix r q) by (transitivity p; assumption).
  eapply not_prefix_disj; [symmetry | ]; eassumption.
Qed.

Lemma prefix_nil p i : prefix p (i, []) -> p = (i, []).
Proof.
  destruct p as (j & q). intros (r & H). unfold app_spath_vpath in H. cbn in H.
  apply pair_equal_spec in H. destruct H as (-> & H).
  apply app_eq_nil in H. destruct H as (-> & _). reflexivity.
Qed.

Lemma app_spath_vpath_inv_head p q r : p +++ q = p +++ r -> q = r.
Proof. intros H%(f_equal snd). eapply app_inv_head. exact H. Qed.

(** Automatic resolution of comparisons between path. *)
Hint Resolve disj_diff_fst : spath.
Hint Resolve disj_diff_fst' : spath.
Hint Resolve not_strict_prefix_nil : spath.
Hint Extern 0 (prefix ?p (?p +++ ?q)) => exists q; reflexivity : spath.
Hint Extern 0 (prefix (?p +++ ?q) (?p +++ ?q ++ ?r)) =>
    exists r; symmetry; apply app_spath_vpath_assoc : spath.

(** * Interface for values. *)
Declare Scope GetSetPath_scope.
Open Scope GetSetPath_scope.

(** A value [v : V] is a tree-like structure. It is characterize by:
   - A node [get_node v], of type [nodes].
   - A list of subvalues [children v].
   - A weight function.
   Also, each node [n] is associated to a fixed number of children [arity n].

   For example, take the value [u = borrow^m(ell, (3, 4))].
   - Its node is [borrow^m(ell, -)]
   - It gets a unique child [v = (3, 4)]
     - The node of v is the pair node [(-, -)]
     - The children of v are [[3, 4]].

   Thus, we can see that:
   - The arity of the node [borrow^m(ell, -)] is 1 (it is a unary node).
   - The arity of the node [(-, -)] is 2 (it is a binary node).
   - The arity of the nodes 3 and 4 are 0 (they are zeroary nodes).
 *)
Class Value (V nodes : Type) `{EqDecision nodes} := {
  arity : nodes -> nat;
  children : V -> list V;
  get_node : V -> nodes;
  (** Create a value given a node and a list of children. This is a total function. Therefore, if
      the numbers of children differ from the arity, the result is unspecified. *)
  fold_value : nodes -> list V -> V;
  (** The sum of some quantity for each node of the tree. *)
  vweight : (nodes -> nat) -> V -> nat;
  (** A special zero-ary value [bot]. *)
  bot : V;

  (** Axioms on values. *)
  length_children_is_arity v : length (children v) = arity (get_node v);
  get_nodes_children_inj v w :
    get_node v = get_node w -> children v = children w -> v = w;
  get_node_fold_value c vs (H : length vs = arity c) : get_node (fold_value c vs) = c;
  children_fold_value c vs (H : length vs = arity c) : children (fold_value c vs) = vs;
  children_bot : children bot = nil;
  vweight_prop weight v :
    vweight weight v = sum (map (vweight weight) (children v)) + (weight (get_node v))
}.

Notation get_subval_or_bot w i :=
  (match nth_error (children w) i with
    | Some u => u
    | None => bot
  end).
(** Read a value at path [p]. If the path p is invalid, return bot. *)
Definition vget {V} `{Value V nodes} : vpath -> V -> V :=
  fold_left (fun w i => get_subval_or_bot w i).
Notation "v .[[ p ]]" := (vget p v) (left associativity, at level 50) : GetSetPath_scope.

(** Set the value at path [p] to [w] in [v]. If the path [p] is invalid, the value [v] is unchanged. *)
Fixpoint vset {V} `{Value V nodes} (p : vpath) (w : V) (v : V) :=
  match p with
  | nil => w
  | i :: q => fold_value (get_node v) (alter_list (children v) i (vset q w))
  end.
Notation "v .[[ p <- w ]]" := (vset p w v) (left associativity, at level 50).

Definition anon := positive.

(** * Interface for states. *)
(** The main ideas for the [State] typeclass are that:
   - A state can be accessed by positives. Any accessor (variable, anonymous binding, abstraction
     element) can be encoded as a positive number.
   - As such, an element [S : state] can be turned into a map, using the method [get_map]
     This map associates positive numbers to values of type [V], with [V] a type that
     satisfies the [Value] typeclass.
   - It is also possible to modify a state as a given positive number, using the method
     [alter_at_accessor]
 *)
(** Note: I am not satisfied with accessors being positive numbers. It should be an arbitrary type.
    In particular, it would be more natural to use a sum type. *)
Class State (state : Type) V `{Value V} := {
  get_map : state -> Pmap V;
  alter_at_accessor : (V -> V) -> positive -> state -> state;

  (** The [extra] type describes all the information that is not contained in the positive
      map. For example, it can be the unit type if [get_map] is injective. For LLBC## and
      LLBC+, the [extra] type is the set of abstractions. *)
  extra : Type;
  get_extra : state -> extra;

  (** The [get_map] and [get_extra] methods completely characterize a state. *)
  state_eq_ext S S' :
    get_map S = get_map S' -> get_extra S = get_extra S' -> S = S';

  (** The method [alter_at_accessor] only updates one value, at accessor a. It does not affect
      the "extra" part of the state. *)
  get_extra_alter S f a : get_extra (alter_at_accessor f a S) = get_extra S;
  get_map_alter S f a : get_map (alter_at_accessor f a S) = alter f a (get_map S);

  (** Generic management of anonymous bindings. *)
  (* TODO: this should be a superclass of [State] *)
  (* The injection from anonymous bindings to positive accessors: *)
  anon_accessor : anon -> positive;
  (* The reciprocal injection. *)
  accessor_anon : positive -> option anon;
  anon_accessor_inj a : accessor_anon (anon_accessor a) = Some a;
  (* It is always possible to add an anonymous value. This insert a new value in the state map,
     and it does not affect the "extra" part of the state. *)
  add_anon : anon -> V -> state -> state;
  get_map_add_anon a v S : get_map (add_anon a v S) = insert (anon_accessor a) v (get_map S);
  get_extra_add_anon a v S : get_extra (add_anon a v S) = get_extra S;
}.
(** Reading at an accessor is performed by only reading in the state map. *)
Notation get_at_accessor S a := (lookup a (get_map S)).
Notation "S ,, a  |->  v" := (add_anon a v S) (left associativity, at level 63, v at level 61).

(** Read a value at path [p]. If the path p is invalid, return [bot]. *)
Definition sget {state V} `{State state V} (p : spath) (S : state) : V :=
  match get_at_accessor S (fst p) with
  | Some v => v.[[snd p]]
  | None => bot
  end.
Notation "S .[ p ]" := (sget p S) (left associativity, at level 50) : GetSetPath_scope.
Local Hint Unfold sget : core.

(** Set the value at path [p] to [v] in [S]. If [p] is invalid, return [S]. *)
Definition sset {state V} `{State state V} (p : spath) (v : V) (S : state) : state :=
  alter_at_accessor (vset (snd p) v) (fst p) S.
Notation "S .[ p <- v ]" := (sset p v S) (left associativity, at level 50).
Local Hint Unfold sset : core.

Section GetSetPath.
  Context {V state : Type}.
  Context `{IsState : State state V}.

  (** * Definitions and lemmas for values and vpaths. *)
  Lemma vget_app v p q : v.[[p ++ q]] = v.[[p]].[[q]].
  Proof. unfold vget. apply fold_left_app. Qed.

  (** ** Validity of vpaths. *)
  (** A vpath [p] is valid with regards to a value [v] if we can follow its indices down the value [v]
      interpreted as a tree. *)
  Inductive valid_vpath : V -> vpath -> Prop :=
    | valid_nil v : valid_vpath v nil
    | valid_cons v i p w :
        nth_error (children v) i = Some w -> valid_vpath w p -> valid_vpath v (i :: p).

  Lemma valid_vpath_app v p q :
    valid_vpath v (p ++ q) <-> valid_vpath v p /\ valid_vpath (v.[[p]]) q.
  Proof.
    split.
    - revert v. induction p as [ | i p IHp].
      + split. constructor. assumption.
      + intros v G. inversion G. subst. split.
        * econstructor; try apply IHp; eassumption.
        * apply IHp. simplify_option.
    - intros (valid_p & valid_q). induction valid_p.
      + exact valid_q.
      + cbn. econstructor.
        * eassumption.
        * cbn in valid_q. simplify_option.
  Qed.

  (** We characterize invalid path by their longest valid prefix [q]. This means that the next
      index [i] is out-of-bounds.*)
  Definition invalid_vpath v p :=
    exists q i r, p = q ++ i :: r /\ valid_vpath v q /\ nth_error (children (v.[[q]])) i = None.

  Lemma valid_or_invalid p : forall v, valid_vpath v p \/ invalid_vpath v p.
  Proof.
    induction p as [ | i p IHp].
    - left. constructor.
    - intro v. destruct (nth_error (children v) i) as [w | ] eqn:EQN.
      + destruct (IHp w) as [ | (q & j & r & -> & valid_q & G)].
        * left. econstructor; eassumption.
        * right. exists (i :: q), j, r. repeat split.
          -- econstructor; eassumption.
          -- cbn. rewrite EQN. exact G.
      + right. exists nil, i, p. repeat split; constructor || assumption.
  Qed.

  Lemma not_valid_and_invalid v p : valid_vpath v p -> invalid_vpath v p -> False.
  Proof.
    intros valid_v_p (q & i & r & -> & valid_p & G). apply valid_vpath_app in valid_v_p.
    destruct valid_v_p as [_ validity']. inversion validity'. simplify_option.
  Qed.

  Lemma vget_bot p : bot.[[p]] = bot.
  Proof.
     induction p.
    - reflexivity.
    - cbn. rewrite children_bot, nth_error_nil. assumption.
  Qed.

  (* TODO: move comment at the definition of vget. *)
  (** The vget function is defined in such a way that for any invalid path p, [v.[[p]] = bot]
      This relies on two design choices:
      - For a value v, if the index i is the index of a child, then
        [v.[[i :: r]] = bot.[[r]]]
      - [bot] has 0 children ([children_bot] axiom), so [bot.[[r]] = r]
   *)
  Lemma vget_invalid v p : invalid_vpath v p -> v.[[p]] = bot.
  Proof.
    intros (q & i & r & -> & _ & Hout). rewrite vget_app. cbn. rewrite Hout. apply vget_bot.
  Qed.

  (** A useful criterion for validity: if [v.[[p]] <> bot], then [p] is a valid path for [v].
      Using that criterion, we do not have to specify that a path is valid when the contained value
      is known and is not [bot]. *)
  Corollary get_not_bot_valid_vpath v p : v.[[p]] <> bot -> valid_vpath v p.
  Proof.
    intros ?. destruct (valid_or_invalid p v).
    - assumption.
    - exfalso. auto using vget_invalid.
  Qed.

  Corollary valid_get_node_vget_not_bot v p : get_node (v.[[p]]) <> get_node bot -> valid_vpath v p.
  Proof. intros G. apply get_not_bot_valid_vpath. congruence. Qed.

  Lemma invalid_prefix v p q : invalid_vpath v p -> invalid_vpath v (p ++ q).
  Proof.
    intros (p' & i & r & -> & ?). exists p', i, (r ++ q). split.
    - rewrite <-app_assoc. reflexivity.
    - assumption.
  Qed.

  (** ** Equations on the vget and vset operations. *)
  Lemma get_node_vset_cons v p w :
    p <> [] -> get_node (v.[[p <- w]]) = get_node v.
  Proof.
    intro. destruct p; [congruence | ].
    apply get_node_fold_value. rewrite alter_list_length. apply length_children_is_arity.
  Qed.

  Lemma children_vset_cons v i p w :
    children (v.[[i :: p <- w]]) = alter_list (children v) i (vset p w).
  Proof. apply children_fold_value. rewrite alter_list_length. apply length_children_is_arity. Qed.

  Lemma vget_cons v i p : v.[[i :: p]] = (get_subval_or_bot v i).[[p]].
  Proof. reflexivity. Qed.

  Lemma vstrict_prefix_one_child v p q (length_one : length (children (v.[[p]])) = 1) :
    vstrict_prefix p q -> valid_vpath v q -> vprefix (p ++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_vpath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- length_one. apply nth_error_Some.
      inversion G. destruct (nth_error (children (v.[[p]]))); easy. }
    exists r. rewrite<- app_assoc. reflexivity.
  Qed.

  Corollary not_vprefix_one_child v p q :
    length (children (v.[[p]])) = 1 -> valid_vpath v q -> ~vprefix (p ++ [0]) q
    -> ~vstrict_prefix p q.
  Proof. intros ? ? not_prefix ?. eapply not_prefix, vstrict_prefix_one_child; eassumption. Qed.

  (* All of the lemmas to reduce an expression of the form [v.[[q <- w]].[[p]]], depending on the
   * following cases:
   * - p = q
   * - p is a prefix of q
   * - q is a prefix of p
   * - p and q are disjoint
   *)
  Lemma vset_vget_prefix v w p q (valid_v_p : valid_vpath v p) :
    v.[[p ++ q <- w]].[[p]] = v.[[p]].[[q <- w]].
  Proof.
    induction valid_v_p as [ | v i p u subval_v_i valid_u_p IH].
    - reflexivity.
    - rewrite vget_cons, <-app_comm_cons, children_vset_cons, nth_error_alter_list_eq.
      simplify_option.
  Qed.

  Corollary vset_vget_equal v w p : valid_vpath v p -> v.[[p <- w]].[[p]] = w.
  Proof. intro. rewrite<- (app_nil_r p) at 2. rewrite vset_vget_prefix; auto. Qed.

  Lemma vset_same_valid v w p (valid_v_p : valid_vpath v p) : valid_vpath (v.[[p <- w]]) p.
  Proof.
    induction valid_v_p as [ | ? ? ? ? validity'].
    - constructor.
    - econstructor.
      + rewrite children_vset_cons, nth_error_alter_list_eq, validity'. reflexivity.
      + assumption.
  Qed.

  Corollary vset_vget_prefix_right v w p q :
    valid_vpath v p -> v.[[p <- w]].[[p ++ q]] = w.[[q]].
  Proof. intros ?. rewrite vget_app, vset_vget_equal; try apply vset_same_valid; auto. Qed.

  (* The validity condition is unnecessary, we are going to remove it. *)
  Lemma _vset_app_split v p q w (valid_v_p : valid_vpath v p) :
    v.[[p ++ q <- w]] = v.[[p <- v.[[p]].[[q <- w]]]].
  Proof.
    induction valid_v_p.
    - reflexivity.
    - cbn. f_equal. eapply alter_list_equal_Some; simplify_option.
  Qed.

  Lemma _vset_same v p (valid_p : valid_vpath v p) : v.[[p <- v.[[p]]]] = v.
  Proof.
    induction valid_p.
    - reflexivity.
    - apply get_nodes_children_inj.
      + apply get_node_vset_cons. discriminate.
      + rewrite children_vset_cons. eapply alter_list_invariant; simplify_option.
  Qed.

  (* TODO: move commment at the definition of [vset] *)
  (** [vset] is defined in such a way that [v.[[p <- w]] = v] when p is invalid.
      This trick allows us to omit validity hypotheses in some lemmas.
   *)
  Lemma vset_invalid v p w : invalid_vpath v p -> v.[[p <- w]] = v.
  Proof.
    intros (q & i & r & -> & valid_q & ?). rewrite<- (_vset_same v q) at 2 by assumption.
    rewrite _vset_app_split by assumption. f_equal.
    apply get_nodes_children_inj.
    - apply get_node_vset_cons. discriminate.
    - rewrite children_vset_cons. apply alter_list_equal_None. assumption.
  Qed.

  Lemma vset_vget_disj_aux v i j p q w :
    i <> j -> v.[[i :: p <- w]].[[j :: q]] = v.[[j :: q]].
  Proof. intro. rewrite vget_cons, children_vset_cons, nth_error_alter_list_neq; auto. Qed.

  Lemma vset_vget_disj v w p q (Hvdisj : vdisj p q) :
    v.[[p <- w]].[[q]] = v.[[q]].
  Proof.
    destruct (valid_or_invalid p v) as [G | ].
    - destruct Hvdisj as (r & p' & q' & i & j & diff & -> & ->).
      apply valid_vpath_app in G. destruct G as [? _].
      rewrite !vget_app, vset_vget_prefix by assumption. apply vset_vget_disj_aux. assumption.
    - rewrite vset_invalid; auto.
  Qed.

  Lemma get_node_vset_vget_strict_prefix v p q w :
    vstrict_prefix p q -> get_node (v.[[q <- w]].[[p]]) = get_node (v.[[p]]).
  Proof.
     intros (i & r & <-). destruct (valid_or_invalid p v).
     - rewrite vset_vget_prefix by assumption. apply get_node_vset_cons. discriminate.
     - assert (invalid_vpath v (p ++ i :: r)) by now apply invalid_prefix.
       now rewrite vset_invalid.
  Qed.

  Lemma get_node_vset_vget_not_prefix v p q w (Hnot_prefix : ~vprefix q p) :
    get_node (v.[[q <- w]].[[p]]) = get_node (v.[[p]]).
  Proof.
    destruct (comparable_vpaths p q) as [<- | | (? & ? & ?) | ].
    - destruct Hnot_prefix. exists nil. apply app_nil_r.
    - apply get_node_vset_vget_strict_prefix. assumption.
    - firstorder.
    - rewrite vset_vget_disj; [reflexivity | symmetry; assumption].
  Qed.

  Lemma vset_twice_equal p x y : forall v, v.[[p <- x]].[[p <- y]] = v.[[p <- y]].
  Proof.
    induction p; intro v.
    - reflexivity.
    - apply get_nodes_children_inj.
      + rewrite !get_node_vset_cons by discriminate. reflexivity.
      + rewrite !children_vset_cons, alter_list_compose. apply alter_list_equiv. assumption.
  Qed.

  Lemma vset_same v p : v.[[p <- v.[[p]]]] = v.
  Proof.
    destruct (valid_or_invalid p v).
    - now apply _vset_same.
    - rewrite vset_invalid; [reflexivity | assumption].
  Qed.

  (* Now that we proved that [v.[[p <- w]] = v] when p in invalid, we can remove the validity
     hypothesis from the theorem [_vset_app_split] *)
  Lemma vset_app_split v p q w : v.[[p ++ q <- w]] = v.[[p <- v.[[p]].[[q <- w]]]].
  Proof.
    destruct (valid_or_invalid p v) as [ | ].
    - apply _vset_app_split. assumption.
    - rewrite !vset_invalid; try auto. apply invalid_prefix. assumption.
  Qed.

  Lemma vset_twice_prefix_right v p q x y : vprefix q p -> v.[[p <- x]].[[q <- y]] = v.[[q <- y]].
  Proof. intros (? & <-). rewrite vset_app_split, vset_twice_equal. reflexivity. Qed.

  Lemma vset_twice_prefix_left v p q x y : v.[[p <- x]].[[p ++ q <- y]] = v.[[p <- x.[[q <- y]]]].
  Proof.
    rewrite vset_app_split, vset_twice_equal. destruct (valid_or_invalid p v).
    - rewrite vset_vget_equal; auto.
    - rewrite !vset_invalid; auto.
  Qed.

  Lemma vset_twice_disj_commute_aux v p q i j x y :
    i <> j -> v.[[i :: p <- x]].[[j :: q <- y]] = v.[[j :: q <- y]].[[i :: p <- x]].
  Proof.
    intro. apply get_nodes_children_inj.
    - rewrite !get_node_vset_cons by discriminate. reflexivity.
    - rewrite !children_vset_cons. apply alter_list_neq_commute. assumption.
  Qed.

  Lemma vset_twice_disj_commute v p q x y :
    vdisj p q -> v.[[p <- x]].[[q <- y]] = v.[[q <- y]].[[p <- x]].
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->).
    rewrite !(vset_app_split v). rewrite !vset_twice_prefix_left.
    rewrite vset_twice_disj_commute_aux; auto.
  Qed.

  (** ** Lemmas about weighted sums on values. *)
  (** The size of value can be used for general induction proofs on values. *)
  Definition vsize := vweight (fun _ => 1).
  Lemma vsize_decreasing (v w : V) i : nth_error (children v) i = Some w -> vsize w < vsize v.
  Proof.
    unfold vsize. intro ith_child. rewrite (vweight_prop _ v).
    apply map_nth_error with (f := vweight (fun _ => 1)) in ith_child.
    apply sum_ge_element in ith_child. lia.
  Qed.

  Lemma value_get_node_ext v w : (forall p, get_node (v.[[p]]) = get_node (w.[[p]])) -> v = w.
  Proof.
    remember (vsize v) as n eqn:Heqn. revert v w Heqn.
    induction n as [n IH] using lt_wf_ind. intros v w -> eq_vget.
    assert (get_node v = get_node w) by (apply (eq_vget [])).
    assert (eq_length : length (children v) = length (children w)).
    { rewrite !length_children_is_arity. congruence. }
    apply get_nodes_children_inj.
    - assumption.
    - apply nth_error_ext. intros i.
      destruct (nth_error (children v) i) as [ | ] eqn:ith_v.
      + destruct (nth_error_Some' (children w) i) as (? & ith_w).
        { rewrite <-eq_length, <-nth_error_Some. congruence. }
        rewrite ith_w. f_equal. eapply IH.
        * eapply vsize_decreasing. exact ith_v.
        * reflexivity.
        * intros p. specialize (eq_vget (i :: p)). cbn in eq_vget.
          rewrite ith_v, ith_w in eq_vget. assumption.
      + symmetry. rewrite nth_error_None in *. congruence.
  Qed.

  Context (weight : nodes -> nat).

  Notation vweight_ := (vweight weight).

  (** These are the two equations that relate vweight/sweight and vset/sset:
     - [weight (v.[[p <- w]]) = weight v - weight (v.[[p]]) + weight w]
     - [weight (S.[p <- v]) = weight S - weight (S.[p]) + weight v]
     Both involve a substraction. Proving (in)equalities with natural substraction is
     inconvenient, because is requires proving at each time that the weight of [v]
     (resp. [S]) is greater than the weight of [v.[[p]]] (resp. [S.[p]]).
     This is why we use relatives to avoid these complications. *)
  Lemma vweight_vset v p w
    (valid_p : valid_vpath v p) :
    Z.of_nat (vweight_ (v.[[p <- w]])) = (vweight_ v - vweight_ (v.[[p]]) + vweight_ w)%Z.
  Proof.
    induction valid_p as [ | u i p v].
    - cbn. lia.
    - rewrite (vweight_prop _ u).
      rewrite (vweight_prop _ (u.[[i :: p <- w]])).
      rewrite get_node_vset_cons by discriminate.
      rewrite children_vset_cons.
      erewrite map_alter_list by eassumption.
      rewrite Nat2Z.inj_add.
      erewrite sum_alter_list by (erewrite map_nth_error by eassumption; reflexivity).
      replace (u.[[i :: p]]) with (v.[[p]]) by simplify_option. lia.
  Qed.

  Lemma weight_vget_le v p (valid_p : valid_vpath v p) : vweight_ (v.[[p]]) <= vweight_ v.
  Proof.
    induction valid_p as [ | ? ? ? ? ith_child].
    - reflexivity.
    - rewrite (vweight_prop _ v). cbn. rewrite ith_child.
      apply (map_nth_error vweight_) in ith_child. apply sum_ge_element in ith_child. lia.
  Qed.

  Lemma weight_vget_node_le v p (valid_p : valid_vpath v p) :
    weight (get_node (v.[[p]])) <= vweight_ v.
  Proof. pose proof (weight_vget_le v p valid_p) as G. rewrite vweight_prop in G. lia. Qed.

  Lemma weight_arity_0 (v : V) :
    arity (get_node v) = 0 -> vweight weight v = weight (get_node v).
  Proof.
    intros arity_0. rewrite vweight_prop.
    rewrite<- length_children_is_arity in arity_0. apply length_zero_iff_nil in arity_0.
    rewrite arity_0. reflexivity.
  Qed.

  Lemma weight_arity_1 (v : V) (arity_1 : arity (get_node v) = 1) :
    vweight weight v = weight (get_node v) + vweight weight (v.[[ [0] ]]).
  Proof.
    rewrite vweight_prop. cbn.
    rewrite<- length_children_is_arity in arity_1. apply length_1_is_singleton in arity_1.
    destruct arity_1 as (? & ->). cbn. lia.
  Qed.

  (** * Definitions and lemmas for states and spaths. *)
  Lemma sget_app (S : state) p q : S.[p +++ q] = S.[p].[[q]].
  Proof.
    unfold sget, app_spath_vpath. cbn. destruct (get_at_accessor S (fst p)).
    - apply vget_app.
    - rewrite vget_bot. reflexivity.
  Qed.

  (** ** Validity of spaths. *)
  Definition valid_spath (S : state) (p : spath) :=
    exists v, get_at_accessor S (fst p) = Some v /\ valid_vpath v (snd p).
  Hint Unfold valid_spath : core.

  Lemma valid_spath_app (S : state) p q :
    valid_spath S (p +++ q) <-> valid_spath S p /\ valid_vpath (S.[p]) q.
  Proof.
    split.
    - intros (v & ? & G). cbn in *. rewrite valid_vpath_app in G. destruct G.
      split.
      + exists v. auto.
      + unfold sget. simplify_option.
    - intros [(v & get_S_p & ?) valid_q]. exists v. cbn. split.
      + assumption.
      + apply valid_vpath_app. unfold sget in valid_q. rewrite get_S_p in valid_q. auto.
  Qed.

  Lemma get_not_bot_valid_spath (S : state) p : S.[p] <> bot -> valid_spath S p.
  Proof.
    unfold sget. intros ?. destruct (get_at_accessor S (fst p)) as [v | ] eqn:EQN.
    - exists v. split. { assumption. } apply get_not_bot_valid_vpath. assumption.
    - exfalso. eauto.
  Qed.

  Corollary valid_get_node_sget_not_bot S p : get_node (S.[p]) <> get_node bot -> valid_spath S p.
  Proof. intros G. apply get_not_bot_valid_spath. intro K. apply G. rewrite K. reflexivity. Qed.

  Lemma valid_spath_app_last_get_node_not_zeroary S p :
    arity (get_node (S.[p])) > 0 -> valid_spath S (p +++ [0]).
  Proof.
    intros arity_0. apply valid_spath_app. split.
    - apply valid_get_node_sget_not_bot. intros G.
      rewrite G, <-length_children_is_arity, children_bot in arity_0. easy.
    - rewrite<- length_children_is_arity in arity_0. apply nth_error_Some' in arity_0.
      destruct arity_0. econstructor; [eassumption | constructor].
  Qed.

  Lemma strict_prefix_one_child S p q (length_one : length (children (S.[p])) = 1) :
    strict_prefix p q -> valid_spath S q -> prefix (p +++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_spath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- length_one. inversion G. eauto using nth_error_length. }
    exists r. rewrite<- app_spath_vpath_assoc. reflexivity.
  Qed.

  Corollary not_prefix_one_child S p q :
    length (children (S.[p])) = 1 -> valid_spath S q -> ~prefix (p +++ [0]) q -> ~strict_prefix p q.
  Proof. intros. eauto using strict_prefix_one_child. Qed.

  Lemma decidable_valid_spath S p : valid_spath S p \/ ~valid_spath S p.
  Proof.
    unfold valid_spath.
    destruct (get_at_accessor S (fst p)) as [v | ].
    - destruct (valid_or_invalid (snd p) v).
      + left. exists v. auto.
      + right. intros (? & [=<-] & ?). eauto using not_valid_and_invalid.
    - right. intros (? & ? & _). discriminate.
  Qed.

  Lemma vset_is_zeroary v w p :
    valid_vpath v p -> arity (get_node (v.[[p <- w]])) = 0 -> p = [].
  Proof.
    intros valid_p. inversion valid_p.
    - reflexivity.
    - rewrite get_node_vset_cons; [ | discriminate]. rewrite <-length_children_is_arity.
      intros G%nil_length_inv. rewrite G, nth_error_nil in * |-. discriminate.
  Qed.

  Lemma sget_invalid S p : ~valid_spath S p -> S.[p] = bot.
  Proof.
    autounfold. intros G. destruct (get_at_accessor S (fst p)) as [v | ].
    - apply vget_invalid. destruct (valid_or_invalid (snd p) v); [ | assumption].
      exfalso. eapply G. exists v. auto.
    - reflexivity.
  Qed.

  Lemma sset_invalid S p v : ~valid_spath S p -> S.[p <- v] = S.
  Proof.
    autounfold. intros G. apply state_eq_ext.
    - rewrite get_map_alter. apply alter_id. intros w ?. apply vset_invalid.
      destruct (valid_or_invalid (snd p) w); [ | assumption].
      exfalso. apply G. exists w. auto.
    - apply get_extra_alter.
  Qed.

  (** ** Equations on the sget and sset operations. *)
  Lemma sset_sget_prefix (S : state) v p q :
    valid_spath S p -> S.[p +++ q <- v].[p] = S.[p].[[q <- v]].
  Proof.
    intros (w & Hget & Hvalid). unfold sget, sset. cbn.
    rewrite get_map_alter, lookup_alter_eq, Hget. apply vset_vget_prefix. assumption.
  Qed.

  Lemma sset_sget_equal S p v : valid_spath S p -> S.[p <- v].[p] = v.
  Proof.
    intro. rewrite <-(app_spath_vpath_nil_r p) at 2.
    rewrite sset_sget_prefix; auto.
  Qed.

  Lemma sset_sget_prefix_right S v p q : valid_spath S p -> S.[p <- v].[p +++ q] = v.[[q]].
  Proof. intros ?. rewrite sget_app, sset_sget_equal; auto. Qed.

  Lemma sset_sget_common_prefix S p q r v :
    valid_spath S p -> S.[p +++ q <- v].[p +++ r] = S.[p].[[q <- v]].[[r]].
  Proof. intro. rewrite sget_app. rewrite sset_sget_prefix by assumption. reflexivity. Qed.

  Lemma get_at_accessor_sset_disj S p v a :
    fst p <> a -> get_at_accessor (S.[p <- v]) a = get_at_accessor S a.
  Proof. intros ?. unfold sset. now rewrite get_map_alter, lookup_alter_ne. Qed.

  Lemma sset_sget_disj (S : state) p v q : disj p q -> S.[p <- v].[q] = S.[q].
  Proof.
    unfold sget. intros [Hdiff | (<- & Hdisj)].
    - rewrite get_at_accessor_sset_disj by assumption. reflexivity.
    - unfold sset. rewrite get_map_alter, lookup_alter_eq.
      destruct (get_at_accessor S (fst p)).
      + cbn. apply vset_vget_disj. assumption.
      + reflexivity.
  Qed.

  (* During the proof of this theorem, we implicitely use the fact that if the spath p is
   * invalid, then the spath q is invalid, and S.[q <- w] = S. *)
  Lemma get_node_sset_sget_strict_prefix (S : state) p q w :
    strict_prefix p q -> get_node (S.[q <- w].[p]) = get_node (S.[p]).
  Proof.
    unfold sset, sget. intro Hstrict_prefix.
    assert (fst p = fst q) as ->. { destruct Hstrict_prefix as (? & ? & <-). reflexivity. }
    rewrite get_map_alter, lookup_alter_eq.
    destruct (get_at_accessor S (fst q)).
    - apply get_node_vset_vget_strict_prefix.
      destruct Hstrict_prefix as (? & ? & <-). eexists _, _. reflexivity.
    - reflexivity.
  Qed.

  Lemma get_node_sset_sget_not_prefix (S : state) p q w (Hnot_prefix : ~prefix q p) :
    get_node (S.[q <- w].[p]) = get_node (S.[p]).
  Proof.
    destruct (comparable_spaths p q) as [<- | | | ].
    - destruct Hnot_prefix. reflexivity.
    - apply get_node_sset_sget_strict_prefix. assumption.
    - destruct Hnot_prefix. apply strict_prefix_is_prefix. assumption.
    - rewrite sset_sget_disj; reflexivity || symmetry; assumption.
  Qed.

  Lemma sset_app_split S p q v : S.[p +++ q <- v] = S.[p <- S.[p].[[q <- v]] ].
  Proof.
    autounfold. unfold sget. cbn. apply state_eq_ext.
    - rewrite !get_map_alter. apply alter_ext. intros ? ->. apply vset_app_split.
    - rewrite !get_extra_alter. reflexivity.
  Qed.

  Lemma sset_twice_prefix_left (S : state) p q x y :
    S.[p <- x].[p +++ q <- y] = S.[p <- x.[[q <- y]]].
  Proof.
    autounfold. cbn. apply state_eq_ext.
    - rewrite !get_map_alter, alter_alter_eq.
      apply alter_ext. intros ? _. apply vset_twice_prefix_left.
    - rewrite !get_extra_alter. reflexivity.
  Qed.

  Corollary sset_twice_equal (S : state) p x y : S.[p <- x].[p <- y] = S.[p <- y].
  Proof.
    pose proof (sset_twice_prefix_left S p [] x y) as eq_states.
    rewrite app_spath_vpath_nil_r in eq_states. assumption.
  Qed.

  Corollary sset_twice_prefix_right (S : state) p q x y :
    S.[p +++ q <- x].[p <- y] = S.[p <- y].
  Proof. rewrite sset_app_split. apply sset_twice_equal. Qed.

  (* Note: unused lemma. *)
  Lemma sset_twice_common_prefix  S p q r v w :
    S.[p +++ q <- v].[p +++ r <- w] = S.[p <- S.[p].[[q <- v]].[[r <- w]] ].
  Proof. rewrite (sset_app_split S p q). rewrite sset_twice_prefix_left. reflexivity. Qed.

  Lemma sset_twice_disj_commute (S : state) p q v w :
    disj p q -> S.[p <- v].[q <- w] = S.[q <- w].[p <- v].
  Proof.
    intros Hdisj. unfold sset. apply state_eq_ext.
    - rewrite !get_map_alter. destruct Hdisj as [ | (<- & Hdisj)].
      + now apply alter_alter_ne.
      + rewrite !alter_alter_eq. apply alter_ext.
        intros ? _. now apply vset_twice_disj_commute.
    - rewrite !get_extra_alter. reflexivity.
  Qed.

  (** * Preservation of validity by vset/sset. *)
  (** Goal: if [q] is not a prefix of [p], then [p] is valid in S iff [p] is valid in [S.[q <- w]]
      In other words, setting [q] does not affect the validity of [p]. *)
  Lemma vset_prefix_right_valid v p q w : valid_vpath v p -> valid_vpath (v.[[p ++ q <- w]]) p.
  Proof.
    intro. destruct (valid_or_invalid (p ++ q) v) as [G | ].
    - apply vset_same_valid with (w := w) in G. apply valid_vpath_app in G. destruct G. assumption.
    - rewrite vset_invalid; assumption.
  Qed.

  Lemma vset_disj_valid_aux v i j p q w :
    i <> j -> valid_vpath v (i :: p) -> valid_vpath (v.[[j :: q <- w]]) (i :: p).
  Proof.
    intros ? valid_i_p. inversion valid_i_p. subst.
    econstructor; [ | eassumption]. rewrite children_vset_cons, nth_error_alter_list_neq; auto.
  Qed.

  Lemma vset_disj_valid v p q w :
    vdisj p q -> valid_vpath v p -> valid_vpath (v.[[q <- w]]) p.
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->) (? & ?)%valid_vpath_app.
    apply valid_vpath_app. split.
    - apply vset_prefix_right_valid. assumption.
    - rewrite vset_vget_prefix by assumption. apply vset_disj_valid_aux; assumption.
  Qed.

  Lemma vset_not_prefix_valid v p q w :
    ~vstrict_prefix q p -> valid_vpath v p -> valid_vpath (v.[[q <- w]]) p.
  Proof.
    intros ? G. destruct (comparable_vpaths p q) as [<- |(? & ? & <-) | | ].
    - eapply vset_same_valid; exact G.
    - rewrite vset_app_split. eapply vset_same_valid; exact G.
    - contradiction.
    - apply vset_disj_valid; assumption.
  Qed.

  Lemma vset_same_valid_rev v p w : valid_vpath (v.[[p <- w]]) p -> valid_vpath v p.
  Proof.
    intro. rewrite <-(vset_same v p). rewrite <-(vset_twice_equal p w _ v).
    apply vset_same_valid. assumption.
  Qed.

  Lemma vset_not_prefix_valid_rev v p q w :
    ~vstrict_prefix q p -> valid_vpath (v.[[q <- w]]) p -> valid_vpath v p.
  Proof.
    intros. erewrite <-(vset_same v q), <-vset_twice_equal.
    apply vset_not_prefix_valid; eassumption.
  Qed.

  Lemma sset_prefix_right_valid (S : state) p q v :
    prefix p q -> valid_spath S p -> valid_spath (S.[q <- v]) p.
  Proof.
    intros (r & <-) (w & get_S_p & ?). exists (w.[[snd p ++ r <- v]]). split.
    - autounfold. cbn. rewrite get_map_alter, lookup_alter_eq, get_S_p. reflexivity.
    - apply vset_prefix_right_valid. assumption.
  Qed.

  Lemma _sset_not_prefix_valid (S : state) p q v :
    ~strict_prefix q p -> valid_spath S p -> valid_spath (S.[q <- v]) p.
  Proof.
    intros ? valid_p.
    destruct (comparable_spaths p q) as [<- | (i & r & <-) | | Hdisj ].
    - apply sset_prefix_right_valid; [reflexivity | assumption].
    - apply sset_prefix_right_valid; [ | assumption]. eexists. reflexivity.
    - contradiction.
    - destruct valid_p as (w & ? & ?). unfold sset.
      destruct Hdisj as [ | (<- & ?)].
      + exists w. split; [ | assumption]. now rewrite get_map_alter, lookup_alter_ne.
      + exists (w.[[snd q <- v]]). split.
        * rewrite get_map_alter, lookup_alter_eq. simplify_option.
        * apply vset_disj_valid; assumption.
  Qed.

  Lemma sset_same (S : state) p : S.[p <- S.[p] ] = S.
  Proof.
    unfold sset, sget. apply state_eq_ext.
    - rewrite !get_map_alter. apply map_eq. intros a.
      destruct (decide (fst p = a)) as [<- | ].
      + simpl_map. destruct (get_at_accessor S (fst p)); [ | reflexivity].
        cbn. rewrite vset_same. reflexivity.
      + now rewrite lookup_alter_ne.
    - rewrite !get_extra_alter. reflexivity.
  Qed.

  Lemma sset_not_prefix_valid (S : state) p q v :
    ~strict_prefix q p -> valid_spath S p <-> valid_spath (S.[q <- v]) p.
  Proof.
    intros ?. split.
    - apply _sset_not_prefix_valid. assumption.
    - intro.
      assert (valid_spath (S.[q <- v].[q <- S.[q] ]) p) by now apply _sset_not_prefix_valid.
      rewrite sset_twice_equal, sset_same in * |-. assumption.
  Qed.

  Corollary sset_prefix_valid S p q v :
    valid_spath S p -> valid_vpath v q -> valid_spath (S.[p <- v]) (p +++ q).
  Proof.
    intros. apply valid_spath_app. split.
    - apply sset_not_prefix_valid; [ apply strict_prefix_irrefl | assumption].
    - rewrite sset_sget_equal; assumption.
  Qed.

  (** * Management of anonymous bindings. *)
  Definition fresh_anon S a := get_at_accessor S (anon_accessor a) = None.
  Hint Unfold fresh_anon : core.

  Lemma _fresh_anon_sset S p v a : fresh_anon S a -> fresh_anon (S.[p <- v]) a.
  Proof. autounfold. intros ?. rewrite get_map_alter. now apply lookup_alter_None. Qed.

  Corollary fresh_anon_sset S p v a : fresh_anon S a <-> fresh_anon (S.[p <- v]) a.
  Proof.
    split.
    - apply _fresh_anon_sset.
    - intros ?. rewrite<- (sset_same S p). erewrite <-sset_twice_equal.
      apply _fresh_anon_sset. eassumption.
  Qed.

  (* Note: by injectivity, the hypothesis anon_accessor a <> anon_accessor b could be
   * replaces by a <> b. *)
  Lemma fresh_anon_add_anon S a b v :
    fresh_anon (S,, a |-> v) b <-> (fresh_anon S b /\ anon_accessor a <> anon_accessor b).
  Proof.
    unfold fresh_anon. rewrite get_map_add_anon. split.
    - intros G. assert (anon_accessor a <> anon_accessor b).
      { intros Heq. rewrite Heq in G. rewrite lookup_insert_eq in G. discriminate. }
      rewrite lookup_insert_ne in G by assumption. auto.
    - intros (? & ?). rewrite lookup_insert_ne; assumption.
  Qed.

  Lemma fresh_anon_diff S a b v
    (get_a : get_at_accessor S (anon_accessor a) = Some v) (fresh_b : fresh_anon S b) :
    a <> b.
  Proof. congruence. Qed.

  Lemma get_at_accessor_add_anon (S : state) a x v :
    x <> anon_accessor a -> get_at_accessor (S,, a |-> v) x = get_at_accessor S x.
  Proof. intros ?. rewrite get_map_add_anon, lookup_insert_ne; auto. Qed.

  Lemma anon_accessor_diff a b : a <> b -> anon_accessor a <> anon_accessor b.
  Proof. intros ? G%(f_equal accessor_anon). rewrite !anon_accessor_inj in G. congruence. Qed.

  Lemma add_anon_commute (S : state) (a b : anon) (v w : V) :
    a <> b -> S,, a |-> v,, b |-> w = S,, b |-> w,, a |-> v.
  Proof.
    intros ?. apply state_eq_ext.
    - rewrite !get_map_add_anon. apply insert_insert_ne, anon_accessor_diff. congruence.
    - rewrite !get_extra_add_anon. reflexivity.
  Qed.

  Lemma sget_add_anon (S : state) a v p :
    fst p <> anon_accessor a -> (S,, a |-> v).[p] = S.[p].
  Proof. intros ?. autounfold. rewrite get_at_accessor_add_anon; auto. Qed.

  Lemma sset_add_anon (S : state) a v w p :
    fst p <> anon_accessor a -> (S,, a |-> w).[p <- v] = S.[p <- v],, a |-> w.
  Proof.
    autounfold. intros ?. apply state_eq_ext.
    - rewrite get_map_alter, !get_map_add_anon, get_map_alter.
      apply alter_insert_ne. assumption.
    - rewrite get_extra_add_anon, !get_extra_alter. apply get_extra_add_anon.
  Qed.

  Lemma sset_anon (S : state) a v w p :
    fst p = anon_accessor a -> (S,, a |-> v).[p <- w] = S,, a |-> v.[[snd p <- w]].
  Proof.
    unfold sset. intros ->. apply state_eq_ext.
    - rewrite get_map_alter, !get_map_add_anon, alter_insert_eq. reflexivity.
    - rewrite get_extra_alter, !get_extra_add_anon. reflexivity.
  Qed.

  Lemma sget_anon (S : state) a v p : fst p = anon_accessor a -> (S,, a |-> v).[p] = v.[[snd p]].
  Proof. unfold sget. intros ->. rewrite get_map_add_anon, lookup_insert_eq. reflexivity. Qed.

  Lemma disj_spath_add_anon S a p q :
    fresh_anon S a -> valid_spath S p -> disj p (anon_accessor a, q).
  Proof. unfold fresh_anon. intros ? (? & ? & _). left. cbn. congruence. Qed.

  Lemma disj_spath_add_anon' S a p q :
    fresh_anon S a -> valid_spath S p -> disj (anon_accessor a, q) p.
  Proof. symmetry. eapply disj_spath_add_anon; eassumption. Qed.

  Lemma valid_spath_add_anon S a p v :
    valid_spath S p -> fresh_anon S a -> valid_spath (S,, a |-> v) p.
  Proof.
    unfold fresh_anon. intros (w & ? & ?) ?. exists w. split; [ | assumption].
    rewrite get_map_add_anon, lookup_insert_ne by congruence. assumption.
  Qed.

  Lemma valid_spath_anon S a v p : valid_vpath v p -> valid_spath (S,, a |-> v) (anon_accessor a, p).
  Proof.
    intro. exists v. split; [ | assumption]. rewrite get_map_add_anon, lookup_insert_eq.
    reflexivity.
  Qed.

  Lemma valid_spath_add_anon_cases S a v p :
    valid_spath (S,, a |-> v) p ->
      fst p <> anon_accessor a /\ valid_spath S p \/
      fst p = anon_accessor a /\ valid_vpath v (snd p).
  Proof.
    unfold valid_spath. intros valid_p.
    destruct (decide (fst p = anon_accessor a)) as [Heq_p_a | ].
    - right. split; [assumption | ]. rewrite Heq_p_a in valid_p.
      rewrite get_map_add_anon, lookup_insert_eq in valid_p.
      destruct valid_p as (? & Heq_v & ?). inversion Heq_v. assumption.
    - left. split; [assumption | ].
      rewrite get_map_add_anon, lookup_insert_ne in valid_p by auto. exact valid_p.
  Qed.

  Lemma valid_spath_diff_fresh_anon S a p :
    fresh_anon S a -> valid_spath S p -> fst p <> anon_accessor a.
  Proof. intros ? (? & ? & _). congruence. Qed.

  Lemma valid_spath_diff_fresh_anon' S a b p :
    fresh_anon S a -> valid_spath S (anon_accessor b, p) -> b <> a.
  Proof. intros ? (? & G & _). cbn in G. congruence. Qed.

  (* TODO: move? *)
  (** Other lemmas on validity. *)
  Lemma valid_vpath_zeroary v p :
    arity (get_node v) = 0 -> valid_vpath v p -> p = [].
  Proof.
    intros G. inversion 1; [reflexivity | ]. subst.
    rewrite <-length_children_is_arity, length_zero_iff_nil in G.
    rewrite G, nth_error_nil in * |-. discriminate.
  Qed.

  Lemma get_zeroary_not_strict_prefix S p q :
    arity (get_node (S .[ p])) = 0 -> valid_spath S q -> ~strict_prefix p q.
  Proof.
    intros arity_0 valid_q (i & r & <-). apply valid_spath_app in valid_q.
    destruct valid_q as (_ & valid_i_r). inversion valid_i_r.
    rewrite<- length_children_is_arity in arity_0. apply length_zero_iff_nil in arity_0.
    rewrite arity_0, nth_error_nil in * |-. discriminate.
  Qed.

  (* A variant that is more useful for LLBC+ *)
  Corollary get_zeroary_not_strict_prefix' S p q v :
    valid_spath (S.[p <- v]) q -> arity (get_node v) = 0 -> ~strict_prefix p q.
  Proof.
    destruct (decidable_valid_spath S p).
    - intros valid_q ?. eapply get_zeroary_not_strict_prefix; [ | exact valid_q].
      rewrite sset_sget_equal; assumption.
    - rewrite sset_invalid by assumption. intros valid_q _ (? & <-)%strict_prefix_is_prefix.
      apply valid_spath_app in valid_q. destruct valid_q. auto.
  Qed.

  Lemma sset_sget_diff S p q v c :
    get_node (S.[p <- v].[q]) = c -> get_node v <> c -> c <> get_node bot -> p <> q.
  Proof.
    intros G ? ? <-. destruct (decidable_valid_spath S p).
    - rewrite sset_sget_equal in G by assumption. auto.
    - rewrite sset_invalid, sget_invalid in G by assumption. auto.
  Qed.

  (** * Definitions and lemmas around [not_value_contains] and [not_state_contains] *)
  (** The goal is to set up the definitions for judgements like "loan \notin [v]" or
     "[l] is fresh". *)
  Definition not_value_contains (P : nodes -> Prop) (v : V) :=
    forall p, valid_vpath v p -> ~P (get_node (v.[[p]])).

  Definition not_state_contains (P : nodes -> Prop) (S : state) :=
    forall p, valid_spath S p -> ~P (get_node (S.[p])).

  Definition not_contains_outer (is_mut_borrow P : nodes -> Prop) v :=
    forall p, valid_vpath v p -> P (get_node (v.[[p]]))
    -> exists q, vstrict_prefix q p /\ is_mut_borrow (get_node (v.[[q]])).

  Lemma not_value_contains_not_prefix P (S : state) p q
    (Hnot_contains : not_value_contains P (S.[p])) (HP : P (get_node (S.[q])))
    (Hvalid : valid_spath S q) :
    ~prefix p q.
  Proof.
    intros (r & <-). apply valid_spath_app in Hvalid. apply Hnot_contains with (p := r); [easy | ].
    rewrite<- sget_app. assumption.
  Qed.

  (* A variant of the previous lemma that is more useful for LLBC+. *)
  Lemma not_value_contains_not_prefix' P S p q v :
    not_value_contains P (S.[p <- v].[q]) -> valid_spath S p -> P (get_node v) ->
    ~prefix q p.
  Proof.
    intros. eapply not_value_contains_not_prefix.
    - eassumption.
    - rewrite sset_sget_equal; assumption.
    - apply sset_prefix_right_valid; [reflexivity | assumption].
  Qed.

  Lemma not_value_contains_vset P v w p : not_value_contains P v -> not_value_contains P w ->
    not_value_contains P (v.[[p <- w]]).
  Proof.
    intros not_contains G q valid_q. destruct (decidable_vprefix p q) as [(? & <-) | ].
    - apply valid_vpath_app in valid_q. destruct valid_q as (?%vset_same_valid_rev & validity_w).
      rewrite vset_vget_equal in validity_w by assumption.
      rewrite vset_vget_prefix_right by assumption. apply G. assumption.
    - rewrite get_node_vset_vget_not_prefix by assumption. apply not_contains.
      eapply vset_not_prefix_valid_rev; [ | eassumption].
      intros ?%vstrict_prefix_is_vprefix. auto.
  Qed.

  Lemma not_value_contains_vget P v p :
    not_value_contains P v -> valid_vpath v p -> not_value_contains P (v.[[p]]).
  Proof. intros G ? q valid_q. rewrite <-vget_app. apply G, valid_vpath_app. auto. Qed.

  (* TODO: name *)
  Lemma not_value_contains_vset_rev P v w p :
    not_value_contains P (v.[[p]]) -> not_value_contains P (v.[[p <- w]]) ->
    not_value_contains P v.
  Proof.
    intros ? ?. erewrite <-vset_same, <-vset_twice_equal.
    apply not_value_contains_vset; eassumption.
  Qed.

  (** * Lemmas about weighted sums on states. *)
  (** Other results on values. *)
  (* TODO: move. *)
  Lemma weight_non_zero v :
    vweight_ v > 0 -> exists p, valid_vpath v p /\ weight (get_node (v.[[p]])) > 0.
  Proof.
    remember (vsize v) as n eqn:Heqn. revert v Heqn.
    induction n as [n IH] using lt_wf_ind. intros v -> weight_non_zero.
    rewrite vweight_prop in weight_non_zero.
    destruct (weight (get_node v)) eqn:?.
    - rewrite Nat.add_0_r in weight_non_zero. apply sum_non_zero in weight_non_zero.
      destruct weight_non_zero as (i & ? & ith_child). rewrite nth_error_map in ith_child.
      destruct (nth_error (children v) i) as [w | ] eqn:G; [ | discriminate].
      injection ith_child as ?.
      edestruct IH as (p & ? & ?).
      + eapply vsize_decreasing. eassumption.
      + reflexivity.
      + lia.
      + exists (i :: p). split.
        * econstructor; eassumption.
        * cbn. rewrite G. assumption.
    - exists []. cbn. split; [constructor | lia].
  Qed.

  Lemma not_value_contains_weight P v (P_weight_zero : forall c, weight c > 0 -> P c) :
    not_value_contains P v -> vweight_ v = 0.
  Proof.
    intros not_contains. destruct (vweight_ v) eqn:?; [reflexivity | ].
    assert (vweight_ v > 0) as (p & valid_p & ?)%weight_non_zero by lia.
    exfalso. eapply not_contains; eauto.
  Qed.

  Lemma weight_zero_not_value_contains (P : nodes -> Prop) v
    (P_non_zero : forall c, P c -> weight c > 0) :
    vweight_ v = 0 -> not_value_contains P v.
  Proof.
    intros ? p valid_p P_p. specialize (P_non_zero _ P_p).
    pose proof (weight_vget_le _ _ valid_p) as G. rewrite (vweight_prop _ (v.[[p]])) in G. lia.
  Qed.

  (* There is at most one path that satisfies a predicate P. *)
  Definition value_at_most_one P v :=
    forall p q, valid_vpath v p -> valid_vpath v q ->
                P (get_node (v.[[p]])) -> P (get_node (v.[[q]])) ->
                p = q.

  Definition vpath_unique  P v p :=
    valid_vpath v p /\ P (get_node (v.[[p]])) /\
    forall q, valid_vpath v q -> P (get_node (v.[[q]])) -> p = q.

  Lemma not_value_contains_implies_vpath_at_most_one P v :
    not_value_contains P v -> value_at_most_one P v.
  Proof. intros G q ? ? _ ?. exfalso. eapply G; eassumption. Qed.

  Lemma vpath_unique_implies_vpath_at_most_one P v p :
    vpath_unique P v p -> value_at_most_one P v.
  Proof. intros G q r ? ? ? ?. transitivity p; [symmetry | ]; now apply G. Qed.

  Lemma value_weight_one v :
    vweight_ v = 1 -> exists p, vpath_unique (fun c => weight c > 0) v p.
  Proof.
    intro weight_1.
    assert (vweight_ v > 0) as (p & valid_p & P_p)%weight_non_zero by lia.
    exists p. repeat split; [assumption.. | ].
    induction valid_p as [ | v i p w ith_child valid_p IH].
    - rewrite vweight_prop in weight_1.
      intros q valid_q. destruct valid_q as [ | ? ? ? ? ith_child valid_rec]; [reflexivity | ].
      cbn in *. rewrite ith_child.
      apply (map_nth_error vweight_) in ith_child. apply sum_ge_element in ith_child.
      pose proof (weight_vget_le _ _ valid_rec) as G.
      rewrite vweight_prop in G. lia.
    - rewrite vweight_prop in weight_1.
      cbn in P_p. rewrite ith_child in P_p.
      pose proof (weight_vget_le _ _ valid_p) as weight_w_p.
      rewrite vweight_prop in weight_w_p.
      pose proof (map_nth_error vweight_ _ _ ith_child) as weight_children.
      apply sum_ge_element in weight_children.
      intros ? valid_q. destruct valid_q as [ | v j q w' G valid_q].
      + cbn. lia.
      + intros P_q. cbn in P_q. rewrite G in P_q. replace j with i in *.
        * replace w' with w in * by congruence.
          f_equal. apply IH; [ | assumption..]. lia.
        * pose proof (weight_vget_le _ _ valid_q) as weight_w'_q.
          rewrite vweight_prop in weight_w'_q.
          apply (map_nth_error vweight_) in ith_child, G.
          eapply sum_le_one; [ | exact ith_child | exact G | | ]; lia.
  Qed.

  Corollary value_weight_at_most_one v :
    vweight_ v <= 1 -> value_at_most_one (fun c => weight c > 0) v.
  Proof.
    intros [ | (p & ?%vpath_unique_implies_vpath_at_most_one)%value_weight_one]%Nat.le_1_r.
    - now apply not_value_contains_implies_vpath_at_most_one, weight_zero_not_value_contains.
    - assumption.
  Qed.

  Lemma weight_one_at_most_one_vpath v
    (weight_le_1 : forall c, weight c <= 1) :
    value_at_most_one (fun c => weight c > 0) v -> vweight_ v <= 1.
  Proof.
    remember (vsize v) as n eqn:Heqn. revert v Heqn.
    induction n as [n IH] using lt_wf_ind. intros v -> at_most_one.
    rewrite vweight_prop.
    pose proof (weight_le_1 (get_node v)) as [-> | weight_node]%Nat.le_1_r.
    - rewrite Nat.add_0_r. apply sum_unique_one.
      + intros i x weight_ith. rewrite nth_error_map in weight_ith.
        destruct (nth_error (children v) i) as [w | ] eqn:Hw; [ | discriminate].
        injection weight_ith as <-.
        eapply IH.
        * eapply vsize_decreasing. exact Hw.
        * reflexivity.
        * intros p q valid_p valid_q Hp Hq.
          injection (at_most_one (i :: p) (i :: q)).
          -- auto.
          -- econstructor; eassumption.
          -- econstructor; eassumption.
          -- cbn. rewrite Hw. assumption.
          -- cbn. rewrite Hw. assumption.
      + intros i j. rewrite !nth_error_map. intros Hi Hj.
        destruct (nth_error (children v) i) as [wi | ] eqn:Hwi; [ | discriminate].
        destruct (nth_error (children v) j) as [wj | ] eqn:Hwj; [ | discriminate].
        injection Hi as ?. injection Hj as ?.
        destruct (weight_non_zero wi) as (p & ? & ?); [lia | ].
        destruct (weight_non_zero wj) as (q & ? & ?); [lia | ].
        assert (i :: p = j :: q) as eq_path; [ | injection eq_path; auto].
        apply at_most_one.
        * econstructor; eassumption.
        * econstructor; eassumption.
        * cbn. rewrite Hwi. assumption.
        * cbn. rewrite Hwj. assumption.
    - assert (sum (map vweight_ (children v)) = 0); [ | lia].
      apply sum_zero. intros i Hi.
      rewrite nth_error_map.
      rewrite length_map in Hi. apply nth_error_Some' in Hi.
      destruct Hi as (w & ith_child). rewrite ith_child. cbn. f_equal.
      replace w with (v.[[ [i] ]]) by (cbn; rewrite ith_child; reflexivity).
      eapply not_value_contains_weight with (P := fun c => weight c > 0); [auto | ].
      intros p q. rewrite<- vget_app.
      intros ?. specialize (at_most_one ([i] ++ p) []).
      discriminate at_most_one.
      + apply valid_vpath_app. split; repeat (econstructor || eassumption).
      + constructor.
      + assumption.
      + cbn. lia.
  Qed.

  Lemma not_state_contains_sset P S v p
    (not_in_S : not_state_contains P S)
    (not_in_v : not_value_contains P v) :
    not_state_contains P (S.[p <- v]).
  Proof.
    intros q valid_q.
    destruct (decidable_prefix p q) as [(r & <-) | ].
    - apply valid_spath_app in valid_q.
      destruct valid_q as (?%sset_not_prefix_valid & valid_r); [ |  apply strict_prefix_irrefl].
      rewrite sset_sget_equal in valid_r by assumption.
      rewrite sset_sget_prefix_right by assumption. apply not_in_v. assumption.
    - rewrite get_node_sset_sget_not_prefix by assumption.
      apply not_in_S. eapply sset_not_prefix_valid; [ | exact valid_q].
      apply not_prefix_implies_not_strict_prefix. assumption.
  Qed.

  Lemma not_state_contains_sset_rev P S v p
    (not_in_S : not_state_contains P (S.[p <- v]))
    (not_in_v : not_value_contains P (S.[p])) :
    not_state_contains P S.
  Proof.
    erewrite <-(sset_same S p), <-sset_twice_equal. apply not_state_contains_sset; eassumption.
  Qed.

  Lemma not_state_contains_add_anon P S v a
    (not_in_S : not_state_contains P S)
    (not_in_v : not_value_contains P v) :
    not_state_contains P (S,, a |-> v).
  Proof.
    intros q [(? & ?) | (? & ?)]%valid_spath_add_anon_cases.
    - rewrite sget_add_anon by assumption. now apply not_in_S.
    - rewrite sget_anon by assumption. now apply not_in_v.
  Qed.

  Lemma not_state_contains_add_anon_rev P S v a :
    not_state_contains P (S,, a |-> v) -> fresh_anon S a ->
    not_state_contains P S /\ not_value_contains P v.
  Proof.
    intros G fresh_a. split.
    - intros q valid_q. specialize (G q). rewrite sget_add_anon in G.
      + apply G. apply valid_spath_add_anon; assumption.
      + eapply valid_spath_diff_fresh_anon; eassumption.
    - intros q valid_q. specialize (G (anon_accessor a, q)).
      rewrite sget_anon in G by reflexivity. apply G.
      apply valid_spath_anon. assumption.
  Qed.

  Lemma not_value_contains_sset P S v p q
    (not_in_Sp : not_value_contains P (S.[p]))
    (not_in_v : not_value_contains P v)
    (valid_p : valid_spath (S.[q <- v]) p) :
    not_value_contains P (S.[q <- v].[p]).
  Proof.
    intros r valid_r. rewrite<- sget_app.
    assert (valid_pr : valid_spath (S.[q <- v]) (p +++ r)).
    { apply valid_spath_app. split; assumption. }
    destruct (decidable_prefix q (p +++ r)) as [(? & eq) | ].
    - rewrite <-eq in *. rewrite valid_spath_app in valid_pr.
      destruct valid_pr as (valid_q & valid_v_r).
      apply sset_not_prefix_valid in valid_q; [ | apply strict_prefix_irrefl].
      rewrite sset_sget_equal in valid_v_r by assumption.
      rewrite sset_sget_prefix_right by assumption. apply not_in_v. exact valid_v_r.
    - rewrite get_node_sset_sget_not_prefix by assumption. rewrite sget_app. apply not_in_Sp.
      apply sset_not_prefix_valid in valid_pr; [ | auto with spath].
      apply valid_spath_app in valid_pr as (_ & ?). assumption.
      apply not_prefix_implies_not_strict_prefix. assumption.
  Qed.

  Lemma not_value_contains_sset_rev P S v p q
    (not_in_Sp : not_value_contains P (S.[q <- v].[p]))
    (not_in_v : not_value_contains P (S.[q]))
    (valid_p : valid_spath S p) :
    not_value_contains P (S.[p]).
  Proof.
    rewrite <-(sset_same S q),  <-(sset_twice_equal S q v) in valid_p |- *.
    apply not_value_contains_sset; assumption.
  Qed.

  Lemma not_value_contains_sset_disj P (S : state) v p q
    (Hdisj : disj q p)
    (not_in_Sp : not_value_contains P (S.[p])) :
    not_value_contains P (S.[q <- v].[p]).
  Proof.
    intros r valid_r. rewrite<- sget_app.
    rewrite sset_sget_disj by now apply disj_if_left_disj_prefix.
    rewrite sget_app. apply not_in_Sp.
    rewrite sset_sget_disj in valid_r; assumption.
  Qed.

  Lemma not_value_contains_zeroary P v :
    arity (get_node v) = 0 -> ~P (get_node v) -> not_value_contains P v.
  Proof.
    rewrite <-length_children_is_arity.
    intros no_child%length_zero_iff_nil ? p valid_p. destruct valid_p; [assumption | ].
    rewrite no_child, nth_error_nil in * |-. discriminate.
  Qed.

  Lemma not_value_contains_unary P v w :
    children v = [w] -> ~P (get_node v) -> not_value_contains P w -> not_value_contains P v.
  Proof.
    intros one_child ? ? p valid_p. destruct valid_p; [assumption | ].
    rewrite one_child, nth_error_cons in * |-.
    destruct i; [ | rewrite nth_error_nil in * |-; discriminate].
    rewrite vget_cons, one_child. simplify_option.
  Qed.

  Lemma not_state_contains_implies_not_value_contains_sget P S p :
    not_state_contains P S -> valid_spath S p -> not_value_contains P (S.[p]).
  Proof.
    intros not_contains valid_p q valid_q G. rewrite<- sget_app in G.
    eapply not_contains; [ | exact G]. apply valid_spath_app. split; assumption.
  Qed.

  Lemma not_contains_implies_not_contains_outer v P is_mut_borrow :
    not_value_contains P v -> not_contains_outer is_mut_borrow P v.
  Proof. intros Hnot_contains ? ? ?. exfalso. eapply Hnot_contains; eassumption. Qed.

  Lemma not_contains_outer_vset is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v -> not_contains_outer is_mut_borrow P w
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv Hw. destruct (valid_or_invalid p v).
    - intros q valid_q Hq. destruct (decidable_vprefix p q) as [(r & <-) | not_prefix].
      + rewrite vset_vget_prefix_right in Hq by assumption.
        apply valid_vpath_app in valid_q. destruct valid_q as (_ & valid_q).
        rewrite vset_vget_equal in valid_q by assumption.
        apply Hw in Hq; [ | assumption]. destruct Hq as (q & (? & ? & <-) & Hq).
        exists (p ++ q). split.
        * eexists _, _. rewrite !app_assoc. reflexivity.
        * rewrite vset_vget_prefix_right by assumption. assumption.
      + destruct (Hv q) as (r & ? & ?).
        * eapply vset_not_prefix_valid_rev; [ | exact valid_q].
          eapply not_vprefix_implies_not_vstrict_prefix; eassumption.
        * rewrite get_node_vset_vget_not_prefix in Hq by assumption. exact Hq.
        * exists r. split; [assumption | ].
          rewrite get_node_vset_vget_not_prefix; [assumption | ].
          intro. apply not_prefix.
          transitivity r; [ | apply vstrict_prefix_is_vprefix]; assumption.
    - rewrite vset_invalid by assumption. assumption.
  Qed.

  Lemma not_contains_outer_sset_no_contains is_mut_borrow P S v p q :
    not_contains_outer is_mut_borrow P (S.[q <- v].[p]) ->
    not_contains_outer is_mut_borrow P (S.[q]) ->
    ~strict_prefix q p ->
    not_contains_outer is_mut_borrow P (S.[p]).
  Proof.
    intros G ? ?. destruct (decidable_valid_spath S p).
    - destruct (decidable_prefix p q) as [(r & <-) | ].
      + rewrite sset_sget_prefix in G by assumption.
        erewrite <-(vset_same _ r), <-vset_twice_equal, <-sget_app.
        apply not_contains_outer_vset; eassumption.
      + assert (disj p q)
          by auto using prove_disj, neq_implies_not_prefix, not_prefix_implies_not_strict_prefix.
        rewrite sset_sget_disj in G by (symmetry; assumption).
        assumption.
    - rewrite sget_invalid by assumption. rewrite sget_invalid in G; [exact G | ].
      rewrite <-sset_not_prefix_valid; assumption.
  Qed.

  Lemma not_contains_outer_vset_in_borrow is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v
    -> (exists q, vstrict_prefix q p /\ is_mut_borrow (get_node (v.[[q]])))
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv (q & strict_prefix & ?). destruct (valid_or_invalid p v).
    - intros r ? Hr. destruct (decidable_vprefix p r) as [(r' & <-) | not_prefix].
      + exists q.
        split.
        * destruct strict_prefix as (i & ? & <-). eexists i, _. rewrite<- app_assoc. reflexivity.
        * rewrite get_node_vset_vget_not_prefix
            by now apply not_vprefix_left_vstrict_prefix_right.
          assumption.
      + destruct (Hv r) as (q' & ? & ?).
        * eapply vset_not_prefix_valid_rev; [ | eassumption].
          eapply not_vprefix_implies_not_vstrict_prefix; eassumption.
        * rewrite get_node_vset_vget_not_prefix in Hr; assumption.
        * exists q'. split; [assumption | ]. rewrite get_node_vset_vget_not_prefix.
          assumption. intro. apply not_prefix.
          transitivity q'; [ | apply vstrict_prefix_is_vprefix]; assumption.
    - rewrite vset_invalid by assumption. assumption.
  Qed.

  (* If the value S.[p <- v].[q] does not contains outer loans, and v is a loan, then the value
   * S.[q] does not contain outer loans. Indeed, if q is a prefix of p, then this means that the
   * path p has a mutable borrow ancestor (because the value v stored there is a loan). We don't
   * even have to check that the value in S.[p] does not contain outer loans. *)
  Lemma not_contains_outer_sset_contains is_mut_borrow P S p q v :
    not_contains_outer is_mut_borrow P (S.[p <- v].[q]) -> P (get_node v) ->
    ~strict_prefix p q -> not_contains_outer is_mut_borrow P (S.[q]).
  Proof.
    destruct (decidable_valid_spath S p) as [valid_p | ].
    - destruct (decidable_prefix q p) as [(r & <-) | ].
      + intros no_outer Pv _. rewrite valid_spath_app in valid_p. destruct valid_p.
        rewrite sset_sget_prefix in no_outer by assumption.
        intros p' valid_p' Pp'. destruct (decidable_vprefix r p') as [Hprefix | Hnot_prefix].
        * destruct (no_outer r) as (q' & Hstrict_prefix & Pq').
          -- apply vset_same_valid. assumption.
          -- rewrite vset_vget_equal; assumption.
          -- exists q'. rewrite get_node_vset_vget_strict_prefix in Pq' by assumption.
             split; [ | exact Pq'].
             destruct Hprefix as (? & <-). destruct Hstrict_prefix as (? & ? & <-).
             eexists _, _. rewrite <-!app_assoc. reflexivity.
        * destruct (no_outer p') as (q' & Hstrict_prefix & Pq').
          -- apply vset_not_prefix_valid; [ | assumption].
             apply not_vprefix_implies_not_vstrict_prefix. assumption.
          -- rewrite get_node_vset_vget_not_prefix; assumption.
          -- exists q'. split; [assumption | ].
             rewrite get_node_vset_vget_not_prefix in Pq'; [assumption | ].
             intros (? & <-). apply Hnot_prefix. destruct Hstrict_prefix as (? & ? & <-).
             rewrite <-!app_assoc. eexists. reflexivity.
      + intros no_outer _ ?. rewrite sset_sget_disj in no_outer.
        * exact no_outer.
        * symmetry. apply prove_disj.
          all: auto using neq_implies_not_prefix, not_prefix_implies_not_strict_prefix.
    - rewrite sset_invalid; auto.
  Qed.

  (** ** Weighted sums on states. *)
  Definition sweight (S : state) := map_sum vweight_ (get_map S).
  Hint Unfold sweight : core.

  Lemma sweight_sset S p v :
    valid_spath S p ->
    Z.of_nat (sweight (S.[p <- v])) = (sweight S - vweight_ (S.[p]) + vweight_ v)%Z.
  Proof.
    intros (w & get_S_p & ?). autounfold.
    rewrite get_S_p.
    rewrite get_map_alter. apply insert_delete_id in get_S_p. rewrite <-get_S_p.
    rewrite alter_insert_eq. rewrite !map_sum_insert by apply lookup_delete_eq.
    rewrite Nat2Z.inj_add, vweight_vset by assumption. lia.
  Qed.

  Lemma weight_sget_le S p : valid_spath S p -> vweight_ (S.[p]) <= sweight S.
  Proof.
    intros (w & get_S_p & ?%weight_vget_le). autounfold. rewrite get_S_p.
    apply insert_delete_id in get_S_p. rewrite <-get_S_p, map_sum_insert by apply lookup_delete_eq. lia.
  Qed.

  Corollary weight_sget_node_le S p : valid_spath S p -> weight (get_node (S.[p])) <= sweight S.
  Proof. intros G%weight_sget_le. rewrite vweight_prop in G. lia. Qed.

  Lemma sweight_add_anon S a v : fresh_anon S a -> sweight (S,, a |-> v) = sweight S + vweight_ v.
  Proof. autounfold. intros ?. rewrite get_map_add_anon, map_sum_insert by assumption. lia. Qed.

  Lemma sweight_non_zero S : sweight S > 0 ->
    exists p, valid_spath S p /\ weight (get_node (S.[p])) > 0.
  Proof.
    intros (k & x & get_S_k & (p & ? & ?)%weight_non_zero)%map_sum_non_zero.
    exists (k, p). autounfold. cbn. rewrite !get_S_k. firstorder.
  Qed.

  Lemma not_state_contains_implies_weight_zero P S :
    (forall c, weight c > 0 -> P c) -> not_state_contains P S -> sweight S = 0.
  Proof.
    intros ? not_contains. assert (~(sweight S > 0)); [ | lia].
    intros (? & ? & ?)%sweight_non_zero. eapply not_contains; eauto.
  Qed.

  (** It is always possible to choose an anonymous variable that is not in the state. *)
  (* TODO: move *)
  Definition maybe_add_anon k (anons_set : gset anon) :=
    match accessor_anon k with
    | Some a => union anons_set (singleton a)
    | None => anons_set
    end.

  Definition anons_set S := map_fold (fun k _ => maybe_add_anon k) empty (get_map S).

  Lemma not_elem_of_anons_set_is_fresh S a : ~elem_of a (anons_set S) -> fresh_anon S a.
  Proof.
    intros G. unfold fresh_anon.
    destruct (get_at_accessor S (anon_accessor a)) eqn:EQN; [ | reflexivity].
    exfalso. apply G. unfold anons_set.
    apply insert_delete_id in EQN. rewrite <-EQN, map_fold_insert_L.
    - unfold maybe_add_anon. rewrite anon_accessor_inj. set_solver.
    - unfold maybe_add_anon. intros. destruct accessor_anon; destruct accessor_anon; set_solver.
    - simpl_map. reflexivity.
  Qed.

  Lemma exists_fresh_anon S : exists a, fresh_anon S a.
  Proof.
    destruct (exist_fresh (anons_set S)) as (? & ?%not_elem_of_anons_set_is_fresh). firstorder.
  Qed.

  Lemma exists_fresh_anon2 S0 S1 : exists a, fresh_anon S0 a /\ fresh_anon S1 a.
  Proof.
    destruct (exist_fresh (union (anons_set S0) (anons_set S1))) as (a & ?).
    exists a. split; apply not_elem_of_anons_set_is_fresh; set_solver.
  Qed.

  Lemma states_add_anon_eq Sl Sr a vl vr :
    fresh_anon Sl a -> fresh_anon Sr a ->
    (Sl,, a |-> vl) = (Sr,, a |-> vr) -> Sl = Sr /\ vl = vr.
  Proof.
    intros ? ? eq_add_anon. split.
    - apply state_eq_ext.
      + apply (f_equal get_map) in eq_add_anon. rewrite !get_map_add_anon in eq_add_anon.
        apply (f_equal (delete (anon_accessor a))) in eq_add_anon.
        rewrite !delete_insert_id in eq_add_anon; assumption.
      + apply (f_equal get_extra) in eq_add_anon. rewrite !get_extra_add_anon in eq_add_anon.
        exact eq_add_anon.
    - apply (f_equal (fun S => S.[(anon_accessor a, [])])) in eq_add_anon.
      rewrite !sget_anon in eq_add_anon by reflexivity. exact eq_add_anon.
  Qed.

  (** [no_ancestor P S p] : none of nodes preceding [p] in the tree satisfy the predicate [P].
     This is used to define properties like "[p] is not in a mutable borrow" or "[p] is not in a shared
     loan". *)
  Definition no_ancestor (P : nodes -> Prop) S p :=
    forall q, P (get_node (S.[q])) -> ~strict_prefix q p.

  Definition no_ancestor_val (P : nodes -> Prop) v p :=
    forall q, P (get_node (v.[[q]])) -> ~vstrict_prefix q p.

  Lemma no_ancestor_sset P S p q v : ~strict_prefix q p ->
    no_ancestor P (S.[q <- v]) p <-> no_ancestor P S p.
  Proof.
    intros not_prefix. split.
    - intros G r K ?. eapply G; [ | eassumption].
      rewrite get_node_sset_sget_not_prefix; [assumption | ].
      intros ?. apply not_prefix.
      eapply prefix_and_strict_prefix_implies_strict_prefix; eassumption.
    - intros G r K ?.
      rewrite get_node_sset_sget_not_prefix in K; [eapply G; eassumption | ].
      intros ?. eapply not_prefix, prefix_and_strict_prefix_implies_strict_prefix; eassumption.
  Qed.

  Lemma no_ancestor_add_anon P S p a v :
    fst p <> anon_accessor a -> no_ancestor P (S,, a |-> v) p <-> no_ancestor P S p.
  Proof.
    intros ?. split.
    - intros G ? ? Hprefix. eapply G; [ | eassumption]. rewrite sget_add_anon; [assumption | ].
      destruct Hprefix as (? & ? & <-). assumption.
    - intros G ? K Hprefix. rewrite sget_add_anon in K.
      + eapply G; eassumption.
      + destruct Hprefix  as (? & ? & <-). assumption.
  Qed.

  Lemma no_ancestor_anon P S p a v (G : fst p = anon_accessor a) :
    no_ancestor P (S,, a |-> v) p <-> no_ancestor_val P v (snd p).
  Proof.
    destruct p; cbn in *. subst. split.
    - intros G q ? (i & r & <-). eapply G with (q := (anon_accessor a, q)).
      + rewrite sget_anon by reflexivity. assumption.
      + exists i, r. reflexivity.
    - intros G ? K (i & r & L). rewrite sget_anon in K.
      + eapply G; [exact K | ]. exists i, r. apply (f_equal snd) in L. exact L.
      + apply (f_equal fst) in L. exact L.
  Qed.

  Lemma no_ancestor_app P S p q (valid_p : valid_spath S p) :
    no_ancestor P S p -> no_ancestor_val P (S.[p]) q -> no_ancestor P S (p +++ q).
  Proof.
    intros no_ancestor_p no_ancestor_q sp G (i & r & K).
    destruct (decidable_prefix p sp) as [(? & <-) | not_prefix].
    - eapply no_ancestor_q.
      + rewrite <-sget_app. exact G.
      + exists i, r. rewrite <-app_spath_vpath_assoc in K.
        eapply app_spath_vpath_inv_head. exact K.
    - destruct (comparable_spaths sp p) as [ | | (? & ? & <-) | Hdisj].
      + subst. apply not_prefix. reflexivity.
      + eapply no_ancestor_p; eassumption.
      + apply not_prefix. eexists. reflexivity.
      + eapply disj_if_left_disj_prefix in Hdisj.
        eapply not_prefix_disj; [exact Hdisj | ]. eexists. exact K.
  Qed.
End GetSetPath.

(** * Reformulation of properties on states using weighted sums. *)
(** These are properties like "The state [S] contains one/at most one/no node that satisfy a given
   predicate." *)
Section StateUniqueConstructor.
  Context `{IsState : State state V}.

  (* Notice that the following definitions don't use validity hypotheses. The reason is that we
     only assert unicity for nodes that are not the bottom value (ex: borrows, loans, pointers,
     locs). Therefore, a validity hypothesis is unnecessary. And because of that, the lemmas include
     a hypothesis "c <> bot". *)
  Definition at_most_one_node c (S : state) :=
    forall p q, get_node (S.[p]) = c -> get_node (S.[q]) = c -> p = q.

  Definition at_most_one_node_alt c (S : state) :=
    exists p, forall q, get_node (S.[q]) = c -> p = q.

  Lemma not_contains_implies_at_most_one_node c S :
    c <> get_node bot -> not_state_contains (eq c) S -> at_most_one_node c S.
  Proof.
    intros not_bot not_contains p ? Hp. exfalso. eapply not_contains; [ | eauto].
    apply get_not_bot_valid_spath. congruence.
  Qed.

  Lemma at_most_one_node_alt_implies_at_most_one_node c S :
    at_most_one_node_alt c S -> at_most_one_node c S.
  Proof.
    intros (p & spath_is_p) q r Hq Hr. rewrite <-(spath_is_p _ Hq), <-(spath_is_p _ Hr). reflexivity.
  Qed.

  Lemma unique_node_implies_at_most_one_node c S :
    c <> get_node bot -> not_state_contains (eq c) S -> at_most_one_node c S.
  Proof.
    intros not_bot not_contains p ? Hp. exfalso. eapply not_contains; [ | eauto].
    apply get_not_bot_valid_spath. congruence.
  Qed.

  Lemma not_state_contains_map_Forall S P :
    not_state_contains P S <-> map_Forall (fun _ => not_value_contains P) (get_map S).
  Proof.
    split.
    - intros Hnot_contains i ? get_i p valid_p ?. eapply (Hnot_contains (i, p)).
      eexists. split; eassumption.
      unfold sget. replace (fst (i, p)) with i by reflexivity. rewrite get_i. assumption.
    - intros Hnot_contains p (? & G & ?) P_p. eapply Hnot_contains. eassumption. eassumption.
      unfold sget in P_p. rewrite G in P_p. exact P_p.
  Qed.

  Lemma decide_at_most_one_node c S (not_bot : c <> get_node bot) :
    at_most_one_node c S <-> sweight (indicator c) S <= 1.
  Proof.
    split.
    - intros at_most_one. apply map_sum_unique_one.
      + intros i ? G. apply weight_one_at_most_one_vpath.
        * intro d. unfold indicator. destruct (decide (c = d)); repeat constructor.
        * intros p q valid_p valid_q ->%indicator_non_zero ?%indicator_non_zero.
          cut ((i, p) = (i, q)). { congruence. }
          eapply at_most_one; unfold sget; cbn; now rewrite G.
      + intros i j ? ? get_S_i get_S_j (p & ? & ?)%weight_non_zero (q & ? & ?)%weight_non_zero.
        cut ((i, p) = (j, q)). { congruence. }
        eapply at_most_one;
          unfold sget; cbn; rewrite ?get_S_i, ?get_S_j; symmetry; now apply indicator_non_zero.
    - unfold at_most_one_node, sget. intros G (i & p) (j & q). cbn. intros.
      destruct (get_at_accessor S i) as [v | ] eqn:?; [ | congruence].
      destruct (get_at_accessor S j) as [w | ] eqn:?; [ | congruence].
      assert (valid_p : valid_vpath v p) by (apply get_not_bot_valid_vpath; congruence).
      assert (valid_q : valid_vpath w q) by (apply get_not_bot_valid_vpath; congruence).
      assert (indicator c (get_node (v.[[p]])) = 1) by now apply indicator_eq.
      assert (indicator c (get_node (w.[[q]])) = 1) by now apply indicator_eq.
      replace j with i in *.
      + f_equal. replace w with v in * by congruence.
        unfold sweight in G. erewrite map_sum_delete in G by eassumption.
        eapply (value_weight_at_most_one (indicator c)); try eassumption; lia.
      + apply (weight_vget_node_le (indicator c)) in valid_p, valid_q.
        eapply map_sum_le_one with (m := get_map S); [eassumption.. | lia | lia].
  Qed.

  (** Decision procedures. *)
  Lemma decidable_not_value_contains_zeroary P (G : forall n, Decision (P n)) v :
    arity (get_node v) = 0 -> Decision (not_value_contains P v).
  Proof.
    intros ?. destruct (decide (P (get_node v))).
    - right. intros K. apply (K []); [constructor | assumption].
    - left. apply not_value_contains_zeroary; assumption.
  Defined.

  Lemma decidable_not_value_contains_unary P (G : forall n, Decision (P n)) v w :
    children v = [w] -> Decision (not_value_contains P w) -> Decision (not_value_contains P v).
  Proof.
    intros v_child Hdec. destruct (decide (P (get_node v))).
    - right. intros K. apply (K []); [constructor | assumption].
    - destruct Hdec as [ | w_not_contains].
      + left. eapply not_value_contains_unary; eassumption.
      + right. intros K. eapply w_not_contains. intros p ? ?. apply (K (0 :: p)).
        * econstructor; [rewrite v_child; reflexivity | assumption].
        * rewrite vget_cons, v_child. assumption.
  Defined.

  Instance decidable_not_state_contains P `(forall v, Decision (not_value_contains P v)) S :
    Decision (not_state_contains P S).
  Proof.
  destruct (decide (map_Forall (fun _ => not_value_contains P) (get_map S)));
  rewrite <-not_state_contains_map_Forall in * |-; [left | right]; assumption.
Defined.
End StateUniqueConstructor.

(** * Automation. *)
Hint Extern 5 (length (children ?v) = _) =>
  match goal with
  | H : get_node (?S.[?p]) = _ |- _ =>
      rewrite length_children_is_arity, H; reflexivity
  end : spath.
Hint Extern 5 (~strict_prefix ?p ?q) =>
  match goal with
  | H : get_node (?S.[?p]) = _ |- _ =>
      simple apply (get_zeroary_not_strict_prefix S); [rewrite H | ]
  end : spath.
Hint Extern 0 (~strict_prefix _ _) =>
  lazymatch goal with
  | H : get_node (?S.[?p <- _].[?q]) = _ |- ~strict_prefix ?p ?q =>
      eapply get_zeroary_not_strict_prefix';
        [apply valid_get_node_sget_not_bot; rewrite H; discriminate | reflexivity]
  end : spath.
Hint Resolve sset_sget_diff : spath.
Hint Resolve disj_spath_add_anon : spath.
Hint Resolve disj_spath_add_anon' : spath.
(* If the goal contains a hypothesis  [get_node (S.[p]) = cp] and a hypothesis
   [get_node (S.[q]) = cq]
 * with [cp <> cq], then we can automatically prove [p <> q] by congruence. *)
Hint Extern 0 (~ (@eq spath _ _)) => congruence : spath.

(** Resolution of goals for freshness of anonymous bindings: *)
Hint Resolve-> fresh_anon_sset : spath weight.
Hint Rewrite<- @fresh_anon_sset : spath.

(* Resolution of goals of the form [fst p <> anon_accessor a]
   They are used to solve the conditions of the rewrite lemmas sget_add_anon and sset_add_anon. *)
Hint Resolve valid_spath_diff_fresh_anon : spath.
Hint Resolve valid_spath_diff_fresh_anon' : spath.
Lemma diff_first_app_spath_vpath p q x : fst p <> x -> fst (p +++ q) <> x.
Proof. easy. Qed.
Hint Resolve diff_first_app_spath_vpath : spath.

(** Hints for [no_ancestor]: *)
Hint Resolve <-no_ancestor_add_anon : spath.
Hint Rewrite @no_ancestor_add_anon using assumption : spath.
Hint Resolve <-no_ancestor_sset : spath.
Hint Rewrite @no_ancestor_sset using eauto with spath; fail: spath.
Hint Rewrite @no_ancestor_anon using assumption : spath.
Hint Resolve no_ancestor_app : spath.

(** ** Automation for comparisons (prefix, strict_prefix, disj, =, and the negations). *)
(** The issue is that to prove a comparison [C p q] (with [C] a comparison predicate), we often
   need to use a lemma that generate other comparison goals. For example:
   - To prove [disj p q], we can use the lemma [prove_disj'], that generates two goals including [~strict_prefix q p].
   - To prove [~strict_prefix q p], we can use the lemma [not_disj_strict_prefix'], that generate a goal [disj p q].
   If we simply placed every lemma in the [spath] database and used the tactic [eauto] for automatic resolution, the cyclic structure of the database would make the tactic inefficient.
 *)
(** When possible, we use immediate hints, to avoid recursively generate subgoals. *)
Hint Immediate symmetric_disj : spath.
Hint Immediate vdisj_symmetric : spath.
Hint Immediate strict_prefix_irrefl : spath.
Hint Immediate not_prefix_implies_not_strict_prefix : spath.
Hint Immediate not_disj_strict_prefix : spath.
Hint Immediate not_disj_strict_prefix' : spath.
Hint Immediate vstrict_prefix_is_vprefix : spath.

(* Hint Immediate<- disj_common_prefix : spath. *)
Lemma _disj_common_prefix p q r : vdisj q r -> disj (p +++ q) (p +++ r).
Proof. rewrite disj_common_prefix. auto. Qed.
Hint Immediate _disj_common_prefix : spath.

(* Hint Immediate<- disj_common_index : spath. *)
Lemma _disj_common_index i p q : vdisj p q -> disj (i, p) (i, q).
Proof. rewrite disj_common_index. auto. Qed.
Hint Immediate _disj_common_index : spath.

(** In case the where the immediate hints are not sufficient, this tactic helps reduce the goal.
   The idea is that when we prove a comparison [C p q], this tactic generated subgoals [D p q] that are weaker ([D p q -> C p q]) and tries to solve as many goals as possible using automatic resolution.

    It never backtracks.
*)
(* TODO: more complete documentation. *)
Ltac reduce_comp :=
  eauto with spath;
  lazymatch goal with
  (* Note: shouldn't I use automatic rewriting instead? *)
  | H : vdisj (?p ++ ?q) (?p ++ ?r) |- _ => rewrite vdisj_common_prefix in H
  | H : disj (?p +++ ?q) (?p +++ ?r) |- _ => rewrite disj_common_prefix in H

  | |- prefix (?p +++ [0]) ?q =>
      eapply strict_prefix_one_child;
        [ eauto with spath |
          apply prefix_and_neq_implies_strict_prefix; [eauto with spath; fail | ] |
        ]

  | |- strict_prefix ?p ?q =>
      apply prefix_and_neq_implies_strict_prefix; eauto with spath; fail

  | |- disj ?p (?q +++ ?r) => apply disj_if_left_disj_prefix; eauto with spath; fail
  | |- disj (?p +++ ?r) ?q => apply disj_if_right_disj_prefix; eauto with spath; fail
  | |- disj ?p ?q => apply prove_disj'

  | |- ?p <> ?q => apply neq_implies_not_prefix; eauto with spath; fail

  | |- ~prefix ?p ?q => apply prove_not_prefix

  | |- ~strict_prefix ?p (?q +++ [?i]) =>
      rewrite strict_prefix_app_last
  | |- ~strict_prefix ?p ?q =>
      first [
        eapply not_prefix_one_child; [eauto with spath | | eauto with spath; fail] |
        rewrite not_strict_prefix_app_last; eauto with spath; fail
      ]
  end
.
(** The tactic [reduce_comp] may not solve the goal. The strategy is to repeatedly "reduce" the
   goal until it is solved. *)
Ltac solve_comp := repeat reduce_comp.

(** ** Automatic resolution of validity. *)
Lemma valid_vpath_app_last_get_node_not_zeroary {V} `{IsValue : Value V nodes} v p :
  arity (get_node (v.[[p]])) > 0 -> valid_vpath v (p ++ [0]).
Proof.
  intro. apply valid_vpath_app. split.
  - apply get_not_bot_valid_vpath. intro G. rewrite G in H.
    rewrite <-length_children_is_arity, children_bot in H. inversion H.
  - rewrite<- length_children_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Ltac validity0 :=
  lazymatch goal with
  | H : get_node (?S.[?p]) = _ |- valid_spath ?S ?p =>
      apply (valid_get_node_sget_not_bot S p);
      rewrite H;
      discriminate
  | H : get_node (?S.[?p]) = _ |- valid_spath ?S (?p +++ [0]) =>
      simple apply valid_spath_app_last_get_node_not_zeroary;
      rewrite H;
      constructor
  | H : get_node (?S.[?p +++ ?q]) = _ |- valid_spath ?S (?p +++ ?q ++ [0]) =>
      rewrite (app_spath_vpath_assoc p q [0]);
      simple apply valid_spath_app_last_get_node_not_zeroary;
      rewrite H;
      constructor
  | H : get_node (?S.[?p +++ ?q ++ ?r]) = _ |- valid_spath ?S (?p +++ ?q ++ ?r ++ [0]) =>
      rewrite (app_assoc q r [0]);
      rewrite (app_spath_vpath_assoc p (q ++ r) [0]);
      simple apply valid_spath_app_last_get_node_not_zeroary;
      rewrite H;
      constructor
  | H : ?S.[?p] = ?v |- valid_spath ?S ?p =>
      simple apply get_not_bot_valid_spath;
      rewrite H;
      discriminate
  | |- valid_spath (?S.[?p <- ?v]) (?p +++ ?q) =>
      simple apply sset_prefix_valid;
      validity0
  | |- valid_spath (?S.[?p <- ?v]) ?q =>
      apply sset_not_prefix_valid; [ | validity0]
  | |- valid_spath (?S,, ?a |-> _) (anon_accessor ?a, ?q) =>
      apply valid_spath_anon;
      validity0
  | |- valid_spath (?S,, _ |-> _) ?p =>
      simple apply valid_spath_add_anon; [validity0 | ]
  | |- valid_spath ?S ?p => idtac

  (* Solving valid_vpath: *)
  | |- valid_vpath (?S.[?p]) ?q =>
      apply (valid_spath_app S p q);
      (* In case p is of the form p0 +++ p1, we rewrite (p0 +++ p1) +++ q into
         p0 +++ (p1 ++ q) *)
      validity0
  | |- valid_vpath _ ([_] ++ _) =>
      econstructor; [reflexivity | validity0]
  | H : get_node (?v.[[?p]]) = _ |- valid_vpath ?v (?p ++ [0]) =>
      simple apply valid_vpath_app_last_get_node_not_zeroary;
      rewrite H;
      constructor
  | |- valid_vpath _ [] => constructor
  | H : ?v.[[?p]] = _ |- valid_vpath ?v ?p =>
      apply (valid_get_node_vget_not_bot v p);
      rewrite H;
      discriminate
  | H : get_node (?v.[[?p]]) = _ |- valid_vpath ?v ?p =>
      apply (valid_get_node_vget_not_bot v p);
      rewrite H;
      discriminate
  (* TODO: maybe use a more general forme ?v.[[?q <- _]] ?p, at the condition that ?q
     is not a strict prefix of p. This would require an extra lemma. *)
  | |- valid_vpath (?v.[[?p ++ _ <- _]]) ?p =>
      simple apply vset_prefix_right_valid; validity0
  | |- valid_vpath ?v ?p => idtac
  end.
Hint Extern 5 (valid_spath _ _) =>
  repeat rewrite <-app_spath_vpath_assoc;
  validity0 : spath.

Ltac validity :=
  repeat rewrite <-app_spath_vpath_assoc;
  validity0;
  solve_comp.

(* Adding a hint to resolve a relation ~prefix p q using the facts that:
 * - S.[p] does not contain a node c.
 * - S.[q] starts by the node c.
 * To solve the second goal, we need to help auto. When we are using this lemma, there should be a
 * hypothesis S.[q] = v. We are giving the instruction to rewrite S.[q] into v, and then to reduce
 * the expression (get_at_accessorue v) produced, so that it can be solved automatically.
 *)
Hint Extern 3 (~prefix ?p ?q) =>
  match goal with
  | H : get_node (?S.[?q]) = _ |- _ =>
    simple eapply not_value_contains_not_prefix; [ | rewrite H; cbn | validity]
  end : spath.
Hint Resolve not_value_contains_not_prefix' : spath.

(** ** Automatic proof of equality between states. *)
(** When we want to prove an equality of the form [Sl = Sr.[p <- v]] or
    [Sl = Sr.[p +++ q <- v]], we perform commutations so that all of the writes
   [[p <- v]] or [[p +++ r <- v]] are at the end.
   We also reorder anonymous bindings.
 *)
Ltac perform_commutation :=
  lazymatch goal with
  | |- _ = _.[?p +++ ?q <- _] =>
    lazymatch goal with
    | |- context [ _.[p <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ p) by solve_comp
    end
  | |- _ = _.[?p <- _] =>
    lazymatch goal with
    | |- context [ _.[p <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ p) by solve_comp
    | |- context [ _.[p +++ ?q <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ (p +++ q)) by solve_comp
    end
  | |- ?Sl,, ?a |-> _,, ?b |-> _ = ?Sr,, ?a |-> _ =>
      rewrite (add_anon_commute Sl a b) by congruence
  end
.

(** Automatically solve equality between two states that are sets of a state [S], _i.e_ solves goals of
    the form:
    [S.[p0 <- v0] ... .[pm <- vm] = S.[q0 <- w0] ... .[qn <- vn]]
 *)
Ltac states_eq :=
  apply reflexive_eq;
  autorewrite with spath;
  (* In case we want to prove equality between pairs (v, S), we prove the equality between the
   * values by reflexivity, and leave as a goal the proof of equality between the states. *)
  lazymatch goal with
  | |- (_, _) = (_, _) => refine (proj2 (pair_equal_spec _ _ _ _) _); split; [reflexivity | ]
  | _ => idtac
  end;
  repeat (repeat (perform_commutation; autorewrite with spath); f_equal)
.

(** ** Automatic rewriting database. *)
(* Informally, here are the normal forms for the main objects: *)
(* Normal form for vpaths : p ++ (p ++ ...) *)
(* Normal form for spaths : p +++ (p ++ ...) *)
(* Normal form for values : v.[[p]].[[p <- v]].[[p <- v]] ... or S.[p].[[p <- v]].[[p <- v]] *)
(* Normal form for states : (S.[p <- v].[p <- v] ...), a |-> v *)

(* Simple simplifications: *)
(* TODO: I should rely on [cbn [fst]] and [cbn [snd]] instead. *)
Hint Rewrite app_nil_r : spath.
Lemma snd_pair [A B] (a : A) (b : B) : snd (a, b) = b. Proof. reflexivity. Qed.
Hint Rewrite snd_pair : spath.
Lemma snd_app (v : spath) w : snd (v +++ w) = (snd v) ++ w. Proof. reflexivity. Qed.
Hint Rewrite @snd_app : spath.

(* Re-parenthizing spaths and vpaths. *)
Hint Rewrite <- app_assoc : spath.
Hint Rewrite <- @app_spath_vpath_assoc : spath.
Hint Rewrite app_spath_vpath_nil_r : spath.

(* When the term to rewrite contains a subterm of the form S.[q <- v].[v], it is not in normal
   form. We apply one of the following rewrite rules to commute the get and the set, or to
   remove the set operation entirely. *)
Hint Rewrite @get_node_sset_sget_not_prefix using solve_comp; fail : spath.
Hint Rewrite @sset_sget_equal using validity : spath.
Hint Rewrite @sset_sget_prefix using validity : spath.
Hint Rewrite @sset_sget_prefix_right using validity : spath.
Hint Rewrite @sset_sget_common_prefix using validity : spath.

Ltac solve_sset_sget_disj :=
 lazymatch goal with
  | H : disj ?p ?q |- disj ?p ?q => apply H
  | H : disj ?p ?q |- disj (?p +++ _) ?q => apply disj_if_right_disj_prefix, H
  | H : disj ?p ?q |- disj ?p (?q +++ _) => apply disj_if_left_disj_prefix, H
  | H : disj ?p ?q |- disj (?p +++ _) (?q +++ _) =>
      apply disj_if_right_disj_prefix, disj_if_left_disj_prefix, H
  | H : disj ?q ?p |- disj ?p ?q => symmetry; apply H
  | H : disj ?q ?p |- disj (?p +++ _) ?q => symmetry; apply disj_if_left_disj_prefix, H
  | H : disj ?q ?p |- disj ?p (?q +++ _) => symmetry; apply disj_if_right_disj_prefix, H
  | H : disj ?q ?p |- disj (?p +++ _) (?q +++ _) =>
      symmetry; apply disj_if_right_disj_prefix, disj_if_left_disj_prefix, H
  end.

Hint Rewrite @sset_sget_disj using solve_sset_sget_disj : spath.

(* Idem for vpaths: *)
Hint Rewrite @vset_vget_equal using validity : spath.
Hint Rewrite @vset_vget_prefix using validity : spath.
Hint Rewrite @vset_vget_prefix_right using validity : spath.

Hint Rewrite @get_node_vset_cons using discriminate : spath.

Hint Rewrite @sset_twice_equal : spath.
Hint Rewrite @sset_twice_prefix_left : spath.
Hint Rewrite @sset_twice_prefix_right : spath.

(* When the term to rewrite contains a subterm of the form (S,, a |-> v).[p] or
   (S,, a |-> v).[p <- w], it is not in normal form.
   Depending on whether p is a path in S, or a path in the last binding Anon |-> v, we use
   one of the following rewrite rules. *)
Hint Rewrite @sset_add_anon using eauto with spath; fail : spath.
Hint Rewrite @sset_anon using try assumption; reflexivity : spath.
Hint Rewrite @sget_add_anon using eauto with spath; fail : spath.
Hint Rewrite @sget_anon using try assumption; reflexivity : spath.
Hint Rewrite<- @sget_app : spath.
Hint Rewrite<- @vget_app : spath.

(* Populating the "weight" rewrite database: *)
(* These hints turn operations on naturals onto operations on relatives, so to rewrite
 * sweight_sset: *)
Hint Rewrite Nat2Z.inj_add : weight.
Hint Rewrite Nat2Z.inj_le : weight.
Hint Rewrite Nat2Z.inj_lt : weight.
Hint Rewrite Nat2Z.inj_gt : weight.

Hint Rewrite @sweight_sset using validity : weight.
Hint Rewrite @sweight_add_anon using auto with weight : weight.

(* When applying twice sweight_sset on a state of the form S.[p <- v].[q <- w], we end up
   with value S.[p <- v].[q], that we reduce using sset_sget_disj: *)
Hint Rewrite @sset_sget_disj using eauto with spath : weight.
Hint Rewrite<- @sget_app : weight.

Hint Rewrite @indicator_same : weight.
Hint Rewrite @indicator_diff using congruence : weight.
Hint Rewrite @indicator_eq using auto; fail : weight.

(** Rewriting [weight_arity_0] and [weight_arity_1] using goals of the form  [get_node S.[p] = c]
   I couldn't do it with autorewrite, so I'm using this strang tactic instead. *)
Ltac weight_given_node :=
  lazymatch goal with
  | H : get_node (?S.[?p]) = _ |- context [vweight _ (?S.[?p])] =>
    let G := fresh in
    pose proof (G := H);
    apply (f_equal arity) in G;
    (eapply weight_arity_0 in G || eapply weight_arity_1 in G);
    (* Why do I rewrite H? *)
    rewrite G, ?H;
    clear G
  | H : get_node (?S.[?p]) = _, K : context [vweight _ (?S.[?p])] |- _ =>
    let G := fresh in
    pose proof (G := H);
    apply (f_equal arity) in G;
    (eapply weight_arity_0 in G || eapply weight_arity_1 in G);
    rewrite G, H in K;
    clear G
  end.

Ltac weight_inequality :=
  (* Translate the inequality into relatives, and repeatedly rewrite sweight_sset. *)
  autorewrite with weight in *;
  (* Use the hypotheses "get_node S.[p] = c" to further rewrite the formula. *)
  repeat weight_given_node;
  (* Final rewriting. *)
  autorewrite with weight in *;
  lia
.
