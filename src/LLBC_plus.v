(** * Mechanized_LLBC.LLBC_plus : definition of symbolic states, and simulation proof for LLBC+. *)
Require Import base.
Require Import lang.
Require Import SimulationUtils.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.
(* Notation conflict between stdpp's [+++] and our [+++]. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap gmap.
Require Import PathToSubtree.
Require Import OptionMonad.

(** A limited notion of type. It only describes values that can be turned into symbolic values, and
    that excludes mutable borrows for the moment.
    The type soundness is ensured dynamically. We only need it for two reasons:
    - Checking that a symbolic value of type T abstracts a value of type T.
    - Checking that we a loan [loan^m(ty, t)] obtains a value back, it is a value of type T. *)
Inductive LLBC_type :=
| intT
| boolT
.

(** * Definition of LLBC+ values and states. *)
Inductive LLBC_plus_val :=
| LLBC_plus_bot
| LLBC_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| LLBC_plus_bool (b : bool)
(* Note: we must add a type parameter in mutable loans, because when we end a mutable loan in a
 * region abstraction, we must ensure that the type of the borrow we end corresponds.
 * However, this creates the issue that now, every mutable loan is typed, even mutable loans out
 * of abstractions.
 * Probably we should remove all dynamic typing, and implement a static type checking, as well as a
 * well-typedness predicate and an invariance proof. *)
| LLBC_plus_mut_loan (ty : LLBC_type) (l : loan_id)
| LLBC_plus_mut_borrow (l : loan_id) (v : LLBC_plus_val)
(*
| LLBC_plus_shr_loan (l : loan_id) (v : LLBC_plus_val)
| LLBC_plus_shr_borrow (l : loan_id)
 *)
(* | LLBC_plus_pair (v0 : LLBC_plus_val) (v1 : LLBC_plus_val) *)
(* Note: symbolic values should be parameterized by a type, when we introduce other datatypes than
   integers. *)
| LLBC_plus_symbolic (ty : LLBC_type)
.

Variant LLBC_plus_nodes :=
| LLBC_plus_botC
| LLBC_plus_intC (n : nat)
| LLBC_plus_boolC (b : bool)
| LLBC_plus_mut_loanC (ty : LLBC_type) (l : loan_id)
| LLBC_plus_mut_borrowC (l : loan_id)
| LLBC_plus_symbolicC (ty : LLBC_type)
.

Instance EqDecision_LLBC_plus_nodes : EqDecision LLBC_plus_nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Defined.

Definition LLBC_plus_arity c := match c with
| LLBC_plus_botC => 0
| LLBC_plus_intC _ => 0
| LLBC_plus_boolC _ => 0
| LLBC_plus_mut_loanC _ _ => 0
| LLBC_plus_mut_borrowC _ => 1
| LLBC_plus_symbolicC _ => 0
end.

Definition LLBC_plus_get_node v := match v with
| LLBC_plus_bot => LLBC_plus_botC
| LLBC_plus_int n => LLBC_plus_intC n
| LLBC_plus_bool b => LLBC_plus_boolC b
| LLBC_plus_mut_loan ty l => LLBC_plus_mut_loanC ty l
| LLBC_plus_mut_borrow l _ => LLBC_plus_mut_borrowC l
| LLBC_plus_symbolic ty => LLBC_plus_symbolicC ty
end.

Definition LLBC_plus_children v := match v with
| LLBC_plus_bot => []
| LLBC_plus_int _ => []
| LLBC_plus_bool _ => []
| LLBC_plus_mut_loan _ _ => []
| LLBC_plus_mut_borrow _ v => [v]
| LLBC_plus_symbolic ty => []
end.

Definition LLBC_plus_fold c vs := match c, vs with
| LLBC_plus_intC n, [] => LLBC_plus_int n
| LLBC_plus_boolC b, [] => LLBC_plus_bool b
| LLBC_plus_mut_loanC ty l, [] => LLBC_plus_mut_loan ty l
| LLBC_plus_mut_borrowC l, [v] => LLBC_plus_mut_borrow l v
| LLBC_plus_symbolicC ty, [] => LLBC_plus_symbolic ty
| _, _ => LLBC_plus_bot
end.

Fixpoint LLBC_plus_weight node_weight v :=
  match v with
  | LLBC_plus_mut_borrow l v => node_weight (LLBC_plus_mut_borrowC l) + LLBC_plus_weight node_weight v
  | v => node_weight (LLBC_plus_get_node v)
end.

Program Instance ValueLLBC_plus : Value LLBC_plus_val LLBC_plus_nodes := {
  arity := LLBC_plus_arity;
  get_node := LLBC_plus_get_node;
  children := LLBC_plus_children;
  fold_value := LLBC_plus_fold;
  vweight := LLBC_plus_weight;
  bot := LLBC_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_nodes eq_children; inversion eq_nodes; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; cbn; lia. Qed.

Record LLBC_plus_state := {
  vars : Pmap LLBC_plus_val;
  anons : Pmap LLBC_plus_val;
  abstractions : Pmap (Pmap LLBC_plus_val);
}.

Definition encode_var (x : var) :=
  encode (A := _ + positive * positive) (inl (encode (A := _ + anon) (inl x))).
Definition encode_anon (a : anon) :=
  encode (A := _ + positive * positive) (inl (encode (A := var + _) (inr a))).
Definition encode_abstraction (x : positive * positive) := encode (A := positive + _) (inr x).

Lemma encode_anon_inj : Inj eq eq encode_anon.
Proof.
  unfold encode_anon. intros ? ? H%encode_inj. inversion H. apply encode_inj. congruence.
Qed.

Instance encode_abstraction_inj : Inj eq eq encode_abstraction.
Proof.
  unfold encode_abstraction. intros x y H. eapply (f_equal decode') in H.
  rewrite !decode'_encode in H. congruence.
Qed.

Program Instance IsState : State LLBC_plus_state LLBC_plus_val := {
  get_map S := sum_maps (sum_maps (vars S) (anons S)) (flatten (abstractions S));

  (* The flatten function in not injective. For example, [R] and [R<[A := empty]>] have the same
   * flattening. An empty region abstraction and a non-existant region abstraction can't be
   * distinguished. Therefore, for the axiom [state_eq_ext] to be true, we need the set of region
   * abstractions identifiers as extra information. *)
  extra := Pset;
  get_extra S := dom (abstractions S);

  alter_at_accessor f a S :=
    match decode' (A := positive + positive * positive) a with
    | Some (inl a) =>
        match decode' (A := var + anon) a with
        | Some (inl x) => {| vars := alter f x (vars S); anons := anons S; abstractions := abstractions S|}
        | Some (inr a) => {| vars := vars S; anons := alter f a (anons S); abstractions := abstractions S|}
        | None => S
        end
    | Some (inr (i, j)) => {| vars := vars S; anons := anons S;
                              abstractions := alter (fun r => alter f j r) i (abstractions S)|}
    | None => S
    end;

  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := positive + positive * positive) x with
    | Some (inl y) =>
        match decode (A := var + anon) y with
        | Some (inr a) => Some a
        | Some (inl _) => None
        | None => None
        end
    | Some (inr _) => None
    | None => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S); abstractions := abstractions S|};
}.
Next Obligation.
  intros [? ? R0] [? ? R1]. cbn. intros ((-> & ->)%sum_maps_eq & ?)%sum_maps_eq ?. f_equal.
  apply map_eq. intros i. destruct (decide (elem_of i (dom R0))) as [e | ].
  - assert (elem_of i (dom R1)) as (b & Ha)%elem_of_dom by congruence.
    apply elem_of_dom in e. destruct e as (a & Hb). rewrite Ha, Hb. f_equal.
    apply map_eq. intros j.
    apply lookup_Some_flatten with (j := j) in Ha. apply lookup_Some_flatten with (j := j) in Hb.
    congruence.
  - assert (~(elem_of i (dom R1))) by congruence. rewrite not_elem_of_dom in * |-. congruence.
Qed.
Next Obligation.
  intros ? ? y. cbn. destruct (decode' y) as [[z | (i & j)] | ] eqn:H.
  - destruct (decode' z) as [[? | ?] | ]; reflexivity.
  - cbn. apply dom_alter_L.
  - reflexivity.
Qed.
Next Obligation.
  intros ? ? y. cbn. destruct (decode' y) as [[z | (i & j)] | ] eqn:H.
  - rewrite decode'_is_Some in H.
    destruct (decode' z) as [[x | a] | ] eqn:G.
    + cbn. rewrite decode'_is_Some in G. rewrite <-H, <-G, <- !sum_maps_alter_inl.
      reflexivity.
    + cbn. rewrite decode'_is_Some in G.
      rewrite <-H, <-G, <-sum_maps_alter_inr, <-sum_maps_alter_inl. reflexivity.
    + symmetry. apply map_alter_not_in_domain. rewrite <-H, sum_maps_lookup_l.
      now apply sum_maps_lookup_None.
  - cbn. rewrite decode'_is_Some in H. rewrite <-H,  sum_maps_alter_inr, alter_flatten. reflexivity.
  - symmetry. apply map_alter_not_in_domain, sum_maps_lookup_None. assumption.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros. cbn. unfold encode_anon. rewrite sum_maps_insert_inl, sum_maps_insert_inr. reflexivity.
Qed.
Next Obligation. intros. unfold encode_anon. reflexivity. Qed.

(* Helper lemmas. *)
Lemma get_at_var S x : get_at_accessor S (encode_var x) = lookup x (vars S).
Proof. unfold get_map, encode_var. cbn. rewrite !sum_maps_lookup_l. reflexivity. Qed.

Lemma get_at_anon S a : get_at_accessor S (anon_accessor a) = lookup a (anons S).
Proof.
  unfold get_map, anon_accessor. cbn. unfold encode_anon.
  rewrite sum_maps_lookup_l, sum_maps_lookup_r. reflexivity.
Qed.

Lemma get_at_abstraction S i j : get_at_accessor S (encode_abstraction (i, j)) =
  mbind (lookup j) (lookup i (abstractions S)).
Proof.
  unfold get_map, encode_abstraction. cbn. rewrite sum_maps_lookup_r. apply lookup_flatten.
Qed.

Lemma get_at_abstraction' S i j A (H : lookup i (abstractions S) = Some A) :
  get_at_accessor S (encode_abstraction (i, j)) = lookup j A.
Proof. rewrite get_at_abstraction, H. reflexivity. Qed.

Variant get_at_accessor_rel S : positive -> Prop :=
  | GetAtVar x v : lookup x (vars S) = Some v -> get_at_accessor_rel S (encode_var x)
  | GetAtAnon a v : lookup a (anons S) = Some v -> get_at_accessor_rel S (anon_accessor a)
  | GetAtAbstraction i j A v
      (get_A : lookup i (abstractions S) = Some A) (get_v : lookup j A = Some v) :
      get_at_accessor_rel S (encode_abstraction (i, j))
.

Lemma get_at_accessor_is_Some S acc :
  is_Some (get_at_accessor S acc) -> get_at_accessor_rel S acc.
Proof.
  intros [(i & -> & H) | ((i & j) & -> & (? & H))]%sum_maps_is_Some.
  - apply sum_maps_is_Some in H. destruct H as [(x & -> & (? & ?)) | (a & -> & (? & ?))].
    + eapply GetAtVar. eassumption.
    + eapply GetAtAnon. eassumption.
  - rewrite lookup_flatten, bind_Some in H. destruct H as (A & ? & ?).
    eapply GetAtAbstraction with (A := A); eauto.
Qed.

Declare Scope llbc_plus_scope.
Delimit Scope llbc_plus_scope with llbc.

(* TODO: move? *)
(* TODO: set every priority to 0? *)
Reserved Notation "'loan^m' ( ty , l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( ty , l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level). (* TODO: unused in LLBC_plus.v *)
Reserved Notation "'ptrC' ( l )" (at level 0). (* TODO: unused in LLBC_plus.v *)

(* Notation "'bot'" := LLBC_plus_bot: llbc_plus_scope. *)
Notation "'loan^m' ( ty , l )" := (LLBC_plus_mut_loan ty l) : llbc_plus_scope.
Notation "'borrow^m' ( l  , v )" := (LLBC_plus_mut_borrow l v) : llbc_plus_scope.

Notation "'botC'" := LLBC_plus_botC: llbc_plus_scope.
Notation "'loanC^m' ( ty , l )" := (LLBC_plus_mut_loanC ty l) : llbc_plus_scope.
Notation "'borrowC^m' ( l )" := (LLBC_plus_mut_borrowC l) : llbc_plus_scope.

(* Bind Scope llbc_plus_scope with LLBC_plus_val. *)
Open Scope llbc_plus_scope.

(** Definitions of LLBC+ operations. *)
Variant is_loan : LLBC_plus_nodes -> Prop :=
| IsLoan_MutLoan ty l : is_loan (loanC^m(ty, l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (is_loan (get_node loan^m(_, _))) => constructor : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Lemma is_loan_valid S sp : is_loan (get_node (S.[sp])) -> valid_spath S sp.
Proof. intros H. apply valid_get_node_sget_not_bot. destruct H; discriminate. Qed.

Variant is_borrow : LLBC_plus_nodes -> Prop :=
| IsLoan_MutBorrow l : is_borrow (borrowC^m(l)).
Hint Constructors is_borrow : spath.
Definition not_contains_borrow := not_value_contains is_borrow.
Hint Unfold not_contains_borrow : spath.
Hint Extern 0 (is_borrow (get_node borrow^m(_, _))) => constructor : spath.
Hint Extern 0 (~is_borrow _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Lemma not_contains_bot_valid S sp : not_contains_bot (S.[sp]) -> valid_spath S sp.
Proof.
  intros H. specialize (H []). cbn in H. apply get_not_bot_valid_spath.
  intros G. apply H. constructor. rewrite G. reflexivity.
Qed.
Hint Resolve not_contains_bot_valid : spath.

Variant is_symbolic : LLBC_plus_nodes -> Prop :=
| IsSymbolic_Symbolic ty : is_symbolic (LLBC_plus_symbolicC ty).
Definition not_contains_symbolic v := (not_value_contains is_symbolic v).
Hint Unfold not_contains_symbolic : spath.
Hint Extern 0 (~is_symbolic _) => intro; easy : spath.

Variant is_mut_borrow : LLBC_plus_nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).

Notation not_in_borrow := (no_ancestor is_mut_borrow).

Definition in_abstraction i x := exists j, x = encode_abstraction (i, j).
Definition not_in_abstraction (p : spath) := forall i, ~in_abstraction i (fst p).

Definition add_abstraction S i A :=
  {|vars := vars S; anons := anons S; abstractions := insert i A (abstractions S)|}.

Notation "S ,,, i |-> A" := (add_abstraction S i A) (at level 50, left associativity).

Definition fresh_abstraction S i := lookup i (abstractions S) = None.

Definition abstraction_element S i j := get_at_accessor S (encode_abstraction (i, j)).

(* Remove the value at j in the region abstraction at i, if this value exists. *)
Definition remove_abstraction_value S i j :=
  {|vars := vars S; anons := anons S; abstractions := alter (delete j) i (abstractions S)|}.

Definition remove_abstraction i S :=
  {|vars := vars S; anons := anons S; abstractions := delete i (abstractions S)|}.

(* Used to change a mutable borrow from borrow^m(l', v) to borrow^m(l, v). *)
Notation rename_mut_borrow S sp l := (S.[sp <- borrow^m(l, S.[sp +++ [0] ])]).

(* [is_of_type ty v] asserts that the value v is initialized (not bot) and of type ty. *)
Variant is_of_type : LLBC_type -> LLBC_plus_val -> Prop :=
| Is_of_type_symbolic ty : is_of_type ty (LLBC_plus_symbolic ty)
| Is_of_type_mut_loan ty l : is_of_type ty (loan^m(ty, l))
| Is_of_type_integer n : is_of_type intT (LLBC_plus_int n)
| Is_of_type_bool b : is_of_type boolT (LLBC_plus_bool b)
.

(* We want to assert that storing a value in a path preserves the type. However, we do not have a
 * global well-typedness predicate, so the type of a path is not defined in general.

 * Furthermore, paths that we store can contain uninitialized values, so we cannot type the path
 * that we overwrite.
 * The trick we use is to say that storing a value w in place p (in the state S) does not change
 * the type of the potential mutable borrows that contains p. *)
Definition store_compatible_types S p v :=
  forall q, strict_prefix q p -> is_mut_borrow (get_node (S.[q])) ->
    exists ty, is_of_type ty (S.[p]) /\ is_of_type ty v.

(* [add_anons S A S'] : when we end an abstraction region A, we need to add its values as anonymous
 * binding in a state S. The property [add_anons S A S'] relates this state S and this
 * abstraction A to a state S' with anonymous bindings added. *)
Variant add_anons : LLBC_plus_state -> Pmap LLBC_plus_val -> LLBC_plus_state -> Prop :=
  | AddAnons S A anons' : union_maps (anons S) A anons' ->
      add_anons S A {|vars := vars S; anons := anons'; abstractions := abstractions S|}
.

Definition get_loan_id c :=
  match c with
  | loanC^m(ty, l) => Some l
  | borrowC^m(l) => Some l
  | _ => None
  end.

Definition is_loan_id l c := get_loan_id c = Some l.
Notation is_fresh l S := (not_state_contains (is_loan_id l) S).
Hint Extern 0 (~is_loan_id _ _) => unfold is_loan_id; cbn; congruence : spath.
Hint Extern 0 (is_loan_id _ _) => reflexivity : spath.

Inductive remove_loans A B : Pmap LLBC_plus_val -> Pmap LLBC_plus_val-> Prop :=
  | Remove_nothing : remove_loans A B A B
  | Remove_MutLoan A' B' i j l ty (H : remove_loans A B A' B') :
      lookup i A' = Some (loan^m(ty, l)) ->
      lookup j B' = Some (borrow^m(l, LLBC_plus_symbolic ty)) ->
      remove_loans A B (delete i A') (delete j B')
.

Definition merge_abstractions A B C := exists A0 B0, remove_loans A B A0 B0 /\ union_maps A0 B0 C.

Definition remove_anon a S :=
  {| vars := vars S; anons := delete a (anons S); abstractions := abstractions S|}.

(** * Permutation of LLBC+ states. *)
(** A state permutation is a permutation of the anonymous variables and the elemnts of each regions.
    It does not affect the variables. *)

(* First, let us introduce renaming of loan identifiers. *)
Definition loan_id_map := Pmap positive.

Definition rename_loan_id (m : loan_id_map) (l : loan_id) :=
  match lookup l m with
  | Some l' => l'
  | None => l
  end.

Definition rename_node (m : loan_id_map) (n : LLBC_plus_nodes) :=
  match n with
  | borrowC^m(l) => borrowC^m(rename_loan_id m l)
  | loanC^m(ty, l) => loanC^m(ty, rename_loan_id m l)
  | _ => n
  end.

Fixpoint rename_value (m : loan_id_map) (v : LLBC_plus_val) :=
  match v with
  | borrow^m(l, w) => borrow^m(rename_loan_id m l, rename_value m w)
  | loan^m(ty, l) => loan^m(ty, rename_loan_id m l)
  | _ => v
  end.

Lemma get_node_rename_value m v : get_node (rename_value m v) = rename_node m (get_node v).
Proof. destruct v; reflexivity. Qed.
Hint Rewrite get_node_rename_value : spath.

Lemma children_rename_value m v : children (rename_value m v) = map (rename_value m) (children v).
Proof. destruct v; reflexivity. Qed.

Lemma vget_rename_value m p : forall v, rename_value m (v.[[p]]) = (rename_value m v).[[p]].
Proof.
  induction p.
  - reflexivity.
  - intros v. rewrite !vget_cons, IHp. f_equal.
    rewrite children_rename_value, nth_error_map. autodestruct.
Qed.

Lemma vset_rename_value m p w :
  forall v, rename_value m (v.[[p <- w]]) = (rename_value m v).[[p <- rename_value m w]].
Proof.
  induction p as [ | i p IH].
  - reflexivity.
  - intros v. apply get_nodes_children_inj.
    + rewrite get_node_rename_value, !get_node_vset_cons by discriminate.
      symmetry. apply get_node_rename_value.
    + rewrite children_rename_value, !children_vset_cons, children_rename_value.
      destruct (nth_error (children v) i) eqn:EQN.
      * erewrite map_alter_list by eassumption. eapply alter_list_equal_Some.
        -- rewrite nth_error_map, EQN. reflexivity.
        -- apply IH.
      * rewrite !alter_list_equal_None; auto. rewrite nth_error_map, EQN. reflexivity.
Qed.

Lemma valid_vpath_rename_value m v p : valid_vpath v p <-> valid_vpath (rename_value m v) p.
Proof.
  split.
  - induction 1 as [ | ? ? ? ? H].
    + constructor.
    + econstructor; [ | eassumption]. rewrite children_rename_value, nth_error_map, H. reflexivity.
  - intros H. remember (rename_value m v) as w eqn:EQN. revert v EQN. induction H as [ | v1 ? ? ? H].
    + constructor.
    + intros v0 ->. rewrite children_rename_value, nth_error_map in H.
      destruct (nth_error (children v0) i) eqn:?; [ | discriminate]. injection H as <-.
      econstructor; eauto.
Qed.

Lemma get_loan_id_rename_node m c :
  get_loan_id (rename_node m c) = fmap (rename_loan_id m) (get_loan_id c).
Proof. destruct c; reflexivity. Qed.

Fixpoint loan_set_val v : Pset :=
  match v with
  | borrow^m(l, v) => union (singleton l) (loan_set_val v)
  | loan^m(ty, l) => (singleton l)
  | _ => empty
  end.

Lemma get_loan_id_valid v p l : get_loan_id (get_node (v.[[p]])) = Some l -> valid_vpath v p.
Proof. intros H. apply valid_get_node_vget_not_bot. destruct (v.[[p]]); easy. Qed.

Lemma get_loan_id_valid_spath S p l : get_loan_id (get_node (S.[p])) = Some l -> valid_spath S p.
Proof. intros H. apply valid_get_node_sget_not_bot. destruct (S.[p]); easy. Qed.

Lemma elem_of_loan_set_val v l :
  elem_of l (loan_set_val v) <-> exists p, get_loan_id (get_node (v.[[p]])) = Some l.
Proof.
  split.
  - intros H. induction v; try discriminate.
    + cbn in H. rewrite elem_of_singleton in H. subst. exists []. reflexivity.
    + (* Why doesn't cbn work properly? *)
      replace (loan_set_val (borrow^m(l0, v))) with (union (singleton l0) (loan_set_val v)) in H
        by reflexivity.
      rewrite elem_of_union in H. destruct H as [H | H].
      * rewrite elem_of_singleton in H. subst. exists []. reflexivity.
      * destruct (IHv H) as (p & ?). exists (0 :: p). assumption.
  - intros (p & H).
    assert (valid_vpath v p) as G by (eapply get_loan_id_valid; exact H).
    induction G as [ | v i p ? get_i ? IH].
    + destruct v; inversion H; set_solver.
    + rewrite vget_cons, get_i in H. specialize (IH H).
      destruct v; cbn in get_i; try (rewrite nth_error_nil in get_i; discriminate).
      apply nth_error_singleton in get_i. destruct get_i as (<- & _).
      apply elem_of_union_r. exact IH.
Qed.

Lemma loan_set_id_empty v
  (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
  loan_set_val v = empty.
Proof.
  rewrite elem_of_equiv_empty_L. intros l (q & Hq)%elem_of_loan_set_val.
  destruct (get_node (v.[[q]])) eqn:EQN; inversion Hq.
  - eapply no_loan; [ | rewrite EQN]; [validity | constructor].
  - eapply no_borrow; [ | rewrite EQN]; [validity | constructor].
Qed.

Lemma rename_value_no_loan_id v p : loan_set_val v = empty -> rename_value p v = v.
Proof. induction v; set_solver. Qed.

Definition loan_set_state S : Pset :=
  map_fold (fun _ v L => union (loan_set_val v) L) empty (get_map S).

Lemma elem_of_loan_set_state S l :
  elem_of l (loan_set_state S) <-> exists p, get_loan_id (get_node (S.[p])) = Some l.
Proof.
  split.
  - unfold loan_set_state, sget. generalize (get_map S). intros A H.
    induction A as [ | i ? ? i_fresh ? IH] using map_first_key_ind.
    + rewrite map_fold_empty in H. set_solver.
    + rewrite map_fold_insert_first_key, elem_of_union in H by assumption. destruct H as [H | H].
      * rewrite elem_of_loan_set_val in H. destruct H as (q & H).
        exists (i, q). rewrite fst_pair, lookup_insert. assumption.
      * specialize (IH H). destruct IH as (p & IH). exists p.
        rewrite lookup_insert_ne; [exact IH | ].
        intros ->. rewrite i_fresh in IH. discriminate.
  - intros ((i & q) & get_l). unfold sget in get_l. rewrite fst_pair, snd_pair in get_l.
    destruct (lookup i (get_map S)) as [v | ] eqn:EQN; [ | discriminate].
    unfold loan_set_state. erewrite map_fold_delete_L; [ | set_solver | exact EQN].
    apply elem_of_union_l, elem_of_loan_set_val. exists q. exact get_l.
Qed.

Lemma loan_set_val_subset_eq_loan_set_state S i v :
  get_at_accessor S i = Some v -> subseteq (loan_set_val v) (loan_set_state S).
Proof.
  intros H%insert_delete. unfold loan_set_state. rewrite <-H.
  rewrite map_fold_insert_L; [set_solver.. | apply lookup_delete ].
Qed.

Record accessor_permutation := {
  anons_perm : Pmap positive;
  abstractions_perm : Pmap (Pmap positive);
}.

Record state_equivalence := {
  accessor_perm : accessor_permutation;
  loan_id_names : loan_id_map;
}.

Definition valid_accessor_permutation perm S :=
  is_permutation (anons_perm perm) (anons S) /\
  map_Forall2 (fun k => is_permutation) (abstractions_perm perm) (abstractions S).

Definition valid_loan_id_names (loan_map : loan_id_map) S :=
  map_inj loan_map /\ subseteq (loan_set_state S) (dom loan_map)
.

Definition is_state_equivalence perm S :=
  valid_accessor_permutation (accessor_perm perm) S /\ (valid_loan_id_names (loan_id_names perm) S).

(* Then, let us introduce renaming of anonymous binding and abstraction elements. *)
Definition rename_accessors perm S := {|
  vars := vars S;
  anons := apply_permutation (anons_perm perm) (anons S);
  abstractions :=
    map_zip_with (fun p A => apply_permutation p A) (abstractions_perm perm) (abstractions S);
|}.

Notation rename_set perm := (fmap (rename_value perm)).

Definition rename_state perm S := {|
  vars := rename_set perm (vars S);
  anons := rename_set perm (anons S);
  abstractions := fmap (M := Pmap) (rename_set perm) (abstractions S)
|}.

(* A state permutation is simply the composition of the renaming of loan identifiers, and the
 * permutation of anonymous bindings and abstraction names. *)
Definition apply_state_permutation perm S :=
  rename_accessors (accessor_perm perm) (rename_state (loan_id_names perm) S).

(* Renaming accessors and loan identifiers are completely orthogonal operations. *)
Lemma rename_state_preserves_accessor_perm_validity r perm S :
  valid_accessor_permutation perm (rename_state r S) <-> valid_accessor_permutation perm S.
Proof.
  split.
  - intros (H & G). split.
    + eapply is_permutation_dom_eq; [apply dom_fmap_L | exact H].
    + intros i. specialize (G i). cbn in G. simpl_map.
      destruct (lookup i (abstractions S)); [ | exact G].
      inversion G. constructor. eapply is_permutation_dom_eq; [apply dom_fmap_L | eassumption].
  - intros (H & G). split.
    + apply is_permutation_fmap. exact H.
    + intros i. specialize (G i). cbn. simpl_map. inversion G; constructor.
      apply is_permutation_fmap. assumption.
Qed.

Lemma rename_accessors_rename_state_commute p0 p1 S :
  valid_accessor_permutation p1 S ->
  rename_accessors p1 (rename_state p0 S) = rename_state p0 (rename_accessors p1 S).
Proof.
  intros ((H & ?) & G). unfold rename_accessors, rename_state. cbn. f_equal.
  - apply pkmap_fmap, map_inj_equiv. assumption.
  - rewrite map_zip_with_fmap_2, map_fmap_zip_with. apply map_eq.
    intros i. specialize (G i). rewrite !map_lookup_zip_with.
    inversion G as [? ? (? & _) | ]; [ | reflexivity]. cbn. f_equal.
    apply pkmap_fmap, map_inj_equiv. assumption.
Qed.

Corollary apply_state_permutation_alt perm S :
  valid_accessor_permutation (accessor_perm perm) S ->
  apply_state_permutation perm S =
  rename_state (loan_id_names perm) (rename_accessors (accessor_perm perm) S).
Proof. apply rename_accessors_rename_state_commute. Qed.

Lemma get_extra_rename_state perm S :
  get_extra (rename_state perm S) = get_extra S.
Proof. apply dom_fmap_L. Qed.

Lemma get_extra_rename_accessors perm S :
  valid_accessor_permutation perm S -> get_extra (rename_accessors perm S) = get_extra S.
Proof.
  intros (_ & Habstractions_equiv). unfold get_extra. cbn. rewrite dom_map_zip_with_L.
  apply map_Forall2_dom_L in Habstractions_equiv. rewrite Habstractions_equiv. set_solver.
Qed.

Lemma get_extra_state_permutation perm S :
  is_state_equivalence perm S -> get_extra (apply_state_permutation perm S) = get_extra S.
Proof.
  intros (? & _). rewrite apply_state_permutation_alt by assumption.
  rewrite get_extra_rename_state, get_extra_rename_accessors; auto.
Qed.

(* Applying a permutation to an accessor. *)
Definition permutation_accessor (perm : accessor_permutation) acc : option positive :=
  match decode' (A := positive + positive * positive) acc with
  | Some (inl i) =>
      match decode' (A := var + anon) i with
      | Some (inl _) => Some acc
      | Some (inr a) => option_map anon_accessor (lookup a (anons_perm perm))
      | None => None
      end
  | Some (inr (i, j)) =>
      option_map (fun k => encode_abstraction (i, k)) (mbind (lookup j) (lookup i (abstractions_perm perm)))
  | None => None
  end.

(* In order to show that permutation_accessor is injective, we are going to give a caracteziration
 * of it as a relation. *)
Variant permutation_accessor_rel perm : positive -> positive -> Prop :=
  | PA_Var x : permutation_accessor_rel perm (encode_var x) (encode_var x)
  | PA_Anon a b (get_a : lookup a (anons_perm perm) = Some b) :
      permutation_accessor_rel perm (encode_anon a) (encode_anon b)
  | PA_Abstraction i j p j' (get_i : lookup i (abstractions_perm perm) = Some p)
      (get_j : lookup j p = Some j') :
      permutation_accessor_rel perm (encode_abstraction (i, j)) (encode_abstraction (i, j'))
.

Lemma permutation_accessor_is_Some perm acc acc' :
  permutation_accessor perm acc = Some acc' -> permutation_accessor_rel perm acc acc'.
Proof.
  unfold permutation_accessor. intros H.
    destruct (decode' acc) as [i | ] eqn:EQN; [ | discriminate].
    rewrite decode'_is_Some in EQN. subst.
    destruct i as [i | (i & j)].
    - destruct (decode' i) as [i' | ] eqn:EQN; [ | discriminate].
      rewrite decode'_is_Some in EQN. subst.
      destruct i'.
      + inversion H. constructor.
      + destruct (lookup a (anons_perm perm)) eqn:?; [ | discriminate].
        inversion H. constructor. assumption.
    - destruct (lookup i (abstractions_perm perm)) as [A | ] eqn:?; [ | discriminate]. cbn in H.
      destruct (lookup j A) as [j' | ] eqn:?; [ | discriminate]. cbn in H. inversion H.
      econstructor; eassumption.
Qed.

Lemma permutation_accessor_inj perm S :
  valid_accessor_permutation perm S -> partial_inj (permutation_accessor perm).
Proof.
  intros ((inj_anons_perm & _) & inj_abstractions_perm).
  intros i Some_i j Hij. pose proof Some_i as Some_j. rewrite Hij in Some_j.
  destruct Some_i as (i' & Some_i). destruct Some_j as (j' & Some_j).
  rewrite Some_i, Some_j in Hij. inversion Hij; subst.
  apply permutation_accessor_is_Some in Some_i, Some_j.
  destruct Some_i.
  - inversion Some_j. f_equal. eapply encode_inj. congruence.
  - inversion Some_j. f_equal. eapply inj_anons_perm; [eassumption.. | ].
    eapply encode_inj. auto.
  - specialize (inj_abstractions_perm i).
    inversion inj_abstractions_perm as [q A (inj_p & _) | ]; [ | congruence].
    replace q with p in * by congruence.
    inversion Some_j as [| | i'' ? q' ? get_i'' ? _H eq_encode].
    f_equal. apply encode_inj in eq_encode. inversion eq_encode. subst. f_equal.
    rewrite get_i in get_i''. replace q' with p in * by congruence.
    eapply inj_p; [eassumption.. | congruence].
Qed.

Lemma permutation_accessor_is_equivalence S perm :
  valid_accessor_permutation perm S -> is_equivalence (permutation_accessor perm) (get_map S).
Proof.
  intros Hperm. split.
  - eapply permutation_accessor_inj. eassumption.
  - destruct Hperm as ((_ & dom_anons_perm) & inj_abstractions_perm).
    unfold get_map, permutation_accessor. cbn. intros i.
    intros [(i' & -> & Hi') | ((i' & j') & -> & Hij')]%sum_maps_is_Some.
    + rewrite decode'_encode.
      apply sum_maps_is_Some in Hi'.
      destruct Hi' as [(? & -> & _) | (? & -> & G)]; rewrite decode'_encode.
      * auto.
      * rewrite <-dom_anons_perm in G. destruct G as (? & G). setoid_rewrite G. auto.
    + rewrite decode'_encode. revert Hij'. rewrite lookup_flatten.
      specialize (inj_abstractions_perm i').
      inversion inj_abstractions_perm as [? A (_ & dom_A) | ];
          [ | intros (? & ?); discriminate].
      cbn. rewrite <-dom_A. intros (? & ->). auto.
Qed.

Lemma perm_at_var perm v : permutation_accessor perm (encode_var v) = Some (encode_var v).
Proof. unfold permutation_accessor, encode_var. rewrite !decode'_encode. reflexivity. Qed.

Lemma perm_at_anon perm a :
  permutation_accessor perm (anon_accessor a) =
  option_map anon_accessor (lookup a (anons_perm perm)).
Proof.
  unfold permutation_accessor, anon_accessor. cbn. unfold encode_anon.
  rewrite !decode'_encode. reflexivity.
Qed.

Lemma perm_at_abstraction perm i j :
  permutation_accessor perm (encode_abstraction (i, j)) =
  option_map (fun j' => encode_abstraction (i, j')) (mbind (lookup j) (lookup i (abstractions_perm perm))).
Proof. unfold permutation_accessor, encode_abstraction. rewrite decode'_encode. reflexivity. Qed.

Lemma abstraction_rename_accessors perm S i p A :
  lookup i (abstractions_perm perm) = Some p ->
  lookup i (abstractions S) = Some A ->
  lookup i (abstractions (rename_accessors perm S)) = Some (apply_permutation p A).
Proof.
  intros H G.  unfold apply_state_permutation. cbn.
  apply map_lookup_zip_with_Some. eexists _, _. eauto.
Qed.

(* The main property of rename_accessors. *)
Lemma get_map_rename_accessors perm S (H : valid_accessor_permutation perm S) :
  get_map (rename_accessors perm S) = pkmap (permutation_accessor perm) (get_map S).
Proof.
  symmetry. apply pkmap_eq.
  - apply permutation_accessor_is_equivalence. assumption.
  - destruct H as ((anons_perm_inj & _) & Habs_perm).
    intros ? ? G%permutation_accessor_is_Some.
    destruct G as [ | | i ? p ? get_p_i].
    + rewrite !get_at_var. reflexivity.
    + rewrite !get_at_anon. unfold apply_state_permutation; cbn.
      erewrite lookup_pkmap by (rewrite <-?map_inj_equiv; eassumption). reflexivity.
    + rewrite !get_at_abstraction.
      specialize (Habs_perm i). rewrite get_p_i in Habs_perm.
      inversion Habs_perm as [? A (? & _) _p get_A_i | ]; subst.
      erewrite abstraction_rename_accessors by eauto.
      symmetry. apply lookup_pkmap; rewrite <-?map_inj_equiv; assumption.
  - destruct H as (Hanons_perm & Habs_perm).
    unfold get_map. cbn. rewrite !size_sum_maps.
    rewrite size_pkmap by now apply permutation_is_equivalence. f_equal.
    apply size_flatten.
    intros i. rewrite map_lookup_zip_with. specialize (Habs_perm i). destruct Habs_perm.
    + constructor. symmetry. apply size_pkmap, permutation_is_equivalence. assumption.
    + constructor.
Qed.

Lemma get_map_rename_state perm S :
  get_map (rename_state perm S) = fmap (rename_value perm) (get_map S).
Proof.
  apply map_eq. intros i. unfold rename_state. simpl_map.
  destruct (get_at_accessor S i) eqn:EQN.
  - destruct (get_at_accessor_is_Some S i); [auto | ..].
    + rewrite get_at_var in *. cbn. simpl_map. cbn. congruence.
    + rewrite get_at_anon in *. cbn. simpl_map. cbn. congruence.
    + rewrite get_at_abstraction in *. revert EQN. cbn. simpl_map. cbn. simpl_map.
      intros ->. reflexivity.
  - apply eq_None_not_Some. intros H. apply get_at_accessor_is_Some in H.
    inversion H; subst.
    + cbn -[get_map] in * |-. simpl_map. rewrite get_at_var in * |-. rewrite EQN in *.
      discriminate.
    + cbn -[get_map] in * |-. simpl_map. rewrite get_at_anon in * |-. rewrite EQN in *.
      discriminate.
    + cbn -[get_map] in * |-. simpl_map. rewrite get_at_abstraction in * |-.
      destruct (lookup _ (abstractions S)).
      * injection get_A. intros G%(f_equal (lookup j)). simpl_map.
        cbn in EQN. rewrite EQN, get_v in G. discriminate.
      * discriminate.
Qed.

Lemma get_map_state_permutation S perm (H : valid_accessor_permutation (accessor_perm perm) S) :
  get_map (apply_state_permutation perm S) =
  rename_set (loan_id_names perm) (pkmap (permutation_accessor (accessor_perm perm)) (get_map S)).
Proof.
  rewrite apply_state_permutation_alt by assumption.
  rewrite get_map_rename_state, get_map_rename_accessors by assumption. reflexivity.
Qed.

Corollary get_at_accessor_rename_accessors perm S i v (H : valid_accessor_permutation perm S) :
  get_at_accessor S i = Some v ->
  exists j, permutation_accessor perm i = Some j /\
  get_at_accessor (rename_accessors perm S) j = Some v.
Proof.
  intros G. rewrite get_map_rename_accessors by assumption.
  apply permutation_accessor_is_equivalence in H.
  destruct H as (inj_perm & H). edestruct H; [eauto | ].
  eexists. split; [eassumption | ]. erewrite lookup_pkmap; [ | eassumption..].
  rewrite G. reflexivity.
Qed.

Corollary get_at_accessor_state_permutation perm S i v
  (H : valid_accessor_permutation (accessor_perm perm) S) :
  get_at_accessor S i = Some v ->
  exists j, permutation_accessor (accessor_perm perm) i = Some j /\
  get_at_accessor (apply_state_permutation perm S) j = Some (rename_value (loan_id_names perm) v).
Proof.
  rewrite apply_state_permutation_alt by assumption.
  rewrite get_map_rename_state. setoid_rewrite lookup_fmap.
  intros ?. edestruct get_at_accessor_rename_accessors as (j & ? & Hj); [eassumption.. | ].
  exists j. rewrite Hj. auto.
Qed.

(* Two states are equivalent if one is the permutation of the other. *)
Definition equiv_states S0 S1 :=
  exists perm, is_state_equivalence perm S0 /\ S1 = apply_state_permutation perm S0.

(* Sometimes, we just need to reason about renaming accessors or loan identifiers individually. *)
Definition equiv_states_up_to_loan_renaming S0 S1 :=
  exists r, valid_loan_id_names r S0 /\ S1 = rename_state r S0.

Definition equiv_states_up_to_accessor_permutation S0 S1 :=
  exists perm, valid_accessor_permutation perm S0 /\ S1 = rename_accessors perm S0.

Lemma prove_equiv_states S0 S1 S2 :
  equiv_states_up_to_loan_renaming S0 S1 ->
  equiv_states_up_to_accessor_permutation S1 S2 ->
  equiv_states S0 S2.
Proof.
  intros (r & Hr & ->) (perm & Hperm & ->).
  exists {|accessor_perm := perm; loan_id_names := r|}. split.
  - split; [ | assumption].
    rewrite rename_state_preserves_accessor_perm_validity in Hperm. exact Hperm.
  - reflexivity.
Qed.

Definition equiv_val_state (vS0 vS1 : LLBC_plus_val * LLBC_plus_state) :=
  let (v0, S0) := vS0 in
  let (v1, S1) := vS1 in
  exists perm, is_state_equivalence perm S0 /\
               subseteq (loan_set_val v0) (dom (loan_id_names perm)) /\
               S1 = apply_state_permutation perm S0 /\ v1 = rename_value (loan_id_names perm) v0.

Definition _permutation_spath (perm : accessor_permutation) (sp : spath) : spath :=
  match permutation_accessor perm (fst sp) with
  | Some j => (j, snd sp)
  | None => sp
  end.
Notation permutation_spath perm := (_permutation_spath (accessor_perm perm)).

(** * Properties of LLBC+ operations. *)
Instance Decidable_in_abstraction i x : Decision (in_abstraction i x).
Proof.
  unfold in_abstraction, encode_abstraction.
  destruct (decode' (A := positive + positive * positive) x) as [[ | (i' & j)] | ] eqn:EQN.
  - right. intros (j & H). rewrite H, decode'_encode in EQN. discriminate.
  - destruct (decide (i = i')) as [<- | ].
    + left. exists j. apply decode'_is_Some in EQN. congruence.
    + right. intros (? & H). rewrite H, decode'_encode in EQN. congruence.
  - right. intros (? & H). rewrite H, decode'_encode in EQN. discriminate.
Qed.

Lemma var_not_in_abstraction p x : fst p = encode_var x -> not_in_abstraction p.
Proof.
  unfold not_in_abstraction, in_abstraction. intros H ? (? & G).
  rewrite G in H. inversion H.
Qed.

Lemma anon_not_in_abstraction p a : fst p = anon_accessor a -> not_in_abstraction p.
Proof.
  unfold not_in_abstraction, in_abstraction. intros H ? (? & G).
  rewrite G in H. inversion H.
Qed.
Hint Resolve anon_not_in_abstraction : spath.

Lemma add_abstraction_commute S i j A B :
  i <> j -> S,,, i |-> A,,, j |-> B = S,,, j |-> B,,, i |-> A.
Proof. intros ?. unfold add_abstraction. cbn. f_equal. apply insert_commute. congruence. Qed.

Lemma get_at_accessor_add_abstraction S i j A :
  get_at_accessor (S,,, i |-> A) (encode_abstraction (i, j)) = lookup j A.
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_lookup_r.
  rewrite <-insert_delete_insert, flatten_insert by now simpl_map.
  rewrite lookup_union_l.
  - rewrite lookup_kmap by typeclasses eauto. reflexivity.
  - apply lookup_None_flatten. simpl_map. reflexivity.
Qed.

(* The hypothesis [fresh_abstraction S i] is not necessary, we're going to remove it. *)
Lemma _get_at_accessor_add_abstraction_notin S i A x (fresh_i : fresh_abstraction S i)
  (H : ~in_abstraction i x) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  unfold get_map. cbn.
  rewrite flatten_insert' by assumption. rewrite sum_maps_union.
  rewrite lookup_union_l; [reflexivity | ].
  rewrite eq_None_not_Some. rewrite lookup_kmap_is_Some by typeclasses eauto.
  intros (p & ? & G). rewrite lookup_kmap_is_Some in G by typeclasses eauto.
  destruct G as (j & -> & _). eapply H. firstorder.
Qed.

Lemma get_map_add_abstraction S i A (H : fresh_abstraction S i) :
  get_map (S,,, i |-> A) = union (get_map S) (kmap (fun j => encode_abstraction (i, j)) A).
Proof.
  cbn. rewrite flatten_insert' by assumption. rewrite sum_maps_union. f_equal.
  apply kmap_compose; typeclasses eauto.
Qed.

Lemma add_remove_abstraction i A S (H : lookup i (abstractions S) = Some A) :
  (remove_abstraction i S),,, i |-> A = S.
Proof.
  unfold add_abstraction, remove_abstraction.
  destruct S. cbn. f_equal. apply insert_delete in H. exact H.
Qed.

Lemma remove_add_abstraction i A S (H : fresh_abstraction S i) :
  remove_abstraction i (S,,, i |-> A) = S.
Proof.
  unfold add_abstraction, remove_abstraction.
  destruct S. cbn. f_equal. apply delete_insert. assumption.
Qed.

Lemma remove_add_abstraction_ne i j A S :
  i <> j -> remove_abstraction i (S,,, j |-> A) = remove_abstraction i S,,, j |-> A.
Proof.
  unfold add_abstraction, remove_abstraction.
  intros ?. destruct S. cbn. f_equal. apply delete_insert_ne. assumption.
Qed.

Lemma add_remove_add_abstraction S i A : (remove_abstraction i S),,, i |-> A = S,,, i |-> A.
Proof. unfold add_abstraction, remove_abstraction. cbn. f_equal. apply insert_delete_insert. Qed.

Lemma get_at_accessor_add_abstraction_notin S i A x (H : ~in_abstraction i x) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN at 2. rewrite <-add_remove_add_abstraction.
    rewrite !_get_at_accessor_add_abstraction_notin; auto; apply lookup_delete.
  - apply _get_at_accessor_add_abstraction_notin; assumption.
Qed.

Lemma sget_add_abstraction_notin S i A p : ~in_abstraction i (fst p) -> (S,,, i |-> A).[p] = S.[p].
Proof. intros H. unfold sget. rewrite get_at_accessor_add_abstraction_notin; auto. Qed.

Lemma sget_add_abstraction S i j A v p :
  lookup j A = Some v -> (S,,, i |-> A).[(encode_abstraction (i, j), p)] = v.[[p]].
Proof.
  unfold sget. replace (fst _) with (encode_abstraction (i, j)) by reflexivity.
  rewrite get_at_accessor_add_abstraction. intros ->. reflexivity.
Qed.

Lemma get_extra_add_abstraction S i A :
  get_extra (S,,, i |-> A) = (union (singleton i) (get_extra S)).
Proof. unfold get_extra. cbn. rewrite dom_insert_L. reflexivity. Qed.

Lemma sset_add_abstraction_notin S i A p v :
  ~in_abstraction i (fst p) -> (S,,, i |-> A).[p <- v] = S.[p <- v],,, i |-> A.
Proof.
  intros ?. unfold sset. apply state_eq_ext.
  - apply map_eq. intros x.
    destruct (decide (fst p = x)) as [<- | ].
    + rewrite get_map_alter, lookup_alter.
      rewrite !get_at_accessor_add_abstraction_notin by assumption.
      rewrite get_map_alter, lookup_alter. reflexivity.
    + rewrite get_map_alter, lookup_alter_ne by auto.
      destruct (decide (in_abstraction i x)) as [(j & ->) | ].
      * rewrite !get_at_accessor_add_abstraction. reflexivity.
      * rewrite !get_at_accessor_add_abstraction_notin by assumption.
        rewrite get_map_alter, lookup_alter_ne by assumption. reflexivity.
  - rewrite get_extra_alter, !get_extra_add_abstraction, get_extra_alter. reflexivity.
Qed.

Lemma sset_add_abstraction S i j A p v :
  (S,,, i |-> A).[(encode_abstraction (i, j), p) <- v] = S,,, i |-> (alter (vset p v) j A).
Proof.
  unfold add_abstraction, encode_abstraction. cbn. rewrite decode'_encode, alter_insert.
  reflexivity.
Qed.

Lemma fresh_anon_add_abstraction S a i A : fresh_anon (S,,, i |-> A) a <-> fresh_anon S a.
Proof. unfold fresh_anon. rewrite !get_at_anon. reflexivity. Qed.

Hint Resolve<- fresh_anon_add_abstraction : spath.

Lemma fresh_anon_remove_abstraction_value S a i j :
  fresh_anon (remove_abstraction_value S i j) a <-> fresh_anon S a.
Proof. unfold fresh_anon. rewrite !get_at_anon. reflexivity. Qed.
Hint Resolve<- fresh_anon_remove_abstraction_value : spath.

Lemma fresh_abstraction_remove_abstraction_value S i i' j :
  fresh_abstraction (remove_abstraction_value S i j) i' <-> fresh_abstraction S i'.
Proof. unfold fresh_abstraction, remove_abstraction_value. cbn. apply lookup_alter_None. Qed.
Hint Resolve<- fresh_abstraction_remove_abstraction_value : spath.

Lemma fresh_abstraction_add_abstraction S i j A :
  fresh_abstraction S i -> fresh_abstraction S j -> i <> j ->
  fresh_abstraction (S,,, i |-> A) j.
Proof. unfold fresh_abstraction, add_abstraction. cbn. intros. simpl_map. assumption. Qed.
Hint Resolve fresh_abstraction_add_abstraction : spath.

Lemma fresh_abstraction_add_abstraction_rev S i j A :
  fresh_abstraction (S,,, i |-> A) j -> fresh_abstraction S j /\ i <> j.
Proof. unfold fresh_abstraction, add_abstraction. cbn. now rewrite lookup_insert_None. Qed.

Lemma fresh_abstraction_sset S p v i :
  fresh_abstraction S i <-> fresh_abstraction (S.[p <- v]) i.
Proof.
  unfold fresh_abstraction. rewrite<-!not_elem_of_dom.
  replace (dom (abstractions S)) with (get_extra S) by reflexivity.
  replace (dom (abstractions (S.[p <- v]))) with (get_extra (S.[p <- v])) by reflexivity.
  unfold sset. rewrite get_extra_alter. reflexivity.
Qed.

Lemma fresh_abstraction_add_anon S a v i :
  fresh_abstraction S i <-> fresh_abstraction (S,, a |-> v) i.
Proof. split; intros H; exact H. Qed.

Hint Resolve-> fresh_abstraction_sset : spath.
Hint Resolve-> fresh_abstraction_add_anon : spath.
Hint Rewrite <-fresh_abstraction_add_anon : spath.

Hint Rewrite sget_add_abstraction_notin using auto; fail : spath.
Hint Rewrite sset_add_abstraction_notin using auto with spath; fail : spath.

Lemma abstractions_remove_abstraction_value S i j :
  flatten (abstractions (remove_abstraction_value S i j)) =
  delete (i, j) (flatten (abstractions S)).
Proof.
  unfold remove_abstraction_value. cbn.
  apply map_eq. intros (a & b). destruct (decide (i = a)) as [<- | ].
  - rewrite lookup_flatten. rewrite lookup_alter.
    rewrite option_fmap_bind.
    destruct (decide (j = b)) as [<- | ].
    + rewrite lookup_delete.
      erewrite option_bind_ext_fun by (intros ?; apply lookup_delete).
      destruct (lookup i (abstractions S)); reflexivity.
    + rewrite lookup_delete_ne by congruence. rewrite lookup_flatten.
      apply option_bind_ext_fun. intros ?. apply lookup_delete_ne. assumption.
  - rewrite lookup_delete_ne by congruence. rewrite !lookup_flatten.
    rewrite lookup_alter_ne by assumption. reflexivity.
Qed.

Lemma get_map_remove_abstraction_value S i j :
  get_map (remove_abstraction_value S i j) = delete (encode_abstraction (i, j)) (get_map S).
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_delete_inr. rewrite <-abstractions_remove_abstraction_value. reflexivity.
Qed.

Lemma get_extra_remove_abstraction_value S i j :
  get_extra (remove_abstraction_value S i j) = get_extra S.
Proof. unfold get_extra. cbn. rewrite dom_alter_L. reflexivity. Qed.

Lemma sget_remove_abstraction_value S i j p (H : fst p <> encode_abstraction (i, j)) :
  (remove_abstraction_value S i j).[p] = S.[p].
Proof. unfold sget. rewrite get_map_remove_abstraction_value. simpl_map. reflexivity. Qed.

Lemma not_in_abstraction_is_not_encode_abstraction sp i j :
  not_in_abstraction sp -> fst sp <> encode_abstraction (i, j).
Proof. intros H G. eapply H. rewrite G. exists j. reflexivity. Qed.
Hint Resolve not_in_abstraction_is_not_encode_abstraction : spath.

Lemma sset_remove_abstraction_value S i j p v (H : fst p <> encode_abstraction (i, j)) :
  remove_abstraction_value (S.[p <-v]) i j = (remove_abstraction_value S i j).[p <- v].
Proof.
  apply state_eq_ext.
  - unfold sset. rewrite get_map_remove_abstraction_value. rewrite !get_map_alter.
    rewrite get_map_remove_abstraction_value. apply delete_alter_ne. congruence.
  - unfold sset. rewrite get_extra_alter, !get_extra_remove_abstraction_value, get_extra_alter.
    reflexivity.
Qed.

Lemma remove_abstraction_value_valid S sp i j :
  valid_spath S sp -> fst sp <> encode_abstraction (i, j) ->
  valid_spath (remove_abstraction_value S i j) sp.
Proof.
  intros (v & ? & ?) ?. exists v. split; [ | assumption].
  rewrite get_map_remove_abstraction_value. simpl_map. reflexivity.
Qed.
Hint Resolve remove_abstraction_value_valid : spath.

Lemma add_abstraction_add_anon S a v i A : (S,, a |-> v),,, i |-> A = (S,,, i |-> A),, a |-> v.
Proof. reflexivity. Qed.

Lemma remove_abstraction_value_add_anon S a v i j :
  remove_abstraction_value (S,, a |-> v) i j = (remove_abstraction_value S i j),, a |-> v.
Proof. reflexivity. Qed.

Lemma abstraction_element_remove_abstraction_value_is_Some S i j i' j' v :
  abstraction_element (remove_abstraction_value S i j) i' j' = Some v <->
  abstraction_element S i' j' = Some v /\ (i, j) <> (i', j').
Proof.
  unfold abstraction_element. rewrite get_map_remove_abstraction_value. split.
  - intros (? & ?)%lookup_delete_Some. split; congruence.
  - intros (? & ?). rewrite lookup_delete_ne; [assumption | ]. intros [=-> ->]%encode_inj. auto.
Qed.

Lemma abstraction_element_remove_abstraction S i j i' j' :
  (i, j) <> (i', j') ->
  abstraction_element (remove_abstraction_value S i j) i' j' = abstraction_element S i' j'.
Proof.
  intros ?. unfold abstraction_element. rewrite get_map_remove_abstraction_value.
  apply lookup_delete_ne. intros [=-> ->]%encode_inj. auto.
Qed.

Lemma remove_abstraction_value_commute S i j i' j' :
  remove_abstraction_value (remove_abstraction_value S i j) i' j' =
  remove_abstraction_value (remove_abstraction_value S i' j') i j.
Proof.
  apply state_eq_ext.
  - rewrite !get_map_remove_abstraction_value. apply delete_commute.
  - rewrite !get_extra_remove_abstraction_value. reflexivity.
Qed.

Hint Rewrite sget_remove_abstraction_value using auto with spath : spath.
Hint Rewrite sset_remove_abstraction_value using eauto with spath : spath.
Hint Rewrite add_abstraction_add_anon : spath.
Hint Rewrite remove_abstraction_value_add_anon : spath.
Hint Rewrite abstraction_element_remove_abstraction_value_is_Some : spath.
Hint Rewrite abstraction_element_remove_abstraction using congruence : spath.

Lemma valid_spath_remove_abstraction_value S i j sp :
  valid_spath (remove_abstraction_value S i j) sp ->
  valid_spath S sp /\ fst sp <> encode_abstraction (i, j).
Proof.
  unfold valid_spath. rewrite get_map_remove_abstraction_value.
  intros (? & (? & ?)%lookup_delete_Some & ?). split; [eexists | ]; eauto.
Qed.

Lemma remove_abstraction_not_state_contains P S i j :
  not_state_contains P S -> not_state_contains P (remove_abstraction_value S i j).
Proof.
  intros H ? (? & ?)%valid_spath_remove_abstraction_value. autorewrite with spath.
  apply H. assumption.
Qed.
Hint Resolve remove_abstraction_not_state_contains : spath.

Lemma not_in_abstraction_valid_spath S i A sp :
  valid_spath (S,,, i |->  A) sp -> ~in_abstraction i (fst sp) -> valid_spath S sp.
Proof.
  unfold not_in_abstraction. intros (v & H & ?) ?.
  exists v. split; [ | assumption].
  rewrite <-H, get_at_accessor_add_abstraction_notin; auto.
Qed.

(* TODO: rewrite with in hypotheses a spath sp and an equality
 * [fst sp = encode_abstraction (i, j)], so as to reduce the number of destructions. *)
Lemma in_abstraction_valid_spath S i j A q :
  valid_spath (S,,, i |->  A) (encode_abstraction (i, j), q) ->
  exists v, lookup j A = Some v /\ valid_vpath v q.
Proof.
  intros (v & get_v & valid_v_q). cbn [fst snd] in *.
  rewrite get_at_accessor_add_abstraction in get_v. firstorder.
Qed.

Lemma valid_spath_add_abstraction S i A sp :
  valid_spath S sp -> fresh_abstraction S i ->
  valid_spath (S,,, i |-> A) sp /\ ~in_abstraction i (fst sp).
Proof.
  intros (v & get_v & ?) fresh_i. assert (~in_abstraction i (fst sp)).
  { intros (j & Hj). rewrite Hj in get_v. rewrite get_at_abstraction, fresh_i in get_v.
    discriminate. }
  split; [ | assumption].
  exists v. split; [ | assumption]. rewrite get_at_accessor_add_abstraction_notin; auto.
Qed.

Lemma not_state_contains_add_abstraction P S i A (fresh_i : fresh_abstraction S i) :
  not_state_contains P (S,,, i |-> A) <->
  (not_state_contains P S /\ map_Forall (fun _ => not_value_contains P) A).
Proof.
  split.
  - intros H. split.
    + intros p valid_p.
      eapply valid_spath_add_abstraction in valid_p; [ | exact fresh_i]. destruct valid_p.
      erewrite <-sget_add_abstraction_notin; eauto.
    + intros j v ? p valid_p.
      specialize (H (encode_abstraction (i, j), p)).
      erewrite sget_add_abstraction in H by eassumption. apply H.
      exists v. split; [ | assumption].
      etransitivity; [apply get_at_abstraction | ]. cbn. simpl_map. assumption.
  - intros (H & G) p valid_p. destruct (decide (in_abstraction i (fst p))) as [(j & Hj) | ].
    + destruct p. cbn in Hj. subst. destruct valid_p as (w & K & ?).
      replace (fst _) with (encode_abstraction (i, j)) in K by reflexivity.
      rewrite get_at_abstraction in K. cbn in K. simpl_map.
      erewrite sget_add_abstraction; [ | exact K]. eapply G; eassumption.
    + rewrite sget_add_abstraction_notin by assumption. apply H.
      eapply not_in_abstraction_valid_spath; eassumption.
Qed.

Lemma vget_at_borrow l v : borrow^m(l, v).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite vget_at_borrow : spath.
Lemma vget_at_borrow' l v p : borrow^m(l, v).[[ [0] ++ p]] = v.[[p]].
Proof. reflexivity. Qed.
Lemma vset_at_borrow l v w : borrow^m(l, v).[[ [0] <- w]] = borrow^m(l, w).
Proof. reflexivity. Qed.
Lemma vset_at_borrow' l p v w : borrow^m(l, v).[[ 0 :: p <- w]] = borrow^m(l, v.[[p <- w]]).
Proof. reflexivity. Qed.

Hint Rewrite vget_at_borrow' : spath.
Hint Rewrite sset_same : spath.
Hint Rewrite app_nil_l : spath.
Hint Rewrite vset_at_borrow : spath.

(* When changing the id of a mutable borrow at p, generally using the rule Leq_Reborrow_MutBorrow,
 * accessing any other node that the one in sp is unchanged. *)
Lemma get_node_rename_mut_borrow S p q l1
  (H : is_mut_borrow (get_node (S.[p]))) (diff_p_q : p <> q) :
  get_node ((rename_mut_borrow S p l1).[q]) = get_node (S.[q]).
Proof.
  destruct (get_node (S.[p])) eqn:G; inversion H. subst.
  destruct (decidable_prefix p q).
  - assert (strict_prefix p q) as (i & ? & <-) by solve_comp.
    autorewrite with spath. destruct i.
    + cbn. autorewrite with spath. reflexivity.
    (* If i > 0, then the path q is invalid. *)
    + cbn. rewrite sget_app.
      apply (f_equal arity) in G. rewrite<- length_children_is_arity in G.
      apply length_1_is_singleton in G. cbn - [children]. destruct G as (? & ->).
      reflexivity.
  - autorewrite with spath. reflexivity.
Qed.

Hint Extern 0 (is_mut_borrow (get_node (?S.[?sp]))) =>
  lazymatch goal with
  | H : get_node (?S.[?sp]) = borrowC^m(_) |- is_mut_borrow (get_node (?S.[?sp])) =>
      rewrite H; constructor
  end : spath.
Hint Rewrite get_node_rename_mut_borrow using eauto with spath; fail : spath.

(* In the state [rename_mut_borrow S p l1], compared to S, only the node at p is changed.
 * Thus, if we read at a place q that is not a prefix of p, no node is changed. *)
Lemma sget_reborrow_mut_borrow_not_prefix S p q l1
  (H : is_mut_borrow (get_node (S.[p]))) (G : ~prefix q p) :
  (rename_mut_borrow S p l1).[q] = S.[q].
Proof.
  destruct (get_node (S.[p])) eqn:?; inversion H. subst.
  apply value_get_node_ext. intros r. rewrite <-!sget_app.
  eapply get_node_rename_mut_borrow.
  - auto with spath.
  - intros ->. apply G. exists r. reflexivity.
Qed.
Hint Rewrite sget_reborrow_mut_borrow_not_prefix using eauto with spath; fail : spath.

Lemma valid_spath_rename_mut_borrow S p q l0 l1
  (H : get_node (S.[p]) = borrowC^m(l0)) :
  valid_spath (rename_mut_borrow S p l1) q <-> valid_spath S q.
Proof.
  split.
  - intros valid_q. destruct (decidable_prefix (p +++ [0]) q) as [(r & <-) | ].
    + rewrite valid_spath_app in *. destruct valid_q as (_ & valid_r). split.
      * apply valid_spath_app_last_get_node_not_zeroary. rewrite H. constructor.
      * autorewrite with spath in valid_r. exact valid_r.
    + rewrite sset_not_prefix_valid. exact valid_q.
      eapply (not_prefix_one_child (rename_mut_borrow S p l1)); [ | eassumption..].
      rewrite length_children_is_arity. autorewrite with spath. reflexivity.
  - intros valid_q. destruct (decidable_prefix (p +++ [0]) q) as [(r & <-) | ].
    + autorewrite with spath in *. rewrite valid_spath_app in *. split.
      * validity.
      * econstructor.
        -- autorewrite with spath. reflexivity.
        -- apply valid_spath_app. autorewrite with spath. rewrite valid_spath_app. auto.
    + rewrite <-sset_not_prefix_valid by solve_comp. assumption.
Qed.

Lemma sset_reborrow_mut_borrow_not_prefix S p q l1 v
  (H : is_mut_borrow (get_node (S.[p]))) (G : ~prefix q p) :
  (rename_mut_borrow S p l1).[q <- v] = rename_mut_borrow (S.[q <- v]) p l1.
Proof.
  destruct (get_node (S.[p])) eqn:?; inversion H. subst. destruct (decidable_valid_spath S q).
  - destruct (decidable_prefix p q) as [ | ].
    + assert (prefix (p +++ [0]) q) as (r & <-) by solve_comp.
      autorewrite with spath. reflexivity.
    + assert (disj p q) by solve_comp. states_eq.
  - rewrite !(sset_invalid _ q); erewrite ?valid_spath_rename_mut_borrow; eauto.
Qed.
Hint Rewrite sset_reborrow_mut_borrow_not_prefix using solve_comp; fail : spath.

Lemma not_contains_rename_mut_borrow S p q l0 l1 P :
  get_node (S.[p]) = borrowC^m(l0) -> ~P (borrowC^m(l0)) ->
  not_value_contains P ((rename_mut_borrow S p l1).[q]) -> not_value_contains P (S.[q]).
Proof.
  destruct (decidable_valid_spath S q) as [valid_q | ].
  - intros get_at_p ? Hnot_contains r valid_r.
    specialize (Hnot_contains r). rewrite <-!sget_app in *.
    destruct (decidable_spath_eq p (q +++ r)) as [-> | ].
    + autorewrite with spath. rewrite get_at_p. assumption.
    + autorewrite with spath in Hnot_contains.
      apply Hnot_contains. apply valid_spath_app.
      rewrite valid_spath_rename_mut_borrow by eassumption.
      rewrite valid_spath_app. auto.
  - intros ? ?. rewrite !sget_invalid; [auto.. | ].
    intros G. apply H. erewrite valid_spath_rename_mut_borrow in G by eassumption. exact G.
Qed.

Lemma exists_fresh_loan_id S : exists l, is_fresh l S.
Proof.
  destruct (exist_fresh (loan_set_state S)) as (l & Hl).
  rewrite elem_of_loan_set_state in Hl.
  exists l. intros p ? get_l. apply Hl. exists p. exact get_l.
Qed.

Lemma is_fresh_rename_mut_borrow S p l l0 l1 :
  get_node (S.[p]) = borrowC^m(l0) -> l <> l0 ->
  is_fresh l (rename_mut_borrow S p l1) -> is_fresh l S.
Proof.
  intros get_l0 Hdiff fresh_l q valid_q. destruct (decidable_spath_eq p q) as [<- | ].
  - rewrite get_l0. eauto with spath.
  - specialize (fresh_l q). autorewrite with spath in fresh_l. apply fresh_l.
    erewrite valid_spath_rename_mut_borrow; eassumption.
Qed.

Lemma not_in_borrow_rename_mut_borrow S p q l0 l1 :
  get_node (S.[p]) = borrowC^m(l0) ->
  not_in_borrow (rename_mut_borrow S p l1) q -> not_in_borrow S q.
Proof.
  intros ? H r ?. apply H.
  destruct (decidable_spath_eq p r) as [<- | ].
  - autorewrite with spath. constructor.
  - erewrite get_node_rename_mut_borrow; auto with spath.
Qed.
Hint Resolve not_in_borrow_rename_mut_borrow : spath.

Lemma loan_contains_loan ty l : ~not_contains_loan (loan^m(ty, l)).
Proof. intros H. apply (H []); constructor. Qed.

(** ** Lemmas about add_anons. *)
Lemma add_anons_delete S i A v S' :
  lookup i A = None -> add_anons S (insert i v A) S' ->
  exists a, fresh_anon S a /\ add_anons (S,, a |-> v) A S'.
Proof.
  intros ? H. inversion H as [? ? ? Hunion]; subst.
  apply union_maps_insert_r_l in Hunion; [ | assumption].
  destruct Hunion as (a & G & fresh_a).
  exists a. unfold fresh_anon. rewrite get_at_anon. split; [assumption | ].
  replace (insert _ _ _) with (anons (S,, a |-> v)) in G by reflexivity.
  apply AddAnons in G. exact G.
Qed.

Lemma add_anons_insert S A S' i v a :
  fresh_anon S' a -> lookup i A = None -> add_anons S A S' ->
  add_anons S (insert i v A) (S',, a |-> v).
Proof.
  unfold fresh_anon. rewrite get_at_anon. intros fresh_a ? H. inversion H. subst.
  unfold add_anon. cbn in *. constructor. eapply UnionInsert with (j := a).
  - rewrite eq_None_not_Some. intros (w & G). eapply union_contains_left in G; [ | eassumption].
    assert (Some w = None). { rewrite <-fresh_a, <-G. reflexivity. } discriminate.
  - assumption.
  - apply union_maps_insert_l; assumption.
Qed.

Lemma add_anons_empty S S' : add_anons S empty S' -> S = S'.
Proof.
  intros H. destruct S. inversion H as [? ? ? G]; subst. inversion G; subst; cbn in *.
  - reflexivity.
  - exfalso. eapply insert_non_empty. eassumption.
Qed.

Lemma add_anons_singleton S i v S' : add_anons S (singletonM i v) S' ->
  exists a, fresh_anon S a /\ S' = S,, a |-> v.
Proof.
  intros (a & fresh_a & H)%add_anons_delete; [ | now simpl_map].
  exists a. split; [assumption | ]. apply add_anons_empty in H. congruence.
Qed.

(* An alternative definition of add_anon. *)
Inductive add_anons' : LLBC_plus_state -> Pmap LLBC_plus_val -> LLBC_plus_state -> Prop :=
  | AddAnons_empty S : add_anons' S empty S
  | AddAnons_insert S A S' a i v :
      lookup i A = None -> fresh_anon S a -> add_anons' (S,, a |-> v) A S' ->
          add_anons' S (insert i v A) S'
.

Lemma add_anons_alt S A S' : add_anons S A S' <-> add_anons' S A S'.
Proof.
  split.
  - intros H. destruct H as [? ? ? H]. remember (anons S) as _anons eqn:EQN.
    revert S EQN. induction H as [ | ? A anons' i a v ? ? ? IH].
    + intros S ->. destruct S; cbn. constructor.
    + intros S ->. apply AddAnons_insert with (a := a);
      [assumption | unfold fresh_anon; now rewrite get_at_anon | ].
      specialize (IH (S,, a |-> v)). unfold add_anon in IH. cbn in IH.
      apply IH. reflexivity.
  - induction 1 as [S | ? ? ? ? ? ? ? fresh_a ? IH].
    + destruct S. constructor. constructor.
    + inversion IH; subst. unfold add_anon in *; cbn in *. constructor.
      unfold fresh_anon in fresh_a. rewrite get_at_anon in fresh_a.
      econstructor; eassumption.
Qed.

(* Commutation lemmas for add_anons. *)
Lemma add_anons_sset S S' A p v :
  add_anons S A S' -> valid_spath S p -> add_anons (S.[p <- v]) A (S'.[p <- v]).
Proof.
  rewrite !add_anons_alt. induction 1.
  - constructor.
  - intros Hvalid. eapply AddAnons_insert.
    + assumption.
    + eauto with spath.
    + autorewrite with spath in IHadd_anons'. apply IHadd_anons'. validity.
Qed.

Lemma add_anons_get_at_accessor S S' A i v :
  add_anons S A S' -> get_at_accessor S i = Some v -> get_at_accessor S' i = Some v.
Proof.
  rewrite add_anons_alt. induction 1.
  - auto.
  - intros ?. rewrite get_at_accessor_add_anon in * |- by congruence. auto.
Qed.

Lemma add_anons_sget S S' A p :
  add_anons S A S' -> valid_spath S p -> S'.[p] = S.[p].
Proof.
  intros ? (? & H & _). unfold sget. erewrite add_anons_get_at_accessor, H by eassumption.
  reflexivity.
Qed.

Lemma add_anons_sset_rev S S' A p v :
  add_anons (S.[p <- v]) A S' -> valid_spath S p ->
  exists S'', add_anons S A S'' /\ S' = S''.[p <- v].
Proof.
  intros. exists (S'.[p <- S.[p] ]). split.
  - rewrite <-(sset_same S p) at 1. erewrite <-(sset_twice_equal S p) at 1.
    apply add_anons_sset; [eassumption | validity].
  - replace v with (S'.[p]).
    + rewrite sset_twice_equal, sset_same. reflexivity.
    + erewrite add_anons_sget by eauto with spath. autorewrite with spath. reflexivity.
Qed.

Lemma add_anons_add_abstraction S A B S' i :
  add_anons (S,,, i |-> B) A S' ->
      exists S'', S' = S'',,, i |-> B /\ add_anons S A S''.
Proof.
  setoid_rewrite add_anons_alt.
  remember (S,,, i |-> B) eqn:EQN. intros H. revert S EQN. induction H; intros ? ->.
  - eexists. split; [reflexivity | constructor].
  - edestruct IHadd_anons' as (S'' & ? & ?).
    { rewrite <-add_abstraction_add_anon. reflexivity. }
    rewrite fresh_anon_add_abstraction in * |-.
    eexists.  split; [eassumption | ]. econstructor; eassumption.
Qed.

Lemma add_abstraction_add_anons S A B S' i :
  add_anons S A S' -> add_anons (S,,, i |-> B) A (S',,, i |-> B).
Proof.
  setoid_rewrite add_anons_alt. induction 1.
  - constructor.
  - autorewrite with spath in * |-. econstructor; [assumption | | eassumption].
    eauto with spath.
Qed.

Lemma add_anons_remove_abstraction_value S A S' i j :
  add_anons S A S' ->
  add_anons (remove_abstraction_value S i j) A (remove_abstraction_value S' i j).
Proof.
  rewrite !add_anons_alt. induction 1.
  - constructor.
  - autorewrite with spath in * |-. econstructor; [assumption | | eassumption].
    apply fresh_anon_remove_abstraction_value. assumption.
Qed.

Lemma add_anons_add_abstraction_value S A S' i j :
  add_anons (remove_abstraction_value S i j) A S' ->
  exists S'', add_anons S A S'' /\ S' = (remove_abstraction_value S'' i j).
Proof.
  setoid_rewrite add_anons_alt. intros H.
  remember (remove_abstraction_value S i j) as S0 eqn:EQN. revert S EQN. induction H.
  - eexists. split; [constructor | assumption].
  - intros ? ->.
    edestruct IHadd_anons' as (? & ? & ->).
    { rewrite <-remove_abstraction_value_add_anon. reflexivity. }
    rewrite fresh_anon_remove_abstraction_value in * |-.
    eexists. split; [ | reflexivity]. econstructor; eassumption.
Qed.

Lemma add_anons_fresh_abstraction S A S' i :
  add_anons S A S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof.
  rewrite add_anons_alt. induction 1.
  - auto.
  - rewrite <-fresh_abstraction_add_anon in * |-. assumption.
Qed.
Hint Resolve add_anons_fresh_abstraction : spath.

Corollary add_anons_abstraction_element S S' A i j v :
  add_anons S A S' ->
  abstraction_element S i j = Some v -> abstraction_element S' i j = Some v.
Proof. apply add_anons_get_at_accessor. Qed.

Lemma is_fresh_add_anons S S' i A l :
  fresh_abstraction S i -> is_fresh l (S,,, i |-> A) -> add_anons S A S' ->
  is_fresh l S'.
Proof.
  intros fresh_i. rewrite not_state_contains_add_abstraction by exact fresh_i.
  intros (H & G). rewrite add_anons_alt. induction 1 as [ | ? ? ? ? i'].
  - assumption.
  - apply IHadd_anons'.
    + auto with spath.
    + apply not_state_contains_add_anon; [assumption | ].
      specialize (G i'). simpl_map. apply G. reflexivity.
    + eapply map_Forall_insert_1_2; eassumption.
Qed.

(* Note: this could be made into a tactic. *)
Lemma prove_add_anons S0 A S1 :
  (exists S', add_anons S' A S1 /\ S0 = S') -> add_anons S0 A S1.
Proof. intros (? & ? & ->). assumption. Qed.

(* Rewriting lemmas for abstraction_element. *)
Lemma abstraction_element_is_sget S i j v :
  abstraction_element S i j = Some v -> S.[(encode_abstraction (i, j), [])] = v.
Proof. unfold abstraction_element, sget. cbn. intros ->. reflexivity. Qed.

Lemma abstraction_element_is_sget' S i j v p :
  abstraction_element S i j = Some v -> fst p = encode_abstraction (i, j) -> S.[p] = v.[[snd p]].
Proof. unfold abstraction_element, sget. intros H ->. rewrite H. reflexivity. Qed.

Lemma abstraction_element_sset S i j p v :
  fst p <> encode_abstraction (i, j) ->
  abstraction_element (S.[p <- v]) i j = abstraction_element S i j.
Proof. apply get_at_accessor_sset_disj. Qed.

Lemma abstraction_element_add_anon S i j a v :
  abstraction_element (S,, a |-> v) i j = abstraction_element S i j.
Proof. apply get_at_accessor_add_anon. inversion 1. Qed.

Lemma abstraction_element_add_abstraction S i j A :
  abstraction_element (S,,, i |-> A) i j = lookup j A.
Proof.
  unfold abstraction_element, add_abstraction.
  rewrite get_at_abstraction. cbn. simpl_map. reflexivity.
Qed.

Lemma abstraction_element_add_abstraction_ne S i i' j A :
  i <> i' -> abstraction_element (S,,, i' |-> A) i j = abstraction_element S i j.
Proof.
  intros ?. unfold abstraction_element, add_abstraction.
  rewrite !get_at_abstraction. cbn. simpl_map. reflexivity.
Qed.

Lemma abstraction_element_fresh_abstraction S i j :
  fresh_abstraction S i -> abstraction_element S i j = None.
Proof. intros H. unfold abstraction_element. rewrite get_at_abstraction, H. reflexivity. Qed.

Hint Rewrite abstraction_element_sset using eauto with spath; fail : spath.
Hint Rewrite abstraction_element_add_anon : spath.
Hint Rewrite abstraction_element_add_abstraction : spath.
Hint Rewrite abstraction_element_add_abstraction_ne using congruence : spath.
Hint Rewrite abstraction_element_fresh_abstraction using assumption : spath.

Lemma not_in_borrow_add_borrow_anon S a l v p :
  not_in_borrow (S,, a |-> borrow^m(l, v)) p -> p <> (anon_accessor a, []) ->
  fst p <> anon_accessor a.
Proof.
  intros H G ?. autorewrite with spath in H. apply (H []); [constructor | ].
  destruct p as (? & [ | ]).
  - exfalso. cbn in * |-. subst. eauto.
  - eexists _, _. reflexivity.
Qed.

Lemma get_abstraction_sset i S p v :
  ~in_abstraction i (fst p) -> lookup i (abstractions (S.[p <- v])) = lookup i (abstractions S).
Proof.
  intros H. unfold sset, alter_at_accessor. cbn. repeat autodestruct.
  intros. cbn. apply lookup_alter_ne. intros ?. subst.
  eapply H. rewrite decode'_is_Some in * |-. eexists. symmetry. eassumption.
Qed.
Hint Rewrite get_abstraction_sset using assumption : spath.

Lemma add_anons_valid_spath S A S' sp :
  valid_spath S sp -> add_anons S A S' -> valid_spath S' sp.
Proof. rewrite add_anons_alt. induction 2; auto using valid_spath_add_anon. Qed.

Lemma not_in_borrow_add_anons S A S' sp :
  add_anons S A S' -> not_in_borrow S sp -> valid_spath S sp -> not_in_borrow S' sp.
Proof. rewrite add_anons_alt. induction 1; eauto with spath. Qed.

Lemma not_in_borrow_add_abstraction S i A sp (H : ~in_abstraction i (fst sp)) :
  not_in_borrow (S,,, i |-> A) sp <-> not_in_borrow S sp.
Proof.
  split.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    rewrite sget_add_abstraction_notin; assumption.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    rewrite sget_add_abstraction_notin in *; assumption.
Qed.

Lemma not_in_borrow_remove_abstraction_value S i j sp :
  fst sp <> encode_abstraction (i, j) ->
  not_in_borrow (remove_abstraction_value S i j) sp <-> not_in_borrow S sp.
Proof.
  intros H. split.
  - intros G q K (? & ? & <-). eapply G; [ | eexists _, _; reflexivity].
    rewrite sget_remove_abstraction_value by exact H. assumption.
  - intros G q K (? & ? & <-). rewrite sget_remove_abstraction_value in K by exact H.
    eapply G; [eassumption | eexists _, _; reflexivity].
Qed.

Hint Rewrite not_in_borrow_add_abstraction using eauto : spath.
Hint Resolve <-not_in_borrow_add_abstraction : spath.
Hint Resolve <-not_in_borrow_remove_abstraction_value : spath.
Hint Rewrite not_in_borrow_remove_abstraction_value using eauto with spath : spath.

Lemma remove_loans_contains_left A B A' B' i v (H : remove_loans A B A' B') :
  lookup i A' = Some v ->
  lookup i A = Some v /\ remove_loans (delete i A) B (delete i A') B'.
Proof.
  induction H.
  - intros ?. split; [assumption | constructor].
  - intros (? & G)%lookup_delete_Some. specialize (IHremove_loans G).
    destruct IHremove_loans as (? & IHremove_loans). split; [assumption | ].
    rewrite delete_commute. econstructor; simpl_map; eauto.
Qed.

Lemma remove_loans_contains_right A B A' B' i v (H : remove_loans A B A' B') :
  lookup i B' = Some v ->
  lookup i B = Some v /\ remove_loans A (delete i B) A' (delete i B').
Proof.
  induction H.
  - intros ?. split; [assumption | constructor].
  - intros (? & G)%lookup_delete_Some. specialize (IHremove_loans G).
    destruct IHremove_loans as (? & IHremove_loans). split; [assumption | ].
    rewrite delete_commute. econstructor; simpl_map; eauto.
Qed.

Lemma merge_abstractions_contains A B C i v :
  merge_abstractions A B C -> lookup i C = Some v ->
  (lookup i A = Some v /\ merge_abstractions (delete i A) B (delete i C)) \/
  (exists j, lookup j B = Some v /\ merge_abstractions A (delete j B) (delete i C)).
Proof.
  intros (A' & B' & Hremove & Hunion) H.
  eapply union_contains in H; [ | exact Hunion]. destruct H as [? | (j & ? & ?)].
  - left. eapply remove_loans_contains_left in Hremove; [ | eassumption].
    destruct Hremove. split; [assumption | ].
    econstructor. eexists. split; [eassumption | ].
    eapply union_maps_delete_l; [rewrite insert_delete; eassumption | simpl_map; reflexivity].
  - right. exists j. eapply remove_loans_contains_right in Hremove; [ | eassumption].
    destruct Hremove. split; [assumption | ]. econstructor. eauto.
Qed.

Lemma remove_loans_elem_right A B A' B' i :
  remove_loans A B A' B' ->
  lookup i B = lookup i B' \/
  exists l ty, lookup i B = Some (borrow^m(l, LLBC_plus_symbolic ty)).
Proof.
  intros H. induction H.
  - left. reflexivity.
  - destruct (decide (i = j)) as [<- | ].
    + right. destruct IHremove_loans as [-> | ]; [ | assumption]. firstorder.
    + simpl_map. assumption.
Qed.

Lemma merge_no_loan A B C :
  merge_abstractions A B C -> map_Forall (fun _ => not_contains_loan) C ->
  map_Forall (fun _ => not_contains_loan) B.
Proof.
  intros (A' & B' & H & Hunion) G i.
  apply remove_loans_elem_right with (i := i) in H. destruct H as [-> | (l & ty & ->) ].
  - intros v ?.  eapply union_contains_right in Hunion; [ | eassumption].
    destruct Hunion as (? & ?). eapply G. eassumption.
  - intros ? [=<-]. unfold not_contains_loan.
    eapply not_value_contains_unary; [.. | apply not_value_contains_zeroary]; easy.
Qed.

Lemma add_anon_remove_anon S a v :
  lookup (anon_accessor a) (get_map S) = Some v -> (remove_anon a S),, a |-> v = S.
Proof.
  intros ?. destruct S. unfold add_anon, remove_anon. cbn. f_equal.
  apply insert_delete. rewrite get_at_anon in H. exact H.
Qed.

Lemma remove_anon_is_fresh S a : fresh_anon (remove_anon a S) a.
Proof. unfold fresh_anon. rewrite get_at_anon. apply lookup_delete. Qed.

Lemma exists_add_anons S A : exists S', add_anons S A S'.
Proof.
  destruct (exists_union_maps A (anons S)) as (anons' & ?).
  eexists. constructor. eassumption.
Qed.

Lemma add_anons_remove_anon S A S' a v :
  add_anons (S,, a |-> v) A S' -> fresh_anon S a ->
  exists S'', S' = S'',, a |-> v /\ fresh_anon S'' a /\ add_anons S A S''.
Proof.
  intros H fresh_a. exists (remove_anon a S'). repeat split.
  - symmetry. apply add_anon_remove_anon.
    remember (S,, a |-> v). destruct H; subst. rewrite get_at_anon.
    eapply union_contains_left; [eassumption | ]. cbn. simpl_map. reflexivity.
  - apply remove_anon_is_fresh.
  - remember (S,, a |-> v). destruct H; subst. unfold remove_anon. cbn. constructor.
    apply union_maps_delete_l with (v := v); [exact H | ].
    unfold fresh_anon in fresh_a. rewrite get_at_anon in fresh_a. exact fresh_a.
Qed.

Lemma add_anons_remove_anon_sset S S' A a p v w :
  add_anons (S.[p <- v],, a |-> w) A S' -> fresh_anon S a -> valid_spath S p ->
  exists S'', add_anons S A S'' /\ S' = S''.[p <- v],, a |-> w /\ fresh_anon S'' a.
Proof.
  intros H ? ?.
  apply add_anons_remove_anon in H; [ | auto with spath]. destruct H as (S'' & -> & ? & H).
  apply add_anons_sset_rev in H; [ | assumption]. destruct H as (S''' & H & ->).
  exists S'''. repeat split; auto. erewrite fresh_anon_sset. eassumption.
Qed.

Lemma add_anon_add_anons' S A a v S' :
  add_anons' (S,, a |-> v) A S' -> fresh_anon S a ->
      exists S'', S' = S'',, a |-> v /\ add_anons' S A S'' /\ fresh_anon S'' a.
Proof.
  intros H. remember (S,, a |-> v) as _S eqn:EQN. revert S EQN.
  induction H as [ | ? ? ? ? ? ? ? H ? IH]; intros ? ->.
  - eexists. repeat split; [constructor | assumption].
  - intros G. apply fresh_anon_add_anon in H. destruct H.
    edestruct IH as (? & ? & ? & ?).
    { rewrite add_anon_commute by congruence. reflexivity. }
    { rewrite fresh_anon_add_anon. auto. }
    eexists. split; [eassumption | ]. split; [ | assumption]. eauto using AddAnons_insert.
Qed.

Lemma vweight_bot weight : vweight weight bot = weight botC.
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.

Lemma vweight_symbolic weight ty :
  vweight weight (LLBC_plus_symbolic ty) = weight (LLBC_plus_symbolicC ty).
Proof. reflexivity. Qed.
Hint Rewrite vweight_symbolic : weight.

Lemma vweight_mut_loan weight ty l : vweight weight loan^m(ty, l) = weight loanC^m(ty, l).
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_loan : weight.

Lemma vweight_mut_borrow weight l v :
  vweight weight borrow^m(l, v) = weight borrowC^m(l) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_borrow : weight.

(* We cannot automatically rewrite map_sum_empty. Is it because of typeclasses?
 * Thus, we crate an alternative. *)
Lemma abstraction_sum_empty (weight : LLBC_plus_val -> nat) : map_sum weight (M := Pmap) empty = 0.
Proof. apply map_sum_empty. Qed.
Hint Rewrite abstraction_sum_empty : weight.

Lemma abstraction_sum_insert weight i v (A : Pmap LLBC_plus_val) :
  lookup i A = None -> map_sum weight (insert i v A) = weight v + map_sum weight A.
Proof. apply map_sum_insert. Qed.
Hint Rewrite abstraction_sum_insert using auto : weight.

Lemma abstraction_sum_singleton weight i v :
  map_sum weight (singletonM (M := Pmap LLBC_plus_val) i v) = weight v.
Proof.
  unfold singletonM, map_singleton.
  rewrite abstraction_sum_insert, abstraction_sum_empty by apply lookup_empty. lia.
Qed.
Hint Rewrite abstraction_sum_singleton : weight.

Lemma eq_add_abstraction S i A S' j B (H : S,,, i |-> A = S',,, j |-> B)
  (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S' j) :
  (i = j /\ S = S' /\ A = B) \/ (i <> j /\ exists S0, S = S0,,, j |-> B /\ S' = S0,,, i |-> A).
Proof.
  destruct (decide (i = j)) as [<- | ].
  - left. split; [reflexivity | ]. split.
    + destruct S, S'. unfold add_abstraction in H. cbn in * |-. f_equal; [congruence.. | ].
      apply (f_equal abstractions) in H. apply (f_equal (delete i)) in H. cbn in H.
      rewrite !delete_insert in H by assumption. exact H.
    + apply (f_equal abstractions), (f_equal (lookup i)) in H. cbn in H. simpl_map. congruence.
  - right. split; [assumption | ]. exists (remove_abstraction j S). split.
    + symmetry. apply add_remove_abstraction.
      apply (f_equal (remove_abstraction i)) in H.
      rewrite remove_add_abstraction in H by assumption. rewrite H. cbn. simpl_map. reflexivity.
    + apply (f_equal (remove_abstraction j)) in H.
      rewrite remove_add_abstraction in H by assumption.
      rewrite <-remove_add_abstraction_ne; congruence.
Qed.

Lemma remove_abstraction_fresh S i : fresh_abstraction (remove_abstraction i S) i.
Proof. unfold fresh_abstraction, remove_abstraction. cbn. now simpl_map. Qed.

Lemma eq_add_anon_add_abstraction S S' a v i A
  (fresh_a : fresh_anon S a) (fresh_i : fresh_abstraction S' i)
  (H : S,, a |-> v = S',,, i |-> A) :
  exists S0, S = S0,,, i |-> A /\ S' = S0,, a |-> v /\
             fresh_abstraction S0 i /\ fresh_anon S0 a.
Proof.
  exists (remove_abstraction i S). repeat split.
  - symmetry. apply add_remove_abstraction.
    apply (f_equal abstractions), (f_equal (lookup i)) in H. cbn in H. simpl_map.
    reflexivity.
  - apply (f_equal (remove_abstraction i)) in H.
    rewrite remove_add_abstraction in H by assumption.
    unfold add_anon, remove_anon in *. destruct S'. cbn in *. inversion H. congruence.
  - apply remove_abstraction_fresh.
  - unfold fresh_anon, remove_abstraction in *. rewrite get_at_anon in *. assumption.
Qed.

Lemma eq_sset_add_abstraction_notin S S' sp i A w
  (fresh_i : fresh_abstraction S' i) (sp_not_in_abstraction : ~in_abstraction i (fst sp))
  (H : S.[sp <- w] = S',,, i |-> A) :
  exists S0, S = S0,,, i |-> A /\ S' = S0.[sp <- w] /\ fresh_abstraction S0 i.
Proof.
  destruct (decidable_valid_spath S sp) as [ | Hinvalid].
  - exists (S'.[sp <- S.[sp] ]). repeat split.
    + apply (f_equal (sset sp (S.[sp]))) in H. autorewrite with spath in H. exact H.
    + apply (f_equal (sget sp)) in H. autorewrite with spath in H. rewrite H.
      autorewrite with spath. reflexivity.
    + eauto with spath.
  - rewrite sset_invalid in H by assumption. subst. exists S'. rewrite sset_invalid.
    + auto.
    + intros K. apply Hinvalid. destruct K as (u & ?). exists u.
      rewrite get_at_accessor_add_abstraction_notin by eauto. assumption.
Qed.

Corollary eq_sset_add_anon_add_abstraction S S' sp a v w i A
  (fresh_a : fresh_anon S a) (fresh_i : fresh_abstraction S' i)
  (sp_not_in_abstraction : not_in_abstraction sp)
  (H : S.[sp <- w],, a |-> v = S',,, i |-> A) :
  exists S0, S = S0,,, i |-> A /\ S' = S0.[sp <- w],, a |-> v /\
             fresh_abstraction S0 i /\ fresh_anon S0 a.
Proof.
  apply eq_add_anon_add_abstraction in H; eauto with spath.
  destruct H as (S0 & H & -> & ? & fresh_a_S0).
  apply eq_sset_add_abstraction_notin in H; [ | eauto with spath..].
  destruct H as (S1 & -> & -> & ?). rewrite <-fresh_anon_sset in fresh_a_S0.
  exists S1. auto.
Qed.

(* For an abstraction A, set the vpath p at index i to v. *)
Definition abstraction_set j p v (A : Pmap LLBC_plus_val) := alter (vset p v) j A.

Lemma eq_sset_add_abstraction S S' sp i j A w
  (fresh_i : fresh_abstraction S' i) (sp_in_abstraction : fst sp = encode_abstraction (i, j))
  (H : S.[sp <- w] = S',,, i |-> A) :
  exists B, S = S',,, i |-> B /\ A = abstraction_set j (snd sp) w B.
Proof.
  destruct sp as (? & q). rewrite fst_pair, snd_pair in *. subst.
  assert (exists B, lookup i (abstractions S) = Some B) as (B & get_B).
  { apply elem_of_dom. apply (f_equal get_extra) in H.
    unfold sset in H. rewrite get_extra_alter in H. cbn in H. rewrite H. set_solver. }
  apply add_remove_abstraction in get_B. rewrite <-get_B in H.
  rewrite sset_add_abstraction in H.
  apply eq_add_abstraction in H; [ | apply remove_abstraction_fresh | assumption ].
  destruct H as [(_ & <- & <-) | (? & _)]; [ | congruence].
  exists B. split; [congruence | reflexivity].
Qed.

(** ** Lemmas about typing. *)
(* Note: when we add a static type checking, we may change the definition of [is_of_type] so
 * that the invalid value [bot] is of any type. For the moment, there is no reason to do that.
 * *)
Lemma is_of_type_does_not_contain_bot ty v :
  is_of_type ty v -> not_value_contains (fun c => c = botC) v.
Proof. destruct v; inversion 1; now apply not_value_contains_zeroary. Qed.
Hint Resolve is_of_type_does_not_contain_bot : spath.

(* This lemma is becoming false when we type borrows. *)
Lemma is_of_type_does_not_contain_borrow ty v :
  is_of_type ty v -> not_contains_borrow v.
Proof. destruct v; inversion 1; now apply not_value_contains_zeroary. Qed.

(* If we type values that may contain mutable borrows, the following two lemmas might become false.
 *)
Lemma is_of_type_valid ty S p : is_of_type ty (S.[p]) -> valid_spath S p.
Proof. intros H. apply valid_get_node_sget_not_bot. destruct H; discriminate. Qed.
Hint Resolve is_of_type_valid : spath.

Lemma is_of_type_valid_vpath ty v p : is_of_type ty (v.[[p]]) -> valid_vpath v p.
Proof. intros H. apply valid_get_node_vget_not_bot. destruct H; discriminate. Qed.
Hint Resolve is_of_type_valid_vpath : spath.

Lemma vset_preserves_type v w p tv tw :
  is_of_type tv v -> is_of_type tw (v.[[p]]) -> is_of_type tw w ->
  is_of_type tv (v.[[p <- w]]).
Proof.
  intros H G ?.
  (* This trick only works because we can only type integer and booleans. When we add types for
   * mutable borrows, tuples or other types, we will need to redo the proof. *)
  assert (p = []) as ->.
  { apply valid_vpath_zeroary with (v := v).
    - inversion H; reflexivity.
    - validity. }
  cbn in G. destruct H; inversion G; subst; assumption.
Qed.

Lemma is_of_type_sset_rev S p q ty0 ty1 v :
  is_of_type ty0 (S.[p <- v].[q]) -> is_of_type ty1 v -> is_of_type ty1 (S.[p]) ->
  ~strict_prefix p q -> is_of_type ty0 (S.[q]).
Proof.
  intros H G K ?.
  assert (valid_spath S q). { eapply sset_not_prefix_valid; eauto with spath. }
  destruct (decidable_prefix q p) as [(r & <-) | ].
  - autorewrite with spath in H.
    rewrite <-(vset_same (S.[q]) r). erewrite <-vset_twice_equal.
    eapply vset_preserves_type.
    + exact H.
    + autorewrite with spath. eassumption.
    + autorewrite with spath. assumption.
  - assert (disj q p) by solve_comp. autorewrite with spath in H. exact H.
Qed.

(* For the moment the theorem is trivial as we don't type mutable borrows. *)
(* Note: with type on borrows, we could just apply the theorems [is_of_type_sset_rev] and
 * [is_of_type_sset_rev]. *)
Lemma _is_of_type_rename_mut_borrow_val v p l0 l1 ty :
  get_node (v.[[p]]) = borrowC^m(l0) -> is_of_type ty v ->
  is_of_type ty (v.[[p <- borrow^m(l1, v.[[p ++ [0] ]])]]).
Proof.
  intros get_borrow Htype. assert (valid_vpath v p) as H by validity.
  apply valid_vpath_zeroary in H; [ | destruct Htype; reflexivity]. subst.
  cbn in get_borrow. destruct Htype; discriminate.
Qed.

Lemma is_of_type_rename_mut_borrow_val v p l0 l1 ty :
  get_node (v.[[p]]) = borrowC^m(l0) ->
  is_of_type ty (v.[[p <- borrow^m(l1, v.[[p ++ [0] ]])]]) ->
  is_of_type ty v.
Proof.
  intros get_l0 Htype.
  eapply _is_of_type_rename_mut_borrow_val with (p := p) (l1 := l0) in Htype.
  - rewrite vset_twice_equal in Htype. autorewrite with spath in Htype.
    rewrite <-(vset_same v p).
    replace (v.[[p]]) with (borrow^m(l0, v.[[p ++ [0] ]])); [exact Htype | ].
    rewrite vget_app. destruct (v.[[p]]); inversion get_l0; reflexivity.
  - autorewrite with spath. reflexivity.
Qed.

Lemma is_of_type_rename_mut_borrow S p q l0 l1 ty
  (get_l0 : get_node (S.[p]) = borrowC^m(l0))
  (Htype : is_of_type ty ((rename_mut_borrow S p l1).[q])) :
  is_of_type ty (S.[q]).
Proof.
  destruct (decidable_prefix q p) as [(r & <-) | ].
  - autorewrite with spath in Htype.
    + eapply is_of_type_rename_mut_borrow_val; autorewrite with spath; eassumption.
    + assert (valid_spath S (q +++ r)) as (? & _)%valid_spath_app by validity. assumption.
  - autorewrite with spath in Htype. exact Htype.
Qed.

Lemma rename_value_preserves_type r v ty : is_of_type ty v -> is_of_type ty (rename_value r v).
Proof. induction 1; constructor. Qed.
Hint Resolve rename_value_preserves_type : spath.

(* TODO: rename *)
Lemma is_of_type_sset_sget S p q w ty0 ty1 :
  is_of_type ty0 (S.[q]) -> is_of_type ty1 w -> is_of_type ty1 (S.[p]) ->
  is_of_type ty0 (S.[p <- w].[q]).
Proof.
  intros H G K.
  assert (~strict_prefix p q).
  { eapply get_zeroary_not_strict_prefix; [ | eapply is_of_type_valid; eassumption].
    inversion K; reflexivity. }
  destruct (decidable_prefix q p) as [(r & <-) | ].
  - autorewrite with spath. eapply vset_preserves_type; autorewrite with spath; eassumption.
  - assert (disj q p) by solve_comp. autorewrite with spath. exact H.
Qed.

Lemma store_compatible_types_vset_symbolic S p v q ty :
  store_compatible_types S p (v.[[q <- LLBC_plus_symbolic ty]]) ->
  is_of_type ty (v.[[q]]) -> store_compatible_types S p v.
Proof.
  intros H G p0 Hprefix get_mut_borrow.
  specialize (H p0 Hprefix get_mut_borrow).
  destruct Hprefix as (i & r & <-). destruct H as (ty' & type_at_p & type_at_v).
  exists ty'. split; [assumption | ].
  rewrite <-(vset_same v q). erewrite <-vset_twice_equal.
  eapply vset_preserves_type.
  - exact type_at_v.
  - autorewrite with spath. constructor.
  - exact G.
Qed.

Lemma store_compatible_types_sset S p v w q ty :
  ~strict_prefix q p ->
  store_compatible_types (S.[q <- w]) p v ->
  is_of_type ty w -> is_of_type ty (S.[q]) -> store_compatible_types S p v.
Proof.
  intros not_strict_prefix H ? G p0 Hprefix get_mut_borrow.
  specialize (H p0 Hprefix).
  (* TODO: are there lemmas to solve this? *)
  assert (~(strict_prefix q p0)).
  { intros ?. apply not_strict_prefix. etransitivity; eassumption. }
  (* For now, we use the trick that we cannot type mutable borrows. It is a real hack, because at
   * some point we want to type mutable borrows. *)
  (* I think it would be cleaner to use the hypothesis that S.[q] does not contain mutable
   * borrows. *)
  assert (q <> p0).
  { intros <-. revert get_mut_borrow. inversion G; inversion 1. }
  rewrite get_node_sset_sget_not_prefix in H by solve_comp. specialize (H get_mut_borrow).
  destruct H as (ty' & ? & ?). exists ty'. split; [ | assumption].
  eapply is_of_type_sset_rev; try eassumption.
Qed.

Lemma store_compatible_types_add_abstraction S p v i A
  (p_not_in_abstraction : ~in_abstraction i (fst p)) :
  store_compatible_types (S,,, i |-> A) p v <-> store_compatible_types S p v.
Proof.
  split.
  - intros Hcomp q Hprefix get_mut_borrow.
    specialize (Hcomp q Hprefix). destruct Hprefix as (j & r & <-).
    autorewrite with spath in Hcomp. auto.
  - intros Hcomp q Hprefix get_mut_borrow.
    destruct (Hprefix) as (j & r & <-). autorewrite with spath in get_mut_borrow |- *.
    eapply Hcomp; eassumption.
Qed.

Lemma store_compatible_types_add_anon S p v a w
  (p_not_in_anon : fst p <> anon_accessor a) :
  store_compatible_types (S,, a |-> w) p v <-> store_compatible_types S p v.
Proof.
  split.
  - intros Hcomp q Hprefix get_mut_borrow.
    specialize (Hcomp q Hprefix). destruct Hprefix as (i & r & <-).
    autorewrite with spath in Hcomp. auto.
  - intros Hcomp q Hprefix get_mut_borrow.
    destruct (Hprefix) as (i & r & <-). autorewrite with spath in get_mut_borrow |- *.
    eapply Hcomp; eassumption.
Qed.

Lemma store_compatible_types_moved_value S sp sp_store v :
  not_in_borrow S sp -> ~strict_prefix sp sp_store ->
  store_compatible_types (S.[sp <- bot]) sp_store v -> store_compatible_types S sp_store v.
Proof.
  intros Hnot_in_borrow H Hcomp q prefix_q_sp_store get_mut_borrow.
  destruct (decidable_prefix (q +++ [0]) sp) as [prefix_q_sp | ].
  - exfalso. eapply Hnot_in_borrow; [eassumption | ].
    destruct prefix_q_sp as (? & <-). autorewrite with spath. eexists 0, _. reflexivity.
  - assert (disj q sp).
    { solve_comp. intros ?. apply H. transitivity q; assumption. }
    assert (disj sp_store sp).
    { destruct prefix_q_sp_store as (? & ? & <-). solve_comp. }
    specialize (Hcomp q prefix_q_sp_store).
    autorewrite with spath in Hcomp. auto.
Qed.

(* TODO: notation rename_mut_borrow for values. *)
Lemma store_compatible_types_rename_mut_borrow_val S p q v l0 l1 :
  get_node (v.[[q]]) = borrowC^m(l0) ->
  store_compatible_types S p (v.[[q <- borrow^m(l1, v.[[q ++ [0] ]])]]) ->
  store_compatible_types S p v.
Proof.
  intros get_borrow_q Hcomp r prefix_r_p get_borrow_r.
  specialize (Hcomp r prefix_r_p get_borrow_r).
  destruct Hcomp as (ty' & ? & ?). exists ty'. split; [assumption | ].
  eapply is_of_type_rename_mut_borrow_val; eassumption.
Qed.

Lemma store_compatible_types_rename_mut_borrow S p q v l0 l1 :
  get_node (S.[q]) = borrowC^m(l0) ->
  store_compatible_types (rename_mut_borrow S q l1) p v ->
  store_compatible_types S p v.
Proof.
  intros ? Hcomp r prefix_r_p get_borrow.
  assert (is_mut_borrow (get_node ((rename_mut_borrow S q l1).[ r]))) as get_borrow'.
  { destruct (decidable_spath_eq q r) as [<- | ]; autorewrite with spath; easy. }
  specialize (Hcomp r prefix_r_p get_borrow').
  destruct Hcomp as (ty & ? & ?). exists ty. split; [ | assumption].
  eapply is_of_type_rename_mut_borrow; eassumption.
Qed.

Lemma store_compatible_types_remove_abstraction_value S sp v i j :
  fst sp <> encode_abstraction (i, j) ->
  store_compatible_types (remove_abstraction_value S i j) sp v ->
  store_compatible_types S sp v.
Proof.
  intros ? Hcomp q Hstrict_prefix get_borrow. destruct (Hstrict_prefix) as (? & ? & <-).
  specialize (Hcomp q Hstrict_prefix). autorewrite with spath in Hcomp. auto.
Qed.

(** ** Automation *)
Lemma not_value_contains_loan_id_loan l0 l1 ty :
  not_value_contains (is_loan_id l0) (loan^m(ty, l1)) -> l0 <> l1.
Proof. intros H <-. apply (H []); [constructor | reflexivity]. Qed.

Lemma not_value_contains_loan_id_borrow l0 l1 v :
  not_value_contains (is_loan_id l0) (borrow^m(l1, v)) ->
  l0 <> l1 /\ not_value_contains (is_loan_id l0) v.
Proof.
  intros H. split.
  - intros <-. apply (H []); [constructor | reflexivity].
  - intros p ?. apply (H ([0] ++ p)). validity.
Qed.

(* TODO: move *)
Lemma no_loan_no_borrow_implies_no_loan_id v l :
  not_contains_loan v -> not_contains_borrow v -> not_value_contains (is_loan_id l) v.
Proof.
  intros no_loan no_borrow p valid_p get_loan_id.
  destruct (get_node (v.[[p]])) eqn:EQN; inversion get_loan_id.
  - eapply no_loan; [eassumption | ]. rewrite EQN. constructor.
  - eapply no_borrow; [eassumption | ]. rewrite EQN. constructor.
Qed.
Hint Resolve no_loan_no_borrow_implies_no_loan_id : spath.

(* Trying to prove that a value doesn't contain a node (ex: loan, loc, bot).
   This tactic tries to solve this by applying the relevant lemmas, and never fails. *)
(* Note: Can we remove the automatic rewriting out of this tactic? *)
(* TODO: precise the "workflow" of this tactic. *)
Ltac not_contains0 :=
  try assumption;
  autounfold with spath in *;
  lazymatch goal with
  (* Processing freshess hypotheses. We don't change the goal, we just pre-process the context. *)
  | H : is_fresh ?l (?S,,, ?i |-> ?A) |- is_fresh ?l' ?S' =>
      rewrite not_state_contains_add_abstraction in H by eauto with spath;
      destruct H
  | H : is_fresh ?l (?S,, ?a |-> ?v) |- is_fresh ?l' ?S' =>
      apply not_state_contains_add_anon_rev in H;
        [destruct H | eauto with spath; fail]
  | H : not_value_contains ?l0 (borrow^m(?l1, ?v)) |- is_fresh ?l' ?S =>
      apply not_value_contains_loan_id_borrow in H; destruct H
  | H : not_value_contains ?l0 (loan^m(?ty, ?l1)) |- is_fresh ?l' ?S =>
      apply not_value_contains_loan_id_loan in H

  (* Proving freshness. *)
  | |- is_fresh ?l (?S,, ?a |-> ?v) =>
      simple apply not_state_contains_add_anon
  | |- is_fresh ?l (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset
  | H : is_fresh ?l (rename_mut_borrow ?S ?p ?l') |- is_fresh ?l ?S =>
      eapply is_fresh_rename_mut_borrow; [eassumption | congruence | exact H]
  | H : is_fresh ?l (?S.[?p <- ?v]) |- is_fresh ?l ?S =>
      eapply not_state_contains_sset_rev; [exact H | ]

  (* Proof of not_value_contains goals (like not_contains_loan or not_contains_bot). *)
  | H : not_value_contains ?P ((rename_mut_borrow ?S ?q ?l).[?p]) |- not_value_contains ?P (?S.[?p]) =>
      eapply not_contains_rename_mut_borrow;
        [eassumption | eauto with spath; fail | exact H]
  | H : not_value_contains ?P (?S.[?q <- ?v].[?p]) |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_value_contains_sset_rev _ _ _ _ _ H); [ | validity]
  | H : not_value_contains ?P (?v.[[?p <- ?w]]) |- not_value_contains ?P ?v =>
      eapply not_value_contains_vset_rev; [ | exact H]
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget _ S p H);
      validity0
  | H : get_node ?v = _ |- not_value_contains ?P ?v =>
      simple apply not_value_contains_zeroary; rewrite H; [reflexivity | ]
  | |- not_value_contains ?P ?v =>
      first [
        apply not_value_contains_zeroary; [reflexivity | ] |
        eapply not_value_contains_unary; [reflexivity | | ]
      ]
  end.
Ltac not_contains := repeat not_contains0; eauto with spath.

(* TODO: document. *)
Ltac not_contains_outer :=
  autorewrite with spath;
  try assumption;
  lazymatch goal with
  | |- not_contains_outer _ ?P (?v.[[?p <- ?w]]) =>
      apply not_contains_outer_vset; not_contains_outer
  | no_outer : not_contains_outer _ ?P (?S.[?q <- ?v].[?p])
    |- not_contains_outer _ ?P (?S.[?p]) =>
      eapply not_contains_outer_sset_no_contains;
        [exact no_outer | not_contains_outer | eauto with spath]
  | |- not_contains_outer _ _ _ =>
      apply not_contains_implies_not_contains_outer; not_contains; fail
  | |- not_contains_outer _ _ _ =>
      idtac
  end.

Hint Resolve <-fresh_anon_add_anon : spath.

(* Frequently, after the combination of tactics [remember] and [destruct], we have
 * hypotheses of the form [E[Sl] = F[Sr]], with E and F expressions over states Sl and Sr
 * (adding anonymous bindings, abstractions and sset).
 * This tactic finds a common unificator S such that Sl are expressions over S, replaces Sl and
 * Sr, with the relevant hypotheses in the context. *)
Ltac process_state_eq0 :=
  let S := fresh "S" in
  let B := fresh "B" in
  let eq_val := fresh "eq_val" in
  lazymatch goal with
  | H : context [ (?S0,, ?a |-> ?v),,, ?i |-> ?A ] |- _ =>
      rewrite !add_abstraction_add_anon in H
  | H : ?Sl,,, ?i |-> ?A = ?Sr,, ?a |-> ?v |- _ => symmetry in H
  | H : ?Sl.[?sp <- ?w],, ?a |-> ?v = ?Sr,,, ?i |-> ?A |- _ =>
      apply eq_sset_add_anon_add_abstraction in H; [ | eauto with spath; fail..];
      destruct H as (S & -> & -> & ? & ?)
  | H : ?Sl,, ?a |-> ?v = ?Sr,,, ?i |-> ?A |- _ =>
      apply eq_add_anon_add_abstraction in H; [ | eauto with spath; fail..];
      first [ destruct H as (S & -> & -> & ? & ?) | destruct H as (S & ? & -> & ? & ?)]
  | H : ?Sl.[?sp <- ?w] = ?Sr,,, ?i |-> ?A, G : fst ?sp = encode_abstraction (?i, ?j) |- _ =>
      eapply eq_sset_add_abstraction in H; [ | eauto with spath; fail | exact G];
      destruct H as (B & -> & ->)
  | H : ?Sl.[?sp <- ?w] = ?Sr,,, ?i |-> ?A, G : ~in_abstraction ?i (fst ?sp) |- _ =>
      eapply eq_sset_add_abstraction_notin in H; [ | eauto with spath; fail | exact G];
      destruct H as (S & -> & -> & ?)
  | H : fresh_anon (_,, ?a |-> ?v) ?b |- _ =>
      rewrite fresh_anon_add_anon in H; destruct H as (H & ?)
  | H : ?S0,, ?a |-> ?v0,, ?b |-> ?v1  = ?S1,, ?a |-> ?v2 |- _ =>
    rewrite add_anon_commute in H by congruence
  | H : ?Sl,, ?a |-> ?vl = ?Sr,, ?a |-> ?vr |- _ =>
      apply states_add_anon_eq in H; [ | auto with spath; fail..];
      destruct H as (H & eq_val); subst
  end.
Ltac process_state_eq := repeat process_state_eq0.

(** * Effect of permutation on LLBC+ operations. *)
Definition id_state_permutation S := {|
  anons_perm := id_permutation (anons S);
  abstractions_perm := fmap id_permutation (abstractions S);
|}.

Lemma apply_id_state_permutation S : rename_accessors (id_state_permutation S) S = S.
Proof.
  unfold rename_accessors. destruct S. cbn. f_equal.
  - apply apply_id_permutation.
  - apply map_eq. intros i. rewrite map_lookup_zip_with. simpl_map.
    destruct (lookup i _); cbn; f_equal. apply apply_id_permutation.
Qed.

Lemma id_state_permutation_is_valid_accessor_permutation S :
  valid_accessor_permutation (id_state_permutation S) S.
Proof.
  split.
  - apply id_permutation_is_permutation.
  - intros i. cbn. simpl_map. destruct (lookup i (abstractions S)); constructor.
    apply id_permutation_is_permutation.
Qed.

Instance reflexive_accessor_perm : Reflexive equiv_states_up_to_accessor_permutation.
Proof.
  intros S. eexists (id_state_permutation S). split.
  - apply id_state_permutation_is_valid_accessor_permutation.
  - symmetry. apply apply_id_state_permutation.
Qed.

Definition id_loan_map (L : Pset) : Pmap positive := set_to_map (fun l => (l, l)) L.

Lemma id_loan_map_inj L : map_inj (id_loan_map L).
Proof.
 intros ? ? (? & _ & ?)%lookup_set_to_map; [ | auto].
 intros ? ? (? & _ & ?)%lookup_set_to_map; [ | auto]. congruence.
Qed.

Lemma lookup_id_loan_map L i j : lookup i (id_loan_map L) = Some j -> i = j.
Proof. intros (? & _ & ?)%lookup_set_to_map; [congruence | auto]. Qed.

Lemma rename_value_id m v (H : forall i j, lookup i m = Some j -> i = j) :
  rename_value m v = v.
Proof.
  induction v; try reflexivity.
  all: cbn; unfold rename_loan_id; autodestruct; intros ?%H; congruence.
Qed.

Corollary rename_set_id m (A : Pmap _) (H : forall i j, lookup i m = Some j -> i = j) :
  fmap (rename_value m) A = A.
Proof.
  erewrite map_fmap_ext; [apply map_fmap_id | ]. intros. apply rename_value_id. assumption.
Qed.

Lemma rename_state_identity L S : rename_state (id_loan_map L) S = S.
Proof.
  unfold rename_state. destruct S. cbn. f_equal.
  - apply rename_set_id. apply lookup_id_loan_map.
  - apply rename_set_id. apply lookup_id_loan_map.
  - erewrite map_fmap_ext; [apply map_fmap_id | ]. intros.
    apply rename_set_id. apply lookup_id_loan_map.
Qed.

Lemma dom_id_loan_map (L : Pset) : dom (id_loan_map L) = L.
Proof.
  apply set_eq. intros i. rewrite elem_of_dom. split.
  - intros (? & (? & ? & ?)%lookup_set_to_map); auto. congruence.
  - unfold id_loan_map. intros ?. exists i. rewrite lookup_set_to_map by auto. exists i. auto.
Qed.

Instance reflexive_rename_loan : Reflexive equiv_states_up_to_loan_renaming.
Proof.
  intros S. exists (id_loan_map (loan_set_state S)). split.
  - split.
    + apply id_loan_map_inj.
    + rewrite dom_id_loan_map. reflexivity.
  - symmetry. apply rename_state_identity.
Qed.

Instance equiv_states_reflexive : Reflexive equiv_states.
Proof. intros S. eapply prove_equiv_states; reflexivity. Qed.

Definition anons_permutation S p := {|
  anons_perm := p;
  abstractions_perm := fmap id_permutation (abstractions S);
|}.

Lemma equiv_states_by_anons_equivalence S S' :
  equiv_map (anons S) (anons S') -> vars S = vars S' -> abstractions S = abstractions S' ->
  equiv_states_up_to_accessor_permutation S S'.
Proof.
  intros (m & equiv_m & ?)%equiv_map_alt ? ?. exists (anons_permutation S m). split.
  - split.
    + assumption.
    + intros i. cbn. simpl_map. destruct (lookup i (abstractions S)); constructor.
      apply id_permutation_is_permutation.
  - unfold rename_accessors. destruct S, S'. cbn in *. subst. f_equal.
    apply map_eq. intros i. rewrite map_lookup_zip_with. simpl_map.
    destruct (lookup i _); cbn; f_equal. symmetry. apply apply_id_permutation.
Qed.

Lemma add_anons_assoc S0 S1 S2 S'2 A B C :
  union_maps A B C -> add_anons S0 B S1 -> add_anons S1 A S2 -> add_anons S0 C S'2 ->
  equiv_states S2 S'2.
Proof.
  intros ? H G K. eapply prove_equiv_states; [reflexivity | ].
  inversion H. inversion G. inversion K. subst.
  apply equiv_states_by_anons_equivalence; [ | reflexivity..]. cbn in *.
  eapply union_maps_assoc; [ | | eassumption..]; eassumption.
Qed.

Lemma add_anons_add_anon S A S' a v :
  add_anons S A S' -> fresh_anon S a ->
  exists S'', add_anons (S,, a |-> v) A (S'',, a |-> v) /\ fresh_anon S'' a /\
              equiv_states_up_to_accessor_permutation S'' S'.
Proof.
  unfold fresh_anon. rewrite get_at_anon. intros H fresh_a.
  destruct (exists_add_anons (S,, a |-> v) A) as (S'' & G).
  exists (remove_anon a S''). split; [ | split].
  - rewrite add_anon_remove_anon; [assumption | ]. inversion G; subst. rewrite get_at_anon.
    eapply union_contains_left; [eassumption | ]. cbn. simpl_map. reflexivity.
  - apply remove_anon_is_fresh.
  - cbn. inversion H. inversion G. subst. cbn.
    apply equiv_states_by_anons_equivalence; [ | reflexivity..].
    symmetry. eapply union_maps_unique; [eassumption | ].
    apply union_maps_delete_l with (v := v); assumption.
Qed.

Lemma rename_state_valid_spath S sp perm :
  valid_spath S sp <-> valid_spath (rename_state perm S) sp.
Proof.
  split.
  - intros (v & ? & ?). exists (rename_value perm v). split.
    + rewrite get_map_rename_state. simpl_map. reflexivity.
    + apply valid_vpath_rename_value. assumption.
  - intros (v & get_v & Hvalid). rewrite get_map_rename_state, lookup_fmap in get_v.
    destruct (get_at_accessor S (fst sp)) as [w | ] eqn:get_w; [ | discriminate].
    exists w. split; [assumption | ]. inversion get_v. subst.
    rewrite <-valid_vpath_rename_value in Hvalid. exact Hvalid.
Qed.

Lemma permutation_valid_spath S sp perm (H : is_state_equivalence perm S) :
  valid_spath S sp ->
  valid_spath (apply_state_permutation perm S) (permutation_spath perm sp).
Proof.
  destruct H as (? & _). intros (? & ? & ?). eexists. unfold permutation_spath.
  edestruct get_at_accessor_state_permutation as (? & -> & ->); eauto.
  split; [reflexivity | ]. apply valid_vpath_rename_value. assumption.
Qed.
Hint Resolve permutation_valid_spath : spath.

Lemma rename_accessors_valid_spath_rev S p perm (H : valid_accessor_permutation perm S) :
  valid_spath (rename_accessors perm S) p ->
  exists q, valid_spath S q /\ p = _permutation_spath perm q.
Proof.
  destruct p as (i & p). intros (v & G & valid_v_p).
  rewrite get_map_rename_accessors in G by assumption.
  pose proof (mk_is_Some _ _ G) as G'.
  apply lookup_pkmap_rev in G'; [ | eapply permutation_accessor_inj; eassumption].
  destruct G' as (j & G').
  erewrite lookup_pkmap in G; [ | eapply permutation_accessor_inj; eassumption | exact G'].
  exists (j, p). split.
  - exists v. split; assumption.
  - unfold permutation_spath. rewrite fst_pair, G'. reflexivity.
Qed.

Lemma permutation_spath_app perm p q :
  (permutation_spath perm p) +++ q = permutation_spath perm (p +++ q).
Proof. unfold permutation_spath. cbn. autodestruct. Qed.
Hint Rewrite permutation_spath_app : spath.

(* TODO: inconsistent lemma names. *)
Lemma rename_state_sget S sp r : (rename_state r S).[sp] = rename_value r (S.[sp]).
Proof.
  unfold sget. rewrite get_map_rename_state, lookup_fmap.
  destruct (get_at_accessor S (fst sp)).
  - cbn. symmetry. apply vget_rename_value.
  - reflexivity.
Qed.

Lemma rename_accessors_sget S perm (H : valid_accessor_permutation perm S)
  sp (valid_sp : valid_spath S sp) :
  (rename_accessors perm S).[_permutation_spath perm sp] = S.[sp].
Proof.
  destruct valid_sp as (v & get_at_sp & _). unfold permutation_spath, sget.
  edestruct get_at_accessor_rename_accessors as (? & -> & G); [eassumption.. | ].
  rewrite fst_pair, snd_pair, G, get_at_sp. reflexivity.
Qed.

Lemma permutation_sget S perm (H : is_state_equivalence perm S)
  sp (valid_sp : valid_spath S sp) :
  (apply_state_permutation perm S).[permutation_spath perm sp] =
  rename_value (loan_id_names perm) (S.[sp]).
Proof.
  destruct (H) as (? & _).
  destruct valid_sp as (v & get_at_sp & _). unfold permutation_spath, sget.
  edestruct get_at_accessor_state_permutation as (? & -> & G); [eassumption.. | ].
  rewrite fst_pair, snd_pair, G, get_at_sp, vget_rename_value. reflexivity.
Qed.

Lemma loan_set_rename_accessors perm S :
  valid_accessor_permutation perm S -> loan_set_state (rename_accessors perm S) = loan_set_state S.
Proof.
  intros H. apply set_eq. intros l. rewrite !elem_of_loan_set_state.
  split.
  - intros (p & Hp).
    edestruct (rename_accessors_valid_spath_rev S p) as (q & valid_q & ?);
      [eauto using get_loan_id_valid_spath.. | ].
    exists q. subst. rewrite rename_accessors_sget in Hp; assumption.
  - intros (p & Hp). exists (_permutation_spath perm p).
    rewrite rename_accessors_sget; eauto using get_loan_id_valid_spath.
Qed.

Lemma rename_accessor_preserves_loan_validity perm r S :
  valid_accessor_permutation perm S ->
  valid_loan_id_names r (rename_accessors perm S) <-> valid_loan_id_names r S.
Proof.
  intros H. unfold valid_loan_id_names. rewrite loan_set_rename_accessors by assumption.
  reflexivity.
Qed.

Lemma valid_loan_id_names_compose m0 m1 S :
  valid_loan_id_names m0 S -> valid_loan_id_names m1 (rename_state m0 S) ->
  valid_loan_id_names (map_compose m1 m0) S.
Proof.
  intros (inj_m0 & dom_m0) (inj_m1 & dom_m1). split.
  - apply injective_compose; assumption.
  - intros l Hl. specialize (dom_m0 l Hl).
    apply elem_of_dom in dom_m0. destruct dom_m0 as (l' & Hl').
    apply elem_of_dom. setoid_rewrite map_lookup_compose. setoid_rewrite Hl'. cbn.
    apply elem_of_dom, dom_m1. apply elem_of_loan_set_state.
    apply elem_of_loan_set_state in Hl. destruct Hl as (p & get_p).
    exists p. rewrite rename_state_sget.
    rewrite get_node_rename_value, get_loan_id_rename_node.
    rewrite get_p. cbn. unfold rename_loan_id. setoid_rewrite Hl'. reflexivity.
Qed.

Definition compose_accessor_permutation p1 p0 := {|
  anons_perm := map_compose (anons_perm p1) (anons_perm p0);
  abstractions_perm :=
    map_zip_with (map_compose (MA := Pmap)) (abstractions_perm p1) (abstractions_perm p0);
|}.

Lemma valid_accessor_permutation_compose p1 p0 S :
  valid_accessor_permutation p0 S -> valid_accessor_permutation p1 (rename_accessors p0 S) ->
  valid_accessor_permutation (compose_accessor_permutation p1 p0) S.
Proof.
  intros p0_perm p1_perm.
  destruct (p0_perm) as (? & H). destruct p1_perm as (? & G).
  split.
  - apply compose_permutation; [assumption | ].
    eapply is_permutation_dom_eq; [ | eassumption]. reflexivity.
  - intros i. specialize (H i). specialize (G i).
    revert G. cbn. rewrite !map_lookup_zip_with. inversion H.
    + cbn. inversion 1. constructor. apply compose_permutation; assumption.
    + cbn. inversion 1. constructor.
Qed.

Definition compose_state_permutation p1 p0 := {|
  accessor_perm := compose_accessor_permutation (accessor_perm p1) (accessor_perm p0);
  loan_id_names := map_compose (loan_id_names p1) (loan_id_names p0);
|}.

Lemma is_permutation_compose S p1 p0 :
  is_state_equivalence p0 S -> is_state_equivalence p1 (apply_state_permutation p0 S) ->
  is_state_equivalence (compose_state_permutation p1 p0) S.
Proof.
  intros (? & ?) (truc & muche). split.
  - apply valid_accessor_permutation_compose; [assumption | ].
    rewrite apply_state_permutation_alt in truc by assumption.
    rewrite rename_state_preserves_accessor_perm_validity in truc. exact truc.
  - apply valid_loan_id_names_compose; [assumption | ].
    unfold apply_state_permutation in muche.
    rewrite rename_accessor_preserves_loan_validity in muche; [exact muche | ].
    rewrite rename_state_preserves_accessor_perm_validity. assumption.
Qed.

Lemma rename_accessors_compose S p1 p0 :
  valid_accessor_permutation p0 S -> valid_accessor_permutation p1 (rename_accessors p0 S) ->
  rename_accessors p1 (rename_accessors p0 S) =
  rename_accessors (compose_accessor_permutation p1 p0) S.
Proof.
  intros (? & H) (? & G). unfold rename_accessors in *. destruct S. cbn in *. f_equal.
  - symmetry. apply apply_permutation_compose; assumption.
  - apply map_eq. intros i. specialize (H i). specialize (G i). revert G. cbn.
    rewrite !map_lookup_zip_with. inversion H.
    + cbn. inversion 1. cbn. rewrite apply_permutation_compose; auto.
    + cbn. inversion 1. reflexivity.
Qed.

(* Why are conversions so bad? *)
Lemma loan_set_borrow l v :
  loan_set_val (borrow^m(l, v)) = union (singleton l) (loan_set_val v).
Proof. reflexivity. Qed.

Lemma rename_loan_id_borrow m l v :
  rename_value m (borrow^m(l, v)) = borrow^m(rename_loan_id m l, rename_value m v).
Proof. reflexivity. Qed.

Lemma rename_value_compose m0 m1 v
  (H : subseteq (loan_set_val v) (dom m0))
  (G : subseteq (loan_set_val (rename_value m0 v)) (dom m1)) :
  rename_value m1 (rename_value m0 v) = rename_value (map_compose m1 m0) v.
Proof.
  induction v; try reflexivity.
  - cbn. unfold rename_loan_id. setoid_rewrite map_lookup_compose.
    cbn in H. apply singleton_subseteq_l, elem_of_dom in H.
    destruct H as (l' & Hl'). setoid_rewrite Hl'. cbn.
    cbn in G. unfold rename_loan_id in G. setoid_rewrite Hl' in G.
    apply singleton_subseteq_l, elem_of_dom in G. destruct G as (l'' & Hl'').
    setoid_rewrite Hl''. reflexivity.
  - rewrite loan_set_borrow in H. rewrite rename_loan_id_borrow, loan_set_borrow in G.
    apply union_subseteq in H, G. rewrite singleton_subseteq_l in H, G.
    destruct H as (H & ?). destruct G as (G & ?).
    rewrite !rename_loan_id_borrow. rewrite IHv by assumption.
    unfold rename_loan_id. setoid_rewrite map_lookup_compose.
    apply elem_of_dom in H. destruct H as (l' & Hl'). setoid_rewrite Hl'. cbn.
    unfold rename_loan_id in G. setoid_rewrite Hl' in G. apply elem_of_dom in G.
    destruct G as (l'' & Hl''). setoid_rewrite Hl''. reflexivity.
Qed.

Lemma rename_state_compose S p1 p0 :
  valid_loan_id_names p0 S -> valid_loan_id_names p1 (rename_state p0 S) ->
  rename_state p1 (rename_state p0 S) = rename_state (map_compose p1 p0) S.
Proof.
  intros (? & ?) (? & ?). apply state_eq_ext.
  - rewrite !get_map_rename_state. rewrite <-map_fmap_compose.
    apply map_fmap_ext. intros i v get_v. apply rename_value_compose.
    + etransitivity; [ | eassumption]. eapply loan_set_val_subset_eq_loan_set_state; eassumption.
    + etransitivity; [ | eassumption]. eapply loan_set_val_subset_eq_loan_set_state.
      rewrite get_map_rename_state, lookup_fmap, get_v. reflexivity.
  - unfold get_extra. cbn. rewrite !dom_fmap_L. reflexivity.
Qed.

Lemma apply_state_permutation_compose S p1 p0 :
  is_state_equivalence p0 S -> is_state_equivalence p1 (apply_state_permutation p0 S) ->
  apply_state_permutation p1 (apply_state_permutation p0 S) =
  apply_state_permutation (compose_state_permutation p1 p0) S.
Proof.
  intros (? & ?) (G & K). unfold apply_state_permutation.
  assert (valid_accessor_permutation (accessor_perm p0) (rename_state (loan_id_names p0) S)).
  { rewrite rename_state_preserves_accessor_perm_validity. assumption. }
  unfold apply_state_permutation in K.
  rewrite rename_accessor_preserves_loan_validity in K by assumption.
  rewrite apply_state_permutation_alt in G by assumption.
  rewrite rename_state_preserves_accessor_perm_validity in G.
  rewrite <-rename_accessors_rename_state_commute by assumption.
  rewrite rename_state_compose by assumption.
  rewrite rename_accessors_compose.
  - reflexivity.
  - rewrite rename_state_preserves_accessor_perm_validity. assumption.
  - rewrite rename_accessors_rename_state_commute by assumption.
    rewrite rename_state_preserves_accessor_perm_validity. assumption.
Qed.

Instance equiv_states_transitive : Transitive equiv_states.
Proof.
  intros S ? ? (p0 & p0_perm & ->) (p1 & p1_perm & ->).
  exists (compose_state_permutation p1 p0). split.
  - apply is_permutation_compose; assumption.
  - apply apply_state_permutation_compose; assumption.
Qed.

Instance transitive_equiv_val_state : Transitive equiv_val_state.
Proof.
  intros (v & S) (? & ?) (? & ?) (p0 & ? & H & -> & ->) (p1 & ? & G & -> & ->).
  exists (compose_state_permutation p1 p0). split.
  - apply is_permutation_compose; assumption.
  - rewrite apply_state_permutation_compose, rename_value_compose by assumption.
    split; [ | auto].
    intros l Hl. specialize (H l Hl).
    apply elem_of_dom. setoid_rewrite map_lookup_compose. apply elem_of_dom in H.
    destruct H as (l' & Hl'). rewrite Hl'. cbn.
    apply elem_of_dom, G.
    apply elem_of_loan_set_val in Hl. destruct Hl as (p & get_l).
    rewrite elem_of_loan_set_val. exists p.
    rewrite <-vget_rename_value, get_node_rename_value, get_loan_id_rename_node.
    rewrite get_l. cbn. unfold rename_loan_id. setoid_rewrite Hl'. reflexivity.
Qed.

Definition invert_accessor_perm perm := {|
  anons_perm := invert_permutation (anons_perm perm);
  abstractions_perm := fmap invert_permutation (abstractions_perm perm);
|}.

Definition invert_state_permutation perm := {|
  accessor_perm := invert_accessor_perm (accessor_perm perm);
  loan_id_names := invert_permutation (loan_id_names perm);
|}.

Lemma invert_valid_accessor_perm perm S :
  valid_accessor_permutation perm S ->
  valid_accessor_permutation (invert_accessor_perm perm) (rename_accessors perm S).
Proof.
  intros (? & Habs_perm). split.
  - apply invert_permutation_is_permutation. assumption.
  - intros i. specialize (Habs_perm i). cbn. simpl_map. rewrite map_lookup_zip_with.
    inversion Habs_perm as [? ? ? | ].
    + constructor. apply invert_permutation_is_permutation. assumption.
    + constructor.
Qed.

Lemma invert_valid_loan_id_names perm S :
  valid_loan_id_names perm S ->
  valid_loan_id_names (invert_permutation perm) (rename_state perm S).
Proof.
  intros (loan_map_inj & Hinclusion). split.
  + apply invert_permutation_inj. assumption.
  + intros l. rewrite elem_of_loan_set_state. intros (p & get_l).
    rewrite rename_state_sget in get_l.
    rewrite get_node_rename_value, get_loan_id_rename_node, fmap_Some in get_l.
    destruct get_l as (l' & ? & ?).
    cbn. rewrite dom_invert_permutation, elem_of_map_img by assumption.
    exists l'. subst. unfold rename_loan_id. autodestruct.
    intros K%not_elem_of_dom. exfalso. apply K, Hinclusion.
    apply elem_of_loan_set_state. exists p. assumption.
Qed.

Lemma invert_state_permutation_is_permutation perm S :
  is_state_equivalence perm S ->
  is_state_equivalence (invert_state_permutation perm) (apply_state_permutation perm S).
Proof.
  intros (? & ?). split.
  - apply invert_valid_accessor_perm, rename_state_preserves_accessor_perm_validity, H.
  - rewrite apply_state_permutation_alt by assumption.
    apply invert_valid_loan_id_names,  rename_accessor_preserves_loan_validity; assumption.
Qed.

Lemma rename_state_invert_permutation S perm (H : valid_loan_id_names perm S) :
  rename_state (invert_permutation perm) (rename_state perm S) = S.
Proof.
  rewrite rename_state_compose by auto using invert_valid_loan_id_names.
  destruct H. apply state_eq_ext.
  - rewrite get_map_rename_state. rewrite compose_invert_permutation by assumption.
    apply map_eq. intros i. rewrite lookup_fmap.
    destruct (get_at_accessor S i); [ | reflexivity]. cbn. f_equal.
    apply rename_value_id, lookup_id_permutation_is_Some.
  - cbn. rewrite !dom_fmap_L. reflexivity.
Qed.

Lemma apply_invert_state_permutation perm S (H : is_state_equivalence perm S) :
  apply_state_permutation (invert_state_permutation perm) (apply_state_permutation perm S) = S.
Proof.
  rewrite apply_state_permutation_compose; auto using invert_state_permutation_is_permutation.
  destruct H as (((? & ?) & H) & ?). unfold apply_state_permutation. cbn.
  rewrite <-rename_state_compose by auto using invert_valid_loan_id_names.
  rewrite rename_state_invert_permutation by assumption.
  unfold rename_accessors, compose_state_permutation. destruct S. cbn. f_equal.
  - rewrite compose_invert_permutation by assumption.
    erewrite id_permutation_same_domain, apply_id_permutation; eauto.
  - apply map_eq. intros i. rewrite !map_lookup_zip_with, lookup_fmap.
    cbn in H. specialize (H i). inversion H as [? ? (? & ?) | ]; [ | reflexivity].
    cbn. f_equal. rewrite compose_invert_permutation by assumption.
    erewrite id_permutation_same_domain, apply_id_permutation; eauto.
Qed.

Instance equiv_states_symmetric : Symmetric equiv_states.
Proof.
  intros S ? (p & Hp & ->). exists (invert_state_permutation p). split.
  - apply invert_state_permutation_is_permutation. assumption.
  - symmetry. apply apply_invert_state_permutation. assumption.
Qed.

(* Note: we do a similar reasonning to prove that that invert_state_permutation is a permutation.
 * Some parts could be factorized. *)
Lemma loan_set_rename_value v m (Hv : subseteq (loan_set_val v) (dom m)) (Hm : map_inj m) :
  subseteq (loan_set_val (rename_value m v)) (dom (invert_permutation m)).
Proof.
  intros l (q & Hq)%elem_of_loan_set_val.
  rewrite dom_invert_permutation, elem_of_map_img by assumption.
  rewrite <-vget_rename_value, get_node_rename_value, get_loan_id_rename_node in Hq.
  destruct (get_loan_id _) as [l' | ] eqn:EQN; [ | discriminate].
  exists l'. injection Hq. unfold rename_loan_id.
  specialize (Hv l'). setoid_rewrite elem_of_dom in Hv. destruct Hv as (l'' & G).
  { apply elem_of_loan_set_val. exists q. assumption. }
  setoid_rewrite G. congruence.
Qed.

Instance equiv_val_state_symmetric : Symmetric equiv_val_state.
Proof.
  intros (v & S) (? & ?) (p & Hp & Hv & -> & ->). exists (invert_state_permutation p).
  split; [ | split; [ | split] ].
  - apply invert_state_permutation_is_permutation. assumption.
  - apply loan_set_rename_value; [exact Hv | apply Hp].
  - symmetry. apply apply_invert_state_permutation. assumption.
  - cbn. rewrite rename_value_compose.
    + rewrite compose_invert_permutation by apply Hp. symmetry. apply rename_value_id.
      intros ? ?. apply lookup_id_permutation_is_Some.
    + assumption.
    + apply loan_set_rename_value; [exact Hv | apply Hp].
Qed.

Lemma equiv_val_state_weaken v0 S0 v1 S1 : equiv_val_state (v0, S0) (v1, S1) -> equiv_states S0 S1.
Proof. intros (perm & ? & _ & ? & _). exists perm. auto. Qed.

Lemma permutation_spath_disj S perm p q :
  is_state_equivalence perm S -> valid_spath S p -> valid_spath S q -> disj p q ->
  disj (permutation_spath perm p) (permutation_spath perm q).
Proof.
  intros (? & _) (? & get_at_p & ?) (? & get_at_q & ?) Hdisj. unfold permutation_spath.
  eapply get_at_accessor_state_permutation in get_at_p, get_at_q; [ | eassumption..].
  destruct get_at_p as (? & get_at_p & _). destruct get_at_q as (? & get_at_q & _).
  rewrite get_at_p, get_at_q.
  destruct Hdisj as [diff_acc | (? & ?)].
  - left. cbn. intros ?. eapply diff_acc.
    eapply permutation_accessor_inj; [eassumption | auto | congruence].
  - right. cbn. split; [congruence | assumption].
Qed.
Hint Resolve permutation_spath_disj : spath.

Lemma sset_abstractions_dom S sp v :
  map_Forall2 (fun _ A A' => dom A = dom A') (abstractions S) (abstractions (S.[sp <- v])).
Proof.
  intros i.
  assert (is_Some (lookup i (abstractions S)) <-> is_Some (lookup i (abstractions (S.[sp <- v])))).
  { rewrite <-!elem_of_dom.
    replace (dom (abstractions S)) with (get_extra S) by reflexivity.
    replace (dom (abstractions (S .[sp <- v]))) with (get_extra (S.[sp <- v])) by reflexivity.
    unfold sset. rewrite get_extra_alter. reflexivity. }
  destruct (lookup i (abstractions S)) eqn:?;
  destruct (lookup i (abstractions (S.[sp <- v]))) eqn:?.
  - constructor. apply set_eq. intros j. rewrite !elem_of_dom.
    erewrite <-get_at_abstraction' by eassumption.
    symmetry. erewrite <-get_at_abstraction' by eassumption.
    unfold sset. rewrite get_map_alter. apply lookup_alter_is_Some.
  - destruct H as (H & _). destruct H; easy.
  - destruct H as (_ & H). destruct H; easy.
  - constructor.
Qed.

Lemma loan_set_vget v p (H : valid_vpath v p) : subseteq (loan_set_val (v.[[p]])) (loan_set_val v).
Proof.
  induction H as [ | v ? ? ? H].
  - reflexivity.
  - destruct v; try now rewrite nth_error_nil in H.
    apply nth_error_singleton in H. destruct H as (<- & ->). set_solver.
Qed.

Lemma loan_set_sget S p : subseteq (loan_set_val (S.[p])) (loan_set_state S).
Proof.
  destruct (decidable_valid_spath S p) as [(w & get_w & H) | ].
  - apply insert_delete in get_w. unfold loan_set_state, sget. rewrite <-get_w at 1 2.
    simpl_map. rewrite !map_fold_insert_L by (simpl_map; auto; set_solver).
    pose proof (loan_set_vget _ _ H). set_solver.
  - rewrite sget_invalid by assumption. set_solver.
Qed.

Lemma loan_set_vset v p w (H : valid_vpath v p) :
  subseteq (loan_set_val (v.[[p <- w]])) (union (loan_set_val v) (loan_set_val w)).
Proof.
  induction H as [ | v ? ? ? H].
  - set_solver.
  - destruct v; try now rewrite nth_error_nil in H.
    apply nth_error_singleton in H. destruct H as (<- & ->).
    rewrite vset_at_borrow', !loan_set_borrow. set_solver.
Qed.

Lemma loan_set_sset S p v :
  subseteq (loan_set_state (S.[p <- v])) (union (loan_set_state S) (loan_set_val v)).
Proof.
  destruct (decidable_valid_spath S p) as [(w & get_w & H) | ].
  - apply insert_delete in get_w. unfold loan_set_state, sset.
    rewrite get_map_alter. rewrite <-get_w at 1 2. rewrite alter_insert.
    rewrite !map_fold_insert_L by (simpl_map; auto; set_solver).
    pose proof (loan_set_vset _ _ v H). set_solver.
  - rewrite sset_invalid by assumption. set_solver.
Qed.

Lemma valid_loan_id_names_sset perm S sp v
  (loan_v_subset : subseteq (loan_set_val v) (dom perm)) :
  valid_loan_id_names perm S -> valid_loan_id_names perm (S.[sp <- v]).
Proof.
  intros (? & ?).  split; [assumption | ]. etransitivity; [apply loan_set_sset | ]. set_solver.
Qed.

Lemma valid_accessor_permutation_sset perm S sp v :
  valid_accessor_permutation perm S -> valid_accessor_permutation perm (S.[sp <- v]).
Proof.
  intros ((? & H) & G). split.
  - split; [assumption | ]. intros a. rewrite H. rewrite <-!get_at_anon.
    rewrite <-!elem_of_dom. unfold sset. rewrite get_map_alter, dom_alter. reflexivity.
  - intros i. specialize (G i).
    remember (lookup i (abstractions S)) as A eqn:EQN_A.
    remember (lookup i (abstractions_perm perm)) as perm_A.
    destruct G as [? ? G | ].
    + pose proof (sset_abstractions_dom S sp v i) as dom_abs.
      rewrite <-EQN_A in dom_abs.
      remember (lookup i (abstractions (S.[sp <- v]))).
      inversion dom_abs as [? ? eq_dom | ]; subst. constructor.
      unfold is_permutation. destruct G. setoid_rewrite <-elem_of_dom.
      rewrite <-eq_dom. setoid_rewrite elem_of_dom. split; assumption.
    + assert (fresh_abstraction S i) as G by easy.
      rewrite fresh_abstraction_sset in G. rewrite G. constructor.
Qed.

Lemma is_state_equivalence_sset perm S sp v
  (loan_v_subset : subseteq (loan_set_val v) (dom (loan_id_names perm))) :
  is_state_equivalence perm S -> is_state_equivalence perm (S.[sp <- v]).
Proof.
  intros (? & ?). split.
  - apply valid_accessor_permutation_sset. assumption.
  - apply valid_loan_id_names_sset; assumption.
Qed.

Lemma is_state_equivalence_sset_rev perm S sp v :
  subseteq (loan_set_val (S.[sp])) (dom (loan_id_names perm)) ->
  is_state_equivalence perm (S.[sp <- v]) -> is_state_equivalence perm S.
Proof.
  intros. erewrite <-sset_same, <-sset_twice_equal. apply is_state_equivalence_sset; eassumption.
Qed.

Lemma rename_state_sset S perm v sp
  (loan_v_subset : subseteq (loan_set_val v) (dom perm)) :
  (rename_state perm (S.[sp <- v])) = (rename_state perm S).[sp <- rename_value perm v].
Proof.
  unfold sset. apply state_eq_ext.
  - rewrite get_map_alter, !get_map_rename_state, get_map_alter.
    destruct (get_at_accessor S (fst sp)) eqn:EQN.
    + erewrite !alter_insert_delete by (simpl_map; reflexivity).
      rewrite fmap_insert, fmap_delete, vset_rename_value. reflexivity.
    + rewrite !map_alter_not_in_domain; simpl_map; rewrite ?EQN; reflexivity.
  - rewrite get_extra_alter, !get_extra_rename_state, get_extra_alter. reflexivity.
Qed.

Lemma permutation_sset S perm v (H : is_state_equivalence perm S) sp
  (valid_sp : valid_spath S sp)
  (loan_v_subset : subseteq (loan_set_val v) (dom (loan_id_names perm))) :
  (apply_state_permutation perm (S.[sp <- v])) =
  (apply_state_permutation perm S).[permutation_spath perm sp <- rename_value (loan_id_names perm) v].
Proof.
  unfold apply_state_permutation. rewrite rename_state_sset by assumption.
  destruct H as (H & _). destruct valid_sp as (w & G & _).
  assert (valid_accessor_permutation (accessor_perm perm) (rename_state (loan_id_names perm) S)).
  { rewrite rename_state_preserves_accessor_perm_validity. assumption. }
  apply state_eq_ext.
  - rewrite get_map_rename_accessors by auto using valid_accessor_permutation_sset.
    unfold sset. rewrite !get_map_alter.
    rewrite get_map_rename_accessors by assumption. unfold permutation_spath.
    edestruct get_at_accessor_rename_accessors as (i & K & ?); [exact H | exact G | ].
    rewrite !K. erewrite alter_pkmap by eauto using permutation_accessor_is_equivalence.
    apply map_eq. intros j. rewrite !fst_pair, !snd_pair.
    destruct (decide (i = j)) as [<- | ].
    * simpl_map. destruct (lookup i (pkmap _ _)) eqn:?; reflexivity.
    * simpl_map. reflexivity.
  - rewrite get_extra_rename_accessors by now apply valid_accessor_permutation_sset.
    unfold sset. rewrite !get_extra_alter. symmetry.
    apply get_extra_rename_accessors. assumption.
Qed.

Lemma loan_set_add_anon S a v (H : fresh_anon S a) :
  loan_set_state (S,, a |-> v) = union (loan_set_state S) (loan_set_val v).
Proof. unfold loan_set_state. rewrite get_map_add_anon, map_fold_insert_L; set_solver. Qed.

Definition add_anon_perm perm a b := {|
  accessor_perm := {|
    anons_perm := insert a b (anons_perm (accessor_perm perm));
    abstractions_perm := abstractions_perm (accessor_perm perm);
  |};
  loan_id_names := loan_id_names perm;
|}.

Lemma add_anon_perm_equivalence perm S a b v
  (loan_v_subset : subseteq (loan_set_val v) (dom (loan_id_names perm))) :
  fresh_anon S a -> fresh_anon (apply_state_permutation perm S) b ->
  is_state_equivalence perm S -> is_state_equivalence (add_anon_perm perm a b) (S,, a |-> v).
Proof.
  intros fresh_a fresh_b p_is_state_equiv.
  unfold fresh_anon in fresh_b. rewrite get_at_anon in fresh_b. cbn in fresh_b.
  destruct p_is_state_equiv as (((? & eq_dom) & Habstractions_perm) & (? & ?)).
  split; split.
  - cbn. split.
    + apply map_inj_insert; [ | assumption]. intros ? get_i.
      erewrite lookup_pkmap in fresh_b; [ | now apply map_inj_equiv | eassumption].
      rewrite eq_None_not_Some, lookup_fmap, fmap_is_Some, <-eq_dom, get_i in fresh_b. auto.
    + setoid_rewrite lookup_insert_is_Some. intros i. specialize (eq_dom i). tauto.
  - exact Habstractions_perm.
  - assumption.
  - rewrite loan_set_add_anon by assumption. set_solver.
Qed.
Hint Resolve add_anon_perm_equivalence : spath.

Lemma rename_state_add_anon S perm a v
  (loan_v_subset : subseteq (loan_set_val v) (dom perm)) :
  valid_loan_id_names perm S ->
  rename_state perm (S,, a |-> v) = (rename_state perm S),, a |-> rename_value perm v.
Proof.
  intros (_ & ?). apply state_eq_ext.
  - rewrite get_map_add_anon, !get_map_rename_state, get_map_add_anon.
    rewrite fmap_insert. reflexivity.
  - reflexivity.
Qed.

Lemma permutation_add_anon S perm a b v
  (loan_v_subset : subseteq (loan_set_val v) (dom (loan_id_names perm))) :
  is_state_equivalence perm S ->
  fresh_anon S a -> fresh_anon (apply_state_permutation perm S) b ->
  apply_state_permutation (add_anon_perm perm a b) (S,, a |-> v) =
      (apply_state_permutation perm S),, b |-> rename_value (loan_id_names perm) v.
Proof.
  intros ? fresh_a fresh_b.
  apply state_eq_ext.
  - assert (is_state_equivalence (add_anon_perm perm a b) (S,, a |-> v)) as G
      by now apply add_anon_perm_equivalence.
    rewrite get_map_state_permutation by apply G.
    rewrite !get_map_add_anon.
    rewrite get_map_state_permutation by apply H.
    destruct G as (G%permutation_accessor_is_equivalence & _).
    rewrite pkmap_insert; [ | apply G | exact fresh_a].
    unfold insert_permuted_key. rewrite perm_at_anon.
    cbn -[get_map anon_accessor]. simpl_map. cbn -[get_map anon_accessor]. rewrite fmap_insert.
    f_equal. f_equal. apply pkmap_fun_eq. intros i get_rel%get_at_accessor_is_Some.
    destruct get_rel as [ | a' ? get_a' | ].
    + rewrite !perm_at_var. reflexivity.
    + rewrite !perm_at_anon. unfold add_anon_perm. cbn.
      rewrite lookup_insert_ne by (rewrite <-get_at_anon in get_a'; congruence).
      reflexivity.
    + erewrite !perm_at_abstraction. reflexivity.
  - rewrite get_extra_state_permutation by now apply add_anon_perm_equivalence.
    rewrite !get_extra_add_anon.
    symmetry. apply get_extra_state_permutation. assumption.
Qed.

Lemma equiv_states_add_anon S a b v :
  fresh_anon S a -> fresh_anon S b ->
  equiv_states_up_to_accessor_permutation (S,, a |-> v) (S,, b |-> v).
Proof.
  intros fresh_a fresh_a'. apply equiv_states_by_anons_equivalence.
  - unfold fresh_anon in * |-. rewrite get_at_anon in * |-. now apply equiv_map_insert.
  - reflexivity.
  - reflexivity.
Qed.

Definition remove_anon_perm perm a := {|
  accessor_perm := {|
    anons_perm := delete a (anons_perm (accessor_perm perm));
    abstractions_perm := abstractions_perm (accessor_perm perm);
  |};
  loan_id_names := loan_id_names perm;
|}.

Lemma remove_anon_perm_equivalence perm S a v :
  fresh_anon S a -> is_state_equivalence perm (S,, a |-> v) ->
  is_state_equivalence (remove_anon_perm perm a) S /\
  exists b, perm = add_anon_perm (remove_anon_perm perm a) a b /\
            fresh_anon (apply_state_permutation (remove_anon_perm perm a) S) b /\
            subseteq (loan_set_val v) (dom (loan_id_names perm)).
Proof.
  intros ? p_is_state_equiv.
  destruct p_is_state_equiv as (((anons_perm_inj & eq_dom) & Habstractions_perm) & (? & ?)).
  rewrite loan_set_add_anon in * |- by assumption.
  split; [split; split | ].
  - cbn. split.
    + intros ? ? (_ & ?)%lookup_delete_Some ? ? (_ & ?)%lookup_delete_Some ?.
      eapply anons_perm_inj; eassumption.
    + intros i. setoid_rewrite lookup_delete_is_Some.
      specialize (eq_dom i). cbn in eq_dom. rewrite lookup_insert_is_Some' in eq_dom.
      unfold fresh_anon in H.
      split.
      -- intuition.
      -- intros ?. rewrite get_at_anon, eq_None_not_Some in H.
        assert (a <> i) by now intros <-. intuition.
  - exact Habstractions_perm.
  - assumption.
  - set_solver.
  - pose proof (eq_dom a) as (_ & (b & G)). { cbn. simpl_map. easy. }
    exists b. repeat split.
    + unfold add_anon_perm, remove_anon_perm. destruct perm as (perm & ?). destruct perm.
      cbn. rewrite insert_delete; easy.
    + unfold fresh_anon. rewrite get_at_anon. cbn.
      replace (anons S) with (delete a (anons (S,, a |-> v))).
      2: { cbn. rewrite delete_insert by now rewrite <-get_at_anon. reflexivity. }
      erewrite fmap_delete, apply_permutation_delete by eassumption. simpl_map. reflexivity.
    + set_solver.
Qed.

Lemma permutation_fresh_abstraction S p i :
  fresh_abstraction S i -> fresh_abstraction (apply_state_permutation p S) i.
Proof.
  unfold fresh_abstraction. cbn. rewrite map_lookup_zip_with_None, lookup_fmap. intros ->. auto.
Qed.

Corollary equiv_states_fresh_abstraction S S' i :
  equiv_states S S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof. intros (? & ? & ->). apply permutation_fresh_abstraction. Qed.

Definition loan_set_abstraction (A : Pmap LLBC_plus_val) : Pset :=
  map_fold (fun _ v L => union (loan_set_val v) L) empty A.

Lemma loan_set_abstraction_union A B (H : map_disjoint A B) :
  loan_set_abstraction (union A B) = union (loan_set_abstraction A) (loan_set_abstraction B).
Proof.
  unfold loan_set_abstraction. rewrite map_fold_disj_union by set_solver.
  clear H. induction A using map_first_key_ind.
  - rewrite !map_fold_empty. set_solver.
  - rewrite !map_fold_insert_first_key by assumption. set_solver.
Qed.

Lemma loan_set_abstraction_kmap f A (H : Inj eq eq f) :
  loan_set_abstraction (kmap f A) = loan_set_abstraction A.
Proof.
  unfold loan_set_abstraction. induction A using map_first_key_ind.
  - reflexivity.
  - rewrite map_fold_insert_first_key by assumption. rewrite kmap_insert by assumption.
    rewrite map_fold_insert_L; [set_solver.. | ]. rewrite lookup_kmap; assumption.
Qed.

Lemma loan_set_add_abstraction S i A (H : fresh_abstraction S i) :
  loan_set_state (S,,, i |-> A) = union (loan_set_state S) (loan_set_abstraction A).
Proof.
  replace (loan_set_state S) with (loan_set_abstraction (get_map S)) by reflexivity.
  replace (loan_set_state (S,,, i |-> A)) with (loan_set_abstraction (get_map (S,,, i |-> A)))
    by reflexivity.
  rewrite get_map_add_abstraction by assumption. rewrite loan_set_abstraction_union.
  - rewrite loan_set_abstraction_kmap by typeclasses eauto. reflexivity.
  - apply map_disjoint_spec. intros ? ? ? G.
    rewrite lookup_kmap_Some by typeclasses eauto. intros (j & -> & ?).
    rewrite get_at_abstraction, H in G. discriminate.
Qed.

Lemma add_anons_rename_accessors perm p S0 A S1 S'1 :
  is_permutation (anons_perm perm) (anons S0) ->
  map_Forall2 (fun k => is_permutation) (abstractions_perm perm) (abstractions S0) ->
  is_permutation p A ->
  let S'0 := rename_accessors perm S0 in
  let B := apply_permutation p A in
  add_anons S0 A S1 -> add_anons S'0 B S'1 ->
  equiv_states_up_to_accessor_permutation S1 S'1.
Proof.
  intros ? ? ? S'0 B.
  inversion 1 as [? ? anons0]. subst. inversion 1 as [? ? anons1 Hunion]; subst. cbn.
  eapply union_maps_invert_permutation in Hunion; [ | assumption..].
  destruct Hunion as (X & ? & Hunion).
  assert (equiv_map anons0 anons1) as (q & q_equiv & ->)%equiv_map_alt.
  { transitivity X; [ | assumption]. eapply union_maps_unique; eassumption. }
  exists {|anons_perm := q;
           abstractions_perm := abstractions_perm perm|}.
  split; [ | reflexivity]. split; assumption.
Qed.

Lemma add_anons_rename_state perm S A S' :
  add_anons S A S' -> add_anons (rename_state perm S) (rename_set perm A) (rename_state perm S').
Proof.
  inversion 1 as [? ? ? Hunion]; subst.
  unfold rename_state; cbn. econstructor. apply union_maps_fmap. assumption.
Qed.

Lemma loan_set_add_anons S A S' :
  add_anons S A S' -> loan_set_state S' = union (loan_set_state S) (loan_set_abstraction A).
Proof.
  rewrite add_anons_alt. unfold loan_set_abstraction. induction 1.
  - rewrite map_fold_empty. set_solver.
  - rewrite map_fold_insert_L by set_solver.
    rewrite loan_set_add_anon in * |- by assumption. set_solver.
Qed.

Lemma add_anons_equiv perm p S0 A S1 S'1 :
  is_state_equivalence perm S0 -> is_permutation p A ->
  subseteq (loan_set_abstraction A) (dom (loan_id_names perm)) ->
  let S'0 := apply_state_permutation perm S0 in
  let B := apply_permutation p (rename_set (loan_id_names perm) A) in
  add_anons S0 A S1 -> add_anons S'0 B S'1 -> equiv_states S1 S'1.
Proof.
  intros ((? & H) & (? & ?)) G Hincl S'0 B.
  intros Hadd_anons ?.
  eapply prove_equiv_states.
  - exists (loan_id_names perm). split; [ | reflexivity]. split; [assumption | ].
    pose proof (loan_set_add_anons _ _ _ Hadd_anons). set_solver.
  - apply (add_anons_rename_state (loan_id_names perm)) in Hadd_anons.
    eapply add_anons_rename_accessors; [.. | eassumption].
    + apply is_permutation_fmap. assumption.
    + intros i. specialize (H i). cbn in *. simpl_map. destruct (lookup i (abstractions S0)); [ | assumption].
      inversion H. constructor. apply is_permutation_fmap. assumption.
    + apply is_permutation_fmap. assumption.
    + eassumption.
Qed.

Definition add_abstraction_accessor_permutation perm i p := {|
  anons_perm := anons_perm perm;
  abstractions_perm := insert i p (abstractions_perm perm);
|}.

Definition add_abstraction_perm perm i p := {|
  accessor_perm := add_abstraction_accessor_permutation (accessor_perm perm) i p;
  loan_id_names := loan_id_names perm;
|}.

Lemma add_abstraction_valid_accessor_permutation S perm p i A :
  valid_accessor_permutation perm S -> is_permutation p A ->
  valid_accessor_permutation (add_abstraction_accessor_permutation perm i p) (S,,, i |-> A).
Proof.
  intros (? & ?) ?. split.
  - assumption.
  - apply map_Forall2_insert_2; assumption.
Qed.

(* Note: the hypothesis [fresh_abstraction S i] could be removed. *)
Lemma add_abstraction_perm_equivalence perm S i A p :
  is_state_equivalence perm S -> is_permutation p A ->
  subseteq (loan_set_abstraction A) (dom (loan_id_names perm)) -> fresh_abstraction S i ->
  is_state_equivalence (add_abstraction_perm perm i p) (S,,, i |-> A).
Proof.
  intros (? & (? & ?)) ? ? ?. split; [ | split].
  - apply add_abstraction_valid_accessor_permutation; assumption.
  - assumption.
  - rewrite loan_set_add_abstraction by assumption. set_solver.
Qed.
Hint Resolve add_abstraction_perm_equivalence : spath.

Lemma rename_state_add_abstraction S perm i A (H : fresh_abstraction S i) :
  rename_state perm (S,,, i |-> A) = (rename_state perm S),,, i |-> rename_set perm A.
Proof.
  assert (fresh_abstraction (rename_state perm S) i).
  { unfold fresh_abstraction. cbn. rewrite lookup_fmap, H. reflexivity. }
  apply state_eq_ext.
  - rewrite get_map_rename_state. rewrite !get_map_add_abstraction by assumption.
    rewrite get_map_rename_state. rewrite map_fmap_union, kmap_fmap by typeclasses eauto.
    reflexivity.
  - rewrite get_extra_add_abstraction. cbn -[singleton].
    rewrite fmap_insert, dom_insert_L. reflexivity.
Qed.

Lemma rename_accessors_add_abstraction S perm p i A :
  fresh_abstraction S i -> valid_accessor_permutation perm S -> is_permutation p A ->
  rename_accessors (add_abstraction_accessor_permutation perm i p) (S,,, i |-> A) =
  rename_accessors perm S,,, i |-> apply_permutation p A.
Proof.
  intros fresh_A Hstate_perm p_is_perm.
  pose proof (add_abstraction_valid_accessor_permutation S perm p i A Hstate_perm p_is_perm) as G.
  apply state_eq_ext.
  - rewrite get_map_rename_accessors by assumption.
    apply pkmap_eq.
    + apply permutation_accessor_is_equivalence. assumption.
    + intros ? ? perm_rel%permutation_accessor_is_Some.
      destruct perm_rel as [ | | i' ? ? ? perm_at_i].
      * rewrite !get_at_var. reflexivity.
      * rewrite !get_at_anon. cbn. erewrite lookup_pkmap;
          [reflexivity | apply map_inj_equiv, G | assumption].
      * erewrite !get_at_abstraction.
        destruct (decide (i = i')) as [<- | ].
        -- cbn in *. simpl_map. inversion perm_at_i; subst. symmetry. cbn.
           apply lookup_pkmap; [apply map_inj_equiv, p_is_perm | assumption].
        -- cbn in *. simpl_map. rewrite map_lookup_zip_with, perm_at_i. cbn.
           destruct Hstate_perm as (_ & Habstractions_perm).
           specialize (Habstractions_perm i'). rewrite perm_at_i in Habstractions_perm.
           inversion Habstractions_perm as [? B (? & _) | ].
           cbn. symmetry. apply lookup_pkmap; [apply map_inj_equiv | ]; assumption.
    + cbn. rewrite !size_sum_maps.
      rewrite flatten_insert by now rewrite fresh_A.
      rewrite flatten_insert by (apply map_lookup_zip_with_None; auto).
      rewrite !map_size_disj_union by
        (apply disj_kmap_flatten; rewrite ?map_lookup_zip_with_None; auto).
      rewrite !size_kmap by typeclasses eauto.
      destruct Hstate_perm as (? & Habstractions_perm).
      rewrite !size_pkmap by now apply permutation_is_equivalence.
      f_equal. f_equal. apply size_flatten.
      intros i'. rewrite map_lookup_zip_with.
      specialize (Habstractions_perm i'). destruct Habstractions_perm; constructor.
      symmetry. apply size_pkmap, permutation_is_equivalence. assumption.
  - rewrite get_extra_add_abstraction, !get_extra_rename_accessors by assumption.
    apply get_extra_add_abstraction.
Qed.

Lemma permutation_add_abstraction S perm p i A :
  fresh_abstraction S i -> is_state_equivalence perm S -> is_permutation p A ->
  subseteq (loan_set_abstraction A) (dom (loan_id_names perm)) ->
  apply_state_permutation (add_abstraction_perm perm i p) (S,,, i |-> A) =
  apply_state_permutation perm S,,, i |-> apply_permutation p (rename_set (loan_id_names perm) A).
Proof.
  intros H (? & ?) G ?.
  rewrite !apply_state_permutation_alt by
    (try apply add_abstraction_valid_accessor_permutation; assumption).
  cbn. rewrite rename_accessors_add_abstraction by assumption.
  rewrite rename_state_add_abstraction.
  - rewrite pkmap_fmap; [reflexivity | apply map_inj_equiv, G].
  - unfold fresh_abstraction. cbn. rewrite map_lookup_zip_with, H.
    destruct (lookup i _); reflexivity.
Qed.

Lemma equiv_add_abstraction S S' i A :
  equiv_states_up_to_accessor_permutation S S' -> fresh_abstraction S i ->
  equiv_states_up_to_accessor_permutation (S,,, i |-> A) (S',,, i |-> A).
Proof.
  intros (perm & Hperm & ->) ?.
  exists (add_abstraction_accessor_permutation perm i (id_permutation A)).
  pose proof (id_permutation_is_permutation A). split.
  - apply add_abstraction_valid_accessor_permutation; assumption.
  - rewrite rename_accessors_add_abstraction by assumption.
    rewrite apply_id_permutation. reflexivity.
Qed.

Definition remove_abstraction_perm perm i := {|
  accessor_perm := {|
    anons_perm := anons_perm (accessor_perm perm);
    abstractions_perm := delete i (abstractions_perm (accessor_perm perm));
  |};
  loan_id_names := loan_id_names perm;
|}.

Lemma remove_abstraction_perm_equivalence perm S i A :
  fresh_abstraction S i ->
  is_state_equivalence perm (S,,, i |-> A) ->
  is_state_equivalence (remove_abstraction_perm perm i) S /\
  exists p, is_permutation p A /\ perm = add_abstraction_perm (remove_abstraction_perm perm i) i p /\ subseteq (loan_set_abstraction A) (dom (loan_id_names (remove_abstraction_perm perm i))).
Proof.
  intros ? ((? & H) & (? & ?)). rewrite loan_set_add_abstraction in * |- by assumption.
  split; [split; split | ].
  - assumption.
  - replace (abstractions S) with (delete i (abstractions (S,,, i |-> A))).
    2: { cbn. now rewrite delete_insert. }
    apply map_Forall2_delete. assumption.
  - assumption.
  - set_solver.
  - specialize (H i). cbn in H. simpl_map. inversion H. eexists. split; [eassumption | split].
    + unfold add_abstraction_perm, remove_abstraction_perm, add_abstraction_accessor_permutation.
      cbn. rewrite insert_delete by congruence.
      destruct perm as (perm & ?). destruct perm. reflexivity.
    + set_solver.
Qed.

Definition remove_abstraction_value_perm perm i j := {|
  accessor_perm := {|
    anons_perm := anons_perm (accessor_perm perm);
    abstractions_perm := alter (delete j) i (abstractions_perm (accessor_perm perm));
  |};
  loan_id_names := loan_id_names perm;
|}.

Lemma remove_abstraction_value_perm_equivalence perm S i j :
  is_state_equivalence perm S ->
  is_state_equivalence (remove_abstraction_value_perm perm i j) (remove_abstraction_value S i j).
Proof.
  intros ((? & H) & (? & G)). split; split.
  - assumption.
  - cbn. intros i'. destruct (decide (i = i')) as [<- | ]; simpl_map.
    + destruct (H i) as [p ? (p_inj & ?) | ]; constructor. split.
      * intros ? ? (_ & ?)%lookup_delete_Some ? ? (_ & ?)%lookup_delete_Some.
        apply p_inj; assumption.
      * setoid_rewrite lookup_delete_is_Some. firstorder.
    + apply H.
  - assumption.
  - cbn. unfold loan_set_state in *. rewrite get_map_remove_abstraction_value.
    destruct (get_at_accessor S (encode_abstraction (i, j))) eqn:?.
    + erewrite map_fold_delete_L in G; set_solver.
    + rewrite delete_notin by assumption. exact G.
Qed.

Lemma remove_abstraction_value_permutation_accessor perm i j acc acc':
  permutation_accessor (accessor_perm (remove_abstraction_value_perm perm i j)) acc = Some acc' <->
  permutation_accessor (accessor_perm perm) acc = Some acc' /\ acc <> encode_abstraction (i, j).
Proof.
  split.
  - intros H%permutation_accessor_is_Some. destruct H as [ | | i'].
    + rewrite perm_at_var. split; [reflexivity | inversion 1].
    + cbn in get_a. rewrite perm_at_anon, get_a. split; [constructor | inversion 1].
    + rewrite perm_at_abstraction. cbn in get_i. destruct (decide (i = i')) as [<- | ].
      * simpl_map. destruct (lookup i (abstractions_perm _)); [ | inversion get_i].
        inversion get_i. subst. cbn.
        rewrite lookup_delete_Some in get_j. destruct get_j as (? & ->).
        split; [reflexivity | ]. intros ?%encode_inj. congruence.
      * simpl_map. cbn. rewrite get_j. split; [reflexivity | ].
        intros ?%encode_inj. congruence.
  - intros (H%permutation_accessor_is_Some & ?).  destruct H as [ | | i'].
    + apply perm_at_var.
    + rewrite perm_at_anon. cbn. rewrite get_a. constructor.
    + rewrite perm_at_abstraction. cbn. destruct (decide (i = i')) as [<- | ].
      * simpl_map. cbn. rewrite lookup_delete_ne, get_j by congruence. reflexivity.
      * simpl_map. cbn. rewrite get_j. reflexivity.
Qed.

Lemma remove_abstraction_value_permutation_spath perm i j q :
  fst q <> encode_abstraction (i, j) ->
  permutation_spath (remove_abstraction_value_perm perm i j) q = permutation_spath perm q.
Proof.
  intros H. unfold permutation_spath.
  destruct (permutation_accessor _ (fst q)) eqn:EQN.
  - apply remove_abstraction_value_permutation_accessor in EQN.
    destruct EQN as (-> & _). reflexivity.
  - autodestruct. intros G.
    pose proof (conj G H) as K. apply remove_abstraction_value_permutation_accessor in K.
    congruence.
Qed.
Hint Rewrite remove_abstraction_value_permutation_spath using auto with spath : spath.

Lemma permutation_accessor_abstraction_element perm S i j :
  is_state_equivalence perm S -> is_Some (abstraction_element S i j) ->
  exists j',
    permutation_accessor (accessor_perm perm) (encode_abstraction (i, j)) = Some (encode_abstraction (i, j')).
Proof.
  intros ((_ & equiv_abs) & _) H%get_at_accessor_is_Some.
  inversion H as [ | | ? ? A ? get_A get_at_j eq_encode].
  apply encode_inj in eq_encode. inversion eq_encode; subst.
  specialize (equiv_abs i). rewrite get_A in equiv_abs.
  inversion equiv_abs as [p ? (_ & eq_dom) | ]; subst.
  apply mk_is_Some in get_at_j. rewrite <-eq_dom in get_at_j. destruct get_at_j as (j' & ?).
  exists j'. rewrite perm_at_abstraction. simpl_map. cbn. simpl_map. reflexivity.
Qed.

(* TODO: delete at some point. *)
Lemma rename_state_remove_abstraction_value S perm i j :
  rename_state perm (remove_abstraction_value S i j) =
  remove_abstraction_value (rename_state perm S) i j.
Proof.
  apply state_eq_ext.
  - rewrite get_map_rename_state, !get_map_remove_abstraction_value, get_map_rename_state.
    rewrite fmap_delete. reflexivity.
  - rewrite get_extra_rename_state, !get_extra_remove_abstraction_value, get_extra_rename_state.
    reflexivity.
Qed.

Lemma permutation_remove_abstraction_value S perm i j j' :
  is_state_equivalence perm S ->
  permutation_accessor (accessor_perm perm) (encode_abstraction (i, j)) = Some (encode_abstraction (i, j')) ->
  apply_state_permutation (remove_abstraction_value_perm perm i j) (remove_abstraction_value S i j) =
  remove_abstraction_value (apply_state_permutation perm S) i j'.
Proof.
  intros H ?. pose proof (remove_abstraction_value_perm_equivalence _ _ i j H) as G.
  destruct (H) as (L & ?). destruct (G) as (? & ?).
  pose proof (permutation_accessor_is_equivalence _ _ L) as K.
  apply state_eq_ext.
  - rewrite get_map_remove_abstraction_value.
    rewrite !get_map_state_permutation by assumption.
    rewrite get_map_remove_abstraction_value.
    erewrite <-fmap_delete, <-pkmap_delete; [ | apply K | eassumption].
    f_equal. apply pkmap_fun_eq.
    intros ? (? & get_rel)%lookup_delete_is_Some.
    apply get_at_accessor_is_Some in get_rel. destruct get_rel as [ | | i' j''].
    + rewrite !perm_at_var. reflexivity.
    + rewrite !perm_at_anon. reflexivity.
    + rewrite !perm_at_abstraction. cbn.
      destruct (decide (i = i')) as [<- | ]; simpl_map; [ | reflexivity].
      assert (j <> j'') by congruence.
      destruct (lookup i (abstractions_perm _)); [ | reflexivity].
      cbn. simpl_map. reflexivity.
  - rewrite get_extra_remove_abstraction_value.
    rewrite !get_extra_state_permutation by assumption. apply get_extra_remove_abstraction_value.
Qed.

Definition add_abstraction_value_perm perm i j k := {|
  accessor_perm := {|
    anons_perm := anons_perm (accessor_perm perm);
    abstractions_perm := alter (insert j k) i (abstractions_perm (accessor_perm perm));
  |};
  loan_id_names := loan_id_names perm;
|}.

Lemma add_abstraction_value_perm_equivalence perm S i j v :
  abstraction_element S i j = Some v ->
  subseteq (loan_set_val v) (dom (loan_id_names perm)) ->
  is_state_equivalence perm (remove_abstraction_value S i j) ->
  exists k, is_state_equivalence (add_abstraction_value_perm perm i j k) S /\
            perm = remove_abstraction_value_perm (add_abstraction_value_perm perm i j k) i j /\
            abstraction_element (apply_state_permutation (add_abstraction_value_perm perm i j k) S) i k = Some (rename_value (loan_id_names perm) v).
Proof.
  unfold abstraction_element. setoid_rewrite get_at_abstraction. rewrite bind_Some.
  intros (A & get_A & get_v) ? ((? & H) & (? & ?)).
  pose proof (H i) as G. cbn in G. simpl_map. rewrite get_A in G.
  inversion G as [p ? p_perm get_p | ]. subst.
  destruct (exist_fresh (map_img (SA := Pset) p)) as (k & Hk). rewrite not_elem_of_map_img in Hk.
  exists k. split; [split; split | split].
  - assumption.
  - intros i'. destruct (decide (i = i')) as [<- | ].
    + cbn. simpl_map. constructor. apply is_permutation_insert; [ | assumption..].
      rewrite get_v. auto.
    + specialize (H i'). cbn in *. simpl_map. assumption.
  - assumption.
  - unfold loan_set_state in *. erewrite map_fold_delete_L;
      [ | set_solver | rewrite get_at_abstraction, get_A; eassumption].
    rewrite get_map_remove_abstraction_value in * |-. set_solver.
  - destruct perm as (perm & ?). destruct perm.
    unfold remove_abstraction_value_perm, add_abstraction_value_perm. cbn in *.
    f_equal. f_equal. rewrite <-alter_compose. symmetry. apply alter_id.
    rewrite <-get_p. intros ? [=<-]. apply delete_insert.
    rewrite eq_None_not_Some. destruct p_perm as (_ & ->). simpl_map. auto.
  - cbn. rewrite map_lookup_zip_with. simpl_map. cbn.
    erewrite lookup_pkmap.
    + rewrite lookup_fmap, get_v. reflexivity.
    + apply map_inj_equiv, map_inj_insert; [assumption | apply p_perm].
    + simpl_map. reflexivity.
Qed.

Lemma permutation_abstraction_element perm S i j k
  (H : is_state_equivalence perm S)
  (G : permutation_accessor (accessor_perm perm) (encode_abstraction (i, j)) =
        Some (encode_abstraction (i, k))) :
  abstraction_element (apply_state_permutation perm S) i k =
  fmap (rename_value (loan_id_names perm)) (abstraction_element S i j).
Proof.
  unfold abstraction_element. rewrite get_map_state_permutation by apply H.
  rewrite lookup_fmap. f_equal. apply lookup_pkmap.
  - eapply permutation_accessor_inj. apply H.
  - exact G.
Qed.

Lemma remove_loans_equiv A B A' B' (H : remove_loans A B A' B') :
  forall pA' pB', is_permutation pA' A' -> is_permutation pB' B' ->
    exists pA pB, is_permutation pA A /\ is_permutation pB B /\
      remove_loans (apply_permutation pA A) (apply_permutation pB B)
                   (apply_permutation pA' A') (apply_permutation pB' B').
Proof.
  induction H as [ | ? ? ? ? ? ? ? IH]; intros pA' pB' perm_A' perm_B'.
  - exists pA', pB'. split; [assumption | ]. split; [assumption | ]. constructor.
  - assert (lookup i pA' = None).
    { rewrite eq_None_not_Some. destruct perm_A' as (_ & ->). simpl_map. auto. }
    assert (lookup j pB' = None).
    { rewrite eq_None_not_Some. destruct perm_B' as (_ & ->). simpl_map. auto. }
    destruct (exist_fresh (map_img (SA := Pset) pA')) as (i' & Hi').
    destruct (exist_fresh (map_img (SA := Pset) pB')) as (j' & Hj').
    rewrite not_elem_of_map_img in Hi', Hj'.
    eapply is_permutation_insert in perm_A', perm_B'; [ | auto..].
    specialize (IH _ _ perm_A' perm_B'). edestruct IH as (pA & pB & perm_A & perm_B & IH').
    exists pA, pB. split; [assumption | ]. split; [assumption | ].
    erewrite <-(insert_delete A') in IH'; [ | eassumption].
    erewrite <-(insert_delete B') in IH'; [ | eassumption].
    erewrite !apply_permutation_insert in IH' by
      (try apply perm_A'; try apply perm_B'; now simpl_map).
    rewrite !delete_insert in IH' by assumption.
    eapply Remove_MutLoan with (i := i') (j := j') in IH'; [ | simpl_map; reflexivity..].
    rewrite !delete_insert in IH' by auto using lookup_pkmap_None.
    exact IH'.
Qed.

Lemma merge_abstractions_equiv A B C pC :
  is_permutation pC C -> merge_abstractions A B C ->
  exists pA pB, is_permutation pA A /\ is_permutation pB B /\
    merge_abstractions (apply_permutation pA A) (apply_permutation pB B) (apply_permutation pC C).
Proof.
  intros perm_C (A' & B' & Hremove & union_A'_B').
  eapply union_maps_permutation_rev in union_A'_B'; [ | eassumption..].
  destruct union_A'_B' as (pA' & pB' & ? & ? & ?).
  edestruct remove_loans_equiv as (pA & pB & ? & ? & ?); [eassumption.. | ].
  exists pA, pB. split; [assumption | ]. split; [assumption | ]. eexists _, _. split; eassumption.
Qed.

Hint Resolve fresh_anon_diff : spath.
Hint Rewrite<- fresh_anon_sset : spath.
Hint Resolve anon_accessor_diff : spath.

Lemma permutation_spath_compose S g f sp :
  valid_accessor_permutation f S -> valid_accessor_permutation g (rename_accessors f S) ->
  valid_spath S sp ->
  _permutation_spath g (_permutation_spath f sp) =
  _permutation_spath (compose_accessor_permutation g f) sp.
Proof.
  intros ((inj_anons_f & anons_f) & H) ((_ & anons_g) & G) (? & get_at_sp & _).
  apply mk_is_Some, get_at_accessor_is_Some in get_at_sp.
  unfold permutation_spath. destruct get_at_sp as [ | a ? get_a | i j A ? get_A get_v].
  - rewrite !perm_at_var. cbn. rewrite perm_at_var. reflexivity.

  - rewrite !perm_at_anon. cbn. rewrite map_lookup_compose.
    apply mk_is_Some in get_a.
    pose proof get_a as get_b. rewrite<- anons_f in get_b. destruct get_b as (b & get_b).
    (* Why does rewrite fail? *)
    setoid_rewrite get_b. replace (lookup a (anons_perm f)) with (Some b). cbn.
    rewrite perm_at_anon.
    specialize (anons_g b).
    cbn in anons_g. erewrite lookup_pkmap in anons_g;
      [ | apply map_inj_equiv, inj_anons_f | eassumption].
    rewrite<-anons_g in get_a. destruct get_a as (c & get_c).
    setoid_rewrite get_c. reflexivity.

  - rewrite !perm_at_abstraction. cbn. rewrite map_lookup_zip_with.
    specialize (H i). specialize (G i). cbn in G. revert G.
    rewrite map_lookup_zip_with. rewrite get_A in *. inversion H as [p ? p_perm | ]. subst. cbn.
    inversion 1 as [q ? q_perm | ]. subst. cbn.
    rewrite map_lookup_compose.

    apply mk_is_Some in get_v. pose proof get_v as get_j'.
    destruct p_perm as (inj_p & dom_p). rewrite <-dom_p in get_j'.
    destruct get_j' as (j' & get_j'). rewrite !get_j'. cbn. rewrite perm_at_abstraction, <-H1. cbn.
    destruct q_perm as (_ & dom_q). specialize (dom_q j').
    erewrite lookup_pkmap in dom_q; [ | apply map_inj_equiv, inj_p | eassumption].
    rewrite <-dom_q in get_v. destruct get_v as (? & ->). reflexivity.
Qed.

Corollary invert_state_permutation_spath perm S sp :
  valid_accessor_permutation perm S -> valid_spath S sp ->
  _permutation_spath (invert_accessor_perm perm) (_permutation_spath perm sp) = sp.
Proof.
  intros. erewrite permutation_spath_compose; eauto using invert_valid_accessor_perm.
  destruct H as ((? & _) & Habs).
  unfold permutation_spath. autodestruct. intros EQ%permutation_accessor_is_Some.
  destruct sp. f_equal. cbn in EQ. destruct EQ.
  - reflexivity.
  - cbn in get_a. rewrite compose_invert_permutation in get_a by assumption.
    apply lookup_id_permutation_is_Some in get_a. congruence.
  - revert get_i. cbn. rewrite map_lookup_zip_with, lookup_fmap.
    specialize (Habs i). inversion Habs as [? ? (? & _) | ]; [ | discriminate].
    intros [=<-]. rewrite compose_invert_permutation in get_j by assumption.
    apply lookup_id_permutation_is_Some in get_j. congruence.
Qed.

Lemma _is_fresh_apply_permutation perm S l l' :
  is_state_equivalence perm S -> lookup l (loan_id_names perm) = Some l' ->
  is_fresh l' (apply_state_permutation perm S) -> is_fresh l S.
Proof.
  intros Hperm H fresh_l p valid_p get_l. eapply fresh_l.
  - apply permutation_valid_spath; eassumption.
  - rewrite permutation_sget, get_node_rename_value by assumption.
    destruct (S.[p]); inversion get_l; cbn; unfold rename_loan_id; rewrite H; constructor.
Qed.

Lemma is_fresh_apply_permutation perm S l l' :
  is_state_equivalence perm S -> lookup l (loan_id_names perm) = Some l' ->
  is_fresh l S -> is_fresh l' (apply_state_permutation perm S).
Proof.
  intros Hperm H. erewrite <-apply_invert_state_permutation at 1 by eassumption.
  eapply _is_fresh_apply_permutation.
  - apply invert_state_permutation_is_permutation. assumption.
  - apply lookup_Some_invert_permutation; [apply Hperm | apply H].
Qed.

Lemma _not_in_borrow_apply_permutation perm S sp :
  is_state_equivalence perm S -> valid_spath S sp ->
  not_in_borrow (apply_state_permutation perm S) (permutation_spath perm sp) ->
  not_in_borrow S sp.
Proof.
  intros Hperm valid_sp H ? Pq (? & ? & <-).
  rewrite valid_spath_app in valid_sp. destruct valid_sp.
  eapply H.
  - rewrite permutation_sget, get_node_rename_value by eassumption. destruct Pq. constructor.
  - eexists _, _. autorewrite with spath. reflexivity.
Qed.

Lemma not_in_borrow_apply_permutation perm S sp :
  is_state_equivalence perm S -> valid_spath S sp ->
  not_in_borrow (apply_state_permutation perm S) (permutation_spath perm sp) <->
  not_in_borrow S sp.
Proof.
  intros ? valid_sp. split.
  - apply _not_in_borrow_apply_permutation; assumption.
  - intros ?. eapply _not_in_borrow_apply_permutation.
    + apply invert_state_permutation_is_permutation. assumption.
    + apply permutation_valid_spath; assumption.
    + rewrite apply_invert_state_permutation by assumption.
      cbn. erewrite invert_state_permutation_spath; try eassumption. apply H.
Qed.
Hint Resolve <-not_in_borrow_apply_permutation : spath.

Lemma not_value_contains_rename_value P m v (H : forall c, P (rename_node m c) -> P c) :
  not_value_contains P v -> not_value_contains P (rename_value m v).
Proof.
  intros Hnot_contains p valid_p%valid_vpath_rename_value.
  rewrite <-vget_rename_value, get_node_rename_value.
  intros ?%H. eapply Hnot_contains; eassumption.
Qed.

Corollary not_contains_bot_rename_value m v :
  not_contains_bot v -> not_contains_bot (rename_value m v).
Proof. apply not_value_contains_rename_value. intros [ ]; easy. Qed.
Hint Resolve not_contains_bot_rename_value : spath.

Corollary not_contains_loan_rename_value m v :
  not_contains_loan v -> not_contains_loan (rename_value m v).
Proof. apply not_value_contains_rename_value. intros [ ]; easy. Qed.
Hint Resolve not_contains_loan_rename_value : spath.

Corollary not_contains_borrow_rename_value m v :
  not_contains_borrow v -> not_contains_borrow (rename_value m v).
Proof. apply not_value_contains_rename_value. intros [ ]; easy. Qed.
Hint Resolve not_contains_borrow_rename_value : spath.

Lemma not_contains_outer_loan_rename_value v r :
  not_contains_outer_loan v -> not_contains_outer_loan (rename_value r v).
Proof.
  intros H p valid_p%valid_vpath_rename_value.
  setoid_rewrite <-vget_rename_value. setoid_rewrite get_node_rename_value.
  specialize (H p valid_p). destruct (get_node (v.[[p]])); inversion 1.
  destruct H as (q & ? & H); [constructor | ].
  exists q. split; [assumption | ]. destruct (get_node (v.[[q]])); inversion H. constructor.
Qed.
Hint Resolve not_contains_outer_loan_rename_value : spath.

Lemma in_abstraction_perm perm i x y :
  permutation_accessor perm x = Some y -> in_abstraction i y -> in_abstraction i x.
Proof.
  intros G%permutation_accessor_is_Some. destruct G.
  - auto.
  - intros (? & H). inversion H.
  - intros (? & H). apply encode_inj in H. inversion H. eexists. reflexivity.
Qed.

Corollary not_in_abstraction_perm perm sp :
  not_in_abstraction sp -> not_in_abstraction (permutation_spath perm sp).
Proof.
  unfold not_in_abstraction. intros H i (j & G). apply (H i).
  unfold permutation_spath in G.
  destruct (permutation_accessor (accessor_perm perm) (fst sp)) eqn:EQN.
  - eapply in_abstraction_perm; [ | eexists]; eassumption.
  - rewrite G. eexists. reflexivity.
Qed.
Hint Resolve not_in_abstraction_perm : spath.

Lemma merge_abstraction_rename_value A B C p :
  merge_abstractions A B C ->
  merge_abstractions (fmap (rename_value p) A) (fmap (rename_value p) B) (fmap (rename_value p) C).
Proof.
  intros (A' & B' & Hremove & Hunion).
  eexists _, _. split; [ | eapply union_maps_fmap, Hunion]. clear Hunion. induction Hremove.
  - constructor.
  - rewrite !fmap_delete. econstructor; simpl_map; eauto.
Qed.

(* We can always extend the map of loan identifiers of [perm] so that it contains every loans
 * of a set L. We obtain a permutation [perm'] that is still a valid permutation of S, and it
 * has the same effect as [perm] when applied on S. *)
Lemma extend_loan_id_names L perm S :
  valid_loan_id_names perm S ->
  exists perm',
    valid_loan_id_names perm' S /\ subseteq L (dom perm') /\
    rename_state perm S = rename_state perm' S.
Proof.
  intros (H & Hincl). apply (extend_inj_map L) in H. destruct H as (perm' & ? & ? & ?).
  exists perm'. repeat split.
  - assumption.
  - etransitivity; [ | apply subseteq_dom]; eassumption.
  - assumption.
  - apply state_eq_ext.
    + rewrite !get_map_rename_state. apply map_fmap_ext. intros i v G.
      apply loan_set_val_subset_eq_loan_set_state in G. induction v; try reflexivity.
      * cbn in G. apply singleton_subseteq_l, Hincl in G. apply elem_of_dom in G.
        destruct G as (? & G). cbn. unfold rename_loan_id. setoid_rewrite G.
        eapply map_subseteq_spec in G; [ | eassumption]. setoid_rewrite G. reflexivity.
      * rewrite loan_set_borrow, union_subseteq in G. destruct G as (G & ?).
        cbn. rewrite IHv by assumption. f_equal.
        apply singleton_subseteq_l, Hincl, elem_of_dom in G. destruct G as (? & G).
        unfold rename_loan_id. setoid_rewrite G.
        eapply map_subseteq_spec in G; [ | eassumption]. setoid_rewrite G. reflexivity.
    + cbn. rewrite !dom_fmap_L. reflexivity.
Qed.

Lemma extend_state_permutation L perm S :
  is_state_equivalence perm S ->
  exists perm',
    is_state_equivalence perm' S /\ subseteq L (dom (loan_id_names perm')) /\
    apply_state_permutation perm S = apply_state_permutation perm' S.
Proof.
  intros (? & H). apply (extend_loan_id_names L) in H.
  unfold apply_state_permutation. destruct H as (m' & ? & ? & ->).
  exists {|accessor_perm := accessor_perm perm; loan_id_names := m'|}.
  split; split; auto.
Qed.

Hint Resolve is_state_equivalence_sset : spath.
Hint Resolve permutation_fresh_abstraction : spath.
Hint Resolve equiv_states_fresh_abstraction : spath.

Hint Rewrite permutation_sset using (eauto with spath) : spath.
Hint Rewrite permutation_sget using (eauto with spath) : spath.
Hint Rewrite permutation_add_anon using (eauto with spath) : spath.
Hint Rewrite permutation_add_abstraction using (eauto with spath) : spath.

(** * Semantics of LLBC+ *)
Inductive eval_proj (S : LLBC_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : LLBC_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd p) pi_0 pi.
Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : LLBC_plus_state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Definition copiable (ty : LLBC_type) := True.

Inductive copy_val : LLBC_plus_val -> LLBC_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (LLBC_plus_int n) (LLBC_plus_int n)
| Copy_val_bool (b : bool) : copy_val (LLBC_plus_bool b) (LLBC_plus_bool b)
| Copy_val_symbolic ty : copiable ty ->
    copy_val (LLBC_plus_symbolic ty) (LLBC_plus_symbolic ty)
.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> LLBC_plus_state -> (LLBC_plus_val * LLBC_plus_state) -> Prop :=
| Eval_IntConst S n : S |-{op} Const (IntConst n) => (LLBC_plus_int n, S)
| Eval_BoolConst S b : S |-{op} Const (BoolConst b) => (LLBC_plus_bool b, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi (Heval : eval_place S Mov p pi)
    (move_no_loan : not_contains_loan (S.[pi])) (move_no_bot : not_contains_bot (S.[pi])) :
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_binary_op : BinOp -> LLBC_plus_val -> LLBC_plus_val -> LLBC_plus_val -> Prop :=
  | Eval_add_int_int m n :
      eval_binary_op BAdd (LLBC_plus_int m) (LLBC_plus_int n) (LLBC_plus_int (m + n))
  | Eval_add_int_symbolic m :
      eval_binary_op BAdd (LLBC_plus_int m) (LLBC_plus_symbolic intT) (LLBC_plus_symbolic intT)
  | Eval_add_symbolic_int n :
      eval_binary_op BAdd (LLBC_plus_symbolic intT) (LLBC_plus_int n) (LLBC_plus_symbolic intT)
  | Eval_add_symbolic_symbolic :
      eval_binary_op BAdd (LLBC_plus_symbolic intT) (LLBC_plus_symbolic intT) (LLBC_plus_symbolic intT)
  | Eval_le_int_int m n :
      eval_binary_op BLe (LLBC_plus_int m) (LLBC_plus_int n) (LLBC_plus_bool (m <=? n))
  | Eval_le_int_symbolic m :
      eval_binary_op BLe (LLBC_plus_int m) (LLBC_plus_symbolic intT) (LLBC_plus_symbolic boolT)
  | Eval_le_symbolic_int n :
      eval_binary_op BLe (LLBC_plus_symbolic intT) (LLBC_plus_int n) (LLBC_plus_symbolic boolT)
  | Eval_le_symbolic_symbolic :
      eval_binary_op BLe (LLBC_plus_symbolic intT) (LLBC_plus_symbolic intT) (LLBC_plus_symbolic boolT)
.

Variant eval_rvalue : rvalue -> LLBC_plus_state -> (LLBC_plus_val * LLBC_plus_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' binop op_0 op_1 v0 v1 w
      (eval_op_0 : S |-{op} op_0 => (v0, S')) (eval_op_1 : S' |-{op} op_1 => (v1, S''))
      (Hbinop : eval_binary_op binop v0 v1 w) :
      S |-{rv} (BinaryOp binop op_0 op_1) => (w, S'')
  (* Note: with a typing judgement on LLBC, and with a well-typedness invariant, the type
   * [ty] could be obtained from the type of the place p, and the well-typedness of
   * [S.[pi]] could be derived from the well-typedness of [S]. *)
  | Eval_mut_borrow S p pi l ty (eval_p : S |-{p} p =>^{Mut} pi)
      (borrow_no_loan : not_contains_loan (S.[pi]))
      (borrow_no_bot : not_contains_bot (S.[pi]))
      (fresh_l : is_fresh l S)
      (Htype : is_of_type ty (S.[pi])) :
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(ty, l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

(* Note: we use the variable names i' and j' instead of i and j that are used for leq_state_base.
 * We are also using the name A' instead of A, B or C for the region abstractions.
 *)
Variant reorg : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Ends a borrow when it's not in an abstraction: *)
| Reorg_end_borrow_m S (p q : spath) l ty
    (get_loan : get_node (S.[p]) = loanC^m(ty, l)) (get_borrow : get_node (S.[q]) = borrowC^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (Hdisj : disj p q)
    (loan_not_in_abstraction : not_in_abstraction p)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
(* Ends a borrow when it's in an abstraction: *)
(* The value that is transferred back, S.[q +++ [0]], has to be of integer type. *)
| Reorg_end_borrow_m_in_abstraction S q i' j' l ty
    (get_loan : abstraction_element S i' j' = Some (loan^m(ty, l)))
    (get_borrow : get_node (S.[q]) = borrowC^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S ((remove_abstraction_value S i' j').[q <- bot])
(* q refers to a path in abstraction A, at index j. *)
| Reorg_end_abstraction S i' A' S'
    (fresh_i' : fresh_abstraction S i')
    (A_no_loans : map_Forall (fun _ => not_contains_loan) A')
    (Hadd_anons : add_anons S A' S') : reorg (S,,, i' |-> A') S'
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : LLBC_plus_val * LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : S |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp]))
  (Hstore_type : store_compatible_types S sp v) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(* A version of to-abs that is limited compared to the paper. Currently, we can only turn into a
 * region abstraction a value of the form:
 * - borrow^m l σ (with σ a symbolic value)
 * - borrow^m l0 (loan^m l1)
 * Consequently, a single region abstraction is created.
 *)
Variant to_abs : LLBC_plus_val -> Pmap LLBC_plus_val -> Prop :=
| ToAbs_MutReborrow l0 l1 kb kl ty (Hk : kb <> kl) :
    to_abs (borrow^m(l0, loan^m(ty, l1)))
           ({[kb := (borrow^m(l0, LLBC_plus_symbolic ty)); kl := loan^m(ty, l1)]})%stdpp
| ToAbs_MutBorrow l v k ty (Htype : is_of_type ty v)
    (v_no_loan : not_contains_loan v) (v_no_borrow : not_contains_borrow v) :
    to_abs (borrow^m(l, v)) ({[k := (borrow^m(l, LLBC_plus_symbolic ty))]})%stdpp
.

(* Note: the definition is duplicated in [leq_state_base_n].
 * Perhaps we should only define leq_state_base_n, and define [leq_state_base Sl Sr] as
 * [exists n, leq_state_base_n n Sl Sr]. *)
Variant leq_state_base : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Contrary to the article, symbolic values should be typed. Thus, only an integer can be converted
 * to a symbolic value for the moment. *)
| Leq_ToSymbolic S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base S (S.[sp <- LLBC_plus_symbolic ty])
| Leq_ToAbs S a i v A
    (fresh_a : fresh_anon S a)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base (S,, a |-> v) (S,,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon S a v
    (fresh_a : fresh_anon S a)
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v) :
    leq_state_base (S,, a |-> v) S
| Leq_MoveValue S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_borrow : not_in_borrow S sp)
    (sp_not_in_abstraction : not_in_abstraction sp) :
    leq_state_base S (S.[sp <- bot],, a |-> S.[sp])
(* Note: for the merge, we reuse the region abstraction at i. Maybe we should use another region
 * abstraction index k? *)
| Leq_MergeAbs S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan S sp l' a ty
    (fresh_l' : is_fresh l' S)
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp])) :
    leq_state_base S (S.[sp <- loan^m(ty, l')],, a |-> borrow^m(l', S.[sp]))
| Leq_Reborrow_MutBorrow (S : LLBC_plus_state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = borrowC^m(l0))
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp +++ [0] ])) :
    leq_state_base S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(ty, l1)))
| Leq_Abs_ClearValue S i j v
    (get_at_i_j : abstraction_element S i j = Some v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base S (remove_abstraction_value S i j)
| Leq_AnonValue S a (is_fresh : fresh_anon S a) : leq_state_base S (S,, a |-> bot)
.

Definition leq_symbolic := chain equiv_states leq_state_base^*.
Definition leq_val_state := chain equiv_val_state (leq_val_state_base leq_state_base)^*.

(** ** Definition of branching semantics and [eval_stmt]. *)
(** A symbolic execution abstracts all executions, from all branches. A "branching state" [B] is a partial map. It can associate a control-flow tag [r] (break, continue, panic...) to symbolic state [S] that is more general than all the computations that terminate with [r]. This maps is partial, because if no computation terminates on [r], we have [lookup r B = None]. *)
Definition branching_state := gmap statement_result LLBC_plus_state.

Reserved Notation "S  |-{stmt}  stmt  =>  B" (at level 50).

(** The simulation relation on branching states. A branching state [Br] is more general than a branching state [Bl] if for any tag [r], if [Bl] maps a control-flow tag [r] to a symbolic state [Sl] ([lookup r Bl = Some Sl]), then [Br] maps [r] to a more general state [Sr] ([lookup r Br = Some Sr] and [leq_symbolic Sl Sr]).

   Note that the domain of [Br] can be bigger than the domain of [Bl]. There can be computations that terminate on a tag [r] that are abstracted by [Bl] but not [Br]. *)
Variant leq_option_symbolic : relation (option LLBC_plus_state) :=
  | LeqNone oSr : leq_option_symbolic None oSr
  | LeqSome Sl Sr : leq_symbolic Sl Sr -> leq_option_symbolic (Some Sl) (Some Sr).

Definition leq_branching (Bl Br : branching_state) :=
  forall r, leq_option_symbolic (lookup r Bl) (lookup r Br).

(** In the ICPF article, Ho et al introduce a join operation, described with non-deterministic computation rules. However, we are not interested in an algorithm for joins. The join [Bjoin] of two states [B0] and [B1] can be provided by an oracle, we do not describe the computation rules. We only require two properties.
   - The state [B_join] is an upper bound of [B0] and [B1], that means that we have [leq_branching B0 Bjoin] and [leq_branching Bs Bjoin].
   - If a control-flow tag [r] is not in the domain of [Bl] (respectively [Br]), then [lookup r Bjoin = lookup r Br] (respectively [lookup r Bjoin = lookup r Bl]).

   The second condition is here to ensure that LLBC is a stable subset of LLBC+. In particular, the join of a state [B = {[r := S]}] and the empty state can only be [B].
 *)
Variant option_is_join :
  option LLBC_plus_state -> option LLBC_plus_state -> option LLBC_plus_state -> Prop :=
  | UpperBound_None_None : option_is_join None None None
  | UpperBound_Some_None S0 : option_is_join (Some S0) None (Some S0)
  | UpperBound_None_Some S1 : option_is_join None (Some S1) (Some S1)
  | UpperBound_Some_Some S0 S1 S2 : leq_symbolic S0 S2 -> leq_symbolic S1 S2 ->
      option_is_join (Some S0) (Some S1) (Some S2).

Definition is_join (B0 B1 Bjoin : branching_state) :=
  forall r, option_is_join (lookup r B0) (lookup r B1) (lookup r Bjoin).

Inductive eval_stmt : statement -> LLBC_plus_state -> branching_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => {[rUnit := S]}
  | Eval_seq_no_unit S0 B1 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 => B1) (Hno_unit : lookup rUnit B1 = None) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) => B1
  | Eval_seq S0 B1 S_unit B_unit B_join stmt_0 stmt_1
      (eval_stmt_0 : S0 |-{stmt} stmt_0 => B1) (H_unit : lookup rUnit B1 = Some S_unit)
      (eval_stmt_1 : S_unit |-{stmt} stmt_1 => B_unit)
      (His_join : is_join B_unit (delete rUnit B1) B_join) :
      S0 |-{stmt} (Seq stmt_0 stmt_1) => B_join
  | Eval_assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv => {[rUnit := S'']}
  | Eval_if_true S S' B_if cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (LLBC_plus_bool true, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if => B_if) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => B_if
  | Eval_if_false S S' B_else cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (LLBC_plus_bool false, S'))
      (Heval_else_branch : S' |-{stmt} stmt_else => B_else) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => B_else
  | Eval_if_symbolic S S' B_if B_else B_join cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (LLBC_plus_symbolic boolT, S'))
      (Heval_if_branch : S' |-{stmt} stmt_if => B_if)
      (Heval_else_branch : S' |-{stmt} stmt_else => B_else)
      (His_join : is_join B_if B_else B_join) :
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => B_join
  | Eval_reorg S0 S1 B2 stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => B2) :
      S0 |-{stmt} stmt => B2
where "S |-{stmt} stmt => B" := (eval_stmt stmt S B).

Lemma sweight_add_abstraction S weight i A :
  fresh_abstraction S i ->
  sweight weight (S,,, i |-> A) = sweight weight S + map_sum (vweight weight) A.
Proof.
  intros ?. unfold sweight, get_map. cbn. rewrite flatten_insert' by assumption.
  rewrite sum_maps_union. rewrite map_sum_union. rewrite !map_sum_kmap by typeclasses eauto.
  reflexivity.
  apply map_disjoint_spec. intros j ? ? lookup_l.
  intros ((? & ?) & ? & (? & (? & ?)%pair_eq & ?)%lookup_kmap_Some)%lookup_kmap_Some.
  subst. rewrite sum_maps_lookup_r, lookup_None_flatten in lookup_l by assumption.
  discriminate. all: typeclasses eauto.
Qed.
Hint Rewrite sweight_add_abstraction using auto with spath; fail : weight.

Hint Rewrite @sweight_add_anon using auto with weight : weight.

Lemma remove_abstraction_value_add_abstraction S i j A :
  remove_abstraction_value (S,,, i |-> A) i j = S,,, i |-> (delete j A).
Proof.
  unfold add_abstraction, remove_abstraction_value. cbn. f_equal. apply alter_insert.
Qed.

Lemma remove_abstraction_value_add_abstraction_ne S i i' j A (H : i <> i') :
  remove_abstraction_value (S,,, i |-> A) i' j =
  (remove_abstraction_value S i' j),,, i |-> A.
Proof.
  unfold add_abstraction, remove_abstraction_value. cbn. f_equal.
  rewrite alter_insert_ne by congruence. reflexivity.
Qed.

Hint Rewrite remove_abstraction_value_add_abstraction : spath.
Hint Rewrite remove_abstraction_value_add_abstraction_ne using congruence : spath.

Lemma sweight_remove_abstraction_value weight S i j v :
  abstraction_element S i j = Some v ->
  (Z.of_nat (sweight weight (remove_abstraction_value S i j)) =
   (Z.of_nat (sweight weight S)) - (Z.of_nat (vweight weight v)))%Z.
Proof.
  unfold abstraction_element. rewrite get_at_abstraction.
  intros (A & get_A & get_v)%bind_Some.
  apply add_remove_abstraction in get_A.
  rewrite <-get_A, remove_abstraction_value_add_abstraction.
  rewrite !sweight_add_abstraction by apply remove_abstraction_fresh.
  apply (map_sum_delete (vweight weight)) in get_v. lia.
Qed.

(* Derived rules of leq_state_base. *)
Lemma Leq_Reborrow_MutBorrow_Abs S sp l0 l1 i kb kl ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_i : fresh_abstraction S i)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (get_borrow_l0 : get_node (S.[sp]) = borrowC^m(l0))
    (Hk : kb <> kl)
    (Htype : is_of_type ty (S.[sp +++ [0] ])):
    leq_state_base^* S (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],,,
                        i |-> {[kb := (borrow^m(l0, LLBC_plus_symbolic ty));
                                kl := loan^m(ty, l1)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. apply Leq_Reborrow_MutBorrow; eassumption. }
  constructor. eapply Leq_ToAbs with (a := a).
  - eauto with spath.
  - repeat apply fresh_abstraction_sset. eassumption.
  - autorewrite with spath. constructor. assumption.
Qed.

Lemma Leq_Fresh_MutLoan_Abs S sp l' i k ty
    (fresh_l' : is_fresh l' S)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (fresh_i : fresh_abstraction S i)
    (no_loan : not_contains_loan (S.[sp]))
    (no_borrow : not_contains_borrow (S.[sp]))
    (Htype : is_of_type ty (S.[sp])) :
    leq_state_base^* S (S.[sp <- loan^m(ty, l')],,,
                        i |-> {[k := borrow^m(l', LLBC_plus_symbolic ty)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. eapply Leq_ToSymbolic; eassumption. }
  etransitivity.
  { constructor. apply Leq_Fresh_MutLoan with (sp := sp).
    - not_contains.
    - apply fresh_anon_sset. eassumption.
    - validity.
    - assumption.
    - autorewrite with spath. constructor. }
  etransitivity.
  { constructor. eapply Leq_ToAbs with (a := a) (i := i).
    - eauto with spath.
    - repeat apply fresh_abstraction_sset. assumption.
    - autorewrite with spath. constructor; [constructor | not_contains..]. }
  autorewrite with spath. reflexivity.
Qed.

(** * Simulation proofs. *)
(** ** leq_state_base is preserved by equivalence. *)
Definition measure S := sweight (fun _ => 1) S + size (abstractions S).
Notation abs_measure S := (map_sum (vweight (fun _ => 1)) S).

Variant leq_state_base_n : nat -> LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Leq_ToSymbolic_n S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base_n (vweight (fun _ => 1) (S.[sp])) S (S.[sp <- LLBC_plus_symbolic ty])
| Leq_ToAbs_n S a i v A
    (fresh_a : fresh_anon S a)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base_n (vweight (fun _ => 1) v) (S,, a |-> v) (S,,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon_n S a v
    (fresh_a : fresh_anon S a)
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v) :
    leq_state_base_n (1 + vweight (fun _ => 1) v) (S,, a |-> v) S
| Leq_MoveValue_n S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_borrow : not_in_borrow S sp)
    (sp_in_abstraction : not_in_abstraction sp) :
    leq_state_base_n 0 S (S.[sp <- bot],, a |-> S.[sp])
| Leq_MergeAbs_n S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base_n (abs_measure A + abs_measure B - abs_measure C + 2)
                                (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan_n S sp l' a ty
    (fresh_l' : is_fresh l' S)
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp])) :
    leq_state_base_n 0 S (S.[sp <- loan^m(ty, l')],, a |-> borrow^m(l', S.[sp]))
| Leq_Reborrow_MutBorrow_n (S : LLBC_plus_state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = borrowC^m(l0))
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp +++ [0] ])) :
    leq_state_base_n 0 S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(ty, l1)))
| Leq_Abs_ClearValue_n S i j v
    (get_at_i_j : abstraction_element S i j  = Some v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base_n (1 + vweight (fun _ => 1) v) S (remove_abstraction_value S i j)
| Leq_AnonValue_n S a (is_fresh : fresh_anon S a) :
    leq_state_base_n 0 S (S,, a |-> bot)
.

Section Leq_state_base_n_is_leq_state_base.
  Hint Constructors leq_state_base : core.
  Hint Constructors leq_state_base_n : core.
  Lemma leq_state_base_n_is_leq_state_base Sl Sr :
    leq_state_base Sl Sr <-> exists n, leq_state_base_n n Sl Sr.
  Proof.
    split.
    - intros [ ]; eexists; eauto.
    - intros (n & [ ]); eauto.
  Qed.
End Leq_state_base_n_is_leq_state_base.

Definition leq_n (n : nat) := chain equiv_states (measured_closure leq_state_base_n n).

Lemma to_abs_loan_id_set v A : to_abs v A -> loan_set_val v = loan_set_abstraction A.
Proof.
  intros [ ].
  - unfold loan_set_abstraction. rewrite map_fold_insert_L; [ | set_solver | now simpl_map].
    rewrite map_fold_singleton. set_solver.
  - unfold loan_set_abstraction. rewrite map_fold_singleton.
    rewrite !loan_set_borrow. rewrite loan_set_id_empty by assumption. set_solver.
Qed.

Lemma to_abs_apply_permutation v A p q :
  is_permutation p A -> to_abs v A ->
  to_abs (rename_value q v) (apply_permutation p (fmap (rename_value q) A)).
Proof.
  intros (inj_p & dom_p) H. destruct H.
  - destruct (dom_p kb) as (_ & (kb' & ?)); [simpl_map; auto | ].
    destruct (dom_p kl) as (_ & (kl' & ?)); [simpl_map; auto | ].
    rewrite fmap_insert, map_fmap_singleton.
    erewrite apply_permutation_insert by (simpl_map; eauto).
    erewrite <-insert_empty, apply_permutation_insert by (simpl_map; auto using map_inj_delete).
    constructor. intros ?. eapply Hk, inj_p; eassumption.
  - specialize (dom_p k). simpl_map. destruct dom_p as (_ & (k' & ?)); [auto | ].
    (* TODO: lemma apply_permutation_singleton. *)
    rewrite map_fmap_singleton.
    erewrite <-insert_empty, apply_permutation_insert by (simpl_map; auto).
    rewrite !rename_loan_id_borrow. constructor; eauto with spath.
Qed.

Ltac process_state_equivalence :=
  let p := fresh "p" in
  let G := fresh "G" in
  let perm_A := fresh "perm_A" in
  let b := fresh "b" in
  let fresh_b := fresh "fresh_b" in
  let S0 := fresh "S0" in
  let B := fresh "B" in
  let Hloan_set := fresh "Hloan_set" in
  lazymatch goal with
  (* First: the hypothesis contains a goal "is_state_equivalence perm S_r".
   * While Sr is an expression E_r[S], we break it down until we obtain a property about the
   * validity of S, the common denominator between S_l and S_r. *)
  | valid_perm : is_state_equivalence ?perm (?S.[?sp <- ?v]) |- _ =>
      apply is_state_equivalence_sset_rev in valid_perm; [ | eauto with spath]
  | valid_perm : is_state_equivalence ?perm (?S,,, ?i |-> ?A) |- _ =>
      apply remove_abstraction_perm_equivalence in valid_perm; [ | eassumption];
      destruct valid_perm as (valid_perm & p & perm_A & G & Hloan_set);
      rewrite G; clear G
  | valid_perm : is_state_equivalence ?perm (?S,, ?a |-> ?v) |- _ =>
      apply remove_anon_perm_equivalence in valid_perm; [ | eauto with spath; fail];
      destruct valid_perm as (valid_perm & b & G & fresh_b & Hloan_set);
      rewrite G; clear G
  end.

Lemma loan_set_no_loan_borrow v (perm : loan_id_map) :
  not_contains_loan v -> not_contains_borrow v -> subseteq (loan_set_val v) (dom perm).
Proof. intros. rewrite loan_set_id_empty by assumption. apply empty_subseteq. Qed.
Hint Resolve loan_set_no_loan_borrow : spath.

Lemma loan_set_symbolic_subseteq ty (perm : loan_id_map) :
  subseteq (loan_set_val (LLBC_plus_symbolic ty)) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_symbolic_subseteq : spath.

Lemma loan_set_bot_subseteq (perm : loan_id_map) : subseteq (loan_set_val bot) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_bot_subseteq : spath.

Lemma prove_rel A (R : A -> A -> Prop) x y z : R x y -> y = z -> R x z.
Proof. congruence. Qed.

Lemma prove_rel_n A (R : nat -> A -> A -> Prop) x y z m n : R m x y -> m = n -> y = z -> R n x z.
Proof. congruence. Qed.

Lemma vsize_rename_value m v : vweight (fun _ => 1) (rename_value m v) = vweight (fun _ => 1) v.
Proof. induction v; cbn in *; congruence. Qed.

Lemma abs_measure_rename_set p (A : Pmap _) : abs_measure (rename_set p A) = abs_measure A.
Proof.
  induction A using map_first_key_ind.
  - reflexivity.
  - rewrite fmap_insert. rewrite !map_sum_insert by (simpl_map; rewrite ?fmap_None; assumption).
    rewrite vsize_rename_value. congruence.
Qed.

Lemma leq_n_equiv_states_commute n :
  forward_simulation (leq_state_base_n n) (leq_state_base_n n) equiv_states equiv_states.
Proof.
  intros Sl Sr (perm & valid_perm & ->) ? Hleq. destruct Hleq.
  (* TODO: automation *)
  - process_state_equivalence. rewrite permutation_sset by eauto with spath.
    execution_step.
    { exists perm. eauto. }
    eapply prove_rel_n.
    { apply Leq_ToSymbolic_n. all: rewrite permutation_sget; eauto with spath. }
    { autorewrite with spath. apply vsize_rename_value. }
    reflexivity.

  - process_state_equivalence. autorewrite with spath.
    erewrite <-to_abs_loan_id_set in * |- by eassumption.
    destruct (exists_fresh_anon (apply_state_permutation (remove_abstraction_perm perm i) S))
      as (b & fresh_b).
    execution_step.
    { eexists. split; eauto with spath. }
    eapply prove_rel_n.
    { autorewrite with spath. apply Leq_ToAbs_n; eauto with spath.
      apply to_abs_apply_permutation; eassumption. }
    { apply vsize_rename_value. }
    reflexivity.

  - destruct (exists_fresh_anon (apply_state_permutation perm S)) as (b & fresh_b).
    pose proof (loan_set_id_empty v no_loan no_borrow).
    execution_step.
    { eexists. split; eauto with spath. }
    autorewrite with spath. rewrite rename_value_no_loan_id by assumption.
    apply Leq_RemoveAnon_n; assumption.

  - repeat process_state_equivalence. autorewrite with spath in *.
    execution_step. { eexists. eauto. }
    eapply prove_rel.
    { apply Leq_MoveValue_n; rewrite ?permutation_sget; eauto with spath. }
    autorewrite with spath. reflexivity.

  - apply (extend_state_permutation (union (loan_set_abstraction A) (loan_set_abstraction B)))
      in valid_perm.
      destruct valid_perm as (perm' & valid_perm & ? & ->). clear perm.
    process_state_equivalence. autorewrite with spath.
    eapply merge_abstractions_equiv in Hmerge; [ | eassumption].
    destruct Hmerge as (pA & pB & perm_pA & perm_pB & Hmerge).
    execution_step.
    { eexists.
      pose proof valid_perm as G.
      apply (add_abstraction_perm_equivalence _ _ i A pA) in G; [ | set_solver..].
      split.
      - apply add_abstraction_perm_equivalence; [set_solver.. | eauto with spath].
      - autorewrite with spath; [reflexivity | set_solver..]. }
    rewrite pkmap_fmap by apply map_inj_equiv, perm_pA.
    rewrite pkmap_fmap by apply map_inj_equiv, perm_pB.
    eapply prove_rel_n.
    { apply Leq_MergeAbs_n; eauto with spath.
      apply merge_abstraction_rename_value, Hmerge. }
    { rewrite !abs_measure_rename_set, !map_sum_permutation by assumption. reflexivity. }
    rewrite pkmap_fmap by apply map_inj_equiv, perm_A. reflexivity.

  - process_state_equivalence.
    pose proof Hloan_set as ?. rewrite loan_set_borrow, union_subseteq in Hloan_set.
    destruct Hloan_set as (Hl' & ?).
    process_state_equivalence.
    autorewrite with spath in fresh_b.
    execution_step. { eexists. split; [eassumption | reflexivity]. }
    autorewrite with spath; [ | autorewrite with spath; eauto with spath].
    apply singleton_subseteq_l, elem_of_dom in Hl'. destruct Hl' as (l & Hl).
    eapply prove_rel.
    { apply Leq_Fresh_MutLoan_n. eapply is_fresh_apply_permutation; eassumption.
      all: eauto with spath. autorewrite with spath. eauto with spath. }
    autorewrite with spath.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl. reflexivity.

  - process_state_equivalence.
    pose proof Hloan_set as ?. rewrite loan_set_borrow, union_subseteq in Hloan_set.
    destruct Hloan_set as (Hl0 & Hl1).
    (* TODO: lemma? *)
    assert (subseteq (loan_set_val (S.[sp +++ [0] ])) (dom (loan_id_names perm))).
    { destruct valid_perm as (_ & (_ & ?)).
      pose proof (loan_set_sget (rename_mut_borrow S sp l1) (sp +++ [0])) as G.
      autorewrite with spath in G. set_solver. }
    process_state_equivalence.
    (* TODO: lemma? *)
    2: { destruct (S.[sp]) eqn:EQN; inversion get_borrow_l0. subst. rewrite loan_set_borrow.
      apply (f_equal (vget [0])) in EQN. autorewrite with spath in EQN. subst. set_solver. }
    autorewrite with spath in fresh_b; [ | rewrite loan_set_borrow; set_solver].
    execution_step. { eexists. split; [exact valid_perm | reflexivity]. }
    assert (subseteq (loan_set_val borrow^m(l1, S.[sp +++ [0] ])) (dom (loan_id_names perm)))
      by set_solver.
    autorewrite with spath; [ | autorewrite with spath; eauto with spath].
    apply singleton_subseteq_l, elem_of_dom in Hl0. destruct Hl0 as (l0' & Hl0').
    cbn in Hl1. apply singleton_subseteq_l, elem_of_dom in Hl1.
    destruct Hl1 as (l1' & Hl1').
    eapply prove_rel.
    { eapply Leq_Reborrow_MutBorrow_n with (sp := permutation_spath _ sp); eauto with spath.
      eapply is_fresh_apply_permutation; eassumption.
      rewrite permutation_sget by eauto with spath. rewrite get_node_rename_value, get_borrow_l0.
      reflexivity. autorewrite with spath. eauto with spath. }
    autorewrite with spath.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl0'. setoid_rewrite Hl1'.
    reflexivity.

  - apply (extend_state_permutation (loan_set_val v)) in valid_perm.
    destruct valid_perm as (perm' & valid_perm & ? & ->). clear perm.
    eapply add_abstraction_value_perm_equivalence in valid_perm; [ | eassumption..].
    destruct valid_perm as (k & valid_perm & G & get_at_i_k). rewrite G.
    execution_step. { eexists. split; [exact valid_perm | reflexivity]. }
    rewrite rename_value_no_loan_id in get_at_i_k by now apply loan_set_id_empty.
    erewrite permutation_remove_abstraction_value.
    { eapply Leq_Abs_ClearValue_n; eassumption. }
    { eassumption. }
    (* TODO: separate lemma *)
    { unfold abstraction_element in get_at_i_j.
      rewrite get_at_abstraction, bind_Some in get_at_i_j.
      destruct get_at_i_j as (A & get_A & _).
      rewrite perm_at_abstraction. cbn.
      destruct valid_perm as ((_ & abs_valid) & _). specialize (abs_valid i).
      rewrite get_A in abs_valid. cbn in abs_valid. simpl_map.
      destruct (lookup i (abstractions_perm _)); [ | inversion abs_valid].
      cbn. simpl_map. reflexivity. }

  - process_state_equivalence.
    execution_step. { eexists. split; [exact valid_perm | reflexivity]. }
    autorewrite with spath. apply Leq_AnonValue_n. auto with spath.
Qed.

Corollary leq_equiv_states_commute :
  forward_simulation leq_state_base leq_state_base equiv_states equiv_states.
Proof.
  intros ? ? ? ? (? & ?)%leq_state_base_n_is_leq_state_base.
  edestruct leq_n_equiv_states_commute as (S' & ? & ?); [eassumption.. | ].
  exists S'. split; [ | assumption].
  eapply leq_state_base_n_is_leq_state_base. eexists. eassumption.
Qed.

Instance leq_symbolic_preorder : PreOrder leq_symbolic.
Proof.
  split.
  - apply reflexive_chain; intros S; reflexivity.
  - apply transitive_leq, leq_equiv_states_commute.
Qed.

Lemma leq_branching_alt Bl Br :
  leq_branching Bl Br <-> map_included (fun _ => leq_symbolic) Bl Br.
Proof.
  split. all: intros H r; specialize (H r); revert H.
  all: remember (lookup r Bl) as Sl eqn:EQN_l; setoid_rewrite <-EQN_l.
  all: remember (lookup r Br) as Sr eqn:EQN_r; setoid_rewrite <-EQN_r.
  - intros [ ]; cbn.
    + autodestruct.
    + assumption.
  - destruct Sl, Sr; cbn; try constructor; easy.
Qed.

(* Because [leq_symbolic] is a pre-order, [map_included (fun _ => leq_symbolic)] also is. We use this to prove that the equivalent relation [leq_branching] is a pre-order. *)
Instance leq_symbolic_branching : PreOrder leq_branching.
Proof.
  split.
  - intros ?. rewrite leq_branching_alt. reflexivity.
  - intros Bl Bm Br. rewrite !leq_branching_alt. transitivity Bm; assumption.
Qed.

(** The following section is here to prove the commutation between the relation
   [leq_val_state_base] and equivalence up to loan renaming.
   The reason why we don't prove this for equivalence is that the actual definition is not
   suitable. If we have [(S,, a |-> v) < (S',, a |-> v')] and a permutation perm on [S,, a |-> v],
   by applying [leq_equiv_states_commute], we only know that there exists a permutation
   [perm'] such that perm [(S,, a |-> v) < perm'(S',, a |-> v')]. But there is no reason why we
   would have perm(a) = perm'(a).
   This is the case with rename_state, but this property is not specific to equivalence up to loan
   renaming. And the theorem [leq_equiv_states_up_to_loan_renaming_commute] is very redundant
   with [leq_equiv_states_commute].
   In order to avoid doing twice a similar tedious proof, a solution is just to change the
   definition of is_state_equivalence and the statement of [leq_equiv_states_commute].
   The idea is to have a single permutation perm such that
   perm(S,, a |-> v) < perm(S',, a |-> v')$. This is not currently possible as the states
   [S,, a |-> v] and [S',, a |-> v'] do not have the same anonymous variables and
   abstraction regions. But if we change the definition on is_state_equivalence so that a
   the domain of a the anonymous and abstractions permutations are superset (and not just equal)
   of the the respective maps, we could prove this.
   TODO: do these changes and remove this entire section.
 *)
Lemma fresh_anon_rename_state S a r : fresh_anon S a -> fresh_anon (rename_state r S) a.
Proof. unfold fresh_anon. rewrite !get_at_anon. cbn. simpl_map. intros ->. reflexivity. Qed.
Hint Resolve fresh_anon_rename_state : spath.

Lemma fresh_abstraction_rename_state S i r :
  fresh_abstraction S i -> fresh_abstraction (rename_state r S) i.
Proof. unfold fresh_abstraction. cbn. simpl_map. intros ->. reflexivity. Qed.
Hint Resolve fresh_abstraction_rename_state : spath.

Hint Resolve-> rename_state_valid_spath : spath.

Lemma _is_fresh_rename_state perm S l l' :
  valid_loan_id_names perm S -> lookup l perm = Some l' ->
  is_fresh l' (rename_state perm S) -> is_fresh l S.
Proof.
  intros Hperm H fresh_l p valid_p get_l. eapply fresh_l.
  - apply rename_state_valid_spath; eassumption.
  - rewrite rename_state_sget, get_node_rename_value by assumption.
    destruct (S.[p]); inversion get_l; cbn; unfold rename_loan_id; rewrite H; constructor.
Qed.

Lemma is_fresh_rename_state perm S l l' :
  valid_loan_id_names perm S -> lookup l perm = Some l' ->
  is_fresh l S -> is_fresh l' (rename_state perm S).
Proof.
  intros Hperm H. rewrite <-rename_state_invert_permutation at 1 by exact Hperm.
  apply _is_fresh_rename_state.
  - apply invert_valid_loan_id_names. exact Hperm.
  - apply lookup_Some_invert_permutation; [apply Hperm | exact H].
Qed.

Lemma leq_equiv_states_up_to_loan_renaming_commute S S' perm :
  valid_loan_id_names perm S -> valid_loan_id_names perm S' -> leq_state_base S' S ->
  leq_state_base (rename_state perm S') (rename_state perm S).
Proof.
  intros H G. destruct (H) as (inj_perm & perm_dom_S). destruct (G) as (_ & perm_dom_S').
  intros K. destruct K.
  - rewrite rename_state_sset by eauto with spath. apply Leq_ToSymbolic.
    all: rewrite rename_state_sget; eauto with spath.
  - rewrite rename_state_add_abstraction by assumption.
    rewrite loan_set_add_anon, loan_set_add_abstraction in * |- by assumption.
    rewrite rename_state_add_anon by (try split; set_solver).
    apply Leq_ToAbs; auto with spath.
    rewrite <-apply_id_permutation. apply to_abs_apply_permutation; [ | assumption].
    eapply is_permutation_dom_eq; [apply dom_fmap_L | apply id_permutation_is_permutation].
  - rewrite loan_set_add_anon in * |- by assumption.
    rewrite rename_state_add_anon by (try split; set_solver).
    apply Leq_RemoveAnon; auto with spath.
  - pose proof (loan_set_sget S sp).
    clear H perm_dom_S.
    rewrite rename_state_add_anon. 2: etransitivity; eassumption.
    2: apply valid_loan_id_names_sset; auto with spath.
    rewrite <-rename_state_sget, rename_state_sset by auto with spath.
    apply Leq_MoveValue; auto with spath.
    + rewrite rename_state_sget. not_contains.
    + intros p. rewrite rename_state_sget, get_node_rename_value.
      intros K. apply sp_not_in_borrow. destruct (get_node _); inversion K. constructor.
  - rewrite !rename_state_add_abstraction by auto with spath.
    apply Leq_MergeAbs; auto with spath.
    apply merge_abstraction_rename_value. assumption.
  - rewrite loan_set_add_anon, loan_set_borrow in perm_dom_S by auto with spath.
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (? & perm_dom_S).
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (l'_in_dom & ?).
    rewrite rename_state_add_anon.
    2: rewrite loan_set_borrow; set_solver. 2: split; assumption.
    rewrite rename_state_sset by set_solver. rewrite rename_loan_id_borrow, <-rename_state_sget.
    apply Leq_Fresh_MutLoan; auto with spath.
    + apply singleton_subseteq_l, elem_of_dom in l'_in_dom. destruct l'_in_dom as (l & get_l).
      eapply is_fresh_rename_state; eauto.
      unfold rename_loan_id. setoid_rewrite get_l. reflexivity.
    + rewrite rename_state_sget. eauto with spath.
  - rewrite loan_set_add_anon, loan_set_borrow in perm_dom_S by auto with spath.
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (? & l0_l1_in_dom).
    pose proof l0_l1_in_dom. rewrite union_subseteq in l0_l1_in_dom.
    destruct l0_l1_in_dom as (l0_in_dom & l1_in_dom).
    pose proof (loan_set_sget S (sp +++ [0])).
    rewrite rename_state_add_anon; [ | assumption | ].
    2: { apply valid_loan_id_names_sset; [ | assumption]. rewrite loan_set_borrow. set_solver. }
    rewrite rename_state_sset by (rewrite loan_set_borrow; set_solver).
    rewrite !rename_loan_id_borrow. rewrite <-rename_state_sget.
    cbn in l1_in_dom. apply singleton_subseteq_l, elem_of_dom in l1_in_dom.
    destruct l1_in_dom as (l'1 & get_l'1).
    apply Leq_Reborrow_MutBorrow.
    + eapply is_fresh_rename_state; eauto. unfold rename_loan_id. setoid_rewrite get_l'1.
      reflexivity.
    + auto with spath.
    + rewrite rename_state_sget, get_node_rename_value, get_borrow_l0. reflexivity.
    + assumption.
    + rewrite rename_state_sget. eauto with spath.
  - rewrite rename_state_remove_abstraction_value.
    eapply Leq_Abs_ClearValue.
    + unfold abstraction_element in *. rewrite get_at_abstraction in *. cbn. simpl_map.
      destruct (lookup i _); [ | discriminate]. cbn in *. simpl_map. reflexivity.
    + auto with spath.
    + auto with spath.
  - rewrite rename_state_add_anon by auto with spath.
    apply Leq_AnonValue. auto with spath.
Qed.

Definition equiv_val_state_up_to_loan_renaming (vS0 vS1 : LLBC_plus_val * LLBC_plus_state) :=
  let (v0, S0) := vS0 in
  let (v1, S1) := vS1 in
  exists perm, valid_loan_id_names perm S0 /\
               subseteq (loan_set_val v0) (dom perm) /\
               S1 = rename_state perm S0 /\ v1 = rename_value perm v0.

Definition leq_val_state_ut := chain equiv_val_state_up_to_loan_renaming (leq_val_state_base leq_state_base)^*.

Lemma equiv_val_state_up_to_loan_renaming_implies_equiv_val_state :
  forall vSl vSr, equiv_val_state_up_to_loan_renaming vSl vSr -> equiv_val_state vSl vSr.
Proof.
  intros (v & S) (? & ?) (r & ? & ? & -> & ->).
  exists {|accessor_perm := id_state_permutation S; loan_id_names := r|}.
  cbn. split.
  - split.
    + apply id_state_permutation_is_valid_accessor_permutation.
    + assumption.
  - split; [assumption | ]. split; [ | reflexivity].
    rewrite apply_state_permutation_alt
      by apply id_state_permutation_is_valid_accessor_permutation.
     cbn. rewrite apply_id_state_permutation. reflexivity.
Qed.

(* TODO: this could be a consequence of [leq_equiv_states_commute], with a different definition
 * of [is_state_equivalence] (see explanation at the start of the section. *)
Lemma prove_leq_val_state_base v S v' S' a :
  fresh_anon S a -> fresh_anon S' a -> leq_state_base (S,, a |-> v) (S',, a |-> v') ->
  leq_val_state_base leq_state_base (v, S) (v', S').
Proof.
  intros fresh_a_S fresh_a_S' Hleq.
  remember (S,, a |-> v) eqn:EQN. remember (S',, a |-> v') eqn:EQN'.
  destruct Hleq; subst.
  - destruct (decide (fst sp = anon_accessor a)).
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros fresh_b _.
      eapply prove_rel.
      { apply Leq_ToSymbolic with (sp := (anon_accessor b, snd sp)).
        all: autorewrite with spath; eassumption. }
      autorewrite with spath. reflexivity.
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros fresh_b _.
      eapply prove_rel.
      { apply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      autorewrite with spath. reflexivity.
  - process_state_eq.
    intros b. rewrite !fst_pair, !snd_pair. intros fresh_b _.
    rewrite fresh_anon_add_anon in fresh_b. destruct fresh_b as (? & ?).
    eapply prove_rel.
    { rewrite add_anon_commute by congruence. apply Leq_ToAbs; eauto with spath. }
    autorewrite with spath. reflexivity.
  - process_state_eq.
    intros b. rewrite !fst_pair, !snd_pair. intros (? & ?)%fresh_anon_add_anon _.
    rewrite add_anon_commute by congruence.
    apply Leq_RemoveAnon; auto with spath.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & valid_sp) | (? & valid_sp)].
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros ? (_ & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_MoveValue with (sp := sp) (a := a0); eauto with spath.
        autorewrite with spath. assumption. }
      states_eq.
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros _ (? & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_MoveValue with (sp := (anon_accessor b, snd sp)) (a := a0); eauto with spath.
        autorewrite with spath. assumption. rewrite no_ancestor_anon; auto. }
      states_eq.
  - process_state_eq.
    intros b. rewrite !fst_pair, !snd_pair. intros _ fresh_b.
    rewrite <-!add_abstraction_add_anon.
    apply Leq_MergeAbs; auto with spath.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & valid_sp) | (? & valid_sp)].
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros ? (_ & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_Fresh_MutLoan with (sp := sp) (l' := l') (a := a0); auto with spath.
        not_contains. autorewrite with spath. eassumption. }
      states_eq.
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros ? (_ & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_Fresh_MutLoan with (sp := (anon_accessor b, snd sp)) (l' := l') (a := a0);
          eauto with spath.
        not_contains. autorewrite with spath. eassumption. }
      states_eq.
  - destruct (decide (fst sp = anon_accessor a)).
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros ? (_ & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_Reborrow_MutBorrow with (sp := (anon_accessor b, snd sp)) (l1 := l1) (a := a0).
        all: eauto with spath. not_contains. all: autorewrite with spath; eassumption. }
      states_eq.
    + autorewrite with spath in * |-. process_state_eq.
      intros b. rewrite !fst_pair, !snd_pair. intros ? (_ & ?)%fresh_anon_add_anon.
      eapply prove_rel.
      { apply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1) (a := a0).
        all: eauto with spath. not_contains. all: autorewrite with spath; eassumption. }
      states_eq.
  - autorewrite with spath in * |-. process_state_eq.
    intros b. rewrite !fst_pair, !snd_pair. intros fresh_b _.
    eapply prove_rel.
    { eapply Leq_Abs_ClearValue with (i := i) (j := j).
      autorewrite with spath. all: eassumption. }
    autorewrite with spath. reflexivity.
  - process_state_eq.
    intros b. rewrite !fst_pair, !snd_pair. intros _ (? & ?)%fresh_anon_add_anon.
    rewrite add_anon_commute by congruence.
    eapply Leq_AnonValue. auto with spath.
Qed.

Instance transitive_equiv_val_state_up_to_loan_renaming :
  Transitive equiv_val_state_up_to_loan_renaming.
Proof.
  intros (v & S) (? & ?) (? & ?) (p0 & ? & H & -> & ->) (p1 & ? & G & -> & ->).
  exists (map_compose p1 p0). split. { apply valid_loan_id_names_compose; assumption. }
  rewrite rename_state_compose, rename_value_compose by assumption. split; [ | auto].
  intros l Hl. specialize (H l Hl).
  apply elem_of_dom. setoid_rewrite map_lookup_compose. apply elem_of_dom in H.
  destruct H as (l' & Hl'). rewrite Hl'. cbn.
  apply elem_of_dom, G.
  apply elem_of_loan_set_val in Hl. destruct Hl as (p & get_l).
  rewrite elem_of_loan_set_val. exists p.
  rewrite <-vget_rename_value, get_node_rename_value, get_loan_id_rename_node.
  rewrite get_l. cbn. unfold rename_loan_id. setoid_rewrite Hl'. reflexivity.
Qed.

Instance reflexive_equiv_val_state_up_to_loan_renaming :
  Reflexive equiv_val_state_up_to_loan_renaming.
Proof.
  intros (v & S). exists (id_loan_map (union (loan_set_state S) (loan_set_val v))). repeat split.
  - apply id_loan_map_inj.
  - rewrite dom_id_loan_map. set_solver.
  - rewrite dom_id_loan_map. set_solver.
  - symmetry. apply rename_state_identity.
  - symmetry. apply rename_value_id. apply lookup_id_loan_map.
Qed.

Instance reflexive_leq_val_state_ut : Reflexive leq_val_state_ut.
Proof. intros (v & S). exists (v, S). split; reflexivity. Qed.

Instance transitive_leq_val_state_ut : Transitive leq_val_state_ut.
Proof.
  apply transitive_leq.
  intros (v & S) (? & ?) (perm & H & ? & -> & ->) (v' & S') Hleq. destruct (H).
  destruct (exists_fresh_anon2 S S') as (a & fresh_a_S & fresh_a_S').
  specialize (Hleq a fresh_a_S' fresh_a_S). rewrite !fst_pair, !snd_pair in Hleq.
  edestruct (extend_loan_id_names (loan_set_state (S',, a |-> v'))) as (perm' & (? & ?) & ? & G).
  { split; [eassumption | ]. rewrite (loan_set_add_anon S a v); set_solver. }
  apply leq_equiv_states_up_to_loan_renaming_commute with (perm := perm') in Hleq.
  - rewrite loan_set_add_anon in * |- by assumption.
    assert (valid_loan_id_names perm' S') by (split; set_solver).
    rewrite <-G in Hleq. rewrite !rename_state_add_anon in Hleq by set_solver.
    eexists. split.
    + eapply prove_leq_val_state_base; [.. | exact Hleq]; now apply fresh_anon_rename_state.
    + exists perm'. set_solver.
  - split; assumption.
  - split; assumption.
Qed.

(** ** Simulation proofs for place evaluation. *)
Lemma eval_path_preservation Sl Sr perm p R :
  (forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) ->
  forward_simulation R R (eval_path Sr perm p) (eval_path Sl perm p).
Proof.
  intros preservation_proj. intros ? ? Heval_path.
  induction Heval_path.
  - intros ?. intros ?. eexists. split; [eassumption | constructor].
  - intros pi_l HR.
    edestruct preservation_proj as (pi_l' & ? & ?); [eassumption.. | ].
    edestruct IHHeval_path as (pi_l'' & ? & ?); [eassumption | ].
    exists pi_l''. split; [ | econstructor]; eassumption.
Qed.

(* This lemma is use to prove preservation of place evaluation for a relation rule Sl < Sr.
 * We prove that if p evaluates to a spath pi_r on Sr, then it also evaluates for a spath
 * pi_l on the left, with R pi_l pi_r.
 * The relation R depends on the rule, but for most rules it is simply going to be the equality. *)
Lemma eval_place_preservation Sl Sr perm p (R : spath -> spath -> Prop)
  (* Initial case: the relation R must be preserved for all spath corresponding to a variable. *)
  (R_nil : forall x, R (encode_var x, []) (encode_var x, []))
  (* All of the variables of Sr are variables of Sl.
   * Since most of the time, Sr is Sl with alterations on region abstractions, anonymous variables
   * or by sset, this is always true. *)
  (dom_eq : dom (vars Sl) = dom (vars Sr))
  (Hsim : forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) :
  forall pi_r, eval_place Sr perm p pi_r -> exists pi_l, R pi_l pi_r /\ eval_place Sl perm p pi_l.
Proof.
  intros pi_r ((? & G%mk_is_Some & _) & Heval_path).
  cbn in G. unfold encode_var in G. rewrite !sum_maps_lookup_l in G.
  rewrite <-elem_of_dom, <-dom_eq, elem_of_dom, <-get_at_var in G. destruct G as (? & ?).
  eapply eval_path_preservation in Heval_path; [ | eassumption].
  edestruct Heval_path as (pi_l' & ? & ?); [apply R_nil | ].
  exists pi_l'. split; [assumption | ]. split; [ | assumption].
  eexists. split; [eassumption | constructor].
Qed.

Lemma sset_preserves_vars_dom S sp v : dom (vars (S.[sp <- v])) = dom (vars S).
Proof.
  unfold sset. unfold alter_at_accessor. cbn. repeat autodestruct.
  intros. apply dom_alter_L.
Qed.

Lemma add_anon_preserves_vars_dom S a v : dom (vars (S,, a |-> v)) = dom (vars S).
Proof. reflexivity. Qed.

Lemma eval_place_ToSymbolic S sp p pi ty perm
  (Htype : is_of_type ty (S.[sp]))
  (H : (S.[sp <- LLBC_plus_symbolic ty]) |-{p} p =>^{perm} pi) :
  S |-{p} p =>^{perm} pi /\ ~strict_prefix sp pi.
Proof.
  pose proof (valid_pi := H). apply eval_place_valid in valid_pi.
  eapply eval_place_preservation with (R := eq) in H.
  - split.
    + destruct H as (? & -> & H). exact H.
    + eapply get_zeroary_not_strict_prefix'; [eassumption | reflexivity].
  - reflexivity.
  - symmetry. apply sset_preserves_vars_dom.
  - intros proj pi_r pi_r' Heval_proj ? ->. eexists. split; [reflexivity | ].
    inversion Heval_proj; subst.
    + autorewrite with spath in get_q. eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(* While we only have mutable loans and borrows, we cannot "jump into" an abstraction. When we
 * introduce shared loans/borrows, we need to redefine this relation. *)
Definition rel_ToAbs a i (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ fst p <> anon_accessor a.

(* Note: the hypothesis [no_borrow] is not necessary to prove this lemma. *)
(* The hypothesis [no_loan] is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_ToAbs S a i v A p perm
  (fresh_a : fresh_anon S a)
  (fresh_i : fresh_abstraction S i)
  (Hto_abs : to_abs v A) :
  forall pi_r, (S,,, i |-> A) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_ToAbs a i pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; [now eapply var_not_in_abstraction | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'.
    inversion Heval_proj; subst. repeat split; auto.
    autorewrite with spath in get_q. econstructor; autorewrite with spath; eassumption.
Qed.

(* Let Sl < Sr be two states in relation. Let's assume that there is a difference of one anonymous
 * variables between the two states.
 * Ex: Sr = Sl.[p <- v],, a |- w, or Sr = remove_anon a Sl
 * Any valid spath in Sl and Sr cannot be in the anonymous variable a.
 * The relation "rel_change_anon a" relates two equal paths in Sl and Sr that are not in a. *)
Definition rel_change_anon a (p q : spath) := p = q /\ fst p <> anon_accessor a.

(* Relates two equal paths pi_l and pi_r such that:
 * - Neither is in the anonymous variable a.
 * - Neither is under a given spath sp. *)
(* Used by the rules Leq_MoveValue and Leq_Fresh_MutLoan. *)
Definition rel_change_anon_not_in_spath sp a pi_l pi_r :=
  rel_change_anon a pi_l pi_r /\ ~strict_prefix sp pi_l.

(* Note: the hypothesis [no_borrow] is not necessary to prove this lemma. *)
(* The hypothesis [no_loan] is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_RemoveAnon S perm a v p
  (fresh_a : fresh_anon S a)
  (no_loan : not_contains_loan v) :
  forall pi_r, S |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  eapply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + autorewrite with spath in get_q.
      repeat split; try assumption.
      eapply Eval_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

(* Take Sr = Sl.[sp <- bot],, a |-> Sl.[sp] the left state. Relation between the evaluation
 * pi_l in Sl and pi_r in Sr: *)
Definition rel_MoveValue_imm sp a pi_l pi_r :=
  (pi_l = pi_r /\ ~strict_prefix sp pi_l /\ fst pi_l <> encode_anon a) \/
  (* If there is a (non-outer) mutable loan in S.[sp], it's possible to evaluate a place p there.
   * What happens is that in Sl, pi_l is under sp whereas in Sr, pi_r is in the newly added
   * anonymous variable. *)
  (* However, this is only possible when evaluating in mode Imm. *)
  (exists r, pi_l = sp +++ r /\ pi_r = (encode_anon a, r)).

Lemma eval_place_MoveValue_imm S sp a p
  (fresh_a : fresh_anon S a)
  (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{Imm} pi_r ->
  exists pi_l, rel_MoveValue_imm sp a pi_l pi_r /\ S |-{p} p =>^{Imm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. left. repeat split; [apply not_strict_prefix_nil | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as [(-> & ? & ?) | (r & -> & ->)].
      * rewrite sget_add_anon in get_q by assumption.
        exists (pi_r +++ [0]). split.
        -- left. repeat split; [solve_comp | assumption].
        -- eapply Eval_Deref_MutBorrow. assumption.
           autorewrite with spath in get_q. exact get_q.
      * exists ((sp +++ r) +++ [0]). split.
        --- right. exists (r ++ [0]). split; autorewrite with spath; reflexivity.
        --- eapply Eval_Deref_MutBorrow. assumption.
            autorewrite with spath in get_q. exact get_q.
Qed.

Lemma eval_place_change_anon_not_in_spath S sp a perm p
  (Hperm : perm <> Imm) (fresh_a : fresh_anon S a) (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. repeat split; [inversion 1 | apply not_strict_prefix_nil].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as ((-> & ?) & ?).
      rewrite sget_add_anon in get_q by assumption.
      exists (pi_r +++ [0]). split.
      * repeat split; [assumption | solve_comp].
      * eapply Eval_Deref_MutBorrow. assumption.
         autorewrite with spath in get_q. exact get_q.
Qed.

Definition rel_MergeAbs i j (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ ~in_abstraction j (fst p) /\ ~in_abstraction i (fst q).

Lemma eval_place_MergeAbs S i j A B C perm p
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) (diff : i <> j) :
    forall pi_r, (S,,, i |-> C) |-{p} p =>^{perm} pi_r ->
    exists pi_l, rel_MergeAbs i j pi_l pi_r /\ (S,,, i |-> A,,, j |-> B) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; intros (? & ?); easy.
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as (-> & ? & ? & ?). exists (pi_r +++ [0]).
      repeat split; [assumption.. | ].
      autorewrite with spath in get_q.
      eapply Eval_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_Fresh_MutLoan S sp l a perm p ty :
  forall pi_r, (S.[sp <- loan^m(ty, l)],, a |-> borrow^m(l, S.[sp])) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; auto with spath.
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? ((-> & ?) & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + (* We must perform a single rewrite in order to have the information required to prove
       * ~prefix sp pi_r. *)
      rewrite sget_add_anon in get_q by assumption.
      assert (~prefix sp pi_r) by solve_comp.
      autorewrite with spath in get_q.
      repeat split; [assumption | solve_comp | ].
      eapply Eval_Deref_MutBorrow; eassumption.
Qed.

Lemma eval_place_Reborrow_MutBorrow S sp l0 l1 a perm p ty
    (get_borrow_l0 : get_node (S.[sp]) = borrowC^m(l0)) pi_r :
  (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(ty, l1))) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  revert pi_r. apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption.
      destruct (decide (sp = pi_r)) as [<- | ].
      * eapply Eval_Deref_MutBorrow; eassumption.
      * autorewrite with spath in get_q.
        (* Note: this rewrite take up to 2s, with 80% of time spent on eauto with spath. *)
        eapply Eval_Deref_MutBorrow; eassumption.
Qed.

Lemma eval_place_Reborrow_MutBorrow_Mov S sp l0 l1 a p ty
    (get_borrow_l0 : get_node (S.[sp]) = borrowC^m(l0)) pi_r :
  (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(ty, l1))) |-{p} p =>^{Mov} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{Mov} pi_l.
Proof.
  revert pi_r. apply eval_place_preservation.
  - split; [split; [reflexivity | inversion 1] | apply not_strict_prefix_nil].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? ((-> & ?) & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; [assumption | solve_comp | ].
      destruct (decide (sp = pi_r)) as [<- | ].
      * eapply Eval_Deref_MutBorrow; eassumption.
      * autorewrite with spath in get_q.
        (* Note: this rewrite take up to 2s, with 80% of time spent on eauto with spath. *)
        eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(* When we add shared borrows and loans, this lemma becomes false when v contains a loan that can
 * be accessed in *)
Lemma eval_place_add_anon S a perm p v :
  forall pi_r, (S,, a |-> v) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption. autorewrite with spath in get_q.
      eapply Eval_Deref_MutBorrow; eassumption.
Qed.

Definition rel_Abs_ClearValue i j (p q : spath) := p = q /\ fst p <> encode_abstraction (i, j).

Lemma eval_place_Abs_ClearValue S i j v perm p :
  abstraction_element S i j = Some v -> not_contains_loan v ->
  forall pi_r, (remove_abstraction_value S i j) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Abs_ClearValue i j pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  intros ? ?. apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption. rewrite sget_remove_abstraction_value in get_q by assumption.
      eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(** Suppose that [Sl < Sr], and that p evaluates to a spath [pi] in [Sr]
   ([Sr |-{p} p =>^{perm} pi]).
    This tactic chooses the right lemmas to apply in order to prove that [p] reduces to a spath [pi'] in [Sl], and generates facts about [pi'].
   Finally, it proves that [pi] is valid in [Sr], and clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  let eval_p_in_Sl := fresh "eval_p_in_Sl" in
  let pi_l := fresh "pi_l" in
  let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
  lazymatch goal with

  (* Case ToSymbolic: *)
  | Htype : (is_of_type ?ty (?S.[?sp])),
    H : (?S.[?sp <- LLBC_plus_symbolic ?ty]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply (eval_place_ToSymbolic _ _ _ _ _ _ Htype) in H;
        destruct H as (eval_p_in_Sl & ?)

  (* Case ToAbs: *)
  | fresh_a : fresh_anon ?S ?a,
    fresh_i : fresh_abstraction ?S ?i,
    Hto_abs : to_abs ?v ?A,
    Heval : (?S,,, ?i |-> ?A) |-{p} ?p =>^{?perm} ?pi |- _ =>
        let _valid_pi := fresh "_valid_pi" in
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        (* Proving that pi is a valid spath of (remove_anon a S),,, i |-> A *)
        pose proof (eval_place_valid _ _ _ _ Heval) as _valid_pi;
        apply (eval_place_ToAbs _ _ _ _ _ _ _ fresh_a fresh_i Hto_abs) in Heval;
        destruct Heval as (? & (-> & pi_not_in_abstraction & pi_not_in_a) & eval_p_in_Sl);
        (* We can then prove that pi is a valid spath of (remove_anon a S) *)
        pose proof (not_in_abstraction_valid_spath _ _ _ _ _valid_pi pi_not_in_abstraction) as valid_pi;
        clear _valid_pi

  (* Case MoveValue *)
  (* Preservation of place evaluation with permission Imm. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{Imm} ?pi |- _ =>
        apply (eval_place_MoveValue_imm _ _ _ _ fresh_a valid_sp Hnot_in_abstraction) in H;
        destruct H as (pi_l & rel_pi_l_pi_r & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Mut or Mov. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_change_anon_not_in_spath in H;[ | discriminate | assumption..];
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  (* Case MergeAbs: *)
  | fresh_i : fresh_abstraction ?S ?i, fresh_j : fresh_abstraction ?S ?j,
    Hmerge : merge_abstractions ?A ?B ?C, diff : ?i <> ?j,
    Heval : (?S,,, ?i |-> ?C) |-{p} ?p =>^{?perm} ?pi_r
    |- _ =>
        apply (eval_place_MergeAbs _ _ _ _ _ _ _ _ fresh_i fresh_j Hmerge diff) in Heval;
        destruct Heval as (? & (-> & ? & ? & ?) & eval_p_in_Sl)

  (* Case Fresh_MutLoan *)
  | H : (?S.[?sp <- loan^m(?ty, ?l)],, ?a |-> borrow^m(?l, ?S.[?sp])) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_Fresh_MutLoan in H;
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  (* Case Reborrow_MutBorrow *)
  (* Preservation of place evaluation with permission Mov. *)
  | eval_p_in_Sr : (rename_mut_borrow ?S ?sp ?l1,, ?a |-> borrow^m(?l0, loan^m(?ty, ?l1))) |-{p} ?p =>^{Mov} ?pi |- _ =>
        apply eval_place_Reborrow_MutBorrow_Mov in eval_p_in_Sr; [ | assumption];
        destruct eval_p_in_Sr as (? & ((-> & ?) & ?) & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Imm or Mut. *)
  | eval_p_in_Sr : (rename_mut_borrow ?S ?sp ?l1,, ?a |-> borrow^m(?l0, loan^m(?ty, ?l1))) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_Reborrow_MutBorrow in eval_p_in_Sr; [ | assumption];
        destruct eval_p_in_Sr as (? & (-> & ?) & eval_p_in_Sl)

  (* Case Abs_ClearValue *)
  | H : abstraction_element ?S ?i ?j = Some ?v,
    no_loan : not_contains_loan ?v,
    Heval : remove_abstraction_value ?S ?i ?j |-{p} ?p =>^{?perm} ?pi_r |- _ =>
        eapply eval_place_Abs_ClearValue in Heval; [ | eassumption..];
        destruct Heval as (? & (-> & ?) & eval_p_in_Sl)

  (* Case AnonValue *)
  | eval_p_in_Sr : (?S,, ?a |-> bot) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_add_anon in eval_p_in_Sr;
        destruct eval_p_in_Sr as (? & (-> & ?) & eval_p_in_Sl)

  (* Case RemoveAnon *)
  | fresh_a : fresh_anon ?S ?a,
    no_loan : not_contains_loan ?v,
    Heval : ?S |-{p} ?p =>^{?perm} ?pi |- _ =>
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        pose proof (eval_place_valid _ _ _ _ Heval) as valid_pi;
        apply (eval_place_RemoveAnon _ _ _ _ _ fresh_a no_loan) in Heval;
        destruct Heval as (? & (-> & pi_not_a) & eval_p_in_Sl)
  end.

Lemma eval_place_permutation S permission P sp permutation
  (valid_permutation : is_state_equivalence permutation S) :
  S |-{p} P =>^{permission} sp ->
  apply_state_permutation permutation S |-{p} P =>^{permission} permutation_spath permutation sp.
Proof.
  intros ((v & get_v & _) & H). split.
  { eexists. split; [ | constructor]. rewrite fst_pair, get_at_var in *.
    cbn. simpl_map. reflexivity. }
  remember (encode_var (fst P), []) as sp0 eqn:EQN.
  replace sp0 with (permutation_spath permutation sp0)
    by (unfold permutation_spath; now rewrite EQN, fst_pair, perm_at_var).
  clear EQN get_v. induction H.
  - constructor.
  - econstructor; [ | eassumption]. destruct Heval_proj.
    + rewrite <-permutation_spath_app. eapply Eval_Deref_MutBorrow; [assumption | ].
      autorewrite with spath. rewrite get_q. reflexivity.
Qed.

(** ** Simulation proofs for operand evaluation. *)
(* TODO: find meaningful names. *)
Lemma _prove_leq_val_state_anon_left vl Sl vm Sm vSr b w
  (fresh_b : fresh_anon Sl b)
  (G : forall a, fresh_anon Sl a -> fresh_anon (Sl,, a |-> vl) b ->
       exists vSm, leq_state_base (Sl,, a |-> vl,, b |-> w) vSm /\ vSm = Sm,, a |-> vm) :
  leq_val_state_ut (vm, Sm) vSr ->
  leq_val_state_ut (vl, Sl,, b |-> w) vSr.
Proof.
  intros ?. etransitivity; [ | eassumption]. eexists.  split; [reflexivity | ]. constructor.
  intros a (? & ?)%fresh_anon_add_anon ?. rewrite !fst_pair, !snd_pair.
  rewrite add_anon_commute by congruence.
  destruct (G a) as (? & ? & ->); try assumption. rewrite fresh_anon_add_anon. auto.
Qed.

Lemma _prove_leq_val_state_left_to_right vl Sl vm Sm vSr
  (G : forall a, fresh_anon Sl a ->
       exists vSm, leq_state_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm) :
  leq_val_state_ut (vm, Sm) vSr ->
  leq_val_state_ut (vl, Sl) vSr.
Proof.
  intros ?. etransitivity; [ | eassumption]. eexists. split; [reflexivity | ]. constructor.
  intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
Qed.

(** This tactic is used to prove a goal of the form [(vl, Sl) < ?vSr] without
    exhibiting the existential variable [?vSr]. *)
Ltac leq_step_left :=
  let a := fresh "a" in
  let H := fresh "H" in
  lazymatch goal with
  |  |- ?leq_star^* (?vl, ?Sl,, ?b |-> ?w) ?vSr =>
      eapply prove_leq_val_state_anon_left;
        [eauto with spath |
         intros a ? ?; eexists; split |
        ]
  |  |- leq_val_state_ut (?vl, ?Sl,, ?b |-> ?w) ?vSr =>
      eapply _prove_leq_val_state_anon_left;
        [eauto with spath |
         intros a ? ?; eexists; split |
        ]
  (** When proving a goal [leq (vl, Sl) ?vSr], using this tactic creates three subgoals:
      - [leq_base (Sl,, a |-> v) ?vSm]
      - [?vSm = ?Sm,, a |-> ?vm]
      - [leq (?vm, ?Sm) ?vSr] *)
  | |- ?leq_star^* (?vl, ?Sl) ?vSr =>
      eapply prove_leq_val_state_left_to_right;
        [intros a ?; rewrite <-?fresh_anon_sset in H; eexists; split; [
          repeat rewrite <-add_abstraction_add_anon |
          ] |
        ]
  | |- leq_val_state_ut (?vl, ?Sl) ?vSr =>
      eapply _prove_leq_val_state_left_to_right;
        [intros a ?; rewrite <-?fresh_anon_sset in H; eexists; split; [
          repeat rewrite <-add_abstraction_add_anon |
          ] |
        ]
  | |- ?leq_star ?Sl ?Sr => eapply leq_step_left
  end.

(* TODO: meaningful name. *)
Lemma _prove_leq_val_state_add_anon vl Sl vm Sm vSr b w
  (fresh_b : fresh_anon Sl b)
  (G : forall a, fresh_anon Sl a -> fresh_anon (Sl,, a |-> vl) b ->
       exists vSm, leq_state_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm,, b |-> w) :
  leq_val_state_ut (vm, Sm,, b |-> w) vSr ->
  leq_val_state_ut (vl, Sl) vSr.
Proof.
  intros ?. etransitivity; [ | eassumption]. eexists. split; [reflexivity | ]. constructor.
  intros a ? (? & ?)%fresh_anon_add_anon. rewrite !fst_pair, !snd_pair.
  rewrite add_anon_commute by congruence.
  destruct (G a) as (? & ? & ->); try assumption.
  now apply fresh_anon_add_anon.
Qed.

(* To apply to the base rules of the form S < S',, b |-> w (with b fresh in S). The presence of
 * two anonymous variables, we need to do a special case.
 * Let a be a fresh anon. We prove that
 * 1. Sl,, a |-> vl < ?vSm
 * 2. ?vSm = Sm,, a |-> vm,, b |-> w
 * 3. (?vm, ?Sm) <* ?vSr
 *
 * To apply the base rule in (1), we need a hypothesis that b is fresh in Sl,, a |-> vl. This is
 * true because a and b are two different fresh variables.
 *
 * Because a and b are fresh, we can perform the following commutation:
 * Sm,, a |-> vm,, b |-> w = Sm,, b |-> w,, a |-> vm
 * Using (2), that shows that (vl, Sl) < (vm, Sm,, b |-> w).
 *)
Ltac leq_val_state_add_anon :=
  let a := fresh "a" in
  let H := fresh "H" in
  lazymatch goal with
  |  |- ?leq_star^* (?vl, ?Sl) ?vSr =>
      eapply prove_leq_val_state_add_anon;
        (* The hypothesis fresh_anon Sl b should be resolved automatically, because there should be
         * a single hypothesis of the form "fresh_anon Sr b" in the context, with Sr an expression
         * of Sl, that can be used. *)
        [eauto with spath; fail |
            intros a H; rewrite <-?fresh_anon_sset in H; eexists; split |
        ]
  |  |- leq_val_state_ut (?vl, ?Sl) ?vSr =>
      eapply _prove_leq_val_state_add_anon;
        (* The hypothesis fresh_anon Sl b should be resolved automatically, because there should be
         * a single hypothesis of the form "fresh_anon Sr b" in the context, with Sr an expression
         * of Sl, that can be used. *)
        [eauto with spath; fail |
            intros a H; rewrite <-?fresh_anon_sset in H; eexists; split |
        ]
  end.

Lemma copy_val_to_symbolic v w p ty (valid_p : valid_vpath v p)
  (no_mut_loan : not_contains_loan v)
  (Htype : is_of_type ty (v.[[p]]))
  (Hcopy_val : copy_val (v.[[p <- LLBC_plus_symbolic ty]]) w) :
  exists w0 q, copy_val v w0 /\ w = w0.[[q <- LLBC_plus_symbolic ty]] /\
               is_of_type ty (w0.[[q]]).
Proof.
  remember (v.[[p <- LLBC_plus_symbolic ty]]) eqn:EQN. induction Hcopy_val.
  - exfalso. symmetry in EQN. assert (p = []) as ->; [ | discriminate].
    eapply vset_is_zeroary; [eassumption | now rewrite EQN].
  - exfalso. symmetry in EQN. assert (p = []) as ->; [ | discriminate].
    eapply vset_is_zeroary; [eassumption | now rewrite EQN].
  - assert (p = []).
    { eapply vset_is_zeroary; [eassumption | ]. rewrite <-EQN. reflexivity. }
    subst. inversion EQN. subst.
    exists v, []. split; [ | auto]. cbn in Htype. inversion Htype; try (constructor; assumption).
    subst. exfalso. eapply no_mut_loan; [apply valid_nil | constructor].
Qed.

Lemma copied_val_no_bot v w : copy_val v w -> not_contains_bot v.
Proof. induction 1; not_contains. Qed.

Lemma copied_val_no_mut_loan v w : copy_val v w -> not_contains_loan v.
Proof. induction 1; not_contains. Qed.

Lemma copied_val_no_mut_borrow v w : copy_val v w -> not_contains_borrow v.
Proof. induction 1; not_contains. Qed.

Lemma copy_no_loan v w : copy_val v w -> not_contains_loan w.
Proof. induction 1; not_contains. Qed.

Lemma copy_no_mut_borrow v w : copy_val v w -> not_contains_borrow w.
Proof. induction 1; not_contains. Qed.

Lemma is_fresh_copy l S pi v :
  is_fresh l S -> copy_val (S.[pi]) v -> not_value_contains (is_loan_id l) v.
Proof.
  intros Hfresh Hcopy.
  destruct (decidable_valid_spath S pi).
  - eapply not_state_contains_implies_not_value_contains_sget in Hfresh; [ | eassumption].
    induction Hcopy; not_contains.
  - rewrite sget_invalid in Hcopy by assumption. inversion Hcopy.
Qed.
Hint Resolve is_fresh_copy : spath.

Lemma operand_preserves_LLBC_plus_rel op :
  forward_simulation leq_state_base^* (leq_val_state_base leq_state_base)^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = IntConst n *)
  - destruct Hle.
    + execution_step. { constructor. }
      leq_step_left.
      { eapply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_ToAbs with (a := a) (i := i) (A := A).
        all: autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply Leq_MoveValue with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_MergeAbs _ i j A B C); assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Fresh_MutLoan _ sp l' a). not_contains.
        eassumption.
        autorewrite with spath. validity. assumption. autorewrite with spath. eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Reborrow_MutBorrow _ sp l0 l1 a). not_contains. eassumption.
        autorewrite with spath. assumption. assumption. autorewrite with spath.  eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_AnonValue _ a); [assumption.. | ]. eassumption. }
      { reflexivity. }
      reflexivity.

  (* op = BoolConst n *)
  - destruct Hle.
    + execution_step. { constructor. }
      leq_step_left.
      { eapply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_ToAbs with (a := a) (i := i) (A := A).
        all: autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply Leq_MoveValue with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_MergeAbs _ i j A B C); assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Fresh_MutLoan _ sp l' a). not_contains. assumption. validity.
        assumption. autorewrite with spath. eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Reborrow_MutBorrow _ sp l0 l1 a). not_contains. assumption.
        autorewrite with spath. assumption. assumption. autorewrite with spath.  eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_AnonValue _ a); [assumption.. | ]. eassumption. }
      { reflexivity. }
      reflexivity.

  (* op = copy p *)
  - destruct Hle.
    (* Leq-ToSymbolic *)
    + eval_place_preservation.
      assert (not_contains_loan (S.[pi])).
      { eapply not_value_contains_sset_rev.
        - eapply copied_val_no_mut_loan. eassumption.
        - assumption.
        - validity. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: we copy the newly introduced symbolic value. *)
      * autorewrite with spath in Hcopy_val.
        apply copy_val_to_symbolic in Hcopy_val;
          [ | validity | assumption | autorewrite with spath; assumption].
          destruct Hcopy_val as (w & q' & Hcopy_val & -> & get_int').
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := pi +++ q); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        pose proof (copy_no_mut_borrow _ _ Hcopy_val).
        pose proof (copy_no_loan _ _ Hcopy_val).
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, q')).
          all: autorewrite with spath. eassumption.
          all: apply not_value_contains_vget; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      (* Case 2: we don't copy the newly introduced symbolic value. *)
      * assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.

    (* Leq-ToAbs *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; [eassumption | ]. autorewrite with spath. eassumption. }
      leq_step_left.
      { apply Leq_ToAbs with (i := i); eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-RemoveAnon *)
    + eval_place_preservation.
      execution_step. { econstructor; [eassumption | ]. autorewrite with spath. eassumption. }
      leq_step_left.
      { apply Leq_RemoveAnon; eauto with spath. }
      { reflexivity. }
      reflexivity.

    (* Leq-MoveValue *)
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [(-> & ? & ?) | (r & -> & ->)].
      (* Case 1: the place we copy is not in the moved value. *)
      * rewrite sget_add_anon in Hcopy_val by assumption.
        (* The place we copy is in fact disjoint from the moved value, because the copied
         * value cannot contain an unitialized value. *)
        assert (~prefix pi sp).
        { intros (q & <-). autorewrite with spath in Hcopy_val.
          eapply copied_val_no_bot; [eassumption | | now rewrite vset_vget_equal by validity].
          eapply vset_same_valid. validity. }
        assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        leq_val_state_add_anon.
        { apply Leq_MoveValue with (a := a) (sp := sp); eauto with spath.
          autorewrite with spath. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      (* Case 2: the place we copy is in the moved value (this can only happen with shared
       * borrows. *)
      * autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        leq_val_state_add_anon.
        { apply Leq_MoveValue with (a := a) (sp := sp); eauto with spath.
          autorewrite with spath. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.

    (* Leq-MergeAbs *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor. eassumption. autorewrite with spath. eassumption. }
      leq_step_left.
      { apply Leq_MergeAbs; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-Fresh-MutLoan *)
    + eval_place_preservation.
      rewrite sget_add_anon in Hcopy_val by assumption.
      assert (~prefix pi sp).
      { intros (q & <-). rewrite sset_sget_prefix in Hcopy_val by validity.
        eapply copied_val_no_mut_loan;
          [eassumption | | rewrite vset_vget_equal by validity; constructor].
        apply vset_same_valid. validity. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_Fresh_MutLoan with (sp := sp) (l' := l'); eauto with spath. not_contains.
        autorewrite with spath. eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-Reborrow-MutBorrow *)
    + eval_place_preservation. rewrite sget_add_anon in Hcopy_val by assumption.
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in Hcopy_val.
        eapply copied_val_no_mut_borrow;
          [eassumption | | rewrite vset_vget_equal by validity; constructor].
        apply vset_same_valid. validity. }
      autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1); eauto with spath.
        not_contains. all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-Abs-ClearValue *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      leq_step_left.
      { eapply Leq_Abs_ClearValue with (i := i) (j := j). autorewrite with spath.
        all: eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-AnonValue *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_AnonValue with (a := a). assumption. }
      { reflexivity. }
      reflexivity.

  (* op = move p *)
  - destruct Hle.
    (* Leq-ToSymbolic *)
    + eval_place_preservation.
      execution_step.
      { constructor. eassumption. not_contains. not_contains. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the value we turn into a symbolic value is in the place we move. *)
      * autorewrite with spath in * |-.
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, q)).
          all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.

      (* Case 2: the value we turn into a symbolic value is disjoint to the place we move. *)
      * assert (disj pi sp) by solve_comp.
        autorewrite with spath in * |-.
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := sp). all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.

    (* Leq-ToAbs *)
    + eval_place_preservation.
      autorewrite with spath in *.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath in *.
      leq_step_left.
      { apply Leq_ToAbs with (a := a) (i := i); [ | autorewrite with spath | ]; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-RemoveAnon *)
    + eval_place_preservation.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; eassumption. }
      autorewrite with spath. leq_step_left.
      { apply Leq_RemoveAnon with (a := a). eauto with spath.
        all: autorewrite with spath; assumption. }
      { reflexivity. }
      reflexivity.

    (* Leq-MoveValue *)
    + eval_place_preservation.
      (* The place pi we move does not contain any bottom value is the right state, as a
       * condition of the move rule.
       * The right state is Sr = S.[sp <- bot],, a |-> S.[sp].
       * That means that that sp cannot be inside sp, thus pi and sp are disjoint. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_bot. eapply move_no_bot with (p := q).
        apply vset_same_valid. validity. autorewrite with spath. reflexivity. }
      assert (disj pi sp) by solve_comp.
      autorewrite with spath in * |-.
      execution_step. { apply Eval_move; eassumption. }
      leq_val_state_add_anon.
       { apply Leq_MoveValue with (sp := sp) (a := a).
         autorewrite with spath; assumption. auto with spath. validity.
         eauto with spath. assumption. }
       { autorewrite with spath. reflexivity. }
      states_eq.

    (* Leq-MergeAbs *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath. leq_step_left.
      { apply Leq_MergeAbs with (A := A) (B := B) (i := i) (j := j); eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-Fresh-MutLoan *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      (* Because the path pi we move does not contain any loan, it cannot contain the spath sp
       * where the mutable loan is written. *)
      (* Note: this is similar to a reasonning we do for the case Leq_MoveValue. Make a lemma? *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_loan.
        eapply move_no_loan with (p := q). apply vset_same_valid. validity.
        autorewrite with spath. constructor. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in *.
      execution_step. { apply Eval_move; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_Fresh_MutLoan with (sp := sp) (l' := l').
        (* TODO: the tactic not_contains should solve it. *)
        not_contains.
        eassumption. all: autorewrite with spath. validity. assumption. eassumption. }
      { autorewrite with spath. reflexivity. }
      states_eq.

    (* Leq-Reborrow-MutBorrow *)
    + eval_place_preservation.
      autorewrite with spath in * |-. (* TODO: long. *)
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the spath sp we reborrow is in the place pi we move. *)
      * execution_step.
        { apply Eval_move. eassumption.
          eapply not_contains_rename_mut_borrow; eauto with spath.
          eapply not_contains_rename_mut_borrow; eauto with spath. }
         leq_val_state_add_anon.
        (* Because the place we reborrow was at sp +++ q, and that we move and return S.[sp],
         * the borrow is now in the anonymous value we evaluate a0, at path q. *)
         (* TODO: rename a0 *)
        { apply Leq_Reborrow_MutBorrow with (sp := (anon_accessor a0, q)) (l1 := l1).
          not_contains. eassumption. autorewrite with spath. eassumption. eauto with spath.
          autorewrite with spath in Htype |- *. exact Htype. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.

       (* Case 2: the spath sp we reborrow is disjoint from the place pi we move. *)
      * assert (disj pi sp) by solve_comp.
        autorewrite with spath in * |-. execution_step.
        { apply Eval_move; eassumption. }
        leq_val_state_add_anon.
        { apply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1).
          not_contains. eassumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.

    (* Leq-Abs-ClearValue *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step. { constructor; eassumption. }
      leq_step_left.
      { eapply Leq_Abs_ClearValue with (i := i) (j := j).
        all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-AnonValue *)
    + eval_place_preservation.
      autorewrite with spath in *.
      execution_step. { econstructor; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_AnonValue; eassumption. }
      { reflexivity. }
      reflexivity.
Qed.

Lemma copy_val_rename_value m v w : copy_val v w -> copy_val (rename_value m v) (rename_value m w).
Proof. induction 1; constructor. assumption. Qed.

Lemma copy_val_loan_set v w : copy_val v w -> subseteq (loan_set_val w) (loan_set_val v).
Proof. induction 1; set_solver. Qed.

Lemma operand_preserves_equiv op :
  forward_simulation equiv_states equiv_val_state (eval_operand op) (eval_operand op).
Proof.
  intros S0 S1 Heval S'0 Hequiv. destruct Heval.
  - execution_step. { constructor. } destruct Hequiv as (perm & ? & ?). exists perm. set_solver.

  - execution_step. { constructor. } destruct Hequiv as (perm & ? & ?). exists perm. set_solver.

  - symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ->).
    assert (valid_spath S pi) by eauto with spath.
    eapply eval_place_permutation in Heval_place; [ | eassumption].
    execution_step.
    { econstructor. eassumption. autorewrite with spath. apply copy_val_rename_value. eassumption. }
    symmetry. exists perm. repeat (easy || split).
    etransitivity; [apply copy_val_loan_set; eassumption | ].
    etransitivity; [apply loan_set_sget | apply Hperm].

  - symmetry in Hequiv. destruct Hequiv as (perm & ? & ->).
    assert (valid_spath S pi) by eauto with spath.
    eapply eval_place_permutation in Heval; [ | eassumption].
    execution_step.
    { econstructor. eassumption. all: autorewrite with spath; eauto with spath. }
    symmetry. exists perm. autorewrite with spath. repeat (eauto with spath || split).
    etransitivity; [apply loan_set_sget | apply H].
Qed.

Lemma operand_preserves_leq op :
  forward_simulation leq_symbolic leq_val_state (eval_operand op) (eval_operand op).
Proof.
  apply forward_simulation_chain.
  - apply operand_preserves_equiv.
  - apply operand_preserves_LLBC_plus_rel.
Qed.

(** ** Simulation proofs for rvalue evaluation. *)
Lemma integer_zeroary v :
  not_contains_loan v -> is_of_type intT v -> arity (get_node v) = 0.
Proof. intros ? H. inversion H; reflexivity. Qed.

Lemma integer_does_not_contain_borrow v : is_of_type intT v -> not_contains_borrow v.
Proof. inversion 1; not_contains. Qed.
Hint Resolve integer_does_not_contain_borrow : spath.

Lemma boolean_does_not_contain_borrow v : is_of_type boolT v -> not_contains_borrow v.
Proof. inversion 1; not_contains. Qed.
Hint Resolve boolean_does_not_contain_borrow : spath.

Lemma leq_val_state_base_integer vl Sl vr Sr :
  leq_val_state_base leq_state_base (vl, Sl) (vr, Sr) ->
  is_of_type intT vr -> not_contains_loan vr ->
  (vl = vr /\ leq_state_base Sl Sr) \/
  (is_of_type intT vl /\ not_contains_loan vl /\ vr = LLBC_plus_symbolic intT /\ Sl = Sr).
Proof.
  destruct (exists_fresh_anon2 Sl Sr) as (a & fresh_a_l & fresh_a_r).
  intros H vr_is_int no_loan.
  specialize (H a fresh_a_l fresh_a_r). rewrite !fst_pair, !snd_pair in H.
  remember (Sl,, a |-> vl) eqn:EQN_l. remember (Sr,, a |-> vr) eqn:EQN_r.
  destruct H; subst.
  - destruct (decide (fst sp = anon_accessor a)).
    + right. autorewrite with spath in * |-. process_state_eq.
      assert (snd sp = []) as G.
      { eapply valid_vpath_zeroary.
        - apply integer_zeroary; eassumption.
        - apply vset_same_valid; eauto with spath. }
      rewrite G in *. cbn in *. inversion vr_is_int. subst. eauto.
    + left. autorewrite with spath in *.
      process_state_eq. split; [reflexivity | ]. econstructor; eassumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; assumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; assumption.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & ?) | (? & ?)].
    2: { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply is_of_type_does_not_contain_bot.
      - eassumption.
      - apply vset_same_valid. validity.
      - autorewrite with spath. reflexivity. }
    autorewrite with spath in *. process_state_eq. autorewrite with spath in *.
    left. split; [reflexivity | ]. constructor; assumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; auto with spath.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & ?) | (? & ?)].
    2: { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply no_loan.
      - apply vset_same_valid. validity.
      - autorewrite with spath. constructor. }
    autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. apply Leq_Fresh_MutLoan; auto. not_contains.
  - destruct (decide (fst sp = anon_accessor a)).
    { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply integer_does_not_contain_borrow.
      - eassumption.
      - apply vset_same_valid. validity.
      - autorewrite with spath. constructor. }
    autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. apply Leq_Reborrow_MutBorrow; auto. not_contains.
  - autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. econstructor; eassumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor. assumption.
Qed.

Definition leq_integer_state (vSl vSr : LLBC_plus_val * LLBC_plus_state) :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  (vl = vr \/ is_of_type intT vl /\ not_contains_loan vl /\ vr = LLBC_plus_symbolic intT) /\ leq_state_base^* Sl Sr.

Lemma leq_val_state_integer vSl vSr :
  (leq_val_state_base leq_state_base)^* vSl vSr ->
  is_of_type intT (fst vSr) -> not_contains_loan (fst vSr) -> leq_integer_state vSl vSr.
Proof.
  intros H Htype no_loan.
  induction H as [(v & S) | (vl & Sl) (vm & Sm) (vr & Sr) ? ? leq_step]
    using clos_refl_trans_ind_left'.
  - split; [ | reflexivity]. left. reflexivity.
  - eapply leq_val_state_base_integer in leq_step; [ | eassumption..].
    destruct leq_step as [(? & ?) | (? & ? & ? & ?)]; subst.
    + destruct IHclos_refl_trans; [assumption.. | ]. split; [assumption | ].
      transitivity Sm; [ | constructor]; assumption.
    + destruct IHclos_refl_trans as ([ | (? & ? & ?)] & ?); [assumption.. | | ];
        subst; unfold leq_integer_state; auto.
Qed.

Lemma to_abs_not_contains v A l :
  map_Forall (fun _ => not_value_contains (is_loan_id l)) A -> to_abs v A ->
  not_value_contains (is_loan_id l) v.
Proof.
  intros G. induction 1.
  - rewrite map_Forall_insert in G by now simpl_map.
    destruct G as ((? & ?)%not_value_contains_loan_id_borrow & G).
    rewrite map_Forall_singleton in G by now simpl_map.
    apply not_value_contains_loan_id_loan in G.
    not_contains.
  - rewrite map_Forall_singleton in G by now simpl_map.
    apply not_value_contains_loan_id_borrow in G. destruct G as (? & _). not_contains.
Qed.

Lemma add_is_integer v0 v1 w (H : eval_binary_op BAdd v0 v1 w) :
  is_of_type intT v0 /\ is_of_type intT v1 /\ is_of_type intT w.
Proof. inversion H; repeat split; constructor. Qed.

Lemma add_no_loan v0 v1 w (H : eval_binary_op BAdd v0 v1 w) :
  not_contains_loan v0 /\ not_contains_loan v1 /\ not_contains_loan w.
Proof. inversion H; repeat split; not_contains. Qed.

Lemma le_is_bool v0 v1 w (H : eval_binary_op BLe v0 v1 w) :
  is_of_type intT v0 /\ is_of_type intT v1 /\ is_of_type boolT w.
Proof. inversion H; repeat split; constructor. Qed.

Lemma le_no_loan v0 v1 w (H : eval_binary_op BLe v0 v1 w) :
  not_contains_loan v0 /\ not_contains_loan v1 /\ not_contains_loan w.
Proof. inversion H; repeat split; not_contains. Qed.

Lemma leq_base_implies_leq_val_state_base Sl Sr v
  (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
  leq_state_base^* Sl Sr -> leq_val_state_ut (v, Sl) (v, Sr).
Proof.
  intros H. eexists. split; [reflexivity | ].
  induction H as [Sl Sr H | | ].
  - constructor. intros a fresh_a_l fresh_a_r. rewrite !fst_pair, !snd_pair in *.
    destruct H.
    + rewrite <-sset_add_anon by eauto with spath.
      econstructor; autorewrite with spath; eassumption.
    + rewrite fresh_anon_add_anon in fresh_a_l. destruct fresh_a_l.
      rewrite <-add_abstraction_add_anon, add_anon_commute by congruence.
      constructor; auto with spath.
    + rewrite fresh_anon_add_anon in fresh_a_l. destruct fresh_a_l.
      rewrite add_anon_commute by congruence. constructor; auto with spath.
    + rewrite fresh_anon_add_anon in fresh_a_r. destruct fresh_a_r.
      rewrite <-add_anon_commute, <-sset_add_anon by congruence || eauto with spath.
      erewrite <-(sget_add_anon _ a) by eauto with spath.
      apply Leq_MoveValue ; eauto with spath. autorewrite with spath. assumption.
    + rewrite <-!add_abstraction_add_anon. constructor; auto with spath.
    + rewrite fresh_anon_add_anon in fresh_a_r. destruct fresh_a_r.
      rewrite <-add_anon_commute, <-sset_add_anon by congruence || eauto with spath.
      erewrite <-(sget_add_anon _ a) by eauto with spath.
      apply Leq_Fresh_MutLoan; eauto with spath.
      * not_contains.
      * autorewrite with spath. assumption.
    + rewrite fresh_anon_add_anon in fresh_a_r. destruct fresh_a_r.
      rewrite <-add_anon_commute, <-sset_add_anon by congruence || eauto with spath.
      erewrite <-(sget_add_anon _ a) by eauto with spath.
      apply Leq_Reborrow_MutBorrow; autorewrite with spath; auto with spath. not_contains.
    + rewrite <- remove_abstraction_value_add_anon.
      econstructor; autorewrite with spath; eassumption.
    + rewrite fresh_anon_add_anon in fresh_a_r. destruct fresh_a_r.
      rewrite <-add_anon_commute by congruence. constructor. eauto with spath.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Lemma binop_integers v0 v1 binop :
  not_contains_loan v0 -> not_contains_loan v1 ->
  is_of_type intT v0 -> is_of_type intT v1 -> exists w, eval_binary_op binop v0 v1 w.
Proof.
  intros v0_no_loan v1_no_loan H G.
  destruct v0; inversion H; destruct v1; inversion G.
  all: try (exfalso; eapply loan_contains_loan; eassumption).
  all: destruct binop; eexists; constructor.
Qed.

Lemma rename_value_subset v m m' :
  subseteq (loan_set_val v) (dom m) -> subseteq m m' ->
  rename_value m' v = rename_value m v.
Proof.
  induction v; intros H Hincl; try reflexivity.
  - cbn in H. apply singleton_subseteq_l, elem_of_dom in H. cbn. unfold rename_loan_id.
    destruct H as (? & G). setoid_rewrite G.
    eapply map_subseteq_spec in Hincl; [ | exact G]. setoid_rewrite Hincl. reflexivity.
  - rewrite loan_set_borrow in H. apply union_subseteq in H. destruct H as (H & ?).
    rewrite !rename_loan_id_borrow. rewrite IHv by assumption.
    apply singleton_subseteq_l, elem_of_dom in H. cbn. unfold rename_loan_id.
    destruct H as (? & H). setoid_rewrite H.
    eapply map_subseteq_spec in Hincl; [ | exact H]. setoid_rewrite Hincl. reflexivity.
Qed.

Lemma rename_state_subset S m m' :
  subseteq (loan_set_state S) (dom m) -> subseteq m m' ->
  rename_state m' S = rename_state m S.
Proof.
  intros ? ?. apply state_eq_ext.
  - rewrite !get_map_rename_state. apply map_fmap_ext. intros.
    apply rename_value_subset; [ | assumption]. etransitivity; [ | eassumption].
    eapply loan_set_val_subset_eq_loan_set_state. eassumption.
  - rewrite !get_extra_rename_state. reflexivity.
Qed.

Lemma rename_loan_eval_mut_borrow S l l' pi ty (valid_pi : valid_spath S pi)
  (fresh_l : is_fresh l S) (fresh_l' : is_fresh l' S) :
  equiv_val_state_up_to_loan_renaming (borrow^m(l', S.[pi]), S.[pi <- loan^m(ty, l')])
                                      (borrow^m(l, S.[pi]), S.[pi <- loan^m(ty, l)]).
Proof.
  exists (insert l' l (id_loan_map (loan_set_state S))). split; split.
  - apply map_inj_insert; [ | apply id_loan_map_inj].
    intros l'' G. pose proof (lookup_id_loan_map _ _ _ G). subst.
    apply mk_is_Some, elem_of_dom in G.
    rewrite dom_id_loan_map, elem_of_loan_set_state in G. destruct G as (q & G).
    eapply fresh_l; [eapply get_loan_id_valid_spath | ]; exact G.
  - setoid_rewrite dom_insert_L. rewrite dom_id_loan_map.
    pose proof (loan_set_sset S pi (loan^m(ty, l'))) as H. cbn [loan_set_val] in H.
    set_solver.
  - setoid_rewrite dom_insert_L. rewrite dom_id_loan_map.
    rewrite loan_set_borrow. pose proof (loan_set_sget S pi). set_solver.
  - rewrite rename_state_sset by (setoid_rewrite dom_insert_L; apply union_subseteq_l).
    rewrite rename_loan_id_borrow. cbn [rename_value].
    unfold rename_loan_id. setoid_rewrite lookup_insert.
    rewrite <-rename_state_sget. replace (rename_state _ S) with S; auto.
    erewrite rename_state_subset, rename_state_identity.
    + reflexivity.
    + rewrite dom_id_loan_map. reflexivity.
    + apply insert_subseteq.
      rewrite eq_None_not_Some, <-elem_of_dom, dom_id_loan_map, elem_of_loan_set_state.
      intros (p & get_l').
      eapply fresh_l'; [eapply get_loan_id_valid_spath | ]; exact get_l'.
Qed.

Lemma leq_val_state_by_equiv vSl vSr :
  equiv_val_state_up_to_loan_renaming vSl vSr -> leq_val_state_ut vSl vSr.
Proof. exists vSr. split; [assumption | reflexivity]. Qed.

Lemma rvalue_preserves_LLBC_plus_rel rv :
  forward_simulation leq_state_base^* leq_val_state_ut (eval_rvalue rv) (eval_rvalue rv).
Proof.
  apply preservation_by_base_case.
  intros Sr vSr eval_rv Sl Hleq. destruct eval_rv.
  - apply operand_preserves_LLBC_plus_rel in Heval_op.
    edestruct Heval_op as (vS'l & ? & ?); [constructor; eassumption | ].
    exists vS'l. split.
    + eexists. split; [reflexivity | assumption].
    + constructor. assumption.

  - apply operand_preserves_LLBC_plus_rel in eval_op_0, eval_op_1.
    edestruct eval_op_0 as ((v0l & S'l) & leq_S'l_S' & H); [constructor; eassumption | ].
    destruct binop.
    + destruct (add_is_integer _ _ _ Hbinop) as (? & ? & ?).
      destruct (add_no_loan _ _ _ Hbinop) as (? & ? & ?).
      apply leq_val_state_integer in leq_S'l_S'; [ | assumption..].
      destruct leq_S'l_S' as (Hv0 & leq_S'l_S').
      edestruct eval_op_1 as ((v1l & S''l) & leq_S''l_S'' & ?); [exact leq_S'l_S' | ].
      apply leq_val_state_integer in leq_S''l_S''; [ | assumption..].
      destruct leq_S''l_S'' as (Hv1 & leq_S''l_S'').
      destruct Hv0 as [-> | (? & ? & ->)]; destruct Hv1 as [-> | (? & ? & ->)].
      * execution_step. { econstructor; eassumption. }
        apply leq_base_implies_leq_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0 v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic intT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0l v1 wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic intT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0l v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic intT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath.
    + destruct (le_is_bool _ _ _ Hbinop) as (? & ? & ?).
      destruct (le_no_loan _ _ _ Hbinop) as (? & ? & ?).
      apply leq_val_state_integer in leq_S'l_S'; [ | assumption..].
      destruct leq_S'l_S' as (Hv0 & leq_S'l_S').
      edestruct eval_op_1 as ((v1l & S''l) & leq_S''l_S'' & ?); [exact leq_S'l_S' | ].
      apply leq_val_state_integer in leq_S''l_S''; [ | assumption..].
      destruct leq_S''l_S'' as (Hv1 & leq_S''l_S'').
      destruct Hv0 as [-> | (? & ? & ->)]; destruct Hv1 as [-> | (? & ? & ->)].
      * execution_step. { econstructor; eassumption. }
        apply leq_base_implies_leq_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BLe v0 v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic boolT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath; not_contains.
      * assert (exists wl, eval_binary_op BLe v0l v1 wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic boolT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath; not_contains.
      * assert (exists wl, eval_binary_op BLe v0l v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, [])).
          all: autorewrite with spath; eauto with spath. }
        { autorewrite with spath. reflexivity. }
        replace w with (LLBC_plus_symbolic boolT) by now inversion Hbinop.
        apply leq_base_implies_leq_val_state_base; eauto with spath; not_contains.

  - destruct Hleq.
    (* Case Leq_ToSymbolic: *)
    + eval_place_preservation.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); [eassumption | not_contains.. | ].
        eapply is_of_type_sset_rev; try eassumption. constructor. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the symbolic value is in the borrowed value. *)
      * leq_step_left.
        { eapply Leq_ToSymbolic with (sp := (anon_accessor a, [0] ++ q)).
          all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.
      (* Case 2: the symbolic value is out of the borrowed value, the place where it is and
       * the borrowed place are disjoint. *)
      * assert (disj pi sp) by solve_comp.
        leq_step_left.
        { eapply Leq_ToSymbolic with (sp := sp).
          all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.
    (* Case Leq_ToAbs: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); autorewrite with spath; try eassumption.
        not_contains. eapply to_abs_not_contains; eassumption. }
      autorewrite with spath. leq_step_left.
      { apply Leq_ToAbs with (i := i); eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    (* Case Leq_RemoveAnon: *)
    + eval_place_preservation.
      execution_step.
      { eapply Eval_mut_borrow with (l := l). eassumption.
        all: autorewrite with spath; not_contains. }
      autorewrite with spath. leq_step_left.
      { apply Leq_RemoveAnon; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    (* Case Leq_MoveValue: *)
    + eval_place_preservation.
      (* The moved value cannot be in the borrowed value, because it does not contain
       * uninitialized values. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in borrow_no_bot.
        eapply borrow_no_bot with (p := q).
        - apply vset_same_valid. validity.
        - autorewrite with spath. reflexivity. }
      assert (disj pi sp) by solve_comp.
      autorewrite with spath in *.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); try eassumption. not_contains. }
      leq_val_state_add_anon.
      { apply Leq_MoveValue with (a := a) (sp := sp). not_contains_outer.
        eauto with spath. validity. eauto with spath. assumption. }
      { autorewrite with spath. reflexivity. }
      states_eq.
    (* Case Leq_MergeAbs: *)
    + autorewrite with spath. eval_place_preservation.
      destruct (exists_fresh_loan_id (S,,, i |-> A,,, j |-> B)) as (l' & fresh_l').
      execution_step.
      { eapply Eval_mut_borrow with (l := l'); try eassumption.
        all: autorewrite with spath in *; not_contains. }
      autorewrite with spath. leq_step_left.
      { eapply Leq_MergeAbs; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      apply leq_val_state_by_equiv.
      (* Sadly I have to undo the automatic rewritings, there is probably a better way to do
       * it. *)
      rewrite <-!sset_add_abstraction_notin by auto with spath.
      rewrite <-!(sget_add_abstraction_notin S i C) by auto with spath.
      apply rename_loan_eval_mut_borrow; eauto with spath.
      rewrite !not_state_contains_add_abstraction in * by eauto with spath.
      destruct fresh_l' as ((? & l'_not_in_A) & l'_not_in_B). split; [assumption | ].
      intros ? ? K. eapply merge_abstractions_contains in K; [ | exact Hmerge].
      destruct K as [(? & _) | (? & ? & _)]; eauto.
    (* Case Leq_Fresh_MutLoan: *)
    + eval_place_preservation.
      (* The loan cannot be in the borrowed value. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in borrow_no_loan.
        eapply borrow_no_loan with (p := q).
        - apply vset_same_valid. validity.
        - autorewrite with spath. constructor. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in *.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); try eassumption. not_contains. }
      leq_val_state_add_anon.
      { apply Leq_Fresh_MutLoan with (a := a) (sp := sp) (l' := l'). not_contains.
        eauto with spath. validity. assumption. autorewrite with spath. eassumption. }
      { autorewrite with spath. reflexivity. }
      states_eq.
    (* Case Leq_Reborrow_MutBorrow: *)
    + eval_place_preservation. rewrite sget_add_anon in * by assumption.
      autorewrite with spath in Htype.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); try eassumption; not_contains.
        eapply is_of_type_rename_mut_borrow; eassumption. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the reborrow is in the borrowed value. *)
      * leq_val_state_add_anon.
        { eapply Leq_Reborrow_MutBorrow
            with (sp := (anon_accessor a0, [0] ++ q)) (l1 := l1) (a := a).
          not_contains. eauto with spath. autorewrite with spath. eassumption. eauto with spath.
          autorewrite with spath in Htype0 |- *. eassumption. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.
      (* Case 2: the reborrow is not in the borrowed value. *)
      * leq_val_state_add_anon.
        { eapply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1) (a := a).
          not_contains. eauto with spath. autorewrite with spath. eassumption. eauto with spath.
          rewrite sget_add_anon by eauto with spath.
          eapply is_of_type_rename_mut_borrow in Htype; [ | eassumption].
          eapply is_of_type_sset_sget; try eassumption. constructor. }
        { autorewrite with spath. (* TODO: long. *) reflexivity. }
        (* TODO: long. *) autorewrite with spath. reflexivity.
    (* Case Leq_Abs_ClearValue: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { eapply Eval_mut_borrow with (l := l); try eassumption.
        (* TODO: lemma. *)
        intros q valid_q. destruct (decide (fst q = encode_abstraction (i, j))).
        - erewrite abstraction_element_is_sget' by eassumption.
          intros G. destruct (v.[[snd q]]) eqn:EQN; inversion G.
          + eapply no_loan; [ | rewrite EQN; constructor]. validity.
          + eapply no_borrow; [ | rewrite EQN; constructor]. validity.
        - specialize (fresh_l q). autorewrite with spath in fresh_l. apply fresh_l. validity. }
      leq_step_left.
      { eapply Leq_Abs_ClearValue with (i := i) (j := j). autorewrite with spath. all: eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    (* Case Leq_AnonValue: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { apply Eval_mut_borrow with (l := l); [eassumption.. | | eassumption]. not_contains. }
      leq_val_state_add_anon.
      { eapply Leq_AnonValue with (a := a). eauto with spath. }
      { reflexivity. }
      reflexivity.
Qed.

Lemma bin_op_rename_value v0 v1 m0 m1 w binop
  (H : eval_binary_op binop (rename_value m0 v0) (rename_value m1 v1) w) :
  eval_binary_op binop v0 v1 w.
Proof.
  replace (rename_value m0 v0) with v0 in H by now destruct v0.
  replace (rename_value m1 v1) with v1 in H by now destruct v1.
  exact H.
Qed.

Lemma rvalue_preserves_equiv rv :
  forward_simulation equiv_states equiv_val_state (eval_rvalue rv) (eval_rvalue rv).
Proof.
  intros S0 S1 Heval S'0 Hequiv. destruct Heval.
  - apply operand_preserves_equiv in Heval_op.
    edestruct Heval_op as (vS'' & ? & ?); [exact Hequiv | ].
    execution_step. { constructor. eassumption. } assumption.
  - apply operand_preserves_equiv in eval_op_0, eval_op_1.
    edestruct eval_op_0 as ((v'0 & ?) & Hequiv' & ?); [exact Hequiv | ].
    edestruct eval_op_1 as ((v'1 & ?) & Hequiv'' & ?);
      [eapply equiv_val_state_weaken; exact Hequiv' | ].
    destruct Hequiv' as (perm & _ & _ & _ & ->).
    destruct Hequiv'' as (perm' & ? & _ & -> & ->).
    apply bin_op_rename_value in Hbinop.
    execution_step. { econstructor; eassumption. }
    exists perm'. assert (loan_set_val w = empty) by now inversion Hbinop.
    rewrite rename_value_no_loan_id by assumption.
    repeat (assumption || split). set_solver.
  - symmetry in Hequiv. destruct Hequiv as (_perm & Hperm & ->).
    apply (extend_state_permutation (singleton l)) in Hperm.
    destruct Hperm as (perm & Hperm & Hl & ->).
    pose proof Hl as (l' & Hl')%singleton_subseteq_l%elem_of_dom.
    eapply eval_place_permutation in eval_p; [ | eassumption].
    execution_step.
    { econstructor. eassumption.
      all: autorewrite with spath; eauto with spath. eapply is_fresh_apply_permutation; eassumption. }
    symmetry. exists perm. autorewrite with spath.
    split; [auto with spath | ]. split.
    + rewrite loan_set_borrow. destruct Hperm as (_ & (_ & ?)).
      pose proof (loan_set_sget S pi). set_solver.
    + cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl'. auto.
Qed.

Lemma rvalue_preserves_leq rv :
  forward_simulation leq_symbolic leq_val_state (eval_rvalue rv) (eval_rvalue rv).
Proof.
  intros S0 (v & S'0) eval_rv S2 (S1 & equiv_S2_S1 & leq_S1_S0).
  eapply rvalue_preserves_LLBC_plus_rel in eval_rv.
  specialize (eval_rv S1 leq_S1_S0). destruct eval_rv as (vS'1 & leq_S'1_S'0 & eval_rv).
  eapply rvalue_preserves_equiv in eval_rv.
  specialize (eval_rv S2 equiv_S2_S1). destruct eval_rv as (vS'2 & equiv_S'2_S'1 & eval_rv).
  exists vS'2. split; [ | exact eval_rv].
  destruct leq_S'1_S'0 as (vS''1 & ? & ?). exists vS''1. split; [ | assumption].
  etransitivity; [eassumption | ].
  apply equiv_val_state_up_to_loan_renaming_implies_equiv_val_state. assumption.
Qed.

(** ** Simulation proofs for the [store] operation. *)
(** We only store values that come from rvalue evaluations, and these values do not contain loans or
    unitialized values. This can be used to prune cases. *)
Lemma eval_rvalue_no_bot S S' rv v : S |-{rv} rv => (v, S') -> not_contains_bot v.
Proof.
  inversion 1; subst; [ | inversion Hbinop; not_contains | not_contains].
  inversion Heval_op; subst.
  + not_contains.
  + not_contains.
  + induction Hcopy_val; not_contains.
  + assumption.
Qed.

Lemma eval_rvalue_no_loan S S' rv v : S |-{rv} rv => (v, S') -> not_contains_loan v.
Proof.
  inversion 1; subst; [ | inversion Hbinop; not_contains | not_contains].
  inversion Heval_op; subst.
  + not_contains.
  + not_contains.
  + induction Hcopy_val; not_contains.
  + assumption.
Qed.

(** The stronger relation between pairs of value and state with the absence of loans and
    unitilialized values. *)
Definition leq_val_state_base' vSl vSr :=
  leq_val_state_base leq_state_base vSl vSr /\
  not_contains_bot (fst vSr) /\ not_contains_loan (fst vSr).

(** If [Sl <^* Sr] and [Sr] does not contain any loan or unitialized value, then this is the case for
    all of the intermediary states. *)
(* Note: this proof is very repetitive, it could easily be automated. *)
Lemma leq_base_does_not_insert_bot_loan vSl vSr :
  leq_val_state_base' vSl vSr -> not_contains_bot (fst vSl) /\ not_contains_loan (fst vSl).
Proof.
  intros (Hle & Hno_bot & Hno_loan).
  edestruct exists_fresh_anon2 as (a & fresh_a_l & fresh_a_r).
  specialize (Hle a fresh_a_l fresh_a_r).
  remember ((vSl.2),, a |-> vSl.1) eqn:EQN_l.
  remember ((vSr.2),, a |-> vSr.1) eqn:EQN_r.
  destruct Hle; subst.
  - destruct (decide (fst sp = anon_accessor a)).
    all: autorewrite with spath in * |-; process_state_eq.
    all: rewrite <-eq_val in *; split; not_contains.
  - process_state_eq. rewrite <-!eq_val. auto.
  - process_state_eq. rewrite <-!eq_val. auto.
  - apply valid_spath_add_anon_cases in valid_sp. destruct valid_sp as [(? & _) | (? & ?)].
    + autorewrite with spath in EQN_r. process_state_eq. rewrite !eq_val. auto.
    + autorewrite with spath in EQN_r. process_state_eq.
      exfalso. eapply Hno_bot with (p := snd sp); rewrite <-eq_val.
      * apply vset_same_valid. assumption.
      * autorewrite with spath. reflexivity.
  - process_state_eq. rewrite !eq_val. auto.
  - apply valid_spath_add_anon_cases in valid_sp. destruct valid_sp as [(? & _) | (? & ?)].
    + autorewrite with spath in EQN_r. process_state_eq. rewrite !eq_val. auto.
    + autorewrite with spath in EQN_r. process_state_eq.
      exfalso. eapply Hno_loan with (p := snd sp); rewrite <-eq_val.
      * apply vset_same_valid. assumption.
      * autorewrite with spath. constructor.
  - destruct (decide (fst sp = anon_accessor a)).
    + autorewrite with spath in *. process_state_eq.
      replace (fst vSl) with ((fst vSr).[[snd sp <- borrow^m(l0, (fst vSr).[[snd sp ++ [0] ]])]]).
      * (* Note: the validity proofs could be better automated. *)
        assert (valid_vpath (fst vSr) (sp.2 ++ [0])).
        { rewrite <-eq_val. apply valid_vpath_app. split.
          - apply vset_same_valid. validity.
          - rewrite vset_vget_equal by validity. econstructor; [reflexivity | constructor].
        }
        split. all: eapply not_value_contains_vset; [eassumption | ]. all: not_contains.
        -- intros q valid_q. autorewrite with spath. eapply Hno_bot.
           rewrite app_assoc, valid_vpath_app. split; assumption.
        -- intros q valid_q. autorewrite with spath. eapply Hno_loan.
           rewrite app_assoc, valid_vpath_app. split; assumption.
      * rewrite <-eq_val. autorewrite with spath. rewrite vset_twice_equal.
        etransitivity; [ | eapply vset_same]. f_equal. rewrite vget_app.
        destruct ((fst vSl).[[snd sp]]); inversion get_borrow_l0. reflexivity.
    + autorewrite with spath in *. process_state_eq. rewrite !eq_val. auto.
  - autorewrite with spath in EQN_r. process_state_eq. rewrite !eq_val. auto.
  - process_state_eq. rewrite !eq_val. auto.
Qed.

Lemma leq_val_state_no_bot_loan_right vSl vSr :
  (leq_val_state_base leq_state_base)^* vSl vSr ->
  not_contains_bot (fst vSr) -> not_contains_loan (fst vSr) -> leq_val_state_base'^* vSl vSr.
Proof.
  intros Hle Hno_loan Hno_loc.
  apply proj1 with (B := (not_contains_bot (fst vSl)) /\ (not_contains_loan (fst vSl))).
  induction Hle.
  - split.
    + constructor. repeat split; assumption.
    + eapply leq_base_does_not_insert_bot_loan. repeat split; eassumption.
  - repeat split; [reflexivity | assumption..].
  - destruct IHHle2 as (? & ? & ?); [assumption.. | ].
    destruct IHHle1 as (? & ? & ?); [assumption.. | ].
    repeat split; [ | assumption..]. etransitivity; eassumption.
Qed.

Lemma not_contains_outer_loan_rename_mut_borrow S sp l0 l1 sp_store :
  get_node (S.[sp]) = borrowC^m(l0) ->
  not_contains_outer_loan (rename_mut_borrow S sp l1.[sp_store]) ->
  not_contains_outer_loan (S.[sp_store]).
Proof.
  intros get_borrow no_outer.
  destruct (decidable_prefix sp_store sp) as [(q & <-) | ].
  - intros r ? get_loan. rewrite <-sget_app in get_loan.
    destruct (decidable_vprefix q r) as [ | not_prefix].
    + exists q. rewrite <-sget_app, get_borrow. split; [ | constructor].
      apply vprefix_and_neq_implies_vstrict_prefix; [assumption | ].
      intros ->. destruct get_loan. discriminate.
    + destruct (no_outer r) as (? & ? & is_borrow).
      * eapply valid_spath_app, valid_spath_rename_mut_borrow.
        -- eassumption.
        -- apply is_loan_valid. assumption.
      * rewrite <-sget_app, get_node_rename_mut_borrow.
        -- assumption.
        -- rewrite get_borrow. constructor.
        -- intros ->%app_spath_vpath_inv_head. apply not_prefix. reflexivity.
      * eexists. split; [eassumption | ].
        rewrite <-sget_app in *. rewrite get_node_rename_mut_borrow in is_borrow.
        -- assumption.
        -- rewrite get_borrow. constructor.
        -- intros ->%app_spath_vpath_inv_head. apply not_prefix. eauto with spath.
  - autorewrite with spath in no_outer. assumption.
Qed.

Lemma eval_place_not_in_abstraction S p sp : S |-{p} p =>^{Mut} sp -> not_in_abstraction sp.
Proof.
  intros (_ & H). remember (encode_var (fst p), []) as sp0 eqn:EQN.
  assert (not_in_abstraction sp0).
  { rewrite EQN. intros ? (? & ?). discriminate. }
  clear EQN. induction H.
  - assumption.
  - apply IHeval_path. destruct Heval_proj. assumption.
Qed.

(* Note: there are "boilerplate lemmas" like [states_add_anon_eq],
 * [add_anon_commute] that we could automate the usage. *)
Lemma store_preserves_leq_rel p :
  forward_simulation leq_val_state_base'^* leq_symbolic (store p) (store p).
Proof.
  eapply preservation_by_base_case.
  intros vSr S'r Hstore (vl & Sl) (Hleq & val_no_bot & val_no_loan).
  destruct Hstore as [vr Sr sp_store a ? ? ? fresh_a].
  assert (valid_spath Sr sp_store) by eauto with spath.
  assert (not_in_abstraction sp_store) by (eapply eval_place_not_in_abstraction; eassumption).
  (* In general, we cannot store the overwritten value in the anonymous variable a in the left
   * state. Indeed, this anonymous binding can be used in the left state (rules Leq_ToAbs and
   * Leq_RemoveAnon). Thus, we are going to store it in an anonymous variable b that is fresh in
   * both the left and the right state. *)
  destruct (exists_fresh_anon2 Sl Sr) as (b & fresh_b_l & fresh_b_r).
  (* By equivalence, we can rename a into b. *)
  cut (exists S'l, leq_state_base^* S'l (Sr .[sp_store <- vr],, b |-> Sr .[sp_store]) /\
                   store p (vl, Sl) S'l).
  { intros (S'l & ? & ?). exists S'l. split; [ | assumption].
    etransitivity.
    - eexists. split; [reflexivity | eassumption].
    - eexists. split; [ | reflexivity]. eapply prove_equiv_states; [reflexivity | ].
      apply equiv_states_add_anon; eauto with spath. }
  clear a fresh_a.
  specialize (Hleq b fresh_b_l fresh_b_r). rewrite !fst_pair, !snd_pair in * |-.
  remember (Sl,, b |-> vl) eqn:EQN_l. remember (Sr,, b |-> vr) eqn:EQN_r.
  destruct Hleq; subst.

  (* Case Leq_ToSymbolic: *)
  - destruct (decide (fst sp = anon_accessor b)).
    (* Case 1: the symbolic value is introduced in the value vr we store. *)
    + autorewrite with spath in EQN_r. process_state_eq.
      autorewrite with spath in Htype, no_loan, no_borrow.
      execution_step.
      { econstructor; try eassumption.
        eapply store_compatible_types_vset_symbolic; eassumption. }
      eapply leq_step_left.
      { eapply Leq_ToSymbolic with (sp := sp_store +++ (snd sp)).
        all: autorewrite with spath; eassumption. }
      autorewrite with spath. reflexivity.
    (* Case 2: the symbolic value in introduced in the state Sr. *)
    + autorewrite with spath in * |-. process_state_eq.
      eval_place_preservation.
      execution_step.
      { eapply Store; try eassumption. not_contains_outer.
        eapply store_compatible_types_sset; try eassumption. constructor. }
      destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
      (* Case 2.a: the symbolic value is introduced in the overwritten value. *)
      * autorewrite with spath in *. eapply leq_step_left.
        { eapply Leq_ToSymbolic with (sp := (encode_anon b, r)).
          all: autorewrite with spath; eassumption. }
        autorewrite with spath. reflexivity.
      (* Case 2.b: the symbolic value is introduced in the overwritten value. *)
      * assert (disj sp_store sp) by solve_comp.
        autorewrite with spath in *. eapply leq_step_left.
        { eapply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
        states_eq.

  (* Case Leq_ToAbs: *)
  - process_state_eq.
    assert (fresh_anon (S0,, a |-> v) b) by eauto with spath.
    clear fresh_b_l fresh_b_r. eval_place_preservation. autorewrite with spath in *.
    execution_step.
    { eapply Store with (a := b); autorewrite with spath; try eassumption.
      rewrite store_compatible_types_add_abstraction in Hstore_type by eauto with spath.
      rewrite store_compatible_types_add_anon; assumption. }
    autorewrite with spath.
    rewrite add_anon_commute by congruence. eapply leq_step_left.
    { apply Leq_ToAbs with (i := i); eauto with spath. }
    autorewrite with spath. reflexivity.

  (* Case Leq_RemoveAnon: *)
  - process_state_eq.
    assert (fresh_anon (Sr,, a |-> v) b) by auto with spath.
    clear val_no_loan fresh_b_r fresh_b_l. eval_place_preservation.
    execution_step.
    { apply Store with (a := b); autorewrite with spath; try eassumption.
      rewrite store_compatible_types_add_anon; assumption. }
    autorewrite with spath.
    rewrite add_anon_commute by congruence. eapply leq_step_left.
    { apply Leq_RemoveAnon; eauto with spath. }
    reflexivity.

  (* Case Leq_MoveValue: *)
  - apply valid_spath_add_anon_cases in valid_sp.
    (* Because vr does not contain any unitialized value, the moved value cannot be in it (that
     * means it cannot be in the anonymous binding b). *)
    destruct valid_sp as [(? & valid_sp) | (? & ?)].
    2: { autorewrite with spath in EQN_r. process_state_eq.
        exfalso. eapply val_no_bot with (p := snd sp).
        (* TODO: automate. *)
        - apply vset_same_valid. assumption.
        - autorewrite with spath. reflexivity. }
    autorewrite with spath in EQN_r. process_state_eq.
    (* TODO: rename no_outer_loan0 *)
    autorewrite with spath in no_outer_loan0, sp_not_in_borrow.
    eval_place_preservation. rewrite sget_add_anon in no_outer_loan by assumption.
    execution_step.
    { eapply Store with (a := b); try eassumption. not_contains_outer.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_moved_value; eassumption. }
    destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
    + autorewrite with spath in *.
      leq_step_left.
      { eapply Leq_MoveValue with (sp := (anon_accessor b, r)) (a := a).
        autorewrite with spath. assumption.
        eauto with spath.
        eauto with spath.
        (* TODO: automate *)
        rewrite no_ancestor_anon by reflexivity. cbn.
        intros q Hq (? & ? & <-). autorewrite with spath in Hq.
        eapply sp_not_in_borrow. exact Hq.
        eexists _, _. autorewrite with spath. reflexivity.
        eauto with spath.
      }
      autorewrite with spath. rewrite add_anon_commute by congruence. reflexivity.
    + assert (disj sp_store sp) by solve_comp. autorewrite with spath in *.
      leq_step_left.
      { eapply Leq_MoveValue with (sp := sp) (a := a).
        autorewrite with spath. all: eauto with spath. }
      states_eq.

  (* Case Leq_MergeAbs: *)
  - process_state_eq. autorewrite with spath in *.
    eval_place_preservation.
    execution_step.
    { apply Store. eassumption. autorewrite with spath in *. assumption.
      rewrite !store_compatible_types_add_abstraction in *; eauto with spath.
      eassumption. }
    autorewrite with spath. rewrite <-!add_abstraction_add_anon.
    leq_step_left. { eapply Leq_MergeAbs; eauto with spath. }
    reflexivity.

  (* Case Leq_Fresh_MutLoan: *)
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & valid_sp) | (? & ?)].
    (* Because vr does not contain any loan, the moved value cannot be in it (that
     * means it cannot be in the anonymous binding b). *)
    2: { autorewrite with spath in EQN_r. process_state_eq.
        exfalso. eapply val_no_loan with (p := snd sp).
        (* TODO: automate. *)
        - apply vset_same_valid. assumption.
        - autorewrite with spath. constructor. }
    autorewrite with spath in *. process_state_eq.
    eval_place_preservation.
    rewrite sget_add_anon in no_outer_loan by assumption.
    execution_step.
    { eapply Store with (a := b); try eassumption.
      eapply not_contains_outer_sset_contains; try eassumption. constructor.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_sset; try eassumption. constructor. }
    destruct (decidable_prefix sp_store sp) as [(q & <-) | ].
    (* Case 1: the fresh mutable loan is introduced in the value we overwrite. *)
    + leq_step_left.
      { eapply Leq_Fresh_MutLoan with (a := a) (sp := (anon_accessor b, q)) (l' := l').
        not_contains. eauto with spath. validity. eauto with spath.
        autorewrite with spath. eassumption. }
      states_eq.
    (* Case 2: the fresh mutable loan is introduced in a place disjoint from the place we
     * overwrite. *)
    + leq_step_left.
      { eapply Leq_Fresh_MutLoan with (a := a) (sp := sp) (l' := l').
        not_contains. eauto with spath. validity. assumption.
        autorewrite with spath. eassumption. }
      assert (disj sp_store sp) by solve_comp. states_eq.

  (* Case Leq_Reborrow_MutBorrow: *)
  - destruct (decide (fst sp = anon_accessor b)).
    (* Case 1: the renamed borrow is in the value vl we store. *)
    + autorewrite with spath in EQN_r. process_state_eq.
      apply eval_place_add_anon in eval_p. destruct eval_p as (? & (-> & ?) & eval_p_in_Sl).
      autorewrite with spath in * |-. execution_step.
      { apply Store with (a := b); try eassumption.
        rewrite store_compatible_types_add_anon in Hstore_type by assumption.
        eapply store_compatible_types_rename_mut_borrow_val; eassumption. }
      leq_step_left.
      { eapply Leq_Reborrow_MutBorrow with (a := a) (sp := sp_store +++ snd sp) (l1 := l1).
        not_contains. auto with spath. autorewrite with spath. eassumption. assumption.
        autorewrite with spath. eassumption. }
      states_eq.
    (* Case 2: the renamed borrow is in the state Sl. *)
    + autorewrite with spath in *. process_state_eq.
      eval_place_preservation.
      rewrite sget_add_anon in no_outer_loan by assumption.
      execution_step.
      { eapply Store with (a := b); try eassumption.
        eapply not_contains_outer_loan_rename_mut_borrow; eassumption.
        rewrite store_compatible_types_add_anon in Hstore_type by assumption.
        eapply store_compatible_types_rename_mut_borrow; eassumption. }
      destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
      (* Case 2.a: the renames borrow is in the ovewritten value. *)
      * leq_step_left.
        { eapply Leq_Reborrow_MutBorrow with (sp := (anon_accessor b, r)) (a := a) (l1 := l1).
          not_contains. eauto with spath. autorewrite with spath. eassumption.
          eauto with spath. autorewrite with spath in Htype |- *. exact Htype. }
        states_eq.
      (* Case 2.b: the renames borrow is in a path disjoint from the path we overwrite. *)
      * rewrite store_compatible_types_add_anon in Hstore_type by assumption.
        (* TODO: this is a subtile piece of proof. I should make a separate lemma and
         * document it. *)
        assert (is_of_type ty (Sl.[ sp_store <- vr].[ sp +++ [0] ])).
        { destruct (decidable_prefix (sp +++ [0]) sp_store) as [(r & <-) | ].
          - autorewrite with spath.
            destruct (Hstore_type sp) as (ty' & G & ?).
            + autorewrite with spath. exists 0, r. reflexivity.
            + autorewrite with spath. constructor.
            + eapply vset_preserves_type; try eassumption.
              autorewrite with spath in G |- *. exact G.
          - assert (disj sp_store sp) by solve_comp. autorewrite with spath. assumption.
        }
        leq_step_left.
        { eapply Leq_Reborrow_MutBorrow with (sp := sp) (a := a) (l1 := l1).
          not_contains. eauto with spath. autorewrite with spath. eassumption.
          eauto with spath.
          rewrite sget_add_anon by assumption. eassumption. }
        states_eq.

  (* Case Leq_Abs_ClearValue: *)
  - autorewrite with spath in EQN_r, get_at_i_j. process_state_eq.
    eval_place_preservation. autorewrite with spath in no_outer_loan.
    execution_step.
    { eapply Store with (a := b); try eassumption.
      eapply store_compatible_types_remove_abstraction_value; eassumption. }
    leq_step_left.
    { eapply Leq_Abs_ClearValue with (i := i) (j := j).
      autorewrite with spath. all: eassumption. }
    states_eq.

  (* Case Leq_AnonValue: *)
  - process_state_eq.
    eval_place_preservation. autorewrite with spath in no_outer_loan.
    rewrite store_compatible_types_add_anon in Hstore_type by assumption.
    execution_step. { eapply Store with (a := b); eassumption. }
    leq_step_left.
    { apply Leq_AnonValue with (a := a). eauto with spath. }
    states_eq.
Qed.

Lemma is_mut_borrow_valid_spath S p (H : is_mut_borrow (get_node (S.[p]))) : valid_spath S p.
Proof. apply valid_get_node_sget_not_bot. intros G. rewrite G in H. inversion H. Qed.
Hint Resolve is_mut_borrow_valid_spath : spath.

(* TODO: move *)
Lemma _permutation_spath_app perm p q :
  (_permutation_spath perm p) +++ q = _permutation_spath perm (p +++ q).
Proof. unfold permutation_spath. cbn. autodestruct. Qed.

Lemma rename_value_preserves_type_rev r v ty :
  is_of_type ty (rename_value r v) -> is_of_type ty v.
Proof.
  remember (rename_value r v) as v' eqn:EQN.
  induction 1. all: destruct v; inversion EQN; subst; constructor.
Qed.

Lemma _store_compatible_types_permutation perm S sp v :
  is_state_equivalence perm S -> valid_spath S sp ->
  store_compatible_types (apply_state_permutation perm S)
    (permutation_spath perm sp) (rename_value (loan_id_names perm) v) ->
  store_compatible_types S sp v.
Proof.
  intros Hperm valid_sp Hcomp q Hprefix Hmut_borrow.
  remember (get_node (S.[q])) eqn:EQN. destruct Hmut_borrow as [l]. symmetry in EQN.
  specialize (Hcomp (permutation_spath perm q)).
  destruct Hcomp as (ty & type_S & type_v).
  - destruct Hprefix as (? & ? & <-). rewrite <-_permutation_spath_app.
    eexists _, _. reflexivity.
  - autorewrite with spath. rewrite EQN. constructor.
  - exists ty. split.
    + autorewrite with spath in type_S.
      now apply rename_value_preserves_type_rev in type_S.
    +  apply rename_value_preserves_type_rev in type_v. assumption.
Qed.

Lemma store_compatible_types_rename_value S p v r :
  store_compatible_types S p v -> store_compatible_types S p (rename_value r v).
Proof.
  intros Hcomp q Hprefix get_mut_borrow. specialize (Hcomp q Hprefix get_mut_borrow).
  destruct Hcomp as (ty & ? & ?). exists ty. split; [assumption | ].
  apply rename_value_preserves_type. assumption.
Qed.

Lemma store_compatible_types_permutation perm S sp v :
  is_state_equivalence perm S -> valid_spath S sp ->
  store_compatible_types S sp v ->
  store_compatible_types (apply_state_permutation perm S)
    (permutation_spath perm sp) (rename_value (loan_id_names perm) v).
Proof.
  intros valid_perm valid_sp H. destruct (valid_perm) as (valid_accessor_perm & _).
  eapply _store_compatible_types_permutation with (perm := invert_state_permutation perm).
  - apply invert_state_permutation_is_permutation. assumption.
  - apply permutation_valid_spath; assumption.
  - rewrite apply_invert_state_permutation by assumption.
    cbn. erewrite invert_state_permutation_spath by eassumption.
    repeat apply store_compatible_types_rename_value. assumption.
Qed.

Lemma store_preserves_equiv p :
  forward_simulation equiv_val_state equiv_states (store p) (store p).
Proof.
  intros (v0 & S0) S1 Heval (? & S'0) Hequiv.
  symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ? & -> & ->).
  inversion Heval; subst.
  assert (valid_spath S0 sp) by eauto with spath.
  destruct (exists_fresh_anon (apply_state_permutation perm S0)) as (b & fresh_b).
  eapply eval_place_permutation in eval_p; [ | eassumption].
  execution_step.
  { econstructor. eassumption. autorewrite with spath.
    apply not_contains_outer_loan_rename_value. assumption.
    apply store_compatible_types_permutation; assumption. eassumption. }
  symmetry. eexists. split.
  - apply add_anon_perm_equivalence with (b := b); eauto with spath.
    + etransitivity; [apply loan_set_sget | apply Hperm].
    + autorewrite with spath. assumption.
  - autorewrite with spath.
    + auto.
    + etransitivity; [apply loan_set_sget | apply Hperm].
    + autorewrite with spath. assumption.
Qed.

Lemma store_preserves_LLBC_plus_rel p vr Sr S'r vl Sl :
  not_contains_loan vr -> not_contains_bot vr ->
  store p (vr, Sr) S'r -> leq_val_state (vl, Sl) (vr, Sr) ->
  exists S'l, store p (vl, Sl) S'l /\ leq_symbolic S'l S'r.
Proof.
  intros no_loan no_bot Hstore ((vm & Sm) & Hequiv & Hleq).
  edestruct store_preserves_leq_rel as (S'm & (? & Hequiv' & Hleq') & Hstore').
  { exact Hstore. }
  { eapply leq_val_state_no_bot_loan_right; eassumption. }
  eapply store_preserves_equiv in Hstore'. specialize (Hstore' _ Hequiv).
  destruct Hstore' as (S'l & ? & ?).
  exists S'l. split.
  - assumption.
  - eexists. split; [ | eassumption]. etransitivity; eassumption.
Qed.

(** ** Simulation proofs for reorganizations. *)
Lemma size_abstractions_sset S p v : size (abstractions (S.[p <- v])) = size (abstractions S).
Proof.
  unfold sset, alter_at_accessor. cbn. repeat autodestruct. cbn.
  rewrite<- !size_dom, dom_alter_L. reflexivity.
Qed.

Lemma size_abstraction_add_anon S a v :
  size (abstractions (S,, a |-> v)) = size (abstractions S).
Proof. reflexivity. Qed.

Lemma size_abstraction_add_abstraction S i A (H : fresh_abstraction S i) :
  size (abstractions (S,,, i |-> A)) = 1 + size (abstractions S).
Proof. cbn. rewrite map_size_insert, H. reflexivity. Qed.

Lemma size_abstraction_remove_abstraction_value S i j :
  size (abstractions (remove_abstraction_value S i j)) = size (abstractions S).
Proof.
  unfold abstractions, remove_abstraction_value. destruct S. cbn.
  destruct (lookup i abstractions0) eqn:H.
  - apply insert_delete in H. rewrite <-H. rewrite alter_insert.
    rewrite !map_size_insert. reflexivity.
  - pose proof (delete_notin _ _ H) as <-. rewrite map_alter_not_in_domain; now simpl_map.
Qed.

Hint Rewrite size_abstractions_sset : weight.
Hint Rewrite size_abstraction_add_anon : weight.
Hint Rewrite size_abstraction_add_abstraction using auto with spath; fail : weight.
Hint Rewrite size_abstraction_remove_abstraction_value : weight.

Lemma leq_state_base_n_decreases n Sl Sr (H : leq_state_base_n n Sl Sr) :
  measure Sl < measure Sr + n.
Proof.
  unfold measure. destruct H.
  - weight_inequality.
  - autorewrite with weight. destruct Hto_abs.
    + autorewrite with weight; [lia | simpl_map; reflexivity].
    + weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - autorewrite with weight. erewrite sweight_remove_abstraction_value by eassumption.
    autorewrite with weight. lia.
  - weight_inequality.
Qed.

Lemma measure_add_anons S A S' :
  add_anons S A S' -> measure S' = measure S + abs_measure A.
Proof.
  rewrite add_anons_alt. induction 1.
  - rewrite Nat.add_comm. reflexivity.
  - rewrite IHadd_anons'. unfold measure. autorewrite with weight. lia.
Qed.

Lemma reorg_decreases S S' (H : reorg S S') : measure S' < measure S.
Proof.
  destruct H.
  - unfold measure. weight_inequality.
  - unfold measure. autorewrite with weight spath.
    erewrite sweight_remove_abstraction_value by eassumption.
    weight_given_node. autorewrite with weight. lia.
  - apply measure_add_anons in Hadd_anons. rewrite Hadd_anons.
    unfold measure. autorewrite with weight. lia.
Qed.

Lemma leq_n_step m n Sl Sm Sr :
  leq_state_base_n m Sl Sm -> m <= n -> leq_n (n - m) Sm Sr -> leq_n n Sl Sr.
Proof.
  intros H ? (Sr' & G & ?). replace n with (m + (n - m)) by lia.
  destruct (leq_n_equiv_states_commute _ _ _ G _ H) as (Sl' & ? & ?).
  exists Sl'. split.
  - assumption.
  - eapply MC_trans.
    + constructor. eassumption.
    + assumption.
Qed.

Lemma prove_leq_n n Sl Sr Sr' :
  leq_state_base_n^{n} Sl Sr -> equiv_states Sr Sr' -> leq_n n Sl Sr'.
Proof.
  intros H G.
  pose proof leq_n_equiv_states_commute as Hsim.
  eapply sim_equiv_leq_n in Hsim. specialize (Hsim _ _ G _ H).
  destruct Hsim as (Sl' & ? & ?). exists Sl'. split; assumption.
Qed.

Lemma leq_n_by_equivalence n S S' : equiv_states_up_to_accessor_permutation S S' -> leq_n n S S'.
Proof.
  intros ?. exists S'. split; [ | reflexivity].
  eapply prove_equiv_states; [reflexivity | eassumption].
Qed.

(** Lemmas used to prove the local commutation between leq_state_base and reorg: *)
Lemma vget_borrow l v p c : get_node (borrow^m(l, v).[[p]]) = c -> c <> botC ->
  p = [] /\ borrowC^m(l) = c \/ exists q, p = [0] ++ q /\ get_node (v.[[q]]) = c.
Proof.
  intros H G. destruct p as [ | [ | ] q].
  - left. auto.
  - right. exists q. auto.
  - exfalso. eapply G. rewrite <-H, vget_cons. cbn. rewrite nth_error_nil.
    replace botC with (get_node bot) by reflexivity. f_equal. exact (vget_bot q).
Qed.

(* This variant is used for the commutation of the rule Leq_Reborrow_MutBorrow_n with the ending of
 * a borrow. *)
Lemma vget_borrow_loan l0 l1 p c ty :
  get_node (borrow^m(l0, loan^m(ty, l1)).[[p]]) = c -> c <> botC ->
  p = [] /\ borrowC^m(l0) = c \/ p = [0] /\ loanC^m(ty, l1) = c.
Proof.
  intros H G. apply vget_borrow in H; [ | assumption]. destruct H as [ | (q & -> & H)].
  - left. assumption.
  - right. destruct q.
    + auto.
    + exfalso. apply G. rewrite <-H. cbn. rewrite nth_error_nil.
      replace botC with (get_node bot) by reflexivity. f_equal. exact (vget_bot q).
Qed.

(* This lemma is used once, when studying reorganizations and the rule Leq_Fresh_MutLoan. *)
Lemma fresh_mut_loan_get_loan S l sp a p ty ty' (fresh_l : is_fresh l S) :
  get_node ((S.[sp <- loan^m(ty, l)],, a |-> borrow^m(l, S.[sp])).[p]) = loanC^m(ty', l) ->
  p = sp.
Proof.
  intros get_loan. destruct (decide (fst p = anon_accessor a)) as [H | ].
  - autorewrite with spath in get_loan. apply vget_borrow in get_loan; [ | discriminate].
    destruct get_loan as [(_ & ?) | (q & ? & get_loan)].
    + discriminate.
    + autorewrite with spath in get_loan. exfalso.
      eapply fresh_l; [ | rewrite get_loan]; auto with spath.
  - autorewrite with spath in get_loan.
    destruct (decidable_spath_eq p sp).
    + assumption.
    + exfalso. assert (~strict_prefix sp p) by eauto with spath.
      autorewrite with spath in get_loan. eapply fresh_l; [ | rewrite get_loan].
      * validity.
      * reflexivity.
Qed.

Lemma get_borrow_rename_mut_borrow S p l l0 q :
  get_node ((rename_mut_borrow S p l).[q]) = borrowC^m(l) -> is_fresh l S ->
  get_node (S.[p]) = borrowC^m(l0) -> p = q.
Proof.
  intros get_borrow fresh_l ?. destruct (decidable_spath_eq p q); [assumption | ].
  exfalso. autorewrite with spath in get_borrow.
  eapply fresh_l; [ | rewrite get_borrow; reflexivity]. validity.
Qed.

Inductive add_anonymous_bots : nat -> LLBC_plus_state -> LLBC_plus_state -> Prop :=
  | Add_no_bots S : add_anonymous_bots 0 S S
  | Add_anonymous_bot n S a S' :
      add_anonymous_bots n S S' -> fresh_anon S' a ->
      add_anonymous_bots (1 + n) S (S',, a |-> bot).

Lemma add_anonymous_bots_fresh_abstraction n S S' i :
  add_anonymous_bots n S S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof. induction 1; eauto with spath. Qed.
Hint Resolve add_anonymous_bots_fresh_abstraction : spath.

Lemma abs_measure_remove_loans A B A' B' :
  remove_loans A B A' B' -> abs_measure A' <= abs_measure A /\ abs_measure B' <= abs_measure B.
Proof.
  induction 1.
  - auto.
  - repeat lazymatch goal with
    | H : lookup ?i ?A = Some ?v |- _ =>
        apply (map_sum_delete (vweight (fun _ => 1))) in H
    end.
    lia.
Qed.

(* The crucial lemma for the commutation between leq and reorganizations, when we end a region C that
 * is the merge of two regions A and B. By definition, C is the union of A' and B' where we removed
 * common loans and borrows.
 * After ending the region B and placing its borrows in anonymous bindings, we must end all the
 * borrows that are in B \ B', and the corresponding loans in A \ A'.
 * TODO: explain the add_anonymous_bots operation. *)
Lemma end_removed_loans S0 S0_anons i A B A' B'
  (H : remove_loans A B A' B') (fresh_i : fresh_abstraction S0 i) :
  add_anons (S0,,, i |-> A) B S0_anons ->
  exists n S1,
    add_anonymous_bots n S0 S1 /\
    2 * n <= abs_measure A + abs_measure B - abs_measure A' - abs_measure B' /\
    exists S1_anons, reorg^* S0_anons S1_anons /\
                     add_anons (S1,,, i |-> A') B' S1_anons.
Proof.
  intros Hadd_anons. induction H as [ | A' B' j ? l ty Hremove_loans IH HA' HB'].
  - eexists 0, _. repeat split.
    + constructor.
    + apply le_0_n.
    + exists S0_anons; easy.
  - clear Hadd_anons.
    destruct IH as (n & S1 & ? & ? & S1_anons & ? & Hadd_anons).
    rewrite <-(insert_delete _ _ _ HB') in Hadd_anons.
    eapply add_anons_delete in Hadd_anons; [ | simpl_map; reflexivity].
    destruct Hadd_anons as (a & fresh_a%fresh_anon_add_abstraction & Hadd_anons).
    eexists (1 + n), _.
    split.
    { econstructor; eassumption. }
    split.
    { apply (map_sum_delete (vweight (fun _ => 1))) in HA', HB'.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      apply abs_measure_remove_loans in Hremove_loans. lia. }
    eexists. split.
    { transitivity S1_anons; [assumption | ].
      constructor. apply Reorg_end_borrow_m_in_abstraction
        with (l := l) (q := (anon_accessor a, [])) (i' := i) (j' := j) (ty := ty).
        - eapply add_anons_abstraction_element; [eassumption | ].
          autorewrite with spath. assumption.
        - erewrite add_anons_sget by eauto with spath.
          autorewrite with spath. reflexivity.
        - erewrite add_anons_sget. 2: eassumption.
          (* TODO: automate *)
          2: { apply valid_spath_anon. econstructor. reflexivity. constructor. }
          autorewrite with spath. constructor.
        - erewrite add_anons_sget; [ | eassumption | ].
          + autorewrite with spath. not_contains.
          + apply valid_spath_anon. econstructor; [reflexivity | constructor].
        - intros ? ?. eauto with spath.
        - eapply anon_not_in_abstraction. reflexivity. }
    eapply prove_add_anons. eexists. split.
    { apply add_anons_sset. apply add_anons_remove_abstraction_value. eassumption.
      eauto with spath. }
    { autorewrite with spath. reflexivity. }
Qed.

Lemma commute_add_anonymous_bots_anons S0 S1 S2 n A :
  add_anonymous_bots n S0 S1 -> add_anons S1 A S2 ->
  exists S'1, add_anons S0 A S'1 /\ add_anonymous_bots n S'1 S2.
Proof.
  setoid_rewrite add_anons_alt. intros H. revert S2. induction H.
  - eexists. split; [eassumption | constructor].
  - intros S2 G.
    apply add_anon_add_anons' in G; [ | assumption]. destruct G as (? & -> & ? & ?).
    edestruct IHadd_anonymous_bots as (S'1 & ? & ?); [eassumption | ].
    exists S'1. split; [assumption | ]. constructor; assumption.
Qed.

Lemma leq_n_add_anonymous_bots S S' n :
  add_anonymous_bots n S S' -> forall m, 2 * n <= m -> leq_state_base_n^{m} S' S.
Proof.
  induction 1 as [ | ? ? ? S'].
  - reflexivity.
  - intros m ?. replace m with (2 + (m - 2)) by lia. eapply MC_trans.
    + constructor.
      replace 2 with (1 + vweight (fun _ => 1) bot) by reflexivity.
      apply Leq_RemoveAnon_n; autorewrite with spath.
      assumption. unfold not_contains_loan. not_contains. unfold not_contains_borrow. not_contains.
    + apply IHadd_anonymous_bots. lia.
Qed.

Lemma add_anons_abstraction_set S B j v w q S' :
  add_anons S (abstraction_set j q v B) S' ->
  lookup j B = Some w -> valid_vpath w q ->
  exists S'' a,
    add_anons S B S'' /\ S' = S''.[(anon_accessor a, q) <- v] /\
    S''.[(anon_accessor a, q)] = w.[[q]].
Proof.
  unfold abstraction_set. intros Hadd_anons get_w ?.
  erewrite alter_insert_delete in Hadd_anons by exact get_w.
  apply add_anons_delete in Hadd_anons; [ | now simpl_map].
  destruct Hadd_anons as (a & fresh_a & Hadd_anons).
  assert (valid_vpath (w .[[ q <- v]]) q) by now apply vset_same_valid.
  assert (valid_spath S' (anon_accessor a, q)).
  { eapply add_anons_valid_spath; [ | eassumption]. validity. }
  pose proof Hadd_anons as get_S'_v.
  eapply add_anons_sget with (p := (anon_accessor a, q)) in get_S'_v; [ | validity].
  autorewrite with spath in get_S'_v.
  eapply add_anons_sset with (p := (anon_accessor a, q)) in Hadd_anons; [ | validity].
  rewrite sset_anon in Hadd_anons by reflexivity.
  rewrite vset_twice_equal, vset_same in Hadd_anons.
  rewrite add_anons_alt in Hadd_anons.
  eapply AddAnons_insert in Hadd_anons; [ | now simpl_map | assumption].
  rewrite insert_delete, <-add_anons_alt in Hadd_anons by assumption.
  eexists _, a. split; [exact Hadd_anons | ].
  rewrite sset_sget_equal by assumption. autorewrite with spath. rewrite <-get_S'_v.
  autorewrite with spath. auto.
Qed.

Lemma reorg_local_preservation n :
  forward_simulation (leq_state_base_n n) (leq_n n) reorg reorg^*.
Proof.
  intros ? ? Hreorg. destruct Hreorg.
  (* Case Reorg_end_borrow_m: *)
  - intros ? Hleq. destruct Hleq.
    (* Case Leq_ToSymbolic_n: *)
    + assert (disj sp p). solve_comp.
      autorewrite with spath in *. (* TODO: takes a bit of time. *)
      reorg_step.
      (* TODO: automate *)
      { eapply Reorg_end_borrow_m with (p := p) (q := q); try eassumption.
        (* TODO: hint. *)
        eapply is_of_type_sset_rev; eauto with spath. constructor.
        eapply get_zeroary_not_strict_prefix'; eauto with spath.
        not_contains. }
      destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
      * autorewrite with spath in *.
        reorg_done.
        eapply leq_n_step.
        { eapply Leq_ToSymbolic_n with (sp := p +++ r); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.
      * assert (disj sp q) by solve_comp.
        reorg_done.
        eapply leq_n_step.
        { eapply Leq_ToSymbolic_n with (sp := sp); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.
    (* Case Leq_ToAbs_n: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_end_borrow_m with (p := p) (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath. eapply leq_n_step.
      { eapply Leq_ToAbs_n; eauto with spath. }
      { reflexivity. }
      reflexivity.
    (* Case Leq_RemoveAnon_n: *)
    + reorg_step.
      { eapply Reorg_end_borrow_m with (p := p) (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath. eapply leq_n_step.
      { eapply Leq_RemoveAnon_n; eauto with spath. }
      { reflexivity. }
      reflexivity.
    (* Case Leq_MoveValue_n: *)
    + destruct (decide (fst p = anon_accessor a)).
      * destruct (decide (fst q = anon_accessor a)).
        (* Case 1: the borrow and the loan are in the value we move. *)
        -- destruct Hdisj as [ | (_ & Hdisj)]; [congruence | ].
           autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_end_borrow_m; try eassumption. eauto with spath.
             all: autorewrite with spath; try assumption. not_contains. solve_comp. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_MoveValue_n with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           { reflexivity. }
           autorewrite with spath. reflexivity.
        (* Case 2: the loan is in the value we move, not the borrow. *)
        -- rewrite sget_add_anon in * by assumption.
           assert (~prefix sp q) by solve_comp.
           autorewrite with spath in get_borrow.
           (* TODO: automate *)
           assert (~strict_prefix q sp).
           { apply sp_not_in_borrow. rewrite get_borrow. constructor. }
           assert (disj sp q). solve_comp. autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_end_borrow_m; try eassumption. solve_comp. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_MoveValue_n with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           { reflexivity. }
           states_eq.
      * rewrite sget_add_anon in get_loan by assumption.
        assert (disj sp p). solve_comp.
        destruct (decide (fst q = anon_accessor a)).
        (* Case 3: the borrow is in the value we move, not the loan. *)
        -- autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_end_borrow_m; try eassumption.
             all: autorewrite with spath; eauto with spath. solve_comp. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_MoveValue_n with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           { reflexivity. }
           states_eq.
        (* Case 4: neither the borrow nor the loan is in the value we move. *)
        -- rewrite sget_add_anon in * by eassumption.
           assert (~prefix sp q) by solve_comp. autorewrite with spath in get_borrow.
           (* TODO: automate *)
           assert (~strict_prefix q sp).
           { apply sp_not_in_borrow. rewrite get_borrow. constructor. }
           assert (disj sp q) by solve_comp. autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_end_borrow_m with (p := p) (q := q); eassumption. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_MoveValue_n with (sp := sp) (a := a).
             all: autorewrite with spath; try assumption. validity. }
           { reflexivity. }
           states_eq.
    (* Case Leq_MergeAbs_n: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_end_borrow_m with (p := p) (q := q); autorewrite with spath; eassumption. }
      reorg_done. autorewrite with spath. eapply leq_n_step.
      { eapply Leq_MergeAbs_n; eauto with spath. }
      { reflexivity. }
      reflexivity.
    (* Case Leq_Fresh_MutLoan_n: *)
    + destruct (decidable_spath_eq q (anon_accessor a, [])) as [-> | ].
      (* Case 1: the borrow we end is the newly introduced borrow of identifier l'. *)
      * (* We prove that l' = l. *)
        autorewrite with spath in get_borrow. inversion get_borrow. subst.
        (* The loan we end is the newly introduced loan. *)
        apply fresh_mut_loan_get_loan in get_loan; [ | exact fresh_l']. subst.
        (* TODO: long. *) autorewrite with spath in *.
        (* The left state is just S,, a |-> bot. It does not contain the borrow of
         * loan id l. Thus, we don't have to do any reorganization step. *)
        reorg_done.
        (* We just have to do one step: adding an anonymous binding a |-> bot. *)
        eapply leq_n_step.
        { apply Leq_AnonValue_n with (a := a). assumption. }
        { reflexivity. }
        reflexivity.
      * assert (fst q <> anon_accessor a).
        { eapply not_in_borrow_add_borrow_anon; eassumption. }
        rewrite sget_add_anon in * by assumption.
        assert (disj sp q) by solve_comp.
        autorewrite with spath in *.
        destruct (decide (fst p = anon_accessor a)).
        (* Case 2: the loan we end is in the anonymous binding a, containing the value of
         * the newly introduced loan. *)
        -- autorewrite with spath in get_loan.
           apply vget_borrow in get_loan; [ | discriminate].
           destruct get_loan as [(_ & [=]) | (r & G & get_loan)].
           autorewrite with spath in *. rewrite G.
           reorg_step.
           { eapply Reorg_end_borrow_m; try eassumption. solve_comp. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_Fresh_MutLoan_n with (sp := sp) (l' := l') (a := a).
             not_contains. eauto with spath. validity. eauto with spath.
             (* TODO: automate. *)
             autorewrite with spath. eapply vset_preserves_type; autorewrite with spath; eauto.
             (* TODO: for zeroary values, we should more easily derive their value
              * when we know their nodes. *)
             destruct (S.[sp +++ r]); inversion get_loan. constructor. }
           { reflexivity. }
           states_eq.
        (* Case 3: the loan we end is disjoint from the anonymous binding a, containing the
           value of the newly introduced loan. *)
        -- autorewrite with spath in *.
           assert (disj sp p). solve_comp.
           (* TODO: automate *)
           { intros ->. autorewrite with spath in get_loan. inversion get_loan. subst.
             eapply fresh_l'; [ | rewrite get_borrow]; auto with spath. }
           autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_end_borrow_m; eassumption. }
           reorg_done. eapply leq_n_step.
           { eapply Leq_Fresh_MutLoan_n with (sp := sp) (l' := l') (a := a).
             not_contains. eauto with spath. validity. assumption.
             autorewrite with spath. eassumption. }
           { reflexivity. }
           states_eq.
    (* Case Leq_Reborrow_MutBorrow_n: *)
    + (* The pointer we end cannot be in the anonymous binding a, because it contains a loan. *)
      assert (fst q <> anon_accessor a).
      { intros ?. autorewrite with spath in get_borrow, Hno_loan.
        apply vget_borrow_loan in get_borrow; [ | discriminate].
        destruct get_borrow as [(Hsnd_q & [=->]) | (_ & [=])].
        eapply Hno_loan with (p := []); rewrite Hsnd_q; constructor. }
      rewrite sget_add_anon in * by assumption.
      destruct (decide (fst p = anon_accessor a)).
      (* Case 1: the borrow we end is the renamed borrow. *)
      * autorewrite with spath in get_loan. autorewrite with spath.
        apply vget_borrow_loan in get_loan; [ | discriminate].
        destruct get_loan as [(_ & [=]) | (-> & [=-> ->])].
        eapply (get_borrow_rename_mut_borrow S) in get_borrow; [ | eassumption..]. subst.
        reorg_done. (* We don't have any reorganization step to perform. *)
        autorewrite with spath in *. assert (not_contains_loan (S.[q])) as Hno_loan'.
        { rewrite sget_app in Hno_loan. destruct (S.[q]); inversion get_borrow_l0.
          eapply not_value_contains_unary; eauto with spath. }
        eapply leq_n_step.
        { apply Leq_MoveValue_n with (sp := q) (a := a). not_contains_outer.
          assumption. validity. assumption. assumption. }
        { reflexivity. }
        rewrite sget_app. destruct (S.[q]); inversion get_borrow_l0. reflexivity.
      (* Case 2: the borrow we end is different to the renamed borrow. *)
      * assert (sp <> p).
        { intros <-. rewrite sget_add_anon in get_loan by assumption.
          rewrite sset_sget_equal in get_loan by validity. discriminate. }
        autorewrite with spath in get_loan, Hnot_in_borrow.
        assert (l1 <> l).
        { intros ->. eapply fresh_l1; [ | rewrite get_loan; reflexivity]. validity. }
        assert (~prefix sp q). eapply prove_not_prefix.
        (* TODO: automate *)
        { eapply sset_sget_diff; [eassumption | cbn; congruence | discriminate]. }
        { eapply Hnot_in_borrow. autorewrite with spath. constructor. }
        autorewrite with spath in *.
        reorg_step.
        { apply Reorg_end_borrow_m with (p := p) (q := q) (l := l) (ty := ty); try assumption.
          (* TODO: automate. *)
          eapply is_of_type_rename_mut_borrow; eassumption.
          eapply not_contains_rename_mut_borrow; try eassumption. inversion 1. }
        reorg_done.
        destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
        (* Case 2a: the renamed borrow is in the ended borrow. *)
        -- autorewrite with spath in get_borrow_l0. eapply leq_n_step.
           { apply Leq_Reborrow_MutBorrow_n with (l1 := l1) (a := a) (sp := p +++ r).
             not_contains. eauto with spath. autorewrite with spath. eassumption. assumption.
             autorewrite with spath in Htype |- *. exact Htype. }
           { reflexivity. }
           states_eq.
           (* Case 2b: the renamed borrow is disjoint from the from the ended borrow. *)
        -- assert (disj sp q) by solve_comp. autorewrite with spath. eapply leq_n_step.
           { apply Leq_Reborrow_MutBorrow_n with (l1 := l1) (a := a) (sp := sp).
             not_contains. eauto with spath. autorewrite with spath. eassumption. assumption.
             (* TODO: automate. *)
             autorewrite with spath.
             eapply is_of_type_sset_sget; [eassumption | ..].
             eapply is_of_type_rename_mut_borrow; eassumption.
             destruct (S.[p]); inversion get_loan; constructor. }
           { reflexivity. }
           states_eq.
    (* Case Leq_Abs_ClearValue_n: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_end_borrow_m with (p := p) (q := q); eassumption. }
      reorg_done. eapply leq_n_step.
      { eapply Leq_Abs_ClearValue_n with (i := i) (j := j). autorewrite with spath.
        all: eassumption. }
      { reflexivity. }
      autorewrite with spath. reflexivity.
    (* Case Leq_AnonValue_n: *)
    + (* TODO: automate? *)
      assert (fst q <> anon_accessor a).
      { intros ?. autorewrite with spath in get_borrow. rewrite vget_bot in get_borrow. discriminate. }
      assert (fst p <> anon_accessor a).
      { intros ?. autorewrite with spath in get_loan. rewrite vget_bot in get_loan. discriminate. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_end_borrow_m with (p := p) (q := q); eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_AnonValue_n with (a := a). eauto with spath. }
      { reflexivity. }
      reflexivity.

  (* Case Reorg_end_borrow_m_in_abstraction: *)
  - intros ? Hleq. destruct Hleq.
    (* Case Leq_ToSymbolic_n: *)
    + (* TODO: lemma *)
      assert (fst sp <> encode_abstraction (i', j')).
      { apply abstraction_element_is_sget in get_loan. intros ?.
        assert (prefix (encode_abstraction (i', j'), []) sp) as G%prefix_if_equal_or_strict_prefix.
        { exists (snd sp). rewrite <-H. destruct sp. reflexivity. }
        destruct G as [<- | G].
        - autorewrite with spath in get_loan. discriminate.
        - eapply get_zeroary_not_strict_prefix; [ | | exact G].
          + rewrite get_loan. reflexivity.
          + validity.
      }
      autorewrite with spath in *.
        reorg_step.
        { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
          all: try eassumption.
          (* TODO: automate. *)
          eapply is_of_type_sset_rev; eauto. constructor. solve_comp. not_contains. }
        reorg_done.
      destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
      * autorewrite with spath in *. reflexivity.
      * assert (disj sp q) by solve_comp.
        eapply leq_n_step.
        { eapply Leq_ToSymbolic_n with (sp := sp); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        states_eq.
    (* Case Leq_ToAbs_n: *)
    + autorewrite with spath in * |-.
      destruct (decide (i' = i)) as [<- | ].
      * autorewrite with spath in get_loan. destruct Hto_abs.
        --  assert (j' = kl /\ l = l1) as (-> & <-).
           { apply lookup_insert_Some in get_loan.
             destruct get_loan as [ | (_ & get_loan)]; [easy | ].
             rewrite lookup_singleton_Some in get_loan.
             destruct get_loan as (<- & get_loan). inversion get_loan. auto. }
           simpl_map. inversion get_loan. subst.
           reorg_step.
           { eapply Reorg_end_borrow_m with (p := (anon_accessor a, []) +++ [0]) (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath.
           eapply leq_n_step.
           { apply Leq_ToAbs_n with (i := i') (a := a). eauto with spath. eauto with spath.
             constructor; [eassumption.. | ].
             (* For the moment, typed values do not contain borrows. *)
             inversion type_borrow; not_contains. }
           { (* typed values are unary for the moment. When we deal with more general types values, a commutation lemma will be necessary. *)
             inversion type_borrow; cbn; lia. }
           apply reflexive_eq.
           rewrite delete_insert_ne, delete_singleton by congruence. reflexivity.
        (* The abstraction H does not contain loans, we can eliminate this case. *)
        -- apply lookup_singleton_Some in get_loan. destruct get_loan. discriminate.
      * autorewrite with spath in * |-. reorg_step.
        { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done.
      autorewrite with spath. eapply leq_n_step.
      { apply Leq_ToAbs_n; eauto with spath. }
      { reflexivity. }
      reflexivity.
    (* Case Leq_RemoveAnon_n: *)
    + reorg_step.
      { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath.
      eapply leq_n_step.
      { apply Leq_RemoveAnon_n; auto with spath. }
      { reflexivity. }
      reflexivity.
    (* Case Leq_MoveValue_n: *)
    + destruct (decide (fst q = anon_accessor a)).
      (* Case 1: the borrow we end is in the anonymous binding a that contains the moved
       * value. *)
      * autorewrite with spath in *. reorg_step.
        { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := sp +++ snd q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done. eapply leq_n_step.
        { apply Leq_MoveValue_n with (sp := sp) (a := a).
          all: autorewrite with spath; eauto with spath. not_contains_outer. }
        { reflexivity. }
        autorewrite with spath. reflexivity.
      * assert (~prefix sp q).
        { intros (? & <-). autorewrite with spath in get_borrow.
          rewrite vget_bot in get_borrow. inversion get_borrow. }
        (* TODO: lemma. *)
        assert (~prefix (q +++ [0]) sp).
        { intros (r & <-).
          pose proof valid_sp.
          rewrite valid_spath_app in valid_sp. destruct valid_sp as (? & ?).
          autorewrite with spath in type_borrow. eapply is_of_type_does_not_contain_bot.
          - exact type_borrow.
          - apply vset_same_valid. assumption.
          - autorewrite with spath. reflexivity. }
        assert (disj sp q) by solve_comp. autorewrite with spath in * |-.
        reorg_step.
        { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
          all: eauto with spath. }
        reorg_done. eapply leq_n_step.
        { apply Leq_MoveValue_n with (sp := sp) (a := a).
          all: autorewrite with spath; eauto with spath. }
        { reflexivity. }
        states_eq.
    (* Case Leq_MergeAbs_n: *)
    + destruct (decide (i = i')) as [<- | ].
      * autorewrite with spath in *.
        eapply merge_abstractions_contains in Hmerge; [ | eassumption].
        destruct Hmerge as [(G & Hmerge) | (k & G & Hmerge)].
        -- reorg_step.
           { eapply Reorg_end_borrow_m_in_abstraction with (i' := i) (j' := j') (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath. eapply leq_n_step.
           { apply Leq_MergeAbs_n; eauto with spath. }
           { eapply map_sum_delete in get_loan, G. rewrite get_loan, G. lia. }
           reflexivity.
        -- reorg_step.
           { eapply Reorg_end_borrow_m_in_abstraction with (i' := j) (j' := k) (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath. eapply leq_n_step.
           { apply Leq_MergeAbs_n; eauto with spath. }
           { eapply map_sum_delete in get_loan, G. rewrite get_loan, G. lia. }
           reflexivity.
      * autorewrite with spath in * |-.
        assert (i' <> j).
        { intros <-. autorewrite with spath in get_loan. discriminate. }
        reorg_step.
        { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done. autorewrite with spath.
        autorewrite with spath. eapply leq_n_step.
        { apply Leq_MergeAbs_n; eauto with spath. }
        { reflexivity. }
        reflexivity.
    (* Case Leq_Fresh_MutLoan_n: *)
    + assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ].
        intros ->. autorewrite with spath in get_borrow, get_borrow. inversion get_borrow; subst.
        autorewrite with spath in get_loan. apply abstraction_element_is_sget in get_loan.
        eapply fresh_l'; [ | rewrite get_loan; constructor]. validity. }
      rewrite sget_add_anon in * by assumption.
      assert (disj sp q). apply prove_disj.
      (* The node q contains a borrow, it cannot be in sp that contains a loan. *)
      { eauto with spath. }
      { eauto with spath. }
      (* The node q +++ [0] is an integer, it cannot contain a loan. *)
      { solve_comp. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
        all: eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_Fresh_MutLoan_n with (l' := l') (a := a) (sp := sp); eauto with spath.
        not_contains. autorewrite with spath. eassumption. }
      { reflexivity. }
      states_eq.
    (* Case Leq_Reborrow_MutBorrow_n: *)
    + assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ].
        intros ->. autorewrite with spath in Hno_loan.
        eapply loan_contains_loan, Hno_loan. }
      rewrite sget_add_anon in * by assumption. autorewrite with spath in get_loan.
      assert (disj q sp). apply prove_disj.
      (* The node q contains a borrow of loan identifier l <> l1 (freshness of l1). *)
      { intros <-. autorewrite with spath in get_borrow. inversion get_borrow; subst.
        apply abstraction_element_is_sget in get_loan.
        eapply fresh_l1; [ | rewrite get_loan; constructor]. validity. }
      (* If sp is in q, there is a nested borrow (sp in q), and we currently do not handle
       * nested borrows. *)
      (* Eventually, we are going to lift this restriction. There will be two cases to
       * consider, one of them being that q is a strict prefix of sp. *)
      { eapply not_prefix_one_child.
        - rewrite length_children_is_arity, get_borrow. reflexivity.
        - validity.
        - assert (valid_spath S sp) as valid_sp by validity.
          intros (r & <-). apply valid_spath_app in valid_sp. destruct valid_sp.
          autorewrite with spath in type_borrow.
          eapply is_of_type_does_not_contain_borrow.
          + exact type_borrow.
          + apply vset_same_valid. assumption.
          + autorewrite with spath. constructor. }
      (* q is not in a borrow. *)
      { intros (? & ? & <-). eapply Hnot_in_borrow with (q := sp).
        - autorewrite with spath. constructor.
        - eexists _, _; reflexivity. }
      assert (sp <> q +++ [0]). { intros ->. eapply not_prefix_disj; eauto with spath. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
        all: eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_Reborrow_MutBorrow_n with (l0 := l0) (l1 := l1) (a := a) (sp := sp).
        not_contains. eauto with spath. all: autorewrite with spath; eassumption. }
      { reflexivity. }
      states_eq.
    (* Case Leq_Abs_ClearValue_n: *)
    + autorewrite with spath in * |-. destruct get_loan.
      reorg_step.
      { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
        all: eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_Abs_ClearValue_n with (i := i) (j := j) (v := v).
        autorewrite with spath. all: assumption. }
      { reflexivity. }
      autorewrite with spath. rewrite remove_abstraction_value_commute. reflexivity.
    (* Case Leq_AnonValue_n: *)
    + assert (fst q <> anon_accessor a).
      { intros ?. autorewrite with spath in get_borrow. rewrite vget_bot in get_borrow. discriminate. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_end_borrow_m_in_abstraction with (i' := i') (j' := j') (q := q).
        all: eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_AnonValue_n with (a := a). eauto with spath. }
      { reflexivity. }
      reflexivity.

  (* Case Reorg_end_abstraction: *)
  - intros ? Hleq. remember (S,,, i' |-> A') as _S eqn:EQN.
    destruct Hleq as [ | | | | _S | | | | ].
    (* Case Leq_ToSymbolic *)
    + destruct (decide (in_abstraction i' (fst sp))) as [(j & Hj) | ].
      * process_state_eq.
        assert (valid_spath (S,,, i' |-> B) sp) as valid_sp by validity.
        destruct sp as (? & q). cbn in Hj. subst.
        apply in_abstraction_valid_spath in valid_sp. destruct valid_sp as (w & ? & ?).
        erewrite sget_add_abstraction in * by eassumption.
        cbn in A_no_loans, Hadd_anons.
        eapply add_anons_abstraction_set in Hadd_anons; [ | eassumption | validity].
        destruct Hadd_anons as (S'' & a & Hadd_anons & -> & get_S''_a_q).
        reorg_step.
        { apply Reorg_end_abstraction. eassumption.
          (* Note: should be a lemma. *)
          unfold abstraction_set in A_no_loans.
          erewrite alter_insert_delete in A_no_loans by eassumption.
          erewrite <-insert_delete by eassumption.
          rewrite map_Forall_insert in A_no_loans |- * by now simpl_map.
          destruct A_no_loans. split; [not_contains | assumption].
          eassumption. }
        reorg_done. eapply leq_n_step.
        { apply Leq_ToSymbolic_n; rewrite get_S''_a_q; eassumption. }
        { rewrite get_S''_a_q. reflexivity. }
        reflexivity.
      * process_state_eq. autorewrite with spath in *.
        apply add_anons_sset_rev in Hadd_anons; [ | validity].
        destruct Hadd_anons as (S'' & Hadd_anons & ->).
        reorg_step.
        { eapply Reorg_end_abstraction; eassumption. }
        reorg_done. eapply leq_n_step.
        { eapply Leq_ToSymbolic_n; erewrite add_anons_sget; eauto with spath. }
        { erewrite add_anons_sget by eauto with spath. reflexivity. }
        reflexivity.
    (* Case Leq_ToAbs *)
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      (* Case 1: we end the abstraction we just introduced. *)
      * destruct EQN as (<- & -> & <-). destruct Hto_abs.
        (* Case 1.a: a reborrow is turned into a region. But we can't end a region that
         * contains a loan. We eliminate this case by contradiction. *)
        -- exfalso. rewrite map_Forall_lookup in A_no_loans.
           eapply A_no_loans with (i := kl).
           simpl_map. reflexivity. constructor. constructor.
           (* Case 1.b. *)
        -- apply add_anons_singleton in Hadd_anons. destruct Hadd_anons as (b & fresh_b & ->).
           (* If v is an integer, we must perform an extra relation step to turn it into a
            * symbolic value. Because when we end the region A, the anonymous binding introduced
            * is a symbolic value. *)
           reorg_done.
           eapply leq_n_step.
           { eapply Leq_ToSymbolic_n with (sp := (anon_accessor a, []) +++ [0]).
             all: autorewrite with spath; eassumption. }
           { autorewrite with spath. autorewrite with weight. lia. }
           autorewrite with spath.
           now apply leq_n_by_equivalence, equiv_states_add_anon.

      (* Case 2: the abstraction we introduce and the abstraction we end are
       * different. *)
      * destruct EQN as (_ & S1 & -> & ->).
        apply fresh_abstraction_add_abstraction_rev in fresh_i', fresh_i.
        destruct fresh_i'. destruct fresh_i as (fresh_i & _).
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (? & -> & Hadd_anons).
        rewrite fresh_anon_add_abstraction in fresh_a.
        apply add_anons_add_anon with (a := a) (v := v) in Hadd_anons; [ | assumption].
        destruct Hadd_anons as (S'1 & Hadd_anons & ? & ?).
        assert (fresh_abstraction S'1 i).
        { apply add_anons_fresh_abstraction with (i := i) in Hadd_anons; eauto with spath. }
        reorg_step.
        { rewrite <-add_abstraction_add_anon.
          apply Reorg_end_abstraction; eauto with spath. }
        reorg_done. eapply leq_n_step.
        { eapply Leq_ToAbs_n; eassumption. }
        { reflexivity. }
        apply leq_n_by_equivalence, equiv_add_abstraction; assumption.
    (* Case Leq_RemoveAnon_n: *)
    + subst. rewrite fresh_anon_add_abstraction in fresh_a.
        apply add_anons_add_anon with (a := a) (v := v) in Hadd_anons; [ | assumption].
        destruct Hadd_anons as (S'' & Hadd_anons & ? & ?).
      reorg_step.
        { rewrite <-add_abstraction_add_anon.
          apply Reorg_end_abstraction; eauto with spath. }
        reorg_done. eapply leq_n_step.
        { eapply Leq_RemoveAnon_n; eassumption. }
        { reflexivity. }
        apply leq_n_by_equivalence. assumption.
    (* Case Leq_MoveValue_n: *)
    + process_state_eq. autorewrite with spath in * |-.
      apply not_in_abstraction_valid_spath in valid_sp; [ | eauto].
      apply add_anons_remove_anon_sset in Hadd_anons; [ | assumption..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_end_abstraction; eauto with spath. }
      reorg_done. eapply leq_n_step.
      (* TODO: eauto? *)
      { apply Leq_MoveValue_n with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath.
        erewrite add_anons_sget by eauto with spath. eassumption.
        eapply add_anons_valid_spath; eassumption.
        eapply not_in_borrow_add_anons; eauto with spath. }
      { reflexivity. }
      erewrite add_anons_sget by eassumption. reflexivity.
    (* Case Leq_MergeAbs_n: *)
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      * destruct EQN as (<- & -> & <-).
        assert (map_Forall (fun _ => not_contains_loan) B) by eauto using merge_no_loan.
        destruct Hmerge as (A' & B' & Hremove_loans & union_A'_B').
        destruct (exists_add_anons (S,,, i |-> A) B) as (Sl1 & HSl1).
        (* Ending the region B: *)
        reorg_step.
        { eapply Reorg_end_abstraction. eauto with spath. assumption. exact HSl1. }
        eapply end_removed_loans with (i := i) in Hremove_loans;
          [ | exact fresh_i | exact HSl1].
        destruct Hremove_loans as (n & Sbots & Hadd_bots & Hn & _Sl2 & reorg_Sl2 & Hadd_anons_Sl2).
        (* Ending all the borrows in the difference between B and B': *)
        reorg_steps. { exact reorg_Sl2. }
        apply add_anons_add_abstraction in Hadd_anons_Sl2.
        destruct Hadd_anons_Sl2 as (Sl2 & -> & Hadd_anons_Sl2).
        destruct (exists_add_anons Sl2 A') as (Sl3 & HSl3).
        (* Ending the region A: *)
        reorg_step.
        { apply Reorg_end_abstraction. eauto with spath.
           (* TODO: lemma *)
           intros ? ? G. eapply union_contains_left in G; [ | exact union_A'_B'].
           eapply A_no_loans. eassumption. eassumption. }
        reorg_done.

        edestruct commute_add_anonymous_bots_anons as (Sl1' & Hadd_anons_Sl1' & Hadd_bots_Sl2);
          [exact Hadd_bots | exact Hadd_anons_Sl2 | ].
        edestruct commute_add_anonymous_bots_anons as (Sl2' & Hadd_anons_Sl2' & Hadd_bots_Sl3);
          [exact Hadd_bots_Sl2 | exact HSl3 | ].
        eapply prove_leq_n.
        { eapply leq_n_add_anonymous_bots; [eassumption | ].
          eapply map_sum_union_maps in union_A'_B'. rewrite union_A'_B'. lia. }
         eapply add_anons_assoc; eassumption.
      * destruct EQN as (? & S0 & -> & ->).
        (* TODO: Ltac? *)
        repeat lazymatch goal with
                 | H : fresh_abstraction (_,,, _ |-> _) _ |- _ =>
                     apply fresh_abstraction_add_abstraction_rev in H;
                     destruct H
               end.
        rewrite !(add_abstraction_commute _ i') by congruence.
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (S'' & -> & Hadd_anons).
        reorg_step.
        { apply Reorg_end_abstraction. eauto with spath. assumption.
          repeat apply add_abstraction_add_anons. eassumption. }
        reorg_done.
        eapply leq_n_step.
        { apply Leq_MergeAbs_n; eauto with spath. } { reflexivity. }
        reflexivity.
    (* Case Leq_Fresh_MutLoan_n: *)
    + process_state_eq.
      apply not_in_abstraction_valid_spath in valid_sp; [ | eauto].
      apply add_anons_remove_anon_sset in Hadd_anons; [ | assumption..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_end_abstraction; eauto with spath. }
      reorg_done.
      autorewrite with spath in Htype |- *.
      eapply leq_n_step.
      { apply Leq_Fresh_MutLoan_n with (sp := sp) (a := a) (l' := l').
        all: autorewrite with spath; eauto with spath.
        eapply is_fresh_add_anons; eassumption.
        eapply add_anons_valid_spath; eassumption.
        erewrite add_anons_sget by eauto with spath. eassumption. }
      { reflexivity. }
      erewrite add_anons_sget by eassumption. reflexivity.
    (* Case Leq_Reborrow_MutBorrow_n: *)
    + process_state_eq. autorewrite with spath in *.
      apply add_anons_remove_anon_sset in Hadd_anons; [ | eauto with spath..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_end_abstraction; eauto with spath. }
      reorg_done. eapply leq_n_step.
      { apply Leq_Reborrow_MutBorrow_n with (sp := sp) (a := a) (l0 := l0) (l1 := l1).
        all: autorewrite with spath; eauto with spath.
        eapply is_fresh_add_anons; eassumption.
        erewrite add_anons_sget; eauto with spath.
        erewrite add_anons_sget; eauto with spath. }
      { reflexivity. }
      erewrite add_anons_sget by eauto with spath. reflexivity.
    (* Case Leq_Abs_ClearValue_n: *)
    + destruct (decide (i = i')) as [<- | ].
      * replace S0 with (S,,, i |-> insert j v A') in *. (* Note: should be a lemma. *)
        2: { apply state_eq_ext.
          - apply map_eq. intros k. destruct (decide (k = encode_abstraction (i, j))) as [-> | ].
            + rewrite get_at_abstraction. cbn. simpl_map. cbn. simpl_map. reflexivity.
            + apply (f_equal get_map) in EQN. apply (f_equal (lookup k)) in EQN.
              rewrite get_map_remove_abstraction_value in EQN. simpl_map. rewrite EQN.
              cbn. rewrite !flatten_insert by assumption.
              rewrite kmap_insert by typeclasses eauto.
              rewrite <-insert_union_l, <-sum_maps_insert_inr.
              apply lookup_insert_ne. symmetry. assumption.
          - apply (f_equal get_extra) in EQN.
            rewrite get_extra_remove_abstraction_value in EQN.
            cbn in *. rewrite dom_insert_L in *. auto. }
        assert (lookup j A' = None).
        { autorewrite with spath in EQN.
          apply (f_equal abstractions), (f_equal (lookup i)) in EQN.
          cbn in EQN. simpl_map. injection EQN as <-. simpl_map. reflexivity. }
        destruct (exists_fresh_anon S') as (a & fresh_a).
        eapply add_anons_insert with (v := v) in Hadd_anons; [ | eassumption..].
        reorg_step.
        { eapply Reorg_end_abstraction; try eassumption. apply map_Forall_insert_2; auto. }
        reorg_done.
        eapply leq_n_step.
        { apply Leq_RemoveAnon_n; assumption. }
        { reflexivity. }
        reflexivity.
      * assert (exists S1,
          S0 = S1,,, i' |-> A' /\
          S = remove_abstraction_value S1 i j /\
          abstraction_element S1 i j = Some v /\ fresh_abstraction S1 i')
        as (S1 & -> & -> & ? & ?).
        (* Note: should be a lemma. *)
        { exists (remove_abstraction i' S0). repeat split.
          - symmetry. apply add_remove_abstraction.
            apply (f_equal abstractions), (f_equal (lookup i')) in EQN. cbn in EQN. simpl_map.
            reflexivity.
          - apply (f_equal (remove_abstraction i')) in EQN.
            rewrite remove_add_abstraction in EQN by assumption.
            unfold remove_abstraction, remove_abstraction_value in *. cbn in *.
            rewrite <-delete_alter_ne; congruence.
          - unfold abstraction_element in *. rewrite get_at_abstraction in *.
            unfold remove_abstraction. cbn. simpl_map. assumption.
          - apply remove_abstraction_fresh. }
        autorewrite with spath in get_at_i_j.
        apply add_anons_add_abstraction_value in Hadd_anons.
        destruct Hadd_anons as (? & Hadd_anons & ->).
        reorg_step.
        { apply Reorg_end_abstraction; eassumption. }
        reorg_done. eapply leq_n_step.
        { eapply Leq_Abs_ClearValue_n with (v := v); try eassumption.
          eapply add_anons_abstraction_element; eassumption. }
        { reflexivity. }
        reflexivity.
    (* Case Leq_AnonValue_n: *)
    + process_state_eq.
      apply add_anons_remove_anon in Hadd_anons; [ | assumption].
      destruct Hadd_anons as (S'' & -> & ? & Hadd_anons).
      reorg_step.
      { eapply Reorg_end_abstraction; eassumption. }
      reorg_done. eapply leq_n_step.
      { eapply Leq_AnonValue_n. eassumption. }
      { reflexivity. }
      reflexivity.
Qed.

Lemma reorg_preserve_equiv : forward_simulation equiv_states equiv_states reorg reorg.
Proof.
  intros S0 S1 Hreorg S'0 Hequiv. symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ->).
  destruct Hreorg.
  - execution_step.
    { eapply Reorg_end_borrow_m with (p := permutation_spath perm p)
                                     (q := permutation_spath perm q).
      all: eauto with spath.
      rewrite permutation_sget, get_node_rename_value, get_loan; eauto with spath.
      rewrite permutation_sget, get_node_rename_value, get_borrow; eauto with spath.
      all: autorewrite with spath; eauto with spath. }
    assert (subseteq (loan_set_val (S .[q +++ [0] ])) (dom (loan_id_names perm))).
    { etransitivity; [apply loan_set_sget | apply Hperm]. }
    symmetry. eexists. autorewrite with spath. auto with spath.

  - edestruct permutation_accessor_abstraction_element as (k & ?); [eauto.. | ].
    execution_step.
    { eapply Reorg_end_borrow_m_in_abstraction with (q := permutation_spath perm q);
        eauto with spath.
      erewrite permutation_abstraction_element, get_loan; eauto.
      autorewrite with spath. rewrite get_borrow. reflexivity.
      all: autorewrite with spath; eauto with spath. }
    pose proof Hperm as Hperm'.
    apply remove_abstraction_value_perm_equivalence with (i := i') (j := j') in Hperm'.
    symmetry. eexists. split; [eauto with spath | ]. autorewrite with spath.
    (* TODO: automatic rewriting *)
    erewrite permutation_remove_abstraction_value by eassumption. reflexivity.

  - process_state_equivalence. autorewrite with spath.
    set (S0 := apply_state_permutation (remove_abstraction_perm perm i') S).
    set (B := apply_permutation p (rename_set (loan_id_names perm) A')).
    destruct (exists_add_anons S0 B) as (S'0 & Hadd_anons').
    execution_step.
    { apply Reorg_end_abstraction; [eauto with spath | | exact Hadd_anons'].
      eauto with spath. unfold B. rewrite pkmap_fmap by apply map_inj_equiv, perm_A.
      apply map_Forall_fmap. apply permutation_forall; [assumption | ].
      intros ? ? ?. eauto with spath. }
    symmetry. eapply add_anons_equiv; eassumption.
Qed.

Lemma reorg_preservation : forward_simulation leq_symbolic leq_symbolic reorg^* reorg^*.
Proof.
  eapply preservation_reorg_l.
  - exact leq_state_base_n_decreases.
  - exact reorg_decreases.
  - exact reorg_preserve_equiv.
  - exact leq_n_equiv_states_commute.
  - exact leq_state_base_n_is_leq_state_base.
  - exact reorg_local_preservation.
Qed.

(** ** Simulation proofs for statement evaluation. *)
Lemma leq_singleton r Sl Sr : leq_symbolic Sl Sr -> leq_branching {[r := Sl]} {[r := Sr]}.
Proof.
  intros H r'. destruct (decide (r = r')) as [<- | ].
  - simpl_map. constructor. assumption.
  - unfold branching_state. simpl_map. constructor.
Qed.

(** If [Bjoin] is a join state for two states [B0_r] and [B1_r], if these two states are more abstract than the respective states [B0_l] and [B1_l], it is not necessary the case that [Bjoin] is a join of [B0_l] and [B1_r]. Indeed, there can be a control-flow tag [r] such that [lookup r B0_l = None] while [Is_Some (lookup r B0_r)], and [lookup r Bjoin_r] is not necessarily [lookup r B1_r].

   We need to "compute" a join by choosing a value among [lookup r B0_l],  [lookup r B1_l] and [lookup r Bjoin] depending if the values [lookup r B0_l] and [lookup r B1_l] are [Some] or [None]. *)
Definition compute_option_join (oSl oSr : option LLBC_plus_state) default :=
  match oSl, oSr with
  | None, _ => oSr
  | _, None => oSl
  | _, _ => Some default
  end.

(* TODO: confusing name, similar to [leq_is_join_l]. *)
Lemma is_join_left B0_l B1_l B0_r B1_r Bjoin_r (Hjoin : is_join B0_r B1_r Bjoin_r)
  (Hleq_0 : leq_branching B0_l B0_r) (Hleq_1 : leq_branching B1_l B1_r) :
  exists Bjoin_l : branching_state, is_join B0_l B1_l Bjoin_l /\ leq_branching Bjoin_l Bjoin_r.
Proof.
  exists (map_imap (fun r => compute_option_join (lookup r B0_l) (lookup r B1_l)) Bjoin_r).
  split.
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hleq_0 r). specialize (Hleq_1 r). specialize (Hjoin r).
    destruct Hjoin; inversion Hleq_0; inversion Hleq_1.
    all: constructor. all: etransitivity; [eassumption | congruence].
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hleq_0 r). specialize (Hleq_1 r). specialize (Hjoin r).
    unfold compute_option_join.
    destruct Hjoin; inversion Hleq_0; inversion Hleq_1; constructor.
    all: try reflexivity. all: try assumption. all: etransitivity; eassumption.
Qed.

Lemma leq_branching_delete r0 Sl Sr :
  leq_branching Sl Sr -> leq_branching (delete r0 Sl) (delete r0 Sr).
Proof.
  intros H r. specialize (H r). unfold branching_state.
  destruct (decide (r0 = r)) as [<- | ]; simpl_map; [constructor | assumption].
Qed.

Lemma leq_is_join_l Bl Br Bjoin : is_join Bl Br Bjoin -> leq_branching Bl Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.

Lemma leq_is_join_r Bl Br Bjoin : is_join Bl Br Bjoin -> leq_branching Br Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.

(* Note: most of that is a copy-paste of similar theorems for integers. *)
(* Note: rewrite the following results when we introduce enumerations. Some of the assumptions this section relies on (e.g: boolean are zeroary, they do not contain borrows) are wrong in general.
   We should prove a more general lemma:
   - The relations [leq_symbolic] and [leq_val_state] preserve types.
   - A value of type A + B is either:
     - inl v, with v : A, and v do not contain loans.
     - inr v, with v : B, and v do not contain loans.
     - sigma_{A + B}
 *)
(* TODO: rewrite the lemma [leq_val_state_integer] accordingly. *)
Definition leq_boolean_state leq (vSl vSr : LLBC_plus_val * LLBC_plus_state) :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  (vl = vr \/ is_of_type boolT vl /\ not_contains_loan vl /\ vr = LLBC_plus_symbolic boolT) /\
  leq Sl Sr.

Lemma boolean_zeroary v :
  not_contains_loan v -> is_of_type boolT v -> arity (get_node v) = 0.
Proof. intros ? H. inversion H; reflexivity. Qed.

Lemma leq_val_state_base_boolean vl Sl vr Sr :
  leq_val_state_base leq_state_base (vl, Sl) (vr, Sr) ->
  is_of_type boolT vr -> not_contains_loan vr ->
  (vl = vr /\ leq_state_base Sl Sr) \/
  (is_of_type boolT vl /\ not_contains_loan vl /\ vr = LLBC_plus_symbolic boolT /\ Sl = Sr).
Proof.
  destruct (exists_fresh_anon2 Sl Sr) as (a & fresh_a_l & fresh_a_r).
  intros H vr_is_int no_loan.
  specialize (H a fresh_a_l fresh_a_r). rewrite !fst_pair, !snd_pair in H.
  remember (Sl,, a |-> vl) eqn:EQN_l. remember (Sr,, a |-> vr) eqn:EQN_r.
  destruct H; subst.
  - destruct (decide (fst sp = anon_accessor a)).
    + right. autorewrite with spath in * |-. process_state_eq.
      assert (snd sp = []) as G.
      { eapply valid_vpath_zeroary.
        - apply boolean_zeroary; eassumption.
        - apply vset_same_valid; eauto with spath. }
      rewrite G in *. cbn in *. inversion vr_is_int. subst. eauto.
    + left. autorewrite with spath in *.
      process_state_eq. split; [reflexivity | ]. econstructor; eassumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; assumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; assumption.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & ?) | (? & ?)].
    2: { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply is_of_type_does_not_contain_bot.
      - eassumption.
      - apply vset_same_valid. validity.
      - autorewrite with spath. reflexivity. }
    autorewrite with spath in *. process_state_eq. autorewrite with spath in *.
    left. split; [reflexivity | ]. constructor; assumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor; auto with spath.
  - apply valid_spath_add_anon_cases in valid_sp.
    destruct valid_sp as [(? & ?) | (? & ?)].
    2: { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply no_loan.
      - apply vset_same_valid. validity.
      - autorewrite with spath. constructor. }
    autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. apply Leq_Fresh_MutLoan; auto. not_contains.
  - destruct (decide (fst sp = anon_accessor a)).
    { autorewrite with spath in * |-. process_state_eq.
      exfalso. eapply boolean_does_not_contain_borrow.
      - eassumption.
      - apply vset_same_valid. validity.
      - autorewrite with spath. constructor. }
    autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. apply Leq_Reborrow_MutBorrow; auto. not_contains.
  - autorewrite with spath in *. process_state_eq.
    left. split; [reflexivity | ]. econstructor; eassumption.
  - process_state_eq. left. split; [reflexivity | ]. constructor. assumption.
Qed.

Lemma _leq_val_state_boolean vl Sl vr Sr :
  (leq_val_state_base leq_state_base)^* (vl, Sl) (vr, Sr) ->
  is_of_type boolT vr -> not_contains_loan vr ->
  leq_boolean_state (leq_state_base^*) (vl, Sl) (vr, Sr).
Proof.
  intros H Htype no_loan.
  remember (vl, Sl) as vSl eqn:EQN_l. remember (vr, Sr) as vSr eqn:EQN_r.
  revert vl Sl vr Sr EQN_l EQN_r Htype no_loan.
  induction H as [ | ? (vm & Sm) ? Hleq_l IH Hleq_r]
    using clos_refl_trans_ind_left';
    intros  vl Sl vr Sr -> -> Htype no_loan.
  - split; [ | reflexivity]. left. reflexivity.
  - eapply leq_val_state_base_boolean in Hleq_r; [ | eassumption..].
    destruct Hleq_r as [(? & ?) | (? & ? & ? & ?)]; subst.
    + edestruct IH; [reflexivity | reflexivity | assumption.. | ]. split; [assumption | ].
      transitivity Sm; [ | constructor]; assumption.
    + edestruct IH as ([ | (? & ? & ?)] & ?); [reflexivity | reflexivity | assumption.. | | ];
        subst; unfold leq_boolean_state; auto.
Qed.

Lemma leq_val_state_boolean vl Sl vr Sr :
  leq_val_state (vl, Sl) (vr, Sr) -> is_of_type boolT vr -> not_contains_loan vr ->
  leq_boolean_state leq_symbolic (vl, Sl) (vr, Sr).
Proof.
  intros ((v'r & S'r) & Hequiv & Hleq) Htype no_loan.
  apply _leq_val_state_boolean in Hleq; [ | assumption..]. destruct Hleq as (Hv & Hleq).
  destruct Hequiv as (perm & Hequiv & _ & -> & ->).
  rewrite !rename_value_no_loan_id in Hv.
  - split.
    + exact Hv.
    + eexists. split; [ | exact Hleq]. exists perm. auto.
  (* This ugly case could be simply resolved with a hypothesis [is_of_type boolT vl]. *)
  - destruct Hv as [<- | (type_vl & no_loan_l & ->)].
    + destruct vl; inversion Htype; subst; try reflexivity.
      exfalso. eapply no_loan; constructor.
    + destruct vl; inversion type_vl; try reflexivity.
      exfalso. eapply no_loan_l; constructor.
Qed.

Lemma leq_val_state_concrete_boolean b vl Sl Sr :
  leq_val_state (vl, Sl) (LLBC_plus_bool b, Sr) -> vl = LLBC_plus_bool b /\ leq_symbolic Sl Sr.
Proof.
  intros (Hvl & Hleq)%leq_val_state_boolean.
  - split; [ | exact Hleq]. destruct Hvl as [ | (_ & _ & [=])]. assumption.
  - constructor.
  - not_contains.
Qed.

Lemma leq_val_state_symbolic_boolean vl Sl Sr :
  leq_val_state (vl, Sl) (LLBC_plus_symbolic boolT, Sr) ->
  ((exists b, vl = LLBC_plus_bool b) \/ vl = LLBC_plus_symbolic boolT) /\ leq_symbolic Sl Sr.
Proof.
  intros (Hvl & Hleq)%leq_val_state_boolean.
  - split; [ | exact Hleq]. destruct Hvl as [ | (Htype & no_loan & _)]; auto.
    inversion Htype; subst; eauto. exfalso. eapply no_loan; constructor.
  - constructor.
  - not_contains.
Qed.

Lemma stmt_preserves_LLBC_plus_rel s :
  forward_simulation leq_symbolic leq_branching (eval_stmt s) (eval_stmt s).
Proof.
  intros Sr S'r Heval. induction Heval; intros Sl Hleq.
  (* Case [Eval_nop]. *)
  - execution_step. { constructor. }
    apply leq_singleton. assumption.

  (* Case [Eval_seq_no_unit] *)
  - specialize (IHHeval _ Hleq). destruct IHHeval as (Bl & ? & ?).
    execution_step.
    { apply Eval_seq_no_unit; [eassumption | ].
      (* TODO: lemma? *) specialize (H rUnit). inversion H; congruence. }
    assumption.

  (* Case [Eval_seq] *)
  - specialize (IHHeval1 _ Hleq). destruct IHHeval1 as (B1l & Hleq1 & ?).
    destruct (lookup rUnit B1l) as [S_unit_l | ] eqn:H_unit_l.
    (* Case 1: TODO *)
    + pose proof (Hleq1 rUnit) as _Hleq1. rewrite H_unit_l, H_unit in _Hleq1.
      inversion _Hleq1 as [ | ? ? Hleq1_unit]. subst. clear _Hleq1.
      specialize (IHHeval2 _ Hleq1_unit). destruct IHHeval2 as (B_unit_l & Hleq2 & Heval2_l).
      edestruct is_join_left as (Bjoin_l & ? & ?);
        [eassumption.. | apply leq_branching_delete; eassumption| ].
      execution_step. { eapply Eval_seq; eassumption. }
      assumption.
    (* Case 2: TODO *)
    + execution_step. { apply Eval_seq_no_unit; eassumption. }
      etransitivity.
      * apply (leq_branching_delete rUnit) in Hleq1.
        unfold branching_state in Hleq1. rewrite delete_notin in Hleq1 by assumption.
        exact Hleq1.
      * eapply leq_is_join_r. exact His_join.

  (* Case [Eval_assign] *)
  - destruct vS' as (vr & S'r).
    assert (not_contains_bot vr). { eapply eval_rvalue_no_bot. eassumption. }
    assert (not_contains_loan vr). { eapply eval_rvalue_no_loan. eassumption. }
    apply rvalue_preserves_leq in eval_rv. specialize (eval_rv _ Hleq).
    destruct eval_rv as ((v'l & S'l) & ? & ?).
    eapply store_preserves_LLBC_plus_rel in Hstore; [ | eassumption..].
    destruct Hstore as (S''l & Hstore & ?).
    execution_step. { econstructor; eassumption. }
    apply leq_singleton. assumption.

  (* Case [Eval_if_true] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_concrete_boolean in Hleq'. destruct Hleq' as (-> & Hleq').
    apply IHHeval in Hleq'. destruct Hleq' as (S''l & Hleq'' & eval_if).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [Eval_if_false] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_concrete_boolean in Hleq'. destruct Hleq' as (-> & Hleq').
    apply IHHeval in Hleq'. destruct Hleq' as (S''l & Hleq'' & eval_else).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [Eval_if_symbolic] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_symbolic_boolean in Hleq'.
    destruct Hleq' as ([([ | ] & ->) | ->] & Hleq').
    (* Case 1: the symbolic value abstracts the boolean true. We apply the rule [Eval_if_true]. *)
    + apply IHHeval1 in Hleq'. destruct Hleq' as (B''l & Hleq'' & eval_if).
      execution_step. { econstructor; eassumption. }
      transitivity B_if; eauto using leq_is_join_l.
    (* Case 2: the symbolic value abstracts the boolean false. We apply the rule [Eval_if_false]. *)
    + apply IHHeval2 in Hleq'. destruct Hleq' as (B''l & Hleq'' & eval_else).
      execution_step. { econstructor; eassumption. }
      transitivity B_else; eauto using leq_is_join_r.
    (* Case 3: the symbolic value abstracts a symbolic value. *)
    + specialize (IHHeval1 _ Hleq'). destruct IHHeval1 as (Bl_if & Hleq'_l & eval_if).
      specialize (IHHeval2 _ Hleq'). destruct IHHeval2 as (Bl_else & Hleq'_r & eval_else).
      eapply is_join_left in His_join; [ | eassumption..].
      destruct His_join as (Bjoin_l & His_join & ?).
      execution_step. { eapply Eval_if_symbolic; eassumption. } assumption.


  (* Case [Eval_reorg] *)
  - eapply reorg_preservation in Hreorg. specialize (Hreorg _ Hleq).
    destruct Hreorg as (S'l & Hleq' & ?).
    specialize (IHHeval _ Hleq'). destruct IHHeval as (? & ? & ?).
    execution_step. { econstructor; eassumption. } assumption.
Qed.

(** * Execution of a program in the LLBC+ semantics. *)
(** Utilities to execute programs. *)
Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(_, l) => false
  | _ => true
  end.

(* TODO: move in PathToSubtree.v *)
Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

(* For the moment, the type of values is so restricted that a value contains an outer loan if and
 * only if it is a mutable loan. *)
Lemma decide_not_contains_outer_loan_correct v :
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] _ H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Instance decidable_not_value_contains P `(P_dec : forall n, Decision (P n)) v :
  Decision (not_value_contains P v).
Proof.
  induction v; eauto using decidable_not_value_contains_zeroary, decidable_not_value_contains_unary.
Defined.

Instance decidable_is_loan v : Decision (is_loan v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance decidable_is_borrow v : Decision (is_borrow v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance LLBC_plus_val_EqDec : EqDecision LLBC_plus_nodes.
Proof. intros ? ?. unfold Decision. repeat decide equality. Defined.

Instance decide_is_fresh l S : Decision (is_fresh l S).
Proof. apply decidable_not_state_contains. unfold is_loan_id. solve_decision. Defined.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)
(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

Ltac remove_abstraction i :=
  lazymatch goal with
  | |- ?leq_star ?S _ =>
      erewrite<- (add_remove_abstraction i _ S) by reflexivity;
      rewrite ?remove_add_abstraction_ne by congruence
  end.

Ltac remove_anon a :=
  lazymatch goal with
  | |- ?leq_star ?S _ => erewrite<- (add_anon_remove_anon S a) by reflexivity
  end.

Lemma prove_leq_symbolic Sl Sm Sr :
  leq_state_base^* Sl Sm -> leq_symbolic Sm Sr -> leq_symbolic Sl Sr.
Proof.
  intros H (? & G & ?).
  pose proof leq_equiv_states_commute as Hsim.
  apply sim_leq_equiv in Hsim. specialize (Hsim _ _ G _ H).
  edestruct Hsim as (Sl' & ? & ?).
  exists Sl'. split; [assumption | ]. etransitivity; eassumption.
Qed.

(* These two lemmas are used to show to limited cases of store_compatible_types.
 * Ideally, to be as general as possible when showing
 * [store_compatible_types S (acc, p) v], we should strip the last elements of p one by one,
 * and for each encountered borrow, prove that the type is preserved. *)
Lemma store_compatible_types_nil S acc v : store_compatible_types S (acc, []) v.
Proof. intros q prefix_q_nil%not_strict_prefix_nil. contradiction. Qed.

Lemma store_compatible_types_borrow S acc v ty :
  is_of_type ty v -> is_of_type ty (S.[(acc, [0])]) ->
  store_compatible_types S (acc, [0]) v.
Proof.
  intros ? ? q. replace (acc, [0]) with ((acc, []) +++ [0]) by reflexivity.
  rewrite strict_prefix_app_last. intros ->%prefix_nil _.
  exists ty. split; assumption.
Qed.

(* TODO: rename Eval_seq to Eval_seq. *)
Lemma eval_seq_unit S0 S1 B2 stmt_l stmt_r
  (eval_stmt_l : S0 |-{stmt} stmt_l => {[rUnit := S1]})
  (eval_stmt_r : S1 |-{stmt} stmt_r => B2) :
  S0 |-{stmt} (Seq stmt_l stmt_r) => B2.
Proof.
  eapply Eval_seq.
  - exact eval_stmt_l.
  - reflexivity.
  - exact eval_stmt_r.
  - (* TODO: lemma? *)
    intros r. unfold branching_state. rewrite delete_singleton, lookup_empty.
    destruct (lookup _ _); constructor.
Qed.

Lemma is_join_singletons r S0 S1 Sjoin :
  leq_symbolic S0 Sjoin -> leq_symbolic S1 Sjoin ->
  is_join {[r := S0]} {[r := S1]} {[r := Sjoin]}.
Proof.
  intros ? ? r'. destruct (decide (r' = r)) as [-> | ].
  - simpl_map. constructor; assumption.
  - unfold branching_state. simpl_map. constructor.
Qed.

Local Open Scope option_monad_scope.
(** The program we execute is:
<<
fn f(x : i32, y : i32) {
   let z;
   if x <= y {
       z = &mut x;
   }
   else {
       z = &mut y;
   }
   *z += 1;
   x += 2;
}
>>
 *)
Notation x := 1%positive.
Notation y := 2%positive.
Notation z := 3%positive.
Notation cond := 4%positive.

(* TODO: solve scope issues. *)
Close Scope stdpp_scope.

(** Note that we have to introduce a temporary variable [cond] to store the result of the comparison. *)
Definition f :=
  ASSIGN (cond, []) <- BinaryOp BLe (Copy (x, [])) (Copy (y, []));;
  IF Copy (cond, []) {{
    ASSIGN (z, []) <- &mut (x, [])
  }}
  ELSE {{
    ASSIGN (z, []) <- &mut (y, [])
  }};;
  ASSIGN (z, [Deref]) <- BinaryOp BAdd (Copy (z, [Deref])) (Const (IntConst 1));;
  ASSIGN (x, []) <- BinaryOp BAdd (Copy (x, [])) (Const (IntConst 2))
.

Open Scope stdpp.
(** We execute the function [f] on the most general state. The arguments << x >> and << y >> are initialized as symbolic values, while the local variables are uninitialized. *)
Definition init_state := {|
  vars := {[x := LLBC_plus_symbolic intT; y := LLBC_plus_symbolic intT; z := bot; cond := bot]};
  anons := empty;
  abstractions := empty;
|}.

Definition lx : loan_id := 1%positive.
Definition ly : loan_id := 2%positive.
Definition lz : loan_id := 3%positive.

Definition A : positive := 1.

(** The join state at the end of the conditional. *)
Definition join_state : LLBC_plus_state := {|
  vars := {[
    x := loan^m(intT, lx);
    y := loan^m(intT, ly);
    z := borrow^m(lz, LLBC_plus_symbolic intT);
    cond := LLBC_plus_symbolic boolT
  ]};
  anons := empty;
  abstractions := {[
    A := {[1%positive := borrow^m(lx, LLBC_plus_symbolic intT);
           2%positive := borrow^m(ly, LLBC_plus_symbolic intT);
           3%positive := loan^m(intT, lz)]} ]}
|}.

Section Eval_LLBC_plus_program.
  Hint Rewrite (@alter_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@delete_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using reflexivity : core.
  Hint Rewrite (@delete_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using congruence : core.
  Hint Rewrite (@delete_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  (* Perform simplifications to put maps of the state in the form [{[x0 := v0; ...; xn := vn]}],
     that is a notation for a sequence of insertions applied to a singleton.
     We cannot use the tactic [vm_compute] because it computes under the insertions and the
     singleton. *)
  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singletonM delete leq_symbolic];
    autorewrite with core.

  Lemma safe_f : exists end_state, eval_stmt f init_state end_state.
  Proof.
    eexists.
    eapply eval_seq_unit.
    (* Evaluation of the computation << x <= y >>. The result is stored in the temporary variable [cond]. *)
    { eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - econstructor.
        + econstructor. eval_var. constructor. constructor. constructor.
        + econstructor. eval_var. constructor. constructor. constructor.
        + constructor.
      - eval_var. constructor.
      - apply decide_not_contains_outer_loan_correct. reflexivity.
      - apply store_compatible_types_nil.
      - reflexivity.
    }
    simpl_state. eapply eval_seq_unit.


    (* Evaluation of the conditional. *)
    { eapply Eval_if_symbolic with (B_join := {[rUnit := join_state]}).
      { econstructor. eval_var. constructor. econstructor. constructor. }

      (* Evaluation of the if branch. *)
      { eapply Eval_assign; [ | apply Store with (a := 2%positive)].
        + apply Eval_mut_borrow with (l := lx).
          * eval_var. constructor.
          * compute_done.
          * compute_done.
          * compute_done.
          * constructor.
        + eval_var. constructor.
        + apply decide_not_contains_outer_loan_correct. constructor.
        + apply store_compatible_types_nil.
        + reflexivity. }

      (* Evaluation of the else branch. *)
      { eapply Eval_assign; [ | apply Store with (a := 2%positive)].
        + apply Eval_mut_borrow with (l := ly).
          * eval_var. constructor.
          * compute_done.
          * compute_done.
          * compute_done.
          * constructor.
        + eval_var. constructor.
        + apply decide_not_contains_outer_loan_correct. constructor.
        + apply store_compatible_types_nil.
        + reflexivity. }

      apply is_join_singletons.
      (* The state [S_join] is more abstract than the state at the end of the if branch. *)
      { simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive) (kb := 1%positive) (kl := 3%positive); try compute_done.
          eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
        simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var y, [])) (l' := ly) (i := 2%positive) (k := 2%positive);
            [compute_done | now eapply var_not_in_abstraction | compute_done.. | constructor]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_abstraction 1%positive. remove_abstraction 2%positive.
          eapply Leq_MergeAbs; [reflexivity.. | | discriminate].
          econstructor. eexists. split. constructor.
          eapply UnionInsert with (j := 2%positive); [reflexivity.. | ].
          apply UnionEmpty. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). constructor. all: compute_done. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 2%positive. apply Leq_RemoveAnon. all: compute_done. }
        reflexivity. }

      (* The state [S_join] is more abstract than the state at the end of the else branch. *)
      { eapply prove_leq_symbolic.
        { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive) (kb := 2%positive) (kl := 3%positive); try compute_done.
          eapply var_not_in_abstraction; reflexivity. reflexivity. constructor. }
        simpl_state.
        eapply prove_leq_symbolic.
        { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var x, [])) (l' := lx) (i := 2%positive) (k := 1%positive);
            [compute_done | now eapply var_not_in_abstraction | compute_done.. | constructor]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_abstraction 1%positive. remove_abstraction 2%positive.
          apply Leq_MergeAbs; [reflexivity.. | | discriminate].
          econstructor. eexists. split. constructor.
          eapply UnionInsert with (j := 1%positive); [reflexivity.. | ].
          apply UnionEmpty. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])); [constructor | compute_done..]. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
        simpl_state.
        eapply prove_leq_symbolic; [constructor | ].
        { remove_anon 2%positive. apply Leq_RemoveAnon. all: compute_done. }
        reflexivity. }
    }

    (* Execution of the line << *z += 1 >> *)
    eapply eval_seq_unit.
    { eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - econstructor.
        + eapply Eval_copy.
          * eval_var. repeat econstructor || easy.
          * constructor. constructor.
        + apply Eval_IntConst.
        + constructor.
      - eval_var. repeat econstructor || easy.
      - cbn. apply decide_not_contains_outer_loan_correct. reflexivity.
      - eapply store_compatible_types_borrow; constructor.
      - reflexivity.
    }
    simpl_state.

    (* In order to access the variable << x >>, we must perform reorganizations in order to end the loan [lx.] *)
    eapply Eval_reorg.
    { etransitivity.
      (* Ending the loan [lz] ... *)
      { constructor.
        eapply Reorg_end_borrow_m_in_abstraction
          with (i' := 1%positive) (j' := 3%positive) (q := (encode_var 3%positive, [])).
        - reflexivity.
        - reflexivity.
        - constructor.
        - compute_done.
        - intros ? ?. apply not_strict_prefix_nil.
        - eapply var_not_in_abstraction. reflexivity. }
      simpl_state. etransitivity.
      (* ... so that we could end the region abstraction ... *)
      { constructor.
        remove_abstraction 1%positive. apply Reorg_end_abstraction.
        - reflexivity.
        - compute_done.
        - constructor. cbn. apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
         apply UnionInsert with (j := 3%positive); [reflexivity.. | ].
          apply UnionEmpty.
      }
      simpl_state.
      (* ... so that we could end the loan [lx]. *)
      { constructor.
        eapply Reorg_end_borrow_m with (p := (encode_var 1%positive, []))
                                       (q := (encode_anon 2%positive, [])).
        - reflexivity.
        - reflexivity.
        - constructor.
        - compute_done.
        - intros ? ?. apply not_strict_prefix_nil.
        - left. discriminate.
        - eapply var_not_in_abstraction. reflexivity.
        - eapply anon_not_in_abstraction. reflexivity. }
    }
    simpl_state.

    (* Execution of the line << x += 2 >> *)
    eapply Eval_assign; [ | apply Store with (a := 5%positive)].
    - econstructor.
      + eapply Eval_copy; [eval_var | ]; constructor. constructor.
      + constructor.
      + constructor.
    - eval_var. constructor.
    - apply decide_not_contains_outer_loan_correct. reflexivity.
    - apply store_compatible_types_nil.
    - reflexivity.
  Qed.
End Eval_LLBC_plus_program.
