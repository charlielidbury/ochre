(** * Mechanized_LLBC.LLBC_sharp_states : Definition of LLBC# states. *)
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
| TInt
| TBool
.

(** * Definition of LLBC## values and states. *)
Inductive value :=
| VBottom
| VInt (n : nat) (* TODO: use Aeneas integer types? *)
| VBool (b : bool)
(* Note: we must add a type parameter in mutable loans, because when we end a mutable loan in a
 * region abstraction, we must ensure that the type of the borrow we end corresponds.
 * However, this creates the issue that now, every mutable loan is typed, even mutable loans out
 * of abstractions.
 * Probably we should remove all dynamic typing, and implement a static type checking, as well as a
 * well-typedness predicate and an invariance proof. *)
| VMutLoan (ty : LLBC_type) (l : loan_id)
| VMutBorrow (l : loan_id) (v : value)
(* Note: symbolic values should be parameterized by a type, when we introduce other datatypes than
   integers. *)
| VSymbolic (ty : LLBC_type)
.

Variant nodes :=
| NBottom
| NInt (n : nat)
| NBool (b : bool)
| NMutLoan (ty : LLBC_type) (l : loan_id)
| NMutBorrow (l : loan_id)
| NSymbolic (ty : LLBC_type)
.

Instance EqDecision_nodes : EqDecision nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Defined.

Definition LLBC_sharp_arity c := match c with
| NBottom => 0
| NInt _ => 0
| NBool _ => 0
| NMutLoan _ _ => 0
| NMutBorrow _ => 1
| NSymbolic _ => 0
end.

Definition LLBC_sharp_get_node v := match v with
| VBottom => NBottom
| VInt n => NInt n
| VBool b => NBool b
| VMutLoan ty l => NMutLoan ty l
| VMutBorrow l _ => NMutBorrow l
| VSymbolic ty => NSymbolic ty
end.

Definition LLBC_sharp_children v := match v with
| VBottom => []
| VInt _ => []
| VBool _ => []
| VMutLoan _ _ => []
| VMutBorrow _ v => [v]
| VSymbolic ty => []
end.

Definition LLBC_sharp_fold c vs := match c, vs with
| NInt n, [] => VInt n
| NBool b, [] => VBool b
| NMutLoan ty l, [] => VMutLoan ty l
| NMutBorrow l, [v] => VMutBorrow l v
| NSymbolic ty, [] => VSymbolic ty
| _, _ => VBottom
end.

Fixpoint LLBC_sharp_weight node_weight v :=
  match v with
  | VMutBorrow l v => node_weight (NMutBorrow l) + LLBC_sharp_weight node_weight v
  | v => node_weight (LLBC_sharp_get_node v)
end.

Program Instance ValueLLBC_sharp : Value value nodes := {
  arity := LLBC_sharp_arity;
  get_node := LLBC_sharp_get_node;
  children := LLBC_sharp_children;
  fold_value := LLBC_sharp_fold;
  vweight := LLBC_sharp_weight;
  bot := VBottom;
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

Record state := {
  vars : Pmap value;
  anons : Pmap value;
  abstractions : Pmap (Pmap value);
}.

(** A symbolic execution abstracts all executions, from all branches. A "branching state" [B] is a partial map. It can associate a control-flow token [r] (break, continue, panic...) to symbolic state [S] that is more general than all the computations that terminate with [r]. This maps is partial, because if no computation terminates on [r], we have [lookup r B = None].

   Note: in the ICFP'24 article, Ho et al. propose a more general notion of branching state. These states are simply sets of pairs [(r, S)] (with [r] a control-flow token and [S] a symbolic state). This allows duplication, and it may be more practical for panic management. The following definition could change in the future. *)
Definition branching_state := gmap flow_token state.

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

Program Instance IsState : State state value := {
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
    + symmetry. apply alter_id'. rewrite <-H, sum_maps_lookup_l.
      now apply sum_maps_lookup_None.
  - cbn. rewrite decode'_is_Some in H. rewrite <-H,  sum_maps_alter_inr, alter_flatten. reflexivity.
  - symmetry. apply alter_id', sum_maps_lookup_None. assumption.
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

Declare Scope llbc_sharp_scope.
Delimit Scope llbc_sharp_scope with llbc_sharp.

(* Notation "'bot'" := VBottom: llbc_sharp_scope. *)
Notation "'loan^m' ( ty , l )" := (VMutLoan ty l) : llbc_sharp_scope.
Notation "'borrow^m' ( l  , v )" := (VMutBorrow l v) : llbc_sharp_scope.

Notation "'nbot'" := NBottom: llbc_sharp_scope.
Notation "'nloan^m' ( ty , l )" := (NMutLoan ty l) : llbc_sharp_scope.
Notation "'nborrow^m' ( l )" := (NMutBorrow l) : llbc_sharp_scope.

(* Bind Scope llbc_sharp_scope with value. *)
Open Scope llbc_sharp_scope.

(** Definitions of LLBC## operations. *)
Variant is_loan : nodes -> Prop :=
| IsLoan_MutLoan ty l : is_loan (nloan^m(ty, l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (is_loan (get_node loan^m(_, _))) => constructor : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Lemma is_loan_valid S sp : is_loan (get_node (S.[sp])) -> valid_spath S sp.
Proof. intros H. apply valid_get_node_sget_not_bot. destruct H; discriminate. Qed.

Variant is_borrow : nodes -> Prop :=
| IsLoan_MutBorrow l : is_borrow (nborrow^m(l)).
Hint Constructors is_borrow : spath.
Definition not_contains_borrow := not_value_contains is_borrow.
Hint Unfold not_contains_borrow : spath.
Hint Extern 0 (is_borrow (get_node borrow^m(_, _))) => constructor : spath.
Hint Extern 0 (~is_borrow _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = nbot) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> nbot) => discriminate : spath.

Lemma not_contains_bot_valid S sp : not_contains_bot (S.[sp]) -> valid_spath S sp.
Proof.
  intros H. specialize (H []). cbn in H. apply get_not_bot_valid_spath.
  intros G. apply H. constructor. rewrite G. reflexivity.
Qed.
Hint Resolve not_contains_bot_valid : spath.

Variant is_symbolic : nodes -> Prop :=
| IsSymbolic_Symbolic ty : is_symbolic (NSymbolic ty).
Definition not_contains_symbolic v := (not_value_contains is_symbolic v).
Hint Unfold not_contains_symbolic : spath.
Hint Extern 0 (~is_symbolic _) => intro; easy : spath.

Variant is_mut_borrow : nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (nborrow^m(l)).
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
Notation rename_mut_borrow_val v vp l := (v.[[vp <- borrow^m(l, v.[[vp ++ [0] ]])]])
  (vp in scope list_scope).

(* [is_of_type ty v] asserts that the value v is initialized (not bot) and of type ty. *)
Variant is_of_type : LLBC_type -> value -> Prop :=
| Is_of_type_symbolic ty : is_of_type ty (VSymbolic ty)
| Is_of_type_mut_loan ty l : is_of_type ty (loan^m(ty, l))
| Is_of_type_integer n : is_of_type TInt (VInt n)
| Is_of_type_bool b : is_of_type TBool (VBool b)
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
Variant add_anons : state -> Pmap value -> state -> Prop :=
  | AddAnons S A anons' : union_maps (anons S) A anons' ->
      add_anons S A {|vars := vars S; anons := anons'; abstractions := abstractions S|}
.

Definition get_loan_id c :=
  match c with
  | nloan^m(ty, l) => Some l
  | nborrow^m(l) => Some l
  | _ => None
  end.

Definition is_loan_id l c := get_loan_id c = Some l.
Notation is_fresh l S := (not_state_contains (is_loan_id l) S).
Hint Extern 0 (~is_loan_id _ _) => unfold is_loan_id; cbn; congruence : spath.
Hint Extern 0 (is_loan_id _ _) => reflexivity : spath.

Inductive remove_loans A B : Pmap value -> Pmap value-> Prop :=
  | Remove_nothing : remove_loans A B A B
  | Remove_MutLoan A' B' i j l ty (H : remove_loans A B A' B') :
      lookup i A' = Some (loan^m(ty, l)) ->
      lookup j B' = Some (borrow^m(l, VSymbolic ty)) ->
      remove_loans A B (delete i A') (delete j B')
.

Definition merge_abstractions A B C := exists A0 B0, remove_loans A B A0 B0 /\ union_maps A0 B0 C.

Definition remove_anon a S :=
  {| vars := vars S; anons := delete a (anons S); abstractions := abstractions S|}.

(** * Permutation of LLBC## states. *)
(** A state permutation is a permutation of the anonymous variables and the elemnts of each regions.
    It does not affect the variables. *)

(* First, let us introduce renaming of loan identifiers. *)
Definition loan_id_map := Pmap positive.

Definition rename_loan_id (m : loan_id_map) (l : loan_id) :=
  match lookup l m with
  | Some l' => l'
  | None => l
  end.

Definition rename_node (m : loan_id_map) (n : nodes) :=
  match n with
  | nborrow^m(l) => nborrow^m(rename_loan_id m l)
  | nloan^m(ty, l) => nloan^m(ty, rename_loan_id m l)
  | _ => n
  end.

Fixpoint rename_value (m : loan_id_map) (v : value) :=
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
        exists (i, q). rewrite fst_pair, lookup_insert_eq. assumption.
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
  intros H%insert_delete_id. unfold loan_set_state. rewrite <-H.
  rewrite map_fold_insert_L; [set_solver.. | apply lookup_delete_eq ].
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
  map_Forall2 (fun k => is_permutation (M := Pmap)) (abstractions_perm perm) (abstractions S).

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
    map_zip_with (fun p (A : Pmap _) => apply_permutation p A) (abstractions_perm perm) (abstractions S);
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

Definition equiv_val_state (vS0 vS1 : value * state) :=
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

(** * Properties of LLBC## operations. *)
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
Proof. intros ?. unfold add_abstraction. cbn. f_equal. apply insert_insert_ne. congruence. Qed.

Lemma get_at_accessor_add_abstraction S i j A :
  get_at_accessor (S,,, i |-> A) (encode_abstraction (i, j)) = lookup j A.
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_lookup_r.
  rewrite <-insert_delete_eq, flatten_insert by now simpl_map.
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
  destruct S. cbn. f_equal. apply insert_delete_id in H. exact H.
Qed.

Lemma remove_add_abstraction i A S (H : fresh_abstraction S i) :
  remove_abstraction i (S,,, i |-> A) = S.
Proof.
  unfold add_abstraction, remove_abstraction.
  destruct S. cbn. f_equal. apply delete_insert_id. assumption.
Qed.

Lemma remove_add_abstraction_ne i j A S :
  i <> j -> remove_abstraction i (S,,, j |-> A) = remove_abstraction i S,,, j |-> A.
Proof.
  unfold add_abstraction, remove_abstraction.
  intros ?. destruct S. cbn. f_equal. apply delete_insert_ne. assumption.
Qed.

Lemma add_remove_add_abstraction S i A : (remove_abstraction i S),,, i |-> A = S,,, i |-> A.
Proof. unfold add_abstraction, remove_abstraction. cbn. f_equal. apply insert_delete_eq. Qed.

Lemma get_at_accessor_add_abstraction_notin S i A x (H : ~in_abstraction i x) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN at 2. rewrite <-add_remove_add_abstraction.
    rewrite !_get_at_accessor_add_abstraction_notin; auto; apply lookup_delete_eq.
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
    + rewrite get_map_alter, lookup_alter_eq.
      rewrite !get_at_accessor_add_abstraction_notin by assumption.
      rewrite get_map_alter, lookup_alter_eq. reflexivity.
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
  unfold add_abstraction, encode_abstraction. cbn. rewrite decode'_encode, alter_insert_eq.
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
  - rewrite lookup_flatten. rewrite lookup_alter_eq.
    rewrite option_fmap_bind.
    destruct (decide (j = b)) as [<- | ].
    + rewrite lookup_delete_eq.
      erewrite option_bind_ext_fun by (intros ?; apply lookup_delete_eq).
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
  - rewrite !get_map_remove_abstraction_value. apply delete_delete.
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
  | H : get_node (?S.[?sp]) = nborrow^m(_) |- is_mut_borrow (get_node (?S.[?sp])) =>
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
  (H : get_node (S.[p]) = nborrow^m(l0)) :
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
  get_node (S.[p]) = nborrow^m(l0) -> ~P (nborrow^m(l0)) ->
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
  get_node (S.[p]) = nborrow^m(l0) -> l <> l0 ->
  is_fresh l (rename_mut_borrow S p l1) -> is_fresh l S.
Proof.
  intros get_l0 Hdiff fresh_l q valid_q. destruct (decidable_spath_eq p q) as [<- | ].
  - rewrite get_l0. eauto with spath.
  - specialize (fresh_l q). autorewrite with spath in fresh_l. apply fresh_l.
    erewrite valid_spath_rename_mut_borrow; eassumption.
Qed.

Lemma not_in_borrow_rename_mut_borrow S p q l0 l1 :
  get_node (S.[p]) = nborrow^m(l0) ->
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

(** ** Lemmas about [add_anons]. *)
Lemma add_anons_delete S i A v S' :
  lookup i A = None -> add_anons S (insert i v A) S' ->
  exists a, fresh_anon S a /\ add_anons (S,, a |-> v) A S'.
Proof.
  intros i_fresh H. inversion H as [? ? ? Hunion]; subst.
  apply union_maps_insert_r_l in Hunion; [ | exact i_fresh].
  destruct Hunion as (a & G & fresh_a).
  exists a. unfold fresh_anon. rewrite get_at_anon. split; [assumption | ].
  refine (AddAnons (S,, a |-> v) _ _ G).
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
  intros (a & fresh_a & H)%(add_anons_delete _ i _ v); [ | now simpl_map].
  exists a. split; [assumption | ]. apply add_anons_empty in H. congruence.
Qed.

(* An alternative definition of add_anon. *)
Inductive add_anons' : state -> Pmap value -> state -> Prop :=
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
    rewrite delete_delete. econstructor; simpl_map; eauto.
Qed.

Lemma remove_loans_contains_right A B A' B' i v (H : remove_loans A B A' B') :
  lookup i B' = Some v ->
  lookup i B = Some v /\ remove_loans A (delete i B) A' (delete i B').
Proof.
  induction H.
  - intros ?. split; [assumption | constructor].
  - intros (? & G)%lookup_delete_Some. specialize (IHremove_loans G).
    destruct IHremove_loans as (? & IHremove_loans). split; [assumption | ].
    rewrite delete_delete. econstructor; simpl_map; eauto.
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
    eapply union_maps_delete_l; [rewrite insert_delete_id; eassumption | simpl_map; reflexivity].
  - right. exists j. eapply remove_loans_contains_right in Hremove; [ | eassumption].
    destruct Hremove. split; [assumption | ]. econstructor. eauto.
Qed.

Lemma remove_loans_elem_right A B A' B' i :
  remove_loans A B A' B' ->
  lookup i B = lookup i B' \/
  exists l ty, lookup i B = Some (borrow^m(l, VSymbolic ty)).
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
  apply insert_delete_id. rewrite get_at_anon in H. exact H.
Qed.

Lemma remove_anon_is_fresh S a : fresh_anon (remove_anon a S) a.
Proof. unfold fresh_anon. rewrite get_at_anon. apply lookup_delete_eq. Qed.

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

Lemma vweight_bot weight : vweight weight bot = weight nbot.
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.

Lemma vweight_symbolic weight ty :
  vweight weight (VSymbolic ty) = weight (NSymbolic ty).
Proof. reflexivity. Qed.
Hint Rewrite vweight_symbolic : weight.

Lemma vweight_mut_loan weight ty l : vweight weight loan^m(ty, l) = weight nloan^m(ty, l).
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_loan : weight.

Lemma vweight_mut_borrow weight l v :
  vweight weight borrow^m(l, v) = weight nborrow^m(l) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_borrow : weight.

(* We cannot automatically rewrite map_sum_empty. Is it because of typeclasses?
 * Thus, we crate an alternative. *)
Lemma abstraction_sum_empty (weight : value -> nat) : map_sum weight (M := Pmap) empty = 0.
Proof. apply map_sum_empty. Qed.
Hint Rewrite abstraction_sum_empty : weight.

Lemma abstraction_sum_insert weight i v (A : Pmap value) :
  lookup i A = None -> map_sum weight (insert i v A) = weight v + map_sum weight A.
Proof. apply map_sum_insert. Qed.
Hint Rewrite abstraction_sum_insert using auto : weight.

Lemma abstraction_sum_singleton weight i v :
  map_sum weight (singletonM (M := Pmap value) i v) = weight v.
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
      rewrite !delete_insert_id in H by assumption. exact H.
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
Definition abstraction_set j p v (A : Pmap value) := alter (vset p v) j A.

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
  is_of_type ty v -> not_value_contains (fun c => c = nbot) v.
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
  get_node (v.[[p]]) = nborrow^m(l0) -> is_of_type ty v ->
  is_of_type ty (v.[[p <- borrow^m(l1, v.[[p ++ [0] ]])]]).
Proof.
  intros get_borrow Htype. assert (valid_vpath v p) as H by validity.
  apply valid_vpath_zeroary in H; [ | destruct Htype; reflexivity]. subst.
  cbn in get_borrow. destruct Htype; discriminate.
Qed.

Lemma is_of_type_rename_mut_borrow_val v p l0 l1 ty :
  get_node (v.[[p]]) = nborrow^m(l0) ->
  is_of_type ty (rename_mut_borrow_val v p l1) ->
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
  (get_l0 : get_node (S.[p]) = nborrow^m(l0))
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
  store_compatible_types S p (v.[[q <- VSymbolic ty]]) ->
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

Lemma store_compatible_types_rename_mut_borrow_val S p q v l0 l1 :
  get_node (v.[[q]]) = nborrow^m(l0) ->
  store_compatible_types S p (rename_mut_borrow_val v q l1) ->
  store_compatible_types S p v.
Proof.
  intros get_borrow_q Hcomp r prefix_r_p get_borrow_r.
  specialize (Hcomp r prefix_r_p get_borrow_r).
  destruct Hcomp as (ty' & ? & ?). exists ty'. split; [assumption | ].
  eapply is_of_type_rename_mut_borrow_val; eassumption.
Qed.

Lemma store_compatible_types_rename_mut_borrow S p q v l0 l1 :
  get_node (S.[q]) = nborrow^m(l0) ->
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

(** * Effect of permutation on LLBC## operations. *)
Definition id_state_permutation S := {|
  anons_perm := id_permutation (anons S);
  abstractions_perm := fmap (id_permutation (M := Pmap)) (abstractions S);
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
  abstractions_perm := fmap (id_permutation (M := Pmap)) (abstractions S);
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
  abstractions_perm := fmap (invert_permutation (M := Pmap)) (abstractions_perm perm);
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
    unfold loan_id_map. rewrite dom_invert_permutation, elem_of_map_img by assumption.
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
  - rewrite get_map_rename_state.
    unfold loan_id_map. rewrite compose_invert_permutation by assumption.
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
    + unfold loan_id_map. rewrite compose_invert_permutation by apply Hp.
      symmetry. apply rename_value_id. intros ? ?. apply lookup_id_permutation_is_Some.
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
  - apply insert_delete_id in get_w. unfold loan_set_state, sget. rewrite <-get_w at 1 2.
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
  - apply insert_delete_id in get_w. unfold loan_set_state, sset.
    rewrite get_map_alter. rewrite <-get_w at 1 2. rewrite alter_insert_eq.
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
    + erewrite !alter_alt_Some by (simpl_map; reflexivity).
      rewrite fmap_insert, vset_rename_value. reflexivity.
    + rewrite !alter_id'; simpl_map; rewrite ?EQN; reflexivity.
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
      cbn. rewrite insert_delete_id; easy.
    + unfold fresh_anon. rewrite get_at_anon. cbn.
      replace (anons S) with (delete a (anons (S,, a |-> v))).
      2: { cbn. rewrite delete_insert_id by now rewrite <-get_at_anon. reflexivity. }
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

Definition loan_set_abstraction (A : Pmap value) : Pset :=
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
  map_Forall2 (fun k => is_permutation (M := Pmap)) (abstractions_perm perm) (abstractions S0) ->
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
    2: { cbn. now rewrite delete_insert_id. }
    apply map_Forall2_delete. assumption.
  - assumption.
  - set_solver.
  - specialize (H i). cbn in H. simpl_map. inversion H. eexists. split; [eassumption | split].
    + unfold add_abstraction_perm, remove_abstraction_perm, add_abstraction_accessor_permutation.
      cbn. rewrite insert_delete_id by congruence.
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
    + rewrite delete_id by assumption. exact G.
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
    f_equal. f_equal. rewrite alter_alter_eq. symmetry. apply alter_id.
    rewrite <-get_p. intros ? [=<-]. apply delete_insert_id.
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
    erewrite <-(insert_delete_id A') in IH'; [ | eassumption].
    erewrite <-(insert_delete_id B') in IH'; [ | eassumption].
    erewrite !apply_permutation_insert in IH' by
      (try apply perm_A'; try apply perm_B'; now simpl_map).
    rewrite !delete_insert_id in IH' by assumption.
    eapply Remove_MutLoan with (i := i') (j := j') in IH'; [ | simpl_map; reflexivity..].
    rewrite !delete_insert_id in IH' by auto using lookup_pkmap_None.
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
  unfold add_abstraction, remove_abstraction_value. cbn. f_equal. apply alter_insert_eq.
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
