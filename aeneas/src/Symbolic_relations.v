(** * Mechanized_LLBC.Symbolic_relations : Definition of the abstraction relations for LLBC#. *)
From stdpp Require Import pmap gmap.
Require Import base OptionMonad PathToSubtree SimulationUtils lang Symbolic_states.

(* A version of to-abs that is limited compared to the paper. Currently, we can only turn into a
 * region abstraction a value of the form:
 * - borrow^m l σ (with σ a symbolic value)
 * - borrow^m l0 (loan^m l1)
 * Consequently, a single region abstraction is created.
 *)
Variant to_abs : value -> Pmap value -> Prop :=
| ToAbs_MutReborrow l0 l1 kb kl ty (Hk : kb <> kl) :
    to_abs (borrow^m(l0, loan^m(ty, l1)))
           ({[kb := (borrow^m(l0, VSymbolic ty)); kl := loan^m(ty, l1)]})%stdpp
| ToAbs_MutBorrow l v k ty (Htype : is_of_type ty v)
    (v_no_loan : not_contains_loan v) (v_no_borrow : not_contains_borrow v) :
    to_abs (borrow^m(l, v)) ({[k := (borrow^m(l, VSymbolic ty))]})%stdpp
.

Definition measure S := sweight (fun _ => 1) S + size (abstractions S).
Notation abs_measure S := (map_sum (vweight (fun _ => 1)) S).

Variant leq_state_base_n : nat -> state -> state -> Prop :=
| Leq_ToSymbolic_n S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base_n (vweight (fun _ => 1) (S.[sp])) S (S.[sp <- VSymbolic ty])
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
| Leq_Reborrow_MutBorrow_n (S : state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
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

(* Note: the definition is duplicated in [leq_state_base_n].
 * Perhaps we should only define leq_state_base_n, and define [leq_state_base Sl Sr] as
 * [exists n, leq_state_base_n n Sl Sr]. *)
Variant leq_state_base : state -> state -> Prop :=
(* Contrary to the article, symbolic values should be typed. Thus, only an integer can be converted
 * to a symbolic value for the moment. *)
| Leq_ToSymbolic S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base S (S.[sp <- VSymbolic ty])
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
| Leq_Reborrow_MutBorrow (S : state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
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
    erewrite <-insert_empty, apply_permutation_insert;
      [ | now apply map_inj_delete | simpl_map; reflexivity..].
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
  subseteq (loan_set_val (VSymbolic ty)) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_symbolic_subseteq : spath.

Lemma loan_set_bot_subseteq (perm : loan_id_map) : subseteq (loan_set_val bot) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_bot_subseteq : spath.

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

Definition equiv_val_state_up_to_loan_renaming (vS0 vS1 : value * state) :=
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

(** Derived rules of [leq_state_base]. *)
Lemma Leq_Reborrow_MutBorrow_Abs S sp l0 l1 i kb kl ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_i : fresh_abstraction S i)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
    (Hk : kb <> kl)
    (Htype : is_of_type ty (S.[sp +++ [0] ])):
    leq_state_base^* S (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],,,
                        i |-> {[kb := (borrow^m(l0, VSymbolic ty));
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
                        i |-> {[k := borrow^m(l', VSymbolic ty)]}%stdpp).
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

Lemma leq_uninitialize_value S sp
  (no_loan : not_contains_loan (S.[sp]))
  (no_borrow : not_contains_borrow (S.[sp]))
  (valid_sp : valid_spath S sp)
  (sp_not_in_borrow : not_in_borrow S sp)
  (sp_in_abstraction : not_in_abstraction sp) :
  leq_state_base^* S (S.[sp <- bot]).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity; constructor.
  { apply Leq_MoveValue with (sp := sp) (a := a); try assumption. not_contains_outer. }
  { apply Leq_RemoveAnon; auto with spath. }
Qed.

(** * The simulation relation on branching states. *)
(** A branching state [Br] is more general than a branching state [Bl] if for any token [r], if [Bl] maps a control-flow token [r] to a symbolic state [Sl] ([lookup r Bl = Some Sl]), then [Br] maps [r] to a more general state [Sr] ([lookup r Br = Some Sr] and [leq_symbolic Sl Sr]).

   Note that the domain of [Br] can be bigger than the domain of [Bl]. There can be computations that terminate on a token [r] that are abstracted by [Bl] but not [Br]. *)
Variant leq_option_symbolic : relation (option state) :=
  | LeqNone oSr : leq_option_symbolic None oSr
  | LeqSome Sl Sr : leq_symbolic Sl Sr -> leq_option_symbolic (Some Sl) (Some Sr).

Definition leq_branching (Bl Br : branching_state) :=
  forall r, leq_option_symbolic (lookup r Bl) (lookup r Br).

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

(** In the ICPF article, Ho et al introduce a join operation, described with non-deterministic computation rules. However, we are not interested in an algorithm for joins. The join [Bjoin] of two states [B0] and [B1] can be provided by an oracle, we do not describe the computation rules. We only require two properties.
   - The state [B_join] is an upper bound of [B0] and [B1], that means that we have [leq_branching B0 Bjoin] and [leq_branching Bs Bjoin].
   - If a control-flow token [r] is not in the domain of [Bl] (respectively [Br]), then [lookup r Bjoin = lookup r Br] (respectively [lookup r Bjoin = lookup r Bl]).

   The second condition is here to ensure that LLBC is a stable subset of LLBC#. In particular, the join of a state [B = {[r := S]}] and the empty state can only be [B].
 *)
Variant option_is_join :
  option state -> option state -> option state -> Prop :=
  | UpperBound_None_None : option_is_join None None None
  | UpperBound_Some_None S0 : option_is_join (Some S0) None (Some S0)
  | UpperBound_None_Some S1 : option_is_join None (Some S1) (Some S1)
  | UpperBound_Some_Some S0 S1 S2 : leq_symbolic S0 S2 -> leq_symbolic S1 S2 ->
      option_is_join (Some S0) (Some S1) (Some S2).

Definition is_join (B0 B1 Bjoin : branching_state) :=
  forall r, option_is_join (lookup r B0) (lookup r B1) (lookup r Bjoin).

(** Lemmas about [leq_branching] and [is_join] *)
Lemma leq_singleton S r B :
  match lookup r B with
  | Some Sr => leq_symbolic S Sr
  | None => False
  end ->
  leq_branching {[r := S]} B.
Proof.
  intros H. destruct (lookup r B) as [Sr | ] eqn:get_Sr; [ | contradiction].
  intros r'. destruct (decide (r = r')) as [<- | ]; unfold branching_state in *.
  - simpl_map. constructor. assumption.
  - simpl_map. constructor.
Qed.

Lemma leq_branching_delete r0 Sl Sr :
  leq_branching Sl Sr -> leq_branching (delete r0 Sl) (delete r0 Sr).
Proof.
  intros H r. specialize (H r). unfold branching_state.
  destruct (decide (r0 = r)) as [<- | ]; simpl_map; [constructor | assumption].
Qed.

Lemma leq_is_join_l Bl Br Bjoin : is_join Bl Br Bjoin -> leq_branching Bl Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.
Hint Resolve leq_is_join_l : spath.

Lemma leq_is_join_r Bl Br Bjoin : is_join Bl Br Bjoin -> leq_branching Br Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.
Hint Resolve leq_is_join_r : spath.

(** If [Bup] is an upper bound of two states [B0] and [B1], it is not necessarily a join. Indeed, there may exist tokens [r] such that [lookup r B0] (respectively [lookup r B1]) is None, but [lookup r Bup] is different from [lookup r B1] (respectively [lookup r B0]).

   We need to "compute" a join by choosing for each tag [r] a value among [lookup r B0],  [lookup r B1] and [lookup r Bup]. *)
Definition compute_option_join (oSl oSr : option state) default :=
  match oSl, oSr with
  | None, _ => oSr
  | _, None => oSl
  | _, _ => Some default
  end.

Definition compute_join (B0 B1 Bup : branching_state) : branching_state :=
  map_imap (fun r => compute_option_join (lookup r B0) (lookup r B1)) Bup.

Lemma exists_join_state B0 B1 Bup
  (Hleq_0 : leq_branching B0 Bup) (Hleq_1 : leq_branching B1 Bup) :
  let Bjoin := compute_join B0 B1 Bup in
  is_join B0 B1 Bjoin /\ leq_branching Bjoin Bup.
Proof.
  intros Bjoin. unfold Bjoin. split.
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hleq_0 r). specialize (Hleq_1 r).
    destruct Hleq_0 as [oSr | ]; inversion Hleq_1; subst.
    all: try destruct oSr; constructor; assumption.
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hleq_0 r). specialize (Hleq_1 r).
    unfold compute_option_join.
    destruct Hleq_0 as [oSr | ]; inversion Hleq_1; subst.
    all: try destruct oSr; constructor; assumption || reflexivity.
Qed.
