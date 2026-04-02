(** * Mechanized_LLBC.Simulation_LLBC_sharp_LLBC_plus : Proof of simulation between LLBC# and LLBC+. *)
From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import fin_map_dom.
Require Import base OptionMonad SimulationUtils PathToSubtree lang.
Require Import LLBC_sharp_states LLBC_sharp_relations LLBC_sharp_semantics.

Local Open Scope llbc_sharp_scope.

(** * Simulation proofs for place evaluation. *)
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
  (H : (S.[sp <- LLBC_sharp_symbolic ty]) |-{p} p =>^{perm} pi) :
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
    H : (?S.[?sp <- LLBC_sharp_symbolic ?ty]) |-{p} ?p =>^{?perm} ?pi |- _ =>
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

(** * Simulation proofs for operand evaluation. *)
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
  (Hcopy_val : copy_val (v.[[p <- LLBC_sharp_symbolic ty]]) w) :
  exists w0 q, copy_val v w0 /\ w = w0.[[q <- LLBC_sharp_symbolic ty]] /\
               is_of_type ty (w0.[[q]]).
Proof.
  remember (v.[[p <- LLBC_sharp_symbolic ty]]) eqn:EQN. induction Hcopy_val.
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

Lemma operand_preserves_LLBC_sharp_rel op :
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
      (* TODO: time wasted by the rule `sget_reborrow_mut_borrow_not_prefix`. *)
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
  - apply operand_preserves_LLBC_sharp_rel.
Qed.

(** * Simulation proofs for rvalue evaluation. *)
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
  (is_of_type intT vl /\ not_contains_loan vl /\ vr = LLBC_sharp_symbolic intT /\ Sl = Sr).
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

Definition leq_integer_state (vSl vSr : LLBC_sharp_val * LLBC_sharp_state) :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  (vl = vr \/ is_of_type intT vl /\ not_contains_loan vl /\ vr = LLBC_sharp_symbolic intT) /\ leq_state_base^* Sl Sr.

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

Lemma rvalue_preserves_LLBC_sharp_rel rv :
  forward_simulation leq_state_base^* leq_val_state_ut (eval_rvalue rv) (eval_rvalue rv).
Proof.
  apply preservation_by_base_case.
  intros Sr vSr eval_rv Sl Hleq. destruct eval_rv.
  - apply operand_preserves_LLBC_sharp_rel in Heval_op.
    edestruct Heval_op as (vS'l & ? & ?); [constructor; eassumption | ].
    exists vS'l. split.
    + eexists. split; [reflexivity | assumption].
    + constructor. assumption.

  - apply operand_preserves_LLBC_sharp_rel in eval_op_0, eval_op_1.
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
        replace w with (LLBC_sharp_symbolic intT) by now inversion Hbinop.
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
        replace w with (LLBC_sharp_symbolic intT) by now inversion Hbinop.
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
        replace w with (LLBC_sharp_symbolic intT) by now inversion Hbinop.
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
        replace w with (LLBC_sharp_symbolic boolT) by now inversion Hbinop.
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
        replace w with (LLBC_sharp_symbolic boolT) by now inversion Hbinop.
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
        replace w with (LLBC_sharp_symbolic boolT) by now inversion Hbinop.
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
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.
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
  eapply rvalue_preserves_LLBC_sharp_rel in eval_rv.
  specialize (eval_rv S1 leq_S1_S0). destruct eval_rv as (vS'1 & leq_S'1_S'0 & eval_rv).
  eapply rvalue_preserves_equiv in eval_rv.
  specialize (eval_rv S2 equiv_S2_S1). destruct eval_rv as (vS'2 & equiv_S'2_S'1 & eval_rv).
  exists vS'2. split; [ | exact eval_rv].
  destruct leq_S'1_S'0 as (vS''1 & ? & ?). exists vS''1. split; [ | assumption].
  etransitivity; [eassumption | ].
  apply equiv_val_state_up_to_loan_renaming_implies_equiv_val_state. assumption.
Qed.

(** * Simulation proofs for the [store] operation. *)
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
    + assert (disj sp_store sp) by solve_comp.
      leq_step_left.
      { eapply Leq_Fresh_MutLoan with (a := a) (sp := sp) (l' := l').
        not_contains. eauto with spath. validity. assumption.
        autorewrite with spath. eassumption. }
      states_eq.

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

Lemma store_preserves_LLBC_sharp_rel p vr Sr S'r vl Sl :
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

(** * Simulation proofs for reorganizations. *)
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
  unfold abstractions, remove_abstraction_value. destruct S as [? ? abs]. cbn.
  destruct (lookup i abs) eqn:H.
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

Inductive add_anonymous_bots : nat -> LLBC_sharp_state -> LLBC_sharp_state -> Prop :=
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

(* Note: this could be made into a tactic. *)
Lemma prove_add_anons S0 A S1 :
  (exists S', add_anons S' A S1 /\ S0 = S') -> add_anons S0 A S1.
Proof. intros (? & ? & ->). assumption. Qed.

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
        (* Issues with rewrite sget_anon, and hints like [valid_spath_diff_fresh_anon] *)
          (* TODO: long. *) autorewrite with spath.
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

(** * Simulation proofs for statement evaluation. *)
Lemma leq_singleton r Sl Sr : leq_symbolic Sl Sr -> leq_branching {[r := Sl]} {[r := Sr]}.
Proof.
  intros H r'. destruct (decide (r = r')) as [<- | ].
  - simpl_map. constructor. assumption.
  - unfold branching_state. simpl_map. constructor.
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
Definition compute_option_join (oSl oSr : option LLBC_sharp_state) default :=
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

(** The LLBC+ rules [LLBC_plus_E_Seq_Unit_Propagate], [LLBC_plus_IfThenElse_Symbolic] and [LLBC_plus_E_Loop_Continue] require exhibiting a "join state" of two states [B0] and [B1]. Square diagrams that involve these rules are tricky, because it is required to prove that the states [B0] and [B1] are related to the final state [Br], but these states are only determined at the execution of the rule.

   This tactic simplifies these square diagrams. It operates like this:
   - The states [B0] and [B1] to join are introduced as existential variables.
   - First, we prove the execution statement. We assume the hypothesis [is_join ?B0 ?B1 B]. Using this as an assumption determines the terms [B0] and [B1].
   - Finally, we only have to prove that [B0] and [B1] are related to [Br]. *)
(* TODO: lemma and tactic names. *)
Lemma execution_join_state n s Sl (B0 B1 Br : branching_state) :
  (forall B, is_join B0 B1 B -> Sl |-{stmt} s ~>{n} B) ->
  leq_branching B0 Br ->
  leq_branching B1 Br ->
  exists Bl, leq_branching Bl Br /\ Sl |-{stmt} s ~>{n} Bl.
Proof.
  intros G leq_0 leq_1. destruct (exists_join_state _ _ _ leq_0 leq_1) as (? & ?).
  exists (compute_join B0 B1 Br). auto.
Qed.
Ltac execution_join_state :=
  let Bjoin_l := fresh "Bjoin_l" in
  let Hjoin_l := fresh "Hjoin_l" in
  eapply execution_join_state; [intros Bjoin_l Hjoin_l | | ].

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
Definition leq_boolean_state leq (vSl vSr : LLBC_sharp_val * LLBC_sharp_state) :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  (vl = vr \/ is_of_type boolT vl /\ not_contains_loan vl /\ vr = LLBC_sharp_symbolic boolT) /\
  leq Sl Sr.

Lemma boolean_zeroary v :
  not_contains_loan v -> is_of_type boolT v -> arity (get_node v) = 0.
Proof. intros ? H. inversion H; reflexivity. Qed.

Lemma leq_val_state_base_boolean vl Sl vr Sr :
  leq_val_state_base leq_state_base (vl, Sl) (vr, Sr) ->
  is_of_type boolT vr -> not_contains_loan vr ->
  (vl = vr /\ leq_state_base Sl Sr) \/
  (is_of_type boolT vl /\ not_contains_loan vl /\ vr = LLBC_sharp_symbolic boolT /\ Sl = Sr).
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
  leq_val_state (vl, Sl) (LLBC_sharp_bool b, Sr) -> vl = LLBC_sharp_bool b /\ leq_symbolic Sl Sr.
Proof.
  intros (Hvl & Hleq)%leq_val_state_boolean.
  - split; [ | exact Hleq]. destruct Hvl as [ | (_ & _ & [=])]. assumption.
  - constructor.
  - not_contains.
Qed.

Lemma leq_val_state_symbolic_boolean vl Sl Sr :
  leq_val_state (vl, Sl) (LLBC_sharp_symbolic boolT, Sr) ->
  ((exists b, vl = LLBC_sharp_bool b) \/ vl = LLBC_sharp_symbolic boolT) /\ leq_symbolic Sl Sr.
Proof.
  intros (Hvl & Hleq)%leq_val_state_boolean.
  - split; [ | exact Hleq]. destruct Hvl as [ | (Htype & no_loan & _)]; auto.
    inversion Htype; subst; eauto. exfalso. eapply no_loan; constructor.
  - constructor.
  - not_contains.
Qed.

Lemma leq_end_loop Bl Br : leq_branching Bl Br -> leq_branching (end_loop Bl) (end_loop Br).
Proof.
  intros H r. destruct (lookup r (end_loop Bl)) eqn:EQN.
  - pose proof EQN as G.
    apply mk_is_Some, lookup_pkmap_rev in G; [ | exact partial_inj_end_loop_tag].
    destruct G as (r0 & get_r).
    unfold end_loop, branching_state in *.
    erewrite lookup_pkmap in EQN |- * by exact get_r || exact partial_inj_end_loop_tag.
    specialize (H r0). unfold branching_state in H. rewrite EQN in H.
    inversion H. constructor. assumption.
  - constructor.
Qed.
Hint Resolve leq_end_loop : spath.

Lemma leq_branching_None_left_branch Bl Br r :
  leq_branching Bl Br -> lookup r Br = None -> lookup r Bl = None.
Proof.
  intros Hleq G. specialize (Hleq r). rewrite G in Hleq. inversion Hleq. reflexivity.
Qed.
Hint Resolve leq_branching_None_left_branch : spath.

Lemma lookup_token_cases Bl Br Sr r :
  leq_branching Bl Br -> lookup r Br = Some Sr ->
  (lookup r Bl = None /\ leq_branching Bl (delete r Br) \/
   exists Sl, lookup r Bl = Some Sl /\
              leq_symbolic Sl Sr /\ leq_branching (delete r Bl) (delete r Br)).
Proof.
  intros Hleq_B Hcontinue.
  pose proof (Hleq_B r) as Hleq_S. apply (leq_branching_delete r) in Hleq_B.
  rewrite Hcontinue in Hleq_S.
  destruct (lookup r Bl) as [Sl | ] eqn:EQN.
  - inversion Hleq_S; subst. eauto.
  - rewrite (delete_notin _ _ EQN) in Hleq_B. auto.
Qed.

Lemma stmt_preserves_LLBC_sharp_rel n s :
  forward_simulation leq_symbolic leq_branching
                     (LLBC_plus_eval_stmt n s) (LLBC_plus_eval_stmt n s).
Proof.
  intros Sr S'r Heval. induction Heval; intros Sl Hleq.
  (* Case [LLBC_plus_E_Step_Zero] *)
  - execution_step. { constructor. } reflexivity.

  (* Case [LLBC_plus_E_Nop]. *)
  - execution_step. { constructor. }
    apply leq_singleton. assumption.

  (* Case [LLBC_plus_E_Propagate] *)
  - specialize (IHHeval _ Hleq). destruct IHHeval as (Bl & ? & ?).
    execution_step.
    { apply LLBC_plus_E_Seq_Propagate; eauto with spath. }
    assumption.

  (* Case [LLBC_plus_E_Seq_Unit_Propagate] *)
  - specialize (IHHeval1 _ Hleq). destruct IHHeval1 as (B1l & Hleq1 & ?).
    eapply lookup_token_cases in Hleq1; [ | exact H_unit].
    destruct Hleq1 as [(? & ?) | (S1l & ? & Hleq1 & ?)].
    (* Case 1: the state after the execution of the first statement ([B1_l]) does not contain
        a [rUnit] token, we simply propagate. *)
    + execution_step. { apply LLBC_plus_E_Seq_Propagate; eassumption. }
      etransitivity; eauto with spath.
    (* Case 2. *)
    + specialize (IHHeval2 _ Hleq1). destruct IHHeval2 as (B_unit_l & Hleq2 & Heval2_l).
      execution_join_state.
      { eapply LLBC_plus_E_Seq_Unit_Propagate; eassumption. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }

  (* Case [LLBC_plus_E_Assign] *)
  - destruct vS' as (vr & S'r).
    assert (not_contains_bot vr). { eapply eval_rvalue_no_bot. eassumption. }
    assert (not_contains_loan vr). { eapply eval_rvalue_no_loan. eassumption. }
    apply rvalue_preserves_leq in eval_rv. specialize (eval_rv _ Hleq).
    destruct eval_rv as ((v'l & S'l) & ? & ?).
    eapply store_preserves_LLBC_sharp_rel in Hstore; [ | eassumption..].
    destruct Hstore as (S''l & Hstore & ?).
    execution_step. { econstructor; eassumption. }
    apply leq_singleton. assumption.

  (* Case [LLBC_plus_E_IfThenElse_T] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_concrete_boolean in Hleq'. destruct Hleq' as (-> & Hleq').
    apply IHHeval in Hleq'. destruct Hleq' as (S''l & Hleq'' & eval_if).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [LLBC_plus_E_IfThenElse_F] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_concrete_boolean in Hleq'. destruct Hleq' as (-> & Hleq').
    apply IHHeval in Hleq'. destruct Hleq' as (S''l & Hleq'' & eval_else).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [LLBC_plus_IfThenElse_Symbolic] *)
  - apply operand_preserves_leq in eval_cond. apply eval_cond in Hleq.
    destruct Hleq as ((v' & S'l) & Hleq' & eval_cond').
    apply leq_val_state_symbolic_boolean in Hleq'.
    destruct Hleq' as ([([ | ] & ->) | ->] & Hleq').
    (* Case 1: the symbolic value abstracts the boolean true. We apply the rule [LLBC_plus_E_IfThenElse_T]. *)
    + apply IHHeval1 in Hleq'. destruct Hleq' as (B''l & Hleq'' & eval_if).
      execution_step. { econstructor; eassumption. }
      transitivity B_if; eauto using leq_is_join_l.
    (* Case 2: the symbolic value abstracts the boolean false. We apply the rule [LLBC_plus_E_IfThenElse_F]. *)
    + apply IHHeval2 in Hleq'. destruct Hleq' as (B''l & Hleq'' & eval_else).
      execution_step. { econstructor; eassumption. }
      transitivity B_else; eauto using leq_is_join_r.
    (* Case 3: the symbolic value abstracts a symbolic value. *)
    + specialize (IHHeval1 _ Hleq'). destruct IHHeval1 as (Bl_if & Hleq'_l & eval_if).
      specialize (IHHeval2 _ Hleq'). destruct IHHeval2 as (Bl_else & Hleq'_r & eval_else).
      execution_join_state.
      { eapply LLBC_plus_IfThenElse_Symbolic; eassumption. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }

  (* Case [LLBC_plus_E_Reorg] *)
  - eapply reorg_preservation in Hreorg. specialize (Hreorg _ Hleq).
    destruct Hreorg as (S'l & Hleq' & ?).
    specialize (IHHeval _ Hleq'). destruct IHHeval as (? & ? & ?).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [LLBC_plus_E_Loop_Stop] *)
  - apply IHHeval in Hleq. destruct Hleq as (B1l & Hleq' & Heval').
    execution_step.
    { apply LLBC_plus_E_Loop_Stop; eauto with spath. }
    auto with spath.

  (* Case [LLBC_plus_E_Loop_Continue] *)
  - apply IHHeval1 in Hleq. destruct Hleq as (B1_l & Hleq' & Heval').
    eapply lookup_token_cases in Hcontinue; [ | exact Hleq'].
    destruct Hcontinue as [(? & ?) | (S1_l & ? & Hleq_S1 & ?)].
    + execution_step.
      { eapply LLBC_plus_E_Loop_Stop; eauto with spath. }
      etransitivity; eauto with spath.
    + apply IHHeval2 in Hleq_S1. destruct Hleq_S1 as (B2_l & Hleq'' & Heval2_l).
      execution_join_state.
      { eapply LLBC_plus_E_Loop_Continue; eauto with spath. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }
Qed.

Lemma simulation_LLBC_sharp_LLBC_plus n s :
  forward_simulation eq leq_branching (LLBC_sharp_eval_stmt s) (LLBC_plus_eval_stmt n s).
Proof.
  intros Sr Br eval_Sr ? ->. revert s Sr Br eval_Sr. induction n as [ | n IHn]; intros.
  - execution_step. { apply LLBC_plus_E_Step_Zero. }
    intros r. unfold branching_state. simpl_map. constructor.
  - induction eval_Sr.
    (* Case [LLBC_sharp_E_Nop] *)
    + execution_step. { constructor. } reflexivity.
    (* Case [LLBC_sharp_E_Seq_Unit_Propagate] *)
    + destruct IHeval_Sr as (Bl & ? & ?).
      execution_step. { eapply LLBC_plus_E_Seq_Propagate; eauto with spath. }
      assumption.
    (* Case [LLBC_sharp_E_Seq_Unit_Propagate] *)
    + destruct IHeval_Sr1 as (B1_l & Hleq_B1 & ?).
      destruct IHeval_Sr2 as (B2_m & Hleq_B2 & ?).
      eapply lookup_token_cases in Hleq_B1; [ | exact H_unit].
      destruct Hleq_B1 as [(? & ?) | (S1_l & ? & Hleq_S1 & ?)].
      * execution_step. { apply LLBC_plus_E_Seq_Propagate; eassumption. }
        etransitivity; eassumption.
      * eapply stmt_preserves_LLBC_sharp_rel in Hleq_S1; [ | eassumption].
        destruct Hleq_S1 as (B2_l & ? & ?).
        execution_join_state.
        { eapply LLBC_plus_E_Seq_Unit_Propagate; eassumption. }
        { transitivity B2_m; assumption. }
        { etransitivity; eauto with spath. }
    (* Case [LLBC_sharp_E_Assign] *)
    + execution_step. { econstructor; eassumption. } reflexivity.
    (* Case [LLBC_sharp_E_IfThenElse_T] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus_E_IfThenElse_T; eassumption. } assumption.
    (* Case [LLBC_sharp_E_IfThenElse_F] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus_E_IfThenElse_F; eassumption. } assumption.
    (* Case [LLBC_sharp_IfThenElse_Symbolic] *)
    + destruct IHeval_Sr1 as (B_if & ? & ?). destruct IHeval_Sr2 as (B_else & ? & ?).
      execution_join_state.
      { eapply LLBC_plus_IfThenElse_Symbolic; eassumption. }
      { assumption. }
      { assumption. }
    (* Case [LLBC_sharp_E_Reorg] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus_E_Reorg; eassumption. } assumption.
    (* Case [LLBC_sharp_E_Loop_Stop] *)
    + destruct IHeval_Sr as (? & ? & ?).
      execution_step. { eapply LLBC_plus_E_Loop_Stop; eauto with spath. } auto with spath.
    (* Case [LLBC_sharp_E_Loop_Continue] *)
    + destruct IHeval_Sr1 as (B1_l & leq_B1 & ?). clear IHeval_Sr2.
      destruct (lookup_token_cases _ _ _ rContinue leq_B1 Hcontinue)
        as [(? & ?) | (S1_l & ? & leq_S1 & leq_B1')].
      * execution_step. { apply LLBC_plus_E_Loop_Stop; eauto with spath. }
        etransitivity; eauto with spath.
      * eapply LLBC_sharp_Weaken_Precondition in eval_Sr2; [ | exact leq_S1].
        apply IHn in eval_Sr2. destruct eval_Sr2 as (B2_l & ? & ?).
        execution_join_state.
        { eapply LLBC_plus_E_Loop_Continue; eauto with spath. }
        { etransitivity; eauto with spath. }
        { assumption. }

    (* Case [LLBC_sharp_E_Loop_Invariant]: *)
    + destruct IHeval_Sr as (B1 & leq_B1 & eval_to_B1).
      edestruct (lookup_token_cases _ _ _ rContinue leq_B1 inv_preservation)
        as [(? & ?) | (S1 & ? & leq_S1 & leq_B1')].
      * execution_step. { apply LLBC_plus_E_Loop_Stop; eauto with spath. }
        apply leq_end_loop. assumption.
      * assert (S1 |-# LOOP {{ body }} ~> (end_loop (delete rContinue Binv))) as eval_S1.
        { eapply LLBC_sharp_Weaken_Precondition; [exact leq_S1 | ].
          apply LLBC_sharp_E_Loop_Invariant; assumption. }
        apply IHn in eval_S1. destruct eval_S1 as (B2 & leq_B2 & eval_to_B2).
        execution_join_state.
        { eapply LLBC_plus_E_Loop_Continue; eauto with spath. }
        { auto with spath. }
        { assumption. }

    (* Case [LLBC_sharp_Weaken_Precondition]: *)
    + destruct IHeval_Sr as (? & ? & ?).
      eapply stmt_preserves_LLBC_sharp_rel in Hweaken; [ | eassumption].
      destruct Hweaken as (? & ? & ?).
      execution_step. { eassumption. } etransitivity; eassumption.
    (* Case [LLBC_sharp_Weaken_Postcondition]: *)
    + destruct IHeval_Sr as (B & Hleq_B & ?).
      execution_step. { eassumption. } transitivity Bl; assumption.
Qed.
