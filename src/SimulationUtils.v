(* TODO: documentation. *)
Require Import RelationClasses.
Require Import PathToSubtree.
From Stdlib Require Import Arith.
From Stdlib Require Import Relations.
From Stdlib Require Import Lia.

Arguments clos_refl_trans {_}.

(* TODO: give a scope. *)
Global Notation "R ^*" := (clos_refl_trans R).

Lemma clos_refl_trans_ind_left' A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, R^* a b -> P a b -> R b c -> P a c) :
  forall a b, R^* a b -> P a b.
Proof. intros ? b. revert b. eapply clos_refl_trans_ind_left; eauto. Qed.

Lemma clos_refl_trans_ind_right' A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, R a b -> R^* b c -> P b c -> P a c) :
  forall a b, R^* a b -> P a b.
Proof. intros ? b. eapply clos_refl_trans_ind_right with (P := fun a => P a b); eauto. Qed.

Global Instance clos_refl_trans_refl A (R : relation A) : Reflexive R^*.
Proof. intros ?. apply rt_refl. Qed.

Global Instance clos_refl_trans_trans A (R : relation A) : Transitive R^*.
Proof. intros ?. apply rt_trans. Qed.

Inductive measured_closure {A : Type} (R : nat -> A -> A -> Prop) : nat -> A -> A -> Prop :=
  | MC_base n x y : R n x y -> measured_closure R n x y
  | MC_refl n x : measured_closure R n x x
  | MC_trans m n x y z :
      measured_closure R m x y -> measured_closure R n y z -> measured_closure R (m + n) x z
.

(* Now let's assume that a relation <_n is equipped with an integer measure.
 * We can define a reflexive-transitive closure that takes the measure into account. *)
Notation "R ^{ n }" := (measured_closure R n).

Global Instance measured_closure_refl A R n : Reflexive (@measured_closure A R n).
Proof. intros ?. apply MC_refl. Qed.

Lemma measured_closure_over_approx {A} R m n x y :
  m <= n -> R^{m} x y -> (@measured_closure A R n x y).
Proof.
  intros ? ?. replace n with (m + (n - m)); [ | lia]. eapply MC_trans.
  - eassumption.
  - reflexivity.
Qed.

Definition equiv_rel {A B} (R0 R1 : A -> B -> Prop) := forall a b, R0 a b <-> R1 a b.

Local Instance equiv_rel_refl A B : Reflexive (@equiv_rel A B).
Proof. intros R a b. reflexivity. Qed.

Lemma measured_closure_equiv A R Rn (H : forall x y : A, R x y <-> exists n, Rn n x y) :
  forall x y, R^* x y <-> exists n, measured_closure Rn n x y.
Proof.
  intros x y. split.
  - induction 1 as [x y | | x y z ? IH0 ? IH1].
    + destruct (H x y) as ((n & ?) & _); [assumption | ]. exists n. constructor. assumption.
    + exists 0. reflexivity.
    + destruct IH0 as (m & ?). destruct IH1 as (n & ?). exists (m + n).
      eapply MC_trans; eassumption.
  - intros (n & G). induction G.
    + constructor. firstorder.
    + reflexivity.
    + etransitivity; eassumption.
Qed.

(* TODO: name *)
Lemma measure_closure_cases {A} (R : nat -> A -> A -> Prop) n x z :
  R^{n} x z -> x = z \/ exists p q y, R^{p} x y /\ R q y z /\ p + q <= n.
Proof.
  induction 1 as [n x z | | m n x y z ? IH0 ? IH1].
  - right. exists 0, n, x. auto using MC_refl.
  - auto.
  - destruct IH1 as [-> | (p & q & y' & ? & ? & ?)].
    + destruct IH0 as [ | (p & q & y & ? & ? & ?)]; [auto | ].
      right. exists p, q, y. repeat split; try assumption. lia.
    + right. eexists _, _, y'. repeat split; [ | eassumption | ].
      * eapply MC_trans; eassumption.
      * lia.
Qed.

(** Chaining two relations. *)
Definition chain {A B C} (RAB : A -> B -> Prop) (RBC : B -> C -> Prop) a c :=
  exists b, RAB a b /\ RBC b c.

Global Instance reflexive_chain {A} (R S : relation A) `{Reflexive A R} `{Reflexive A S} :
  Reflexive (chain R S).
Proof. intros x. exists x. split; reflexivity. Qed.

(** The general definition of forward simulation. That means that for all [a >= b] (with
    [a : A] and [b : B]) and [a -> c] (with [c : C]), then there exists [d : D] that completes
    the following square diagram:
    b <= a
    |    |
    v    v
    d <= c
    If [A = B] and [C = D], we call it "preservation".

    Genarally,
    - The Leq relations is between states ([S <= S']), or pairs of value and state ([(v, S) <= (v', S')]).
    - The Red relations are among the following ones:
      - Evaluation of operands.
      - Evalutaion of rvalues.
      - Store operation.
      - Reorganization.
      - Evaluation of statements.
 *)
Definition forward_simulation {A B C D : Type}
  (LeqBA : B -> A -> Prop) (LeqDC : D -> C -> Prop)
  (RedAC : A -> C -> Prop) (RedBD : B -> D -> Prop) :=
  forall a c, RedAC a c -> forall b, LeqBA b a -> exists d, LeqDC d c /\ RedBD b d.

Lemma prove_execution_step {B C D : Type}
  (LeqDC : D -> C -> Prop) (RedBD : B -> D -> Prop) Sl S'l S'r :
  RedBD Sl S'l -> LeqDC S'l S'r
  -> exists S'l, LeqDC S'l S'r /\ RedBD Sl S'l.
Proof. exists S'l. split; assumption. Qed.

Ltac execution_step := eapply prove_execution_step.

(** Generally, to prove preservation when the relation is a reflexive transitive closure, it
    suffices to prove it for the base cases. *)
Lemma preservation_by_base_case {A B : Type}
  {LeqA : relation A} {LeqB : relation B} `{Reflexive _ LeqB} `{Transitive _ LeqB}
  {Red : A -> B -> Prop} :
  forward_simulation LeqA LeqB Red Red ->
  forward_simulation LeqA^* LeqB Red Red.
Proof.
  intros Hloc a b red_ab a' Leq_a_a'. revert b red_ab.
  induction Leq_a_a' as [ | | a2 a1 a0 _ IH0 _ IH1].
  - intros. eapply Hloc; eassumption.
  - intros. eexists. split; [reflexivity | eassumption].
  - intros b0 Red_a0_b0.
    destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
    destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
    exists b2. split; [ | assumption]. transitivity b1; assumption.
Qed.

(* TODO: define an equivalence between relations? *)
Lemma forward_simulation_chain {S0 S1} (R0l R0r : S0 -> S0 -> Prop) (R1l R1r : S1 -> S1 -> Prop)
  (red : S0 -> S1 -> Prop) :
  forward_simulation R0l R1l red red -> forward_simulation R0r R1r red red ->
  forward_simulation (chain R0l R0r) (chain R1l R1r) red red.
Proof.
  intros Sim_l Sim_r Sr S'r red_Sr_S'r Sl (Sm & R_Sl_Sm & R_Sm_Sr).
  specialize (Sim_r _ _ red_Sr_S'r _ R_Sm_Sr). destruct Sim_r as (S'm & R_S'm_S'r & red_Sm_S'm).
  specialize (Sim_l _ _ red_Sm_S'm _ R_Sl_Sm). destruct Sim_l as (S'l & R_S'l_S'm & red_Sl_S'l).
  exists S'l. split; [ | assumption]. exists S'm. split; assumption.
Qed.

Section LeqValStateUtils.
  Context `{State state V}.
  Context (leq_base : state -> state -> Prop).

  Definition leq_val_state_base (vSl vSr : V * state) :=
    forall a, fresh_anon (snd vSl) a -> fresh_anon (snd vSr) a ->
    leq_base ((snd vSl),, a |-> fst vSl) ((snd vSr),, a |-> fst vSr).

  (* The following two lemmas are used by the tactic `leq_val_state_step`. *)
  Lemma prove_leq_val_state_right_to_left vSl vm Sm vr Sr
    (G : forall a, fresh_anon Sr a ->
         exists vSm, leq_base vSm (Sr,, a |-> vr) /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* vSl (vm, Sm) ->
    leq_val_state_base^* vSl (vr, Sr).
  Proof.
    intros ?. eapply rt_trans; [eassumption | ]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
  Qed.

  Lemma prove_leq_val_state_left_to_right vl Sl vm Sm vSr
    (G : forall a, fresh_anon Sl a ->
         exists vSm, leq_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* (vm, Sm) vSr ->
    leq_val_state_base^* (vl, Sl) vSr.
  Proof.
    intros ?. eapply rt_trans; [ | eassumption]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
  Qed.

  Lemma prove_leq_val_state_anon_left vl Sl vm Sm vSr b w
    (fresh_b : fresh_anon Sl b)
    (G : forall a, fresh_anon Sl a -> fresh_anon (Sl,, a |-> vl) b ->
         exists vSm, leq_base (Sl,, a |-> vl,, b |-> w) vSm /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* (vm, Sm) vSr ->
    leq_val_state_base^* (vl, Sl,, b |-> w) vSr.
  Proof.
    intros ?. eapply rt_trans; [ | eassumption]. constructor.
    intros a (? & ?)%fresh_anon_add_anon ?. cbn in *.
    rewrite add_anon_commute by congruence.
    destruct (G a) as (? & ? & ->); try assumption. rewrite fresh_anon_add_anon. auto.
  Qed.

  (* This lemma is used by the tactic `leq_val_state_add_anon`. *)
  Lemma prove_leq_val_state_add_anon vl Sl vm Sm vSr b w
    (fresh_b : fresh_anon Sl b)
    (G : forall a, fresh_anon Sl a -> fresh_anon (Sl,, a |-> vl) b ->
         exists vSm, leq_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm,, b |-> w) :
    leq_val_state_base^* (vm, Sm,, b |-> w) vSr ->
    leq_val_state_base^* (vl, Sl) vSr.
  Proof.
    intros ?. eapply rt_trans; [ | eassumption]. constructor.
    intros a ? (? & ?)%fresh_anon_add_anon. cbn in *.
    rewrite add_anon_commute by congruence.
    destruct (G a) as (? & ? & ->); try assumption.
    now apply fresh_anon_add_anon.
  Qed.
End LeqValStateUtils.

Lemma leq_step_right {S} {R : relation S} Sl Sm Sr : R Sm Sr -> R^* Sl Sm -> R^* Sl Sr.
Proof. intros. transitivity Sm; [ | constructor]; assumption. Qed.

Lemma leq_step_left {S} {R : relation S} Sl Sm Sr : R Sl Sm -> R^* Sm Sr -> R^* Sl Sr.
Proof. intros. transitivity Sm; [constructor | ]; assumption. Qed.

(** Tactics to prove commutation of reorganizations. *)
(* TODO: document it *)
Lemma prove_reorg_step {S} {reorg leq : relation S} S0 S1 Sr:
  reorg S0 S1 -> (exists Sl, leq Sl Sr /\ reorg^* S1 Sl) ->
  exists Sl, leq Sl Sr /\ reorg^* S0 Sl.
Proof.
  intros ? (Sl & ? & ?). exists Sl. split; [assumption | ].
  etransitivity; [constructor | ]; eassumption.
Qed.

Lemma prove_reorg_steps {S} {reorg leq : relation S} S0 S1 Sr:
  reorg^* S0 S1 -> (exists Sl, leq Sl Sr /\ reorg^* S1 Sl) ->
  exists Sl, leq Sl Sr /\ reorg^* S0 Sl.
Proof.
  intros ? (Sl & ? & ?). exists Sl. split; [assumption | ].
  etransitivity; eassumption.
Qed.

Ltac reorg_step := eapply prove_reorg_step.
Ltac reorg_steps := eapply prove_reorg_steps.
Ltac reorg_done := eexists; split; [ | reflexivity].

Section Leq.
  Context {state : Type}.
  Context {equiv : state -> state -> Prop}.
  Context `{Reflexive _ equiv}.
  Context `{Transitive _ equiv}.
  Context (leq_base : state -> state -> Prop).
  Context (sim_leq_base_equiv : forward_simulation leq_base leq_base equiv equiv).

  Definition leq := chain equiv leq_base^*.

  Global Instance reflexive_leq : Reflexive leq.
  Proof. intros x. exists x. split; reflexivity. Qed.

  Lemma sim_leq_equiv : forward_simulation leq_base^* leq_base^* equiv equiv.
  Proof.
    intros a b red_ab a' Leq_a_a'. revert b red_ab.
    induction Leq_a_a' as [? ? Leq_a_a' | | a2 a1 a0 _ IH0 _ IH1].
    - intros. specialize (sim_leq_base_equiv _ _ red_ab _ Leq_a_a').
      destruct sim_leq_base_equiv as (d & ? & ?). exists d. split; [constructor | ]; assumption.
    - intros. eexists. split; [reflexivity | eassumption].
    - intros b0 Red_a0_b0.
      destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
      destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
      exists b2. split; [ | assumption]. transitivity b1; assumption.
  Qed.

  Global Instance transitive_leq : Transitive leq.
  Proof.
    intros x y z (y' & ? & leq_y'_y) (z' & equiv_y_z' & ?).
    pose proof (sim_leq_equiv _ _ equiv_y_z' _ leq_y'_y) as G.
    destruct G as (z'' & ? & ?). exists z''. split.
    - transitivity y'; assumption.
    - transitivity z'; assumption.
  Qed.

  Context (reorg : state -> state -> Prop).
  Context (measure : state -> nat).
  Context (leq_base_n : nat -> state -> state -> Prop).
  Definition leq_n n := chain equiv (measured_closure leq_base_n n).

  Hypothesis (leq_decreasing : forall n a b, leq_base_n n a b -> measure a < measure b + n).
  Hypothesis (reorg_decreasing : forall a b, reorg a b -> measure b < measure a).

  Lemma leq_clos_decreasing : forall S S', reorg^* S S' -> measure S' <= measure S.
  Proof. intros ? ? Hreorg. induction Hreorg; eauto using Nat.lt_le_incl, Nat.le_trans. Qed.

  Hypothesis (reorg_preserves_equiv : forward_simulation equiv equiv reorg reorg).
  Lemma reorgs_preserve_equiv : forward_simulation equiv equiv reorg^* reorg^*.
  Proof.
  intros a b. induction 1 as [? ? Hreorg | | a0 a1 a2 _ IH0 _ IH1].
  - intros ? Hequiv. specialize (reorg_preserves_equiv _ _ Hreorg _ Hequiv).
    destruct reorg_preserves_equiv as (d & ? & ?). exists d.
    split; [ | constructor]; assumption.
  - intros. eexists. split; [ | reflexivity]. assumption.
  - intros b0 equiv_b0_a0.
    destruct (IH0 _ equiv_b0_a0) as (b1 & Red_b1_a1 & ?).
    destruct (IH1 _ Red_b1_a1) as (b2 & Red_b2_a1 & ?).
    exists b2. split; [assumption | ]. transitivity b1; assumption.
  Qed.

  Context (sim_equiv_leq_base_n :
    forall n, forward_simulation (leq_base_n n) (leq_base_n n) equiv equiv).

  Lemma leq_n_cases n Sl Sr (G : leq_n n Sl Sr) :
    (equiv Sl Sr) \/
    (exists p q Sm, leq_n p Sl Sm /\ leq_base_n q Sm Sr /\ p + q <= n).
  Proof.
    destruct G as (Sr' & Gequiv & Gcases%measure_closure_cases).
    destruct Gcases as [-> | (p & q & Sm & ? & G & ?)].
    - left. assumption.
    - right. exists p, q, Sm. firstorder.
  Qed.

  Lemma sim_equiv_leq_n n : forward_simulation (leq_base_n^{n}) (leq_base_n^{n}) equiv equiv.
  Proof.
    intros a b equiv_ab a' Leq_a'_a. revert b equiv_ab.
    induction Leq_a'_a as [n ? ? Leq_a'_a | | p q a2 a1 a0 _ IH0 _ IH1].
    - intros. specialize (sim_equiv_leq_base_n n _ _ equiv_ab _ Leq_a'_a).
      destruct sim_equiv_leq_base_n as (d & ? & ?). exists d. split; [constructor | ]; assumption.
    - intros. eexists. split; [reflexivity | eassumption].
    - intros b0 equiv_a0_b0.
      destruct (IH1 _ equiv_a0_b0) as (b1 & ? & equiv_a1_b1).
      destruct (IH0 _ equiv_a1_b1) as (b2 & ? & equiv_a2_b2).
      exists b2. split; [ | assumption]. eapply MC_trans; eassumption.
  Qed.

  Lemma leq_n_trans Sl Sm Sr p q n :
    leq_n p Sl Sm -> leq_n q Sm Sr -> p + q <= n -> leq_n n Sl Sr.
  Proof.
    intros (S'l & ? & leq_S'l_Sm) (S'm & equiv_Sm_S'm & ?).
    pose proof (sim_equiv_leq_n p _ _ equiv_Sm_S'm _ leq_S'l_Sm) as (S''l & ? & ?).
    intros ?. exists S''l. split.
    - transitivity S'l; assumption.
    - eapply measured_closure_over_approx; [ eassumption |].
      eapply MC_trans; eassumption.
  Qed.

  Lemma measured_preservation_reorg_l
    (G : forall n, forward_simulation (leq_base_n n) (leq_n n) reorg reorg^*) :
    forall n, forward_simulation (leq_n n) (leq_n n) reorg^* reorg^*.
  Proof.
    intros n Sr. remember (measure Sr + n) as N eqn:EQN.
    revert n Sr EQN. induction N as [? IH] using lt_wf_ind.
    intros n Sr -> S''r reorg_Sr_S''r Sl leq_Sl_Sr.
    destruct reorg_Sr_S''r as [ | Sr S'r S''r reorg_Sr_S'r ? _] using clos_refl_trans_ind_right'.
    { eexists. split; [eassumption | reflexivity]. }
    apply leq_n_cases in leq_Sl_Sr.
    destruct leq_Sl_Sr as [Hequiv | (p & q & Sm & leq_Sl_Sm & leq_Sm_Sr & ?)].
    { eapply reorgs_preserve_equiv in Hequiv.
      - destruct Hequiv as (Sl' & ? & ?). exists Sl'. split; [ | assumption].
        eexists. split; [eassumption | reflexivity].
      - transitivity S'r; [constructor | ]; assumption. }
    specialize (G q _ _ reorg_Sr_S'r _ leq_Sm_Sr).
    destruct G as (S'm & leq_S'm_S'r & reorg_Sm_S'm).
    specialize (leq_decreasing _ _ _ leq_Sm_Sr).
    edestruct IH with (Sr := Sm) as (S'l & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    pose proof (reorg_decreasing _ _ reorg_Sr_S'r).
    edestruct IH with (Sr := S'r) as (S''m & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    pose proof (leq_clos_decreasing _ _ reorg_Sm_S'm).
    edestruct IH with (Sr := S'm) as (S''l & ? & ?);
      [ | reflexivity | eassumption.. | ]. lia.
    exists S''l. split.
    - eapply leq_n_trans; eassumption.
    - transitivity S'l; assumption.
  Qed.

  Context (leq_base_is_leq_base_n : forall Sl Sr, leq_base Sl Sr <-> exists n, leq_base_n n Sl Sr).

  Lemma leq_n_is_leq Sl Sr : leq Sl Sr <-> exists n, leq_n n Sl Sr.
  Proof.
    split.
    - intros (Sl' & Hequiv & Hleq).
      rewrite measured_closure_equiv in Hleq by exact leq_base_is_leq_base_n.
      destruct Hleq as (n & Hleq). exists n, Sl'. auto.
    - intros (n & Sl' & Hequiv & Hleq). exists Sl'. split; [assumption | ].
      rewrite measured_closure_equiv by exact leq_base_is_leq_base_n.
      exists n. exact Hleq.
  Qed.

  Corollary preservation_reorg_l
    (G : forall n, forward_simulation (leq_base_n n) (leq_n n) reorg reorg^*) :
    forward_simulation leq leq reorg^* reorg^*.
  Proof.
    intros Sr S'l reorg_Sr_S'r Sl leq_Sl_Sr.
    rewrite leq_n_is_leq in leq_Sl_Sr. destruct leq_Sl_Sr as (n & leq_n_Sl_Sr).
    pose proof (measured_preservation_reorg_l G _ _ _ reorg_Sr_S'r _ leq_n_Sl_Sr)
      as (Sl' & ? & ?).
    exists Sl'. split; [ | assumption]. rewrite leq_n_is_leq. exists n. assumption.
  Qed.
End Leq.

Section WellFormedSimulations.
  Context {state : Type}.
  Context (leq_base : state -> state -> Prop).
  Context (well_formed : state -> Prop).

  (* Preservation of reorgs require well-formedness. However, well-formedness for related states is
   * not proved the same in LLBC+ and HLPL+:
   * - In HLPL+, we prove that well-formedness is preserves from right-to-left. That means that
   *   if Sl < Sr and Sr is well-formed, than Sl is well-formed.
   * - In LLBC+, we prove that well-formedness is preserves from left-to-right. That means that
   *   if Sl < Sr and Sl is well-formed, than Sr is well-formed.
   * Thus, we are going to state two different definitions and lemmas. *)
  Definition well_formed_forward_simulation_r {B C D : Type}
    (LeqBA : B -> state -> Prop) (LeqDC : D -> C -> Prop)
    (RedAC : state -> C -> Prop) (RedBD : B -> D -> Prop) :=
    forall a c, well_formed a -> RedAC a c -> forall b, LeqBA b a -> exists d, LeqDC d c /\ RedBD b d.

  (* Reorganizations and leq are defined as reflexive-transitive closure of relations (that we are
   * going to denote < and reorg). When we want to prove the preservation, ie:

      Sl <*  Sr

      |      |
      *      *
      v      v

     Sl' <* Sr'

   * We want to derive it by only considering the cases of < and reorg, and ignoring the reflexive and
   * transitive cases:

      Sl <  Sr

      |     |
      *     |
      v     v

     Sl' <* Sr'

   * However, this proof scheme is wrong in general. Our strategy is to exhibit a measure |.| from
   * states to a well-founded order, that is decreasing by applications of < and reorg.
   *)
  Lemma preservation_reorg_r (reorg : state -> state -> Prop)
    (measure : state -> nat)
    (leq_decreasing : forall a b, leq_base a b -> measure a < measure b)
    (reorg_decreasing : forall a b, reorg a b -> measure b < measure a)
    (leq_base_preserves_wf_r : forall a b, well_formed b -> leq_base a b -> well_formed a)
    (reorg_preserves_wf : forall a b, reorg a b -> well_formed a -> well_formed b)
    (H : well_formed_forward_simulation_r leq_base leq_base^* reorg reorg^*) :
    well_formed_forward_simulation_r leq_base^* leq_base^* reorg^* reorg^*.
  Proof.
    (* Sequences of reorgenizations make the measure decrease. *)
    assert (forall S S', reorg^* S S' -> measure S' <= measure S).
    { intros ? ? Hreorg. induction Hreorg; subst; eauto using Nat.lt_le_incl, Nat.le_trans. }
    (* The well-formedness is preserved by sequences of the base. *)
    assert (forall Sl Sr, well_formed Sr -> leq_base^* Sl Sr -> well_formed Sl).
    { intros ? ? ? G. induction G; eauto. }
    intros Sr. remember (measure Sr) as n eqn:EQN. revert Sr EQN.
    induction n as [? IH] using lt_wf_ind. intros Sr -> Sr' well_formed_Sr reorg_Sr_Sr'.
    destruct reorg_Sr_Sr' as [ | Sr Sr' Sr'' reorg_Sr_Sr' ? _] using clos_refl_trans_ind_right'.
    { intros. eexists. split; [eassumption | apply rt_refl]. }
    intros Sl leq_Sl_Sr.
    destruct leq_Sl_Sr as [ | Sl Sm Sr ? _ leq_Sm_Sr] using clos_refl_trans_ind_left'.
    { eexists. split; [apply rt_refl | ]. eapply rt_trans; [constructor | ]; eassumption. }
    specialize (H _ _ well_formed_Sr reorg_Sr_Sr' _ leq_Sm_Sr). destruct H as (Sm' & leq_Sm'_Sr' & reorg_Sm_Sm').
    assert (exists Sl', leq_base^* Sl' Sm' /\ reorg^* Sl Sl')
      as (Sl' & ? & ?)
      by eauto.
    assert (exists Sm'', leq_base^* Sm'' Sr'' /\ reorg^* Sm' Sm'')
      as (Sm'' & ? & ?)
      by eauto.
    assert (exists Sl'', leq_base^* Sl'' Sm'' /\ reorg^* Sl' Sl'')
      as (? & ? & ?).
    { eapply IH; [ | reflexivity | | eassumption..]; eauto using Nat.le_lt_trans. }
    eexists. split; eapply rt_trans; eassumption.
  Qed.
End WellFormedSimulations.

Definition rel_compose {A B C : Type} (R : A -> B -> Prop) (S : B -> C -> Prop) a c :=
  exists b, R a b /\ S b c.

Lemma forward_simulation_closure A (E R : relation A) :
  forward_simulation E E R R -> forward_simulation E E R^* R^*.
Proof.
  intros H ? ? G. induction G as [ | | ? ? ? ? IH0 ? IH1].
  - intros. edestruct H as (? & ? & ?); [eassumption.. | ].
    eexists. split; [ | constructor]; eassumption.
  - intros. eexists. split; [ | apply rt_refl]. assumption.
  - intros.
    edestruct IH0 as (? & ? & ?); [eassumption | ].
    edestruct IH1 as (? & ? & ?); [eassumption | ].
    eexists. split; [ | eapply rt_trans]; eassumption.
Qed.
