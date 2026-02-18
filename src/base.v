(* TODO: documentation. *)
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat Lia ZArith.
Require Import OptionMonad.
Import ListNotations.

From stdpp Require Import fin_maps pmap gmap.

Local Open Scope option_monad_scope.

Lemma fst_pair {A B} (a : A) (b : B) : fst (a, b) = a. Proof. reflexivity. Qed.

Definition indicator {A : Type} `{EqDecision A} (a b : A) :=
  if decide (a = b) then 1 else 0.

Lemma indicator_same {A} `{EqDecision A} (a : A) : indicator a a = 1.
Proof. unfold indicator. destruct (decide (a = a)); congruence. Qed.

Lemma indicator_eq {A} `{EqDecision A} (a b : A) : a = b -> indicator a b = 1.
Proof. intros <-. apply indicator_same. Qed.

Lemma indicator_non_zero {A} `{EqDecision A} (a b : A) : indicator a b > 0 -> a = b.
Proof. unfold indicator. destruct (decide (a = b)); easy. Qed.

Lemma indicator_diff {A} `{EqDecision A} (a b : A) : a <> b -> indicator a b = 0.
Proof. unfold indicator. destruct (decide (a = b)); congruence. Qed.

Lemma length_1_is_singleton [A : Type] [l : list A] : length l = 1 -> exists a, l = [a].
Proof.
  intro H. destruct l as [ | a l'].
  - inversion H.
  - exists a. f_equal. apply length_zero_iff_nil. inversion H. auto.
Qed.

Lemma nth_error_singleton {A} (a b : A) i : nth_error [a] i = Some b -> a = b /\ i = 0.
Proof. destruct i; cbn; rewrite ?nth_error_nil; split; congruence. Qed.

(* A variant of the lemma `nth_error_Some` that is more convenient to use.
   Indeed, it let us perform an inversion on the result. *)
Lemma nth_error_Some' [A : Type] (l : list A) n :
  n < length l -> Is_Some (nth_error l n).
Proof.
  intros ?%nth_error_Some. destruct (nth_error l n); [eexists; reflexivity | contradiction].
Qed.

Lemma nth_error_length [A] (l : list A) n x : nth_error l n = Some x -> n < length l.
Proof. intro H. apply nth_error_Some. rewrite H. discriminate. Qed.
Local Hint Resolve nth_error_length : core.

(* TODO: could be removed, to use "list_alter" from stdpp. *)
Section Alter_list.
  Context {A : Type}.

  (* Returns the list where the n-th element has been set to `a`. If n is out of bound,
     returns the list l unchanged. *)
  Fixpoint alter_list (l : list A) n (f : A -> A) :=
  match l, n with
  | nil, _ => nil
  | a :: l', 0 => (f a) :: l'
  | a :: l', S m => a :: (alter_list l' m f)
  end.

  Lemma alter_list_length l f : forall n, length (alter_list l n f) = length l.
  Proof. induction l; intros [ | ]; cbn; auto. Qed.

  Lemma nth_error_alter_list_eq l f :
    forall n, nth_error (alter_list l n f) n = SOME x <- nth_error l n IN Some (f x).
  Proof.
    induction l; intros; try rewrite !nth_error_nil; cbn; simplify_option.
  Qed.

  Corollary nth_error_alter_list_eq_some l f n a (H : nth_error l n = Some a) :
    nth_error (alter_list l n f) n = Some (f a).
  Proof. rewrite nth_error_alter_list_eq, H. reflexivity. Qed.

  Lemma nth_error_alter_list_lt l a :
    forall m n, m < n -> nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct n; try easy. destruct m; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Lemma nth_error_alter_list_gt l a :
    forall m n, m > n -> nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct m; try easy. destruct n; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Corollary nth_error_alter_list_neq l a m n (H : m <> n) :
    nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    rewrite Nat.lt_gt_cases in H. destruct H.
    - apply nth_error_alter_list_lt. assumption.
    - apply nth_error_alter_list_gt. assumption.
   Qed.

  Lemma alter_list_neq_commute l m n f g (H : m <> n) :
    alter_list (alter_list l m f) n g = alter_list (alter_list l n g) m f.
  Proof.
    apply nth_error_ext. intro i.
    destruct (Nat.eq_dec m i) as [-> | ]; destruct (Nat.eq_dec n i) as [-> | ];
      repeat rewrite nth_error_alter_list_eq || rewrite nth_error_alter_list_neq by auto; easy.
  Qed.

  Lemma alter_list_invariant (l : list A) n x f
    (Hx : nth_error l n = Some x) (Hf : f x = x) : alter_list l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite nth_error_alter_list_eq. autodestruct.
    - rewrite nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equal_Some (l : list A) n x f g
    (Hx : nth_error l n = Some x) (Hfg : f x = g x) : alter_list l n f = alter_list l n g.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equal_None (l : list A) n f
    (Hx : nth_error l n = None) : alter_list l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_compose (l : list A) n f g :
    alter_list (alter_list l n g) n f = alter_list l n (fun x => f (g x)).
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equiv (l : list A) n f g
    (Hfg : forall x, f x = g x) : alter_list l n f = alter_list l n g.
  Proof.
    destruct (nth_error l n) eqn:EQN.
    - eapply alter_list_equal_Some; eauto.
    - rewrite !alter_list_equal_None; auto.
  Qed.
End Alter_list.

Lemma map_alter_list [A B] l (f : A -> B) g n x : nth_error l n = Some x ->
  map f (alter_list l n g) = alter_list (map f l) n (fun _ => f (g x)).
Proof.
  intro. apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
  - rewrite nth_error_map.
    rewrite !nth_error_alter_list_eq.
    rewrite nth_error_map. simplify_option.
  - rewrite nth_error_map.
    rewrite !nth_error_alter_list_neq by assumption.
    rewrite nth_error_map. reflexivity.
Qed.

Definition sum (l : list nat) := fold_right Nat.add 0 l.

Lemma sum_alter_list l n f x : nth_error l n = Some x ->
  (Z.of_nat (sum (alter_list l n f))) = ((Z.of_nat (sum l)) - (Z.of_nat x) + (Z.of_nat (f x)))%Z.
Proof.
  revert l. induction n.
  - intros [ | ? l] [=->]. cbn. lia.
  - intros [ | y l] [=H]. specialize (IHn _ H). cbn. unfold sum in IHn. lia.
Qed.

Lemma sum_ge_element l n x : nth_error l n = Some x -> sum l >= x.
Proof.
  revert l. induction n.
  - intros [ | ? l] [=->]. cbn. lia.
  - intros [ | y l] [=H]. specialize (IHn _ H). cbn. unfold sum in IHn. lia.
Qed.

Lemma sum_non_zero l :
  sum l > 0 -> (exists i x, nth_error l i = Some (S x)).
Proof.
  induction l as [ | y l IH].
  - cbn. lia.
  - intro H. destruct y as [ | z]; cbn in H.
    + specialize (IH H). destruct IH as (i & x & ?). exists (S i), x. assumption.
    + exists 0, z. reflexivity.
Qed.

Lemma sum_zero l : sum l = 0 <-> (forall i, i < length l -> nth_error l i = Some 0).
Proof.
  split.
  - intros ? i Hi. apply nth_error_Some' in Hi. destruct Hi as (x & Hi). rewrite Hi.
    apply sum_ge_element in Hi. f_equal. lia.
  - intros ?. destruct (sum l) eqn:?; [reflexivity | ].
    assert (sum l > 0) as (? & ? & G)%sum_non_zero by lia. rewrite H in G; [discriminate | eauto].
Qed.

Lemma sum_le_one l :
  sum l <= 1 -> (forall i j x y, nth_error l i = Some x -> nth_error l j = Some y -> x > 0 -> y > 0 -> i = j).
Proof.
  intros H. induction l as [ | n l IH].
  - intros i ? x ? G. rewrite nth_error_nil in G. congruence.
  - cbn in H. destruct n.
    + intros [ | i] [ | j] ? ?; [rewrite nth_error_cons_0; simplify_option; lia.. | ].
      rewrite !nth_error_cons_succ.
      assert (sum l <= 1) as G by (unfold sum; lia). specialize (IH G).
      intros. f_equal. eauto.
    + intros i j [ | ] [ | ] Hi Hj Hx Hy; [lia.. | ].
      assert (sum l = 0) as G by (unfold sum; lia).
      destruct i. 2: { cbn in Hi. apply sum_ge_element in Hi. lia. }
      destruct j. 2: { cbn in Hj. apply sum_ge_element in Hj. lia. }
      reflexivity.
Qed.

Lemma sum_unique_one l (H : forall i x, nth_error l i = Some x -> x <= 1)
  (G : forall i j, nth_error l i = Some 1 -> nth_error l j = Some 1 -> i = j) :
  sum l <= 1.
Proof.
  induction l as [ | [ | [ | x]] l IH].
  - cbn. lia.
  - apply IH.
    + intros i. specialize (H (S i)). rewrite nth_error_cons_succ in H. exact H.
    + intros i j ? ?. specialize (G (S i) (S j)). rewrite !nth_error_cons_succ in G.
      injection G; auto.
  - transitivity (1 + sum l); [reflexivity | ].
    destruct (sum l) eqn:?.
    + rewrite Nat.add_0_r. reflexivity.
    + assert (sum l > 0) as (i & x & Hi)%sum_non_zero by lia.
      specialize (H (S i) _ Hi). replace (S x) with 1 in Hi by lia.
      specialize (G (S i) 0 Hi). discriminate G. reflexivity.
  - specialize (H 0 (2 + x)). rewrite nth_error_cons_0 in H.
    assert (2 + x <= 1) by auto. lia.
Qed.

Section Map_sum.
  Context {K : Type}.
  Context {M : Type -> Type}.
  Context `{FinMap K M}.

  (* Contrary to the sum of a list, the sum of a map is defined over a map with in arbitrary value
     type A, and a weight function. *)
  Context {A : Type}.
  Context (weight : A -> nat).

  Definition map_sum : M A -> nat := map_fold (fun _ x n => weight x + n) 0.

  Lemma map_sum_insert m k x : lookup k m = None -> map_sum (insert k x m) = weight x + map_sum m.
  Proof. intros. unfold map_sum. rewrite map_fold_insert_L; [reflexivity | lia | assumption]. Qed.

  Corollary map_sum_delete m k x : lookup k m = Some x -> map_sum m = weight x + map_sum (delete k m).
  Proof. intros G%insert_delete. rewrite<- G at 1. apply map_sum_insert, lookup_delete. Qed.

  Lemma map_sum_non_zero m : map_sum m > 0 -> exists k x, lookup k m = Some x /\ weight x > 0.
  Proof.
    unfold map_sum. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
    - rewrite map_fold_empty. lia.
    - rewrite map_sum_insert by assumption. destruct (weight x) eqn:?.
      + intros (k' & y & ? & ?)%IHm. exists k', y. rewrite lookup_insert_ne by congruence. auto.
      + eexists k, _. rewrite lookup_insert. split; [reflexivity | lia].
  Qed.

  Corollary map_sum_zero m : (forall k x, lookup k m = Some x -> weight x = 0) -> map_sum m = 0.
  Proof.
    intros elems_zero. destruct (map_sum m) eqn:?; [reflexivity | ].
    assert (map_sum m > 0) as (? & ? & get_m & ?)%map_sum_non_zero by lia.
    specialize (elems_zero _ _ get_m). lia.
  Qed.

  Lemma map_sum_le_one m :
    map_sum m <= 1 ->
    forall i j x y, lookup i m = Some x -> lookup j m = Some y -> weight x > 0 -> weight y > 0 -> i = j.
  Proof.
    intros sum_one i j. destruct (decide (i = j)); [auto | ].
    intros ? ? delete_i%insert_delete. rewrite <-delete_i in *.
    rewrite lookup_insert_ne by assumption. intros delete_j%insert_delete.
    rewrite <-delete_j, !map_sum_insert in sum_one
     by (rewrite ?lookup_insert_ne, ?lookup_delete_ne by auto; apply lookup_delete).
    lia.
  Qed.

  Lemma map_sum_unique_one m (elems_at_most_one : forall i x, lookup i m = Some x -> weight x <= 1) :
    (forall i j x y, lookup i m = Some x -> lookup j m = Some y -> weight x > 0 -> weight y > 0 -> i = j) ->
    map_sum m <= 1.
  Proof.
    intros ?. destruct (map_sum m) eqn:?; [lia | ].
    assert (map_sum m > 0) as (k & x & get_m_k & ?)%map_sum_non_zero by lia.
    assert (weight x <= 1) by (eapply elems_at_most_one; eassumption).
    pose proof (sum_m_delete := get_m_k).
    apply map_sum_delete in sum_m_delete. rewrite (map_sum_zero (delete k m)) in sum_m_delete.
    - lia.
    - intros k' y (? & ?)%lookup_delete_Some.
      destruct (weight y) eqn:?.
      + reflexivity.
      + assert (weight y > 0) by lia. exfalso. eauto.
  Qed.

  Lemma map_sum_empty : map_sum empty = 0.
  Proof. apply map_fold_empty. Qed.

  Lemma map_sum_union m0 m1 : map_disjoint m0 m1 -> map_sum (union m0 m1) = map_sum m0 + map_sum m1.
  Proof.
    intros disj. induction m1 as [ | k x m1 ? _ IHm] using map_first_key_ind.
    - rewrite map_union_empty, !map_sum_empty. lia.
    - rewrite map_disjoint_insert_r in disj. destruct disj as (? & disj).
      specialize (IHm disj).
      rewrite<- insert_union_r by assumption.
      rewrite !map_sum_insert by now rewrite ?lookup_union_None_2.
      lia.
  Qed.
End Map_sum.

Lemma map_sum_kmap {M0 M1 K0 K1 A} `{FinMap K0 M0} `{FinMap K1 M1} (f : K0 -> K1) (m : M0 A) weight :
  Inj eq eq f -> map_sum (M := M1) weight (kmap f m) = map_sum weight m.
Proof.
  intros ?. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - rewrite kmap_empty, !map_sum_empty. reflexivity.
  - rewrite kmap_insert by assumption.
    rewrite !map_sum_insert by (rewrite ?lookup_kmap by assumption; assumption).
    congruence.
Qed.

Definition decode' {A} `{Countable A} (x : positive) :=
  match decode x with
  | Some y => if (decide (encode (A := A) y = x)) then Some y else None
  | None => None
  end.

Lemma decode'_encode {A} `{Countable A} (a : A) : decode' (encode a) = Some a.
Proof. unfold decode'. rewrite decode_encode. destruct decide; easy. Qed.

Lemma decode'_is_Some {A} `{Countable A} x (y : A) : decode' x = Some y <-> encode y = x.
Proof.
  unfold decode'. split.
  - simplify_option.
  - intros G. assert (decode x = Some y). { pose proof (decode_encode y). congruence. }
    simplify_option.
Qed.

Lemma map_alter_not_in_domain `{FinMap K M} `(m : M V) k f :
  lookup k m = None -> alter f k m = m.
Proof.
  intros ?. apply map_eq. intros k'.
  destruct (decide (k = k')) as [<- | ]; simplify_map_eq; reflexivity.
Qed.

Lemma size_kmap `{FinMap K1 M1} `{FinMap K2 M2} {A} f (m : M1 A) :
  Inj eq eq f -> size (kmap (M2 := M2) f m) = size m.
Proof.
  intros ?. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - rewrite kmap_empty, !map_size_empty. reflexivity.
  - rewrite kmap_insert by assumption. rewrite !map_size_insert_None.
    + congruence.
    + assumption.
    + now rewrite lookup_kmap.
Qed.

(* TODO: name similar to "sum_map", could be confusing *)
Section SumMaps.
  Context {V K0 K1 : Type}.
  Context `{FinMap K0 M0}.
  Context `{FinMap K1 M1}.
  Context `{Countable (K0 + K1)}.

  Let encode_inl k := encode (A := K0 + K1) (inl k).
  Let encode_inr k := encode (A := K0 + K1) (inr k).

  Definition sum_maps (m0 : M0 V) (m1 : M1 V) : Pmap V :=
    union (kmap encode_inl m0) (kmap encode_inr m1).

  Local Instance encode_inl_inj : Inj eq eq encode_inl.
  Proof. eapply compose_inj; typeclasses eauto. Qed.

  Local Instance encode_inr_inj : Inj eq eq encode_inl.
  Proof. eapply compose_inj; typeclasses eauto. Qed.

  Lemma lookup_inl_kmap_inr (m1 : M1 V) k :
    kmap (M2 := Pmap) encode_inr m1 !! encode_inl k = None.
  Proof.
    unfold encode_inl, encode_inr. apply lookup_kmap_None.
    - typeclasses eauto.
    - intros ? ?%encode_inj. discriminate.
  Qed.

  Lemma lookup_inr_kmap_inl (m0 : M0 V) k :
    kmap (M2 := Pmap) encode_inl m0 !! encode_inr k = None.
  Proof.
    unfold encode_inl, encode_inr. apply lookup_kmap_None.
    - typeclasses eauto.
    - intros ? ?%encode_inj. discriminate.
  Qed.

  Hint Rewrite lookup_inl_kmap_inr : core.
  Hint Rewrite lookup_inr_kmap_inl : core.

  Lemma sum_maps_lookup_l m0 m1 k :
    lookup (encode_inl k) (sum_maps m0 m1) = lookup k m0.
  Proof.
    unfold sum_maps. rewrite lookup_union_l.
    - apply lookup_kmap. typeclasses eauto.
    - autorewrite with core. reflexivity.
  Qed.

  Lemma sum_maps_lookup_r m0 m1 k :
    lookup (encode_inr k) (sum_maps m0 m1) = lookup k m1.
  Proof.
    unfold sum_maps. rewrite lookup_union_r.
    - apply lookup_kmap. typeclasses eauto.
    - autorewrite with core. reflexivity.
  Qed.

  Lemma sum_maps_alter_inl m0 m1 f k :
    alter f (encode_inl k) (sum_maps m0 m1) = sum_maps (alter f k m0) m1.
  Proof.
    unfold sum_maps, union, map_union.
    rewrite alter_union_with_l; autorewrite with core; try easy.
    rewrite kmap_alter by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_alter_inr m0 m1 f k :
    alter f (encode_inr k) (sum_maps m0 m1) = sum_maps m0 (alter f k m1).
  Proof.
    unfold sum_maps, union, map_union.
    rewrite alter_union_with_r; autorewrite with core; try easy.
    rewrite kmap_alter by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_insert_inl m0 m1 k v :
    insert (encode_inl k) v (sum_maps m0 m1) = sum_maps (insert k v m0) m1.
  Proof.
    unfold sum_maps. rewrite insert_union_l by now autorewrite with core.
    rewrite kmap_insert by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_insert_inr m0 m1 k v :
    insert (encode_inr k) v (sum_maps m0 m1) = sum_maps m0 (insert k v m1).
  Proof.
    unfold sum_maps. rewrite insert_union_r by now autorewrite with core.
    rewrite kmap_insert by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_eq m0 m1 m0' m1' : sum_maps m0 m1 = sum_maps m0' m1' -> m0 = m0' /\ m1 = m1'.
  Proof.
    intros eq_sums. split; apply map_eq; intros k.
    - erewrite<- !sum_maps_lookup_l, eq_sums. reflexivity.
    - erewrite<- !sum_maps_lookup_r, eq_sums. reflexivity.
  Qed.

  Lemma sum_maps_lookup_None (m0 : M0 V) (m1 : M1 V) k (G : decode' (A := K0 + K1) k = None) :
    lookup k (sum_maps m0 m1) = None.
  Proof.
    apply lookup_union_None_2.
    - rewrite lookup_kmap_None by typeclasses eauto.
      intros ? ->. unfold encode_inl in G. rewrite decode'_encode in G. discriminate.
    - rewrite lookup_kmap_None by typeclasses eauto.
      intros ? ->. unfold encode_inr in G. rewrite decode'_encode in G. discriminate.
  Qed.

  Lemma sum_maps_union m0 m1 m2 :
    sum_maps m0 (union m1 m2) = union (sum_maps m0 m1) (kmap encode_inr m2).
  Proof.
    unfold sum_maps. rewrite kmap_union by typeclasses eauto.
    apply map_union_assoc.
  Qed.

  Lemma sum_maps_delete_inr m0 m1 k :
    delete (encode_inr k) (sum_maps m0 m1) = sum_maps m0 (delete k m1).
  Proof.
    unfold sum_maps. rewrite delete_union. f_equal.
    - apply delete_notin. autorewrite with core. reflexivity.
    - symmetry. apply kmap_delete. typeclasses eauto.
  Qed.

  Lemma size_sum_maps m0 m1 : size (sum_maps m0 m1) = size m0 + size m1.
  Proof.
    unfold sum_maps. rewrite map_size_disj_union.
    - rewrite !size_kmap by typeclasses eauto. reflexivity.
    - rewrite map_disjoint_spec.
      intros ? ? ? (? & -> & _)%lookup_kmap_Some; [ | typeclasses eauto].
      rewrite lookup_inl_kmap_inr. easy.
  Qed.

  Lemma sum_maps_is_Some m0 m1 k : is_Some (lookup k (sum_maps m0 m1)) ->
    (exists i, k = encode_inl i /\ is_Some (lookup i m0)) \/
    (exists i, k = encode_inr i /\ is_Some (lookup i m1)).
  Proof.
    intros get_k. destruct (decode' (A := K0 + K1) k) as [decode_k | ] eqn:EQN.
    - apply decode'_is_Some in EQN. rewrite <-!EQN in *. destruct decode_k as [i | i].
      + left. exists i. replace (encode (inl i)) with (encode_inl i) in * by reflexivity.
        rewrite sum_maps_lookup_l in get_k. auto.
      + right. exists i. replace (encode (inr i)) with (encode_inr i) in * by reflexivity.
        rewrite sum_maps_lookup_r in get_k. auto.
    - rewrite sum_maps_lookup_None in get_k by assumption. inversion get_k. discriminate.
  Qed.
End SumMaps.

(* Collapse the 2-dimensional map of regions into a 1-dimensional map. *)
Section Flatten.
  Context {V : Type}.

  Definition flatten : Pmap (Pmap V) -> gmap (positive * positive) V :=
    map_fold (fun i m Ms => union (kmap (fun j => (i, j)) m) Ms) empty.

  Lemma flatten_insert Ms i m (G : lookup i Ms = None) :
    flatten (insert i m Ms) = union (kmap (fun j => (i, j)) m) (flatten Ms).
  Proof.
    unfold flatten. rewrite map_fold_insert_L.
    - reflexivity.
    - intros. rewrite !map_union_assoc. f_equal. apply map_union_comm.
      apply map_disjoint_spec.
      intros ? ? ? (? & ? & _)%lookup_kmap_Some (? & ? & _)%lookup_kmap_Some. congruence.
      all: typeclasses eauto.
    - assumption.
  Qed.

  Lemma lookup_flatten Ms i j : lookup (i, j) (flatten Ms) = mbind (lookup j) (lookup i Ms).
  Proof.
    induction Ms as [ | k x Ms ? _ IHm] using map_first_key_ind.
    - unfold flatten. rewrite map_fold_empty. simpl_map. reflexivity.
    - rewrite flatten_insert by assumption. destruct (decide (i = k)) as [-> | ].
      + simpl_map. rewrite lookup_union. rewrite lookup_kmap by typeclasses eauto.
        rewrite IHm, H. apply option_union_right_id.
      + simpl_map. rewrite lookup_union_r; [exact IHm | ].
        rewrite lookup_kmap_None by typeclasses eauto. congruence.
  Qed.

  Lemma lookup_None_flatten Ms i j : lookup i Ms = None -> lookup (i, j) (flatten Ms) = None.
  Proof. intros H. rewrite lookup_flatten, H. reflexivity. Qed.

  Lemma lookup_Some_flatten Ms i j m :
    lookup i Ms = Some m -> lookup (i, j) (flatten Ms) = lookup j m.
  Proof. intros H. rewrite lookup_flatten, H. reflexivity. Qed.

  Lemma disj_kmap_flatten Ms i (m : Pmap V) :
    lookup i Ms = None -> map_disjoint (kmap (fun j => (i, j)) m) (flatten Ms).
  Proof.
    intros ?. apply map_disjoint_spec. intros ? ? ? (? & -> & ?)%lookup_kmap_Some.
    - rewrite lookup_None_flatten by assumption. discriminate.
    - typeclasses eauto.
  Qed.

  Lemma flatten_insert' Ms i m (G : lookup i Ms = None) :
    flatten (insert i m Ms) = union (flatten Ms) (kmap (fun j => (i, j)) m).
  Proof. rewrite flatten_insert by assumption. apply map_union_comm, disj_kmap_flatten, G. Qed.

  Lemma alter_flatten f i j Ms :
    alter f (i, j) (flatten Ms) = flatten (alter (alter f j) i Ms).
  Proof.
    induction Ms as [ | k x Ms ? _ IHm] using map_first_key_ind.
    - rewrite !map_alter_not_in_domain by now simpl_map. reflexivity.
    - destruct (decide (i = k)) as [<- | ].
      + rewrite alter_insert.
        rewrite !flatten_insert by assumption.
        unfold union, map_union. rewrite alter_union_with_l.
        * now rewrite kmap_alter by typeclasses eauto.
        * reflexivity.
        * intros ? ?. rewrite lookup_None_flatten; easy.
      + rewrite alter_insert_ne by assumption. rewrite !flatten_insert by now simpl_map.
        unfold union, map_union. rewrite alter_union_with by reflexivity. rewrite IHm.
        rewrite map_alter_not_in_domain.
        * reflexivity.
        * rewrite eq_None_not_Some.
          intros (? & ? & _)%lookup_kmap_is_Some; [congruence | typeclasses eauto].
  Qed.

  Lemma size_flatten M M' :
    map_Forall2 (fun _ m m' => size m = size m') M M' -> size (flatten M) = size (flatten M').
  Proof.
    revert M'. induction M as [ | k x M H _ IHM] using map_first_key_ind.
    - intros ? ->%map_Forall2_empty_inv_l. reflexivity.
    - intros _M' G. apply map_Forall2_insert_inv_l in G; [ | assumption].
      destruct G as (p & M' & -> & ? & ? & ?).
      rewrite !flatten_insert by assumption.
      rewrite !map_size_disj_union by now apply disj_kmap_flatten.
      rewrite !size_kmap by typeclasses eauto.
      erewrite IHM by eassumption. lia.
  Qed.
End Flatten.

(* We need to reason about the permutations of keys of a map m.
 * We can't really use the function kmap f m, because f must be a total injective permutation.
 * Thus, we are going to introduce pkmap f m ("partial key map"), where "f" is a partial function.
 *)

Definition insert_permuted_key {A}
  (f : positive -> option positive) (i : positive) (a : A) (m : Pmap A) :=
  match f i with
  | Some j => insert j a m
  | None => m
  end.

Definition pkmap {A} f : Pmap A -> Pmap A := map_fold (insert_permuted_key f) empty.

(* A permutation needs to be injective for the operation to be sound. *)
Definition partial_inj (f : positive -> option positive) :=
  forall i, is_Some (f i) -> forall j, f i = f j -> i = j.

Lemma pkmap_insert {A} p i x (m : Pmap A) :
  partial_inj p -> lookup i m = None ->
  pkmap p (insert i x m) = insert_permuted_key p i x (pkmap p m).
Proof.
  intros H ?. unfold pkmap. apply map_fold_insert_L.
  - unfold insert_permuted_key. intros j1 j2 ? ? ? diff_j. autodestruct. autodestruct. intros.
    apply insert_commute. intros ?. apply diff_j. eapply H; [auto | congruence].
  - assumption.
Qed.

Lemma lookup_pkmap {A} f i j (m : Pmap A) :
  partial_inj f -> f i = Some j -> lookup j (pkmap f m) = lookup i m.
Proof.
  intros inj_p H. unfold pkmap.
  induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - rewrite map_fold_empty. simpl_map. reflexivity.
  - destruct (decide (i = k)) as [<- | n].
    + rewrite map_fold_insert_first_key by assumption.
      unfold insert_permuted_key. rewrite H. simpl_map. reflexivity.
    + simpl_map. rewrite map_fold_insert_first_key by assumption.
      unfold insert_permuted_key. destruct (f k) eqn:EQN.
      * rewrite lookup_insert_ne.
        -- exact IHm.
       (* By injectivity, we can prove that i = k, which is a contradiction. *)
        -- intros ->. apply n, inj_p; [auto | congruence].
      * exact IHm.
Qed.

Lemma lookup_pkmap_None {A} f j (m : Pmap A) :
  (forall i, f i <> Some j) -> lookup j (pkmap f m) = None.
Proof.
  intros H. unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite map_fold_insert_first_key by assumption.
    unfold insert_permuted_key at 1. destruct (f k) as [j' | ] eqn:EQN.
    + rewrite lookup_insert_ne by congruence. exact IHm.
    + exact IHm.
Qed.

Lemma pkmap_delete {A} f i j (m : Pmap A) :
  partial_inj f -> f i = Some j -> pkmap f (delete i m) = delete j (pkmap f m).
Proof.
  intros H G. destruct (lookup i m) as [x | ] eqn:EQN.
  - apply insert_delete in EQN. rewrite <-EQN at 2. rewrite pkmap_insert by now simpl_map.
    unfold insert_permuted_key. rewrite G. symmetry. apply delete_insert.
    erewrite lookup_pkmap by eassumption. simpl_map. reflexivity.
  - rewrite delete_notin by assumption. symmetry. apply delete_notin.
    erewrite lookup_pkmap; eassumption.
Qed.

Lemma pkmap_fmap {A} f (g : A -> A) (m : Pmap A) (inj_f : partial_inj f) :
  pkmap f (fmap g m) = fmap g (pkmap f m).
Proof.
  unfold pkmap. induction m as [ | k x m k_fresh ? IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite map_fold_insert_first_key, fmap_insert by assumption.
    rewrite map_fold_insert_L.
    * unfold insert_permuted_key. destruct (f k) eqn:EQN.
      -- rewrite fmap_insert. f_equal. exact IHm.
      -- exact IHm.
    * intros ? ? ? ? ? diff ? ?. unfold insert_permuted_key. autodestruct. autodestruct.
      intros. rewrite insert_commute; [reflexivity | ].
      intros ?. apply diff, inj_f; [auto | congruence].
    * rewrite lookup_fmap, k_fresh. reflexivity.
Qed.

Lemma lookup_pkmap_rev {A} f j (m : Pmap A) :
  partial_inj f -> is_Some (lookup j (pkmap f m)) -> exists i, f i = Some j.
Proof.
  intros inj_f H. unfold pkmap. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - inversion H. discriminate.
  - rewrite pkmap_insert in H by assumption.
    unfold insert_permuted_key in H. destruct (f k) as [j' | ] eqn:?; [ | auto].
    destruct (decide (j = j')) as [<- | ]; simpl_map.
    + exists k. assumption.
    + apply IHm. assumption.
Qed.

Definition is_equivalence {A} f (m : Pmap A) :=
  partial_inj f /\ forall i, is_Some (lookup i m) -> is_Some (f i).

Lemma size_pkmap {A} f m (H : @is_equivalence A f m) : size (pkmap f m) = size m.
Proof.
  destruct H as (inj_f & dom_f).
  induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite map_size_insert_None by assumption.
    rewrite pkmap_insert by assumption.
    unfold insert_permuted_key. destruct (dom_f k) as (v & Hv); [now simpl_map | ].
    rewrite Hv. rewrite map_size_insert_None, IHm.
    + reflexivity.
    + intros ? (? & ?). apply dom_f. now rewrite lookup_insert_ne by congruence.
    + erewrite lookup_pkmap; eassumption.
Qed.

Lemma pkmap_eq {A} f (m0 m1 : Pmap A) :
  is_equivalence f m0 ->
  (forall i j, f i = Some j -> lookup i m0 = lookup j m1) ->
  size m0 = size m1 ->
  pkmap f m0 = m1.
Proof.
  intros equiv_f H size_eq. apply map_subseteq_size_eq.
  - intros j.
    destruct (lookup j (pkmap f m0)) eqn:EQN; cbn; [ | autodestruct].
    destruct (lookup_pkmap_rev f j m0) as (i & Hi); [apply equiv_f | auto | ].
    erewrite <-H by eassumption.
    erewrite lookup_pkmap in EQN; [ | apply equiv_f | eassumption].
    rewrite EQN. reflexivity.
  - rewrite size_pkmap by assumption. rewrite size_eq. reflexivity.
Qed.

(* When the functions f and g are equal on the domain of m, we can prove equality without any
 * injectivity hypothesis. *)
Lemma pkmap_fun_eq {A} f g (m : Pmap A) (H : forall i, is_Some (lookup i m) -> f i = g i) :
  pkmap f m = pkmap g m.
Proof.
  unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite !map_fold_insert_first_key by assumption.
    rewrite IHm.
    + unfold insert_permuted_key. rewrite H; [reflexivity | ]. simpl_map. auto.
    + intros i ?. apply H. apply lookup_insert_is_Some'. auto.
Qed.

Lemma alter_pkmap {A} f g i j (m : Pmap A) (H : is_equivalence f m) (G : f i = Some j) :
  pkmap f (alter g i m) = alter g j (pkmap f m).
Proof.
  destruct H as (inj_f & H). apply pkmap_eq.
  - split; [assumption | ]. intros ?. rewrite lookup_alter_is_Some. auto.
  - intros i' j' G'. destruct (decide (i = i')) as [<- | n].
    + replace j' with j in * by congruence. simpl_map.
      symmetry. f_equal. apply lookup_pkmap; assumption.
    + simpl_map. rewrite lookup_alter_ne.
      * symmetry. apply lookup_pkmap; assumption.
      * intros <-. apply n. apply inj_f. auto. congruence.
  - rewrite <-!size_dom, !dom_alter, !size_dom. symmetry. apply size_pkmap. split; assumption.
Qed.

Definition equiv_map {A} (m0 m1 : Pmap A) :=
  exists f, is_equivalence f m0 /\ m1 = pkmap f m0.

Global Instance reflexive_equiv_map A : Reflexive (@equiv_map A).
Proof.
  intros m. exists Some. split; [split | ].
  - intros ? _ ? [=]. assumption.
  - auto.
  - unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    + reflexivity.
    + rewrite map_fold_insert_first_key by assumption. rewrite <-IHm. reflexivity.
Qed.

(* Defining a computable equivalent notion of map equivalence. *)
Definition map_inj {A} (p : Pmap A) :=
  map_Forall (fun i x => map_Forall (fun j y => x = y -> i = j) p) p.

Lemma map_inj_equiv (p : Pmap positive) :
  map_inj p <-> partial_inj (fun i => lookup i p).
Proof.
  split.
  - intros inj_p i (? & pi) j ?. eapply inj_p; [eassumption | | reflexivity]. congruence.
  - intros inj_p i ? pi j ? pj <-. apply inj_p; [auto | congruence].
Qed.

(* The notion of permutation is nearly equivalent to the notion of equivalence with one difference:
 * the domains of the permutations is equal to the domain of the map m. For an equivalence, it is
 * sufficient that the domain of the function f contains the domains of m. *)
Definition is_permutation {A} (p : Pmap positive) (m : Pmap A) :=
  map_inj p /\ forall i, is_Some (lookup i p) <-> is_Some (lookup i m).

Lemma permutation_is_equivalence {A} p m :
  @is_permutation A p m -> is_equivalence (fun i => lookup i p) m.
Proof.
  intros (inj_p & dom_p). split.
  - rewrite <-map_inj_equiv. assumption.
  - intros ?. apply dom_p.
Qed.

Lemma is_permutation_dom_eq {A} p (m0 m1 : Pmap A) :
  dom m0 = dom m1 -> is_permutation p m0 -> is_permutation p m1.
Proof. unfold is_permutation. setoid_rewrite <-elem_of_dom. intros <- H. exact H. Qed.

Corollary is_permutation_fmap {A} p (f : A -> A) (m : Pmap A) :
  is_permutation p m -> is_permutation p (fmap f m).
Proof. apply is_permutation_dom_eq. symmetry. apply dom_fmap_L. Qed.

Global Notation apply_permutation p := (pkmap (fun i => lookup i p)).

Lemma lookup_apply_permutation {A} p i j (m : Pmap A) :
  map_inj p -> lookup i p = Some j -> apply_permutation p m !! j = m !! i.
Proof. intros ?%map_inj_equiv ?. apply lookup_pkmap; assumption. Qed.

Lemma apply_permutation_insert {A} (p : Pmap positive) i j (a : A) m :
  map_inj p -> lookup i m = None -> lookup i p = Some j ->
  apply_permutation p (insert i a m) = insert j a (apply_permutation (delete i p) m).
Proof.
  intros. rewrite pkmap_insert; [ | now apply map_inj_equiv | assumption].
  unfold insert_permuted_key. simpl_map. f_equal.
  apply pkmap_fun_eq. intros i' (? & ?). symmetry. apply lookup_delete_ne. congruence.
Qed.

Lemma apply_permutation_insert' {A} (p : Pmap positive) i j (a : A) m :
  map_inj (insert i j p) -> lookup i m = Some a -> lookup i p = None ->
  apply_permutation (insert i j p) m = insert j a (apply_permutation p (delete i m)).
Proof.
  intros ? <-%insert_delete.
  rewrite delete_insert by now simpl_map. etransitivity.
  + apply apply_permutation_insert; simpl_map; eauto.
  + rewrite delete_insert by assumption. reflexivity.
Qed.

Lemma map_inj_delete {A} m i : @map_inj A m -> map_inj (delete i m).
Proof.
  intros inj_m ? ? (_ & ?)%lookup_delete_Some ? ? (_ & ?)%lookup_delete_Some.
  apply inj_m; assumption.
Qed.

Lemma apply_permutation_delete {A} p (m : Pmap A) i j :
  map_inj p -> lookup i p = Some j ->
  apply_permutation (delete i p) (delete i m) = delete j (apply_permutation p m).
Proof.
  intros inj_p H. rewrite <-pkmap_delete with (i := i).
  - apply pkmap_fun_eq. intros ? (? & (? & _)%lookup_delete_Some).
    apply lookup_delete_ne. congruence.
  - apply map_inj_equiv. assumption.
  - assumption.
Qed.

Lemma prove_eq_dom {A B} (m : Pmap A) (m' : Pmap B) :
  dom m = dom m' -> (forall i, is_Some (lookup i m) <-> is_Some (lookup i m')).
Proof. setoid_rewrite <-elem_of_dom. intros ->. auto. Qed.

Lemma equiv_map_alt {A} (m0 m1 : Pmap A) :
  equiv_map m0 m1 <-> exists p, is_permutation p m0 /\ m1 = apply_permutation p m0.
Proof.
  split.
  - intros (f & equiv_f & ->).
    assert (map_inj (map_imap (fun i _ => f i) m0)). {
      destruct equiv_f as (inj_f & _).
      rewrite map_inj_equiv. intros i Hi j G. rewrite !map_lookup_imap in *.
      destruct (lookup i m0) eqn:eqn_i; cbn in *. 2: { inversion Hi. discriminate. }
      destruct (lookup j m0) eqn:eqn_j; cbn in *. 2: { rewrite G in Hi. inversion Hi. discriminate. }
      apply inj_f; assumption. }
    exists (map_imap (fun i _ => f i) m0). split; [split | ].
    + assumption.
    + apply prove_eq_dom.
      destruct equiv_f as (_ & ?). apply dom_imap_L. intros i. rewrite elem_of_dom. firstorder.
    + apply pkmap_fun_eq. setoid_rewrite map_lookup_imap. intros i (? & ->). reflexivity.
  - intros (p & H%permutation_is_equivalence & ->). eexists. split; [exact H | reflexivity].
Qed.

Lemma map_inj_insert {A} p x (y : A) (H : forall i, lookup i p <> Some y) :
  map_inj p -> map_inj (insert x y p).
Proof.
  intros inj_p i j. destruct (decide (i = x)) as [-> | ]; simpl_map.
  - intros [=<-]. intros ? ? ? <-. apply dec_stable. intros ?. simpl_map. eapply H. eassumption.
  - intros ? i' ? ? ?.
    assert (i' <> x). { intros <-. simpl_map. congruence. }
    simpl_map. eapply inj_p; eassumption.
Qed.

Definition id_permutation {A} (m : Pmap A) : Pmap positive := map_imap (fun k _ => Some k) m.

Lemma lookup_id_permutation {A} (m : Pmap A) i :
  is_Some (lookup i m) -> lookup i (id_permutation m) = Some i.
Proof. unfold id_permutation. rewrite map_lookup_imap. intros (? & ->). reflexivity. Qed.

Lemma lookup_id_permutation_is_Some {A} (m : Pmap A) i j :
  lookup i (id_permutation m) = Some j -> i = j.
Proof.
  intros H. destruct (lookup i m) eqn:EQN.
  - rewrite lookup_id_permutation in H by auto. congruence.
  - unfold id_permutation in H. rewrite map_lookup_imap, EQN in H. discriminate.
Qed.

Lemma id_permutation_is_permutation {A} m : @is_permutation A (id_permutation m) m.
Proof.
  split.
  - intros ? ? H ? ? G <-. apply lookup_id_permutation_is_Some in H, G. congruence.
  - apply prove_eq_dom, dom_imap_L. intros ?. rewrite elem_of_dom. firstorder.
Qed.

Lemma apply_id_permutation {A} (m : Pmap A) : apply_permutation (id_permutation m) m = m.
Proof.
  apply pkmap_eq.
  - apply permutation_is_equivalence, id_permutation_is_permutation.
  - intros ? ? ?%lookup_id_permutation_is_Some. congruence.
  - reflexivity.
Qed.

Lemma injective_compose (p q : Pmap positive) :
  map_inj p -> map_inj q -> map_inj (map_compose q p).
Proof.
  intros inj_p inj_q.
  intros ? ? (? & ? & ?)%map_lookup_compose_Some_1 ? ? (? & ? & ?)%map_lookup_compose_Some_1 ?.
  eapply inj_p; [eassumption.. | ]. eapply inj_q; eauto.
Qed.

Lemma compose_permutation {A} p q (m : Pmap A) :
  is_permutation p m -> is_permutation q (apply_permutation p m) ->
  is_permutation (map_compose q p) m.
Proof.
  intros (inj_p & dom_p) (inj_q & dom_q). split.
  - apply injective_compose; assumption.
  - intros i. rewrite map_lookup_compose. split.
    + rewrite <-dom_p. destruct (lookup i p); auto.
    + rewrite <-dom_p. intros (? & H). rewrite H. apply dom_q.
      erewrite lookup_pkmap.
      * rewrite <-dom_p, H. auto.
      * rewrite <-map_inj_equiv. assumption.
      * exact H.
Qed.

Lemma apply_permutation_compose {A} p q (m : Pmap A) :
  is_permutation p m -> is_permutation q (apply_permutation p m) ->
  apply_permutation (map_compose q p) m = apply_permutation q (apply_permutation p m).
Proof.
  intros perm_p perm_q. apply pkmap_eq.
  - apply permutation_is_equivalence, compose_permutation; assumption.
  - intros i j (? & ? & ?)%map_lookup_compose_Some_1.
    erewrite lookup_pkmap; [ | eapply map_inj_equiv, perm_q | eassumption].
    symmetry. apply lookup_pkmap; [ | assumption]. apply map_inj_equiv, perm_p.
  - rewrite !size_pkmap by auto using permutation_is_equivalence. reflexivity.
Qed.

Global Instance transitive_equiv_map A : Transitive (@equiv_map A).
Proof.
  intros ? ? ?. rewrite !equiv_map_alt.
  intros (p & ? & ->) (q & ? & ->). exists (map_compose q p). split.
  - apply compose_permutation; assumption.
  - symmetry. apply apply_permutation_compose; assumption.
Qed.

Lemma is_permutation_insert {A} p (m : Pmap A) i j (H : is_Some (lookup i m))
  (G : forall k, lookup k p <> Some j) :
  is_permutation p (delete i m) -> is_permutation (insert i j p) m.
Proof.
  intros (inj_p & eq_dom). split.
  - apply map_inj_insert; assumption.
  - intros i'. rewrite lookup_insert_is_Some, eq_dom, lookup_delete_is_Some.
    destruct (decide (i = i')) as [<- | ]; intuition.
Qed.

Lemma is_permutation_delete {A} p i (a : A) m (H : lookup i m = None) :
  is_permutation p (insert i a m) ->
  exists i', lookup i p = Some i' /\ (forall j, lookup j (delete i p) <> Some i') /\
             is_permutation (delete i p) m.
Proof.
  intros (inj_p & dom_p). destruct (lookup i p) as [i' | ] eqn:EQN.
  - exists i'. split; [reflexivity | ]. split; [ | split].
    + intros j Hj. replace j with i in Hj; [simpl_map; discriminate | ].
      eapply inj_p; [eassumption | eapply lookup_delete_Some; eassumption | reflexivity].
    + apply map_inj_delete, inj_p.
    + intros j. split.
      * intros (? & ?)%lookup_delete_is_Some. specialize (dom_p j). simpl_map.
        apply dom_p. assumption.
      * intros (? & ?). rewrite lookup_delete_is_Some. split; [congruence | ].
        apply dom_p. rewrite lookup_insert_ne by congruence. auto.
  - exfalso. eapply is_Some_None. rewrite <-EQN. apply dom_p. simpl_map. auto.
Qed.

Lemma equiv_map_insert {A} m0 m1 i j (a : A) :
  equiv_map m0 m1 -> lookup i m0 = None -> lookup j m1 = None ->
  equiv_map (insert i a m0) (insert j a m1).
Proof.
  rewrite !equiv_map_alt. intros (p & (? & eq_dom) & ->) get_i j_not_in_dom.
  assert (map_inj (insert i j p)). {
    apply map_inj_insert; [ | assumption]. intros ? G.
    erewrite lookup_apply_permutation in j_not_in_dom by eassumption.
    apply mk_is_Some in G. rewrite eq_dom, j_not_in_dom in G. eapply is_Some_None, G. }
  exists (insert i j p). split; [split | ].
  - assumption.
  - setoid_rewrite lookup_insert_is_Some. firstorder.
  - erewrite apply_permutation_insert by now simpl_map. rewrite delete_insert; [reflexivity | ].
    rewrite eq_None_not_Some, eq_dom, get_i. auto.
Qed.

(* A permutation can be inverted. *)
Definition invert_permutation : Pmap positive -> Pmap positive :=
  map_fold (fun i j m => insert j i m) empty.

Lemma invert_permutation_lookup_Some p i j :
  lookup i (invert_permutation p) = Some j -> is_Some (lookup j p).
Proof.
  induction p as [ | k x p ? ? IHp] using map_first_key_ind.
  + unfold invert_permutation. rewrite map_fold_empty. discriminate.
  + unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
    destruct (decide (x = i)) as [-> | ].
    * simpl_map. intros [=->]. simpl_map. auto.
    * simpl_map. destruct (decide (j = k)) as [-> | ]; simpl_map; auto.
Qed.

Lemma lookup_Some_invert_permutation p i j (inj_p : map_inj p) :
  lookup i p = Some j -> lookup j (invert_permutation p) = Some i.
Proof.
  intros H%insert_delete. unfold invert_permutation. rewrite <-H.
  rewrite map_fold_insert_L.
  - simpl_map. reflexivity.
  - rewrite H. intros ? ? ? ? ? diff. intros. apply insert_commute. intros ?. apply diff.
    eapply inj_p; eassumption.
  - simpl_map. reflexivity.
Qed.

Lemma id_permutation_same_domain {A B} (m : Pmap A) (n : Pmap B)
  (eq_dom : forall i, is_Some (lookup i m) <-> is_Some (lookup i n)) :
  id_permutation m = id_permutation n.
Proof.
  apply map_eq. intros i. unfold id_permutation. rewrite !map_lookup_imap.
  destruct (lookup i m) eqn:EQN.
  - apply mk_is_Some in EQN. rewrite eq_dom in EQN. destruct EQN as (? & ->). reflexivity.
  - rewrite eq_None_not_Some, eq_dom, <-eq_None_not_Some in EQN. rewrite EQN. reflexivity.
Qed.

Lemma invert_permutation_inj : forall m, map_inj m -> map_inj (invert_permutation m).
Proof.
  induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - auto.
  - intros Hinj. unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
    apply map_inj_insert.
    + intros i G. apply invert_permutation_lookup_Some in G.
      rewrite H in G. eapply is_Some_None, G.
    + apply IHm. erewrite <-delete_insert by eassumption. apply map_inj_delete. exact Hinj.
Qed.

Lemma dom_invert_permutation : forall m, map_inj m -> dom (invert_permutation m) = map_img m.
Proof.
  induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - reflexivity.
  - intros inj_m. unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
    rewrite dom_insert_L. rewrite map_img_insert_notin_L by assumption. f_equal.
    apply IHm. eapply map_inj_delete in inj_m. rewrite delete_insert in inj_m by assumption.
    exact inj_m.
Qed.

Lemma invert_permutation_is_permutation {A} perm (m : Pmap A) :
  is_permutation perm m ->
  is_permutation (invert_permutation perm) (apply_permutation perm m).
Proof.
  intros (inj_perm & dom_perm). split.
  - apply invert_permutation_inj. exact inj_perm.
  - intros k. rewrite <-elem_of_dom. rewrite dom_invert_permutation by assumption.
    rewrite elem_of_map_img. split.
    + intros (i & ?). erewrite lookup_apply_permutation; eauto. rewrite <-dom_perm. auto.
    + apply lookup_pkmap_rev. apply map_inj_equiv. assumption.
Qed.

Lemma map_compose_notin {A B C} `{FinMap A MA} `{FinMap B MB} (m : MB C) (n : MA B) (c : C) (b : B) :
  (forall a, lookup a n <> Some b) -> map_compose (insert b c m) n = map_compose m n.
Proof.
  intros G. apply omap_ext. intros ? ? get_b.
  apply lookup_insert_ne. intros <-. eapply G, get_b.
Qed.

Lemma compose_invert_permutation p :
  map_inj p -> map_compose (invert_permutation p) p = id_permutation p.
Proof.
  induction p as [ | k x p ? ? IHp] using map_first_key_ind.
  - reflexivity.
  - intros p_inj.
    unfold invert_permutation, id_permutation.
    rewrite map_fold_insert_first_key by assumption.
    erewrite map_imap_insert_Some by reflexivity.
    erewrite map_compose_insert_Some by (simpl_map; reflexivity). f_equal.
    rewrite map_compose_notin.
    + apply IHp. apply (map_inj_delete _ k) in p_inj.
      rewrite delete_insert in p_inj by assumption. exact p_inj.
    + intros i ?. replace i with k in *; [congruence | ].
      eapply p_inj; [simpl_map; reflexivity | | reflexivity].
      destruct (decide (i = k)) as [<- | ]; simpl_map; reflexivity.
Qed.

Global Instance equiv_map_sym {A} : Symmetric (@equiv_map A).
Proof.
  intros ? ?. rewrite !equiv_map_alt. intros (p & H & ->). exists (invert_permutation p).
  pose proof (invert_permutation_is_permutation _ _ H).
  split; [assumption | ]. rewrite <-apply_permutation_compose by assumption.
  rewrite compose_invert_permutation by apply H.
  symmetry. erewrite id_permutation_same_domain by apply H. apply apply_id_permutation.
Qed.

Lemma map_sum_permutation {A} weight (m : Pmap A) :
  forall p, is_permutation p m -> map_sum weight (apply_permutation p m) = map_sum weight m.
Proof.
  induction m as [ | k x m ? _ IHm] using map_first_key_ind; intros p perm_p.
  - unfold apply_permutation. rewrite map_fold_empty. reflexivity.
  - destruct (perm_p) as (inj_p & _).
    apply is_permutation_delete in perm_p; [ | assumption].
    destruct perm_p as (k' & get_k' & ? & perm_p).
    erewrite apply_permutation_insert by eassumption.
    rewrite !map_sum_insert.
    + rewrite IHm by assumption. reflexivity.
    + assumption.
    + apply lookup_pkmap_None. assumption.
Qed.

Lemma permutation_forall {A} (P : A -> Prop) p (m : Pmap A) :
  is_permutation p m -> map_Forall (fun _ => P) m -> map_Forall (fun _ => P) (apply_permutation p m).
Proof.
  intros (inj_p & dom_p). intros H i a G.
  pose proof (mk_is_Some _ _ G) as K.
  apply lookup_pkmap_rev in K; [ | now apply map_inj_equiv]. destruct K.
  erewrite lookup_apply_permutation in G by eassumption.
  eapply H, G.
Qed.

Section UnionMaps.
  Context {V : Type}.

  (* The property union_maps A B C is true if the map C contains all of the pairs (key, element) of
   * A, and all the elements of B with possibly different keys.

   * Example: let's take A = {[1 := x; 2 := y|} and B = {[1 := z]}. Then union_maps A B C is true for
     any map C = {[ 1 := x; 2 := y; i := z]} for any i different from 1 or 2. *)
  Inductive union_maps : Pmap V -> Pmap V -> Pmap V -> Prop :=
    | UnionEmpty A : union_maps A empty A
    | UnionInsert A B C i j x :
        lookup j A = None -> lookup i B = None ->
        union_maps (insert j x A) B C -> union_maps A (insert i x B) C.

  Lemma union_contains_left A B C i x (Hunion : union_maps A B C) :
    lookup i A = Some x -> lookup i C = Some x.
  Proof.
    induction Hunion as [ | A B C i' j' ? ? ? ? IH].
    - auto.
    - intros ?. assert (i <> j') by congruence. simpl_map. auto.
  Qed.

  Lemma union_contains_right A B C i x (Hunion : union_maps A B C) :
    lookup i B = Some x -> exists j, lookup j C = Some x.
  Proof.
    induction Hunion as [ | A B C i' j' ? ? ? ? IH].
    - simpl_map. discriminate.
    - intros ?. destruct (decide (i = i')) as [<- | ].
      + exists j'. eapply union_contains_left; [eassumption | ]. simpl_map. auto.
      + simpl_map. auto.
  Qed.

  Variable (A B : Pmap V).

  Lemma union_maps_permutation C (H : union_maps A B C) :
    forall pA pB, is_permutation pA A -> is_permutation pB B ->
    exists pC, is_permutation pC C /\ union_maps (apply_permutation pA A) (apply_permutation pB B) (apply_permutation pC C).
  Proof.
    induction H as [ | A B ? i j v get_j i_notin ? IH].
    - eexists. split; [eassumption | constructor].
    - intros pA pB (? & dom_A) equiv_B'.
      assert (map_inj pB) by apply equiv_B'.
      apply is_permutation_delete in equiv_B'; [ | assumption].
      destruct equiv_B' as (i' & HpB & ? & equiv_B).
      destruct (exist_fresh (dom (apply_permutation pA A))) as (j' & Hj'%not_elem_of_dom).
      specialize (IH (insert j j' pA) (delete i pB)).
      assert (lookup j pA = None) by now rewrite eq_None_not_Some, dom_A, get_j.
      assert (map_inj (insert j j' pA)). {
        apply map_inj_insert; [ | assumption]. intros k Hk.
        erewrite lookup_apply_permutation in Hj' by eassumption.
        rewrite eq_None_not_Some, <-dom_A, Hk in Hj'. auto. }
      destruct IH as (pC & ? & IHunion).
      + split; [assumption | ]. setoid_rewrite lookup_insert_is_Some.
        intros k. specialize (dom_A k). tauto.
      + exact equiv_B.
      + exists pC. split; [assumption | ].
        erewrite apply_permutation_insert by eassumption.
        rewrite apply_permutation_insert with (j := j') in IHunion by now simpl_map.
        rewrite delete_insert in IHunion by assumption.
        apply UnionInsert with (j := j'); [ | now apply lookup_pkmap_None | ]; assumption.
  Qed.

  Lemma union_maps_permutation_rev C (H : union_maps A B C) :
    forall pC, is_permutation pC C ->
      exists pA pB, is_permutation pA A /\ is_permutation pB B /\
                    union_maps (apply_permutation pA A) (apply_permutation pB B) (apply_permutation pC C).
  Proof.
    induction H as [ | A B ? i j v get_j i_notin ? IH].
    - intros pC ?. eexists pC, _. split; [assumption | ].
      split; [apply id_permutation_is_permutation | ]. constructor.
    - intros pC pC_perm. specialize (IH _ pC_perm).
      destruct IH as (pA & pB & perm_pA & perm_pB & IH).
      destruct (perm_pA) as (inj_pA & _).
      apply is_permutation_delete in perm_pA; [ | assumption].
      destruct perm_pA as (j' & ? & ? & perm_pA).
      assert (lookup i pB = None).
      { rewrite eq_None_not_Some. destruct perm_pB as (_ & ->). rewrite i_notin. auto. }
      destruct (exist_fresh (map_img (SA := Pset) pB)) as (i' & Hi').
      rewrite not_elem_of_map_img in Hi'.
      erewrite <-(delete_insert B) in perm_pB by eassumption.
      eapply is_permutation_insert in perm_pB; [ | simpl_map; eauto..].
      eexists _, _. split; [exact perm_pA | ]. split; [exact perm_pB | ].
      erewrite apply_permutation_insert; [ | apply perm_pB | simpl_map; eauto..].
      rewrite delete_insert by assumption.
      econstructor; [eauto using lookup_pkmap_None.. | ].
      rewrite <-apply_permutation_insert; assumption.
  Qed.

  Lemma exists_union_maps (m1 : Pmap V) : forall m0, exists m2, union_maps m0 m1 m2.
  Proof.
    induction m1 as [| i x m1 ? _ IH] using map_first_key_ind.
    - intros m. exists m. constructor.
    - intros m0. destruct (exist_fresh (dom m0)) as (j & ?%not_elem_of_dom).
      specialize (IH (insert j x m0)). destruct IH as (m2 & ?).
      exists m2. econstructor; eassumption.
  Qed.

  Lemma union_maps_empty X Y : union_maps X empty Y -> X = Y.
  Proof. inversion 1; [reflexivity | ]. exfalso. eapply insert_non_empty. eassumption. Qed.

  Lemma union_maps_insert_r_l (m0 m1 m2 : Pmap V) i x :
    union_maps m0 (insert i x m1) m2 -> lookup i m1 = None ->
    exists j, union_maps (insert j x m0) m1 m2 /\ lookup j m0 = None.
  Proof.
    intros H. remember (insert i x m1) as m'1 eqn:EQN. revert m1 EQN.
    induction H as [ | m0 m'1 ? i' j y ? ? ? IH].
    - intros ? EQN. symmetry in EQN. apply insert_non_empty in EQN. contradiction.
    - intros m1 EQN ?.
      destruct (decide (i = i')) as [<- | ].
      + assert (y = x).
        { apply (f_equal (lookup i)) in EQN. simpl_map. congruence. }
        assert (m'1 = m1).
        { apply (f_equal (delete i)) in EQN. now rewrite !delete_insert in EQN by assumption. }
        subst. exists j. split; assumption.
      + specialize (IH (delete i' m1)).
        destruct IH as (j' & union_ind & ?).
        { apply (f_equal (delete i')) in EQN. rewrite delete_insert in EQN by assumption.
          rewrite <-delete_insert_ne by congruence. exact EQN. }
        { simpl_map. assumption. }
        assert (j <> j'). { intros <-. simpl_map. discriminate. }
        exists j'. split.
        * assert (lookup i' m1 = Some y) as <-%insert_delete.
          { apply (f_equal (lookup i')) in EQN. now simpl_map. }
          rewrite insert_commute in union_ind by congruence.
          econstructor; [ | | exact union_ind]; now simpl_map.
        * simpl_map. assumption.
  Qed.

  Lemma map_sum_union_maps f m0 m1 m2 :
    union_maps m0 m1 m2 -> map_sum f m2 = map_sum f m0 + map_sum f m1.
  Proof.
    induction 1.
    - rewrite map_sum_empty. lia.
    - rewrite map_sum_insert in * by assumption. lia.
  Qed.

  Lemma union_maps_delete_l X Y Z k v (H : union_maps (insert k v X) Y Z) :
    lookup k X = None -> union_maps X Y (delete k Z).
  Proof.
    remember (insert k v X) as X' eqn:EQN. revert X k v EQN.
    induction H; intros X k v ->.
    - intros ?. rewrite delete_insert by assumption. constructor.
    - intros ?.
      assert (k <> j). { intros <-. simpl_map. discriminate. }
      simpl_map.
      eapply UnionInsert with (j := j); [assumption.. | ].
      eapply IHunion_maps.
      + rewrite insert_commute by congruence. reflexivity.
      + simpl_map. assumption.
  Qed.

  Lemma union_maps_insert_l X Y Z k v (H : union_maps X Y Z) :
    lookup k Z = None -> union_maps (insert k v X) Y (insert k v Z).
  Proof.
    intros G. induction H as [ | ? ? ? ? j ? ? ? Hunion].
    - constructor.
    - assert (j <> k).
      { intros <-. eapply union_contains_left in Hunion; [ | apply lookup_insert].
        congruence. }
      apply UnionInsert with (j := j).
      + simpl_map. assumption.
      + assumption.
      + rewrite insert_commute by congruence. auto.
  Qed.

  Lemma union_contains C i x (Hunion : union_maps A B C) :
    lookup i C = Some x ->
    lookup i A = Some x \/ (exists j, lookup j B = Some x /\ union_maps A (delete j B) (delete i C)).
  Proof.
    intros H. induction Hunion as [ | A B C i' j' ? ? ? ? IH].
    - auto.
    - destruct (IH H) as [ | (j & ? & Hunion')].
      + destruct (decide (i = j')) as [<- | ].
        * right. exists i'. simpl_map. rewrite delete_insert by assumption.
          split; [assumption | ]. eapply union_maps_delete_l; eassumption.
        * simpl_map. auto.
      + right. exists j. assert (i' <> j) by congruence. simpl_map. split; [reflexivity | ].
        rewrite delete_insert_ne by congruence. econstructor; simpl_map; eassumption.
  Qed.

  Lemma union_maps_fmap C (f : V -> V) :
    union_maps A B C -> union_maps (fmap f A) (fmap f B) (fmap f C).
  Proof.
    induction 1.
    - constructor.
    - rewrite fmap_insert in *. econstructor; simpl_map; rewrite ?fmap_None; eassumption.
  Qed.

  Lemma union_maps_fmap_rev C' (f : V -> V) :
    union_maps (fmap f A) (fmap f B) C' -> exists C, C' = fmap f C /\ union_maps A B C.
  Proof.
    intros H. remember (fmap f A) eqn:EQN_A. remember (fmap f B) eqn:EQN_B.
    symmetry in EQN_B. revert A B EQN_A EQN_B. induction H; intros ? ? ->.
    - intros ?%fmap_empty_inv. subst. eexists. split; [reflexivity | constructor].
    - intros EQN_B%fmap_insert_inv; [ | assumption]. destruct EQN_B as (? & ? & -> & ? & -> & ->).
      edestruct IHunion_maps as (? & ? & ?).
      + symmetry. apply fmap_insert.
      + reflexivity.
      + eexists. split; [eassumption | ]. econstructor; try eassumption.
        simpl_map. eapply fmap_None; eassumption.
  Qed.
End UnionMaps.

Lemma union_maps_invert_permutation {V} (A B C' : Pmap V) pA pB :
  is_permutation pA A -> is_permutation pB B ->
  union_maps (apply_permutation pA A) (apply_permutation pB B) C' ->
  exists C, equiv_map C C' /\ union_maps A B C.
Proof.
  intros HA HB H.
  assert (equiv_map A (apply_permutation pA A)) as H'A. { apply equiv_map_alt. exists pA. auto. }
  assert (equiv_map B (apply_permutation pB B)) as H'B. { apply equiv_map_alt. exists pB. auto. }
  symmetry in H'A, H'B. rewrite equiv_map_alt in H'A, H'B.
  destruct H'A as (? & ? & ?). destruct H'B as (? & ? & ?).
  eapply union_maps_permutation in H; [ | eassumption..].
  destruct H as (pC & ? & H).
  assert (equiv_map C' (apply_permutation pC C')) as HC. { apply equiv_map_alt. exists pC. auto. }
  eexists. split.
  - symmetry. eassumption.
  - congruence.
Qed.

Lemma union_maps_unique {V} (X Y Z Z' : Pmap V) :
  union_maps X Y Z -> union_maps X Y Z' -> equiv_map Z Z'.
Proof.
  intros H. revert Z'. induction H as [ | ? ? ? ? ? v ? ? H IH].
  - intros ? ->%union_maps_empty. reflexivity.
  - intros Z' G. apply union_maps_insert_r_l in G; [ | assumption].
    destruct G as (k & G & ?).
    assert (equiv_map (insert k v A) (insert j v A)) as K.
    { apply equiv_map_insert; [reflexivity | assumption..]. }
    rewrite equiv_map_alt in K. destruct K as (p & ? & K).
    eapply union_maps_permutation in G; [ | eassumption | apply id_permutation_is_permutation].
    rewrite <-K in G. rewrite apply_id_permutation in G.
    destruct G as (q & ? & G). etransitivity.
    + apply IH. exact G.
    + symmetry. rewrite equiv_map_alt. exists q. auto.
Qed.

Lemma union_maps_assoc {V} (s0 s1 s2 s'2 A B C : Pmap V) :
  union_maps A B C -> union_maps s0 B s1 -> union_maps s1 A s2 -> union_maps s0 C s'2 ->
  equiv_map s2 s'2.
Proof.
  intros H. revert s0 s1 s2 s'2. induction H; intros s0 s1 s2 s'2.
  - intros ->%union_maps_empty. apply union_maps_unique.
  - intros (k & G & get_s0_k)%union_maps_insert_r_l; [ | assumption].
    assert (lookup k s1 = Some x).
    { eapply union_contains_left; [eassumption | ]. simpl_map. reflexivity. }
    apply union_maps_delete_l in G; [ | assumption].
    intros. eapply IHunion_maps.
    + eassumption.
    + apply UnionInsert with (j := k); simpl_map; [easy.. | ].
      rewrite insert_delete; assumption.
    + assumption.
Qed.

(* An injective map can always be extended so that its domain contains the set s. *)
Lemma extend_inj_map s (m : Pmap positive) (H : map_inj m) :
  exists m', subseteq m m' /\ subseteq s (dom m') /\ map_inj m'.
Proof.
  induction s as [ | i ? ? (m' & ? & ? & ?)] using set_ind_L.
  - exists m. set_solver.
  - destruct (decide (elem_of i (dom m'))) as [ | ?%not_elem_of_dom].
    + exists m'. set_solver.
    + destruct (exist_fresh (map_img (SA := Pset) m')) as (j & ?).
      exists (insert i j m'). repeat split.
      * transitivity m'; [ | apply insert_subseteq]; assumption.
      * set_solver.
      * apply map_inj_insert; [ | assumption].
        intros ?. apply (not_elem_of_map_img_1 (SA := Pset)). assumption.
Qed.

(* TODO: should be a part of std++ *)
Lemma alter_insert_delete {K M A} `{FinMap K M} (m : M A) (k : K) (a : A) (f : A -> A) :
  lookup k m = Some a -> alter f k m = insert k (f a) (delete k m).
Proof.
  intros G. apply map_eq. intros k'.
  destruct (decide (k' = k)) as [-> | ]; simpl_map; reflexivity.
Qed.

Lemma kmap_compose {A B C V} `{FinMap A MA} `{FinMap B MB} `{FinMap C MC}
  (m : MA V) (f : A -> B) (g : B -> C) :
  Inj eq eq f -> Inj eq eq g -> kmap (M2 := MC) g (kmap (M2 := MB) f m) = kmap (compose g f) m.
Proof.
  intros. apply map_eq. intros c. destruct (lookup c (kmap (compose g f) m)) eqn:EQN.
  - rewrite lookup_kmap_Some in EQN by typeclasses eauto. rewrite lookup_kmap_Some by assumption.
    destruct EQN as (a & -> & ?). exists (f a). split; [reflexivity | ].
    rewrite lookup_kmap_Some by assumption. exists a. eauto.
  - rewrite lookup_kmap_None in EQN by typeclasses eauto. rewrite lookup_kmap_None by assumption.
    intros b ->. rewrite lookup_kmap_None by assumption. intros a ->. apply EQN. reflexivity.
Qed.

Lemma prove_rel A B (R : A -> B -> Prop) x y z : R x y -> y = z -> R x z.
Proof. congruence. Qed.

Lemma prove_rel_n A B (R : nat -> A -> B -> Prop) x y z m n : R m x y -> m = n -> y = z -> R n x z.
Proof. congruence. Qed.
