Require Import Coq.Program.Equality.
Require Import List.
Open Scope list_scope.

Section Adj_Perm.

Variable T : Type.

Inductive adj : list T -> T -> list T -> Prop :=
  | adj_same : forall X L, adj L X (X :: L)
  | adj_diff : forall X Y K L, adj K X L -> adj (Y :: K) X (Y :: L).

Theorem adj_swap :
  forall J X K Y L,
  adj J X K -> adj K Y L ->
  exists KK, adj J Y KK /\ adj KK X L.
Proof.
intros until 2 ; revert J X H ; induction H0.
* intros ; inversion H.
  - exists (X :: J). split. refine (adj_same _ _). refine (adj_diff _ _ _ _ (adj_same _ _)).
  - exists (X :: Y :: K) ; split.
    + refine (adj_same _ _).
    + refine (adj_diff _ _ _ _ (adj_diff _ _ _ _ _)). auto.
* intros ; inversion H.
  - exists L ; split ; [ exact H0 | refine (adj_same _ _) ].
  - destruct (IHadj _ _ H4) ; destruct H6 ; rename x into XX.
    exists (Y :: XX) ; split ; refine (adj_diff _ _ _ _ _) ; auto.
Qed.

Inductive perm : list T -> list T -> Prop :=
  | perm_nil : perm nil nil
  | perm_adj : forall X KK K LL L, adj KK X K -> adj LL X L -> perm KK LL -> perm K L.

Theorem perm_refl : forall L, perm L L.
Proof.
induction L ; [ exact perm_nil | refine (perm_adj a _ _ _ _ (adj_same _ _) (adj_same _ _) IHL) ].
Qed.

Theorem perm_sym : forall K L, perm K L -> perm L K.
Proof.
induction 1 ; [ exact perm_nil | refine (perm_adj _ _ _ _ _ H0 H IHperm) ].
Qed.

Theorem perm_nil_1 : forall L, perm nil L -> L = nil.
Proof.
inversion 1 ; [ reflexivity | inversion H0 ].
Qed.

Theorem perm_nil_2 : forall L, perm L nil -> L = nil.
Proof.
inversion 1 ; [ reflexivity | inversion H1 ].
Qed.

Theorem perm_cons_1 : forall X K L,
  perm (X :: K) L ->
  exists J, adj J X L /\ perm K J.
Proof.
intros X K L Hp. dependent induction Hp generalizing K.
inversion H.
* exists LL ; rewrite <- H4, <- H5 ; auto.
* symmetry in H2 ; rewrite H1 in H2.
  destruct (IHHp _ H2) as [ Z HH ] ; destruct HH.
  destruct (adj_swap _ _ _ _ _ H6 H0) as [ ZZ HH ] ; destruct HH.
  exists ZZ ; split ; [ auto | refine (perm_adj _ _ _ _ _ H4 H8 H7) ].
Qed.

Theorem perm_cons_2 : forall X K L,
  perm K (X :: L) ->
  exists J, adj J X K /\ perm J L.
Proof.
intros until 1. dependent induction H generalizing L.
inversion H0.
* exists KK ; rewrite <- H5, <- H6 ; auto.
* symmetry in H3 ; rewrite H2 in H3.
  destruct (IHperm _ H3) as [ Z HH ] ; destruct HH.
  destruct (adj_swap _ _ _ _ _ H7 H) as [ ZZ HH ] ; destruct HH.
  exists ZZ ; split ; [ auto | refine (perm_adj _ _ _ _ _ H9 H5 H8) ].
Qed.

Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
Proof.
intros J K ; revert J ; induction K.
* intros ; rewrite (perm_nil_2 _ H) ; rewrite (perm_nil_1 _ H0) ; exact perm_nil.
* intros.
  destruct (perm_cons_2 _ _ _ H) as [ JJ HH ] ; destruct HH ; clear H.
  destruct (perm_cons_1 _ _ _ H0) as [ LL HH ] ; destruct HH ; clear H0.
  refine (perm_adj  _ _ _ _ _ H1 H (IHK _ _ H2 H3)).
Qed.

Theorem adj_same_source : forall J X L1 L2,
  adj J X L1 ->
  adj J X L2 ->
  perm L1 L2.
Proof.
intros. refine (perm_adj _ _ _ _ _ H H0 (perm_refl _)).
Qed.

Theorem adj_same_result : forall J K X L,
  adj J X L ->
  adj K X L ->
  perm J K.
Proof.
intros until 1. dependent induction H generalizing K.
* intros. inversion H.
  - eapply perm_refl.
  - refine (perm_adj _ _ _ _ _ H3 (adj_same _ _) (perm_refl K0)).
* intros. inversion H0.
  - rewrite <- H4. refine (perm_adj _ _ _ _ _ (adj_same _ _) H (perm_refl K0)).
  - refine (perm_adj _ _ _ _ _ (adj_same _ _) (adj_same _ _) (IHadj _ H4)).
Qed.

Theorem adj_same_result_diff : forall J X K B L,
  adj J X L ->
  adj K B L ->
  (X = B /\ perm J K) \/
  exists KK, adj KK X K.
Proof.
intros until 1. dependent induction H generalizing K B.
* intros. inversion H.
  - pose (HH := perm_refl L). auto.
  - right. exists K0. eapply adj_same.
* intros. inversion H0.
  - right. exists K0. auto.
  - destruct (IHadj K1 B H4) as [ HH | HH ].
    + destruct HH. left. split. auto. refine (perm_adj _ _ _ _ _ (adj_same Y _) (adj_same Y _) H7).
    + destruct HH as [ KK ]. right. exists (Y :: KK).
      eapply adj_diff. auto.
Qed.

Theorem perm_invert : forall X J K JJ KK,
  perm J K ->
  adj JJ X J ->
  adj KK X K ->
  perm JJ KK.
Proof.
intros until 1. dependent induction H generalizing X JJ KK.
* intros. inversion H.
* intros.
  destruct (adj_same_result_diff _ _ _ _ _ H2 H) as [ HH | HH ].
  - destruct HH ; rewrite <- H4 in * ; clear H4.
    refine (perm_trans _ _ _ H5 (perm_trans _ _ _ H1 _)).
    refine (adj_same_result _ _ _ _ H0 H3).
  - destruct HH as [ Z ].
    destruct (adj_same_result_diff _ _ _ _ _ H3 H0) as [ HH | HH ].
    + destruct HH. rewrite <- H5 in H.
      eapply perm_trans.
      eapply adj_same_result. exact H2. exact H.
      eapply perm_trans. exact H1. eapply perm_sym. auto.
    + destruct HH as [ ZZ ].
      destruct (adj_swap _ _ _ _ _ H4 H) as [ U HH ] ; destruct HH.
      destruct (adj_swap _ _ _ _ _ H5 H0) as [ UU HH ] ; destruct HH.
      eapply perm_trans.
      exact (adj_same_result _ _ _ _ H2 H7).
      eapply perm_trans. eapply perm_adj. exact H6. exact H8.
      eapply IHperm. exact H4. exact H5.
      exact (adj_same_result _ _ _ _ H9 H3).
Qed.

Theorem adj_perm_result : forall J K X JJ,
  perm J K ->
  adj JJ X J ->
  exists KK, adj KK X K /\ perm JJ KK.
Proof.
intros until 1. dependent induction H generalizing X JJ.
* intros. inversion H.
* intros.
  destruct (adj_same_result_diff _ _ _ _ _ H2 H) as [ HH | HH ].
  - destruct HH. exists LL. rewrite <- H3 in H0.
    pose (HH := perm_trans _ _ _ H4 H1). auto.
  - destruct HH as [ Z ].
    destruct (adj_swap _ _ _ _ _ H3 H) as [ ZZ HH ] ; destruct HH.
    destruct (IHperm _ _ H3) as [ U HH ] ; destruct HH.
    destruct (adj_swap _ _ _ _ _ H6 H0) as [ UU HH ] ; destruct HH.
    assert (perm ZZ UU). eapply perm_adj. exact H4. exact H8. exact H7.
    exists UU. split. auto.
    eapply perm_trans. eapply adj_same_result. exact H2. exact H5. auto.
Qed.

Theorem adj_perm_source : forall J K A L,
  perm J K ->
  adj J A L ->
  exists LL, adj K A LL /\ perm L LL.
Proof.
intros.
assert (adj K A (A :: K)). eapply adj_same.
exists (A :: K). split. auto.
refine (perm_adj _ _ _ _ _ H0 H1 H).
Qed.

End Adj_Perm.
