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

Lemma perm_nil_1 : forall L, perm nil L -> L = nil.
Proof.
  inversion 1 ; [ reflexivity | inversion H0 ].
Qed.

Lemma perm_nil_2 : forall L, perm L nil -> L = nil.
Proof.
  inversion 1 ; [ reflexivity | inversion H1 ].
Qed.

Lemma perm_uncons_1 : forall X K L,
  perm (X :: K) L ->
  exists J, adj J X L /\ perm K J.
Proof.
  intros X K L Hp ; dependent induction Hp generalizing K ; inversion H.
  * exists LL ; rewrite <- H4, <- H5 ; auto.
  * symmetry in H2 ; rewrite H1 in H2.
    destruct (IHHp _ H2) as [ Z HH ] ; destruct HH.
    destruct (adj_swap _ _ _ _ _ H6 H0) as [ ZZ HH ] ; destruct HH.
    exists ZZ ; split ; [ auto | refine (perm_adj _ _ _ _ _ H4 H8 H7) ].
Qed.

Lemma perm_uncons_2 : forall X K L,
  perm K (X :: L) ->
  exists J, adj J X K /\ perm J L.
Proof.
  intros until 1 ; dependent induction H generalizing L ; inversion H0.
  * exists KK ; rewrite <- H5, <- H6 ; auto.
  * symmetry in H3 ; rewrite H2 in H3.
    destruct (IHperm _ H3) as [ Z HH ] ; destruct HH.
    destruct (adj_swap _ _ _ _ _ H7 H) as [ ZZ HH ] ; destruct HH.
    exists ZZ ; split ; [ auto | refine (perm_adj _ _ _ _ _ H9 H5 H8) ].
Qed.

Lemma list_finite : forall (X : T) L, (X :: L) = L -> False.
Proof.
  induction L. intros.
  * discriminate H.
  * intros. inversion H. rewrite H1 in IHL. eapply IHL. auto.
Qed.

Lemma adj_grows : forall X L,
  adj L X L -> False.
Proof.
  induction L ; intros ; inversion H.
  - refine (list_finite _ _ H4).
  - auto.
Qed.

Lemma adj_same_invert : forall X K L,
  adj K X (X :: L) ->
  perm K L.
Proof.
  intros. inversion_clear H.
  * now refine (perm_refl L).
  * eapply perm_adj.
    eapply adj_same. exact H0.
    now refine (perm_refl K0).
Qed.

Ltac adj_one :=
  match goal with
  | [ H : adj ?L ?X nil |- _ ] =>
      now inversion H
  | [ H : adj ?L ?X ?L |- _ ] =>
      now destruct (adj_grows X L H)
  | [ H : adj ?K ?X (?X :: ?L) |- _ ] =>
      cut (perm K L) ; [ clear H ; intro H |
        now refine (adj_same_invert X K L H)
      ]
  | [ |- adj ?K ?X (?X :: ?K) ] =>
      now refine (adj_same X K)
  | [ |- adj (?Y :: ?J) ?X (?Y :: ?K) ] =>
      cut (adj J X K) ; [
        let HH := fresh in intro HH ; now refine (@adj_diff X Y J K HH)
      | ]
  | [ |- context [?X :: ?K] ] =>
      let L := fresh "L" in
      let Heq := fresh "HeqL" in
      remember (X :: K) as L eqn:Heq ;
      assert (adj K X L) ; [ rewrite Heq ; now refine (adj_same X K) | ]
  end.

Ltac perm_one :=
  match goal with
  | [ H : perm nil ?L |- _ ] =>
      let HH := fresh in
      pose (HH := perm_nil_1 L H) ; rewrite HH in * ; clear H HH
  | [ H : perm ?L nil |- _ ] =>
      let HH := fresh in
      pose (HH := perm_nil_2 L H) ; rewrite HH in * ; clear H HH
  | [ H : perm ?K (?X :: ?L) |- _ ] =>
      let KK := fresh K in
      let HH := fresh in
      destruct (perm_uncons_2 X K L H) as [ KK HH ] ; clear H ; destruct HH
  | [ H : perm (?X :: ?K) ?L |- _ ] =>
      let KK := fresh K in
      let HH := fresh in
      destruct (perm_uncons_1 X K L H) as [ KK HH ] ; clear H ; destruct HH
  | [ |- perm ?L ?L ] =>
      now refine (perm_refl L)
  | [ |- perm (?X :: ?K) (?X :: ?L) ] =>
      refine (perm_adj X K (X :: K) L (X :: L) (adj_same X K) (adj_same X L) _)
  | [ H : perm ?K ?L |- perm ?L ?K ] =>
      now refine (perm_sym K L H)
  | [ H1 : adj ?JJ ?X ?J, H2 : adj ?KK ?X ?K |- perm ?J ?K ] =>
      cut (perm JJ KK) ; [
        let HH := fresh in intro HH ; now refine (@perm_adj X JJ J KK K H1 H2 HH)
      | ]
  end.

Ltac ms_simpl := repeat (intros ; eauto ; (adj_one || perm_one)).

Theorem perm_trans : forall J K L, perm J K -> perm K L -> perm J L.
Proof.
  intros until K. dependent induction K generalizing J ; now ms_simpl.
Qed.

Theorem adj_same_source : forall J X L1 L2,
  adj J X L1 ->
  adj J X L2 ->
  perm L1 L2.
Proof.
  ms_simpl.
Qed.

Theorem adj_same_result : forall J K X L,
  adj J X L ->
  adj K X L ->
  perm J K.
Proof.
intros until 1. dependent induction H generalizing K.
* now ms_simpl.
* intros. inversion H0.
  - rewrite <- H4 ; now ms_simpl.
  - now ms_simpl.
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
  - now ms_simpl.
* intros. inversion H0.
  - now ms_simpl.
  - destruct (IHadj K1 B H4) as [ HH | HH ].
    + destruct HH. left. split. auto. refine (perm_adj _ _ _ _ _ (adj_same Y _) (adj_same Y _) H7).
    + destruct HH as [ KK ]. right. exists (Y :: KK).
      eapply adj_diff. auto.
Qed.

(* Rest have not been ms_simpl'd *)
(* 2016-08-10 16:12:24+0200 *)

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
