Require Import Coq.Program.Equality.
Require Import List.
Open Scope list_scope.

Section Adj_Perm.

Variable T : Type.

Inductive adj : list T -> T -> list T -> Prop :=
  | adj_same : forall X L, adj L X (X :: L)
  | adj_diff : forall X Y K L, adj K X L -> adj (Y :: K) X (Y :: L).

Theorem adj_swap_lem :
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

Ltac adj_swap H1 H2 KK :=
  let H := fresh in
  destruct (adj_swap_lem _ _ _ _ _ H1 H2) as [ KK H ] ; destruct H.

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
    adj_swap H6 H0 U.
    exists U ; split ; [ trivial | refine (perm_adj _ _ _ _ _ H4 H8 H7) ].
Qed.

Lemma perm_uncons_2 : forall X K L,
  perm K (X :: L) ->
  exists J, adj J X K /\ perm J L.
Proof.
  intros until 1 ; dependent induction H generalizing L ; inversion H0.
  * exists KK ; rewrite <- H5, <- H6 ; auto.
  * symmetry in H3 ; rewrite H2 in H3.
    destruct (IHperm _ H3) as [ Z HH ] ; destruct HH.
    adj_swap H7 H U.
    exists U ; split ; [ auto | refine (perm_adj _ _ _ _ _ H9 H5 H8) ].
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
  end.

Ltac perm_one :=
  match goal with
  | [ H : perm nil ?L |- _ ] =>
      rewrite (perm_nil_1 L H) in * ; clear H
  | [ H : perm ?L nil |- _ ] =>
      rewrite (perm_nil_2 L H) in * ; clear H
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

(* This is the most questionable simplification rule *)
Ltac adjify_one :=
  match goal with
  | [ |- context [?X :: ?K] ] =>
      let L := fresh "L" in
      let Heq := fresh "HeqL" in
      remember (X :: K) as L eqn:Heq ;
      assert (adj K X L) ; [ rewrite Heq ; now refine (adj_same X K) | ]
  end.

Ltac ms_simpl := repeat (intros ; eauto ; (adj_one || perm_one || adjify_one)).

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

Lemma adj_same_result_diff_lem : forall J X K Y L,
  adj J X L ->
  adj K Y L ->
  (X = Y /\ perm J K) \/
  exists KK, adj KK X K.
Proof.
  intros until 1. dependent induction H generalizing K.
  * intros. inversion H.
    - pose (HH := perm_refl L). auto.
    - now ms_simpl.
  * intros. inversion H0.
    - now ms_simpl.
    - destruct (IHadj K1 H4) as [ HH | HH ].
      + destruct HH. left. split ; now ms_simpl.
      + destruct HH as [ KK ]. right.
        exists (Y0 :: KK). now ms_simpl.
Qed.

Ltac adj_same_result_diff H1 H2 :=
   let H := fresh "H" in
   destruct (adj_same_result_diff_lem _ _ _ _ _ H1 H2) as [ H | H ] ;
   [ (let Heq := fresh "Heq" in
      destruct H as [ Heq ] ; rewrite <- Heq in * ; clear Heq)
   | (let KK := fresh "KK" in
      destruct H as [ KK ])
   ].

Theorem perm_invert : forall X J K JJ KK,
  perm J K ->
  adj JJ X J ->
  adj KK X K ->
  perm JJ KK.
Proof.
  intros until 1. dependent induction H generalizing JJ KK.
  * now ms_simpl.
  * intros. adj_same_result_diff H2 H.
    - refine (perm_trans _ _ _ H4 (perm_trans _ _ _ H1 _)).
      refine (adj_same_result _ _ _ _ H0 H3).
    - adj_same_result_diff H3 H0.
      + refine (perm_trans _ _ _ (adj_same_result _ _ _ _ H2 H) (perm_trans _ _ _ H1 (perm_sym _ _ H5))).
      + adj_swap H4 H U. adj_swap H5 H0 UU.
        refine (perm_trans _ _ _ (adj_same_result _ _ _ _ H2 H7) _).
        specialize (IHperm _ _ H4 H5).
        refine (perm_trans _ _ _ (perm_adj _ _ _ _ _ H6 H8 IHperm) (adj_same_result _ _ _ _ H9 H3)).
Qed.

Theorem adj_perm_result_lem : forall J K X JJ,
  perm J K ->
  adj JJ X J ->
  exists KK, adj KK X K /\ perm JJ KK.
Proof.
  intros until 1. dependent induction H generalizing JJ ; intros.
  * now ms_simpl.
  * adj_same_result_diff H2 H.
    - exists LL. split ; [ trivial | refine (perm_trans _ _ _ H3 H1) ].
    - adj_swap H3 H ZZ. specialize (IHperm _ H3). destruct IHperm as [ U HH ] ; destruct HH.
      adj_swap H6 H0 UU.
      assert (perm ZZ UU) by ms_simpl.
      exists UU. split ; [ trivial | ].
      refine (perm_trans _ _ _ (adj_same_result _ _ _ _ H2 H5) H10).
Qed.

Ltac adj_perm_result H1 H2 U :=
  let H := fresh in
  destruct (adj_perm_result_lem _ _ _ _ H1 H2) as [ U H ] ; destruct H.

Theorem adj_perm_source_lem : forall J K X L,
  perm J K ->
  adj J X L ->
  exists LL, adj K X LL /\ perm L LL.
Proof.
  intros. exists (X :: K). split ; now ms_simpl.
Qed.

Ltac adj_perm_source H1 H2 U :=
  let H := fresh in
  destruct (adj_perm_source_lem _ _ _ _ H1 H2) as [ U H ] ; destruct H.

End Adj_Perm.
