Require Import Coq.Program.Equality.
Require Import List.
Open Scope list_scope.

Module Type CARRIER.
  Parameter T : Type.
End CARRIER.

Module Adj (Import CC : CARRIER).

Inductive adj : list T -> T -> list T -> Prop :=
  | adj_same : forall {X L}, adj L X (X :: L)
  | adj_diff : forall {X Y K L}, adj K X L -> adj (Y :: K) X (Y :: L).

Hint Resolve adj_same adj_diff : adj.

Theorem adj_swap :
  forall {X Y : T} {J K L : list T},
  adj J X K -> adj K Y L ->
  exists KK, adj J Y KK /\ adj KK X L.
Proof.
  intros until 2 ; revert J X H ; induction H0.
  * intros ; inversion H.
    - exists (X :: J). split. refine adj_same. refine (adj_diff adj_same).
    - exists (X :: Y :: K) ; split.
      + exact adj_same.
      + exact (adj_diff (adj_diff H0)).
  * intros ; inversion H.
    - exists L ; split ; [ exact H0 | exact adj_same ].
    - let H1 := fresh in let H2 := fresh in destruct (IHadj _ _ H4) as [ XX ( H1 & H2 ) ].
      exists (Y :: XX) ; split ; refine (adj_diff _) ; trivial.
Qed.

Ltac adj_one :=
  match goal with
  | [ H : adj ?L ?X nil |- _ ] =>
      now inversion H
  end.

End Adj.

Module Perm (Import CC : CARRIER).

Include Adj CC.

Inductive perm : list T -> list T -> Prop :=
  | perm_nil : perm nil nil
  | perm_adj : forall {X KK K LL L}, adj KK X K -> adj LL X L -> perm KK LL -> perm K L.

Hint Resolve perm_nil perm_adj : perm.

Theorem perm_refl : forall {L}, perm L L.
Proof.
  induction L ; [ exact perm_nil | exact (perm_adj adj_same adj_same IHL) ].
Qed.

Theorem perm_sym : forall {K L}, perm K L -> perm L K.
Proof.
  induction 1 ; [ exact perm_nil | exact (perm_adj H0 H IHperm) ].
Qed.

Theorem perm_nil_1 : forall {L}, perm nil L -> L = nil.
Proof.
  inversion 1 ; [ reflexivity | inversion H0 ].
Qed.

Theorem perm_nil_2 : forall {L}, perm L nil -> L = nil.
Proof.
  inversion 1 ; [ reflexivity | inversion H1 ].
Qed.

Theorem perm_uncons_1 : forall {X K L},
  perm (X :: K) L ->
  exists J, adj J X L /\ perm K J.
Proof.
  intros X K L Hp ; dependent induction Hp generalizing K ; inversion H.
  * exists LL ; rewrite <- H4, <- H5 ; auto.
  * symmetry in H2 ; rewrite H1 in H2 ; clear H1.
    destruct (IHHp _ H2) as [ Z ( Hadj & Hperm ) ].
    destruct (adj_swap Hadj H0) as [ U ( HadjZ & HadjL ) ].
    exists U ; split ; [ assumption | exact (perm_adj H4 HadjZ Hperm) ].
Qed.

Theorem perm_uncons_2 : forall {X K L},
  perm K (X :: L) ->
  exists J, adj J X K /\ perm J L.
Proof.
  intros until 1 ; dependent induction H generalizing L ; inversion H0.
  * exists KK ; rewrite <- H5, <- H6 ; auto.
  * symmetry in H3 ; rewrite H2 in H3.
    destruct (IHperm _ H3) as [ Z ( Hadj & Hperm) ].
    destruct (adj_swap Hadj H) as [ U ( HadjZ & HadjK ) ].
    exists U ; split ; [ assumption | exact (perm_adj HadjZ H5 Hperm) ].
Qed.

Theorem adj_same_invert : forall {X K L},
  adj K X (X :: L) ->
  perm K L.
Proof.
  intros. inversion_clear H.
  * exact perm_refl.
  * exact (perm_adj adj_same H0 perm_refl).
Qed.

Ltac perm_one :=
  match goal with
  | [ H : adj ?K ?X (?X :: ?L) |- _ ] =>
      cut (perm K L) ; [ clear H ; intro H |
        now refine (@adj_same_invert X K L H)
      ]
  | [ H : perm nil ?L |- _ ] =>
      rewrite (@perm_nil_1 L H) in * ; clear H
  | [ H : perm ?L nil |- _ ] =>
      rewrite (@perm_nil_2 L H) in * ; clear H
  | [ H : perm ?K (?X :: ?L) |- _ ] =>
      let KK := fresh K in
      let HH := fresh in
      destruct (@perm_uncons_2 X K L H) as [ KK HH ] ; clear H ; destruct HH
  | [ H : perm (?X :: ?K) ?L |- _ ] =>
      let KK := fresh K in
      let HH := fresh in
      destruct (@perm_uncons_1 X K L H) as [ KK HH ] ; clear H ; destruct HH
  | [ |- perm ?L ?L ] =>
      now refine (@perm_refl L)
  | [ H : perm ?K ?L |- perm ?L ?K ] =>
      now refine (@perm_sym K L H)
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
      assert (adj K X L) ; [ rewrite Heq ; exact adj_same | ]
  end.

Ltac ms_simpl := repeat (intros ; eauto with adj perm ; (adj_one || perm_one (* || adjify_one *))).

Theorem perm_trans : forall {J K L}, perm J K -> perm K L -> perm J L.
Proof.
  intros until K ; dependent induction K generalizing J ; ms_simpl.
Qed.

Theorem adj_same_source : forall J X L1 L2,
  adj J X L1 ->
  adj J X L2 ->
  perm L1 L2.
Proof. ms_simpl. Qed.

Theorem adj_same_result : forall {J K X L},
  adj J X L ->
  adj K X L ->
  perm J K.
Proof.
  intros until 1. dependent induction H generalizing K.
  * ms_simpl.
  * intros. inversion H0.
    - rewrite <- H4 ; now ms_simpl.
    - now ms_simpl.
Qed.

Theorem adj_same_result_diff : forall {J X K Y L},
  adj J X L ->
  adj K Y L ->
  (X = Y /\ perm J K) \/
  exists KK, adj KK X K.
Proof.
  intros until 1. dependent induction H generalizing K.
  * intros. inversion H.
    - left ; split ; [ trivial | now ms_simpl ].
    - now ms_simpl.
  * intros. inversion H0.
    - now ms_simpl.
    - destruct (IHadj K1 H4) as [ ( Heq & Hperm ) | ( KK & HH ) ] ; now ms_simpl.
Qed.

Theorem perm_invert : forall X J K JJ KK,
  perm J K ->
  adj JJ X J ->
  adj KK X K ->
  perm JJ KK.
Proof.
  intros until 1. dependent induction H generalizing JJ KK.
  * now ms_simpl.
  * intros. destruct (adj_same_result_diff H2 H) as [ ( Heq & Hperm ) | ( KKK & Hadj ) ].
    - subst X ; refine (perm_trans Hperm (perm_trans H1 (adj_same_result H0 H3))).
    - destruct (adj_same_result_diff H3 H0) as [ ( Heq & Hperm )  | ( KKK1 & Hadj1 ) ].
      + subst X ; refine (perm_trans (adj_same_result H2 H) (perm_trans H1 (perm_sym Hperm))).
      + destruct (adj_swap Hadj H) as [ U ( HKU & HUK ) ].
        destruct (adj_swap Hadj1 H0) as [ UU ( HKUU & HUUL ) ].
        specialize (IHperm _ _ Hadj Hadj1).
        refine (perm_trans (adj_same_result H2 HUK)
                 (perm_trans (perm_adj HKU HKUU IHperm) (adj_same_result HUUL H3))).
Qed.

Theorem adj_perm_result : forall J K X JJ,
  perm J K ->
  adj JJ X J ->
  exists KK, adj KK X K /\ perm JJ KK.
Proof.
  intros until 1. dependent induction H generalizing JJ ; intros.
  * now ms_simpl.
  * destruct (adj_same_result_diff H2 H) as [ ( Heq & Hperm ) | ( KKK & Hadj ) ].
    - subst X ; exists LL ; split ; [ assumption | refine (perm_trans Hperm H1) ].
    - destruct (adj_swap Hadj H) as [ U ( HK3U & HUK ) ].
      destruct (IHperm _ Hadj) as [ UU ( HUULL & Hperm ) ].
      destruct (adj_swap HUULL H0) as [ Z ( HUUZ & HZL ) ].
      cut (perm JJ Z) ; [ eauto | refine (perm_trans (adj_same_result H2 HUK) _) ; now ms_simpl ].
Qed.

Theorem adj_perm_source : forall J K X L,
  perm J K ->
  adj J X L ->
  exists LL, adj K X LL /\ perm L LL.
Proof.
  intros. exists (X :: K). split ; now ms_simpl.
Qed.

End Perm.

Module Merge (Import CC : CARRIER).

Include Perm CC.

End Merge.

Print Merge.