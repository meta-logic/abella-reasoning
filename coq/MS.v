Require Import Coq.Program.Equality.
Require Import List.
Open Scope list_scope.

Module Type CARRIER.
  Parameter T : Set.
End CARRIER.

Module Adj (Import CC : CARRIER).

Inductive adj : list T -> T -> list T -> Prop :=
  | adj_same : forall {X L}, adj L X (X :: L)
  | adj_diff : forall {X Y K L}, adj K X L -> adj (Y :: K) X (Y :: L).

Hint Constructors adj : ms.

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

Hint Constructors perm : ms.

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

Ltac ms_simpl := repeat (intros ; eauto with ms ; (adj_one || perm_one (* || adjify_one *))).

Theorem perm_trans : forall {J K L}, perm J K -> perm K L -> perm J L.
Proof.
  intros until K ; dependent induction K generalizing J ; ms_simpl.
Qed.

Theorem adj_same_source : forall {J X L1 L2},
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

Theorem perm_invert : forall {X J K JJ KK},
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

Theorem adj_perm_result : forall {J K JJ X},
  adj JJ X J ->
  perm J K ->
  exists KK, adj KK X K /\ perm JJ KK.
Proof.
  intros until 1. dependent induction H generalizing K ; intros ; ms_simpl.
  destruct (IHadj _ H1) as [ KK ( Hadj & Hperm ) ].
  destruct (adj_swap Hadj H0) as [ U ( HKKU & HUK ) ].
  ms_simpl.
Qed.

Theorem adj_perm_source : forall {J K X L},
  perm J K ->
  adj J X L ->
  exists LL, adj K X LL /\ perm L LL.
Proof.
  intros. exists (X :: K). split ; now ms_simpl.
Qed.

End Perm.

Module Merge (Import CC : CARRIER).

Include Perm CC.

Inductive merge : list T -> list T -> list T -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_left : forall {X JJ J K LL L}, merge JJ K LL -> adj JJ X J -> adj LL X L -> merge J K L
  | merge_right : forall {X J KK K LL L}, merge J KK LL -> adj KK X K -> adj LL X L -> merge J K L.

Hint Constructors merge : ms.

Theorem perm_merge_1 : forall {J K L JJ},
  merge J K L ->
  perm J JJ ->
  merge JJ K L.
Proof.
  intros until 1. dependent induction H generalizing JJ ; intros ; ms_simpl.
  destruct (adj_perm_result H0 H2) as [ U ( Hadj & Hperm ) ].
  specialize (IHmerge _ Hperm). eauto with ms.
Qed.

Theorem perm_merge_2 : forall {J K L KK},
  merge J K L ->
  perm K KK ->
  merge J KK L.
Proof.
  intros until 1. dependent induction H generalizing KK ; intros ; ms_simpl.
  destruct (adj_perm_result H0 H2) as [ U ( Hadj & Hperm ) ].
  specialize (IHmerge _ Hperm). eauto with ms.
Qed.

Theorem perm_merge_3 : forall {J K L LL},
  merge J K L ->
  perm L LL ->
  merge J K LL.
Proof.
  intros until 1. dependent induction H generalizing LL ; intros ; ms_simpl ;
  destruct (adj_perm_result H1 H2) as [ U ( Hadj & Hperm ) ] ;
  specialize (IHmerge _ Hperm) ; eauto with ms.
Qed.

Theorem merge_sym : forall {J K L},
  merge J K L ->
  merge K J L.
Proof.
  induction 1 ; eauto with ms.
Qed.

Theorem merge_unadj_1 : forall {X JJ J K L},
  merge J K L ->
  adj JJ X J ->
  exists LL, adj LL X L /\ merge JJ K LL.
Proof.
  intros until 1. dependent induction H generalizing JJ ; intros ; ms_simpl.
  * destruct (adj_same_result_diff H2 H0) as [ ( Heq & Hperm ) | ( KK & Hadj ) ].
    - subst X0. exists LL. split ; [ assumption | exact (perm_merge_1 H (perm_sym Hperm)) ].
    - destruct (IHmerge _ Hadj) as [ U ( HU & Hmerge ) ].
      destruct (adj_swap HU H1) as [ V ( HUV & HVL ) ].
      exists V ; split ; [ assumption | ].
      destruct (adj_swap Hadj H0) as [ W ( HKKW & HWJ ) ].
      refine (perm_merge_1 _ (adj_same_result HWJ H2)). eauto with ms.
  * destruct (IHmerge _ H2) as [ U ( HU & Hmerge ) ].
    destruct (adj_swap HU H1) as [ V ( HUV & HVL ) ].
    assert (merge JJ K V) ; eauto with ms.
Qed.

Theorem merge_unadj_2 : forall {X J KK K L},
  merge J K L ->
  adj KK X K ->
  exists LL, adj LL X L /\ merge J KK LL.
Proof.
  intros.
  destruct (merge_unadj_1 (merge_sym H) H0) as [ U ( Hadj & Hmerge ) ].
  pose (HH := merge_sym Hmerge).
  eauto with ms.
Qed.

Theorem merge_unadj_3 : forall {X J K L LL},
  merge J K L ->
  adj LL X L ->
  (exists JJ, adj JJ X J /\ merge JJ K LL) \/
  (exists KK, adj KK X K /\ merge J KK LL).
Proof.
  intros until 1. dependent induction H generalizing LL ; intros ; ms_simpl ; 
  destruct (adj_same_result_diff H1 H2) as [ ( Heq & Hperm ) | ( U & Hadj ) ].
  * left ; subst X0 ; exists JJ ; split ; [ assumption | exact (perm_merge_3 H Hperm) ].
  * destruct (adj_swap Hadj H2) as [ V ( HUV & HVL ) ].
    destruct (adj_perm_result HUV (adj_same_result HVL H1)) as [ W ( HadjW & HpermW ) ].
    destruct (IHmerge _ HadjW) as [ (Z & HadjZ & HmergeZ ) | ( Z & HadjZ & HmergeZ ) ].
    - destruct (adj_swap HadjZ H0) as [ ZZ ( HtoZZ & HfromZZ ) ].
      left ; exists ZZ ; split. assumption.
      pose (HH := perm_merge_3 HmergeZ (perm_sym HpermW)). eauto with ms.
    - right ; exists Z ; split. assumption.
      destruct (adj_swap HadjW H1) as [ ZZ ( HtoZZ & HfromZZ ) ].
      refine (perm_merge_3 _ (adj_same_result HfromZZ H2)). eauto with ms.
  * right ; subst X0 ; exists KK ; split ; [ assumption | exact (perm_merge_3 H Hperm) ].
  * destruct (adj_swap Hadj H2) as [ V ( HUV & HVL ) ].
    destruct (adj_perm_result HUV (adj_same_result HVL H1)) as [ W ( HadjW & HpermW ) ].
    destruct (IHmerge _ HadjW) as [ (Z & HadjZ & HmergeZ ) | ( Z & HadjZ & HmergeZ ) ].
    - left ; exists Z ; split. assumption.
      destruct (adj_swap HadjW H1) as [ ZZ ( HtoZZ & HfromZZ ) ].
      refine (perm_merge_3 _ (adj_same_result HfromZZ H2)). eauto with ms.
    - destruct (adj_swap HadjZ H0) as [ ZZ ( HtoZZ & HfromZZ ) ].
      right ; exists ZZ ; split. assumption.
      pose (HH := perm_merge_3 HmergeZ (perm_sym HpermW)). eauto with ms.
Qed.

Theorem merge_invert_1 : forall {X JJ J K LL L},
  merge J K L ->
  adj JJ X J ->
  adj LL X L ->
  merge JJ K LL.
Proof.
  intros.
  destruct (merge_unadj_1 H H0) as [ U ( Hadj & Hmerge ) ].
  exact (perm_merge_3 Hmerge (adj_same_result Hadj H1)).
Qed.

Theorem merge_invert_2 : forall {X J KK K LL L},
  merge J K L ->
  adj KK X K ->
  adj LL X L ->
  merge J KK LL.
Proof.
  intros.
  destruct (merge_unadj_2 H H0) as [ U ( Hadj & Hmerge ) ].
  exact (perm_merge_3 Hmerge (adj_same_result Hadj H1)).
Qed.

Theorem merge_move_12 : forall {X JJ J KK K L},
  adj JJ X J ->
  adj KK X K ->
  merge J KK L ->
  merge JJ K L.
Proof.
  intros.
  destruct (merge_unadj_1 H1 H) as [ U ( Hadj & Hmerge ) ].
  eauto with ms.
Qed.

Theorem merge_move_21 : forall {X JJ J KK K L},
  adj JJ X J ->
  adj KK X K ->
  merge JJ K L ->
  merge J KK L.
Proof.
  intros.
  destruct (merge_unadj_2 H1 H0) as [ U ( Hadj & Hmerge ) ].
  eauto with ms.
Qed.

Theorem merge_nil_perm : forall {K L},
  merge nil K L -> perm K L.
Proof.
  intros until 1. dependent induction H ; ms_simpl.
Qed.

Theorem merge_assoc : forall {J K L JK KL JKL1 JKL2},
  merge J K JK -> merge K L KL ->
  merge J KL JKL1 -> merge JK L JKL2 ->
  perm JKL1 JKL2.
Proof.
  intros until 1. dependent induction H generalizing L KL JKL1 JKL2 ; intros.
  - exact (perm_trans (perm_sym (merge_nil_perm H0))
             (perm_trans (perm_sym (merge_nil_perm H)) (merge_nil_perm H1))).
  - destruct (merge_unadj_1 H3 H0) as [ U ( HadjU & HmergeU ) ].
    destruct (merge_unadj_1 H4 H1) as [ V ( HadjV & HmergeV ) ].
    specialize (IHmerge _ _ _ _ H2 HmergeU HmergeV).
    eauto with ms.
  - destruct (merge_unadj_1 H2 H0) as [ U ( HadjU & HmergeU ) ].
    destruct (merge_unadj_1 H4 H1) as [ V ( HadjV & HmergeV ) ].
    destruct (merge_unadj_2 H3 HadjU) as [ W ( HadjW & HmergeW ) ].
    specialize (IHmerge _ _ _ _ HmergeU HmergeW HmergeV).
    eauto with ms.
Qed.

End Merge.