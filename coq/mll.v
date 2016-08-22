Require Import Coq.Program.Equality.
Require Import List.
Require Import MS.
Open Scope list_scope.

Parameter atm : Set.

Module Form.

  Inductive form : Type :=
  | atom  : atm -> form
  | natom : atm -> form
  | tens  : form -> form -> form
  | one   : form
  | par   : form -> form -> form
  | bot   : form.

  Fixpoint dual (f:form) : form :=
    match f with
    | atom A   => natom A
    | natom A  => atom A
    | tens A B => par (dual A) (dual B)
    | one      => bot
    | par A B  => tens (dual A) (dual B)
    | bot      => one
    end.

  Definition T := form.

End Form.

Import Form.
Include Merge Form.

Inductive mll : list form -> Prop :=
| mll_init : forall {A L}, adj (natom A :: nil) (atom A) L -> mll L
| mll_tens : forall {A B J K L JJ KK LL},
    adj L (tens A B) LL ->
    merge J K L ->
    adj J A JJ -> mll JJ ->
    adj K B KK -> mll KK ->
    mll LL
| mll_one : mll (one :: nil)
| mll_par : forall {A B J K L LL},
    adj J (par A B) LL ->
    adj J A K -> adj K B L -> mll L ->
    mll LL
| mll_bot : forall {L LL},
    adj L bot LL ->
    mll L -> mll LL.

Hint Constructors mll : ms.

Theorem mll_perm : forall {K L}, mll K -> perm K L -> mll L.
Proof.
  intros until 1. dependent induction H generalizing L ; intros.
  * eapply mll_init.
    destruct (adj_perm_result H H0) as [ U ( adjU & permU ) ].
    destruct (perm_uncons_1 permU) as [ K ( adjK & permK ) ].
    assert (K = nil) ; [ ms_simpl | subst K ].
    inversion adjK ; subst.
    exact adjU.
  * assert (perm JJ (A :: J)). eapply perm_adj ; eauto with ms ; eapply perm_refl.
    specialize (IHmll1 _ H6).
    assert (perm KK (B :: K)). eapply perm_adj ; eauto with ms ; eapply perm_refl.
    specialize (IHmll2 _ H7).
    destruct (adj_perm_result H H5) as [ U ( adjU & permU ) ].
    assert (merge J K U) ; [ eapply perm_merge_3 | ] ; eauto with ms.
  * destruct (perm_uncons_1 H) as [ K ( adjK & permK ) ].
    assert (K = nil) ; [ ms_simpl | subst K ].
    inversion adjK ; subst ; eauto with ms.
  * destruct (adj_perm_result H H3) as [ U ( adjU & permU ) ].
    assert (adj U A (A :: U)) ; [ exact adj_same | ].
    assert (adj (A :: U) B (A :: B :: U)) ; [ exact (adj_diff adj_same) | ].
    specialize (IHmll _ (perm_adj H1 H5 (perm_adj H0 H4 permU))).
    eauto with ms.
  * destruct (adj_perm_result H H1) as [ U ( adjU & permU ) ].
    assert (adj U bot (bot :: U)) ; [ exact adj_same | ].
    specialize (IHmll _ permU).
    eauto with ms.
Qed.

Theorem mll_id : forall {A}, mll (A :: dual A :: nil).
Proof.
  induction A ; intros ; eauto with ms ; simpl dual.
  * eapply mll_par ; eauto with ms.
    eapply @mll_tens with (J := dual A1 :: nil)
                          (K := dual A2 :: nil) ;
      eauto with ms.
  * eapply mll_par ; eauto with ms.
    eapply @mll_tens with (J := A1 :: nil)
                          (K := A2 :: nil) ; eauto with ms.
    - refine (mll_perm IHA1 _).
      refine (perm_adj adj_same (adj_diff adj_same) (perm_adj adj_same adj_same perm_nil)).
    - refine (mll_perm IHA2 _).
      refine (perm_adj adj_same (adj_diff adj_same) (perm_adj adj_same adj_same perm_nil)).
Qed.
