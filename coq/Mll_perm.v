Require Import Coq.Program.Equality.
Require Import List.
Require Import Permutation.
Open Scope list_scope.

Section Mll_perm.

Parameter atm : Type.

Inductive form : Type :=
| atom : atm -> form
| natom : atm -> form
| tens : form -> form -> form
| one : form
| par : form -> form -> form
| bot : form.

Inductive mll : list form -> Prop :=
| mll_init : forall {A L},
    Permutation (atom A :: natom A :: nil) L ->
    mll L

| mll_par : forall {K A B L},
    mll (A :: B :: K) ->
    Permutation (par A B :: K) L ->
    mll L

| mll_bot : forall {K L},
    mll K ->
    Permutation (bot :: K) L ->
    mll L

| mll_tens : forall {J A K B L},
    mll (A :: J) ->
    mll (B :: K) ->
    Permutation (tens A B :: J ++ K) L ->
    mll L

| mll_one : mll (one :: nil).

Theorem mll_perm : forall {K L}, mll K -> Permutation K L -> mll L.
Proof.
  intros K L mll ; dependent destruction mll generalizing L ; intros.
  - refine (mll_init (perm_trans H H0)).
  - refine (mll_par mll0 (perm_trans H H0)).
  - refine (mll_bot mll0 (perm_trans H H0)).
  - refine (mll_tens mll1 mll2 (perm_trans H H0)).
  - rewrite (Permutation_length_1_inv H). exact mll_one.
Qed.

Fixpoint dual (f : form) : form :=
  match f with
  | atom A => natom A
  | natom A => atom A
  | tens A B => par (dual A) (dual B)
  | one => bot
  | par A B => tens (dual A) (dual B)
  | bot => one
  end.

Theorem mll_id : forall {F}, mll (F :: dual F :: nil).
Proof.
  intro F ; dependent induction F ; simpl.
  - refine (mll_init (Permutation_refl _)).
  - refine (mll_init (perm_swap _ _ _)).
  - refine (mll_par _ _).
    + refine (mll_tens IHF1 IHF2 _).
      refine (perm_trans (perm_swap _ _ _) (perm_skip _ (perm_swap _ _ _))).
    + refine (perm_swap _ _ _).
  - refine (mll_bot mll_one (perm_swap _ _ _)).
  - refine (mll_par _ _).
    + refine (mll_tens (mll_perm IHF1 (perm_swap _ _ _))
                       (mll_perm IHF2 (perm_swap _ _ _)) _) ; simpl.
      refine (perm_trans (perm_swap _ _ _) (perm_skip _ (perm_swap _ _ _))).
    + refine (Permutation_refl _).
  - refine (mll_bot mll_one (Permutation_refl _)).
Qed.

Inductive pos : form -> Prop :=
| pos_atom : forall {A}, pos (atom A)
| pos_tens : forall {A B}, pos (tens A B)
| pos_one  : pos one.

Theorem mll_cut : forall {C J K L},
  pos C ->
  mll (C :: J) -> mll (dual C :: K) ->
  Permutation (J ++ K) L ->
  mll L.
Proof.
  intros until 1 ; dependent induction H generalizing J K L ; simpl ; 
  intros until 1 ; dependent induction H generalizing K L ; intros.
  - destruct (Permutation_length_2_inv H).
    + injection H2 ; intros ; subst ; refine (mll_perm H0 H1).
    + discriminate H2.
Abort.

End Mll_perm.