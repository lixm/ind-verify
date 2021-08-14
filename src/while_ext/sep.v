
Require Import Coq.Program.Basics. 
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq.

From indv Require Import arith tactics.
From indv.while_ext Require Import lang.

Definition sep X1 l1 h1 X2 l2 h2 (st: state) : Prop :=
  exists loc1 loc2,
    stt_a st X1 = Some loc1 /\ 
    stt_a st X2 = Some loc2 /\ 
    ((loc1 + h1 < loc2 + l2)%Z \/ (loc2 + h2 < loc1 + l1)%Z).

Lemma sep_ex_loc_1:
  forall X1 l1 h1 X2 l2 h2 st, 
    sep X1 l1 h1 X2 l2 h2 st ->
    exists l, stt_a st X1 = Some l.
Proof.
  move=> X1 l1 h1 X2 l2 h2 st.
  move=> H_sep.
  rewrite /sep in H_sep.
  inversion H_sep as [loc1 [loc2 [H_loc1 [H_loc2 H_or]]]].
  exists loc1; auto.
Qed. 

Lemma sep_ex_loc_2:
  forall X1 l1 h1 X2 l2 h2 st, 
    sep X1 l1 h1 X2 l2 h2 st ->
    exists l, stt_a st X2 = Some l.
Proof.  
  move=> X1 l1 h1 X2 l2 h2 st.
  move=> H_sep.
  rewrite /sep in H_sep.
  inversion H_sep as [loc1 [loc2 [H_loc1 [H_loc2 H_or]]]].
  exists loc2; auto.
Qed. 

Lemma sep_sym:
  forall X1 b1 e1 X2 b2 e2 st,
    sep X1 b1 e1 X2 b2 e2 st -> sep X2 b2 e2 X1 b1 e1 st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st.
  rewrite /sep=>H_sep1.
  inversion H_sep1 as [loc1 [loc2 H_body]]; clear H_sep1.
  inv H_body. inv H0.
  exists loc2. exists loc1.
  do 2! apply: conj=>//.
  inv H2; [right | left]=>//.
Qed.   

Lemma sep_sub_rgn_left:
  forall X1 b1 e1 X2 b2 e2 st b1' e1', 
    sep X1 b1 e1 X2 b2 e2 st ->
    (b1 <= b1')%Z -> (e1' <= e1)%Z -> 
    sep X1 b1' e1' X2 b2 e2 st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st b1' e1' H_sep1.
  move=> H_le1 H_le2.
  rewrite /sep in H_sep1; rewrite /sep.
  inversion H_sep1 as [loc1 [loc2 H_body]].
  exists loc1. exists loc2.
  inv H_body. inv H0.
  do 2! apply: conj=>//.
  inv H2; auto with zarith.
Qed.

Lemma sep_sub_rgn_right:
  forall X1 b1 e1 X2 b2 e2 st b2' e2',
    sep X1 b1 e1 X2 b2 e2 st ->
    (b2 <= b2')%Z -> (e2' <= e2)%Z ->
    sep X1 b1 e1 X2 b2' e2' st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st b2' e2' /sep_sym.
  move=> H_sep2 H_le2 H_le2'.
  have: (sep X2 b2' e2' X1 b1 e1 st).
  { eapply sep_sub_rgn_left; eauto. }
  apply /sep_sym.
Qed.

Lemma sep_change_st:
  forall X1 b1 e1 X2 b2 e2 st X1' X2' st', 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = stt_a st' X1' ->
    stt_a st X2 = stt_a st' X2' ->
    sep X1' b1 e1 X2' b2 e2 st'.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st X1' X2' st'.
  move=> H_sep H_eq1 H_eq2.
  rewrite /sep in H_sep; rewrite /sep.
  inversion H_sep as [loc1 [loc2 H_body]]; clear H_sep.
  exists loc1. exists loc2.
  move: H_eq1 H_eq2; rewrite /stt_a /compose=><-=><-=>//.
Qed.

Lemma sep_preserve_general:
  forall X1 b1 e1 X2 b2 e2 st X1' b1' e1' X2' b2' e2' st', 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = stt_a st' X1' ->
    stt_a st X2 = stt_a st' X2' ->
    (b1 <= b1')%Z -> (e1' <= e1)%Z ->
    (b2 <= b2')%Z -> (e2' <= e2)%Z ->
    sep X1' b1' e1' X2' b2' e2' st'.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st X1' b1' e1' X2' b2' e2' st'.
  move=> H_sep H_stt_eq1 H_stt_eq2 H_leb1 H_lee1 H_leb2 H_lee2.
  rewrite /sep in H_sep. rewrite /sep.
  inversion H_sep as [loc1 [loc2 [H_X1loc1 [H_X2loc2 H_rgn]]]];
    clear H_sep.
  exists loc1. exists loc2.
  rewrite <-H_stt_eq1. rewrite <-H_stt_eq2.
  apply: conj=>//. apply: conj=>//.
  inv H_rgn; auto with zarith.
Qed.  
