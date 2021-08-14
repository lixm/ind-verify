
Require Import Coq.Program.Basics. 
Require Import FunctionalExtensionality.
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

From indv Require Import arith tactics.
From indv.while_ext Require Import lang sep. 

Lemma st_upd_eq:
  forall st x z, stt_v (state_upd_var st x z) x = Some z.
Proof.
  move=> st x z.
  rewrite /stt_v /compose /state_upd_var /store_of=>/=.
  rewrite /st_upd_var /varst_upd /varst_of=>/=.
  elim eqP=>//=.
Qed.

Lemma st_upd_neq:
  forall st x x' z,
    x <> x' -> stt_v (state_upd_var st x z) x' = stt_v st x'.
Proof.
  move=> st x x' z H_neq.
  rewrite /stt_v /compose /state_upd_var /store_of=>/=.
  rewrite /st_upd_var /varst_upd /varst_of=>/=.
  elim: eqP=>//=.
  move=> H_eq. move: H_eq H_neq. move->=>//.
Qed.

Ltac updsimp :=
  repeat (
      first [
          rewrite st_upd_eq |
          rewrite st_upd_neq; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updsimp_h hyp :=
  repeat (
      first [
          rewrite st_upd_eq in hyp |
          rewrite st_upd_neq in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

Lemma st_upd_eq_arr:
  forall st X z, stt_a (state_upd_arr st X z) X = Some z.
Proof.
  move=> st X z.
  rewrite /stt_a /compose /state_upd_arr /store_of=>/=.
  rewrite /st_upd_arr /arrst_upd /arrst_of=>/=.
  elim eqP=>//=.
Qed.

Lemma st_upd_neq_arr:
  forall st X X' z, 
    X <> X' -> stt_a (state_upd_arr st X z) X' = stt_a st X'.
Proof.
  move=> st X X' z H_neq.
  rewrite /stt_a /compose /state_upd_arr /store_of=>/=.
  rewrite /st_upd_arr /arrst_upd /arrst_of=>/=.
  elim: eqP=>//=.
  move=> H_eq. move: H_eq H_neq. move->=>//.
Qed.

Ltac updsimp_a :=
  repeat (
      first [
          rewrite st_upd_eq_arr |
          rewrite st_upd_neq_arr; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updsimp_a_h hyp :=
  repeat (
      first [
          rewrite st_upd_eq_arr in hyp |
          rewrite st_upd_neq_arr in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

Lemma st_upd_var_arr :
  forall st X x z, stt_a (state_upd_var st x z) X = stt_a st X.
Proof.
  move=> st X x z.
  rewrite /state_upd_var /st_upd_var /store_of /stt_a /compose=>//=.
Qed.

Lemma st_upd_var_loc :
  forall st x z, stt_l (state_upd_var st x z) = stt_l st.
Proof.
  move=> st x z.
  rewrite /state_upd_var /st_upd_var /store_of /stt_l /compose=>//=.
Qed.

Lemma st_upd_loc_var :
  forall st l z x, stt_v (state_upd_loc st l z) x = stt_v st x.
Proof.
  move=> st l z x.
  rewrite /stt_v /compose /state_upd_loc /varst_of /store_of
          /st_upd_loc /varst_of /arrst_of /locst_upd /locst_of.
  simpl. auto. 
Qed.   

Lemma st_upd_loc_arr:
  forall st X l z, stt_a (state_upd_loc st l z) X = stt_a st X. 
Proof.
  move=> st X l z.
  rewrite /state_upd_loc /st_upd_loc /stt_a /compose
          /arrst_of /store_of /varst_of=>//.
Qed.

Lemma st_upd_eq_loc:
  forall st l z, stt_l (state_upd_loc st l z) l = z.
Proof.
  move=> st l z.
  rewrite /stt_l /compose /locst_of /state_upd_loc /st_upd_loc
          /store_of /varst_of /arrst_of /locst_upd /locst_of.
  simpl.
  case Enl: (l =? l)%Z=>//.
  rewrite Z.eqb_refl in Enl; inv Enl. 
Qed.

Lemma st_upd_neq_loc:
  forall st l l' z,
    l <> l' -> stt_l (state_upd_loc st l' z) l = stt_l st l.
Proof.
  move=> st l l' z H_neq.
  rewrite /stt_l /state_upd_loc /compose /locst_of /store_of
          /st_upd_loc /varst_of /arrst_of /locst_of /locst_upd=>//=.
  have H_neq': l' <> l by auto.
  case Enl: (l' =? l)%Z=>//.
  move: H_neq'; move /Z.eqb_neq. move: Enl->. 
  move=> contra; inv contra.
Qed.   

Lemma st_upd_loc_sep:
  forall X1 b1 e1 X2 b2 e2 st l1 l2 z1 z2 z, 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = Some l1 ->
    stt_a st X2 = Some l2 -> 
    (b1 <= z1 <= e1)%Z ->
    (b2 <= z2 <= e2)%Z -> 
    stt_l st (l1+z1)%Z =
    stt_l (state_upd_loc st (l2+z2)%Z z) (l1+z1)%Z.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st l1 l2 z1 z2 z.
  move=> H_sep H_l1 H_l2 H_z1_rgn H_z2_rgn.
  rewrite /sep in H_sep.
  inversion H_sep as
      [l1' [l2' [H_l1' [H_l2' H_or]]]]; clear H_sep.
  have H_l1'l1: l1' = l1 by some_eq H_l1 H_l1'.
  have H_l2'l2: l2' = l2 by some_eq H_l2 H_l2'.
  rewrite H_l1'l1 H_l2'l2 in H_or.
  have H_ne: (l1 + z1)%Z <> (l2 + z2)%Z.
  {
    inversion H_or as [H_12 | H_21].
    - have H_lt: (l1+z1 < l2+z2)%Z
        by apply Z.le_lt_trans with (m:=(l1+e1)%Z);
        inv H_z1_rgn; auto with zarith.
      apply Z.lt_neq=>//.
    - apply ssrfun.nesym.
      have H_lt: (l2+z2 < l1+z1)%Z.
      apply Z.le_lt_trans with (m:=(l2+e2)%Z);
        inv H_z1_rgn; inv H_z2_rgn; auto with zarith.
      apply Z.lt_neq=>//.
  }
  rewrite st_upd_neq_loc=>//.
Qed.   

Lemma st_upd_switch:
  forall st x x' z z',
    x <> x' -> 
    state_upd_var (state_upd_var st x z) x' z' =
    state_upd_var (state_upd_var st x' z') x z.
Proof. 
  move=> st x x' z z' H_neq.
  rewrite /state_upd_var /st_upd_var /varst_upd
          /store_of /varst_of /arrst_of =>//=.
  have H_steq:
    ((fun x'0 : var_id =>
        if x'0 == x' then Some z' else if x'0 == x then Some z else fst (fst (fst st)) x'0)
     = (fun x'0 : var_id =>
          if x'0 == x then Some z else if x'0 == x' then Some z' else fst (fst (fst st)) x'0)).
  {
    apply functional_extensionality.
    move=> x0.
    case En: (x0 == x)=>//.
    case En': (x0 == x')=>//.
    exfalso. apply H_neq.
    apply: eqP. 
    move: En; move /eqP; move: En'; move /eqP->=>->=>//. 
  }
  congruence.
Qed.

Lemma st_upd_st_upd_eq:
  forall st x z z',
    state_upd_var (state_upd_var st x z) x z' = state_upd_var st x z'.
Proof.
  move=> st x z z'.
  rewrite /state_upd_var /st_upd_var /varst_upd
          /store_of /varst_of /arrst_of /locst_of=>//=.
  have H_steq:
    (fun x' : var_id => if x' == x then Some z' else if x' == x then Some z else fst (fst (fst st)) x')
    = (fun x' : var_id => if x' == x then Some z' else fst (fst (fst st)) x').
  {
    apply functional_extensionality.
    move=> x0.
    case En: (x0 == x)=>//.
  }
  congruence. 
Qed.         

Lemma st_upd_st_upd_neq:
  forall st x x' z z' z'',
    x <> x' -> 
    state_upd_var (state_upd_var (state_upd_var st x z) x' z') x z'' =
    state_upd_var (state_upd_var st x' z') x z''.
Proof.
  move=> st x x' z z' z'' H_neq.
  have H_switch: 
    state_upd_var (state_upd_var st x z) x' z' =
    state_upd_var (state_upd_var st x' z') x z by apply: st_upd_switch.
  rewrite H_switch.
  set st' := state_upd_var st x' z'.
  apply: st_upd_st_upd_eq. 
Qed.

Ltac updupdsimp :=
  repeat (
      first [
          rewrite st_upd_st_upd_eq |
          rewrite st_upd_st_upd_neq; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updupdsimp_h hyp :=
  repeat (
      first [
          rewrite st_upd_st_upd_eq in hyp |
          rewrite st_upd_st_upd_neq in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).
