
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

From indv Require Import arith tactics sem.
From indv.fun Require Import lang.

Ltac inv_zlcfm :=
  match goal with [ H : context [is_zlcfm _] |- _ ] => inv H end.

Lemma zlcfm_shape:
  forall cf, 
    is_zlcfm cf ->
    (cf = NilE \/ exists z cf', cf = PPendE (NE z) cf').
Proof.
  move=> cf H_zlcfm; 
  try destruct cf; inv H_zlcfm.
  - left=>//.
  - right.
    destruct cf1; inv H0.
    exists z. exists cf2. auto.
Qed.     
  
Lemma zlcfm_subst:
  forall e x e', is_zlcfm e -> e_subst e x e' = e.
Proof.
  elim; try (move=> *; inv_zlcfm; fail).
  - move=>//.
  - move=> e IH1 e0 IH2 x e' H_zlcfm.
    move=>/=.
    move: IH1=> /(_ x e')=> IH1.
    move: IH2=> /(_ x e')=> IH2.
    inversion H_zlcfm; subst.
    case En: e; rewrite En in H0; inv H0.
    move=>/=.
    apply IH2 in H0. rewrite H0=>//.
Qed.

Definition cfm_not_in_spec
           {PARAM: Type}
           (prm: PARAM)
           (phi: Spec PARAM fun_config fun_rconfig prm) : Prop
  := forall cf, is_cfm cf -> ~(exists P, phi cf P).

Lemma zlcfm_is_cfm:
  forall cf, is_zlcfm cf -> is_cfm cf.
Proof.
  elim; try (move=> *; inv_zlcfm; fail).
  - rewrite /is_cfm=>//.
  - move=> e1 IH1 e2 IH2 H_zlcfm.
    inversion H_zlcfm.
    case En_e1: e1; rewrite En_e1 in H0; inv H0.
    rewrite H1 in IH2. rem_prem IH2.
    simpl=>//.
Qed.     

Lemma zlcfm_infer_preserve {PARAM: Type}:
  forall (prm: PARAM) phi lcf cf,
    cfm_not_in_spec prm phi ->
    is_zlcfm lcf ->
    infer prm phi (lcf, cf) ->
    cf = lcf. 
Proof.
  move=> prm phi. 
  elim; try (move=> *; inv_zlcfm; fail).
  - move=> cf H_nispc H_zlcfm H_inf. inv H_inf.
    inv H1; subst. auto.
  - move=> e1 IH1 e2 IH2 cf H_nispc H_zlcfm H_inf.
    inversion H_zlcfm; subst.
    destruct e1; inv H0.
    inversion H_inf; subst.
    rename H3 into H_rule. inversion H_rule; subst.
    have: cf0 = (NE z).
    {
      prem0 H4 H_inf_cf0. inv H_inf_cf0. clear H_inf_cf0.
      have: ~(exists P, phi (NE z) P) by apply H_nispc=>//=. 
      move/H2=> H_inf'_cf0. 
      inversion H_inf'_cf0; subst. inv H8; subst. done.
    }      
    have: cf' = e2.
    {
      prem1 H4 H_inf_cf'. inv H_inf_cf'.
      have: ~(exists P, phi e2 P)
        by apply H_nispc; apply zlcfm_is_cfm=>//.
      move /H2=> H_inf'_cf'.
      move: IH2=> /(_ cf' H_nispc H0 H_inf'_cf')=>->=>//.
    }
    do 2!(move->)=>//. 
Qed. 
  
Lemma zlcfm_infer_nil {PARAM: Type}:
  forall (prm: PARAM) phi lcf, 
    is_zlcfm lcf ->
    infer prm phi (lcf, NilE) ->
    lcf = NilE.
Proof.
  move=> prm phi.
  elim; try (move=> *; inv_zlcfm; fail).
  - done.
  - move=> e IH1 e0 IH2 H_zlcfm H_inf.
    inv H_inf; subst.
    inv H1; subst.
Qed.     

Ltac get_branch hyp_or hyp_nex :=
        let h1 := fresh "h" in (
          let h2 := fresh "h" in (
            let h3 := fresh "h" in (
              let h4 := fresh "h" in (
                inversion hyp_or as [h1 | h2];
                [ inv h1; auto |
                  inversion h2 as [P h4]; inv h4;
                  exfalso; apply hyp_nex; exists P; auto ]
              )
            )
          )
        ).

Lemma zlcfm_infer_pend0 {PARAM: Type}:
  forall (prm: PARAM) phi lcf cf cf',
    cfm_not_in_spec prm phi ->
    is_zlcfm lcf ->
    infer prm phi (lcf, PPendE cf cf') ->
    exists z lcf'',
      lcf = PPendE (NE z) lcf'' /\
      cf = (NE z) /\
      cf' = lcf'' /\
      is_zlcfm lcf''.
Proof.
  move=> prm phi.
  elim; try (move=> *; inv_zlcfm; fail).
  - move=> cf cf' H_nispc H_zlcfm H_inf. inv H_inf. inv H1.
  - move=> e1 IH1 e2 IH2 cf cf' H_nispc H_zlcfm H_inf.
    inv H_zlcfm; subst.
    destruct e1; inv H0.
    have: cf = NE z.
    {
      inv H_inf; subst. inv H3; subst.
      prem0 H4 H40. inv H40.
      have: ~(exists P, phi (NE z) P) by apply H_nispc=>//=.
      move /H2=> H_inf_cf. 
      inv H_inf_cf; subst. inv H8; subst. done.
    }
    have: cf' = e2.
    {
      inv H_inf; subst. inv H3; subst.
      prem1 H4 H41. inv H41.
      have: ~(exists P, phi e2 P)
        by apply H_nispc; apply zlcfm_is_cfm=>//.
      move /H2=> H_inf_cf'.
      apply zlcfm_infer_preserve in H_inf_cf'=>//.
    }
    do 2!(move->).
    exists z, e2. apply: conj=>//.
Qed.     

Lemma zlcfm_infer_pend {PARAM: Type}: 
  forall (prm: PARAM) phi lcf cf cf',
    cfm_not_in_spec prm phi ->
    is_zlcfm lcf ->
    infer prm phi (lcf, PPendE cf cf') ->
    exists z,
      lcf = PPendE (NE z) cf' /\
      cf = NE z /\
      is_zlcfm cf'.
Proof.
  move=> prm phi lcf cf cf' H_nispc H_zlcfm H_inf.
  have H_ex0:
    exists z lcf'',
      lcf = PPendE (NE z) lcf'' /\
      cf = NE z /\ 
      cf' = lcf'' /\
      is_zlcfm lcf''
      by apply zlcfm_infer_pend0 with (prm0:=prm) (phi0:=phi)=>//.
  inv H_ex0. inv H. inv H0. inv H2. inv H4.
  exists x. apply: conj. congruence. apply: conj=>//. congruence.
Qed.   

