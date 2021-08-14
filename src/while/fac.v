
From mathcomp Require Import ssreflect eqtype ssrbool seq.

Require Export Arith.
Require Export ZArith.

From indv Require Import sem tactics lang st_upd. 

(* the factorial program *)
Definition m: id := Id 0.
Definition fac: id := Id 1. 

Definition c_seq: com :=
  (CmSeq (CmAssg m (ASub (AVar m) (ANum 1)))
         (CmAssg fac (AMul (AVar fac) (AVar m)))). 
  
Definition c_wh: com := CmWh (BLt (ANum 1) (AVar m)) c_seq. 
  
Definition c0: com := CmSeq (CmAssg fac (AVar m)) c_wh.


(* the specification *)
Fixpoint factorial (n: nat): nat :=
  match n with 0 => 1 | (S n') => n * factorial n' end.

Eval compute in (factorial 0).
Eval compute in (factorial 3).

Definition facz (z: Z) : Z :=
  Z.of_nat (factorial (Z.to_nat z)). 
  
Definition c_wh_res (s: state) : wh_rconfig -> Prop := 
  (fun s' => (s' fac = (Z.mul (s fac) (facz (s m - 1))))). 

Definition c0_res (s: state) : wh_rconfig -> Prop :=
  (fun s' => (s' fac = facz (s m))).

Inductive c0_spec (u:unit): Spec unit wh_config wh_rconfig u :=
  WH_SP_c_wh: forall (s: state),
    Z.gt (s m) 0 -> c0_spec _ (c_wh, s) (c_wh_res s) |
  WH_SP_c0: forall s, Z.gt (s m) 0 -> c0_spec _ (c0, s) (c0_res s).

Lemma facz_unfold:
  forall z, (z > 0)%Z -> Z.mul z (facz (z-1)) = facz z.
Proof.
  move=> z H_zpos. rewrite /facz.  
  have H: Z.to_nat z = S (Z.to_nat (z-1)) by auto with zarith.
  rewrite H. rewrite {2}/factorial -/factorial.
  by rewrite <-H; auto with zarith.
Qed.


(* the correctness proof *)
Theorem c0_spec_valid: forall prm, valid _ (c0_spec prm).
Proof.
  init_verif. 
  inversion H0; subst.
  - inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst.
    + prem0_exe H_all. prem0_exe hall. prem1_exe hall. 
      clear hall0 hall1 hall.
      prem1_spec H_all. use_spec hspc.
      { eexists. eapply WH_SP_c_wh. updsimp.
        simpl in H4. apply Z.ltb_lt in H4. auto with zarith. }
      updsimp_h H5. unfold c_wh_res. 
      have H_minus_one: (s m - 2)%Z = ((s m - 1) - 1)%Z
        by auto with zarith.
      rewrite <-facz_unfold; auto with zarith.      
    + simpl in H4. apply Z.ltb_ge in H4.
      have H00: (r m = 1)%Z by auto with zarith.
      unfold c_wh_res. rewrite H00. simpl.
      unfold facz; simpl. auto with zarith.
  - inversion H; subst. inversion H4; subst. clear H4.
    prem0_exe H5. clear hall. prem1_spec H5.
    use_spec hspc. { eexists. eapply WH_SP_c_wh. updsimp; auto. }
    unfold c0_res. rewrite H4.
    updsimp. rewrite facz_unfold; auto.
Qed.

