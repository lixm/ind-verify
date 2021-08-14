
From mathcomp Require Import ssreflect eqtype ssrnat ssrbool.

Require Export Arith.
Require Export ZArith.

From indv Require Import tactics. 

Lemma sub_zero: forall n:nat, n - n = 0.
    by auto with arith. Qed.

Lemma add_zero: forall n:nat, n + 0 = n.
Proof. 
  move=> n.
  specialize (Nat.add_comm n 0)=>H. simpl in H. rewrite -{2} H.
  auto with arith.
Qed.

Lemma add_zero_l: forall n:nat, 0 + n = n.
Proof. move=> n; auto with arith. Qed.

Lemma sub_add_1: forall m n, m <= n -> n - m + m.+1 = n + 1.
Proof.
  move=> m n H. rewrite addnBAC=>//. rewrite <- addnBA=>//.
  rewrite subSnn. auto.
Qed.

Lemma z_tonat_1: Z.to_nat 1 = 1. 
Proof. auto with zarith. Qed.

Lemma lt_1_le: forall n m, n < m -> n + 1 <= m.
Proof.
  move=> n m; move: m n.
  elim.
  - move=> n H. inv H.
  - move=> n IH.
    move=> n0 H_n0_rgn.
    have: (n0 < n) || ~~(n0 < n) by case (n0 < n)=>//.
    move /orP=> H_cases.
    inv H_cases.
    specialize (IH _ H). auto with arith.
    rewrite <- ltnNge in H.
    apply ltnSE in H_n0_rgn. apply ltnSE in H.
    have: n0 == n.
    { rewrite eqn_leq. apply /andP. apply: conj=>//. }
    move /eqP ->.
    rewrite addn1. auto with arith.
Qed.

Lemma le_1_lt: forall n m, n + 1 <= m -> n < m.
Proof. 
  move=> n m; move: m n. 
  elim.
  - move=> n H. destruct n. auto. auto.
  - move=> n IH.
    move=> n0 H.
    have: (n0+1 <= n) || ~~(n0+1 <= n) by case (n0+1 <= n)=>//.
    move /orP=> H_cases.
    inv H_cases.
    specialize (IH _ H0).
    auto.
    rewrite <- ltnNge in H0.
    rewrite addn1 in H0. apply ltnSE in H0.
    rewrite addn1 in H.
    apply ltnSE in H.
    have: n0 == n.
    { rewrite eqn_leq. apply /andP. apply: conj=>//. }
    move /eqP ->.
    auto with arith. 
Qed.

Lemma nat_ge_cases:
  forall n m, n <= m -> m = n \/ n+1 <= m.
Proof.
  move=> n m H_le.
  rewrite leq_eqVlt in H_le.
  case En: (n == m).
  move: En; move /eqP. auto.
  rewrite En in H_le.
  simpl in H_le. right.
  apply lt_1_le=>//. 
Qed.

Lemma n_lt: forall n:nat, ~~(n < n).
Proof.
  move=> n. 
  have H_eq: n <= n by auto.
  rewrite leqNgt in H_eq=>//. 
Qed.

Lemma ltn_leq_trans:
  forall n m p : nat, m < n -> n <= p -> m < p.
Proof.
  move=> n m p H_lt_mn H_le_np.
  case En: (n == p).
  - move: En. move /eqP=>H. rewrite H in H_lt_mn=>//.
  - move: En. move /eqP=>H.
    have H_lt_np: n < p.
    {
      rewrite leq_eqVlt in H_le_np.
      move: H_le_np; move /orP=>H_or; inv H_or.
      move: H0; move /eqP. move /H=>//.
      done. 
    }
    apply ltn_trans with (n:=n)=>//.
Qed.

Lemma n_z_ge_z1: forall z:Z, ~(z >= z+1)%Z.
Proof.
  elim=>//=; move=> p; elim; apply /Z.compare_lt_iff. 
  - by auto with zarith.
  - by rewrite <- Pos2Z.add_neg_pos; auto with zarith. 
Qed.

Lemma z1_nle_z: forall z, (z + 1 <=? z)%Z = false.
Proof.
  move=> z; elim z=>//; 
  move=> p; apply /Z.leb_gt; auto with zarith.
Qed.

Lemma rgn_divide:
  forall a b c,
    0 <= a <= b -> b + 1 <= c ->
    forall i, a <= i <= c -> (a <= i <= b \/ b + 1 <= i <= c).
Proof.
  move=> a b c H_ab H_bc.
  move=> i H_i_rgn.
  have H_cases: (i <= b) || ~~(i <= b) by case (i <= b)=>//. 
  move: H_cases. move /orP.
  case=> H_cs.
  - left. apply /andP. apply: conj=>//.
    move: H_i_rgn. move /andP=>HH. inv HH; auto. 
  - rewrite <- ltnNge in H_cs. right.
    apply /andP. apply: conj.
    apply lt_1_le=>//.
    move: H_i_rgn. move /andP=> HH.
    inv HH=>//.
Qed.
