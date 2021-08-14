
Require Import List.
Require Import ZArith. 
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq.

From indv Require Import tactics arith.

Definition occ (zs: seq Z) (z: Z) : nat :=
  count (fun z'=> Z.eqb z' z) zs.

Eval compute in (occ ([:: 2; -43; 2; 32; 22; -43; -2; 3; -43]) (-43))%Z.

Lemma occ_cat:
  forall zs1 zs2 z,
    occ (zs1 ++ zs2) z = occ zs1 z + occ zs2 z.
Proof.
  move=> zs1 zs2 z.
  rewrite /occ.
  rewrite count_cat=>//.
Qed. 

Definition sorted (zs: seq Z) : Prop :=
  forall i j, 
    0 <= i -> i < j -> j < size zs ->
    (nth (0%Z) zs i <= nth (0%Z) zs j)%Z.

Lemma empty_lst_sorted: sorted [:: ].
Proof.
  rewrite /sorted. move=> i j H_0i H_ij H_jsz.
  simpl in H_jsz. inv H_jsz.
Qed.

Lemma singleton_sorted: forall (z:Z), sorted [:: z].
Proof.
  move=> z. rewrite /sorted.
  move=> i j H_0i H_ij H_jsz.
  simpl in H_jsz.
  case En: j=>[ | j0].
  - rewrite En in H_ij. rewrite ltn0 in H_ij. inv H_ij.
  - rewrite En in H_jsz. inv H_jsz. 
Qed. 

(* zs1 is a continuous fragment of zs2 *)
Definition lst_frag (b0: Z) zs1 zs2 :=
  forall i,
    i < size zs1 ->
    ((i + Z.to_nat b0 < size zs2) /\ 
     nth (0%Z) zs1 i = nth (0%Z) zs2 (i + Z.to_nat b0)).

Lemma sorted_lst_frag: 
  forall b0 zs1 zs2,
    lst_frag b0 zs1 zs2 -> sorted zs2 -> sorted zs1.
Proof.
  move=> b0 zs1 zs2 H_lst_frag H_sorted2.
  rewrite /lst_frag in H_lst_frag.
  rewrite /sorted in H_sorted2.
  rewrite /sorted.
  move=> i j H_0i H_ij H_jsz.
  have H_isz: i < size zs1 by apply ltn_trans with (n:=j)=>//. 
  specialize (H_lst_frag i H_isz) as H_corr1.
  specialize (H_lst_frag j H_jsz) as H_corr2.
  inversion H_corr1 as [H_i_b0_sz1 H_nth1]; clear H_corr1.
  inversion H_corr2 as [H_j_b0_sz2 H_nth2]; clear H_corr2.
  rewrite H_nth1. rewrite H_nth2.
  apply H_sorted2.
  apply leq_trans with (n:=i); auto.
  apply leq_addr.
  rewrite ltn_add2r; auto.
  auto.
Qed.

Lemma sorted_concat:
  forall zs1 zs2,
    sorted zs1 ->
    sorted zs2 -> 
    (nth 0 zs2 0 >= nth 0 zs1 (size zs1 - 1))%Z ->
    sorted (zs1 ++ zs2).
Proof.
  move=> zs1 zs2 H_sorted1 H_sorted2 H_ge.
  case En1: zs1=> [ | z1 zs1' ].
  - move=>//.
  - rewrite <- En1.
    unfold sorted in *.
    move=> i j H_0i H_ij H_jsz.
    have: (j < size zs1) || ~~(j < size zs1)
      by case (j < size zs1); auto.
    move /orP=> H_case_j.
    inversion H_case_j as [H_j_left | H_j_right].
    + have H_i_left: i < size zs1 
        by apply ltn_trans with (n:=j); auto.
      rewrite nth_cat. rewrite H_i_left.
      rewrite nth_cat. rewrite H_j_left.
      apply H_sorted1; auto.
    + have H_j_r: ~~ (j < size zs1) by auto.
      rewrite <- leqNgt in H_j_right.
      have: (i < size zs1) || ~~(i < size zs1)
        by case (i < size zs1); auto.
      move /orP=> H_case_i.
      inversion H_case_i as [H_i_left | H_i_right].
      * 2: { (* i j both pointing into zs2 *)
          case En: (i < size zs1).
          rewrite En in H_i_right; inv H_i_right.
          case En': (j < size zs1). 
          rewrite En' in H_j_r; inv H_j_r.
          have H_lt_or_eq: size zs1 < j \/ size zs1 = j.
          {
            rewrite leq_eqVlt in H_j_right.
            move: H_j_right; move /orP=>H_or.
            inv H_or.
            right. move: H; move /eqP=>//. left=>//.
          }
          inv H_lt_or_eq.
          rewrite nth_cat. rewrite En.
          rewrite nth_cat. rewrite En'.
          apply H_sorted2; auto with arith.
          apply ltn_sub2r; auto.
          rewrite size_cat in H_jsz.
          rewrite <- ltn_subLR in H_jsz; auto.
          rewrite <-H in H_ij. rewrite H_ij in En. inv En.
        }
      * (* i < size zs1, size zs1 <= j*)
        rewrite nth_cat. rewrite H_i_left.
        have: (j < size zs1)=false by apply: negPf=>//.
        rewrite nth_cat. move->.
        clear H_case_i; clear H_case_j.
        have H_le1: (nth (0%Z) zs1 i <= nth (0%Z) zs1 (size zs1 - 1))%Z.
        {
          have H_i_le: i <= size zs1 - 1.
          {
            apply lt_1_le in H_i_left.
            apply leq_sub2r with (p:=1) in H_i_left.
            rewrite <- addnBA in H_i_left=>//.
            rewrite sub_zero in H_i_left.
            rewrite add_zero in H_i_left=>//.
          }
          rewrite leq_eqVlt in H_i_le.
          move: H_i_le; move /orP=> H_or.
          inv H_or. move: H; move /eqP->. apply: Z.le_refl.
          apply H_sorted1; auto.
          rewrite ltn_subrL.
          apply /andP. apply: conj. auto. rewrite En1. simpl; auto.
        }
        have H_le2: (nth 0 zs2 0 <= nth 0 zs2 (j - size zs1))%Z.
        {
          rewrite leq_eqVlt in H_j_right.
          move: H_j_right; move /orP=> H_or.
          inv H_or.
          move: H; move /eqP->. rewrite sub_zero. apply: Z.le_refl.
          apply H_sorted2; auto.
          rewrite subn_gt0=>//.
          rewrite size_cat in H_jsz.
          rewrite <- ltn_subLR in H_jsz; auto.
        }
        apply Z.le_trans with (m:= nth (0%Z) zs1 (size zs1 - 1)); auto.
        apply Z.le_trans with (m:= nth (0%Z) zs2 0); auto.
        auto with zarith.
Qed.         

Lemma sorted_tail:
  forall z zs, sorted (z :: zs) -> sorted zs.
Proof.
  move=> z zs H_sorted.
  rewrite /sorted in H_sorted.
  rewrite /sorted.
  move=> i j H_0i H_ij H_j_sz.
  specialize (H_sorted (i.+1) (j.+1)).
  simpl in H_sorted.
  apply H_sorted; auto with arith.
Qed.

Lemma sorted_occ_le:
  forall zs z, sorted zs -> 0 < occ zs z -> ((nth (0%Z) zs 0) <= z)%Z.
Proof. 
  elim.
  - move=> z H_sorted H_lt. simpl in H_lt. inv H_lt.
  - move=> a l IH z H_sorted H_lt.
    assert (H_sorted0:=H_sorted).
    apply sorted_tail in H_sorted.
    simpl in H_lt.
    case En: (a =? z)%Z.
    + move: En. move /Z.eqb_eq. move->. simpl. auto with zarith.
    + simpl. 
      rewrite En in H_lt. simpl in H_lt. rewrite add_zero_l in H_lt.
      specialize (IH z H_sorted H_lt).
      case Enl: l=> [ | a' l'].
      rewrite Enl in H_lt. simpl in H_lt. inv H_lt.
      rewrite Enl in IH. simpl in IH.
      rewrite Enl in H_sorted0. rewrite /sorted in H_sorted0.
      specialize (H_sorted0 0 1).
      simpl in H_sorted0.
      apply Z.le_trans with (m:=a'); auto with zarith.
Qed.

Lemma occ_sorted_hd_corr:
  forall zs zs1 zs2,
    size zs > 0 -> 
    sorted zs ->
    sorted zs1 ->
    sorted zs2 ->
    (forall z, occ zs z = occ zs1 z + occ zs2 z) ->
    (size zs1 > 0 /\ nth (0%Z) zs 0 = nth (0%Z) zs1 0 \/
     size zs2 > 0 /\ nth (0%Z) zs 0 = nth (0%Z) zs2 0).
Proof.
  move=> zs zs1 zs2 H_0_zs
            H_sorted_zs H_sorted_zs1 H_sorted_zs2 H_occ.
  have H_pos_occ: occ zs (nth (0%Z) zs 0) > 0.
  {
    simpl. case En: zs => [ | z zs']. rewrite En in H_0_zs.
    simpl in H_0_zs. inv H_0_zs. simpl.
    case En': (z =? z)%Z. auto with arith.
    move: En'. move /Z.eqb_neq. auto with zarith.
  }
  specialize (H_occ (nth (0%Z) zs 0)) as H_occ'.
  rewrite H_occ' in H_pos_occ.
  have H_or: 0 < occ zs1 (nth 0%Z zs 0) \/ 0 < occ zs2 (nth 0%Z zs 0).
  {
    case En': (occ zs1 (nth 0%Z zs 0)) => [ | n']. 
    rewrite En' in H_pos_occ. right. auto with arith.
    left. auto with arith.
  }
  inversion H_or as [H_pos_occ_zs1 | H_pos_occ_zs2]; clear H_or.
  -
    have H_pos_occ_zs1': 0 < occ zs1 (nth 0%Z zs1 0).
    {
      case En: zs1 => [| z0 zs1'].
      rewrite En in H_pos_occ_zs1. simpl in H_pos_occ_zs1. inv H_pos_occ_zs1.
      simpl.
      have: (z0 =? z0)%Z = true by apply Z.eqb_refl.
      move->. auto with arith.
    }
    have H_le: (nth 0%Z zs 0 <= nth 0%Z zs1 0)%Z.
    {
      apply sorted_occ_le; auto.
      rewrite (H_occ (nth 0%Z zs1 0)).
      apply ltn_leq_trans with (n:=occ zs1 (nth 0%Z zs1 0)); auto.
      apply leq_addr.
    }
    have H_le': (nth 0%Z zs1 0 <= nth 0%Z zs 0)%Z 
        by apply sorted_occ_le; auto.
    left.
    apply: conj.
    destruct zs1. simpl in H_pos_occ_zs1. inv H_pos_occ_zs1. simpl; auto.
    auto with zarith.
  -
    have H_pos_occ_zs2': 0 < occ zs2 (nth 0%Z zs2 0).
    {
      case En: zs2 => [| z0 zs2'].
      rewrite En in H_pos_occ_zs2. simpl in H_pos_occ_zs2. inv H_pos_occ_zs2.
      simpl.
      have: (z0 =? z0)%Z = true by apply Z.eqb_refl.
      move->. auto with arith.
    }
    have H_le: (nth 0%Z zs 0 <= nth 0%Z zs2 0)%Z.
    {
      apply sorted_occ_le; auto.
      rewrite (H_occ (nth 0%Z zs2 0)).
      apply ltn_leq_trans with (n:=occ zs2 (nth 0%Z zs2 0)); auto.
      apply leq_addl.
    }
    have H_le': (nth 0%Z zs2 0 <= nth 0%Z zs 0)%Z 
        by apply sorted_occ_le; auto.
    right.
    apply: conj.
    destruct zs2. simpl in H_pos_occ_zs2. inv H_pos_occ_zs2. simpl; auto.
    auto with zarith.
Qed.     

Lemma sorted_hd_nxt:
  forall z zs,
    size zs > 0 -> 
    sorted (z :: zs) ->
    (z <= (nth 0%Z zs 0))%Z.
Proof.
  move=> z zs H_sz H_sorted. 
  specialize (H_sorted 0 1).
  have H': nth 0%Z (z :: zs) 1 = nth 0%Z zs 0.
  { destruct zs. inv H_sz. simpl; auto. }
  rewrite H' in H_sorted.
  have H'': nth 0%Z (z :: zs) 0 = z by simpl; auto.
  rewrite H'' in H_sorted.
  apply H_sorted; auto.
Qed.   
  
  
  
