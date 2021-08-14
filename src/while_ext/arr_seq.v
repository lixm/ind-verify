
Require Import Coq.Program.Basics. 
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq.

From indv Require Import arith tactics lists.
From indv.while_ext Require Import lang.

Definition arr_seq (X: arr_id) (b e: Z) (st: state) (zs: seq Z) : Prop :=
  (e < b)%Z /\ zs = [:: ] \/
  ((0<= b <= e)%Z /\ 
   (exists (b' e': nat) (l: Z),
       b' = (Z.to_nat b) /\ e' = (Z.to_nat e) /\
       arrst_of (store_of st) X = Some l /\
       size zs = e' - b' + 1 /\
       (forall i, b' <= i <= e' ->
                  stt_l st (Z.add l (Z.of_nat i)) = nth (0%Z) zs (i-b')))). 


Lemma arr_seq_empty:
  forall S b e st, Z.lt e b -> arr_seq S b e st [:: ].
Proof.
  move=> S b e st H_lt.
  rewrite /arr_seq.
  left; by apply: conj=>//.
Qed.

Lemma arr_seq_empty':
  forall X b e st zs, Z.lt e b -> arr_seq X b e st zs -> zs = [:: ].
Proof.
  move=> X b e st zs H_lt H_arrseq.
  inv H_arrseq.
  inv H; auto.
  inv H. inv H0.
  comp_contra H_lt H3.
Qed.

Lemma arr_seq_some_X:
  forall X b e st zs,
    (b <= e)%Z -> arr_seq X b e st zs -> exists l, stt_a st X = Some l.
Proof.
  move=> X b e st zs H_be H_arrseq.
  rewrite /arr_seq in H_arrseq.
  inv H_arrseq.
  inv H. comp_contra H0 H_be.
  clear H_arrseq.
  inv H.
  inversion H1 as [b' [e' [l [H_b' [H_e' [H_some_l H']]]]]];
    clear H1.
  exists l=>//.
Qed.

Lemma arr_seq_singleton:
  forall X b st l, 
    (0 <= b)%Z ->
    stt_a st X = Some l -> 
    arr_seq X b b st [:: stt_l st (l + b)%Z].
Proof.
  move=> X b st l H_0b H_l.
  rewrite /arr_seq.
  right.
  apply: conj. auto with zarith.
  do 2! (exists (Z.to_nat b)).
  exists l.
  repeat apply: conj=>//.
  simpl. rewrite sub_zero. auto.
  move=> i H_i_rgn. 
  have: i = Z.to_nat b
    by rewrite -eqn_leq in H_i_rgn; move: H_i_rgn; move /eqP=>//.
  move->. rewrite sub_zero. simpl.
  rewrite Z2Nat.id. auto.
  auto with zarith.
Qed.                      

Lemma arr_seq_eq:
  forall b e X1 X2 st1 st2 zs,
    stt_a st1 X1 = stt_a st2 X2 ->
    stt_l st1 = stt_l st2 ->
    arr_seq X1 b e st1 zs ->
    arr_seq X2 b e st2 zs.
Proof.
  move=> b e X1 X2 st1 st2 zs H_eq H_eq_sttl H_sta1.
  unfold arr_seq in *.
  inv H_sta1.
  - left=>//.
  - right.
    inversion H as [H_le [b' [e' [l H']]]].
    apply: conj=>//.
    exists b'. exists e'. exists l.
    inv H'. inv H1. inv H3. inv H5.
    repeat (try apply: conj=>//). 
    rewrite /stt_a /compose in H_eq.
    congruence.
    move=> i /H7; by congruence.
Qed.

Lemma arr_seq_eq_deep:
  forall b e X1 X2 st1 st2 zs l,
    stt_a st1 X1 = stt_a st2 X2 ->
    stt_a st1 X1 = Some l -> 
    (forall z, (b <= z)%Z -> (z <= e)%Z -> 
               stt_l st1 (l + z)%Z = stt_l st2 (l + z)%Z) ->
    arr_seq X1 b e st1 zs ->
    arr_seq X2 b e st2 zs.
Proof.
  move=> b e X1 X2 st1 st2 zs l H_X1_X2 H_X1_l H_eq H_arrseq_X1.
  rewrite /arr_seq in H_arrseq_X1. rewrite /arr_seq.
  inv H_arrseq_X1.
  - left=>//.
  - right. clear H_arrseq_X1.
    inversion H as [Hle [b' [e' [l' [H_b' [H_e' [H_l' [H_sz H']]]]]]]];
      clear H.
    apply conj=>//.
    exists b'. exists e'. exists l'.
    repeat apply: conj=>//.
    rewrite /stt_a /compose in H_X1_X2. congruence.
    move=> i H_i_rgn.
    have H_l'l: l = l'.
    { rewrite /stt_a /compose in H_X1_l. some_eq H_X1_l H_l'. }
    rewrite <- H_l'l in *. 
    move: H_i_rgn; move /andP=> HH.
    case HH=> H_b'i H_ie'.
    have H_ii: i = Z.to_nat (Z.of_nat i) by rewrite Nat2Z.id. 
    rewrite <- H_eq.
    apply H'; intuition.
    rewrite H_b' in H_b'i.    
    rewrite H_ii in H_b'i.
    move: H_b'i. move /leP. move /Z2Nat.inj_le=> H.
    apply: H; auto with zarith.
    rewrite H_e' in H_ie'.
    rewrite H_ii in H_ie'.
    move: H_ie'. move /leP. move /Z2Nat.inj_le=> H.
    apply H; auto with zarith.
Qed.

Lemma arr_seq_unique:
  forall S b e st zs zs',
    arr_seq S b e st zs -> arr_seq S b e st zs' -> zs = zs'.
Proof.
  move=> S0 b e st zs zs'.
  rewrite /arr_seq=>H1 H2.
  inv H1. inv H2.
  - inv H. inv H0. congruence.
  - inv H. inv H0. inv H5. comp_contra H3 H8. 
  - inv H2. inv H. inv H0. inv H3. comp_contra H5 H8. 
  - inv H. inv H0. clear H1. clear H2. clear H. clear H0.
    inversion H4 as [b1' [e1' [l1' [H_b1' [H_e1' [H_l1' [H_size1' H_all1]]]]]]];
      clear H4.
    inversion H6 as [b2' [e2' [l2' [H_b2' [H_e2' [H_l2' [H_size2' H_all2]]]]]]];
      clear H6.
    have H_eqsz: size zs = size zs' by congruence.
    inversion H3 as [H_0_le_b H_b_le_e]; clear H3 H5.
    have H_0_le_e: (0 <= e)%Z by apply Z.le_trans with (m:=b)=>//.
    have H_le1: b1' <= e1'.
    { rewrite H_b1'. rewrite H_e1'. apply /leP. apply /Z2Nat.inj_le=>//. }
    have H_eq_b: b1' = b2' by congruence.
    have H_eq_e: e1' = e2' by congruence.
    have H_eq_l: l1' = l2'.
    { rewrite H_l1' in H_l2'. inv H_l2'; auto. }
    rewrite <- H_eq_l in *.
    rewrite <- H_eq_b in *. rewrite <- H_eq_e in *.
    have H_i_eleeq:
      forall k, 0<=k<size zs -> nth (0%Z) zs k = nth (0%Z) zs' k.
    {
      move=> k H_rgn. 
      move: H_all1=>/(_ (k+b1'))=> H1.
      move: H_all2=>/(_ (k+b1'))=> H2.
      have H0: k + b1' - b1' = k.
      {
        rewrite <- addnBA. rewrite sub_zero. rewrite add_zero. auto.
        auto with arith.
      }
      have H_k_b1'_e1': k + b1' <= e1'.
      {
        inv H_rgn.
        have H_k_b1'_sz: k + b1' < size zs + b1' by rewrite ltn_add2r; auto.
        have: size zs + b1' == (e1' - b1' + 1) + b1' by rewrite eqn_add2r; apply /eqP=>//.
        move /eqP=>H''.
        have: e1' - b1' + 1 + b1' = e1' + 1.
        {
          apply /eqP. rewrite <- Nat.add_assoc. simpl.
          rewrite <- sub_add_1 with (m:=b1')=>//.
        }
        move: H''<-=>H_eq'. rewrite H_eq' in H_k_b1'_sz.
        rewrite addn1 in H_k_b1'_sz. auto with arith.
      }
      have H_b1'_le: 0 + b1' <= k + b1' by rewrite leq_add2r; auto. 
      rewrite add_zero_l in H_b1'_le.
      have H00:  b1' <= k + b1' <= e1'.
      { apply /andP /conj=>//. }
      specialize (H1 H00). specialize (H2 H00).      
      rewrite H1 in H2.
      rewrite <- addnBA in H2=>//. rewrite sub_zero in H2. rewrite add_zero in H2.
      auto. 
    }
    eapply eq_from_nth; eauto. 
Qed.

Lemma arr_seq_subrgn:
  forall S b e st1 st2 zs zs' b' e',
    arr_seq S b e st1 zs ->
    arr_seq S b e st2 zs ->
    (0 <= b <= b')%Z ->
    (0 <= e' <= e)%Z ->
    arr_seq S b' e' st1 zs' ->
    arr_seq S b' e' st2 zs'.
Proof.
  move=> S0 b e st1 st2 zs zs' b' e'
            H_arr_seq1 H_arr_seq2 H_b_le H_e_le H_arr_seq1'.
  unfold arr_seq in *.
  inversion H_arr_seq1 as [H_e_lt_b_conj | H_b_le_e_conj].
  -
    inv H_e_lt_b_conj.
    have H_e'_lt_b': (e' < b')%Z by auto with zarith.
    left. 
    inv H_arr_seq1'.
    + auto.
    + inv H1. inv H2. comp_contra H_e'_lt_b' H5. 
  -      
    inv H_b_le_e_conj.
    inv H_arr_seq2. inv H1. inv H. comp_contra H2 H5. 
    clear H_arr_seq1. clear H_arr_seq2.
    inv H1. clear H1. clear H2. 
    clear H_b_le_e_conj.
    inv H_arr_seq1'; clear H_arr_seq1'. 
    + left. auto.
    + right.
      rename H0 into H_st1_orig. rename H3 into H_st2_orig.
      inv H1; clear H1.
      apply: conj=>//. rename H2 into H_st1_subrgn.
      inversion H_st1_subrgn as
          [b'0 [e'0 [l [H_b'0 [H_e'0 [H_S0_l [H_sz H_all]]]]]]];
        clear H_st1_subrgn.
      exists b'0. exists e'0. 
      inversion H_st1_orig as
          [b1' [e1' [l1 [H_b1' [H_e1' [H_l1 [H_sz1 H_all1]]]]]]]; 
        clear H_st1_orig. 
      inversion H_st2_orig as
          [b2' [e2' [l2 [H_b2' [H_e2' [H_l2 [H_sz2 H_all2]]]]]]];
        clear H_st2_orig.
      have H_b'_eq: b1' = b2' by congruence. 
      have H_e'_eq: e1' = e2' by congruence.
      exists l2. 
      repeat (try apply: conj=>//).
      move=> i H_i_subrgn. move: H_all=>/(_ i H_i_subrgn).
      have: l = l1 by some_eq H_S0_l H_l1.
      move->.
      rewrite <- H_b'_eq in H_all2. rewrite <- H_e'_eq in H_all2.
      have H1'': b1' <= b'0.
      { rewrite H_b'0. rewrite H_b1'. apply /leP. apply Z2Nat.inj_le.
        inv H_b_le. auto. inv H0. auto. inv H_b_le. auto. }
      have H2'': e'0 <= e1'.
      { rewrite H_e'0. rewrite H_e1'. apply /leP. apply Z2Nat.inj_le.
        inv H_e_le. auto. inv H. apply Z.le_trans with (m:=b)=>//.
        inv H_e_le; auto. }
      have H_i_orig_rgn: b1' <= i <= e1'.
      {
        apply /andP. move: H_i_subrgn. move /andP=>H0''. inv H0''.
        apply: conj; eapply leq_trans; eauto.  
      }
      move: H_all1=>/(_ i H_i_orig_rgn).
      move: H_all2=>/(_ i H_i_orig_rgn)=><-=>H00.
      congruence.
Qed.

Lemma arr_seq_ele0:
  forall X b e st zs ae z l, 
    arr_seq X b e st zs ->
    arrst_of (store_of st) X = Some l -> 
    (l + z < floc_of st)%Z ->
    aval ae st = Some z ->
    (b <= z)%Z ->
    (z <= e)%Z ->
    aval (AARef (AArr X) ae) st =
    Some (nth (0%Z) zs (Z.to_nat (z - b))).
Proof.
  move=> X b e st zs ae z l H_zs H_l H_flc H_z H_bz H_ze.
  rewrite /arr_seq in H_zs.
  inv H_zs; clear H_zs.
  inv H.
  have H_be: (b <= e)%Z by auto with zarith.
  comp_contra H0 H_be.
  inv H; clear H.
  inversion H1 as [b' [e' [l0 [H_b' [H_e' [H_l0 [H_zs' H_all]]]]]]];
    clear H1.
  simpl.
  rewrite /stt_a /compose. rewrite H_l.
  rewrite H_z.
  have: (z >=? 0)%Z && (l + z <? floc_of st)%Z.
  apply /andP. apply: conj. 
  apply /Z.geb_le. auto with zarith.
  apply /Z.ltb_lt=>//. 
  move->.
  have: l = l0 by some_eq H_l H_l0.
  move->.
  have H_rgn: b' <= Z.to_nat z <= e'.
  {
    apply /andP; apply: conj;
    [rewrite H_b' | rewrite H_e']; 
    apply /leP; apply Z2Nat.inj_le; auto with zarith.    
  }
  specialize (H_all (Z.to_nat z) H_rgn).
  rewrite Z2Nat.id in H_all.
  rewrite Z2Nat.inj_sub. rewrite <- H_b'.
  rewrite H_all. auto.
  auto with zarith. auto with zarith.
Qed.

Lemma arr_seq_ele:
  forall X b e st zs l z,
    arr_seq X b e st zs ->
    stt_a st X = Some l ->
    (b <= z)%Z ->
    (z <= e)%Z ->
    stt_l st (l + z)%Z = (nth (0%Z) zs (Z.to_nat (z - b))).
Proof.
  move=> X b e st zs l z H_arrseq H_l H_bz H_ze.
  rewrite /arr_seq in H_arrseq.
  have H_be: (b <= e)%Z by auto with zarith.
  inv H_arrseq; clear H_arrseq.
  - inv H. comp_contra H0 H_be.
  - inv H; clear H.
    inversion H1 as [b' [e' [l' [H_b' [H_e' [H_l' [H_zs H_alli]]]]]]];
      clear H1.
    have H_ll': l = l' by rewrite /stt_a /compose in H_l; some_eq H_l H_l'.
    rewrite <- H_ll' in *. 
    clear l' H_ll'.
    have H_z_rgn:  b' <= Z.to_nat z <= e'.
    {
      rewrite H_b' H_e'. apply /andP. apply: conj.
      assert (H_bz0:=H_bz).
      move: H_bz; move /Z2Nat.inj_le=> H'. 
      apply /leP. apply H'; auto with zarith.
      assert (H_ze0:=H_ze).
      move: H_ze; move /Z2Nat.inj_le=> H'.
      apply /leP. apply H'; auto with zarith.
    }
    specialize (H_alli (Z.to_nat z) H_z_rgn).
    rewrite Z2Nat.id in H_alli; auto with zarith.
    rewrite H_b' in H_alli.
    rewrite Z2Nat.inj_sub; auto with zarith.
Qed.

Lemma arr_seq_ele_eq:
  forall X b e st st' zs i l l', 
    arr_seq X b e st zs ->
    arr_seq X b e st' zs ->
    (0 <= b)%Z -> 
    (b <= i)%Z ->
    (i <= e)%Z ->
    stt_a st X = Some l ->
    stt_a st' X = Some l' ->  
    stt_l st (l + i)%Z = stt_l st' (l' + i)%Z.
Proof.
  move=> X b e st st' zs i l l'.
  move=> H_arrseq_st H_arrseq_st' H_0b H_bi H_ie H_l H_l'.
  have Heq1:
    stt_l st (l + i)%Z = (nth (0%Z) zs (Z.to_nat (i - b)))
    by apply arr_seq_ele with (X:=X) (e:=e); auto with zarith.
  have Heq2:
    stt_l st' (l' + i)%Z = (nth (0%Z) zs (Z.to_nat (i - b)))
    by apply arr_seq_ele with (X:=X) (e:=e); auto with zarith.
  congruence.
Qed.   

Lemma arr_seq_size:
  forall X b e st zs, 
    (b <= e)%Z -> 
    arr_seq X b e st zs ->
    size zs = Z.to_nat (e - b) + 1.
Proof.
  move=> X b e st zs.
  move=> H_be H_arrseq.
  rewrite /arr_seq in H_arrseq.
  inv H_arrseq.
  inv H.
  comp_contra H_be H0.
  inv H; clear H. clear H_arrseq. 
  inversion H1 as [b' [e' [l [H_b' [H_e' [H_l [H_sz H_alli]]]]]]];
    clear H1.
  rewrite H_sz.
  rewrite H_b' H_e'.
  rewrite Z2Nat.inj_sub. auto with zarith.
  inv H0; auto.
Qed.

Lemma arr_seq_concat :
  forall S b1 e1 e2 st zs1 zs2,
    (0 <= b1 <= e1)%Z ->
    (e1 + 1 <= e2)%Z -> 
    arr_seq S b1 e1 st zs1 ->
    arr_seq S (e1 + 1) e2 st zs2 ->
    arr_seq S b1 e2 st (zs1 ++ zs2).
Proof.
  move=> S b1 e1 e2 st zs1 zs2 H_b1e1 H_e1e2.
  move=> H_arrseq1 H_arrseq2.
  unfold arr_seq in *.
  inv H_arrseq1.
  - inv H. inv H_b1e1. comp_contra H0 H3. 
  - inv H_arrseq2. inv H0. comp_contra H1 H_e1e2.
    clear H_arrseq1; clear H_arrseq2.
    right.
    apply: conj.
    + apply: conj; auto with zarith. 
    + inv H. clear H1. inv H0. clear H1.
      clear H0. clear H.
      inversion H2 as [b1' [e1' [l1 [H_b1' [H_e1' [H_l1 [H_sz1 H_all1]]]]]]];
        clear H2.
      inversion H3 as [b2' [e2' [l2 [H_b2' [H_e2' [H_l2 [H_sz2 H_all2]]]]]]];
        clear H3.
      exists b1'. exists e2'. exists l1.
      repeat (try apply: conj=>//).
      *
        rewrite size_cat. rewrite H_sz1. rewrite H_sz2.
        rewrite H_b1'; rewrite H_e1'; rewrite H_b2'; rewrite H_e2'.
        rewrite addnBAC.
        have H_e1_1: Z.to_nat e1 + 1 = Z.to_nat (e1 + 1).
        {
          rewrite <- z_tonat_1. symmetry. 
          apply Z2Nat.inj_add; auto with zarith.
        }
        rewrite H_e1_1.
        rewrite addnBAC. rewrite addnBAC. rewrite addnABC. 
        rewrite sub_zero. rewrite add_zero_l. 
        rewrite addnBAC. reflexivity.
        inv H_b1e1.
        apply /leP. apply Z2Nat.inj_le; try (inv H_b1e1; auto with zarith).
        apply leqnn.
        rewrite -{1} z_tonat_1. rewrite <- Z2Nat.inj_add. 
        apply /leP. apply Z2Nat.inj_le; try (inv H_b1e1; auto with zarith). 
        auto with zarith. auto with zarith.
        apply /leP. apply Z2Nat.inj_le; try (inv H_b1e1; auto with zarith). 
        apply /leP. apply Z2Nat.inj_le; try (inv H_b1e1; auto with zarith). 
        apply /leP. apply Z2Nat.inj_le; try (inv H_b1e1; auto with zarith).
      *
        move=> i H_i_rgn.
        have H_b2'_e1': b2' = e1' + 1.
        { rewrite H_e1'. rewrite H_b2'. rewrite <- z_tonat_1.
          apply Z2Nat.inj_add; auto with zarith. }
        have H_i_rgns: (b1' <= i <= e1' \/ b2' <= i <= e2').
        {
          rewrite H_b2'_e1'. apply rgn_divide=>//.
          rewrite H_b1'. rewrite H_e1'. 
          apply /andP. apply: conj.
          inv H_b1e1. auto with zarith.
          inv H_b1e1. apply /leP; apply Z2Nat.inj_le; auto with zarith.
          rewrite H_e1'. rewrite H_e2'. rewrite <- z_tonat_1.
          rewrite <- Z2Nat.inj_add; inv H_b1e1; auto with zarith.
          apply /leP. apply Z2Nat.inj_le; auto with zarith.
        }
        inversion H_i_rgns as [H_i_left | H_i_right].
        (* i in the left range *)
        specialize (H_all1 i H_i_left).
        have H_i_lt_sz: i - b1' < size zs1.
        {
          have H_le: i - b1' <= e1' - b1'.
          { apply leq_sub2r. move: H_i_left; move /andP.
            move=> HH; inv HH; auto. }
          rewrite H_sz1.
          rewrite addn1. rewrite ltnS. auto. 
        }
        rewrite nth_cat. rewrite H_i_lt_sz. auto. 
        (* i in the right range *)
        specialize (H_all2 i H_i_right).
        have: l1 = l2 by some_eq H_l1 H_l2. 
        move->.
        have H_i_b1'_sz: i - b1' - size zs1 = i - b2'.
        {
          rewrite H_sz1. rewrite subnDA. rewrite subnBA. 
          rewrite <- addnABC. rewrite sub_zero.
          rewrite add_zero. rewrite <- subnDA. 
          rewrite <- H_b2'_e1'=>//.
          move: H_i_rgn; move /andP. move=> HH; inv HH; auto.
          auto with arith.
          rewrite H_b1'. rewrite H_e1'.
          apply /leP. apply Z2Nat.inj_le. auto with zarith.
          inv H_b1e1; auto with zarith. 
          inv H_b1e1; auto with zarith. 
        }
        rewrite nth_cat.
        have H_i_b1'_gt_sz: i - b1' >= size zs1. 
        {
          rewrite H_sz1. rewrite addn1.           
          apply ltn_sub2r.
          move: H_i_right; move /andP.
          move=> HH; inv HH.
          have H_b1'_lt_b2': b1' < b2'.
          { rewrite H_b1'. rewrite H_b2'.
            apply /ltP. apply Z2Nat.inj_lt.
            inv H_b1e1; auto. inv H_b1e1; auto with zarith.
            inv H_b1e1; auto with zarith. }
          rewrite leq_eqVlt in H.
          move: H; move /orP. move=> HH'. inv HH'.
          move: H; move /eqP. move=> H_b2'_i.
          rewrite H_b2'_i in H_b1'_lt_b2'. auto.
          eapply ltn_trans; eauto.
          move: H_i_right; move /andP. move=> HH.
          inv HH. rewrite H_b2' in H.
          rewrite Z2Nat.inj_add in H.
          rewrite <- H_e1' in H. rewrite z_tonat_1 in H.
          apply le_1_lt. auto with arith. 
          inv H_b1e1; auto with zarith.
          auto with zarith. 
        }
        have: i - b1' < size zs1 = false.
        rewrite ltnNge. rewrite H_i_b1'_gt_sz=>//. 
        move->. rewrite H_i_b1'_sz=>//.
Qed.

Lemma arr_seq_concat_general :
  forall X b1 e1 e2 st zs1 zs2,
    (0 <= b1)%Z ->
    (b1-1 <= e1)%Z ->
    (e1 <= e2)%Z ->
    arr_seq X b1 e1 st zs1 ->
    arr_seq X (e1 + 1) e2 st zs2 ->
    arr_seq X b1 e2 st (zs1 ++ zs2).
Proof.
  move=> X b1 e1 e2 st zs1 zs2 H_0b1 H_b1e1 H_e1e2
           H_arrseq_zs1 H_arrseq_zs2.
  have H_case_b1e1: (b1 <= e1)%Z \/ (e1 = b1 - 1)%Z.
  {
    apply Zle_lt_or_eq in H_b1e1.
    inv H_b1e1; [left; auto with zarith | right; auto with zarith].
  }
  have H_case_e1e2: (e1+1 <= e2)%Z \/ (e1 = e2)%Z.
  {
    apply Zle_lt_or_eq in H_e1e2.
    inv H_e1e2; [left; auto with zarith | right; auto with zarith].
  }
  inversion H_case_b1e1 as [H_b1_le_e1 | H_e1_eq_b1_1];
    clear H_case_b1e1.
  -
    inversion H_case_e1e2 as [H_e1_1_le_e2 | H_e1_eq_e2];
      clear H_case_e1e2.
    +
      apply arr_seq_concat with (e1:=e1); auto with zarith.
    +
      have H_e2_lt: (e2 < e1 + 1)%Z by auto with zarith.
      have: zs2 = [:: ]
        by apply arr_seq_empty' with (X:=X) (b:=(e1+1)%Z) (e:=e2) (st:=st);
        auto with zarith.
      move->.
      have: zs1 ++ [:: ] = zs1 by apply cats0.
      move->.
      congruence.
  -
    have H_e1_lt: (e1 < b1)%Z by auto with zarith.
    have: zs1 = [:: ]
      by apply arr_seq_empty' with (X:=X) (b:=b1) (e:=e1) (st:=st);
      auto with zarith.
    move->=>/=.
    rewrite H_e1_eq_b1_1 in H_arrseq_zs2.
    have: (b1 - 1 + 1 = b1)%Z by auto with zarith.
    move<-=>//.
Qed.    
       
Lemma arr_seq_subrgn_lst_frag: 
  forall S b e b' e' st zs zs',
    (0 <= b <= e)%Z ->
    (0 <= b' <= e')%Z ->
    arr_seq S b e st zs ->
    arr_seq S b' e' st zs' ->
    (b <= b')%Z ->
    (e' <= e)%Z ->
    lst_frag (b'-b)%Z zs' zs. 
Proof.
  move=> S0 b e b' e' st zs zs'
            H_be H_b'e' H_arrseq_zs H_arrseq_zs' H_bb' H_e'e.
  inv H_arrseq_zs.
  - inv H; inv H_be; comp_contra H0 H3.
  - inv H_arrseq_zs'.
    + inv H0; inv H_b'e'; comp_contra H1 H4.
    + inv H. inv H0. clear H. clear H0.
      inversion H2 as [b'1 [e'1 [l1 [H_b'1 [H_e'1 [H_S0_l1 [H_sz1 H_all1]]]]]]];
        clear H2. 
      inversion H4 as [b'2 [e'2 [l2 [H_b'2 [H_e'2 [H_S0_l2 [H_sz2 H_all2]]]]]]];
        clear H4.
      rewrite /lst_frag.
      move=> i H_i_lt.
      apply: conj.
      * rewrite H_sz1. rewrite H_sz2 in H_i_lt.
        rewrite H_b'1 H_e'1. rewrite H_b'2 H_e'2 in H_i_lt. 
        have H_pre: i + Z.to_nat (b' - b) <
              (Z.to_nat e' - Z.to_nat b' + 1) + Z.to_nat (b' - b) 
          by rewrite ltn_add2r=>//.
        rewrite {2}[Z.to_nat (b'-b)]Z2Nat.inj_sub in H_pre;
          auto with zarith. 
        rewrite <- Nat.add_assoc in H_pre.
        rewrite [(1 + _)%coq_nat]Nat.add_comm in H_pre.
        rewrite Nat.add_assoc in H_pre; auto with zarith. 
        rewrite [((_ - _) + (_ - _)%coq_nat)%coq_nat]addnBA in H_pre.
        rewrite subnK in H_pre.
        apply ltn_leq_trans with (n:=Z.to_nat e' - Z.to_nat b + 1). 
        assumption.
        rewrite leq_add2r. rewrite leq_sub2r=>//.
        apply /leP; apply Z2Nat.inj_le;
          try (inv H_be; inv H_b'e'; auto with zarith).
        apply /leP; apply Z2Nat.inj_le;
          try (inv H_be; inv H_b'e'; auto with zarith).
        apply /leP; apply Z2Nat.inj_le;
          try (inv H_be; inv H_b'e'; auto with zarith).
      * have H_l1l2: l1 = l2 by some_eq H_S0_l1 H_S0_l2.
        rewrite <- H_l1l2 in *.
        specialize (H_all2 (i+b'2)).
        rewrite <- addnBA in H_all2.
        rewrite sub_zero add_zero in H_all2.
        have H_eq': stt_l st (l1 + Z.of_nat (i + b'2))%Z = nth 0%Z zs' i.
        apply H_all2. apply /andP. apply: conj.
        apply leq_addl.
        rewrite H_sz2 in H_i_lt.
        rewrite <- ltn_add2r with (p:=b'2) in H_i_lt.
        rewrite <- Nat.add_assoc in H_i_lt.
        rewrite [(1+b'2)%coq_nat] Nat.add_comm in H_i_lt.
        rewrite Nat.add_assoc in H_i_lt.
        rewrite [(e'2-b'2+b'2)%coq_nat]subnK in H_i_lt.
        rewrite [(e'2+1)%coq_nat]addn1 in H_i_lt.
        apply ltnSE; auto.
        rewrite H_b'2; rewrite H_e'2.
        apply /leP; apply Z2Nat.inj_le; auto with zarith.
        specialize (H_all1 (i+b'2)).
        rewrite H_all1 in H_eq'.
        rewrite <- H_eq'.
        rewrite H_b'2. rewrite H_b'1.
        rewrite <- addnBA. 
        rewrite Z2Nat.inj_sub; auto.
        inv H_be; auto.
        apply /leP; apply Z2Nat.inj_le; auto with zarith.
        apply /andP. apply: conj.
        rewrite H_b'1. rewrite H_b'2.
        apply leq_trans with (n:=Z.to_nat b').
        apply /leP; apply Z2Nat.inj_le; auto with zarith.
        apply leq_addl. 
        rewrite H_b'2. rewrite H_e'1. 
        rewrite <- ltn_add2r with (p:=Z.to_nat b') in H_i_lt.
        rewrite H_sz2 in H_i_lt.
        rewrite H_e'2 in H_i_lt. rewrite H_b'2 in H_i_lt.
        rewrite <- Nat.add_assoc in H_i_lt.
        rewrite [(1+Z.to_nat b')%coq_nat]Nat.add_comm in H_i_lt.
        rewrite Nat.add_assoc in H_i_lt.
        rewrite [(_ - Z.to_nat b' + Z.to_nat b')%coq_nat]subnK in H_i_lt.
        rewrite [(Z.to_nat e' + 1)%coq_nat]addn1 in H_i_lt.
        apply ltnSE in H_i_lt. 
        apply leq_trans with (n:= Z.to_nat e'); auto.
        apply /leP; apply Z2Nat.inj_le;
          try (inv H_be; inv H_b'e'; auto with zarith).
        apply /leP; apply Z2Nat.inj_le;
          try (inv H_be; inv H_b'e'; auto with zarith).
        auto.
Qed.

Lemma arr_seq_ex:
  forall X b e st l,
    (0 <= b)%Z ->
    stt_a st X = Some l -> 
    exists zs', arr_seq X b e st zs'. 
Proof.
  move=> X b e st l H_b H_l.
  rewrite /arr_seq.
  have: (e < b \/ b <= e)%Z
    by apply Z.lt_ge_cases; auto.
  case=>H_cs.
  - exists [:: ]. left; apply: conj=>//.
  - move En: (Z.to_nat (e - b)) => delta.
    move: delta b e En H_b H_cs l H_l.
    elim.
    + move=> b e H_delta H_0b H_be l H_l.
      have: b = e by auto with zarith.
      move->.
      exists [:: (stt_l st (l+e)%Z) ].
      right.
      apply: conj; auto with zarith.
      exists (Z.to_nat e). exists (Z.to_nat e). exists l.
      apply: conj=>//. apply: conj=>//.
      rewrite /stt_a /compose in H_l. apply: conj=>//.
      apply: conj. simpl. rewrite sub_zero. auto.
      move=> i H_i_rgn. 
      have: i = Z.to_nat e.
      { rewrite <- eqn_leq in H_i_rgn.
        move: H_i_rgn; move /eqP=>//. }
      move->.
      rewrite sub_zero. simpl.
      rewrite Z2Nat.id; auto with zarith.
    + move=> n IH.
      move=> b e H_delta H_0b H_be l H_l.
      move Enb'': (b+1)%Z => b''.
      have H_0b'': (0 <= b'')%Z by auto with zarith.
      have H_eb1: (e >= b+1)%Z by auto with zarith.
      have H_b''e: (b'' <= e)%Z by auto with zarith.
      have H_delta0: Z.to_nat (e - b'') = n by auto with zarith.
      specialize (IH b'' e H_delta0 H_0b'' H_b''e l H_l).
      inversion IH as [zs0 H_or]; clear IH. 
      inv H_or; clear H_or.
      * inv H. comp_contra H0 H_b''e. 
      * inv H; clear H.
        inversion H1 as
            [b' [e' [l' [H_b' [H_e' [H_l' [H_sz' H_forall]]]]]]];
          clear H1.
        move En_zs: ((stt_l st (l+b)%Z) :: zs0) => zs.
        exists zs.
        right.
        apply: conj=>//.
        exists (Z.to_nat b). exists (Z.to_nat e). exists l.
        do 3! (apply: conj=>//).
        apply: conj.
        
        rewrite <- En_zs. simpl. rewrite H_sz'.
        rewrite H_e' H_b' - Enb''.
        rewrite <- addn1.
        apply /eqP; rewrite eqn_add2r.
        rewrite Z2Nat.inj_add; auto with zarith.
        rewrite subnDA. rewrite z_tonat_1.
        rewrite subnK=>//.
        rewrite <- Z2Nat.inj_sub; auto with zarith.
        have H_diff1: (e - b >= 1)%Z by auto with zarith.
        case En_tonat: (Z.to_nat (e - b))=> [| n'].
        have Heq: e = b by auto with zarith. rewrite Heq in H_diff1.
        rewrite Z.sub_diag in H_diff1; auto.
        apply ltn_leq_trans with (n:=1); auto.

        move=> i H_i_rgn'.
        move: H_i_rgn'; move /andP=> HH; inv HH.
        have: i = (Z.to_nat b) \/ i >= b'.
        {
          rewrite H_b' -Enb''.
          have: Z.to_nat (b+1) = Z.to_nat b + 1
            by rewrite Z2Nat.inj_add; auto with zarith.
          move->.
          apply nat_ge_cases; auto.
        }
        case=> H_case. 
        rewrite H_case. rewrite sub_zero.
        rewrite Z2Nat.id; auto with zarith.
        rewrite <-En_zs=>//. 
        rewrite <- H_e' in H1.
        have H_i_newrgn: b' <= i <= e' by apply /andP=>//.
        specialize (H_forall i H_i_newrgn).
        have: l = l' by rewrite /stt_a /compose in H_l; some_eq H_l H_l'.
        move->.
        rewrite H_forall. 
        have H_1: i - Z.to_nat b = (i - b') + 1.
        {
          rewrite H_b' -Enb''.
          rewrite Z2Nat.inj_add; auto with zarith.
          rewrite subnDA. rewrite z_tonat_1.
          rewrite subnK=>//.
          rewrite H_b' -Enb'' in H_case.
          apply leq_sub2r with (p:=Z.to_nat b) in H_case.
          rewrite Z2Nat.inj_add in H_case; auto with zarith.
          rewrite Nat.add_comm in H_case. 
          rewrite <- addnBA in H_case; auto with zarith.
          rewrite sub_zero in H_case. rewrite add_zero in H_case.
          apply /ltP.
          apply lt_le_trans with (m:=Z.to_nat 1).
          rewrite z_tonat_1; auto.
          apply /leP; auto.
        }
        have: i - Z.to_nat b = (i - b').+1 by rewrite <- addn1; auto.
        move->. rewrite <- En_zs.
        simpl. auto.
Qed.

(* specialized version of arr_seq_concat *)
Lemma arr_seq_extend:
  forall X b e st zs l z, 
    arr_seq X b e st zs ->
    (0 <= b)%Z ->
    (b <= e)%Z -> 
    stt_a st X = Some l -> 
    z = stt_l st (l + e + 1)%Z ->
    arr_seq X b (e+1) st (zs++[:: z]).
Proof.
  move=> X b e st zs l z.
  move=> H_arrseq H_0b H_be H_l H_z.
  have H_arr_seq': arr_seq X (e+1) (e+1) st [:: z].
  {
    rewrite /arr_seq. right.
    apply: conj.
    - auto with zarith.
    - exists (Z.to_nat (e+1)).
      exists (Z.to_nat (e+1)).
      exists l.
      repeat (apply: conj=>//).
      simpl. rewrite sub_zero. auto.
      move=> i H_i_rgn.
      rewrite <- eqn_leq in H_i_rgn.
      move: H_i_rgn. move /eqP<-.
      rewrite sub_zero.
      simpl.
      rewrite Z2Nat.id; auto with zarith.
      rewrite Z.add_assoc=>//.
  }
  apply arr_seq_concat with (e1:=e); auto with zarith.
Qed.
