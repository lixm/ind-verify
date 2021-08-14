
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

From indv Require Import arith tactics lists sem.
From indv.fun Require Import lang cfm.


(* the list-merging program *)

Definition merge_id: id := 0.

Definition x_id: id := 1.
Definition x'_id: id := 2.

Definition i_id: id := 3.
Definition i'_id: id := 4.

Definition r_id: id := 5.
Definition r'_id: id := 6. 

Definition e_if :=
  IfE (LeE (VarE i_id) (VarE i'_id))
      (PPendE (VarE i_id) (AppE (AppE (VarE merge_id) (VarE r_id)) (VarE x'_id)))
      (PPendE (VarE i'_id) (AppE (AppE (VarE merge_id) (VarE x_id)) (VarE r'_id))).

Definition e_lcase :=
  LCaseE (VarE x_id)
         (VarE x'_id)
         (AbsE i_id (AbsE r_id
                          (LCaseE (VarE x'_id)
                                  (VarE x_id)
                                  (AbsE i'_id (AbsE r'_id e_if))))). 

Definition e_mg (lcf1 lcf2: expr) :=
  LetRecE merge_id
          (AbsE x_id (AbsE x'_id e_lcase))
          (AppE (AppE (VarE merge_id) lcf1) lcf2).


(* the specification *)

(* aux. function computing the sequence (list) for a list canonical form *)
(* assuming lcf is a list canonical form *) 
Fixpoint lcf_seq (lcf: expr) : seq Z :=
  match lcf with
    PPendE (NE z) lcf' => (z :: lcf_seq lcf')
  | _ => [:: ]
  end.

(* the actual specification *) 
Inductive mg_spec (u:unit): Spec unit fun_config fun_rconfig u :=
  
  FUN_SP_e_mg (lcf1 lcf2: expr) (zs1 zs2: seq Z):
    is_zlcfm lcf1 ->
    is_zlcfm lcf2 ->
    zs1 = lcf_seq lcf1 ->
    zs2 = lcf_seq lcf2 -> 
    sorted zs1 ->
    sorted zs2 -> 
    mg_spec _
            (e_mg lcf1 lcf2)
            (fun r => (is_zlcfm r /\
                       (forall z, occ (lcf_seq r) z = occ zs1 z + occ zs2 z) /\
                       sorted (lcf_seq r)))
            
| FUN_SP_e_unfold (lcf1 lcf2: expr) (zs1 zs2: seq Z):
    is_zlcfm lcf1 ->
    is_zlcfm lcf2 ->
    zs1 = lcf_seq lcf1 ->
    zs2 = lcf_seq lcf2 -> 
    sorted zs1 ->
    sorted zs2 -> 
    mg_spec _
            (AppE 
               (AppE
                  (AbsE x_id
                        (LetRecE merge_id
                                 (AbsE x_id (AbsE x'_id e_lcase))
                                 (AbsE x'_id e_lcase)))
                  lcf1)
               lcf2) 
            (fun r => (is_zlcfm r /\
                       (forall z, occ (lcf_seq r) z = occ zs1 z + occ zs2 z) /\
                       sorted (lcf_seq r))).

Lemma cfm_not_in_mg_spec:
  forall (u:unit), cfm_not_in_spec u (mg_spec u).
Proof.
  move=> u. 
  rewrite /cfm_not_in_spec.
  move=> cf H_is_cfm.
  try destruct cf; inv H_is_cfm; 
  try (move=> contra; inv contra; inv H).
Qed. 


(* the correctness proof *) 

Theorem mg_spec_valid: forall prm, valid _ (mg_spec prm).
Proof.
  init_verif. 
  inversion H0; subst.
  
  - (* proof for overall expression *)
    rename H1 into H_lcfm_lcf1. rename H2 into H_lcfm_lcf2.
    rename H5 into H_sorted_lcf1. rename H6 into H_sorted_lcf2.
    inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst. clear H_rule.
    rename H4 into H_abs_eq. inversion H_abs_eq; subst. clear H_abs_eq.

    prem0_exe H_all.
    prem0_exe hall. clear hall0. prem1_exe hall. clear hall0.
    simpl in hall. repeat rewrite zlcfm_subst in hall; auto.
    prem2_spec hall. use_spec hspc.
    {
      eexists; 
        apply FUN_SP_e_unfold
          with (lcf1:=lcf1) (lcf2:=lcf2) (zs1:=lcf_seq lcf1) (zs2:=lcf_seq lcf2);
        auto.
    }
    apply: conj=>//.
    
  - (* proof for the unfolded expression *)
    rename H1 into H_lcfm_lcf1. rename H2 into H_lcfm_lcf2.
    rename H5 into H_sorted_lcf1. rename H6 into H_sorted_lcf2.
    inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst. clear H_rule.
    prem0_exe H_all.
    prem0_exe hall. clear hall0. prem1 hall hall1.
    inversion hall1 as [H_allP H_nexP]; clear hall1 H_allP.
    have H_inf: infer prm (mg_spec prm) (lcf1, cf'0).
    { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
    have H_cf'0_eq_lcf1: cf'0 = lcf1.
    { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
    symmetry in H_cf'0_eq_lcf1. rewrite <- H_cf'0_eq_lcf1 in *.
    prem2_exe hall. 
    rename H7 into H_abs_eq. inversion H_abs_eq; subst. clear H_abs_eq.
    prem0_exe hall0.
    prem0_exe hall1. clear hall2. prem1_exe hall1. clear hall2.
    prem2_exe hall1. clear hall2.
    rename H7 into H_is_cfm_abs. clear H_is_cfm_abs.
    rename H10 into H_is_cfm_abs. clear H_is_cfm_abs.
    clear hall1. clear hall0.
    rename H5 into H_is_cfm_abs. clear H_is_cfm_abs.
    clear H_inf. clear H_nexP. 
    clear hall.
    prem1 H_all H_all1.
    inversion H_all1 as [H_allP H_nexP]; clear H_all1 H_allP.
    have H_inf: infer prm (mg_spec prm) (lcf2, cf').
    { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
    clear H_nexP.
    have H_cf'_eq_lcf2: cf' = lcf2.
    { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
    symmetry in H_cf'_eq_lcf2. rewrite <- H_cf'_eq_lcf2 in *.
    clear cf' H_cf'_eq_lcf2. clear H_inf.
    prem2_exe H_all; rename cf'0 into lcf1.
    
    +  (* first list is NilE *)
      repeat rewrite zlcfm_subst in hall; auto.
      2: { rewrite zlcfm_subst; auto. }
      prem0 hall h'. inversion h' as [H_allP H_nexP]; clear h' H_allP.
      have H_inf: infer prm (mg_spec prm) (lcf1, NilE). 
      { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
      clear H_nexP. 
      have H_lcf1_nil: lcf1 = NilE by eapply zlcfm_infer_nil; eauto. 
      prem1 hall h'. inversion h' as [H_allP H_nexP]; clear h' H_allP.
      have H_inf': infer prm (mg_spec prm) (lcf2, r).
      { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
      have H_r_eq_cf': r = lcf2.
      { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
      symmetry in H_r_eq_cf'. rewrite <- H_r_eq_cf' in *. 
      rewrite H_lcf1_nil. simpl.
      apply: conj=>//.
      
    + (* first list is not NilE *)
      repeat rewrite zlcfm_subst in hall; auto.
      2: { rewrite zlcfm_subst; auto. }
      prem0 hall h'. inversion h' as [H_allP H_nexP]; clear h'.
      have H_inf: infer prm (mg_spec prm) (lcf1, PPendE cf cf'). 
      { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
      apply zlcfm_infer_pend in H_inf; auto. 2: { apply cfm_not_in_mg_spec. }
      inversion H_inf as [z1 [H_lcf1_eq_pend [H_cf_ne H_zlcfm_cf'0]]]; clear H_inf.
      symmetry in H_lcf1_eq_pend. rewrite <- H_lcf1_eq_pend in *.
      clear lcf1 H_lcf1_eq_pend.
      symmetry in H_cf_ne. rewrite <- H_cf_ne in *. clear cf H_cf_ne.
      clear H_allP H_nexP.
      prem1_exe hall.
      prem0_exe hall0.
      prem0_exe hall1. clear hall2. prem1_exe hall1. clear hall2.
      prem2_exe hall1. clear hall2. clear hall1.
      rename H9 into H_is_cfm_abs. clear H_is_cfm_abs.
      rename H15 into H_is_cfm_ne_z1. clear H_is_cfm_ne_z1.
      prem1 hall0 h'.
      inversion h' as [H_allP H_nexP]; clear h' H_allP.
      have H_inf: infer prm (mg_spec prm) (cf', cf'0).
      { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
      have H_cf'0_eq_cf'1: cf'0 = cf'.  
      { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
      clear H_inf. 
      rewrite <- H_cf'0_eq_cf'1 in *. clear cf' H_cf'0_eq_cf'1.
      rename cf'0 into cf'1. (* cf'1 is the tail of the first list *)
      rewrite zlcfm_subst in hall0; auto.
      rewrite zlcfm_subst in hall0; auto.
      clear H_nexP.
      prem2_exe hall0.
      
      * (* second list is NilE *)
        prem0 hall1 h'.
        rewrite zlcfm_subst in h'; auto.
        inversion h' as [H_allP H_nexP]; clear h' H_allP.
        have H_inf: infer prm (mg_spec prm) (lcf2, NilE).
        { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
        have H_lcf2_nil: lcf2 = NilE by eapply zlcfm_infer_nil; eauto.
        clear H_inf. 
        rewrite H_lcf2_nil. clear H_nexP.
        prem1_exe hall1.
        prem0_exe hall2. clear hall3.
        prem1 hall2 h2'. rewrite zlcfm_subst in h2'; auto.
        inversion h2' as [H_allP H_nexP]; clear h2' H_allP.
        have H_inf: infer prm (mg_spec prm) (cf'1, cf').
        { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
        have H_cf'_eq_cf'0: cf' = cf'1. 
        { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
        clear H_nexP H_inf.
        rewrite H_cf'_eq_cf'0.
        apply: conj.
        simpl; auto.  (* is_zlcfm (PPendE (NE z1) cf'1) *)
        (* goal with occ *)
        apply: conj. move=> z.
        have: occ (lcf_seq NilE) z = 0 by simpl; auto.
        move->. rewrite add_zero. auto.
        (* sorted ... *)
        assumption.

      * (* second list is not NilE *)
        prem0 hall1 h1'. rewrite zlcfm_subst in h1'; auto.
        inversion h1' as [H_allP H_nexP]; clear h1' H_allP. 
        have H_inf: infer prm (mg_spec prm) (lcf2, PPendE cf cf').
        { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
        apply zlcfm_infer_pend in H_inf; auto. 2:{ apply cfm_not_in_mg_spec. }
        inversion H_inf as [z2 [H_lcf2_eq_ [H_cf_eq_ H_zlcfm_cf']]];
          clear H_inf.
        subst. clear H_nexP. rename cf' into cf'2. 
        prem1_exe hall1. 
        prem0_exe hall2.
        prem0_exe hall3. clear hall4. 
        prem1 hall3 h'.
        inversion h' as [H_allP H_nexP]; clear h' H_allP.
        have H_inf: infer prm (mg_spec prm) (NE z2, cf'0).
        { apply H_nexP. apply cfm_not_in_mg_spec. simpl. done. }
        have H_cf'0_eq_z2: cf'0 = NE z2.
        { inversion H_inf; subst. inv H3; subst. done. }
        symmetry in H_cf'0_eq_z2. rewrite <- H_cf'0_eq_z2 in *. clear cf'0 H_cf'0_eq_z2.
        clear H_nexP H_inf. 
        rename H20 into H_cfm_ne_z2. clear H_cfm_ne_z2.
        rename H15 into H_cfm_abs. clear H_cfm_abs.
        prem2_exe hall3. clear hall4.
        clear hall3.
        prem1 hall2 h2'. inversion h2' as [H_allP H_nexP]; clear h2'.
        have H_inf: infer prm (mg_spec prm) (cf'2, cf').
        { apply H_nexP. apply cfm_not_in_mg_spec. apply zlcfm_is_cfm=>//. }
        have H_cf'_eq_cf'_2: cf' = cf'2.
        { eapply zlcfm_infer_preserve; eauto. apply cfm_not_in_mg_spec. }
        symmetry in H_cf'_eq_cf'_2. rewrite <- H_cf'_eq_cf'_2 in *.
        clear cf' H_cf'_eq_cf'_2.
        clear H_inf H_allP H_nexP.
        prem2_exe hall2.
        
        (* the true branch for the if expression *)
        prem0_exe hall3.
        prem0_exe hall4. clear hall5. prem1_exe hall4. clear hall5 hall4.
        rename z0 into z1. rename z3 into z2.
        rename H19 into H_inf_tt.
        prem1_exe hall3.
        prem0_exe hall4. clear hall5.
        prem1_spec hall4. fold e_lcase in hspc.
        repeat (try (rewrite zlcfm_subst in hspc;
                     [ | auto; try (rewrite zlcfm_subst; auto)])).
        2: { rewrite zlcfm_subst; auto. } 
        2: { rewrite zlcfm_subst; auto. }
        use_spec hspc.
        {
          eexists.
          apply FUN_SP_e_unfold
          with (lcf1:=cf'1) (lcf2:=PPendE (NE z2) cf'2)
               (zs1:=lcf_seq cf'1) (zs2:=lcf_seq (PPendE (NE z2) cf'2));
            eauto.
          simpl in H_sorted_lcf1.
          apply sorted_tail in H_sorted_lcf1; auto.
        }
        rename H_zlcfm_cf' into H_zlcfm_cf'2. 
        rename H1 into H_zlcfm_cf'.
        inversion H2 as [H_occ H_sorted]; clear H2.
        apply: conj. simpl; auto. (* goal with is_zlcfm *)
        apply: conj. 
        (* goal with occ *)
        move=> z. specialize (H_occ z).
        simpl in H_occ. simpl. rewrite H_occ. 
        case En: (z1 =? z)%Z; case En': (z2 =? z)%Z;
          auto with zarith.
        (* goal with sorted *) 
        simpl.
        have H_cf'_cases: cf' = NilE \/ exists z cf'', cf' = PPendE (NE z) cf''
              by apply zlcfm_shape; auto.
        inversion H_cf'_cases as [H_nil | H_n_nil]; clear H_cf'_cases. 
        rewrite H_nil. simpl. apply singleton_sorted.
        inversion H_n_nil as [z0 [cf'' H_cf'_eq]]; clear H_n_nil.
        have H_corr:
          size (lcf_seq cf'1) > 0 /\
          nth 0%Z (lcf_seq cf') 0 = nth 0%Z (lcf_seq cf'1) 0 \/
          size (lcf_seq (PPendE (NE z2) cf'2)) > 0 /\ 
          nth 0%Z (lcf_seq cf') 0 = nth 0%Z (lcf_seq (PPendE (NE z2) cf'2)) 0.
        {
          apply occ_sorted_hd_corr; auto with zarith.
          rewrite H_cf'_eq. simpl. auto.
        }
        have H_simp: nth 0%Z (lcf_seq cf') 0 = z0 by rewrite H_cf'_eq=>//=. 
        rewrite H_simp in H_corr.
        inversion H_corr as [H_l_first | H_r_first]; clear H_corr.
        (* head ele of new list is head ele of first list *)
        inversion H_l_first as [H_sz_cf'1 H_z0_eq_]; clear H_l_first.
        have H_z1_le_: (z1 <= nth 0%Z (lcf_seq cf'1) 0)%Z.
        { apply sorted_hd_nxt; auto with zarith. }
        rewrite <- H_z0_eq_ in H_z1_le_. rewrite <- H_simp in H_z1_le_.
        have: z1 :: lcf_seq cf' = [:: z1] ++ lcf_seq cf' by auto. move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted. 
        have: size [:: z1] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z1] 0 = z1 by auto. move->.
        auto with zarith.
        (* head ele of new list if head ele of second list *)
        inversion H_r_first as [H_sz_ H_z0_eq_]; clear H_r_first.
        have H_z1_le_: (z1 <= z2)%Z by apply Zle_bool_imp_le; auto.
        simpl in H_z0_eq_. rewrite <- H_z0_eq_ in *.
        have: z1 :: lcf_seq cf' = [:: z1] ++ lcf_seq cf' by auto. move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted.
        have: size [:: z1] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z1] 0 = z1 by auto. move->.
        auto with zarith.

        (* the false branch for the if expression *)
        prem0_exe hall3. 
        prem0_exe hall4. clear hall5. prem1_exe hall4. clear hall5 hall4.
        rename z0 into z1. rename z3 into z2.
        rename H19 into H_inf_ff.
        prem1_exe hall3.
        prem0_exe hall4. clear hall5.
        prem1_spec hall4. fold e_lcase in hspc.
        repeat (try (rewrite zlcfm_subst in hspc;
                     [ | auto; try (rewrite zlcfm_subst; auto)])).
        2: { rewrite zlcfm_subst; auto. } 
        2: { rewrite zlcfm_subst; auto. }
        use_spec hspc.
        {
          eexists.
          eapply FUN_SP_e_unfold
            with (lcf1:=(PPendE (NE z1) cf'1)) (lcf2:=cf'2)
                 (zs1:=lcf_seq (PPendE (NE z1) cf'1)) (zs2:=lcf_seq cf'2);
            eauto.
          simpl in H_sorted_lcf2. 
          apply sorted_tail in H_sorted_lcf2; auto.
        }
        rename H_zlcfm_cf' into H_zlcfm_cf'2.
        rename H1 into H_zlcfm_cf'.
        inversion H2 as [H_occ H_sorted]; clear H2.
        
        apply: conj. simpl; auto. (* goal with is_zlcfm *)
        apply: conj.
        (* goal on occ *)
        move=> z. specialize (H_occ z).
        simpl in H_occ. simpl. rewrite H_occ.
        rewrite [(z2 =? z)%Z + ((z1 =? z)%Z + _ + _)]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + ((z1 =? z)%Z + _))%coq_nat]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + (z1 =? z)%Z)%coq_nat]Nat.add_comm.
        rewrite -[(((z1 =? z)%Z + (z2 =? z)%Z)%coq_nat + _)%coq_nat]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + occ _ z)%coq_nat]Nat.add_comm.
        rewrite [((z1 =? z)%Z + (_ + (z2 =? z)%Z)%coq_nat)%coq_nat]Nat.add_assoc.
        auto with arith.
        (* goal on sortedness *)
        simpl.
        have H_cf'_cases: cf' = NilE \/ exists z cf'', cf' = PPendE (NE z) cf''
              by apply zlcfm_shape; auto.
        inversion H_cf'_cases as [H_nil | H_n_nil]; clear H_cf'_cases.
        rewrite H_nil. simpl. apply singleton_sorted.
        inversion H_n_nil as [z0 [cf'' H_cf'_eq]]; clear H_n_nil.
        have H_corr:
          size (lcf_seq (PPendE (NE z1) cf'1)) > 0 /\
          nth 0%Z (lcf_seq cf') 0 = nth 0%Z (lcf_seq (PPendE (NE z1) cf'1)) 0 \/
          size (lcf_seq cf'2) > 0 /\
          nth 0%Z (lcf_seq cf') 0 = nth 0%Z (lcf_seq cf'2) 0.
        {
          apply occ_sorted_hd_corr; auto with zarith.
          rewrite H_cf'_eq. simpl. auto.
        }
        have H_simp: nth 0%Z (lcf_seq cf') 0 = z0 by rewrite H_cf'_eq=>//=. 
        rewrite H_simp in H_corr.
        inversion H_corr as [H_l_first | H_r_first]; clear H_corr.
        (* head ele of new list is head ele of first list *)
        inversion H_l_first as [H_sz_ H_z0_eq_]; clear H_l_first.
        have H_z2_lt_: (z2 < z1)%Z by apply Z.leb_gt; auto.
        have H_z2_le_: (z2 <= z1)%Z by auto with zarith.
        simpl in H_z0_eq_. symmetry in H_z0_eq_. rewrite <- H_z0_eq_ in *.
        have: z2 :: lcf_seq cf' = [:: z2] ++ lcf_seq cf' by auto. move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted.
        have: size [:: z2] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z2] 0 = z2 by auto. move->.
        auto with zarith.
        (* head ele of new list is head ele of second list *)
        inversion H_r_first as [H_sz_cf'0 H_z0_eq_]; clear H_r_first.
        have H_z2_le_: (z2 <= nth 0%Z (lcf_seq cf'2) 0)%Z.
        { apply sorted_hd_nxt; auto with zarith. }
        rewrite <- H_z0_eq_ in H_z2_le_. rewrite <- H_simp in H_z2_le_.
        have: z2 :: lcf_seq cf' = [:: z2] ++ lcf_seq cf' by auto. move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted. 
        have: size [:: z2] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z2] 0 = z2 by auto. move->.
        auto with zarith.

Qed.       


