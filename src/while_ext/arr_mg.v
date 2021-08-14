
Require Import Coq.Program.Basics. 
Require Import FunctionalExtensionality.
Require Import Classical.
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

From indv Require Import tactics arith lists sem.
From indv.while_ext Require Import lang arr_seq sep st_upd.

(* The array-mering program *)

Definition i_id : var_id := 0.
Definition m_id : var_id := 1.
Definition j_id : var_id := 2.
Definition n_id : var_id := 3.
Definition k_id : var_id := 4.

Definition l_id : var_id := 5.
Definition h_id : var_id := 6. 

Definition S : arr_id := 0.
Definition T : arr_id := 1.
Definition Tmp : arr_id := 2. 

Definition merge : fun_id := 0.
(* Definition msort : fun_id := 1. *)

Definition seq1 :=
  (CmArrAssg T (AVar k_id) (AARef (AArr S) (AVar i_id)));; 
  (CmAssg i_id (AAdd (AVar i_id) (ANum 1))).

Definition seq2 :=
  (CmArrAssg T (AVar k_id) (AARef (AArr S) (AVar j_id)));; 
  (CmAssg j_id (AAdd (AVar j_id) (ANum 1))). 

Definition com_wh :=
  CmWh
    (BAnd (BLe (AVar i_id) (AVar m_id)) (BLe (AVar j_id) (AVar n_id)))
    ( 
      (CmIf
         (BLe (AARef (AArr S) (AVar i_id)) (AARef (AArr S) (AVar j_id)))
         seq1
         seq2);;
      (CmAssg k_id (AAdd (AVar k_id) (ANum 1)))
    ).

Definition com_ab (x1 x2: var_id) := 
  CmWh
    (BLe (AVar x1) (AVar x2))
    (
      (CmArrAssg T (AVar k_id) (AARef (AArr S) (AVar x1)));; 
      (CmAssg x1 (AAdd (AVar x1) (ANum 1)));;
      (CmAssg k_id (AAdd (AVar k_id) (ANum 1))) 
    ).

(* the body of the merge function *)
Definition com_mg : com :=
  CmVarDecl j_id;;
  CmVarDecl k_id;; 
  CmAssg j_id (AAdd (AVar m_id) (ANum 1));;
  CmAssg k_id (AVar i_id);;
  com_wh;;
  (com_ab i_id m_id);;
  (com_ab j_id n_id). 
  
Definition mg_func: func :=
  ([:: (ArrParam S); (ArrParam T); (VarParam i_id); (VarParam m_id); (VarParam n_id)],
   [:: ],
   com_mg). 

Definition mg_prog: prog :=
  (fun fid => if fid == merge then Some mg_func else None).

Definition mg_spec_param : Type := Z.
  
Definition Sx_ge_Tk_1 (x: var_id) (st: state) :=
  exists l1 l2 z1 z2,
    stt_a st S = Some l1 /\ stt_a st T = Some l2 /\
    stt_v st x = Some z1 /\ stt_v st k_id = Some z2 /\
    (stt_l st (l1 + z1) >= stt_l st (l2 + z2 - 1))%Z. 


(* Specification of the array-mering program *) 

Inductive mg_spec (lprm: mg_spec_param):
  Spec mg_spec_param waf_config waf_rconfig lprm :=
  
  WAF_SP_f_mg: 
    forall X1 X2 al am ah m h (st: state),
      stt_a st X1 <> None -> stt_a st X2 <> None -> 
      aval al st = Some lprm -> aval am st = Some m -> aval ah st = Some h ->
      Z.le 0 lprm -> Z.le lprm m -> Z.lt m h ->
      (exists zs, arr_seq X1 lprm m st zs /\ sorted zs) ->
      (exists zs, arr_seq X1 (m+1) h st zs /\ sorted zs) -> 
      sep X1 lprm h X2 lprm h st -> 
      mg_spec
        _
        ((CmCall merge [:: AArr X1; AArr X2; al; am; ah] [:: ]), st, mg_prog)
        (fun r => (exists zs1 zs2,
                      arr_seq X1 lprm h st zs1 /\
                      arr_seq X2 lprm h r zs2 /\
                      occ zs1 = occ zs2 /\ sorted zs2))
        
| WAF_SP_com_wh:
    forall i j k m n (st: state) zs1 zs2 zs3,
      stt_v st i_id = Some i -> stt_v st j_id = Some j ->
      stt_v st k_id = Some k -> k = (i + j - (m + 1))%Z -> 
      stt_v st m_id = Some m -> stt_v st n_id = Some n ->      
      Z.le 0 lprm -> Z.le lprm i -> Z.le i m -> Z.lt m j -> Z.le j n ->
      (Z.ge k (lprm + 1) -> (Sx_ge_Tk_1 i_id st /\ Sx_ge_Tk_1 j_id st)) -> 
      arr_seq S i m st zs1 -> arr_seq S j n st zs2 ->
      arr_seq T lprm (k-1) st zs3 -> 
      sorted zs1 -> sorted zs2 -> sorted zs3 ->
      sep S lprm n T lprm n st -> 
      (* sep S i m T k n st -> sep S j n T k n st ->  *)
      mg_spec
        _
        (com_wh, st, mg_prog)
        (fun r => (
             exists i' j' k',
               stt_v r i_id = Some i' /\ stt_v r j_id = Some j' /\
               stt_v r k_id = Some k' /\ 
               ((Z.le i i' /\ i' = (Z.add m 1) /\ Z.le j j' /\ Z.le j' n) \/ 
                (Z.le j j' /\ j' = (Z.add n 1) /\ Z.le i i' /\ Z.le i' m)) /\
               k' = (k + (i' - i) + (j' - j))%Z /\
               stt_v r m_id = Some m /\ stt_v r n_id = Some n /\
               stt_a r S = stt_a st S /\ stt_a r T = stt_a st T /\
               (exists zs1 zs2 zs3,
                   arr_seq S i (i'-1) st zs1 /\ arr_seq S j (j'-1) st zs2 /\
                   arr_seq T k (k'-1) r zs3 /\
                   (forall z, occ zs1 z + occ zs2 z = occ zs3 z)) /\
               (exists zs, arr_seq T lprm (k'-1) r zs /\ sorted zs) /\
               (exists zs, arr_seq S lprm n st zs /\ arr_seq S lprm n r zs) /\
               (exists zs, arr_seq T lprm (k-1) st zs /\ arr_seq T lprm (k-1) r zs) /\ 
               ((i' <= m /\ k' >= lprm+1)%Z -> Sx_ge_Tk_1 i_id r) /\
               ((j'<=n /\ k'>=lprm+1)%Z -> Sx_ge_Tk_1 j_id r)))
        
| WAF_SP_com_im (st: state):
    forall i j k m n, 
      stt_v st i_id = Some i -> stt_v st j_id = Some j ->
      stt_v st k_id = Some k -> k = (i + j - (m + 1))%Z -> 
      stt_v st m_id = Some m -> stt_v st n_id = Some n ->
      Z.le 0 lprm -> Z.le lprm i -> Z.le i m -> Z.lt m n ->
      j = (n + 1)%Z ->
      sep S lprm n T lprm n st -> 
      (* sep S i m T k n st ->  *)
      mg_spec
        _
        (com_ab i_id m_id, st, mg_prog)
        (fun r => (
             exists i' j' k',
               stt_v r i_id = Some i' /\ stt_v r j_id = Some j' /\
               stt_v r k_id = Some k' /\
               Z.ge i' i /\ (i' = m + 1)%Z /\ j' = j /\ (k' = k + (i' - i))%Z /\
               stt_v r m_id = Some m /\ stt_v r n_id = Some n /\
               stt_a r T = stt_a st T /\
               (exists zs, arr_seq S i (i'-1) st zs /\
                           arr_seq T k (k'-1) r zs) /\
               (exists zs, arr_seq T lprm (k-1) st zs /\
                           arr_seq T lprm (k-1) r zs)))
        
| WAF_SP_com_jn (st: state):
    forall i j k m n,
      stt_v st i_id = Some i -> stt_v st j_id = Some j ->
      stt_v st k_id = Some k -> k = (i + j - (m + 1))%Z -> 
      stt_v st m_id = Some m -> stt_v st n_id = Some n ->
      Z.le 0 lprm -> Z.le lprm m -> Z.lt m j -> Z.le j n ->
      i = (m + 1)%Z -> 
      sep S lprm n T lprm n st -> 
      (* sep S j n T k n st -> *)
      mg_spec
        _
        (com_ab j_id n_id, st, mg_prog)
        (fun r => (
             exists i' j' k',
               stt_v r i_id = Some i' /\ stt_v r j_id = Some j' /\
               stt_v r k_id = Some k' /\ 
               i' = i /\ (Z.ge j' j) /\ (j' = n+1)%Z /\ (k' = k + (j' - j))%Z /\
               stt_v r m_id = Some m /\ stt_v r n_id = Some n /\
               stt_a r T = stt_a st T /\
               (exists zs, arr_seq S j (j'-1) st zs /\
                           arr_seq T k (k'-1) r zs) /\
               (exists zs, arr_seq T lprm (k-1) st zs /\
                           arr_seq T lprm (k-1) r zs))).

Lemma sorted_arr_ele_compare:
  forall X b e st zs l i j,
    arr_seq X b e st zs ->
    sorted zs ->
    (b <= i)%Z ->
    (i <= j)%Z ->
    (j <= e)%Z ->
    stt_a st X = Some l ->
    (stt_l st (l + i) <= stt_l st (l + j))%Z.
Proof.
  move=> X b e st zs l i j.
  move=> H_arrseq H_sorted H_bi H_ij H_je H_l.
  have H_sz: size zs = Z.to_nat (e - b) + 1
    by apply arr_seq_size with (X:=X) (st:=st); auto with zarith.
  have: stt_l st (l+i)%Z = nth (0%Z) zs (Z.to_nat (i-b))
    by apply arr_seq_ele with (X:=X) (e:=e); auto with zarith.
  move->.
  have: stt_l st (l+j)%Z = nth (0%Z) zs (Z.to_nat (j-b))
    by apply arr_seq_ele with (X:=X) (e:=e); auto with zarith.
  move->.
  have: (i < j \/ i = j)%Z by apply Zle_lt_or_eq=>//.
  case=> IEn.
  apply H_sorted; auto with zarith.
  apply /ltP. apply /Z2Nat.inj_lt; auto with zarith.
  apply /ltP.
  apply le_lt_trans with (m:=Z.to_nat (e-b)).
  apply Z2Nat.inj_le; auto with zarith.
  rewrite H_sz. 
  rewrite addn1. apply /ltP. apply ltnSn with (n:=Z.to_nat (e-b)).
  rewrite IEn.
  auto with zarith.
Qed. 
       
Definition stt_cini st vals : state :=
  (call_ini (store_of st)
                [:: ArrParam S; ArrParam T;
                 VarParam i_id; VarParam m_id; VarParam n_id] vals [::],
   floc_of st).

Ltac c_ini_id_corr :=
  move=> st vals; 
  rewrite /stt_cini /stt_v /compose /call_ini /varst_of=>//=.

Lemma stt_cini_i_id:
  forall st vals,
    stt_v (stt_cini st vals) i_id = Some (nth (0%Z) vals 2).
    by c_ini_id_corr. Qed. 

Lemma stt_cini_m_id:
  forall st vals,
    stt_v (stt_cini st vals) m_id = Some (nth (0%Z) vals 3).
    by c_ini_id_corr. Qed.

Lemma stt_cini_n_id:
  forall st vals,
    stt_v (stt_cini st vals) n_id = Some (nth (0%Z) vals 4).
    by c_ini_id_corr. Qed.

Ltac c_ini_arr_corr :=
  move=> st vals; 
  rewrite /stt_cini /stt_a /compose /call_ini /arrst_of=>//=.

Lemma stt_cini_S:
  forall st vals,
    stt_a (stt_cini st vals) S = Some (nth (0%Z) vals 0).
    by c_ini_arr_corr. Qed. 

Lemma stt_cini_T:
  forall st vals,
    stt_a (stt_cini st vals) T = Some (nth (0%Z) vals 1).
    by c_ini_arr_corr. Qed.   

Lemma stt_l_cini:
  forall st vals, stt_l (stt_cini st vals) = stt_l st.
Proof.
  move=> st vals.
  rewrite /stt_l /compose /locst_of /store_of /stt_cini /call_ini=>//=.
Qed.

Lemma stt_l_callfin:
  forall st st' xs xs', 
    stt_l st' = stt_l (call_fin (store_of st) (store_of st') xs xs', floc_of st).
Proof.
  move=> st st' xs xs'.
  rewrite /stt_l /compose /locst_of /store_of.
  rewrite /call_fin /locst_of=>//.
Qed. 

Lemma contra_pos: forall (P Q: Prop), (P -> Q) -> (~Q -> ~P).
    by intuition. Qed. 

Ltac push_eqs :=
  match goal with
    [ H: ?p = ?q |- _ ] => (
      match p with
        Some _ => fail 1
      | size _ => fail 1
      | _ => match q with
               Some _ => fail 1
             | size _ => fail 1
             | _ => move: H
             end
      end)
  end.

Ltac pop_eqs :=
  let heq := fresh "heq" in 
  match goal with
    [ H: _ |- ((_ = _) -> _) ] => intro heq
  | _ => fail 
  end. 
      
Ltac use_spec_protect hyp_spc :=
  let pp := fresh "pp" with hex := fresh "hex"
              in (
                  assert_in_spc hyp_spc;
                  [ |
                    elim=> [pp hex];
                           specialize (hyp_spc pp hex);
                           repeat (try push_eqs);  
                           inversion hex; subst; clear hex;
                           repeat (try pop_eqs) ]). 
            
(* Correctness proof for the array-merging program *) 

Theorem mg_spec_valid: forall prm, valid _ (mg_spec prm).
Proof.
  init_verif. 
  inv H0; subst.
  
  - (* proof for call to "merge" *)
    inv H; subst.
    inv H14; subst. clear H14.
    rename H22 into H_args_eval. 
    inv H20; subst. clear H20.
    fold (stt_cini st vals) in H15.
    prem0_exe H15. clear H15.
    prem0_exe hall. clear hall0. prem1_exe hall. clear hall.
    prem0_exe hall0. clear hall. prem1_exe hall0. clear hall0.
    prem0_exe hall. clear hall0. prem1_exe hall. clear hall.
    prem0_exe hall0. clear hall. prem1_exe hall0. clear hall0.
    updupdsimp_h hall.
    
    have H_prm0: prm = nth (0%Z) vals 2.
    {
      specialize (H_args_eval 2) as H_args_i.
      rem_prem H_args_i. some_eq H3 H_args_i.
    }
    have H_m: m = nth (0%Z) vals 3.
    {
      specialize (H_args_eval 3) as H_args_m.
      rem_prem H_args_m. some_eq H4 H_args_m.
    }
    have H_h: h = nth (0%Z) vals 4.
    {
      specialize (H_args_eval 4) as H_args_h.
      rem_prem H_args_h. some_eq H5 H_args_h.
    }
    have H_mz: (m+1)%Z = z
      by simpl in H21; simpl in H_m; some_eq H_m H21.
    rewrite <- H_mz in *. clear z H_mz.
    have H_z0prm: prm = z0.
    {
      simpl in H24. updsimp_h H24. 
      rewrite stt_cini_i_id in H24. some_eq H_prm0 H24.
    }
    rewrite <- H_z0prm in *. clear z0 H_z0prm.
    have H_X1: stt_a st X1 = Some (nth (0%Z) vals 0).
    {
      specialize (H_args_eval 0) as H_args_S.
      rem_prem H_args_S. rewrite <- H_args_S; auto. 
    }
    have H_X2: stt_a st X2 = Some (nth (0%Z) vals 1).
    {
      specialize (H_args_eval 1) as H_args_T.
      rem_prem H_args_T. rewrite <- H_args_T; auto.
    }

    inversion H9 as [zs1 [H_arrseq_left H_sorted_zs1]].
    inversion H10 as [zs2 [H_arrseq_right H_sorted_zs2]]. 

    (* the first loop in the function body reached by symbolic execution *)
    prem0_spec hall. 
    use_spec_protect hspc.
    {
      eexists;
        eapply WAF_SP_com_wh with (zs1:=zs1) (zs2:=zs2) (zs3:=[::]) (m:=m) (n:=h);
        try updsimp; try auto with zarith.
      rewrite H_prm0. apply stt_cini_i_id.
      auto with zarith.
      rewrite H_m. apply stt_cini_m_id.
      rewrite H_h. apply stt_cini_n_id.
      (* _ -> Sx_ge_Tk_1 ... /\ Sx_ge_Tk_1 ...*)
      intro contra; 
      move: (n_z_ge_z1 prm)=>H_contra; by apply H_contra in contra; inv contra.
      (* arr_seq *)
      apply arr_seq_eq with (b:=prm) (e:=m) (X1:=X1) (X2:=S) (st1:=st).
      do 2! (rewrite st_upd_var_arr). rewrite stt_cini_S. apply: H_X1.
      do 2! (rewrite st_upd_var_loc). rewrite stt_l_cini=>//.
      exact H_arrseq_left.
      apply arr_seq_eq with (e:=h) (X1:=X1) (X2:=S) (st1:=st). 
      do 2! (rewrite st_upd_var_arr). rewrite stt_cini_S. apply: H_X1.
      do 2! (rewrite st_upd_var_loc). rewrite stt_l_cini=>//.
      exact H_arrseq_right.
      have: Z.lt (prm-1)%Z prm by auto with zarith. 
      apply /arr_seq_empty. apply empty_lst_sorted.
      (* goal with sep *)
      apply sep_change_st with (X1:=X1) (X2:=X2) (st:=st)=>//.
    }
    have H_n: n = nth 0%Z vals 4.
    { rename H20 into H_sttv_n_id;
        updsimp_h H_sttv_n_id. some_eq stt_cini_n_id H_sttv_n_id. }
    have H_nh: n = h by congruence.
    rewrite <- H_nh in *; clear h H_nh. clear H_n.
    rename heq1 into H_prm; rename heq2 into H_m; rename heq3 into H_n.
    have H_mm0: m = m0.
    { updsimp_h H19. some_eq H19 stt_cini_m_id. }
    rewrite <- H_mm0 in *. clear m0 H_mm0.
    have H_j_m1: j = (m + 1)%Z.
    { updsimp_h H14. inv H14; auto. }    
    have H_i_prm: prm = i.
    {
      rename H24 into H_stt_v_i_id. simpl in H_stt_v_i_id.
      updsimp_h H_stt_v_i_id.
      rename H13 into H_stt_v_i_id_. simpl in H_stt_v_i_id_.
      updsimp_h H_stt_v_i_id_. some_eq H_stt_v_i_id_ H_stt_v_i_id.
    }
    rewrite <- H_i_prm in *; clear i H_i_prm.
    inversion hspc as [i' [j' [k' H_P_st''_body]]]; clear hspc.
    inversion H_P_st''_body as
        [H_i' [H_j' [H_k' [H_rgn [H_k'_eq [H_m0 [H_n0 [H_S [H_T [H_occ [H_sorted H_body']]]]]]]]]]];
      clear H_P_st''_body. 
    inversion H_body' as [H_S_preserve [H_T_preserve [H_lnext_ge H_rnext_ge]]]; clear H_body'.
    updupdsimp_h H_occ. updupdsimp_h H_S_preserve.
    
    inversion H_rgn as [H_i'_gt_m | H_j'_gt_n].
    +
      inversion H_i'_gt_m as [H_i_le_i' [H_i'_m_1 H_jj']].
      repeat (try push_eqs). prem1_exe hall.
      prem0 hall0 hall00.
      inversion hall00 as [hall00_allP hall00_nexP]; clear hall00 hall00_allP.
      repeat (try pop_eqs). 
      have H_inf: infer prm (mg_spec prm) (com_ab i_id m_id, st'', mg_prog, st''0).
      {
        apply hall00_nexP.
        intro H_exP. inversion H_exP as [P H_mg_spec].
        inversion H_mg_spec; subst.
        rename H44 into H_i0_le_m0. move: H_i0_le_m0.
        have: i = (nth 0 vals 3 + 1)%Z by some_eq H16 H_i'. move->.
        have: m0 = (nth 0 vals 3)%Z by some_eq H40 H_m0. move->.
        auto with zarith.
      }
      repeat (try push_eqs). inversion H_inf; subst. clear H_inf. 
      rename H37 into H_rule_wh2.
      inversion H_rule_wh2; subst; clear H_rule_wh2. 
      * (* cond of second loop evaluates to true -- impossible *)
        rename H37 into H_cond_true. simpl in H_cond_true.
        rewrite H_i' in H_cond_true. rewrite H_m0 in H_cond_true.
        inversion H_cond_true as [contra]. 
        intros. rewrite heq8 in contra.
        rewrite z1_nle_z in contra; inv contra.
      * (* cond of second loop evaluates to false *)
        clear H38.
        have H_prm_lt_j': (prm < j')%Z by auto with zarith.
        prem1_spec hall0. intros. use_spec_protect hspc.
        {          
          eexists; eapply WAF_SP_com_jn with (st:=st''0); eauto;
          auto with zarith.
          updupdsimp_h H_sep_S_T_.
          apply sep_change_st with
              (X1:=S) (X2:=T)
              (st:=(state_upd_var (state_upd_var (stt_cini st vals) j_id (m+1)) k_id prm));
          auto.        
        }
        inversion hspc as [i'' [j'' [k'' H_bd]]]; clear hspc. 
        inversion H_bd as
            [H_i'' [H_j'' [H_k'' [H_i''_i0 [H_j''_j0 [H_j''_n0 [H_k''_k0 H'']]]]]]];
          clear H_bd.
        inversion H'' as [H_st0'_m1 [H_st0'_n0 [H_st0'_st''0_T [H_S_T_rem H_T_preserve']]]];
          clear H''.
        inversion H_S_T_rem as [zs_rem [H_S_zs_rem H_T_zs_rem]]; clear H_S_T_rem.
        inversion H_occ as
            [zs1' [zs2' [zs3' [H_S_zs1' [H_S_zs2' [H_T_zs3' H_occ_pluseq]]]]]];
          clear H_occ.
        have H_m0m: m = m0 by some_eq H_m0 H41.
        rewrite <- H_m0m in *; clear m0 H_m0m.
        have H_n0n: n = n0 by some_eq H_n0 H42.
        rewrite <- H_n0n in *; clear n0 H_n0n.
        have H_j''1_n: (j''-1 = n)%Z.
        {
          rewrite H_j''_n0. rewrite <- Z.add_sub_assoc.
          simpl. rewrite Z.add_0_r=>//.
        }
        have H_j'_eq_j0: j' = j0 by some_eq H_j' H38. 
        rewrite <- H_j'_eq_j0 in *. clear j0 H_j'_eq_j0.
        have H_k'_j': j' = k' by auto with zarith.
        rewrite <- H_k'_j' in *; clear k' H_k'_j'.
        move En_st0:
          (state_upd_var (state_upd_var (stt_cini st vals) j_id (m+1)) k_id prm) => st0.
        symmetry in En_st0; rewrite <- En_st0 in *. rename st''0 into st''.
        have H_S_zs_rem0: arr_seq S j' (j''-1) st0 zs_rem.
        {
          inversion H_S_preserve as [zs00 [H_arrseq_S_st H_arrseq_S_st'']];
            clear H_S_preserve. 
          apply arr_seq_subrgn with (b:=prm) (e:=n) (st1:=st'') (zs:=zs00); 
            auto with zarith.
        }
        move: H_S_zs1'. have: (i' - 1)%Z = m by auto with zarith. move->.
        move=> H_S_zs1'.
        rewrite heq4 in H_S_zs2'. 
        have H_S_left: arr_seq S prm (j'-1) st0 (zs1' ++ zs2')
          by apply arr_seq_concat_general with (e1:=m); auto with zarith.
        have H_S_full: arr_seq S prm (j''-1) st0 ((zs1' ++ zs2') ++ zs_rem).
        {
          apply arr_seq_concat with (e1:=(j'-1)%Z); auto with zarith.
          rewrite Z.sub_add; auto. 
        }
        move: H_T_zs3'. have: (prm + j - (m + 1))%Z = prm by auto with zarith. move->.
        move=> H_T_zs3'.
        inversion H_T_preserve' as [zs0' [H_T_st'' H_T_st0']]; clear H_T_preserve'.
        have H_simp: (m + 1 + j' - (m + 1) - 1)%Z = (j' - 1)%Z
          by auto with zarith.
        rewrite H_simp in H_T_st'' H_T_st0'.
        have H_zs_eq: zs3' = zs0'
          by apply arr_seq_unique with (S:=T) (b:=prm) (e:=(j'-1)%Z) (st:=st'');
          auto.
        rewrite <- H_zs_eq in *; clear zs0' H_zs_eq.
        have H_T_full: arr_seq T prm (k''-1) st0' (zs3' ++ zs_rem).
        {
          have H_simp': (m + 1 + j' - (m + 1))%Z = j' by auto with zarith.
          rewrite H_simp' in H_T_zs_rem.
          apply arr_seq_concat with (e1:=(j'-1)%Z); auto with zarith.
          rewrite Z.sub_add. auto with zarith.
        }
        have H_k''_j'': k'' = j'' by rewrite H_k''_k0; auto with zarith.
        rewrite H_k''_j'' in H_T_full.
        (* preparation for the proof of sortedness *)
        inversion H_sorted as [zs_T1 [H_arrseq_zs_T1 H_sorted_T1]];
          clear H_sorted.
        have H_zs3'_zsT1: zs3' = zs_T1
          by apply arr_seq_unique with (S:=T) (b:=prm) (e:=(j'-1)%Z) (st:=st'');
          auto.
        rewrite <- H_zs3'_zsT1 in *. clear zs_T1 H_zs3'_zsT1.
        rename H31 into H_arrseq_zs3.
        have H_zs_rem_frag: lst_frag (j'-j) zs_rem zs3.
        {
          move: H_S_zs_rem0 => H_S_zs_rem0.
          eapply arr_seq_subrgn_lst_frag
            with (S:=S) (b:=j%Z) (e:=n) (b':=j') (e':=(j''-1)%Z) (st:=st0);
            auto with zarith.
        }
        have H_sorted_zs_rem: sorted zs_rem
          by apply sorted_lst_frag with (b0:=(j'-j)%Z) (zs2:=zs3); auto.

        (* prove the goal *)
        exists ((zs1'++zs2')++zs_rem).
        exists (zs3'++zs_rem).
        rewrite H_j''1_n in H_S_full.
        apply: conj. 
        apply arr_seq_eq with (X1:=S) (X2:=X1) (st1:=st0) (st2:=st); auto.
        rewrite En_st0. repeat (try rewrite st_upd_var_arr). rewrite stt_cini_S; auto.
        rewrite En_st0. repeat (try rewrite st_upd_var_loc). apply stt_l_cini.
        apply: conj.
        rewrite H_j''1_n in H_T_full.
        apply arr_seq_eq with (X1:=T) (X2:=X2) (st1:=st0'); auto.
        rewrite H_st0'_st''0_T. rename heq7 into H_T. rewrite H_T.
        rewrite En_st0. repeat rewrite st_upd_var_arr. rewrite stt_cini_T.
        rewrite /call_fin /varst_of /stt_a /compose /arrst_of /store_of=>/=.
        rewrite /stt_a /compose /arrst_of /store_of in H_X2.
        congruence.
        apply: conj. (* occ *)
        apply functional_extensionality. move=> z'.
        rewrite occ_cat. rewrite [occ (zs3'++zs_rem) z']occ_cat.
        apply /eqP. rewrite eqn_add2r.
        rewrite occ_cat. rewrite H_occ_pluseq=>//.
        (* sorted *)
        move: H_rnext_ge => H_rnext_ge.
        have H_Sx_ge_Tk_1: Sx_ge_Tk_1 j_id st''. 
        { apply H_rnext_ge. apply: conj=>//. auto with zarith. }
        unfold Sx_ge_Tk_1 in H_Sx_ge_Tk_1.
        inversion H_Sx_ge_Tk_1 as
            [l1 [l2 [z1 [z2 [H_S_st''_ [H_T_st''_ [H_z1 [H_z2 H_ge]]]]]]]];
          clear H_Sx_ge_Tk_1.
        have H_z1_zs_rem_0: stt_l st'' (l1 + z1)%Z = nth (0%Z) zs_rem 0.
        {
          have: z1 = j' by some_eq H_z1 H38. move->.
          have: 0 = Z.to_nat (j'-j') by rewrite Z.sub_diag; auto with zarith.
          move->.
          eapply arr_seq_ele with
              (X:=S) (b:=j') (e:=(j''-1)%Z)
              (st:=st'') (zs:=zs_rem) (l:=l1) (z:=j'); auto with zarith.
        }
        have H_z2_z3'_last: stt_l st'' (l2 + z2 - 1)%Z = nth (0%Z) zs3' (size zs3' - 1).
        {
          have H_sz_zs3': size zs3' = Z.to_nat (j' - 1 - prm) + 1
            by apply arr_seq_size with (X:=T) (b:=prm) (e:=(j'-1)%Z) (st:=st'');
            auto with zarith.
          have: size zs3' - 1 = Z.to_nat (j' - 1 - prm).
          {
            rewrite H_sz_zs3'.
            rewrite <- addnBA; auto. rewrite sub_zero. rewrite add_zero. auto.
          }
          move->.
          have: z2 = j' by some_eq H_z2 H39; auto with zarith.
          move->. rewrite <- Z.add_sub_assoc.
          eapply arr_seq_ele with
              (X:=T) (b:=prm) (e:=(j'-1)%Z) (st:=st'') (zs:=zs3') (l:=l2) (z:=(j'-1)%Z);
            auto with zarith.          
        }
        rewrite H_z1_zs_rem_0 H_z2_z3'_last in H_ge.
        apply sorted_concat; auto.
    + 
      inversion H_j'_gt_n as [H_j_le_j' [H_j'_n1 H_ii']].
      repeat (try push_eqs). prem1_exe hall.
      (* 2nd loop in spec *)
      prem0_spec hall0. repeat (try pop_eqs).
      use_spec_protect hspc.
      {
        eexists; eapply WAF_SP_com_im with (st:=st''); eauto;
          auto with zarith.
        apply sep_change_st with
            (X1:=S) (X2:=T)
            (st:=state_upd_var (state_upd_var (stt_cini st vals) j_id (m + 1)) k_id prm);
          auto. 
      }
      have H_nn0: n = n0 by some_eq H_n0 H41. 
      rewrite <- H_nn0 in *. clear n0 H_nn0.
      have H_mm0: m = m0 by some_eq H_m0 H40.
      rewrite <- H_mm0 in *. clear m0 H_mm0.
      rename heq4 into H_j_eq_m_1. symmetry in H_j_eq_m_1.
      rewrite <- H_j_eq_m_1 in *; clear j H_j_eq_m_1.
      rename heq8 into H_j'_eq_n_1. symmetry in H_j'_eq_n_1.
      rewrite <- H_j'_eq_n_1 in *; clear j' H_j'_eq_n_1.
      have H_k'_eq: k' = (i' + n - m)%Z by auto with zarith.

      inversion hspc as [i'' [j'' [k'' H_bd]]]; clear hspc. 
      inversion H_bd as
          [H_i'' [H_j'' [H_k'' [H_i''_i0 [H_i''_m1 [H_j''_j0 [H_k''_k0 H'']]]]]]];
        clear H_bd.
      inversion H'' as [H_st0'_m1 [H_st0'_n0 [H_st''0_st''_T [H_S_T_rem H_T_preserve']]]];
        clear H''.
      inversion H_S_T_rem as [zs_rem [H_S_zs_rem H_T_zs_rem]]; clear H_S_T_rem.
      inversion H_occ as
          [zs1' [zs2' [zs3' [H_S_zs1' [H_S_zs2' [H_T_zs3' H_occ_pluseq]]]]]];
        clear H_occ.        
      move En_st0:
        (state_upd_var (state_upd_var (stt_cini st vals) j_id (m+1)) k_id prm) => st0.
      symmetry in En_st0. rewrite <- En_st0 in *.
      have H_i0_i': i' = i by some_eq H16 H_i'.
      rewrite <- H_i0_i' in *. clear i H_i0_i'.
      have H_i''_sub_1: (i'' - 1)%Z = m by auto with zarith.
      inversion H_S_preserve as [zs0' [H_arrseq_S_st0 H_arrseq_S_st'']];
        clear H_S_preserve.
      have H_S_zs_rem_st0: arr_seq S i' (i''-1) st0 zs_rem.
      {
        apply arr_seq_subrgn with (b:=prm) (e:=n) (st1:=st'') (zs:=zs0');
          auto with zarith.
      }
      have H_S_left: arr_seq S prm (i''-1) st0 (zs1'++zs_rem). 
      {
        apply arr_seq_concat_general with (e1:=(i'-1)%Z); auto with zarith.
        have: (i' - 1 + 1)%Z = i' by auto with zarith.
        move->=>//.
      }
      have H_S_full: arr_seq S prm n st0 ((zs1'++zs_rem)++zs2'). 
      {
        apply arr_seq_concat with (e1:=(i''-1)%Z); auto with zarith.
        rewrite Z.sub_add. rewrite <- Z.add_sub_assoc in H_S_zs2'.
        rewrite Z.sub_diag in H_S_zs2'. rewrite Z.add_0_r in H_S_zs2'.
        congruence.
      }
      move: H_T_zs3'.
      have: (prm + (m + 1) - (m + 1))%Z = prm by auto with zarith. move->.
      move=> H_T_zs3'.
      have H_arrseq_T0: arr_seq T prm (i' + n - m - 1) st''0 zs3'.
      {
        inversion H_T_preserve' as [zs0'' [H_T_st'' H_T_st''0]]; clear H_T_preserve'.
        have H_simp: (i' + (n + 1) - (m + 1) - 1)%Z = (i' + n - m - 1)%Z by
            auto with zarith.
        rewrite H_simp in H_T_st'' H_T_st''0. rewrite H_k'_eq in H_T_zs3'.
        apply arr_seq_subrgn with (b:=prm) (e:=(i'+n-m-1)%Z) (st1:=st'') (zs:=zs0'');
          auto with zarith.
      }
      have H_T_full: arr_seq T prm (k''-1) st''0 (zs3'++zs_rem).
      {
        have H_simp: (i' + (n + 1) - (m + 1))%Z = ((i' + n - m - 1) + 1)%Z
          by auto with zarith.
        rewrite H_simp in H_T_zs_rem.
        apply arr_seq_concat with (e1:=(i'+n-m-1)%Z); auto with zarith.
      }
      have H_simp: (k'' - 1)%Z = n by rewrite H_k''_k0; auto with zarith.
      rewrite H_simp in H_T_full.
      
      (* preparation of proof for sortedness *)
      inversion H_sorted as [zs00 [H_arrseq_T_st''_zs00 H_sorted_zs00]];
        clear H_sorted.
      have H_zs00_zs3': zs00 = zs3'
        by apply arr_seq_unique with (S:=T) (b:=prm) (e:=(k'-1)%Z) (st:=st'');
        auto with zarith.
      rewrite H_zs00_zs3' in H_sorted_zs00. 
      have H_lst_frag: lst_frag (i'-prm) zs_rem zs0.
      {
        apply arr_seq_subrgn_lst_frag with
            (S:=S) (b:=prm) (e:=m) (b':=i') (e':=(i''-1)%Z) (st:=st0);
          auto with zarith.
      }
      have H_sorted_zs_rem: sorted zs_rem
        by apply sorted_lst_frag with (b0:=(i'-prm)%Z) (zs2:=zs0);
        auto with zarith.

      move: H_lnext_ge=> H_lnext_ge.
      have H_Sx_ge_Tk_1: Sx_ge_Tk_1 i_id st''. 
      { apply H_lnext_ge. apply: conj=>//. auto with zarith. }
      unfold Sx_ge_Tk_1 in H_Sx_ge_Tk_1.
      inversion H_Sx_ge_Tk_1 as
          [l1 [l2 [z1 [z2 [H_l1 [H_l2 [H_z1 [H_z2 H_ge]]]]]]]];
        clear H_Sx_ge_Tk_1.
      have H_z1_zs_rem_0: stt_l st'' (l1 + z1)%Z = nth (0%Z) zs_rem 0.
      {
        have: 0 = Z.to_nat (i'-i') by rewrite Z.sub_diag; auto with zarith.
        move->.
        have: z1 = i' by some_eq H_z1 H16. move->.
        eapply arr_seq_ele with
            (X:=S) (b:=i') (e:=(i''-1)%Z) (st:=st'') (zs:=zs_rem) (l:=l1) (z:=i');
          auto with zarith. 
      }
      have H_z2_z3'_last: stt_l st'' (l2 + z2 - 1)%Z = nth (0%Z) zs3' (size zs3' - 1).
      {
        have: size zs3' = Z.to_nat (k' - 1 - prm) + 1
          by apply arr_seq_size with (X:=T) (b:=prm) (e:=(k'-1)%Z) (st:=st'');
          auto with zarith.
        move->.
        rewrite <-addnBA; auto. rewrite sub_zero. rewrite add_zero.
        have: z2 = (i' + n - m)%Z by some_eq H_z2 H38; auto with zarith.
        move->.
        rewrite <- Z.add_sub_assoc.
        rewrite -H_k'_eq. 
        eapply arr_seq_ele with
            (X:=T) (b:=prm) (e:=(k'-1)%Z) (st:=st'') (zs:=zs3')
            (l:=l2) (z:=(k'-1)%Z);
          auto with zarith.
      }
      rewrite H_z1_zs_rem_0 H_z2_z3'_last in H_ge.
      have H_sorted_zs3'_zs_rem: sorted (zs3'++zs_rem). 
      { apply sorted_concat; auto. }

      (* 3rd loop *)
      symmetry in H_zs00_zs3'; rewrite <- H_zs00_zs3' in *; clear H_zs00_zs3'.
      repeat (try push_eqs).
      prem1 hall0 hall01. 
      inversion hall01 as [H_allP H_nexP]; clear hall01 H_allP.
      repeat (try pop_eqs).
      have H_inf: infer prm (mg_spec prm) (com_ab j_id n_id, st''0, mg_prog, st0').
      {
        apply H_nexP. 
        intro contra. inversion contra as [P H_mg_spec]; clear contra.
        inversion H_mg_spec; subst.
        rename H55 into H_j_le_n0. move: H_j_le_n0.
        rewrite H_j'' in H46. inversion H46.
        rewrite H_st0'_n0 in H51. inversion H51. auto with zarith.
      }
      repeat (try push_eqs).
      inversion H_inf; subst.
      rename H46 into H_rule_wh3. inversion H_rule_wh3; subst.
      * (* cond eval to true *)
        rename H46 into H_cond_true. simpl in H_cond_true.
        rewrite H_j'' in H_cond_true.
        rewrite H_st0'_n0 in H_cond_true.
        repeat (try pop_eqs). rewrite heq9 in H_cond_true.
        inversion H_cond_true. rewrite z1_nle_z in H39.
        inv H39.
      * (* cond eval to false *) (* prove the goal *)
        repeat (try pop_eqs).
        rename heq12 into En_st0.
        move: H_S_full H_T_full H_sorted_zs3'_zs_rem=>
        H_S_full H_T_full H_sorted_zs3'_zs_rem.
        have H_n_h: (k''-1)%Z = n by auto with zarith. 
        rewrite <- H_n_h in *. 
        exists ((zs1' ++ zs_rem) ++ zs2'). exists (zs3' ++ zs_rem).
        apply: conj.
        apply arr_seq_eq with (X1:=S) (st1:=st0); auto.
        rewrite En_st0. repeat (try rewrite st_upd_var_arr). rewrite stt_cini_S; auto. 
        rewrite En_st0. repeat (try rewrite st_upd_var_loc). apply stt_l_cini.
        apply: conj.
        apply arr_seq_eq with (X1:=T) (st1:=st0'); auto.
        rename heq11 into H_st0'_T_st''_T. rewrite H_st0'_T_st''_T.
        rename heq6 into H_st''_T_st0_T. rewrite H_st''_T_st0_T.
        rewrite En_st0. repeat rewrite st_upd_var_arr.
        rewrite stt_cini_T. rewrite -H_X2.
        rewrite /call_fin /store_of /varst_of. simpl. 
        rewrite /arrst_of /store_of /locst_of. 
        rewrite /stt_a /compose /store_of /arrst_of. simpl. auto.
        apply: conj.
        apply functional_extensionality. move=> z'.
        repeat rewrite occ_cat.
        rewrite <- Nat.add_assoc.
        rewrite [(occ zs_rem z' + occ zs2' z')%coq_nat] Nat.add_comm.
        rewrite Nat.add_assoc.
        rewrite [(occ zs1' z' + occ zs2' z')%coq_nat]H_occ_pluseq.
        auto.
        (* sorted *)
        auto.

  -  (* proof for first loop *)
    inv H; subst. clear H0.
    rename H21 into H_rule_wh. inv H_rule_wh; subst; clear H_rule_wh.
    (* refute exiting the loop *) 
    2: {
      rename H20 into Hcond. simpl in Hcond.
      rewrite H1 in Hcond. rewrite H5 in Hcond.
      rewrite H2 in Hcond. rewrite H6 in Hcond.
      apply Zle_imp_le_bool in H9. apply Zle_imp_le_bool in H11.
      rewrite H9 H11 in Hcond. simpl in Hcond. inv Hcond.
    }
    rename H22 into Hforall.
    prem0_exe Hforall. prem0_exe hall.
    + (* cond of if evaluated to true *)
      assert (Hcond0 := H21). rename H21 into Hcond. simpl in Hcond.
      case EnS: (stt_a st S)=> [lS | ]; rewrite EnS in Hcond; [ | inv Hcond ].
      rewrite H1 in Hcond. 
      case H_ige0: (i >=? 0)%Z; rewrite H_ige0 in Hcond;
        [ | simpl in Hcond; inv Hcond ].
      case H_lSi: (lS + i <? floc_of st)%Z;
        rewrite H_lSi in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      rewrite H2 in Hcond.
      case H_jge0: (j >=? 0)%Z; rewrite H_jge0 in Hcond;
        [ | simpl in Hcond; inv Hcond ]. 
      case H_lSj: (lS + j <? floc_of st)%Z; 
        rewrite H_lSj in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond. 
      case H_lSij: (stt_l st (lS + i) <=? stt_l st (lS + j))%Z; 
        rewrite H_lSij in Hcond; [ | simpl in Hcond; inv Hcond ].
      clear Hcond.
      (* execute first round of the loop *)
      prem0_exe hall0.
      prem0_exe hall1. clear hall2. prem1_exe hall1. clear hall2 hall1.
      prem1_exe hall. clear hall1 hall hall0.
      (* re-visiting the loop after executing its body *) 
      move En_st'':
        (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) i_id z) k_id z0)
      => st''.
      symmetry in En_st''; rewrite <- En_st'' in *.
      rewrite -/com_wh in Hforall.
      have H_z1: z1 = (i + j - (m+1))%Z.
      { 
        rename H27 into H_k_id_eval. simpl in H_k_id_eval. some_eq H_k_id_eval H3.
      }
      have H_z2: z2 = stt_l st (lS + i)%Z.
      {
        rename H28 into H_S_i_eval. simpl in H_S_i_eval.
        rewrite EnS in H_S_i_eval. rewrite H1 in H_S_i_eval.
        rewrite H_ige0 in H_S_i_eval. rewrite H_lSi in H_S_i_eval.
        simpl in H_S_i_eval; inv H_S_i_eval; auto.
      }
      have H_arrseq_S_im_st'': arr_seq S i m st'' zs1.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto. 
        rewrite En_st''. repeat (try rewrite st_upd_var_arr).
        rewrite st_upd_loc_arr=>//.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        move=> z3 H_i_le_z3 H_z3_le_m.
        rewrite <- st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n); 
          auto with zarith.
      }
      have H_exzs_Si1_m_st'': exists zs1', arr_seq S (i + 1) m st'' zs1'.
      {
        apply arr_seq_ex with (l:=lS); auto with zarith. rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr.
        auto.
      }
      inversion H_exzs_Si1_m_st'' as [zs1' H_arrseq_S_i1m_st''];
        clear H_exzs_Si1_m_st''.
      have H_st''_i: stt_v st'' i_id = Some (i + 1)%Z.
      {
        rewrite En_st''. updsimp. 
        rename H31 into H_eval_i_1_. simpl in H_eval_i_1_.
        rewrite st_upd_loc_var in H_eval_i_1_.
        rewrite H1 in H_eval_i_1_; inv H_eval_i_1_; auto.
      }
      have H_st''_j: stt_v st'' j_id = Some j 
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_k: stt_v st'' k_id = Some (i + j - m)%Z.
      {
        rename H33 into H_eval_k_.
        simpl in H_eval_k_. updsimp_h H_eval_k_.
        rewrite st_upd_loc_var in H_eval_k_.
        rewrite H3 in H_eval_k_.
        rewrite En_st''. updsimp.
        rewrite <- H_eval_k_.
        congr Some. auto with zarith.
      }
      have H_st''_m: stt_v st'' m_id = Some m
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_n: stt_v st'' n_id = Some n
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_S: stt_a st'' S = Some lS.
      {
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr=>//.
      }
      have H_st''_T: stt_a st'' T = Some l.
      {
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr=>//.
      }
      have H_stt_l_st''_ijm: stt_l st'' (l + (i+j-(m+1)))%Z = stt_l st (lS + i)%Z.
      {
        rewrite -H_z1. rewrite {1}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2=>//.
      }
      have H_arrseq_st''_zs3: arr_seq T prm (i + j - (m + 1) - 1) st'' zs3.
      {
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with zarith.
        some_eq H_st''_T H25.
        move=> z3 H_prm0_le_z3 H_z3_le_ijm.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
      }
      have H_arr_seq_T_st''_ext: 
        arr_seq T prm (i+j-m-1) st'' (zs3 ++ [:: (stt_l st'' (l+i+j-(m+1))%Z)]).
      {
        have: (i + j - m - 1)%Z = (i + j - (m + 1) - 1 + 1)%Z by auto with zarith.
        move->.
        apply arr_seq_concat_general with (e1:=(i + j - (m + 1) - 1)%Z);
          auto with zarith.
        have: (i+j-(m+1)-1+1)%Z = (i + j - (m+1))%Z by auto with zarith. move->. 
        have: (l+i+j-(m+1))%Z = (l+ (i+j-(m+1)))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
      }      
      have H_sorted_z3_ext: sorted (zs3 ++ [:: stt_l st'' (l+i+j-(m+1))%Z]).
      {
        have H_prm0_rgn: (prm <= i + j - (m + 1))%Z by auto with zarith.
        have H_prm0_cases: (prm < i+j-(m+1))%Z \/ (prm = i+j-(m+1))%Z 
          by apply Zle_lt_or_eq=>//.
        inversion H_prm0_cases as [H_prm0_lt | H_prm0_eq].
        (* first case *)
        apply sorted_concat; auto with zarith.
        apply singleton_sorted. simpl.
        have: size zs3 = Z.to_nat ((i + j - (m + 1) - 1) - prm) + 1
          by apply arr_seq_size with (X:=T) (st:=st); auto with zarith.
        move->.
        have H_gt: (i + j - (m + 1) >= prm + 1)%Z by auto with zarith.
        rename H12 into H_Sx_ge_Tk_1_orig. 
        specialize (H_Sx_ge_Tk_1_orig H_gt).
        inversion H_Sx_ge_Tk_1_orig as [H_Sx_ge_left H_Sx_ge_right];
          clear H_Sx_ge_Tk_1_orig.
        rewrite /Sx_ge_Tk_1 in H_Sx_ge_left.
        have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite H_stt_l_st''_ijm.
        inversion H_Sx_ge_left as
            [l1' [l2' [z1' [z2' [H_l1' [H_l2' [H_z1' [H_z2' H_ge]]]]]]]].
        move: H_ge. have: l1' = lS by some_eq H_l1' EnS. move->.
        have: z1' = i by some_eq H_z1' H1. move->.
        have: l2' = l by some_eq H_l2' H25. move->.
        have: z2' = (i + j - (m + 1))%Z by some_eq H_z2' H3. move->.
        have: stt_l st (l + (i + j - (m + 1)) - 1)%Z =
              nth (0%Z) zs3 (Z.to_nat (i + j - (m + 1) - 1 - prm)).
        { rewrite -Z.add_sub_assoc.
          apply arr_seq_ele with
              (X:=T) (b:=prm) (e:=(i + j - (m + 1) - 1)%Z) (st:=st) (zs:=zs3)
              (l:=l) (z:=((i + j - (m + 1)) - 1)%Z); auto with zarith. }
        move->. rewrite -addnBA; auto. rewrite sub_zero. rewrite add_zero=>//.
        (* second case *)
        have: zs3 = [:: ] 
          by apply arr_seq_empty' with
            (X:=T) (b:=prm) (e:=(i + j - (m + 1) - 1)%Z) (st:=st);
          auto with zarith.
        move->=>/=. 
        apply singleton_sorted; auto.
      }
      have H_arrseq_Sjn_st'': arr_seq S j n st'' zs2.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto.
        some_eq EnS H_st''_S.
        move=> z3 H_j_le_z3 H_z3_le_n.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite <- st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n);
          auto with zarith.
      }
      
      have H_exP_cond:
        (i+1 <= m)%Z <-> (exists P, mg_spec prm (com_wh, st'', mg_prog) P).
      {
        apply: conj.
        - move=> H_i1_le_m.
          have H_lstfrag: lst_frag ((i+1)-i) zs1' zs1
            by apply arr_seq_subrgn_lst_frag with
              (S:=S) (b:=i) (e:=m) (b':=(i+1)%Z) (e':=m) (st:=st'');
            auto with zarith.
          eexists. 
          eapply WAF_SP_com_wh with
              (lprm:=prm) (i:=(i+1)%Z) (j:=j) (k:=(i+j-m)%Z) (m:=m) (n:=n) (st:=st'')
              (zs1:=zs1') (zs2:=zs2) (zs3:=zs3++[:: (stt_l st'' (l+i+j-(m+1))%Z)]);
            auto with zarith.
          (* goal with Sx_ge_Tk_1 *)
          have H_Sx_ge_Tk_1:
            (i + j - m >= prm + 1)%Z -> Sx_ge_Tk_1 i_id st'' /\ Sx_ge_Tk_1 j_id st''.
          {
            move=> H_k_ge. rewrite /Sx_ge_Tk_1. 
            apply: conj.
            exists lS. exists l. exists (i+1)%Z. exists (i+j-m)%Z.
            repeat (try apply: conj=>//).
            have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
              by auto with zarith. move->.
            rewrite H_stt_l_st''_ijm. 
            have: stt_l st (lS + (i + 1))%Z = stt_l st'' (lS + (i + 1))%Z.
            {
              rewrite En_st''. repeat (try rewrite st_upd_var_loc).
              apply st_upd_loc_sep with
                  (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
                  (l1:=lS) (l2:=l) (z1:=(i+1)%Z) (z2:=z1) (z:=z2);
                auto with zarith.          
            }
            move<-. apply Z.le_ge.
            apply sorted_arr_ele_compare with (X:=S) (b:=i) (e:=m) (zs:=zs1);
              auto with zarith.
            
            exists lS. exists l. exists j. exists (i+j-m)%Z.
            repeat (try apply: conj=>//).
            have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
              by auto with zarith. move->.
            rewrite - H_z1. rewrite {2}En_st''.
            repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
            rewrite H_z2.
            have: stt_l st (lS + j)%Z = stt_l st'' (lS + j)%Z.
            {
              rewrite En_st''. repeat (try rewrite st_upd_var_loc).
              apply st_upd_loc_sep with
                  (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
                  (l1:=lS) (l2:=l) (z1:=j) (z2:=z1) (z:=z2); auto with zarith. 
            }
            move<-. apply Z.le_ge. apply Zle_bool_imp_le=>//.
          }
          apply H_Sx_ge_Tk_1.
          apply sorted_lst_frag with (b0:=(i + 1 - i)%Z) (zs2:=zs1); auto.
          apply sep_change_st with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st);
            auto with arith.
          some_eq H_st''_S EnS.
          some_eq H_st''_T H25.
          
        - elim=> [P H_spc_P]. inversion H_spc_P; subst.
          updsimp_h H4. updsimp_h H_st''_i.
          have: (i + 1)%Z = i0 by some_eq H4 H_st''_i. move->.
          updsimp_h H32. rewrite st_upd_loc_var in H32.
          have: m = m0 by some_eq H32 H5. move->=>//.
      }

      prem1 Hforall H_wh_spc_exe.
      inversion H_wh_spc_exe as [H_allP H_nexP]; clear H_wh_spc_exe.
      have: (~(i+1 <= m)%Z) \/ (i+1 <= m)%Z by apply /or_comm; apply classic.
      elim. 
      * (* remaining loop is not in spec *)
        move=> H_n_i_le. assert (H_i_rgn := H_n_i_le).
        move: H_n_i_le. move /H_exP_cond. move /H_nexP=> H_inf_wh.
        repeat (try push_eqs). inversion H_inf_wh; subst.
        rename H21 into H_rule_wh'. inversion H_rule_wh'; clear H_rule_wh'.
        (* the impossible case -- true *)
        clear H26. repeat (try pop_eqs).
        rename H21 into H_cond_eval_tt. simpl in H_cond_eval_tt.
        rewrite H_st''_i in H_cond_eval_tt. rewrite H_st''_m in H_cond_eval_tt.
        rewrite H_st''_j in H_cond_eval_tt. rewrite H_st''_n in H_cond_eval_tt.
        inversion H_cond_eval_tt as [H_cond_true]. 
        have contra: (i + 1 <=? m)%Z = true.
        { case En':(i + 1 <=? m)%Z=>//.
          rewrite En' in H_cond_true; inv H_cond_true. }
        apply Z.leb_nle in H_i_rgn. rewrite contra in H_i_rgn. inv H_i_rgn.
        (* the actual case -- false *) 
        rename H32 into H_st0st''. (* no need for rewriting *) clear st0 H_st0st''.
        rename H35 into H_st''r. rewrite <- H_st''r in *. clear r H_st''r.
        rename H21 into H_cond_eval_ff. 
        repeat (try pop_eqs).
        
        exists (i+1)%Z. exists j. exists (i + j - m)%Z.
        apply: conj; [auto | ]. apply: conj; [auto | ]. apply: conj; [auto | ].
        apply: conj. left. auto with zarith. 
        apply: conj. auto with zarith.
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj. some_eq H_st''_T H25. 
        apply: conj.
        exists [:: stt_l st (lS+i)%Z]. exists [:: ]. exists [:: stt_l st (lS+i)%Z].
        apply: conj.
        have: (i + 1 - 1)%Z = i by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        apply: conj.
        apply arr_seq_empty; auto with zarith.
        apply: conj. 
        rename heq7 into H_stt_l_st''_ijm. rewrite - H_stt_l_st''_ijm.
        have: (i + j - m - 1)%Z = (i + j - (m + 1))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        move=> z3. simpl. repeat rewrite add_zero=>//.  
        apply: conj.
        (*  exists zs, arr_seq T param0 (i + j - m - 1) st'' zs /\ sorted zs *)
        exists (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
        apply: conj.
        apply H_arr_seq_T_st''_ext. apply H_sorted_z3_ext.
        apply: conj.
        (* (exists zs, arr_seq S param0 n st zs /\ arr_seq S param0 n st'' zs) *)
        have H_ex_zs_arrseq: exists zs, arr_seq S prm n st zs
            by apply arr_seq_ex with (l:=lS); auto with zarith.
        inversion H_ex_zs_arrseq as [zs' H_arrseq_S_zs']; clear H_ex_zs_arrseq.
        exists zs'.
        apply: conj. auto.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_prm0z3 H_z3n.
        rename heq4 into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep
          with (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n)
               (st:=st) (l1:=lS) (l2:=l) (z1:=z3) (z2:=z1) (z:=z2);
          auto with zarith. 

        apply: conj. (* preservation of initial fragment of T *)
        have H_ex_zs_arrseq_T_st_zs: exists zs, arr_seq T prm (i+j-(m+1)-1) st zs
            by apply arr_seq_ex with (l:=l); auto with zarith.
        inversion H_ex_zs_arrseq_T_st_zs as [zs_T H_arrseq_T_zs_T];
          clear H_ex_zs_arrseq_T_st_zs.
        exists zs_T.
        apply: conj. auto. 
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with arith.
        some_eq H25 H_st''_T.
        move=> z3 H_prm0_z3 H_z3_ijm.
        rename heq4 into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
        rewrite st_upd_neq_loc; auto.
        rename heq5 into H_z1. rewrite H_z1. auto with zarith.
        
        apply: conj. (* goal with Sx_ge_Tk_1 *)
        move=> H_ijm_rgn_contra.
        inversion H_ijm_rgn_contra as [H_i1_le_m H_ijm_ge_];
          clear H_ijm_rgn_contra.
        apply H_i_rgn in H_i1_le_m. inv H_i1_le_m.

        move=> H_jim_rgn.
        inversion H_jim_rgn as [H_j_le_n H_ijm_ge_]; clear H_jim_rgn.
        rewrite /Sx_ge_Tk_1.
        exists lS. exists l. exists j. exists (i+j-m)%Z.
        repeat (try apply: conj=>//).
        have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite -heq5. rename heq4 into En_st''. rewrite {2}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite heq6.
        have: stt_l st (lS + j)%Z = stt_l st'' (lS + j)%Z.
        {
          rewrite En_st''. repeat (try rewrite st_upd_var_loc).
          apply st_upd_loc_sep with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
              (l1:=lS) (l2:=l) (z1:=j) (z2:=z1) (z:=z2); auto with zarith. 
        }
        move<-. apply Z.le_ge. apply Zle_bool_imp_le=>//.
        
      * (* remaining loop is in spec *) 
        move=> H_i_le. assert (H_i_rgn := H_i_le).
        move: H_i_le. move /H_exP_cond. 
        elim=> [P H_P_spc].
        specialize (H_allP P H_P_spc). move: H_allP=> H_P_r.
        inversion H_P_spc. rename H48 into H_fun_r_eq_P.
        rewrite <- H_fun_r_eq_P in H_P_r. clear H_fun_r_eq_P.
        
        rename H0 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
        have H_ii0: (i+1)%Z = i0 by some_eq  H_st''_i H4.
        have H_jj0: j = j0 by some_eq H_st''_j H21.
        have H_ijm_k: (i + j - m)%Z = k by some_eq H_st''_k H24.
        have H_mm0: m = m0 by some_eq H_st''_m H32.
        have H_nn0: n = n0 by some_eq H_st''_n H34.
        rewrite <- H_ii0 in *. clear i0 H_ii0.
        rewrite <- H_jj0 in *. clear j0 H_jj0.
        rewrite <- H_mm0 in *. clear m0 H_mm0.
        rewrite <- H_nn0 in *. clear n0 H_nn0.
        have H_zs0_: zs1' = zs0
          by apply arr_seq_unique with
            (S:=S) (b:=(i+1)%Z) (e:=m) (st:=st''); auto with zarith.
        rewrite <- H_zs0_ in *. clear zs0 H_zs0_.
        rename H44 into H_sorted_zs1'.
        rename H41 into H_arrseq_S_st''; clear H_arrseq_S_st''.
        rename H42 into H_arrseq_S_st''_zs4. rename H45 into H_sorted_zs4.
        clear zs4 H_arrseq_S_st''_zs4 H_sorted_zs4.
        rename H43 into H_arrseq_T_st''_zs5. rename H46 into H_sorted_zs5.
        clear zs5 H_arrseq_T_st''_zs5 H_sorted_zs5.

        inversion H_P_r as
            [i' [j' [k' [H_i'0 [H_j' [H_k' [H_ijkm_or [H_k'_ [H_m_ [H_n_ [H_S_ [H_T_ H'']]]]]]]]]]]]; clear H_P_r.
        inversion H'' as
            [H_occ' [H_sorted' [H_S_preserve' [H_T_preserve' [H_Sx_ge_Tk_1_i' H_Sx_ge_Tk_1_j']]]]]; clear H''.
        exists i'. exists j'. exists k'.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj.
        inv H_ijkm_or; [left | right]; auto with zarith.
        apply: conj.
        auto with zarith. (* k' = (i + j - (m + 1) + (i'0 - i) + (j' - j))%Z *)
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by rewrite H_st''_S in H_S_; inv H_S_; auto.
        apply: conj. 
        { rewrite H_st''_T in H_T_. rewrite <- H25 in H_T_. inv H_T_; auto. }
        apply: conj. (* goal with occ *)
        inversion H_occ' as
            [zs10 [zs20 [zs30 [H_zs10 [H_zs20 [H_zs30 H_all]]]]]]; clear H_occ'.
        exists ((stt_l st (lS+i)%Z) :: zs10). 
        exists zs20.
        exists ((stt_l st (lS+i)%Z) :: zs30).
        have H_arrseq_S_i_1_st: arr_seq S (i + 1) (i' - 1) st zs10.
        {
          apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
            auto with zarith.
          rewrite En_st''. repeat rewrite st_upd_var_arr.
          rewrite st_upd_loc_arr=>//.
          move=> z3 H_iz3 H_z3i0.
          rewrite En_st''. repeat rewrite st_upd_var_loc.
          symmetry.
          apply st_upd_loc_sep with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T)
              (b2:=prm) (e2:=n) (l2:=l) (z2:=z1) (z:=z2);
            auto with zarith.
        }
        apply: conj.
        have: stt_l st (lS + i)%Z :: zs10 = [:: stt_l st (lS + i)%Z] ++ zs10
          by simpl; auto. move->.
        apply arr_seq_concat_general with (e1:=i); auto with zarith.
        by apply arr_seq_singleton; auto with zarith.
        apply: conj.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
          auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_jz3 H_z3j'_1. rewrite En_st''. repeat rewrite st_upd_var_loc.
        symmetry.
        by apply st_upd_loc_sep with (X1:=S) (b1:=prm) (e1:=n)
                                     (X2:=T) (b2:=prm) (e2:=n); auto with zarith.
        apply: conj.
        have: (i + j - (m+1))%Z = (k - 1)%Z by auto with zarith. move->.
        have: stt_l st (lS + i)%Z :: zs30 = [:: stt_l st (lS + i)%Z] ++ zs30
          by auto. move->.
        apply arr_seq_concat with (e1:=(k-1)%Z); auto with zarith.
        inversion H_S_preserve' as
            [zs [H_arrseq_S_st'' H_arrseq_S_r]]; clear H_S_preserve'.
        rewrite <- H_stt_l_st''_ijm.
        have: (l + (i + j - (m + 1)))%Z = (k - 1 + l)%Z by auto with zarith. move->.
        have: stt_l st'' (l + (k-1))%Z = stt_l r (l + (k-1))%Z.
        {
          inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]]. 
          apply arr_seq_ele_eq with (X:=T) (b:=prm) (e:=(k-1)%Z) (zs:=zs_T);
            auto with zarith.
          congruence.
        }
        have: (k - 1 + l)%Z = (l + (k - 1))%Z by auto with zarith. move->. move->.
        apply arr_seq_singleton; auto with zarith.
        congruence.
        have: (k - 1 + 1)%Z = k by auto with zarith. move->.
        auto.        
        move=> z3.
        have: stt_l st (lS + i)%Z :: zs10 = [:: stt_l st (lS+i)%Z] ++ zs10
          by simpl; auto. move->.
        have: stt_l st (lS + i)%Z :: zs30 = [:: stt_l st (lS+i)%Z] ++ zs30
          by simpl; auto. move->.
        do 2! (rewrite occ_cat).  
        rewrite <- Nat.add_assoc.
        rewrite [(occ zs10 z3 + occ zs20 z3)%coq_nat]H_all.
        by auto.

        apply: conj. (* initial fragment of T sorted *) assumption.
        apply: conj.
        (* preservation of content of S *)
        inversion H_S_preserve' as [zs_S [H_arrseq_S_st'' H_arrseq_S_r]].
        exists zs_S. apply: conj; [ | auto].
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence. 
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
        apply st_upd_loc_sep with (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n);
          auto with zarith.
        apply: conj.
        (* preservation of content of initial fragment of T *)
        have H_ijm_rgn: (0 <= i + j - (m + 1))%Z by auto with zarith.
        have: (0 < i + j - (m + 1))%Z \/ (0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq; auto.
        case=> H_cs.
        (* first case *)
        inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]].
        have H_ex_T': exists zs_T', arr_seq T prm (i+j-(m+1)-1) r zs_T'.
        { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
        inversion H_ex_T' as [zs_T' H_arrseq_T_zs_T']; clear H_ex_T'.
        have H_arrseq_T_st''_zs_T': arr_seq T prm (i+j-(m+1)-1) st'' zs_T'
          by apply arr_seq_subrgn with (b:=prm) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
          auto with zarith.
        have H_arrseq_T_st_zs_T': arr_seq T prm (i+j-(m+1)-1) st zs_T'.
        {
          apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
          congruence.
          move=> z3 H_prm0_z3 H_z3_ijm.
          rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
          rewrite st_upd_neq_loc; auto.
          rewrite H_z1. auto with zarith.
        }
        exists zs_T'. apply: conj; auto.
        (* second case *)
        rewrite <- H_cs. simpl.
        exists [:: ].
        apply: conj; apply arr_seq_empty; auto with zarith.
        (* goal with Sx_ge_Tk_1 *)
        apply: conj. assumption. assumption.

    + (* cond of if evaluates to false *) 
      assert (Hcond0 := H21).
      rename H21 into Hcond. simpl in Hcond.
      case EnS: (stt_a st S)=> [lS | ]; rewrite EnS in Hcond; [ | inv Hcond ].
      rewrite H1 in Hcond. 
      case H_ige0: (i >=? 0)%Z; rewrite H_ige0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case H_lSi: (lS + i <? floc_of st)%Z;
        rewrite H_lSi in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      rewrite H2 in Hcond.
      case H_jge0: (j >=? 0)%Z; rewrite H_jge0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case H_lSj: (lS + j <? floc_of st)%Z;
        rewrite H_lSj in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      case H_lSij: (stt_l st (lS + i) <=? stt_l st (lS + j))%Z; 
        rewrite H_lSij in Hcond; [ simpl in Hcond; inv Hcond | ].
      clear Hcond.
      (* execute first round of the loop *)
      prem0_exe hall0.
      prem0_exe hall1. clear hall2. prem1_exe hall1. clear hall2 hall1.
      prem1_exe hall. clear hall1 hall hall0.
      (* re-visiting the loop after executing its body *) 
      move En_st'':
        (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) j_id z) k_id z0)
      => st''.
      symmetry in En_st''; rewrite <- En_st'' in *.
      rewrite -/com_wh in Hforall.
      have H_z1: z1 = (i + j - (m+1))%Z.
      {
        rename H27 into H_k_id_eval. simpl in H_k_id_eval. some_eq H_k_id_eval H3.
      }
      have H_z2: z2 = stt_l st (lS + j)%Z.
      {
        rename H28 into H_S_j_eval. simpl in H_S_j_eval.
        rewrite EnS in H_S_j_eval. rewrite H2 in H_S_j_eval.
        rewrite H_jge0 in H_S_j_eval. rewrite H_lSj in H_S_j_eval.
        simpl in H_S_j_eval; inv H_S_j_eval; auto.
      }
      have H_arrseq_S_jn_st'': arr_seq S j n st'' zs2.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto. 
        rewrite En_st''. repeat (try rewrite st_upd_var_arr).
        rewrite st_upd_loc_arr=>//.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        move=> z3 H_j_le_z3 H_z3_le_n.
        rewrite <- st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n);
          auto with zarith.
      }
      have H_exzs_Sj1_n_st'': exists zs2', arr_seq S (j + 1) n st'' zs2'.
      {
        apply arr_seq_ex with (l:=lS); auto with zarith.
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr. auto.
      }
      inversion H_exzs_Sj1_n_st'' as [zs2' H_arrseq_S_j1n_st''];
        clear H_exzs_Sj1_n_st''.
      have H_st''_j: stt_v st'' j_id = Some (j + 1)%Z.
      {
        rewrite En_st''. updsimp. 
        rename H31 into H_eval_j_1_. simpl in H_eval_j_1_.
        rewrite st_upd_loc_var in H_eval_j_1_.
        rewrite H2 in H_eval_j_1_; inv H_eval_j_1_; auto.
      }
      have H_st''_i: stt_v st'' i_id = Some i 
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_k: stt_v st'' k_id = Some (i + j - m)%Z.
      {
        rename H33 into H_eval_k_. simpl in H_eval_k_. updsimp_h H_eval_k_.
        rewrite st_upd_loc_var H3 in H_eval_k_.
        rewrite En_st''. updsimp.
        rewrite <- H_eval_k_.
        congr Some. auto with zarith.
      }
      have H_st''_m: stt_v st'' m_id = Some m
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_n: stt_v st'' n_id = Some n
        by rewrite En_st''; updsimp; rewrite st_upd_loc_var=>//.
      have H_st''_S: stt_a st'' S = Some lS.
      {
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr=>//.
      }
      have H_st''_T: stt_a st'' T = Some l.
      {
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr=>//.
      }
      have H_stt_l_st''_ijm: stt_l st'' (l + (i + j - (m + 1)))%Z = stt_l st (lS + j)%Z.
      {
        rewrite -H_z1. rewrite {1}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2=>//.
      }
      have H_arrseq_st''_zs3: arr_seq T prm (i + j - (m + 1) - 1) st'' zs3.
      {
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with zarith.
        some_eq H_st''_T H25.
        move=> z3 H_prm0_le_z3 H_z3_le_ijm.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
      }
      have H_arr_seq_T_st''_ext: 
        arr_seq T prm (i + j - m - 1) st'' (zs3 ++ [:: (stt_l st'' (l+i+j-(m+1))%Z)]).
      {
        have: (i + j - m - 1)%Z = (i + j - (m + 1) - 1 + 1)%Z by auto with zarith.
        move->.
        apply arr_seq_concat_general with (e1:=(i + j - (m + 1) - 1)%Z);
          auto with zarith.
        have: (i + j - (m+1) - 1 + 1)%Z = (i + j - (m+1))%Z by auto with zarith. move->. 
        have: (l + i + j - (m+1))%Z = (l + (i + j - (m+1)))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
      }
      have H_sorted_z3_ext: sorted (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
      {
        have H_prm0_rgn: (prm <= i + j - (m + 1))%Z by auto with zarith.
        have H_prm0_cases: (prm < i + j - (m + 1))%Z \/ (prm = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq=>//.
        inversion H_prm0_cases as [H_prm0_lt | H_prm0_eq].
        (* first case *)
        apply sorted_concat; auto with zarith.
        apply singleton_sorted. simpl.
        have: size zs3 = Z.to_nat ((i + j - (m + 1) - 1) - prm) + 1
          by apply arr_seq_size with (X:=T) (st:=st); auto with zarith.
        move->.
        have H_gt: (i + j - (m + 1) >= prm + 1)%Z by auto with zarith.
        rename H12 into H_Sx_ge_Tk_1_orig. 
        specialize (H_Sx_ge_Tk_1_orig H_gt).
        inversion H_Sx_ge_Tk_1_orig as [H_Sx_ge_left H_Sx_ge_right];
          clear H_Sx_ge_Tk_1_orig.
        rewrite /Sx_ge_Tk_1 in H_Sx_ge_right.
        have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite H_stt_l_st''_ijm.
        inversion H_Sx_ge_right as
            [l1' [l2' [z1' [z2' [H_l1' [H_l2' [H_z1' [H_z2' H_ge]]]]]]]].
        move: H_ge. have: l1' = lS by some_eq H_l1' EnS. move->.
        have: z1' = j by some_eq H_z1' H2. move->.
        have: l2' = l by some_eq H_l2' H25. move->.
        have: z2' = (i + j - (m + 1))%Z by some_eq H_z2' H3. move->.
        have: stt_l st (l + (i + j - (m + 1)) - 1)%Z =
              nth (0%Z) zs3 (Z.to_nat (i + j - (m + 1) - 1 - prm)).
        { rewrite -Z.add_sub_assoc.
          apply arr_seq_ele with
              (X:=T) (b:=prm) (e:=(i + j - (m + 1) - 1)%Z) (st:=st) (zs:=zs3)
              (l:=l) (z:=((i + j - (m + 1)) - 1)%Z); auto with zarith. }
        move->. rewrite -addnBA; auto. rewrite sub_zero. rewrite add_zero=>//.
        (* second case *)
        have: zs3 = [:: ] 
          by apply arr_seq_empty' with
            (X:=T) (b:=prm) (e:=(i + j - (m + 1) - 1)%Z) (st:=st);
          auto with zarith. move->=>/=. 
        apply singleton_sorted; auto.
      }
      have H_arrseq_Sim_st'': arr_seq S i m st'' zs1.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto.
        some_eq EnS H_st''_S.
        move=> z3 H_i_le_z3 H_z3_le_m.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite <- st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n); auto with zarith.
      }
      have H_exP_cond:
        (j+1 <= n)%Z <-> (exists P, mg_spec prm (com_wh, st'', mg_prog) P).
      {
        apply: conj.
        - move=> H_j1_le_m. 
          have H_lstfrag: lst_frag ((j+1)-j) zs2' zs2
            by apply arr_seq_subrgn_lst_frag with
              (S:=S) (b:=j) (e:=n) (b':=(j+1)%Z) (e':=n) (st:=st'');
            auto with zarith.
          eexists. 
          eapply WAF_SP_com_wh with
              (lprm:=prm) (i:=i) (j:=(j+1)%Z) (k:=(i+j-m)%Z) (m:=m) (n:=n) (st:=st'')
              (zs1:=zs1) (zs2:=zs2') (zs3:=zs3++[:: (stt_l st'' (l+i+j-(m+1))%Z)]);
            auto with zarith.
          (* goal with Sx_ge_Tk_1 *)
          have H_Sx_ge_Tk_1:
            (i + j - m >= prm + 1)%Z -> Sx_ge_Tk_1 i_id st'' /\ Sx_ge_Tk_1 j_id st''.
          {
            move=> H_k_ge. rewrite /Sx_ge_Tk_1. 
            apply: conj.
            2:{ 
              exists lS. exists l. exists (j+1)%Z. exists (i+j-m)%Z.
              repeat (try apply: conj=>//).
              have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
                by auto with zarith. move->.
              rewrite H_stt_l_st''_ijm. 
              have: stt_l st (lS + (j + 1))%Z = stt_l st'' (lS + (j + 1))%Z.
              {
                rewrite En_st''. repeat (try rewrite st_upd_var_loc).
                apply st_upd_loc_sep with
                    (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
                    (l1:=lS) (l2:=l) (z1:=(j+1)%Z) (z2:=z1) (z:=z2);
                  auto with zarith.          
              }
              move<-. apply Z.le_ge.
              apply sorted_arr_ele_compare with (X:=S) (b:=j) (e:=n) (zs:=zs2);
                auto with zarith.
            }
            exists lS. exists l. exists i. exists (i+j-m)%Z.
            repeat (try apply: conj=>//).
            have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
              by auto with zarith. move->.
            rewrite - H_z1. rewrite {2}En_st''.
            repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
            rewrite H_z2.
            have: stt_l st (lS + i)%Z = stt_l st'' (lS + i)%Z.
            {
              rewrite En_st''. repeat (try rewrite st_upd_var_loc).
              apply st_upd_loc_sep with
                  (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
                  (l1:=lS) (l2:=l) (z1:=i) (z2:=z1) (z:=z2);
                auto with zarith. 
            }
            move<-. move: H_lSij. move /Z.leb_gt. auto with zarith.            
          }
          apply H_Sx_ge_Tk_1.
          (* sorted zs2' *)
          apply sorted_lst_frag with (b0:=(j + 1 - j)%Z) (zs2:=zs2); auto.
          (* sep S param0 n T param0 n st'' *)
          apply sep_change_st with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st);
            auto with arith.
          some_eq H_st''_S EnS.
          some_eq H_st''_T H25.
          
        - elim=> [P H_spc_P].
          inversion H_spc_P; subst. updsimp_h H21.
          simpl in H31. rewrite st_upd_loc_var in H31. rewrite H2 in H31. 
          have: (j + 1)%Z = j0 by some_eq H21 H31. move->.
          updsimp_h H34. rewrite st_upd_loc_var in H34.
          have: n = n0 by some_eq H34 H6. move->=>//.
      }

      prem1 Hforall H_wh_spc_exe.
      inversion H_wh_spc_exe as [H_allP H_nexP]; clear H_wh_spc_exe.
      have: (~(j+1 <= n)%Z) \/ (j+1 <= n)%Z by apply /or_comm; apply classic.
      elim. 
      * (* remaining loop is not in spec *)
        move=> H_n_j_le. assert (H_j_rgn := H_n_j_le).
        move: H_n_j_le. move /H_exP_cond. move /H_nexP=> H_inf_wh.
        repeat (try push_eqs). inversion H_inf_wh; subst.
        rename H21 into H_rule_wh'. inversion H_rule_wh'; clear H_rule_wh'.
        (* the impossible case -- true *)
        clear H26. repeat (try push_eqs).
        rename H21 into H_cond_eval_tt.
        simpl in H_cond_eval_tt.
        rewrite H_st''_i in H_cond_eval_tt. rewrite H_st''_m in H_cond_eval_tt.
        rewrite H_st''_j in H_cond_eval_tt. rewrite H_st''_n in H_cond_eval_tt.
        have H_cond_true: ((i <=? m)%Z && (j + 1<=? n)%Z) = true
          by inv H_cond_eval_tt; auto.
        have contra: (j + 1 <=? n)%Z = true.
        { case En':(j + 1 <=? n)%Z=>//. rewrite En' in H_cond_true.
          case En'': (i <=? m)%Z=>//; rewrite En'' in H_cond_true.
          inv H_cond_true. inv H_cond_true. }
        apply Z.leb_nle in H_j_rgn. rewrite H_j_rgn in contra. inv contra.
        (* the actual case -- false *)
        rename H32 into H_st0st''. (* no need for rewriting *) clear st0 H_st0st''.
        rename H35 into H_st''r. rewrite <- H_st''r in *. clear r H_st''r.
        rename H21 into H_cond_eval_ff. 
        repeat (try pop_eqs).
        exists i. exists (j+1)%Z. exists (i + j - m)%Z.
        apply: conj; [auto | ]. apply: conj; [auto | ]. apply: conj; [auto | ].
        apply: conj. right. auto with zarith. 
        apply: conj. auto with zarith.
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj. some_eq H_st''_T H25. 
        apply: conj.
        exists [:: ]. exists [:: stt_l st (lS + j)%Z]. exists [:: stt_l st (lS + j)%Z].
        apply: conj. 
        apply arr_seq_empty; auto with zarith.
        apply: conj. 
        have: (j + 1 - 1)%Z = j by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        apply: conj. 
        rename heq7 into H_stt_l_st''_ijm. rewrite - H_stt_l_st''_ijm.
        have: (i + j - m - 1)%Z = (i + j - (m + 1))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        move=> z3. simpl. repeat rewrite add_zero=>//.  
        apply: conj.
        (*  exists zs : seq Z, arr_seq T prm (i + j - m - 1) st'' zs /\ sorted zs *)
        exists (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
        apply: conj.
        apply H_arr_seq_T_st''_ext. apply H_sorted_z3_ext.
        apply: conj.
        (* (exists zs : seq Z, arr_seq S prm n st zs /\ arr_seq S prm n st'' zs) *)
        have H_ex_zs_arrseq: exists zs, arr_seq S prm n st zs
            by apply arr_seq_ex with (l:=lS); auto with zarith.
        inversion H_ex_zs_arrseq as [zs' H_arrseq_S_zs']; clear H_ex_zs_arrseq.
        exists zs'.
        apply: conj. auto.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_prm0z3 H_z3n.
        rename heq4 into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep with (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n)
                                  (st:=st) (l1:=lS) (l2:=l) (z1:=z3) (z2:=z1) (z:=z2);
          auto with zarith. 
        apply: conj.
        (* preservation of initial fragment of T *)
        have H_ex_zs_arrseq_T_st_zs: exists zs, arr_seq T prm (i+j-(m+1)-1) st zs
            by apply arr_seq_ex with (l:=l); auto with zarith.
        inversion H_ex_zs_arrseq_T_st_zs as [zs_T H_arrseq_T_zs_T];
          clear H_ex_zs_arrseq_T_st_zs.
        exists zs_T.
        apply: conj. auto. 
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with arith.
        some_eq H25 H_st''_T.
        move=> z3 H_prm0_z3 H_z3_ijm.
        rename heq4 into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
        rewrite st_upd_neq_loc; auto.
        rename heq5 into H_z1. rewrite H_z1. auto with zarith.
        (* goal with Sx_ge_Tk_1 *)
        apply: conj.
        move=> H_jim_rgn.
        inversion H_jim_rgn as [H_i_le_m H_ijm_ge_]; clear H_jim_rgn.
        rewrite /Sx_ge_Tk_1.
        exists lS. exists l. exists i. exists (i+j-m)%Z.
        repeat (try apply: conj=>//).
        have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite -heq5. rename heq4 into En_st''. rewrite {2}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rename heq6 into H_z2. rewrite H_z2.
        have: stt_l st (lS + i)%Z = stt_l st'' (lS + i)%Z.
        {
          rewrite En_st''. repeat (try rewrite st_upd_var_loc).
          apply st_upd_loc_sep with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n) (st:=st)
              (l1:=lS) (l2:=l) (z1:=i) (z2:=z1) (z:=z2);
            auto with zarith. 
        }
        move<-. apply Z.le_ge. move: heq3. move /Z.leb_gt. auto with zarith.

        move=> H_ijm_rgn_contra.
        inversion H_ijm_rgn_contra as [H_j1_le_n H_ijm_ge_];
          clear H_ijm_rgn_contra.
        apply H_j_rgn in H_j1_le_n. inv H_j1_le_n.
        
      * (* remaining loop is in spec *)
        move=> H_j_le. assert (H_j_rgn := H_j_le).
        move: H_j_le. move /H_exP_cond. 
        elim=> [P H_P_spc].
        specialize (H_allP P H_P_spc). move: H_allP=> H_P_r.
        inversion H_P_spc. rename H48 into H_fun_r_eq_P.
        rewrite <- H_fun_r_eq_P in H_P_r. clear H_fun_r_eq_P.

        rename H0 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
        have H_jj0: (j+1)%Z = j0 by some_eq H_st''_j H21.
        have H_ii0: i = i0 by some_eq H_st''_i H4.
        have H_ijm_k: (i + j - m)%Z = k by some_eq H_st''_k H24.
        have H_mm0: m = m0 by some_eq H_st''_m H32.
        have H_nn0: n = n0 by some_eq H_st''_n H34.
        rewrite <- H_ii0 in *. clear i0 H_ii0.
        rewrite <- H_jj0 in *. clear j0 H_jj0.
        rewrite <- H_mm0 in *. clear m0 H_mm0.
        rewrite <- H_nn0 in *. clear n0 H_nn0.

        have H_zs4_: zs2' = zs4
          by apply arr_seq_unique with
            (S:=S) (b:=(j+1)%Z) (e:=n) (st:=st''); auto with zarith.
        rewrite <- H_zs4_ in *. clear zs4 H_zs4_.
        rename H45 into H_sorted_zs2'.
        rename H42 into H_arrseq_S_st''; clear H_arrseq_S_st''.
        rename H41 into H_arrseq_S_st''_zs0. rename H44 into H_sorted_zs0.
        clear zs0 H_arrseq_S_st''_zs0 H_sorted_zs0.
        rename H43 into H_arrseq_T_st''_zs5. rename H46 into H_sorted_zs5.
        clear zs5 H_arrseq_T_st''_zs5 H_sorted_zs5.

        inversion H_P_r as 
            [i' [j' [k' [H_i'0 [H_j' [H_k' [H_ijkm_or [H_k'_ [H_m_ [H_n_ [H_S_ [H_T_ H'']]]]]]]]]]]]; clear H_P_r.
        inversion H'' as
            [H_occ' [H_sorted' [H_S_preserve' [H_T_preserve' [H_Sx_ge_Tk_1_i' H_Sx_ge_Tk_1_j']]]]]; clear H''.
        
        exists i'. exists j'. exists k'.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. inv H_ijkm_or; [left | right]; auto with zarith. 
        apply: conj.
        auto with zarith. (* k' = (i + j - (m + 1) + (i'0 - i) + (j' - j))%Z *)
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by rewrite H_st''_S in H_S_; inv H_S_; auto.
        apply: conj. 
        { rewrite H_st''_T in H_T_. rewrite <- H25 in H_T_. inv H_T_; auto. }
        apply: conj. (* goal with occ *)
        inversion H_occ' as
            [zs10 [zs20 [zs30 [H_zs10 [H_zs20 [H_zs30 H_all]]]]]]; clear H_occ'.
        exists zs10. 
        exists ((stt_l st (lS+j)%Z) :: zs20).
        exists ((stt_l st (lS+j)%Z) :: zs30).

        have H_arrseq_S_j_1_st: arr_seq S (j + 1) (j' - 1) st zs20.
        {
          apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
            auto with zarith.
          rewrite En_st''. repeat rewrite st_upd_var_arr.
          rewrite st_upd_loc_arr=>//.
          move=> z3 H_jz3 H_z3j0.
          rewrite En_st''. repeat rewrite st_upd_var_loc.
          symmetry.
          apply st_upd_loc_sep with
              (X1:=S) (b1:=prm) (e1:=n) (X2:=T)
              (b2:=prm) (e2:=n) (l2:=l) (z2:=z1) (z:=z2);
            auto with zarith.
        }
        apply: conj.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
          auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_iz3 H_z3i'_1.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        symmetry.
        by apply st_upd_loc_sep with (X1:=S) (b1:=prm) (e1:=n)
                                     (X2:=T) (b2:=prm) (e2:=n);
          auto with zarith.
        apply: conj. 
        have: stt_l st (lS + j)%Z :: zs20 = [:: stt_l st (lS + j)%Z] ++ zs20
          by simpl; auto. move->.
        apply arr_seq_concat_general with (e1:=j); auto with zarith. by
            apply arr_seq_singleton; auto with zarith.
        apply: conj.
        have: (i + j - (m+1))%Z = (k - 1)%Z by auto with zarith. move->.
        have: stt_l st (lS + j)%Z :: zs30 = [:: stt_l st (lS + j)%Z] ++ zs30
          by auto. move->.        
        apply arr_seq_concat with (e1:=(k-1)%Z); auto with zarith.
        inversion H_S_preserve' as
            [zs [H_arrseq_S_st'' H_arrseq_S_r]]; clear H_S_preserve'.
        rewrite <- H_stt_l_st''_ijm.
        have: (l + (i + j - (m + 1)))%Z = (k - 1 + l)%Z by auto with zarith. move->.
        have: stt_l st'' (l + (k-1))%Z = stt_l r (l + (k-1))%Z.
        {
          inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]]. 
          apply arr_seq_ele_eq with (X:=T) (b:=prm) (e:=(k-1)%Z) (zs:=zs_T);
            auto with zarith.
          congruence.
        }
        have: (k - 1 + l)%Z = (l + (k - 1))%Z by auto with zarith. move->. move->.
        apply arr_seq_singleton; auto with zarith.
        congruence.
        have: (k - 1 + 1)%Z = k by auto with zarith. move->. auto.
        move=> z3.
        have: stt_l st (lS + j)%Z :: zs20 = [:: stt_l st (lS+j)%Z] ++ zs20 by simpl; auto.
        move->.
        have: stt_l st (lS + j)%Z :: zs30 = [:: stt_l st (lS+j)%Z] ++ zs30 by simpl; auto.
        move->.
        do 2! (rewrite occ_cat).        
        rewrite [(occ [:: stt_l st (lS + j)%Z] z3 + occ zs20 z3)]Nat.add_comm.
        rewrite [occ zs10 z3 + (occ zs20 z3 + _)]Nat.add_assoc.
        rewrite [(occ zs10 z3 + occ zs20 z3)%coq_nat]H_all.
        rewrite {1}Nat.add_comm. by auto.
        
        apply: conj. by assumption. (* initial fragment of T sorted *)
        apply: conj. (* preservation of content of S *)        
        inversion H_S_preserve' as [zs_S [H_arrseq_S_st'' H_arrseq_S_r]].
        exists zs_S. apply: conj; [ | auto].
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence. 
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
        apply st_upd_loc_sep with (X1:=S) (b1:=prm) (e1:=n) (X2:=T) (b2:=prm) (e2:=n);
          auto with zarith.

        apply: conj.
        (* preservation of content of initial fragment of T *)
        have H_ijm_rgn: (0 <= i + j - (m + 1))%Z by auto with zarith.
        have: (0 < i + j - (m + 1))%Z \/ (0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq; auto.
        case=> H_cs.
        (* first case *)
        inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]].
        have H_ex_T': exists zs_T', arr_seq T prm (i+j-(m+1)-1) r zs_T'.
        { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
        inversion H_ex_T' as [zs_T' H_arrseq_T_zs_T']; clear H_ex_T'.
        have H_arrseq_T_st''_zs_T': arr_seq T prm (i+j-(m+1)-1) st'' zs_T'
          by apply arr_seq_subrgn with (b:=prm) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
          auto with zarith.
        have H_arrseq_T_st_zs_T': arr_seq T prm (i+j-(m+1)-1) st zs_T'.
        {
          apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
          congruence.
          move=> z3 H_prm0_z3 H_z3_ijm.
          rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
          rewrite st_upd_neq_loc; auto.
          rewrite H_z1. auto with zarith.
        }
        exists zs_T'. apply: conj; auto.
        (* second case *)
        rewrite <- H_cs. simpl.
        exists [:: ].
        apply: conj; apply arr_seq_empty; auto with zarith.

        (* goal with Sx_ge_Tk_1 *)
        apply: conj. assumption. assumption.   
        
  - (* proof for 2nd loop *)
    inv H; subst. clear H0.
    rename H13 into H_rule_wh.
    inv H_rule_wh; subst; clear H_rule_wh.
    (* refute exiting the loop *)
    2: {
      rename H9 into H_i_le_m. rename H11 into Hcond.
      simpl in Hcond. rewrite H5 in Hcond. rewrite H1 in Hcond.
      have: (i <=? m)%Z = false by inv Hcond; auto.
      move /Z.leb_gt=> contra. 
      apply Zlt_not_le in contra. apply contra in H_i_le_m.
      inv H_i_le_m.
    }
    (* entering the loop *)
    rename H11 into Hcond. rename H14 into Hforall.
    prem0_exe Hforall. 
    prem0_exe hall. clear hall0. prem1_exe hall. 
    prem0_exe hall0. clear hall1. prem1_exe hall0.
    clear hall1 hall0 hall.
    fold (com_ab i_id m_id) in Hforall. 
    rename H19 into H_eval_Si.
    rename H22 into H_eval_i_1.
    rename H24 into H_eval_k_1.
    rename H16 into H_st_T.
    rename H12 into H_sep_S_T.

    move En_st'':
      (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) i_id z) k_id z0)
    => st''.
    symmetry in En_st''. rewrite <- En_st'' in *.

    have H_z: (i+1)%Z = z.
    {
      simpl in H_eval_i_1. rewrite st_upd_loc_var in H_eval_i_1.
      rewrite H1 in H_eval_i_1. inv H_eval_i_1; auto.
    }
    rewrite <- H_z in *; clear z H_z.
    (* move En_j: (n+1)%Z => j.  *)
    have H_z0: (i+n-m+1)%Z = z0.
    {
      simpl in H_eval_k_1. updsimp_h H_eval_k_1.
      rewrite st_upd_loc_var in H_eval_k_1. 
      rewrite H3 in H_eval_k_1.
      inv H_eval_k_1; auto with zarith.
    }
    rewrite <- H_z0 in *; clear z0 H_z0.
    have H_z1: (i+n-m)%Z = z1.
    {
      rename H18 into H_eval_k. simpl in H_eval_k.      
      some_eq H_eval_k H3. auto with zarith.
    }
    rewrite <- H_z1 in *; clear z1 H_z1.
    have H_st''_i: stt_v st'' i_id = Some (i + 1)%Z.
    { rewrite En_st''. updsimp. auto. }
    have H_st''_j: stt_v st'' j_id = Some (n+1)%Z.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var; auto. }
    have H_st''_k: stt_v st'' k_id = Some (i + n - m + 1)%Z.
    { rewrite En_st''. updsimp. auto with zarith. }
    have H_st''_m: stt_v st'' m_id = Some m.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var. auto. }
    have H_st''_n: stt_v st'' n_id = Some n.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var. auto. }
    have H_st''_st_S: stt_a st S = stt_a st'' S.
    { rewrite En_st''. repeat rewrite st_upd_var_arr.
      rewrite st_upd_loc_arr. auto. }
    have H_st''_st_T: stt_a st T = stt_a st'' T.
    { rewrite En_st''. repeat rewrite st_upd_var_arr.
      rewrite st_upd_loc_arr. auto. }

    have: exists l, stt_a st S = Some l
        by apply sep_ex_loc_1 with (l1:=prm) (h1:=n) (l2:=prm) (h2:=n) (X2:=T);
                      auto.
    elim=> [lS H_lS].
    have H_z2: z2 = stt_l st (lS + i)%Z.
    {
      simpl in H_eval_Si. rewrite H_lS in H_eval_Si.
      rewrite H1 in H_eval_Si.
      case En: (i >=? 0)%Z; case En': (lS + i <? floc_of st)%Z;
        rewrite En En' in H_eval_Si; simpl in H_eval_Si; try inv H_eval_Si; auto.
    }
    have H_st_lSi_st''_: stt_l st (lS+i)%Z = stt_l st'' (l+i+n-m)%Z.
    {
      rewrite En_st''. repeat rewrite st_upd_var_loc.
      have: (l + (i + n - m))%Z = (l + i + n - m)%Z by auto with zarith. move->.
      rewrite st_upd_eq_loc=>//.
    }

    have H_exP_cond:
      (i + 1 <= m)%Z <-> (exists P, mg_spec prm (com_ab i_id m_id, st'', mg_prog) P).
    {
      apply: conj.
      -  move=> H_i_1_m.
         eexists.
         eapply WAF_SP_com_im with
             (st:=st'') (i:=(i+1)%Z) (j:=(n+1)%Z) (k:=(i+n-m+1)%Z) (m:=m) (n:=n).
         apply H_st''_i. apply H_st''_j. apply H_st''_k.
         auto with zarith.
         apply H_st''_m. apply H_st''_n.
         assumption. (* (0 <= prm)%Z *)
         auto with zarith. (* (prm <= i + 1)%Z *)
         assumption. assumption. (* m < n *)
         auto. (* n+1 = n+1 *)
         apply sep_change_st with (X1:=S) (X2:=T) (st:=st); auto.
      - elim=> [P H_spc_P].
        inversion H_spc_P; subst.
        updsimp_h H4. inv H4. rewrite H15. 
        updsimp_h H16. rewrite st_upd_loc_var in H16.
        have: m = m0 by some_eq H16 H5. move->=>//.
    }

    prem1 Hforall H_wh.
    inversion H_wh as [H_allP H_nexP]; clear H_wh.
    have: (~(i+1 <= m)%Z) \/ (i+1 <= m)%Z by apply /or_comm; apply classic.
    elim. 
    + (* remaining loop is not in spec *)
      move=> H_n_i_le. assert (H_i_rgn := H_n_i_le).
      move: H_n_i_le. move /H_exP_cond. move /H_nexP=> H_inf_wh.
      repeat (try push_eqs). inversion H_inf_wh; subst.
      rename H11 into H_rule_wh'. inversion H_rule_wh'; clear H_rule_wh'.
      (* the impossible case -- true *)
      clear H15. rename H11 into H_cond_ev_true. simpl in H_cond_ev_true.
      rewrite H_st''_i in H_cond_ev_true. rewrite H_st''_m in H_cond_ev_true.
      have contra: (i + 1 <=? m)%Z = true by inv H_cond_ev_true; auto.
      apply Zle_bool_imp_le in contra. apply H_i_rgn in contra. inv contra.
      (* the actual case -- false *)
      clear H15. repeat (try pop_eqs).
      rename H19 into H_st''_eq_r. rewrite <- H_st''_eq_r in *. clear r H_st''_eq_r.
      rename H16 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
      rename H4 into H_crs_emp. clear crs H_crs_emp H12.
      rename H17 into H_p_eq_myprog. clear p H_p_eq_myprog.
      rename H0 into H_b_eq_ble. clear b H_b_eq_ble.
      (* establish the false condition *)
      (* move En_j: (n + 1)%Z => j.  *)
      exists (i+1)%Z. exists (n+1)%Z. exists (i+n-m+1)%Z.
      apply: conj. by assumption.
      apply: conj. rewrite H_st''_j; by auto.
      apply: conj. auto.
      apply: conj. by auto with zarith.
      apply: conj. by auto with zarith.
      apply: conj. by reflexivity.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by assumption. (* stt_v st'' n_id = Some n *)
      apply: conj. by auto. (* stt_a st'' T = stt_a st T *)
      apply: conj. 
      (* S -> T *)
      exists [:: stt_l st (lS + i)%Z]. 
      apply: conj. 
      have: (i+1-1)%Z = i by auto with zarith. move->.
      apply arr_seq_singleton; auto with zarith.
      have: (i + (n + 1) - (m + 1))%Z = (i + n - m)%Z by auto with zarith. move->.
      rename heq3 into H_st_lSi_st''_. rewrite H_st_lSi_st''_.
      have: (i + n - m + 1 - 1)%Z = (i + n - m)%Z by auto with zarith. move->.
      have: (l + i + n - m)%Z = (l + (i + n - m))%Z by auto with zarith. move->.
      apply arr_seq_singleton; auto with zarith. 
      congruence.
      (* preservation of initial fragment of T *)
      have: exists zs, arr_seq T prm (i+n-m-1)%Z st'' zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim => [zs_T H_arrseq_T_st''_zs_T].
      exists zs_T.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z1 H_prm0_z1 H_z1_ijm.
      rename heq into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
      rewrite st_upd_neq_loc; auto with zarith.
      have: (i+(n+1)-(m+1)-1)%Z = (i+n-m-1)%Z by auto with zarith. move->=>//.
      have: (i+(n+1)-(m+1)-1)%Z = (i+n-m-1)%Z by auto with zarith. move->=>//.

    + (* remaining loop is in spec *)
      move=> H_i_le. assert (H_i_rgn := H_i_le).
      move: H_i_le. move /H_exP_cond. 
      elim=> [P H_P_spc].
      specialize (H_allP P H_P_spc). move: H_allP=> H_P_r.
      inversion H_P_spc. rename H27 into H_fun_r_eq_P.
      rewrite <- H_fun_r_eq_P in H_P_r. clear H_fun_r_eq_P.

      inversion H_P_r as
          [i' [j' [k' [H_i' [H_j' [H_k' [H_i'_i0 [H_i'_m0_1 [H_j'_j0 [H_k'_ H_body]]]]]]]]]]; clear H_P_r.
      inversion H_body as [H_m0 [H_n0 [H_st''_T [H_ex_S_T H_T_preserve]]]]; clear H_body.
      have H_i_1_i0: (i + 1)%Z = i0 by some_eq H_st''_i H4.
      have H_j_j0: (n+1)%Z = j by rename H11 into H_st''_j0; some_eq H_st''_j0 H_st''_j.
      have H_m_m0: m = m0 by rename H16 into H_st''_m0; some_eq H_st''_m0 H_st''_m.
      have H_n_n0: n = n0 by rename H17 into H_st''_n0; some_eq H_st''_n0 H_st''_n.
      rewrite <- H_i_1_i0 in *. rewrite <- H_j_j0 in *.
      rewrite <- H_m_m0 in *. rewrite <- H_n_n0 in *.
      clear i0 H_i_1_i0. clear j H_j_j0. clear m0 H_m_m0. clear n0 H_n_n0.
      symmetry in H_j'_j0. rewrite <- H_j'_j0 in *. clear j' H_j'_j0.

      exists i'. exists (n+1)%Z. exists k'.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by reflexivity.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by congruence.
      apply: conj.
      (* S -> T *)
      inversion H_ex_S_T as [zs0 [H_arrseq_S_st'' H_arrseq_T_r]].
      exists ([:: stt_l st (lS+i)%Z] ++ zs0).
      apply: conj.
      have H_arrseq_S_st': arr_seq S (i + 1) (i' - 1) st zs0.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence.
        move=>z3 H_iz3 H_z3i'.
        rewrite En_st''. symmetry. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n);
          auto with zarith.
      }
      apply arr_seq_concat_general with (e1:=i); auto with zarith.
      apply arr_seq_singleton; auto with zarith.      
      
      apply arr_seq_concat_general with (e1:=(i+n-m)%Z); auto with zarith.        
      rewrite H_st_lSi_st''_.
      have: (l + i + n - m)%Z = (l + (i + n - m))%Z by auto with zarith. move->. 
      have: stt_l st'' (l + (i + n - m))%Z = stt_l r (l + (i + n - m))%Z.
      {
        inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]].
        apply arr_seq_ele_eq with (X:=T) (b:=prm) (e:=(k-1)%Z) (zs:=zs_T);
          auto with zarith.
        congruence. congruence.
      }
      move->.
      have: (i + (n + 1) - (m + 1))%Z = (i + n - m)%Z by auto with zarith. move->.
      apply arr_seq_singleton; auto with zarith. congruence.
      have: (i + n - m + 1)%Z = k by auto with zarith. move->.
      auto.

      (* preservation of initial fragment of T *) 
      inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]];
        clear H_T_preserve. 
      have: exists zs, arr_seq T prm (i + n - m - 1) r zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim=> [zs_T' H_arrseq_T_r_zs_T'].
      have H_arrseq_T_st''_zs_T': arr_seq T prm (i + n - m - 1) st'' zs_T'.
      apply arr_seq_subrgn with (b:=prm) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
        auto with zarith.
      exists zs_T'.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z3 H_prm0_z3 H_z3_ijm.
      rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
      rewrite st_upd_neq_loc; auto with zarith.
      have: (i+(n+1)-(m+1)-1)%Z = (i+n-m-1)%Z by auto with zarith. move->=>//.
      have: (i+(n+1)-(m+1)-1)%Z = (i+n-m-1)%Z by auto with zarith. move->=>//.
      
  - (* proof for the 3rd loop *)
    inv H; subst. clear H0.
    rename H13 into H_rule_wh. inv H_rule_wh; subst; clear H_rule_wh.
    (* refute exiting the loop *)
    2: {
      rename H10 into H_j_le_n. rename H11 into Hcond.
      simpl in Hcond. rewrite H2 in Hcond. rewrite H6 in Hcond.
      have: (j <=? n)%Z = false by inv Hcond; auto.
      move /Z.leb_gt=> contra. 
      apply Zlt_not_le in contra. apply contra in H_j_le_n.
      inv H_j_le_n.
    }
    (* entering the loop *)
    rename H11 into Hcond. rename H14 into Hforall.
    prem0_exe Hforall.
    prem0_exe hall. clear hall0. prem1_exe hall.
    prem0_exe hall0. clear hall1. prem1_exe hall0. clear hall1 hall0 hall.
    
    fold (com_ab j_id n_id) in Hforall.
    rename H19 into H_eval_Sj.
    rename H22 into H_eval_j_1.
    rename H24 into H_eval_k_1.
    rename H16 into H_st_T.
    rename H12 into H_sep_S_T.

    move En_st'':
      (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) j_id z) k_id z0)
    => st''.
    symmetry in En_st''. rewrite <- En_st'' in *.
    have H_z: (j+1)%Z = z.
    {
      simpl in H_eval_j_1. rewrite st_upd_loc_var in H_eval_j_1.
      rewrite H2 in H_eval_j_1. inv H_eval_j_1; auto.
    }
    rewrite <- H_z in *. clear z H_z.
    (* move En_i: (m+1)%Z => i.  *)
    have H_z0: (j + 1)%Z = z0. 
    {
      simpl in H_eval_k_1. updsimp_h H_eval_k_1.
      rewrite st_upd_loc_var in H_eval_k_1. 
      rewrite H3 in H_eval_k_1.
      inv H_eval_k_1; auto with zarith.
    }
    rewrite <- H_z0 in *. clear z0 H_z0.
    have H_z1: j = z1.
    {
      rename H18 into H_eval_k. simpl in H_eval_k.
      rewrite H_eval_k in H3. inv H3; auto with zarith.
    }
    rewrite <- H_z1 in *. clear z1 H_z1.  
    have H_st''_j: stt_v st'' j_id = Some (j + 1)%Z.
    { rewrite En_st''. updsimp. auto. }
    have H_st''_i: stt_v st'' i_id = Some (m + 1)%Z.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var; auto. }
    have H_st''_k: stt_v st'' k_id = Some (j+1)%Z.
    { rewrite En_st''. updsimp. auto with zarith. }
    have H_st''_m: stt_v st'' m_id = Some m.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var. auto. }
    have H_st''_n: stt_v st'' n_id = Some n.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var. auto. }
    have H_st''_st_S: stt_a st S = stt_a st'' S.
    { rewrite En_st''. repeat rewrite st_upd_var_arr.
      rewrite st_upd_loc_arr. auto. }
    have H_st''_st_T: stt_a st T = stt_a st'' T.
    { rewrite En_st''. repeat rewrite st_upd_var_arr.
      rewrite st_upd_loc_arr. auto. }
    have: exists l, stt_a st S = Some l
        by apply sep_ex_loc_1 with (l1:=prm) (h1:=n) (l2:=prm) (h2:=n) (X2:=T); auto.
    elim=> [lS H_lS].
    have H_z2: z2 = stt_l st (lS + j)%Z.
    {
      simpl in H_eval_Sj. rewrite H_lS in H_eval_Sj.
      rewrite H2 in H_eval_Sj.
      case En: (j >=? 0)%Z;
        case En': (lS + j <? floc_of st)%Z;
        rewrite En En' in H_eval_Sj; simpl in H_eval_Sj;
          try inv H_eval_Sj; auto.
    }
    have H_st_lSj_st''_: stt_l st (lS+j)%Z = stt_l st'' (l+j)%Z.
    {
      rewrite En_st''. repeat rewrite st_upd_var_loc. rewrite st_upd_eq_loc=>//.
    }
    
    have H_exP_cond:
      (j + 1 <= n)%Z <-> (exists P, mg_spec prm (com_ab j_id n_id, st'', mg_prog) P).      
    {
      apply: conj.
      - move=> H_j_1_n.
        eexists.
        eapply WAF_SP_com_jn with
            (st:=st'') (i:=(m+1)%Z) (j:=(j+1)%Z) (k:=(j+1)%Z) (m:=m) (n:=n).
        apply H_st''_i. apply H_st''_j. apply H_st''_k.
        auto with zarith.
        apply H_st''_m. apply H_st''_n.
        assumption. (* (0 <= param0)%Z *)
        auto with zarith. (* (param0 <= i)%Z *)
        auto with zarith.
        assumption. (* m < n *)
        auto. (* i = m+1 *)
        apply sep_change_st with (X1:=S) (X2:=T) (st:=st); auto.
      - elim=> [P H_spc_P].
        inversion H_spc_P; subst. updsimp_h H11. inv H11. rewrite H15.
        updsimp_h H17. rewrite st_upd_loc_var in H17. some_eq H17 H6. auto with zarith.
    }

    prem1 Hforall H_wh.
    inversion H_wh as [H_allP H_nexP]; clear H_wh.
    have: (~(j+1 <= n)%Z) \/ (j+1 <= n)%Z by apply /or_comm; apply classic.
    elim. 
    + (* remaining loop is not in spec *)
      move=> H_n_j_le. assert (H_j_rgn := H_n_j_le).
      move: H_n_j_le. move /H_exP_cond. move /H_nexP=> H_inf_wh.
      repeat (try push_eqs). inversion H_inf_wh; subst.
      rename H11 into H_rule_wh'. inversion H_rule_wh'; clear H_rule_wh'.
      (* the impossible case -- true *)
      clear H15. repeat (try pop_eqs). 
      rename H11 into H_cond_ev_true. simpl in H_cond_ev_true.
      rewrite H_st''_j in H_cond_ev_true. rewrite H_st''_n in H_cond_ev_true.
      have contra: (j + 1 <=? n)%Z = true by inv H_cond_ev_true; auto.
      apply Zle_bool_imp_le in contra. apply H_j_rgn in contra. inv contra.
      (* the actual case -- false *) 
      clear H15. repeat (try pop_eqs). 
      rename H19 into H_st''_eq_r. rewrite <- H_st''_eq_r in *. clear r H_st''_eq_r.
      rename H16 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
      rename H4 into H_crs_emp. clear crs H_crs_emp H12.
      rename H17 into H_p_eq_myprog. clear p H_p_eq_myprog.
      rename H0 into H_b_eq_ble. clear b H_b_eq_ble.
      (* establish the false condition *)
      (* move En_i: (m + 1)%Z => i.  *)
      exists (m + 1)%Z. exists (j + 1)%Z. exists (j + 1)%Z.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by auto with zarith.
      apply: conj. by auto with zarith.
      apply: conj. by auto with zarith.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by assumption. (* stt_v st'' n_id = Some n *)
      apply: conj. by auto. (* stt_a st'' T = stt_a st T *)
      apply: conj. 
      (* S -> T *)
      exists [:: stt_l st (lS + j)%Z].
      apply: conj.
      have: (j+1-1)%Z = j by auto with zarith. move->.
      apply arr_seq_singleton; auto with zarith.
      have: (m + 1 + j - (m + 1))%Z = j by auto with zarith. move->.
      have: (j + 1 - 1)%Z = j by auto with zarith. move->.
      rename heq3 into H_st_lSj_st''_. rewrite H_st_lSj_st''_.      
      apply arr_seq_singleton; auto with zarith.
      congruence.
      
      (* preservation of initial fragment of T *)
      have: exists zs, arr_seq T prm (j - 1)%Z st'' zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim => [zs_T H_arrseq_T_st''_zs_T].
      exists zs_T.
      apply: conj=>//.
      have: (m + 1 + j - (m + 1) - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z1 H_prm0_z1 H_z1_j_1.
      rename heq into En_st''. rewrite En_st''. repeat rewrite st_upd_var_loc.
      rewrite st_upd_neq_loc; auto with zarith.
      have: (m + 1 + j - (m + 1) - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      auto.

    + (* remaining loop is in spec *)
      move=> H_j_le. assert (H_j_rgn := H_j_le).
      move: H_j_le. move /H_exP_cond. 
      elim=> [P H_P_spc].
      specialize (H_allP P H_P_spc). move: H_allP=> H_P_r.
      inversion H_P_spc. rename H27 into H_fun_r_eq_P.
      rewrite <- H_fun_r_eq_P in H_P_r. clear H_fun_r_eq_P.

      inversion H_P_r as
          [i' [j' [k' [H_i' [H_j' [H_k' [H_i'_i0 [H_i'_m0_1 [H_j'_j0 [H_k'_ H_body]]]]]]]]]]; clear H_P_r. 
      inversion H_body as [H_m0 [H_n0 [H_st''_T [H_ex_S_T H_T_preserve]]]]; clear H_body.
      have H_j_1_j0: (j + 1)%Z = j0 by some_eq H_st''_j H11.
      have H_i_i0: (m+1)%Z = i by rename H4 into H_st''_i0; some_eq H_st''_i0 H_st''_i.
      have H_m_m0: m = m0 by rename H16 into H_st''_m0; some_eq H_st''_m0 H_st''_m.
      have H_n_n0: n = n0 by rename H17 into H_st''_n0; some_eq H_st''_n0 H_st''_n.
      rewrite <- H_j_1_j0 in *.
      rewrite <- H_i_i0 in *.
      rewrite <- H_m_m0 in *. 
      rewrite <- H_n_n0 in *.
      clear j0 H_j_1_j0. clear i H_i_i0. clear m0 H_m_m0. clear n0 H_n_n0.
      symmetry in H_i'_i0. rewrite <- H_i'_i0 in *. clear i' H_i'_i0.      

      exists (m+1)%Z. exists j'. exists k'. 
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by reflexivity.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by auto with zarith.
      apply: conj. by assumption.
      apply: conj. by assumption.
      apply: conj. by congruence.
      apply: conj.
      (* S -> T *)
      inversion H_ex_S_T as [zs0 [H_arrseq_S_st'' H_arrseq_T_r]].
      exists ([:: stt_l st (lS+j)%Z] ++ zs0).
      apply: conj.
      have H_arrseq_S_st': arr_seq S (j + 1) (j' - 1) st zs0.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence.
        move=>z3 H_jz3 H_z3j'.
        rewrite En_st''. symmetry. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=prm) (e1:=n) (b2:=prm) (e2:=n);
          auto with zarith.
      }
      apply arr_seq_concat_general with (e1:=j); auto with zarith.
      apply arr_seq_singleton; auto with zarith.      
      rewrite H_st_lSj_st''_.
      have: (m + 1 + j - (m + 1))%Z = j by auto with zarith. move->.
      (* have: (l + i + j - (m + 1))%Z = (l + j)%Z by auto with zarith. move->. *)
      apply arr_seq_concat_general with (e1:=j); auto with zarith.
      have: stt_l st'' (l + j)%Z = stt_l r (l + j)%Z.
      {
        inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]].
        apply arr_seq_ele_eq with (X:=T) (b:=prm) (e:=(k-1)%Z) (zs:=zs_T);
          auto with zarith.
        congruence. congruence.
      }
      move->.
      apply arr_seq_singleton; auto with zarith. congruence.
      have: (j + 1)%Z = k by auto with zarith. move->. auto.
      (* preservation of initial fragment of T *) 
      inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]];
        clear H_T_preserve.
      have: (m + 1 + j - (m + 1) - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      have: exists zs, arr_seq T prm (j - 1) r zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim=> [zs_T' H_arrseq_T_r_zs_T'].
      have H_arrseq_T_st''_zs_T': arr_seq T prm (j - 1) st'' zs_T'
        by apply arr_seq_subrgn with (b:=prm) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
        auto with zarith.
      exists zs_T'.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z3 H_prm0_z3 H_z3_j_1.
      rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
      rewrite st_upd_neq_loc; auto with zarith.
      
Qed.       
