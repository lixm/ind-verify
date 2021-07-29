
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

Require Import arith. 
Require Import tactics.
Require Import lists.
Require Import sem.

Definition id := nat.

Inductive expr : Type :=
  NE of Z
| BE of bool
| AddE of expr & expr
| SubE of expr & expr
| MulE of expr & expr
| DivE of expr & expr
| EqE of expr & expr
| LtE of expr & expr
| LeE of expr & expr 
| NegE of expr
| AndE of expr & expr
| IfE of expr & expr & expr
| NilE 
| PPendE of expr & expr
| LCaseE of expr & expr & expr
| VarE of id
| AppE of expr & expr
| AbsE of id & expr 
| LetRecE of id & expr & expr
.

Definition is_icfm (e: expr) :=
  match e with NE _ => true | _ => false end.

Definition is_bcfm (e: expr) :=
  match e with BE _ => true | _ => false end.

Definition is_fcfm (e: expr) :=
  match e with AbsE _ _ => true | _ => false end.

Fixpoint is_cfm (e: expr) :=
  match e with
    NE _ => true
  | BE _ => true
  | AbsE _ _ => true
  | NilE => true
  | PPendE e1 e2 => is_cfm e1 && is_cfm e2 
  | _ => false
  end.

Definition is_lcfm (e: expr) :=
  match e with
    NilE => true
  | PPendE e1 e2 => is_cfm e1 && is_cfm e2
  | _ => false  
  end.

Fixpoint is_zlcfm (e: expr) : bool :=
  match e with
    NilE => true
  | PPendE (NE z) e2 => is_zlcfm e2
  | _ => false
  end.

Definition fun_config := expr.
Definition fun_rconfig := expr.

Fixpoint e_subst (e: expr) (x: id) (e': expr) :=
  match e with
    NE z => NE z
  | BE b => BE b
  | AddE e1 e2 => AddE (e_subst e1 x e') (e_subst e2 x e')
  | SubE e1 e2 => SubE (e_subst e1 x e') (e_subst e2 x e')
  | MulE e1 e2 => MulE (e_subst e1 x e') (e_subst e2 x e')
  | DivE e1 e2 => DivE (e_subst e1 x e') (e_subst e2 x e')
  | EqE e1 e2 => EqE (e_subst e1 x e') (e_subst e2 x e')
  | LtE e1 e2 => LtE (e_subst e1 x e') (e_subst e2 x e')
  | LeE e1 e2 => LeE (e_subst e1 x e') (e_subst e2 x e')
  | NegE e1 => NegE (e_subst e1 x e')
  | AndE e1 e2 => AndE (e_subst e1 x e') (e_subst e2 x e')
  | IfE e1 e2 e3 =>
    IfE (e_subst e1 x e') (e_subst e2 x e') (e_subst e3 x e')
  | NilE => NilE
  | PPendE e1 e2 => PPendE (e_subst e1 x e') (e_subst e2 x e')
  | LCaseE e1 e2 e3 =>
    LCaseE (e_subst e1 x e') (e_subst e2 x e') (e_subst e3 x e')
  | VarE x' => if (x == x') then e' else (VarE x')
  | AppE e1 e2 => AppE (e_subst e1 x e') (e_subst e2 x e')
  | AbsE x' e1 => if (x == x') then (AbsE x' e1) else (AbsE x' (e_subst e1 x e'))
  (* letrec x1 = \lam x2.e2 in e1 *) 
  | LetRecE x1 e2 e1 =>
    let: e1' := (if x == x1 then e1 else (e_subst e1 x e')) in
    LetRecE x1 (e_subst e2 x e') e1'
  end.
  
Inductive fun_rule :
  seq (prod fun_config fun_rconfig) -> (prod fun_config fun_rconfig) -> Prop :=
  
| FUNR_NUM z: fun_rule [:: ] (NE z, NE z)
| FUNR_BOOL b: fun_rule [:: ] (BE b, BE b)
| FUNR_ADD e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (AddE e1 e2, NE (z1+z2)%Z)
| FUNR_SUB e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (SubE e1 e2, NE (z1-z2)%Z)
| FUNR_MUL e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (MulE e1 e2, NE (z1*z2)%Z)
| FUNR_DIV e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (DivE e1 e2, NE (z1/z2)%Z)
| FUNR_EQ e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (EqE e1 e2, BE (Z.eqb z1 z2))
| FUNR_LT e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (LtE e1 e2, BE (Z.ltb z1 z2))
| FUNR_LE e1 e2 z1 z2:
    fun_rule [:: (e1, NE z1); (e2, NE z2) ] (LeE e1 e2, BE (Z.leb z1 z2)) 
| FUNR_NEQ e1 b1:
    fun_rule [:: (e1, BE b1) ] (NegE e1, BE (~~b1))
| FUNR_AND e1 e2 b1 b2:
    fun_rule [:: (e1, BE b1); (e2, BE b2) ] (EqE e1 e2, BE (b1 && b2))
| FUNR_IFTT e1 e2 e3 cf:
    fun_rule [:: (e1, BE true); (e2, cf) ] (IfE e1 e2 e3, cf)
| FUNR_IFFF e1 e2 e3 cf:
    fun_rule [:: (e1, BE false); (e3, cf) ] (IfE e1 e2 e3, cf)
| FUNR_NIL: fun_rule [:: ] (NilE, NilE)
| FUNR_PPEND e e' cf cf':
    is_cfm cf -> is_cfm cf' -> 
    fun_rule [:: (e, cf); (e', cf') ] (PPendE e e', PPendE cf cf')
| FUNR_LCASE1 e e' e'' cf:
    is_cfm cf -> fun_rule [:: (e, NilE); (e', cf) ] (LCaseE e e' e'', cf)
| FUNR_LCASE2 e e' e'' cf cf' cf'':
    is_cfm cf -> is_cfm cf' -> is_cfm cf'' -> 
    fun_rule [:: (e, PPendE cf cf'); ((AppE (AppE e'' cf) cf'), cf'') ]
             (LCaseE e e' e'', cf'')
| FUNR_APP e e' e'' x cf cf':
    is_cfm cf -> is_cfm cf' ->
    fun_rule [:: (e, AbsE x e''); (e', cf'); (e_subst e'' x cf', cf) ]
             (AppE e e', cf)
| FUNR_ABS x e: fun_rule [:: ] (AbsE x e, AbsE x e)
| FUNR_LETREC e e' e'' x x' cf:
    e'' = (AbsE x' e') -> 
    x <> x' ->
    fun_rule [:: (AppE (AbsE x e) (AbsE x' (LetRecE x (AbsE x' e') e')), cf) ] 
             (LetRecE x e'' e, cf)
.

Instance fun_Sem : Sem fun_config fun_rconfig :=
  {
  rule := fun_rule
  }.


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


Ltac inv_zlcfm :=
  match goal with [ H : context [is_zlcfm _] |- _ ] => inv H end.
  
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

Lemma zlcfm_not_in_spec:
  forall lcf prm, is_zlcfm lcf -> ~(exists P, mg_spec prm lcf P).
Proof.
  move=> lcf prm H_zlcfm H_ex_P.
  inversion H_ex_P as [P H_spec_P]; clear H_ex_P.
  inv H_spec_P; subst;
  simpl in H_zlcfm; inv H_zlcfm.
Qed. 

Lemma zlcfm_infer_preserve:
  forall lcf cf param, 
    is_zlcfm lcf ->
    infer param (mg_spec param) (lcf, cf) ->
    cf = lcf. 
Proof.
  elim; try (move=> *; inv_zlcfm; fail).
  -
    move=> cf prm H_zlcfm H_inf. inv H_inf.
    inv H1; subst. auto.
  -
    move=> e IH1 e0 IH2 cf prm H_zlcfm H_inf.
    inversion H_zlcfm; subst.
    case En: e; rewrite En in H0; simpl in H0; inv H0. 
    inversion H_inf; subst.
    rename H3 into H_rule; inversion H_rule; subst.
    ith_prem_exe_0 H4 h' mg_spec. clear h.
    ith_prem_1 H4 H'.
    have: ~(exists P, mg_spec prm e0 P) by apply zlcfm_not_in_spec; auto.
    inversion H' as [H_ne | H_e]; clear H'.
    +
      move=> H_ne'. inv H_ne.
      move: IH2=>/(_ cf' prm H0)=>IH2. apply IH2 in H2. rewrite H2=>//.
    +
      move=> H_ne'. inv H_e. inv H.
      have H_ex: exists P, mg_spec prm e0 P. 
      { exists x; auto. }
      apply H_ne' in H_ex. inv H_ex.
Qed.

Lemma zlcfm_infer_nil:
  forall lcf param,
    is_zlcfm lcf ->
    infer param (mg_spec param) (lcf, NilE) ->
    lcf = NilE.
Proof.
  elim; try (move=> *; inv_zlcfm; fail).
  - try done.
  - move=> e IH1 e0 IH2 prm H_zlcfm H_inf.
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

Lemma zlcfm_infer_pend0: 
  forall lcf param cf cf', 
    is_zlcfm lcf -> 
    infer param (mg_spec param) (lcf, PPendE cf cf') ->
    exists z lcf'',
      lcf = PPendE (NE z) lcf'' /\
      cf = (NE z) /\ 
      cf' = lcf'' /\
      is_zlcfm lcf''.
Proof.
  elim; try (move=> *; inv_zlcfm; fail).
  -
    move=> param cf cf' H_zlcfm H_inf.
    inv H_inf. inv H1.
  -
    move=> e IH1 e0 IH2 prm cf cf' H_zlcfm H_inf.
    inversion H_zlcfm; subst.
    case En: e; rewrite En in H0; simpl in H0; inv H0.
    inversion H_inf; subst.
    inversion H3; subst.
    eexists. exists e0.
    apply: conj. eauto. apply: conj. 
    ith_prem_exe_0 H4 h' mg_spec; auto.
    ith_prem_1 H4 h'.
    have H_nex: ~(exists P, mg_spec prm e0 P)
      by apply zlcfm_not_in_spec; auto.
    have H_inf0: infer prm (mg_spec prm) (e0, cf')
      by get_branch h' H_nex.
    apply: conj.
    apply zlcfm_infer_preserve with (param:=prm); auto.
    auto.
Qed.

Lemma zlcfm_infer_pend: 
  forall lcf param cf cf', 
    is_zlcfm lcf -> 
    infer param (mg_spec param) (lcf, PPendE cf cf') ->
    exists z,
      lcf = PPendE (NE z) cf' /\
      cf = (NE z) /\ 
      is_zlcfm cf'.
Proof.
  move=> lcf prm cf cf' H_zlcfm H_inf.
  have H_ex0:
    exists z lcf'',
      lcf = PPendE (NE z) lcf'' /\
      cf = (NE z) /\ 
      cf' = lcf'' /\
      is_zlcfm lcf'' by apply zlcfm_infer_pend0 with (param:=prm); auto.
  inv H_ex0. inv H. inv H0. inv H2. inv H4.
  exists x. apply: conj. congruence. apply: conj=>//. congruence.
Qed.

Lemma inf_le_comp:
  forall z1 z2 prm b, 
    infer prm (mg_spec prm) (LeE (NE z1) (NE z2), BE b) ->
    (z1 <=? z2)%Z = b.
Proof.
  move=> z1 z2 prm b H_inf.
  inv H_inf; subst.
  inv H1; subst.
  ith_prem_0 H2 H2'.
  have H_inf1': infer prm (mg_spec prm) (NE z1, NE z0). 
  {
    have H_nex: ~(exists P, mg_spec prm (NE z1) P).
    { move=> contra. inv contra. inv H; subst. }
    get_branch H2' H_nex.
  }
  have H_z1_eq_z0: z1 = z0. 
  { inv H_inf1'; subst. inv H3; subst; auto. }
  rewrite <- H_z1_eq_z0 in *.
  clear H2'. clear H_inf1'.
  ith_prem_1 H2 H2'.
  have H_inf2': infer prm (mg_spec prm) (NE z2, NE z3).
  {
    have H_nex: ~(exists P, mg_spec prm (NE z2) P).
    { move=> contra. inv contra. inv H; subst. }
    get_branch H2' H_nex.
  }
  have H_z3_eq_z2: z2 = z3.
  { inv H_inf2'; subst. inv H3; subst; auto. }
  rewrite <- H_z3_eq_z2 in *.
  done.
Qed.

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


(* the correctness proof *) 

Theorem mg_spec_valid: forall param, valid _ (mg_spec param).
Proof.
  init_verif. 
  inversion H0; subst.
  
  - (* proof for overall expression *)
    rename H1 into H_lcfm_lcf1. rename H2 into H_lcfm_lcf2.
    rename H5 into H_sorted_lcf1. rename H6 into H_sorted_lcf2.
    inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst. clear H_rule.
    rename H4 into H_abs_eq.
    inversion H_abs_eq; subst.
    clear H_abs_eq.
    
    ith_prem_exe_0 H_all H' mg_spec.
    ith_prem_exe_0 h h' mg_spec. clear h0.
    ith_prem_exe_1 h h' mg_spec. clear h0.
    
    simpl in h. repeat rewrite zlcfm_subst in h; auto.
    ith_prem_2 h h'.
    inversion h' as [H_nex_P | H_exP]; clear h'.
    +  (* refute that there is no info about the expr *)
      exfalso. apply H_nex_P.
      eexists.
      apply FUN_SP_e_unfold
        with (lcf1:=lcf1) (lcf2:=lcf2) (zs1:=lcf_seq lcf1) (zs2:=lcf_seq lcf2);
        auto.
    +  (* there is some info about the expr in the spec *)
      inversion H_exP as [P [H_spec_P H_P_r]]; clear H_exP.
      inv H_spec_P; subst.
      auto.
      
  - (* proof for the unfolded expression *)
    rename H1 into H_lcfm_lcf1. rename H2 into H_lcfm_lcf2.
    rename H5 into H_sorted_lcf1. rename H6 into H_sorted_lcf2.
    inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst. clear H_rule.

    ith_prem_exe_0 H_all H' mg_spec.
    ith_prem_exe_0 h h' mg_spec. clear h0.
    ith_prem_1 h h'.
    inversion h' as [H_nexP | H_exP]; clear h'.
    2: {
      have H_nex: ~(exists P, mg_spec param lcf1 P) by apply zlcfm_not_in_spec; auto.
      inv H_exP. inv H1. exfalso. apply H_nex. exists x0; auto.
    }
    inversion H_nexP as [H_nexP0  H_infer]; clear H_nexP.
    have H_cf'0_eq_lcf1: cf'0 = lcf1 by eapply zlcfm_infer_preserve; eauto.
    symmetry in H_cf'0_eq_lcf1. rewrite <- H_cf'0_eq_lcf1 in *.
    ith_prem_exe_2 h h' mg_spec.
    rename H7 into H_abs_eq. inv H_abs_eq; subst.
    ith_prem_exe_0 h0 h' mg_spec.
    ith_prem_exe_0 h1 h' mg_spec. clear h2.
    ith_prem_exe_1 h1 h' mg_spec. clear h2.
    ith_prem_exe_2 h1 h' mg_spec. clear h2.
    rename H7 into H_is_cfm_abs. clear H_is_cfm_abs.
    rename H10 into H_is_cfm_abs. clear H_is_cfm_abs.
    clear h1. clear h0. 
    rename H5 into H_is_cfm_abs. clear H_is_cfm_abs.
    clear H_infer. clear H_nexP0. clear H_abs_eq.
    
    ith_prem_1 H_all H'.
    inversion H' as [H_nexP | H_exP]; clear H'.
    2: {
      have H_nex: ~(exists P, mg_spec param lcf2 P) by apply zlcfm_not_in_spec; auto.
      inv H_exP. inv H1. exfalso. apply H_nex. exists x; auto.
    }
    inversion H_nexP as [H_nex H_infer]; clear H_nexP.
    have H_cf'_eq_lcf2: cf' = lcf2 by eapply zlcfm_infer_preserve; eauto.
    symmetry in H_cf'_eq_lcf2. rewrite <- H_cf'_eq_lcf2 in *.
    ith_prem_2 H_all H'.
    inversion H' as [H_nexP | H_exP]; clear H'.
    2: { inv H_exP. inv H1. inv H2. }
    repeat rewrite zlcfm_subst in H_nexP; auto.
    2: { rewrite zlcfm_subst; auto. }
    clear H_nex. clear H_infer.
    inversion H_nexP as [H_nex H_infer]; clear H_nexP.
    rename cf'0 into lcf1.

    inversion H_infer as [c0 r0 crs0 H_rule_lcase H_all'].
    rename H1 into H_c0_eq_. clear c0 H_c0_eq_.
    rename H2 into H_r0_eq_. clear r0 H_r0_eq_. 
    clear H_nex.
    inv H_rule_lcase; subst.
    
    +  (* first list is NilE *) 
      ith_prem_0 H_all' h'.
      have H_nex: ~(exists P, mg_spec param lcf1 P) by eapply zlcfm_not_in_spec; eauto.
      have H_inf:  infer param (mg_spec param) (lcf1, NilE). 
      { inv h'. inv H1; auto. inv H1. inv H2. exfalso. apply H_nex. exists x; auto. }
      clear h'. clear H_nex. 
      have H_lcf1_nil: lcf1 = NilE by eapply zlcfm_infer_nil; eauto.
      ith_prem_1 H_all' h'.
      have H_nex: ~(exists P, mg_spec param cf' P) by eapply zlcfm_not_in_spec; eauto.      
      have H_inf': infer param (mg_spec param) (cf', r) by get_branch h' H_nex.    
      have H_r_eq_cf': r = cf'. eapply zlcfm_infer_preserve; eauto.
      symmetry in H_r_eq_cf'. rewrite <- H_r_eq_cf' in *.
      rewrite H_lcf1_nil. simpl.
      apply: conj=>//.

    + (* first list is not NilE *)
      ith_prem_0 H_all' h'.
      have H_nex: ~ (exists P, mg_spec param lcf1 P) by eapply zlcfm_not_in_spec; eauto.
      have H_inf: infer param (mg_spec param) (lcf1, PPendE cf cf'0)
        by get_branch h' H_nex.
      apply zlcfm_infer_pend in H_inf; auto.
      inversion H_inf as [z1 [H_lcf1_eq_pend [H_cf_ne H_zlcfm_cf'0]]]; clear H_inf.
      symmetry in H_lcf1_eq_pend. rewrite <- H_lcf1_eq_pend in *.
      symmetry in H_cf_ne. rewrite <- H_cf_ne in *.
      clear h'. clear H_nex.
      ith_prem_exe_1 H_all' h' mg_spec.
      ith_prem_exe_0 h0 h' mg_spec.
      ith_prem_exe_0 h1 h' mg_spec. clear h2.
      ith_prem_exe_1 h1 h' mg_spec. 
      ith_prem_exe_2 h1 h' mg_spec. clear h3. clear h2. clear h1.
      rename H9 into H_is_cfm_abs. clear H_is_cfm_abs.
      (* clear H1. clear H2. *) clear H15. 
      ith_prem_1 h0 h'.
      have H_nex: ~(exists P, mg_spec param cf'0 P)
        by apply zlcfm_not_in_spec; auto.
      have H_inf: infer param (mg_spec param) (cf'0, cf'1) by get_branch h' H_nex. 
      have H_cf'0_eq_cf'1: cf'1 = cf'0
        by apply zlcfm_infer_preserve with (param:=param); auto.
      rewrite <- H_cf'0_eq_cf'1 in *.
      (* cf'1 is the tail of the first list *)
      rewrite zlcfm_subst in h0; auto.
      rewrite zlcfm_subst in h0; auto.
      rename cf' into lcf2.
      clear H_nex h'.
      ith_prem_exe_2 h0 h' mg_spec.

      * (* second list is NilE *)
        ith_prem_0 h1 h'.
        have H_nex: ~(exists P, mg_spec param lcf2 P)
          by apply zlcfm_not_in_spec; auto.
        clear H_inf.
        rewrite zlcfm_subst in h'; auto.
        have H_inf: infer param (mg_spec param) (lcf2, NilE)
          by get_branch h' H_nex. 
        have H_lcf2_nil: lcf2 = NilE
          by apply zlcfm_infer_nil with (param:=param); auto.
        rewrite H_lcf2_nil.
        
        clear H_nex. ith_prem_exe_1 h1 h1' mg_spec.
        ith_prem_exe_0 h2 h2' mg_spec. clear h3.
        ith_prem_1 h2 h2'.
        clear H_inf.
        rewrite zlcfm_subst in h2'; auto.
        have H_nex: (~exists P, mg_spec param cf'0 P)
          by apply zlcfm_not_in_spec; auto.
        have H_inf: infer param (mg_spec param) (cf'0, cf')
          by get_branch h2' H_nex.
        have H_cf'_eq_cf'0: cf' = cf'0
          by apply zlcfm_infer_preserve with (param:=param); auto.
        rewrite H_cf'_eq_cf'0.
        apply: conj.
        (* is_zlcfm (PPendE (NE z1) cf'0) *)
        simpl; auto.
        (* goal with occ *)
        apply: conj. move=> z.
        have: occ (lcf_seq NilE) z = 0 by simpl; auto.
        move->. rewrite add_zero. auto.
        (* sorted ... *)
        assumption.

      * (* second list is not NilE *)
        ith_prem_0 h1 h1'.
        rewrite zlcfm_subst in h1'; auto.
        have H_nex: ~(exists P, mg_spec param lcf2 P)
          by apply zlcfm_not_in_spec; auto.
        clear H_inf.
        have H_inf: infer param (mg_spec param) (lcf2, PPendE cf cf').
        get_branch h1' H_nex.
        apply zlcfm_infer_pend in H_inf; auto.
        inversion H_inf as [z2 [H_lcf2_eq_ [H_cf_eq_ H_zlcfm_cf']]];
          clear H_inf.
        subst. clear H_nex.
        ith_prem_exe_2 h0 h0' mg_spec.
        ith_prem_0 h2 h2'.
        inv h2'. inv H1. inv H9. inv H19.
        inv H1. inv H2. inv H9.
        rewrite zlcfm_subst in h2; auto.
        ith_prem_exe_0 h2 h2' mg_spec.
        ith_prem_0 h3 h3'.
        have H_nex: ~(exists P, mg_spec param (NE z2) P)
          by intro contra; inv contra; inv H1.
        have H_inf: infer param (mg_spec param) (NE z2, cf)
          by get_branch h3' H_nex.
        have H_ne_z2_eq_cf: NE z2 = cf.
        { inversion H_inf; subst. inv H3; subst; auto. }
        rewrite <- H_ne_z2_eq_cf in *.
        clear h3'. clear H_nex. clear H_inf.
        ith_prem_1 h3 h3'.
        have H_nex: ~(exists P, mg_spec param cf' P)
          by apply zlcfm_not_in_spec; auto.
        have H_inf: infer param (mg_spec param) (cf', cf'1) 
          by get_branch h3' H_nex.
        have H_cf'_1_eq_cf': cf'1 = cf'.
        apply zlcfm_infer_preserve with (param:=param); auto.
        symmetry in H_cf'_1_eq_cf'. rewrite <- H_cf'_1_eq_cf' in *.
        clear H_nex H_inf.
        clear H_ne_z2_eq_cf H_cf'_1_eq_cf'. clear h3'.
        rename H9 into H_is_cfm_ne_z2. clear H_is_cfm_ne_z2.
        clear h3.
        ith_prem_exe_1 h2 h2' mg_spec.
        ith_prem_exe_0 h3 h3' mg_spec.
        ith_prem_exe_0 h4 h4' mg_spec. clear h5.
        ith_prem_1 h4 h4'.
        have H_nex: ~(exists P, mg_spec param (NE z2) P).
        { intro contra. inv contra. inv H1. }
        have H_inf: infer param (mg_spec param) (NE z2, cf'3)
          by get_branch h4' H_nex.
        have H_cf'3_eq_ne_z2: NE z2 = cf'3.
        { inv H_inf; subst. inv H3; subst; auto. }
        rewrite <- H_cf'3_eq_ne_z2 in *. clear H_cf'3_eq_ne_z2.
        clear h4' H_inf H_nex.
        ith_prem_exe_2 h4 h4' mg_spec. clear h5.
        rename H18 into H_is_cfm_abs. clear H_is_cfm_abs.
        clear h4.
        ith_prem_2 h3 h3'. 
        inversion h3' as [H_nexP | H_exP]. 
        2: { inv H_exP. inv H1. inv H2. }
        inversion H_nexP as [H_nex H_inf]. clear H_nex.
        repeat (rewrite zlcfm_subst in H_inf; auto;
                [ | try (rewrite zlcfm_subst; auto)]).
        (* H_inf is about the inf result of the if expression *) 
        inversion H_inf; subst.
        rename H3 into H_rule_if.
        inversion H_rule_if; subst.

        (* the true branch for the if expression *)
        rename H18 into H_forall_true.
        ith_prem_0 H_forall_true h'.
        have H_inf_tt: infer param (mg_spec param) (LeE (NE z1) (NE z2), BE true).
        {
          have H_nex: ~(exists P, mg_spec param (LeE (NE z1) (NE z2)) P).
          { intro contra. inv contra. inv H1. }
          get_branch h' H_nex. 
        }
        apply inf_le_comp in H_inf_tt.
        clear h'.
        ith_prem_exe_1 H_forall_true h' mg_spec.
        ith_prem_exe_0 h4 h4' mg_spec.         
        ith_prem_1 h4 h4'.
        fold e_lcase in h4'.
        rewrite zlcfm_subst in h4'; auto.
        rewrite zlcfm_subst in h4'; auto; [ | try (rewrite zlcfm_subst; auto)].
        rewrite zlcfm_subst in h4'; auto.
        clear H_nexP. 
        inversion h4' as [H_nexP | H_exP]; clear h4'.
        (* refute that there is no info in the spec *)
        inv H_nexP.
        exfalso. apply H1.
        eexists.
        apply FUN_SP_e_unfold
          with (lcf1:=cf'0) (lcf2:=PPendE (NE z2) cf')
               (zs1:=lcf_seq cf'0) (zs2:=lcf_seq (PPendE (NE z2) cf'));
          eauto.
        (* goal on the sortedness of tail of first list *)
        simpl in H_sorted_lcf1.
        apply sorted_tail in H_sorted_lcf1; auto.
        
        (* there is some info in the spec *)
        inversion H_exP as [P H_mg_spec]; clear H_exP.
        inversion H_mg_spec as [H_spec_P H_P_cf'4]; clear H_mg_spec.
        inv H_spec_P; subst. clear H_spec_P.
        inversion H_P_cf'4 as [H_zlcfm_cf'4 [H_occ H_sorted]]; clear H_P_cf'4.
        apply: conj. simpl; auto. (* goal with is_zlcfm *)
        apply: conj.
        (* goal with occ *)
        move=> z. specialize (H_occ z).
        simpl in H_occ. simpl. rewrite H_occ. 
        case En: (z1 =? z)%Z; case En': (z2 =? z)%Z;
          auto with zarith.
        (* goal on sortedness *)
        simpl.
        have H_cf'4_cases: cf'4 = NilE \/ exists z cf', cf'4 = PPendE (NE z) cf'
              by apply zlcfm_shape; auto.
        inversion H_cf'4_cases as [H_nil | H_n_nil]; clear H_cf'4_cases.
        rewrite H_nil. simpl. apply singleton_sorted.
        inversion H_n_nil as [z0 [cf'' H_cf'4_eq]]; clear H_n_nil.
        have H_corr:
          size (lcf_seq cf'0) > 0 /\ nth 0%Z (lcf_seq cf'4) 0 = nth 0%Z (lcf_seq cf'0) 0 \/
          size (lcf_seq (PPendE (NE z2) cf')) > 0 /\
          nth 0%Z (lcf_seq cf'4) 0 = nth 0%Z (lcf_seq (PPendE (NE z2) cf')) 0.
        {
          apply occ_sorted_hd_corr; auto with zarith.
          rewrite H_cf'4_eq. simpl. auto.
        }
        have H_simp: nth 0%Z (lcf_seq cf'4) 0 = z0 by rewrite H_cf'4_eq=>//=. 
        rewrite H_simp in H_corr.
        inversion H_corr as [H_l_first | H_r_first]; clear H_corr.
        (* head ele of new list is head ele of first list *)
        inversion H_l_first as [H_sz_cf'0 H_z0_eq_]; clear H_l_first.
        have H_z1_le_: (z1 <= nth 0%Z (lcf_seq cf'0) 0)%Z.
        { apply sorted_hd_nxt; auto with zarith. }
        rewrite <- H_z0_eq_ in H_z1_le_. rewrite <- H_simp in H_z1_le_.
        have: z1 :: lcf_seq cf'4 = [:: z1] ++ lcf_seq cf'4 by auto.
        move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted. 
        have: size [:: z1] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z1] 0 = z1 by auto. move->.
        auto with zarith.
        (* head ele of new list if head ele of second list *)
        inversion H_r_first as [H_sz_ H_z0_eq_]; clear H_r_first.
        have H_z1_le_: (z1 <= z2)%Z by apply Zle_bool_imp_le; auto.
        simpl in H_z0_eq_. rewrite <- H_z0_eq_ in *.
        have: z1 :: lcf_seq cf'4 = [:: z1] ++ lcf_seq cf'4 by auto.
        move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted.
        have: size [:: z1] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z1] 0 = z1 by auto. move->.
        auto with zarith.
        
        (* the false branch for the if expression *)
        have H_cf'2_eq_cf': cf'2 = cf'.
        {
          ith_prem_1 h3 h3''.
          have H_nex: ~(exists P, mg_spec param cf' P) 
            by apply zlcfm_not_in_spec; auto.
          have H_inf': infer param (mg_spec param) (cf', cf'2)
            by get_branch h3'' H_nex.
          apply zlcfm_infer_preserve with (param:=param); auto.
        }
        symmetry in H_cf'2_eq_cf'. rewrite <- H_cf'2_eq_cf' in *.
        move: H_cf'2_eq_cf'.
        rename H18 into H_forall_false.
        ith_prem_0 H_forall_false h'.
        have H_inf_ff: infer param (mg_spec param) (LeE (NE z1) (NE z2), BE false).
        {
          have H_nex: ~(exists P, mg_spec param (LeE (NE z1) (NE z2)) P).
          { intro contra. inv contra. inv H1. }
          get_branch h' H_nex. 
        }
        apply inf_le_comp in H_inf_ff.
        clear h'.
        ith_prem_exe_1 H_forall_false h' mg_spec.
        ith_prem_exe_0 h4 h4' mg_spec.
        ith_prem_1 h4 h4'.
        fold e_lcase in h4'.
        rewrite zlcfm_subst in h4'; auto. 2: { repeat rewrite zlcfm_subst; auto. }
        rewrite zlcfm_subst in h4'; auto. 2: { rewrite zlcfm_subst; auto. }
        rewrite zlcfm_subst in h4'; auto.
        clear H_nexP. 
        inversion h4' as [H_nexP | H_exP]; clear h4'.
        (* refute that there is no info in the spec *)
        inv H_nexP.
        exfalso. apply H1.
        eexists.
        apply FUN_SP_e_unfold
          with (lcf1:=(PPendE (NE z1) cf'0)) (lcf2:=cf')
               (zs1:=lcf_seq (PPendE (NE z1) cf'0)) (zs2:=lcf_seq cf');
          eauto.
        (* goal on the sortedness of tail of first list *)
        simpl in H_sorted_lcf2. 
        apply sorted_tail in H_sorted_lcf2; auto.

        (* there is some info in the spec *)
        move=> H'. move=> {H'}.
        inversion H_exP as [P H_mg_spec]; clear H_exP.
        inversion H_mg_spec as [H_spec_P H_P_cf'4]; clear H_mg_spec.
        inv H_spec_P; subst. clear H_spec_P.
        inversion H_P_cf'4 as [H_zlcfm_cf'4 [H_occ H_sorted]]; clear H_P_cf'4.
        apply: conj. simpl; auto. (* goal with is_zlcfm *)
        apply: conj.
        (* goal on occ *)
        move=> z. specialize (H_occ z).
        simpl in H_occ. simpl. rewrite H_occ.
        rewrite [(z2 =? z)%Z + ((z1 =? z)%Z + _ + _)]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + ((z1 =? z)%Z + _))%coq_nat]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + (z1 =? z)%Z)%coq_nat]Nat.add_comm.
        rewrite -[(((z1 =? z)%Z + (z2 =? z)%Z)%coq_nat + _)%coq_nat]Nat.add_assoc.
        rewrite [((z2 =? z)%Z + occ (lcf_seq cf'0) z)%coq_nat]Nat.add_comm.
        rewrite [((z1 =? z)%Z + (_ + (z2 =? z)%Z)%coq_nat)%coq_nat]Nat.add_assoc.
        auto with arith.
        (* goal on sortedness *)
        simpl.
        have H_cf'4_cases: cf'4 = NilE \/ exists z cf', cf'4 = PPendE (NE z) cf'
              by apply zlcfm_shape; auto.
        inversion H_cf'4_cases as [H_nil | H_n_nil]; clear H_cf'4_cases.
        rewrite H_nil. simpl. apply singleton_sorted.
        inversion H_n_nil as [z0 [cf'' H_cf'4_eq]]; clear H_n_nil.
        have H_corr:
          size (lcf_seq (PPendE (NE z1) cf'0)) > 0 /\
          nth 0%Z (lcf_seq cf'4) 0 = nth 0%Z (lcf_seq (PPendE (NE z1) cf'0)) 0 \/
          size (lcf_seq cf') > 0 /\
          nth 0%Z (lcf_seq cf'4) 0 = nth 0%Z (lcf_seq cf') 0.
        {
          apply occ_sorted_hd_corr; auto with zarith.
          rewrite H_cf'4_eq. simpl. auto.
        }
        have H_simp: nth 0%Z (lcf_seq cf'4) 0 = z0 by rewrite H_cf'4_eq=>//=. 
        rewrite H_simp in H_corr.
        inversion H_corr as [H_l_first | H_r_first]; clear H_corr.
        (* head ele of new list is head ele of first list *)
        inversion H_l_first as [H_sz_ H_z0_eq_]; clear H_l_first.
        have H_z2_lt_: (z2 < z1)%Z by apply Z.leb_gt; auto.
        have H_z2_le_: (z2 <= z1)%Z by auto with zarith.
        simpl in H_z0_eq_. symmetry in H_z0_eq_. rewrite <- H_z0_eq_ in *.
        have: z2 :: lcf_seq cf'4 = [:: z2] ++ lcf_seq cf'4 by auto.
        move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted.
        have: size [:: z2] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z2] 0 = z2 by auto. move->.
        auto with zarith.
        (* head ele of new list is head ele of second list *)
        inversion H_r_first as [H_sz_cf'0 H_z0_eq_]; clear H_r_first.
        have H_z2_le_: (z2 <= nth 0%Z (lcf_seq cf') 0)%Z.
        { apply sorted_hd_nxt; auto with zarith. }
        rewrite <- H_z0_eq_ in H_z2_le_. rewrite <- H_simp in H_z2_le_.
        have: z2 :: lcf_seq cf'4 = [:: z2] ++ lcf_seq cf'4 by auto.
        move->.
        apply sorted_concat; auto with zarith. apply singleton_sorted. 
        have: size [:: z2] - 1 = 0 by auto with arith. move->.
        have: nth 0%Z [:: z2] 0 = z2 by auto. move->.
        auto with zarith.

Qed.
