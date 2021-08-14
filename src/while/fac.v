
From mathcomp Require Import ssreflect eqtype ssrbool seq.

Require Export Arith.
Require Export ZArith.
Require Export tactics.

Require Import sem.

Inductive id : Type := Id: nat -> id.

Definition eqid x1 x2 := 
  match x1 with
    Id n1 => match x2 with Id n2 => beq_nat n1 n2 end
  end.

Lemma eqidP : Equality.axiom eqid. 
Proof.
  move=>x1 x2.
  rewrite /eqid; apply: (iffP idP) => [|<-]; last first.
  - elim x1=>//; apply: Nat.eqb_refl.
  - elim: x1=> n. elim: x2=> n0.
    move=> H_eq. apply beq_nat_true in H_eq. 
    move: H_eq=>->=>//.
Qed.

Canonical id_eqMixin := EqMixin eqidP.
Canonical id_eqType := EqType id id_eqMixin. 

Inductive aexp : Type :=
  ANum: Z -> aexp |
  AVar: id -> aexp |
  AAdd: aexp -> aexp -> aexp |
  ASub: aexp -> aexp -> aexp |
  AMul: aexp -> aexp -> aexp
.

Inductive bexp : Type :=
  BConst: bool -> bexp |
  BEq: aexp -> aexp -> bexp |
  BLt: aexp -> aexp -> bexp |
  BNot: bexp -> bexp |
  BAnd: bexp -> bexp -> bexp
.

Definition state := (id -> Z). 

Fixpoint aval (a: aexp) (st: state) : Z :=
  match a with
    ANum z => z
  | AVar x => (st x)
  | AAdd a1 a2 => (aval a1 st) + (aval a2 st)
  | ASub a1 a2 => (aval a1 st) - (aval a2 st)
  | AMul a1 a2 => (aval a1 st) * (aval a2 st) 
  end.

Fixpoint bval (b: bexp) (st: state) : bool :=
  match b with
    BConst v => v
  | BEq a1 a2 => (Z.eqb (aval a1 st) (aval a2 st))
  | BLt a1 a2 => (Z.ltb (aval a1 st) (aval a2 st)) 
  | BNot b0 => if (bval b0 st) then false else true
  | BAnd b1 b2 =>
    if (bval b1 st) then
      (if (bval b2 st) then true else false)
    else false
  end. 

Inductive com : Type :=
  CmSkp: com |
  CmAssg: id -> aexp -> com |
  CmIf: bexp -> com -> com -> com |
  CmWh: bexp -> com -> com |
  CmSeq: com -> com -> com.

Definition wh_config := (prod com state).
Definition wh_rconfig := state.

Definition st_upd (s: state) x z :=
  (fun x' => (if (x == x') then z else (s x'))).

(* the semantic rules *) 
Inductive wh_rule :
  seq (prod wh_config wh_rconfig) -> (prod wh_config wh_rconfig) -> Prop :=
| WHR_SKP s: wh_rule [:: ] ((CmSkp, s), s)
| WHR_ASSG s x a: wh_rule [:: ] ((CmAssg x a, s), (st_upd s x (aval a s)))
| WHR_IFTT s s' b c1 c2:
    bval b s = true -> wh_rule [:: ((c1, s), s')] ((CmIf b c1 c2, s), s')
| WHR_IFFF s s' b c1 c2: 
    bval b s = false -> wh_rule [:: ((c2, s), s')] ((CmIf b c1 c2, s), s') 
| WHR_WHTT s s' s'' b c: 
    bval b s = true ->
    wh_rule [:: ((c, s), s''); ((CmWh b c, s''), s')] ((CmWh b c, s), s') 
| WHR_WHFF s b c:
    bval b s = false -> wh_rule [:: ] ((CmWh b c, s), s) 
| WHR_SEQ s s'' s' c1 c2: 
    wh_rule [:: ((c1, s), s''); ((c2, s''), s')] ((CmSeq c1 c2, s), s')
.

Instance wh_Sem : Sem wh_config wh_rconfig :=
  {
  rule := wh_rule
  }.


Lemma st_upd_eq: forall s x z, (st_upd s x z) x = z.
Proof. move=> s x z. rewrite /st_upd. elim: eqP=>//. Qed.

Lemma st_upd_neq: forall s x z x', x <> x' -> (st_upd s x z) x' = s x'.
Proof. move=> s x z x' H_neq. rewrite /st_upd. elim: eqP=>//. Qed. 


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

Ltac updsimp_h hyp :=
  repeat (
      first [
          rewrite st_upd_eq in hyp |
          rewrite st_upd_neq in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updsimp :=
  repeat (
      first [
          rewrite st_upd_eq |
          rewrite st_upd_neq; [| intro H_eq; inversion H_eq ]
        ]
    ).


(* the correctness proof *)
  
Theorem c0_spec_valid: forall param, valid _ (c0_spec param).
Proof.
  init_verif. 
  inversion H0; subst.
  -
    inversion H as [c r' crs H_rule H_all]; subst.
    inversion H_rule; subst.
    +
      ith_prem_exe_0 H_all H_i' c0_spec. 
      ith_prem_exe_0 h H_bd' c0_spec. 
      ith_prem_exe_1 h H_bd' c0_spec. 
      clear h0 h1.
      ith_prem_1 H_all H_all. 
      inversion H_all.
      exfalso. apply H2. eexists. eapply WH_SP_c_wh. updsimp.
      simpl in H4. apply Z.ltb_lt in H4. auto with zarith.
      inversion H2 as [P [H_spec H_Pr]].
      inversion H_spec; subst. 
      updsimp_h H5. inversion H_Pr; subst. updsimp_h H6.
      unfold c_wh_res. 
      have H_minus_one: (s m - 2)%Z = ((s m - 1) - 1)%Z
        by auto with zarith.
      rewrite <-facz_unfold; auto with zarith.
    +
      simpl in H4. apply Z.ltb_ge in H4.
      have H00: (r m = 1)%Z by auto with zarith.
      unfold c_wh_res. rewrite H00. simpl.
      unfold facz; simpl. auto with zarith.
  -
    inversion H; subst.
    inversion H4; subst.
    ith_prem_exe_0 H5 H5' c0_spec. clear h.
    ith_prem_1 H5 H5.
    inversion H5. inversion H2.
    exfalso. apply H3. eexists. eapply WH_SP_c_wh. updsimp; auto.
    inversion H2. inversion H3. rename x into P'.
    inversion H6; subst. inversion H7; subst.
    updsimp_h H10. 
    unfold c0_res. rewrite <-facz_unfold; auto.
Qed. 
