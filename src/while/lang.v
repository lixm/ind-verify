
From mathcomp Require Import ssreflect eqtype ssrbool seq.

Require Export Arith.
Require Export ZArith.

From indv Require Import sem tactics. 

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

