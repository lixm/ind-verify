
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

From indv Require Import arith sem. 

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

