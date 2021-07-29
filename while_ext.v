
Require Import Coq.Program.Basics. 
Require Import FunctionalExtensionality.
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq. 

Require Import tactics.
Require Import arith. 
Require Import lists. 
Require Import sem.

Definition var_id : Type := nat. 
Definition arr_id : Type := nat.
Definition fun_id : Type := nat.

Inductive aexp : Type :=
  ANum of Z |
  AVar of var_id |
  AArr of arr_id | 
  AARef of aexp & aexp | 
  AAdd of aexp & aexp |
  ASub of aexp & aexp |
  AMul of aexp & aexp |
  ADiv of aexp & aexp
.

Inductive bexp : Type :=
  BConst of bool |
  BEq of aexp & aexp |
  BLt of aexp & aexp |
  BLe of aexp & aexp | 
  BNot of bexp |
  BAnd of bexp & bexp 
.

Inductive com : Type :=
  CmVarDecl of var_id |
  CmArrDecl of arr_id & nat |
  CmSkp |
  CmAssg of var_id & aexp |
  CmArrAssg of arr_id & aexp & aexp | 
  CmIf of bexp & com & com |
  CmWh of bexp & com |
  CmSeq of com & com |
  CmCall of fun_id & seq aexp & seq var_id 
.

Notation "cm1 ;; cm2" := 
  (CmSeq cm1 cm2) (at level 80, right associativity).

Inductive param : Type :=
  VarParam of var_id | ArrParam of arr_id. 

Definition func : Type :=
  (seq param) * (seq var_id) * com. 

Definition prog : Type := fun_id -> (option func).

Definition eqpm pm1 pm2 := 
  match pm1 with
    VarParam x => (
      match pm2 with
        VarParam x' => x == x'
      | _ => false
      end)
  | ArrParam X => (
      match pm2 with
        ArrParam X' => X == X'
      | _ => false
      end)
  end.

Lemma eqpmP : Equality.axiom eqpm. 
Proof.
  move=>pm1 pm2.
  rewrite /eqpm. apply: (iffP idP).
  - 
    case En1: pm1=> [x1 | X1]; 
    case En2: pm2=> [x2 | X2]=>//;
    move /eqP=>->=>//.
  -
    move->. case En: pm2=> [x | X]; apply: eq_refl. 
Qed.

Canonical pm_eqMixin := EqMixin eqpmP.
Canonical pm_eqType := EqType param pm_eqMixin. 


(* SEMANTICS *) 

Definition var_state: Type := var_id -> (option Z).
Definition arr_state: Type := var_id -> (option Z).
Definition loc_state: Type := Z -> Z.

Definition store: Type := var_state * arr_state * loc_state.
Definition varst_of (st : store) := fst (fst st).
Definition arrst_of (st : store) := snd (fst st).
Definition locst_of (st : store) := snd st.

(* the integer is the next fresh location for an array in the stack *)
Definition state: Type := store * Z. 
Definition store_of (st : state) := fst st.
Definition floc_of (st : state) := snd st.

Definition stt_v: state -> var_state :=
  compose varst_of store_of. 
Definition stt_a: state -> arr_state :=
  compose arrst_of store_of.
Definition stt_l: state -> loc_state :=
  compose locst_of store_of. 

Fixpoint aval (a: aexp) (st: state) : option Z :=
  match a with
    ANum z => Some z
  | AVar x => stt_v st x
  | AArr X => stt_a st X
  | AARef a1 a2 => (
      match aval a1 st with
        Some l => (
          match aval a2 st with
            Some z => (
              if (z >=? 0)%Z && ((l + z) <? floc_of st)%Z then
                Some (stt_l st (Z.add l z))
              else
                None
            )
          | None => None
          end)
      | None => None
      end)
  | AAdd a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.add z1 z2) else None)
      | None => None
      end )
  | ASub a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.sub z1 z2) else None)
      | None => None
      end
    ) 
  | AMul a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.mul z1 z2) else None)
      | None => None
      end
    )
  | ADiv a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.div z1 z2) else None) 
      | None => None
      end      
    )
  end.

Fixpoint bval (b: bexp) (st: state) : option bool :=
  match b with
    BConst v => Some v
  | BEq a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.eqb z1 z2) else None)
      | _ => None
      end)
  | BLt a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.ltb z1 z2) else None)
      | _ => None
      end)
  | BLe a1 a2 => (
      match aval a1 st with
        Some z1 => (if aval a2 st is Some z2 then Some (Z.leb z1 z2) else None)
      | _ => None
      end)
  | BNot b0 => (
      match bval b0 st with
        Some true => Some false
      | Some false => Some true
      | None => None
      end) 
  | BAnd b1 b2 => (
      match bval b1 st with
        Some t1 => (
          match bval b2 st with
            Some t2 => Some (andb t1 t2)
          | None => None
          end) 
      | None => None 
      end) 
  end. 

Definition varst_upd (vst: var_state) (x: var_id) (z: Z) : var_state :=
  (fun x' => if x' == x then (Some z) else vst x').

Definition arrst_upd (ast: arr_state) (X: arr_id) (l: Z) : arr_state :=
  (fun X' => if X' == X then (Some l) else ast X').

Definition locst_upd (locst: loc_state) (l: Z) (z: Z) : loc_state :=
  (fun l' => if Z.eqb l l' then z else locst l'). 
  
Definition st_upd_var (st: store) (x: var_id) (z: Z) :=
  (varst_upd (varst_of st) x z, arrst_of st, locst_of st).

Definition st_upd_arr (st: store) (X: arr_id) (l: Z) :=
  (varst_of st, arrst_upd (arrst_of st) X l, locst_of st).

Definition st_upd_loc (st: store) (l: Z) (z: Z) :=
  (varst_of st, arrst_of st, locst_upd (locst_of st) l z).

Definition state_upd_var (st: state) x z :=
  (st_upd_var (store_of st) x z, floc_of st).

Definition state_upd_arr (st: state) X l :=
  (st_upd_arr (store_of st) X l, floc_of st).

Definition state_upd_loc (st: state) l z :=
  (st_upd_loc (store_of st) l z, floc_of st). 

Definition waf_config := (prod (prod com state) prog).
Definition waf_rconfig := state.

Eval compute in (find (fun (x: nat) => x == 3) [:: 4; 3; 1]).
Eval compute in (index (VarParam 0) [:: (VarParam 3)]). 

Definition call_ini
           (st: store) (ws: seq param) (vs: seq Z) (xs: seq var_id)
           : store
  :=
    (
      (fun x => (
          let idx := index (VarParam x) ws in
          if idx < size ws then Some (nth (0%Z) vs idx) else
            let idx' := index x xs in
            if idx < size xs then Some (0%Z) else None 
      )),
      (fun X => (
           let idx := index (ArrParam X) ws in
           if idx < size ws then Some (nth (0%Z) vs idx) else None
      )),
      (locst_of st)
    ).

Definition call_fin (st st': store) (xs xs': seq var_id) : store
  :=
    (
      (fun x' => (
           let idx := index x' xs' in
           if idx < size xs' then (varst_of st') (nth 0 xs idx) else varst_of st x')), 
      (arrst_of st),
      (locst_of st') 
    ). 

Inductive waf_rule :
  seq (prod waf_config waf_rconfig) -> (prod waf_config waf_rconfig) -> Prop :=
  
| WAFR_SKP p st: waf_rule [:: ] ((CmSkp, st, p), st)
| WAFR_VDECL p st x:
    stt_v st x = None -> 
    waf_rule [:: ] ((CmVarDecl x, st, p), (state_upd_var st x 0))
| WAFR_ADECL p st X n:
    stt_a st X = None -> 
    waf_rule [:: ]
             ((CmArrDecl X n, st, p),
              (st_upd_arr (store_of st) X (floc_of st),
               Z.add (floc_of st)  (Z.of_nat n)))
| WAFR_ASSG p st x a z:
    stt_v st x <> None ->
    aval a st = Some z -> 
    waf_rule [:: ]
             ((CmAssg x a, st, p), (state_upd_var st x z))
| WAFR_ARRASSG p st X a1 a2 z1 z2 l:
    stt_a st X = Some l ->
    aval a1 st = Some z1 -> aval a2 st = Some z2 ->
    Z.ge z1 0 -> (l + z1 <? (floc_of st))%Z -> 
    waf_rule [:: ]
             ((CmArrAssg X a1 a2, st, p),
              (state_upd_loc st (l + z1) z2))
| WAFR_IFTT p st b cm1 cm2 st':
    bval b st = Some true ->
    waf_rule [:: ((cm1, st, p), st') ] ((CmIf b cm1 cm2, st, p), st')
| WAFR_IFFF p st b cm1 cm2 st':
    bval b st = Some false ->
    waf_rule [:: ((cm2, st, p), st') ] ((CmIf b cm1 cm2, st, p), st')
| WAFR_WHTT p st b cm st'' st':
    bval b st = Some true ->
    waf_rule [:: ((cm, st, p), st''); ((CmWh b cm, st'', p), st') ]
             ((CmWh b cm, st, p), st')
| WAFR_WHFF p st b cm:
    bval b st = Some false ->
    waf_rule [:: ] ((CmWh b cm, st, p), st)
| WAFR_SEQ p cm1 cm2 st st'' st':
    waf_rule [:: ((cm1, st, p), st''); ((cm2, st'', p), st') ]
             ((CmSeq cm1 cm2, st, p), st')
| WAFR_FCALL (p:prog) st st0' f aes ws xs xs' vals cm s' s'': 
    p f = Some (ws, xs', cm) ->
    (forall i, i < size aes ->
               (aval (nth (ANum 0) aes i) st = Some (nth (0%Z) vals i))) ->
    size ws = size vals -> 
    call_ini (store_of st) ws vals xs' = s'' ->
    s' = call_fin (store_of st) (store_of st0') xs xs' -> 
    waf_rule [:: ((cm, (s'', floc_of st), p), st0') ]
             ((CmCall f aes xs, st, p), (s', floc_of st)) 
. 


Instance waf_Sem : Sem waf_config waf_rconfig :=
  {
  rule := waf_rule
  }.


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
  
Definition arr_seq (X: arr_id) (b e: Z) (st: state) (zs: seq Z) : Prop :=
  (e < b)%Z /\ zs = [:: ] \/
  ((0<= b <= e)%Z /\ 
   (exists (b' e': nat) (l: Z),
       b' = (Z.to_nat b) /\ e' = (Z.to_nat e) /\
       arrst_of (store_of st) X = Some l /\
       size zs = e' - b' + 1 /\
       (forall i, b' <= i <= e' ->
                  stt_l st (Z.add l (Z.of_nat i)) = nth (0%Z) zs (i-b')))). 

Definition sep X1 l1 h1 X2 l2 h2 (st: state) : Prop :=
  exists loc1 loc2,
    stt_a st X1 = Some loc1 /\ 
    stt_a st X2 = Some loc2 /\ 
    ((loc1 + h1 < loc2 + l2)%Z \/ (loc2 + h2 < loc1 + l1)%Z).

Lemma sep_ex_loc_1:
  forall X1 l1 h1 X2 l2 h2 st, 
    sep X1 l1 h1 X2 l2 h2 st ->
    exists l, stt_a st X1 = Some l.
Proof.
  move=> X1 l1 h1 X2 l2 h2 st.
  move=> H_sep.
  rewrite /sep in H_sep.
  inversion H_sep as [loc1 [loc2 [H_loc1 [H_loc2 H_or]]]].
  exists loc1; auto.
Qed. 

Lemma sep_ex_loc_2:
  forall X1 l1 h1 X2 l2 h2 st, 
    sep X1 l1 h1 X2 l2 h2 st ->
    exists l, stt_a st X2 = Some l.
Proof.  
  move=> X1 l1 h1 X2 l2 h2 st.
  move=> H_sep.
  rewrite /sep in H_sep.
  inversion H_sep as [loc1 [loc2 [H_loc1 [H_loc2 H_or]]]].
  exists loc2; auto.
Qed. 

Lemma sep_sym:
  forall X1 b1 e1 X2 b2 e2 st,
    sep X1 b1 e1 X2 b2 e2 st -> sep X2 b2 e2 X1 b1 e1 st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st.
  rewrite /sep=>H_sep1.
  inversion H_sep1 as [loc1 [loc2 H_body]]; clear H_sep1.
  inv H_body. inv H0.
  exists loc2. exists loc1.
  do 2! apply: conj=>//.
  inv H2; [right | left]=>//.
Qed.   

Lemma sep_sub_rgn_left:
  forall X1 b1 e1 X2 b2 e2 st b1' e1', 
    sep X1 b1 e1 X2 b2 e2 st ->
    (b1 <= b1')%Z -> (e1' <= e1)%Z -> 
    sep X1 b1' e1' X2 b2 e2 st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st b1' e1' H_sep1.
  move=> H_le1 H_le2.
  rewrite /sep in H_sep1; rewrite /sep.
  inversion H_sep1 as [loc1 [loc2 H_body]].
  exists loc1. exists loc2.
  inv H_body. inv H0.
  do 2! apply: conj=>//.
  inv H2; auto with zarith.
Qed.

Lemma sep_sub_rgn_right:
  forall X1 b1 e1 X2 b2 e2 st b2' e2',
    sep X1 b1 e1 X2 b2 e2 st ->
    (b2 <= b2')%Z -> (e2' <= e2)%Z ->
    sep X1 b1 e1 X2 b2' e2' st.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st b2' e2' /sep_sym.
  move=> H_sep2 H_le2 H_le2'.
  have: (sep X2 b2' e2' X1 b1 e1 st).
  { eapply sep_sub_rgn_left; eauto. }
  apply /sep_sym.
Qed.

Lemma sep_change_st:
  forall X1 b1 e1 X2 b2 e2 st X1' X2' st', 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = stt_a st' X1' ->
    stt_a st X2 = stt_a st' X2' ->
    sep X1' b1 e1 X2' b2 e2 st'.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st X1' X2' st'.
  move=> H_sep H_eq1 H_eq2.
  rewrite /sep in H_sep; rewrite /sep.
  inversion H_sep as [loc1 [loc2 H_body]]; clear H_sep.
  exists loc1. exists loc2.
  move: H_eq1 H_eq2; rewrite /stt_a /compose=><-=><-=>//.
Qed.

Lemma sep_preserve_general:
  forall X1 b1 e1 X2 b2 e2 st X1' b1' e1' X2' b2' e2' st', 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = stt_a st' X1' ->
    stt_a st X2 = stt_a st' X2' ->
    (b1 <= b1')%Z -> (e1' <= e1)%Z ->
    (b2 <= b2')%Z -> (e2' <= e2)%Z ->
    sep X1' b1' e1' X2' b2' e2' st'.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st X1' b1' e1' X2' b2' e2' st'.
  move=> H_sep H_stt_eq1 H_stt_eq2 H_leb1 H_lee1 H_leb2 H_lee2.
  rewrite /sep in H_sep. rewrite /sep.
  inversion H_sep as [loc1 [loc2 [H_X1loc1 [H_X2loc2 H_rgn]]]];
    clear H_sep.
  exists loc1. exists loc2.
  rewrite <-H_stt_eq1. rewrite <-H_stt_eq2.
  apply: conj=>//. apply: conj=>//.
  inv H_rgn; auto with zarith.
Qed.  

Definition Sx_ge_Tk_1 (x: var_id) (st: state) :=
  exists l1 l2 z1 z2,
    stt_a st S = Some l1 /\ stt_a st T = Some l2 /\
    stt_v st x = Some z1 /\ stt_v st k_id = Some z2 /\
    (stt_l st (l1 + z1) >= stt_l st (l2 + z2 - 1))%Z. 

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


Ltac rem_prem hyp :=
  match type of hyp with
  | _ -> ?P => have: P; [apply hyp=>// | ]=>{hyp}=>hyp
  end.

(* solve goal with contradicting hypothesis of the forms 
   (a < b)%Z and (b <= a)%Z *) 
Ltac comp_contra hyp1 hyp2 :=
  let contra := fresh "contra" in (
    match type of hyp1 with
      (?x < ?y)%Z => (
        specialize (Z.lt_le_trans _ _ _ hyp1 hyp2)
        => contra; apply Z.lt_irrefl in contra; inv contra)
    | (?x <= ?y)%Z => (
        specialize (Z.le_lt_trans _ _ _ hyp1 hyp2)
        => contra; apply Z.lt_irrefl in contra; inv contra)
    end
  ).

Ltac some_eq hyp1 hyp2 :=
  first [
      rewrite hyp1 in hyp2; inv hyp2; auto |
      rewrite <- hyp1 in hyp2; inv hyp2; auto |
      rewrite hyp2 in hyp1; inv hyp1; auto |
      rewrite <- hyp2 in hyp2; inv hyp1; auto
    ].

Goal forall x (y z:nat), Some y = x -> Some z = x -> y = z.
  move=> x y z H1 H2.
  some_eq H1 H2.
Qed. 

Lemma st_upd_eq:
  forall st x z, stt_v (state_upd_var st x z) x = Some z.
Proof.
  move=> st x z.
  rewrite /stt_v /compose /state_upd_var /store_of=>/=.
  rewrite /st_upd_var /varst_upd /varst_of=>/=.
  elim eqP=>//=.
Qed.

Lemma st_upd_neq:
  forall st x x' z,
    x <> x' -> stt_v (state_upd_var st x z) x' = stt_v st x'.
Proof.
  move=> st x x' z H_neq.
  rewrite /stt_v /compose /state_upd_var /store_of=>/=.
  rewrite /st_upd_var /varst_upd /varst_of=>/=.
  elim: eqP=>//=.
  move=> H_eq. move: H_eq H_neq. move->=>//.
Qed.

Ltac updsimp :=
  repeat (
      first [
          rewrite st_upd_eq |
          rewrite st_upd_neq; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updsimp_h hyp :=
  repeat (
      first [
          rewrite st_upd_eq in hyp |
          rewrite st_upd_neq in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

Lemma st_upd_eq_arr:
  forall st X z, stt_a (state_upd_arr st X z) X = Some z.
Proof.
  move=> st X z.
  rewrite /stt_a /compose /state_upd_arr /store_of=>/=.
  rewrite /st_upd_arr /arrst_upd /arrst_of=>/=.
  elim eqP=>//=.
Qed.

Lemma st_upd_neq_arr:
  forall st X X' z, 
    X <> X' -> stt_a (state_upd_arr st X z) X' = stt_a st X'.
Proof.
  move=> st X X' z H_neq.
  rewrite /stt_a /compose /state_upd_arr /store_of=>/=.
  rewrite /st_upd_arr /arrst_upd /arrst_of=>/=.
  elim: eqP=>//=.
  move=> H_eq. move: H_eq H_neq. move->=>//.
Qed.

Ltac updsimp_a :=
  repeat (
      first [
          rewrite st_upd_eq_arr |
          rewrite st_upd_neq_arr; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updsimp_a_h hyp :=
  repeat (
      first [
          rewrite st_upd_eq_arr in hyp |
          rewrite st_upd_neq_arr in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

Lemma st_upd_var_arr :
  forall st X x z, stt_a (state_upd_var st x z) X = stt_a st X.
Proof.
  move=> st X x z.
  rewrite /state_upd_var /st_upd_var /store_of /stt_a /compose=>//=.
Qed.

Lemma st_upd_var_loc :
  forall st x z, stt_l (state_upd_var st x z) = stt_l st.
Proof.
  move=> st x z.
  rewrite /state_upd_var /st_upd_var /store_of /stt_l /compose=>//=.
Qed.

Lemma st_upd_loc_var :
  forall st l z x, stt_v (state_upd_loc st l z) x = stt_v st x.
Proof.
  move=> st l z x.
  rewrite /stt_v /compose /state_upd_loc /varst_of /store_of
          /st_upd_loc /varst_of /arrst_of /locst_upd /locst_of.
  simpl. auto. 
Qed.   

Lemma st_upd_loc_arr:
  forall st X l z, stt_a (state_upd_loc st l z) X = stt_a st X. 
Proof.
  move=> st X l z.
  rewrite /state_upd_loc /st_upd_loc /stt_a /compose
          /arrst_of /store_of /varst_of=>//.
Qed.

Lemma st_upd_eq_loc:
  forall st l z, stt_l (state_upd_loc st l z) l = z.
Proof.
  move=> st l z.
  rewrite /stt_l /compose /locst_of /state_upd_loc /st_upd_loc
          /store_of /varst_of /arrst_of /locst_upd /locst_of.
  simpl.
  case Enl: (l =? l)%Z=>//.
  rewrite Z.eqb_refl in Enl; inv Enl. 
Qed.

Lemma st_upd_neq_loc:
  forall st l l' z,
    l <> l' -> stt_l (state_upd_loc st l' z) l = stt_l st l.
Proof.
  move=> st l l' z H_neq.
  rewrite /stt_l /state_upd_loc /compose /locst_of /store_of
          /st_upd_loc /varst_of /arrst_of /locst_of /locst_upd=>//=.
  have H_neq': l' <> l by auto.
  case Enl: (l' =? l)%Z=>//.
  move: H_neq'; move /Z.eqb_neq. move: Enl->. 
  move=> contra; inv contra.
Qed.   

Lemma st_upd_loc_sep:
  forall X1 b1 e1 X2 b2 e2 st l1 l2 z1 z2 z, 
    sep X1 b1 e1 X2 b2 e2 st ->
    stt_a st X1 = Some l1 ->
    stt_a st X2 = Some l2 -> 
    (b1 <= z1 <= e1)%Z ->
    (b2 <= z2 <= e2)%Z -> 
    stt_l st (l1+z1)%Z =
    stt_l (state_upd_loc st (l2+z2)%Z z) (l1+z1)%Z.
Proof.
  move=> X1 b1 e1 X2 b2 e2 st l1 l2 z1 z2 z.
  move=> H_sep H_l1 H_l2 H_z1_rgn H_z2_rgn.
  rewrite /sep in H_sep.
  inversion H_sep as
      [l1' [l2' [H_l1' [H_l2' H_or]]]]; clear H_sep.
  have H_l1'l1: l1' = l1 by some_eq H_l1 H_l1'.
  have H_l2'l2: l2' = l2 by some_eq H_l2 H_l2'.
  rewrite H_l1'l1 H_l2'l2 in H_or.
  have H_ne: (l1 + z1)%Z <> (l2 + z2)%Z.
  {
    inversion H_or as [H_12 | H_21].
    - have H_lt: (l1+z1 < l2+z2)%Z
        by apply Z.le_lt_trans with (m:=(l1+e1)%Z);
        inv H_z1_rgn; auto with zarith.
      apply Z.lt_neq=>//.
    - apply ssrfun.nesym.
      have H_lt: (l2+z2 < l1+z1)%Z.
      apply Z.le_lt_trans with (m:=(l2+e2)%Z);
        inv H_z1_rgn; inv H_z2_rgn; auto with zarith.
      apply Z.lt_neq=>//.
  }
  rewrite st_upd_neq_loc=>//.
Qed.   

Lemma st_upd_switch:
  forall st x x' z z',
    x <> x' -> 
    state_upd_var (state_upd_var st x z) x' z' =
    state_upd_var (state_upd_var st x' z') x z.
Proof. 
  move=> st x x' z z' H_neq.
  rewrite /state_upd_var /st_upd_var /varst_upd
          /store_of /varst_of /arrst_of =>//=.
  have H_steq:
    ((fun x'0 : var_id =>
        if x'0 == x' then Some z' else if x'0 == x then Some z else fst (fst (fst st)) x'0)
     = (fun x'0 : var_id =>
          if x'0 == x then Some z else if x'0 == x' then Some z' else fst (fst (fst st)) x'0)).
  {
    apply functional_extensionality.
    move=> x0.
    case En: (x0 == x)=>//.
    case En': (x0 == x')=>//.
    exfalso. apply H_neq.
    apply: eqP. 
    move: En; move /eqP; move: En'; move /eqP->=>->=>//. 
  }
  congruence.
Qed.

Lemma st_upd_st_upd_eq:
  forall st x z z',
    state_upd_var (state_upd_var st x z) x z' = state_upd_var st x z'.
Proof.
  move=> st x z z'.
  rewrite /state_upd_var /st_upd_var /varst_upd
          /store_of /varst_of /arrst_of /locst_of=>//=.
  have H_steq:
    (fun x' : var_id => if x' == x then Some z' else if x' == x then Some z else fst (fst (fst st)) x')
    = (fun x' : var_id => if x' == x then Some z' else fst (fst (fst st)) x').
  {
    apply functional_extensionality.
    move=> x0.
    case En: (x0 == x)=>//.
  }
  congruence. 
Qed.         

Lemma st_upd_st_upd_neq:
  forall st x x' z z' z'',
    x <> x' -> 
    state_upd_var (state_upd_var (state_upd_var st x z) x' z') x z'' =
    state_upd_var (state_upd_var st x' z') x z''.
Proof.
  move=> st x x' z z' z'' H_neq.
  have H_switch: 
    state_upd_var (state_upd_var st x z) x' z' =
    state_upd_var (state_upd_var st x' z') x z by apply: st_upd_switch.
  rewrite H_switch.
  set st' := state_upd_var st x' z'.
  apply: st_upd_st_upd_eq. 
Qed.

Ltac updupdsimp :=
  repeat (
      first [
          rewrite st_upd_st_upd_eq |
          rewrite st_upd_st_upd_neq; [| intro H_eq; inversion H_eq ]
        ]
    ).

Ltac updupdsimp_h hyp :=
  repeat (
      first [
          rewrite st_upd_st_upd_eq in hyp |
          rewrite st_upd_st_upd_neq in hyp; [| intro H_eq; inversion H_eq ]
        ]
    ).

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


(* the correctness proof *)

Theorem mg_spec_valid: forall param, valid _ (mg_spec param).
Proof.
  init_verif. 
  inv H0; subst.
  
  - (* proof for call to "merge" *)
    inv H; subst.
    inv H14; subst.
    rename H22 into H_args_eval. 
    inv H20; subst. clear H20.
    fold (stt_cini st vals) in H15.
    ith_prem_exe_0 H15 H15' mg_spec. 
    ith_prem_exe_0 h0 h0' mg_spec. clear h1.
    ith_prem_exe_1 h0 h0' mg_spec. clear h0.
    ith_prem_exe_0 h1 h1' mg_spec. clear h0.
    ith_prem_exe_1 h1 h1' mg_spec. clear h1.
    ith_prem_exe_0 h0 h0' mg_spec. clear h1.
    ith_prem_exe_1 h0 h2' mg_spec. clear h0.
    ith_prem_exe_0 h1 h1' mg_spec. clear h0.
    ith_prem_exe_1 h1 h1' mg_spec. clear h1.
    
    (* the first loop in the function body reached by symbolic execution *)
    ith_prem_0 h0 h0'. 
    
    have H_prm0: param0 = nth (0%Z) vals 2.
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
    have H_mz: (m+1)%Z = z by simpl in H24; simpl in H_m; some_eq H_m H24.
    have H_z0prm: z0 = param0.
    {
      simpl in H26. updsimp_h H26. 
      rewrite stt_cini_i_id in H26. some_eq H_prm0 H26.
    }
    have H_X1: stt_a st X1 = Some (nth (0%Z) vals 0).
    {
      specialize (H_args_eval 0) as H_args_S.
      rem_prem H_args_S. 
      rewrite <- H_args_S; auto. 
    }
    have H_X2: stt_a st X2 = Some (nth (0%Z) vals 1).
    {
      specialize (H_args_eval 1) as H_args_T.
      rem_prem H_args_T.
      rewrite <- H_args_T; auto.
    }
    
    inversion h0'.
    +
      inversion H9 as [zs1 [H_arrseq_left H_sorted_zs1]].
      inversion H10 as [zs2 [H_arrseq_right H_sorted_zs2]]. 
      inversion H12.
      (* refute that there is no info about the 1st loop in the spec *)
      exfalso. apply H13.
      eexists; eapply WAF_SP_com_wh with (zs1:=zs1) (zs2:=zs2) (zs3:=[::]) (m:=m);
        try updsimp; auto. 
      apply stt_cini_i_id. 
      rewrite <- H_mz.
      rewrite -Z.add_sub_assoc Z.sub_diag Z.add_0_r; auto with zarith.
      rewrite H_m. apply stt_cini_m_id.
      apply stt_cini_n_id.
      auto with zarith.
      auto with zarith.
      auto with zarith.
      auto with zarith.
      (* _ -> Sx_ge_Tk_1 ... /\ Sx_ge_Tk_1 ...*)
      rewrite <- H_mz.
      rewrite H_z0prm. intro contra. 
      move: (n_z_ge_z1 param0)=>H_contra; by apply H_contra in contra; inv contra.
      rewrite <- H_prm0. (* rewrite <- H_m. *)
      updupdsimp. 
      (* rewrite H_z0prm. rewrite <- H_mz. *)
      apply arr_seq_eq with (b:=param0) (e:=m) (X1:=X1) (X2:=S) (st1:=st).
      do 2! (rewrite st_upd_var_arr). 
      rewrite stt_cini_S. apply: H_X1.
      do 2! (rewrite st_upd_var_loc).
      rewrite stt_l_cini=>//.
      exact H_arrseq_left.
      rewrite <- H_h. rewrite -{1} H_mz.
      apply arr_seq_eq with (e:=h) (X1:=X1) (X2:=S) (st1:=st). 
      do 4! (rewrite st_upd_var_arr).
      rewrite stt_cini_S. apply: H_X1.
      do 4! (rewrite st_upd_var_loc).
      rewrite stt_l_cini=>//.
      exact H_arrseq_right.
      rewrite -{1} H_z0prm.
      have: Z.lt (z0-1)%Z z0. auto with zarith.
      apply /arr_seq_empty. apply empty_lst_sorted.
      (* goal with sep *)
      rewrite <- H_h.
      apply sep_change_st with (X1:=X1) (X2:=X2) (st:=st)=>//.
    +
      (* there is some info about the 1st loop in the spec *)
      rename h0' into H_exP_or_nexP; clear H_exP_or_nexP.
      inversion H12 as [P [H_wh_in_spec H_P_st'']]; clear H12.
      move: H_prm0 H_m H_h H_mz H_z0prm H_X1 H_X2; 
        inversion H_wh_in_spec; subst;
          move=> H_prm0 H_m H_h H_mz H_z0prm H_X1 H_X2.
      have H_i_prm0: i = param0.
      { updsimp_h H13. some_eq stt_cini_i_id H13. }
      have H_j_m1: j = (m + 1)%Z.
      { updsimp_h H18. some_eq H_mz H18. }
      (*simpl in H_P_st''.*)
      inversion H_P_st'' as [i' [j' [k' H_P_st''_body]]]; clear H_P_st''.
      inversion H_P_st''_body as
          [H_i' [H_j' [H_k' [H_rgn [H_k'_eq [H_m0 [H_n [H_S [ H_T [H_occ [H_sorted H_body']]]]]]]]]]];
        clear H_P_st''_body. 
      inversion H_body' as [H_S_preserve [H_T_preserve [H_lnext_ge H_rnext_ge]]]; clear H_body'.
      clear H_wh_in_spec.
      updupdsimp_h H_occ. updupdsimp_h H_S_preserve.
      have H_m_m0: (m0 = m).
      { updupdsimp_h H25. updsimp_h H25. some_eq stt_cini_m_id H25. }
      inversion H_rgn as [H_i'_gt_m0 | H_j'_gt_n].
      *
        inversion H_i'_gt_m0 as [H_i_le_i' [H_i'_m01 H_jj']]. 
        move: H_prm0 H_m H_h H_mz H_z0prm H_X1 H_X2 H_m_m0 H_m0 H_n H_i_prm0 H_j_m1. 
        ith_prem_exe_1 h0 h0' mg_spec. 
        clear h0.
        ith_prem_0 h1 h1'.
        inversion h1' as [H_ne | H_e].
        (* refute that there is some info about second loop in the spec *)
        2:{ inv H_e. inv H12. inversion H22; subst.
            rewrite H_i' in H43. inversion H43; subst.
            move=> H_prm0 H_m H_h H_zm1 H_z0 H_stt1 H_stt2 H_m0m H_m0 H_n.
            rewrite H47 in H_m0. inversion H_m0.
            have contra: (m0 + 1 <=? m0)%Z = true by auto with zarith.
            have H_contra: (m0 + 1 <=? m0)%Z = false by apply z1_nle_z.
            rewrite contra in H_contra; inv H_contra. 
        }
        (* no info about second loop in the spec *)
        inversion H_ne as [H_nex H_inf_wh2]; clear H_ne H_nex. 
        inversion H_inf_wh2; subst.
        rename H41 into H_rule_wh_im.
        inversion H_rule_wh_im; subst.
        move=> H_prm0 H_m H_h H_z H_z0 H_X1 H_X2 H_mm0 H_m0 H_n H_i_prm0 H_j_m1.
        simpl in H41. rewrite H_i' in H41. rewrite H_m0 in H41. 
        inv H41.
        have contra: (m0 + 1 <=? m0)%Z = false by apply z1_nle_z.
        rewrite H22 in contra; inv contra.
        clear H_rule_wh_im. clear H42. 
        rename H41 into H_eval_wh2_cond_ff.
        clear h1'. ith_prem_1 h1 h1'.
        move=> H_prm0 H_m H_h H_z H_z0 H_X1 H_X2 H_m0m H_m0 H_n H_i_prm0 H_j_m1.
        (* reasoning about third loop *) 
        have H_prm0lt: (param0 < j')%Z.
        {
          apply Z.lt_le_trans with (m:=j).
          apply Z.le_lt_trans with (m:=m0)=>//.
          apply Z.le_trans with (m:=i)=>//.
          by inv H_jj'; auto.
        }
        inversion h1' as [H_nex | H_ex].
        (* refute that there is no info about the 3rd loop in the spec *)
        inv H_nex. exfalso. apply H12.
        eexists.
        eapply WAF_SP_com_jn with (st:=st''0); eauto.
        auto with zarith.
        auto with zarith.
        auto with zarith. (* establish param0 <= j'*)
        inv H_jj'; auto. (* establish j' <= n*)
        rename H40 into H_sep_S_T_. 
        updupdsimp_h H_sep_S_T_.
        apply sep_change_st with
            (X1:=S) (X2:=T) (st:=(state_upd_var (state_upd_var (stt_cini st vals) j_id z) k_id z0));
          auto.        
        
        (* there is some info about the 3rd loop in the spec *)
        inversion H_ex as [P [H_spec_whjn H_P_st0']].
        move: H_prm0 H_m H_h H_z H_z0 H_X1 H_X2 H_m0m H_m0 H_n H_i_prm0 H_j_m1.
        inversion H_spec_whjn; subst. clear H_spec_whjn.
        inversion H_P_st0' as [i'' [j'' [k'' H_bd]]]; clear H_P_st0'. 
        inversion H_bd as
            [H_i'' [H_j'' [H_k'' [H_i''_i0 [H_j''_j0 [H_j''_n0 [H_k''_k0 H'']]]]]]];
          clear H_bd.
        inversion H'' as [H_st0'_m1 [H_st0'_n0 [H_st0'_st''0_T [H_S_T_rem H_T_preserve']]]];
          clear H''.
        inversion H_S_T_rem as [zs_rem [H_S_zs_rem H_T_zs_rem]]; clear H_S_T_rem.
        inversion H_occ as
            [zs1' [zs2' [zs3' [H_S_zs1' [H_S_zs2' [H_T_zs3' H_occ_pluseq]]]]]];
          clear H_occ.
        have H_j''1_n0: (j''-1 = n0)%Z.
        {
          rewrite H_j''_n0. rewrite <- Z.add_sub_assoc. simpl. rewrite Z.add_0_r=>//.
        }
        move=> H_prm0 H_m H_h H_z H_z0 H_X1 H_X2 H_m0m H_m0 H_n H_i H_j.
        have H_m1_m0: m0 = m1 by some_eq H_m0 H44.
        rewrite <- H_m1_m0 in *. clear m1 H_m1_m0.
        have H00: (m0 + 1 - 1 = m0)%Z by auto with zarith.
        rewrite H00 in H_S_zs1'.
        rewrite <-H_m0m in *; clear H_m0m.
        symmetry in H_z0; rewrite <-H_z0 in *; clear H_z0.
        rewrite H_i in H_S_zs1'. 
        rewrite H_j in H_S_zs2'.
        have H_j'_eq_j0: j' = j0 by some_eq H_j' H41. 
        rewrite <- H_j'_eq_j0 in *. clear H_j'_eq_j0.
        move En_st0:
          (state_upd_var (state_upd_var (stt_cini st vals) j_id z) k_id param0) => st0.
        symmetry in En_st0; rewrite <- En_st0 in *.
        rename st''0 into st''.
        have H_n0n: n0 = n by some_eq H_n H45. 
        rewrite <- H_n0n in *. clear H_n0n.
        move: H_S_preserve=> H_S_preserve.
        have H_S_zs_rem0: arr_seq S j' (j''-1) st0 zs_rem.
        inversion H_S_preserve as [zs0 [H_arrseq_S_st H_arrseq_S_st'']];
          clear H_S_preserve. 
        apply arr_seq_subrgn with (b:=param0) (e:=n0) (st1:=st'') (zs:=zs0); 
          auto with zarith.
        have H_S_left: arr_seq S param0 (j'-1) st0 (zs1' ++ zs2').
        {
          have H_m0_1_j': (m0 + 1 <= j')%Z by rewrite <- H_j; auto with zarith.
          have H_cases: (m0 + 1 <= j' - 1)%Z \/ (m0 = j' - 1)%Z.
          {
            have: (m0 + 1 < j')%Z \/ (m0 + 1 = j')%Z by
                apply Zle_lt_or_eq in H_m0_1_j'; auto. 
            move=> H_cases. inv H_cases.
            left. apply Zlt_is_le_bool in H12. apply Zle_bool_imp_le; auto. 
            right. auto with zarith. 
          }
          inversion H_cases as [H_le | H_nle].
          - apply arr_seq_concat with (e1:=m0)=>//.
          - rewrite <- H_nle. rewrite <- H_nle in H_S_zs2'.
            have H_zs2'_emp: arr_seq S (m0 + 1) m0 st0 [:: ]
              by apply arr_seq_empty; auto with zarith.
            have: zs2' = [:: ]
              by apply arr_seq_unique with (S:=S) (b:=(m0+1)%Z) (e:=m0) (st:=st0);
              eauto with zarith.
            move->. rewrite cats0; auto. 
        }
        have H_S_full: arr_seq S param0 (j''-1) st0 ((zs1' ++ zs2') ++ zs_rem).
        {
          apply arr_seq_concat with (e1:=(j'-1)%Z); auto with zarith.
          rewrite Z.sub_add; auto. 
        }
        rewrite H_i in H_T_zs3'. (* rewrite H_k in H_T_zs3'. *)
        rewrite H_j in H_T_zs3'.
        rewrite Z.add_simpl_r in H_T_zs3'. 
        rewrite Zplus_minus in H_T_zs3'.
        rewrite Zplus_minus in H_T_zs3'.
        
        inversion H_T_preserve' as [zs0' [H_T_st'' H_T_st0']]; clear H_T_preserve'.
        have H_simp: (m0 + 1 + j' - (m0 + 1) - 1)%Z = (j' - 1)%Z
          by auto with zarith.
        rewrite H_simp in H_T_st'' H_T_st0'.
        have H_zs_eq: zs0' = zs3'. 
          by apply arr_seq_unique with (S:=T) (b:=param0) (e:=(j'-1)%Z) (st:=st'');
          auto.
        rewrite H_zs_eq in H_T_st0'.
        
        have H_T_full: arr_seq T param0 (k''-1) st0' (zs3' ++ zs_rem).
        {
          have H_simp': (m0 + 1 + j' - (m0 + 1))%Z = j' by auto with zarith.
          rewrite H_simp' in H_T_zs_rem.
          apply arr_seq_concat with (e1:=(j'-1)%Z); auto with arith.
          apply: conj=>//. inv H_jj'; auto with zarith.
          rewrite Z.sub_add. auto with zarith.
          rewrite Z.sub_add; auto.
        }
        have H_k''_j'': k'' = j'' by rewrite H_k''_k0; auto with zarith.
        rewrite H_k''_j'' in H_T_full.
        
        (* preparation for the proof of sortedness *)
        inversion H_sorted as [zs_T1 [H_arrseq_zs_T1 H_sorted_T1]];
          clear H_sorted.
        have H_simp': (i + j - (m0 + 1) + (m0 + 1 - i) + (j' - j) - 1)%Z = (j' - 1)%Z
          by auto with zarith.
        rewrite H_simp' in H_arrseq_zs_T1. 
        have H_zs3'_zsT1: zs3' = zs_T1
          by apply arr_seq_unique with (S:=T) (b:=param0) (e:=(j'-1)%Z) (st:=st'');
          auto.
        rewrite <- H_zs3'_zsT1 in *.
        rename H35 into H_arrseq_zs2.
        rewrite H_j in H_arrseq_zs2.
        updupdsimp_h H_arrseq_zs2. rewrite <- En_st0 in H_arrseq_zs2.
        move: H_S_zs_rem0 => H_S_zs_rem0.
        have H_zs_rem_frag: lst_frag (j'-(m0+1)) zs_rem zs2.
        {
          eapply arr_seq_subrgn_lst_frag
            with (S:=S) (b:=(m0+1)%Z) (e:=n0) (b':=j') (e':=(j''-1)%Z) (st:=st0)=>//. 
          auto with zarith.
          apply: conj; auto with zarith.
          inv H_jj'; auto with zarith.
          rewrite H_j''1_n0; auto with zarith.
        }
        have H_sorted_zs_rem: sorted zs_rem
          by apply sorted_lst_frag with (b0:=(j'-(m0+1))%Z) (zs2:=zs2); auto.

        (* prove the goal *)
        have H_n0h: n0 = h.
        { updsimp_h H27. rewrite stt_cini_n_id in H27. congruence. }
        exists ((zs1'++zs2')++zs_rem).
        exists (zs3'++zs_rem).
        rewrite H_j''1_n0 H_n0h in H_S_full.
        apply: conj. 
        apply arr_seq_eq with (X1:=S) (X2:=X1) (st1:=st0) (st2:=st); auto.
        rewrite En_st0.
        repeat (try rewrite st_upd_var_arr). 
        rewrite stt_cini_S; auto.
        rewrite En_st0.
        repeat (try rewrite st_upd_var_loc).
        apply stt_l_cini.
        apply: conj.
        rewrite H_j''1_n0 H_n0h in H_T_full.
        apply arr_seq_eq with (X1:=T) (X2:=X2) (st1:=st0'); auto.
        repeat (try rewrite st_upd_var_arr in H_T).
        rewrite H_st0'_st''0_T.
        rewrite /call_fin /varst_of /stt_a /compose /arrst_of /store_of=>/=.
        rewrite /stt_a /compose /arrst_of /store_of in H_X2.
        rewrite H_X2. rewrite stt_cini_T in H_T.
        rewrite <- H_T.
        rewrite /stt_a /compose /arrst_of /store_of=>//.
        apply: conj. (* occ *)
        apply functional_extensionality. move=> z'.
        rewrite occ_cat. rewrite [occ (zs3'++zs_rem) z']occ_cat.
        apply /eqP. rewrite eqn_add2r.
        rewrite occ_cat. rewrite H_occ_pluseq=>//.
        (* sorted *)
        move: H_rnext_ge => H_rnext_ge.
        have H_smp: (i + j - (m0 + 1) + (m0 + 1 - i) + (j' - j))%Z = j'
          by auto with zarith.
        rewrite H_smp in H_rnext_ge.
        have H_Sx_ge_Tk_1: Sx_ge_Tk_1 j_id st''.
        { apply H_rnext_ge. apply: conj=>//. auto with zarith. }
        unfold Sx_ge_Tk_1 in H_Sx_ge_Tk_1.
        inversion H_Sx_ge_Tk_1 as
            [l1 [l2 [z1 [z2 [H_S_st''_ [H_T_st''_ [H_z1 [H_z2 H_ge]]]]]]]];
          clear H_Sx_ge_Tk_1.

        have H_z1_zs_rem_0: stt_l st'' (l1 + z1)%Z = nth (0%Z) zs_rem 0.
        {
          have: z1 = j' by some_eq H_z1 H41. move->.
          have: 0 = Z.to_nat (j'-j') by rewrite Z.sub_diag; auto with zarith.
          move->.
          eapply arr_seq_ele with
              (X:=S) (b:=j') (e:=(j''-1)%Z)
              (st:=st'') (zs:=zs_rem) (l:=l1) (z:=j'); auto with zarith.
        }
        have H_z2_z3'_last: stt_l st'' (l2 + z2 - 1)%Z = nth (0%Z) zs3' (size zs3' - 1).
        {
          have H_sz_zs3': size zs3' = Z.to_nat (j' - 1 - param0) + 1
            by apply arr_seq_size with (X:=T) (b:=param0) (e:=(j'-1)%Z) (st:=st'');
            auto with zarith.
          have: size zs3' - 1 = Z.to_nat (j' - 1 - param0).
          {
            rewrite H_sz_zs3'.
            rewrite <- addnBA; auto. rewrite sub_zero. rewrite add_zero. auto.
          }
          move->.
          have: z2 = j' by some_eq H_z2 H42; auto with zarith.
          move->.
          rewrite <- Z.add_sub_assoc.
          eapply arr_seq_ele with
              (X:=T) (b:=param0) (e:=(j'-1)%Z)
              (st:=st'') (zs:=zs3') (l:=l2) (z:=(j'-1)%Z);
            auto with zarith.          
        }
        rewrite H_z1_zs_rem_0 H_z2_z3'_last in H_ge.
        apply sorted_concat; auto.
         
      *
        inversion H_j'_gt_n as [H_j_le_j' [H_j'_n1 H_ii']]. 
        move: H_prm0 H_m H_h H_mz H_z0prm H_X1 H_X2
                     H_m_m0 H_m0 H_n H_i_prm0 H_j_m1 H_j'_n1. 
        ith_prem_exe_1 h0 h0' mg_spec. 
        clear h0.
        ith_prem_0 h1 h1'.
        move=> H_prm0 H_m H_h H_mz H_z0prm H_X1 H_X2 H_m_m0 H_m0 H_n H_i_prm0 H_j_m1 H_j'_n1. 
        inversion h1' as [H_ne | H_e]; clear h1'.
        (* refute that there is no info about 2nd loop in the spec *)
        inv H_ne. exfalso. apply H12.
        eexists.
        eapply WAF_SP_com_im with (st:=st''); eauto.
        auto with zarith.
        auto with zarith. (* establish param0 <= j'*)
        inv H_ii'; auto. (* establish j' <= n*)
        auto with zarith.
        rename H40 into H_sep_S_l_T_rem. updupdsimp_h H_sep_S_l_T_rem.
        apply sep_change_st with
            (X1:=S) (X2:=T) (st:=(state_upd_var (state_upd_var (stt_cini st vals) j_id z) k_id z0));
          auto.
        
        (* there is some info about the 2nd loop in the spec *)
        inversion H_e as [P [H_spec_whim H_P_st''0]].
        move: H_prm0 H_m H_h H_X1 H_X2 H_m_m0 H_m0 H_n H_i_prm0 H_j_m1.
        inversion H_spec_whim; subst. clear H_spec_whim.
        inversion H_P_st''0 as [i'' [j'' [k'' H_bd]]]; clear H_P_st''0. 
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
          (state_upd_var (state_upd_var (stt_cini st vals) j_id (m+1)) k_id param0) => st0.
        symmetry in En_st0. rewrite <- En_st0 in *.
        have H_i0_i': i' = i0 by some_eq H22 H_i'.
        rewrite <- H_i0_i' in *. clear H_i0_i'.
        move=> H_prm0 H_m H_h H_X1 H_X2 H_m0m H_m0 H_n H_i H_j.
        rewrite H_i in H_S_zs1'.
        have H_m1m0: m0 = m1 by some_eq H44 H_m0. 
        rewrite <- H_m1m0 in *. clear H_m1m0.
        symmetry in H_m0m. rewrite <- H_m0m in *. clear H_m0m.
        inversion H_S_preserve as [zs0 [H_arrseq_S_st0 H_arrseq_S_st'']];
          clear H_S_preserve.
        have H_i''_sub_1: (i'' - 1)%Z = m by auto with zarith.
        have H_S_zs_rem_st0: arr_seq S i' (i''-1) st0 zs_rem.
        {
          apply arr_seq_subrgn with (b:=param0) (e:=n) (st1:=st'') (zs:=zs0)=>//.
          rewrite H_i''_sub_1.
          apply: conj.
          apply Z.le_trans with (m:=param0); auto.
          apply Z.lt_le_incl; apply Z.lt_le_trans with (m:=j); auto.
        }
        have H_S_left: arr_seq S param0 (i''-1) st0 (zs1'++zs_rem). 
        {
          have H_le: (param0 <= i')%Z by auto with zarith.
          have H_cases: ((param0 < i')%Z \/ (param0 = i')%Z) by
            apply Zle_lt_or_eq=>//. 
          inversion H_cases as [H_prm0_lt_i' | H_prm0_eq_i'];
            clear H_cases.
          - apply arr_seq_concat with (e1:=(i'-1)%Z); auto with zarith.
            rewrite Z.sub_add. auto.
          - rewrite <- H_prm0_eq_i' in H_S_zs_rem_st0.
            have H_arrseq_emp: arr_seq S param0 (i' - 1) st0 [:: ].
            apply arr_seq_empty. auto with zarith.
            have: zs1' = [:: ] by
                apply arr_seq_unique with (S:=S) (b:=param0) (e:=(i'-1)%Z) (st:=st0); auto.
            move->. simpl. auto.
        }
        have H_S_full: arr_seq S param0 n st0 ((zs1'++zs_rem)++zs2'). 
        {
          apply arr_seq_concat with (e1:=(i''-1)%Z); auto with zarith.
          rewrite Z.sub_add. rewrite <- Z.add_sub_assoc in H_S_zs2'.
          rewrite Z.sub_diag in H_S_zs2'. rewrite Z.add_0_r in H_S_zs2'.
          have: i''=j by congruence. move->=>//.
        }
        have H_i'nm: (param0 + (i' - i) + (n + 1 - j) = i' + n - m)%Z
          by rewrite H_i H_j; auto with zarith.
        rewrite H_i H_j in H_T_zs3'. move: H_T_zs3'. 
        have: (param0 + (m + 1) - (m + 1))%Z = param0 by auto with zarith.
        move->.
        have: (param0 + (i' - param0) + (n + 1 - (m + 1)) - 1)%Z = (i' + n - m - 1)%Z
          by auto with zarith.
        move->=>H_T_zs3'.
        (* have H_j0_n_1: (n + 1)%Z = j0 by some_eq H_j' H41. *)
        (* rewrite <- H_j0_n_1 in *; clear j0 H_j0_n_1. *)
        have H_n0n: n = n0 by some_eq H_n H45. rewrite <- H_n0n in *.
        clear n0 H_n0n.
        have H_arrseq_T0: arr_seq T param0 (i' + n - m - 1) st''0 zs3'.
        {
          inversion H_T_preserve' as [zs0' [H_T_st'' H_T_st''0]]; clear H_T_preserve'.
          have H_simp: (i' + (n + 1) - (m + 1) - 1)%Z = (i' + n - m - 1)%Z by
              auto with zarith.
          rewrite H_simp in H_T_st'' H_T_st''0.
          apply arr_seq_subrgn with (b:=param0) (e:=(i'+n-m-1)%Z) (st1:=st'') (zs:=zs0');
            auto with zarith.
        }
        have H_T_full: arr_seq T param0 (k''-1) st''0 (zs3'++zs_rem).
        {
          have H_simp: (i' + (n + 1) - (m + 1))%Z = ((i' + n - m - 1) + 1)%Z
            by auto with zarith.
          rewrite H_simp in H_T_zs_rem.
          apply arr_seq_concat with (e1:=(i'+n-m-1)%Z); auto with zarith.
        }
        have H_simp: (k'' - 1)%Z = n by rewrite H_k''_k0; auto with zarith.
        rewrite H_simp in H_T_full. 
        
        (* preparation for the proof of sortedness *)
        inversion H_sorted as [zs00 [H_arrseq_T_st''_zs00 H_sorted_zs00]];
          clear H_sorted.
        have H_simp': (i + j - (m + 1) + (i' - i) + (n + 1 - j) - 1)%Z =
                      (i' + n - m - 1)%Z
          by auto with zarith.
        rewrite H_simp' in H_arrseq_T_st''_zs00. 
        have H_zs00_zs3': zs00 = zs3'
          by apply arr_seq_unique with (S:=T) (b:=param0) (e:=(i'+n-m-1)%Z) (st:=st'');
          auto with zarith.
        rewrite H_zs00_zs3' in H_sorted_zs00.

        have H_lst_frag: lst_frag (i'-param0) zs_rem zs1.
        {
          apply arr_seq_subrgn_lst_frag with
              (S:=S) (b:=param0) (e:=m) (b':=i') (e':=(i''-1)%Z) (st:=st0);
            auto with zarith.
          rewrite H_i in H34.
          updupdsimp_h H34. rewrite <- En_st0 in H34; auto.
        }
        have H_sorted_zs_rem: sorted zs_rem
          by apply sorted_lst_frag with (b0:=(i'-param0)%Z) (zs2:=zs1);
          auto with zarith.

        move: H_lnext_ge=> H_lnext_ge.
        have H_smp: (i + j - (m + 1) + (i' - i) + (n + 1 - j))%Z = (i' + n - m)%Z
          by auto with zarith.
        rewrite H_smp in H_lnext_ge. 
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
          have: z1 = i' by some_eq H_z1 H22. move->.
          eapply arr_seq_ele with
              (X:=S) (b:=i') (e:=(i''-1)%Z) (st:=st'') (zs:=zs_rem) (l:=l1) (z:=i');
            auto with zarith. 
        }
        have H_z2_z3'_last: stt_l st'' (l2 + z2 - 1)%Z = nth (0%Z) zs3' (size zs3' - 1).
        {
          have: size zs3' = Z.to_nat (i'+n-m-1 - param0) + 1
            by apply arr_seq_size with (X:=T) (b:=param0) (e:=(i'+n-m-1)%Z) (st:=st'');
              auto with zarith.
          move->.
          rewrite <-addnBA; auto. rewrite sub_zero. rewrite add_zero.
          have: z2 = (i' + n - m)%Z by some_eq H_z2 H42; auto with zarith.
          move->.
          rewrite <- Z.add_sub_assoc.
          eapply arr_seq_ele with
              (X:=T) (b:=param0) (e:=(i'+n-m-1)%Z) (st:=st'') (zs:=zs3')
              (l:=l2) (z:=(i'+n-m-1)%Z);
            auto with zarith.
        }
        rewrite H_z1_zs_rem_0 H_z2_z3'_last in H_ge.
        have H_sorted_zs3'_zs_rem: sorted (zs3'++zs_rem). 
        { apply sorted_concat; auto. }

        (* 3rd loop *)
        symmetry in H_zs00_zs3'; rewrite <- H_zs00_zs3' in *; clear H_zs00_zs3'.
        clear z1 z2 H_z1 H_z2 H_z1_zs_rem_0 H_z2_z3'_last zs00. 
        move: H_prm0 H_m H_h H_X1 H_X2 H_m0 H_n H_i H_j 
                     H_j''_j0 H_k''_k0 H_i''_m1 En_st0.
        ith_prem_1 h1 h1'.
        inversion h1' as [H_neP | H_eP]; clear h1'.
        (* no info about 3rd loop in spec *)
        inversion H_neP as [H_ne H_inf]; clear H_neP H_ne.
        inversion H_inf; subst.
        rename H50 into H_rule_wh_jn. inversion H_rule_wh_jn; subst.
        (* true *)
        move=> H_prm0 H_m H_h H_X1 H_X2 H_m0 H_n H_i H_j 
                      H_j''_j0 H_k''_k0 H_i''_m1 En_st0.
        simpl in H50. rewrite H_j'' in H50. rewrite H_st0'_n0 in H50.
        rewrite H_j''_j0 in H50. inv H50. rewrite z1_nle_z in H43. inv H43.
        (* false *)
        move=> H_prm0 H_m H_h H_X1 H_X2 H_m0 H_n H_i H_j 
                      H_j''_j0 H_i''_m1 H_k''_n En_st0.
        move: H_S_full H_T_full H_sorted_zs3'_zs_rem=>
        H_S_full H_T_full H_sorted_zs3'_zs_rem.

        (* have H_k''_1_n0: n0 = (k''-1)%Z by some_eq H_n H45. *)
        have H_n_h: (k''-1)%Z = h.
        { updsimp_h H27. rewrite stt_cini_n_id in H27. congruence. }
        rewrite <- H_n_h in *.
        exists ((zs1' ++ zs_rem) ++ zs2').
        exists (zs3' ++ zs_rem).
        apply: conj.
        apply arr_seq_eq with (X1:=S) (st1:=st0); auto.
        rewrite En_st0. 
        repeat (try rewrite st_upd_var_arr). 
        rewrite stt_cini_S; auto.        
        rewrite En_st0.
        repeat (try rewrite st_upd_var_loc). 
        apply stt_l_cini.
        (* rewrite H_k''_1_n0=>//. *)
        apply: conj.
        apply arr_seq_eq with (X1:=T) (st1:=st0'); auto.
        rewrite H_st''0_st''_T H_T. 
        repeat (try rewrite st_upd_var_arr). 
        rewrite /call_fin /store_of /varst_of. simpl. 
        rewrite /arrst_of /store_of /locst_of. 
        rewrite /stt_a /compose /store_of /arrst_of. simpl.
        rewrite /stt_a /compose /arrst_of /store_of in H_X2.
        rewrite H_X2. auto.
        (* rewrite H_k''_1_n0=>//. *)
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

        (* refute that there is info about 3rd loop in spec *)
        inversion H_eP as [P [H_spec H_P_st0']]; clear H_eP.
        inversion H_spec; subst.        
        (* have H_j1_j'': j1 = j'' by some_eq H_j'' H51.  *)
        move=> H_prm0 H_i''_sub_1 H_h H_X1 H_X2 H_m H_n_ H_i H_j 
                      H_j''_ H_k''_ H_i''_ En_st0.
        have H_j0_j'': j'' = j0 by some_eq H_j'' H50.
        have H_n1_n0: (k''-1)%Z = n0 by some_eq H_st0'_n0 H55.
        rewrite <- H_j0_j'' in *. clear j0 H_j0_j''.
        rewrite <- H_n1_n0 in *. clear n0 H_n1_n0.
        (* have H_n0_k''_1: n0 = (k'' - 1)%Z by some_eq H_n_ H45. *)
        have: ((k''-1)%Z < j'')%Z.
        { rewrite H_j''_. auto with zarith. }
        move /Zlt_not_le=> contra.
        apply contra in H59; inv H59.
        
  - (* proof for first loop *) 
    inv H; subst. clear H0.
    rename H21 into H_rule_wh. inv H_rule_wh; subst. 
    (* refute exiting the loop *)
    2: {
      rename H20 into Hcond. simpl in Hcond.
      rewrite H1 in Hcond. rewrite H5 in Hcond.
      rewrite H2 in Hcond. rewrite H6 in Hcond.
      apply Zle_imp_le_bool in H9. apply Zle_imp_le_bool in H11.
      rewrite H9 H11 in Hcond. simpl in Hcond. inv Hcond.
    }
    (* entering the loop *)
    rename H22 into Hforall. 
    ith_prem_exe_0 Hforall H' mg_spec.
    ith_prem_exe_0 h h' mg_spec.
    + (* cond of if evaluated to true *)
      assert (Hcond0 := H21).
      rename H21 into Hcond. simpl in Hcond.
      case EnS: (stt_a st S)=> [lS | ]; rewrite EnS in Hcond; [ | inv Hcond ].
      rewrite H1 in Hcond. 
      case Enige0: (i >=? 0)%Z; rewrite Enige0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case EnlSi: (lS + i <? floc_of st)%Z;
        rewrite EnlSi in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      rewrite H2 in Hcond.
      case Enjge0: (j >=? 0)%Z; rewrite Enjge0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case EnlSj: (lS + j <? floc_of st)%Z;
        rewrite EnlSj in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      case EnlSij: (stt_l st (lS + i) <=? stt_l st (lS + j))%Z; 
        rewrite EnlSij in Hcond; [ | simpl in Hcond; inv Hcond ].
      clear Hcond.

      ith_prem_exe_0 h0 h0' mg_spec. 
      ith_prem_exe_0 h1 h1' mg_spec. clear h2.
      ith_prem_exe_1 h1 h1' mg_spec. clear h2. clear h1. clear h0.
      ith_prem_exe_1 h h' mg_spec. clear h. 

      (* re-visiting the loop after reasoning about its body *)
      ith_prem_1 Hforall H'.
      move En_st'':
        (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) i_id z) k_id z0)
      => st''.
      symmetry in En_st''; rewrite <- En_st'' in *.
      rewrite -/com_wh in H'.
      have H_z1: z1 = (i + j - (m+1))%Z.
      {
        rename H27 into H_k_id_eval.
        simpl in H_k_id_eval.
        some_eq H_k_id_eval H3.
      }
      have H_z2: z2 = stt_l st (lS + i)%Z.
      {
        rename H28 into H_S_i_eval.
        simpl in H_S_i_eval.
        rewrite EnS in H_S_i_eval. rewrite H1 in H_S_i_eval.
        rewrite Enige0 in H_S_i_eval. rewrite EnlSi in H_S_i_eval.
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
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }
      have H_exzs_Si1_m_st'': exists zs1', arr_seq S (i + 1) m st'' zs1'.
      {
        apply arr_seq_ex with (l:=lS); auto with zarith.
        rewrite En_st''.
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
      have H_stt_l_st''_ijm: stt_l st'' (l + (i + j - (m + 1)))%Z = stt_l st (lS + i)%Z.
      {
        rewrite -H_z1. rewrite {1}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2=>//.
      }
      have H_arrseq_st''_zs3: arr_seq T param0 (i + j - (m + 1) - 1) st'' zs3.
      {
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l);
          auto with zarith.
        some_eq H_st''_T H25.
        move=> z3 H_prm0_le_z3 H_z3_le_ijm.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
      }
      have H_arr_seq_T_st''_ext: 
        arr_seq T param0 (i + j - m - 1) st'' (zs3 ++ [:: (stt_l st'' (l+i+j-(m+1))%Z)]).
      {
        have: (i + j - m - 1)%Z = (i + j - (m + 1) - 1 + 1)%Z by auto with zarith.
        move->.
        apply arr_seq_concat_general with (e1:=(i + j - (m + 1) - 1)%Z);
          auto with zarith.
        have: (i + j - (m+1) - 1 + 1)%Z = (i + j - (m+1))%Z by auto with zarith. move->. 
        have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
      }      
      have H_sorted_z3_ext: sorted (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
      {
        have H_prm0_rgn: (param0 <= i + j - (m + 1))%Z by auto with zarith.
        have H_prm0_cases: (param0 < i + j - (m + 1))%Z \/ (param0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq=>//.
        inversion H_prm0_cases as [H_prm0_lt | H_prm0_eq].
        (* first case *)
        apply sorted_concat; auto with zarith.
        apply singleton_sorted. simpl.
        have: size zs3 = Z.to_nat ((i + j - (m + 1) - 1) - param0) + 1
          by apply arr_seq_size with (X:=T) (st:=st); auto with zarith.
        move->.
        have H_gt: (i + j - (m + 1) >= param0 + 1)%Z by auto with zarith.
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
              nth (0%Z) zs3 (Z.to_nat (i + j - (m + 1) - 1 - param0)).
        { rewrite -Z.add_sub_assoc.
          apply arr_seq_ele with
              (X:=T) (b:=param0) (e:=(i + j - (m + 1) - 1)%Z) (st:=st) (zs:=zs3)
              (l:=l) (z:=((i + j - (m + 1)) - 1)%Z); auto with zarith. }
        move->. rewrite -addnBA; auto. rewrite sub_zero. rewrite add_zero=>//.
        (* second case *)
        have: zs3 = [:: ] 
          by apply arr_seq_empty' with
            (X:=T) (b:=param0) (e:=(i + j - (m + 1) - 1)%Z) (st:=st);
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
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }

      have H_exP_cond:
        (i+1 <= m)%Z ->
        (exists P : waf_rconfig -> Prop, mg_spec param0 (com_wh, st'', mg_prog) P).
      {        
        move=> H_i1_le_m.
        have H_lstfrag: lst_frag ((i+1)-i) zs1' zs1
          by apply arr_seq_subrgn_lst_frag with
            (S:=S) (b:=i) (e:=m) (b':=(i+1)%Z) (e':=m) (st:=st'');
          auto with zarith.
        eexists. 
        eapply WAF_SP_com_wh with
            (lprm:=param0) (i:=(i+1)%Z) (j:=j) (k:=(i+j-m)%Z) (m:=m) (n:=n) (st:=st'')
            (zs1:=zs1') (zs2:=zs2) (zs3:=zs3++[:: (stt_l st'' (l+i+j-(m+1))%Z)]);
          auto with zarith.
        (* goal with Sx_ge_Tk_1 *)

        have H_Sx_ge_Tk_1:
          (i + j - m >= param0 + 1)%Z -> Sx_ge_Tk_1 i_id st'' /\ Sx_ge_Tk_1 j_id st''.
        {
          move=> H_k_ge.
          rewrite /Sx_ge_Tk_1. 
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
                (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
                (l1:=lS) (l2:=l) (z1:=(i+1)%Z) (z2:=z1) (z:=z2);
              auto with zarith.          
          }
          move<-.
          apply Z.le_ge.
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
                (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
                (l1:=lS) (l2:=l) (z1:=j) (z2:=z1) (z:=z2);
              auto with zarith. 
          }
          move<-.
          apply Z.le_ge. apply Zle_bool_imp_le=>//.
        }
        apply H_Sx_ge_Tk_1.
        (* arr_seq S j n st'' zs2 solved automatically using H_arrseq_Sjn_st'' *)
        (* arr_seq T param0 (i + j - m - 1) st'' (zs3 ++ [:: (stt_l st'' (l+i+j-(m+1))%Z)]) 
           proven automatically *)
        (* sorted zs1' *)
        apply sorted_lst_frag with (b0:=(i + 1 - i)%Z) (zs2:=zs1); auto.
        (* sorted (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]) proven automatically *)
        (* sep S param0 n T param0 n st'' *)
        apply sep_change_st with
            (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st);
          auto with arith.
        some_eq H_st''_S EnS.
        some_eq H_st''_T H25.
      }

      inversion H' as [H_nexP | H_exP].
      * (* there is no info about result of first round execution in the spec *)
        inversion H_nexP as [H_nP H_inf]; clear H_nexP.
        specialize (contra_pos _ _ H_exP_cond) as H_cp.
        specialize (H_cp H_nP).
        move: H_z1 H_z2 En_st''.
        inversion H_inf; subst.
        rename H21 into H_rule_wh'.
        inversion H_rule_wh'; clear H_rule_wh'.
        clear H26.
        move=> H_z1 H_z2 En_st''.
        rename H21 into H_cond_eval_tt.
        simpl in H_cond_eval_tt.
        rewrite H_st''_i in H_cond_eval_tt. rewrite H_st''_m in H_cond_eval_tt.
        rewrite H_st''_j in H_cond_eval_tt. rewrite H_st''_n in H_cond_eval_tt.
        have H_cond_true: ((i + 1 <=? m)%Z && (j <=? n)%Z) = true
          by inv H_cond_eval_tt; auto.
        have: (i + 1 <=? m)%Z = true.
        { case En':(i + 1 <=? m)%Z=>//. rewrite En' in H_cond_true; inv H_cond_true. }
        move /Z.leb_spec0=>contra.
        apply H_cp in contra; inv contra.
        (* the actual case -- false *) 
        rename H32 into H_st0st''. (* no need for rewriting *) clear H_st0st''.
        rename H35 into H_st''r. rewrite <- H_st''r. 
        rename H21 into H_cond_eval_ff. 
        move=> H_z1 H_z2 En_st''.
        
        exists (i+1)%Z. exists j. exists (i + j - m)%Z.
        apply: conj; [auto | ]. apply: conj; [auto | ]. apply: conj; [auto | ].
        apply: conj. left. auto with zarith. 
        apply: conj. auto with zarith.
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj. some_eq H_st''_T H25. 
        apply: conj.
        exists [:: stt_l st (lS + i)%Z]. exists [:: ].
        exists [:: stt_l st (lS + i)%Z].
        apply: conj.
        have: (i + 1 - 1)%Z = i by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        apply: conj.
        apply arr_seq_empty; auto with zarith.
        apply: conj. 
        rewrite - H_stt_l_st''_ijm.
        have: (i + j - m - 1)%Z = (i + j - (m + 1))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        move=> z3. simpl. repeat rewrite add_zero=>//.  
        apply: conj.
        (*  exists zs : seq Z, arr_seq T param0 (i + j - m - 1) st'' zs /\ sorted zs *)
        exists (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
        apply: conj.
        apply H_arr_seq_T_st''_ext.
        apply H_sorted_z3_ext.
        
        (* (exists zs : seq Z, arr_seq S param0 n st zs /\ arr_seq S param0 n st'' zs) *)
        apply: conj.
        have H_ex_zs_arrseq: exists zs, arr_seq S param0 n st zs
            by apply arr_seq_ex with (l:=lS); auto with zarith.
        inversion H_ex_zs_arrseq as [zs' H_arrseq_S_zs']; clear H_ex_zs_arrseq.
        exists zs'.
        apply: conj. auto.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n)
                                  (st:=st) (l1:=lS) (l2:=l) (z1:=z3) (z2:=z1) (z:=z2);
          auto with zarith. 

        (* preservation of initial fragment of T *)
        apply: conj.
        have H_ex_zs_arrseq_T_st_zs: exists zs, arr_seq T param0 (i+j-(m+1)-1) st zs
            by apply arr_seq_ex with (l:=l); auto with zarith.
        inversion H_ex_zs_arrseq_T_st_zs as [zs_T H_arrseq_T_zs_T];
          clear H_ex_zs_arrseq_T_st_zs.
        exists zs_T.
        apply: conj. auto. 
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with arith.
        some_eq H25 H_st''_T.
        move=> z3 H_prm0_z3 H_z3_ijm.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
        
        (* goal with Sx_ge_Tk_1 *)
        apply: conj.
        move=> H_ijm_rgn_contra.
        inversion H_ijm_rgn_contra as [H_i1_le_m H_ijm_ge_];
          clear H_ijm_rgn_contra.
        apply H_cp in H_i1_le_m. inv H_i1_le_m.
        move=> H_jim_rgn.
        inversion H_jim_rgn as [H_j_le_n H_ijm_ge_]; clear H_jim_rgn.

        rewrite /Sx_ge_Tk_1.
        exists lS. exists l. exists j. exists (i+j-m)%Z.
        repeat (try apply: conj=>//).
        have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite -H_z1. rewrite {2}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2.
        have: stt_l st (lS + j)%Z = stt_l st'' (lS + j)%Z.
        {
          rewrite En_st''. repeat (try rewrite st_upd_var_loc).
          apply st_upd_loc_sep with
              (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
              (l1:=lS) (l2:=l) (z1:=j) (z2:=z1) (z:=z2);
            auto with zarith. 
        }
        move<-.
        apply Z.le_ge. apply Zle_bool_imp_le=>//.

      * (* there is some info about result of first round execution in the spec *)
        inversion H_exP as [P [H_spec_P H_P_r]]; clear H_exP.
        inversion H_spec_P.
        rename H48 into H_fun_r_eq_P.
        rewrite <- H_fun_r_eq_P in H_P_r. clear H_fun_r_eq_P.
        inv H_P_r. rename H48 into H_wh_post_cond. 
        
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
        rewrite <- H_zs0_ in *.
        clear zs0 H_zs0_.
        rename H44 into H_sorted_zs1'.
        rename H41 into H_arrseq_S_st''; clear H_arrseq_S_st''.

        rename H42 into H_arrseq_S_st''_zs4. rename H45 into H_sorted_zs4.
        clear zs4 H_arrseq_S_st''_zs4 H_sorted_zs4.
        rename H43 into H_arrseq_T_st''_zs5. rename H46 into H_sorted_zs5.
        clear zs5 H_arrseq_T_st''_zs5 H_sorted_zs5.

        rename x into i'0. 
        inversion H_wh_post_cond as
            [j' [k' [H_i'0 [H_j' [H_k' [H_ijkm_or [H_k'_ [H_m_ [H_n_ [H_S_ [H_T_ H'']]]]]]]]]]];
          clear H_wh_post_cond.
        inversion H'' as
            [H_occ' [H_sorted' [H_S_preserve' [H_T_preserve' [H_Sx_ge_Tk_1_i' H_Sx_ge_Tk_1_j']]]]];
          clear H''.
        clear H_P_r.
        
        exists i'0. exists j'. exists k'.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj.
        inv H_ijkm_or.
        left; auto with zarith. right; auto with zarith.
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

        have H_arrseq_S_i_1_st: arr_seq S (i + 1) (i'0 - 1) st zs10.
        {
          apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
            auto with zarith.
          rewrite En_st''. repeat rewrite st_upd_var_arr.
          rewrite st_upd_loc_arr=>//.
          move=> z3 H_iz3 H_z3i0.
          rewrite En_st''. repeat rewrite st_upd_var_loc.
          symmetry.
          apply st_upd_loc_sep with
              (X1:=S) (b1:=param0) (e1:=n) (X2:=T)
              (b2:=param0) (e2:=n) (l2:=l) (z2:=z1) (z:=z2);
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
        move=> z3 H_jz3 H_z3j'_1.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        symmetry.
        by apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n)
                                     (X2:=T) (b2:=param0) (e2:=n);
          auto with zarith.
        apply: conj.
        have: (i + j - (m+1))%Z = (k - 1)%Z by auto with zarith.
        move->.
        have: stt_l st (lS + i)%Z :: zs30 = [:: stt_l st (lS + i)%Z] ++ zs30
          by auto.
        move->.
        apply arr_seq_concat with (e1:=(k-1)%Z); auto with zarith.
        inversion H_S_preserve' as
            [zs [H_arrseq_S_st'' H_arrseq_S_r]]; clear H_S_preserve'.

        rewrite <- H_stt_l_st''_ijm.
        have: (l + (i + j - (m + 1)))%Z = (k - 1 + l)%Z by auto with zarith.
        move->.
        have: stt_l st'' (l + (k-1))%Z = stt_l r (l + (k-1))%Z.
        {
          inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]]. 
          apply arr_seq_ele_eq with (X:=T) (b:=param0) (e:=(k-1)%Z) (zs:=zs_T);
            auto with zarith.
          congruence.
        }
        have: (k - 1 + l)%Z = (l + (k - 1))%Z by auto with zarith.
        move->. move->.
        apply arr_seq_singleton; auto with zarith.
        congruence.
        have: (k - 1 + 1)%Z = k by auto with zarith.
        move->. auto.
        move=> z3.
        have: stt_l st (lS + i)%Z :: zs10 = [:: stt_l st (lS+i)%Z] ++ zs10
          by simpl; auto.
        move->.
        have: stt_l st (lS + i)%Z :: zs30 = [:: stt_l st (lS+i)%Z] ++ zs30
          by simpl; auto.
        move->.
        do 2! (rewrite occ_cat).  
        rewrite <- Nat.add_assoc.
        rewrite [(occ zs10 z3 + occ zs20 z3)%coq_nat]H_all.
        by auto.

        apply: conj. 
        assumption. (* initial fragment of T sorted *)

        apply: conj.
        (* preservation of content of S *)
        inversion H_S_preserve' as [zs_S [H_arrseq_S_st'' H_arrseq_S_r]].
        exists zs_S. apply: conj; [ | auto].
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence. 
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
        apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n);
          auto with zarith.

        apply: conj.
        (* preservation of content of initial fragment of T *)
        have H_ijm_rgn: (0 <= i + j - (m + 1))%Z by auto with zarith.
        have: (0 < i + j - (m + 1))%Z \/ (0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq; auto.
        case=> H_cs.
        (* first case *)
        inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]].
        have H_ex_T': exists zs_T', arr_seq T param0 (i+j-(m+1)-1) r zs_T'.
        { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
        inversion H_ex_T' as [zs_T' H_arrseq_T_zs_T']; clear H_ex_T'.
        have H_arrseq_T_st''_zs_T': arr_seq T param0 (i+j-(m+1)-1) st'' zs_T'
          by apply arr_seq_subrgn with (b:=param0) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
          auto with zarith.
        have H_arrseq_T_st_zs_T': arr_seq T param0 (i+j-(m+1)-1) st zs_T'.
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
        
    + (* cond of if evaluated to false *)
      assert (Hcond0 := H21).
      rename H21 into Hcond. simpl in Hcond.
      case EnS: (stt_a st S)=> [lS | ]; rewrite EnS in Hcond; [ | inv Hcond ].
      rewrite H1 in Hcond. 
      case Enige0: (i >=? 0)%Z; rewrite Enige0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case EnlSi: (lS + i <? floc_of st)%Z;
        rewrite EnlSi in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      rewrite H2 in Hcond.
      case Enjge0: (j >=? 0)%Z; rewrite Enjge0 in Hcond; [ | simpl in Hcond; inv Hcond ].
      case EnlSj: (lS + j <? floc_of st)%Z;
        rewrite EnlSj in Hcond; [ | simpl in Hcond; inv Hcond ].
      simpl in Hcond.
      case EnlSij: (stt_l st (lS + i) <=? stt_l st (lS + j))%Z; 
        rewrite EnlSij in Hcond; [ simpl in Hcond; inv Hcond | ].
      clear Hcond.

      ith_prem_exe_0 h0 h0' mg_spec. 
      ith_prem_exe_0 h1 h1' mg_spec. clear h2.
      ith_prem_exe_1 h1 h1' mg_spec. clear h2. clear h1. clear h0.
      ith_prem_exe_1 h h' mg_spec. clear h. 

      (* re-visiting the loop after reasoning about its body *)
      ith_prem_1 Hforall H'. 
      move En_st'':
        (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) j_id z) k_id z0)
      => st''.
      symmetry in En_st''; rewrite <- En_st'' in *.
      rewrite -/com_wh in H'.
      have H_z1: z1 = (i + j - (m+1))%Z.
      {
        rename H27 into H_k_id_eval.
        simpl in H_k_id_eval.
        some_eq H_k_id_eval H3.
      }
      have H_z2: z2 = stt_l st (lS + j)%Z.
      {
        rename H28 into H_S_j_eval.
        simpl in H_S_j_eval.
        rewrite EnS in H_S_j_eval. rewrite H2 in H_S_j_eval.
        rewrite Enjge0 in H_S_j_eval. rewrite EnlSj in H_S_j_eval.
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
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }
      have H_exzs_Sj1_n_st'': exists zs2', arr_seq S (j + 1) n st'' zs2'.
      {
        apply arr_seq_ex with (l:=lS); auto with zarith.
        rewrite En_st''.
        repeat (try rewrite st_upd_var_arr). rewrite st_upd_loc_arr.
        auto.
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
      have H_stt_l_st''_ijm: stt_l st'' (l + (i + j - (m + 1)))%Z = stt_l st (lS + j)%Z.
      {
        rewrite -H_z1. rewrite {1}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2=>//.
      }
      have H_arrseq_st''_zs3: arr_seq T param0 (i + j - (m + 1) - 1) st'' zs3.
      {
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l);
          auto with zarith.
        some_eq H_st''_T H25.
        move=> z3 H_prm0_le_z3 H_z3_le_ijm.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
      }
      
      have H_arr_seq_T_st''_ext: 
        arr_seq T param0 (i + j - m - 1) st'' (zs3 ++ [:: (stt_l st'' (l+i+j-(m+1))%Z)]).
      {
        have: (i + j - m - 1)%Z = (i + j - (m + 1) - 1 + 1)%Z by auto with zarith.
        move->.
        apply arr_seq_concat_general with (e1:=(i + j - (m + 1) - 1)%Z);
          auto with zarith.
        have: (i + j - (m+1) - 1 + 1)%Z = (i + j - (m+1))%Z by auto with zarith. move->. 
        have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
      }
      
      have H_sorted_z3_ext: sorted (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
      {
        have H_prm0_rgn: (param0 <= i + j - (m + 1))%Z by auto with zarith.
        have H_prm0_cases: (param0 < i + j - (m + 1))%Z \/ (param0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq=>//.
        inversion H_prm0_cases as [H_prm0_lt | H_prm0_eq].
        (* first case *)
        apply sorted_concat; auto with zarith.
        apply singleton_sorted. simpl.
        have: size zs3 = Z.to_nat ((i + j - (m + 1) - 1) - param0) + 1
          by apply arr_seq_size with (X:=T) (st:=st); auto with zarith.
        move->.
        have H_gt: (i + j - (m + 1) >= param0 + 1)%Z by auto with zarith.
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
              nth (0%Z) zs3 (Z.to_nat (i + j - (m + 1) - 1 - param0)).
        { rewrite -Z.add_sub_assoc.
          apply arr_seq_ele with
              (X:=T) (b:=param0) (e:=(i + j - (m + 1) - 1)%Z) (st:=st) (zs:=zs3)
              (l:=l) (z:=((i + j - (m + 1)) - 1)%Z); auto with zarith. }
        move->. rewrite -addnBA; auto. rewrite sub_zero. rewrite add_zero=>//.
        (* second case *)
        have: zs3 = [:: ] 
          by apply arr_seq_empty' with
            (X:=T) (b:=param0) (e:=(i + j - (m + 1) - 1)%Z) (st:=st);
          auto with zarith.
        move->=>/=. 
        apply singleton_sorted; auto.
      }

      have H_arrseq_Sim_st'': arr_seq S i m st'' zs1.
      {
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto.
        some_eq EnS H_st''_S.
        move=> z3 H_i_le_z3 H_z3_le_m.
        rewrite En_st''. repeat (try rewrite st_upd_var_loc).
        rewrite <- st_upd_loc_sep with
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }

      have H_exP_cond:
        (j+1 <= n)%Z ->
        (exists P : waf_rconfig -> Prop, mg_spec param0 (com_wh, st'', mg_prog) P).
      {        
        move=> H_j1_le_m.
        have H_lstfrag: lst_frag ((j+1)-j) zs2' zs2
          by apply arr_seq_subrgn_lst_frag with
            (S:=S) (b:=j) (e:=n) (b':=(j+1)%Z) (e':=n) (st:=st'');
          auto with zarith.
        eexists. 
        eapply WAF_SP_com_wh with
            (lprm:=param0) (i:=i) (j:=(j+1)%Z) (k:=(i+j-m)%Z) (m:=m) (n:=n) (st:=st'')
            (zs1:=zs1) (zs2:=zs2') (zs3:=zs3++[:: (stt_l st'' (l+i+j-(m+1))%Z)]);
          auto with zarith.
        (* goal with Sx_ge_Tk_1 *)

        have H_Sx_ge_Tk_1:
          (i + j - m >= param0 + 1)%Z -> Sx_ge_Tk_1 i_id st'' /\ Sx_ge_Tk_1 j_id st''.
        {
          move=> H_k_ge.
          rewrite /Sx_ge_Tk_1. 
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
                  (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
                  (l1:=lS) (l2:=l) (z1:=(j+1)%Z) (z2:=z1) (z:=z2);
                auto with zarith.          
            }
            move<-.
            apply Z.le_ge.
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
                (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
                (l1:=lS) (l2:=l) (z1:=i) (z2:=z1) (z:=z2);
              auto with zarith. 
          }
          move<-.
          move: EnlSij. move /Z.leb_gt. auto with zarith.
        }
        apply H_Sx_ge_Tk_1.
        (* sorted zs2' *)
        apply sorted_lst_frag with (b0:=(j + 1 - j)%Z) (zs2:=zs2); auto.
        (* sep S param0 n T param0 n st'' *)
        apply sep_change_st with
            (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st);
          auto with arith.
        some_eq H_st''_S EnS.
        some_eq H_st''_T H25.
      }

      inversion H' as [H_nexP | H_exP].
      * (* there is no info about result of first round execution in the spec *)
        inversion H_nexP as [H_nP H_inf]; clear H_nexP.
        specialize (contra_pos _ _ H_exP_cond) as H_cp.
        specialize (H_cp H_nP).
        move: H_z1 H_z2 En_st''.
        inversion H_inf; subst.
        rename H21 into H_rule_wh'.
        inversion H_rule_wh'; clear H_rule_wh'.
        clear H26.
        move=> H_z1 H_z2 En_st''.
        rename H21 into H_cond_eval_tt.
        simpl in H_cond_eval_tt.
        rewrite H_st''_i in H_cond_eval_tt. rewrite H_st''_m in H_cond_eval_tt.
        rewrite H_st''_j in H_cond_eval_tt. rewrite H_st''_n in H_cond_eval_tt.
        have H_cond_true: ((i <=? m)%Z && (j + 1<=? n)%Z) = true
          by inv H_cond_eval_tt; auto.
        have: (j + 1 <=? n)%Z = true.
        { case En':(j + 1 <=? n)%Z=>//. rewrite En' in H_cond_true.
          case En'': (i <=? m)%Z=>//; rewrite En'' in H_cond_true.
          inv H_cond_true. inv H_cond_true. }
        move /Z.leb_spec0=>contra.
        apply H_cp in contra; inv contra.
        (* the actual case -- false *) 
        rename H32 into H_st0st''. (* no need for rewriting *) clear H_st0st''.
        rename H35 into H_st''r. rewrite <- H_st''r. 
        rename H21 into H_cond_eval_ff. 
        move=> H_z1 H_z2 En_st''.
        
        exists i. exists (j+1)%Z. exists (i + j - m)%Z.
        apply: conj; [auto | ]. apply: conj; [auto | ]. apply: conj; [auto | ].
        apply: conj. right. auto with zarith. 
        apply: conj. auto with zarith.
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj; [auto | ].
        apply: conj. some_eq H_st''_T H25. 
        apply: conj.
        exists [:: ]. exists [:: stt_l st (lS + j)%Z]. 
        exists [:: stt_l st (lS + j)%Z].
        apply: conj. 
        apply arr_seq_empty; auto with zarith.
        apply: conj. 
        have: (j + 1 - 1)%Z = j by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        apply: conj. 
        rewrite - H_stt_l_st''_ijm.
        have: (i + j - m - 1)%Z = (i + j - (m + 1))%Z by auto with zarith. move->.
        apply arr_seq_singleton; auto with zarith.
        move=> z3. simpl. repeat rewrite add_zero=>//.  
        apply: conj.
        (*  exists zs : seq Z, arr_seq T param0 (i + j - m - 1) st'' zs /\ sorted zs *)
        exists (zs3 ++ [:: stt_l st'' (l + i + j - (m + 1))%Z]).
        apply: conj.
        apply H_arr_seq_T_st''_ext.
        apply H_sorted_z3_ext.
        apply: conj.
        (* (exists zs : seq Z, arr_seq S param0 n st zs /\ arr_seq S param0 n st'' zs) *)
        have H_ex_zs_arrseq: exists zs, arr_seq S param0 n st zs
            by apply arr_seq_ex with (l:=lS); auto with zarith.
        inversion H_ex_zs_arrseq as [zs' H_arrseq_S_zs']; clear H_ex_zs_arrseq.
        exists zs'.
        apply: conj. auto.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st) (l:=lS); auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n)
                                  (st:=st) (l1:=lS) (l2:=l) (z1:=z3) (z2:=z1) (z:=z2);
          auto with zarith. 
        apply: conj.
        (* preservation of initial fragment of T *)
        have H_ex_zs_arrseq_T_st_zs: exists zs, arr_seq T param0 (i+j-(m+1)-1) st zs
            by apply arr_seq_ex with (l:=l); auto with zarith.
        inversion H_ex_zs_arrseq_T_st_zs as [zs_T H_arrseq_T_zs_T];
          clear H_ex_zs_arrseq_T_st_zs.
        exists zs_T.
        apply: conj. auto. 
        apply arr_seq_eq_deep with (X1:=T) (st1:=st) (l:=l); auto with arith.
        some_eq H25 H_st''_T.
        move=> z3 H_prm0_z3 H_z3_ijm.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        rewrite st_upd_neq_loc; auto.
        rewrite H_z1. auto with zarith.
        
        (* goal with Sx_ge_Tk_1 *)
        apply: conj.
        move=> H_jim_rgn.
        inversion H_jim_rgn as [H_i_le_m H_ijm_ge_]; clear H_jim_rgn.
        rewrite /Sx_ge_Tk_1.
        exists lS. exists l. exists i. exists (i+j-m)%Z.
        repeat (try apply: conj=>//).
        have: (l + (i + j - m) - 1)%Z = (l + (i + j - (m + 1)))%Z
          by auto with zarith. move->.
        rewrite -H_z1. rewrite {2}En_st''.
        repeat (try rewrite st_upd_var_loc). rewrite st_upd_eq_loc.
        rewrite H_z2.
        have: stt_l st (lS + i)%Z = stt_l st'' (lS + i)%Z.
        {
          rewrite En_st''. repeat (try rewrite st_upd_var_loc).
          apply st_upd_loc_sep with
              (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n) (st:=st)
              (l1:=lS) (l2:=l) (z1:=i) (z2:=z1) (z:=z2);
            auto with zarith. 
        }
        move<-.
        apply Z.le_ge. move: EnlSij. move /Z.leb_gt. auto with zarith.

        move=> H_ijm_rgn_contra.
        inversion H_ijm_rgn_contra as [H_j1_le_n H_ijm_ge_];
          clear H_ijm_rgn_contra.
        apply H_cp in H_j1_le_n. inv H_j1_le_n.

      * (* there is some info about result of first round execution in the spec *)
        inversion H_exP as [P [H_spec_P H_P_r]]; clear H_exP.
        inversion H_spec_P.
        rename H48 into H_fun_r_eq_P.
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
        rewrite <- H_zs4_ in *.
        clear zs4 H_zs4_.
        rename H45 into H_sorted_zs2'.
        rename H42 into H_arrseq_S_st''; clear H_arrseq_S_st''.

        rename H41 into H_arrseq_S_st''_zs0. rename H44 into H_sorted_zs0.
        clear zs0 H_arrseq_S_st''_zs0 H_sorted_zs0.
        rename H43 into H_arrseq_T_st''_zs5. rename H46 into H_sorted_zs5.
        clear zs5 H_arrseq_T_st''_zs5 H_sorted_zs5.

        inversion H_P_r as 
            [i' [j'0 [k' [H_i'0 [H_j' [H_k' [H_ijkm_or [H_k'_ [H_m_ [H_n_ [H_S_ [H_T_ H'']]]]]]]]]]]];
          clear H_P_r.
        inversion H'' as
            [H_occ' [H_sorted' [H_S_preserve' [H_T_preserve' [H_Sx_ge_Tk_1_i' H_Sx_ge_Tk_1_j']]]]];
          clear H''.
        
        exists i'. exists j'0. exists k'.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj. by assumption.
        apply: conj.
        inv H_ijkm_or.
        left; auto with zarith. right; auto with zarith.
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

        have H_arrseq_S_j_1_st: arr_seq S (j + 1) (j'0 - 1) st zs20.
        {
          apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
            auto with zarith.
          rewrite En_st''. repeat rewrite st_upd_var_arr.
          rewrite st_upd_loc_arr=>//.
          move=> z3 H_jz3 H_z3j0.
          rewrite En_st''. repeat rewrite st_upd_var_loc.
          symmetry.
          apply st_upd_loc_sep with
              (X1:=S) (b1:=param0) (e1:=n) (X2:=T)
              (b2:=param0) (e2:=n) (l2:=l) (z2:=z1) (z:=z2);
            auto with zarith.
        }
        apply: conj.
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS);
          auto with zarith.
        some_eq EnS H_st''_S.
        move=> z3 H_iz3 H_z3i'_1.
        rewrite En_st''. repeat rewrite st_upd_var_loc.
        symmetry.
        by apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n)
                                     (X2:=T) (b2:=param0) (e2:=n);
          auto with zarith.
        apply: conj. 
        have: stt_l st (lS + j)%Z :: zs20 = [:: stt_l st (lS + j)%Z] ++ zs20
          by simpl; auto. move->.
        apply arr_seq_concat_general with (e1:=j); auto with zarith. by
            apply arr_seq_singleton; auto with zarith.
        apply: conj.
        have: (i + j - (m+1))%Z = (k - 1)%Z by auto with zarith.
        move->.
        have: stt_l st (lS + j)%Z :: zs30 = [:: stt_l st (lS + j)%Z] ++ zs30
          by auto.
        move->.
        apply arr_seq_concat with (e1:=(k-1)%Z); auto with zarith.
        inversion H_S_preserve' as
            [zs [H_arrseq_S_st'' H_arrseq_S_r]]; clear H_S_preserve'.

        rewrite <- H_stt_l_st''_ijm.
        have: (l + (i + j - (m + 1)))%Z = (k - 1 + l)%Z by auto with zarith.
        move->.
        have: stt_l st'' (l + (k-1))%Z = stt_l r (l + (k-1))%Z.
        {
          inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]]. 
          apply arr_seq_ele_eq with (X:=T) (b:=param0) (e:=(k-1)%Z) (zs:=zs_T);
            auto with zarith.
          congruence.
        }
        have: (k - 1 + l)%Z = (l + (k - 1))%Z by auto with zarith.
        move->. move->.
        apply arr_seq_singleton; auto with zarith.
        congruence.
        have: (k - 1 + 1)%Z = k by auto with zarith.
        move->. auto.
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

        apply: conj.
        (* preservation of content of S *)
        inversion H_S_preserve' as [zs_S [H_arrseq_S_st'' H_arrseq_S_r]].
        exists zs_S. apply: conj; [ | auto].
        apply arr_seq_eq_deep with (X1:=S) (st1:=st'') (l:=lS); auto with zarith.
        congruence. 
        move=> z3 H_prm0z3 H_z3n.
        rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
        apply st_upd_loc_sep with (X1:=S) (b1:=param0) (e1:=n) (X2:=T) (b2:=param0) (e2:=n);
          auto with zarith.

        apply: conj.
        (* preservation of content of initial fragment of T *)
        have H_ijm_rgn: (0 <= i + j - (m + 1))%Z by auto with zarith.
        have: (0 < i + j - (m + 1))%Z \/ (0 = i + j - (m + 1))%Z
          by apply Zle_lt_or_eq; auto.
        case=> H_cs.
        (* first case *)
        inversion H_T_preserve' as [zs_T [H_arrseq_T_st'' H_arrseq_T_r]].
        have H_ex_T': exists zs_T', arr_seq T param0 (i+j-(m+1)-1) r zs_T'.
        { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
        inversion H_ex_T' as [zs_T' H_arrseq_T_zs_T']; clear H_ex_T'.
        have H_arrseq_T_st''_zs_T': arr_seq T param0 (i+j-(m+1)-1) st'' zs_T'
          by apply arr_seq_subrgn with (b:=param0) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
          auto with zarith.
        have H_arrseq_T_st_zs_T': arr_seq T param0 (i+j-(m+1)-1) st zs_T'.
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

  - (* proof for second loop *)
    inv H; subst. clear H0.
    rename H13 into H_rule_wh.
    inv H_rule_wh; subst.
    (* refute exiting the loop *)
    2: {
      rename H9 into H_i_le_m.
      rename H11 into Hcond.
      simpl in Hcond. rewrite H5 in Hcond. rewrite H1 in Hcond.
      have: (i <=? m)%Z = false by inv Hcond; auto.
      move /Z.leb_gt=> contra. 
      apply Zlt_not_le in contra. apply contra in H_i_le_m.
      inv H_i_le_m.
    }
    (* entering the loop *)
    rename H11 into Hcond.
    rename H14 into Hforall. 
    ith_prem_exe_0 Hforall H' mg_spec.
    ith_prem_exe_0 h h' mg_spec. clear h0.
    ith_prem_exe_1 h h' mg_spec.
    ith_prem_exe_0 h0 h' mg_spec. clear h1.
    ith_prem_exe_1 h0 h' mg_spec. clear h1.
    clear H_rule_wh.
    
    fold (com_ab i_id m_id) in Hforall.
    rename H19 into H_eval_Si.
    rename H22 into H_eval_i_1.
    rename H24 into H_eval_k_1.
    rename H16 into H_st_T.
    rename H12 into H_sep_S_T.

    ith_prem_1 Hforall h'.
    move En_st'':
      (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) i_id z) k_id z0)
    => st''.
    symmetry in En_st''. rewrite <- En_st'' in *.

    have H_z: z = (i+1)%Z.
    {
      simpl in H_eval_i_1. rewrite st_upd_loc_var in H_eval_i_1.
      rewrite H1 in H_eval_i_1. inv H_eval_i_1; auto.
    }
    move En_j: (n+1)%Z => j. 
    have H_z0: z0 = (i+j-m)%Z.
    {
      simpl in H_eval_k_1. updsimp_h H_eval_k_1.
      rewrite st_upd_loc_var in H_eval_k_1. 
      rewrite H3 in H_eval_k_1.
      inv H_eval_k_1; auto with zarith.
    }
    have H_z1: z1 = (i+j-(m+1))%Z.
    {
      rename H18 into H_eval_k. simpl in H_eval_k.
      rewrite En_j in H3.
      some_eq H_eval_k H3.
    }
    have H_st''_i: stt_v st'' i_id = Some (i + 1)%Z.
    { rewrite En_st''. updsimp. rewrite H_z; auto. }
    have H_st''_j: stt_v st'' j_id = Some j.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var; auto. rewrite <- En_j; auto. }
    have H_st''_k: stt_v st'' k_id = Some (i + j - m)%Z.
    { rewrite En_st''. updsimp. rewrite H_z0; auto with zarith. }
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
    have H_exP_cond:
      (i + 1 <= m)%Z ->
      (exists P : waf_rconfig -> Prop, mg_spec param0 (com_ab i_id m_id, st'', mg_prog) P).
    {
      move=> H_i_1_m.
      eexists.
      eapply WAF_SP_com_im with
          (st:=st'') (i:=(i+1)%Z) (j:=j) (k:=(i+j-m)%Z) (m:=m) (n:=n).
      apply H_st''_i.
      apply H_st''_j.
      apply H_st''_k.
      auto with zarith.
      apply H_st''_m.
      apply H_st''_n.
      assumption. (* (0 <= param0)%Z *)
      auto with zarith. (* (param0 <= i + 1)%Z *)
      assumption.
      assumption. (* m < n *)
      auto. (* j = n+1 *)
      apply sep_change_st with (X1:=S) (X2:=T) (st:=st); auto.
    }
    have: exists l, stt_a st S = Some l
        by apply sep_ex_loc_1 with (l1:=param0) (h1:=n) (l2:=param0) (h2:=n) (X2:=T); auto.
    elim=> [lS H_lS].
    have H_z2: z2 = stt_l st (lS + i)%Z.
    {
      simpl in H_eval_Si. rewrite H_lS in H_eval_Si.
      rewrite H1 in H_eval_Si.
      case En: (i >=? 0)%Z;
        case En': (lS + i <? floc_of st)%Z;
        rewrite En En' in H_eval_Si; simpl in H_eval_Si;
          try inv H_eval_Si; auto.
    }
    have H_st_lSi_st''_: stt_l st (lS+i)%Z = stt_l st'' (l+i+j-(m+1))%Z.
    {
      rewrite En_st''. repeat rewrite st_upd_var_loc.
      have: (l + i + j - (m + 1))%Z = (l + z1)%Z by auto with zarith.
      move->. rewrite st_upd_eq_loc=>//.
    }
    
    inversion h' as [H_nexP | H_exP].
    * (* there is no info about result of first round execution in the spec *)
      inversion H_nexP as [H_nP H_inf]; clear H_nexP.
      specialize (contra_pos _ _ H_exP_cond) as H_cp.
      specialize (H_cp H_nP).
      move: H_z H_z0 En_st''.
      inversion H_inf; subst.
      rename H11 into H_rule_wh'.
      inversion H_rule_wh'; clear H_rule_wh'.
      (* the true case, which is not possible *)
      clear H15. move=> H_z1 H_z2 En_st''.
      rename H11 into H_cond_ev_true.
      simpl in H_cond_ev_true.
      rewrite H_st''_i in H_cond_ev_true. rewrite H_st''_m in H_cond_ev_true.
      have contra: (i + 1 <=? m)%Z = true
        by inv H_cond_ev_true; auto.
      apply Zle_bool_imp_le in contra. apply H_cp in contra. inv contra.
      (* the false case *)
      clear H15. move=> H_z1 H_z2 En_st''.
      rename H19 into H_st''_eq_r. rewrite <- H_st''_eq_r in *.
      clear r H_st''_eq_r.
      rename H16 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
      rename H4 into H_crs_emp. clear crs H_crs_emp H12.
      rename H17 into H_p_eq_myprog. clear p H_p_eq_myprog.
      rename H0 into H_b_eq_ble. clear b H_b_eq_ble.
      (* establish the false condition *)
      move En_j: (n + 1)%Z => j. 
      exists (i+1)%Z. exists j. exists (i+j-m)%Z.
      apply: conj. by assumption.
      apply: conj. rewrite H_st''_j; rewrite En_j; by auto.
      apply: conj. rewrite <- En_j; by auto.
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
      have: (i + j - m - 1)%Z = (i + j - (m + 1))%Z by auto with zarith.
      move->.
      rewrite H_st_lSi_st''_.
      rewrite En_j.
      have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z
        by auto with zarith.
      move->.
      apply arr_seq_singleton; auto with zarith.
      congruence.
      (* preservation of initial fragment of T *)
      have: exists zs, arr_seq T param0 (i+j-(m+1)-1)%Z st'' zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim => [zs_T H_arrseq_T_st''_zs_T].
      exists zs_T.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l);
        auto with zarith.
      congruence.
      move=> z1 H_prm0_z1 H_z1_ijm.
      rewrite En_st''. repeat rewrite st_upd_var_loc.
      rewrite st_upd_neq_loc; auto with zarith.

    * (* there is some info about result of first round execution in the spec *)
      inversion H_exP as [P [H_spec_P H_P_r]].
      inv H_spec_P.
      rename H27 into H_fun_r_eq_P. rewrite <- H_fun_r_eq_P in H_P_r.
      clear H_fun_r_eq_P.
      inversion H_P_r as
          [i' [j' [k' [H_i' [H_j' [H_k' [H_i'_i0 [H_i'_m0_1 [H_j'_j0 [H_k'_ H_body]]]]]]]]]];
        clear H_P_r.
      inversion H_body as [H_m0 [H_n0 [H_st''_T [H_ex_S_T H_T_preserve]]]]; clear H_body.
      have H_i_1_i0: (i + 1)%Z = i0 by some_eq H_st''_i H4.
      have H_j_j0: j = j0 by rename H11 into H_st''_j0; some_eq H_st''_j0 H_st''_j.
      have H_m_m0: m = m0 by rename H16 into H_st''_m0; some_eq H_st''_m0 H_st''_m.
      have H_n_n0: n = n0 by rename H17 into H_st''_n0; some_eq H_st''_n0 H_st''_n.
      rewrite <- H_i_1_i0 in *.
      rewrite <- H_j_j0 in *.
      rewrite <- H_m_m0 in *. 
      rewrite <- H_n_n0 in *.
      clear i0 H_i_1_i0. clear j0 H_j_j0. clear m0 H_m_m0. clear n0 H_n_n0.
      symmetry in H_j'_j0. rewrite <- H_j'_j0 in *. clear j' H_j'_j0.
      
      exists i'. exists j. exists k'.
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
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }
      apply arr_seq_concat_general with (e1:=i); auto with zarith.
      apply arr_seq_singleton; auto with zarith.      
      
      apply arr_seq_concat_general with (e1:=(i+j-(m+1))%Z); auto with zarith.        
      rewrite H_st_lSi_st''_.
      have: (l + i + j - (m + 1))%Z = (l + (i + j - (m + 1)))%Z
        by auto with zarith.
      move->. 
      have: stt_l st'' (l + (i + j - (m + 1)))%Z = stt_l r (l + (i + j - (m + 1)))%Z.
      {
        inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]].
        apply arr_seq_ele_eq with (X:=T) (b:=param0) (e:=(k-1)%Z) (zs:=zs_T);
          auto with zarith.
        congruence. congruence.
      }
      move->.
      apply arr_seq_singleton; auto with zarith. congruence.
      have: (i + j - (m + 1) + 1)%Z = k by auto with zarith. move->.
      auto.

      (* preservation of initial fragment of T *) 
      inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]];
        clear H_T_preserve.
      have: exists zs, arr_seq T param0 (i + j - (m + 1) - 1) r zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim=> [zs_T' H_arrseq_T_r_zs_T'].
      have H_arrseq_T_st''_zs_T': arr_seq T param0 (i + j - (m + 1) - 1) st'' zs_T'.
      apply arr_seq_subrgn with (b:=param0) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
        auto with zarith.
      exists zs_T'.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z3 H_prm0_z3 H_z3_ijm.
      rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
      rewrite st_upd_neq_loc; auto with zarith.

  - (* proof for 3rd loop *)
    inv H; subst. clear H0.
    rename H13 into H_rule_wh.
    inv H_rule_wh; subst.
    (* refute exiting the loop *)
    2: {
      rename H10 into H_j_le_n.
      rename H11 into Hcond.
      simpl in Hcond. rewrite H2 in Hcond. rewrite H6 in Hcond.
      have: (j <=? n)%Z = false by inv Hcond; auto.
      move /Z.leb_gt=> contra. 
      apply Zlt_not_le in contra. apply contra in H_j_le_n.
      inv H_j_le_n.
    }
    (* entering the loop *)
    rename H11 into Hcond.
    rename H14 into Hforall. 
    ith_prem_exe_0 Hforall H' mg_spec.
    ith_prem_exe_0 h h' mg_spec. clear h0.
    ith_prem_exe_1 h h' mg_spec.
    ith_prem_exe_0 h0 h' mg_spec. clear h1.
    ith_prem_exe_1 h0 h' mg_spec. clear h1.
    clear H_rule_wh.
    
    fold (com_ab j_id n_id) in Hforall.
    rename H19 into H_eval_Sj.
    rename H22 into H_eval_j_1.
    rename H24 into H_eval_k_1.
    rename H16 into H_st_T.
    rename H12 into H_sep_S_T.

    ith_prem_1 Hforall h'.
    move En_st'':
      (state_upd_var (state_upd_var (state_upd_loc st (l + z1) z2) j_id z) k_id z0)
    => st''.
    symmetry in En_st''. rewrite <- En_st'' in *.

    have H_z: z = (j+1)%Z.
    {
      simpl in H_eval_j_1. rewrite st_upd_loc_var in H_eval_j_1.
      rewrite H2 in H_eval_j_1. inv H_eval_j_1; auto.
    }
    move En_i: (m+1)%Z => i. 
    have H_z0: z0 = (j + 1)%Z.
    {
      simpl in H_eval_k_1. updsimp_h H_eval_k_1.
      rewrite st_upd_loc_var in H_eval_k_1. 
      rewrite H3 in H_eval_k_1.
      inv H_eval_k_1; auto with zarith.
    }
    have H_z1: z1 = j.
    {
      rename H18 into H_eval_k. simpl in H_eval_k.
      rewrite H_eval_k in H3. inv H3; auto with zarith.
    }
    have H_st''_j: stt_v st'' j_id = Some (j + 1)%Z.
    { rewrite En_st''. updsimp. rewrite H_z; auto. }
    have H_st''_i: stt_v st'' i_id = Some i.
    { rewrite En_st''. updsimp. rewrite st_upd_loc_var; auto. rewrite <- En_i; auto. }
    have H_st''_k: stt_v st'' k_id = Some (j+1)%Z.
    { rewrite En_st''. updsimp. rewrite H_z0; auto with zarith. }
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
    have H_exP_cond:
      (j + 1 <= n)%Z ->
      (exists P : waf_rconfig -> Prop, mg_spec param0 (com_ab j_id n_id, st'', mg_prog) P).
    {
      move=> H_j_1_n.
      eexists.
      eapply WAF_SP_com_jn with
          (st:=st'') (i:=i) (j:=(j+1)%Z) (k:=(j+1)%Z) (m:=m) (n:=n).
      apply H_st''_i.
      apply H_st''_j.
      apply H_st''_k.
      auto with zarith.
      apply H_st''_m.
      apply H_st''_n.
      assumption. (* (0 <= param0)%Z *)
      auto with zarith. (* (param0 <= i)%Z *)
      auto with zarith.
      assumption. (* m < n *)
      auto. (* i = m+1 *)
      apply sep_change_st with (X1:=S) (X2:=T) (st:=st); auto.
    }
    have: exists l, stt_a st S = Some l
        by apply sep_ex_loc_1 with (l1:=param0) (h1:=n) (l2:=param0) (h2:=n) (X2:=T); auto.
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
    have H_st_lSj_st''_: stt_l st (lS+j)%Z = stt_l st'' (l+i+j-(m+1))%Z.
    {
      rewrite En_st''. repeat rewrite st_upd_var_loc.
      have: (l + i + j - (m + 1))%Z = (l + z1)%Z by auto with zarith.
      move->. rewrite st_upd_eq_loc=>//.
    }
    
    inversion h' as [H_nexP | H_exP].
    * (* there is no info about result of first round execution in the spec *)
      inversion H_nexP as [H_nP H_inf]; clear H_nexP.
      specialize (contra_pos _ _ H_exP_cond) as H_cp.
      specialize (H_cp H_nP).
      move: H_z H_z0 En_st''.
      inversion H_inf; subst.
      rename H11 into H_rule_wh'.
      inversion H_rule_wh'; clear H_rule_wh'.
      (* the true case, which is not possible *)
      clear H15. move=> H_z1 H_z2 En_st''.
      rename H11 into H_cond_ev_true.
      simpl in H_cond_ev_true.
      rewrite H_st''_j in H_cond_ev_true. rewrite H_st''_n in H_cond_ev_true.
      have contra: (j + 1 <=? n)%Z = true
        by inv H_cond_ev_true; auto.
      apply Zle_bool_imp_le in contra. apply H_cp in contra. inv contra.
      (* the false case *)
      clear H15. move=> H_z1 H_z2 En_st''.
      rename H19 into H_st''_eq_r. rewrite <- H_st''_eq_r in *.
      clear r H_st''_eq_r.
      rename H16 into H_st0_eq_st''. clear st0 H_st0_eq_st''.
      rename H4 into H_crs_emp. clear crs H_crs_emp H12.
      rename H17 into H_p_eq_myprog. clear p H_p_eq_myprog.
      rename H0 into H_b_eq_ble. clear b H_b_eq_ble.
      (* establish the false condition *)
      move En_i: (m + 1)%Z => i. 
      exists i. exists (j + 1)%Z. exists (j + 1)%Z.
      apply: conj. rewrite En_i in H_st''_i; by assumption.
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
      have: (i + j - i)%Z = j by auto with zarith. move->.
      have: (j + 1 - 1)%Z = j by auto with zarith. move->.
      rewrite H_st_lSj_st''_.
      rewrite En_i.
      have: (l + i + j - i)%Z = (l + j)%Z by auto with zarith. move->.
      apply arr_seq_singleton; auto with zarith.
      congruence.
      
      (* preservation of initial fragment of T *)
      have: exists zs, arr_seq T param0 (j - 1)%Z st'' zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim => [zs_T H_arrseq_T_st''_zs_T].
      exists zs_T.
      apply: conj=>//.
      have: (i + j - i - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l);
        auto with zarith.
      congruence.
      move=> z1 H_prm0_z1 H_z1_j_1.
      rewrite En_st''. repeat rewrite st_upd_var_loc.
      rewrite st_upd_neq_loc; auto with zarith.
      have: (i + j - i - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      auto.

    * (* there is some info about result of first round execution in the spec *)
      inversion H_exP as [P [H_spec_P H_P_r]].
      inv H_spec_P.
      rename H27 into H_fun_r_eq_P. rewrite <- H_fun_r_eq_P in H_P_r.
      clear H_fun_r_eq_P.
      inversion H_P_r as
          [i' [j' [k' [H_i' [H_j' [H_k' [H_i'_i0 [H_i'_m0_1 [H_j'_j0 [H_k'_ H_body]]]]]]]]]];
        clear H_P_r.
      inversion H_body as [H_m0 [H_n0 [H_st''_T [H_ex_S_T H_T_preserve]]]]; clear H_body.
      have H_j_1_j0: (j + 1)%Z = j0 by some_eq H_st''_j H11.
      have H_i_i0: i = i0 by rename H4 into H_st''_i0; some_eq H_st''_i0 H_st''_i.
      have H_m_m0: m = m0 by rename H16 into H_st''_m0; some_eq H_st''_m0 H_st''_m.
      have H_n_n0: n = n0 by rename H17 into H_st''_n0; some_eq H_st''_n0 H_st''_n.
      rewrite <- H_j_1_j0 in *.
      rewrite <- H_i_i0 in *.
      rewrite <- H_m_m0 in *. 
      rewrite <- H_n_n0 in *.
      clear j0 H_j_1_j0. clear i0 H_i_i0. clear m0 H_m_m0. clear n0 H_n_n0.
      symmetry in H_i'_i0. rewrite <- H_i'_i0 in *. clear i' H_i'_i0.
      
      exists i. exists j'. exists k'.
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
            (X1:=S) (X2:=T) (b1:=param0) (e1:=n) (b2:=param0) (e2:=n);
          auto with zarith.
      }
      apply arr_seq_concat_general with (e1:=j); auto with zarith.
      apply arr_seq_singleton; auto with zarith.      
      rewrite H_st_lSj_st''_.
      have: (i + j - i)%Z = j by auto with zarith. move->.
      have: (l + i + j - (m + 1))%Z = (l + j)%Z by auto with zarith. move->.
      apply arr_seq_concat_general with (e1:=j); auto with zarith.
      have: stt_l st'' (l + j)%Z = stt_l r (l + j)%Z.
      {
        inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]].
        apply arr_seq_ele_eq with (X:=T) (b:=param0) (e:=(k-1)%Z) (zs:=zs_T);
          auto with zarith.
        congruence. congruence.
      }
      move->.
      apply arr_seq_singleton; auto with zarith. congruence.

      have: (j + 1)%Z = k by auto with zarith. move->. auto.
      
      (* preservation of initial fragment of T *) 
      inversion H_T_preserve as [zs_T [H_arrseq_T_st''_zs_T H_arrseq_T_r_zs_T]];
        clear H_T_preserve.
      have: (i + j - i - 1)%Z = (j - 1)%Z by auto with zarith. move->.
      have: exists zs, arr_seq T param0 (j - 1) r zs.
      { apply arr_seq_ex with (l:=l); auto with zarith. congruence. }
      elim=> [zs_T' H_arrseq_T_r_zs_T'].
      have H_arrseq_T_st''_zs_T': arr_seq T param0 (j - 1) st'' zs_T'
        by apply arr_seq_subrgn with (b:=param0) (e:=(k-1)%Z) (st1:=r) (zs:=zs_T);
        auto with zarith.
      exists zs_T'.
      apply: conj=>//.
      apply arr_seq_eq_deep with (X1:=T) (st1:=st'') (l:=l); auto with zarith.
      congruence.
      move=> z3 H_prm0_z3 H_z3_j_1.
      rewrite En_st''. repeat rewrite st_upd_var_loc. symmetry.
      rewrite st_upd_neq_loc; auto with zarith.

Qed.

