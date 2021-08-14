
Require Import Coq.Program.Basics. 
From mathcomp
     Require Import ssreflect eqtype ssrnat ssrbool seq.

From indv Require Import arith.

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
