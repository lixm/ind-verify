
Require Import Classical.
Require Import List. 
From mathcomp Require Import ssreflect seq.

Class Sem (CFG : Type) (RCFG : Type) :=
  {
  rule : seq (prod CFG RCFG) -> (prod CFG RCFG) -> Prop
  }. 

Definition Spec (PARAM : Type) (CFG : Type) (RCFG : Type)
           (param : PARAM) :=
  CFG -> (RCFG -> Prop) -> Prop.

Inductive deriv {CFG} {RCFG} {sem : Sem CFG RCFG} 
  : (prod CFG RCFG)->Prop := 
  Der:
    forall c r lst,
      rule lst (c, r) ->
      (forall i p, nth_error lst i = Some p -> deriv p) -> 
      deriv (c, r).

(* definition of "res" inlined into definition of "infer" *)
Inductive infer {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}
          (param : PARAM) (phi : Spec PARAM CFG RCFG param)
  : (prod CFG RCFG) -> Prop :=
  Inf:
    forall c r crs,
      rule crs (c, r) ->
      (forall i p,
          nth_error crs i = Some p ->
          ((forall P, phi (fst p) P -> P (snd p)) /\
           (~(exists P, phi (fst p) P) -> infer param phi p))
          (* (((~(exists P, phi (fst p) P)) /\ infer param phi p) \/ *)
          (*  (exists P, phi (fst p) P /\ P (snd p))) *)
      ) ->
      infer param phi (c, r).

(* Check infer_ind. *)

(* The generated induction principle for infer is unusable. *)
(* We prove a custome induction principle for infer. *)
Fixpoint infer_ind'
         (PARAM CFG RCFG: Type)
         (sem: Sem CFG RCFG)
         (prm: PARAM)
         (phi: Spec PARAM CFG RCFG prm)
         (P: (prod CFG RCFG) -> Prop)
         (eInf: forall c r crs,
             rule crs (c, r) ->
             (forall i p',
                 nth_error crs i = Some p' ->
                 ((forall P', phi (fst p') P' -> P' (snd p')) /\
                  (~(exists P', phi (fst p') P') -> infer prm phi p'))) ->
             (forall i p',
                 nth_error crs i = Some p' ->
                 ((forall P', phi (fst p') P' -> P' (snd p')) /\
                  (~(exists P', phi (fst p') P') -> P p'))) ->
             P (c, r)
         )
         (p: prod CFG RCFG)
         (e: infer prm phi p)
  : P p.
  refine (match e with
          | Inf c r crs H_rule H' => _
          end).
  apply eInf with (crs:=crs)=>//.
  move=> i p' H_ip'.
  move: H'=> /(_ i p' H_ip')=> H'.
  inversion H' as [H_allP H_nexP].
  apply: conj=>//.
  move /H_nexP.
  apply: infer_ind'=>//.
Defined.    

Definition verif {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}
           (param : PARAM)
  : (Spec PARAM CFG RCFG param) -> Prop :=
  (fun phi =>
     (forall c r P,
         infer param phi (c, r) -> phi c P -> P r)). 

Definition valid {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}
           (param : PARAM) 
  : (Spec PARAM CFG RCFG param) -> Prop :=
  (fun phi =>
     (forall c r P,
         deriv (c, r) -> phi c P -> P r)).

Lemma deriv_impl_infer {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}:
  forall (prm: PARAM) (phi: Spec PARAM CFG RCFG prm) c r,
    verif prm phi -> deriv (c, r) -> infer prm phi (c, r).
Proof.
  move=> prm phi c r H_ver. 
  move En: (c, r)=> p0 H_deriv.
  move: H_deriv c r En.
  elim.
  move=> c r lst H_rule H_der_i IH c0 r0 H_eq.
  apply: Inf. apply: H_rule.
  move=> i p' H_ip'.
  move: IH=> /(_ i p' H_ip' (fst p') (snd p')).
  rewrite -surjective_pairing=> /(_ (eq_refl _))=> IH.
  rewrite /verif in H_ver.
  apply: conj.
  - move=> P.
    move: H_ver=> /(_ (fst p') (snd p') P).
    rewrite -surjective_pairing. move/(_ IH)=>//.
  - move=> H'. by apply: IH.
Qed.     
    
Theorem soundness {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}: 
  forall (param: PARAM) phi, verif param phi -> valid param phi.
Proof.
  move=> param phi H_ver.
  have H'_ver: verif param phi by done.
  rewrite /verif in H'_ver. rewrite /valid.
  move=> c r P H_der H_phic.
  have H_inf: infer param phi (c, r) by apply: deriv_impl_infer=>//. 
  move: H'_ver=> /(_ c r P H_inf H_phic)=>//.
Qed. 
  
Inductive phi_valid {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG} (param: PARAM):
  (Spec PARAM CFG RCFG param) :=
  PV c: phi_valid param c (fun r => deriv (c, r)).

Lemma phi_valid_infer_deriv {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}:
  forall (prm: PARAM) c r,
    infer prm (phi_valid prm) (c, r) -> deriv (c, r).
Proof.
  move=> prm c r.
  move En: (c, r)=> p.
  move En': (phi_valid prm)=> phiprm.
  move=> H_infer. move: H_infer c r En.
  elim /infer_ind'.
  move=> c r crs H_rule H_i IH c0 r0 H_eq.
  apply: Der. apply: H_rule.
  move=> i p0 H_ip0.
  move: IH=>/(_ i p0 H_ip0). elim=> [H_allP' H_nexP'].
  have: (exists P', phiprm (fst p0) P') \/ ~(exists P', phiprm (fst p0) P')
    by apply classic.
  elim=> [H_case_ex | H_case_nex].
  - inversion H_case_ex as [P' H_phiprm].
    move: H_allP'=> /(_ P').
    rewrite -En' in H_phiprm. 
    inversion H_phiprm; subst.
    move/(_ H_phiprm).
    rewrite -surjective_pairing=>//.
  - apply H_nexP' with (c:=fst p0) (r:=snd p0)=>//.
    rewrite -surjective_pairing=>//.
Qed.    
        
Lemma phi_valid_verifiable {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}:
  forall (prm: PARAM), verif prm (phi_valid prm).
Proof.
  move=> prm.
  rewrite /verif. 
  move=> c r P H_infer H_phi_v.
  inversion H_phi_v; subst.
  apply phi_valid_infer_deriv with (prm0:=prm)=>//.
Qed.  
  
Definition spec_le {PARAM} {CFG} {RCFG}
           (prm: PARAM) (phi phi' : Spec PARAM CFG RCFG prm) : Prop
  := 
  (forall c P, (phi c P ->
                (exists (P': RCFG->Prop),
                    (forall r, P' r -> P r) /\ phi' c P'))). 

Lemma valid_phi_le_phi_valid {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG} :
  forall (prm: PARAM) phi,
    valid prm phi -> spec_le prm phi (phi_valid prm).
Proof.
  rewrite /valid /spec_le. 
  move=> prm phi H_all c P H_phic.
  exists (fun r => deriv (c, r)).
  apply: conj. move=> r H_der.
  move: H_all=> /(_ c r P H_der H_phic)=>//.
  by apply: PV.  
Qed.

Theorem completeness {PARAM} {CFG} {RCFG} {sem : Sem CFG RCFG}:
  forall (prm: PARAM) (phi : Spec PARAM CFG RCFG prm),
    valid prm phi ->
    (exists phi', valid prm phi' /\
                  spec_le prm phi phi' /\
                  verif prm phi'). 
Proof.
  move=> prm phi H_valid.
  exists (phi_valid prm).
  apply: conj.
  rewrite /valid.
  move=> c r P H_der H_phi_valid.
  inversion H_phi_valid; subst=>//.
  apply: conj;
    [apply: valid_phi_le_phi_valid | apply: phi_valid_verifiable]=>//.
Qed.
