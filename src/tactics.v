
Require Import List. 
From mathcomp Require Import ssreflect seq.

Require Import ZArith.
From indv Require Import sem.

Ltac inv h := inversion h. 

Ltac init_verif :=
  intros; apply soundness; unfold verif; intros.

Ltac rem_hd hyp :=
  match type of hyp with
  | (_ = _) -> ?P => have: P; [apply hyp=>// | ]
  end.

Ltac ith_prem hyp_alli i p hyp_as :=
  specialize (hyp_alli i p) as hyp_as; simpl in hyp_as;
  rem_hd hyp_as; clear hyp_as; intro hyp_as.

Ltac ith_prem_spec hyp_alli i p :=
  let hypas := fresh "hypas" with
    hspc := fresh "hspc" with
    hexe := fresh "hexe"
                 in (
                     specialize (hyp_alli i p) as hypas; simpl in hypas;
                     rem_hd hypas; clear hypas; intro hypas;
                     inversion hypas as [hspc hexe]; clear hypas; clear hexe
                   ).

Ltac ith_prem_exe hyp_alli i p :=
  let hypas := fresh "hypas" with
    hallP := fresh "hallP" with
    hnexP := fresh "hnexP" with
    hp := fresh "hp" with
    pp := fresh "pp" with
    hpp := fresh "hpp" with 
    hinf := fresh "hinf" with
    cc := fresh "cc" with 
    rr := fresh "rr" with
    crs := fresh "crs" with
    hrule := fresh "hrule" with
    hall := fresh "hall"
                 in (
                     ith_prem hyp_alli i p hypas; 
                     inversion hypas as [hallP hnexP];
                     clear hypas hallP;
                     (match type of hnexP with
                      | _ -> ?P => (
                          have: P by
                            (apply hnexP; intro hp; inversion hp as [pp hpp];
                             inversion hpp))
                      end;
                      clear hnexP; intro hinf;
                      inversion hinf as [cc rr crs hrule hall]; subst; clear hinf;
                      inversion hrule; subst; clear hrule)). 

Ltac prem0 hyp_alli hyp_as :=
  match type of hyp_alli with
    (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: _ => ith_prem hyp_alli 0 p hyp_as
      end
    )
  end.

Ltac prem0_spec hyp_alli :=
  match type of hyp_alli with
    (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: _ => ith_prem_spec hyp_alli 0 p 
      end
    )
  end.

Ltac prem1 hyp_alli hyp_as :=
  match type of hyp_alli with
  | (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: ?lst' => (
          match lst' with
            nil => idtac
          | ?p' :: ?lst'' => ith_prem hyp_alli 1 p' hyp_as
          end)
      end)
  end.

Ltac prem1_spec hyp_alli :=
  match type of hyp_alli with
  | (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: ?lst' => (
          match lst' with
            nil => idtac
          | ?p' :: ?lst'' => ith_prem_spec hyp_alli 1 p' 
          end)
      end)
  end.

Ltac prem2 hyp_alli hyp_as :=
  match type of hyp_alli with
  | (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: ?lst' => (
          match lst' with
            nil => idtac
          | ?p' :: ?lst'' => (
              match lst'' with
                nil => idtac
              | ?p'' :: ?lst''' => ith_prem hyp_alli 2 p'' hyp_as
              end)
          end)
      end)
  end.

Ltac prem2_spec hyp_alli :=
  match type of hyp_alli with
  | (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: ?lst' => (
          match lst' with
            nil => idtac
          | ?p' :: ?lst'' => (
              match lst'' with
                nil => idtac
              | ?p'' :: ?lst''' => ith_prem_spec hyp_alli 2 p'' 
              end)
          end)
      end)
  end. 
  
Ltac prem0_exe hyp_alli :=
  let h := fresh "h" in (
    match type of hyp_alli with
    | (forall _ _, nth_error ?lst _ = _ -> _) => (
        match lst with
          nil => idtac 
        | ?p :: _ => ith_prem_exe hyp_alli 0 p 
        end)
    end).

Ltac prem1_exe hyp_alli :=
  let h := fresh "h" in (
    match type of hyp_alli with
    | (forall _ _, nth_error ?lst _ = _ -> _) => (
        match lst with
          nil => idtac
        | ?p :: ?lst' => (
            match lst' with
              nil => idtac
            | ?p' :: ?lst'' => ith_prem_exe hyp_alli 1 p' 
            end)
        end)
    end).

Ltac prem2_exe hyp_alli :=
  let h := fresh "h" in (
    match type of hyp_alli with
    | (forall _ _, nth_error ?lst _ = _ -> _) => (
        match lst with
          nil => idtac
        | ?p :: ?lst' => (
            match lst' with
              nil => idtac
            | ?p' :: ?lst'' => (
                match lst'' with
                  nil => idtac
                | ?p'' :: ?lst''' =>
                  ith_prem_exe hyp_alli 2 p'' 
                end)
            end)
        end)
    end).

Ltac assert_in_spc hyp_spc := 
  match type of hyp_spc with
    forall P, ?S ?a ?b P -> P _ =>
    have: exists P, S a b P
  end.

(* hex is the proposition saying that pp is a set of result configs 
   given by the specification *)
Ltac use_spec hyp_spc :=
  let pp := fresh "pp" with hex := fresh "hex"
              in (
                  assert_in_spc hyp_spc;
                  [ |
                    elim=> [pp hex];
                           specialize (hyp_spc pp hex);
                           inversion hex; subst; clear hex;
                           inversion hyp_spc; subst; clear hyp_spc]).


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
            
