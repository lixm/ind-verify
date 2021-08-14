
Require Import List. 
From mathcomp Require Import ssreflect seq.

Require Import sem.

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

Ltac ith_prem_exe hyp_alli i p hyp_as spec :=
  let h := fresh "h" in (
    ith_prem hyp_alli i p hyp_as; 
    inversion hyp_as as [H_nex | H_ex]; clear hyp_as;
    [
      inversion H_nex as [H_ne H_inf']; clear H_nex H_ne;
      inversion H_inf' as [c r' crs H_rule' h]; subst; clear H_inf';
      inversion H_rule'; subst; clear H_rule' |      
      inversion H_ex; 
      match goal with | [ H: spec _ _ _ /\ _ |- _ ] => inversion H end;
      match goal with | [ H: spec _ _ _ |- _ ] => inversion H end
  ]).

Ltac ith_prem_0 hyp_alli hyp_as :=
  match type of hyp_alli with
    (forall _ _, nth_error ?lst _ = _ -> _) => (
      match lst with
        nil => idtac
      | ?p :: _ => ith_prem hyp_alli 0 p hyp_as
      end
    )
  end.

Ltac ith_prem_1 hyp_alli hyp_as :=
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

Ltac ith_prem_2 hyp_alli hyp_as :=
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
  
Ltac ith_prem_exe_0 hyp_alli hyp_as spec :=
  let h := fresh "h" in (
    match type of hyp_alli with
    | (forall _ _, nth_error ?lst _ = _ -> _) => (
        match lst with
          nil => idtac 
        | ?p :: _ => ith_prem_exe hyp_alli 0 p hyp_as spec
        end)
    end).

Ltac ith_prem_exe_1 hyp_alli hyp_as spec :=
  let h := fresh "h" in (
    match type of hyp_alli with
    | (forall _ _, nth_error ?lst _ = _ -> _) => (
        match lst with
          nil => idtac
        | ?p :: ?lst' => (
            match lst' with
              nil => idtac
            | ?p' :: ?lst'' => ith_prem_exe hyp_alli 1 p' hyp_as spec
            end)
        end)
    end).

Ltac ith_prem_exe_2 hyp_alli hyp_as spec :=
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
                  ith_prem_exe hyp_alli 2 p'' hyp_as spec
                end)
            end)
        end)
    end).

