
From mathcomp Require Import ssreflect eqtype ssrbool seq.

From indv Require Import tactics lang. 

Lemma st_upd_eq: forall s x z, (st_upd s x z) x = z.
Proof. move=> s x z. rewrite /st_upd. elim: eqP=>//. Qed.

Lemma st_upd_neq: forall s x z x', x <> x' -> (st_upd s x z) x' = s x'.
Proof. move=> s x z x' H_neq. rewrite /st_upd. elim: eqP=>//. Qed. 

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
