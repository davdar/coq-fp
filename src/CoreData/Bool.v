Require Coq.Bool.Bool.

Module BoolNotation.
  Infix "||" := orb.
  Infix "&&" := andb.
End BoolNotation.
Import BoolNotation.

Definition consider_bool (b:bool) : {b=true}+{b=false}.
Proof. destruct (Bool.bool_dec b true) as [H | H] ; eauto.
  apply Bool.not_true_is_false in H ; eauto.
Qed.

Definition orf {A} (f:A -> bool) (g:A -> bool) (a:A) : bool := f a || g a.
Definition andf {A} (f:A -> bool) (g:A -> bool) (a:A) : bool := f a && g a.

Lemma bool_conj_true : forall b1 b2, (b1 && b2) = true <-> b1 = true /\ b2 = true.
Proof.
  intros ; constructor ; intros.
  - destruct b1,b2 ; auto.
  - destruct b1,b2 ; auto.
    destruct H as [H1 H2] ; discriminate H2.
    destruct H as [H1 H2] ; discriminate H1.
    destruct H as [H1 H2] ; discriminate H1.
Qed.
