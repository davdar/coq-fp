Require Export Coq.Bool.Bool.

Definition consider_bool (b:bool) : {b=true}+{b=false}.
Proof. destruct (bool_dec b true) as [H | H] ; eauto.
  apply not_true_is_false in H ; eauto.
Qed.
