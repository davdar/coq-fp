Require Coq.Bool.Bool.

Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.

Section EqDec.
  Global Instance bool_EqDec : EqDec bool := { eq_dec := Bool.eqb }.
  Global Instance bool_Eq_RelDecCorrect : RelDecCorrect bool eq eq_dec.
  Proof. constructor ; destruct x ; destruct y ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance bool_Eqv : Eqv bool := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance bool_EqvDec : EqvDec bool := { eqv_dec := eq_dec }.
  Global Instance bool_Eqv_RelDecCorrect : RelDecCorrect bool eqv eqv_dec.
  Proof. apply bool_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Ord.
  Definition bool_lt x y := x = false /\ y = true.
  Global Instance bool_Ord : Ord bool := { lt := bool_lt }.
End Ord.

Section LteDec.
  Definition bool_ord_dec x y :=
    match x, y with
    | true, true => Eq
    | false, true => Lt
    | true, false => Gt
    | false, false => Eq
    end.
  Global Instance bool_OrdDec : OrdDec bool := { ord_dec := bool_ord_dec  }.
End LteDec.