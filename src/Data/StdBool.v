Require Import Bool.
Export Bool.

Require Import Equivalence.
Require Import RelDec.
Require Import Eq.
Require Import Eqv.
Require Import Lte.
Require Import Show.

Module BoolNotation.
  Infix "&&" := andb.
End BoolNotation.
Import BoolNotation.

Section EqDec.
  Global Instance bool_EqDec : EqDec bool := { eq_dec := eqb }.
  Global Instance bool_Eq_RelDecCorrect : RelDecCorrect (T:=bool) eq_dec eq.
  Proof. constructor ; destruct x ; destruct y ; simpl ; constructor ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance bool_Eqv : Eqv bool := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance bool_EqvDec : EqvDec bool := { eqv_dec := eqb }.
  Global Instance bool_Eqv_RelDecCorrect : RelDecCorrect (T:=bool) eqv_dec eqv.
  Proof. apply bool_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Lte.
  Global Instance bool_Lte : Lte bool := { lte := leb }.
  Global Instance bool_PreOrder : PreOrder (A:=bool) lte.
  Admitted.
End Lte.

Section LteDec.
  Global Instance bool_LteDec : LteDec bool := { lte_dec := implb  }.
  Global Instance bool_Lte_RelDecCorrect : RelDecCorrect (T:=bool) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Section bool_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition bool_show (x:bool) : R :=
      rawshow_string (if x then "true" else "false").
  End bool_show.

  Global Instance bool_Show : Show bool := { show := bool_show }.
End Show.
