Require Export Data.BoolPre.

Require Import Data.StringPre.

Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Ord.
Require Import Structures.Show.

Import StringNotation.

Section EqDec.
  Global Instance bool_EqDec : EqDec bool := { eq_dec := Bool.eqb }.
  Global Instance bool_Eq_RelDecCorrect : RelDecCorrect (T:=bool) eq_dec eq.
  Proof. constructor ; destruct x ; destruct y ; simpl ; constructor ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance bool_Eqv : Eqv bool := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance bool_EqvDec : EqvDec bool := { eqv_dec := eq_dec }.
  Global Instance bool_Eqv_RelDecCorrect : RelDecCorrect (T:=bool) eqv_dec eqv.
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

Section Show.
  Section bool_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition bool_show (x:bool) : R :=
      raw_string (if x then "true" else "false").
  End bool_show.

  Global Instance bool_Show : Show bool := { show := bool_show }.
End Show.