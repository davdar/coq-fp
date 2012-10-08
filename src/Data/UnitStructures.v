Require Export Data.Unit.

Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lte.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Section EqDec.
  Fixpoint unit_eq_dec (_x:unit) (_y:unit) : bool := true.
  Global Instance unit_EqDec : EqDec unit := { eq_dec := unit_eq_dec }.
  Global Instance unit_Eq_RelDecCorrect : RelDecCorrect (T:=unit) eq_dec eq.
  Proof. constructor ; destruct x ; destruct y ; simpl ; constructor ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance unit_Eqv : Eqv unit := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance unit_EqvDec : EqvDec unit := { eqv_dec := unit_eq_dec }.
  Global Instance unit_Eqv_RelDecCorrect : RelDecCorrect (T:=unit) eqv_dec eqv.
  Proof. apply unit_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Lte.
  Global Instance unit_Lte : Lte unit := { lte := eq }.
  Global Instance unit_PreOrder : PreOrder (A:=unit) lte.
  Admitted.
End Lte.

Section LteDec.
  Global Instance unit_LteDec : LteDec unit := { lte_dec := unit_eq_dec }.
  Global Instance unit_Lte_RelDecCorrect : RelDecCorrect (T:=unit) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Section unit_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition unit_show (_x:unit) : R := rawshow_string "tt".
  End unit_show.

  Global Instance unit_Show : Show unit := { show := unit_show }.
End Show.