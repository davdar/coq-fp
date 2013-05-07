Require Import FP.Data.String.
Require Import FP.Data.Ascii.
Require Import FP.Data.AsciiRelations.
Require Import FP.Data.List.
Require Import FP.Data.ListRelations.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.

Import FunctionNotation.

Section EqDec.
  Definition string_eq_dec := eq_dec `on` string2list.

  Global Instance string_EqDec : EqDec string := { eq_dec := string_eq_dec }.
  Global Instance string_Eq_RelDecCorrect : RelDecCorrect string eq eq_dec.
  Admitted.
End EqDec.

Section Eqv.
  Global Instance string_Eqv : Eqv string := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance string_EqvDec : EqvDec string := { eqv_dec := eq_dec }.
  Global Instance string_Eqv_RelDecCorrect : RelDecCorrect string eqv eqv_dec.
  Admitted.
End EqvDec.

Section Ord.
  Definition string_lt := lt `on` string2list.

  Global Instance string_Ord : Ord string := { lt := string_lt }.
End Ord.

Section OrdDec.
  Definition string_ord_dec := ord_dec `on` string2list.

  Global Instance string_OrdDec : OrdDec string := { ord_dec := string_ord_dec  }.
End OrdDec.
