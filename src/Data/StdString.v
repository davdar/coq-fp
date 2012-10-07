Require Import String.
Export String.

Require Import StdFun.
Import FunNotation.
Require Import StdList.
Import ListNotation.
Require Import StdAscii.
Require Import Equivalence.
Require Import RelDec.
Require Import Eq.
Import EqNotation.
Require Import Eqv.
Require Import Lte.
Require Import Show.
Require Import Monoid.
Import MonoidNotation.

Fixpoint string2list s :=
  match s with
  | EmptyString => nil
  | String c s' => c::string2list s'
  end.

Section EqDec.
  Definition string_eq_dec := eq_dec `on` string2list.

  Global Instance string_EqDec : EqDec string := { eq_dec := string_eq_dec }.
  Global Instance string_Eq_RelDecCorrect : RelDecCorrect (T:=string) eq_dec eq.
  Admitted.
End EqDec.

Section Eqv.
  Global Instance string_Eqv : Eqv string := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance string_EqvDec : EqvDec string := { eqv_dec := eq_dec }.
  Global Instance string_Eqv_RelDecCorrect : RelDecCorrect (T:=string) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Lte.
  Definition string_lte := lte `on` string2list.

  Global Instance string_Lte : Lte string := { lte := string_lte }.
  Global Instance string_PreOrder : PreOrder (A:=string) lte.
  Admitted.
End Lte.

Section LteDec.
  Definition string_lte_dec := lte_dec `on` string2list.

  Global Instance string_LteDec : LteDec string := { lte_dec := string_lte_dec  }.
  Global Instance string_Lte_RelDecCorrect : RelDecCorrect (T:=string) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Section string_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition string_show (s:string) : R :=
         rawshow_char """"
      ** rawshow_string s
      ** rawshow_char """".
  End string_show.

  Global Instance string_Show : Show string := { show := string_show }.
End Show.