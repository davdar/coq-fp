Require Export Data.StringPre.

Require Import Data.FunctionPre.

Require Import Data.Ascii.
Require Import Data.List.
Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Injection.
Require Import Structures.Monoid.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Import CharNotation.
Import EqDecNotation.
Import FunctionNotation.
Import MonoidNotation.

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

Section Ord.
  Definition string_lt := lt `on` string2list.

  Global Instance string_Ord : Ord string := { lt := string_lt }.
End Ord.

Section OrdDec.
  Definition string_ord_dec := ord_dec `on` string2list.

  Global Instance string_OrdDec : OrdDec string := { ord_dec := string_ord_dec  }.
End OrdDec.

Section Show.
  Section string_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition string_show (s:string) : R :=
         raw_char """"%char
      ** raw_string s
      ** raw_char """"%char.
  End string_show.

  Global Instance string_Show : Show string := { show := string_show }.
End Show.

Section Monoid.
  Global Instance string_Monoid : Monoid string :=
    { Monoid_Semigroup := {| gtimes := String.append |}
    ; gunit := EmptyString
    }.
End Monoid.

Section Injection.
  Global Instance string_ascii_Injection : Injection ascii string :=
    { inject c := String c EmptyString }.
End Injection.