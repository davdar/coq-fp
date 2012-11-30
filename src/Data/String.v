Require Export FP.Data.StringPre.

Require Import FP.Data.FunctionPre.

Require Import FP.Data.Ascii.
Require Import FP.Data.PrettyI.
Require Import FP.Data.List.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Monad.
Require Import FP.Data.N.
Require Import FP.Structures.Comonad.

Import ComonadNotation.
Import CharNotation.
Import EqDecNotation.
Import FunctionNotation.
Import MonoidNotation.

Module StringNotation.
  Delimit Scope string_scope with string.
End StringNotation.
Open Scope string_scope.

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

Section Foldable.
  Fixpoint string_cofold {w} {W:Comonad w} {B} (f:ascii -> w B -> B) (bW:w B) (t:string) : B :=
    match t with
    | EmptyString => coret bW
    | String a t =>
        let bW := codo bW => string_cofold f bW t
        in f a bW
    end.
  Global Instance string_Foldable : Foldable ascii string :=
    { cofold := @string_cofold }.
End Foldable.

Section Buildable.
  Definition string_mbuild {m} {M:Monad m} (f:forall {C}, (ascii -> C -> C) -> C -> m C) : m string :=
    f String EmptyString.
  Global Instance string_Buildable : Buildable ascii string :=
    { mbuild := @string_mbuild }.
End Buildable.

Instance N_Pretty : Pretty N := { pretty := text_d <.> show }.
