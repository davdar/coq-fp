Require Import Data.String.
Require Import Data.Function.
Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Import StringNotation.

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

Section Ord.
  Definition unit_lt : unit -> unit -> Prop := const2 False.
  Global Instance unit_Ord : Ord unit := { lt := unit_lt }.
End Ord.

Section OrdDec.
  Definition unit_ord_dec : unit -> unit -> comparison := const2 Eq.
  Global Instance unit_OrdDec : OrdDec unit := { ord_dec := unit_ord_dec }.
End OrdDec.

Section Show.
  Section unit_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition unit_show (_x:unit) : R := raw_string "tt".
  End unit_show.

  Global Instance unit_Show : Show unit := { show := unit_show }.
End Show.