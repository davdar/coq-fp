Require Import Ascii.
Export Ascii.

Require Import StdFun.
Import FunNotation.
Require Import StdProd.
Require Import StdBool.
Require Import Equivalence.
Require Import RelDec.
Require Import Eq.
Import EqNotation.
Require Import Eqv.
Require Import Lte.
Require Import Show.
Require Import Monoid.
Import MonoidNotation.

Definition ascii2prod c :=
  let '(Ascii b1 b2 b3 b4 b5 b6 b7 b8) := c in (b1, b2, b3, b4, b5, b6, b7, b8).

Section EqDec.
  Definition ascii_eq_dec := eq_dec `on` ascii2prod.

  Global Instance ascii_EqDec : EqDec ascii := { eq_dec := ascii_eq_dec }.
  Global Instance ascii_Eq_RelDecCorrect : RelDecCorrect (T:=ascii) eq_dec eq.
  Admitted.
End EqDec.

Section Eqv.
  Global Instance ascii_Eqv : Eqv ascii := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance ascii_EqvDec : EqvDec ascii := { eqv_dec := eq_dec }.
  Global Instance ascii_Eqv_RelDecCorrect : RelDecCorrect (T:=ascii) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Lte.
  Definition ascii_lte := lte `on` ascii2prod.

  Global Instance ascii_Lte : Lte ascii := { lte := ascii_lte }.
  Global Instance ascii_PreOrder : PreOrder (A:=ascii) lte.
  Admitted.
End Lte.

Section LteDec.
  Definition ascii_lte_dec := lte_dec `on` ascii2prod.

  Global Instance ascii_LteDec : LteDec ascii := { lte_dec := ascii_lte_dec  }.
  Global Instance ascii_Lte_RelDecCorrect : RelDecCorrect (T:=ascii) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Section ascii_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition ascii_show (c:ascii) : R :=
         rawshow_char "'"
      ** rawshow_char c
      ** rawshow_char "'".
  End ascii_show.

  Global Instance ascii_Show : Show ascii := { show := ascii_show }.
End Show.