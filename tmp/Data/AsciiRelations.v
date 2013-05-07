Require Import FP.Data.Bool.
Require Import FP.Data.BoolRelations.
Require Import FP.Data.Prod.
Require Import FP.Data.ProdRelations.
Require Import FP.Data.Function.
Require Import FP.Data.Ascii.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.

Import FunctionNotation.

Section EqDec.
  Definition ascii_eq_dec := eq_dec `on` ascii2prod.

  Global Instance ascii_EqDec : EqDec ascii := { eq_dec := ascii_eq_dec }.
End EqDec.

Section Eqv.
  Global Instance ascii_Eqv : Eqv ascii := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance ascii_EqvDec : EqvDec ascii := { eqv_dec := eq_dec }.
End EqvDec.

Section Ord.
  Definition ascii_lt := lt `on` ascii2prod.

  Global Instance ascii_Ord : Ord ascii := { lt := ascii_lt }.
End Ord.

Section OrdDec.
  Definition ascii_ord_dec := ord_dec `on` ascii2prod.

  Global Instance ascii_OrdDec : OrdDec ascii := { ord_dec := ascii_ord_dec  }.
End OrdDec.