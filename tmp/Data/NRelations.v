Require Coq.NArith.BinNat.

Require Import FP.Data.N.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.

Import EqDecNotation.

Section EqDec.
  Global Instance N_EqDec : EqDec N := { eq_dec := BinNat.N.eqb }.
End EqDec.

Section Eqv.
  Global Instance N_Eqv : Eqv N := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance N_EqvDec : EqvDec N := { eqv_dec := eq_dec }.
End EqvDec.

Section Ord.
  Global Instance N_Ord : Ord N := { lt := BinNat.N.lt }.
End Ord.

Section OrdDec.
  Definition N_ord_dec (z1:N) (z2:N) : comparison :=
    if z1 =! z2 then Eq
    else if BinNat.N.ltb z1 z2 then Lt
    else Gt.
  Global Instance N_OrdDec : OrdDec N := { ord_dec := N_ord_dec }.
End OrdDec.
