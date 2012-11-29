Require BinNums.
Require BinInt.

Require Import Data.AsciiPre.

Require Import Data.Positive.
Require Import Data.Nat.
Require Import Data.Function.
Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Ord.
Require Import Structures.Monoid.
Require Import Structures.RelationClasses.
Require Import Structures.Show.
Require Import Structures.Additive.
Require Import Structures.Lattice.
Require Import Structures.Multiplicative.
Require Import Structures.Convertible.

Import MonoidNotation.
Import FunctionNotation.
Import EqDecNotation.

Definition Z := BinNums.Z.

Definition Z0 := BinNums.Z0.
Definition Zpos := BinNums.Zpos.
Definition Zneg := BinNums.Zneg.

Module ZNotation.
  Delimit Scope Z_scope with Z.
End ZNotation.

Instance Z_nat_Convertible : Convertible Z nat :=
  { convert := BinInt.Z.to_nat }.
Instance nat_Z_Convertible : Convertible nat Z :=
  { convert := BinInt.Z.of_nat }.

Section EqDec.
  Global Instance Z_EqDec : EqDec Z := { eq_dec := BinInt.Z.eqb }.
End EqDec.

Section Eqv.
  Global Instance Z_Eqv : Eqv Z := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance Z_EqvDec : EqvDec Z := { eqv_dec := eq_dec }.
End EqvDec.

Section Ord.
  Global Instance Z_Ord : Ord Z := { lt := BinInt.Z.lt }.
End Ord.

Section OrdDec.
  Definition Z_ord_dec (z1:Z) (z2:Z) : comparison :=
    if z1 '=! z2 then Eq
    else if BinInt.Z.ltb z1 z2 then Lt
    else Gt.
  Global Instance Z_OrdDec : OrdDec Z := { ord_dec := Z_ord_dec }.
End OrdDec.

Section Lattice.
  Global Instance Z_Lattice : Lattice Z :=
    { lmeet := BinInt.Z.min
    ; ljoin := BinInt.Z.max
    }.
End Lattice.

Section Show.
  Definition Z_show {R} {SR:ShowResult R} : Z -> R := show <.> convert (to:=nat).
  Global Instance Z_Show : Show Z := { show := @Z_show }.
End Show.

Section Additive.
  Definition Z_additive_InverseMonoid : InverseMonoid Z :=
    {| InverseMonoid_Monoid := 
        {| Monoid_Semigroup :=
             {| gtimes := BinInt.Z.add |}
         ; gunit := BinInt.Z.zero
        |}
     ; ginv := BinInt.Z.opp
     ; gdiv := BinInt.Z.sub
    |}.
  Global Instance Z_InverseAdditive : InverseAdditive Z :=
    { InverseAdditive_InverseMonoid := Z_additive_InverseMonoid }.
End Additive.

Section Multiplicative.
  Definition Z_multiplicative_Monoid : Monoid Z :=
    {| Monoid_Semigroup := {| gtimes := BinInt.Z.mul |}
     ; gunit := BinInt.Z.one
    |}.
  Global Instance Z_Multiplicative : Multiplicative Z :=
    { Multiplicative_Monoid := Z_multiplicative_Monoid }.
End Multiplicative.