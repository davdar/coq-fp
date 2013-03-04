Require BinNums.
Require BinInt.

Require Import FP.Data.Ascii.
Require Import FP.Data.Positive.
Require Import FP.Data.Nat.
Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Peano.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Show.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Convertible.

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
    if z1 =! z2 then Eq
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
  Definition Z_show {R} {SR:ShowResult R} : Z -> R := show '.' convert_to nat.
  Global Instance Z_Show : Show Z := { show := @Z_show }.
End Show.

Section Additive.
  Definition Z_additive_InvMonoid : InvMonoid Z :=
    {| inv_monoid_times := BinInt.Z.add
     ; inv_monoid_unit := BinInt.Z.zero
     ; inv_monoid_inv := BinInt.Z.opp
     ; inv_monoid_div := BinInt.Z.sub
    |}.
  Global Instance Z_InverseAdditive : NegAdditive Z :=
    { neg_additive_InvMonoid := Z_additive_InvMonoid }.
End Additive.

Section Multiplicative.
  Definition Z_multiplicative_Monoid : Monoid Z :=
    {| monoid_times := BinInt.Z.mul
     ; monoid_unit := BinInt.Z.one
    |}.
  Global Instance Z_Multiplicative : Multiplicative Z :=
    { multiplicative_Monoid := Z_multiplicative_Monoid }.
End Multiplicative.

Definition Z_coloopr {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (z:Z) : A :=
  match z with
  | Z0 => coret aM
  | Zpos p => coloopr f aM p
  | Zneg p => coloopr f aM p
  end.
Definition Z_coloopl {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (z:Z) : A :=
  match z with
  | Z0 => coret aM
  | Zpos p => coloopl f aM p
  | Zneg p => coloopl f aM p
  end.
Instance Z_Peano : Peano Z :=
  { pzero := Z0
  ; psucc := BinInt.Z.succ
  ; coloopr := @Z_coloopr
  ; coloopl := @Z_coloopl
  }.