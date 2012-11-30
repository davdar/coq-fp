Require Export FP.Data.NPre.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.FunctionPre.

Require Import FP.Data.Nat.
Require Import FP.Data.Positive.
Require Import FP.Data.PrettyI.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Convertible.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Peano.

Import EqDecNotation.
Import FunctionNotation.
Import MonoidNotation.
Import ComonadNotation.

Definition small_N :=        10.
Definition medium_N :=     1000.
Definition large_N  :=   100000.
Definition larger_N := 10000000.
 

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
    if z1 '=! z2 then Eq
    else if BinNat.N.ltb z1 z2 then Lt
    else Gt.
  Global Instance N_OrdDec : OrdDec N := { ord_dec := N_ord_dec }.
End OrdDec.

Section Lattice.
  Global Instance N_Lattice : Lattice N :=
    { lmeet := BinNat.N.min
    ; ljoin := BinNat.N.max
    }.
End Lattice.

Section Show.
  Definition N_show {R} {SR:ShowResult R} : N -> R := show <.> convert (to:=nat).
  Global Instance N_Show : Show N := { show := @N_show }.
End Show.

Section Additive.
  Definition additive_N_Monoid : Monoid N :=
    {| Monoid_Semigroup := {| gtimes := BinNat.N.add |}
     ; gunit := BinNat.N.zero
    |}.
  Global Instance Additive_N : Additive N :=
    { Additive_Monoid := additive_N_Monoid }.
End Additive.

Section Multiplicative.
  Definition multiplicative_N_Monoid : Monoid N :=
    {| Monoid_Semigroup := {| gtimes := BinNat.N.mul |}
     ; gunit := BinNat.N.one 
    |}.
  Global Instance Multiplicative_N : Multiplicative N :=
    { Multiplicative_Monoid := multiplicative_N_Monoid }.
End Multiplicative.

Definition N_cofold {m} {M:Comonad m} {A} (f:N -> m A -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM =>
    match n with
    | N0 => coret aM
    | Npos p => cofold (fun p aM => f (Npos p) aM) aM p
    end
  in
  f N0 aM.
Instance N_Foldable : Foldable N N := { cofold := @N_cofold }.

Definition N_coiter {m} {M:Comonad m} {A} (f:m A -> N -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM => f aM N0 in
  match n with
  | N0 => coret aM
  | Npos p => coiter (fun aM p => f aM (Npos p)) aM p
  end.
Instance N_Iterable : Iterable N N := { coiter := @N_coiter }.

Definition N_coloopr {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:N) : A :=
  match n with
  | N0 => coret aM
  | Npos p => coloopr f aM p
  end.
Definition N_coloopl {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:N) : A :=
  match n with
  | N0 => coret aM
  | Npos p => coloopl f aM p
  end.
Instance N_Peano : Peano N :=
  { pzero := N0
  ; psucc := BinNat.N.succ
  ; coloopr := @N_coloopr
  ; coloopl := @N_coloopl
  }.