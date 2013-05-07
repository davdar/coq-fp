Require Coq.NArith.BinNat.

Require Import FP.Data.Nat.
Require Import FP.Data.N.
Require Import FP.Data.Positive.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Show.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Peano.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Convertible.
Require Import FP.Data.Function.

Import FunctionNotation.
Import ComonadNotation.

Instance N_nat_Convertible : Convertible N nat :=
  { convert := BinNat.N.to_nat }.
Instance nat_N_Convertible : Convertible nat N :=
  { convert := BinNat.N.of_nat }.

Instance N_Convertible_Z : Convertible N BinNums.Z :=
  { convert := N2Z }.

Section Lattice.
  Global Instance N_Lattice : Lattice N :=
    { lmeet := BinNat.N.min
    ; ljoin := BinNat.N.max
    }.
End Lattice.

Section Show.
  Definition N_show {R} {SR:ShowResult R} : N -> R := show '.' convert_to nat.
  Global Instance N_Show : Show N := { show := @N_show }.
End Show.

Section Additive.
  Definition additive_N_DivMonoid : DivMonoid N :=
    {| div_monoid_times := BinNat.N.add
     ; div_monoid_unit := BinNat.N.zero
     ; div_monoid_div := BinNat.N.sub
    |}.
  Global Instance MinusAdditive_N : MinusAdditive N :=
    { minus_additive_DivMonoid := additive_N_DivMonoid }.
End Additive.

Section Multiplicative.
  Definition multiplicative_N_Monoid : Monoid N :=
    {| monoid_times := BinNat.N.mul
     ; monoid_unit := BinNat.N.one 
    |}.
  Global Instance Multiplicative_N : Multiplicative N :=
    { multiplicative_Monoid := multiplicative_N_Monoid }.
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