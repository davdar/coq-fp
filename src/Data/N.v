Require Export Data.NPre.

Require Import Data.AsciiPre.
Require Import Data.FunctionPre.

Require Import Data.Nat.
Require Import Data.Positive.
Require Import Relations.RelDec.
Require Import Structures.Additive.
Require Import Structures.Convertible.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lattice.
Require Import Structures.Monoid.
Require Import Structures.Multiplicative.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.
Require Import Structures.Comonad.
Require Import Structures.Foldable.
Require Import Structures.Peano.

Import EqDecNotation.
Import FunctionNotation.
Import MonoidNotation.
Import ComonadNotation.

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
    { meet := BinNat.N.min
    ; join := BinNat.N.max
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

Definition N_cofoldr {m} {M:Comonad m} {A} (f:N -> m A -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM =>
    match n with
    | N0 => coret aM
    | Npos p => cofoldr (fun p aM => f (Npos p) aM) aM p
    end
  in
  f N0 aM.
Instance N_FoldableR : FoldableR N N := { cofoldr := @N_cofoldr }.

Definition N_cofoldl {m} {M:Comonad m} {A} (f:m A -> N -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM => f aM N0 in
  match n with
  | N0 => coret aM
  | Npos p => cofoldl (fun aM p => f aM (Npos p)) aM p
  end.
Instance N_FoldableL : FoldableL N N := { cofoldl := @N_cofoldl }.

Definition N_iterr {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM =>
    match n with
    | N0 => coret aM
    | Npos p => coiterr f aM p
    end
  in
  f aM.
Instance N_PeanoR : PeanoR N := { coiterr := @N_iterr }.

Definition N_iterl {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:N) : A :=
  let aM := codo aM => f aM in
  match n with
  | N0 => coret aM
  | Npos p => coiterl f aM p
  end.
Instance N_PeanoL : PeanoL N := { coiterl := @N_iterl }.