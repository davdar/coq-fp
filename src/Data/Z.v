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
    { meet := BinInt.Z.min
    ; join := BinInt.Z.max
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

(*
Definition Z_foldl {A} (f:Z -> A -> A) (a:A) (n:Z) : A :=
  let a' := f Z0 a in
  match n with
  | Z0 => a'
  | Zpos p => pos_foldl (fun p' a'' => f (Zpos p') a'') a' p
  | Zneg p => pos_foldl (fun p' a'' => f (Zneg p') a'') a' p
  end.
Definition Z_iterl {A} (f:A -> A) : A -> Z -> A := Z_foldl $ const f.

Definition Z_foldl_k {A} (f:forall {B}, Z -> (B -> A) -> B -> A) (a:A) (n:Z) : A :=
  let a' := f Z0 id a in
  match n with
  | Z0 => a'
  | Zpos p => pos_foldl_k (fun _ p' ak b => f (Zpos p') ak b) a' p
  | Zneg p => pos_foldl_k (fun _ p' ak b => f (Zneg p') ak b) a' p
  end.
Definition Z_iterl_k {A} (f:forall {B}, (B -> A) -> B -> A) : A -> Z -> A := Z_foldl_k $ fun _ => const f.

*)