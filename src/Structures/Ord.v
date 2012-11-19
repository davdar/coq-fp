Require Import Data.BoolPre.

Require Import Structures.Eqv.

Import BoolNotation.

Class Ord t := { ord_Eqv :> Eqv t ; lt : t -> t -> Prop }.
Class OrdDec t := { ord_dec_EqvDec :> EqvDec t ; ord_dec : t -> t -> comparison }.

Section Ord.
  Context {t} {O:Ord t}.

  Definition lte x y := lt x y \/ eqv x y.
End Ord.

Section OrdDec.
  Context {t} {tOD:OrdDec t}.

  Definition lt_dec x y :=
    match ord_dec x y with Lt => true  | Eq => false | Gt => false end.
  Definition lte_dec x y :=
    match ord_dec x y with Lt => true  | Eq => true  | Gt => false end.

  Context {tO:Ord t}.

  Definition ord_dec_p (x:t) (y:t) : {lt x y}+{eqv x y}+{lt y x}. Admitted.
  Definition lt_dec_p (x:t) (y:t) : {lt x y}+{~lt x y}. Admitted.
  Definition lte_dec_p (x:t) (y:t) : {lte x y}+{~lte x y}. Admitted.
  
End OrdDec.

Module OrdNotation.
  Notation "x '< y"       := (lt x y)
    (at level 70, no associativity).
  Notation "x '< y '< z" := (lt x y /\ lt y z)
    (at level 70, y at next level, no associativity).
  Notation "x '> y"       := (lt y x)
    (at level 70, no associativity, only parsing).
  Notation "x '> y '> z" := (lt z y /\ lt y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x '<= y"       := (lte x y)
    (at level 70, no associativity).
  Notation "x '<= y '<= z" := (lte x y /\ lte y z)
    (at level 70, y at next level, no associativity).
  Notation "x '>= y"       := (lte y x)
    (at level 70, no associativity, only parsing).
  Notation "x '>= y '>= z" := (lte z y /\ lte y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x '<! y"       := (lt_dec x y)
    (at level 35, no associativity).
  Notation "x '<! y '<! z"  := (lt_dec x y && lt_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>! y"       := (lt_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>! y '>! z"  := (lt_dec z y && lt_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x '<=! y"       := (lte_dec x y)
    (at level 35, no associativity).
  Notation "x '<=! y '<=! z" := (lte_dec x y && lte_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>=! y"       := (lte_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>=! y '>=! z" := (lte_dec z y && lte_dec y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x '<? y"       := (lt_dec_p x y)
    (at level 35, no associativity).
  Notation "x '<? y '<? z"  := (lt_dec_p x y /\ lt_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>? y"       := (lt_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>? y '>? z"  := (lt_dec_p z y /\ lt_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x '<=? y"       := (lte_dec_p x y)
    (at level 35, no associativity).
  Notation "x '<=? y '<=? z" := (lte_dec_p x y /\ lte_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>=? y"       := (lte_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>=? y '>=? z" := (lte_dec_p z y /\ lte_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x '<=>! y" := (ord_dec x y)
    (at level 35, no associativity).

  Notation "x '<=>? y" := (ord_dec_p x y)
    (at level 35, no associativity).
End OrdNotation.