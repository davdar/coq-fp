Require Import FP.Data.ListPre.
Require Import FP.Data.SumPre.

Require Import FP.Data.Function.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.

Import FunctionNotation.
Import FunctorNotation.
Import AdditiveNotation.
Import MultiplicativeNotation.

Local Infix "+" := sum.

Class Alternative t :=
  { fzero : forall {A}, t A
  ; fplus : forall {A B}, t A -> t B -> t (A+B)
  }.

Section Alternative.
  Context {t} {t_Functor : Functor t} {t_Alternative : Alternative t}.
  Definition fchoice {A} : t A -> t A -> t A := fmap collapse '..' fplus.

  Definition Alternative_Monoid {A} : Monoid (t A) :=
    {| monoid_times := fchoice
     ; monoid_unit := fzero
    |}.
End Alternative.

Module AlternativeNotation.
  Infix "<+>" := fplus (at level 48, left associativity).
  Infix "<|>" := fchoice (at level 48, left associativity).
End AlternativeNotation.

