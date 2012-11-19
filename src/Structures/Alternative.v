Require Import Data.FunctionPre.
Require Import Data.ListPre.

Require Import Data.SumPre.
Require Import Structures.Additive.
Require Import Structures.Applicative.
Require Import Structures.Functor.
Require Import Structures.Monoid.
Require Import Structures.Multiplicative.

Import FunctionNotation.
Import FunctorNotation.
Import AdditiveNotation.
Import MultiplicativeNotation.

Local Infix "+" := sum.

Class Alternative t :=
  { fzero : forall {A}, t A
  ; fplus : forall {A B}, t A -> t B -> t (A+B)
  }.

Definition fchoice {t} {F:Functor t} {P:Alternative t} {A} : t A -> t A -> t A :=
  fmap collapse <..> fplus.

Module AlternativeNotation.
  Infix "<+>" := fplus (at level 48, left associativity).
  Infix "<|>" := fchoice (at level 48, left associativity).
End AlternativeNotation.
Import AlternativeNotation.

Section Alternative.
  Context {t} {F:Functor t} {A:Alternative t}.

  Definition fchoices {A} : list (t A) -> t A := foldr fchoice fzero.
End Alternative.

Instance Alternative_Monoid {m} {M:Applicative m} {MP:Alternative m} {A} : Monoid (m A) :=
  { Monoid_Semigroup := {| gtimes := fchoice |}
  ; gunit := fzero
  }.
