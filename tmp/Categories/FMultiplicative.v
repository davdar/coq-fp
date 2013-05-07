Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Functor.
Require Import FP.Structures.FUnit.
Require Import FP.Data.Type.
Require Import FP.Data.Function.

Import MultiplicativeNotation.
Import FunctionNotation.

Class FTimes (t:Type->Type) :=
  { ftimes : forall {A B}, t A -> t B -> t (A*B) }.

Class FMultiplicative (t:Type -> Type) : Type :=
  { FMultiplicative_FUnit : FUnit t
  ; FMultiplicative_FTimes : FTimes t
  }.
Hint Resolve Build_FMultiplicative : typeclass_instances.
Hint Immediate FMultiplicative_FUnit : typeclass_instances.
Hint Immediate FMultiplicative_FTimes : typeclass_instances.

Section FTimes.
  Context {t} {FMap:FMap t} {FTimes:FTimes t}.

  Definition ftimes_forget_right {A B} : t A -> t B -> t A :=
    fmap fst '..' ftimes.

  Definition ftimes_forget_left {A B} : t A -> t B -> t B :=
    fmap snd '..' ftimes.
End FTimes.

Module ApplicativeNotation.
  Infix "<*>" := ftimes (at level 47, left associativity).
  Infix "<*" := ftimes_forget_right (at level 46, left associativity).
  Infix "*>" := ftimes_forget_left (at level 46, left associativity).
End ApplicativeNotation.