Require Import FP.Data.ProdPre.
Require Import FP.Data.FunctionPre.

Require Import FP.Structures.Functor.

Import FunctionNotation.

Class Applicative t :=
  { fret : forall {A}, A -> t A
  ; fapply : forall {A B}, t (A -> B) -> t A -> t B
  }.

Definition apmap {t} {tA:Applicative t} {A B} : (A -> B) -> t A -> t B :=
  fapply <.> fret.

Instance Applicative_Functor {t} {tA:Applicative t} : Functor t :=
  { fmap _a _b := apmap }.

Definition fapplyl {t A B} {F:Applicative t} : t A -> t B -> t A :=
  fapply <.> fmap const.

Definition fapplyr {t A B} {F:Applicative t} : t A -> t B ->  t B :=
  fapply <.> fmap (const id).

Class Field t :=
  { times : t -> t -> t }.

Instance type_field : Field Type :=
  { times t1 t2 := prod t1 t2 }.

Definition ftimes {t A B} {F:Applicative t} : t A -> t B -> t (times A B) :=
  fun aT bT => fapply (fmap pair aT) bT.
    
Module ApplicativeNotation.
  Infix "<@>" := fapply (at level 46, left associativity).
  Infix "<@" := fapplyl (at level 46, left associativity).
  Infix "@>" := fapplyr (at level 46, left associativity).
  Infix "<*>" := ftimes (at level 47, left associativity).
End ApplicativeNotation.