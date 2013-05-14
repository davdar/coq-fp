Require Import FP.Categories.Pointed.
Require Import FP.Categories.Monad.

Definition functor := Type -> Type.
Definition functor_morphism (t u:functor) := forall A, t A -> u A.
Module MorphismNotation.
  Infix "->>" := functor_morphism (at level 80, right associativity).
End MorphismNotation.
Import MorphismNotation.

Class FFUnit t := { ffunit : forall {m} `{! FUnit m ,! MBind m }, m ->> t m }.

Class FFMap t :=
  { ffmap : forall {m n} `{! FUnit m ,! MBind m ,! FUnit n ,! MBind m },
    (m ->> n) -> (t m ->> t n)
  }.
